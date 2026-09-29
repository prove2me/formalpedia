-- Prove2me | solution 1 for syracuse_descends_range_1182408_1184408
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:10:33.274357+00:00
-- url     : https://prove2.me/submissions/fb437d2c-d90c-454b-8c1f-59c5720a6df5

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


theorem B2400301 : Blo 1182408 2400301 := bbase (se 3 (by rfl) ⟨450056, by rfl⟩ : syracuseStep 2400301 = 900113) (by norm_num)
theorem B2662469 : Blo 1182408 2662469 := bbase (se 4 (by rfl) ⟨249606, by rfl⟩ : syracuseStep 2662469 = 499213) (by norm_num)
theorem B2842733 : Blo 1182408 2842733 := bbase (se 3 (by rfl) ⟨533012, by rfl⟩ : syracuseStep 2842733 = 1066025) (by norm_num)
theorem B2662541 : Blo 1182408 2662541 := bbase (se 3 (by rfl) ⟨499226, by rfl⟩ : syracuseStep 2662541 = 998453) (by norm_num)
theorem B2244773 : Blo 1182408 2244773 := bbase (se 4 (by rfl) ⟨210447, by rfl⟩ : syracuseStep 2244773 = 420895) (by norm_num)
theorem B2662613 : Blo 1182408 2662613 := bbase (se 7 (by rfl) ⟨31202, by rfl⟩ : syracuseStep 2662613 = 62405) (by norm_num)
theorem B2662685 : Blo 1182408 2662685 := bbase (se 3 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 2662685 = 998507) (by norm_num)
theorem B2244925 : Blo 1182408 2244925 := bbase (se 3 (by rfl) ⟨420923, by rfl⟩ : syracuseStep 2244925 = 841847) (by norm_num)
theorem B2662757 : Blo 1182408 2662757 := bbase (se 4 (by rfl) ⟨249633, by rfl⟩ : syracuseStep 2662757 = 499267) (by norm_num)
theorem B2662829 : Blo 1182408 2662829 := bbase (se 3 (by rfl) ⟨499280, by rfl⟩ : syracuseStep 2662829 = 998561) (by norm_num)
theorem B2662901 : Blo 1182408 2662901 := bbase (se 5 (by rfl) ⟨124823, by rfl⟩ : syracuseStep 2662901 = 249647) (by norm_num)
theorem B2163245 : Blo 1182408 2163245 := bbase (se 3 (by rfl) ⟨405608, by rfl⟩ : syracuseStep 2163245 = 811217) (by norm_num)
theorem B4268597 : Blo 1182408 4268597 := bbase (se 5 (by rfl) ⟨200090, by rfl⟩ : syracuseStep 4268597 = 400181) (by norm_num)
theorem B2662973 : Blo 1182408 2662973 := bbase (se 3 (by rfl) ⟨499307, by rfl⟩ : syracuseStep 2662973 = 998615) (by norm_num)
theorem B2024029 : Blo 1182408 2024029 := bbase (se 3 (by rfl) ⟨379505, by rfl⟩ : syracuseStep 2024029 = 759011) (by norm_num)
theorem B2245229 : Blo 1182408 2245229 := bbase (se 3 (by rfl) ⟨420980, by rfl⟩ : syracuseStep 2245229 = 841961) (by norm_num)
theorem B2663045 : Blo 1182408 2663045 := bbase (se 4 (by rfl) ⟨249660, by rfl⟩ : syracuseStep 2663045 = 499321) (by norm_num)
theorem B1598125 : Blo 1182408 1598125 := bbase (se 3 (by rfl) ⟨299648, by rfl⟩ : syracuseStep 1598125 = 599297) (by norm_num)
theorem B2663117 : Blo 1182408 2663117 := bbase (se 3 (by rfl) ⟨499334, by rfl⟩ : syracuseStep 2663117 = 998669) (by norm_num)
theorem B2663189 : Blo 1182408 2663189 := bbase (se 6 (by rfl) ⟨62418, by rfl⟩ : syracuseStep 2663189 = 124837) (by norm_num)
theorem B2663261 : Blo 1182408 2663261 := bbase (se 3 (by rfl) ⟨499361, by rfl⟩ : syracuseStep 2663261 = 998723) (by norm_num)
theorem B3597205 : Blo 1182408 3597205 := bbase (se 6 (by rfl) ⟨84309, by rfl⟩ : syracuseStep 3597205 = 168619) (by norm_num)
theorem B2024357 : Blo 1182408 2024357 := bbase (se 4 (by rfl) ⟨189783, by rfl⟩ : syracuseStep 2024357 = 379567) (by norm_num)
theorem B2663333 : Blo 1182408 2663333 := bbase (se 4 (by rfl) ⟨249687, by rfl⟩ : syracuseStep 2663333 = 499375) (by norm_num)
theorem B5989301 : Blo 1182408 5989301 := bbase (se 5 (by rfl) ⟨280748, by rfl⟩ : syracuseStep 5989301 = 561497) (by norm_num)
theorem B2663405 : Blo 1182408 2663405 := bbase (se 3 (by rfl) ⟨499388, by rfl⟩ : syracuseStep 2663405 = 998777) (by norm_num)
theorem B4490261 : Blo 1182408 4490261 := bbase (se 6 (by rfl) ⟨105240, by rfl⟩ : syracuseStep 4490261 = 210481) (by norm_num)
theorem B2663477 : Blo 1182408 2663477 := bbase (se 5 (by rfl) ⟨124850, by rfl⟩ : syracuseStep 2663477 = 249701) (by norm_num)
theorem B2663549 : Blo 1182408 2663549 := bbase (se 3 (by rfl) ⟨499415, by rfl⟩ : syracuseStep 2663549 = 998831) (by norm_num)
theorem B3794053 : Blo 1182408 3794053 := bbase (se 4 (by rfl) ⟨355692, by rfl⟩ : syracuseStep 3794053 = 711385) (by norm_num)
theorem B2278541 : Blo 1182408 2278541 := bbase (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) (by norm_num)
theorem B3368117 : Blo 1182408 3368117 := bbase (se 5 (by rfl) ⟨157880, by rfl⟩ : syracuseStep 3368117 = 315761) (by norm_num)
theorem B2663621 : Blo 1182408 2663621 := bbase (se 4 (by rfl) ⟨249714, by rfl⟩ : syracuseStep 2663621 = 499429) (by norm_num)
theorem B2663693 : Blo 1182408 2663693 := bbase (se 3 (by rfl) ⟨499442, by rfl⟩ : syracuseStep 2663693 = 998885) (by norm_num)
theorem B4490549 : Blo 1182408 4490549 := bbase (se 5 (by rfl) ⟨210494, by rfl⟩ : syracuseStep 4490549 = 420989) (by norm_num)
theorem B5055797 : Blo 1182408 5055797 := bbase (se 5 (by rfl) ⟨236990, by rfl⟩ : syracuseStep 5055797 = 473981) (by norm_num)
theorem B3990869 : Blo 1182408 3990869 := bbase (se 12 (by rfl) ⟨1461, by rfl⟩ : syracuseStep 3990869 = 2923) (by norm_num)
theorem B2663765 : Blo 1182408 2663765 := bbase (se 12 (by rfl) ⟨975, by rfl⟩ : syracuseStep 2663765 = 1951) (by norm_num)
theorem B2245981 : Blo 1182408 2245981 := bbase (se 3 (by rfl) ⟨421121, by rfl⟩ : syracuseStep 2245981 = 842243) (by norm_num)
theorem B1598821 : Blo 1182408 1598821 := bbase (se 4 (by rfl) ⟨149889, by rfl⟩ : syracuseStep 1598821 = 299779) (by norm_num)
theorem B1262989 : Blo 1182408 1262989 := bbase (se 3 (by rfl) ⟨236810, by rfl⟩ : syracuseStep 1262989 = 473621) (by norm_num)
theorem B2663837 : Blo 1182408 2663837 := bbase (se 3 (by rfl) ⟨499469, by rfl⟩ : syracuseStep 2663837 = 998939) (by norm_num)
theorem B1263061 : Blo 1182408 1263061 := bbase (se 7 (by rfl) ⟨14801, by rfl⟩ : syracuseStep 1263061 = 29603) (by norm_num)
theorem B5400037 : Blo 1182408 5400037 := bbase (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) (by norm_num)
theorem B2663909 : Blo 1182408 2663909 := bbase (se 4 (by rfl) ⟨249741, by rfl⟩ : syracuseStep 2663909 = 499483) (by norm_num)
theorem B2246125 : Blo 1182408 2246125 := bbase (se 3 (by rfl) ⟨421148, by rfl⟩ : syracuseStep 2246125 = 842297) (by norm_num)
theorem B2663981 : Blo 1182408 2663981 := bbase (se 3 (by rfl) ⟨499496, by rfl⟩ : syracuseStep 2663981 = 998993) (by norm_num)
theorem B6735413 : Blo 1182408 6735413 := bbase (se 5 (by rfl) ⟨315722, by rfl⟩ : syracuseStep 6735413 = 631445) (by norm_num)
theorem B2664053 : Blo 1182408 2664053 := bbase (se 5 (by rfl) ⟨124877, by rfl⟩ : syracuseStep 2664053 = 249755) (by norm_num)
theorem B2737781 : Blo 1182408 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B2246285 : Blo 1182408 2246285 := bbase (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) (by norm_num)
theorem B1517221 : Blo 1182408 1517221 := bbase (se 4 (by rfl) ⟨142239, by rfl⟩ : syracuseStep 1517221 = 284479) (by norm_num)
theorem B2664125 : Blo 1182408 2664125 := bbase (se 3 (by rfl) ⟨499523, by rfl⟩ : syracuseStep 2664125 = 999047) (by norm_num)
theorem B3991301 : Blo 1182408 3991301 := bbase (se 4 (by rfl) ⟨374184, by rfl⟩ : syracuseStep 3991301 = 748369) (by norm_num)
theorem B2664197 : Blo 1182408 2664197 := bbase (se 4 (by rfl) ⟨249768, by rfl⟩ : syracuseStep 2664197 = 499537) (by norm_num)
theorem B2246429 : Blo 1182408 2246429 := bbase (se 3 (by rfl) ⟨421205, by rfl⟩ : syracuseStep 2246429 = 842411) (by norm_num)
theorem B1263433 : Blo 1182408 1263433 := bbase (se 2 (by rfl) ⟨473787, by rfl⟩ : syracuseStep 1263433 = 947575) (by norm_num)
theorem B2664269 : Blo 1182408 2664269 := bbase (se 3 (by rfl) ⟨499550, by rfl⟩ : syracuseStep 2664269 = 999101) (by norm_num)
theorem B11364245 : Blo 1182408 11364245 := bbase (se 6 (by rfl) ⟨266349, by rfl⟩ : syracuseStep 11364245 = 532699) (by norm_num)
theorem B2664341 : Blo 1182408 2664341 := bbase (se 6 (by rfl) ⟨62445, by rfl⟩ : syracuseStep 2664341 = 124891) (by norm_num)
theorem B2131877 : Blo 1182408 2131877 := bbase (se 4 (by rfl) ⟨199863, by rfl⟩ : syracuseStep 2131877 = 399727) (by norm_num)
theorem B9734069 : Blo 1182408 9734069 := bbase (se 5 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 9734069 = 912569) (by norm_num)
theorem B1894349 : Blo 1182408 1894349 := bbase (se 3 (by rfl) ⟨355190, by rfl⟩ : syracuseStep 1894349 = 710381) (by norm_num)
theorem B2664413 : Blo 1182408 2664413 := bbase (se 3 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 2664413 = 999155) (by norm_num)
theorem B4794389 : Blo 1182408 4794389 := bbase (se 6 (by rfl) ⟨112368, by rfl⟩ : syracuseStep 4794389 = 224737) (by norm_num)
theorem B4261909 : Blo 1182408 4261909 := bbase (se 6 (by rfl) ⟨99888, by rfl⟩ : syracuseStep 4261909 = 199777) (by norm_num)
theorem B4556837 : Blo 1182408 4556837 := bbase (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) (by norm_num)
theorem B2664485 : Blo 1182408 2664485 := bbase (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) (by norm_num)
theorem B2246717 : Blo 1182408 2246717 := bbase (se 3 (by rfl) ⟨421259, by rfl⟩ : syracuseStep 2246717 = 842519) (by norm_num)
theorem B2844733 : Blo 1182408 2844733 := bbase (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) (by norm_num)
theorem B2664557 : Blo 1182408 2664557 := bbase (se 3 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 2664557 = 999209) (by norm_num)
theorem B1517725 : Blo 1182408 1517725 := bbase (se 3 (by rfl) ⟨284573, by rfl⟩ : syracuseStep 1517725 = 569147) (by norm_num)
theorem B4262053 : Blo 1182408 4262053 := bbase (se 4 (by rfl) ⟨399567, by rfl⟩ : syracuseStep 4262053 = 799135) (by norm_num)
theorem B3991733 : Blo 1182408 3991733 := bbase (se 5 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 3991733 = 374225) (by norm_num)
theorem B2664629 : Blo 1182408 2664629 := bbase (se 5 (by rfl) ⟨124904, by rfl⟩ : syracuseStep 2664629 = 249809) (by norm_num)
theorem B1263809 : Blo 1182408 1263809 := bbase (se 2 (by rfl) ⟨473928, by rfl⟩ : syracuseStep 1263809 = 947857) (by norm_num)
theorem B5990597 : Blo 1182408 5990597 := bbase (se 4 (by rfl) ⟨561618, by rfl⟩ : syracuseStep 5990597 = 1123237) (by norm_num)
theorem B2844877 : Blo 1182408 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B2246869 : Blo 1182408 2246869 := bbase (se 7 (by rfl) ⟨26330, by rfl⟩ : syracuseStep 2246869 = 52661) (by norm_num)
theorem B1894637 : Blo 1182408 1894637 := bbase (se 3 (by rfl) ⟨355244, by rfl⟩ : syracuseStep 1894637 = 710489) (by norm_num)
theorem B7194869 : Blo 1182408 7194869 := bbase (se 5 (by rfl) ⟨337259, by rfl⟩ : syracuseStep 7194869 = 674519) (by norm_num)
theorem B2664701 : Blo 1182408 2664701 := bbase (se 3 (by rfl) ⟨499631, by rfl⟩ : syracuseStep 2664701 = 999263) (by norm_num)
theorem B1263881 : Blo 1182408 1263881 := bbase (se 2 (by rfl) ⟨473955, by rfl⟩ : syracuseStep 1263881 = 947911) (by norm_num)
theorem B5056789 : Blo 1182408 5056789 := bbase (se 6 (by rfl) ⟨118518, by rfl⟩ : syracuseStep 5056789 = 237037) (by norm_num)
theorem B2664773 : Blo 1182408 2664773 := bbase (se 4 (by rfl) ⟨249822, by rfl⟩ : syracuseStep 2664773 = 499645) (by norm_num)
theorem B2664845 : Blo 1182408 2664845 := bbase (se 3 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 2664845 = 999317) (by norm_num)
theorem B1599925 : Blo 1182408 1599925 := bbase (se 5 (by rfl) ⟨74996, by rfl⟩ : syracuseStep 1599925 = 149993) (by norm_num)
theorem B1264069 : Blo 1182408 1264069 := bbase (se 4 (by rfl) ⟨118506, by rfl⟩ : syracuseStep 1264069 = 237013) (by norm_num)
theorem B1894861 : Blo 1182408 1894861 := bbase (se 3 (by rfl) ⟨355286, by rfl⟩ : syracuseStep 1894861 = 710573) (by norm_num)
theorem B4491733 : Blo 1182408 4491733 := bbase (se 7 (by rfl) ⟨52637, by rfl⟩ : syracuseStep 4491733 = 105275) (by norm_num)
theorem B2664917 : Blo 1182408 2664917 := bbase (se 7 (by rfl) ⟨31229, by rfl⟩ : syracuseStep 2664917 = 62459) (by norm_num)
theorem B2247173 : Blo 1182408 2247173 := bbase (se 4 (by rfl) ⟨210672, by rfl⟩ : syracuseStep 2247173 = 421345) (by norm_num)
theorem B6400565 : Blo 1182408 6400565 := bbase (se 5 (by rfl) ⟨300026, by rfl⟩ : syracuseStep 6400565 = 600053) (by norm_num)
theorem B3992165 : Blo 1182408 3992165 := bbase (se 4 (by rfl) ⟨374265, by rfl⟩ : syracuseStep 3992165 = 748531) (by norm_num)
theorem B1264253 : Blo 1182408 1264253 := bbase (se 3 (by rfl) ⟨237047, by rfl⟩ : syracuseStep 1264253 = 474095) (by norm_num)
theorem B2525917 : Blo 1182408 2525917 := bbase (se 3 (by rfl) ⟨473609, by rfl⟩ : syracuseStep 2525917 = 947219) (by norm_num)
theorem B3369701 : Blo 1182408 3369701 := bbase (se 4 (by rfl) ⟨315909, by rfl⟩ : syracuseStep 3369701 = 631819) (by norm_num)
theorem B4492037 : Blo 1182408 4492037 := bbase (se 4 (by rfl) ⟨421128, by rfl⟩ : syracuseStep 4492037 = 842257) (by norm_num)
theorem B2845493 : Blo 1182408 2845493 := bbase (se 5 (by rfl) ⟨133382, by rfl⟩ : syracuseStep 2845493 = 266765) (by norm_num)
theorem B2993021 : Blo 1182408 2993021 := bbase (se 3 (by rfl) ⟨561191, by rfl⟩ : syracuseStep 2993021 = 1122383) (by norm_num)
theorem B1280917 : Blo 1182408 1280917 := bbase (se 6 (by rfl) ⟨30021, by rfl⟩ : syracuseStep 1280917 = 60043) (by norm_num)
theorem B3992597 : Blo 1182408 3992597 := bbase (se 6 (by rfl) ⟨93576, by rfl⟩ : syracuseStep 3992597 = 187153) (by norm_num)
theorem B1330213 : Blo 1182408 1330213 := bbase (se 4 (by rfl) ⟨124707, by rfl⟩ : syracuseStep 1330213 = 249415) (by norm_num)
theorem B2993213 : Blo 1182408 2993213 := bbase (se 3 (by rfl) ⟨561227, by rfl⟩ : syracuseStep 2993213 = 1122455) (by norm_num)
theorem B1330249 : Blo 1182408 1330249 := bbase (se 2 (by rfl) ⟨498843, by rfl⟩ : syracuseStep 1330249 = 997687) (by norm_num)
theorem B1330285 : Blo 1182408 1330285 := bbase (se 3 (by rfl) ⟨249428, by rfl⟩ : syracuseStep 1330285 = 498857) (by norm_num)
theorem B1330321 : Blo 1182408 1330321 := bbase (se 2 (by rfl) ⟨498870, by rfl⟩ : syracuseStep 1330321 = 997741) (by norm_num)
theorem B4795541 : Blo 1182408 4795541 := bbase (se 6 (by rfl) ⟨112395, by rfl⟩ : syracuseStep 4795541 = 224791) (by norm_num)
theorem B4500629 : Blo 1182408 4500629 := bbase (se 6 (by rfl) ⟨105483, by rfl⟩ : syracuseStep 4500629 = 210967) (by norm_num)
theorem B1330357 : Blo 1182408 1330357 := bbase (se 5 (by rfl) ⟨62360, by rfl⟩ : syracuseStep 1330357 = 124721) (by norm_num)
theorem B2133197 : Blo 1182408 2133197 := bbase (se 3 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 2133197 = 799949) (by norm_num)
theorem B6745301 : Blo 1182408 6745301 := bbase (se 7 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 6745301 = 158093) (by norm_num)
theorem B1330393 : Blo 1182408 1330393 := bbase (se 2 (by rfl) ⟨498897, by rfl⟩ : syracuseStep 1330393 = 997795) (by norm_num)
theorem B3788005 : Blo 1182408 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B2247925 : Blo 1182408 2247925 := bbase (se 5 (by rfl) ⟨105371, by rfl⟩ : syracuseStep 2247925 = 210743) (by norm_num)
theorem B1330429 : Blo 1182408 1330429 := bbase (se 3 (by rfl) ⟨249455, by rfl⟩ : syracuseStep 1330429 = 498911) (by norm_num)
theorem B1330465 : Blo 1182408 1330465 := bbase (se 2 (by rfl) ⟨498924, by rfl⟩ : syracuseStep 1330465 = 997849) (by norm_num)
theorem B1330501 : Blo 1182408 1330501 := bbase (se 4 (by rfl) ⟨124734, by rfl⟩ : syracuseStep 1330501 = 249469) (by norm_num)
theorem B1330537 : Blo 1182408 1330537 := bbase (se 2 (by rfl) ⟨498951, by rfl⟩ : syracuseStep 1330537 = 997903) (by norm_num)
theorem B3370373 : Blo 1182408 3370373 := bbase (se 4 (by rfl) ⟨315972, by rfl⟩ : syracuseStep 3370373 = 631945) (by norm_num)
theorem B2248069 : Blo 1182408 2248069 := bbase (se 4 (by rfl) ⟨210756, by rfl⟩ : syracuseStep 2248069 = 421513) (by norm_num)
theorem B1330573 : Blo 1182408 1330573 := bbase (se 3 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 1330573 = 498965) (by norm_num)
theorem B2993557 : Blo 1182408 2993557 := bbase (se 6 (by rfl) ⟨70161, by rfl⟩ : syracuseStep 2993557 = 140323) (by norm_num)
theorem B1330609 : Blo 1182408 1330609 := bbase (se 2 (by rfl) ⟨498978, by rfl⟩ : syracuseStep 1330609 = 997957) (by norm_num)
theorem B3034565 : Blo 1182408 3034565 := bbase (se 4 (by rfl) ⟨284490, by rfl⟩ : syracuseStep 3034565 = 568981) (by norm_num)
theorem B3993029 : Blo 1182408 3993029 := bbase (se 4 (by rfl) ⟨374346, by rfl⟩ : syracuseStep 3993029 = 748693) (by norm_num)
theorem B1330645 : Blo 1182408 1330645 := bbase (se 7 (by rfl) ⟨15593, by rfl⟩ : syracuseStep 1330645 = 31187) (by norm_num)
theorem B5991893 : Blo 1182408 5991893 := bbase (se 7 (by rfl) ⟨70217, by rfl⟩ : syracuseStep 5991893 = 140435) (by norm_num)
theorem B3788261 : Blo 1182408 3788261 := bbase (se 4 (by rfl) ⟨355149, by rfl⟩ : syracuseStep 3788261 = 710299) (by norm_num)
theorem B1330681 : Blo 1182408 1330681 := bbase (se 2 (by rfl) ⟨499005, by rfl⟩ : syracuseStep 1330681 = 998011) (by norm_num)
theorem B2993669 : Blo 1182408 2993669 := bbase (se 4 (by rfl) ⟨280656, by rfl⟩ : syracuseStep 2993669 = 561313) (by norm_num)
theorem B1330717 : Blo 1182408 1330717 := bbase (se 3 (by rfl) ⟨249509, by rfl⟩ : syracuseStep 1330717 = 499019) (by norm_num)
theorem B2248229 : Blo 1182408 2248229 := bbase (se 4 (by rfl) ⟨210771, by rfl⟩ : syracuseStep 2248229 = 421543) (by norm_num)
theorem B1895989 : Blo 1182408 1895989 := bbase (se 5 (by rfl) ⟨88874, by rfl⟩ : syracuseStep 1895989 = 177749) (by norm_num)
theorem B1330753 : Blo 1182408 1330753 := bbase (se 2 (by rfl) ⟨499032, by rfl⟩ : syracuseStep 1330753 = 998065) (by norm_num)
theorem B2526805 : Blo 1182408 2526805 := bbase (se 8 (by rfl) ⟨14805, by rfl⟩ : syracuseStep 2526805 = 29611) (by norm_num)
theorem B1330789 : Blo 1182408 1330789 := bbase (se 4 (by rfl) ⟨124761, by rfl⟩ : syracuseStep 1330789 = 249523) (by norm_num)
theorem B1199729 : Blo 1182408 1199729 := bbase (se 2 (by rfl) ⟨449898, by rfl⟩ : syracuseStep 1199729 = 899797) (by norm_num)
theorem B1330825 : Blo 1182408 1330825 := bbase (se 2 (by rfl) ⟨499059, by rfl⟩ : syracuseStep 1330825 = 998119) (by norm_num)
theorem B12136085 : Blo 1182408 12136085 := bbase (se 6 (by rfl) ⟨284439, by rfl⟩ : syracuseStep 12136085 = 568879) (by norm_num)
theorem B1330861 : Blo 1182408 1330861 := bbase (se 3 (by rfl) ⟨249536, by rfl⟩ : syracuseStep 1330861 = 499073) (by norm_num)
theorem B2248373 : Blo 1182408 2248373 := bbase (se 5 (by rfl) ⟨105392, by rfl⟩ : syracuseStep 2248373 = 210785) (by norm_num)
theorem B2993861 : Blo 1182408 2993861 := bbase (se 4 (by rfl) ⟨280674, by rfl⟩ : syracuseStep 2993861 = 561349) (by norm_num)
theorem B1330897 : Blo 1182408 1330897 := bbase (se 2 (by rfl) ⟨499086, by rfl⟩ : syracuseStep 1330897 = 998173) (by norm_num)
theorem B1330933 : Blo 1182408 1330933 := bbase (se 5 (by rfl) ⟨62387, by rfl⟩ : syracuseStep 1330933 = 124775) (by norm_num)
theorem B1421069 : Blo 1182408 1421069 := bbase (se 3 (by rfl) ⟨266450, by rfl⟩ : syracuseStep 1421069 = 532901) (by norm_num)
theorem B9596693 : Blo 1182408 9596693 := bbase (se 6 (by rfl) ⟨224922, by rfl⟩ : syracuseStep 9596693 = 449845) (by norm_num)
theorem B1330969 : Blo 1182408 1330969 := bbase (se 2 (by rfl) ⟨499113, by rfl⟩ : syracuseStep 1330969 = 998227) (by norm_num)
theorem B1519393 : Blo 1182408 1519393 := bbase (se 2 (by rfl) ⟨569772, by rfl⟩ : syracuseStep 1519393 = 1139545) (by norm_num)
theorem B3370805 : Blo 1182408 3370805 := bbase (se 5 (by rfl) ⟨158006, by rfl⟩ : syracuseStep 3370805 = 316013) (by norm_num)
theorem B1331005 : Blo 1182408 1331005 := bbase (se 3 (by rfl) ⟨249563, by rfl⟩ : syracuseStep 1331005 = 499127) (by norm_num)
theorem B13487957 : Blo 1182408 13487957 := bbase (se 9 (by rfl) ⟨39515, by rfl⟩ : syracuseStep 13487957 = 79031) (by norm_num)
theorem B1331041 : Blo 1182408 1331041 := bbase (se 2 (by rfl) ⟨499140, by rfl⟩ : syracuseStep 1331041 = 998281) (by norm_num)
theorem B3993461 : Blo 1182408 3993461 := bbase (se 5 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 3993461 = 374387) (by norm_num)
theorem B1331077 : Blo 1182408 1331077 := bbase (se 4 (by rfl) ⟨124788, by rfl⟩ : syracuseStep 1331077 = 249577) (by norm_num)
theorem B1331113 : Blo 1182408 1331113 := bbase (se 2 (by rfl) ⟨499167, by rfl⟩ : syracuseStep 1331113 = 998335) (by norm_num)
theorem B1707949 : Blo 1182408 1707949 := bbase (se 3 (by rfl) ⟨320240, by rfl⟩ : syracuseStep 1707949 = 640481) (by norm_num)
theorem B1200065 : Blo 1182408 1200065 := bbase (se 2 (by rfl) ⟨450024, by rfl⟩ : syracuseStep 1200065 = 900049) (by norm_num)
theorem B1331149 : Blo 1182408 1331149 := bbase (se 3 (by rfl) ⟨249590, by rfl⟩ : syracuseStep 1331149 = 499181) (by norm_num)
theorem B1331185 : Blo 1182408 1331185 := bbase (se 2 (by rfl) ⟨499194, by rfl⟩ : syracuseStep 1331185 = 998389) (by norm_num)
theorem B1896437 : Blo 1182408 1896437 := bbase (se 5 (by rfl) ⟨88895, by rfl⟩ : syracuseStep 1896437 = 177791) (by norm_num)
theorem B1331221 : Blo 1182408 1331221 := bbase (se 6 (by rfl) ⟨31200, by rfl⟩ : syracuseStep 1331221 = 62401) (by norm_num)
theorem B2994205 : Blo 1182408 2994205 := bbase (se 3 (by rfl) ⟨561413, by rfl⟩ : syracuseStep 2994205 = 1122827) (by norm_num)
theorem B1331257 : Blo 1182408 1331257 := bbase (se 2 (by rfl) ⟨499221, by rfl⟩ : syracuseStep 1331257 = 998443) (by norm_num)
theorem B1773629 : Blo 1182408 1773629 := bbase (se 3 (by rfl) ⟨332555, by rfl⟩ : syracuseStep 1773629 = 665111) (by norm_num)
theorem B2527301 : Blo 1182408 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B1773653 : Blo 1182408 1773653 := bbase (se 8 (by rfl) ⟨10392, by rfl⟩ : syracuseStep 1773653 = 20785) (by norm_num)
theorem B1331293 : Blo 1182408 1331293 := bbase (se 3 (by rfl) ⟨249617, by rfl⟩ : syracuseStep 1331293 = 499235) (by norm_num)
theorem B1773677 : Blo 1182408 1773677 := bbase (se 3 (by rfl) ⟨332564, by rfl⟩ : syracuseStep 1773677 = 665129) (by norm_num)
theorem B2191469 : Blo 1182408 2191469 := bbase (se 3 (by rfl) ⟨410900, by rfl⟩ : syracuseStep 2191469 = 821801) (by norm_num)
theorem B1421425 : Blo 1182408 1421425 := bbase (se 2 (by rfl) ⟨533034, by rfl⟩ : syracuseStep 1421425 = 1066069) (by norm_num)
theorem B1331329 : Blo 1182408 1331329 := bbase (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) (by norm_num)
theorem B1773701 : Blo 1182408 1773701 := bbase (se 4 (by rfl) ⟨166284, by rfl⟩ : syracuseStep 1773701 = 332569) (by norm_num)
theorem B2994317 : Blo 1182408 2994317 := bbase (se 3 (by rfl) ⟨561434, by rfl⟩ : syracuseStep 2994317 = 1122869) (by norm_num)
theorem B1773725 : Blo 1182408 1773725 := bbase (se 3 (by rfl) ⟨332573, by rfl⟩ : syracuseStep 1773725 = 665147) (by norm_num)
theorem B1331365 : Blo 1182408 1331365 := bbase (se 4 (by rfl) ⟨124815, by rfl⟩ : syracuseStep 1331365 = 249631) (by norm_num)
theorem B1773749 : Blo 1182408 1773749 := bbase (se 5 (by rfl) ⟨83144, by rfl⟩ : syracuseStep 1773749 = 166289) (by norm_num)
theorem B5689541 : Blo 1182408 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B1331401 : Blo 1182408 1331401 := bbase (se 2 (by rfl) ⟨499275, by rfl⟩ : syracuseStep 1331401 = 998551) (by norm_num)
theorem B1773773 : Blo 1182408 1773773 := bbase (se 3 (by rfl) ⟨332582, by rfl⟩ : syracuseStep 1773773 = 665165) (by norm_num)
theorem B7794901 : Blo 1182408 7794901 := bbase (se 7 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 7794901 = 182693) (by norm_num)
theorem B1200349 : Blo 1182408 1200349 := bbase (se 3 (by rfl) ⟨225065, by rfl⟩ : syracuseStep 1200349 = 450131) (by norm_num)
theorem B1773797 : Blo 1182408 1773797 := bbase (se 4 (by rfl) ⟨166293, by rfl⟩ : syracuseStep 1773797 = 332587) (by norm_num)
theorem B1331437 : Blo 1182408 1331437 := bbase (se 3 (by rfl) ⟨249644, by rfl⟩ : syracuseStep 1331437 = 499289) (by norm_num)
theorem B1773821 : Blo 1182408 1773821 := bbase (se 3 (by rfl) ⟨332591, by rfl⟩ : syracuseStep 1773821 = 665183) (by norm_num)
theorem B3035389 : Blo 1182408 3035389 := bbase (se 3 (by rfl) ⟨569135, by rfl⟩ : syracuseStep 3035389 = 1138271) (by norm_num)
theorem B1331473 : Blo 1182408 1331473 := bbase (se 2 (by rfl) ⟨499302, by rfl⟩ : syracuseStep 1331473 = 998605) (by norm_num)
theorem B1773845 : Blo 1182408 1773845 := bbase (se 6 (by rfl) ⟨41574, by rfl⟩ : syracuseStep 1773845 = 83149) (by norm_num)
theorem B3993893 : Blo 1182408 3993893 := bbase (se 4 (by rfl) ⟨374427, by rfl⟩ : syracuseStep 3993893 = 748855) (by norm_num)
theorem B1683757 : Blo 1182408 1683757 := bbase (se 3 (by rfl) ⟨315704, by rfl⟩ : syracuseStep 1683757 = 631409) (by norm_num)
theorem B1773869 : Blo 1182408 1773869 := bbase (se 3 (by rfl) ⟨332600, by rfl⟩ : syracuseStep 1773869 = 665201) (by norm_num)
theorem B1421617 : Blo 1182408 1421617 := bbase (se 2 (by rfl) ⟨533106, by rfl⟩ : syracuseStep 1421617 = 1066213) (by norm_num)
theorem B1331509 : Blo 1182408 1331509 := bbase (se 5 (by rfl) ⟨62414, by rfl⟩ : syracuseStep 1331509 = 124829) (by norm_num)
theorem B1773893 : Blo 1182408 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B2994509 : Blo 1182408 2994509 := bbase (se 3 (by rfl) ⟨561470, by rfl⟩ : syracuseStep 2994509 = 1122941) (by norm_num)
theorem B2773333 : Blo 1182408 2773333 := bbase (se 10 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 2773333 = 8125) (by norm_num)
theorem B1331545 : Blo 1182408 1331545 := bbase (se 2 (by rfl) ⟨499329, by rfl⟩ : syracuseStep 1331545 = 998659) (by norm_num)
theorem B1773917 : Blo 1182408 1773917 := bbase (se 3 (by rfl) ⟨332609, by rfl⟩ : syracuseStep 1773917 = 665219) (by norm_num)
theorem B1773941 : Blo 1182408 1773941 := bbase (se 5 (by rfl) ⟨83153, by rfl⟩ : syracuseStep 1773941 = 166307) (by norm_num)
theorem B1331581 : Blo 1182408 1331581 := bbase (se 3 (by rfl) ⟨249671, by rfl⟩ : syracuseStep 1331581 = 499343) (by norm_num)
theorem B1773965 : Blo 1182408 1773965 := bbase (se 3 (by rfl) ⟨332618, by rfl⟩ : syracuseStep 1773965 = 665237) (by norm_num)
theorem B1331617 : Blo 1182408 1331617 := bbase (se 2 (by rfl) ⟨499356, by rfl⟩ : syracuseStep 1331617 = 998713) (by norm_num)
theorem B1773989 : Blo 1182408 1773989 := bbase (se 4 (by rfl) ⟨166311, by rfl⟩ : syracuseStep 1773989 = 332623) (by norm_num)
theorem B5394853 : Blo 1182408 5394853 := bbase (se 4 (by rfl) ⟨505767, by rfl⟩ : syracuseStep 5394853 = 1011535) (by norm_num)
theorem B1774013 : Blo 1182408 1774013 := bbase (se 3 (by rfl) ⟨332627, by rfl⟩ : syracuseStep 1774013 = 665255) (by norm_num)
theorem B1421761 : Blo 1182408 1421761 := bbase (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) (by norm_num)
theorem B1331653 : Blo 1182408 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B1774037 : Blo 1182408 1774037 := bbase (se 7 (by rfl) ⟨20789, by rfl⟩ : syracuseStep 1774037 = 41579) (by norm_num)
theorem B1331689 : Blo 1182408 1331689 := bbase (se 2 (by rfl) ⟨499383, by rfl⟩ : syracuseStep 1331689 = 998767) (by norm_num)
theorem B1774061 : Blo 1182408 1774061 := bbase (se 3 (by rfl) ⟨332636, by rfl⟩ : syracuseStep 1774061 = 665273) (by norm_num)
theorem B1774085 : Blo 1182408 1774085 := bbase (se 4 (by rfl) ⟨166320, by rfl⟩ : syracuseStep 1774085 = 332641) (by norm_num)
theorem B1798669 : Blo 1182408 1798669 := bbase (se 3 (by rfl) ⟨337250, by rfl⟩ : syracuseStep 1798669 = 674501) (by norm_num)
theorem B1331725 : Blo 1182408 1331725 := bbase (se 3 (by rfl) ⟨249698, by rfl⟩ : syracuseStep 1331725 = 499397) (by norm_num)
theorem B1774109 : Blo 1182408 1774109 := bbase (se 3 (by rfl) ⟨332645, by rfl⟩ : syracuseStep 1774109 = 665291) (by norm_num)
theorem B3371557 : Blo 1182408 3371557 := bbase (se 4 (by rfl) ⟨316083, by rfl⟩ : syracuseStep 3371557 = 632167) (by norm_num)
theorem B1331761 : Blo 1182408 1331761 := bbase (se 2 (by rfl) ⟨499410, by rfl⟩ : syracuseStep 1331761 = 998821) (by norm_num)
theorem B1774133 : Blo 1182408 1774133 := bbase (se 5 (by rfl) ⟨83162, by rfl⟩ : syracuseStep 1774133 = 166325) (by norm_num)
theorem B7582261 : Blo 1182408 7582261 := bbase (se 5 (by rfl) ⟨355418, by rfl⟩ : syracuseStep 7582261 = 710837) (by norm_num)
theorem B3600949 : Blo 1182408 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B1774157 : Blo 1182408 1774157 := bbase (se 3 (by rfl) ⟨332654, by rfl⟩ : syracuseStep 1774157 = 665309) (by norm_num)
theorem B17052245 : Blo 1182408 17052245 := bbase (se 8 (by rfl) ⟨99915, by rfl⟩ : syracuseStep 17052245 = 199831) (by norm_num)
theorem B1331797 : Blo 1182408 1331797 := bbase (se 8 (by rfl) ⟨7803, by rfl⟩ : syracuseStep 1331797 = 15607) (by norm_num)
theorem B1774181 : Blo 1182408 1774181 := bbase (se 4 (by rfl) ⟨166329, by rfl⟩ : syracuseStep 1774181 = 332659) (by norm_num)
theorem B1331833 : Blo 1182408 1331833 := bbase (se 2 (by rfl) ⟨499437, by rfl⟩ : syracuseStep 1331833 = 998875) (by norm_num)
theorem B1684093 : Blo 1182408 1684093 := bbase (se 3 (by rfl) ⟨315767, by rfl⟩ : syracuseStep 1684093 = 631535) (by norm_num)
theorem B1774205 : Blo 1182408 1774205 := bbase (se 3 (by rfl) ⟨332663, by rfl⟩ : syracuseStep 1774205 = 665327) (by norm_num)
theorem B1774229 : Blo 1182408 1774229 := bbase (se 6 (by rfl) ⟨41583, by rfl⟩ : syracuseStep 1774229 = 83167) (by norm_num)
theorem B1995421 : Blo 1182408 1995421 := bbase (se 3 (by rfl) ⟨374141, by rfl⟩ : syracuseStep 1995421 = 748283) (by norm_num)
theorem B1331869 : Blo 1182408 1331869 := bbase (se 3 (by rfl) ⟨249725, by rfl⟩ : syracuseStep 1331869 = 499451) (by norm_num)
theorem B2994853 : Blo 1182408 2994853 := bbase (se 4 (by rfl) ⟨280767, by rfl⟩ : syracuseStep 2994853 = 561535) (by norm_num)
theorem B1774253 : Blo 1182408 1774253 := bbase (se 3 (by rfl) ⟨332672, by rfl⟩ : syracuseStep 1774253 = 665345) (by norm_num)
theorem B1331905 : Blo 1182408 1331905 := bbase (se 2 (by rfl) ⟨499464, by rfl⟩ : syracuseStep 1331905 = 998929) (by norm_num)
theorem B1774277 : Blo 1182408 1774277 := bbase (se 4 (by rfl) ⟨166338, by rfl⟩ : syracuseStep 1774277 = 332677) (by norm_num)
theorem B3994325 : Blo 1182408 3994325 := bbase (se 7 (by rfl) ⟨46808, by rfl⟩ : syracuseStep 3994325 = 93617) (by norm_num)
theorem B1774301 : Blo 1182408 1774301 := bbase (se 3 (by rfl) ⟨332681, by rfl⟩ : syracuseStep 1774301 = 665363) (by norm_num)
theorem B5993189 : Blo 1182408 5993189 := bbase (se 4 (by rfl) ⟨561861, by rfl⟩ : syracuseStep 5993189 = 1123723) (by norm_num)
theorem B1331941 : Blo 1182408 1331941 := bbase (se 4 (by rfl) ⟨124869, by rfl⟩ : syracuseStep 1331941 = 249739) (by norm_num)
theorem B1995509 : Blo 1182408 1995509 := bbase (se 5 (by rfl) ⟨93539, by rfl⟩ : syracuseStep 1995509 = 187079) (by norm_num)
theorem B1774325 : Blo 1182408 1774325 := bbase (se 5 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 1774325 = 166343) (by norm_num)
theorem B10113781 : Blo 1182408 10113781 := bbase (se 5 (by rfl) ⟨474083, by rfl⟩ : syracuseStep 10113781 = 948167) (by norm_num)
theorem B1331977 : Blo 1182408 1331977 := bbase (se 2 (by rfl) ⟨499491, by rfl⟩ : syracuseStep 1331977 = 998983) (by norm_num)
theorem B1774349 : Blo 1182408 1774349 := bbase (se 3 (by rfl) ⟨332690, by rfl⟩ : syracuseStep 1774349 = 665381) (by norm_num)
theorem B2994965 : Blo 1182408 2994965 := bbase (se 6 (by rfl) ⟨70194, by rfl⟩ : syracuseStep 2994965 = 140389) (by norm_num)
theorem B1774373 : Blo 1182408 1774373 := bbase (se 4 (by rfl) ⟨166347, by rfl⟩ : syracuseStep 1774373 = 332695) (by norm_num)
theorem B1332013 : Blo 1182408 1332013 := bbase (se 3 (by rfl) ⟨249752, by rfl⟩ : syracuseStep 1332013 = 499505) (by norm_num)
theorem B1774397 : Blo 1182408 1774397 := bbase (se 3 (by rfl) ⟨332699, by rfl⟩ : syracuseStep 1774397 = 665399) (by norm_num)
theorem B4494149 : Blo 1182408 4494149 := bbase (se 4 (by rfl) ⟨421326, by rfl⟩ : syracuseStep 4494149 = 842653) (by norm_num)
theorem B1332049 : Blo 1182408 1332049 := bbase (se 2 (by rfl) ⟨499518, by rfl⟩ : syracuseStep 1332049 = 999037) (by norm_num)
theorem B1684309 : Blo 1182408 1684309 := bbase (se 9 (by rfl) ⟨4934, by rfl⟩ : syracuseStep 1684309 = 9869) (by norm_num)
theorem B1774421 : Blo 1182408 1774421 := bbase (se 9 (by rfl) ⟨5198, by rfl⟩ : syracuseStep 1774421 = 10397) (by norm_num)
theorem B3036005 : Blo 1182408 3036005 := bbase (se 4 (by rfl) ⟨284625, by rfl⟩ : syracuseStep 3036005 = 569251) (by norm_num)
theorem B1774445 : Blo 1182408 1774445 := bbase (se 3 (by rfl) ⟨332708, by rfl⟩ : syracuseStep 1774445 = 665417) (by norm_num)
theorem B1995637 : Blo 1182408 1995637 := bbase (se 5 (by rfl) ⟨93545, by rfl⟩ : syracuseStep 1995637 = 187091) (by norm_num)
theorem B1332085 : Blo 1182408 1332085 := bbase (se 5 (by rfl) ⟨62441, by rfl⟩ : syracuseStep 1332085 = 124883) (by norm_num)
theorem B1774469 : Blo 1182408 1774469 := bbase (se 4 (by rfl) ⟨166356, by rfl⟩ : syracuseStep 1774469 = 332713) (by norm_num)
theorem B3240853 : Blo 1182408 3240853 := bbase (se 6 (by rfl) ⟨75957, by rfl⟩ : syracuseStep 3240853 = 151915) (by norm_num)
theorem B1332121 : Blo 1182408 1332121 := bbase (se 2 (by rfl) ⟨499545, by rfl⟩ : syracuseStep 1332121 = 999091) (by norm_num)
theorem B1774493 : Blo 1182408 1774493 := bbase (se 3 (by rfl) ⟨332717, by rfl⟩ : syracuseStep 1774493 = 665435) (by norm_num)
theorem B2528165 : Blo 1182408 2528165 := bbase (se 4 (by rfl) ⟨237015, by rfl⟩ : syracuseStep 2528165 = 474031) (by norm_num)
theorem B1774517 : Blo 1182408 1774517 := bbase (se 5 (by rfl) ⟨83180, by rfl⟩ : syracuseStep 1774517 = 166361) (by norm_num)
theorem B1332157 : Blo 1182408 1332157 := bbase (se 3 (by rfl) ⟨249779, by rfl⟩ : syracuseStep 1332157 = 499559) (by norm_num)
theorem B1995725 : Blo 1182408 1995725 := bbase (se 3 (by rfl) ⟨374198, by rfl⟩ : syracuseStep 1995725 = 748397) (by norm_num)
theorem B1774541 : Blo 1182408 1774541 := bbase (se 3 (by rfl) ⟨332726, by rfl⟩ : syracuseStep 1774541 = 665453) (by norm_num)
theorem B2995157 : Blo 1182408 2995157 := bbase (se 7 (by rfl) ⟨35099, by rfl⟩ : syracuseStep 2995157 = 70199) (by norm_num)
theorem B1332193 : Blo 1182408 1332193 := bbase (se 2 (by rfl) ⟨499572, by rfl⟩ : syracuseStep 1332193 = 999145) (by norm_num)
theorem B1774565 : Blo 1182408 1774565 := bbase (se 4 (by rfl) ⟨166365, by rfl⟩ : syracuseStep 1774565 = 332731) (by norm_num)
theorem B1774589 : Blo 1182408 1774589 := bbase (se 3 (by rfl) ⟨332735, by rfl⟩ : syracuseStep 1774589 = 665471) (by norm_num)
theorem B1332229 : Blo 1182408 1332229 := bbase (se 4 (by rfl) ⟨124896, by rfl⟩ : syracuseStep 1332229 = 249793) (by norm_num)
theorem B1774613 : Blo 1182408 1774613 := bbase (se 6 (by rfl) ⟨41592, by rfl⟩ : syracuseStep 1774613 = 83185) (by norm_num)
theorem B1332265 : Blo 1182408 1332265 := bbase (se 2 (by rfl) ⟨499599, by rfl⟩ : syracuseStep 1332265 = 999199) (by norm_num)
theorem B1774637 : Blo 1182408 1774637 := bbase (se 3 (by rfl) ⟨332744, by rfl⟩ : syracuseStep 1774637 = 665489) (by norm_num)
theorem B2528309 : Blo 1182408 2528309 := bbase (se 5 (by rfl) ⟨118514, by rfl⟩ : syracuseStep 2528309 = 237029) (by norm_num)
theorem B1774661 : Blo 1182408 1774661 := bbase (se 4 (by rfl) ⟨166374, by rfl⟩ : syracuseStep 1774661 = 332749) (by norm_num)
theorem B1995853 : Blo 1182408 1995853 := bbase (se 3 (by rfl) ⟨374222, by rfl⟩ : syracuseStep 1995853 = 748445) (by norm_num)
theorem B1332301 : Blo 1182408 1332301 := bbase (se 3 (by rfl) ⟨249806, by rfl⟩ : syracuseStep 1332301 = 499613) (by norm_num)
theorem B1774685 : Blo 1182408 1774685 := bbase (se 3 (by rfl) ⟨332753, by rfl⟩ : syracuseStep 1774685 = 665507) (by norm_num)
theorem B1709149 : Blo 1182408 1709149 := bbase (se 3 (by rfl) ⟨320465, by rfl⟩ : syracuseStep 1709149 = 640931) (by norm_num)
theorem B4494437 : Blo 1182408 4494437 := bbase (se 4 (by rfl) ⟨421353, by rfl⟩ : syracuseStep 4494437 = 842707) (by norm_num)
theorem B1332337 : Blo 1182408 1332337 := bbase (se 2 (by rfl) ⟨499626, by rfl⟩ : syracuseStep 1332337 = 999253) (by norm_num)
theorem B1774709 : Blo 1182408 1774709 := bbase (se 5 (by rfl) ⟨83189, by rfl⟩ : syracuseStep 1774709 = 166379) (by norm_num)
theorem B3994757 : Blo 1182408 3994757 := bbase (se 4 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 3994757 = 749017) (by norm_num)
theorem B1774733 : Blo 1182408 1774733 := bbase (se 3 (by rfl) ⟨332762, by rfl⟩ : syracuseStep 1774733 = 665525) (by norm_num)
theorem B1332373 : Blo 1182408 1332373 := bbase (se 6 (by rfl) ⟨31227, by rfl⟩ : syracuseStep 1332373 = 62455) (by norm_num)
theorem B1995941 : Blo 1182408 1995941 := bbase (se 4 (by rfl) ⟨187119, by rfl⟩ : syracuseStep 1995941 = 374239) (by norm_num)
theorem B1774757 : Blo 1182408 1774757 := bbase (se 4 (by rfl) ⟨166383, by rfl⟩ : syracuseStep 1774757 = 332767) (by norm_num)
theorem B1332409 : Blo 1182408 1332409 := bbase (se 2 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 1332409 = 999307) (by norm_num)
theorem B1774781 : Blo 1182408 1774781 := bbase (se 3 (by rfl) ⟨332771, by rfl⟩ : syracuseStep 1774781 = 665543) (by norm_num)
theorem B1684685 : Blo 1182408 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B1774805 : Blo 1182408 1774805 := bbase (se 7 (by rfl) ⟨20798, by rfl⟩ : syracuseStep 1774805 = 41597) (by norm_num)
theorem B1332445 : Blo 1182408 1332445 := bbase (se 3 (by rfl) ⟨249833, by rfl⟩ : syracuseStep 1332445 = 499667) (by norm_num)
theorem B1774829 : Blo 1182408 1774829 := bbase (se 3 (by rfl) ⟨332780, by rfl⟩ : syracuseStep 1774829 = 665561) (by norm_num)
theorem B1774853 : Blo 1182408 1774853 := bbase (se 4 (by rfl) ⟨166392, by rfl⟩ : syracuseStep 1774853 = 332785) (by norm_num)
theorem B5395733 : Blo 1182408 5395733 := bbase (se 6 (by rfl) ⟨126462, by rfl⟩ : syracuseStep 5395733 = 252925) (by norm_num)
theorem B1774877 : Blo 1182408 1774877 := bbase (se 3 (by rfl) ⟨332789, by rfl⟩ : syracuseStep 1774877 = 665579) (by norm_num)
theorem B1996069 : Blo 1182408 1996069 := bbase (se 4 (by rfl) ⟨187131, by rfl⟩ : syracuseStep 1996069 = 374263) (by norm_num)
theorem B2995501 : Blo 1182408 2995501 := bbase (se 3 (by rfl) ⟨561656, by rfl⟩ : syracuseStep 2995501 = 1123313) (by norm_num)
theorem B1774901 : Blo 1182408 1774901 := bbase (se 5 (by rfl) ⟨83198, by rfl⟩ : syracuseStep 1774901 = 166397) (by norm_num)
theorem B1774925 : Blo 1182408 1774925 := bbase (se 3 (by rfl) ⟨332798, by rfl⟩ : syracuseStep 1774925 = 665597) (by norm_num)
theorem B1774949 : Blo 1182408 1774949 := bbase (se 4 (by rfl) ⟨166401, by rfl⟩ : syracuseStep 1774949 = 332803) (by norm_num)
theorem B1996157 : Blo 1182408 1996157 := bbase (se 3 (by rfl) ⟨374279, by rfl⟩ : syracuseStep 1996157 = 748559) (by norm_num)
theorem B1774973 : Blo 1182408 1774973 := bbase (se 3 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 1774973 = 665615) (by norm_num)
theorem B1774997 : Blo 1182408 1774997 := bbase (se 6 (by rfl) ⟨41601, by rfl⟩ : syracuseStep 1774997 = 83203) (by norm_num)
theorem B2995613 : Blo 1182408 2995613 := bbase (se 3 (by rfl) ⟨561677, by rfl⟩ : syracuseStep 2995613 = 1123355) (by norm_num)
theorem B1775021 : Blo 1182408 1775021 := bbase (se 3 (by rfl) ⟨332816, by rfl⟩ : syracuseStep 1775021 = 665633) (by norm_num)
theorem B1775045 : Blo 1182408 1775045 := bbase (se 4 (by rfl) ⟨166410, by rfl⟩ : syracuseStep 1775045 = 332821) (by norm_num)
theorem B1775069 : Blo 1182408 1775069 := bbase (se 3 (by rfl) ⟨332825, by rfl⟩ : syracuseStep 1775069 = 665651) (by norm_num)
theorem B1775093 : Blo 1182408 1775093 := bbase (se 5 (by rfl) ⟨83207, by rfl⟩ : syracuseStep 1775093 = 166415) (by norm_num)
theorem B1996285 : Blo 1182408 1996285 := bbase (se 3 (by rfl) ⟨374303, by rfl⟩ : syracuseStep 1996285 = 748607) (by norm_num)
theorem B1775117 : Blo 1182408 1775117 := bbase (se 3 (by rfl) ⟨332834, by rfl⟩ : syracuseStep 1775117 = 665669) (by norm_num)
theorem B1775141 : Blo 1182408 1775141 := bbase (se 4 (by rfl) ⟨166419, by rfl⟩ : syracuseStep 1775141 = 332839) (by norm_num)
theorem B3995189 : Blo 1182408 3995189 := bbase (se 5 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 3995189 = 374549) (by norm_num)
theorem B1775165 : Blo 1182408 1775165 := bbase (se 3 (by rfl) ⟨332843, by rfl⟩ : syracuseStep 1775165 = 665687) (by norm_num)
theorem B1496657 : Blo 1182408 1496657 := bbase (se 2 (by rfl) ⟨561246, by rfl⟩ : syracuseStep 1496657 = 1122493) (by norm_num)
theorem B1996373 : Blo 1182408 1996373 := bbase (se 8 (by rfl) ⟨11697, by rfl⟩ : syracuseStep 1996373 = 23395) (by norm_num)
theorem B1775189 : Blo 1182408 1775189 := bbase (se 8 (by rfl) ⟨10401, by rfl⟩ : syracuseStep 1775189 = 20803) (by norm_num)
theorem B2995805 : Blo 1182408 2995805 := bbase (se 3 (by rfl) ⟨561713, by rfl⟩ : syracuseStep 2995805 = 1123427) (by norm_num)
theorem B1775213 : Blo 1182408 1775213 := bbase (se 3 (by rfl) ⟨332852, by rfl⟩ : syracuseStep 1775213 = 665705) (by norm_num)
theorem B1775237 : Blo 1182408 1775237 := bbase (se 4 (by rfl) ⟨166428, by rfl⟩ : syracuseStep 1775237 = 332857) (by norm_num)
theorem B1496713 : Blo 1182408 1496713 := bbase (se 2 (by rfl) ⟨561267, by rfl⟩ : syracuseStep 1496713 = 1122535) (by norm_num)
theorem B1775261 : Blo 1182408 1775261 := bbase (se 3 (by rfl) ⟨332861, by rfl⟩ : syracuseStep 1775261 = 665723) (by norm_num)
theorem B1775285 : Blo 1182408 1775285 := bbase (se 5 (by rfl) ⟨83216, by rfl⟩ : syracuseStep 1775285 = 166433) (by norm_num)
theorem B8099509 : Blo 1182408 8099509 := bbase (se 5 (by rfl) ⟨379664, by rfl⟩ : syracuseStep 8099509 = 759329) (by norm_num)
theorem B1775309 : Blo 1182408 1775309 := bbase (se 3 (by rfl) ⟨332870, by rfl⟩ : syracuseStep 1775309 = 665741) (by norm_num)
theorem B1996501 : Blo 1182408 1996501 := bbase (se 7 (by rfl) ⟨23396, by rfl⟩ : syracuseStep 1996501 = 46793) (by norm_num)
theorem B1775333 : Blo 1182408 1775333 := bbase (se 4 (by rfl) ⟨166437, by rfl⟩ : syracuseStep 1775333 = 332875) (by norm_num)
theorem B1496809 : Blo 1182408 1496809 := bbase (se 2 (by rfl) ⟨561303, by rfl⟩ : syracuseStep 1496809 = 1122607) (by norm_num)
theorem B2397941 : Blo 1182408 2397941 := bbase (se 5 (by rfl) ⟨112403, by rfl⟩ : syracuseStep 2397941 = 224807) (by norm_num)
theorem B1775357 : Blo 1182408 1775357 := bbase (se 3 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 1775357 = 665759) (by norm_num)
theorem B1775381 : Blo 1182408 1775381 := bbase (se 6 (by rfl) ⟨41610, by rfl⟩ : syracuseStep 1775381 = 83221) (by norm_num)
theorem B2529053 : Blo 1182408 2529053 := bbase (se 3 (by rfl) ⟨474197, by rfl⟩ : syracuseStep 2529053 = 948395) (by norm_num)
theorem B1996589 : Blo 1182408 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B1775405 : Blo 1182408 1775405 := bbase (se 3 (by rfl) ⟨332888, by rfl⟩ : syracuseStep 1775405 = 665777) (by norm_num)
theorem B1775429 : Blo 1182408 1775429 := bbase (se 4 (by rfl) ⟨166446, by rfl⟩ : syracuseStep 1775429 = 332893) (by norm_num)
theorem B2398037 : Blo 1182408 2398037 := bbase (se 9 (by rfl) ⟨7025, by rfl⟩ : syracuseStep 2398037 = 14051) (by norm_num)
theorem B1775453 : Blo 1182408 1775453 := bbase (se 3 (by rfl) ⟨332897, by rfl⟩ : syracuseStep 1775453 = 665795) (by norm_num)
theorem B3790709 : Blo 1182408 3790709 := bbase (se 5 (by rfl) ⟨177689, by rfl⟩ : syracuseStep 3790709 = 355379) (by norm_num)
theorem B1775477 : Blo 1182408 1775477 := bbase (se 5 (by rfl) ⟨83225, by rfl⟩ : syracuseStep 1775477 = 166451) (by norm_num)
theorem B1775501 : Blo 1182408 1775501 := bbase (se 3 (by rfl) ⟨332906, by rfl⟩ : syracuseStep 1775501 = 665813) (by norm_num)
theorem B1496981 : Blo 1182408 1496981 := bbase (se 6 (by rfl) ⟨35085, by rfl⟩ : syracuseStep 1496981 = 70171) (by norm_num)
theorem B1800085 : Blo 1182408 1800085 := bbase (se 6 (by rfl) ⟨42189, by rfl⟩ : syracuseStep 1800085 = 84379) (by norm_num)
theorem B1775525 : Blo 1182408 1775525 := bbase (se 4 (by rfl) ⟨166455, by rfl⟩ : syracuseStep 1775525 = 332911) (by norm_num)
theorem B1996717 : Blo 1182408 1996717 := bbase (se 3 (by rfl) ⟨374384, by rfl⟩ : syracuseStep 1996717 = 748769) (by norm_num)
theorem B2996149 : Blo 1182408 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B1775549 : Blo 1182408 1775549 := bbase (se 3 (by rfl) ⟨332915, by rfl⟩ : syracuseStep 1775549 = 665831) (by norm_num)
theorem B1497037 : Blo 1182408 1497037 := bbase (se 3 (by rfl) ⟨280694, by rfl⟩ : syracuseStep 1497037 = 561389) (by norm_num)
theorem B1775573 : Blo 1182408 1775573 := bbase (se 7 (by rfl) ⟨20807, by rfl⟩ : syracuseStep 1775573 = 41615) (by norm_num)
theorem B3995621 : Blo 1182408 3995621 := bbase (se 4 (by rfl) ⟨374589, by rfl⟩ : syracuseStep 3995621 = 749179) (by norm_num)
theorem B1775597 : Blo 1182408 1775597 := bbase (se 3 (by rfl) ⟨332924, by rfl⟩ : syracuseStep 1775597 = 665849) (by norm_num)
theorem B5994485 : Blo 1182408 5994485 := bbase (se 5 (by rfl) ⟨280991, by rfl⟩ : syracuseStep 5994485 = 561983) (by norm_num)
theorem B1996805 : Blo 1182408 1996805 := bbase (se 4 (by rfl) ⟨187200, by rfl⟩ : syracuseStep 1996805 = 374401) (by norm_num)
theorem B1775621 : Blo 1182408 1775621 := bbase (se 4 (by rfl) ⟨166464, by rfl⟩ : syracuseStep 1775621 = 332929) (by norm_num)
theorem B1775645 : Blo 1182408 1775645 := bbase (se 3 (by rfl) ⟨332933, by rfl⟩ : syracuseStep 1775645 = 665867) (by norm_num)
theorem B2996261 : Blo 1182408 2996261 := bbase (se 4 (by rfl) ⟨280899, by rfl⟩ : syracuseStep 2996261 = 561799) (by norm_num)
theorem B1497133 : Blo 1182408 1497133 := bbase (se 3 (by rfl) ⟨280712, by rfl⟩ : syracuseStep 1497133 = 561425) (by norm_num)
theorem B1775669 : Blo 1182408 1775669 := bbase (se 5 (by rfl) ⟨83234, by rfl⟩ : syracuseStep 1775669 = 166469) (by norm_num)
theorem B1775693 : Blo 1182408 1775693 := bbase (se 3 (by rfl) ⟨332942, by rfl⟩ : syracuseStep 1775693 = 665885) (by norm_num)
theorem B2660453 : Blo 1182408 2660453 := bbase (se 4 (by rfl) ⟨249417, by rfl⟩ : syracuseStep 2660453 = 498835) (by norm_num)
theorem B1775717 : Blo 1182408 1775717 := bbase (se 4 (by rfl) ⟨166473, by rfl⟩ : syracuseStep 1775717 = 332947) (by norm_num)
theorem B2562173 : Blo 1182408 2562173 := bbase (se 3 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 2562173 = 960815) (by norm_num)
theorem B1775741 : Blo 1182408 1775741 := bbase (se 3 (by rfl) ⟨332951, by rfl⟩ : syracuseStep 1775741 = 665903) (by norm_num)
theorem B1996933 : Blo 1182408 1996933 := bbase (se 4 (by rfl) ⟨187212, by rfl⟩ : syracuseStep 1996933 = 374425) (by norm_num)
theorem B1620109 : Blo 1182408 1620109 := bbase (se 3 (by rfl) ⟨303770, by rfl⟩ : syracuseStep 1620109 = 607541) (by norm_num)
theorem B1775765 : Blo 1182408 1775765 := bbase (se 6 (by rfl) ⟨41619, by rfl⟩ : syracuseStep 1775765 = 83239) (by norm_num)
theorem B2660525 : Blo 1182408 2660525 := bbase (se 3 (by rfl) ⟨498848, by rfl⟩ : syracuseStep 2660525 = 997697) (by norm_num)
theorem B1775789 : Blo 1182408 1775789 := bbase (se 3 (by rfl) ⟨332960, by rfl⟩ : syracuseStep 1775789 = 665921) (by norm_num)
theorem B1775813 : Blo 1182408 1775813 := bbase (se 4 (by rfl) ⟨166482, by rfl⟩ : syracuseStep 1775813 = 332965) (by norm_num)
theorem B1497305 : Blo 1182408 1497305 := bbase (se 2 (by rfl) ⟨561489, by rfl⟩ : syracuseStep 1497305 = 1122979) (by norm_num)
theorem B1997021 : Blo 1182408 1997021 := bbase (se 3 (by rfl) ⟨374441, by rfl⟩ : syracuseStep 1997021 = 748883) (by norm_num)
theorem B1775837 : Blo 1182408 1775837 := bbase (se 3 (by rfl) ⟨332969, by rfl⟩ : syracuseStep 1775837 = 665939) (by norm_num)
theorem B2996453 : Blo 1182408 2996453 := bbase (se 4 (by rfl) ⟨280917, by rfl⟩ : syracuseStep 2996453 = 561835) (by norm_num)
theorem B3037421 : Blo 1182408 3037421 := bbase (se 3 (by rfl) ⟨569516, by rfl⟩ : syracuseStep 3037421 = 1139033) (by norm_num)
theorem B2660597 : Blo 1182408 2660597 := bbase (se 5 (by rfl) ⟨124715, by rfl⟩ : syracuseStep 2660597 = 249431) (by norm_num)
theorem B1775861 : Blo 1182408 1775861 := bbase (se 5 (by rfl) ⟨83243, by rfl⟩ : syracuseStep 1775861 = 166487) (by norm_num)
theorem B1349881 : Blo 1182408 1349881 := bbase (se 2 (by rfl) ⟨506205, by rfl⟩ : syracuseStep 1349881 = 1012411) (by norm_num)
theorem B4495621 : Blo 1182408 4495621 := bbase (se 4 (by rfl) ⟨421464, by rfl⟩ : syracuseStep 4495621 = 842929) (by norm_num)
theorem B1775885 : Blo 1182408 1775885 := bbase (se 3 (by rfl) ⟨332978, by rfl⟩ : syracuseStep 1775885 = 665957) (by norm_num)
theorem B1497361 : Blo 1182408 1497361 := bbase (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) (by norm_num)
theorem B1775909 : Blo 1182408 1775909 := bbase (se 4 (by rfl) ⟨166491, by rfl⟩ : syracuseStep 1775909 = 332983) (by norm_num)
theorem B2660669 : Blo 1182408 2660669 := bbase (se 3 (by rfl) ⟨498875, by rfl⟩ : syracuseStep 2660669 = 997751) (by norm_num)
theorem B1775933 : Blo 1182408 1775933 := bbase (se 3 (by rfl) ⟨332987, by rfl⟩ : syracuseStep 1775933 = 665975) (by norm_num)
theorem B1775957 : Blo 1182408 1775957 := bbase (se 10 (by rfl) ⟨2601, by rfl⟩ : syracuseStep 1775957 = 5203) (by norm_num)
theorem B1997149 : Blo 1182408 1997149 := bbase (se 3 (by rfl) ⟨374465, by rfl⟩ : syracuseStep 1997149 = 748931) (by norm_num)
theorem B1775981 : Blo 1182408 1775981 := bbase (se 3 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 1775981 = 665993) (by norm_num)
theorem B1497457 : Blo 1182408 1497457 := bbase (se 2 (by rfl) ⟨561546, by rfl⟩ : syracuseStep 1497457 = 1123093) (by norm_num)
theorem B2660741 : Blo 1182408 2660741 := bbase (se 4 (by rfl) ⟨249444, by rfl⟩ : syracuseStep 2660741 = 498889) (by norm_num)
theorem B1776005 : Blo 1182408 1776005 := bbase (se 4 (by rfl) ⟨166500, by rfl⟩ : syracuseStep 1776005 = 333001) (by norm_num)
theorem B2161037 : Blo 1182408 2161037 := bbase (se 3 (by rfl) ⟨405194, by rfl⟩ : syracuseStep 2161037 = 810389) (by norm_num)
theorem B5986709 : Blo 1182408 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B3996053 : Blo 1182408 3996053 := bbase (se 6 (by rfl) ⟨93657, by rfl⟩ : syracuseStep 3996053 = 187315) (by norm_num)
theorem B2398621 : Blo 1182408 2398621 := bbase (se 3 (by rfl) ⟨449741, by rfl⟩ : syracuseStep 2398621 = 899483) (by norm_num)
theorem B1776029 : Blo 1182408 1776029 := bbase (se 3 (by rfl) ⟨333005, by rfl⟩ : syracuseStep 1776029 = 666011) (by norm_num)
theorem B5683621 : Blo 1182408 5683621 := bbase (se 4 (by rfl) ⟨532839, by rfl⟩ : syracuseStep 5683621 = 1065679) (by norm_num)
theorem B1997237 : Blo 1182408 1997237 := bbase (se 5 (by rfl) ⟨93620, by rfl⟩ : syracuseStep 1997237 = 187241) (by norm_num)
theorem B1776053 : Blo 1182408 1776053 := bbase (se 5 (by rfl) ⟨83252, by rfl⟩ : syracuseStep 1776053 = 166505) (by norm_num)
theorem B2660813 : Blo 1182408 2660813 := bbase (se 3 (by rfl) ⟨498902, by rfl⟩ : syracuseStep 2660813 = 997805) (by norm_num)
theorem B1776077 : Blo 1182408 1776077 := bbase (se 3 (by rfl) ⟨333014, by rfl⟩ : syracuseStep 1776077 = 666029) (by norm_num)
theorem B1776101 : Blo 1182408 1776101 := bbase (se 4 (by rfl) ⟨166509, by rfl⟩ : syracuseStep 1776101 = 333019) (by norm_num)
theorem B1776125 : Blo 1182408 1776125 := bbase (se 3 (by rfl) ⟨333023, by rfl⟩ : syracuseStep 1776125 = 666047) (by norm_num)
theorem B2660885 : Blo 1182408 2660885 := bbase (se 6 (by rfl) ⟨62364, by rfl⟩ : syracuseStep 2660885 = 124729) (by norm_num)
theorem B4798997 : Blo 1182408 4798997 := bbase (se 6 (by rfl) ⟨112476, by rfl⟩ : syracuseStep 4798997 = 224953) (by norm_num)
theorem B1776149 : Blo 1182408 1776149 := bbase (se 6 (by rfl) ⟨41628, by rfl⟩ : syracuseStep 1776149 = 83257) (by norm_num)
theorem B1497629 : Blo 1182408 1497629 := bbase (se 3 (by rfl) ⟨280805, by rfl⟩ : syracuseStep 1497629 = 561611) (by norm_num)
theorem B1776173 : Blo 1182408 1776173 := bbase (se 3 (by rfl) ⟨333032, by rfl⟩ : syracuseStep 1776173 = 666065) (by norm_num)
theorem B1997365 : Blo 1182408 1997365 := bbase (se 5 (by rfl) ⟨93626, by rfl⟩ : syracuseStep 1997365 = 187253) (by norm_num)
theorem B4495925 : Blo 1182408 4495925 := bbase (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) (by norm_num)
theorem B2996797 : Blo 1182408 2996797 := bbase (se 3 (by rfl) ⟨561899, by rfl⟩ : syracuseStep 2996797 = 1123799) (by norm_num)
theorem B1776197 : Blo 1182408 1776197 := bbase (se 4 (by rfl) ⟨166518, by rfl⟩ : syracuseStep 1776197 = 333037) (by norm_num)
theorem B1497685 : Blo 1182408 1497685 := bbase (se 8 (by rfl) ⟨8775, by rfl⟩ : syracuseStep 1497685 = 17551) (by norm_num)
theorem B2660957 : Blo 1182408 2660957 := bbase (se 3 (by rfl) ⟨498929, by rfl⟩ : syracuseStep 2660957 = 997859) (by norm_num)
theorem B1776221 : Blo 1182408 1776221 := bbase (se 3 (by rfl) ⟨333041, by rfl⟩ : syracuseStep 1776221 = 666083) (by norm_num)
theorem B1686109 : Blo 1182408 1686109 := bbase (se 3 (by rfl) ⟨316145, by rfl⟩ : syracuseStep 1686109 = 632291) (by norm_num)
theorem B1776245 : Blo 1182408 1776245 := bbase (se 5 (by rfl) ⟨83261, by rfl⟩ : syracuseStep 1776245 = 166523) (by norm_num)
theorem B2161285 : Blo 1182408 2161285 := bbase (se 4 (by rfl) ⟨202620, by rfl⟩ : syracuseStep 2161285 = 405241) (by norm_num)
theorem B1997453 : Blo 1182408 1997453 := bbase (se 3 (by rfl) ⟨374522, by rfl⟩ : syracuseStep 1997453 = 749045) (by norm_num)
theorem B1776269 : Blo 1182408 1776269 := bbase (se 3 (by rfl) ⟨333050, by rfl⟩ : syracuseStep 1776269 = 666101) (by norm_num)
theorem B7576213 : Blo 1182408 7576213 := bbase (se 6 (by rfl) ⟨177567, by rfl⟩ : syracuseStep 7576213 = 355135) (by norm_num)
theorem B8993429 : Blo 1182408 8993429 := bbase (se 6 (by rfl) ⟨210783, by rfl⟩ : syracuseStep 8993429 = 421567) (by norm_num)
theorem B2661029 : Blo 1182408 2661029 := bbase (se 4 (by rfl) ⟨249471, by rfl⟩ : syracuseStep 2661029 = 498943) (by norm_num)
theorem B1776293 : Blo 1182408 1776293 := bbase (se 4 (by rfl) ⟨166527, by rfl⟩ : syracuseStep 1776293 = 333055) (by norm_num)
theorem B2996909 : Blo 1182408 2996909 := bbase (se 3 (by rfl) ⟨561920, by rfl⟩ : syracuseStep 2996909 = 1123841) (by norm_num)
theorem B1497781 : Blo 1182408 1497781 := bbase (se 5 (by rfl) ⟨70208, by rfl⟩ : syracuseStep 1497781 = 140417) (by norm_num)
theorem B10115765 : Blo 1182408 10115765 := bbase (se 5 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 10115765 = 948353) (by norm_num)
theorem B1776317 : Blo 1182408 1776317 := bbase (se 3 (by rfl) ⟨333059, by rfl⟩ : syracuseStep 1776317 = 666119) (by norm_num)
theorem B2841293 : Blo 1182408 2841293 := bbase (se 3 (by rfl) ⟨532742, by rfl⟩ : syracuseStep 2841293 = 1065485) (by norm_num)
theorem B4799189 : Blo 1182408 4799189 := bbase (se 7 (by rfl) ⟨56240, by rfl⟩ : syracuseStep 4799189 = 112481) (by norm_num)
theorem B1776341 : Blo 1182408 1776341 := bbase (se 7 (by rfl) ⟨20816, by rfl⟩ : syracuseStep 1776341 = 41633) (by norm_num)
theorem B2661101 : Blo 1182408 2661101 := bbase (se 3 (by rfl) ⟨498956, by rfl⟩ : syracuseStep 2661101 = 997913) (by norm_num)
theorem B1776365 : Blo 1182408 1776365 := bbase (se 3 (by rfl) ⟨333068, by rfl⟩ : syracuseStep 1776365 = 666137) (by norm_num)
theorem B1776389 : Blo 1182408 1776389 := bbase (se 4 (by rfl) ⟨166536, by rfl⟩ : syracuseStep 1776389 = 333073) (by norm_num)
theorem B1997581 : Blo 1182408 1997581 := bbase (se 3 (by rfl) ⟨374546, by rfl⟩ : syracuseStep 1997581 = 749093) (by norm_num)
theorem B1776413 : Blo 1182408 1776413 := bbase (se 3 (by rfl) ⟨333077, by rfl⟩ : syracuseStep 1776413 = 666155) (by norm_num)
theorem B1440545 : Blo 1182408 1440545 := bbase (se 2 (by rfl) ⟨540204, by rfl⟩ : syracuseStep 1440545 = 1080409) (by norm_num)
theorem B2841389 : Blo 1182408 2841389 := bbase (se 3 (by rfl) ⟨532760, by rfl⟩ : syracuseStep 2841389 = 1065521) (by norm_num)
theorem B2661173 : Blo 1182408 2661173 := bbase (se 5 (by rfl) ⟨124742, by rfl⟩ : syracuseStep 2661173 = 249485) (by norm_num)
theorem B1776437 : Blo 1182408 1776437 := bbase (se 5 (by rfl) ⟨83270, by rfl⟩ : syracuseStep 1776437 = 166541) (by norm_num)
theorem B3996485 : Blo 1182408 3996485 := bbase (se 4 (by rfl) ⟨374670, by rfl⟩ : syracuseStep 3996485 = 749341) (by norm_num)
theorem B1776461 : Blo 1182408 1776461 := bbase (se 3 (by rfl) ⟨333086, by rfl⟩ : syracuseStep 1776461 = 666173) (by norm_num)
theorem B1497953 : Blo 1182408 1497953 := bbase (se 2 (by rfl) ⟨561732, by rfl⟩ : syracuseStep 1497953 = 1123465) (by norm_num)
theorem B1997669 : Blo 1182408 1997669 := bbase (se 4 (by rfl) ⟨187281, by rfl⟩ : syracuseStep 1997669 = 374563) (by norm_num)
theorem B1776485 : Blo 1182408 1776485 := bbase (se 4 (by rfl) ⟨166545, by rfl⟩ : syracuseStep 1776485 = 333091) (by norm_num)
theorem B2997101 : Blo 1182408 2997101 := bbase (se 3 (by rfl) ⟨561956, by rfl⟩ : syracuseStep 2997101 = 1123913) (by norm_num)
theorem B2661245 : Blo 1182408 2661245 := bbase (se 3 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 2661245 = 997967) (by norm_num)
theorem B3038077 : Blo 1182408 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B1776509 : Blo 1182408 1776509 := bbase (se 3 (by rfl) ⟨333095, by rfl⟩ : syracuseStep 1776509 = 666191) (by norm_num)
theorem B1776533 : Blo 1182408 1776533 := bbase (se 6 (by rfl) ⟨41637, by rfl⟩ : syracuseStep 1776533 = 83275) (by norm_num)
theorem B1498009 : Blo 1182408 1498009 := bbase (se 2 (by rfl) ⟨561753, by rfl⟩ : syracuseStep 1498009 = 1123507) (by norm_num)
theorem B2399141 : Blo 1182408 2399141 := bbase (se 4 (by rfl) ⟨224919, by rfl⟩ : syracuseStep 2399141 = 449839) (by norm_num)
theorem B1776557 : Blo 1182408 1776557 := bbase (se 3 (by rfl) ⟨333104, by rfl⟩ : syracuseStep 1776557 = 666209) (by norm_num)
theorem B2661317 : Blo 1182408 2661317 := bbase (se 4 (by rfl) ⟨249498, by rfl⟩ : syracuseStep 2661317 = 498997) (by norm_num)
theorem B1776581 : Blo 1182408 1776581 := bbase (se 4 (by rfl) ⟨166554, by rfl⟩ : syracuseStep 1776581 = 333109) (by norm_num)
theorem B1776605 : Blo 1182408 1776605 := bbase (se 3 (by rfl) ⟨333113, by rfl⟩ : syracuseStep 1776605 = 666227) (by norm_num)
theorem B1997797 : Blo 1182408 1997797 := bbase (se 4 (by rfl) ⟨187293, by rfl⟩ : syracuseStep 1997797 = 374587) (by norm_num)
theorem B1498105 : Blo 1182408 1498105 := bbase (se 2 (by rfl) ⟨561789, by rfl⟩ : syracuseStep 1498105 = 1123579) (by norm_num)
theorem B2661389 : Blo 1182408 2661389 := bbase (se 3 (by rfl) ⟨499010, by rfl⟩ : syracuseStep 2661389 = 998021) (by norm_num)
theorem B8985653 : Blo 1182408 8985653 := bbase (se 5 (by rfl) ⟨421202, by rfl⟩ : syracuseStep 8985653 = 842405) (by norm_num)
theorem B1997885 : Blo 1182408 1997885 := bbase (se 3 (by rfl) ⟨374603, by rfl⟩ : syracuseStep 1997885 = 749207) (by norm_num)
theorem B2661461 : Blo 1182408 2661461 := bbase (se 8 (by rfl) ⟨15594, by rfl⟩ : syracuseStep 2661461 = 31189) (by norm_num)
theorem B1440877 : Blo 1182408 1440877 := bbase (se 3 (by rfl) ⟨270164, by rfl⟩ : syracuseStep 1440877 = 540329) (by norm_num)
theorem B12795029 : Blo 1182408 12795029 := bbase (se 6 (by rfl) ⟨299883, by rfl⟩ : syracuseStep 12795029 = 599767) (by norm_num)
theorem B2661533 : Blo 1182408 2661533 := bbase (se 3 (by rfl) ⟨499037, by rfl⟩ : syracuseStep 2661533 = 998075) (by norm_num)
theorem B1498277 : Blo 1182408 1498277 := bbase (se 4 (by rfl) ⟨140463, by rfl⟩ : syracuseStep 1498277 = 280927) (by norm_num)
theorem B3792053 : Blo 1182408 3792053 := bbase (se 5 (by rfl) ⟨177752, by rfl⟩ : syracuseStep 3792053 = 355505) (by norm_num)
theorem B1998013 : Blo 1182408 1998013 := bbase (se 3 (by rfl) ⟨374627, by rfl⟩ : syracuseStep 1998013 = 749255) (by norm_num)
theorem B2997445 : Blo 1182408 2997445 := bbase (se 4 (by rfl) ⟨281010, by rfl⟩ : syracuseStep 2997445 = 562021) (by norm_num)
theorem B1498333 : Blo 1182408 1498333 := bbase (se 3 (by rfl) ⟨280937, by rfl⟩ : syracuseStep 1498333 = 561875) (by norm_num)
theorem B2661605 : Blo 1182408 2661605 := bbase (se 4 (by rfl) ⟨249525, by rfl⟩ : syracuseStep 2661605 = 499051) (by norm_num)
theorem B3996917 : Blo 1182408 3996917 := bbase (se 5 (by rfl) ⟨187355, by rfl⟩ : syracuseStep 3996917 = 374711) (by norm_num)
theorem B5995781 : Blo 1182408 5995781 := bbase (se 4 (by rfl) ⟨562104, by rfl⟩ : syracuseStep 5995781 = 1124209) (by norm_num)
theorem B1998101 : Blo 1182408 1998101 := bbase (se 6 (by rfl) ⟨46830, by rfl⟩ : syracuseStep 1998101 = 93661) (by norm_num)
theorem B2661677 : Blo 1182408 2661677 := bbase (se 3 (by rfl) ⟨499064, by rfl⟩ : syracuseStep 2661677 = 998129) (by norm_num)
theorem B2997557 : Blo 1182408 2997557 := bbase (se 5 (by rfl) ⟨140510, by rfl⟩ : syracuseStep 2997557 = 281021) (by norm_num)
theorem B1498429 : Blo 1182408 1498429 := bbase (se 3 (by rfl) ⟨280955, by rfl⟩ : syracuseStep 1498429 = 561911) (by norm_num)
theorem B7585109 : Blo 1182408 7585109 := bbase (se 11 (by rfl) ⟨5555, by rfl⟩ : syracuseStep 7585109 = 11111) (by norm_num)
theorem B2661749 : Blo 1182408 2661749 := bbase (se 5 (by rfl) ⟨124769, by rfl⟩ : syracuseStep 2661749 = 249539) (by norm_num)
theorem B1998229 : Blo 1182408 1998229 := bbase (se 6 (by rfl) ⟨46833, by rfl⟩ : syracuseStep 1998229 = 93667) (by norm_num)
theorem B2661821 : Blo 1182408 2661821 := bbase (se 3 (by rfl) ⟨499091, by rfl⟩ : syracuseStep 2661821 = 998183) (by norm_num)
theorem B1498601 : Blo 1182408 1498601 := bbase (se 2 (by rfl) ⟨561975, by rfl⟩ : syracuseStep 1498601 = 1123951) (by norm_num)
theorem B1998317 : Blo 1182408 1998317 := bbase (se 3 (by rfl) ⟨374684, by rfl⟩ : syracuseStep 1998317 = 749369) (by norm_num)
theorem B2997749 : Blo 1182408 2997749 := bbase (se 5 (by rfl) ⟨140519, by rfl⟩ : syracuseStep 2997749 = 281039) (by norm_num)
theorem B2661893 : Blo 1182408 2661893 := bbase (se 4 (by rfl) ⟨249552, by rfl⟩ : syracuseStep 2661893 = 499105) (by norm_num)
theorem B1498657 : Blo 1182408 1498657 := bbase (se 2 (by rfl) ⟨561996, by rfl⟩ : syracuseStep 1498657 = 1123993) (by norm_num)
theorem B6159925 : Blo 1182408 6159925 := bbase (se 5 (by rfl) ⟨288746, by rfl⟩ : syracuseStep 6159925 = 577493) (by norm_num)
theorem B5054021 : Blo 1182408 5054021 := bbase (se 4 (by rfl) ⟨473814, by rfl⟩ : syracuseStep 5054021 = 947629) (by norm_num)
theorem B2661965 : Blo 1182408 2661965 := bbase (se 3 (by rfl) ⟨499118, by rfl⟩ : syracuseStep 2661965 = 998237) (by norm_num)
theorem B1998445 : Blo 1182408 1998445 := bbase (se 3 (by rfl) ⟨374708, by rfl⟩ : syracuseStep 1998445 = 749417) (by norm_num)
theorem B1498753 : Blo 1182408 1498753 := bbase (se 2 (by rfl) ⟨562032, by rfl⟩ : syracuseStep 1498753 = 1124065) (by norm_num)
theorem B2662037 : Blo 1182408 2662037 := bbase (se 6 (by rfl) ⟨62391, by rfl⟩ : syracuseStep 2662037 = 124783) (by norm_num)
theorem B5988005 : Blo 1182408 5988005 := bbase (se 4 (by rfl) ⟨561375, by rfl⟩ : syracuseStep 5988005 = 1122751) (by norm_num)
theorem B3997349 : Blo 1182408 3997349 := bbase (se 4 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 3997349 = 749503) (by norm_num)
theorem B1998533 : Blo 1182408 1998533 := bbase (se 4 (by rfl) ⟨187362, by rfl⟩ : syracuseStep 1998533 = 374725) (by norm_num)
theorem B2662109 : Blo 1182408 2662109 := bbase (se 3 (by rfl) ⟨499145, by rfl⟩ : syracuseStep 2662109 = 998291) (by norm_num)
theorem B2662181 : Blo 1182408 2662181 := bbase (se 4 (by rfl) ⟨249579, by rfl⟩ : syracuseStep 2662181 = 499159) (by norm_num)
theorem B1498925 : Blo 1182408 1498925 := bbase (se 3 (by rfl) ⟨281048, by rfl⟩ : syracuseStep 1498925 = 562097) (by norm_num)
theorem B1998661 : Blo 1182408 1998661 := bbase (se 4 (by rfl) ⟨187374, by rfl⟩ : syracuseStep 1998661 = 374749) (by norm_num)
theorem B10944341 : Blo 1182408 10944341 := bbase (se 9 (by rfl) ⟨32063, by rfl⟩ : syracuseStep 10944341 = 64127) (by norm_num)
theorem B5128037 : Blo 1182408 5128037 := bbase (se 4 (by rfl) ⟨480753, by rfl⟩ : syracuseStep 5128037 = 961507) (by norm_num)
theorem B1498981 : Blo 1182408 1498981 := bbase (se 4 (by rfl) ⟨140529, by rfl⟩ : syracuseStep 1498981 = 281059) (by norm_num)
theorem B2662253 : Blo 1182408 2662253 := bbase (se 3 (by rfl) ⟨499172, by rfl⟩ : syracuseStep 2662253 = 998345) (by norm_num)
theorem B2662325 : Blo 1182408 2662325 := bbase (se 5 (by rfl) ⟨124796, by rfl⟩ : syracuseStep 2662325 = 249593) (by norm_num)
theorem B2662397 : Blo 1182408 2662397 := bbase (se 3 (by rfl) ⟨499199, by rfl⟩ : syracuseStep 2662397 = 998399) (by norm_num)
theorem B9592901 : Blo 1182408 9592901 := bstep (se 4 (by rfl) ⟨899334, by rfl⟩ : syracuseStep 9592901 = 1798669) B1798669
theorem B3792977 : Blo 1182408 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B2662577 : Blo 1182408 2662577 := bstep (se 2 (by rfl) ⟨998466, by rfl⟩ : syracuseStep 2662577 = 1996933) B1996933
theorem B2662595 : Blo 1182408 2662595 := bstep (se 1 (by rfl) ⟨1996946, by rfl⟩ : syracuseStep 2662595 = 3993893) B3993893
theorem B2023633 : Blo 1182408 2023633 := bstep (se 2 (by rfl) ⟨758862, by rfl⟩ : syracuseStep 2023633 = 1517725) B1517725
theorem B3793169 : Blo 1182408 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B4047185 : Blo 1182408 4047185 := bstep (se 2 (by rfl) ⟨1517694, by rfl⟩ : syracuseStep 4047185 = 3035389) B3035389
theorem B6742385 : Blo 1182408 6742385 := bstep (se 2 (by rfl) ⟨2528394, by rfl⟩ : syracuseStep 6742385 = 5056789) B5056789
theorem B2245009 : Blo 1182408 2245009 := bstep (se 2 (by rfl) ⟨841878, by rfl⟩ : syracuseStep 2245009 = 1683757) B1683757
theorem B13476293 : Blo 1182408 13476293 := bstep (se 4 (by rfl) ⟨1263402, by rfl⟩ : syracuseStep 13476293 = 2526805) B2526805
theorem B2662865 : Blo 1182408 2662865 := bstep (se 2 (by rfl) ⟨998574, by rfl⟩ : syracuseStep 2662865 = 1997149) B1997149
theorem B2662883 : Blo 1182408 2662883 := bstep (se 1 (by rfl) ⟨1997162, by rfl⟩ : syracuseStep 2662883 = 3994325) B3994325
theorem B15172109 : Blo 1182408 15172109 := bstep (se 3 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 15172109 = 5689541) B5689541
theorem B7578161 : Blo 1182408 7578161 := bstep (se 2 (by rfl) ⟨2841810, by rfl⟩ : syracuseStep 7578161 = 5683621) B5683621
theorem B2024003 : Blo 1182408 2024003 := bstep (se 1 (by rfl) ⟨1518002, by rfl⟩ : syracuseStep 2024003 = 3036005) B3036005
theorem B5988977 : Blo 1182408 5988977 := bstep (se 2 (by rfl) ⟨2245866, by rfl⟩ : syracuseStep 5988977 = 4491733) B4491733
theorem B10109681 : Blo 1182408 10109681 := bstep (se 2 (by rfl) ⟨3791130, by rfl⟩ : syracuseStep 10109681 = 7582261) B7582261
theorem B2663153 : Blo 1182408 2663153 := bstep (se 2 (by rfl) ⟨998682, by rfl⟩ : syracuseStep 2663153 = 1997365) B1997365
theorem B4801265 : Blo 1182408 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B2663171 : Blo 1182408 2663171 := bstep (se 1 (by rfl) ⟨1997378, by rfl⟩ : syracuseStep 2663171 = 3994757) B3994757
theorem B2245411 : Blo 1182408 2245411 := bstep (se 1 (by rfl) ⟨1684058, by rfl⟩ : syracuseStep 2245411 = 3368117) B3368117
theorem B2245457 : Blo 1182408 2245457 := bstep (se 2 (by rfl) ⟨842046, by rfl⟩ : syracuseStep 2245457 = 1684093) B1684093
theorem B3597155 : Blo 1182408 3597155 := bstep (se 1 (by rfl) ⟨2697866, by rfl⟩ : syracuseStep 3597155 = 5395733) B5395733
theorem B10101617 : Blo 1182408 10101617 := bstep (se 2 (by rfl) ⟨3788106, by rfl⟩ : syracuseStep 10101617 = 7576213) B7576213
theorem B2130833 : Blo 1182408 2130833 := bstep (se 2 (by rfl) ⟨799062, by rfl⟩ : syracuseStep 2130833 = 1598125) B1598125
theorem B3367889 : Blo 1182408 3367889 := bstep (se 2 (by rfl) ⟨1262958, by rfl⟩ : syracuseStep 3367889 = 2525917) B2525917
theorem B13485041 : Blo 1182408 13485041 := bstep (se 2 (by rfl) ⟨5056890, by rfl⟩ : syracuseStep 13485041 = 10113781) B10113781
theorem B2663441 : Blo 1182408 2663441 := bstep (se 2 (by rfl) ⟨998790, by rfl⟩ : syracuseStep 2663441 = 1997581) B1997581
theorem B4490275 : Blo 1182408 4490275 := bstep (se 1 (by rfl) ⟨3367706, by rfl⟩ : syracuseStep 4490275 = 6735413) B6735413
theorem B2663459 : Blo 1182408 2663459 := bstep (se 1 (by rfl) ⟨1997594, by rfl⟩ : syracuseStep 2663459 = 3995189) B3995189
theorem B2245745 : Blo 1182408 2245745 := bstep (se 2 (by rfl) ⟨842154, by rfl⟩ : syracuseStep 2245745 = 1684309) B1684309
theorem B1598627 : Blo 1182408 1598627 := bstep (se 1 (by rfl) ⟨1198970, by rfl⟩ : syracuseStep 1598627 = 2397941) B2397941
theorem B6489379 : Blo 1182408 6489379 := bstep (se 1 (by rfl) ⟨4867034, by rfl⟩ : syracuseStep 6489379 = 9734069) B9734069
theorem B2663729 : Blo 1182408 2663729 := bstep (se 2 (by rfl) ⟨998898, by rfl⟩ : syracuseStep 2663729 = 1997797) B1997797
theorem B1262899 : Blo 1182408 1262899 := bstep (se 1 (by rfl) ⟨947174, by rfl⟩ : syracuseStep 1262899 = 1894349) B1894349
theorem B27329845 : Blo 1182408 27329845 := bstep (se 5 (by rfl) ⟨1281086, by rfl⟩ : syracuseStep 27329845 = 2562173) B2562173
theorem B2663747 : Blo 1182408 2663747 := bstep (se 1 (by rfl) ⟨1997810, by rfl⟩ : syracuseStep 2663747 = 3995621) B3995621
theorem B3196259 : Blo 1182408 3196259 := bstep (se 1 (by rfl) ⟨2397194, by rfl⟩ : syracuseStep 3196259 = 4794389) B4794389
theorem B5768653 : Blo 1182408 5768653 := bstep (se 3 (by rfl) ⟨1081622, by rfl⟩ : syracuseStep 5768653 = 2163245) B2163245
theorem B2278865 : Blo 1182408 2278865 := bstep (se 2 (by rfl) ⟨854574, by rfl⟩ : syracuseStep 2278865 = 1709149) B1709149
theorem B2024947 : Blo 1182408 2024947 := bstep (se 1 (by rfl) ⟨1518710, by rfl⟩ : syracuseStep 2024947 = 3037421) B3037421
theorem B3991085 : Blo 1182408 3991085 := bstep (se 3 (by rfl) ⟨748328, by rfl⟩ : syracuseStep 3991085 = 1496657) B1496657
theorem B2664017 : Blo 1182408 2664017 := bstep (se 2 (by rfl) ⟨999006, by rfl⟩ : syracuseStep 2664017 = 1998013) B1998013
theorem B3991139 : Blo 1182408 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B2664035 : Blo 1182408 2664035 := bstep (se 1 (by rfl) ⟨1998026, by rfl⟩ : syracuseStep 2664035 = 3996053) B3996053
theorem B6743843 : Blo 1182408 6743843 := bstep (se 1 (by rfl) ⟨5057882, by rfl⟩ : syracuseStep 6743843 = 10115765) B10115765
theorem B1894195 : Blo 1182408 1894195 := bstep (se 1 (by rfl) ⟨1420646, by rfl⟩ : syracuseStep 1894195 = 2841293) B2841293
theorem B2246467 : Blo 1182408 2246467 := bstep (se 1 (by rfl) ⟨1684850, by rfl⟩ : syracuseStep 2246467 = 3369701) B3369701
theorem B3991409 : Blo 1182408 3991409 := bstep (se 2 (by rfl) ⟨1496778, by rfl⟩ : syracuseStep 3991409 = 2993557) B2993557
theorem B2664305 : Blo 1182408 2664305 := bstep (se 2 (by rfl) ⟨999114, by rfl⟩ : syracuseStep 2664305 = 1998229) B1998229
theorem B1894259 : Blo 1182408 1894259 := bstep (se 1 (by rfl) ⟨1420694, by rfl⟩ : syracuseStep 1894259 = 2841389) B2841389
theorem B2664323 : Blo 1182408 2664323 := bstep (se 1 (by rfl) ⟨1998242, by rfl⟩ : syracuseStep 2664323 = 3996485) B3996485
theorem B12797837 : Blo 1182408 12797837 := bstep (se 3 (by rfl) ⟨2399594, by rfl⟩ : syracuseStep 12797837 = 4799189) B4799189
theorem B1599427 : Blo 1182408 1599427 := bstep (se 1 (by rfl) ⟨1199570, by rfl⟩ : syracuseStep 1599427 = 2399141) B2399141
theorem B5990435 : Blo 1182408 5990435 := bstep (se 1 (by rfl) ⟨4492826, by rfl⟩ : syracuseStep 5990435 = 8985653) B8985653
theorem B32368693 : Blo 1182408 32368693 := bstep (se 5 (by rfl) ⟨1517282, by rfl⟩ : syracuseStep 32368693 = 3034565) B3034565
theorem B3197027 : Blo 1182408 3197027 := bstep (se 1 (by rfl) ⟨2397770, by rfl⟩ : syracuseStep 3197027 = 4795541) B4795541
theorem B3000419 : Blo 1182408 3000419 := bstep (se 1 (by rfl) ⟨2250314, by rfl⟩ : syracuseStep 3000419 = 4500629) B4500629
theorem B8530019 : Blo 1182408 8530019 := bstep (se 1 (by rfl) ⟨6397514, by rfl⟩ : syracuseStep 8530019 = 12795029) B12795029
theorem B2664593 : Blo 1182408 2664593 := bstep (se 2 (by rfl) ⟨999222, by rfl⟩ : syracuseStep 2664593 = 1998445) B1998445
theorem B2664611 : Blo 1182408 2664611 := bstep (se 1 (by rfl) ⟨1998458, by rfl⟩ : syracuseStep 2664611 = 3996917) B3996917
theorem B28772549 : Blo 1182408 28772549 := bstep (se 4 (by rfl) ⟨2697426, by rfl⟩ : syracuseStep 28772549 = 5394853) B5394853
theorem B5056739 : Blo 1182408 5056739 := bstep (se 1 (by rfl) ⟨3792554, by rfl⟩ : syracuseStep 5056739 = 7585109) B7585109
theorem B10799345 : Blo 1182408 10799345 := bstep (se 2 (by rfl) ⟨4049754, by rfl⟩ : syracuseStep 10799345 = 8099509) B8099509
theorem B2246915 : Blo 1182408 2246915 := bstep (se 1 (by rfl) ⟨1685186, by rfl⟩ : syracuseStep 2246915 = 3370373) B3370373
theorem B2525507 : Blo 1182408 2525507 := bstep (se 1 (by rfl) ⟨1894130, by rfl⟩ : syracuseStep 2525507 = 3788261) B3788261
theorem B2025857 : Blo 1182408 2025857 := bstep (se 2 (by rfl) ⟨759696, by rfl⟩ : syracuseStep 2025857 = 1519393) B1519393
theorem B3369347 : Blo 1182408 3369347 := bstep (se 1 (by rfl) ⟨2527010, by rfl⟩ : syracuseStep 3369347 = 5054021) B5054021
theorem B3991949 : Blo 1182408 3991949 := bstep (se 3 (by rfl) ⟨748490, by rfl⟩ : syracuseStep 3991949 = 1496981) B1496981
theorem B2664881 : Blo 1182408 2664881 := bstep (se 2 (by rfl) ⟨999330, by rfl⟩ : syracuseStep 2664881 = 1998661) B1998661
theorem B3992003 : Blo 1182408 3992003 := bstep (se 1 (by rfl) ⟨2994002, by rfl⟩ : syracuseStep 3992003 = 5988005) B5988005
theorem B2664899 : Blo 1182408 2664899 := bstep (se 1 (by rfl) ⟨1998674, by rfl⟩ : syracuseStep 2664899 = 3997349) B3997349
theorem B2247203 : Blo 1182408 2247203 := bstep (se 1 (by rfl) ⟨1685402, by rfl⟩ : syracuseStep 2247203 = 3370805) B3370805
theorem B3418691 : Blo 1182408 3418691 := bstep (se 1 (by rfl) ⟨2564018, by rfl⟩ : syracuseStep 3418691 = 5128037) B5128037
theorem B1264291 : Blo 1182408 1264291 := bstep (se 1 (by rfl) ⟨948218, by rfl⟩ : syracuseStep 1264291 = 1896437) B1896437
theorem B3992273 : Blo 1182408 3992273 := bstep (se 2 (by rfl) ⟨1497102, by rfl⟩ : syracuseStep 3992273 = 2994205) B2994205
theorem B1182419 : Blo 1182408 1182419 := bstep (se 1 (by rfl) ⟨886814, by rfl⟩ : syracuseStep 1182419 = 1773629) B1773629
theorem B1182435 : Blo 1182408 1182435 := bstep (se 1 (by rfl) ⟨886826, by rfl⟩ : syracuseStep 1182435 = 1773653) B1773653
theorem B1182451 : Blo 1182408 1182451 := bstep (se 1 (by rfl) ⟨886838, by rfl⟩ : syracuseStep 1182451 = 1773677) B1773677
theorem B1182467 : Blo 1182408 1182467 := bstep (se 1 (by rfl) ⟨886850, by rfl⟩ : syracuseStep 1182467 = 1773701) B1773701
theorem B12151565 : Blo 1182408 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B1182483 : Blo 1182408 1182483 := bstep (se 1 (by rfl) ⟨886862, by rfl⟩ : syracuseStep 1182483 = 1773725) B1773725
theorem B46107413 : Blo 1182408 46107413 := bstep (se 6 (by rfl) ⟨1080642, by rfl⟩ : syracuseStep 46107413 = 2161285) B2161285
theorem B1182499 : Blo 1182408 1182499 := bstep (se 1 (by rfl) ⟨886874, by rfl⟩ : syracuseStep 1182499 = 1773749) B1773749
theorem B1182515 : Blo 1182408 1182515 := bstep (se 1 (by rfl) ⟨886886, by rfl⟩ : syracuseStep 1182515 = 1773773) B1773773
theorem B1895233 : Blo 1182408 1895233 := bstep (se 2 (by rfl) ⟨710712, by rfl⟩ : syracuseStep 1895233 = 1421425) B1421425
theorem B1182531 : Blo 1182408 1182531 := bstep (se 1 (by rfl) ⟨886898, by rfl⟩ : syracuseStep 1182531 = 1773797) B1773797
theorem B5991245 : Blo 1182408 5991245 := bstep (se 3 (by rfl) ⟨1123358, by rfl⟩ : syracuseStep 5991245 = 2246717) B2246717
theorem B1182547 : Blo 1182408 1182547 := bstep (se 1 (by rfl) ⟨886910, by rfl⟩ : syracuseStep 1182547 = 1773821) B1773821
theorem B1182563 : Blo 1182408 1182563 := bstep (se 1 (by rfl) ⟨886922, by rfl⟩ : syracuseStep 1182563 = 1773845) B1773845
theorem B1182579 : Blo 1182408 1182579 := bstep (se 1 (by rfl) ⟨886934, by rfl⟩ : syracuseStep 1182579 = 1773869) B1773869
theorem B1182595 : Blo 1182408 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B1182611 : Blo 1182408 1182611 := bstep (se 1 (by rfl) ⟨886958, by rfl⟩ : syracuseStep 1182611 = 1773917) B1773917
theorem B1182627 : Blo 1182408 1182627 := bstep (se 1 (by rfl) ⟨886970, by rfl⟩ : syracuseStep 1182627 = 1773941) B1773941
theorem B1182643 : Blo 1182408 1182643 := bstep (se 1 (by rfl) ⟨886982, by rfl⟩ : syracuseStep 1182643 = 1773965) B1773965
theorem B1182659 : Blo 1182408 1182659 := bstep (se 1 (by rfl) ⟨886994, by rfl⟩ : syracuseStep 1182659 = 1773989) B1773989
theorem B7580621 : Blo 1182408 7580621 := bstep (se 3 (by rfl) ⟨1421366, by rfl⟩ : syracuseStep 7580621 = 2842733) B2842733
theorem B5843917 : Blo 1182408 5843917 := bstep (se 3 (by rfl) ⟨1095734, by rfl⟩ : syracuseStep 5843917 = 2191469) B2191469
theorem B1600465 : Blo 1182408 1600465 := bstep (se 2 (by rfl) ⟨600174, by rfl⟩ : syracuseStep 1600465 = 1200349) B1200349
theorem B1182675 : Blo 1182408 1182675 := bstep (se 1 (by rfl) ⟨887006, by rfl⟩ : syracuseStep 1182675 = 1774013) B1774013
theorem B1182691 : Blo 1182408 1182691 := bstep (se 1 (by rfl) ⟨887018, by rfl⟩ : syracuseStep 1182691 = 1774037) B1774037
theorem B1182707 : Blo 1182408 1182707 := bstep (se 1 (by rfl) ⟨887030, by rfl⟩ : syracuseStep 1182707 = 1774061) B1774061
theorem B1182723 : Blo 1182408 1182723 := bstep (se 1 (by rfl) ⟨887042, by rfl⟩ : syracuseStep 1182723 = 1774085) B1774085
theorem B1182739 : Blo 1182408 1182739 := bstep (se 1 (by rfl) ⟨887054, by rfl⟩ : syracuseStep 1182739 = 1774109) B1774109
theorem B1182755 : Blo 1182408 1182755 := bstep (se 1 (by rfl) ⟨887066, by rfl⟩ : syracuseStep 1182755 = 1774133) B1774133
theorem B1182771 : Blo 1182408 1182771 := bstep (se 1 (by rfl) ⟨887078, by rfl⟩ : syracuseStep 1182771 = 1774157) B1774157
theorem B1895489 : Blo 1182408 1895489 := bstep (se 2 (by rfl) ⟨710808, by rfl⟩ : syracuseStep 1895489 = 1421617) B1421617
theorem B1182787 : Blo 1182408 1182787 := bstep (se 1 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 1182787 = 1774181) B1774181
theorem B2993233 : Blo 1182408 2993233 := bstep (se 2 (by rfl) ⟨1122462, by rfl⟩ : syracuseStep 2993233 = 2244925) B2244925
theorem B1182803 : Blo 1182408 1182803 := bstep (se 1 (by rfl) ⟨887102, by rfl⟩ : syracuseStep 1182803 = 1774205) B1774205
theorem B1182819 : Blo 1182408 1182819 := bstep (se 1 (by rfl) ⟨887114, by rfl⟩ : syracuseStep 1182819 = 1774229) B1774229
theorem B3697777 : Blo 1182408 3697777 := bstep (se 2 (by rfl) ⟨1386666, by rfl⟩ : syracuseStep 3697777 = 2773333) B2773333
theorem B1182835 : Blo 1182408 1182835 := bstep (se 1 (by rfl) ⟨887126, by rfl⟩ : syracuseStep 1182835 = 1774253) B1774253
theorem B1182851 : Blo 1182408 1182851 := bstep (se 1 (by rfl) ⟨887138, by rfl⟩ : syracuseStep 1182851 = 1774277) B1774277
theorem B10112141 : Blo 1182408 10112141 := bstep (se 3 (by rfl) ⟨1896026, by rfl⟩ : syracuseStep 10112141 = 3792053) B3792053
theorem B1182867 : Blo 1182408 1182867 := bstep (se 1 (by rfl) ⟨887150, by rfl⟩ : syracuseStep 1182867 = 1774301) B1774301
theorem B1330339 : Blo 1182408 1330339 := bstep (se 1 (by rfl) ⟨997754, by rfl⟩ : syracuseStep 1330339 = 1995509) B1995509
theorem B1182883 : Blo 1182408 1182883 := bstep (se 1 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 1182883 = 1774325) B1774325
theorem B3370157 : Blo 1182408 3370157 := bstep (se 3 (by rfl) ⟨631904, by rfl⟩ : syracuseStep 3370157 = 1263809) B1263809
theorem B1182899 : Blo 1182408 1182899 := bstep (se 1 (by rfl) ⟨887174, by rfl⟩ : syracuseStep 1182899 = 1774349) B1774349
theorem B1182915 : Blo 1182408 1182915 := bstep (se 1 (by rfl) ⟨887186, by rfl⟩ : syracuseStep 1182915 = 1774373) B1774373
theorem B4492493 : Blo 1182408 4492493 := bstep (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) B1684685
theorem B3198161 : Blo 1182408 3198161 := bstep (se 2 (by rfl) ⟨1199310, by rfl⟩ : syracuseStep 3198161 = 2398621) B2398621
theorem B1182931 : Blo 1182408 1182931 := bstep (se 1 (by rfl) ⟨887198, by rfl⟩ : syracuseStep 1182931 = 1774397) B1774397
theorem B1182947 : Blo 1182408 1182947 := bstep (se 1 (by rfl) ⟨887210, by rfl⟩ : syracuseStep 1182947 = 1774421) B1774421
theorem B3992813 : Blo 1182408 3992813 := bstep (se 3 (by rfl) ⟨748652, by rfl⟩ : syracuseStep 3992813 = 1497305) B1497305
theorem B2133233 : Blo 1182408 2133233 := bstep (se 2 (by rfl) ⟨799962, by rfl⟩ : syracuseStep 2133233 = 1599925) B1599925
theorem B1182963 : Blo 1182408 1182963 := bstep (se 1 (by rfl) ⟨887222, by rfl⟩ : syracuseStep 1182963 = 1774445) B1774445
theorem B1895681 : Blo 1182408 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B1182979 : Blo 1182408 1182979 := bstep (se 1 (by rfl) ⟨887234, by rfl⟩ : syracuseStep 1182979 = 1774469) B1774469
theorem B2526481 : Blo 1182408 2526481 := bstep (se 2 (by rfl) ⟨947430, by rfl⟩ : syracuseStep 2526481 = 1894861) B1894861
theorem B1182995 : Blo 1182408 1182995 := bstep (se 1 (by rfl) ⟨887246, by rfl⟩ : syracuseStep 1182995 = 1774493) B1774493
theorem B1183011 : Blo 1182408 1183011 := bstep (se 1 (by rfl) ⟨887258, by rfl⟩ : syracuseStep 1183011 = 1774517) B1774517
theorem B3992867 : Blo 1182408 3992867 := bstep (se 1 (by rfl) ⟨2994650, by rfl⟩ : syracuseStep 3992867 = 5989301) B5989301
theorem B1330483 : Blo 1182408 1330483 := bstep (se 1 (by rfl) ⟨997862, by rfl⟩ : syracuseStep 1330483 = 1995725) B1995725
theorem B1183027 : Blo 1182408 1183027 := bstep (se 1 (by rfl) ⟨887270, by rfl⟩ : syracuseStep 1183027 = 1774541) B1774541
theorem B1183043 : Blo 1182408 1183043 := bstep (se 1 (by rfl) ⟨887282, by rfl⟩ : syracuseStep 1183043 = 1774565) B1774565
theorem B1183059 : Blo 1182408 1183059 := bstep (se 1 (by rfl) ⟨887294, by rfl⟩ : syracuseStep 1183059 = 1774589) B1774589
theorem B2993507 : Blo 1182408 2993507 := bstep (se 1 (by rfl) ⟨2245130, by rfl⟩ : syracuseStep 2993507 = 4490261) B4490261
theorem B1183075 : Blo 1182408 1183075 := bstep (se 1 (by rfl) ⟨887306, by rfl⟩ : syracuseStep 1183075 = 1774613) B1774613
theorem B3370349 : Blo 1182408 3370349 := bstep (se 3 (by rfl) ⟨631940, by rfl⟩ : syracuseStep 3370349 = 1263881) B1263881
theorem B1183091 : Blo 1182408 1183091 := bstep (se 1 (by rfl) ⟨887318, by rfl⟩ : syracuseStep 1183091 = 1774637) B1774637
theorem B1183107 : Blo 1182408 1183107 := bstep (se 1 (by rfl) ⟨887330, by rfl⟩ : syracuseStep 1183107 = 1774661) B1774661
theorem B1183123 : Blo 1182408 1183123 := bstep (se 1 (by rfl) ⟨887342, by rfl⟩ : syracuseStep 1183123 = 1774685) B1774685
theorem B1183139 : Blo 1182408 1183139 := bstep (se 1 (by rfl) ⟨887354, by rfl⟩ : syracuseStep 1183139 = 1774709) B1774709
theorem B1183155 : Blo 1182408 1183155 := bstep (se 1 (by rfl) ⟨887366, by rfl⟩ : syracuseStep 1183155 = 1774733) B1774733
theorem B1330627 : Blo 1182408 1330627 := bstep (se 1 (by rfl) ⟨997970, by rfl⟩ : syracuseStep 1330627 = 1995941) B1995941
theorem B1183171 : Blo 1182408 1183171 := bstep (se 1 (by rfl) ⟨887378, by rfl⟩ : syracuseStep 1183171 = 1774757) B1774757
theorem B2698705 : Blo 1182408 2698705 := bstep (se 2 (by rfl) ⟨1012014, by rfl⟩ : syracuseStep 2698705 = 2024029) B2024029
theorem B2248145 : Blo 1182408 2248145 := bstep (se 2 (by rfl) ⟨843054, by rfl⟩ : syracuseStep 2248145 = 1686109) B1686109
theorem B1183187 : Blo 1182408 1183187 := bstep (se 1 (by rfl) ⟨887390, by rfl⟩ : syracuseStep 1183187 = 1774781) B1774781
theorem B1183203 : Blo 1182408 1183203 := bstep (se 1 (by rfl) ⟨887402, by rfl⟩ : syracuseStep 1183203 = 1774805) B1774805
theorem B1183219 : Blo 1182408 1183219 := bstep (se 1 (by rfl) ⟨887414, by rfl⟩ : syracuseStep 1183219 = 1774829) B1774829
theorem B1183235 : Blo 1182408 1183235 := bstep (se 1 (by rfl) ⟨887426, by rfl⟩ : syracuseStep 1183235 = 1774853) B1774853
theorem B1183251 : Blo 1182408 1183251 := bstep (se 1 (by rfl) ⟨887438, by rfl⟩ : syracuseStep 1183251 = 1774877) B1774877
theorem B2993699 : Blo 1182408 2993699 := bstep (se 1 (by rfl) ⟨2245274, by rfl⟩ : syracuseStep 2993699 = 4490549) B4490549
theorem B1183267 : Blo 1182408 1183267 := bstep (se 1 (by rfl) ⟨887450, by rfl⟩ : syracuseStep 1183267 = 1774901) B1774901
theorem B3993137 : Blo 1182408 3993137 := bstep (se 2 (by rfl) ⟨1497426, by rfl⟩ : syracuseStep 3993137 = 2994853) B2994853
theorem B1183283 : Blo 1182408 1183283 := bstep (se 1 (by rfl) ⟨887462, by rfl⟩ : syracuseStep 1183283 = 1774925) B1774925
theorem B25579061 : Blo 1182408 25579061 := bstep (se 5 (by rfl) ⟨1199018, by rfl⟩ : syracuseStep 25579061 = 2398037) B2398037
theorem B1183299 : Blo 1182408 1183299 := bstep (se 1 (by rfl) ⟨887474, by rfl⟩ : syracuseStep 1183299 = 1774949) B1774949
theorem B1330771 : Blo 1182408 1330771 := bstep (se 1 (by rfl) ⟨998078, by rfl⟩ : syracuseStep 1330771 = 1996157) B1996157
theorem B1183315 : Blo 1182408 1183315 := bstep (se 1 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 1183315 = 1774973) B1774973
theorem B1183331 : Blo 1182408 1183331 := bstep (se 1 (by rfl) ⟨887498, by rfl⟩ : syracuseStep 1183331 = 1774997) B1774997
theorem B1183347 : Blo 1182408 1183347 := bstep (se 1 (by rfl) ⟨887510, by rfl⟩ : syracuseStep 1183347 = 1775021) B1775021
theorem B1183363 : Blo 1182408 1183363 := bstep (se 1 (by rfl) ⟨887522, by rfl⟩ : syracuseStep 1183363 = 1775045) B1775045
theorem B1183379 : Blo 1182408 1183379 := bstep (se 1 (by rfl) ⟨887534, by rfl⟩ : syracuseStep 1183379 = 1775069) B1775069
theorem B1183395 : Blo 1182408 1183395 := bstep (se 1 (by rfl) ⟨887546, by rfl⟩ : syracuseStep 1183395 = 1775093) B1775093
theorem B1183411 : Blo 1182408 1183411 := bstep (se 1 (by rfl) ⟨887558, by rfl⟩ : syracuseStep 1183411 = 1775117) B1775117
theorem B1183427 : Blo 1182408 1183427 := bstep (se 1 (by rfl) ⟨887570, by rfl⟩ : syracuseStep 1183427 = 1775141) B1775141
theorem B5762765 : Blo 1182408 5762765 := bstep (se 3 (by rfl) ⟨1080518, by rfl⟩ : syracuseStep 5762765 = 2161037) B2161037
theorem B1183443 : Blo 1182408 1183443 := bstep (se 1 (by rfl) ⟨887582, by rfl⟩ : syracuseStep 1183443 = 1775165) B1775165
theorem B1330915 : Blo 1182408 1330915 := bstep (se 1 (by rfl) ⟨998186, by rfl⟩ : syracuseStep 1330915 = 1996373) B1996373
theorem B1183459 : Blo 1182408 1183459 := bstep (se 1 (by rfl) ⟨887594, by rfl⟩ : syracuseStep 1183459 = 1775189) B1775189
theorem B1183475 : Blo 1182408 1183475 := bstep (se 1 (by rfl) ⟨887606, by rfl⟩ : syracuseStep 1183475 = 1775213) B1775213
theorem B1183491 : Blo 1182408 1183491 := bstep (se 1 (by rfl) ⟨887618, by rfl⟩ : syracuseStep 1183491 = 1775237) B1775237
theorem B1183507 : Blo 1182408 1183507 := bstep (se 1 (by rfl) ⟨887630, by rfl⟩ : syracuseStep 1183507 = 1775261) B1775261
theorem B1183523 : Blo 1182408 1183523 := bstep (se 1 (by rfl) ⟨887642, by rfl⟩ : syracuseStep 1183523 = 1775285) B1775285
theorem B1183539 : Blo 1182408 1183539 := bstep (se 1 (by rfl) ⟨887654, by rfl⟩ : syracuseStep 1183539 = 1775309) B1775309
theorem B1183555 : Blo 1182408 1183555 := bstep (se 1 (by rfl) ⟨887666, by rfl⟩ : syracuseStep 1183555 = 1775333) B1775333
theorem B4050769 : Blo 1182408 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B1183571 : Blo 1182408 1183571 := bstep (se 1 (by rfl) ⟨887678, by rfl⟩ : syracuseStep 1183571 = 1775357) B1775357
theorem B1183587 : Blo 1182408 1183587 := bstep (se 1 (by rfl) ⟨887690, by rfl⟩ : syracuseStep 1183587 = 1775381) B1775381
theorem B4796273 : Blo 1182408 4796273 := bstep (se 2 (by rfl) ⟨1798602, by rfl⟩ : syracuseStep 4796273 = 3597205) B3597205
theorem B1331059 : Blo 1182408 1331059 := bstep (se 1 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 1331059 = 1996589) B1996589
theorem B1183603 : Blo 1182408 1183603 := bstep (se 1 (by rfl) ⟨887702, by rfl⟩ : syracuseStep 1183603 = 1775405) B1775405
theorem B1183619 : Blo 1182408 1183619 := bstep (se 1 (by rfl) ⟨887714, by rfl⟩ : syracuseStep 1183619 = 1775429) B1775429
theorem B1183635 : Blo 1182408 1183635 := bstep (se 1 (by rfl) ⟨887726, by rfl⟩ : syracuseStep 1183635 = 1775453) B1775453
theorem B2527139 : Blo 1182408 2527139 := bstep (se 1 (by rfl) ⟨1895354, by rfl⟩ : syracuseStep 2527139 = 3790709) B3790709
theorem B1183651 : Blo 1182408 1183651 := bstep (se 1 (by rfl) ⟨887738, by rfl⟩ : syracuseStep 1183651 = 1775477) B1775477
theorem B1183667 : Blo 1182408 1183667 := bstep (se 1 (by rfl) ⟨887750, by rfl⟩ : syracuseStep 1183667 = 1775501) B1775501
theorem B1183683 : Blo 1182408 1183683 := bstep (se 1 (by rfl) ⟨887762, by rfl⟩ : syracuseStep 1183683 = 1775525) B1775525
theorem B1183699 : Blo 1182408 1183699 := bstep (se 1 (by rfl) ⟨887774, by rfl⟩ : syracuseStep 1183699 = 1775549) B1775549
theorem B1183715 : Blo 1182408 1183715 := bstep (se 1 (by rfl) ⟨887786, by rfl⟩ : syracuseStep 1183715 = 1775573) B1775573
theorem B1183731 : Blo 1182408 1183731 := bstep (se 1 (by rfl) ⟨887798, by rfl⟩ : syracuseStep 1183731 = 1775597) B1775597
theorem B1331203 : Blo 1182408 1331203 := bstep (se 1 (by rfl) ⟨998402, by rfl⟩ : syracuseStep 1331203 = 1996805) B1996805
theorem B1183747 : Blo 1182408 1183747 := bstep (se 1 (by rfl) ⟨887810, by rfl⟩ : syracuseStep 1183747 = 1775621) B1775621
theorem B1183763 : Blo 1182408 1183763 := bstep (se 1 (by rfl) ⟨887822, by rfl⟩ : syracuseStep 1183763 = 1775645) B1775645
theorem B1183779 : Blo 1182408 1183779 := bstep (se 1 (by rfl) ⟨887834, by rfl⟩ : syracuseStep 1183779 = 1775669) B1775669
theorem B1773617 : Blo 1182408 1773617 := bstep (se 2 (by rfl) ⟨665106, by rfl⟩ : syracuseStep 1773617 = 1330213) B1330213
theorem B1183795 : Blo 1182408 1183795 := bstep (se 1 (by rfl) ⟨887846, by rfl⟩ : syracuseStep 1183795 = 1775693) B1775693
theorem B1773635 : Blo 1182408 1773635 := bstep (se 1 (by rfl) ⟨1330226, by rfl⟩ : syracuseStep 1773635 = 2660453) B2660453
theorem B1183811 : Blo 1182408 1183811 := bstep (se 1 (by rfl) ⟨887858, by rfl⟩ : syracuseStep 1183811 = 1775717) B1775717
theorem B3993677 : Blo 1182408 3993677 := bstep (se 3 (by rfl) ⟨748814, by rfl⟩ : syracuseStep 3993677 = 1497629) B1497629
theorem B1183827 : Blo 1182408 1183827 := bstep (se 1 (by rfl) ⟨887870, by rfl⟩ : syracuseStep 1183827 = 1775741) B1775741
theorem B1773665 : Blo 1182408 1773665 := bstep (se 2 (by rfl) ⟨665124, by rfl⟩ : syracuseStep 1773665 = 1330249) B1330249
theorem B1183843 : Blo 1182408 1183843 := bstep (se 1 (by rfl) ⟨887882, by rfl⟩ : syracuseStep 1183843 = 1775765) B1775765
theorem B1773683 : Blo 1182408 1773683 := bstep (se 1 (by rfl) ⟨1330262, by rfl⟩ : syracuseStep 1773683 = 2660525) B2660525
theorem B1183859 : Blo 1182408 1183859 := bstep (se 1 (by rfl) ⟨887894, by rfl⟩ : syracuseStep 1183859 = 1775789) B1775789
theorem B3993731 : Blo 1182408 3993731 := bstep (se 1 (by rfl) ⟨2995298, by rfl⟩ : syracuseStep 3993731 = 5990597) B5990597
theorem B1183875 : Blo 1182408 1183875 := bstep (se 1 (by rfl) ⟨887906, by rfl⟩ : syracuseStep 1183875 = 1775813) B1775813
theorem B11382925 : Blo 1182408 11382925 := bstep (se 3 (by rfl) ⟨2134298, by rfl⟩ : syracuseStep 11382925 = 4268597) B4268597
theorem B1773713 : Blo 1182408 1773713 := bstep (se 2 (by rfl) ⟨665142, by rfl⟩ : syracuseStep 1773713 = 1330285) B1330285
theorem B1921169 : Blo 1182408 1921169 := bstep (se 2 (by rfl) ⟨720438, by rfl⟩ : syracuseStep 1921169 = 1440877) B1440877
theorem B1331347 : Blo 1182408 1331347 := bstep (se 1 (by rfl) ⟨998510, by rfl⟩ : syracuseStep 1331347 = 1997021) B1997021
theorem B1183891 : Blo 1182408 1183891 := bstep (se 1 (by rfl) ⟨887918, by rfl⟩ : syracuseStep 1183891 = 1775837) B1775837
theorem B1773731 : Blo 1182408 1773731 := bstep (se 1 (by rfl) ⟨1330298, by rfl⟩ : syracuseStep 1773731 = 2660597) B2660597
theorem B4796579 : Blo 1182408 4796579 := bstep (se 1 (by rfl) ⟨3597434, by rfl⟩ : syracuseStep 4796579 = 7194869) B7194869
theorem B1183907 : Blo 1182408 1183907 := bstep (se 1 (by rfl) ⟨887930, by rfl⟩ : syracuseStep 1183907 = 1775861) B1775861
theorem B5058737 : Blo 1182408 5058737 := bstep (se 2 (by rfl) ⟨1897026, by rfl⟩ : syracuseStep 5058737 = 3794053) B3794053
theorem B1183923 : Blo 1182408 1183923 := bstep (se 1 (by rfl) ⟨887942, by rfl⟩ : syracuseStep 1183923 = 1775885) B1775885
theorem B1773761 : Blo 1182408 1773761 := bstep (se 2 (by rfl) ⟨665160, by rfl⟩ : syracuseStep 1773761 = 1330321) B1330321
theorem B1183939 : Blo 1182408 1183939 := bstep (se 1 (by rfl) ⟨887954, by rfl⟩ : syracuseStep 1183939 = 1775909) B1775909
theorem B1773779 : Blo 1182408 1773779 := bstep (se 1 (by rfl) ⟨1330334, by rfl⟩ : syracuseStep 1773779 = 2660669) B2660669
theorem B1183955 : Blo 1182408 1183955 := bstep (se 1 (by rfl) ⟨887966, by rfl⟩ : syracuseStep 1183955 = 1775933) B1775933
theorem B1183971 : Blo 1182408 1183971 := bstep (se 1 (by rfl) ⟨887978, by rfl⟩ : syracuseStep 1183971 = 1775957) B1775957
theorem B1773809 : Blo 1182408 1773809 := bstep (se 2 (by rfl) ⟨665178, by rfl⟩ : syracuseStep 1773809 = 1330357) B1330357
theorem B1183987 : Blo 1182408 1183987 := bstep (se 1 (by rfl) ⟨887990, by rfl⟩ : syracuseStep 1183987 = 1775981) B1775981
theorem B1773827 : Blo 1182408 1773827 := bstep (se 1 (by rfl) ⟨1330370, by rfl⟩ : syracuseStep 1773827 = 2660741) B2660741
theorem B1184003 : Blo 1182408 1184003 := bstep (se 1 (by rfl) ⟨888002, by rfl⟩ : syracuseStep 1184003 = 1776005) B1776005
theorem B1184019 : Blo 1182408 1184019 := bstep (se 1 (by rfl) ⟨888014, by rfl⟩ : syracuseStep 1184019 = 1776029) B1776029
theorem B1773857 : Blo 1182408 1773857 := bstep (se 2 (by rfl) ⟨665196, by rfl⟩ : syracuseStep 1773857 = 1330393) B1330393
theorem B1331491 : Blo 1182408 1331491 := bstep (se 1 (by rfl) ⟨998618, by rfl⟩ : syracuseStep 1331491 = 1997237) B1997237
theorem B1184035 : Blo 1182408 1184035 := bstep (se 1 (by rfl) ⟨888026, by rfl⟩ : syracuseStep 1184035 = 1776053) B1776053
theorem B3199277 : Blo 1182408 3199277 := bstep (se 3 (by rfl) ⟨599864, by rfl⟩ : syracuseStep 3199277 = 1199729) B1199729
theorem B5050673 : Blo 1182408 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B1773875 : Blo 1182408 1773875 := bstep (se 1 (by rfl) ⟨1330406, by rfl⟩ : syracuseStep 1773875 = 2660813) B2660813
theorem B1184051 : Blo 1182408 1184051 := bstep (se 1 (by rfl) ⟨888038, by rfl⟩ : syracuseStep 1184051 = 1776077) B1776077
theorem B1184067 : Blo 1182408 1184067 := bstep (se 1 (by rfl) ⟨888050, by rfl⟩ : syracuseStep 1184067 = 1776101) B1776101
theorem B3371341 : Blo 1182408 3371341 := bstep (se 3 (by rfl) ⟨632126, by rfl⟩ : syracuseStep 3371341 = 1264253) B1264253
theorem B1773905 : Blo 1182408 1773905 := bstep (se 2 (by rfl) ⟨665214, by rfl⟩ : syracuseStep 1773905 = 1330429) B1330429
theorem B1184083 : Blo 1182408 1184083 := bstep (se 1 (by rfl) ⟨888062, by rfl⟩ : syracuseStep 1184083 = 1776125) B1776125
theorem B1773923 : Blo 1182408 1773923 := bstep (se 1 (by rfl) ⟨1330442, by rfl⟩ : syracuseStep 1773923 = 2660885) B2660885
theorem B3199331 : Blo 1182408 3199331 := bstep (se 1 (by rfl) ⟨2399498, by rfl⟩ : syracuseStep 3199331 = 4798997) B4798997
theorem B1184099 : Blo 1182408 1184099 := bstep (se 1 (by rfl) ⟨888074, by rfl⟩ : syracuseStep 1184099 = 1776149) B1776149
theorem B1184115 : Blo 1182408 1184115 := bstep (se 1 (by rfl) ⟨888086, by rfl⟩ : syracuseStep 1184115 = 1776173) B1776173
theorem B1773953 : Blo 1182408 1773953 := bstep (se 2 (by rfl) ⟨665232, by rfl⟩ : syracuseStep 1773953 = 1330465) B1330465
theorem B1184131 : Blo 1182408 1184131 := bstep (se 1 (by rfl) ⟨888098, by rfl⟩ : syracuseStep 1184131 = 1776197) B1776197
theorem B3994001 : Blo 1182408 3994001 := bstep (se 2 (by rfl) ⟨1497750, by rfl⟩ : syracuseStep 3994001 = 2995501) B2995501
theorem B1773971 : Blo 1182408 1773971 := bstep (se 1 (by rfl) ⟨1330478, by rfl⟩ : syracuseStep 1773971 = 2660957) B2660957
theorem B1184147 : Blo 1182408 1184147 := bstep (se 1 (by rfl) ⟨888110, by rfl⟩ : syracuseStep 1184147 = 1776221) B1776221
theorem B1184163 : Blo 1182408 1184163 := bstep (se 1 (by rfl) ⟨888122, by rfl⟩ : syracuseStep 1184163 = 1776245) B1776245
theorem B1774001 : Blo 1182408 1774001 := bstep (se 2 (by rfl) ⟨665250, by rfl⟩ : syracuseStep 1774001 = 1330501) B1330501
theorem B1331635 : Blo 1182408 1331635 := bstep (se 1 (by rfl) ⟨998726, by rfl⟩ : syracuseStep 1331635 = 1997453) B1997453
theorem B1184179 : Blo 1182408 1184179 := bstep (se 1 (by rfl) ⟨888134, by rfl⟩ : syracuseStep 1184179 = 1776269) B1776269
theorem B1774019 : Blo 1182408 1774019 := bstep (se 1 (by rfl) ⟨1330514, by rfl⟩ : syracuseStep 1774019 = 2661029) B2661029
theorem B1184195 : Blo 1182408 1184195 := bstep (se 1 (by rfl) ⟨888146, by rfl⟩ : syracuseStep 1184195 = 1776293) B1776293
theorem B2994641 : Blo 1182408 2994641 := bstep (se 2 (by rfl) ⟨1122990, by rfl⟩ : syracuseStep 2994641 = 2245981) B2245981
theorem B1184211 : Blo 1182408 1184211 := bstep (se 1 (by rfl) ⟨888158, by rfl⟩ : syracuseStep 1184211 = 1776317) B1776317
theorem B1774049 : Blo 1182408 1774049 := bstep (se 2 (by rfl) ⟨665268, by rfl⟩ : syracuseStep 1774049 = 1330537) B1330537
theorem B1184227 : Blo 1182408 1184227 := bstep (se 1 (by rfl) ⟨888170, by rfl⟩ : syracuseStep 1184227 = 1776341) B1776341
theorem B1774067 : Blo 1182408 1774067 := bstep (se 1 (by rfl) ⟨1330550, by rfl⟩ : syracuseStep 1774067 = 2661101) B2661101
theorem B1184243 : Blo 1182408 1184243 := bstep (se 1 (by rfl) ⟨888182, by rfl⟩ : syracuseStep 1184243 = 1776365) B1776365
theorem B2994691 : Blo 1182408 2994691 := bstep (se 1 (by rfl) ⟨2246018, by rfl⟩ : syracuseStep 2994691 = 4492037) B4492037
theorem B1184259 : Blo 1182408 1184259 := bstep (se 1 (by rfl) ⟨888194, by rfl⟩ : syracuseStep 1184259 = 1776389) B1776389
theorem B1683985 : Blo 1182408 1683985 := bstep (se 2 (by rfl) ⟨631494, by rfl⟩ : syracuseStep 1683985 = 1262989) B1262989
theorem B1774097 : Blo 1182408 1774097 := bstep (se 2 (by rfl) ⟨665286, by rfl⟩ : syracuseStep 1774097 = 1330573) B1330573
theorem B1184275 : Blo 1182408 1184275 := bstep (se 1 (by rfl) ⟨888206, by rfl⟩ : syracuseStep 1184275 = 1776413) B1776413
theorem B1774115 : Blo 1182408 1774115 := bstep (se 1 (by rfl) ⟨1330586, by rfl⟩ : syracuseStep 1774115 = 2661173) B2661173
theorem B1896995 : Blo 1182408 1896995 := bstep (se 1 (by rfl) ⟨1422746, by rfl⟩ : syracuseStep 1896995 = 2845493) B2845493
theorem B1184291 : Blo 1182408 1184291 := bstep (se 1 (by rfl) ⟨888218, by rfl⟩ : syracuseStep 1184291 = 1776437) B1776437
theorem B1184307 : Blo 1182408 1184307 := bstep (se 1 (by rfl) ⟨888230, by rfl⟩ : syracuseStep 1184307 = 1776461) B1776461
theorem B1774145 : Blo 1182408 1774145 := bstep (se 2 (by rfl) ⟨665304, by rfl⟩ : syracuseStep 1774145 = 1330609) B1330609
theorem B1331779 : Blo 1182408 1331779 := bstep (se 1 (by rfl) ⟨998834, by rfl⟩ : syracuseStep 1331779 = 1997669) B1997669
theorem B1184323 : Blo 1182408 1184323 := bstep (se 1 (by rfl) ⟨888242, by rfl⟩ : syracuseStep 1184323 = 1776485) B1776485
theorem B1995347 : Blo 1182408 1995347 := bstep (se 1 (by rfl) ⟨1496510, by rfl⟩ : syracuseStep 1995347 = 2993021) B2993021
theorem B1774163 : Blo 1182408 1774163 := bstep (se 1 (by rfl) ⟨1330622, by rfl⟩ : syracuseStep 1774163 = 2661245) B2661245
theorem B1184339 : Blo 1182408 1184339 := bstep (se 1 (by rfl) ⟨888254, by rfl⟩ : syracuseStep 1184339 = 1776509) B1776509
theorem B1184355 : Blo 1182408 1184355 := bstep (se 1 (by rfl) ⟨888266, by rfl⟩ : syracuseStep 1184355 = 1776533) B1776533
theorem B1684081 : Blo 1182408 1684081 := bstep (se 2 (by rfl) ⟨631530, by rfl⟩ : syracuseStep 1684081 = 1263061) B1263061
theorem B1774193 : Blo 1182408 1774193 := bstep (se 2 (by rfl) ⟨665322, by rfl⟩ : syracuseStep 1774193 = 1330645) B1330645
theorem B1184371 : Blo 1182408 1184371 := bstep (se 1 (by rfl) ⟨888278, by rfl⟩ : syracuseStep 1184371 = 1776557) B1776557
theorem B1774211 : Blo 1182408 1774211 := bstep (se 1 (by rfl) ⟨1330658, by rfl⟩ : syracuseStep 1774211 = 2661317) B2661317
theorem B1184387 : Blo 1182408 1184387 := bstep (se 1 (by rfl) ⟨888290, by rfl⟩ : syracuseStep 1184387 = 1776581) B1776581
theorem B2994833 : Blo 1182408 2994833 := bstep (se 2 (by rfl) ⟨1123062, by rfl⟩ : syracuseStep 2994833 = 2246125) B2246125
theorem B1184403 : Blo 1182408 1184403 := bstep (se 1 (by rfl) ⟨888302, by rfl⟩ : syracuseStep 1184403 = 1776605) B1776605
theorem B1774241 : Blo 1182408 1774241 := bstep (se 2 (by rfl) ⟨665340, by rfl⟩ : syracuseStep 1774241 = 1330681) B1330681
theorem B1774259 : Blo 1182408 1774259 := bstep (se 1 (by rfl) ⟨1330694, by rfl⟩ : syracuseStep 1774259 = 2661389) B2661389
theorem B12800693 : Blo 1182408 12800693 := bstep (se 5 (by rfl) ⟨600032, by rfl⟩ : syracuseStep 12800693 = 1200065) B1200065
theorem B3789517 : Blo 1182408 3789517 := bstep (se 3 (by rfl) ⟨710534, by rfl⟩ : syracuseStep 3789517 = 1421069) B1421069
theorem B1774289 : Blo 1182408 1774289 := bstep (se 2 (by rfl) ⟨665358, by rfl⟩ : syracuseStep 1774289 = 1330717) B1330717
theorem B1995475 : Blo 1182408 1995475 := bstep (se 1 (by rfl) ⟨1496606, by rfl⟩ : syracuseStep 1995475 = 2993213) B2993213
theorem B1331923 : Blo 1182408 1331923 := bstep (se 1 (by rfl) ⟨998942, by rfl⟩ : syracuseStep 1331923 = 1997885) B1997885
theorem B1774307 : Blo 1182408 1774307 := bstep (se 1 (by rfl) ⟨1330730, by rfl⟩ : syracuseStep 1774307 = 2661461) B2661461
theorem B2527985 : Blo 1182408 2527985 := bstep (se 2 (by rfl) ⟨947994, by rfl⟩ : syracuseStep 2527985 = 1895989) B1895989
theorem B8213233 : Blo 1182408 8213233 := bstep (se 2 (by rfl) ⟨3079962, by rfl⟩ : syracuseStep 8213233 = 6159925) B6159925
theorem B1774337 : Blo 1182408 1774337 := bstep (se 2 (by rfl) ⟨665376, by rfl⟩ : syracuseStep 1774337 = 1330753) B1330753
theorem B1774355 : Blo 1182408 1774355 := bstep (se 1 (by rfl) ⟨1330766, by rfl⟩ : syracuseStep 1774355 = 2661533) B2661533
theorem B1774385 : Blo 1182408 1774385 := bstep (se 2 (by rfl) ⟨665394, by rfl⟩ : syracuseStep 1774385 = 1330789) B1330789
theorem B1422131 : Blo 1182408 1422131 := bstep (se 1 (by rfl) ⟨1066598, by rfl⟩ : syracuseStep 1422131 = 2133197) B2133197
theorem B1774403 : Blo 1182408 1774403 := bstep (se 1 (by rfl) ⟨1330802, by rfl⟩ : syracuseStep 1774403 = 2661605) B2661605
theorem B1995617 : Blo 1182408 1995617 := bstep (se 2 (by rfl) ⟨748356, by rfl⟩ : syracuseStep 1995617 = 1496713) B1496713
theorem B1774433 : Blo 1182408 1774433 := bstep (se 2 (by rfl) ⟨665412, by rfl⟩ : syracuseStep 1774433 = 1330825) B1330825
theorem B1332067 : Blo 1182408 1332067 := bstep (se 1 (by rfl) ⟨999050, by rfl⟩ : syracuseStep 1332067 = 1998101) B1998101
theorem B1774451 : Blo 1182408 1774451 := bstep (se 1 (by rfl) ⟨1330838, by rfl⟩ : syracuseStep 1774451 = 2661677) B2661677
theorem B1774481 : Blo 1182408 1774481 := bstep (se 2 (by rfl) ⟨665430, by rfl⟩ : syracuseStep 1774481 = 1330861) B1330861
theorem B1774499 : Blo 1182408 1774499 := bstep (se 1 (by rfl) ⟨1330874, by rfl⟩ : syracuseStep 1774499 = 2661749) B2661749
theorem B3994541 : Blo 1182408 3994541 := bstep (se 3 (by rfl) ⟨748976, by rfl⟩ : syracuseStep 3994541 = 1497953) B1497953
theorem B1774529 : Blo 1182408 1774529 := bstep (se 2 (by rfl) ⟨665448, by rfl⟩ : syracuseStep 1774529 = 1330897) B1330897
theorem B1774547 : Blo 1182408 1774547 := bstep (se 1 (by rfl) ⟨1330910, by rfl⟩ : syracuseStep 1774547 = 2661821) B2661821
theorem B1995745 : Blo 1182408 1995745 := bstep (se 2 (by rfl) ⟨748404, by rfl⟩ : syracuseStep 1995745 = 1496809) B1496809
theorem B3994595 : Blo 1182408 3994595 := bstep (se 1 (by rfl) ⟨2995946, by rfl⟩ : syracuseStep 3994595 = 5991893) B5991893
theorem B1774577 : Blo 1182408 1774577 := bstep (se 2 (by rfl) ⟨665466, by rfl⟩ : syracuseStep 1774577 = 1330933) B1330933
theorem B1332211 : Blo 1182408 1332211 := bstep (se 1 (by rfl) ⟨999158, by rfl⟩ : syracuseStep 1332211 = 1998317) B1998317
theorem B1995779 : Blo 1182408 1995779 := bstep (se 1 (by rfl) ⟨1496834, by rfl⟩ : syracuseStep 1995779 = 2993669) B2993669
theorem B1774595 : Blo 1182408 1774595 := bstep (se 1 (by rfl) ⟨1330946, by rfl⟩ : syracuseStep 1774595 = 2661893) B2661893
theorem B1774625 : Blo 1182408 1774625 := bstep (se 2 (by rfl) ⟨665484, by rfl⟩ : syracuseStep 1774625 = 1330969) B1330969
theorem B1774643 : Blo 1182408 1774643 := bstep (se 1 (by rfl) ⟨1330982, by rfl⟩ : syracuseStep 1774643 = 2661965) B2661965
theorem B1774673 : Blo 1182408 1774673 := bstep (se 2 (by rfl) ⟨665502, by rfl⟩ : syracuseStep 1774673 = 1331005) B1331005
theorem B1684577 : Blo 1182408 1684577 := bstep (se 2 (by rfl) ⟨631716, by rfl⟩ : syracuseStep 1684577 = 1263433) B1263433
theorem B8090723 : Blo 1182408 8090723 := bstep (se 1 (by rfl) ⟨6068042, by rfl⟩ : syracuseStep 8090723 = 12136085) B12136085
theorem B1774691 : Blo 1182408 1774691 := bstep (se 1 (by rfl) ⟨1331018, by rfl⟩ : syracuseStep 1774691 = 2662037) B2662037
theorem B1774721 : Blo 1182408 1774721 := bstep (se 2 (by rfl) ⟨665520, by rfl⟩ : syracuseStep 1774721 = 1331041) B1331041
theorem B1995907 : Blo 1182408 1995907 := bstep (se 1 (by rfl) ⟨1496930, by rfl⟩ : syracuseStep 1995907 = 2993861) B2993861
theorem B1332355 : Blo 1182408 1332355 := bstep (se 1 (by rfl) ⟨999266, by rfl⟩ : syracuseStep 1332355 = 1998533) B1998533
theorem B1774739 : Blo 1182408 1774739 := bstep (se 1 (by rfl) ⟨1331054, by rfl⟩ : syracuseStep 1774739 = 2662109) B2662109
theorem B1774769 : Blo 1182408 1774769 := bstep (se 2 (by rfl) ⟨665538, by rfl⟩ : syracuseStep 1774769 = 1331077) B1331077
theorem B1774787 : Blo 1182408 1774787 := bstep (se 1 (by rfl) ⟨1331090, by rfl⟩ : syracuseStep 1774787 = 2662181) B2662181
theorem B1774817 : Blo 1182408 1774817 := bstep (se 2 (by rfl) ⟨665556, by rfl⟩ : syracuseStep 1774817 = 1331113) B1331113
theorem B7296227 : Blo 1182408 7296227 := bstep (se 1 (by rfl) ⟨5472170, by rfl⟩ : syracuseStep 7296227 = 10944341) B10944341
theorem B8991971 : Blo 1182408 8991971 := bstep (se 1 (by rfl) ⟨6743978, by rfl⟩ : syracuseStep 8991971 = 13487957) B13487957
theorem B3994865 : Blo 1182408 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B1774835 : Blo 1182408 1774835 := bstep (se 1 (by rfl) ⟨1331126, by rfl⟩ : syracuseStep 1774835 = 2662253) B2662253
theorem B1996049 : Blo 1182408 1996049 := bstep (se 2 (by rfl) ⟨748518, by rfl⟩ : syracuseStep 1996049 = 1497037) B1497037
theorem B1774865 : Blo 1182408 1774865 := bstep (se 2 (by rfl) ⟨665574, by rfl⟩ : syracuseStep 1774865 = 1331149) B1331149
theorem B1774883 : Blo 1182408 1774883 := bstep (se 1 (by rfl) ⟨1331162, by rfl⟩ : syracuseStep 1774883 = 2662325) B2662325
theorem B1774913 : Blo 1182408 1774913 := bstep (se 2 (by rfl) ⟨665592, by rfl⟩ : syracuseStep 1774913 = 1331185) B1331185
theorem B1774931 : Blo 1182408 1774931 := bstep (se 1 (by rfl) ⟨1331198, by rfl⟩ : syracuseStep 1774931 = 2662397) B2662397
theorem B5682545 : Blo 1182408 5682545 := bstep (se 2 (by rfl) ⟨2130954, by rfl⟩ : syracuseStep 5682545 = 4261909) B4261909
theorem B1774961 : Blo 1182408 1774961 := bstep (se 2 (by rfl) ⟨665610, by rfl⟩ : syracuseStep 1774961 = 1331221) B1331221
theorem B1774979 : Blo 1182408 1774979 := bstep (se 1 (by rfl) ⟨1331234, by rfl⟩ : syracuseStep 1774979 = 2662469) B2662469
theorem B1996177 : Blo 1182408 1996177 := bstep (se 2 (by rfl) ⟨748566, by rfl⟩ : syracuseStep 1996177 = 1497133) B1497133
theorem B3200401 : Blo 1182408 3200401 := bstep (se 2 (by rfl) ⟨1200150, by rfl⟩ : syracuseStep 3200401 = 2400301) B2400301
theorem B1775009 : Blo 1182408 1775009 := bstep (se 2 (by rfl) ⟨665628, by rfl⟩ : syracuseStep 1775009 = 1331257) B1331257
theorem B1996211 : Blo 1182408 1996211 := bstep (se 1 (by rfl) ⟨1497158, by rfl⟩ : syracuseStep 1996211 = 2994317) B2994317
theorem B1775027 : Blo 1182408 1775027 := bstep (se 1 (by rfl) ⟨1331270, by rfl⟩ : syracuseStep 1775027 = 2662541) B2662541
theorem B1775057 : Blo 1182408 1775057 := bstep (se 2 (by rfl) ⟨665646, by rfl⟩ : syracuseStep 1775057 = 1331293) B1331293
theorem B1775075 : Blo 1182408 1775075 := bstep (se 1 (by rfl) ⟨1331306, by rfl⟩ : syracuseStep 1775075 = 2662613) B2662613
theorem B1775105 : Blo 1182408 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B6739469 : Blo 1182408 6739469 := bstep (se 3 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 6739469 = 2527301) B2527301
theorem B2160145 : Blo 1182408 2160145 := bstep (se 2 (by rfl) ⟨810054, by rfl⟩ : syracuseStep 2160145 = 1620109) B1620109
theorem B1775123 : Blo 1182408 1775123 := bstep (se 1 (by rfl) ⟨1331342, by rfl⟩ : syracuseStep 1775123 = 2662685) B2662685
theorem B5682737 : Blo 1182408 5682737 := bstep (se 2 (by rfl) ⟨2131026, by rfl⟩ : syracuseStep 5682737 = 4262053) B4262053
theorem B1996339 : Blo 1182408 1996339 := bstep (se 1 (by rfl) ⟨1497254, by rfl⟩ : syracuseStep 1996339 = 2994509) B2994509
theorem B1775153 : Blo 1182408 1775153 := bstep (se 2 (by rfl) ⟨665682, by rfl⟩ : syracuseStep 1775153 = 1331365) B1331365
theorem B1775171 : Blo 1182408 1775171 := bstep (se 1 (by rfl) ⟨1331378, by rfl⟩ : syracuseStep 1775171 = 2662757) B2662757
theorem B1775201 : Blo 1182408 1775201 := bstep (se 2 (by rfl) ⟨665700, by rfl⟩ : syracuseStep 1775201 = 1331401) B1331401
theorem B2995825 : Blo 1182408 2995825 := bstep (se 2 (by rfl) ⟨1123434, by rfl⟩ : syracuseStep 2995825 = 2246869) B2246869
theorem B10393201 : Blo 1182408 10393201 := bstep (se 2 (by rfl) ⟨3897450, by rfl⟩ : syracuseStep 10393201 = 7794901) B7794901
theorem B1775219 : Blo 1182408 1775219 := bstep (se 1 (by rfl) ⟨1331414, by rfl⟩ : syracuseStep 1775219 = 2662829) B2662829
theorem B1775249 : Blo 1182408 1775249 := bstep (se 2 (by rfl) ⟨665718, by rfl⟩ : syracuseStep 1775249 = 1331437) B1331437
theorem B1775267 : Blo 1182408 1775267 := bstep (se 1 (by rfl) ⟨1331450, by rfl⟩ : syracuseStep 1775267 = 2662901) B2662901
theorem B5994161 : Blo 1182408 5994161 := bstep (se 2 (by rfl) ⟨2247810, by rfl⟩ : syracuseStep 5994161 = 4495621) B4495621
theorem B1996481 : Blo 1182408 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B1775297 : Blo 1182408 1775297 := bstep (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) B1331473
theorem B6076109 : Blo 1182408 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B1775315 : Blo 1182408 1775315 := bstep (se 1 (by rfl) ⟨1331486, by rfl⟩ : syracuseStep 1775315 = 2662973) B2662973
theorem B11368163 : Blo 1182408 11368163 := bstep (se 1 (by rfl) ⟨8526122, by rfl⟩ : syracuseStep 11368163 = 17052245) B17052245
theorem B1775345 : Blo 1182408 1775345 := bstep (se 2 (by rfl) ⟨665754, by rfl⟩ : syracuseStep 1775345 = 1331509) B1331509
theorem B1496819 : Blo 1182408 1496819 := bstep (se 1 (by rfl) ⟨1122614, by rfl⟩ : syracuseStep 1496819 = 2245229) B2245229
theorem B1775363 : Blo 1182408 1775363 := bstep (se 1 (by rfl) ⟨1331522, by rfl⟩ : syracuseStep 1775363 = 2663045) B2663045
theorem B5986061 : Blo 1182408 5986061 := bstep (se 3 (by rfl) ⟨1122386, by rfl⟩ : syracuseStep 5986061 = 2244773) B2244773
theorem B3995405 : Blo 1182408 3995405 := bstep (se 3 (by rfl) ⟨749138, by rfl⟩ : syracuseStep 3995405 = 1498277) B1498277
theorem B1775393 : Blo 1182408 1775393 := bstep (se 2 (by rfl) ⟨665772, by rfl⟩ : syracuseStep 1775393 = 1331545) B1331545
theorem B1775411 : Blo 1182408 1775411 := bstep (se 1 (by rfl) ⟨1331558, by rfl⟩ : syracuseStep 1775411 = 2663117) B2663117
theorem B1996609 : Blo 1182408 1996609 := bstep (se 2 (by rfl) ⟨748728, by rfl⟩ : syracuseStep 1996609 = 1497457) B1497457
theorem B3995459 : Blo 1182408 3995459 := bstep (se 1 (by rfl) ⟨2996594, by rfl⟩ : syracuseStep 3995459 = 5993189) B5993189
theorem B1775441 : Blo 1182408 1775441 := bstep (se 2 (by rfl) ⟨665790, by rfl⟩ : syracuseStep 1775441 = 1331581) B1331581
theorem B1996643 : Blo 1182408 1996643 := bstep (se 1 (by rfl) ⟨1497482, by rfl⟩ : syracuseStep 1996643 = 2994965) B2994965
theorem B1775459 : Blo 1182408 1775459 := bstep (se 1 (by rfl) ⟨1331594, by rfl⟩ : syracuseStep 1775459 = 2663189) B2663189
theorem B1775489 : Blo 1182408 1775489 := bstep (se 2 (by rfl) ⟨665808, by rfl⟩ : syracuseStep 1775489 = 1331617) B1331617
theorem B2996099 : Blo 1182408 2996099 := bstep (se 1 (by rfl) ⟨2247074, by rfl⟩ : syracuseStep 2996099 = 4494149) B4494149
theorem B1775507 : Blo 1182408 1775507 := bstep (se 1 (by rfl) ⟨1331630, by rfl⟩ : syracuseStep 1775507 = 2663261) B2663261
theorem B1775537 : Blo 1182408 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B1775555 : Blo 1182408 1775555 := bstep (se 1 (by rfl) ⟨1331666, by rfl⟩ : syracuseStep 1775555 = 2663333) B2663333
theorem B1685443 : Blo 1182408 1685443 := bstep (se 1 (by rfl) ⟨1264082, by rfl⟩ : syracuseStep 1685443 = 2528165) B2528165
theorem B5052365 : Blo 1182408 5052365 := bstep (se 3 (by rfl) ⟨947318, by rfl⟩ : syracuseStep 5052365 = 1894637) B1894637
theorem B1775585 : Blo 1182408 1775585 := bstep (se 2 (by rfl) ⟨665844, by rfl⟩ : syracuseStep 1775585 = 1331689) B1331689
theorem B1996771 : Blo 1182408 1996771 := bstep (se 1 (by rfl) ⟨1497578, by rfl⟩ : syracuseStep 1996771 = 2995157) B2995157
theorem B1775603 : Blo 1182408 1775603 := bstep (se 1 (by rfl) ⟨1331702, by rfl⟩ : syracuseStep 1775603 = 2663405) B2663405
theorem B1775633 : Blo 1182408 1775633 := bstep (se 2 (by rfl) ⟨665862, by rfl⟩ : syracuseStep 1775633 = 1331725) B1331725
theorem B1775651 : Blo 1182408 1775651 := bstep (se 1 (by rfl) ⟨1331738, by rfl⟩ : syracuseStep 1775651 = 2663477) B2663477
theorem B1685539 : Blo 1182408 1685539 := bstep (se 1 (by rfl) ⟨1264154, by rfl⟩ : syracuseStep 1685539 = 2528309) B2528309
theorem B4495409 : Blo 1182408 4495409 := bstep (se 2 (by rfl) ⟨1685778, by rfl⟩ : syracuseStep 4495409 = 3371557) B3371557
theorem B1775681 : Blo 1182408 1775681 := bstep (se 2 (by rfl) ⟨665880, by rfl⟩ : syracuseStep 1775681 = 1331761) B1331761
theorem B2996291 : Blo 1182408 2996291 := bstep (se 1 (by rfl) ⟨2247218, by rfl⟩ : syracuseStep 2996291 = 4494437) B4494437
theorem B3995729 : Blo 1182408 3995729 := bstep (se 2 (by rfl) ⟨1498398, by rfl⟩ : syracuseStep 3995729 = 2996797) B2996797
theorem B1775699 : Blo 1182408 1775699 := bstep (se 1 (by rfl) ⟨1331774, by rfl⟩ : syracuseStep 1775699 = 2663549) B2663549
theorem B1996913 : Blo 1182408 1996913 := bstep (se 2 (by rfl) ⟨748842, by rfl⟩ : syracuseStep 1996913 = 1497685) B1497685
theorem B1775729 : Blo 1182408 1775729 := bstep (se 2 (by rfl) ⟨665898, by rfl⟩ : syracuseStep 1775729 = 1331797) B1331797
theorem B1775747 : Blo 1182408 1775747 := bstep (se 1 (by rfl) ⟨1331810, by rfl⟩ : syracuseStep 1775747 = 2663621) B2663621
theorem B13482125 : Blo 1182408 13482125 := bstep (se 3 (by rfl) ⟨2527898, by rfl⟩ : syracuseStep 13482125 = 5055797) B5055797
theorem B1775777 : Blo 1182408 1775777 := bstep (se 2 (by rfl) ⟨665916, by rfl⟩ : syracuseStep 1775777 = 1331833) B1331833
theorem B1775795 : Blo 1182408 1775795 := bstep (se 1 (by rfl) ⟨1331846, by rfl⟩ : syracuseStep 1775795 = 2663693) B2663693
theorem B8091845 : Blo 1182408 8091845 := bstep (se 4 (by rfl) ⟨758610, by rfl⟩ : syracuseStep 8091845 = 1517221) B1517221
theorem B2660561 : Blo 1182408 2660561 := bstep (se 2 (by rfl) ⟨997710, by rfl⟩ : syracuseStep 2660561 = 1995421) B1995421
theorem B1775825 : Blo 1182408 1775825 := bstep (se 2 (by rfl) ⟨665934, by rfl⟩ : syracuseStep 1775825 = 1331869) B1331869
theorem B2660579 : Blo 1182408 2660579 := bstep (se 1 (by rfl) ⟨1995434, by rfl⟩ : syracuseStep 2660579 = 3990869) B3990869
theorem B1775843 : Blo 1182408 1775843 := bstep (se 1 (by rfl) ⟨1331882, by rfl⟩ : syracuseStep 1775843 = 2663765) B2663765
theorem B1997041 : Blo 1182408 1997041 := bstep (se 2 (by rfl) ⟨748890, by rfl⟩ : syracuseStep 1997041 = 1497781) B1497781
theorem B1775873 : Blo 1182408 1775873 := bstep (se 2 (by rfl) ⟨665952, by rfl⟩ : syracuseStep 1775873 = 1331905) B1331905
theorem B1997075 : Blo 1182408 1997075 := bstep (se 1 (by rfl) ⟨1497806, by rfl⟩ : syracuseStep 1997075 = 2995613) B2995613
theorem B1775891 : Blo 1182408 1775891 := bstep (se 1 (by rfl) ⟨1331918, by rfl⟩ : syracuseStep 1775891 = 2663837) B2663837
theorem B1775921 : Blo 1182408 1775921 := bstep (se 2 (by rfl) ⟨665970, by rfl⟩ : syracuseStep 1775921 = 1331941) B1331941
theorem B1775939 : Blo 1182408 1775939 := bstep (se 1 (by rfl) ⟨1331954, by rfl⟩ : syracuseStep 1775939 = 2663909) B2663909
theorem B1775969 : Blo 1182408 1775969 := bstep (se 2 (by rfl) ⟨665988, by rfl⟩ : syracuseStep 1775969 = 1331977) B1331977
theorem B1775987 : Blo 1182408 1775987 := bstep (se 1 (by rfl) ⟨1331990, by rfl⟩ : syracuseStep 1775987 = 2663981) B2663981
theorem B1776017 : Blo 1182408 1776017 := bstep (se 2 (by rfl) ⟨666006, by rfl⟩ : syracuseStep 1776017 = 1332013) B1332013
theorem B1997203 : Blo 1182408 1997203 := bstep (se 1 (by rfl) ⟨1497902, by rfl⟩ : syracuseStep 1997203 = 2995805) B2995805
theorem B1776035 : Blo 1182408 1776035 := bstep (se 1 (by rfl) ⟨1332026, by rfl⟩ : syracuseStep 1776035 = 2664053) B2664053
theorem B1825187 : Blo 1182408 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B1497523 : Blo 1182408 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B1776065 : Blo 1182408 1776065 := bstep (se 2 (by rfl) ⟨666024, by rfl⟩ : syracuseStep 1776065 = 1332049) B1332049
theorem B1776083 : Blo 1182408 1776083 := bstep (se 1 (by rfl) ⟨1332062, by rfl⟩ : syracuseStep 1776083 = 2664125) B2664125
theorem B2660849 : Blo 1182408 2660849 := bstep (se 2 (by rfl) ⟨997818, by rfl⟩ : syracuseStep 2660849 = 1995637) B1995637
theorem B1776113 : Blo 1182408 1776113 := bstep (se 2 (by rfl) ⟨666042, by rfl⟩ : syracuseStep 1776113 = 1332085) B1332085
theorem B2660867 : Blo 1182408 2660867 := bstep (se 1 (by rfl) ⟨1995650, by rfl⟩ : syracuseStep 2660867 = 3991301) B3991301
theorem B1776131 : Blo 1182408 1776131 := bstep (se 1 (by rfl) ⟨1332098, by rfl⟩ : syracuseStep 1776131 = 2664197) B2664197
theorem B1497619 : Blo 1182408 1497619 := bstep (se 1 (by rfl) ⟨1123214, by rfl⟩ : syracuseStep 1497619 = 2246429) B2246429
theorem B1686035 : Blo 1182408 1686035 := bstep (se 1 (by rfl) ⟨1264526, by rfl⟩ : syracuseStep 1686035 = 2529053) B2529053
theorem B1997345 : Blo 1182408 1997345 := bstep (se 2 (by rfl) ⟨749004, by rfl⟩ : syracuseStep 1997345 = 1498009) B1498009
theorem B1776161 : Blo 1182408 1776161 := bstep (se 2 (by rfl) ⟨666060, by rfl⟩ : syracuseStep 1776161 = 1332121) B1332121
theorem B1776179 : Blo 1182408 1776179 := bstep (se 1 (by rfl) ⟨1332134, by rfl⟩ : syracuseStep 1776179 = 2664269) B2664269
theorem B1776209 : Blo 1182408 1776209 := bstep (se 2 (by rfl) ⟨666078, by rfl⟩ : syracuseStep 1776209 = 1332157) B1332157
theorem B7576163 : Blo 1182408 7576163 := bstep (se 1 (by rfl) ⟨5682122, by rfl⟩ : syracuseStep 7576163 = 11364245) B11364245
theorem B1776227 : Blo 1182408 1776227 := bstep (se 1 (by rfl) ⟨1332170, by rfl⟩ : syracuseStep 1776227 = 2664341) B2664341
theorem B3996269 : Blo 1182408 3996269 := bstep (se 3 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 3996269 = 1498601) B1498601
theorem B1776257 : Blo 1182408 1776257 := bstep (se 2 (by rfl) ⟨666096, by rfl⟩ : syracuseStep 1776257 = 1332193) B1332193
theorem B7199365 : Blo 1182408 7199365 := bstep (se 4 (by rfl) ⟨674940, by rfl⟩ : syracuseStep 7199365 = 1349881) B1349881
theorem B1776275 : Blo 1182408 1776275 := bstep (se 1 (by rfl) ⟨1332206, by rfl⟩ : syracuseStep 1776275 = 2664413) B2664413
theorem B1997473 : Blo 1182408 1997473 := bstep (se 2 (by rfl) ⟨749052, by rfl⟩ : syracuseStep 1997473 = 1498105) B1498105
theorem B3996323 : Blo 1182408 3996323 := bstep (se 1 (by rfl) ⟨2997242, by rfl⟩ : syracuseStep 3996323 = 5994485) B5994485
theorem B1776305 : Blo 1182408 1776305 := bstep (se 2 (by rfl) ⟨666114, by rfl⟩ : syracuseStep 1776305 = 1332229) B1332229
theorem B1997507 : Blo 1182408 1997507 := bstep (se 1 (by rfl) ⟨1498130, by rfl⟩ : syracuseStep 1997507 = 2996261) B2996261
theorem B1776323 : Blo 1182408 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B1776353 : Blo 1182408 1776353 := bstep (se 2 (by rfl) ⟨666132, by rfl⟩ : syracuseStep 1776353 = 1332265) B1332265
theorem B1776371 : Blo 1182408 1776371 := bstep (se 1 (by rfl) ⟨1332278, by rfl⟩ : syracuseStep 1776371 = 2664557) B2664557
theorem B2661137 : Blo 1182408 2661137 := bstep (se 2 (by rfl) ⟨997926, by rfl⟩ : syracuseStep 2661137 = 1995853) B1995853
theorem B1776401 : Blo 1182408 1776401 := bstep (se 2 (by rfl) ⟨666150, by rfl⟩ : syracuseStep 1776401 = 1332301) B1332301
theorem B2661155 : Blo 1182408 2661155 := bstep (se 1 (by rfl) ⟨1995866, by rfl⟩ : syracuseStep 2661155 = 3991733) B3991733
theorem B1776419 : Blo 1182408 1776419 := bstep (se 1 (by rfl) ⟨1332314, by rfl⟩ : syracuseStep 1776419 = 2664629) B2664629
theorem B1776449 : Blo 1182408 1776449 := bstep (se 2 (by rfl) ⟨666168, by rfl⟩ : syracuseStep 1776449 = 1332337) B1332337
theorem B1997635 : Blo 1182408 1997635 := bstep (se 1 (by rfl) ⟨1498226, by rfl⟩ : syracuseStep 1997635 = 2996453) B2996453
theorem B1776467 : Blo 1182408 1776467 := bstep (se 1 (by rfl) ⟨1332350, by rfl⟩ : syracuseStep 1776467 = 2664701) B2664701
theorem B1776497 : Blo 1182408 1776497 := bstep (se 2 (by rfl) ⟨666186, by rfl⟩ : syracuseStep 1776497 = 1332373) B1332373
theorem B1776515 : Blo 1182408 1776515 := bstep (se 1 (by rfl) ⟨1332386, by rfl⟩ : syracuseStep 1776515 = 2664773) B2664773
theorem B1776545 : Blo 1182408 1776545 := bstep (se 2 (by rfl) ⟨666204, by rfl⟩ : syracuseStep 1776545 = 1332409) B1332409
theorem B3996593 : Blo 1182408 3996593 := bstep (se 2 (by rfl) ⟨1498722, by rfl⟩ : syracuseStep 3996593 = 2997445) B2997445
theorem B1776563 : Blo 1182408 1776563 := bstep (se 1 (by rfl) ⟨1332422, by rfl⟩ : syracuseStep 1776563 = 2664845) B2664845
theorem B1997777 : Blo 1182408 1997777 := bstep (se 2 (by rfl) ⟨749166, by rfl⟩ : syracuseStep 1997777 = 1498333) B1498333
theorem B1776593 : Blo 1182408 1776593 := bstep (se 2 (by rfl) ⟨666222, by rfl⟩ : syracuseStep 1776593 = 1332445) B1332445
theorem B1776611 : Blo 1182408 1776611 := bstep (se 1 (by rfl) ⟨1332458, by rfl⟩ : syracuseStep 1776611 = 2664917) B2664917
theorem B2997233 : Blo 1182408 2997233 := bstep (se 2 (by rfl) ⟨1123962, by rfl⟩ : syracuseStep 2997233 = 2247925) B2247925
theorem B1498115 : Blo 1182408 1498115 := bstep (se 1 (by rfl) ⟨1123586, by rfl⟩ : syracuseStep 1498115 = 2247173) B2247173
theorem B4267043 : Blo 1182408 4267043 := bstep (se 1 (by rfl) ⟨3200282, by rfl⟩ : syracuseStep 4267043 = 6400565) B6400565
theorem B2997283 : Blo 1182408 2997283 := bstep (se 1 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 2997283 = 4495925) B4495925
theorem B2661425 : Blo 1182408 2661425 := bstep (se 2 (by rfl) ⟨998034, by rfl⟩ : syracuseStep 2661425 = 1996069) B1996069
theorem B21593141 : Blo 1182408 21593141 := bstep (se 5 (by rfl) ⟨1012178, by rfl⟩ : syracuseStep 21593141 = 2024357) B2024357
theorem B2661443 : Blo 1182408 2661443 := bstep (se 1 (by rfl) ⟨1996082, by rfl⟩ : syracuseStep 2661443 = 3992165) B3992165
theorem B1997905 : Blo 1182408 1997905 := bstep (se 2 (by rfl) ⟨749214, by rfl⟩ : syracuseStep 1997905 = 1498429) B1498429
theorem B5995619 : Blo 1182408 5995619 := bstep (se 1 (by rfl) ⟨4496714, by rfl⟩ : syracuseStep 5995619 = 8993429) B8993429
theorem B1997939 : Blo 1182408 1997939 := bstep (se 1 (by rfl) ⟨1498454, by rfl⟩ : syracuseStep 1997939 = 2996909) B2996909
theorem B2997425 : Blo 1182408 2997425 := bstep (se 2 (by rfl) ⟨1124034, by rfl⟩ : syracuseStep 2997425 = 2248069) B2248069
theorem B8527045 : Blo 1182408 8527045 := bstep (se 4 (by rfl) ⟨799410, by rfl⟩ : syracuseStep 8527045 = 1598821) B1598821
theorem B1998067 : Blo 1182408 1998067 := bstep (se 1 (by rfl) ⟨1498550, by rfl⟩ : syracuseStep 1998067 = 2997101) B2997101
theorem B7200049 : Blo 1182408 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B2661713 : Blo 1182408 2661713 := bstep (se 2 (by rfl) ⟨998142, by rfl⟩ : syracuseStep 2661713 = 1996285) B1996285
theorem B2661731 : Blo 1182408 2661731 := bstep (se 1 (by rfl) ⟨1996298, by rfl⟩ : syracuseStep 2661731 = 3992597) B3992597
theorem B1998209 : Blo 1182408 1998209 := bstep (se 2 (by rfl) ⟨749328, by rfl⟩ : syracuseStep 1998209 = 1498657) B1498657
theorem B3841453 : Blo 1182408 3841453 := bstep (se 3 (by rfl) ⟨720272, by rfl⟩ : syracuseStep 3841453 = 1440545) B1440545
theorem B17284549 : Blo 1182408 17284549 := bstep (se 4 (by rfl) ⟨1620426, by rfl⟩ : syracuseStep 17284549 = 3240853) B3240853
theorem B6831557 : Blo 1182408 6831557 := bstep (se 4 (by rfl) ⟨640458, by rfl⟩ : syracuseStep 6831557 = 1280917) B1280917
theorem B3997133 : Blo 1182408 3997133 := bstep (se 3 (by rfl) ⟨749462, by rfl⟩ : syracuseStep 3997133 = 1498925) B1498925
theorem B4496867 : Blo 1182408 4496867 := bstep (se 1 (by rfl) ⟨3372650, by rfl⟩ : syracuseStep 4496867 = 6745301) B6745301
theorem B1998337 : Blo 1182408 1998337 := bstep (se 2 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 1998337 = 1498753) B1498753
theorem B3997187 : Blo 1182408 3997187 := bstep (se 1 (by rfl) ⟨2997890, by rfl⟩ : syracuseStep 3997187 = 5995781) B5995781
theorem B1998371 : Blo 1182408 1998371 := bstep (se 1 (by rfl) ⟨1498778, by rfl⟩ : syracuseStep 1998371 = 2997557) B2997557
theorem B9109061 : Blo 1182408 9109061 := bstep (se 4 (by rfl) ⟨853974, by rfl⟩ : syracuseStep 9109061 = 1707949) B1707949
theorem B2662001 : Blo 1182408 2662001 := bstep (se 2 (by rfl) ⟨998250, by rfl⟩ : syracuseStep 2662001 = 1996501) B1996501
theorem B2662019 : Blo 1182408 2662019 := bstep (se 1 (by rfl) ⟨1996514, by rfl⟩ : syracuseStep 2662019 = 3993029) B3993029
theorem B1998499 : Blo 1182408 1998499 := bstep (se 1 (by rfl) ⟨1498874, by rfl⟩ : syracuseStep 1998499 = 2997749) B2997749
theorem B1498819 : Blo 1182408 1498819 := bstep (se 1 (by rfl) ⟨1124114, by rfl⟩ : syracuseStep 1498819 = 2248229) B2248229
theorem B6741701 : Blo 1182408 6741701 := bstep (se 4 (by rfl) ⟨632034, by rfl⟩ : syracuseStep 6741701 = 1264069) B1264069
theorem B5685005 : Blo 1182408 5685005 := bstep (se 3 (by rfl) ⟨1065938, by rfl⟩ : syracuseStep 5685005 = 2131877) B2131877
theorem B1498915 : Blo 1182408 1498915 := bstep (se 1 (by rfl) ⟨1124186, by rfl⟩ : syracuseStep 1498915 = 2248373) B2248373
theorem B1998641 : Blo 1182408 1998641 := bstep (se 2 (by rfl) ⟨749490, by rfl⟩ : syracuseStep 1998641 = 1498981) B1498981
theorem B6397795 : Blo 1182408 6397795 := bstep (se 1 (by rfl) ⟨4798346, by rfl⟩ : syracuseStep 6397795 = 9596693) B9596693
theorem B2400113 : Blo 1182408 2400113 := bstep (se 2 (by rfl) ⟨900042, by rfl⟩ : syracuseStep 2400113 = 1800085) B1800085
theorem B2662289 : Blo 1182408 2662289 := bstep (se 2 (by rfl) ⟨998358, by rfl⟩ : syracuseStep 2662289 = 1996717) B1996717
theorem B2662307 : Blo 1182408 2662307 := bstep (se 1 (by rfl) ⟨1996730, by rfl⟩ : syracuseStep 2662307 = 3993461) B3993461
theorem B2662451 : Blo 1182408 2662451 := bstep (se 1 (by rfl) ⟨1996838, by rfl⟩ : syracuseStep 2662451 = 3993677) B3993677
theorem B2662487 : Blo 1182408 2662487 := bstep (se 1 (by rfl) ⟨1996865, by rfl⟩ : syracuseStep 2662487 = 3993731) B3993731
theorem B3367115 : Blo 1182408 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B2662667 : Blo 1182408 2662667 := bstep (se 1 (by rfl) ⟨1997000, by rfl⟩ : syracuseStep 2662667 = 3994001) B3994001
theorem B5988653 : Blo 1182408 5988653 := bstep (se 3 (by rfl) ⟨1122872, by rfl⟩ : syracuseStep 5988653 = 2245745) B2245745
theorem B2662721 : Blo 1182408 2662721 := bstep (se 2 (by rfl) ⟨998520, by rfl⟩ : syracuseStep 2662721 = 1997041) B1997041
theorem B2662937 : Blo 1182408 2662937 := bstep (se 2 (by rfl) ⟨998601, by rfl⟩ : syracuseStep 2662937 = 1997203) B1997203
theorem B8528429 : Blo 1182408 8528429 := bstep (se 3 (by rfl) ⟨1599080, by rfl⟩ : syracuseStep 8528429 = 3198161) B3198161
theorem B6734411 : Blo 1182408 6734411 := bstep (se 1 (by rfl) ⟨5050808, by rfl⟩ : syracuseStep 6734411 = 10101617) B10101617
theorem B2663027 : Blo 1182408 2663027 := bstep (se 1 (by rfl) ⟨1997270, by rfl⟩ : syracuseStep 2663027 = 3994541) B3994541
theorem B2245259 : Blo 1182408 2245259 := bstep (se 1 (by rfl) ⟨1683944, by rfl⟩ : syracuseStep 2245259 = 3367889) B3367889
theorem B2663063 : Blo 1182408 2663063 := bstep (se 1 (by rfl) ⟨1997297, by rfl⟩ : syracuseStep 2663063 = 3994595) B3994595
theorem B5055149 : Blo 1182408 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B2245313 : Blo 1182408 2245313 := bstep (se 2 (by rfl) ⟨841992, by rfl⟩ : syracuseStep 2245313 = 1683985) B1683985
theorem B2663243 : Blo 1182408 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B6742885 : Blo 1182408 6742885 := bstep (se 4 (by rfl) ⟨632145, by rfl⟩ : syracuseStep 6742885 = 1264291) B1264291
theorem B2663297 : Blo 1182408 2663297 := bstep (se 2 (by rfl) ⟨998736, by rfl⟩ : syracuseStep 2663297 = 1997473) B1997473
theorem B2130839 : Blo 1182408 2130839 := bstep (se 1 (by rfl) ⟨1598129, by rfl⟩ : syracuseStep 2130839 = 3196259) B3196259
theorem B8987597 : Blo 1182408 8987597 := bstep (se 3 (by rfl) ⟨1685174, by rfl⟩ : syracuseStep 8987597 = 3370349) B3370349
theorem B2663513 : Blo 1182408 2663513 := bstep (se 2 (by rfl) ⟨998817, by rfl⟩ : syracuseStep 2663513 = 1997635) B1997635
theorem B4867165 : Blo 1182408 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B7578775 : Blo 1182408 7578775 := bstep (se 1 (by rfl) ⟨5684081, by rfl⟩ : syracuseStep 7578775 = 11368163) B11368163
theorem B3990707 : Blo 1182408 3990707 := bstep (se 1 (by rfl) ⟨2993030, by rfl⟩ : syracuseStep 3990707 = 5986061) B5986061
theorem B2663603 : Blo 1182408 2663603 := bstep (se 1 (by rfl) ⟨1997702, by rfl⟩ : syracuseStep 2663603 = 3995405) B3995405
theorem B2663639 : Blo 1182408 2663639 := bstep (se 1 (by rfl) ⟨1997729, by rfl⟩ : syracuseStep 2663639 = 3995459) B3995459
theorem B1262839 : Blo 1182408 1262839 := bstep (se 1 (by rfl) ⟨947129, by rfl⟩ : syracuseStep 1262839 = 1894259) B1894259
theorem B7791889 : Blo 1182408 7791889 := bstep (se 2 (by rfl) ⟨2921958, by rfl⟩ : syracuseStep 7791889 = 5843917) B5843917
theorem B3368243 : Blo 1182408 3368243 := bstep (se 1 (by rfl) ⟨2526182, by rfl⟩ : syracuseStep 3368243 = 5052365) B5052365
theorem B2663819 : Blo 1182408 2663819 := bstep (se 1 (by rfl) ⟨1997864, by rfl⟩ : syracuseStep 2663819 = 3995729) B3995729
theorem B2000279 : Blo 1182408 2000279 := bstep (se 1 (by rfl) ⟨1500209, by rfl⟩ : syracuseStep 2000279 = 3000419) B3000419
theorem B5686679 : Blo 1182408 5686679 := bstep (se 1 (by rfl) ⟨4265009, by rfl⟩ : syracuseStep 5686679 = 8530019) B8530019
theorem B8988083 : Blo 1182408 8988083 := bstep (se 1 (by rfl) ⟨6741062, by rfl⟩ : syracuseStep 8988083 = 13482125) B13482125
theorem B3990977 : Blo 1182408 3990977 := bstep (se 2 (by rfl) ⟨1496616, by rfl⟩ : syracuseStep 3990977 = 2993233) B2993233
theorem B2663873 : Blo 1182408 2663873 := bstep (se 2 (by rfl) ⟨998952, by rfl⟩ : syracuseStep 2663873 = 1997905) B1997905
theorem B2246231 : Blo 1182408 2246231 := bstep (se 1 (by rfl) ⟨1684673, by rfl⟩ : syracuseStep 2246231 = 3369347) B3369347
theorem B2664089 : Blo 1182408 2664089 := bstep (se 2 (by rfl) ⟨999033, by rfl⟩ : syracuseStep 2664089 = 1998067) B1998067
theorem B3368641 : Blo 1182408 3368641 := bstep (se 2 (by rfl) ⟨1263240, by rfl⟩ : syracuseStep 3368641 = 2526481) B2526481
theorem B8652505 : Blo 1182408 8652505 := bstep (se 2 (by rfl) ⟨3244689, by rfl⟩ : syracuseStep 8652505 = 6489379) B6489379
theorem B36439793 : Blo 1182408 36439793 := bstep (se 2 (by rfl) ⟨13664922, by rfl⟩ : syracuseStep 36439793 = 27329845) B27329845
theorem B2664179 : Blo 1182408 2664179 := bstep (se 1 (by rfl) ⟨1998134, by rfl⟩ : syracuseStep 2664179 = 3996269) B3996269
theorem B2664215 : Blo 1182408 2664215 := bstep (se 1 (by rfl) ⟨1998161, by rfl⟩ : syracuseStep 2664215 = 3996323) B3996323
theorem B30738275 : Blo 1182408 30738275 := bstep (se 1 (by rfl) ⟨23053706, by rfl⟩ : syracuseStep 30738275 = 46107413) B46107413
theorem B5121937 : Blo 1182408 5121937 := bstep (se 2 (by rfl) ⟨1920726, by rfl⟩ : syracuseStep 5121937 = 3841453) B3841453
theorem B23046065 : Blo 1182408 23046065 := bstep (se 2 (by rfl) ⟨8642274, by rfl⟩ : syracuseStep 23046065 = 17284549) B17284549
theorem B3598273 : Blo 1182408 3598273 := bstep (se 2 (by rfl) ⟨1349352, by rfl⟩ : syracuseStep 3598273 = 2698705) B2698705
theorem B2664395 : Blo 1182408 2664395 := bstep (se 1 (by rfl) ⟨1998296, by rfl⟩ : syracuseStep 2664395 = 3996593) B3996593
theorem B3991517 : Blo 1182408 3991517 := bstep (se 3 (by rfl) ⟨748409, by rfl⟩ : syracuseStep 3991517 = 1496819) B1496819
theorem B2664449 : Blo 1182408 2664449 := bstep (se 2 (by rfl) ⟨999168, by rfl⟩ : syracuseStep 2664449 = 1998337) B1998337
theorem B2844695 : Blo 1182408 2844695 := bstep (se 1 (by rfl) ⟨2133521, by rfl⟩ : syracuseStep 2844695 = 4267043) B4267043
theorem B14395427 : Blo 1182408 14395427 := bstep (se 1 (by rfl) ⟨10796570, by rfl⟩ : syracuseStep 14395427 = 21593141) B21593141
theorem B1263659 : Blo 1182408 1263659 := bstep (se 1 (by rfl) ⟨947744, by rfl⟩ : syracuseStep 1263659 = 1895489) B1895489
theorem B2246771 : Blo 1182408 2246771 := bstep (se 1 (by rfl) ⟨1685078, by rfl⟩ : syracuseStep 2246771 = 3370157) B3370157
theorem B2664665 : Blo 1182408 2664665 := bstep (se 2 (by rfl) ⟨999249, by rfl⟩ : syracuseStep 2664665 = 1998499) B1998499
theorem B6400301 : Blo 1182408 6400301 := bstep (se 3 (by rfl) ⟨1200056, by rfl⟩ : syracuseStep 6400301 = 2400113) B2400113
theorem B2664755 : Blo 1182408 2664755 := bstep (se 1 (by rfl) ⟨1998566, by rfl⟩ : syracuseStep 2664755 = 3997133) B3997133
theorem B2664791 : Blo 1182408 2664791 := bstep (se 1 (by rfl) ⟨1998593, by rfl⟩ : syracuseStep 2664791 = 3997187) B3997187
theorem B6072707 : Blo 1182408 6072707 := bstep (se 1 (by rfl) ⟨4554530, by rfl⟩ : syracuseStep 6072707 = 9109061) B9109061
theorem B2525593 : Blo 1182408 2525593 := bstep (se 2 (by rfl) ⟨947097, by rfl⟩ : syracuseStep 2525593 = 1894195) B1894195
theorem B5401025 : Blo 1182408 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B8530393 : Blo 1182408 8530393 := bstep (se 2 (by rfl) ⟨3198897, by rfl⟩ : syracuseStep 8530393 = 6397795) B6397795
theorem B3197515 : Blo 1182408 3197515 := bstep (se 1 (by rfl) ⟨2398136, by rfl⟩ : syracuseStep 3197515 = 4796273) B4796273
theorem B2132569 : Blo 1182408 2132569 := bstep (se 2 (by rfl) ⟨799713, by rfl⟩ : syracuseStep 2132569 = 1599427) B1599427
theorem B2247257 : Blo 1182408 2247257 := bstep (se 2 (by rfl) ⟨842721, by rfl⟩ : syracuseStep 2247257 = 1685443) B1685443
theorem B1182411 : Blo 1182408 1182411 := bstep (se 1 (by rfl) ⟨886808, by rfl⟩ : syracuseStep 1182411 = 1773617) B1773617
theorem B1182423 : Blo 1182408 1182423 := bstep (se 1 (by rfl) ⟨886817, by rfl⟩ : syracuseStep 1182423 = 1773635) B1773635
theorem B1182443 : Blo 1182408 1182443 := bstep (se 1 (by rfl) ⟨886832, by rfl⟩ : syracuseStep 1182443 = 1773665) B1773665
theorem B43158257 : Blo 1182408 43158257 := bstep (se 2 (by rfl) ⟨16184346, by rfl⟩ : syracuseStep 43158257 = 32368693) B32368693
theorem B1182455 : Blo 1182408 1182455 := bstep (se 1 (by rfl) ⟨886841, by rfl⟩ : syracuseStep 1182455 = 1773683) B1773683
theorem B1182475 : Blo 1182408 1182475 := bstep (se 1 (by rfl) ⟨886856, by rfl⟩ : syracuseStep 1182475 = 1773713) B1773713
theorem B1280779 : Blo 1182408 1280779 := bstep (se 1 (by rfl) ⟨960584, by rfl⟩ : syracuseStep 1280779 = 1921169) B1921169
theorem B1182487 : Blo 1182408 1182487 := bstep (se 1 (by rfl) ⟨886865, by rfl⟩ : syracuseStep 1182487 = 1773731) B1773731
theorem B3197719 : Blo 1182408 3197719 := bstep (se 1 (by rfl) ⟨2398289, by rfl⟩ : syracuseStep 3197719 = 4796579) B4796579
theorem B1182507 : Blo 1182408 1182507 := bstep (se 1 (by rfl) ⟨886880, by rfl⟩ : syracuseStep 1182507 = 1773761) B1773761
theorem B1182519 : Blo 1182408 1182519 := bstep (se 1 (by rfl) ⟨886889, by rfl⟩ : syracuseStep 1182519 = 1773779) B1773779
theorem B1182539 : Blo 1182408 1182539 := bstep (se 1 (by rfl) ⟨886904, by rfl⟩ : syracuseStep 1182539 = 1773809) B1773809
theorem B1182551 : Blo 1182408 1182551 := bstep (se 1 (by rfl) ⟨886913, by rfl⟩ : syracuseStep 1182551 = 1773827) B1773827
theorem B8989541 : Blo 1182408 8989541 := bstep (se 4 (by rfl) ⟨842769, by rfl⟩ : syracuseStep 8989541 = 1685539) B1685539
theorem B1182571 : Blo 1182408 1182571 := bstep (se 1 (by rfl) ⟨886928, by rfl⟩ : syracuseStep 1182571 = 1773857) B1773857
theorem B1182583 : Blo 1182408 1182583 := bstep (se 1 (by rfl) ⟨886937, by rfl⟩ : syracuseStep 1182583 = 1773875) B1773875
theorem B1182603 : Blo 1182408 1182603 := bstep (se 1 (by rfl) ⟨886952, by rfl⟩ : syracuseStep 1182603 = 1773905) B1773905
theorem B2698123 : Blo 1182408 2698123 := bstep (se 1 (by rfl) ⟨2023592, by rfl⟩ : syracuseStep 2698123 = 4047185) B4047185
theorem B1182615 : Blo 1182408 1182615 := bstep (se 1 (by rfl) ⟨886961, by rfl⟩ : syracuseStep 1182615 = 1773923) B1773923
theorem B2132887 : Blo 1182408 2132887 := bstep (se 1 (by rfl) ⟨1599665, by rfl⟩ : syracuseStep 2132887 = 3199331) B3199331
theorem B1182635 : Blo 1182408 1182635 := bstep (se 1 (by rfl) ⟨886976, by rfl⟩ : syracuseStep 1182635 = 1773953) B1773953
theorem B4492205 : Blo 1182408 4492205 := bstep (se 3 (by rfl) ⟨842288, by rfl⟩ : syracuseStep 4492205 = 1684577) B1684577
theorem B1182647 : Blo 1182408 1182647 := bstep (se 1 (by rfl) ⟨886985, by rfl⟩ : syracuseStep 1182647 = 1773971) B1773971
theorem B1182667 : Blo 1182408 1182667 := bstep (se 1 (by rfl) ⟨887000, by rfl⟩ : syracuseStep 1182667 = 1774001) B1774001
theorem B1182679 : Blo 1182408 1182679 := bstep (se 1 (by rfl) ⟨887009, by rfl⟩ : syracuseStep 1182679 = 1774019) B1774019
theorem B1182699 : Blo 1182408 1182699 := bstep (se 1 (by rfl) ⟨887024, by rfl⟩ : syracuseStep 1182699 = 1774049) B1774049
theorem B1182711 : Blo 1182408 1182711 := bstep (se 1 (by rfl) ⟨887033, by rfl⟩ : syracuseStep 1182711 = 1774067) B1774067
theorem B1182731 : Blo 1182408 1182731 := bstep (se 1 (by rfl) ⟨887048, by rfl⟩ : syracuseStep 1182731 = 1774097) B1774097
theorem B1182743 : Blo 1182408 1182743 := bstep (se 1 (by rfl) ⟨887057, by rfl⟩ : syracuseStep 1182743 = 1774115) B1774115
theorem B1264663 : Blo 1182408 1264663 := bstep (se 1 (by rfl) ⟨948497, by rfl⟩ : syracuseStep 1264663 = 1896995) B1896995
theorem B1182763 : Blo 1182408 1182763 := bstep (se 1 (by rfl) ⟨887072, by rfl⟩ : syracuseStep 1182763 = 1774145) B1774145
theorem B1330231 : Blo 1182408 1330231 := bstep (se 1 (by rfl) ⟨997673, by rfl⟩ : syracuseStep 1330231 = 1995347) B1995347
theorem B1182775 : Blo 1182408 1182775 := bstep (se 1 (by rfl) ⟨887081, by rfl⟩ : syracuseStep 1182775 = 1774163) B1774163
theorem B1182795 : Blo 1182408 1182795 := bstep (se 1 (by rfl) ⟨887096, by rfl⟩ : syracuseStep 1182795 = 1774193) B1774193
theorem B3992651 : Blo 1182408 3992651 := bstep (se 1 (by rfl) ⟨2994488, by rfl⟩ : syracuseStep 3992651 = 5988977) B5988977
theorem B1182807 : Blo 1182408 1182807 := bstep (se 1 (by rfl) ⟨887105, by rfl⟩ : syracuseStep 1182807 = 1774211) B1774211
theorem B4263005 : Blo 1182408 4263005 := bstep (se 3 (by rfl) ⟨799313, by rfl⟩ : syracuseStep 4263005 = 1598627) B1598627
theorem B1182827 : Blo 1182408 1182827 := bstep (se 1 (by rfl) ⟨887120, by rfl⟩ : syracuseStep 1182827 = 1774241) B1774241
theorem B1182839 : Blo 1182408 1182839 := bstep (se 1 (by rfl) ⟨887129, by rfl⟩ : syracuseStep 1182839 = 1774259) B1774259
theorem B1182859 : Blo 1182408 1182859 := bstep (se 1 (by rfl) ⟨887144, by rfl⟩ : syracuseStep 1182859 = 1774289) B1774289
theorem B1182871 : Blo 1182408 1182871 := bstep (se 1 (by rfl) ⟨887153, by rfl⟩ : syracuseStep 1182871 = 1774307) B1774307
theorem B1182891 : Blo 1182408 1182891 := bstep (se 1 (by rfl) ⟨887168, by rfl⟩ : syracuseStep 1182891 = 1774337) B1774337
theorem B1182903 : Blo 1182408 1182903 := bstep (se 1 (by rfl) ⟨887177, by rfl⟩ : syracuseStep 1182903 = 1774355) B1774355
theorem B2993345 : Blo 1182408 2993345 := bstep (se 2 (by rfl) ⟨1122504, by rfl⟩ : syracuseStep 2993345 = 2245009) B2245009
theorem B1182923 : Blo 1182408 1182923 := bstep (se 1 (by rfl) ⟨887192, by rfl⟩ : syracuseStep 1182923 = 1774385) B1774385
theorem B1182935 : Blo 1182408 1182935 := bstep (se 1 (by rfl) ⟨887201, by rfl⟩ : syracuseStep 1182935 = 1774403) B1774403
theorem B1330411 : Blo 1182408 1330411 := bstep (se 1 (by rfl) ⟨997808, by rfl⟩ : syracuseStep 1330411 = 1995617) B1995617
theorem B1182955 : Blo 1182408 1182955 := bstep (se 1 (by rfl) ⟨887216, by rfl⟩ : syracuseStep 1182955 = 1774433) B1774433
theorem B1182967 : Blo 1182408 1182967 := bstep (se 1 (by rfl) ⟨887225, by rfl⟩ : syracuseStep 1182967 = 1774451) B1774451
theorem B8981765 : Blo 1182408 8981765 := bstep (se 4 (by rfl) ⟨842040, by rfl⟩ : syracuseStep 8981765 = 1684081) B1684081
theorem B19721477 : Blo 1182408 19721477 := bstep (se 4 (by rfl) ⟨1848888, by rfl⟩ : syracuseStep 19721477 = 3697777) B3697777
theorem B55430405 : Blo 1182408 55430405 := bstep (se 4 (by rfl) ⟨5196600, by rfl⟩ : syracuseStep 55430405 = 10393201) B10393201
theorem B1182987 : Blo 1182408 1182987 := bstep (se 1 (by rfl) ⟨887240, by rfl⟩ : syracuseStep 1182987 = 1774481) B1774481
theorem B1182999 : Blo 1182408 1182999 := bstep (se 1 (by rfl) ⟨887249, by rfl⟩ : syracuseStep 1182999 = 1774499) B1774499
theorem B1183019 : Blo 1182408 1183019 := bstep (se 1 (by rfl) ⟨887264, by rfl⟩ : syracuseStep 1183019 = 1774529) B1774529
theorem B1183031 : Blo 1182408 1183031 := bstep (se 1 (by rfl) ⟨887273, by rfl⟩ : syracuseStep 1183031 = 1774547) B1774547
theorem B1183051 : Blo 1182408 1183051 := bstep (se 1 (by rfl) ⟨887288, by rfl⟩ : syracuseStep 1183051 = 1774577) B1774577
theorem B8990027 : Blo 1182408 8990027 := bstep (se 1 (by rfl) ⟨6742520, by rfl⟩ : syracuseStep 8990027 = 13485041) B13485041
theorem B1330519 : Blo 1182408 1330519 := bstep (se 1 (by rfl) ⟨997889, by rfl⟩ : syracuseStep 1330519 = 1995779) B1995779
theorem B1183063 : Blo 1182408 1183063 := bstep (se 1 (by rfl) ⟨887297, by rfl⟩ : syracuseStep 1183063 = 1774595) B1774595
theorem B3992921 : Blo 1182408 3992921 := bstep (se 2 (by rfl) ⟨1497345, by rfl⟩ : syracuseStep 3992921 = 2994691) B2994691
theorem B1183083 : Blo 1182408 1183083 := bstep (se 1 (by rfl) ⟨887312, by rfl⟩ : syracuseStep 1183083 = 1774625) B1774625
theorem B36466037 : Blo 1182408 36466037 := bstep (se 5 (by rfl) ⟨1709345, by rfl⟩ : syracuseStep 36466037 = 3418691) B3418691
theorem B1183095 : Blo 1182408 1183095 := bstep (se 1 (by rfl) ⟨887321, by rfl⟩ : syracuseStep 1183095 = 1774643) B1774643
theorem B1183115 : Blo 1182408 1183115 := bstep (se 1 (by rfl) ⟨887336, by rfl⟩ : syracuseStep 1183115 = 1774673) B1774673
theorem B1183127 : Blo 1182408 1183127 := bstep (se 1 (by rfl) ⟨887345, by rfl⟩ : syracuseStep 1183127 = 1774691) B1774691
theorem B1183147 : Blo 1182408 1183147 := bstep (se 1 (by rfl) ⟨887360, by rfl⟩ : syracuseStep 1183147 = 1774721) B1774721
theorem B1183159 : Blo 1182408 1183159 := bstep (se 1 (by rfl) ⟨887369, by rfl⟩ : syracuseStep 1183159 = 1774739) B1774739
theorem B1183179 : Blo 1182408 1183179 := bstep (se 1 (by rfl) ⟨887384, by rfl⟩ : syracuseStep 1183179 = 1774769) B1774769
theorem B8531405 : Blo 1182408 8531405 := bstep (se 3 (by rfl) ⟨1599638, by rfl⟩ : syracuseStep 8531405 = 3199277) B3199277
theorem B1183191 : Blo 1182408 1183191 := bstep (se 1 (by rfl) ⟨887393, by rfl⟩ : syracuseStep 1183191 = 1774787) B1774787
theorem B1183211 : Blo 1182408 1183211 := bstep (se 1 (by rfl) ⟨887408, by rfl⟩ : syracuseStep 1183211 = 1774817) B1774817
theorem B1183223 : Blo 1182408 1183223 := bstep (se 1 (by rfl) ⟨887417, by rfl⟩ : syracuseStep 1183223 = 1774835) B1774835
theorem B1330699 : Blo 1182408 1330699 := bstep (se 1 (by rfl) ⟨998024, by rfl⟩ : syracuseStep 1330699 = 1996049) B1996049
theorem B1183243 : Blo 1182408 1183243 := bstep (se 1 (by rfl) ⟨887432, by rfl⟩ : syracuseStep 1183243 = 1774865) B1774865
theorem B1183255 : Blo 1182408 1183255 := bstep (se 1 (by rfl) ⟨887441, by rfl⟩ : syracuseStep 1183255 = 1774883) B1774883
theorem B1183275 : Blo 1182408 1183275 := bstep (se 1 (by rfl) ⟨887456, by rfl⟩ : syracuseStep 1183275 = 1774913) B1774913
theorem B1183287 : Blo 1182408 1183287 := bstep (se 1 (by rfl) ⟨887465, by rfl⟩ : syracuseStep 1183287 = 1774931) B1774931
theorem B3788363 : Blo 1182408 3788363 := bstep (se 1 (by rfl) ⟨2841272, by rfl⟩ : syracuseStep 3788363 = 5682545) B5682545
theorem B1183307 : Blo 1182408 1183307 := bstep (se 1 (by rfl) ⟨887480, by rfl⟩ : syracuseStep 1183307 = 1774961) B1774961
theorem B1183319 : Blo 1182408 1183319 := bstep (se 1 (by rfl) ⟨887489, by rfl⟩ : syracuseStep 1183319 = 1774979) B1774979
theorem B1183339 : Blo 1182408 1183339 := bstep (se 1 (by rfl) ⟨887504, by rfl⟩ : syracuseStep 1183339 = 1775009) B1775009
theorem B1330807 : Blo 1182408 1330807 := bstep (se 1 (by rfl) ⟨998105, by rfl⟩ : syracuseStep 1330807 = 1996211) B1996211
theorem B1183351 : Blo 1182408 1183351 := bstep (se 1 (by rfl) ⟨887513, by rfl⟩ : syracuseStep 1183351 = 1775027) B1775027
theorem B1183371 : Blo 1182408 1183371 := bstep (se 1 (by rfl) ⟨887528, by rfl⟩ : syracuseStep 1183371 = 1775057) B1775057
theorem B1183383 : Blo 1182408 1183383 := bstep (se 1 (by rfl) ⟨887537, by rfl⟩ : syracuseStep 1183383 = 1775075) B1775075
theorem B1183403 : Blo 1182408 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B5402285 : Blo 1182408 5402285 := bstep (se 3 (by rfl) ⟨1012928, by rfl⟩ : syracuseStep 5402285 = 2025857) B2025857
theorem B4492979 : Blo 1182408 4492979 := bstep (se 1 (by rfl) ⟨3369734, by rfl⟩ : syracuseStep 4492979 = 6739469) B6739469
theorem B1183415 : Blo 1182408 1183415 := bstep (se 1 (by rfl) ⟨887561, by rfl⟩ : syracuseStep 1183415 = 1775123) B1775123
theorem B1183435 : Blo 1182408 1183435 := bstep (se 1 (by rfl) ⟨887576, by rfl⟩ : syracuseStep 1183435 = 1775153) B1775153
theorem B1183447 : Blo 1182408 1183447 := bstep (se 1 (by rfl) ⟨887585, by rfl⟩ : syracuseStep 1183447 = 1775171) B1775171
theorem B2993881 : Blo 1182408 2993881 := bstep (se 2 (by rfl) ⟨1122705, by rfl⟩ : syracuseStep 2993881 = 2245411) B2245411
theorem B1183467 : Blo 1182408 1183467 := bstep (se 1 (by rfl) ⟨887600, by rfl⟩ : syracuseStep 1183467 = 1775201) B1775201
theorem B1183479 : Blo 1182408 1183479 := bstep (se 1 (by rfl) ⟨887609, by rfl⟩ : syracuseStep 1183479 = 1775219) B1775219
theorem B2526977 : Blo 1182408 2526977 := bstep (se 2 (by rfl) ⟨947616, by rfl⟩ : syracuseStep 2526977 = 1895233) B1895233
theorem B10792709 : Blo 1182408 10792709 := bstep (se 4 (by rfl) ⟨1011816, by rfl⟩ : syracuseStep 10792709 = 2023633) B2023633
theorem B1183499 : Blo 1182408 1183499 := bstep (se 1 (by rfl) ⟨887624, by rfl⟩ : syracuseStep 1183499 = 1775249) B1775249
theorem B1183511 : Blo 1182408 1183511 := bstep (se 1 (by rfl) ⟨887633, by rfl⟩ : syracuseStep 1183511 = 1775267) B1775267
theorem B1330987 : Blo 1182408 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B1183531 : Blo 1182408 1183531 := bstep (se 1 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 1183531 = 1775297) B1775297
theorem B4050739 : Blo 1182408 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B1183543 : Blo 1182408 1183543 := bstep (se 1 (by rfl) ⟨887657, by rfl⟩ : syracuseStep 1183543 = 1775315) B1775315
theorem B1183563 : Blo 1182408 1183563 := bstep (se 1 (by rfl) ⟨887672, by rfl⟩ : syracuseStep 1183563 = 1775345) B1775345
theorem B1183575 : Blo 1182408 1183575 := bstep (se 1 (by rfl) ⟨887681, by rfl⟩ : syracuseStep 1183575 = 1775363) B1775363
theorem B1183595 : Blo 1182408 1183595 := bstep (se 1 (by rfl) ⟨887696, by rfl⟩ : syracuseStep 1183595 = 1775393) B1775393
theorem B1183607 : Blo 1182408 1183607 := bstep (se 1 (by rfl) ⟨887705, by rfl⟩ : syracuseStep 1183607 = 1775411) B1775411
theorem B1183627 : Blo 1182408 1183627 := bstep (se 1 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 1183627 = 1775441) B1775441
theorem B1331095 : Blo 1182408 1331095 := bstep (se 1 (by rfl) ⟨998321, by rfl⟩ : syracuseStep 1331095 = 1996643) B1996643
theorem B1183639 : Blo 1182408 1183639 := bstep (se 1 (by rfl) ⟨887729, by rfl⟩ : syracuseStep 1183639 = 1775459) B1775459
theorem B1183659 : Blo 1182408 1183659 := bstep (se 1 (by rfl) ⟨887744, by rfl⟩ : syracuseStep 1183659 = 1775489) B1775489
theorem B8531891 : Blo 1182408 8531891 := bstep (se 1 (by rfl) ⟨6398918, by rfl⟩ : syracuseStep 8531891 = 12797837) B12797837
theorem B1183671 : Blo 1182408 1183671 := bstep (se 1 (by rfl) ⟨887753, by rfl⟩ : syracuseStep 1183671 = 1775507) B1775507
theorem B2133953 : Blo 1182408 2133953 := bstep (se 2 (by rfl) ⟨800232, by rfl⟩ : syracuseStep 2133953 = 1600465) B1600465
theorem B1183691 : Blo 1182408 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B1183703 : Blo 1182408 1183703 := bstep (se 1 (by rfl) ⟨887777, by rfl⟩ : syracuseStep 1183703 = 1775555) B1775555
theorem B1183723 : Blo 1182408 1183723 := bstep (se 1 (by rfl) ⟨887792, by rfl⟩ : syracuseStep 1183723 = 1775585) B1775585
theorem B1183735 : Blo 1182408 1183735 := bstep (se 1 (by rfl) ⟨887801, by rfl⟩ : syracuseStep 1183735 = 1775603) B1775603
theorem B1183755 : Blo 1182408 1183755 := bstep (se 1 (by rfl) ⟨887816, by rfl⟩ : syracuseStep 1183755 = 1775633) B1775633
theorem B3993623 : Blo 1182408 3993623 := bstep (se 1 (by rfl) ⟨2995217, by rfl⟩ : syracuseStep 3993623 = 5990435) B5990435
theorem B1183767 : Blo 1182408 1183767 := bstep (se 1 (by rfl) ⟨887825, by rfl⟩ : syracuseStep 1183767 = 1775651) B1775651
theorem B1183787 : Blo 1182408 1183787 := bstep (se 1 (by rfl) ⟨887840, by rfl⟩ : syracuseStep 1183787 = 1775681) B1775681
theorem B1183799 : Blo 1182408 1183799 := bstep (se 1 (by rfl) ⟨887849, by rfl⟩ : syracuseStep 1183799 = 1775699) B1775699
theorem B1331275 : Blo 1182408 1331275 := bstep (se 1 (by rfl) ⟨998456, by rfl⟩ : syracuseStep 1331275 = 1996913) B1996913
theorem B1183819 : Blo 1182408 1183819 := bstep (se 1 (by rfl) ⟨887864, by rfl⟩ : syracuseStep 1183819 = 1775729) B1775729
theorem B1183831 : Blo 1182408 1183831 := bstep (se 1 (by rfl) ⟨887873, by rfl⟩ : syracuseStep 1183831 = 1775747) B1775747
theorem B5992541 : Blo 1182408 5992541 := bstep (se 3 (by rfl) ⟨1123601, by rfl⟩ : syracuseStep 5992541 = 2247203) B2247203
theorem B1183851 : Blo 1182408 1183851 := bstep (se 1 (by rfl) ⟨887888, by rfl⟩ : syracuseStep 1183851 = 1775777) B1775777
theorem B1183863 : Blo 1182408 1183863 := bstep (se 1 (by rfl) ⟨887897, by rfl⟩ : syracuseStep 1183863 = 1775795) B1775795
theorem B5394563 : Blo 1182408 5394563 := bstep (se 1 (by rfl) ⟨4045922, by rfl⟩ : syracuseStep 5394563 = 8091845) B8091845
theorem B19181699 : Blo 1182408 19181699 := bstep (se 1 (by rfl) ⟨14386274, by rfl⟩ : syracuseStep 19181699 = 28772549) B28772549
theorem B1773707 : Blo 1182408 1773707 := bstep (se 1 (by rfl) ⟨1330280, by rfl⟩ : syracuseStep 1773707 = 2660561) B2660561
theorem B1183883 : Blo 1182408 1183883 := bstep (se 1 (by rfl) ⟨887912, by rfl⟩ : syracuseStep 1183883 = 1775825) B1775825
theorem B1773719 : Blo 1182408 1773719 := bstep (se 1 (by rfl) ⟨1330289, by rfl⟩ : syracuseStep 1773719 = 2660579) B2660579
theorem B3371159 : Blo 1182408 3371159 := bstep (se 1 (by rfl) ⟨2528369, by rfl⟩ : syracuseStep 3371159 = 5056739) B5056739
theorem B1183895 : Blo 1182408 1183895 := bstep (se 1 (by rfl) ⟨887921, by rfl⟩ : syracuseStep 1183895 = 1775843) B1775843
theorem B1183915 : Blo 1182408 1183915 := bstep (se 1 (by rfl) ⟨887936, by rfl⟩ : syracuseStep 1183915 = 1775873) B1775873
theorem B1331383 : Blo 1182408 1331383 := bstep (se 1 (by rfl) ⟨998537, by rfl⟩ : syracuseStep 1331383 = 1997075) B1997075
theorem B1183927 : Blo 1182408 1183927 := bstep (se 1 (by rfl) ⟨887945, by rfl⟩ : syracuseStep 1183927 = 1775891) B1775891
theorem B1183947 : Blo 1182408 1183947 := bstep (se 1 (by rfl) ⟨887960, by rfl⟩ : syracuseStep 1183947 = 1775921) B1775921
theorem B1683671 : Blo 1182408 1683671 := bstep (se 1 (by rfl) ⟨1262753, by rfl⟩ : syracuseStep 1683671 = 2525507) B2525507
theorem B1183959 : Blo 1182408 1183959 := bstep (se 1 (by rfl) ⟨887969, by rfl⟩ : syracuseStep 1183959 = 1775939) B1775939
theorem B1773785 : Blo 1182408 1773785 := bstep (se 2 (by rfl) ⟨665169, by rfl⟩ : syracuseStep 1773785 = 1330339) B1330339
theorem B1183979 : Blo 1182408 1183979 := bstep (se 1 (by rfl) ⟨887984, by rfl⟩ : syracuseStep 1183979 = 1775969) B1775969
theorem B1183991 : Blo 1182408 1183991 := bstep (se 1 (by rfl) ⟨887993, by rfl⟩ : syracuseStep 1183991 = 1775987) B1775987
theorem B1184011 : Blo 1182408 1184011 := bstep (se 1 (by rfl) ⟨888008, by rfl⟩ : syracuseStep 1184011 = 1776017) B1776017
theorem B1184023 : Blo 1182408 1184023 := bstep (se 1 (by rfl) ⟨888017, by rfl⟩ : syracuseStep 1184023 = 1776035) B1776035
theorem B1184043 : Blo 1182408 1184043 := bstep (se 1 (by rfl) ⟨888032, by rfl⟩ : syracuseStep 1184043 = 1776065) B1776065
theorem B1184055 : Blo 1182408 1184055 := bstep (se 1 (by rfl) ⟨888041, by rfl⟩ : syracuseStep 1184055 = 1776083) B1776083
theorem B1773899 : Blo 1182408 1773899 := bstep (se 1 (by rfl) ⟨1330424, by rfl⟩ : syracuseStep 1773899 = 2660849) B2660849
theorem B1184075 : Blo 1182408 1184075 := bstep (se 1 (by rfl) ⟨888056, by rfl⟩ : syracuseStep 1184075 = 1776113) B1776113
theorem B1773911 : Blo 1182408 1773911 := bstep (se 1 (by rfl) ⟨1330433, by rfl⟩ : syracuseStep 1773911 = 2660867) B2660867
theorem B1184087 : Blo 1182408 1184087 := bstep (se 1 (by rfl) ⟨888065, by rfl⟩ : syracuseStep 1184087 = 1776131) B1776131
theorem B1331563 : Blo 1182408 1331563 := bstep (se 1 (by rfl) ⟨998672, by rfl⟩ : syracuseStep 1331563 = 1997345) B1997345
theorem B1184107 : Blo 1182408 1184107 := bstep (se 1 (by rfl) ⟨888080, by rfl⟩ : syracuseStep 1184107 = 1776161) B1776161
theorem B1184119 : Blo 1182408 1184119 := bstep (se 1 (by rfl) ⟨888089, by rfl⟩ : syracuseStep 1184119 = 1776179) B1776179
theorem B1184139 : Blo 1182408 1184139 := bstep (se 1 (by rfl) ⟨888104, by rfl⟩ : syracuseStep 1184139 = 1776209) B1776209
theorem B5050775 : Blo 1182408 5050775 := bstep (se 1 (by rfl) ⟨3788081, by rfl⟩ : syracuseStep 5050775 = 7576163) B7576163
theorem B1184151 : Blo 1182408 1184151 := bstep (se 1 (by rfl) ⟨888113, by rfl⟩ : syracuseStep 1184151 = 1776227) B1776227
theorem B1683865 : Blo 1182408 1683865 := bstep (se 2 (by rfl) ⟨631449, by rfl⟩ : syracuseStep 1683865 = 1262899) B1262899
theorem B1773977 : Blo 1182408 1773977 := bstep (se 2 (by rfl) ⟨665241, by rfl⟩ : syracuseStep 1773977 = 1330483) B1330483
theorem B1184171 : Blo 1182408 1184171 := bstep (se 1 (by rfl) ⟨888128, by rfl⟩ : syracuseStep 1184171 = 1776257) B1776257
theorem B1184183 : Blo 1182408 1184183 := bstep (se 1 (by rfl) ⟨888137, by rfl⟩ : syracuseStep 1184183 = 1776275) B1776275
theorem B1184203 : Blo 1182408 1184203 := bstep (se 1 (by rfl) ⟨888152, by rfl⟩ : syracuseStep 1184203 = 1776305) B1776305
theorem B1331671 : Blo 1182408 1331671 := bstep (se 1 (by rfl) ⟨998753, by rfl⟩ : syracuseStep 1331671 = 1997507) B1997507
theorem B1184215 : Blo 1182408 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B1184235 : Blo 1182408 1184235 := bstep (se 1 (by rfl) ⟨888176, by rfl⟩ : syracuseStep 1184235 = 1776353) B1776353
theorem B1184247 : Blo 1182408 1184247 := bstep (se 1 (by rfl) ⟨888185, by rfl⟩ : syracuseStep 1184247 = 1776371) B1776371
theorem B1774091 : Blo 1182408 1774091 := bstep (se 1 (by rfl) ⟨1330568, by rfl⟩ : syracuseStep 1774091 = 2661137) B2661137
theorem B1184267 : Blo 1182408 1184267 := bstep (se 1 (by rfl) ⟨888200, by rfl⟩ : syracuseStep 1184267 = 1776401) B1776401
theorem B1774103 : Blo 1182408 1774103 := bstep (se 1 (by rfl) ⟨1330577, by rfl⟩ : syracuseStep 1774103 = 2661155) B2661155
theorem B1184279 : Blo 1182408 1184279 := bstep (se 1 (by rfl) ⟨888209, by rfl⟩ : syracuseStep 1184279 = 1776419) B1776419
theorem B1184299 : Blo 1182408 1184299 := bstep (se 1 (by rfl) ⟨888224, by rfl⟩ : syracuseStep 1184299 = 1776449) B1776449
theorem B3994163 : Blo 1182408 3994163 := bstep (se 1 (by rfl) ⟨2995622, by rfl⟩ : syracuseStep 3994163 = 5991245) B5991245
theorem B1184311 : Blo 1182408 1184311 := bstep (se 1 (by rfl) ⟨888233, by rfl⟩ : syracuseStep 1184311 = 1776467) B1776467
theorem B1184331 : Blo 1182408 1184331 := bstep (se 1 (by rfl) ⟨888248, by rfl⟩ : syracuseStep 1184331 = 1776497) B1776497
theorem B1184343 : Blo 1182408 1184343 := bstep (se 1 (by rfl) ⟨888257, by rfl⟩ : syracuseStep 1184343 = 1776515) B1776515
theorem B1774169 : Blo 1182408 1774169 := bstep (se 2 (by rfl) ⟨665313, by rfl⟩ : syracuseStep 1774169 = 1330627) B1330627
theorem B1184363 : Blo 1182408 1184363 := bstep (se 1 (by rfl) ⟨888272, by rfl⟩ : syracuseStep 1184363 = 1776545) B1776545
theorem B1184375 : Blo 1182408 1184375 := bstep (se 1 (by rfl) ⟨888281, by rfl⟩ : syracuseStep 1184375 = 1776563) B1776563
theorem B1331851 : Blo 1182408 1331851 := bstep (se 1 (by rfl) ⟨998888, by rfl⟩ : syracuseStep 1331851 = 1997777) B1997777
theorem B1184395 : Blo 1182408 1184395 := bstep (se 1 (by rfl) ⟨888296, by rfl⟩ : syracuseStep 1184395 = 1776593) B1776593
theorem B1184407 : Blo 1182408 1184407 := bstep (se 1 (by rfl) ⟨888305, by rfl⟩ : syracuseStep 1184407 = 1776611) B1776611
theorem B2699929 : Blo 1182408 2699929 := bstep (se 2 (by rfl) ⟨1012473, by rfl⟩ : syracuseStep 2699929 = 2024947) B2024947
theorem B2880193 : Blo 1182408 2880193 := bstep (se 2 (by rfl) ⟨1080072, by rfl⟩ : syracuseStep 2880193 = 2160145) B2160145
theorem B1774283 : Blo 1182408 1774283 := bstep (se 1 (by rfl) ⟨1330712, by rfl⟩ : syracuseStep 1774283 = 2661425) B2661425
theorem B1774295 : Blo 1182408 1774295 := bstep (se 1 (by rfl) ⟨1330721, by rfl⟩ : syracuseStep 1774295 = 2661443) B2661443
theorem B1331959 : Blo 1182408 1331959 := bstep (se 1 (by rfl) ⟨998969, by rfl⟩ : syracuseStep 1331959 = 1997939) B1997939
theorem B17068805 : Blo 1182408 17068805 := bstep (se 4 (by rfl) ⟨1600200, by rfl⟩ : syracuseStep 17068805 = 3200401) B3200401
theorem B1774361 : Blo 1182408 1774361 := bstep (se 2 (by rfl) ⟨665385, by rfl⟩ : syracuseStep 1774361 = 1330771) B1330771
theorem B2994995 : Blo 1182408 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B3994433 : Blo 1182408 3994433 := bstep (se 2 (by rfl) ⟨1497912, by rfl⟩ : syracuseStep 3994433 = 2995825) B2995825
theorem B1422155 : Blo 1182408 1422155 := bstep (se 1 (by rfl) ⟨1066616, by rfl⟩ : syracuseStep 1422155 = 2133233) B2133233
theorem B1774475 : Blo 1182408 1774475 := bstep (se 1 (by rfl) ⟨1330856, by rfl⟩ : syracuseStep 1774475 = 2661713) B2661713
theorem B1995671 : Blo 1182408 1995671 := bstep (se 1 (by rfl) ⟨1496753, by rfl⟩ : syracuseStep 1995671 = 2993507) B2993507
theorem B1774487 : Blo 1182408 1774487 := bstep (se 1 (by rfl) ⟨1330865, by rfl⟩ : syracuseStep 1774487 = 2661731) B2661731
theorem B1332139 : Blo 1182408 1332139 := bstep (se 1 (by rfl) ⟨999104, by rfl⟩ : syracuseStep 1332139 = 1998209) B1998209
theorem B1774553 : Blo 1182408 1774553 := bstep (se 2 (by rfl) ⟨665457, by rfl⟩ : syracuseStep 1774553 = 1330915) B1330915
theorem B1995799 : Blo 1182408 1995799 := bstep (se 1 (by rfl) ⟨1496849, by rfl⟩ : syracuseStep 1995799 = 2993699) B2993699
theorem B1332247 : Blo 1182408 1332247 := bstep (se 1 (by rfl) ⟨999185, by rfl⟩ : syracuseStep 1332247 = 1998371) B1998371
theorem B17052707 : Blo 1182408 17052707 := bstep (se 1 (by rfl) ⟨12789530, by rfl⟩ : syracuseStep 17052707 = 25579061) B25579061
theorem B5682221 : Blo 1182408 5682221 := bstep (se 3 (by rfl) ⟨1065416, by rfl⟩ : syracuseStep 5682221 = 2130833) B2130833
theorem B1774667 : Blo 1182408 1774667 := bstep (se 1 (by rfl) ⟨1331000, by rfl⟩ : syracuseStep 1774667 = 2662001) B2662001
theorem B1774679 : Blo 1182408 1774679 := bstep (se 1 (by rfl) ⟨1331009, by rfl⟩ : syracuseStep 1774679 = 2662019) B2662019
theorem B2995289 : Blo 1182408 2995289 := bstep (se 2 (by rfl) ⟨1123233, by rfl⟩ : syracuseStep 2995289 = 2246467) B2246467
theorem B6739037 : Blo 1182408 6739037 := bstep (se 3 (by rfl) ⟨1263569, by rfl⟩ : syracuseStep 6739037 = 2527139) B2527139
theorem B4494467 : Blo 1182408 4494467 := bstep (se 1 (by rfl) ⟨3370850, by rfl⟩ : syracuseStep 4494467 = 6741701) B6741701
theorem B1774745 : Blo 1182408 1774745 := bstep (se 2 (by rfl) ⟨665529, by rfl⟩ : syracuseStep 1774745 = 1331059) B1331059
theorem B3790003 : Blo 1182408 3790003 := bstep (se 1 (by rfl) ⟨2842502, by rfl⟩ : syracuseStep 3790003 = 5685005) B5685005
theorem B1332427 : Blo 1182408 1332427 := bstep (se 1 (by rfl) ⟨999320, by rfl⟩ : syracuseStep 1332427 = 1998641) B1998641
theorem B1774859 : Blo 1182408 1774859 := bstep (se 1 (by rfl) ⟨1331144, by rfl⟩ : syracuseStep 1774859 = 2662289) B2662289
theorem B1774871 : Blo 1182408 1774871 := bstep (se 1 (by rfl) ⟨1331153, by rfl⟩ : syracuseStep 1774871 = 2662307) B2662307
theorem B1774937 : Blo 1182408 1774937 := bstep (se 2 (by rfl) ⟨665601, by rfl⟩ : syracuseStep 1774937 = 1331203) B1331203
theorem B3994973 : Blo 1182408 3994973 := bstep (se 3 (by rfl) ⟨749057, by rfl⟩ : syracuseStep 3994973 = 1498115) B1498115
theorem B6395267 : Blo 1182408 6395267 := bstep (se 1 (by rfl) ⟨4796450, by rfl⟩ : syracuseStep 6395267 = 9592901) B9592901
theorem B2528651 : Blo 1182408 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B1775051 : Blo 1182408 1775051 := bstep (se 1 (by rfl) ⟨1331288, by rfl⟩ : syracuseStep 1775051 = 2662577) B2662577
theorem B3372491 : Blo 1182408 3372491 := bstep (se 1 (by rfl) ⟨2529368, by rfl⟩ : syracuseStep 3372491 = 5058737) B5058737
theorem B1775063 : Blo 1182408 1775063 := bstep (se 1 (by rfl) ⟨1331297, by rfl⟩ : syracuseStep 1775063 = 2662595) B2662595
theorem B15177233 : Blo 1182408 15177233 := bstep (se 2 (by rfl) ⟨5691462, by rfl⟩ : syracuseStep 15177233 = 11382925) B11382925
theorem B1775129 : Blo 1182408 1775129 := bstep (se 2 (by rfl) ⟨665673, by rfl⟩ : syracuseStep 1775129 = 1331347) B1331347
theorem B4494923 : Blo 1182408 4494923 := bstep (se 1 (by rfl) ⟨3371192, by rfl⟩ : syracuseStep 4494923 = 6742385) B6742385
theorem B21575261 : Blo 1182408 21575261 := bstep (se 3 (by rfl) ⟨4045361, by rfl⟩ : syracuseStep 21575261 = 8090723) B8090723
theorem B8525405 : Blo 1182408 8525405 := bstep (se 3 (by rfl) ⟨1598513, by rfl⟩ : syracuseStep 8525405 = 3197027) B3197027
theorem B8984195 : Blo 1182408 8984195 := bstep (se 1 (by rfl) ⟨6738146, by rfl⟩ : syracuseStep 8984195 = 13476293) B13476293
theorem B1996427 : Blo 1182408 1996427 := bstep (se 1 (by rfl) ⟨1497320, by rfl⟩ : syracuseStep 1996427 = 2994641) B2994641
theorem B1775243 : Blo 1182408 1775243 := bstep (se 1 (by rfl) ⟨1331432, by rfl⟩ : syracuseStep 1775243 = 2662865) B2662865
theorem B1775255 : Blo 1182408 1775255 := bstep (se 1 (by rfl) ⟨1331441, by rfl⟩ : syracuseStep 1775255 = 2662883) B2662883
theorem B10114739 : Blo 1182408 10114739 := bstep (se 1 (by rfl) ⟨7586054, by rfl⟩ : syracuseStep 10114739 = 15172109) B15172109
theorem B5052107 : Blo 1182408 5052107 := bstep (se 1 (by rfl) ⟨3789080, by rfl⟩ : syracuseStep 5052107 = 7578161) B7578161
theorem B1349335 : Blo 1182408 1349335 := bstep (se 1 (by rfl) ⟨1012001, by rfl⟩ : syracuseStep 1349335 = 2024003) B2024003
theorem B1775321 : Blo 1182408 1775321 := bstep (se 2 (by rfl) ⟨665745, by rfl⟩ : syracuseStep 1775321 = 1331491) B1331491
theorem B1996555 : Blo 1182408 1996555 := bstep (se 1 (by rfl) ⟨1497416, by rfl⟩ : syracuseStep 1996555 = 2994833) B2994833
theorem B4495121 : Blo 1182408 4495121 := bstep (se 2 (by rfl) ⟨1685670, by rfl⟩ : syracuseStep 4495121 = 3371341) B3371341
theorem B8533795 : Blo 1182408 8533795 := bstep (se 1 (by rfl) ⟨6400346, by rfl⟩ : syracuseStep 8533795 = 12800693) B12800693
theorem B6739787 : Blo 1182408 6739787 := bstep (se 1 (by rfl) ⟨5054840, by rfl⟩ : syracuseStep 6739787 = 10109681) B10109681
theorem B1775435 : Blo 1182408 1775435 := bstep (se 1 (by rfl) ⟨1331576, by rfl⟩ : syracuseStep 1775435 = 2663153) B2663153
theorem B1685323 : Blo 1182408 1685323 := bstep (se 1 (by rfl) ⟨1263992, by rfl⟩ : syracuseStep 1685323 = 2527985) B2527985
theorem B3200843 : Blo 1182408 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B1775447 : Blo 1182408 1775447 := bstep (se 1 (by rfl) ⟨1331585, by rfl⟩ : syracuseStep 1775447 = 2663171) B2663171
theorem B1496971 : Blo 1182408 1496971 := bstep (se 1 (by rfl) ⟨1122728, by rfl⟩ : syracuseStep 1496971 = 2245457) B2245457
theorem B2398103 : Blo 1182408 2398103 := bstep (se 1 (by rfl) ⟨1798577, by rfl⟩ : syracuseStep 2398103 = 3597155) B3597155
theorem B1996697 : Blo 1182408 1996697 := bstep (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) B1497523
theorem B1775513 : Blo 1182408 1775513 := bstep (se 2 (by rfl) ⟨665817, by rfl⟩ : syracuseStep 1775513 = 1331635) B1331635
theorem B1775627 : Blo 1182408 1775627 := bstep (se 1 (by rfl) ⟨1331720, by rfl⟩ : syracuseStep 1775627 = 2663441) B2663441
theorem B1775639 : Blo 1182408 1775639 := bstep (se 1 (by rfl) ⟨1331729, by rfl⟩ : syracuseStep 1775639 = 2663459) B2663459
theorem B1996825 : Blo 1182408 1996825 := bstep (se 2 (by rfl) ⟨748809, by rfl⟩ : syracuseStep 1996825 = 1497619) B1497619
theorem B10115117 : Blo 1182408 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B1775705 : Blo 1182408 1775705 := bstep (se 2 (by rfl) ⟨665889, by rfl⟩ : syracuseStep 1775705 = 1331779) B1331779
theorem B4864151 : Blo 1182408 4864151 := bstep (se 1 (by rfl) ⟨3648113, by rfl⟩ : syracuseStep 4864151 = 7296227) B7296227
theorem B5994647 : Blo 1182408 5994647 := bstep (se 1 (by rfl) ⟨4495985, by rfl⟩ : syracuseStep 5994647 = 8991971) B8991971
theorem B9599153 : Blo 1182408 9599153 := bstep (se 2 (by rfl) ⟨3599682, by rfl⟩ : syracuseStep 9599153 = 7199365) B7199365
theorem B1775819 : Blo 1182408 1775819 := bstep (se 1 (by rfl) ⟨1331864, by rfl⟩ : syracuseStep 1775819 = 2663729) B2663729
theorem B1775831 : Blo 1182408 1775831 := bstep (se 1 (by rfl) ⟨1331873, by rfl⟩ : syracuseStep 1775831 = 2663747) B2663747
theorem B5052689 : Blo 1182408 5052689 := bstep (se 2 (by rfl) ⟨1894758, by rfl⟩ : syracuseStep 5052689 = 3789517) B3789517
theorem B2660633 : Blo 1182408 2660633 := bstep (se 2 (by rfl) ⟨997737, by rfl⟩ : syracuseStep 2660633 = 1995475) B1995475
theorem B1775897 : Blo 1182408 1775897 := bstep (se 2 (by rfl) ⟨665961, by rfl⟩ : syracuseStep 1775897 = 1331923) B1331923
theorem B10950977 : Blo 1182408 10950977 := bstep (se 2 (by rfl) ⟨4106616, by rfl⟩ : syracuseStep 10950977 = 8213233) B8213233
theorem B2660723 : Blo 1182408 2660723 := bstep (se 1 (by rfl) ⟨1995542, by rfl⟩ : syracuseStep 2660723 = 3991085) B3991085
theorem B1776011 : Blo 1182408 1776011 := bstep (se 1 (by rfl) ⟨1332008, by rfl⟩ : syracuseStep 1776011 = 2664017) B2664017
theorem B2660759 : Blo 1182408 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B1776023 : Blo 1182408 1776023 := bstep (se 1 (by rfl) ⟨1332017, by rfl⟩ : syracuseStep 1776023 = 2664035) B2664035
theorem B3996107 : Blo 1182408 3996107 := bstep (se 1 (by rfl) ⟨2997080, by rfl⟩ : syracuseStep 3996107 = 5994161) B5994161
theorem B1776089 : Blo 1182408 1776089 := bstep (se 2 (by rfl) ⟨666033, by rfl⟩ : syracuseStep 1776089 = 1332067) B1332067
theorem B4495895 : Blo 1182408 4495895 := bstep (se 1 (by rfl) ⟨3371921, by rfl⟩ : syracuseStep 4495895 = 6743843) B6743843
theorem B6076973 : Blo 1182408 6076973 := bstep (se 3 (by rfl) ⟨1139432, by rfl⟩ : syracuseStep 6076973 = 2278865) B2278865
theorem B2660939 : Blo 1182408 2660939 := bstep (se 1 (by rfl) ⟨1995704, by rfl⟩ : syracuseStep 2660939 = 3991409) B3991409
theorem B1776203 : Blo 1182408 1776203 := bstep (se 1 (by rfl) ⟨1332152, by rfl⟩ : syracuseStep 1776203 = 2664305) B2664305
theorem B1997399 : Blo 1182408 1997399 := bstep (se 1 (by rfl) ⟨1498049, by rfl⟩ : syracuseStep 1997399 = 2996099) B2996099
theorem B1776215 : Blo 1182408 1776215 := bstep (se 1 (by rfl) ⟨1332161, by rfl⟩ : syracuseStep 1776215 = 2664323) B2664323
theorem B2660993 : Blo 1182408 2660993 := bstep (se 2 (by rfl) ⟨997872, by rfl⟩ : syracuseStep 2660993 = 1995745) B1995745
theorem B1776281 : Blo 1182408 1776281 := bstep (se 2 (by rfl) ⟨666105, by rfl⟩ : syracuseStep 1776281 = 1332211) B1332211
theorem B2996939 : Blo 1182408 2996939 := bstep (se 1 (by rfl) ⟨2247704, by rfl⟩ : syracuseStep 2996939 = 4495409) B4495409
theorem B1997527 : Blo 1182408 1997527 := bstep (se 1 (by rfl) ⟨1498145, by rfl⟩ : syracuseStep 1997527 = 2996291) B2996291
theorem B5987033 : Blo 1182408 5987033 := bstep (se 2 (by rfl) ⟨2245137, by rfl⟩ : syracuseStep 5987033 = 4490275) B4490275
theorem B3996377 : Blo 1182408 3996377 := bstep (se 2 (by rfl) ⟨1498641, by rfl⟩ : syracuseStep 3996377 = 2997283) B2997283
theorem B4496093 : Blo 1182408 4496093 := bstep (se 3 (by rfl) ⟨843017, by rfl⟩ : syracuseStep 4496093 = 1686035) B1686035
theorem B1776395 : Blo 1182408 1776395 := bstep (se 1 (by rfl) ⟨1332296, by rfl⟩ : syracuseStep 1776395 = 2664593) B2664593
theorem B1776407 : Blo 1182408 1776407 := bstep (se 1 (by rfl) ⟨1332305, by rfl⟩ : syracuseStep 1776407 = 2664611) B2664611
theorem B15153965 : Blo 1182408 15153965 := bstep (se 3 (by rfl) ⟨2841368, by rfl⟩ : syracuseStep 15153965 = 5682737) B5682737
theorem B7199563 : Blo 1182408 7199563 := bstep (se 1 (by rfl) ⟨5399672, by rfl⟩ : syracuseStep 7199563 = 10799345) B10799345
theorem B1497943 : Blo 1182408 1497943 := bstep (se 1 (by rfl) ⟨1123457, by rfl⟩ : syracuseStep 1497943 = 2246915) B2246915
theorem B2661209 : Blo 1182408 2661209 := bstep (se 2 (by rfl) ⟨997953, by rfl⟩ : syracuseStep 2661209 = 1995907) B1995907
theorem B1776473 : Blo 1182408 1776473 := bstep (se 2 (by rfl) ⟨666177, by rfl⟩ : syracuseStep 1776473 = 1332355) B1332355
theorem B11369393 : Blo 1182408 11369393 := bstep (se 2 (by rfl) ⟨4263522, by rfl⟩ : syracuseStep 11369393 = 8527045) B8527045
theorem B2661299 : Blo 1182408 2661299 := bstep (se 1 (by rfl) ⟨1995974, by rfl⟩ : syracuseStep 2661299 = 3991949) B3991949
theorem B1776587 : Blo 1182408 1776587 := bstep (se 1 (by rfl) ⟨1332440, by rfl⟩ : syracuseStep 1776587 = 2664881) B2664881
theorem B2661335 : Blo 1182408 2661335 := bstep (se 1 (by rfl) ⟨1996001, by rfl⟩ : syracuseStep 2661335 = 3992003) B3992003
theorem B1776599 : Blo 1182408 1776599 := bstep (se 1 (by rfl) ⟨1332449, by rfl⟩ : syracuseStep 1776599 = 2664899) B2664899
theorem B9600065 : Blo 1182408 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B2661515 : Blo 1182408 2661515 := bstep (se 1 (by rfl) ⟨1996136, by rfl⟩ : syracuseStep 2661515 = 3992273) B3992273
theorem B8101043 : Blo 1182408 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B2661569 : Blo 1182408 2661569 := bstep (se 2 (by rfl) ⟨998088, by rfl⟩ : syracuseStep 2661569 = 1996177) B1996177
theorem B7691537 : Blo 1182408 7691537 := bstep (se 2 (by rfl) ⟨2884326, by rfl⟩ : syracuseStep 7691537 = 5768653) B5768653
theorem B5053747 : Blo 1182408 5053747 := bstep (se 1 (by rfl) ⟨3790310, by rfl⟩ : syracuseStep 5053747 = 7580621) B7580621
theorem B1998155 : Blo 1182408 1998155 := bstep (se 1 (by rfl) ⟨1498616, by rfl⟩ : syracuseStep 1998155 = 2997233) B2997233
theorem B3997079 : Blo 1182408 3997079 := bstep (se 1 (by rfl) ⟨2997809, by rfl⟩ : syracuseStep 3997079 = 5995619) B5995619
theorem B2661785 : Blo 1182408 2661785 := bstep (se 2 (by rfl) ⟨998169, by rfl⟩ : syracuseStep 2661785 = 1996339) B1996339
theorem B6741427 : Blo 1182408 6741427 := bstep (se 1 (by rfl) ⟨5056070, by rfl⟩ : syracuseStep 6741427 = 10112141) B10112141
theorem B1998283 : Blo 1182408 1998283 := bstep (se 1 (by rfl) ⟨1498712, by rfl⟩ : syracuseStep 1998283 = 2997425) B2997425
theorem B3792349 : Blo 1182408 3792349 := bstep (se 3 (by rfl) ⟨711065, by rfl⟩ : syracuseStep 3792349 = 1422131) B1422131
theorem B2661875 : Blo 1182408 2661875 := bstep (se 1 (by rfl) ⟨1996406, by rfl⟩ : syracuseStep 2661875 = 3992813) B3992813
theorem B2661911 : Blo 1182408 2661911 := bstep (se 1 (by rfl) ⟨1996433, by rfl⟩ : syracuseStep 2661911 = 3992867) B3992867
theorem B1998425 : Blo 1182408 1998425 := bstep (se 2 (by rfl) ⟨749409, by rfl⟩ : syracuseStep 1998425 = 1498819) B1498819
theorem B4554371 : Blo 1182408 4554371 := bstep (se 1 (by rfl) ⟨3415778, by rfl⟩ : syracuseStep 4554371 = 6831557) B6831557
theorem B1498763 : Blo 1182408 1498763 := bstep (se 1 (by rfl) ⟨1124072, by rfl⟩ : syracuseStep 1498763 = 2248145) B2248145
theorem B2997911 : Blo 1182408 2997911 := bstep (se 1 (by rfl) ⟨2248433, by rfl⟩ : syracuseStep 2997911 = 4496867) B4496867
theorem B2662091 : Blo 1182408 2662091 := bstep (se 1 (by rfl) ⟨1996568, by rfl⟩ : syracuseStep 2662091 = 3993137) B3993137
theorem B1998553 : Blo 1182408 1998553 := bstep (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) B1498915
theorem B2662145 : Blo 1182408 2662145 := bstep (se 2 (by rfl) ⟨998304, by rfl⟩ : syracuseStep 2662145 = 1996609) B1996609
theorem B3841843 : Blo 1182408 3841843 := bstep (se 1 (by rfl) ⟨2881382, by rfl⟩ : syracuseStep 3841843 = 5762765) B5762765
theorem B2662361 : Blo 1182408 2662361 := bstep (se 2 (by rfl) ⟨998385, by rfl⟩ : syracuseStep 2662361 = 1996771) B1996771
theorem B2662415 : Blo 1182408 2662415 := bstep (se 1 (by rfl) ⟨1996811, by rfl⟩ : syracuseStep 2662415 = 3993623) B3993623
theorem B2662433 : Blo 1182408 2662433 := bstep (se 2 (by rfl) ⟨998412, by rfl⟩ : syracuseStep 2662433 = 1996825) B1996825
theorem B3596375 : Blo 1182408 3596375 := bstep (se 1 (by rfl) ⟨2697281, by rfl⟩ : syracuseStep 3596375 = 5394563) B5394563
theorem B12787799 : Blo 1182408 12787799 := bstep (se 1 (by rfl) ⟨9590849, by rfl⟩ : syracuseStep 12787799 = 19181699) B19181699
theorem B2244743 : Blo 1182408 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B3367183 : Blo 1182408 3367183 := bstep (se 1 (by rfl) ⟨2525387, by rfl⟩ : syracuseStep 3367183 = 5050775) B5050775
theorem B2662775 : Blo 1182408 2662775 := bstep (se 1 (by rfl) ⟨1997081, by rfl⟩ : syracuseStep 2662775 = 3994163) B3994163
theorem B4489607 : Blo 1182408 4489607 := bstep (se 1 (by rfl) ⟨3367205, by rfl⟩ : syracuseStep 4489607 = 6734411) B6734411
theorem B11379203 : Blo 1182408 11379203 := bstep (se 1 (by rfl) ⟨8534402, by rfl⟩ : syracuseStep 11379203 = 17068805) B17068805
theorem B3367457 : Blo 1182408 3367457 := bstep (se 2 (by rfl) ⟨1262796, by rfl⟩ : syracuseStep 3367457 = 2525593) B2525593
theorem B2245153 : Blo 1182408 2245153 := bstep (se 2 (by rfl) ⟨841932, by rfl⟩ : syracuseStep 2245153 = 1683865) B1683865
theorem B2662955 : Blo 1182408 2662955 := bstep (se 1 (by rfl) ⟨1997216, by rfl⟩ : syracuseStep 2662955 = 3994433) B3994433
theorem B4489789 : Blo 1182408 4489789 := bstep (se 3 (by rfl) ⟨841835, by rfl⟩ : syracuseStep 4489789 = 1683671) B1683671
theorem B2843425 : Blo 1182408 2843425 := bstep (se 2 (by rfl) ⟨1066284, by rfl⟩ : syracuseStep 2843425 = 2132569) B2132569
theorem B2245495 : Blo 1182408 2245495 := bstep (se 1 (by rfl) ⟨1684121, by rfl⟩ : syracuseStep 2245495 = 3368243) B3368243
theorem B2663315 : Blo 1182408 2663315 := bstep (se 1 (by rfl) ⟨1997486, by rfl⟩ : syracuseStep 2663315 = 3994973) B3994973
theorem B2663369 : Blo 1182408 2663369 := bstep (se 2 (by rfl) ⟨998763, by rfl⟩ : syracuseStep 2663369 = 1997527) B1997527
theorem B10118155 : Blo 1182408 10118155 := bstep (se 1 (by rfl) ⟨7588616, by rfl⟩ : syracuseStep 10118155 = 15177233) B15177233
theorem B5989463 : Blo 1182408 5989463 := bstep (se 1 (by rfl) ⟨4492097, by rfl⟩ : syracuseStep 5989463 = 8984195) B8984195
theorem B6743159 : Blo 1182408 6743159 := bstep (se 1 (by rfl) ⟨5057369, by rfl⟩ : syracuseStep 6743159 = 10114739) B10114739
theorem B3368071 : Blo 1182408 3368071 := bstep (se 1 (by rfl) ⟨2526053, by rfl⟩ : syracuseStep 3368071 = 5052107) B5052107
theorem B3597497 : Blo 1182408 3597497 := bstep (se 2 (by rfl) ⟨1349061, by rfl⟩ : syracuseStep 3597497 = 2698123) B2698123
theorem B2843849 : Blo 1182408 2843849 := bstep (se 2 (by rfl) ⟨1066443, by rfl⟩ : syracuseStep 2843849 = 2132887) B2132887
theorem B1598735 : Blo 1182408 1598735 := bstep (se 1 (by rfl) ⟨1199051, by rfl⟩ : syracuseStep 1598735 = 2398103) B2398103
theorem B6743411 : Blo 1182408 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B22742477 : Blo 1182408 22742477 := bstep (se 3 (by rfl) ⟨4264214, by rfl⟩ : syracuseStep 22742477 = 8528429) B8528429
theorem B6489553 : Blo 1182408 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B3368459 : Blo 1182408 3368459 := bstep (se 1 (by rfl) ⟨2526344, by rfl⟩ : syracuseStep 3368459 = 5052689) B5052689
theorem B7300651 : Blo 1182408 7300651 := bstep (se 1 (by rfl) ⟨5475488, by rfl⟩ : syracuseStep 7300651 = 10950977) B10950977
theorem B5989949 : Blo 1182408 5989949 := bstep (se 3 (by rfl) ⟨1123115, by rfl⟩ : syracuseStep 5989949 = 2246231) B2246231
theorem B4048471 : Blo 1182408 4048471 := bstep (se 1 (by rfl) ⟨3036353, by rfl⟩ : syracuseStep 4048471 = 6072707) B6072707
theorem B2664071 : Blo 1182408 2664071 := bstep (se 1 (by rfl) ⟨1998053, by rfl⟩ : syracuseStep 2664071 = 3996107) B3996107
theorem B10389185 : Blo 1182408 10389185 := bstep (se 2 (by rfl) ⟨3895944, by rfl⟩ : syracuseStep 10389185 = 7791889) B7791889
theorem B3991355 : Blo 1182408 3991355 := bstep (se 1 (by rfl) ⟨2993516, by rfl⟩ : syracuseStep 3991355 = 5987033) B5987033
theorem B2664251 : Blo 1182408 2664251 := bstep (se 1 (by rfl) ⟨1998188, by rfl⟩ : syracuseStep 2664251 = 3996377) B3996377
theorem B28772171 : Blo 1182408 28772171 := bstep (se 1 (by rfl) ⟨21579128, by rfl⟩ : syracuseStep 28772171 = 43158257) B43158257
theorem B10102643 : Blo 1182408 10102643 := bstep (se 1 (by rfl) ⟨7576982, by rfl⟩ : syracuseStep 10102643 = 15153965) B15153965
theorem B8988569 : Blo 1182408 8988569 := bstep (se 2 (by rfl) ⟨3370713, by rfl⟩ : syracuseStep 8988569 = 6741427) B6741427
theorem B2664377 : Blo 1182408 2664377 := bstep (se 2 (by rfl) ⟨999141, by rfl⟩ : syracuseStep 2664377 = 1998283) B1998283
theorem B7579595 : Blo 1182408 7579595 := bstep (se 1 (by rfl) ⟨5684696, by rfl⟩ : syracuseStep 7579595 = 11369393) B11369393
theorem B5056465 : Blo 1182408 5056465 := bstep (se 2 (by rfl) ⟨1896174, by rfl⟩ : syracuseStep 5056465 = 3792349) B3792349
theorem B6400043 : Blo 1182408 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B5400695 : Blo 1182408 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B4491521 : Blo 1182408 4491521 := bstep (se 2 (by rfl) ⟨1684320, by rfl⟩ : syracuseStep 4491521 = 3368641) B3368641
theorem B2664719 : Blo 1182408 2664719 := bstep (se 1 (by rfl) ⟨1998539, by rfl⟩ : syracuseStep 2664719 = 3997079) B3997079
theorem B3991841 : Blo 1182408 3991841 := bstep (se 2 (by rfl) ⟨1496940, by rfl⟩ : syracuseStep 3991841 = 2993881) B2993881
theorem B11536673 : Blo 1182408 11536673 := bstep (se 2 (by rfl) ⟨4326252, by rfl⟩ : syracuseStep 11536673 = 8652505) B8652505
theorem B2664737 : Blo 1182408 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B5687603 : Blo 1182408 5687603 := bstep (se 1 (by rfl) ⟨4265702, by rfl⟩ : syracuseStep 5687603 = 8531405) B8531405
theorem B2525575 : Blo 1182408 2525575 := bstep (se 1 (by rfl) ⟨1894181, by rfl⟩ : syracuseStep 2525575 = 3788363) B3788363
theorem B5122457 : Blo 1182408 5122457 := bstep (se 2 (by rfl) ⟨1920921, by rfl⟩ : syracuseStep 5122457 = 3841843) B3841843
theorem B5400985 : Blo 1182408 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B2247097 : Blo 1182408 2247097 := bstep (se 2 (by rfl) ⟨842661, by rfl⟩ : syracuseStep 2247097 = 1685323) B1685323
theorem B7195139 : Blo 1182408 7195139 := bstep (se 1 (by rfl) ⟨5396354, by rfl⟩ : syracuseStep 7195139 = 10792709) B10792709
theorem B5687927 : Blo 1182408 5687927 := bstep (se 1 (by rfl) ⟨4265945, by rfl⟩ : syracuseStep 5687927 = 8531891) B8531891
theorem B1182471 : Blo 1182408 1182471 := bstep (se 1 (by rfl) ⟨886853, by rfl⟩ : syracuseStep 1182471 = 1773707) B1773707
theorem B1182479 : Blo 1182408 1182479 := bstep (se 1 (by rfl) ⟨886859, by rfl⟩ : syracuseStep 1182479 = 1773719) B1773719
theorem B2247439 : Blo 1182408 2247439 := bstep (se 1 (by rfl) ⟨1685579, by rfl⟩ : syracuseStep 2247439 = 3371159) B3371159
theorem B3369757 : Blo 1182408 3369757 := bstep (se 3 (by rfl) ⟨631829, by rfl⟩ : syracuseStep 3369757 = 1263659) B1263659
theorem B6744869 : Blo 1182408 6744869 := bstep (se 4 (by rfl) ⟨632331, by rfl⟩ : syracuseStep 6744869 = 1264663) B1264663
theorem B1182523 : Blo 1182408 1182523 := bstep (se 1 (by rfl) ⟨886892, by rfl⟩ : syracuseStep 1182523 = 1773785) B1773785
theorem B3992435 : Blo 1182408 3992435 := bstep (se 1 (by rfl) ⟨2994326, by rfl⟩ : syracuseStep 3992435 = 5988653) B5988653
theorem B1182599 : Blo 1182408 1182599 := bstep (se 1 (by rfl) ⟨886949, by rfl⟩ : syracuseStep 1182599 = 1773899) B1773899
theorem B1182607 : Blo 1182408 1182607 := bstep (se 1 (by rfl) ⟨886955, by rfl⟩ : syracuseStep 1182607 = 1773911) B1773911
theorem B1182651 : Blo 1182408 1182651 := bstep (se 1 (by rfl) ⟨886988, by rfl⟩ : syracuseStep 1182651 = 1773977) B1773977
theorem B1182727 : Blo 1182408 1182727 := bstep (se 1 (by rfl) ⟨887045, by rfl⟩ : syracuseStep 1182727 = 1774091) B1774091
theorem B1182735 : Blo 1182408 1182735 := bstep (se 1 (by rfl) ⟨887051, by rfl⟩ : syracuseStep 1182735 = 1774103) B1774103
theorem B1182779 : Blo 1182408 1182779 := bstep (se 1 (by rfl) ⟨887084, by rfl⟩ : syracuseStep 1182779 = 1774169) B1774169
theorem B3370099 : Blo 1182408 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B1182855 : Blo 1182408 1182855 := bstep (se 1 (by rfl) ⟨887141, by rfl⟩ : syracuseStep 1182855 = 1774283) B1774283
theorem B1182863 : Blo 1182408 1182863 := bstep (se 1 (by rfl) ⟨887147, by rfl⟩ : syracuseStep 1182863 = 1774295) B1774295
theorem B1182907 : Blo 1182408 1182907 := bstep (se 1 (by rfl) ⟨887180, by rfl⟩ : syracuseStep 1182907 = 1774361) B1774361
theorem B1182983 : Blo 1182408 1182983 := bstep (se 1 (by rfl) ⟨887237, by rfl⟩ : syracuseStep 1182983 = 1774475) B1774475
theorem B1420559 : Blo 1182408 1420559 := bstep (se 1 (by rfl) ⟨1065419, by rfl⟩ : syracuseStep 1420559 = 2130839) B2130839
theorem B1330447 : Blo 1182408 1330447 := bstep (se 1 (by rfl) ⟨997835, by rfl⟩ : syracuseStep 1330447 = 1995671) B1995671
theorem B1182991 : Blo 1182408 1182991 := bstep (se 1 (by rfl) ⟨887243, by rfl⟩ : syracuseStep 1182991 = 1774487) B1774487
theorem B11373857 : Blo 1182408 11373857 := bstep (se 2 (by rfl) ⟨4265196, by rfl⟩ : syracuseStep 11373857 = 8530393) B8530393
theorem B5991731 : Blo 1182408 5991731 := bstep (se 1 (by rfl) ⟨4493798, by rfl⟩ : syracuseStep 5991731 = 8987597) B8987597
theorem B1183035 : Blo 1182408 1183035 := bstep (se 1 (by rfl) ⟨887276, by rfl⟩ : syracuseStep 1183035 = 1774553) B1774553
theorem B3788147 : Blo 1182408 3788147 := bstep (se 1 (by rfl) ⟨2841110, by rfl⟩ : syracuseStep 3788147 = 5682221) B5682221
theorem B1183111 : Blo 1182408 1183111 := bstep (se 1 (by rfl) ⟨887333, by rfl⟩ : syracuseStep 1183111 = 1774667) B1774667
theorem B1183119 : Blo 1182408 1183119 := bstep (se 1 (by rfl) ⟨887339, by rfl⟩ : syracuseStep 1183119 = 1774679) B1774679
theorem B4492691 : Blo 1182408 4492691 := bstep (se 1 (by rfl) ⟨3369518, by rfl⟩ : syracuseStep 4492691 = 6739037) B6739037
theorem B4263353 : Blo 1182408 4263353 := bstep (se 2 (by rfl) ⟨1598757, by rfl⟩ : syracuseStep 4263353 = 3197515) B3197515
theorem B1183163 : Blo 1182408 1183163 := bstep (se 1 (by rfl) ⟨887372, by rfl⟩ : syracuseStep 1183163 = 1774745) B1774745
theorem B17067469 : Blo 1182408 17067469 := bstep (se 3 (by rfl) ⟨3200150, by rfl⟩ : syracuseStep 17067469 = 6400301) B6400301
theorem B1183239 : Blo 1182408 1183239 := bstep (se 1 (by rfl) ⟨887429, by rfl⟩ : syracuseStep 1183239 = 1774859) B1774859
theorem B1183247 : Blo 1182408 1183247 := bstep (se 1 (by rfl) ⟨887435, by rfl⟩ : syracuseStep 1183247 = 1774871) B1774871
theorem B3599905 : Blo 1182408 3599905 := bstep (se 2 (by rfl) ⟨1349964, by rfl⟩ : syracuseStep 3599905 = 2699929) B2699929
theorem B1183291 : Blo 1182408 1183291 := bstep (se 1 (by rfl) ⟨887468, by rfl⟩ : syracuseStep 1183291 = 1774937) B1774937
theorem B4263511 : Blo 1182408 4263511 := bstep (se 1 (by rfl) ⟨3197633, by rfl⟩ : syracuseStep 4263511 = 6395267) B6395267
theorem B5992055 : Blo 1182408 5992055 := bstep (se 1 (by rfl) ⟨4494041, by rfl⟩ : syracuseStep 5992055 = 8988083) B8988083
theorem B1183367 : Blo 1182408 1183367 := bstep (se 1 (by rfl) ⟨887525, by rfl⟩ : syracuseStep 1183367 = 1775051) B1775051
theorem B2248327 : Blo 1182408 2248327 := bstep (se 1 (by rfl) ⟨1686245, by rfl⟩ : syracuseStep 2248327 = 3372491) B3372491
theorem B1183375 : Blo 1182408 1183375 := bstep (se 1 (by rfl) ⟨887531, by rfl⟩ : syracuseStep 1183375 = 1775063) B1775063
theorem B1183419 : Blo 1182408 1183419 := bstep (se 1 (by rfl) ⟨887564, by rfl⟩ : syracuseStep 1183419 = 1775129) B1775129
theorem B4263625 : Blo 1182408 4263625 := bstep (se 2 (by rfl) ⟨1598859, by rfl⟩ : syracuseStep 4263625 = 3197719) B3197719
theorem B1330951 : Blo 1182408 1330951 := bstep (se 1 (by rfl) ⟨998213, by rfl⟩ : syracuseStep 1330951 = 1996427) B1996427
theorem B1183495 : Blo 1182408 1183495 := bstep (se 1 (by rfl) ⟨887621, by rfl⟩ : syracuseStep 1183495 = 1775243) B1775243
theorem B1183503 : Blo 1182408 1183503 := bstep (se 1 (by rfl) ⟨887627, by rfl⟩ : syracuseStep 1183503 = 1775255) B1775255
theorem B8990513 : Blo 1182408 8990513 := bstep (se 2 (by rfl) ⟨3371442, by rfl⟩ : syracuseStep 8990513 = 6742885) B6742885
theorem B1183547 : Blo 1182408 1183547 := bstep (se 1 (by rfl) ⟨887660, by rfl⟩ : syracuseStep 1183547 = 1775321) B1775321
theorem B24293195 : Blo 1182408 24293195 := bstep (se 1 (by rfl) ⟨18219896, by rfl⟩ : syracuseStep 24293195 = 36439793) B36439793
theorem B4493191 : Blo 1182408 4493191 := bstep (se 1 (by rfl) ⟨3369893, by rfl⟩ : syracuseStep 4493191 = 6739787) B6739787
theorem B1183623 : Blo 1182408 1183623 := bstep (se 1 (by rfl) ⟨887717, by rfl⟩ : syracuseStep 1183623 = 1775435) B1775435
theorem B1183631 : Blo 1182408 1183631 := bstep (se 1 (by rfl) ⟨887723, by rfl⟩ : syracuseStep 1183631 = 1775447) B1775447
theorem B20492183 : Blo 1182408 20492183 := bstep (se 1 (by rfl) ⟨15369137, by rfl⟩ : syracuseStep 20492183 = 30738275) B30738275
theorem B1331131 : Blo 1182408 1331131 := bstep (se 1 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 1331131 = 1996697) B1996697
theorem B1183675 : Blo 1182408 1183675 := bstep (se 1 (by rfl) ⟨887756, by rfl⟩ : syracuseStep 1183675 = 1775513) B1775513
theorem B15364043 : Blo 1182408 15364043 := bstep (se 1 (by rfl) ⟨11523032, by rfl⟩ : syracuseStep 15364043 = 23046065) B23046065
theorem B1183751 : Blo 1182408 1183751 := bstep (se 1 (by rfl) ⟨887813, by rfl⟩ : syracuseStep 1183751 = 1775627) B1775627
theorem B1183759 : Blo 1182408 1183759 := bstep (se 1 (by rfl) ⟨887819, by rfl⟩ : syracuseStep 1183759 = 1775639) B1775639
theorem B1896463 : Blo 1182408 1896463 := bstep (se 1 (by rfl) ⟨1422347, by rfl⟩ : syracuseStep 1896463 = 2844695) B2844695
theorem B9596951 : Blo 1182408 9596951 := bstep (se 1 (by rfl) ⟨7197713, by rfl⟩ : syracuseStep 9596951 = 14395427) B14395427
theorem B1183803 : Blo 1182408 1183803 := bstep (se 1 (by rfl) ⟨887852, by rfl⟩ : syracuseStep 1183803 = 1775705) B1775705
theorem B1773641 : Blo 1182408 1773641 := bstep (se 2 (by rfl) ⟨665115, by rfl⟩ : syracuseStep 1773641 = 1330231) B1330231
theorem B1183879 : Blo 1182408 1183879 := bstep (se 1 (by rfl) ⟨887909, by rfl⟩ : syracuseStep 1183879 = 1775819) B1775819
theorem B1183887 : Blo 1182408 1183887 := bstep (se 1 (by rfl) ⟨887915, by rfl⟩ : syracuseStep 1183887 = 1775831) B1775831
theorem B1773755 : Blo 1182408 1773755 := bstep (se 1 (by rfl) ⟨1330316, by rfl⟩ : syracuseStep 1773755 = 2660633) B2660633
theorem B1183931 : Blo 1182408 1183931 := bstep (se 1 (by rfl) ⟨887948, by rfl⟩ : syracuseStep 1183931 = 1775897) B1775897
theorem B10105033 : Blo 1182408 10105033 := bstep (se 2 (by rfl) ⟨3789387, by rfl⟩ : syracuseStep 10105033 = 7578775) B7578775
theorem B1773815 : Blo 1182408 1773815 := bstep (se 1 (by rfl) ⟨1330361, by rfl⟩ : syracuseStep 1773815 = 2660723) B2660723
theorem B1184007 : Blo 1182408 1184007 := bstep (se 1 (by rfl) ⟨888005, by rfl⟩ : syracuseStep 1184007 = 1776011) B1776011
theorem B1773839 : Blo 1182408 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B1184015 : Blo 1182408 1184015 := bstep (se 1 (by rfl) ⟨888011, by rfl⟩ : syracuseStep 1184015 = 1776023) B1776023
theorem B3600683 : Blo 1182408 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B1773881 : Blo 1182408 1773881 := bstep (se 2 (by rfl) ⟨665205, by rfl⟩ : syracuseStep 1773881 = 1330411) B1330411
theorem B1184059 : Blo 1182408 1184059 := bstep (se 1 (by rfl) ⟨888044, by rfl⟩ : syracuseStep 1184059 = 1776089) B1776089
theorem B1683785 : Blo 1182408 1683785 := bstep (se 2 (by rfl) ⟨631419, by rfl⟩ : syracuseStep 1683785 = 1262839) B1262839
theorem B4051315 : Blo 1182408 4051315 := bstep (se 1 (by rfl) ⟨3038486, by rfl⟩ : syracuseStep 4051315 = 6076973) B6076973
theorem B1773959 : Blo 1182408 1773959 := bstep (se 1 (by rfl) ⟨1330469, by rfl⟩ : syracuseStep 1773959 = 2660939) B2660939
theorem B1184135 : Blo 1182408 1184135 := bstep (se 1 (by rfl) ⟨888101, by rfl⟩ : syracuseStep 1184135 = 1776203) B1776203
theorem B1331599 : Blo 1182408 1331599 := bstep (se 1 (by rfl) ⟨998699, by rfl⟩ : syracuseStep 1331599 = 1997399) B1997399
theorem B1184143 : Blo 1182408 1184143 := bstep (se 1 (by rfl) ⟨888107, by rfl⟩ : syracuseStep 1184143 = 1776215) B1776215
theorem B6738329 : Blo 1182408 6738329 := bstep (se 2 (by rfl) ⟨2526873, by rfl⟩ : syracuseStep 6738329 = 5053747) B5053747
theorem B1773995 : Blo 1182408 1773995 := bstep (se 1 (by rfl) ⟨1330496, by rfl⟩ : syracuseStep 1773995 = 2660993) B2660993
theorem B1184187 : Blo 1182408 1184187 := bstep (se 1 (by rfl) ⟨888140, by rfl⟩ : syracuseStep 1184187 = 1776281) B1776281
theorem B1774025 : Blo 1182408 1774025 := bstep (se 2 (by rfl) ⟨665259, by rfl⟩ : syracuseStep 1774025 = 1330519) B1330519
theorem B1184263 : Blo 1182408 1184263 := bstep (se 1 (by rfl) ⟨888197, by rfl⟩ : syracuseStep 1184263 = 1776395) B1776395
theorem B1184271 : Blo 1182408 1184271 := bstep (se 1 (by rfl) ⟨888203, by rfl⟩ : syracuseStep 1184271 = 1776407) B1776407
theorem B1774139 : Blo 1182408 1774139 := bstep (se 1 (by rfl) ⟨1330604, by rfl⟩ : syracuseStep 1774139 = 2661209) B2661209
theorem B1184315 : Blo 1182408 1184315 := bstep (se 1 (by rfl) ⟨888236, by rfl⟩ : syracuseStep 1184315 = 1776473) B1776473
theorem B5993027 : Blo 1182408 5993027 := bstep (se 1 (by rfl) ⟨4494770, by rfl⟩ : syracuseStep 5993027 = 8989541) B8989541
theorem B2994803 : Blo 1182408 2994803 := bstep (se 1 (by rfl) ⟨2246102, by rfl⟩ : syracuseStep 2994803 = 4492205) B4492205
theorem B1774199 : Blo 1182408 1774199 := bstep (se 1 (by rfl) ⟨1330649, by rfl⟩ : syracuseStep 1774199 = 2661299) B2661299
theorem B1184391 : Blo 1182408 1184391 := bstep (se 1 (by rfl) ⟨888293, by rfl⟩ : syracuseStep 1184391 = 1776587) B1776587
theorem B1774223 : Blo 1182408 1774223 := bstep (se 1 (by rfl) ⟨1330667, by rfl⟩ : syracuseStep 1774223 = 2661335) B2661335
theorem B1184399 : Blo 1182408 1184399 := bstep (se 1 (by rfl) ⟨888299, by rfl⟩ : syracuseStep 1184399 = 1776599) B1776599
theorem B1774265 : Blo 1182408 1774265 := bstep (se 2 (by rfl) ⟨665349, by rfl⟩ : syracuseStep 1774265 = 1330699) B1330699
theorem B27316997 : Blo 1182408 27316997 := bstep (se 4 (by rfl) ⟨2560968, by rfl⟩ : syracuseStep 27316997 = 5121937) B5121937
theorem B1774343 : Blo 1182408 1774343 := bstep (se 1 (by rfl) ⟨1330757, by rfl⟩ : syracuseStep 1774343 = 2661515) B2661515
theorem B1995563 : Blo 1182408 1995563 := bstep (se 1 (by rfl) ⟨1496672, by rfl⟩ : syracuseStep 1995563 = 2993345) B2993345
theorem B1774379 : Blo 1182408 1774379 := bstep (se 1 (by rfl) ⟨1330784, by rfl⟩ : syracuseStep 1774379 = 2661569) B2661569
theorem B1774409 : Blo 1182408 1774409 := bstep (se 2 (by rfl) ⟨665403, by rfl⟩ : syracuseStep 1774409 = 1330807) B1330807
theorem B5993351 : Blo 1182408 5993351 := bstep (se 1 (by rfl) ⟨4495013, by rfl⟩ : syracuseStep 5993351 = 8990027) B8990027
theorem B1332103 : Blo 1182408 1332103 := bstep (se 1 (by rfl) ⟨999077, by rfl⟩ : syracuseStep 1332103 = 1998155) B1998155
theorem B24310691 : Blo 1182408 24310691 := bstep (se 1 (by rfl) ⟨18233018, by rfl⟩ : syracuseStep 24310691 = 36466037) B36466037
theorem B1774523 : Blo 1182408 1774523 := bstep (se 1 (by rfl) ⟨1330892, by rfl⟩ : syracuseStep 1774523 = 2661785) B2661785
theorem B1799113 : Blo 1182408 1799113 := bstep (se 2 (by rfl) ⟨674667, by rfl⟩ : syracuseStep 1799113 = 1349335) B1349335
theorem B1774583 : Blo 1182408 1774583 := bstep (se 1 (by rfl) ⟨1330937, by rfl⟩ : syracuseStep 1774583 = 2661875) B2661875
theorem B19190789 : Blo 1182408 19190789 := bstep (se 4 (by rfl) ⟨1799136, by rfl⟩ : syracuseStep 19190789 = 3598273) B3598273
theorem B1774607 : Blo 1182408 1774607 := bstep (se 1 (by rfl) ⟨1330955, by rfl⟩ : syracuseStep 1774607 = 2661911) B2661911
theorem B1774649 : Blo 1182408 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B1332283 : Blo 1182408 1332283 := bstep (se 1 (by rfl) ⟨999212, by rfl⟩ : syracuseStep 1332283 = 1998425) B1998425
theorem B3036247 : Blo 1182408 3036247 := bstep (se 1 (by rfl) ⟨2277185, by rfl⟩ : syracuseStep 3036247 = 4554371) B4554371
theorem B3601523 : Blo 1182408 3601523 := bstep (se 1 (by rfl) ⟨2701142, by rfl⟩ : syracuseStep 3601523 = 5402285) B5402285
theorem B2995319 : Blo 1182408 2995319 := bstep (se 1 (by rfl) ⟨2246489, by rfl⟩ : syracuseStep 2995319 = 4492979) B4492979
theorem B1774727 : Blo 1182408 1774727 := bstep (se 1 (by rfl) ⟨1331045, by rfl⟩ : syracuseStep 1774727 = 2662091) B2662091
theorem B1774763 : Blo 1182408 1774763 := bstep (se 1 (by rfl) ⟨1331072, by rfl⟩ : syracuseStep 1774763 = 2662145) B2662145
theorem B1684651 : Blo 1182408 1684651 := bstep (se 1 (by rfl) ⟨1263488, by rfl⟩ : syracuseStep 1684651 = 2526977) B2526977
theorem B1995961 : Blo 1182408 1995961 := bstep (se 2 (by rfl) ⟨748485, by rfl⟩ : syracuseStep 1995961 = 1496971) B1496971
theorem B1774793 : Blo 1182408 1774793 := bstep (se 2 (by rfl) ⟨665547, by rfl⟩ : syracuseStep 1774793 = 1331095) B1331095
theorem B1422635 : Blo 1182408 1422635 := bstep (se 1 (by rfl) ⟨1066976, by rfl⟩ : syracuseStep 1422635 = 2133953) B2133953
theorem B1774907 : Blo 1182408 1774907 := bstep (se 1 (by rfl) ⟨1331180, by rfl⟩ : syracuseStep 1774907 = 2662361) B2662361
theorem B1774967 : Blo 1182408 1774967 := bstep (se 1 (by rfl) ⟨1331225, by rfl⟩ : syracuseStep 1774967 = 2662451) B2662451
theorem B1774991 : Blo 1182408 1774991 := bstep (se 1 (by rfl) ⟨1331243, by rfl⟩ : syracuseStep 1774991 = 2662487) B2662487
theorem B3995027 : Blo 1182408 3995027 := bstep (se 1 (by rfl) ⟨2996270, by rfl⟩ : syracuseStep 3995027 = 5992541) B5992541
theorem B1775033 : Blo 1182408 1775033 := bstep (se 2 (by rfl) ⟨665637, by rfl⟩ : syracuseStep 1775033 = 1331275) B1331275
theorem B1775111 : Blo 1182408 1775111 := bstep (se 1 (by rfl) ⟨1331333, by rfl⟩ : syracuseStep 1775111 = 2662667) B2662667
theorem B1775147 : Blo 1182408 1775147 := bstep (se 1 (by rfl) ⟨1331360, by rfl⟩ : syracuseStep 1775147 = 2662721) B2662721
theorem B1775177 : Blo 1182408 1775177 := bstep (se 2 (by rfl) ⟨665691, by rfl⟩ : syracuseStep 1775177 = 1331383) B1331383
theorem B1775291 : Blo 1182408 1775291 := bstep (se 1 (by rfl) ⟨1331468, by rfl⟩ : syracuseStep 1775291 = 2662937) B2662937
theorem B1775351 : Blo 1182408 1775351 := bstep (se 1 (by rfl) ⟨1331513, by rfl⟩ : syracuseStep 1775351 = 2663027) B2663027
theorem B1775375 : Blo 1182408 1775375 := bstep (se 1 (by rfl) ⟨1331531, by rfl⟩ : syracuseStep 1775375 = 2663063) B2663063
theorem B1496875 : Blo 1182408 1496875 := bstep (se 1 (by rfl) ⟨1122656, by rfl⟩ : syracuseStep 1496875 = 2245313) B2245313
theorem B1775417 : Blo 1182408 1775417 := bstep (se 2 (by rfl) ⟨665781, by rfl⟩ : syracuseStep 1775417 = 1331563) B1331563
theorem B1996663 : Blo 1182408 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B1775495 : Blo 1182408 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B1775531 : Blo 1182408 1775531 := bstep (se 1 (by rfl) ⟨1331648, by rfl⟩ : syracuseStep 1775531 = 2663297) B2663297
theorem B1775561 : Blo 1182408 1775561 := bstep (se 2 (by rfl) ⟨665835, by rfl⟩ : syracuseStep 1775561 = 1331671) B1331671
theorem B11368471 : Blo 1182408 11368471 := bstep (se 1 (by rfl) ⟨8526353, by rfl⟩ : syracuseStep 11368471 = 17052707) B17052707
theorem B20510765 : Blo 1182408 20510765 := bstep (se 3 (by rfl) ⟨3845768, by rfl⟩ : syracuseStep 20510765 = 7691537) B7691537
theorem B1996859 : Blo 1182408 1996859 := bstep (se 1 (by rfl) ⟨1497644, by rfl⟩ : syracuseStep 1996859 = 2995289) B2995289
theorem B1775675 : Blo 1182408 1775675 := bstep (se 1 (by rfl) ⟨1331756, by rfl⟩ : syracuseStep 1775675 = 2663513) B2663513
theorem B2996311 : Blo 1182408 2996311 := bstep (se 1 (by rfl) ⟨2247233, by rfl⟩ : syracuseStep 2996311 = 4494467) B4494467
theorem B2660471 : Blo 1182408 2660471 := bstep (se 1 (by rfl) ⟨1995353, by rfl⟩ : syracuseStep 2660471 = 3990707) B3990707
theorem B1775735 : Blo 1182408 1775735 := bstep (se 1 (by rfl) ⟨1331801, by rfl⟩ : syracuseStep 1775735 = 2663603) B2663603
theorem B1775759 : Blo 1182408 1775759 := bstep (se 1 (by rfl) ⟨1331819, by rfl⟩ : syracuseStep 1775759 = 2663639) B2663639
theorem B1775801 : Blo 1182408 1775801 := bstep (se 2 (by rfl) ⟨665925, by rfl⟩ : syracuseStep 1775801 = 1331851) B1331851
theorem B3840257 : Blo 1182408 3840257 := bstep (se 2 (by rfl) ⟨1440096, by rfl⟩ : syracuseStep 3840257 = 2880193) B2880193
theorem B1775879 : Blo 1182408 1775879 := bstep (se 1 (by rfl) ⟨1331909, by rfl⟩ : syracuseStep 1775879 = 2663819) B2663819
theorem B1685767 : Blo 1182408 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B1333519 : Blo 1182408 1333519 := bstep (se 1 (by rfl) ⟨1000139, by rfl⟩ : syracuseStep 1333519 = 2000279) B2000279
theorem B3791119 : Blo 1182408 3791119 := bstep (se 1 (by rfl) ⟨2843339, by rfl⟩ : syracuseStep 3791119 = 5686679) B5686679
theorem B2660651 : Blo 1182408 2660651 := bstep (se 1 (by rfl) ⟨1995488, by rfl⟩ : syracuseStep 2660651 = 3990977) B3990977
theorem B1775915 : Blo 1182408 1775915 := bstep (se 1 (by rfl) ⟨1331936, by rfl⟩ : syracuseStep 1775915 = 2663873) B2663873
theorem B1775945 : Blo 1182408 1775945 := bstep (se 2 (by rfl) ⟨665979, by rfl⟩ : syracuseStep 1775945 = 1331959) B1331959
theorem B2996615 : Blo 1182408 2996615 := bstep (se 1 (by rfl) ⟨2247461, by rfl⟩ : syracuseStep 2996615 = 4494923) B4494923
theorem B14383507 : Blo 1182408 14383507 := bstep (se 1 (by rfl) ⟨10787630, by rfl⟩ : syracuseStep 14383507 = 21575261) B21575261
theorem B5683603 : Blo 1182408 5683603 := bstep (se 1 (by rfl) ⟨4262702, by rfl⟩ : syracuseStep 5683603 = 8525405) B8525405
theorem B9599417 : Blo 1182408 9599417 := bstep (se 2 (by rfl) ⟨3599781, by rfl⟩ : syracuseStep 9599417 = 7199563) B7199563
theorem B1776059 : Blo 1182408 1776059 := bstep (se 1 (by rfl) ⟨1332044, by rfl⟩ : syracuseStep 1776059 = 2664089) B2664089
theorem B1997257 : Blo 1182408 1997257 := bstep (se 2 (by rfl) ⟨748971, by rfl⟩ : syracuseStep 1997257 = 1497943) B1497943
theorem B1776119 : Blo 1182408 1776119 := bstep (se 1 (by rfl) ⟨1332089, by rfl⟩ : syracuseStep 1776119 = 2664179) B2664179
theorem B2996747 : Blo 1182408 2996747 := bstep (se 1 (by rfl) ⟨2247560, by rfl⟩ : syracuseStep 2996747 = 4495121) B4495121
theorem B1776143 : Blo 1182408 1776143 := bstep (se 1 (by rfl) ⟨1332107, by rfl⟩ : syracuseStep 1776143 = 2664215) B2664215
theorem B1776185 : Blo 1182408 1776185 := bstep (se 2 (by rfl) ⟨666069, by rfl⟩ : syracuseStep 1776185 = 1332139) B1332139
theorem B1776263 : Blo 1182408 1776263 := bstep (se 1 (by rfl) ⟨1332197, by rfl⟩ : syracuseStep 1776263 = 2664395) B2664395
theorem B2661011 : Blo 1182408 2661011 := bstep (se 1 (by rfl) ⟨1995758, by rfl⟩ : syracuseStep 2661011 = 3991517) B3991517
theorem B1776299 : Blo 1182408 1776299 := bstep (se 1 (by rfl) ⟨1332224, by rfl⟩ : syracuseStep 1776299 = 2664449) B2664449
theorem B2661065 : Blo 1182408 2661065 := bstep (se 2 (by rfl) ⟨997899, by rfl⟩ : syracuseStep 2661065 = 1995799) B1995799
theorem B1776329 : Blo 1182408 1776329 := bstep (se 2 (by rfl) ⟨666123, by rfl⟩ : syracuseStep 1776329 = 1332247) B1332247
theorem B6830821 : Blo 1182408 6830821 := bstep (se 4 (by rfl) ⟨640389, by rfl⟩ : syracuseStep 6830821 = 1280779) B1280779
theorem B1497847 : Blo 1182408 1497847 := bstep (se 1 (by rfl) ⟨1123385, by rfl⟩ : syracuseStep 1497847 = 2246771) B2246771
theorem B3242767 : Blo 1182408 3242767 := bstep (se 1 (by rfl) ⟨2432075, by rfl⟩ : syracuseStep 3242767 = 4864151) B4864151
theorem B3996431 : Blo 1182408 3996431 := bstep (se 1 (by rfl) ⟨2997323, by rfl⟩ : syracuseStep 3996431 = 5994647) B5994647
theorem B1776443 : Blo 1182408 1776443 := bstep (se 1 (by rfl) ⟨1332332, by rfl⟩ : syracuseStep 1776443 = 2664665) B2664665
theorem B1776503 : Blo 1182408 1776503 := bstep (se 1 (by rfl) ⟨1332377, by rfl⟩ : syracuseStep 1776503 = 2664755) B2664755
theorem B1776527 : Blo 1182408 1776527 := bstep (se 1 (by rfl) ⟨1332395, by rfl⟩ : syracuseStep 1776527 = 2664791) B2664791
theorem B5053337 : Blo 1182408 5053337 := bstep (se 2 (by rfl) ⟨1895001, by rfl⟩ : syracuseStep 5053337 = 3790003) B3790003
theorem B1776569 : Blo 1182408 1776569 := bstep (se 2 (by rfl) ⟨666213, by rfl⟩ : syracuseStep 1776569 = 1332427) B1332427
theorem B2997263 : Blo 1182408 2997263 := bstep (se 1 (by rfl) ⟨2247947, by rfl⟩ : syracuseStep 2997263 = 4495895) B4495895
theorem B5987357 : Blo 1182408 5987357 := bstep (se 3 (by rfl) ⟨1122629, by rfl⟩ : syracuseStep 5987357 = 2245259) B2245259
theorem B3996701 : Blo 1182408 3996701 := bstep (se 3 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 3996701 = 1498763) B1498763
theorem B1498171 : Blo 1182408 1498171 := bstep (se 1 (by rfl) ⟨1123628, by rfl⟩ : syracuseStep 1498171 = 2247257) B2247257
theorem B1997959 : Blo 1182408 1997959 := bstep (se 1 (by rfl) ⟨1498469, by rfl⟩ : syracuseStep 1997959 = 2996939) B2996939
theorem B2997395 : Blo 1182408 2997395 := bstep (se 1 (by rfl) ⟨2248046, by rfl⟩ : syracuseStep 2997395 = 4496093) B4496093
theorem B102390965 : Blo 1182408 102390965 := bstep (se 5 (by rfl) ⟨4799576, by rfl⟩ : syracuseStep 102390965 = 9599153) B9599153
theorem B2661767 : Blo 1182408 2661767 := bstep (se 1 (by rfl) ⟨1996325, by rfl⟩ : syracuseStep 2661767 = 3992651) B3992651
theorem B2842003 : Blo 1182408 2842003 := bstep (se 1 (by rfl) ⟨2131502, by rfl⟩ : syracuseStep 2842003 = 4263005) B4263005
theorem B5987843 : Blo 1182408 5987843 := bstep (se 1 (by rfl) ⟨4490882, by rfl⟩ : syracuseStep 5987843 = 8981765) B8981765
theorem B13147651 : Blo 1182408 13147651 := bstep (se 1 (by rfl) ⟨9860738, by rfl⟩ : syracuseStep 13147651 = 19721477) B19721477
theorem B36953603 : Blo 1182408 36953603 := bstep (se 1 (by rfl) ⟨27715202, by rfl⟩ : syracuseStep 36953603 = 55430405) B55430405
theorem B3792413 : Blo 1182408 3792413 := bstep (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) B1422155
theorem B8535581 : Blo 1182408 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B2661947 : Blo 1182408 2661947 := bstep (se 1 (by rfl) ⟨1996460, by rfl⟩ : syracuseStep 2661947 = 3992921) B3992921
theorem B2662073 : Blo 1182408 2662073 := bstep (se 2 (by rfl) ⟨998277, by rfl⟩ : syracuseStep 2662073 = 1996555) B1996555
theorem B11378393 : Blo 1182408 11378393 := bstep (se 2 (by rfl) ⟨4266897, by rfl⟩ : syracuseStep 11378393 = 8533795) B8533795
theorem B1998607 : Blo 1182408 1998607 := bstep (se 1 (by rfl) ⟨1498955, by rfl⟩ : syracuseStep 1998607 = 2997911) B2997911
theorem B6397967 : Blo 1182408 6397967 := bstep (se 1 (by rfl) ⟨4798475, by rfl⟩ : syracuseStep 6397967 = 9596951) B9596951
theorem B2400455 : Blo 1182408 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B7586135 : Blo 1182408 7586135 := bstep (se 1 (by rfl) ⟨5689601, by rfl⟩ : syracuseStep 7586135 = 11379203) B11379203
theorem B4489577 : Blo 1182408 4489577 := bstep (se 2 (by rfl) ⟨1683591, by rfl⟩ : syracuseStep 4489577 = 3367183) B3367183
theorem B5054825 : Blo 1182408 5054825 := bstep (se 2 (by rfl) ⟨1895559, by rfl⟩ : syracuseStep 5054825 = 3791119) B3791119
theorem B2244971 : Blo 1182408 2244971 := bstep (se 1 (by rfl) ⟨1683728, by rfl⟩ : syracuseStep 2244971 = 3367457) B3367457
theorem B18211331 : Blo 1182408 18211331 := bstep (se 1 (by rfl) ⟨13658498, by rfl⟩ : syracuseStep 18211331 = 27316997) B27316997
theorem B3367433 : Blo 1182408 3367433 := bstep (se 2 (by rfl) ⟨1262787, by rfl⟩ : syracuseStep 3367433 = 2525575) B2525575
theorem B19178009 : Blo 1182408 19178009 := bstep (se 2 (by rfl) ⟨7191753, by rfl⟩ : syracuseStep 19178009 = 14383507) B14383507
theorem B7578137 : Blo 1182408 7578137 := bstep (se 2 (by rfl) ⟨2841801, by rfl⟩ : syracuseStep 7578137 = 5683603) B5683603
theorem B7201313 : Blo 1182408 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B2663009 : Blo 1182408 2663009 := bstep (se 2 (by rfl) ⟨998628, by rfl⟩ : syracuseStep 2663009 = 1997257) B1997257
theorem B10240685 : Blo 1182408 10240685 := bstep (se 3 (by rfl) ⟨1920128, by rfl⟩ : syracuseStep 10240685 = 3840257) B3840257
theorem B2401015 : Blo 1182408 2401015 := bstep (se 1 (by rfl) ⟨1800761, by rfl⟩ : syracuseStep 2401015 = 3601523) B3601523
theorem B4490093 : Blo 1182408 4490093 := bstep (se 3 (by rfl) ⟨841892, by rfl⟩ : syracuseStep 4490093 = 1683785) B1683785
theorem B2663351 : Blo 1182408 2663351 := bstep (se 1 (by rfl) ⟨1997513, by rfl⟩ : syracuseStep 2663351 = 3995027) B3995027
theorem B2245639 : Blo 1182408 2245639 := bstep (se 1 (by rfl) ⟨1684229, by rfl⟩ : syracuseStep 2245639 = 3368459) B3368459
theorem B6735095 : Blo 1182408 6735095 := bstep (se 1 (by rfl) ⟨5051321, by rfl⟩ : syracuseStep 6735095 = 10102643) B10102643
theorem B13673843 : Blo 1182408 13673843 := bstep (se 1 (by rfl) ⟨10255382, by rfl⟩ : syracuseStep 13673843 = 20510765) B20510765
theorem B4490761 : Blo 1182408 4490761 := bstep (se 2 (by rfl) ⟨1684035, by rfl⟩ : syracuseStep 4490761 = 3368071) B3368071
theorem B2663945 : Blo 1182408 2663945 := bstep (se 2 (by rfl) ⟨998979, by rfl⟩ : syracuseStep 2663945 = 1997959) B1997959
theorem B2246201 : Blo 1182408 2246201 := bstep (se 2 (by rfl) ⟨842325, by rfl⟩ : syracuseStep 2246201 = 1684651) B1684651
theorem B6399611 : Blo 1182408 6399611 := bstep (se 1 (by rfl) ⟨4799708, by rfl⟩ : syracuseStep 6399611 = 9599417) B9599417
theorem B2664287 : Blo 1182408 2664287 := bstep (se 1 (by rfl) ⟨1998215, by rfl⟩ : syracuseStep 2664287 = 3996431) B3996431
theorem B3368891 : Blo 1182408 3368891 := bstep (se 1 (by rfl) ⟨2526668, by rfl⟩ : syracuseStep 3368891 = 5053337) B5053337
theorem B8652737 : Blo 1182408 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B3991571 : Blo 1182408 3991571 := bstep (se 1 (by rfl) ⟨2993678, by rfl⟩ : syracuseStep 3991571 = 5987357) B5987357
theorem B2664467 : Blo 1182408 2664467 := bstep (se 1 (by rfl) ⟨1998350, by rfl⟩ : syracuseStep 2664467 = 3996701) B3996701
theorem B9734201 : Blo 1182408 9734201 := bstep (se 2 (by rfl) ⟨3650325, by rfl⟩ : syracuseStep 9734201 = 7300651) B7300651
theorem B2525431 : Blo 1182408 2525431 := bstep (se 1 (by rfl) ⟨1894073, by rfl⟩ : syracuseStep 2525431 = 3788147) B3788147
theorem B3991895 : Blo 1182408 3991895 := bstep (se 1 (by rfl) ⟨2993921, by rfl⟩ : syracuseStep 3991895 = 5987843) B5987843
theorem B24635735 : Blo 1182408 24635735 := bstep (se 1 (by rfl) ⟨18476801, by rfl⟩ : syracuseStep 24635735 = 36953603) B36953603
theorem B2664809 : Blo 1182408 2664809 := bstep (se 2 (by rfl) ⟨999303, by rfl⟩ : syracuseStep 2664809 = 1998607) B1998607
theorem B5990921 : Blo 1182408 5990921 := bstep (se 2 (by rfl) ⟨2246595, by rfl⟩ : syracuseStep 5990921 = 4493191) B4493191
theorem B20212253 : Blo 1182408 20212253 := bstep (se 3 (by rfl) ⟨3789797, by rfl⟩ : syracuseStep 20212253 = 7579595) B7579595
theorem B10242695 : Blo 1182408 10242695 := bstep (se 1 (by rfl) ⟨7682021, by rfl⟩ : syracuseStep 10242695 = 15364043) B15364043
theorem B15157961 : Blo 1182408 15157961 := bstep (se 2 (by rfl) ⟨5684235, by rfl⟩ : syracuseStep 15157961 = 11368471) B11368471
theorem B1182427 : Blo 1182408 1182427 := bstep (se 1 (by rfl) ⟨886820, by rfl⟩ : syracuseStep 1182427 = 1773641) B1773641
theorem B1182503 : Blo 1182408 1182503 := bstep (se 1 (by rfl) ⟨886877, by rfl⟩ : syracuseStep 1182503 = 1773755) B1773755
theorem B1182543 : Blo 1182408 1182543 := bstep (se 1 (by rfl) ⟨886907, by rfl⟩ : syracuseStep 1182543 = 1773815) B1773815
theorem B1182559 : Blo 1182408 1182559 := bstep (se 1 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 1182559 = 1773839) B1773839
theorem B1182587 : Blo 1182408 1182587 := bstep (se 1 (by rfl) ⟨886940, by rfl⟩ : syracuseStep 1182587 = 1773881) B1773881
theorem B2993071 : Blo 1182408 2993071 := bstep (se 1 (by rfl) ⟨2244803, by rfl⟩ : syracuseStep 2993071 = 4489607) B4489607
theorem B1182639 : Blo 1182408 1182639 := bstep (se 1 (by rfl) ⟨886979, by rfl⟩ : syracuseStep 1182639 = 1773959) B1773959
theorem B4492219 : Blo 1182408 4492219 := bstep (se 1 (by rfl) ⟨3369164, by rfl⟩ : syracuseStep 4492219 = 6738329) B6738329
theorem B1182663 : Blo 1182408 1182663 := bstep (se 1 (by rfl) ⟨886997, by rfl⟩ : syracuseStep 1182663 = 1773995) B1773995
theorem B1182683 : Blo 1182408 1182683 := bstep (se 1 (by rfl) ⟨887012, by rfl⟩ : syracuseStep 1182683 = 1774025) B1774025
theorem B2247689 : Blo 1182408 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B1182759 : Blo 1182408 1182759 := bstep (se 1 (by rfl) ⟨887069, by rfl⟩ : syracuseStep 1182759 = 1774139) B1774139
theorem B1182799 : Blo 1182408 1182799 := bstep (se 1 (by rfl) ⟨887099, by rfl⟩ : syracuseStep 1182799 = 1774199) B1774199
theorem B1182815 : Blo 1182408 1182815 := bstep (se 1 (by rfl) ⟨887111, by rfl⟩ : syracuseStep 1182815 = 1774223) B1774223
theorem B15174773 : Blo 1182408 15174773 := bstep (se 5 (by rfl) ⟨711317, by rfl⟩ : syracuseStep 15174773 = 1422635) B1422635
theorem B1182843 : Blo 1182408 1182843 := bstep (se 1 (by rfl) ⟨887132, by rfl⟩ : syracuseStep 1182843 = 1774265) B1774265
theorem B1182895 : Blo 1182408 1182895 := bstep (se 1 (by rfl) ⟨887171, by rfl⟩ : syracuseStep 1182895 = 1774343) B1774343
theorem B1330375 : Blo 1182408 1330375 := bstep (se 1 (by rfl) ⟨997781, by rfl⟩ : syracuseStep 1330375 = 1995563) B1995563
theorem B1182919 : Blo 1182408 1182919 := bstep (se 1 (by rfl) ⟨887189, by rfl⟩ : syracuseStep 1182919 = 1774379) B1774379
theorem B1182939 : Blo 1182408 1182939 := bstep (se 1 (by rfl) ⟨887204, by rfl⟩ : syracuseStep 1182939 = 1774409) B1774409
theorem B16207127 : Blo 1182408 16207127 := bstep (se 1 (by rfl) ⟨12155345, by rfl⟩ : syracuseStep 16207127 = 24310691) B24310691
theorem B1183015 : Blo 1182408 1183015 := bstep (se 1 (by rfl) ⟨887261, by rfl⟩ : syracuseStep 1183015 = 1774523) B1774523
theorem B1183055 : Blo 1182408 1183055 := bstep (se 1 (by rfl) ⟨887291, by rfl⟩ : syracuseStep 1183055 = 1774583) B1774583
theorem B1183071 : Blo 1182408 1183071 := bstep (se 1 (by rfl) ⟨887303, by rfl⟩ : syracuseStep 1183071 = 1774607) B1774607
theorem B1183099 : Blo 1182408 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B4263293 : Blo 1182408 4263293 := bstep (se 3 (by rfl) ⟨799367, by rfl⟩ : syracuseStep 4263293 = 1598735) B1598735
theorem B2993537 : Blo 1182408 2993537 := bstep (se 2 (by rfl) ⟨1122576, by rfl⟩ : syracuseStep 2993537 = 2245153) B2245153
theorem B3992975 : Blo 1182408 3992975 := bstep (se 1 (by rfl) ⟨2994731, by rfl⟩ : syracuseStep 3992975 = 5989463) B5989463
theorem B30764461 : Blo 1182408 30764461 := bstep (se 3 (by rfl) ⟨5768336, by rfl⟩ : syracuseStep 30764461 = 11536673) B11536673
theorem B1183151 : Blo 1182408 1183151 := bstep (se 1 (by rfl) ⟨887363, by rfl⟩ : syracuseStep 1183151 = 1774727) B1774727
theorem B1183175 : Blo 1182408 1183175 := bstep (se 1 (by rfl) ⟨887381, by rfl⟩ : syracuseStep 1183175 = 1774763) B1774763
theorem B1183195 : Blo 1182408 1183195 := bstep (se 1 (by rfl) ⟨887396, by rfl⟩ : syracuseStep 1183195 = 1774793) B1774793
theorem B1895899 : Blo 1182408 1895899 := bstep (se 1 (by rfl) ⟨1421924, by rfl⟩ : syracuseStep 1895899 = 2843849) B2843849
theorem B1183271 : Blo 1182408 1183271 := bstep (se 1 (by rfl) ⟨887453, by rfl⟩ : syracuseStep 1183271 = 1774907) B1774907
theorem B1183311 : Blo 1182408 1183311 := bstep (se 1 (by rfl) ⟨887483, by rfl⟩ : syracuseStep 1183311 = 1774967) B1774967
theorem B1183327 : Blo 1182408 1183327 := bstep (se 1 (by rfl) ⟨887495, by rfl⟩ : syracuseStep 1183327 = 1774991) B1774991
theorem B1183355 : Blo 1182408 1183355 := bstep (se 1 (by rfl) ⟨887516, by rfl⟩ : syracuseStep 1183355 = 1775033) B1775033
theorem B1183407 : Blo 1182408 1183407 := bstep (se 1 (by rfl) ⟨887555, by rfl⟩ : syracuseStep 1183407 = 1775111) B1775111
theorem B1183431 : Blo 1182408 1183431 := bstep (se 1 (by rfl) ⟨887573, by rfl⟩ : syracuseStep 1183431 = 1775147) B1775147
theorem B4493009 : Blo 1182408 4493009 := bstep (se 2 (by rfl) ⟨1684878, by rfl⟩ : syracuseStep 4493009 = 3369757) B3369757
theorem B3993299 : Blo 1182408 3993299 := bstep (se 1 (by rfl) ⟨2994974, by rfl⟩ : syracuseStep 3993299 = 5989949) B5989949
theorem B1183451 : Blo 1182408 1183451 := bstep (se 1 (by rfl) ⟨887588, by rfl⟩ : syracuseStep 1183451 = 1775177) B1775177
theorem B1183527 : Blo 1182408 1183527 := bstep (se 1 (by rfl) ⟨887645, by rfl⟩ : syracuseStep 1183527 = 1775291) B1775291
theorem B6926123 : Blo 1182408 6926123 := bstep (se 1 (by rfl) ⟨5194592, by rfl⟩ : syracuseStep 6926123 = 10389185) B10389185
theorem B2993993 : Blo 1182408 2993993 := bstep (se 2 (by rfl) ⟨1122747, by rfl⟩ : syracuseStep 2993993 = 2245495) B2245495
theorem B1183567 : Blo 1182408 1183567 := bstep (se 1 (by rfl) ⟨887675, by rfl⟩ : syracuseStep 1183567 = 1775351) B1775351
theorem B1183583 : Blo 1182408 1183583 := bstep (se 1 (by rfl) ⟨887687, by rfl⟩ : syracuseStep 1183583 = 1775375) B1775375
theorem B1183611 : Blo 1182408 1183611 := bstep (se 1 (by rfl) ⟨887708, by rfl⟩ : syracuseStep 1183611 = 1775417) B1775417
theorem B19181447 : Blo 1182408 19181447 := bstep (se 1 (by rfl) ⟨14386085, by rfl⟩ : syracuseStep 19181447 = 28772171) B28772171
theorem B1183663 : Blo 1182408 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B5992379 : Blo 1182408 5992379 := bstep (se 1 (by rfl) ⟨4494284, by rfl⟩ : syracuseStep 5992379 = 8988569) B8988569
theorem B1183687 : Blo 1182408 1183687 := bstep (se 1 (by rfl) ⟨887765, by rfl⟩ : syracuseStep 1183687 = 1775531) B1775531
theorem B1183707 : Blo 1182408 1183707 := bstep (se 1 (by rfl) ⟨887780, by rfl⟩ : syracuseStep 1183707 = 1775561) B1775561
theorem B1331239 : Blo 1182408 1331239 := bstep (se 1 (by rfl) ⟨998429, by rfl⟩ : syracuseStep 1331239 = 1996859) B1996859
theorem B1183783 : Blo 1182408 1183783 := bstep (se 1 (by rfl) ⟨887837, by rfl⟩ : syracuseStep 1183783 = 1775675) B1775675
theorem B1773647 : Blo 1182408 1773647 := bstep (se 1 (by rfl) ⟨1330235, by rfl⟩ : syracuseStep 1773647 = 2660471) B2660471
theorem B1183823 : Blo 1182408 1183823 := bstep (se 1 (by rfl) ⟨887867, by rfl⟩ : syracuseStep 1183823 = 1775735) B1775735
theorem B3600463 : Blo 1182408 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B1183839 : Blo 1182408 1183839 := bstep (se 1 (by rfl) ⟨887879, by rfl⟩ : syracuseStep 1183839 = 1775759) B1775759
theorem B1183867 : Blo 1182408 1183867 := bstep (se 1 (by rfl) ⟨887900, by rfl⟩ : syracuseStep 1183867 = 1775801) B1775801
theorem B4493465 : Blo 1182408 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B2994347 : Blo 1182408 2994347 := bstep (se 1 (by rfl) ⟨2245760, by rfl⟩ : syracuseStep 2994347 = 4491521) B4491521
theorem B1183919 : Blo 1182408 1183919 := bstep (se 1 (by rfl) ⟨887939, by rfl⟩ : syracuseStep 1183919 = 1775879) B1775879
theorem B1773767 : Blo 1182408 1773767 := bstep (se 1 (by rfl) ⟨1330325, by rfl⟩ : syracuseStep 1773767 = 2660651) B2660651
theorem B1183943 : Blo 1182408 1183943 := bstep (se 1 (by rfl) ⟨887957, by rfl⟩ : syracuseStep 1183943 = 1775915) B1775915
theorem B1183963 : Blo 1182408 1183963 := bstep (se 1 (by rfl) ⟨887972, by rfl⟩ : syracuseStep 1183963 = 1775945) B1775945
theorem B1184039 : Blo 1182408 1184039 := bstep (se 1 (by rfl) ⟨888029, by rfl⟩ : syracuseStep 1184039 = 1776059) B1776059
theorem B1184079 : Blo 1182408 1184079 := bstep (se 1 (by rfl) ⟨888059, by rfl⟩ : syracuseStep 1184079 = 1776119) B1776119
theorem B4796759 : Blo 1182408 4796759 := bstep (se 1 (by rfl) ⟨3597569, by rfl⟩ : syracuseStep 4796759 = 7195139) B7195139
theorem B1184095 : Blo 1182408 1184095 := bstep (se 1 (by rfl) ⟨888071, by rfl⟩ : syracuseStep 1184095 = 1776143) B1776143
theorem B1773929 : Blo 1182408 1773929 := bstep (se 2 (by rfl) ⟨665223, by rfl⟩ : syracuseStep 1773929 = 1330447) B1330447
theorem B1184123 : Blo 1182408 1184123 := bstep (se 1 (by rfl) ⟨888092, by rfl⟩ : syracuseStep 1184123 = 1776185) B1776185
theorem B1184175 : Blo 1182408 1184175 := bstep (se 1 (by rfl) ⟨888131, by rfl⟩ : syracuseStep 1184175 = 1776263) B1776263
theorem B1774007 : Blo 1182408 1774007 := bstep (se 1 (by rfl) ⟨1330505, by rfl⟩ : syracuseStep 1774007 = 2661011) B2661011
theorem B1184199 : Blo 1182408 1184199 := bstep (se 1 (by rfl) ⟨888149, by rfl⟩ : syracuseStep 1184199 = 1776299) B1776299
theorem B1774043 : Blo 1182408 1774043 := bstep (se 1 (by rfl) ⟨1330532, by rfl⟩ : syracuseStep 1774043 = 2661065) B2661065
theorem B1184219 : Blo 1182408 1184219 := bstep (se 1 (by rfl) ⟨888164, by rfl⟩ : syracuseStep 1184219 = 1776329) B1776329
theorem B3789337 : Blo 1182408 3789337 := bstep (se 2 (by rfl) ⟨1421001, by rfl⟩ : syracuseStep 3789337 = 2842003) B2842003
theorem B1184295 : Blo 1182408 1184295 := bstep (se 1 (by rfl) ⟨888221, by rfl⟩ : syracuseStep 1184295 = 1776443) B1776443
theorem B1184335 : Blo 1182408 1184335 := bstep (se 1 (by rfl) ⟨888251, by rfl⟩ : syracuseStep 1184335 = 1776503) B1776503
theorem B1184351 : Blo 1182408 1184351 := bstep (se 1 (by rfl) ⟨888263, by rfl⟩ : syracuseStep 1184351 = 1776527) B1776527
theorem B21607013 : Blo 1182408 21607013 := bstep (se 4 (by rfl) ⟨2025657, by rfl⟩ : syracuseStep 21607013 = 4051315) B4051315
theorem B1184379 : Blo 1182408 1184379 := bstep (se 1 (by rfl) ⟨888284, by rfl⟩ : syracuseStep 1184379 = 1776569) B1776569
theorem B68260643 : Blo 1182408 68260643 := bstep (se 1 (by rfl) ⟨51195482, by rfl⟩ : syracuseStep 68260643 = 102390965) B102390965
theorem B7582571 : Blo 1182408 7582571 := bstep (se 1 (by rfl) ⟨5686928, by rfl⟩ : syracuseStep 7582571 = 11373857) B11373857
theorem B3994487 : Blo 1182408 3994487 := bstep (se 1 (by rfl) ⟨2995865, by rfl⟩ : syracuseStep 3994487 = 5991731) B5991731
theorem B1774511 : Blo 1182408 1774511 := bstep (se 1 (by rfl) ⟨1330883, by rfl⟩ : syracuseStep 1774511 = 2661767) B2661767
theorem B2995127 : Blo 1182408 2995127 := bstep (se 1 (by rfl) ⟨2246345, by rfl⟩ : syracuseStep 2995127 = 4492691) B4492691
theorem B1774601 : Blo 1182408 1774601 := bstep (se 2 (by rfl) ⟨665475, by rfl⟩ : syracuseStep 1774601 = 1330951) B1330951
theorem B2528275 : Blo 1182408 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B5690387 : Blo 1182408 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B1774631 : Blo 1182408 1774631 := bstep (se 1 (by rfl) ⟨1330973, by rfl⟩ : syracuseStep 1774631 = 2661947) B2661947
theorem B1995833 : Blo 1182408 1995833 := bstep (se 2 (by rfl) ⟨748437, by rfl⟩ : syracuseStep 1995833 = 1496875) B1496875
theorem B3994703 : Blo 1182408 3994703 := bstep (se 1 (by rfl) ⟨2996027, by rfl⟩ : syracuseStep 3994703 = 5992055) B5992055
theorem B1774715 : Blo 1182408 1774715 := bstep (se 1 (by rfl) ⟨1331036, by rfl⟩ : syracuseStep 1774715 = 2662073) B2662073
theorem B5993675 : Blo 1182408 5993675 := bstep (se 1 (by rfl) ⟨4495256, by rfl⟩ : syracuseStep 5993675 = 8990513) B8990513
theorem B1774841 : Blo 1182408 1774841 := bstep (se 2 (by rfl) ⟨665565, by rfl⟩ : syracuseStep 1774841 = 1331131) B1331131
theorem B13661455 : Blo 1182408 13661455 := bstep (se 1 (by rfl) ⟨10246091, by rfl⟩ : syracuseStep 13661455 = 20492183) B20492183
theorem B1774943 : Blo 1182408 1774943 := bstep (se 1 (by rfl) ⟨1331207, by rfl⟩ : syracuseStep 1774943 = 2662415) B2662415
theorem B2528617 : Blo 1182408 2528617 := bstep (se 2 (by rfl) ⟨948231, by rfl⟩ : syracuseStep 2528617 = 1896463) B1896463
theorem B1774955 : Blo 1182408 1774955 := bstep (se 1 (by rfl) ⟨1331216, by rfl⟩ : syracuseStep 1774955 = 2662433) B2662433
theorem B2397583 : Blo 1182408 2397583 := bstep (se 1 (by rfl) ⟨1798187, by rfl⟩ : syracuseStep 2397583 = 3596375) B3596375
theorem B1496495 : Blo 1182408 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B3995081 : Blo 1182408 3995081 := bstep (se 2 (by rfl) ⟨1498155, by rfl⟩ : syracuseStep 3995081 = 2996311) B2996311
theorem B15152629 : Blo 1182408 15152629 := bstep (se 5 (by rfl) ⟨710279, by rfl⟩ : syracuseStep 15152629 = 1420559) B1420559
theorem B34100797 : Blo 1182408 34100797 := bstep (se 3 (by rfl) ⟨6393899, by rfl⟩ : syracuseStep 34100797 = 12787799) B12787799
theorem B1775183 : Blo 1182408 1775183 := bstep (se 1 (by rfl) ⟨1331387, by rfl⟩ : syracuseStep 1775183 = 2662775) B2662775
theorem B13473377 : Blo 1182408 13473377 := bstep (se 2 (by rfl) ⟨5052516, by rfl⟩ : syracuseStep 13473377 = 10105033) B10105033
theorem B28448405 : Blo 1182408 28448405 := bstep (se 6 (by rfl) ⟨666759, by rfl⟩ : syracuseStep 28448405 = 1333519) B1333519
theorem B1775303 : Blo 1182408 1775303 := bstep (se 1 (by rfl) ⟨1331477, by rfl⟩ : syracuseStep 1775303 = 2662955) B2662955
theorem B3995351 : Blo 1182408 3995351 := bstep (se 1 (by rfl) ⟨2996513, by rfl⟩ : syracuseStep 3995351 = 5993027) B5993027
theorem B1996535 : Blo 1182408 1996535 := bstep (se 1 (by rfl) ⟨1497401, by rfl⟩ : syracuseStep 1996535 = 2994803) B2994803
theorem B1775465 : Blo 1182408 1775465 := bstep (se 2 (by rfl) ⟨665799, by rfl⟩ : syracuseStep 1775465 = 1331599) B1331599
theorem B2996129 : Blo 1182408 2996129 := bstep (se 2 (by rfl) ⟨1123548, by rfl⟩ : syracuseStep 2996129 = 2247097) B2247097
theorem B3995567 : Blo 1182408 3995567 := bstep (se 1 (by rfl) ⟨2996675, by rfl⟩ : syracuseStep 3995567 = 5993351) B5993351
theorem B1775543 : Blo 1182408 1775543 := bstep (se 1 (by rfl) ⟨1331657, by rfl⟩ : syracuseStep 1775543 = 2663315) B2663315
theorem B1775579 : Blo 1182408 1775579 := bstep (se 1 (by rfl) ⟨1331684, by rfl⟩ : syracuseStep 1775579 = 2663369) B2663369
theorem B12793859 : Blo 1182408 12793859 := bstep (se 1 (by rfl) ⟨9595394, by rfl⟩ : syracuseStep 12793859 = 19190789) B19190789
theorem B1996879 : Blo 1182408 1996879 := bstep (se 1 (by rfl) ⟨1497659, by rfl⟩ : syracuseStep 1996879 = 2995319) B2995319
theorem B4495439 : Blo 1182408 4495439 := bstep (se 1 (by rfl) ⟨3371579, by rfl⟩ : syracuseStep 4495439 = 6743159) B6743159
theorem B5986385 : Blo 1182408 5986385 := bstep (se 2 (by rfl) ⟨2244894, by rfl⟩ : syracuseStep 5986385 = 4489789) B4489789
theorem B2398331 : Blo 1182408 2398331 := bstep (se 1 (by rfl) ⟨1798748, by rfl⟩ : syracuseStep 2398331 = 3597497) B3597497
theorem B4495607 : Blo 1182408 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B9107761 : Blo 1182408 9107761 := bstep (se 2 (by rfl) ⟨3415410, by rfl⟩ : syracuseStep 9107761 = 6830821) B6830821
theorem B15161651 : Blo 1182408 15161651 := bstep (se 1 (by rfl) ⟨11371238, by rfl⟩ : syracuseStep 15161651 = 22742477) B22742477
theorem B1997129 : Blo 1182408 1997129 := bstep (se 2 (by rfl) ⟨748923, by rfl⟩ : syracuseStep 1997129 = 1497847) B1497847
theorem B4323689 : Blo 1182408 4323689 := bstep (se 2 (by rfl) ⟨1621383, by rfl⟩ : syracuseStep 4323689 = 3242767) B3242767
theorem B2996585 : Blo 1182408 2996585 := bstep (se 2 (by rfl) ⟨1123719, by rfl⟩ : syracuseStep 2996585 = 2247439) B2247439
theorem B3791233 : Blo 1182408 3791233 := bstep (se 2 (by rfl) ⟨1421712, by rfl⟩ : syracuseStep 3791233 = 2843425) B2843425
theorem B1776047 : Blo 1182408 1776047 := bstep (se 1 (by rfl) ⟨1332035, by rfl⟩ : syracuseStep 1776047 = 2664071) B2664071
theorem B1776137 : Blo 1182408 1776137 := bstep (se 2 (by rfl) ⟨666051, by rfl⟩ : syracuseStep 1776137 = 1332103) B1332103
theorem B2660903 : Blo 1182408 2660903 := bstep (se 1 (by rfl) ⟨1995677, by rfl⟩ : syracuseStep 2660903 = 3991355) B3991355
theorem B1776167 : Blo 1182408 1776167 := bstep (se 1 (by rfl) ⟨1332125, by rfl⟩ : syracuseStep 1776167 = 2664251) B2664251
theorem B2398817 : Blo 1182408 2398817 := bstep (se 2 (by rfl) ⟨899556, by rfl⟩ : syracuseStep 2398817 = 1799113) B1799113
theorem B1776251 : Blo 1182408 1776251 := bstep (se 1 (by rfl) ⟨1332188, by rfl⟩ : syracuseStep 1776251 = 2664377) B2664377
theorem B13490873 : Blo 1182408 13490873 := bstep (se 2 (by rfl) ⟨5059077, by rfl⟩ : syracuseStep 13490873 = 10118155) B10118155
theorem B4266695 : Blo 1182408 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B1997561 : Blo 1182408 1997561 := bstep (se 2 (by rfl) ⟨749085, by rfl⟩ : syracuseStep 1997561 = 1498171) B1498171
theorem B1776377 : Blo 1182408 1776377 := bstep (se 2 (by rfl) ⟨666141, by rfl⟩ : syracuseStep 1776377 = 1332283) B1332283
theorem B1776479 : Blo 1182408 1776479 := bstep (se 1 (by rfl) ⟨1332359, by rfl⟩ : syracuseStep 1776479 = 2664719) B2664719
theorem B2661227 : Blo 1182408 2661227 := bstep (se 1 (by rfl) ⟨1995920, by rfl⟩ : syracuseStep 2661227 = 3991841) B3991841
theorem B1776491 : Blo 1182408 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B3791735 : Blo 1182408 3791735 := bstep (se 1 (by rfl) ⟨2843801, by rfl⟩ : syracuseStep 3791735 = 5687603) B5687603
theorem B2661281 : Blo 1182408 2661281 := bstep (se 2 (by rfl) ⟨997980, by rfl⟩ : syracuseStep 2661281 = 1995961) B1995961
theorem B1997743 : Blo 1182408 1997743 := bstep (se 1 (by rfl) ⟨1498307, by rfl⟩ : syracuseStep 1997743 = 2996615) B2996615
theorem B3414971 : Blo 1182408 3414971 := bstep (se 1 (by rfl) ⟨2561228, by rfl⟩ : syracuseStep 3414971 = 5122457) B5122457
theorem B1997831 : Blo 1182408 1997831 := bstep (se 1 (by rfl) ⟨1498373, by rfl⟩ : syracuseStep 1997831 = 2996747) B2996747
theorem B3791951 : Blo 1182408 3791951 := bstep (se 1 (by rfl) ⟨2843963, by rfl⟩ : syracuseStep 3791951 = 5687927) B5687927
theorem B64773269 : Blo 1182408 64773269 := bstep (se 6 (by rfl) ⟨1518123, by rfl⟩ : syracuseStep 64773269 = 3036247) B3036247
theorem B4496579 : Blo 1182408 4496579 := bstep (se 1 (by rfl) ⟨3372434, by rfl⟩ : syracuseStep 4496579 = 6744869) B6744869
theorem B2661623 : Blo 1182408 2661623 := bstep (se 1 (by rfl) ⟨1996217, by rfl⟩ : syracuseStep 2661623 = 3992435) B3992435
theorem B22756625 : Blo 1182408 22756625 := bstep (se 2 (by rfl) ⟨8533734, by rfl⟩ : syracuseStep 22756625 = 17067469) B17067469
theorem B17530201 : Blo 1182408 17530201 := bstep (se 2 (by rfl) ⟨6573825, by rfl⟩ : syracuseStep 17530201 = 13147651) B13147651
theorem B1998175 : Blo 1182408 1998175 := bstep (se 1 (by rfl) ⟨1498631, by rfl⟩ : syracuseStep 1998175 = 2997263) B2997263
theorem B4799873 : Blo 1182408 4799873 := bstep (se 2 (by rfl) ⟨1799952, by rfl⟩ : syracuseStep 4799873 = 3599905) B3599905
theorem B1998263 : Blo 1182408 1998263 := bstep (se 1 (by rfl) ⟨1498697, by rfl⟩ : syracuseStep 1998263 = 2997395) B2997395
theorem B5684681 : Blo 1182408 5684681 := bstep (se 2 (by rfl) ⟨2131755, by rfl⟩ : syracuseStep 5684681 = 4263511) B4263511
theorem B5397961 : Blo 1182408 5397961 := bstep (se 2 (by rfl) ⟨2024235, by rfl⟩ : syracuseStep 5397961 = 4048471) B4048471
theorem B2997769 : Blo 1182408 2997769 := bstep (se 2 (by rfl) ⟨1124163, by rfl⟩ : syracuseStep 2997769 = 2248327) B2248327
theorem B5684833 : Blo 1182408 5684833 := bstep (se 2 (by rfl) ⟨2131812, by rfl⟩ : syracuseStep 5684833 = 4263625) B4263625
theorem B2842235 : Blo 1182408 2842235 := bstep (se 1 (by rfl) ⟨2131676, by rfl⟩ : syracuseStep 2842235 = 4263353) B4263353
theorem B7585595 : Blo 1182408 7585595 := bstep (se 1 (by rfl) ⟨5689196, by rfl⟩ : syracuseStep 7585595 = 11378393) B11378393
theorem B2662217 : Blo 1182408 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B16195463 : Blo 1182408 16195463 := bstep (se 1 (by rfl) ⟨12146597, by rfl⟩ : syracuseStep 16195463 = 24293195) B24293195
theorem B6741953 : Blo 1182408 6741953 := bstep (se 2 (by rfl) ⟨2528232, by rfl⟩ : syracuseStep 6741953 = 5056465) B5056465
theorem B2662505 : Blo 1182408 2662505 := bstep (se 2 (by rfl) ⟨998439, by rfl⟩ : syracuseStep 2662505 = 1996879) B1996879
theorem B4800617 : Blo 1182408 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B3367241 : Blo 1182408 3367241 := bstep (se 2 (by rfl) ⟨1262715, by rfl⟩ : syracuseStep 3367241 = 2525431) B2525431
theorem B12140887 : Blo 1182408 12140887 := bstep (se 1 (by rfl) ⟨9105665, by rfl⟩ : syracuseStep 12140887 = 18211331) B18211331
theorem B4800875 : Blo 1182408 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B5054977 : Blo 1182408 5054977 := bstep (se 2 (by rfl) ⟨1895616, by rfl⟩ : syracuseStep 5054977 = 3791233) B3791233
theorem B45507095 : Blo 1182408 45507095 := bstep (se 1 (by rfl) ⟨34130321, by rfl⟩ : syracuseStep 45507095 = 68260643) B68260643
theorem B5055047 : Blo 1182408 5055047 := bstep (se 1 (by rfl) ⟨3791285, by rfl⟩ : syracuseStep 5055047 = 7582571) B7582571
theorem B2662991 : Blo 1182408 2662991 := bstep (se 1 (by rfl) ⟨1997243, by rfl⟩ : syracuseStep 2662991 = 3994487) B3994487
theorem B3793591 : Blo 1182408 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B2663135 : Blo 1182408 2663135 := bstep (se 1 (by rfl) ⟨1997351, by rfl⟩ : syracuseStep 2663135 = 3994703) B3994703
theorem B4490063 : Blo 1182408 4490063 := bstep (se 1 (by rfl) ⟨3367547, by rfl⟩ : syracuseStep 4490063 = 6735095) B6735095
theorem B2663387 : Blo 1182408 2663387 := bstep (se 1 (by rfl) ⟨1997540, by rfl⟩ : syracuseStep 2663387 = 3995081) B3995081
theorem B18965603 : Blo 1182408 18965603 := bstep (se 1 (by rfl) ⟨14224202, by rfl⟩ : syracuseStep 18965603 = 28448405) B28448405
theorem B3990653 : Blo 1182408 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B2663567 : Blo 1182408 2663567 := bstep (se 1 (by rfl) ⟨1997675, by rfl⟩ : syracuseStep 2663567 = 3995351) B3995351
theorem B3990761 : Blo 1182408 3990761 := bstep (se 2 (by rfl) ⟨1496535, by rfl⟩ : syracuseStep 3990761 = 2993071) B2993071
theorem B2663657 : Blo 1182408 2663657 := bstep (se 2 (by rfl) ⟨998871, by rfl⟩ : syracuseStep 2663657 = 1997743) B1997743
theorem B5989625 : Blo 1182408 5989625 := bstep (se 2 (by rfl) ⟨2246109, by rfl⟩ : syracuseStep 5989625 = 4492219) B4492219
theorem B2663711 : Blo 1182408 2663711 := bstep (se 1 (by rfl) ⟨1997783, by rfl⟩ : syracuseStep 2663711 = 3995567) B3995567
theorem B5768491 : Blo 1182408 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B8529239 : Blo 1182408 8529239 := bstep (se 1 (by rfl) ⟨6396929, by rfl⟩ : syracuseStep 8529239 = 12793859) B12793859
theorem B8979821 : Blo 1182408 8979821 := bstep (se 3 (by rfl) ⟨1683716, by rfl⟩ : syracuseStep 8979821 = 3367433) B3367433
theorem B6489467 : Blo 1182408 6489467 := bstep (se 1 (by rfl) ⟨4867100, by rfl⟩ : syracuseStep 6489467 = 9734201) B9734201
theorem B3990923 : Blo 1182408 3990923 := bstep (se 1 (by rfl) ⟨2993192, by rfl⟩ : syracuseStep 3990923 = 5986385) B5986385
theorem B1598887 : Blo 1182408 1598887 := bstep (se 1 (by rfl) ⟨1199165, by rfl⟩ : syracuseStep 1598887 = 2398331) B2398331
theorem B27313853 : Blo 1182408 27313853 := bstep (se 3 (by rfl) ⟨5121347, by rfl⟩ : syracuseStep 27313853 = 10242695) B10242695
theorem B1599211 : Blo 1182408 1599211 := bstep (se 1 (by rfl) ⟨1199408, by rfl⟩ : syracuseStep 1599211 = 2398817) B2398817
theorem B2664233 : Blo 1182408 2664233 := bstep (se 2 (by rfl) ⟨999087, by rfl⟩ : syracuseStep 2664233 = 1998175) B1998175
theorem B41019281 : Blo 1182408 41019281 := bstep (se 2 (by rfl) ⟨15382230, by rfl⟩ : syracuseStep 41019281 = 30764461) B30764461
theorem B20203505 : Blo 1182408 20203505 := bstep (se 2 (by rfl) ⟨7576314, by rfl⟩ : syracuseStep 20203505 = 15152629) B15152629
theorem B45467729 : Blo 1182408 45467729 := bstep (se 2 (by rfl) ⟨17050398, by rfl⟩ : syracuseStep 45467729 = 34100797) B34100797
theorem B43182179 : Blo 1182408 43182179 := bstep (se 1 (by rfl) ⟨32386634, by rfl⟩ : syracuseStep 43182179 = 64773269) B64773269
theorem B7579777 : Blo 1182408 7579777 := bstep (se 2 (by rfl) ⟨2842416, by rfl⟩ : syracuseStep 7579777 = 5684833) B5684833
theorem B1894823 : Blo 1182408 1894823 := bstep (se 1 (by rfl) ⟨1421117, by rfl⟩ : syracuseStep 1894823 = 2842235) B2842235
theorem B5057063 : Blo 1182408 5057063 := bstep (se 1 (by rfl) ⟨3792797, by rfl⟩ : syracuseStep 5057063 = 7585595) B7585595
theorem B1182431 : Blo 1182408 1182431 := bstep (se 1 (by rfl) ⟨886823, by rfl⟩ : syracuseStep 1182431 = 1773647) B1773647
theorem B1182511 : Blo 1182408 1182511 := bstep (se 1 (by rfl) ⟨886883, by rfl⟩ : syracuseStep 1182511 = 1773767) B1773767
theorem B3197839 : Blo 1182408 3197839 := bstep (se 1 (by rfl) ⟨2398379, by rfl⟩ : syracuseStep 3197839 = 4796759) B4796759
theorem B5057423 : Blo 1182408 5057423 := bstep (se 1 (by rfl) ⟨3793067, by rfl⟩ : syracuseStep 5057423 = 7586135) B7586135
theorem B2993051 : Blo 1182408 2993051 := bstep (se 1 (by rfl) ⟨2244788, by rfl⟩ : syracuseStep 2993051 = 4489577) B4489577
theorem B1182619 : Blo 1182408 1182619 := bstep (se 1 (by rfl) ⟨886964, by rfl⟩ : syracuseStep 1182619 = 1773929) B1773929
theorem B3369883 : Blo 1182408 3369883 := bstep (se 1 (by rfl) ⟨2527412, by rfl⟩ : syracuseStep 3369883 = 5054825) B5054825
theorem B1182671 : Blo 1182408 1182671 := bstep (se 1 (by rfl) ⟨887003, by rfl⟩ : syracuseStep 1182671 = 1774007) B1774007
theorem B1182695 : Blo 1182408 1182695 := bstep (se 1 (by rfl) ⟨887021, by rfl⟩ : syracuseStep 1182695 = 1774043) B1774043
theorem B12143681 : Blo 1182408 12143681 := bstep (se 2 (by rfl) ⟨4553880, by rfl⟩ : syracuseStep 12143681 = 9107761) B9107761
theorem B14404675 : Blo 1182408 14404675 := bstep (se 1 (by rfl) ⟨10803506, by rfl⟩ : syracuseStep 14404675 = 21607013) B21607013
theorem B6827123 : Blo 1182408 6827123 := bstep (se 1 (by rfl) ⟨5120342, by rfl⟩ : syracuseStep 6827123 = 10240685) B10240685
theorem B6401213 : Blo 1182408 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B2993395 : Blo 1182408 2993395 := bstep (se 1 (by rfl) ⟨2245046, by rfl⟩ : syracuseStep 2993395 = 4490093) B4490093
theorem B1183007 : Blo 1182408 1183007 := bstep (se 1 (by rfl) ⟨887255, by rfl⟩ : syracuseStep 1183007 = 1774511) B1774511
theorem B1183067 : Blo 1182408 1183067 := bstep (se 1 (by rfl) ⟨887300, by rfl⟩ : syracuseStep 1183067 = 1774601) B1774601
theorem B1183087 : Blo 1182408 1183087 := bstep (se 1 (by rfl) ⟨887315, by rfl⟩ : syracuseStep 1183087 = 1774631) B1774631
theorem B1330555 : Blo 1182408 1330555 := bstep (se 1 (by rfl) ⟨997916, by rfl⟩ : syracuseStep 1330555 = 1995833) B1995833
theorem B1183143 : Blo 1182408 1183143 := bstep (se 1 (by rfl) ⟨887357, by rfl⟩ : syracuseStep 1183143 = 1774715) B1774715
theorem B1183227 : Blo 1182408 1183227 := bstep (se 1 (by rfl) ⟨887420, by rfl⟩ : syracuseStep 1183227 = 1774841) B1774841
theorem B1183295 : Blo 1182408 1183295 := bstep (se 1 (by rfl) ⟨887471, by rfl⟩ : syracuseStep 1183295 = 1774943) B1774943
theorem B1183303 : Blo 1182408 1183303 := bstep (se 1 (by rfl) ⟨887477, by rfl⟩ : syracuseStep 1183303 = 1774955) B1774955
theorem B1183455 : Blo 1182408 1183455 := bstep (se 1 (by rfl) ⟨887591, by rfl⟩ : syracuseStep 1183455 = 1775183) B1775183
theorem B8982251 : Blo 1182408 8982251 := bstep (se 1 (by rfl) ⟨6736688, by rfl⟩ : syracuseStep 8982251 = 13473377) B13473377
theorem B1183535 : Blo 1182408 1183535 := bstep (se 1 (by rfl) ⟨887651, by rfl⟩ : syracuseStep 1183535 = 1775303) B1775303
theorem B1331023 : Blo 1182408 1331023 := bstep (se 1 (by rfl) ⟨998267, by rfl⟩ : syracuseStep 1331023 = 1996535) B1996535
theorem B1183643 : Blo 1182408 1183643 := bstep (se 1 (by rfl) ⟨887732, by rfl⟩ : syracuseStep 1183643 = 1775465) B1775465
theorem B1183695 : Blo 1182408 1183695 := bstep (se 1 (by rfl) ⟨887771, by rfl⟩ : syracuseStep 1183695 = 1775543) B1775543
theorem B1183719 : Blo 1182408 1183719 := bstep (se 1 (by rfl) ⟨887789, by rfl⟩ : syracuseStep 1183719 = 1775579) B1775579
theorem B2994185 : Blo 1182408 2994185 := bstep (se 2 (by rfl) ⟨1122819, by rfl⟩ : syracuseStep 2994185 = 2245639) B2245639
theorem B3371033 : Blo 1182408 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B1331419 : Blo 1182408 1331419 := bstep (se 1 (by rfl) ⟨998564, by rfl⟩ : syracuseStep 1331419 = 1997129) B1997129
theorem B1773833 : Blo 1182408 1773833 := bstep (se 2 (by rfl) ⟨665187, by rfl⟩ : syracuseStep 1773833 = 1330375) B1330375
theorem B1184031 : Blo 1182408 1184031 := bstep (se 1 (by rfl) ⟨888023, by rfl⟩ : syracuseStep 1184031 = 1776047) B1776047
theorem B3993947 : Blo 1182408 3993947 := bstep (se 1 (by rfl) ⟨2995460, by rfl⟩ : syracuseStep 3993947 = 5990921) B5990921
theorem B1184091 : Blo 1182408 1184091 := bstep (se 1 (by rfl) ⟨888068, by rfl⟩ : syracuseStep 1184091 = 1776137) B1776137
theorem B18215273 : Blo 1182408 18215273 := bstep (se 2 (by rfl) ⟨6830727, by rfl⟩ : syracuseStep 18215273 = 13661455) B13661455
theorem B1773935 : Blo 1182408 1773935 := bstep (se 1 (by rfl) ⟨1330451, by rfl⟩ : syracuseStep 1773935 = 2660903) B2660903
theorem B1184111 : Blo 1182408 1184111 := bstep (se 1 (by rfl) ⟨888083, by rfl⟩ : syracuseStep 1184111 = 1776167) B1776167
theorem B1184167 : Blo 1182408 1184167 := bstep (se 1 (by rfl) ⟨888125, by rfl⟩ : syracuseStep 1184167 = 1776251) B1776251
theorem B10105307 : Blo 1182408 10105307 := bstep (se 1 (by rfl) ⟨7578980, by rfl⟩ : syracuseStep 10105307 = 15157961) B15157961
theorem B3371489 : Blo 1182408 3371489 := bstep (se 2 (by rfl) ⟨1264308, by rfl⟩ : syracuseStep 3371489 = 2528617) B2528617
theorem B1331707 : Blo 1182408 1331707 := bstep (se 1 (by rfl) ⟨998780, by rfl⟩ : syracuseStep 1331707 = 1997561) B1997561
theorem B1184251 : Blo 1182408 1184251 := bstep (se 1 (by rfl) ⟨888188, by rfl⟩ : syracuseStep 1184251 = 1776377) B1776377
theorem B1184319 : Blo 1182408 1184319 := bstep (se 1 (by rfl) ⟨888239, by rfl⟩ : syracuseStep 1184319 = 1776479) B1776479
theorem B1774151 : Blo 1182408 1774151 := bstep (se 1 (by rfl) ⟨1330613, by rfl⟩ : syracuseStep 1774151 = 2661227) B2661227
theorem B1184327 : Blo 1182408 1184327 := bstep (se 1 (by rfl) ⟨888245, by rfl⟩ : syracuseStep 1184327 = 1776491) B1776491
theorem B2527823 : Blo 1182408 2527823 := bstep (se 1 (by rfl) ⟨1895867, by rfl⟩ : syracuseStep 2527823 = 3791735) B3791735
theorem B7197281 : Blo 1182408 7197281 := bstep (se 2 (by rfl) ⟨2698980, by rfl⟩ : syracuseStep 7197281 = 5397961) B5397961
theorem B1774187 : Blo 1182408 1774187 := bstep (se 1 (by rfl) ⟨1330640, by rfl⟩ : syracuseStep 1774187 = 2661281) B2661281
theorem B2527865 : Blo 1182408 2527865 := bstep (se 2 (by rfl) ⟨947949, by rfl⟩ : syracuseStep 2527865 = 1895899) B1895899
theorem B1331887 : Blo 1182408 1331887 := bstep (se 1 (by rfl) ⟨998915, by rfl⟩ : syracuseStep 1331887 = 1997831) B1997831
theorem B2527967 : Blo 1182408 2527967 := bstep (se 1 (by rfl) ⟨1895975, by rfl⟩ : syracuseStep 2527967 = 3791951) B3791951
theorem B1774415 : Blo 1182408 1774415 := bstep (se 1 (by rfl) ⟨1330811, by rfl⟩ : syracuseStep 1774415 = 2661623) B2661623
theorem B1995691 : Blo 1182408 1995691 := bstep (se 1 (by rfl) ⟨1496768, by rfl⟩ : syracuseStep 1995691 = 2993537) B2993537
theorem B3199915 : Blo 1182408 3199915 := bstep (se 1 (by rfl) ⟨2399936, by rfl⟩ : syracuseStep 3199915 = 4799873) B4799873
theorem B1332175 : Blo 1182408 1332175 := bstep (se 1 (by rfl) ⟨999131, by rfl⟩ : syracuseStep 1332175 = 1998263) B1998263
theorem B3789787 : Blo 1182408 3789787 := bstep (se 1 (by rfl) ⟨2842340, by rfl⟩ : syracuseStep 3789787 = 5684681) B5684681
theorem B2995339 : Blo 1182408 2995339 := bstep (se 1 (by rfl) ⟨2246504, by rfl⟩ : syracuseStep 2995339 = 4493009) B4493009
theorem B8983709 : Blo 1182408 8983709 := bstep (se 3 (by rfl) ⟨1684445, by rfl⟩ : syracuseStep 8983709 = 3368891) B3368891
theorem B9106589 : Blo 1182408 9106589 := bstep (se 3 (by rfl) ⟨1707485, by rfl⟩ : syracuseStep 9106589 = 3414971) B3414971
theorem B4617415 : Blo 1182408 4617415 := bstep (se 1 (by rfl) ⟨3463061, by rfl⟩ : syracuseStep 4617415 = 6926123) B6926123
theorem B1995995 : Blo 1182408 1995995 := bstep (se 1 (by rfl) ⟨1496996, by rfl⟩ : syracuseStep 1995995 = 2993993) B2993993
theorem B1774811 : Blo 1182408 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B3994919 : Blo 1182408 3994919 := bstep (se 1 (by rfl) ⟨2996189, by rfl⟩ : syracuseStep 3994919 = 5992379) B5992379
theorem B4494635 : Blo 1182408 4494635 := bstep (se 1 (by rfl) ⟨3370976, by rfl⟩ : syracuseStep 4494635 = 6741953) B6741953
theorem B4265311 : Blo 1182408 4265311 := bstep (se 1 (by rfl) ⟨3198983, by rfl⟩ : syracuseStep 4265311 = 6397967) B6397967
theorem B5993837 : Blo 1182408 5993837 := bstep (se 3 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 5993837 = 2247689) B2247689
theorem B1774985 : Blo 1182408 1774985 := bstep (se 2 (by rfl) ⟨665619, by rfl⟩ : syracuseStep 1774985 = 1331239) B1331239
theorem B2995643 : Blo 1182408 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B1996231 : Blo 1182408 1996231 := bstep (se 1 (by rfl) ⟨1497173, by rfl⟩ : syracuseStep 1996231 = 2994347) B2994347
theorem B1496647 : Blo 1182408 1496647 := bstep (se 1 (by rfl) ⟨1122485, by rfl⟩ : syracuseStep 1496647 = 2244971) B2244971
theorem B12785339 : Blo 1182408 12785339 := bstep (se 1 (by rfl) ⟨9589004, by rfl⟩ : syracuseStep 12785339 = 19178009) B19178009
theorem B5052091 : Blo 1182408 5052091 := bstep (se 1 (by rfl) ⟨3789068, by rfl⟩ : syracuseStep 5052091 = 7578137) B7578137
theorem B1775339 : Blo 1182408 1775339 := bstep (se 1 (by rfl) ⟨1331504, by rfl⟩ : syracuseStep 1775339 = 2663009) B2663009
theorem B1996751 : Blo 1182408 1996751 := bstep (se 1 (by rfl) ⟨1497563, by rfl⟩ : syracuseStep 1996751 = 2995127) B2995127
theorem B1775567 : Blo 1182408 1775567 := bstep (se 1 (by rfl) ⟨1331675, by rfl⟩ : syracuseStep 1775567 = 2663351) B2663351
theorem B5052449 : Blo 1182408 5052449 := bstep (se 2 (by rfl) ⟨1894668, by rfl⟩ : syracuseStep 5052449 = 3789337) B3789337
theorem B3995783 : Blo 1182408 3995783 := bstep (se 1 (by rfl) ⟨2996837, by rfl⟩ : syracuseStep 3995783 = 5993675) B5993675
theorem B9115895 : Blo 1182408 9115895 := bstep (se 1 (by rfl) ⟨6836921, by rfl⟩ : syracuseStep 9115895 = 13673843) B13673843
theorem B3201353 : Blo 1182408 3201353 := bstep (se 2 (by rfl) ⟨1200507, by rfl⟩ : syracuseStep 3201353 = 2401015) B2401015
theorem B1775963 : Blo 1182408 1775963 := bstep (se 1 (by rfl) ⟨1331972, by rfl⟩ : syracuseStep 1775963 = 2663945) B2663945
theorem B1497467 : Blo 1182408 1497467 := bstep (se 1 (by rfl) ⟨1123100, by rfl⟩ : syracuseStep 1497467 = 2246201) B2246201
theorem B4266407 : Blo 1182408 4266407 := bstep (se 1 (by rfl) ⟨3199805, by rfl⟩ : syracuseStep 4266407 = 6399611) B6399611
theorem B1776191 : Blo 1182408 1776191 := bstep (se 1 (by rfl) ⟨1332143, by rfl⟩ : syracuseStep 1776191 = 2664287) B2664287
theorem B1997419 : Blo 1182408 1997419 := bstep (se 1 (by rfl) ⟨1498064, by rfl⟩ : syracuseStep 1997419 = 2996129) B2996129
theorem B2661047 : Blo 1182408 2661047 := bstep (se 1 (by rfl) ⟨1995785, by rfl⟩ : syracuseStep 2661047 = 3991571) B3991571
theorem B1776311 : Blo 1182408 1776311 := bstep (se 1 (by rfl) ⟨1332233, by rfl⟩ : syracuseStep 1776311 = 2664467) B2664467
theorem B2996959 : Blo 1182408 2996959 := bstep (se 1 (by rfl) ⟨2247719, by rfl⟩ : syracuseStep 2996959 = 4495439) B4495439
theorem B2997071 : Blo 1182408 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B10107767 : Blo 1182408 10107767 := bstep (se 1 (by rfl) ⟨7580825, by rfl⟩ : syracuseStep 10107767 = 15161651) B15161651
theorem B2661263 : Blo 1182408 2661263 := bstep (se 1 (by rfl) ⟨1995947, by rfl⟩ : syracuseStep 2661263 = 3991895) B3991895
theorem B16423823 : Blo 1182408 16423823 := bstep (se 1 (by rfl) ⟨12317867, by rfl⟩ : syracuseStep 16423823 = 24635735) B24635735
theorem B2882459 : Blo 1182408 2882459 := bstep (se 1 (by rfl) ⟨2161844, by rfl⟩ : syracuseStep 2882459 = 4323689) B4323689
theorem B1997723 : Blo 1182408 1997723 := bstep (se 1 (by rfl) ⟨1498292, by rfl⟩ : syracuseStep 1997723 = 2996585) B2996585
theorem B1776539 : Blo 1182408 1776539 := bstep (se 1 (by rfl) ⟨1332404, by rfl⟩ : syracuseStep 1776539 = 2664809) B2664809
theorem B13474835 : Blo 1182408 13474835 := bstep (se 1 (by rfl) ⟨10106126, by rfl⟩ : syracuseStep 13474835 = 20212253) B20212253
theorem B8993915 : Blo 1182408 8993915 := bstep (se 1 (by rfl) ⟨6745436, by rfl⟩ : syracuseStep 8993915 = 13490873) B13490873
theorem B93494405 : Blo 1182408 93494405 := bstep (se 4 (by rfl) ⟨8765100, by rfl⟩ : syracuseStep 93494405 = 17530201) B17530201
theorem B11377853 : Blo 1182408 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B5987681 : Blo 1182408 5987681 := bstep (se 2 (by rfl) ⟨2245380, by rfl⟩ : syracuseStep 5987681 = 4490761) B4490761
theorem B3997025 : Blo 1182408 3997025 := bstep (se 2 (by rfl) ⟨1498884, by rfl⟩ : syracuseStep 3997025 = 2997769) B2997769
theorem B10116515 : Blo 1182408 10116515 := bstep (se 1 (by rfl) ⟨7587386, by rfl⟩ : syracuseStep 10116515 = 15174773) B15174773
theorem B12787109 : Blo 1182408 12787109 := bstep (se 4 (by rfl) ⟨1198791, by rfl⟩ : syracuseStep 12787109 = 2397583) B2397583
theorem B2997719 : Blo 1182408 2997719 := bstep (se 1 (by rfl) ⟨2248289, by rfl⟩ : syracuseStep 2997719 = 4496579) B4496579
theorem B15171083 : Blo 1182408 15171083 := bstep (se 1 (by rfl) ⟨11378312, by rfl⟩ : syracuseStep 15171083 = 22756625) B22756625
theorem B10804751 : Blo 1182408 10804751 := bstep (se 1 (by rfl) ⟨8103563, by rfl⟩ : syracuseStep 10804751 = 16207127) B16207127
theorem B2842195 : Blo 1182408 2842195 := bstep (se 1 (by rfl) ⟨2131646, by rfl⟩ : syracuseStep 2842195 = 4263293) B4263293
theorem B2661983 : Blo 1182408 2661983 := bstep (se 1 (by rfl) ⟨1996487, by rfl⟩ : syracuseStep 2661983 = 3992975) B3992975
theorem B2662199 : Blo 1182408 2662199 := bstep (se 1 (by rfl) ⟨1996649, by rfl⟩ : syracuseStep 2662199 = 3993299) B3993299
theorem B12787631 : Blo 1182408 12787631 := bstep (se 1 (by rfl) ⟨9590723, by rfl⟩ : syracuseStep 12787631 = 19181447) B19181447
theorem B10796975 : Blo 1182408 10796975 := bstep (se 1 (by rfl) ⟨8097731, by rfl⟩ : syracuseStep 10796975 = 16195463) B16195463
theorem B2244827 : Blo 1182408 2244827 := bstep (se 1 (by rfl) ⟨1683620, by rfl⟩ : syracuseStep 2244827 = 3367241) B3367241
theorem B2662631 : Blo 1182408 2662631 := bstep (se 1 (by rfl) ⟨1996973, by rfl⟩ : syracuseStep 2662631 = 3993947) B3993947
theorem B16187849 : Blo 1182408 16187849 := bstep (se 2 (by rfl) ⟨6070443, by rfl⟩ : syracuseStep 16187849 = 12140887) B12140887
theorem B5989139 : Blo 1182408 5989139 := bstep (se 1 (by rfl) ⟨4491854, by rfl⟩ : syracuseStep 5989139 = 8983709) B8983709
theorem B6071059 : Blo 1182408 6071059 := bstep (se 1 (by rfl) ⟨4553294, by rfl⟩ : syracuseStep 6071059 = 9106589) B9106589
theorem B2663225 : Blo 1182408 2663225 := bstep (se 2 (by rfl) ⟨998709, by rfl⟩ : syracuseStep 2663225 = 1997419) B1997419
theorem B2663279 : Blo 1182408 2663279 := bstep (se 1 (by rfl) ⟨1997459, by rfl⟩ : syracuseStep 2663279 = 3994919) B3994919
theorem B5686159 : Blo 1182408 5686159 := bstep (se 1 (by rfl) ⟨4264619, by rfl⟩ : syracuseStep 5686159 = 8529239) B8529239
theorem B4326311 : Blo 1182408 4326311 := bstep (se 1 (by rfl) ⟨3244733, by rfl⟩ : syracuseStep 4326311 = 6489467) B6489467
theorem B24626213 : Blo 1182408 24626213 := bstep (se 4 (by rfl) ⟨2308707, by rfl⟩ : syracuseStep 24626213 = 4617415) B4617415
theorem B27346187 : Blo 1182408 27346187 := bstep (se 1 (by rfl) ⟨20509640, by rfl⟩ : syracuseStep 27346187 = 41019281) B41019281
theorem B13469003 : Blo 1182408 13469003 := bstep (se 1 (by rfl) ⟨10101752, by rfl⟩ : syracuseStep 13469003 = 20203505) B20203505
theorem B3368299 : Blo 1182408 3368299 := bstep (se 1 (by rfl) ⟨2526224, by rfl⟩ : syracuseStep 3368299 = 5052449) B5052449
theorem B30311819 : Blo 1182408 30311819 := bstep (se 1 (by rfl) ⟨22733864, by rfl⟩ : syracuseStep 30311819 = 45467729) B45467729
theorem B28788119 : Blo 1182408 28788119 := bstep (se 1 (by rfl) ⟨21591089, by rfl⟩ : syracuseStep 28788119 = 43182179) B43182179
theorem B2663855 : Blo 1182408 2663855 := bstep (se 1 (by rfl) ⟨1997891, by rfl⟩ : syracuseStep 2663855 = 3995783) B3995783
theorem B1263215 : Blo 1182408 1263215 := bstep (se 1 (by rfl) ⟨947411, by rfl⟩ : syracuseStep 1263215 = 1894823) B1894823
theorem B2844271 : Blo 1182408 2844271 := bstep (se 1 (by rfl) ⟨2133203, by rfl⟩ : syracuseStep 2844271 = 4266407) B4266407
theorem B3991193 : Blo 1182408 3991193 := bstep (se 2 (by rfl) ⟨1496697, by rfl⟩ : syracuseStep 3991193 = 2993395) B2993395
theorem B5687081 : Blo 1182408 5687081 := bstep (se 2 (by rfl) ⟨2132655, by rfl⟩ : syracuseStep 5687081 = 4265311) B4265311
theorem B2131849 : Blo 1182408 2131849 := bstep (se 2 (by rfl) ⟨799443, by rfl⟩ : syracuseStep 2131849 = 1598887) B1598887
theorem B8095787 : Blo 1182408 8095787 := bstep (se 1 (by rfl) ⟨6071840, by rfl⟩ : syracuseStep 8095787 = 12143681) B12143681
theorem B3991787 : Blo 1182408 3991787 := bstep (se 1 (by rfl) ⟨2993840, by rfl⟩ : syracuseStep 3991787 = 5987681) B5987681
theorem B2664683 : Blo 1182408 2664683 := bstep (se 1 (by rfl) ⟨1998512, by rfl⟩ : syracuseStep 2664683 = 3997025) B3997025
theorem B6736121 : Blo 1182408 6736121 := bstep (se 2 (by rfl) ⟨2526045, by rfl⟩ : syracuseStep 6736121 = 5052091) B5052091
theorem B6744343 : Blo 1182408 6744343 := bstep (se 1 (by rfl) ⟨5058257, by rfl⟩ : syracuseStep 6744343 = 10116515) B10116515
theorem B2132281 : Blo 1182408 2132281 := bstep (se 2 (by rfl) ⟨799605, by rfl⟩ : syracuseStep 2132281 = 1599211) B1599211
theorem B7203167 : Blo 1182408 7203167 := bstep (se 1 (by rfl) ⟨5402375, by rfl⟩ : syracuseStep 7203167 = 10804751) B10804751
theorem B2247355 : Blo 1182408 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B1182555 : Blo 1182408 1182555 := bstep (se 1 (by rfl) ⟨886916, by rfl⟩ : syracuseStep 1182555 = 1773833) B1773833
theorem B12143515 : Blo 1182408 12143515 := bstep (se 1 (by rfl) ⟨9107636, by rfl⟩ : syracuseStep 12143515 = 18215273) B18215273
theorem B1182623 : Blo 1182408 1182623 := bstep (se 1 (by rfl) ⟨886967, by rfl⟩ : syracuseStep 1182623 = 1773935) B1773935
theorem B18205661 : Blo 1182408 18205661 := bstep (se 3 (by rfl) ⟨3413561, by rfl⟩ : syracuseStep 18205661 = 6827123) B6827123
theorem B6736871 : Blo 1182408 6736871 := bstep (se 1 (by rfl) ⟨5052653, by rfl⟩ : syracuseStep 6736871 = 10105307) B10105307
theorem B2247659 : Blo 1182408 2247659 := bstep (se 1 (by rfl) ⟨1685744, by rfl⟩ : syracuseStep 2247659 = 3371489) B3371489
theorem B30338063 : Blo 1182408 30338063 := bstep (se 1 (by rfl) ⟨22753547, by rfl⟩ : syracuseStep 30338063 = 45507095) B45507095
theorem B1182767 : Blo 1182408 1182767 := bstep (se 1 (by rfl) ⟨887075, by rfl⟩ : syracuseStep 1182767 = 1774151) B1774151
theorem B3370031 : Blo 1182408 3370031 := bstep (se 1 (by rfl) ⟨2527523, by rfl⟩ : syracuseStep 3370031 = 5055047) B5055047
theorem B1182791 : Blo 1182408 1182791 := bstep (se 1 (by rfl) ⟨887093, by rfl⟩ : syracuseStep 1182791 = 1774187) B1774187
theorem B2993375 : Blo 1182408 2993375 := bstep (se 1 (by rfl) ⟨2245031, by rfl⟩ : syracuseStep 2993375 = 4490063) B4490063
theorem B1182943 : Blo 1182408 1182943 := bstep (se 1 (by rfl) ⟨887207, by rfl⟩ : syracuseStep 1182943 = 1774415) B1774415
theorem B12643735 : Blo 1182408 12643735 := bstep (se 1 (by rfl) ⟨9482801, by rfl⟩ : syracuseStep 12643735 = 18965603) B18965603
theorem B1330663 : Blo 1182408 1330663 := bstep (se 1 (by rfl) ⟨997997, by rfl⟩ : syracuseStep 1330663 = 1995995) B1995995
theorem B1183207 : Blo 1182408 1183207 := bstep (se 1 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 1183207 = 1774811) B1774811
theorem B3993083 : Blo 1182408 3993083 := bstep (se 1 (by rfl) ⟨2994812, by rfl⟩ : syracuseStep 3993083 = 5989625) B5989625
theorem B5058121 : Blo 1182408 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B1183323 : Blo 1182408 1183323 := bstep (se 1 (by rfl) ⟨887492, by rfl⟩ : syracuseStep 1183323 = 1774985) B1774985
theorem B3993245 : Blo 1182408 3993245 := bstep (se 3 (by rfl) ⟨748733, by rfl⟩ : syracuseStep 3993245 = 1497467) B1497467
theorem B8523559 : Blo 1182408 8523559 := bstep (se 1 (by rfl) ⟨6392669, by rfl⟩ : syracuseStep 8523559 = 12785339) B12785339
theorem B1183559 : Blo 1182408 1183559 := bstep (se 1 (by rfl) ⟨887669, by rfl⟩ : syracuseStep 1183559 = 1775339) B1775339
theorem B4263785 : Blo 1182408 4263785 := bstep (se 2 (by rfl) ⟨1598919, by rfl⟩ : syracuseStep 4263785 = 3197839) B3197839
theorem B4493177 : Blo 1182408 4493177 := bstep (se 2 (by rfl) ⟨1684941, by rfl⟩ : syracuseStep 4493177 = 3369883) B3369883
theorem B1331167 : Blo 1182408 1331167 := bstep (se 1 (by rfl) ⟨998375, by rfl⟩ : syracuseStep 1331167 = 1996751) B1996751
theorem B1183711 : Blo 1182408 1183711 := bstep (se 1 (by rfl) ⟨887783, by rfl⟩ : syracuseStep 1183711 = 1775567) B1775567
theorem B19206233 : Blo 1182408 19206233 := bstep (se 2 (by rfl) ⟨7202337, by rfl⟩ : syracuseStep 19206233 = 14404675) B14404675
theorem B3993785 : Blo 1182408 3993785 := bstep (se 2 (by rfl) ⟨1497669, by rfl⟩ : syracuseStep 3993785 = 2995339) B2995339
theorem B2134235 : Blo 1182408 2134235 := bstep (se 1 (by rfl) ⟨1600676, by rfl⟩ : syracuseStep 2134235 = 3201353) B3201353
theorem B1183975 : Blo 1182408 1183975 := bstep (se 1 (by rfl) ⟨887981, by rfl⟩ : syracuseStep 1183975 = 1775963) B1775963
theorem B3371375 : Blo 1182408 3371375 := bstep (se 1 (by rfl) ⟨2528531, by rfl⟩ : syracuseStep 3371375 = 5057063) B5057063
theorem B1184127 : Blo 1182408 1184127 := bstep (se 1 (by rfl) ⟨888095, by rfl⟩ : syracuseStep 1184127 = 1776191) B1776191
theorem B1774031 : Blo 1182408 1774031 := bstep (se 1 (by rfl) ⟨1330523, by rfl⟩ : syracuseStep 1774031 = 2661047) B2661047
theorem B1184207 : Blo 1182408 1184207 := bstep (se 1 (by rfl) ⟨888155, by rfl⟩ : syracuseStep 1184207 = 1776311) B1776311
theorem B1774073 : Blo 1182408 1774073 := bstep (se 2 (by rfl) ⟨665277, by rfl⟩ : syracuseStep 1774073 = 1330555) B1330555
theorem B6738511 : Blo 1182408 6738511 := bstep (se 1 (by rfl) ⟨5053883, by rfl⟩ : syracuseStep 6738511 = 10107767) B10107767
theorem B1774175 : Blo 1182408 1774175 := bstep (se 1 (by rfl) ⟨1330631, by rfl⟩ : syracuseStep 1774175 = 2661263) B2661263
theorem B3371615 : Blo 1182408 3371615 := bstep (se 1 (by rfl) ⟨2528711, by rfl⟩ : syracuseStep 3371615 = 5057423) B5057423
theorem B10949215 : Blo 1182408 10949215 := bstep (se 1 (by rfl) ⟨8211911, by rfl⟩ : syracuseStep 10949215 = 16423823) B16423823
theorem B1995367 : Blo 1182408 1995367 := bstep (se 1 (by rfl) ⟨1496525, by rfl⟩ : syracuseStep 1995367 = 2993051) B2993051
theorem B1921639 : Blo 1182408 1921639 := bstep (se 1 (by rfl) ⟨1441229, by rfl⟩ : syracuseStep 1921639 = 2882459) B2882459
theorem B1331815 : Blo 1182408 1331815 := bstep (se 1 (by rfl) ⟨998861, by rfl⟩ : syracuseStep 1331815 = 1997723) B1997723
theorem B1184359 : Blo 1182408 1184359 := bstep (se 1 (by rfl) ⟨888269, by rfl⟩ : syracuseStep 1184359 = 1776539) B1776539
theorem B8983223 : Blo 1182408 8983223 := bstep (se 1 (by rfl) ⟨6737417, by rfl⟩ : syracuseStep 8983223 = 13474835) B13474835
theorem B62329603 : Blo 1182408 62329603 := bstep (se 1 (by rfl) ⟨46747202, by rfl⟩ : syracuseStep 62329603 = 93494405) B93494405
theorem B1995529 : Blo 1182408 1995529 := bstep (se 2 (by rfl) ⟨748323, by rfl⟩ : syracuseStep 1995529 = 1496647) B1496647
theorem B3789593 : Blo 1182408 3789593 := bstep (se 2 (by rfl) ⟨1421097, by rfl⟩ : syracuseStep 3789593 = 2842195) B2842195
theorem B8524739 : Blo 1182408 8524739 := bstep (se 1 (by rfl) ⟨6393554, by rfl⟩ : syracuseStep 8524739 = 12787109) B12787109
theorem B10114055 : Blo 1182408 10114055 := bstep (se 1 (by rfl) ⟨7585541, by rfl⟩ : syracuseStep 10114055 = 15171083) B15171083
theorem B1774655 : Blo 1182408 1774655 := bstep (se 1 (by rfl) ⟨1330991, by rfl⟩ : syracuseStep 1774655 = 2661983) B2661983
theorem B1774697 : Blo 1182408 1774697 := bstep (se 2 (by rfl) ⟨665511, by rfl⟩ : syracuseStep 1774697 = 1331023) B1331023
theorem B1774799 : Blo 1182408 1774799 := bstep (se 1 (by rfl) ⟨1331099, by rfl⟩ : syracuseStep 1774799 = 2662199) B2662199
theorem B8525087 : Blo 1182408 8525087 := bstep (se 1 (by rfl) ⟨6393815, by rfl⟩ : syracuseStep 8525087 = 12787631) B12787631
theorem B7197983 : Blo 1182408 7197983 := bstep (se 1 (by rfl) ⟨5398487, by rfl⟩ : syracuseStep 7197983 = 10796975) B10796975
theorem B1996123 : Blo 1182408 1996123 := bstep (se 1 (by rfl) ⟨1497092, by rfl⟩ : syracuseStep 1996123 = 2994185) B2994185
theorem B1775003 : Blo 1182408 1775003 := bstep (se 1 (by rfl) ⟨1331252, by rfl⟩ : syracuseStep 1775003 = 2662505) B2662505
theorem B3200411 : Blo 1182408 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B10106369 : Blo 1182408 10106369 := bstep (se 2 (by rfl) ⟨3789888, by rfl⟩ : syracuseStep 10106369 = 7579777) B7579777
theorem B1775225 : Blo 1182408 1775225 := bstep (se 2 (by rfl) ⟨665709, by rfl⟩ : syracuseStep 1775225 = 1331419) B1331419
theorem B1775327 : Blo 1182408 1775327 := bstep (se 1 (by rfl) ⟨1331495, by rfl⟩ : syracuseStep 1775327 = 2662991) B2662991
theorem B1685215 : Blo 1182408 1685215 := bstep (se 1 (by rfl) ⟨1263911, by rfl⟩ : syracuseStep 1685215 = 2527823) B2527823
theorem B4798187 : Blo 1182408 4798187 := bstep (se 1 (by rfl) ⟨3598640, by rfl⟩ : syracuseStep 4798187 = 7197281) B7197281
theorem B1685243 : Blo 1182408 1685243 := bstep (se 1 (by rfl) ⟨1263932, by rfl⟩ : syracuseStep 1685243 = 2527865) B2527865
theorem B1775423 : Blo 1182408 1775423 := bstep (se 1 (by rfl) ⟨1331567, by rfl⟩ : syracuseStep 1775423 = 2663135) B2663135
theorem B1775591 : Blo 1182408 1775591 := bstep (se 1 (by rfl) ⟨1331693, by rfl⟩ : syracuseStep 1775591 = 2663387) B2663387
theorem B1775609 : Blo 1182408 1775609 := bstep (se 2 (by rfl) ⟨665853, by rfl⟩ : syracuseStep 1775609 = 1331707) B1331707
theorem B6739969 : Blo 1182408 6739969 := bstep (se 2 (by rfl) ⟨2527488, by rfl⟩ : syracuseStep 6739969 = 5054977) B5054977
theorem B2660435 : Blo 1182408 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B1775711 : Blo 1182408 1775711 := bstep (se 1 (by rfl) ⟨1331783, by rfl⟩ : syracuseStep 1775711 = 2663567) B2663567
theorem B2660507 : Blo 1182408 2660507 := bstep (se 1 (by rfl) ⟨1995380, by rfl⟩ : syracuseStep 2660507 = 3990761) B3990761
theorem B1775771 : Blo 1182408 1775771 := bstep (se 1 (by rfl) ⟨1331828, by rfl⟩ : syracuseStep 1775771 = 2663657) B2663657
theorem B1775807 : Blo 1182408 1775807 := bstep (se 1 (by rfl) ⟨1331855, by rfl⟩ : syracuseStep 1775807 = 2663711) B2663711
theorem B2996423 : Blo 1182408 2996423 := bstep (se 1 (by rfl) ⟨2247317, by rfl⟩ : syracuseStep 2996423 = 4494635) B4494635
theorem B1775849 : Blo 1182408 1775849 := bstep (se 2 (by rfl) ⟨665943, by rfl⟩ : syracuseStep 1775849 = 1331887) B1331887
theorem B5986547 : Blo 1182408 5986547 := bstep (se 1 (by rfl) ⟨4489910, by rfl⟩ : syracuseStep 5986547 = 8979821) B8979821
theorem B3995891 : Blo 1182408 3995891 := bstep (se 1 (by rfl) ⟨2996918, by rfl⟩ : syracuseStep 3995891 = 5993837) B5993837
theorem B2660615 : Blo 1182408 2660615 := bstep (se 1 (by rfl) ⟨1995461, by rfl⟩ : syracuseStep 2660615 = 3990923) B3990923
theorem B12802333 : Blo 1182408 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B1997095 : Blo 1182408 1997095 := bstep (se 1 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 1997095 = 2995643) B2995643
theorem B3995945 : Blo 1182408 3995945 := bstep (se 2 (by rfl) ⟨1498479, by rfl⟩ : syracuseStep 3995945 = 2996959) B2996959
theorem B1776155 : Blo 1182408 1776155 := bstep (se 1 (by rfl) ⟨1332116, by rfl⟩ : syracuseStep 1776155 = 2664233) B2664233
theorem B2660921 : Blo 1182408 2660921 := bstep (se 2 (by rfl) ⟨997845, by rfl⟩ : syracuseStep 2660921 = 1995691) B1995691
theorem B4266553 : Blo 1182408 4266553 := bstep (se 2 (by rfl) ⟨1599957, by rfl⟩ : syracuseStep 4266553 = 3199915) B3199915
theorem B1776233 : Blo 1182408 1776233 := bstep (se 2 (by rfl) ⟨666087, by rfl⟩ : syracuseStep 1776233 = 1332175) B1332175
theorem B5053049 : Blo 1182408 5053049 := bstep (se 2 (by rfl) ⟨1894893, by rfl⟩ : syracuseStep 5053049 = 3789787) B3789787
theorem B6077263 : Blo 1182408 6077263 := bstep (se 1 (by rfl) ⟨4557947, by rfl⟩ : syracuseStep 6077263 = 9115895) B9115895
theorem B7691321 : Blo 1182408 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B1998047 : Blo 1182408 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B6741245 : Blo 1182408 6741245 := bstep (se 3 (by rfl) ⟨1263983, by rfl⟩ : syracuseStep 6741245 = 2527967) B2527967
theorem B2661641 : Blo 1182408 2661641 := bstep (se 2 (by rfl) ⟨998115, by rfl⟩ : syracuseStep 2661641 = 1996231) B1996231
theorem B291347765 : Blo 1182408 291347765 := bstep (se 5 (by rfl) ⟨13656926, by rfl⟩ : syracuseStep 291347765 = 27313853) B27313853
theorem B5995943 : Blo 1182408 5995943 := bstep (se 1 (by rfl) ⟨4496957, by rfl⟩ : syracuseStep 5995943 = 8993915) B8993915
theorem B7585235 : Blo 1182408 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B4267475 : Blo 1182408 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B1998479 : Blo 1182408 1998479 := bstep (se 1 (by rfl) ⟨1498859, by rfl⟩ : syracuseStep 1998479 = 2997719) B2997719
theorem B5988167 : Blo 1182408 5988167 := bstep (se 1 (by rfl) ⟨4491125, by rfl⟩ : syracuseStep 5988167 = 8982251) B8982251
theorem B8986625 : Blo 1182408 8986625 := bstep (se 2 (by rfl) ⟨3369984, by rfl⟩ : syracuseStep 8986625 = 6739969) B6739969
theorem B12804155 : Blo 1182408 12804155 := bstep (se 1 (by rfl) ⟨9603116, by rfl⟩ : syracuseStep 12804155 = 19206233) B19206233
theorem B2662523 : Blo 1182408 2662523 := bstep (se 1 (by rfl) ⟨1996892, by rfl⟩ : syracuseStep 2662523 = 3993785) B3993785
theorem B2662793 : Blo 1182408 2662793 := bstep (se 2 (by rfl) ⟨998547, by rfl⟩ : syracuseStep 2662793 = 1997095) B1997095
theorem B2843041 : Blo 1182408 2843041 := bstep (se 2 (by rfl) ⟨1066140, by rfl⟩ : syracuseStep 2843041 = 2132281) B2132281
theorem B5988815 : Blo 1182408 5988815 := bstep (se 1 (by rfl) ⟨4491611, by rfl⟩ : syracuseStep 5988815 = 8983223) B8983223
theorem B6742703 : Blo 1182408 6742703 := bstep (se 1 (by rfl) ⟨5057027, by rfl⟩ : syracuseStep 6742703 = 10114055) B10114055
theorem B16417475 : Blo 1182408 16417475 := bstep (se 1 (by rfl) ⟨12313106, by rfl⟩ : syracuseStep 16417475 = 24626213) B24626213
theorem B14598953 : Blo 1182408 14598953 := bstep (se 2 (by rfl) ⟨5474607, by rfl⟩ : syracuseStep 14598953 = 10949215) B10949215
theorem B8979335 : Blo 1182408 8979335 := bstep (se 1 (by rfl) ⟨6734501, by rfl⟩ : syracuseStep 8979335 = 13469003) B13469003
theorem B8094745 : Blo 1182408 8094745 := bstep (se 2 (by rfl) ⟨3035529, by rfl⟩ : syracuseStep 8094745 = 6071059) B6071059
theorem B8103017 : Blo 1182408 8103017 := bstep (se 2 (by rfl) ⟨3038631, by rfl⟩ : syracuseStep 8103017 = 6077263) B6077263
theorem B3991031 : Blo 1182408 3991031 := bstep (se 1 (by rfl) ⟨2993273, by rfl⟩ : syracuseStep 3991031 = 5986547) B5986547
theorem B2663927 : Blo 1182408 2663927 := bstep (se 1 (by rfl) ⟨1997945, by rfl⟩ : syracuseStep 2663927 = 3995891) B3995891
theorem B4490747 : Blo 1182408 4490747 := bstep (se 1 (by rfl) ⟨3368060, by rfl⟩ : syracuseStep 4490747 = 6736121) B6736121
theorem B2663963 : Blo 1182408 2663963 := bstep (se 1 (by rfl) ⟨1997972, by rfl⟩ : syracuseStep 2663963 = 3995945) B3995945
theorem B4802111 : Blo 1182408 4802111 := bstep (se 1 (by rfl) ⟨3601583, by rfl⟩ : syracuseStep 4802111 = 7203167) B7203167
theorem B3368573 : Blo 1182408 3368573 := bstep (se 3 (by rfl) ⟨631607, by rfl⟩ : syracuseStep 3368573 = 1263215) B1263215
theorem B3368699 : Blo 1182408 3368699 := bstep (se 1 (by rfl) ⟨2526524, by rfl⟩ : syracuseStep 3368699 = 5053049) B5053049
theorem B4491065 : Blo 1182408 4491065 := bstep (se 2 (by rfl) ⟨1684149, by rfl⟩ : syracuseStep 4491065 = 3368299) B3368299
theorem B4491247 : Blo 1182408 4491247 := bstep (se 1 (by rfl) ⟨3368435, by rfl⟩ : syracuseStep 4491247 = 6736871) B6736871
theorem B2246687 : Blo 1182408 2246687 := bstep (se 1 (by rfl) ⟨1685015, by rfl⟩ : syracuseStep 2246687 = 3370031) B3370031
theorem B6744161 : Blo 1182408 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B2246953 : Blo 1182408 2246953 := bstep (se 2 (by rfl) ⟨842607, by rfl⟩ : syracuseStep 2246953 = 1685215) B1685215
theorem B5056823 : Blo 1182408 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B2844983 : Blo 1182408 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B11364745 : Blo 1182408 11364745 := bstep (se 2 (by rfl) ⟨4261779, by rfl⟩ : syracuseStep 11364745 = 8523559) B8523559
theorem B11536829 : Blo 1182408 11536829 := bstep (se 3 (by rfl) ⟨2163155, by rfl⟩ : syracuseStep 11536829 = 4326311) B4326311
theorem B3992111 : Blo 1182408 3992111 := bstep (se 1 (by rfl) ⟨2994083, by rfl⟩ : syracuseStep 3992111 = 5988167) B5988167
theorem B48548429 : Blo 1182408 48548429 := bstep (se 3 (by rfl) ⟨9102830, by rfl⟩ : syracuseStep 48548429 = 18205661) B18205661
theorem B2247583 : Blo 1182408 2247583 := bstep (se 1 (by rfl) ⟨1685687, by rfl⟩ : syracuseStep 2247583 = 3371375) B3371375
theorem B10791899 : Blo 1182408 10791899 := bstep (se 1 (by rfl) ⟨8093924, by rfl⟩ : syracuseStep 10791899 = 16187849) B16187849
theorem B1182687 : Blo 1182408 1182687 := bstep (se 1 (by rfl) ⟨887015, by rfl⟩ : syracuseStep 1182687 = 1774031) B1774031
theorem B1182715 : Blo 1182408 1182715 := bstep (se 1 (by rfl) ⟨887036, by rfl⟩ : syracuseStep 1182715 = 1774073) B1774073
theorem B1182783 : Blo 1182408 1182783 := bstep (se 1 (by rfl) ⟨887087, by rfl⟩ : syracuseStep 1182783 = 1774175) B1774175
theorem B2247743 : Blo 1182408 2247743 := bstep (se 1 (by rfl) ⟨1685807, by rfl⟩ : syracuseStep 2247743 = 3371615) B3371615
theorem B3992759 : Blo 1182408 3992759 := bstep (se 1 (by rfl) ⟨2994569, by rfl⟩ : syracuseStep 3992759 = 5989139) B5989139
theorem B2526395 : Blo 1182408 2526395 := bstep (se 1 (by rfl) ⟨1894796, by rfl⟩ : syracuseStep 2526395 = 3789593) B3789593
theorem B1183103 : Blo 1182408 1183103 := bstep (se 1 (by rfl) ⟨887327, by rfl⟩ : syracuseStep 1183103 = 1774655) B1774655
theorem B1183131 : Blo 1182408 1183131 := bstep (se 1 (by rfl) ⟨887348, by rfl⟩ : syracuseStep 1183131 = 1774697) B1774697
theorem B5688737 : Blo 1182408 5688737 := bstep (se 2 (by rfl) ⟨2133276, by rfl⟩ : syracuseStep 5688737 = 4266553) B4266553
theorem B1183199 : Blo 1182408 1183199 := bstep (se 1 (by rfl) ⟨887399, by rfl⟩ : syracuseStep 1183199 = 1774799) B1774799
theorem B18230791 : Blo 1182408 18230791 := bstep (se 1 (by rfl) ⟨13673093, by rfl⟩ : syracuseStep 18230791 = 27346187) B27346187
theorem B1183335 : Blo 1182408 1183335 := bstep (se 1 (by rfl) ⟨887501, by rfl⟩ : syracuseStep 1183335 = 1775003) B1775003
theorem B2133607 : Blo 1182408 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B6737579 : Blo 1182408 6737579 := bstep (se 1 (by rfl) ⟨5053184, by rfl⟩ : syracuseStep 6737579 = 10106369) B10106369
theorem B1183483 : Blo 1182408 1183483 := bstep (se 1 (by rfl) ⟨887612, by rfl⟩ : syracuseStep 1183483 = 1775225) B1775225
theorem B1183551 : Blo 1182408 1183551 := bstep (se 1 (by rfl) ⟨887663, by rfl⟩ : syracuseStep 1183551 = 1775327) B1775327
theorem B3198791 : Blo 1182408 3198791 := bstep (se 1 (by rfl) ⟨2399093, by rfl⟩ : syracuseStep 3198791 = 4798187) B4798187
theorem B7581545 : Blo 1182408 7581545 := bstep (se 2 (by rfl) ⟨2843079, by rfl⟩ : syracuseStep 7581545 = 5686159) B5686159
theorem B16191353 : Blo 1182408 16191353 := bstep (se 2 (by rfl) ⟨6071757, by rfl⟩ : syracuseStep 16191353 = 12143515) B12143515
theorem B1183615 : Blo 1182408 1183615 := bstep (se 1 (by rfl) ⟨887711, by rfl⟩ : syracuseStep 1183615 = 1775423) B1775423
theorem B1183727 : Blo 1182408 1183727 := bstep (se 1 (by rfl) ⟨887795, by rfl⟩ : syracuseStep 1183727 = 1775591) B1775591
theorem B1183739 : Blo 1182408 1183739 := bstep (se 1 (by rfl) ⟨887804, by rfl⟩ : syracuseStep 1183739 = 1775609) B1775609
theorem B1773623 : Blo 1182408 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B1183807 : Blo 1182408 1183807 := bstep (se 1 (by rfl) ⟨887855, by rfl⟩ : syracuseStep 1183807 = 1775711) B1775711
theorem B1773671 : Blo 1182408 1773671 := bstep (se 1 (by rfl) ⟨1330253, by rfl⟩ : syracuseStep 1773671 = 2660507) B2660507
theorem B1183847 : Blo 1182408 1183847 := bstep (se 1 (by rfl) ⟨887885, by rfl⟩ : syracuseStep 1183847 = 1775771) B1775771
theorem B1183871 : Blo 1182408 1183871 := bstep (se 1 (by rfl) ⟨887903, by rfl⟩ : syracuseStep 1183871 = 1775807) B1775807
theorem B1183899 : Blo 1182408 1183899 := bstep (se 1 (by rfl) ⟨887924, by rfl⟩ : syracuseStep 1183899 = 1775849) B1775849
theorem B1773743 : Blo 1182408 1773743 := bstep (se 1 (by rfl) ⟨1330307, by rfl⟩ : syracuseStep 1773743 = 2660615) B2660615
theorem B1184103 : Blo 1182408 1184103 := bstep (se 1 (by rfl) ⟨888077, by rfl⟩ : syracuseStep 1184103 = 1776155) B1776155
theorem B1773947 : Blo 1182408 1773947 := bstep (se 1 (by rfl) ⟨1330460, by rfl⟩ : syracuseStep 1773947 = 2660921) B2660921
theorem B1184155 : Blo 1182408 1184155 := bstep (se 1 (by rfl) ⟨888116, by rfl⟩ : syracuseStep 1184155 = 1776233) B1776233
theorem B1774217 : Blo 1182408 1774217 := bstep (se 2 (by rfl) ⟨665331, by rfl⟩ : syracuseStep 1774217 = 1330663) B1330663
theorem B4493981 : Blo 1182408 4493981 := bstep (se 3 (by rfl) ⟨842621, by rfl⟩ : syracuseStep 4493981 = 1685243) B1685243
theorem B1995583 : Blo 1182408 1995583 := bstep (se 1 (by rfl) ⟨1496687, by rfl⟩ : syracuseStep 1995583 = 2993375) B2993375
theorem B1332031 : Blo 1182408 1332031 := bstep (se 1 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 1332031 = 1998047) B1998047
theorem B4494163 : Blo 1182408 4494163 := bstep (se 1 (by rfl) ⟨3370622, by rfl⟩ : syracuseStep 4494163 = 6741245) B6741245
theorem B1774427 : Blo 1182408 1774427 := bstep (se 1 (by rfl) ⟨1330820, by rfl⟩ : syracuseStep 1774427 = 2661641) B2661641
theorem B1332319 : Blo 1182408 1332319 := bstep (se 1 (by rfl) ⟨999239, by rfl⟩ : syracuseStep 1332319 = 1998479) B1998479
theorem B2995451 : Blo 1182408 2995451 := bstep (se 1 (by rfl) ⟨2246588, by rfl⟩ : syracuseStep 2995451 = 4493177) B4493177
theorem B1774889 : Blo 1182408 1774889 := bstep (se 2 (by rfl) ⟨665583, by rfl⟩ : syracuseStep 1774889 = 1331167) B1331167
theorem B1496551 : Blo 1182408 1496551 := bstep (se 1 (by rfl) ⟨1122413, by rfl⟩ : syracuseStep 1496551 = 2244827) B2244827
theorem B1775087 : Blo 1182408 1775087 := bstep (se 1 (by rfl) ⟨1331315, by rfl⟩ : syracuseStep 1775087 = 2662631) B2662631
theorem B8992457 : Blo 1182408 8992457 := bstep (se 2 (by rfl) ⟨3372171, by rfl⟩ : syracuseStep 8992457 = 6744343) B6744343
theorem B17069777 : Blo 1182408 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B1775483 : Blo 1182408 1775483 := bstep (se 1 (by rfl) ⟨1331612, by rfl⟩ : syracuseStep 1775483 = 2663225) B2663225
theorem B5691293 : Blo 1182408 5691293 := bstep (se 3 (by rfl) ⟨1067117, by rfl⟩ : syracuseStep 5691293 = 2134235) B2134235
theorem B1775519 : Blo 1182408 1775519 := bstep (se 1 (by rfl) ⟨1331639, by rfl⟩ : syracuseStep 1775519 = 2663279) B2663279
theorem B5683159 : Blo 1182408 5683159 := bstep (se 1 (by rfl) ⟨4262369, by rfl⟩ : syracuseStep 5683159 = 8524739) B8524739
theorem B8984681 : Blo 1182408 8984681 := bstep (se 2 (by rfl) ⟨3369255, by rfl⟩ : syracuseStep 8984681 = 6738511) B6738511
theorem B2660489 : Blo 1182408 2660489 := bstep (se 2 (by rfl) ⟨997683, by rfl⟩ : syracuseStep 2660489 = 1995367) B1995367
theorem B2562185 : Blo 1182408 2562185 := bstep (se 2 (by rfl) ⟨960819, by rfl⟩ : syracuseStep 2562185 = 1921639) B1921639
theorem B1775753 : Blo 1182408 1775753 := bstep (se 2 (by rfl) ⟨665907, by rfl⟩ : syracuseStep 1775753 = 1331815) B1331815
theorem B5683391 : Blo 1182408 5683391 := bstep (se 1 (by rfl) ⟨4262543, by rfl⟩ : syracuseStep 5683391 = 8525087) B8525087
theorem B4798655 : Blo 1182408 4798655 := bstep (se 1 (by rfl) ⟨3598991, by rfl⟩ : syracuseStep 4798655 = 7197983) B7197983
theorem B2996473 : Blo 1182408 2996473 := bstep (se 2 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 2996473 = 2247355) B2247355
theorem B20207879 : Blo 1182408 20207879 := bstep (se 1 (by rfl) ⟨15155909, by rfl⟩ : syracuseStep 20207879 = 30311819) B30311819
theorem B19192079 : Blo 1182408 19192079 := bstep (se 1 (by rfl) ⟨14394059, by rfl⟩ : syracuseStep 19192079 = 28788119) B28788119
theorem B1775903 : Blo 1182408 1775903 := bstep (se 1 (by rfl) ⟨1331927, by rfl⟩ : syracuseStep 1775903 = 2663855) B2663855
theorem B83106137 : Blo 1182408 83106137 := bstep (se 2 (by rfl) ⟨31164801, by rfl⟩ : syracuseStep 83106137 = 62329603) B62329603
theorem B2660705 : Blo 1182408 2660705 := bstep (se 2 (by rfl) ⟨997764, by rfl⟩ : syracuseStep 2660705 = 1995529) B1995529
theorem B2660795 : Blo 1182408 2660795 := bstep (se 1 (by rfl) ⟨1995596, by rfl⟩ : syracuseStep 2660795 = 3991193) B3991193
theorem B3791387 : Blo 1182408 3791387 := bstep (se 1 (by rfl) ⟨2843540, by rfl⟩ : syracuseStep 3791387 = 5687081) B5687081
theorem B5397191 : Blo 1182408 5397191 := bstep (se 1 (by rfl) ⟨4047893, by rfl⟩ : syracuseStep 5397191 = 8095787) B8095787
theorem B1997615 : Blo 1182408 1997615 := bstep (se 1 (by rfl) ⟨1498211, by rfl⟩ : syracuseStep 1997615 = 2996423) B2996423
theorem B2661191 : Blo 1182408 2661191 := bstep (se 1 (by rfl) ⟨1995893, by rfl⟩ : syracuseStep 2661191 = 3991787) B3991787
theorem B1776455 : Blo 1182408 1776455 := bstep (se 1 (by rfl) ⟨1332341, by rfl⟩ : syracuseStep 1776455 = 2664683) B2664683
theorem B2661497 : Blo 1182408 2661497 := bstep (se 2 (by rfl) ⟨998061, by rfl⟩ : syracuseStep 2661497 = 1996123) B1996123
theorem B16858313 : Blo 1182408 16858313 := bstep (se 2 (by rfl) ⟨6321867, by rfl⟩ : syracuseStep 16858313 = 12643735) B12643735
theorem B1498439 : Blo 1182408 1498439 := bstep (se 1 (by rfl) ⟨1123829, by rfl⟩ : syracuseStep 1498439 = 2247659) B2247659
theorem B20225375 : Blo 1182408 20225375 := bstep (se 1 (by rfl) ⟨15169031, by rfl⟩ : syracuseStep 20225375 = 30338063) B30338063
theorem B5127547 : Blo 1182408 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B3792361 : Blo 1182408 3792361 := bstep (se 2 (by rfl) ⟨1422135, by rfl⟩ : syracuseStep 3792361 = 2844271) B2844271
theorem B194231843 : Blo 1182408 194231843 := bstep (se 1 (by rfl) ⟨145673882, by rfl⟩ : syracuseStep 194231843 = 291347765) B291347765
theorem B3997295 : Blo 1182408 3997295 := bstep (se 1 (by rfl) ⟨2997971, by rfl⟩ : syracuseStep 3997295 = 5995943) B5995943
theorem B2662055 : Blo 1182408 2662055 := bstep (se 1 (by rfl) ⟨1996541, by rfl⟩ : syracuseStep 2662055 = 3993083) B3993083
theorem B2662163 : Blo 1182408 2662163 := bstep (se 1 (by rfl) ⟨1996622, by rfl⟩ : syracuseStep 2662163 = 3993245) B3993245
theorem B2842465 : Blo 1182408 2842465 := bstep (se 2 (by rfl) ⟨1065924, by rfl⟩ : syracuseStep 2842465 = 2131849) B2131849
theorem B2842523 : Blo 1182408 2842523 := bstep (se 1 (by rfl) ⟨2131892, by rfl⟩ : syracuseStep 2842523 = 4263785) B4263785
theorem B8536103 : Blo 1182408 8536103 := bstep (se 1 (by rfl) ⟨6402077, by rfl⟩ : syracuseStep 8536103 = 12804155) B12804155
theorem B43171973 : Blo 1182408 43171973 := bstep (se 4 (by rfl) ⟨4047372, by rfl⟩ : syracuseStep 43171973 = 8094745) B8094745
theorem B10944983 : Blo 1182408 10944983 := bstep (se 1 (by rfl) ⟨8208737, by rfl⟩ : syracuseStep 10944983 = 16417475) B16417475
theorem B9732635 : Blo 1182408 9732635 := bstep (se 1 (by rfl) ⟨7299476, by rfl⟩ : syracuseStep 9732635 = 14598953) B14598953
theorem B7586621 : Blo 1182408 7586621 := bstep (se 3 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 7586621 = 2844983) B2844983
theorem B2245715 : Blo 1182408 2245715 := bstep (se 1 (by rfl) ⟨1684286, by rfl⟩ : syracuseStep 2245715 = 3368573) B3368573
theorem B11379851 : Blo 1182408 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B2245799 : Blo 1182408 2245799 := bstep (se 1 (by rfl) ⟨1684349, by rfl⟩ : syracuseStep 2245799 = 3368699) B3368699
theorem B3794195 : Blo 1182408 3794195 := bstep (se 1 (by rfl) ⟨2845646, by rfl⟩ : syracuseStep 3794195 = 5691293) B5691293
theorem B5989787 : Blo 1182408 5989787 := bstep (se 1 (by rfl) ⟨4492340, by rfl⟩ : syracuseStep 5989787 = 8984681) B8984681
theorem B10110365 : Blo 1182408 10110365 := bstep (se 3 (by rfl) ⟨1895693, by rfl⟩ : syracuseStep 10110365 = 3791387) B3791387
theorem B55404091 : Blo 1182408 55404091 := bstep (se 1 (by rfl) ⟨41553068, by rfl⟩ : syracuseStep 55404091 = 83106137) B83106137
theorem B3598127 : Blo 1182408 3598127 := bstep (se 1 (by rfl) ⟨2698595, by rfl⟩ : syracuseStep 3598127 = 5397191) B5397191
theorem B5056481 : Blo 1182408 5056481 := bstep (se 2 (by rfl) ⟨1896180, by rfl⟩ : syracuseStep 5056481 = 3792361) B3792361
theorem B7194599 : Blo 1182408 7194599 := bstep (se 1 (by rfl) ⟨5395949, by rfl⟩ : syracuseStep 7194599 = 10791899) B10791899
theorem B24307721 : Blo 1182408 24307721 := bstep (se 2 (by rfl) ⟨9115395, by rfl⟩ : syracuseStep 24307721 = 18230791) B18230791
theorem B2844809 : Blo 1182408 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B2664863 : Blo 1182408 2664863 := bstep (se 1 (by rfl) ⟨1998647, by rfl⟩ : syracuseStep 2664863 = 3997295) B3997295
theorem B4491719 : Blo 1182408 4491719 := bstep (se 1 (by rfl) ⟨3368789, by rfl⟩ : syracuseStep 4491719 = 6737579) B6737579
theorem B2132527 : Blo 1182408 2132527 := bstep (se 1 (by rfl) ⟨1599395, by rfl⟩ : syracuseStep 2132527 = 3198791) B3198791
theorem B1895015 : Blo 1182408 1895015 := bstep (se 1 (by rfl) ⟨1421261, by rfl⟩ : syracuseStep 1895015 = 2842523) B2842523
theorem B5991083 : Blo 1182408 5991083 := bstep (se 1 (by rfl) ⟨4493312, by rfl⟩ : syracuseStep 5991083 = 8986625) B8986625
theorem B1182415 : Blo 1182408 1182415 := bstep (se 1 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 1182415 = 1773623) B1773623
theorem B1182447 : Blo 1182408 1182447 := bstep (se 1 (by rfl) ⟨886835, by rfl⟩ : syracuseStep 1182447 = 1773671) B1773671
theorem B1182495 : Blo 1182408 1182495 := bstep (se 1 (by rfl) ⟨886871, by rfl⟩ : syracuseStep 1182495 = 1773743) B1773743
theorem B1182631 : Blo 1182408 1182631 := bstep (se 1 (by rfl) ⟨886973, by rfl⟩ : syracuseStep 1182631 = 1773947) B1773947
theorem B3992543 : Blo 1182408 3992543 := bstep (se 1 (by rfl) ⟨2994407, by rfl⟩ : syracuseStep 3992543 = 5988815) B5988815
theorem B1182811 : Blo 1182408 1182811 := bstep (se 1 (by rfl) ⟨887108, by rfl⟩ : syracuseStep 1182811 = 1774217) B1774217
theorem B6737053 : Blo 1182408 6737053 := bstep (se 3 (by rfl) ⟨1263197, by rfl⟩ : syracuseStep 6737053 = 2526395) B2526395
theorem B1182951 : Blo 1182408 1182951 := bstep (se 1 (by rfl) ⟨887213, by rfl⟩ : syracuseStep 1182951 = 1774427) B1774427
theorem B51178877 : Blo 1182408 51178877 := bstep (se 3 (by rfl) ⟨9596039, by rfl⟩ : syracuseStep 51178877 = 19192079) B19192079
theorem B5402011 : Blo 1182408 5402011 := bstep (se 1 (by rfl) ⟨4051508, by rfl⟩ : syracuseStep 5402011 = 8103017) B8103017
theorem B1183259 : Blo 1182408 1183259 := bstep (se 1 (by rfl) ⟨887444, by rfl⟩ : syracuseStep 1183259 = 1774889) B1774889
theorem B1183391 : Blo 1182408 1183391 := bstep (se 1 (by rfl) ⟨887543, by rfl⟩ : syracuseStep 1183391 = 1775087) B1775087
theorem B2993831 : Blo 1182408 2993831 := bstep (se 1 (by rfl) ⟨2245373, by rfl⟩ : syracuseStep 2993831 = 4490747) B4490747
theorem B5992217 : Blo 1182408 5992217 := bstep (se 2 (by rfl) ⟨2247081, by rfl⟩ : syracuseStep 5992217 = 4494163) B4494163
theorem B2994043 : Blo 1182408 2994043 := bstep (se 1 (by rfl) ⟨2245532, by rfl⟩ : syracuseStep 2994043 = 4491065) B4491065
theorem B1183655 : Blo 1182408 1183655 := bstep (se 1 (by rfl) ⟨887741, by rfl⟩ : syracuseStep 1183655 = 1775483) B1775483
theorem B1183679 : Blo 1182408 1183679 := bstep (se 1 (by rfl) ⟨887759, by rfl⟩ : syracuseStep 1183679 = 1775519) B1775519
theorem B1773659 : Blo 1182408 1773659 := bstep (se 1 (by rfl) ⟨1330244, by rfl⟩ : syracuseStep 1773659 = 2660489) B2660489
theorem B1708123 : Blo 1182408 1708123 := bstep (se 1 (by rfl) ⟨1281092, by rfl⟩ : syracuseStep 1708123 = 2562185) B2562185
theorem B1183835 : Blo 1182408 1183835 := bstep (se 1 (by rfl) ⟨887876, by rfl⟩ : syracuseStep 1183835 = 1775753) B1775753
theorem B3788927 : Blo 1182408 3788927 := bstep (se 1 (by rfl) ⟨2841695, by rfl⟩ : syracuseStep 3788927 = 5683391) B5683391
theorem B3199103 : Blo 1182408 3199103 := bstep (se 1 (by rfl) ⟨2399327, by rfl⟩ : syracuseStep 3199103 = 4798655) B4798655
theorem B13471919 : Blo 1182408 13471919 := bstep (se 1 (by rfl) ⟨10103939, by rfl⟩ : syracuseStep 13471919 = 20207879) B20207879
theorem B1183935 : Blo 1182408 1183935 := bstep (se 1 (by rfl) ⟨887951, by rfl⟩ : syracuseStep 1183935 = 1775903) B1775903
theorem B3371215 : Blo 1182408 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B1773803 : Blo 1182408 1773803 := bstep (se 1 (by rfl) ⟨1330352, by rfl⟩ : syracuseStep 1773803 = 2660705) B2660705
theorem B1773863 : Blo 1182408 1773863 := bstep (se 1 (by rfl) ⟨1330397, by rfl⟩ : syracuseStep 1773863 = 2660795) B2660795
theorem B6836729 : Blo 1182408 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B1331743 : Blo 1182408 1331743 := bstep (se 1 (by rfl) ⟨998807, by rfl⟩ : syracuseStep 1331743 = 1997615) B1997615
theorem B1774127 : Blo 1182408 1774127 := bstep (se 1 (by rfl) ⟨1330595, by rfl⟩ : syracuseStep 1774127 = 2661191) B2661191
theorem B1184303 : Blo 1182408 1184303 := bstep (se 1 (by rfl) ⟨888227, by rfl⟩ : syracuseStep 1184303 = 1776455) B1776455
theorem B1995401 : Blo 1182408 1995401 := bstep (se 2 (by rfl) ⟨748275, by rfl⟩ : syracuseStep 1995401 = 1496551) B1496551
theorem B1774331 : Blo 1182408 1774331 := bstep (se 1 (by rfl) ⟨1330748, by rfl⟩ : syracuseStep 1774331 = 2661497) B2661497
theorem B129487895 : Blo 1182408 129487895 := bstep (se 1 (by rfl) ⟨97115921, by rfl⟩ : syracuseStep 129487895 = 194231843) B194231843
theorem B1774703 : Blo 1182408 1774703 := bstep (se 1 (by rfl) ⟨1331027, by rfl⟩ : syracuseStep 1774703 = 2662055) B2662055
theorem B3789953 : Blo 1182408 3789953 := bstep (se 2 (by rfl) ⟨1421232, by rfl⟩ : syracuseStep 3789953 = 2842465) B2842465
theorem B1774775 : Blo 1182408 1774775 := bstep (se 1 (by rfl) ⟨1331081, by rfl⟩ : syracuseStep 1774775 = 2662163) B2662163
theorem B10794235 : Blo 1182408 10794235 := bstep (se 1 (by rfl) ⟨8095676, by rfl⟩ : syracuseStep 10794235 = 16191353) B16191353
theorem B1775015 : Blo 1182408 1775015 := bstep (se 1 (by rfl) ⟨1331261, by rfl⟩ : syracuseStep 1775015 = 2662523) B2662523
theorem B1775195 : Blo 1182408 1775195 := bstep (se 1 (by rfl) ⟨1331396, by rfl⟩ : syracuseStep 1775195 = 2662793) B2662793
theorem B3995297 : Blo 1182408 3995297 := bstep (se 2 (by rfl) ⟨1498236, by rfl⟩ : syracuseStep 3995297 = 2996473) B2996473
theorem B2995937 : Blo 1182408 2995937 := bstep (se 2 (by rfl) ⟨1123476, by rfl⟩ : syracuseStep 2995937 = 2246953) B2246953
theorem B2995987 : Blo 1182408 2995987 := bstep (se 1 (by rfl) ⟨2246990, by rfl⟩ : syracuseStep 2995987 = 4493981) B4493981
theorem B4495135 : Blo 1182408 4495135 := bstep (se 1 (by rfl) ⟨3371351, by rfl⟩ : syracuseStep 4495135 = 6742703) B6742703
theorem B15152993 : Blo 1182408 15152993 := bstep (se 2 (by rfl) ⟨5682372, by rfl⟩ : syracuseStep 15152993 = 11364745) B11364745
theorem B3790721 : Blo 1182408 3790721 := bstep (se 2 (by rfl) ⟨1421520, by rfl⟩ : syracuseStep 3790721 = 2843041) B2843041
theorem B5986223 : Blo 1182408 5986223 := bstep (se 1 (by rfl) ⟨4489667, by rfl⟩ : syracuseStep 5986223 = 8979335) B8979335
theorem B1996967 : Blo 1182408 1996967 := bstep (se 1 (by rfl) ⟨1497725, by rfl⟩ : syracuseStep 1996967 = 2995451) B2995451
theorem B3995837 : Blo 1182408 3995837 := bstep (se 3 (by rfl) ⟨749219, by rfl⟩ : syracuseStep 3995837 = 1498439) B1498439
theorem B2660687 : Blo 1182408 2660687 := bstep (se 1 (by rfl) ⟨1995515, by rfl⟩ : syracuseStep 2660687 = 3991031) B3991031
theorem B1775951 : Blo 1182408 1775951 := bstep (se 1 (by rfl) ⟨1331963, by rfl⟩ : syracuseStep 1775951 = 2663927) B2663927
theorem B1775975 : Blo 1182408 1775975 := bstep (se 1 (by rfl) ⟨1331981, by rfl⟩ : syracuseStep 1775975 = 2663963) B2663963
theorem B3201407 : Blo 1182408 3201407 := bstep (se 1 (by rfl) ⟨2401055, by rfl⟩ : syracuseStep 3201407 = 4802111) B4802111
theorem B2660777 : Blo 1182408 2660777 := bstep (se 2 (by rfl) ⟨997791, by rfl⟩ : syracuseStep 2660777 = 1995583) B1995583
theorem B1776041 : Blo 1182408 1776041 := bstep (se 2 (by rfl) ⟨666015, by rfl⟩ : syracuseStep 1776041 = 1332031) B1332031
theorem B5994971 : Blo 1182408 5994971 := bstep (se 1 (by rfl) ⟨4496228, by rfl⟩ : syracuseStep 5994971 = 8992457) B8992457
theorem B2996777 : Blo 1182408 2996777 := bstep (se 2 (by rfl) ⟨1123791, by rfl⟩ : syracuseStep 2996777 = 2247583) B2247583
theorem B1497791 : Blo 1182408 1497791 := bstep (se 1 (by rfl) ⟨1123343, by rfl⟩ : syracuseStep 1497791 = 2246687) B2246687
theorem B4496107 : Blo 1182408 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B1776425 : Blo 1182408 1776425 := bstep (se 2 (by rfl) ⟨666159, by rfl⟩ : syracuseStep 1776425 = 1332319) B1332319
theorem B7691219 : Blo 1182408 7691219 := bstep (se 1 (by rfl) ⟨5768414, by rfl⟩ : syracuseStep 7691219 = 11536829) B11536829
theorem B2661407 : Blo 1182408 2661407 := bstep (se 1 (by rfl) ⟨1996055, by rfl⟩ : syracuseStep 2661407 = 3992111) B3992111
theorem B32365619 : Blo 1182408 32365619 := bstep (se 1 (by rfl) ⟨24274214, by rfl⟩ : syracuseStep 32365619 = 48548429) B48548429
theorem B1498495 : Blo 1182408 1498495 := bstep (se 1 (by rfl) ⟨1123871, by rfl⟩ : syracuseStep 1498495 = 2247743) B2247743
theorem B2661839 : Blo 1182408 2661839 := bstep (se 1 (by rfl) ⟨1996379, by rfl⟩ : syracuseStep 2661839 = 3992759) B3992759
theorem B11238875 : Blo 1182408 11238875 := bstep (se 1 (by rfl) ⟨8429156, by rfl⟩ : syracuseStep 11238875 = 16858313) B16858313
theorem B13483583 : Blo 1182408 13483583 := bstep (se 1 (by rfl) ⟨10112687, by rfl⟩ : syracuseStep 13483583 = 20225375) B20225375
theorem B3792491 : Blo 1182408 3792491 := bstep (se 1 (by rfl) ⟨2844368, by rfl⟩ : syracuseStep 3792491 = 5688737) B5688737
theorem B5054363 : Blo 1182408 5054363 := bstep (se 1 (by rfl) ⟨3790772, by rfl⟩ : syracuseStep 5054363 = 7581545) B7581545
theorem B7577545 : Blo 1182408 7577545 := bstep (se 2 (by rfl) ⟨2841579, by rfl⟩ : syracuseStep 7577545 = 5683159) B5683159
theorem B5988329 : Blo 1182408 5988329 := bstep (se 2 (by rfl) ⟨2245623, by rfl⟩ : syracuseStep 5988329 = 4491247) B4491247
theorem B2277497 : Blo 1182408 2277497 := bstep (se 2 (by rfl) ⟨854061, by rfl⟩ : syracuseStep 2277497 = 1708123) B1708123
theorem B6488423 : Blo 1182408 6488423 := bstep (se 1 (by rfl) ⟨4866317, by rfl⟩ : syracuseStep 6488423 = 9732635) B9732635
theorem B2843369 : Blo 1182408 2843369 := bstep (se 2 (by rfl) ⟨1066263, by rfl⟩ : syracuseStep 2843369 = 2132527) B2132527
theorem B7586567 : Blo 1182408 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B2663531 : Blo 1182408 2663531 := bstep (se 1 (by rfl) ⟨1997648, by rfl⟩ : syracuseStep 2663531 = 3995297) B3995297
theorem B10101995 : Blo 1182408 10101995 := bstep (se 1 (by rfl) ⟨7576496, by rfl⟩ : syracuseStep 10101995 = 15152993) B15152993
theorem B3990815 : Blo 1182408 3990815 := bstep (se 1 (by rfl) ⟨2993111, by rfl⟩ : syracuseStep 3990815 = 5986223) B5986223
theorem B16205147 : Blo 1182408 16205147 := bstep (se 1 (by rfl) ⟨12153860, by rfl⟩ : syracuseStep 16205147 = 24307721) B24307721
theorem B2663891 : Blo 1182408 2663891 := bstep (se 1 (by rfl) ⟨1997918, by rfl⟩ : syracuseStep 2663891 = 3995837) B3995837
theorem B7202681 : Blo 1182408 7202681 := bstep (se 2 (by rfl) ⟨2701005, by rfl⟩ : syracuseStep 7202681 = 5402011) B5402011
theorem B8989055 : Blo 1182408 8989055 := bstep (se 1 (by rfl) ⟨6741791, by rfl⟩ : syracuseStep 8989055 = 13483583) B13483583
theorem B3992057 : Blo 1182408 3992057 := bstep (se 2 (by rfl) ⟨1497021, by rfl⟩ : syracuseStep 3992057 = 2994043) B2994043
theorem B10103393 : Blo 1182408 10103393 := bstep (se 2 (by rfl) ⟨3788772, by rfl⟩ : syracuseStep 10103393 = 7577545) B7577545
theorem B3369575 : Blo 1182408 3369575 := bstep (se 1 (by rfl) ⟨2527181, by rfl⟩ : syracuseStep 3369575 = 5054363) B5054363
theorem B3992219 : Blo 1182408 3992219 := bstep (se 1 (by rfl) ⟨2994164, by rfl⟩ : syracuseStep 3992219 = 5988329) B5988329
theorem B1182439 : Blo 1182408 1182439 := bstep (se 1 (by rfl) ⟨886829, by rfl⟩ : syracuseStep 1182439 = 1773659) B1773659
theorem B2525951 : Blo 1182408 2525951 := bstep (se 1 (by rfl) ⟨1894463, by rfl⟩ : syracuseStep 2525951 = 3788927) B3788927
theorem B2132735 : Blo 1182408 2132735 := bstep (se 1 (by rfl) ⟨1599551, by rfl⟩ : syracuseStep 2132735 = 3199103) B3199103
theorem B28781315 : Blo 1182408 28781315 := bstep (se 1 (by rfl) ⟨21585986, by rfl⟩ : syracuseStep 28781315 = 43171973) B43171973
theorem B8981279 : Blo 1182408 8981279 := bstep (se 1 (by rfl) ⟨6735959, by rfl⟩ : syracuseStep 8981279 = 13471919) B13471919
theorem B1182535 : Blo 1182408 1182535 := bstep (se 1 (by rfl) ⟨886901, by rfl⟩ : syracuseStep 1182535 = 1773803) B1773803
theorem B1182575 : Blo 1182408 1182575 := bstep (se 1 (by rfl) ⟨886931, by rfl⟩ : syracuseStep 1182575 = 1773863) B1773863
theorem B1182751 : Blo 1182408 1182751 := bstep (se 1 (by rfl) ⟨887063, by rfl⟩ : syracuseStep 1182751 = 1774127) B1774127
theorem B1330267 : Blo 1182408 1330267 := bstep (se 1 (by rfl) ⟨997700, by rfl⟩ : syracuseStep 1330267 = 1995401) B1995401
theorem B1182887 : Blo 1182408 1182887 := bstep (se 1 (by rfl) ⟨887165, by rfl⟩ : syracuseStep 1182887 = 1774331) B1774331
theorem B5057747 : Blo 1182408 5057747 := bstep (se 1 (by rfl) ⟨3793310, by rfl⟩ : syracuseStep 5057747 = 7586621) B7586621
theorem B1183135 : Blo 1182408 1183135 := bstep (se 1 (by rfl) ⟨887351, by rfl⟩ : syracuseStep 1183135 = 1774703) B1774703
theorem B2526635 : Blo 1182408 2526635 := bstep (se 1 (by rfl) ⟨1894976, by rfl⟩ : syracuseStep 2526635 = 3789953) B3789953
theorem B1183183 : Blo 1182408 1183183 := bstep (se 1 (by rfl) ⟨887387, by rfl⟩ : syracuseStep 1183183 = 1774775) B1774775
theorem B3993191 : Blo 1182408 3993191 := bstep (se 1 (by rfl) ⟨2994893, by rfl⟩ : syracuseStep 3993191 = 5989787) B5989787
theorem B1183343 : Blo 1182408 1183343 := bstep (se 1 (by rfl) ⟨887507, by rfl⟩ : syracuseStep 1183343 = 1775015) B1775015
theorem B1183463 : Blo 1182408 1183463 := bstep (se 1 (by rfl) ⟨887597, by rfl⟩ : syracuseStep 1183463 = 1775195) B1775195
theorem B2527147 : Blo 1182408 2527147 := bstep (se 1 (by rfl) ⟨1895360, by rfl⟩ : syracuseStep 2527147 = 3790721) B3790721
theorem B3370987 : Blo 1182408 3370987 := bstep (se 1 (by rfl) ⟨2528240, by rfl⟩ : syracuseStep 3370987 = 5056481) B5056481
theorem B18231277 : Blo 1182408 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B4796399 : Blo 1182408 4796399 := bstep (se 1 (by rfl) ⟨3597299, by rfl⟩ : syracuseStep 4796399 = 7194599) B7194599
theorem B1896539 : Blo 1182408 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B1331311 : Blo 1182408 1331311 := bstep (se 1 (by rfl) ⟨998483, by rfl⟩ : syracuseStep 1331311 = 1996967) B1996967
theorem B8982737 : Blo 1182408 8982737 := bstep (se 2 (by rfl) ⟨3368526, by rfl⟩ : syracuseStep 8982737 = 6737053) B6737053
theorem B1773791 : Blo 1182408 1773791 := bstep (se 1 (by rfl) ⟨1330343, by rfl⟩ : syracuseStep 1773791 = 2660687) B2660687
theorem B1183967 : Blo 1182408 1183967 := bstep (se 1 (by rfl) ⟨887975, by rfl⟩ : syracuseStep 1183967 = 1775951) B1775951
theorem B1183983 : Blo 1182408 1183983 := bstep (se 1 (by rfl) ⟨887987, by rfl⟩ : syracuseStep 1183983 = 1775975) B1775975
theorem B2134271 : Blo 1182408 2134271 := bstep (se 1 (by rfl) ⟨1600703, by rfl⟩ : syracuseStep 2134271 = 3201407) B3201407
theorem B1773851 : Blo 1182408 1773851 := bstep (se 1 (by rfl) ⟨1330388, by rfl⟩ : syracuseStep 1773851 = 2660777) B2660777
theorem B1184027 : Blo 1182408 1184027 := bstep (se 1 (by rfl) ⟨888020, by rfl⟩ : syracuseStep 1184027 = 1776041) B1776041
theorem B2994479 : Blo 1182408 2994479 := bstep (se 1 (by rfl) ⟨2245859, by rfl⟩ : syracuseStep 2994479 = 4491719) B4491719
theorem B3994055 : Blo 1182408 3994055 := bstep (se 1 (by rfl) ⟨2995541, by rfl⟩ : syracuseStep 3994055 = 5991083) B5991083
theorem B3994109 : Blo 1182408 3994109 := bstep (se 3 (by rfl) ⟨748895, by rfl⟩ : syracuseStep 3994109 = 1497791) B1497791
theorem B1184283 : Blo 1182408 1184283 := bstep (se 1 (by rfl) ⟨888212, by rfl⟩ : syracuseStep 1184283 = 1776425) B1776425
theorem B1774271 : Blo 1182408 1774271 := bstep (se 1 (by rfl) ⟨1330703, by rfl⟩ : syracuseStep 1774271 = 2661407) B2661407
theorem B73872121 : Blo 1182408 73872121 := bstep (se 2 (by rfl) ⟨27702045, by rfl⟩ : syracuseStep 73872121 = 55404091) B55404091
theorem B1774559 : Blo 1182408 1774559 := bstep (se 1 (by rfl) ⟨1330919, by rfl⟩ : syracuseStep 1774559 = 2661839) B2661839
theorem B7492583 : Blo 1182408 7492583 := bstep (se 1 (by rfl) ⟨5619437, by rfl⟩ : syracuseStep 7492583 = 11238875) B11238875
theorem B3994649 : Blo 1182408 3994649 := bstep (se 2 (by rfl) ⟨1497993, by rfl⟩ : syracuseStep 3994649 = 2995987) B2995987
theorem B5993513 : Blo 1182408 5993513 := bstep (se 2 (by rfl) ⟨2247567, by rfl⟩ : syracuseStep 5993513 = 4495135) B4495135
theorem B2528327 : Blo 1182408 2528327 := bstep (se 1 (by rfl) ⟨1896245, by rfl⟩ : syracuseStep 2528327 = 3792491) B3792491
theorem B1995887 : Blo 1182408 1995887 := bstep (se 1 (by rfl) ⟨1496915, by rfl⟩ : syracuseStep 1995887 = 2993831) B2993831
theorem B3994811 : Blo 1182408 3994811 := bstep (se 1 (by rfl) ⟨2996108, by rfl⟩ : syracuseStep 3994811 = 5992217) B5992217
theorem B5690735 : Blo 1182408 5690735 := bstep (se 1 (by rfl) ⟨4268051, by rfl⟩ : syracuseStep 5690735 = 8536103) B8536103
theorem B4494953 : Blo 1182408 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B7296655 : Blo 1182408 7296655 := bstep (se 1 (by rfl) ⟨5472491, by rfl⟩ : syracuseStep 7296655 = 10944983) B10944983
theorem B86325263 : Blo 1182408 86325263 := bstep (se 1 (by rfl) ⟨64743947, by rfl⟩ : syracuseStep 86325263 = 129487895) B129487895
theorem B1775657 : Blo 1182408 1775657 := bstep (se 2 (by rfl) ⟨665871, by rfl⟩ : syracuseStep 1775657 = 1331743) B1331743
theorem B1497143 : Blo 1182408 1497143 := bstep (se 1 (by rfl) ⟨1122857, by rfl⟩ : syracuseStep 1497143 = 2245715) B2245715
theorem B1497199 : Blo 1182408 1497199 := bstep (se 1 (by rfl) ⟨1122899, by rfl⟩ : syracuseStep 1497199 = 2245799) B2245799
theorem B2529463 : Blo 1182408 2529463 := bstep (se 1 (by rfl) ⟨1897097, by rfl⟩ : syracuseStep 2529463 = 3794195) B3794195
theorem B6740243 : Blo 1182408 6740243 := bstep (se 1 (by rfl) ⟨5055182, by rfl⟩ : syracuseStep 6740243 = 10110365) B10110365
theorem B5994809 : Blo 1182408 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B1997291 : Blo 1182408 1997291 := bstep (se 1 (by rfl) ⟨1497968, by rfl⟩ : syracuseStep 1997291 = 2995937) B2995937
theorem B2398751 : Blo 1182408 2398751 := bstep (se 1 (by rfl) ⟨1799063, by rfl⟩ : syracuseStep 2398751 = 3598127) B3598127
theorem B5053373 : Blo 1182408 5053373 := bstep (se 3 (by rfl) ⟨947507, by rfl⟩ : syracuseStep 5053373 = 1895015) B1895015
theorem B1776575 : Blo 1182408 1776575 := bstep (se 1 (by rfl) ⟨1332431, by rfl⟩ : syracuseStep 1776575 = 2664863) B2664863
theorem B3996647 : Blo 1182408 3996647 := bstep (se 1 (by rfl) ⟨2997485, by rfl⟩ : syracuseStep 3996647 = 5994971) B5994971
theorem B14392313 : Blo 1182408 14392313 := bstep (se 2 (by rfl) ⟨5397117, by rfl⟩ : syracuseStep 14392313 = 10794235) B10794235
theorem B1997851 : Blo 1182408 1997851 := bstep (se 1 (by rfl) ⟨1498388, by rfl⟩ : syracuseStep 1997851 = 2996777) B2996777
theorem B1997993 : Blo 1182408 1997993 := bstep (se 2 (by rfl) ⟨749247, by rfl⟩ : syracuseStep 1997993 = 1498495) B1498495
theorem B5127479 : Blo 1182408 5127479 := bstep (se 1 (by rfl) ⟨3845609, by rfl⟩ : syracuseStep 5127479 = 7691219) B7691219
theorem B2661695 : Blo 1182408 2661695 := bstep (se 1 (by rfl) ⟨1996271, by rfl⟩ : syracuseStep 2661695 = 3992543) B3992543
theorem B21577079 : Blo 1182408 21577079 := bstep (se 1 (by rfl) ⟨16182809, by rfl⟩ : syracuseStep 21577079 = 32365619) B32365619
theorem B34119251 : Blo 1182408 34119251 := bstep (se 1 (by rfl) ⟨25589438, by rfl⟩ : syracuseStep 34119251 = 51178877) B51178877
theorem B5988491 : Blo 1182408 5988491 := bstep (se 1 (by rfl) ⟨4491368, by rfl⟩ : syracuseStep 5988491 = 8982737) B8982737
theorem B4325615 : Blo 1182408 4325615 := bstep (se 1 (by rfl) ⟨3244211, by rfl⟩ : syracuseStep 4325615 = 6488423) B6488423
theorem B2662703 : Blo 1182408 2662703 := bstep (se 1 (by rfl) ⟨1997027, by rfl⟩ : syracuseStep 2662703 = 3994055) B3994055
theorem B2662739 : Blo 1182408 2662739 := bstep (se 1 (by rfl) ⟨1997054, by rfl⟩ : syracuseStep 2662739 = 3994109) B3994109
theorem B2663099 : Blo 1182408 2663099 := bstep (se 1 (by rfl) ⟨1997324, by rfl⟩ : syracuseStep 2663099 = 3994649) B3994649
theorem B2663207 : Blo 1182408 2663207 := bstep (se 1 (by rfl) ⟨1997405, by rfl⟩ : syracuseStep 2663207 = 3994811) B3994811
theorem B6734663 : Blo 1182408 6734663 := bstep (se 1 (by rfl) ⟨5050997, by rfl⟩ : syracuseStep 6734663 = 10101995) B10101995
theorem B3793823 : Blo 1182408 3793823 := bstep (se 1 (by rfl) ⟨2845367, by rfl⟩ : syracuseStep 3793823 = 5690735) B5690735
theorem B4801787 : Blo 1182408 4801787 := bstep (se 1 (by rfl) ⟨3601340, by rfl⟩ : syracuseStep 4801787 = 7202681) B7202681
theorem B57550175 : Blo 1182408 57550175 := bstep (se 1 (by rfl) ⟨43162631, by rfl⟩ : syracuseStep 57550175 = 86325263) B86325263
theorem B2663801 : Blo 1182408 2663801 := bstep (se 2 (by rfl) ⟨998925, by rfl⟩ : syracuseStep 2663801 = 1997851) B1997851
theorem B1599167 : Blo 1182408 1599167 := bstep (se 1 (by rfl) ⟨1199375, by rfl⟩ : syracuseStep 1599167 = 2398751) B2398751
theorem B6735595 : Blo 1182408 6735595 := bstep (se 1 (by rfl) ⟨5051696, by rfl⟩ : syracuseStep 6735595 = 10103393) B10103393
theorem B2246383 : Blo 1182408 2246383 := bstep (se 1 (by rfl) ⟨1684787, by rfl⟩ : syracuseStep 2246383 = 3369575) B3369575
theorem B19187543 : Blo 1182408 19187543 := bstep (se 1 (by rfl) ⟨14390657, by rfl⟩ : syracuseStep 19187543 = 28781315) B28781315
theorem B3368915 : Blo 1182408 3368915 := bstep (se 1 (by rfl) ⟨2526686, by rfl⟩ : syracuseStep 3368915 = 5053373) B5053373
theorem B2664431 : Blo 1182408 2664431 := bstep (se 1 (by rfl) ⟨1998323, by rfl⟩ : syracuseStep 2664431 = 3996647) B3996647
theorem B9594875 : Blo 1182408 9594875 := bstep (se 1 (by rfl) ⟨7196156, by rfl⟩ : syracuseStep 9594875 = 14392313) B14392313
theorem B6735869 : Blo 1182408 6735869 := bstep (se 3 (by rfl) ⟨1262975, by rfl⟩ : syracuseStep 6735869 = 2525951) B2525951
theorem B3418319 : Blo 1182408 3418319 := bstep (se 1 (by rfl) ⟨2563739, by rfl⟩ : syracuseStep 3418319 = 5127479) B5127479
theorem B3369529 : Blo 1182408 3369529 := bstep (se 2 (by rfl) ⟨1263573, by rfl⟩ : syracuseStep 3369529 = 2527147) B2527147
theorem B24308369 : Blo 1182408 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B3197599 : Blo 1182408 3197599 := bstep (se 1 (by rfl) ⟨2398199, by rfl⟩ : syracuseStep 3197599 = 4796399) B4796399
theorem B1518331 : Blo 1182408 1518331 := bstep (se 1 (by rfl) ⟨1138748, by rfl⟩ : syracuseStep 1518331 = 2277497) B2277497
theorem B3992381 : Blo 1182408 3992381 := bstep (se 3 (by rfl) ⟨748571, by rfl⟩ : syracuseStep 3992381 = 1497143) B1497143
theorem B1182527 : Blo 1182408 1182527 := bstep (se 1 (by rfl) ⟨886895, by rfl⟩ : syracuseStep 1182527 = 1773791) B1773791
theorem B1182567 : Blo 1182408 1182567 := bstep (se 1 (by rfl) ⟨886925, by rfl⟩ : syracuseStep 1182567 = 1773851) B1773851
theorem B1182847 : Blo 1182408 1182847 := bstep (se 1 (by rfl) ⟨887135, by rfl⟩ : syracuseStep 1182847 = 1774271) B1774271
theorem B1895579 : Blo 1182408 1895579 := bstep (se 1 (by rfl) ⟨1421684, by rfl⟩ : syracuseStep 1895579 = 2843369) B2843369
theorem B5057711 : Blo 1182408 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B1183039 : Blo 1182408 1183039 := bstep (se 1 (by rfl) ⟨887279, by rfl⟩ : syracuseStep 1183039 = 1774559) B1774559
theorem B1330591 : Blo 1182408 1330591 := bstep (se 1 (by rfl) ⟨997943, by rfl⟩ : syracuseStep 1330591 = 1995887) B1995887
theorem B20229749 : Blo 1182408 20229749 := bstep (se 5 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 20229749 = 1896539) B1896539
theorem B98496161 : Blo 1182408 98496161 := bstep (se 2 (by rfl) ⟨36936060, by rfl⟩ : syracuseStep 98496161 = 73872121) B73872121
theorem B1183771 : Blo 1182408 1183771 := bstep (se 1 (by rfl) ⟨887828, by rfl⟩ : syracuseStep 1183771 = 1775657) B1775657
theorem B1773689 : Blo 1182408 1773689 := bstep (se 2 (by rfl) ⟨665133, by rfl⟩ : syracuseStep 1773689 = 1330267) B1330267
theorem B4493495 : Blo 1182408 4493495 := bstep (se 1 (by rfl) ⟨3370121, by rfl⟩ : syracuseStep 4493495 = 6740243) B6740243
theorem B5992703 : Blo 1182408 5992703 := bstep (se 1 (by rfl) ⟨4494527, by rfl⟩ : syracuseStep 5992703 = 8989055) B8989055
theorem B1331527 : Blo 1182408 1331527 := bstep (se 1 (by rfl) ⟨998645, by rfl⟩ : syracuseStep 1331527 = 1997291) B1997291
theorem B1184383 : Blo 1182408 1184383 := bstep (se 1 (by rfl) ⟨888287, by rfl⟩ : syracuseStep 1184383 = 1776575) B1776575
theorem B1331995 : Blo 1182408 1331995 := bstep (se 1 (by rfl) ⟨998996, by rfl⟩ : syracuseStep 1331995 = 1997993) B1997993
theorem B3371831 : Blo 1182408 3371831 := bstep (se 1 (by rfl) ⟨2528873, by rfl⟩ : syracuseStep 3371831 = 5057747) B5057747
theorem B9728873 : Blo 1182408 9728873 := bstep (se 2 (by rfl) ⟨3648327, by rfl⟩ : syracuseStep 9728873 = 7296655) B7296655
theorem B1774463 : Blo 1182408 1774463 := bstep (se 1 (by rfl) ⟨1330847, by rfl⟩ : syracuseStep 1774463 = 2661695) B2661695
theorem B1684423 : Blo 1182408 1684423 := bstep (se 1 (by rfl) ⟨1263317, by rfl⟩ : syracuseStep 1684423 = 2526635) B2526635
theorem B22746167 : Blo 1182408 22746167 := bstep (se 1 (by rfl) ⟨17059625, by rfl⟩ : syracuseStep 22746167 = 34119251) B34119251
theorem B4494649 : Blo 1182408 4494649 := bstep (se 2 (by rfl) ⟨1685493, by rfl⟩ : syracuseStep 4494649 = 3370987) B3370987
theorem B1996265 : Blo 1182408 1996265 := bstep (se 2 (by rfl) ⟨748599, by rfl⟩ : syracuseStep 1996265 = 1497199) B1497199
theorem B1775081 : Blo 1182408 1775081 := bstep (se 2 (by rfl) ⟨665655, by rfl⟩ : syracuseStep 1775081 = 1331311) B1331311
theorem B1422847 : Blo 1182408 1422847 := bstep (se 1 (by rfl) ⟨1067135, by rfl⟩ : syracuseStep 1422847 = 2134271) B2134271
theorem B1996319 : Blo 1182408 1996319 := bstep (se 1 (by rfl) ⟨1497239, by rfl⟩ : syracuseStep 1996319 = 2994479) B2994479
theorem B3372617 : Blo 1182408 3372617 := bstep (se 2 (by rfl) ⟨1264731, by rfl⟩ : syracuseStep 3372617 = 2529463) B2529463
theorem B4995055 : Blo 1182408 4995055 := bstep (se 1 (by rfl) ⟨3746291, by rfl⟩ : syracuseStep 4995055 = 7492583) B7492583
theorem B3995675 : Blo 1182408 3995675 := bstep (se 1 (by rfl) ⟨2996756, by rfl⟩ : syracuseStep 3995675 = 5993513) B5993513
theorem B1685551 : Blo 1182408 1685551 := bstep (se 1 (by rfl) ⟨1264163, by rfl⟩ : syracuseStep 1685551 = 2528327) B2528327
theorem B1775687 : Blo 1182408 1775687 := bstep (se 1 (by rfl) ⟨1331765, by rfl⟩ : syracuseStep 1775687 = 2663531) B2663531
theorem B2660543 : Blo 1182408 2660543 := bstep (se 1 (by rfl) ⟨1995407, by rfl⟩ : syracuseStep 2660543 = 3990815) B3990815
theorem B10803431 : Blo 1182408 10803431 := bstep (se 1 (by rfl) ⟨8102573, by rfl⟩ : syracuseStep 10803431 = 16205147) B16205147
theorem B1775927 : Blo 1182408 1775927 := bstep (se 1 (by rfl) ⟨1331945, by rfl⟩ : syracuseStep 1775927 = 2663891) B2663891
theorem B2996635 : Blo 1182408 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B3996539 : Blo 1182408 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B2661371 : Blo 1182408 2661371 := bstep (se 1 (by rfl) ⟨1996028, by rfl⟩ : syracuseStep 2661371 = 3992057) B3992057
theorem B2661479 : Blo 1182408 2661479 := bstep (se 1 (by rfl) ⟨1996109, by rfl⟩ : syracuseStep 2661479 = 3992219) B3992219
theorem B5987519 : Blo 1182408 5987519 := bstep (se 1 (by rfl) ⟨4490639, by rfl⟩ : syracuseStep 5987519 = 8981279) B8981279
theorem B14384719 : Blo 1182408 14384719 := bstep (se 1 (by rfl) ⟨10788539, by rfl⟩ : syracuseStep 14384719 = 21577079) B21577079
theorem B2662127 : Blo 1182408 2662127 := bstep (se 1 (by rfl) ⟨1996595, by rfl⟩ : syracuseStep 2662127 = 3993191) B3993191
theorem B22749173 : Blo 1182408 22749173 := bstep (se 5 (by rfl) ⟨1066367, by rfl⟩ : syracuseStep 22749173 = 2132735) B2132735
theorem B2883743 : Blo 1182408 2883743 := bstep (se 1 (by rfl) ⟨2162807, by rfl⟩ : syracuseStep 2883743 = 4325615) B4325615
theorem B4489775 : Blo 1182408 4489775 := bstep (se 1 (by rfl) ⟨3367331, by rfl⟩ : syracuseStep 4489775 = 6734663) B6734663
theorem B15164111 : Blo 1182408 15164111 := bstep (se 1 (by rfl) ⟨11373083, by rfl⟩ : syracuseStep 15164111 = 22746167) B22746167
theorem B2024441 : Blo 1182408 2024441 := bstep (se 2 (by rfl) ⟨759165, by rfl⟩ : syracuseStep 2024441 = 1518331) B1518331
theorem B2245897 : Blo 1182408 2245897 := bstep (se 2 (by rfl) ⟨842211, by rfl⟩ : syracuseStep 2245897 = 1684423) B1684423
theorem B2245943 : Blo 1182408 2245943 := bstep (se 1 (by rfl) ⟨1684457, by rfl⟩ : syracuseStep 2245943 = 3368915) B3368915
theorem B4490579 : Blo 1182408 4490579 := bstep (se 1 (by rfl) ⟨3367934, by rfl⟩ : syracuseStep 4490579 = 6735869) B6735869
theorem B2663783 : Blo 1182408 2663783 := bstep (se 1 (by rfl) ⟨1997837, by rfl⟩ : syracuseStep 2663783 = 3995675) B3995675
theorem B7202287 : Blo 1182408 7202287 := bstep (se 1 (by rfl) ⟨5401715, by rfl⟩ : syracuseStep 7202287 = 10803431) B10803431
theorem B16205579 : Blo 1182408 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B2664359 : Blo 1182408 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B1263719 : Blo 1182408 1263719 := bstep (se 1 (by rfl) ⟨947789, by rfl⟩ : syracuseStep 1263719 = 1895579) B1895579
theorem B19179625 : Blo 1182408 19179625 := bstep (se 2 (by rfl) ⟨7192359, by rfl⟩ : syracuseStep 19179625 = 14384719) B14384719
theorem B3991679 : Blo 1182408 3991679 := bstep (se 1 (by rfl) ⟨2993759, by rfl⟩ : syracuseStep 3991679 = 5987519) B5987519
theorem B8980793 : Blo 1182408 8980793 := bstep (se 2 (by rfl) ⟨3367797, by rfl⟩ : syracuseStep 8980793 = 6735595) B6735595
theorem B13486499 : Blo 1182408 13486499 := bstep (se 1 (by rfl) ⟨10114874, by rfl⟩ : syracuseStep 13486499 = 20229749) B20229749
theorem B15166115 : Blo 1182408 15166115 := bstep (se 1 (by rfl) ⟨11374586, by rfl⟩ : syracuseStep 15166115 = 22749173) B22749173
theorem B2247401 : Blo 1182408 2247401 := bstep (se 2 (by rfl) ⟨842775, by rfl⟩ : syracuseStep 2247401 = 1685551) B1685551
theorem B1182459 : Blo 1182408 1182459 := bstep (se 1 (by rfl) ⟨886844, by rfl⟩ : syracuseStep 1182459 = 1773689) B1773689
theorem B3992327 : Blo 1182408 3992327 := bstep (se 1 (by rfl) ⟨2994245, by rfl⟩ : syracuseStep 3992327 = 5988491) B5988491
theorem B2247887 : Blo 1182408 2247887 := bstep (se 1 (by rfl) ⟨1685915, by rfl⟩ : syracuseStep 2247887 = 3371831) B3371831
theorem B1182975 : Blo 1182408 1182975 := bstep (se 1 (by rfl) ⟨887231, by rfl⟩ : syracuseStep 1182975 = 1774463) B1774463
theorem B4492705 : Blo 1182408 4492705 := bstep (se 2 (by rfl) ⟨1684764, by rfl⟩ : syracuseStep 4492705 = 3369529) B3369529
theorem B38366783 : Blo 1182408 38366783 := bstep (se 1 (by rfl) ⟨28775087, by rfl⟩ : syracuseStep 38366783 = 57550175) B57550175
theorem B1330843 : Blo 1182408 1330843 := bstep (se 1 (by rfl) ⟨998132, by rfl⟩ : syracuseStep 1330843 = 1996265) B1996265
theorem B1183387 : Blo 1182408 1183387 := bstep (se 1 (by rfl) ⟨887540, by rfl⟩ : syracuseStep 1183387 = 1775081) B1775081
theorem B1330879 : Blo 1182408 1330879 := bstep (se 1 (by rfl) ⟨998159, by rfl⟩ : syracuseStep 1330879 = 1996319) B1996319
theorem B2248411 : Blo 1182408 2248411 := bstep (se 1 (by rfl) ⟨1686308, by rfl⟩ : syracuseStep 2248411 = 3372617) B3372617
theorem B12791695 : Blo 1182408 12791695 := bstep (se 1 (by rfl) ⟨9593771, by rfl⟩ : syracuseStep 12791695 = 19187543) B19187543
theorem B1183791 : Blo 1182408 1183791 := bstep (se 1 (by rfl) ⟨887843, by rfl⟩ : syracuseStep 1183791 = 1775687) B1775687
theorem B1773695 : Blo 1182408 1773695 := bstep (se 1 (by rfl) ⟨1330271, by rfl⟩ : syracuseStep 1773695 = 2660543) B2660543
theorem B1183951 : Blo 1182408 1183951 := bstep (se 1 (by rfl) ⟨887963, by rfl⟩ : syracuseStep 1183951 = 1775927) B1775927
theorem B5992865 : Blo 1182408 5992865 := bstep (se 2 (by rfl) ⟨2247324, by rfl⟩ : syracuseStep 5992865 = 4494649) B4494649
theorem B4264445 : Blo 1182408 4264445 := bstep (se 3 (by rfl) ⟨799583, by rfl⟩ : syracuseStep 4264445 = 1599167) B1599167
theorem B1774121 : Blo 1182408 1774121 := bstep (se 2 (by rfl) ⟨665295, by rfl⟩ : syracuseStep 1774121 = 1330591) B1330591
theorem B1774247 : Blo 1182408 1774247 := bstep (se 1 (by rfl) ⟨1330685, by rfl⟩ : syracuseStep 1774247 = 2661371) B2661371
theorem B1897129 : Blo 1182408 1897129 := bstep (se 2 (by rfl) ⟨711423, by rfl⟩ : syracuseStep 1897129 = 1422847) B1422847
theorem B1774319 : Blo 1182408 1774319 := bstep (se 1 (by rfl) ⟨1330739, by rfl⟩ : syracuseStep 1774319 = 2661479) B2661479
theorem B3371807 : Blo 1182408 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B2995177 : Blo 1182408 2995177 := bstep (se 2 (by rfl) ⟨1123191, by rfl⟩ : syracuseStep 2995177 = 2246383) B2246383
theorem B65664107 : Blo 1182408 65664107 := bstep (se 1 (by rfl) ⟨49248080, by rfl⟩ : syracuseStep 65664107 = 98496161) B98496161
theorem B1774751 : Blo 1182408 1774751 := bstep (se 1 (by rfl) ⟨1331063, by rfl⟩ : syracuseStep 1774751 = 2662127) B2662127
theorem B2995663 : Blo 1182408 2995663 := bstep (se 1 (by rfl) ⟨2246747, by rfl⟩ : syracuseStep 2995663 = 4493495) B4493495
theorem B3995135 : Blo 1182408 3995135 := bstep (se 1 (by rfl) ⟨2996351, by rfl⟩ : syracuseStep 3995135 = 5992703) B5992703
theorem B1775135 : Blo 1182408 1775135 := bstep (se 1 (by rfl) ⟨1331351, by rfl⟩ : syracuseStep 1775135 = 2662703) B2662703
theorem B1775159 : Blo 1182408 1775159 := bstep (se 1 (by rfl) ⟨1331369, by rfl⟩ : syracuseStep 1775159 = 2662739) B2662739
theorem B1775369 : Blo 1182408 1775369 := bstep (se 2 (by rfl) ⟨665763, by rfl⟩ : syracuseStep 1775369 = 1331527) B1331527
theorem B1775399 : Blo 1182408 1775399 := bstep (se 1 (by rfl) ⟨1331549, by rfl⟩ : syracuseStep 1775399 = 2663099) B2663099
theorem B1775471 : Blo 1182408 1775471 := bstep (se 1 (by rfl) ⟨1331603, by rfl⟩ : syracuseStep 1775471 = 2663207) B2663207
theorem B3995513 : Blo 1182408 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B9115517 : Blo 1182408 9115517 := bstep (se 3 (by rfl) ⟨1709159, by rfl⟩ : syracuseStep 9115517 = 3418319) B3418319
theorem B6485915 : Blo 1182408 6485915 := bstep (se 1 (by rfl) ⟨4864436, by rfl⟩ : syracuseStep 6485915 = 9728873) B9728873
theorem B2529215 : Blo 1182408 2529215 := bstep (se 1 (by rfl) ⟨1896911, by rfl⟩ : syracuseStep 2529215 = 3793823) B3793823
theorem B17053861 : Blo 1182408 17053861 := bstep (se 4 (by rfl) ⟨1598799, by rfl⟩ : syracuseStep 17053861 = 3197599) B3197599
theorem B3201191 : Blo 1182408 3201191 := bstep (se 1 (by rfl) ⟨2400893, by rfl⟩ : syracuseStep 3201191 = 4801787) B4801787
theorem B1775867 : Blo 1182408 1775867 := bstep (se 1 (by rfl) ⟨1331900, by rfl⟩ : syracuseStep 1775867 = 2663801) B2663801
theorem B1775993 : Blo 1182408 1775993 := bstep (se 2 (by rfl) ⟨665997, by rfl⟩ : syracuseStep 1775993 = 1331995) B1331995
theorem B1776287 : Blo 1182408 1776287 := bstep (se 1 (by rfl) ⟨1332215, by rfl⟩ : syracuseStep 1776287 = 2664431) B2664431
theorem B6396583 : Blo 1182408 6396583 := bstep (se 1 (by rfl) ⟨4797437, by rfl⟩ : syracuseStep 6396583 = 9594875) B9594875
theorem B2661587 : Blo 1182408 2661587 := bstep (se 1 (by rfl) ⟨1996190, by rfl⟩ : syracuseStep 2661587 = 3992381) B3992381
theorem B6660073 : Blo 1182408 6660073 := bstep (se 2 (by rfl) ⟨2497527, by rfl⟩ : syracuseStep 6660073 = 4995055) B4995055
theorem B10109407 : Blo 1182408 10109407 := bstep (se 1 (by rfl) ⟨7582055, by rfl⟩ : syracuseStep 10109407 = 15164111) B15164111
theorem B8528777 : Blo 1182408 8528777 := bstep (se 2 (by rfl) ⟨3198291, by rfl⟩ : syracuseStep 8528777 = 6396583) B6396583
theorem B2663423 : Blo 1182408 2663423 := bstep (se 1 (by rfl) ⟨1997567, by rfl⟩ : syracuseStep 2663423 = 3995135) B3995135
theorem B2663675 : Blo 1182408 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B11371853 : Blo 1182408 11371853 := bstep (se 3 (by rfl) ⟨2132222, by rfl⟩ : syracuseStep 11371853 = 4264445) B4264445
theorem B10110743 : Blo 1182408 10110743 := bstep (se 1 (by rfl) ⟨7583057, by rfl⟩ : syracuseStep 10110743 = 15166115) B15166115
theorem B5990273 : Blo 1182408 5990273 := bstep (se 2 (by rfl) ⟨2246352, by rfl⟩ : syracuseStep 5990273 = 4492705) B4492705
theorem B9603049 : Blo 1182408 9603049 := bstep (se 2 (by rfl) ⟨3601143, by rfl⟩ : syracuseStep 9603049 = 7202287) B7202287
theorem B24308045 : Blo 1182408 24308045 := bstep (se 3 (by rfl) ⟨4557758, by rfl⟩ : syracuseStep 24308045 = 9115517) B9115517
theorem B25577855 : Blo 1182408 25577855 := bstep (se 1 (by rfl) ⟨19183391, by rfl⟩ : syracuseStep 25577855 = 38366783) B38366783
theorem B1182463 : Blo 1182408 1182463 := bstep (se 1 (by rfl) ⟨886847, by rfl⟩ : syracuseStep 1182463 = 1773695) B1773695
theorem B3369917 : Blo 1182408 3369917 := bstep (se 3 (by rfl) ⟨631859, by rfl⟩ : syracuseStep 3369917 = 1263719) B1263719
theorem B1182747 : Blo 1182408 1182747 := bstep (se 1 (by rfl) ⟨887060, by rfl⟩ : syracuseStep 1182747 = 1774121) B1774121
theorem B2993183 : Blo 1182408 2993183 := bstep (se 1 (by rfl) ⟨2244887, by rfl⟩ : syracuseStep 2993183 = 4489775) B4489775
theorem B1182831 : Blo 1182408 1182831 := bstep (se 1 (by rfl) ⟨887123, by rfl⟩ : syracuseStep 1182831 = 1774247) B1774247
theorem B1182879 : Blo 1182408 1182879 := bstep (se 1 (by rfl) ⟨887159, by rfl⟩ : syracuseStep 1182879 = 1774319) B1774319
theorem B1183167 : Blo 1182408 1183167 := bstep (se 1 (by rfl) ⟨887375, by rfl⟩ : syracuseStep 1183167 = 1774751) B1774751
theorem B2993719 : Blo 1182408 2993719 := bstep (se 1 (by rfl) ⟨2245289, by rfl⟩ : syracuseStep 2993719 = 4490579) B4490579
theorem B1183423 : Blo 1182408 1183423 := bstep (se 1 (by rfl) ⟨887567, by rfl⟩ : syracuseStep 1183423 = 1775135) B1775135
theorem B1183439 : Blo 1182408 1183439 := bstep (se 1 (by rfl) ⟨887579, by rfl⟩ : syracuseStep 1183439 = 1775159) B1775159
theorem B1183579 : Blo 1182408 1183579 := bstep (se 1 (by rfl) ⟨887684, by rfl⟩ : syracuseStep 1183579 = 1775369) B1775369
theorem B1183599 : Blo 1182408 1183599 := bstep (se 1 (by rfl) ⟨887699, by rfl⟩ : syracuseStep 1183599 = 1775399) B1775399
theorem B1183647 : Blo 1182408 1183647 := bstep (se 1 (by rfl) ⟨887735, by rfl⟩ : syracuseStep 1183647 = 1775471) B1775471
theorem B3993569 : Blo 1182408 3993569 := bstep (se 2 (by rfl) ⟨1497588, by rfl⟩ : syracuseStep 3993569 = 2995177) B2995177
theorem B2134127 : Blo 1182408 2134127 := bstep (se 1 (by rfl) ⟨1600595, by rfl⟩ : syracuseStep 2134127 = 3201191) B3201191
theorem B1183911 : Blo 1182408 1183911 := bstep (se 1 (by rfl) ⟨887933, by rfl⟩ : syracuseStep 1183911 = 1775867) B1775867
theorem B1183995 : Blo 1182408 1183995 := bstep (se 1 (by rfl) ⟨887996, by rfl⟩ : syracuseStep 1183995 = 1775993) B1775993
theorem B8990999 : Blo 1182408 8990999 := bstep (se 1 (by rfl) ⟨6743249, by rfl⟩ : syracuseStep 8990999 = 13486499) B13486499
theorem B2994529 : Blo 1182408 2994529 := bstep (se 2 (by rfl) ⟨1122948, by rfl⟩ : syracuseStep 2994529 = 2245897) B2245897
theorem B1184191 : Blo 1182408 1184191 := bstep (se 1 (by rfl) ⟨888143, by rfl⟩ : syracuseStep 1184191 = 1776287) B1776287
theorem B3994217 : Blo 1182408 3994217 := bstep (se 2 (by rfl) ⟨1497831, by rfl⟩ : syracuseStep 3994217 = 2995663) B2995663
theorem B8991485 : Blo 1182408 8991485 := bstep (se 3 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 8991485 = 3371807) B3371807
theorem B1774391 : Blo 1182408 1774391 := bstep (se 1 (by rfl) ⟨1330793, by rfl⟩ : syracuseStep 1774391 = 2661587) B2661587
theorem B1774457 : Blo 1182408 1774457 := bstep (se 2 (by rfl) ⟨665421, by rfl⟩ : syracuseStep 1774457 = 1330843) B1330843
theorem B1774505 : Blo 1182408 1774505 := bstep (se 2 (by rfl) ⟨665439, by rfl⟩ : syracuseStep 1774505 = 1330879) B1330879
theorem B1922495 : Blo 1182408 1922495 := bstep (se 1 (by rfl) ⟨1441871, by rfl⟩ : syracuseStep 1922495 = 2883743) B2883743
theorem B25572833 : Blo 1182408 25572833 := bstep (se 2 (by rfl) ⟨9589812, by rfl⟩ : syracuseStep 25572833 = 19179625) B19179625
theorem B22738481 : Blo 1182408 22738481 := bstep (se 2 (by rfl) ⟨8526930, by rfl⟩ : syracuseStep 22738481 = 17053861) B17053861
theorem B3995243 : Blo 1182408 3995243 := bstep (se 1 (by rfl) ⟨2996432, by rfl⟩ : syracuseStep 3995243 = 5992865) B5992865
theorem B1349627 : Blo 1182408 1349627 := bstep (se 1 (by rfl) ⟨1012220, by rfl⟩ : syracuseStep 1349627 = 2024441) B2024441
theorem B43776071 : Blo 1182408 43776071 := bstep (se 1 (by rfl) ⟨32832053, by rfl⟩ : syracuseStep 43776071 = 65664107) B65664107
theorem B1497295 : Blo 1182408 1497295 := bstep (se 1 (by rfl) ⟨1122971, by rfl⟩ : syracuseStep 1497295 = 2245943) B2245943
theorem B2529505 : Blo 1182408 2529505 := bstep (se 2 (by rfl) ⟨948564, by rfl⟩ : syracuseStep 2529505 = 1897129) B1897129
theorem B1775855 : Blo 1182408 1775855 := bstep (se 1 (by rfl) ⟨1331891, by rfl⟩ : syracuseStep 1775855 = 2663783) B2663783
theorem B10803719 : Blo 1182408 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B4323943 : Blo 1182408 4323943 := bstep (se 1 (by rfl) ⟨3242957, by rfl⟩ : syracuseStep 4323943 = 6485915) B6485915
theorem B1776239 : Blo 1182408 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B1686143 : Blo 1182408 1686143 := bstep (se 1 (by rfl) ⟨1264607, by rfl⟩ : syracuseStep 1686143 = 2529215) B2529215
theorem B2661119 : Blo 1182408 2661119 := bstep (se 1 (by rfl) ⟨1995839, by rfl⟩ : syracuseStep 2661119 = 3991679) B3991679
theorem B5987195 : Blo 1182408 5987195 := bstep (se 1 (by rfl) ⟨4490396, by rfl⟩ : syracuseStep 5987195 = 8980793) B8980793
theorem B1498267 : Blo 1182408 1498267 := bstep (se 1 (by rfl) ⟨1123700, by rfl⟩ : syracuseStep 1498267 = 2247401) B2247401
theorem B2661551 : Blo 1182408 2661551 := bstep (se 1 (by rfl) ⟨1996163, by rfl⟩ : syracuseStep 2661551 = 3992327) B3992327
theorem B1498591 : Blo 1182408 1498591 := bstep (se 1 (by rfl) ⟨1123943, by rfl⟩ : syracuseStep 1498591 = 2247887) B2247887
theorem B2997881 : Blo 1182408 2997881 := bstep (se 2 (by rfl) ⟨1124205, by rfl⟩ : syracuseStep 2997881 = 2248411) B2248411
theorem B17055593 : Blo 1182408 17055593 := bstep (se 2 (by rfl) ⟨6395847, by rfl⟩ : syracuseStep 17055593 = 12791695) B12791695
theorem B8880097 : Blo 1182408 8880097 := bstep (se 2 (by rfl) ⟨3330036, by rfl⟩ : syracuseStep 8880097 = 6660073) B6660073
theorem B2662811 : Blo 1182408 2662811 := bstep (se 1 (by rfl) ⟨1997108, by rfl⟩ : syracuseStep 2662811 = 3994217) B3994217
theorem B5685851 : Blo 1182408 5685851 := bstep (se 1 (by rfl) ⟨4264388, by rfl⟩ : syracuseStep 5685851 = 8528777) B8528777
theorem B17048555 : Blo 1182408 17048555 := bstep (se 1 (by rfl) ⟨12786416, by rfl⟩ : syracuseStep 17048555 = 25572833) B25572833
theorem B2663495 : Blo 1182408 2663495 := bstep (se 1 (by rfl) ⟨1997621, by rfl⟩ : syracuseStep 2663495 = 3995243) B3995243
theorem B16205363 : Blo 1182408 16205363 := bstep (se 1 (by rfl) ⟨12154022, by rfl⟩ : syracuseStep 16205363 = 24308045) B24308045
theorem B3991463 : Blo 1182408 3991463 := bstep (se 1 (by rfl) ⟨2993597, by rfl⟩ : syracuseStep 3991463 = 5987195) B5987195
theorem B2246611 : Blo 1182408 2246611 := bstep (se 1 (by rfl) ⟨1684958, by rfl⟩ : syracuseStep 2246611 = 3369917) B3369917
theorem B3991625 : Blo 1182408 3991625 := bstep (se 2 (by rfl) ⟨1496859, by rfl⟩ : syracuseStep 3991625 = 2993719) B2993719
theorem B11840129 : Blo 1182408 11840129 := bstep (se 2 (by rfl) ⟨4440048, by rfl⟩ : syracuseStep 11840129 = 8880097) B8880097
theorem B3599005 : Blo 1182408 3599005 := bstep (se 3 (by rfl) ⟨674813, by rfl⟩ : syracuseStep 3599005 = 1349627) B1349627
theorem B3992705 : Blo 1182408 3992705 := bstep (se 2 (by rfl) ⟨1497264, by rfl⟩ : syracuseStep 3992705 = 2994529) B2994529
theorem B1182927 : Blo 1182408 1182927 := bstep (se 1 (by rfl) ⟨887195, by rfl⟩ : syracuseStep 1182927 = 1774391) B1774391
theorem B1182971 : Blo 1182408 1182971 := bstep (se 1 (by rfl) ⟨887228, by rfl⟩ : syracuseStep 1182971 = 1774457) B1774457
theorem B1183003 : Blo 1182408 1183003 := bstep (se 1 (by rfl) ⟨887252, by rfl⟩ : syracuseStep 1183003 = 1774505) B1774505
theorem B13479209 : Blo 1182408 13479209 := bstep (se 2 (by rfl) ⟨5054703, by rfl⟩ : syracuseStep 13479209 = 10109407) B10109407
theorem B15158987 : Blo 1182408 15158987 := bstep (se 1 (by rfl) ⟨11369240, by rfl⟩ : syracuseStep 15158987 = 22738481) B22738481
theorem B3993515 : Blo 1182408 3993515 := bstep (se 1 (by rfl) ⟨2995136, by rfl⟩ : syracuseStep 3993515 = 5990273) B5990273
theorem B29184047 : Blo 1182408 29184047 := bstep (se 1 (by rfl) ⟨21888035, by rfl⟩ : syracuseStep 29184047 = 43776071) B43776071
theorem B1183903 : Blo 1182408 1183903 := bstep (se 1 (by rfl) ⟨887927, by rfl⟩ : syracuseStep 1183903 = 1775855) B1775855
theorem B17051903 : Blo 1182408 17051903 := bstep (se 1 (by rfl) ⟨12788927, by rfl⟩ : syracuseStep 17051903 = 25577855) B25577855
theorem B1184159 : Blo 1182408 1184159 := bstep (se 1 (by rfl) ⟨888119, by rfl⟩ : syracuseStep 1184159 = 1776239) B1776239
theorem B1774079 : Blo 1182408 1774079 := bstep (se 1 (by rfl) ⟨1330559, by rfl⟩ : syracuseStep 1774079 = 2661119) B2661119
theorem B1995455 : Blo 1182408 1995455 := bstep (se 1 (by rfl) ⟨1496591, by rfl⟩ : syracuseStep 1995455 = 2993183) B2993183
theorem B1774367 : Blo 1182408 1774367 := bstep (se 1 (by rfl) ⟨1330775, by rfl⟩ : syracuseStep 1774367 = 2661551) B2661551
theorem B1422751 : Blo 1182408 1422751 := bstep (se 1 (by rfl) ⟨1067063, by rfl⟩ : syracuseStep 1422751 = 2134127) B2134127
theorem B5993999 : Blo 1182408 5993999 := bstep (se 1 (by rfl) ⟨4495499, by rfl⟩ : syracuseStep 5993999 = 8990999) B8990999
theorem B1996393 : Blo 1182408 1996393 := bstep (se 2 (by rfl) ⟨748647, by rfl⟩ : syracuseStep 1996393 = 1497295) B1497295
theorem B3372673 : Blo 1182408 3372673 := bstep (se 2 (by rfl) ⟨1264752, by rfl⟩ : syracuseStep 3372673 = 2529505) B2529505
theorem B5994323 : Blo 1182408 5994323 := bstep (se 1 (by rfl) ⟨4495742, by rfl⟩ : syracuseStep 5994323 = 8991485) B8991485
theorem B1775615 : Blo 1182408 1775615 := bstep (se 1 (by rfl) ⟨1331711, by rfl⟩ : syracuseStep 1775615 = 2663423) B2663423
theorem B5765257 : Blo 1182408 5765257 := bstep (se 2 (by rfl) ⟨2161971, by rfl⟩ : syracuseStep 5765257 = 4323943) B4323943
theorem B1775783 : Blo 1182408 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B30324941 : Blo 1182408 30324941 := bstep (se 3 (by rfl) ⟨5685926, by rfl⟩ : syracuseStep 30324941 = 11371853) B11371853
theorem B5126653 : Blo 1182408 5126653 := bstep (se 3 (by rfl) ⟨961247, by rfl⟩ : syracuseStep 5126653 = 1922495) B1922495
theorem B6740495 : Blo 1182408 6740495 := bstep (se 1 (by rfl) ⟨5055371, by rfl⟩ : syracuseStep 6740495 = 10110743) B10110743
theorem B28809917 : Blo 1182408 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B1997689 : Blo 1182408 1997689 := bstep (se 2 (by rfl) ⟨749133, by rfl⟩ : syracuseStep 1997689 = 1498267) B1498267
theorem B4496381 : Blo 1182408 4496381 := bstep (se 3 (by rfl) ⟨843071, by rfl⟩ : syracuseStep 4496381 = 1686143) B1686143
theorem B1998121 : Blo 1182408 1998121 := bstep (se 2 (by rfl) ⟨749295, by rfl⟩ : syracuseStep 1998121 = 1498591) B1498591
theorem B1998587 : Blo 1182408 1998587 := bstep (se 1 (by rfl) ⟨1498940, by rfl⟩ : syracuseStep 1998587 = 2997881) B2997881
theorem B11370395 : Blo 1182408 11370395 := bstep (se 1 (by rfl) ⟨8527796, by rfl⟩ : syracuseStep 11370395 = 17055593) B17055593
theorem B12804065 : Blo 1182408 12804065 := bstep (se 2 (by rfl) ⟨4801524, by rfl⟩ : syracuseStep 12804065 = 9603049) B9603049
theorem B2662379 : Blo 1182408 2662379 := bstep (se 1 (by rfl) ⟨1996784, by rfl⟩ : syracuseStep 2662379 = 3993569) B3993569
theorem B19456031 : Blo 1182408 19456031 := bstep (se 1 (by rfl) ⟨14592023, by rfl⟩ : syracuseStep 19456031 = 29184047) B29184047
theorem B2663585 : Blo 1182408 2663585 := bstep (se 2 (by rfl) ⟨998844, by rfl⟩ : syracuseStep 2663585 = 1997689) B1997689
theorem B2664161 : Blo 1182408 2664161 := bstep (se 2 (by rfl) ⟨999060, by rfl⟩ : syracuseStep 2664161 = 1998121) B1998121
theorem B7580263 : Blo 1182408 7580263 := bstep (se 1 (by rfl) ⟨5685197, by rfl⟩ : syracuseStep 7580263 = 11370395) B11370395
theorem B7687009 : Blo 1182408 7687009 := bstep (se 2 (by rfl) ⟨2882628, by rfl⟩ : syracuseStep 7687009 = 5765257) B5765257
theorem B1182719 : Blo 1182408 1182719 := bstep (se 1 (by rfl) ⟨887039, by rfl⟩ : syracuseStep 1182719 = 1774079) B1774079
theorem B1330303 : Blo 1182408 1330303 := bstep (se 1 (by rfl) ⟨997727, by rfl⟩ : syracuseStep 1330303 = 1995455) B1995455
theorem B1182911 : Blo 1182408 1182911 := bstep (se 1 (by rfl) ⟨887183, by rfl⟩ : syracuseStep 1182911 = 1774367) B1774367
theorem B11365703 : Blo 1182408 11365703 := bstep (se 1 (by rfl) ⟨8524277, by rfl⟩ : syracuseStep 11365703 = 17048555) B17048555
theorem B6835537 : Blo 1182408 6835537 := bstep (se 2 (by rfl) ⟨2563326, by rfl⟩ : syracuseStep 6835537 = 5126653) B5126653
theorem B1183743 : Blo 1182408 1183743 := bstep (se 1 (by rfl) ⟨887807, by rfl⟩ : syracuseStep 1183743 = 1775615) B1775615
theorem B1183855 : Blo 1182408 1183855 := bstep (se 1 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 1183855 = 1775783) B1775783
theorem B4493663 : Blo 1182408 4493663 := bstep (se 1 (by rfl) ⟨3370247, by rfl⟩ : syracuseStep 4493663 = 6740495) B6740495
theorem B19206611 : Blo 1182408 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B1897001 : Blo 1182408 1897001 := bstep (se 2 (by rfl) ⟨711375, by rfl⟩ : syracuseStep 1897001 = 1422751) B1422751
theorem B10105991 : Blo 1182408 10105991 := bstep (se 1 (by rfl) ⟨7579493, by rfl⟩ : syracuseStep 10105991 = 15158987) B15158987
theorem B1332391 : Blo 1182408 1332391 := bstep (se 1 (by rfl) ⟨999293, by rfl⟩ : syracuseStep 1332391 = 1998587) B1998587
theorem B2995481 : Blo 1182408 2995481 := bstep (se 2 (by rfl) ⟨1123305, by rfl⟩ : syracuseStep 2995481 = 2246611) B2246611
theorem B1774919 : Blo 1182408 1774919 := bstep (se 1 (by rfl) ⟨1331189, by rfl⟩ : syracuseStep 1774919 = 2662379) B2662379
theorem B11367935 : Blo 1182408 11367935 := bstep (se 1 (by rfl) ⟨8525951, by rfl⟩ : syracuseStep 11367935 = 17051903) B17051903
theorem B1775207 : Blo 1182408 1775207 := bstep (se 1 (by rfl) ⟨1331405, by rfl⟩ : syracuseStep 1775207 = 2662811) B2662811
theorem B3790567 : Blo 1182408 3790567 := bstep (se 1 (by rfl) ⟨2842925, by rfl⟩ : syracuseStep 3790567 = 5685851) B5685851
theorem B1775663 : Blo 1182408 1775663 := bstep (se 1 (by rfl) ⟨1331747, by rfl⟩ : syracuseStep 1775663 = 2663495) B2663495
theorem B4798673 : Blo 1182408 4798673 := bstep (se 2 (by rfl) ⟨1799502, by rfl⟩ : syracuseStep 4798673 = 3599005) B3599005
theorem B3995999 : Blo 1182408 3995999 := bstep (se 1 (by rfl) ⟨2996999, by rfl⟩ : syracuseStep 3995999 = 5993999) B5993999
theorem B10803575 : Blo 1182408 10803575 := bstep (se 1 (by rfl) ⟨8102681, by rfl⟩ : syracuseStep 10803575 = 16205363) B16205363
theorem B3996215 : Blo 1182408 3996215 := bstep (se 1 (by rfl) ⟨2997161, by rfl⟩ : syracuseStep 3996215 = 5994323) B5994323
theorem B2660975 : Blo 1182408 2660975 := bstep (se 1 (by rfl) ⟨1995731, by rfl⟩ : syracuseStep 2660975 = 3991463) B3991463
theorem B126294709 : Blo 1182408 126294709 := bstep (se 5 (by rfl) ⟨5920064, by rfl⟩ : syracuseStep 126294709 = 11840129) B11840129
theorem B2661083 : Blo 1182408 2661083 := bstep (se 1 (by rfl) ⟨1995812, by rfl⟩ : syracuseStep 2661083 = 3991625) B3991625
theorem B20216627 : Blo 1182408 20216627 := bstep (se 1 (by rfl) ⟨15162470, by rfl⟩ : syracuseStep 20216627 = 30324941) B30324941
theorem B2997587 : Blo 1182408 2997587 := bstep (se 1 (by rfl) ⟨2248190, by rfl⟩ : syracuseStep 2997587 = 4496381) B4496381
theorem B2661803 : Blo 1182408 2661803 := bstep (se 1 (by rfl) ⟨1996352, by rfl⟩ : syracuseStep 2661803 = 3992705) B3992705
theorem B2661857 : Blo 1182408 2661857 := bstep (se 2 (by rfl) ⟨998196, by rfl⟩ : syracuseStep 2661857 = 1996393) B1996393
theorem B4496897 : Blo 1182408 4496897 := bstep (se 2 (by rfl) ⟨1686336, by rfl⟩ : syracuseStep 4496897 = 3372673) B3372673
theorem B8986139 : Blo 1182408 8986139 := bstep (se 1 (by rfl) ⟨6739604, by rfl⟩ : syracuseStep 8986139 = 13479209) B13479209
theorem B2662343 : Blo 1182408 2662343 := bstep (se 1 (by rfl) ⟨1996757, by rfl⟩ : syracuseStep 2662343 = 3993515) B3993515
theorem B8536043 : Blo 1182408 8536043 := bstep (se 1 (by rfl) ⟨6402032, by rfl⟩ : syracuseStep 8536043 = 12804065) B12804065
theorem B12804407 : Blo 1182408 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B7578623 : Blo 1182408 7578623 := bstep (se 1 (by rfl) ⟨5683967, by rfl⟩ : syracuseStep 7578623 = 11367935) B11367935
theorem B10249345 : Blo 1182408 10249345 := bstep (se 2 (by rfl) ⟨3843504, by rfl⟩ : syracuseStep 10249345 = 7687009) B7687009
theorem B2663999 : Blo 1182408 2663999 := bstep (se 1 (by rfl) ⟨1997999, by rfl⟩ : syracuseStep 2663999 = 3995999) B3995999
theorem B2664143 : Blo 1182408 2664143 := bstep (se 1 (by rfl) ⟨1998107, by rfl⟩ : syracuseStep 2664143 = 3996215) B3996215
theorem B13477751 : Blo 1182408 13477751 := bstep (se 1 (by rfl) ⟨10108313, by rfl⟩ : syracuseStep 13477751 = 20216627) B20216627
theorem B5990759 : Blo 1182408 5990759 := bstep (se 1 (by rfl) ⟨4493069, by rfl⟩ : syracuseStep 5990759 = 8986139) B8986139
theorem B12970687 : Blo 1182408 12970687 := bstep (se 1 (by rfl) ⟨9728015, by rfl⟩ : syracuseStep 12970687 = 19456031) B19456031
theorem B1264667 : Blo 1182408 1264667 := bstep (se 1 (by rfl) ⟨948500, by rfl⟩ : syracuseStep 1264667 = 1897001) B1897001
theorem B6737327 : Blo 1182408 6737327 := bstep (se 1 (by rfl) ⟨5052995, by rfl⟩ : syracuseStep 6737327 = 10105991) B10105991
theorem B1183279 : Blo 1182408 1183279 := bstep (se 1 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 1183279 = 1774919) B1774919
theorem B1183471 : Blo 1182408 1183471 := bstep (se 1 (by rfl) ⟨887603, by rfl⟩ : syracuseStep 1183471 = 1775207) B1775207
theorem B1183775 : Blo 1182408 1183775 := bstep (se 1 (by rfl) ⟨887831, by rfl⟩ : syracuseStep 1183775 = 1775663) B1775663
theorem B3199115 : Blo 1182408 3199115 := bstep (se 1 (by rfl) ⟨2399336, by rfl⟩ : syracuseStep 3199115 = 4798673) B4798673
theorem B1773737 : Blo 1182408 1773737 := bstep (se 2 (by rfl) ⟨665151, by rfl⟩ : syracuseStep 1773737 = 1330303) B1330303
theorem B1773983 : Blo 1182408 1773983 := bstep (se 1 (by rfl) ⟨1330487, by rfl⟩ : syracuseStep 1773983 = 2660975) B2660975
theorem B9114049 : Blo 1182408 9114049 := bstep (se 2 (by rfl) ⟨3417768, by rfl⟩ : syracuseStep 9114049 = 6835537) B6835537
theorem B1774055 : Blo 1182408 1774055 := bstep (se 1 (by rfl) ⟨1330541, by rfl⟩ : syracuseStep 1774055 = 2661083) B2661083
theorem B1774535 : Blo 1182408 1774535 := bstep (se 1 (by rfl) ⟨1330901, by rfl⟩ : syracuseStep 1774535 = 2661803) B2661803
theorem B1774571 : Blo 1182408 1774571 := bstep (se 1 (by rfl) ⟨1330928, by rfl⟩ : syracuseStep 1774571 = 2661857) B2661857
theorem B1774895 : Blo 1182408 1774895 := bstep (se 1 (by rfl) ⟨1331171, by rfl⟩ : syracuseStep 1774895 = 2662343) B2662343
theorem B5690695 : Blo 1182408 5690695 := bstep (se 1 (by rfl) ⟨4268021, by rfl⟩ : syracuseStep 5690695 = 8536043) B8536043
theorem B2995775 : Blo 1182408 2995775 := bstep (se 1 (by rfl) ⟨2246831, by rfl⟩ : syracuseStep 2995775 = 4493663) B4493663
theorem B1775723 : Blo 1182408 1775723 := bstep (se 1 (by rfl) ⟨1331792, by rfl⟩ : syracuseStep 1775723 = 2663585) B2663585
theorem B10107017 : Blo 1182408 10107017 := bstep (se 2 (by rfl) ⟨3790131, by rfl⟩ : syracuseStep 10107017 = 7580263) B7580263
theorem B1996987 : Blo 1182408 1996987 := bstep (se 1 (by rfl) ⟨1497740, by rfl⟩ : syracuseStep 1996987 = 2995481) B2995481
theorem B168392945 : Blo 1182408 168392945 := bstep (se 2 (by rfl) ⟨63147354, by rfl⟩ : syracuseStep 168392945 = 126294709) B126294709
theorem B28809533 : Blo 1182408 28809533 := bstep (se 3 (by rfl) ⟨5401787, by rfl⟩ : syracuseStep 28809533 = 10803575) B10803575
theorem B1776107 : Blo 1182408 1776107 := bstep (se 1 (by rfl) ⟨1332080, by rfl⟩ : syracuseStep 1776107 = 2664161) B2664161
theorem B1776521 : Blo 1182408 1776521 := bstep (se 2 (by rfl) ⟨666195, by rfl⟩ : syracuseStep 1776521 = 1332391) B1332391
theorem B7577135 : Blo 1182408 7577135 := bstep (se 1 (by rfl) ⟨5682851, by rfl⟩ : syracuseStep 7577135 = 11365703) B11365703
theorem B1998391 : Blo 1182408 1998391 := bstep (se 1 (by rfl) ⟨1498793, by rfl⟩ : syracuseStep 1998391 = 2997587) B2997587
theorem B5054089 : Blo 1182408 5054089 := bstep (se 2 (by rfl) ⟨1895283, by rfl⟩ : syracuseStep 5054089 = 3790567) B3790567
theorem B2997931 : Blo 1182408 2997931 := bstep (se 1 (by rfl) ⟨2248448, by rfl⟩ : syracuseStep 2997931 = 4496897) B4496897
theorem B8536271 : Blo 1182408 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B2662649 : Blo 1182408 2662649 := bstep (se 2 (by rfl) ⟨998493, by rfl⟩ : syracuseStep 2662649 = 1996987) B1996987
theorem B17294249 : Blo 1182408 17294249 := bstep (se 2 (by rfl) ⟨6485343, by rfl⟩ : syracuseStep 17294249 = 12970687) B12970687
theorem B7587593 : Blo 1182408 7587593 := bstep (se 2 (by rfl) ⟨2845347, by rfl⟩ : syracuseStep 7587593 = 5690695) B5690695
theorem B2664521 : Blo 1182408 2664521 := bstep (se 2 (by rfl) ⟨999195, by rfl⟩ : syracuseStep 2664521 = 1998391) B1998391
theorem B4491551 : Blo 1182408 4491551 := bstep (se 1 (by rfl) ⟨3368663, by rfl⟩ : syracuseStep 4491551 = 6737327) B6737327
theorem B2132743 : Blo 1182408 2132743 := bstep (se 1 (by rfl) ⟨1599557, by rfl⟩ : syracuseStep 2132743 = 3199115) B3199115
theorem B1182491 : Blo 1182408 1182491 := bstep (se 1 (by rfl) ⟨886868, by rfl⟩ : syracuseStep 1182491 = 1773737) B1773737
theorem B1182655 : Blo 1182408 1182655 := bstep (se 1 (by rfl) ⟨886991, by rfl⟩ : syracuseStep 1182655 = 1773983) B1773983
theorem B1182703 : Blo 1182408 1182703 := bstep (se 1 (by rfl) ⟨887027, by rfl⟩ : syracuseStep 1182703 = 1774055) B1774055
theorem B12152065 : Blo 1182408 12152065 := bstep (se 2 (by rfl) ⟨4557024, by rfl⟩ : syracuseStep 12152065 = 9114049) B9114049
theorem B1183023 : Blo 1182408 1183023 := bstep (se 1 (by rfl) ⟨887267, by rfl⟩ : syracuseStep 1183023 = 1774535) B1774535
theorem B1183047 : Blo 1182408 1183047 := bstep (se 1 (by rfl) ⟨887285, by rfl⟩ : syracuseStep 1183047 = 1774571) B1774571
theorem B1183263 : Blo 1182408 1183263 := bstep (se 1 (by rfl) ⟨887447, by rfl⟩ : syracuseStep 1183263 = 1774895) B1774895
theorem B1183815 : Blo 1182408 1183815 := bstep (se 1 (by rfl) ⟨887861, by rfl⟩ : syracuseStep 1183815 = 1775723) B1775723
theorem B6738011 : Blo 1182408 6738011 := bstep (se 1 (by rfl) ⟨5053508, by rfl⟩ : syracuseStep 6738011 = 10107017) B10107017
theorem B19206355 : Blo 1182408 19206355 := bstep (se 1 (by rfl) ⟨14404766, by rfl⟩ : syracuseStep 19206355 = 28809533) B28809533
theorem B3993839 : Blo 1182408 3993839 := bstep (se 1 (by rfl) ⟨2995379, by rfl⟩ : syracuseStep 3993839 = 5990759) B5990759
theorem B1184071 : Blo 1182408 1184071 := bstep (se 1 (by rfl) ⟨888053, by rfl⟩ : syracuseStep 1184071 = 1776107) B1776107
theorem B1184347 : Blo 1182408 1184347 := bstep (se 1 (by rfl) ⟨888260, by rfl⟩ : syracuseStep 1184347 = 1776521) B1776521
theorem B6738785 : Blo 1182408 6738785 := bstep (se 2 (by rfl) ⟨2527044, by rfl⟩ : syracuseStep 6738785 = 5054089) B5054089
theorem B5051423 : Blo 1182408 5051423 := bstep (se 1 (by rfl) ⟨3788567, by rfl⟩ : syracuseStep 5051423 = 7577135) B7577135
theorem B3372445 : Blo 1182408 3372445 := bstep (se 3 (by rfl) ⟨632333, by rfl⟩ : syracuseStep 3372445 = 1264667) B1264667
theorem B5052415 : Blo 1182408 5052415 := bstep (se 1 (by rfl) ⟨3789311, by rfl⟩ : syracuseStep 5052415 = 7578623) B7578623
theorem B54663173 : Blo 1182408 54663173 := bstep (se 4 (by rfl) ⟨5124672, by rfl⟩ : syracuseStep 54663173 = 10249345) B10249345
theorem B1997183 : Blo 1182408 1997183 := bstep (se 1 (by rfl) ⟨1497887, by rfl⟩ : syracuseStep 1997183 = 2995775) B2995775
theorem B1775999 : Blo 1182408 1775999 := bstep (se 1 (by rfl) ⟨1331999, by rfl⟩ : syracuseStep 1775999 = 2663999) B2663999
theorem B1776095 : Blo 1182408 1776095 := bstep (se 1 (by rfl) ⟨1332071, by rfl⟩ : syracuseStep 1776095 = 2664143) B2664143
theorem B8985167 : Blo 1182408 8985167 := bstep (se 1 (by rfl) ⟨6738875, by rfl⟩ : syracuseStep 8985167 = 13477751) B13477751
theorem B112261963 : Blo 1182408 112261963 := bstep (se 1 (by rfl) ⟨84196472, by rfl⟩ : syracuseStep 112261963 = 168392945) B168392945
theorem B3997241 : Blo 1182408 3997241 := bstep (se 2 (by rfl) ⟨1498965, by rfl⟩ : syracuseStep 3997241 = 2997931) B2997931
theorem B2662559 : Blo 1182408 2662559 := bstep (se 1 (by rfl) ⟨1996919, by rfl⟩ : syracuseStep 2662559 = 3993839) B3993839
theorem B25608473 : Blo 1182408 25608473 := bstep (se 2 (by rfl) ⟨9603177, by rfl⟩ : syracuseStep 25608473 = 19206355) B19206355
theorem B2843657 : Blo 1182408 2843657 := bstep (se 2 (by rfl) ⟨1066371, by rfl⟩ : syracuseStep 2843657 = 2132743) B2132743
theorem B5990111 : Blo 1182408 5990111 := bstep (se 1 (by rfl) ⟨4492583, by rfl⟩ : syracuseStep 5990111 = 8985167) B8985167
theorem B2664827 : Blo 1182408 2664827 := bstep (se 1 (by rfl) ⟨1998620, by rfl⟩ : syracuseStep 2664827 = 3997241) B3997241
theorem B6736553 : Blo 1182408 6736553 := bstep (se 2 (by rfl) ⟨2526207, by rfl⟩ : syracuseStep 6736553 = 5052415) B5052415
theorem B4492007 : Blo 1182408 4492007 := bstep (se 1 (by rfl) ⟨3369005, by rfl⟩ : syracuseStep 4492007 = 6738011) B6738011
theorem B13470461 : Blo 1182408 13470461 := bstep (se 3 (by rfl) ⟨2525711, by rfl⟩ : syracuseStep 13470461 = 5051423) B5051423
theorem B4492523 : Blo 1182408 4492523 := bstep (se 1 (by rfl) ⟨3369392, by rfl⟩ : syracuseStep 4492523 = 6738785) B6738785
theorem B5058395 : Blo 1182408 5058395 := bstep (se 1 (by rfl) ⟨3793796, by rfl⟩ : syracuseStep 5058395 = 7587593) B7587593
theorem B36442115 : Blo 1182408 36442115 := bstep (se 1 (by rfl) ⟨27331586, by rfl⟩ : syracuseStep 36442115 = 54663173) B54663173
theorem B2994367 : Blo 1182408 2994367 := bstep (se 1 (by rfl) ⟨2245775, by rfl⟩ : syracuseStep 2994367 = 4491551) B4491551
theorem B1331455 : Blo 1182408 1331455 := bstep (se 1 (by rfl) ⟨998591, by rfl⟩ : syracuseStep 1331455 = 1997183) B1997183
theorem B1183999 : Blo 1182408 1183999 := bstep (se 1 (by rfl) ⟨887999, by rfl⟩ : syracuseStep 1183999 = 1775999) B1775999
theorem B1184063 : Blo 1182408 1184063 := bstep (se 1 (by rfl) ⟨888047, by rfl⟩ : syracuseStep 1184063 = 1776095) B1776095
theorem B46117997 : Blo 1182408 46117997 := bstep (se 3 (by rfl) ⟨8647124, by rfl⟩ : syracuseStep 46117997 = 17294249) B17294249
theorem B1775099 : Blo 1182408 1775099 := bstep (se 1 (by rfl) ⟨1331324, by rfl⟩ : syracuseStep 1775099 = 2662649) B2662649
theorem B22763389 : Blo 1182408 22763389 := bstep (se 3 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 22763389 = 8536271) B8536271
theorem B149682617 : Blo 1182408 149682617 := bstep (se 2 (by rfl) ⟨56130981, by rfl⟩ : syracuseStep 149682617 = 112261963) B112261963
theorem B1776347 : Blo 1182408 1776347 := bstep (se 1 (by rfl) ⟨1332260, by rfl⟩ : syracuseStep 1776347 = 2664521) B2664521
theorem B16202753 : Blo 1182408 16202753 := bstep (se 2 (by rfl) ⟨6076032, by rfl⟩ : syracuseStep 16202753 = 12152065) B12152065
theorem B4496593 : Blo 1182408 4496593 := bstep (se 2 (by rfl) ⟨1686222, by rfl⟩ : syracuseStep 4496593 = 3372445) B3372445
theorem B17072315 : Blo 1182408 17072315 := bstep (se 1 (by rfl) ⟨12804236, by rfl⟩ : syracuseStep 17072315 = 25608473) B25608473
theorem B30745331 : Blo 1182408 30745331 := bstep (se 1 (by rfl) ⟨23058998, by rfl⟩ : syracuseStep 30745331 = 46117997) B46117997
theorem B99788411 : Blo 1182408 99788411 := bstep (se 1 (by rfl) ⟨74841308, by rfl⟩ : syracuseStep 99788411 = 149682617) B149682617
theorem B4491035 : Blo 1182408 4491035 := bstep (se 1 (by rfl) ⟨3368276, by rfl⟩ : syracuseStep 4491035 = 6736553) B6736553
theorem B8980307 : Blo 1182408 8980307 := bstep (se 1 (by rfl) ⟨6735230, by rfl⟩ : syracuseStep 8980307 = 13470461) B13470461
theorem B3992489 : Blo 1182408 3992489 := bstep (se 2 (by rfl) ⟨1497183, by rfl⟩ : syracuseStep 3992489 = 2994367) B2994367
theorem B1895771 : Blo 1182408 1895771 := bstep (se 1 (by rfl) ⟨1421828, by rfl⟩ : syracuseStep 1895771 = 2843657) B2843657
theorem B1183399 : Blo 1182408 1183399 := bstep (se 1 (by rfl) ⟨887549, by rfl⟩ : syracuseStep 1183399 = 1775099) B1775099
theorem B3993407 : Blo 1182408 3993407 := bstep (se 1 (by rfl) ⟨2995055, by rfl⟩ : syracuseStep 3993407 = 5990111) B5990111
theorem B1184231 : Blo 1182408 1184231 := bstep (se 1 (by rfl) ⟨888173, by rfl⟩ : syracuseStep 1184231 = 1776347) B1776347
theorem B2994671 : Blo 1182408 2994671 := bstep (se 1 (by rfl) ⟨2246003, by rfl⟩ : syracuseStep 2994671 = 4492007) B4492007
theorem B10801835 : Blo 1182408 10801835 := bstep (se 1 (by rfl) ⟨8101376, by rfl⟩ : syracuseStep 10801835 = 16202753) B16202753
theorem B2995015 : Blo 1182408 2995015 := bstep (se 1 (by rfl) ⟨2246261, by rfl⟩ : syracuseStep 2995015 = 4492523) B4492523
theorem B3372263 : Blo 1182408 3372263 := bstep (se 1 (by rfl) ⟨2529197, by rfl⟩ : syracuseStep 3372263 = 5058395) B5058395
theorem B24294743 : Blo 1182408 24294743 := bstep (se 1 (by rfl) ⟨18221057, by rfl⟩ : syracuseStep 24294743 = 36442115) B36442115
theorem B1775039 : Blo 1182408 1775039 := bstep (se 1 (by rfl) ⟨1331279, by rfl⟩ : syracuseStep 1775039 = 2662559) B2662559
theorem B1775273 : Blo 1182408 1775273 := bstep (se 2 (by rfl) ⟨665727, by rfl⟩ : syracuseStep 1775273 = 1331455) B1331455
theorem B1776551 : Blo 1182408 1776551 := bstep (se 1 (by rfl) ⟨1332413, by rfl⟩ : syracuseStep 1776551 = 2664827) B2664827
theorem B5995457 : Blo 1182408 5995457 := bstep (se 2 (by rfl) ⟨2248296, by rfl⟩ : syracuseStep 5995457 = 4496593) B4496593
theorem B30351185 : Blo 1182408 30351185 := bstep (se 2 (by rfl) ⟨11381694, by rfl⟩ : syracuseStep 30351185 = 22763389) B22763389
theorem B7201223 : Blo 1182408 7201223 := bstep (se 1 (by rfl) ⟨5400917, by rfl⟩ : syracuseStep 7201223 = 10801835) B10801835
theorem B20496887 : Blo 1182408 20496887 := bstep (se 1 (by rfl) ⟨15372665, by rfl⟩ : syracuseStep 20496887 = 30745331) B30745331
theorem B16196495 : Blo 1182408 16196495 := bstep (se 1 (by rfl) ⟨12147371, by rfl⟩ : syracuseStep 16196495 = 24294743) B24294743
theorem B1263847 : Blo 1182408 1263847 := bstep (se 1 (by rfl) ⟨947885, by rfl⟩ : syracuseStep 1263847 = 1895771) B1895771
theorem B11381543 : Blo 1182408 11381543 := bstep (se 1 (by rfl) ⟨8536157, by rfl⟩ : syracuseStep 11381543 = 17072315) B17072315
theorem B2248175 : Blo 1182408 2248175 := bstep (se 1 (by rfl) ⟨1686131, by rfl⟩ : syracuseStep 2248175 = 3372263) B3372263
theorem B1183359 : Blo 1182408 1183359 := bstep (se 1 (by rfl) ⟨887519, by rfl⟩ : syracuseStep 1183359 = 1775039) B1775039
theorem B3993353 : Blo 1182408 3993353 := bstep (se 2 (by rfl) ⟨1497507, by rfl⟩ : syracuseStep 3993353 = 2995015) B2995015
theorem B1183515 : Blo 1182408 1183515 := bstep (se 1 (by rfl) ⟨887636, by rfl⟩ : syracuseStep 1183515 = 1775273) B1775273
theorem B2994023 : Blo 1182408 2994023 := bstep (se 1 (by rfl) ⟨2245517, by rfl⟩ : syracuseStep 2994023 = 4491035) B4491035
theorem B1184367 : Blo 1182408 1184367 := bstep (se 1 (by rfl) ⟨888275, by rfl⟩ : syracuseStep 1184367 = 1776551) B1776551
theorem B1996447 : Blo 1182408 1996447 := bstep (se 1 (by rfl) ⟨1497335, by rfl⟩ : syracuseStep 1996447 = 2994671) B2994671
theorem B66525607 : Blo 1182408 66525607 := bstep (se 1 (by rfl) ⟨49894205, by rfl⟩ : syracuseStep 66525607 = 99788411) B99788411
theorem B5986871 : Blo 1182408 5986871 := bstep (se 1 (by rfl) ⟨4490153, by rfl⟩ : syracuseStep 5986871 = 8980307) B8980307
theorem B2661659 : Blo 1182408 2661659 := bstep (se 1 (by rfl) ⟨1996244, by rfl⟩ : syracuseStep 2661659 = 3992489) B3992489
theorem B3996971 : Blo 1182408 3996971 := bstep (se 1 (by rfl) ⟨2997728, by rfl⟩ : syracuseStep 3996971 = 5995457) B5995457
theorem B2662271 : Blo 1182408 2662271 := bstep (se 1 (by rfl) ⟨1996703, by rfl⟩ : syracuseStep 2662271 = 3993407) B3993407
theorem B20234123 : Blo 1182408 20234123 := bstep (se 1 (by rfl) ⟨15175592, by rfl⟩ : syracuseStep 20234123 = 30351185) B30351185
theorem B4800815 : Blo 1182408 4800815 := bstep (se 1 (by rfl) ⟨3600611, by rfl⟩ : syracuseStep 4800815 = 7201223) B7201223
theorem B13664591 : Blo 1182408 13664591 := bstep (se 1 (by rfl) ⟨10248443, by rfl⟩ : syracuseStep 13664591 = 20496887) B20496887
theorem B3991247 : Blo 1182408 3991247 := bstep (se 1 (by rfl) ⟨2993435, by rfl⟩ : syracuseStep 3991247 = 5986871) B5986871
theorem B7587695 : Blo 1182408 7587695 := bstep (se 1 (by rfl) ⟨5690771, by rfl⟩ : syracuseStep 7587695 = 11381543) B11381543
theorem B2664647 : Blo 1182408 2664647 := bstep (se 1 (by rfl) ⟨1998485, by rfl⟩ : syracuseStep 2664647 = 3996971) B3996971
theorem B43190653 : Blo 1182408 43190653 := bstep (se 3 (by rfl) ⟨8098247, by rfl⟩ : syracuseStep 43190653 = 16196495) B16196495
theorem B1774439 : Blo 1182408 1774439 := bstep (se 1 (by rfl) ⟨1330829, by rfl⟩ : syracuseStep 1774439 = 2661659) B2661659
theorem B1996015 : Blo 1182408 1996015 := bstep (se 1 (by rfl) ⟨1497011, by rfl⟩ : syracuseStep 1996015 = 2994023) B2994023
theorem B1774847 : Blo 1182408 1774847 := bstep (se 1 (by rfl) ⟨1331135, by rfl⟩ : syracuseStep 1774847 = 2662271) B2662271
theorem B13489415 : Blo 1182408 13489415 := bstep (se 1 (by rfl) ⟨10117061, by rfl⟩ : syracuseStep 13489415 = 20234123) B20234123
theorem B1685129 : Blo 1182408 1685129 := bstep (se 2 (by rfl) ⟨631923, by rfl⟩ : syracuseStep 1685129 = 1263847) B1263847
theorem B5995133 : Blo 1182408 5995133 := bstep (se 3 (by rfl) ⟨1124087, by rfl⟩ : syracuseStep 5995133 = 2248175) B2248175
theorem B354803237 : Blo 1182408 354803237 := bstep (se 4 (by rfl) ⟨33262803, by rfl⟩ : syracuseStep 354803237 = 66525607) B66525607
theorem B2661929 : Blo 1182408 2661929 := bstep (se 2 (by rfl) ⟨998223, by rfl⟩ : syracuseStep 2661929 = 1996447) B1996447
theorem B2662235 : Blo 1182408 2662235 := bstep (se 1 (by rfl) ⟨1996676, by rfl⟩ : syracuseStep 2662235 = 3993353) B3993353
theorem B9109727 : Blo 1182408 9109727 := bstep (se 1 (by rfl) ⟨6832295, by rfl⟩ : syracuseStep 9109727 = 13664591) B13664591
theorem B1182959 : Blo 1182408 1182959 := bstep (se 1 (by rfl) ⟨887219, by rfl⟩ : syracuseStep 1182959 = 1774439) B1774439
theorem B1183231 : Blo 1182408 1183231 := bstep (se 1 (by rfl) ⟨887423, by rfl⟩ : syracuseStep 1183231 = 1774847) B1774847
theorem B5058463 : Blo 1182408 5058463 := bstep (se 1 (by rfl) ⟨3793847, by rfl⟩ : syracuseStep 5058463 = 7587695) B7587695
theorem B4493677 : Blo 1182408 4493677 := bstep (se 3 (by rfl) ⟨842564, by rfl⟩ : syracuseStep 4493677 = 1685129) B1685129
theorem B1774619 : Blo 1182408 1774619 := bstep (se 1 (by rfl) ⟨1330964, by rfl⟩ : syracuseStep 1774619 = 2661929) B2661929
theorem B1774823 : Blo 1182408 1774823 := bstep (se 1 (by rfl) ⟨1331117, by rfl⟩ : syracuseStep 1774823 = 2662235) B2662235
theorem B3200543 : Blo 1182408 3200543 := bstep (se 1 (by rfl) ⟨2400407, by rfl⟩ : syracuseStep 3200543 = 4800815) B4800815
theorem B57587537 : Blo 1182408 57587537 := bstep (se 2 (by rfl) ⟨21595326, by rfl⟩ : syracuseStep 57587537 = 43190653) B43190653
theorem B8992943 : Blo 1182408 8992943 := bstep (se 1 (by rfl) ⟨6744707, by rfl⟩ : syracuseStep 8992943 = 13489415) B13489415
theorem B2660831 : Blo 1182408 2660831 := bstep (se 1 (by rfl) ⟨1995623, by rfl⟩ : syracuseStep 2660831 = 3991247) B3991247
theorem B1776431 : Blo 1182408 1776431 := bstep (se 1 (by rfl) ⟨1332323, by rfl⟩ : syracuseStep 1776431 = 2664647) B2664647
theorem B2661353 : Blo 1182408 2661353 := bstep (se 2 (by rfl) ⟨998007, by rfl⟩ : syracuseStep 2661353 = 1996015) B1996015
theorem B3996755 : Blo 1182408 3996755 := bstep (se 1 (by rfl) ⟨2997566, by rfl⟩ : syracuseStep 3996755 = 5995133) B5995133
theorem B236535491 : Blo 1182408 236535491 := bstep (se 1 (by rfl) ⟨177401618, by rfl⟩ : syracuseStep 236535491 = 354803237) B354803237
theorem B2664503 : Blo 1182408 2664503 := bstep (se 1 (by rfl) ⟨1998377, by rfl⟩ : syracuseStep 2664503 = 3996755) B3996755
theorem B157690327 : Blo 1182408 157690327 := bstep (se 1 (by rfl) ⟨118267745, by rfl⟩ : syracuseStep 157690327 = 236535491) B236535491
theorem B6744617 : Blo 1182408 6744617 := bstep (se 2 (by rfl) ⟨2529231, by rfl⟩ : syracuseStep 6744617 = 5058463) B5058463
theorem B6073151 : Blo 1182408 6073151 := bstep (se 1 (by rfl) ⟨4554863, by rfl⟩ : syracuseStep 6073151 = 9109727) B9109727
theorem B5991569 : Blo 1182408 5991569 := bstep (se 2 (by rfl) ⟨2246838, by rfl⟩ : syracuseStep 5991569 = 4493677) B4493677
theorem B1183079 : Blo 1182408 1183079 := bstep (se 1 (by rfl) ⟨887309, by rfl⟩ : syracuseStep 1183079 = 1774619) B1774619
theorem B1183215 : Blo 1182408 1183215 := bstep (se 1 (by rfl) ⟨887411, by rfl⟩ : syracuseStep 1183215 = 1774823) B1774823
theorem B2133695 : Blo 1182408 2133695 := bstep (se 1 (by rfl) ⟨1600271, by rfl⟩ : syracuseStep 2133695 = 3200543) B3200543
theorem B38391691 : Blo 1182408 38391691 := bstep (se 1 (by rfl) ⟨28793768, by rfl⟩ : syracuseStep 38391691 = 57587537) B57587537
theorem B1773887 : Blo 1182408 1773887 := bstep (se 1 (by rfl) ⟨1330415, by rfl⟩ : syracuseStep 1773887 = 2660831) B2660831
theorem B1184287 : Blo 1182408 1184287 := bstep (se 1 (by rfl) ⟨888215, by rfl⟩ : syracuseStep 1184287 = 1776431) B1776431
theorem B1774235 : Blo 1182408 1774235 := bstep (se 1 (by rfl) ⟨1330676, by rfl⟩ : syracuseStep 1774235 = 2661353) B2661353
theorem B5995295 : Blo 1182408 5995295 := bstep (se 1 (by rfl) ⟨4496471, by rfl⟩ : syracuseStep 5995295 = 8992943) B8992943
theorem B1182591 : Blo 1182408 1182591 := bstep (se 1 (by rfl) ⟨886943, by rfl⟩ : syracuseStep 1182591 = 1773887) B1773887
theorem B1182823 : Blo 1182408 1182823 := bstep (se 1 (by rfl) ⟨887117, by rfl⟩ : syracuseStep 1182823 = 1774235) B1774235
theorem B3994379 : Blo 1182408 3994379 := bstep (se 1 (by rfl) ⟨2995784, by rfl⟩ : syracuseStep 3994379 = 5991569) B5991569
theorem B1422463 : Blo 1182408 1422463 := bstep (se 1 (by rfl) ⟨1066847, by rfl⟩ : syracuseStep 1422463 = 2133695) B2133695
theorem B51188921 : Blo 1182408 51188921 := bstep (se 2 (by rfl) ⟨19195845, by rfl⟩ : syracuseStep 51188921 = 38391691) B38391691
theorem B210253769 : Blo 1182408 210253769 := bstep (se 2 (by rfl) ⟨78845163, by rfl⟩ : syracuseStep 210253769 = 157690327) B157690327
theorem B1776335 : Blo 1182408 1776335 := bstep (se 1 (by rfl) ⟨1332251, by rfl⟩ : syracuseStep 1776335 = 2664503) B2664503
theorem B4496411 : Blo 1182408 4496411 := bstep (se 1 (by rfl) ⟨3372308, by rfl⟩ : syracuseStep 4496411 = 6744617) B6744617
theorem B3996863 : Blo 1182408 3996863 := bstep (se 1 (by rfl) ⟨2997647, by rfl⟩ : syracuseStep 3996863 = 5995295) B5995295
theorem B16195069 : Blo 1182408 16195069 := bstep (se 3 (by rfl) ⟨3036575, by rfl⟩ : syracuseStep 16195069 = 6073151) B6073151
theorem B2662919 : Blo 1182408 2662919 := bstep (se 1 (by rfl) ⟨1997189, by rfl⟩ : syracuseStep 2662919 = 3994379) B3994379
theorem B2664575 : Blo 1182408 2664575 := bstep (se 1 (by rfl) ⟨1998431, by rfl⟩ : syracuseStep 2664575 = 3996863) B3996863
theorem B140169179 : Blo 1182408 140169179 := bstep (se 1 (by rfl) ⟨105126884, by rfl⟩ : syracuseStep 140169179 = 210253769) B210253769
theorem B1896617 : Blo 1182408 1896617 := bstep (se 2 (by rfl) ⟨711231, by rfl⟩ : syracuseStep 1896617 = 1422463) B1422463
theorem B1184223 : Blo 1182408 1184223 := bstep (se 1 (by rfl) ⟨888167, by rfl⟩ : syracuseStep 1184223 = 1776335) B1776335
theorem B34125947 : Blo 1182408 34125947 := bstep (se 1 (by rfl) ⟨25594460, by rfl⟩ : syracuseStep 34125947 = 51188921) B51188921
theorem B21593425 : Blo 1182408 21593425 := bstep (se 2 (by rfl) ⟨8097534, by rfl⟩ : syracuseStep 21593425 = 16195069) B16195069
theorem B2997607 : Blo 1182408 2997607 := bstep (se 1 (by rfl) ⟨2248205, by rfl⟩ : syracuseStep 2997607 = 4496411) B4496411
theorem B22750631 : Blo 1182408 22750631 := bstep (se 1 (by rfl) ⟨17062973, by rfl⟩ : syracuseStep 22750631 = 34125947) B34125947
theorem B1264411 : Blo 1182408 1264411 := bstep (se 1 (by rfl) ⟨948308, by rfl⟩ : syracuseStep 1264411 = 1896617) B1896617
theorem B28791233 : Blo 1182408 28791233 := bstep (se 2 (by rfl) ⟨10796712, by rfl⟩ : syracuseStep 28791233 = 21593425) B21593425
theorem B1775279 : Blo 1182408 1775279 := bstep (se 1 (by rfl) ⟨1331459, by rfl⟩ : syracuseStep 1775279 = 2662919) B2662919
theorem B1776383 : Blo 1182408 1776383 := bstep (se 1 (by rfl) ⟨1332287, by rfl⟩ : syracuseStep 1776383 = 2664575) B2664575
theorem B3996809 : Blo 1182408 3996809 := bstep (se 2 (by rfl) ⟨1498803, by rfl⟩ : syracuseStep 3996809 = 2997607) B2997607
theorem B93446119 : Blo 1182408 93446119 := bstep (se 1 (by rfl) ⟨70084589, by rfl⟩ : syracuseStep 93446119 = 140169179) B140169179
theorem B19194155 : Blo 1182408 19194155 := bstep (se 1 (by rfl) ⟨14395616, by rfl⟩ : syracuseStep 19194155 = 28791233) B28791233
theorem B2664539 : Blo 1182408 2664539 := bstep (se 1 (by rfl) ⟨1998404, by rfl⟩ : syracuseStep 2664539 = 3996809) B3996809
theorem B498379301 : Blo 1182408 498379301 := bstep (se 4 (by rfl) ⟨46723059, by rfl⟩ : syracuseStep 498379301 = 93446119) B93446119
theorem B15167087 : Blo 1182408 15167087 := bstep (se 1 (by rfl) ⟨11375315, by rfl⟩ : syracuseStep 15167087 = 22750631) B22750631
theorem B1183519 : Blo 1182408 1183519 := bstep (se 1 (by rfl) ⟨887639, by rfl⟩ : syracuseStep 1183519 = 1775279) B1775279
theorem B1184255 : Blo 1182408 1184255 := bstep (se 1 (by rfl) ⟨888191, by rfl⟩ : syracuseStep 1184255 = 1776383) B1776383
theorem B1685881 : Blo 1182408 1685881 := bstep (se 2 (by rfl) ⟨632205, by rfl⟩ : syracuseStep 1685881 = 1264411) B1264411
theorem B12796103 : Blo 1182408 12796103 := bstep (se 1 (by rfl) ⟨9597077, by rfl⟩ : syracuseStep 12796103 = 19194155) B19194155
theorem B332252867 : Blo 1182408 332252867 := bstep (se 1 (by rfl) ⟨249189650, by rfl⟩ : syracuseStep 332252867 = 498379301) B498379301
theorem B10111391 : Blo 1182408 10111391 := bstep (se 1 (by rfl) ⟨7583543, by rfl⟩ : syracuseStep 10111391 = 15167087) B15167087
theorem B2247841 : Blo 1182408 2247841 := bstep (se 2 (by rfl) ⟨842940, by rfl⟩ : syracuseStep 2247841 = 1685881) B1685881
theorem B1776359 : Blo 1182408 1776359 := bstep (se 1 (by rfl) ⟨1332269, by rfl⟩ : syracuseStep 1776359 = 2664539) B2664539
theorem B886007645 : Blo 1182408 886007645 := bstep (se 3 (by rfl) ⟨166126433, by rfl⟩ : syracuseStep 886007645 = 332252867) B332252867
theorem B34122941 : Blo 1182408 34122941 := bstep (se 3 (by rfl) ⟨6398051, by rfl⟩ : syracuseStep 34122941 = 12796103) B12796103
theorem B1184239 : Blo 1182408 1184239 := bstep (se 1 (by rfl) ⟨888179, by rfl⟩ : syracuseStep 1184239 = 1776359) B1776359
theorem B2997121 : Blo 1182408 2997121 := bstep (se 2 (by rfl) ⟨1123920, by rfl⟩ : syracuseStep 2997121 = 2247841) B2247841
theorem B6740927 : Blo 1182408 6740927 := bstep (se 1 (by rfl) ⟨5055695, by rfl⟩ : syracuseStep 6740927 = 10111391) B10111391
theorem B590671763 : Blo 1182408 590671763 := bstep (se 1 (by rfl) ⟨443003822, by rfl⟩ : syracuseStep 590671763 = 886007645) B886007645
theorem B4493951 : Blo 1182408 4493951 := bstep (se 1 (by rfl) ⟨3370463, by rfl⟩ : syracuseStep 4493951 = 6740927) B6740927
theorem B3996161 : Blo 1182408 3996161 := bstep (se 2 (by rfl) ⟨1498560, by rfl⟩ : syracuseStep 3996161 = 2997121) B2997121
theorem B22748627 : Blo 1182408 22748627 := bstep (se 1 (by rfl) ⟨17061470, by rfl⟩ : syracuseStep 22748627 = 34122941) B34122941
theorem B2664107 : Blo 1182408 2664107 := bstep (se 1 (by rfl) ⟨1998080, by rfl⟩ : syracuseStep 2664107 = 3996161) B3996161
theorem B15165751 : Blo 1182408 15165751 := bstep (se 1 (by rfl) ⟨11374313, by rfl⟩ : syracuseStep 15165751 = 22748627) B22748627
theorem B2995967 : Blo 1182408 2995967 := bstep (se 1 (by rfl) ⟨2246975, by rfl⟩ : syracuseStep 2995967 = 4493951) B4493951
theorem B393781175 : Blo 1182408 393781175 := bstep (se 1 (by rfl) ⟨295335881, by rfl⟩ : syracuseStep 393781175 = 590671763) B590671763
theorem B20221001 : Blo 1182408 20221001 := bstep (se 2 (by rfl) ⟨7582875, by rfl⟩ : syracuseStep 20221001 = 15165751) B15165751
theorem B1776071 : Blo 1182408 1776071 := bstep (se 1 (by rfl) ⟨1332053, by rfl⟩ : syracuseStep 1776071 = 2664107) B2664107
theorem B1997311 : Blo 1182408 1997311 := bstep (se 1 (by rfl) ⟨1497983, by rfl⟩ : syracuseStep 1997311 = 2995967) B2995967
theorem B262520783 : Blo 1182408 262520783 := bstep (se 1 (by rfl) ⟨196890587, by rfl⟩ : syracuseStep 262520783 = 393781175) B393781175
theorem B2663081 : Blo 1182408 2663081 := bstep (se 2 (by rfl) ⟨998655, by rfl⟩ : syracuseStep 2663081 = 1997311) B1997311
theorem B1184047 : Blo 1182408 1184047 := bstep (se 1 (by rfl) ⟨888035, by rfl⟩ : syracuseStep 1184047 = 1776071) B1776071
theorem B13480667 : Blo 1182408 13480667 := bstep (se 1 (by rfl) ⟨10110500, by rfl⟩ : syracuseStep 13480667 = 20221001) B20221001
theorem B175013855 : Blo 1182408 175013855 := bstep (se 1 (by rfl) ⟨131260391, by rfl⟩ : syracuseStep 175013855 = 262520783) B262520783
theorem B8987111 : Blo 1182408 8987111 := bstep (se 1 (by rfl) ⟨6740333, by rfl⟩ : syracuseStep 8987111 = 13480667) B13480667
theorem B116675903 : Blo 1182408 116675903 := bstep (se 1 (by rfl) ⟨87506927, by rfl⟩ : syracuseStep 116675903 = 175013855) B175013855
theorem B1775387 : Blo 1182408 1775387 := bstep (se 1 (by rfl) ⟨1331540, by rfl⟩ : syracuseStep 1775387 = 2663081) B2663081
theorem B77783935 : Blo 1182408 77783935 := bstep (se 1 (by rfl) ⟨58337951, by rfl⟩ : syracuseStep 77783935 = 116675903) B116675903
theorem B5991407 : Blo 1182408 5991407 := bstep (se 1 (by rfl) ⟨4493555, by rfl⟩ : syracuseStep 5991407 = 8987111) B8987111
theorem B1183591 : Blo 1182408 1183591 := bstep (se 1 (by rfl) ⟨887693, by rfl⟩ : syracuseStep 1183591 = 1775387) B1775387
theorem B103711913 : Blo 1182408 103711913 := bstep (se 2 (by rfl) ⟨38891967, by rfl⟩ : syracuseStep 103711913 = 77783935) B77783935
theorem B3994271 : Blo 1182408 3994271 := bstep (se 1 (by rfl) ⟨2995703, by rfl⟩ : syracuseStep 3994271 = 5991407) B5991407
theorem B2662847 : Blo 1182408 2662847 := bstep (se 1 (by rfl) ⟨1997135, by rfl⟩ : syracuseStep 2662847 = 3994271) B3994271
theorem B69141275 : Blo 1182408 69141275 := bstep (se 1 (by rfl) ⟨51855956, by rfl⟩ : syracuseStep 69141275 = 103711913) B103711913
theorem B1775231 : Blo 1182408 1775231 := bstep (se 1 (by rfl) ⟨1331423, by rfl⟩ : syracuseStep 1775231 = 2662847) B2662847
theorem B46094183 : Blo 1182408 46094183 := bstep (se 1 (by rfl) ⟨34570637, by rfl⟩ : syracuseStep 46094183 = 69141275) B69141275
theorem B30729455 : Blo 1182408 30729455 := bstep (se 1 (by rfl) ⟨23047091, by rfl⟩ : syracuseStep 30729455 = 46094183) B46094183
theorem B1183487 : Blo 1182408 1183487 := bstep (se 1 (by rfl) ⟨887615, by rfl⟩ : syracuseStep 1183487 = 1775231) B1775231
theorem B20486303 : Blo 1182408 20486303 := bstep (se 1 (by rfl) ⟨15364727, by rfl⟩ : syracuseStep 20486303 = 30729455) B30729455
theorem B13657535 : Blo 1182408 13657535 := bstep (se 1 (by rfl) ⟨10243151, by rfl⟩ : syracuseStep 13657535 = 20486303) B20486303
theorem B9105023 : Blo 1182408 9105023 := bstep (se 1 (by rfl) ⟨6828767, by rfl⟩ : syracuseStep 9105023 = 13657535) B13657535
theorem B6070015 : Blo 1182408 6070015 := bstep (se 1 (by rfl) ⟨4552511, by rfl⟩ : syracuseStep 6070015 = 9105023) B9105023
theorem B8093353 : Blo 1182408 8093353 := bstep (se 2 (by rfl) ⟨3035007, by rfl⟩ : syracuseStep 8093353 = 6070015) B6070015
theorem B10791137 : Blo 1182408 10791137 := bstep (se 2 (by rfl) ⟨4046676, by rfl⟩ : syracuseStep 10791137 = 8093353) B8093353
theorem B7194091 : Blo 1182408 7194091 := bstep (se 1 (by rfl) ⟨5395568, by rfl⟩ : syracuseStep 7194091 = 10791137) B10791137
theorem B9592121 : Blo 1182408 9592121 := bstep (se 2 (by rfl) ⟨3597045, by rfl⟩ : syracuseStep 9592121 = 7194091) B7194091
theorem B6394747 : Blo 1182408 6394747 := bstep (se 1 (by rfl) ⟨4796060, by rfl⟩ : syracuseStep 6394747 = 9592121) B9592121
theorem B8526329 : Blo 1182408 8526329 := bstep (se 2 (by rfl) ⟨3197373, by rfl⟩ : syracuseStep 8526329 = 6394747) B6394747
theorem B5684219 : Blo 1182408 5684219 := bstep (se 1 (by rfl) ⟨4263164, by rfl⟩ : syracuseStep 5684219 = 8526329) B8526329
theorem B3789479 : Blo 1182408 3789479 := bstep (se 1 (by rfl) ⟨2842109, by rfl⟩ : syracuseStep 3789479 = 5684219) B5684219
theorem B2526319 : Blo 1182408 2526319 := bstep (se 1 (by rfl) ⟨1894739, by rfl⟩ : syracuseStep 2526319 = 3789479) B3789479
theorem B3368425 : Blo 1182408 3368425 := bstep (se 2 (by rfl) ⟨1263159, by rfl⟩ : syracuseStep 3368425 = 2526319) B2526319
theorem B4491233 : Blo 1182408 4491233 := bstep (se 2 (by rfl) ⟨1684212, by rfl⟩ : syracuseStep 4491233 = 3368425) B3368425
theorem B2994155 : Blo 1182408 2994155 := bstep (se 1 (by rfl) ⟨2245616, by rfl⟩ : syracuseStep 2994155 = 4491233) B4491233
theorem B1996103 : Blo 1182408 1996103 := bstep (se 1 (by rfl) ⟨1497077, by rfl⟩ : syracuseStep 1996103 = 2994155) B2994155
theorem B1330735 : Blo 1182408 1330735 := bstep (se 1 (by rfl) ⟨998051, by rfl⟩ : syracuseStep 1330735 = 1996103) B1996103
theorem B1774313 : Blo 1182408 1774313 := bstep (se 2 (by rfl) ⟨665367, by rfl⟩ : syracuseStep 1774313 = 1330735) B1330735
theorem B1182875 : Blo 1182408 1182875 := bstep (se 1 (by rfl) ⟨887156, by rfl⟩ : syracuseStep 1182875 = 1774313) B1774313

theorem C0 (j : ℕ) (h1 : 295602 ≤ j) (h2 : j ≤ 296101) : Blo 1182408 (4 * j + 3) := by
  interval_cases j
  · exact B1182411
  · exact B1182415
  · exact B1182419
  · exact B1182423
  · exact B1182427
  · exact B1182431
  · exact B1182435
  · exact B1182439
  · exact B1182443
  · exact B1182447
  · exact B1182451
  · exact B1182455
  · exact B1182459
  · exact B1182463
  · exact B1182467
  · exact B1182471
  · exact B1182475
  · exact B1182479
  · exact B1182483
  · exact B1182487
  · exact B1182491
  · exact B1182495
  · exact B1182499
  · exact B1182503
  · exact B1182507
  · exact B1182511
  · exact B1182515
  · exact B1182519
  · exact B1182523
  · exact B1182527
  · exact B1182531
  · exact B1182535
  · exact B1182539
  · exact B1182543
  · exact B1182547
  · exact B1182551
  · exact B1182555
  · exact B1182559
  · exact B1182563
  · exact B1182567
  · exact B1182571
  · exact B1182575
  · exact B1182579
  · exact B1182583
  · exact B1182587
  · exact B1182591
  · exact B1182595
  · exact B1182599
  · exact B1182603
  · exact B1182607
  · exact B1182611
  · exact B1182615
  · exact B1182619
  · exact B1182623
  · exact B1182627
  · exact B1182631
  · exact B1182635
  · exact B1182639
  · exact B1182643
  · exact B1182647
  · exact B1182651
  · exact B1182655
  · exact B1182659
  · exact B1182663
  · exact B1182667
  · exact B1182671
  · exact B1182675
  · exact B1182679
  · exact B1182683
  · exact B1182687
  · exact B1182691
  · exact B1182695
  · exact B1182699
  · exact B1182703
  · exact B1182707
  · exact B1182711
  · exact B1182715
  · exact B1182719
  · exact B1182723
  · exact B1182727
  · exact B1182731
  · exact B1182735
  · exact B1182739
  · exact B1182743
  · exact B1182747
  · exact B1182751
  · exact B1182755
  · exact B1182759
  · exact B1182763
  · exact B1182767
  · exact B1182771
  · exact B1182775
  · exact B1182779
  · exact B1182783
  · exact B1182787
  · exact B1182791
  · exact B1182795
  · exact B1182799
  · exact B1182803
  · exact B1182807
  · exact B1182811
  · exact B1182815
  · exact B1182819
  · exact B1182823
  · exact B1182827
  · exact B1182831
  · exact B1182835
  · exact B1182839
  · exact B1182843
  · exact B1182847
  · exact B1182851
  · exact B1182855
  · exact B1182859
  · exact B1182863
  · exact B1182867
  · exact B1182871
  · exact B1182875
  · exact B1182879
  · exact B1182883
  · exact B1182887
  · exact B1182891
  · exact B1182895
  · exact B1182899
  · exact B1182903
  · exact B1182907
  · exact B1182911
  · exact B1182915
  · exact B1182919
  · exact B1182923
  · exact B1182927
  · exact B1182931
  · exact B1182935
  · exact B1182939
  · exact B1182943
  · exact B1182947
  · exact B1182951
  · exact B1182955
  · exact B1182959
  · exact B1182963
  · exact B1182967
  · exact B1182971
  · exact B1182975
  · exact B1182979
  · exact B1182983
  · exact B1182987
  · exact B1182991
  · exact B1182995
  · exact B1182999
  · exact B1183003
  · exact B1183007
  · exact B1183011
  · exact B1183015
  · exact B1183019
  · exact B1183023
  · exact B1183027
  · exact B1183031
  · exact B1183035
  · exact B1183039
  · exact B1183043
  · exact B1183047
  · exact B1183051
  · exact B1183055
  · exact B1183059
  · exact B1183063
  · exact B1183067
  · exact B1183071
  · exact B1183075
  · exact B1183079
  · exact B1183083
  · exact B1183087
  · exact B1183091
  · exact B1183095
  · exact B1183099
  · exact B1183103
  · exact B1183107
  · exact B1183111
  · exact B1183115
  · exact B1183119
  · exact B1183123
  · exact B1183127
  · exact B1183131
  · exact B1183135
  · exact B1183139
  · exact B1183143
  · exact B1183147
  · exact B1183151
  · exact B1183155
  · exact B1183159
  · exact B1183163
  · exact B1183167
  · exact B1183171
  · exact B1183175
  · exact B1183179
  · exact B1183183
  · exact B1183187
  · exact B1183191
  · exact B1183195
  · exact B1183199
  · exact B1183203
  · exact B1183207
  · exact B1183211
  · exact B1183215
  · exact B1183219
  · exact B1183223
  · exact B1183227
  · exact B1183231
  · exact B1183235
  · exact B1183239
  · exact B1183243
  · exact B1183247
  · exact B1183251
  · exact B1183255
  · exact B1183259
  · exact B1183263
  · exact B1183267
  · exact B1183271
  · exact B1183275
  · exact B1183279
  · exact B1183283
  · exact B1183287
  · exact B1183291
  · exact B1183295
  · exact B1183299
  · exact B1183303
  · exact B1183307
  · exact B1183311
  · exact B1183315
  · exact B1183319
  · exact B1183323
  · exact B1183327
  · exact B1183331
  · exact B1183335
  · exact B1183339
  · exact B1183343
  · exact B1183347
  · exact B1183351
  · exact B1183355
  · exact B1183359
  · exact B1183363
  · exact B1183367
  · exact B1183371
  · exact B1183375
  · exact B1183379
  · exact B1183383
  · exact B1183387
  · exact B1183391
  · exact B1183395
  · exact B1183399
  · exact B1183403
  · exact B1183407
  · exact B1183411
  · exact B1183415
  · exact B1183419
  · exact B1183423
  · exact B1183427
  · exact B1183431
  · exact B1183435
  · exact B1183439
  · exact B1183443
  · exact B1183447
  · exact B1183451
  · exact B1183455
  · exact B1183459
  · exact B1183463
  · exact B1183467
  · exact B1183471
  · exact B1183475
  · exact B1183479
  · exact B1183483
  · exact B1183487
  · exact B1183491
  · exact B1183495
  · exact B1183499
  · exact B1183503
  · exact B1183507
  · exact B1183511
  · exact B1183515
  · exact B1183519
  · exact B1183523
  · exact B1183527
  · exact B1183531
  · exact B1183535
  · exact B1183539
  · exact B1183543
  · exact B1183547
  · exact B1183551
  · exact B1183555
  · exact B1183559
  · exact B1183563
  · exact B1183567
  · exact B1183571
  · exact B1183575
  · exact B1183579
  · exact B1183583
  · exact B1183587
  · exact B1183591
  · exact B1183595
  · exact B1183599
  · exact B1183603
  · exact B1183607
  · exact B1183611
  · exact B1183615
  · exact B1183619
  · exact B1183623
  · exact B1183627
  · exact B1183631
  · exact B1183635
  · exact B1183639
  · exact B1183643
  · exact B1183647
  · exact B1183651
  · exact B1183655
  · exact B1183659
  · exact B1183663
  · exact B1183667
  · exact B1183671
  · exact B1183675
  · exact B1183679
  · exact B1183683
  · exact B1183687
  · exact B1183691
  · exact B1183695
  · exact B1183699
  · exact B1183703
  · exact B1183707
  · exact B1183711
  · exact B1183715
  · exact B1183719
  · exact B1183723
  · exact B1183727
  · exact B1183731
  · exact B1183735
  · exact B1183739
  · exact B1183743
  · exact B1183747
  · exact B1183751
  · exact B1183755
  · exact B1183759
  · exact B1183763
  · exact B1183767
  · exact B1183771
  · exact B1183775
  · exact B1183779
  · exact B1183783
  · exact B1183787
  · exact B1183791
  · exact B1183795
  · exact B1183799
  · exact B1183803
  · exact B1183807
  · exact B1183811
  · exact B1183815
  · exact B1183819
  · exact B1183823
  · exact B1183827
  · exact B1183831
  · exact B1183835
  · exact B1183839
  · exact B1183843
  · exact B1183847
  · exact B1183851
  · exact B1183855
  · exact B1183859
  · exact B1183863
  · exact B1183867
  · exact B1183871
  · exact B1183875
  · exact B1183879
  · exact B1183883
  · exact B1183887
  · exact B1183891
  · exact B1183895
  · exact B1183899
  · exact B1183903
  · exact B1183907
  · exact B1183911
  · exact B1183915
  · exact B1183919
  · exact B1183923
  · exact B1183927
  · exact B1183931
  · exact B1183935
  · exact B1183939
  · exact B1183943
  · exact B1183947
  · exact B1183951
  · exact B1183955
  · exact B1183959
  · exact B1183963
  · exact B1183967
  · exact B1183971
  · exact B1183975
  · exact B1183979
  · exact B1183983
  · exact B1183987
  · exact B1183991
  · exact B1183995
  · exact B1183999
  · exact B1184003
  · exact B1184007
  · exact B1184011
  · exact B1184015
  · exact B1184019
  · exact B1184023
  · exact B1184027
  · exact B1184031
  · exact B1184035
  · exact B1184039
  · exact B1184043
  · exact B1184047
  · exact B1184051
  · exact B1184055
  · exact B1184059
  · exact B1184063
  · exact B1184067
  · exact B1184071
  · exact B1184075
  · exact B1184079
  · exact B1184083
  · exact B1184087
  · exact B1184091
  · exact B1184095
  · exact B1184099
  · exact B1184103
  · exact B1184107
  · exact B1184111
  · exact B1184115
  · exact B1184119
  · exact B1184123
  · exact B1184127
  · exact B1184131
  · exact B1184135
  · exact B1184139
  · exact B1184143
  · exact B1184147
  · exact B1184151
  · exact B1184155
  · exact B1184159
  · exact B1184163
  · exact B1184167
  · exact B1184171
  · exact B1184175
  · exact B1184179
  · exact B1184183
  · exact B1184187
  · exact B1184191
  · exact B1184195
  · exact B1184199
  · exact B1184203
  · exact B1184207
  · exact B1184211
  · exact B1184215
  · exact B1184219
  · exact B1184223
  · exact B1184227
  · exact B1184231
  · exact B1184235
  · exact B1184239
  · exact B1184243
  · exact B1184247
  · exact B1184251
  · exact B1184255
  · exact B1184259
  · exact B1184263
  · exact B1184267
  · exact B1184271
  · exact B1184275
  · exact B1184279
  · exact B1184283
  · exact B1184287
  · exact B1184291
  · exact B1184295
  · exact B1184299
  · exact B1184303
  · exact B1184307
  · exact B1184311
  · exact B1184315
  · exact B1184319
  · exact B1184323
  · exact B1184327
  · exact B1184331
  · exact B1184335
  · exact B1184339
  · exact B1184343
  · exact B1184347
  · exact B1184351
  · exact B1184355
  · exact B1184359
  · exact B1184363
  · exact B1184367
  · exact B1184371
  · exact B1184375
  · exact B1184379
  · exact B1184383
  · exact B1184387
  · exact B1184391
  · exact B1184395
  · exact B1184399
  · exact B1184403
  · exact B1184407

theorem solution (m : ℕ) (hlo : 1182408 ≤ m) (hhi : m ≤ 1184408) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 295602 ≤ j := by omega
    have hj2 : j ≤ 296101 := by omega
    have hb : Blo 1182408 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
