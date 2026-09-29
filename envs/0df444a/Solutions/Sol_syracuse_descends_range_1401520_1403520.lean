-- Prove2me | solution 1 for syracuse_descends_range_1401520_1403520
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:13:53.372853+00:00
-- url     : https://prove2.me/submissions/462610f2-4629-479c-935d-154d6e8d524f

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


theorem B3153941 : Blo 1401520 3153941 := bbase (se 6 (by rfl) ⟨73920, by rfl⟩ : syracuseStep 3153941 = 147841) (by norm_num)
theorem B2662445 : Blo 1401520 2662445 := bbase (se 3 (by rfl) ⟨499208, by rfl⟩ : syracuseStep 2662445 = 998417) (by norm_num)
theorem B3154013 : Blo 1401520 3154013 := bbase (se 3 (by rfl) ⟨591377, by rfl⟩ : syracuseStep 3154013 = 1182755) (by norm_num)
theorem B7102565 : Blo 1401520 7102565 := bbase (se 4 (by rfl) ⟨665865, by rfl⟩ : syracuseStep 7102565 = 1331731) (by norm_num)
theorem B2367589 : Blo 1401520 2367589 := bbase (se 4 (by rfl) ⟨221961, by rfl⟩ : syracuseStep 2367589 = 443923) (by norm_num)
theorem B10649717 : Blo 1401520 10649717 := bbase (se 5 (by rfl) ⟨499205, by rfl⟩ : syracuseStep 10649717 = 998411) (by norm_num)
theorem B5988485 : Blo 1401520 5988485 := bbase (se 4 (by rfl) ⟨561420, by rfl⟩ : syracuseStep 5988485 = 1122841) (by norm_num)
theorem B3154085 : Blo 1401520 3154085 := bbase (se 4 (by rfl) ⟨295695, by rfl⟩ : syracuseStep 3154085 = 591391) (by norm_num)
theorem B2367677 : Blo 1401520 2367677 := bbase (se 3 (by rfl) ⟨443939, by rfl⟩ : syracuseStep 2367677 = 887879) (by norm_num)
theorem B4735205 : Blo 1401520 4735205 := bbase (se 4 (by rfl) ⟨443925, by rfl⟩ : syracuseStep 4735205 = 887851) (by norm_num)
theorem B3154157 : Blo 1401520 3154157 := bbase (se 3 (by rfl) ⟨591404, by rfl⟩ : syracuseStep 3154157 = 1182809) (by norm_num)
theorem B3154229 : Blo 1401520 3154229 := bbase (se 5 (by rfl) ⟨147854, by rfl⟩ : syracuseStep 3154229 = 295709) (by norm_num)
theorem B2367805 : Blo 1401520 2367805 := bbase (se 3 (by rfl) ⟨443963, by rfl⟩ : syracuseStep 2367805 = 887927) (by norm_num)
theorem B2662733 : Blo 1401520 2662733 := bbase (se 3 (by rfl) ⟨499262, by rfl⟩ : syracuseStep 2662733 = 998525) (by norm_num)
theorem B5988725 : Blo 1401520 5988725 := bbase (se 5 (by rfl) ⟨280721, by rfl⟩ : syracuseStep 5988725 = 561443) (by norm_num)
theorem B3154301 : Blo 1401520 3154301 := bbase (se 3 (by rfl) ⟨591431, by rfl⟩ : syracuseStep 3154301 = 1182863) (by norm_num)
theorem B2367893 : Blo 1401520 2367893 := bbase (se 6 (by rfl) ⟨55497, by rfl⟩ : syracuseStep 2367893 = 110995) (by norm_num)
theorem B3154373 : Blo 1401520 3154373 := bbase (se 4 (by rfl) ⟨295722, by rfl⟩ : syracuseStep 3154373 = 591445) (by norm_num)
theorem B2662885 : Blo 1401520 2662885 := bbase (se 4 (by rfl) ⟨249645, by rfl⟩ : syracuseStep 2662885 = 499291) (by norm_num)
theorem B3154445 : Blo 1401520 3154445 := bbase (se 3 (by rfl) ⟨591458, by rfl⟩ : syracuseStep 3154445 = 1182917) (by norm_num)
theorem B2368021 : Blo 1401520 2368021 := bbase (se 6 (by rfl) ⟨55500, by rfl⟩ : syracuseStep 2368021 = 111001) (by norm_num)
theorem B3547709 : Blo 1401520 3547709 := bbase (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) (by norm_num)
theorem B3154517 : Blo 1401520 3154517 := bbase (se 8 (by rfl) ⟨18483, by rfl⟩ : syracuseStep 3154517 = 36967) (by norm_num)
theorem B2368109 : Blo 1401520 2368109 := bbase (se 3 (by rfl) ⟨444020, by rfl⟩ : syracuseStep 2368109 = 888041) (by norm_num)
theorem B4735637 : Blo 1401520 4735637 := bbase (se 6 (by rfl) ⟨110991, by rfl⟩ : syracuseStep 4735637 = 221983) (by norm_num)
theorem B3154589 : Blo 1401520 3154589 := bbase (se 3 (by rfl) ⟨591485, by rfl⟩ : syracuseStep 3154589 = 1182971) (by norm_num)
theorem B2245349 : Blo 1401520 2245349 := bbase (se 4 (by rfl) ⟨210501, by rfl⟩ : syracuseStep 2245349 = 421003) (by norm_num)
theorem B3154661 : Blo 1401520 3154661 := bbase (se 4 (by rfl) ⟨295749, by rfl⟩ : syracuseStep 3154661 = 591499) (by norm_num)
theorem B2368237 : Blo 1401520 2368237 := bbase (se 3 (by rfl) ⟨444044, by rfl⟩ : syracuseStep 2368237 = 888089) (by norm_num)
theorem B3547901 : Blo 1401520 3547901 := bbase (se 3 (by rfl) ⟨665231, by rfl⟩ : syracuseStep 3547901 = 1330463) (by norm_num)
theorem B2663189 : Blo 1401520 2663189 := bbase (se 6 (by rfl) ⟨62418, by rfl⟩ : syracuseStep 2663189 = 124837) (by norm_num)
theorem B3154733 : Blo 1401520 3154733 := bbase (se 3 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 3154733 = 1183025) (by norm_num)
theorem B2368325 : Blo 1401520 2368325 := bbase (se 4 (by rfl) ⟨222030, by rfl⟩ : syracuseStep 2368325 = 444061) (by norm_num)
theorem B207496021 : Blo 1401520 207496021 := bbase (se 9 (by rfl) ⟨607898, by rfl⟩ : syracuseStep 207496021 = 1215797) (by norm_num)
theorem B2245477 : Blo 1401520 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B3154805 : Blo 1401520 3154805 := bbase (se 5 (by rfl) ⟨147881, by rfl⟩ : syracuseStep 3154805 = 295763) (by norm_num)
theorem B3367813 : Blo 1401520 3367813 := bbase (se 4 (by rfl) ⟨315732, by rfl⟩ : syracuseStep 3367813 = 631465) (by norm_num)
theorem B26960789 : Blo 1401520 26960789 := bbase (se 6 (by rfl) ⟨631893, by rfl⟩ : syracuseStep 26960789 = 1263787) (by norm_num)
theorem B14599061 : Blo 1401520 14599061 := bbase (se 6 (by rfl) ⟨342165, by rfl⟩ : syracuseStep 14599061 = 684331) (by norm_num)
theorem B3154877 : Blo 1401520 3154877 := bbase (se 3 (by rfl) ⟨591539, by rfl⟩ : syracuseStep 3154877 = 1183079) (by norm_num)
theorem B3154949 : Blo 1401520 3154949 := bbase (se 4 (by rfl) ⟨295776, by rfl⟩ : syracuseStep 3154949 = 591553) (by norm_num)
theorem B4736069 : Blo 1401520 4736069 := bbase (se 4 (by rfl) ⟨444006, by rfl⟩ : syracuseStep 4736069 = 888013) (by norm_num)
theorem B3155021 : Blo 1401520 3155021 := bbase (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) (by norm_num)
theorem B3548245 : Blo 1401520 3548245 := bbase (se 8 (by rfl) ⟨20790, by rfl⟩ : syracuseStep 3548245 = 41581) (by norm_num)
theorem B3155093 : Blo 1401520 3155093 := bbase (se 6 (by rfl) ⟨73947, by rfl⟩ : syracuseStep 3155093 = 147895) (by norm_num)
theorem B13477013 : Blo 1401520 13477013 := bbase (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) (by norm_num)
theorem B3548357 : Blo 1401520 3548357 := bbase (se 4 (by rfl) ⟨332658, by rfl⟩ : syracuseStep 3548357 = 665317) (by norm_num)
theorem B3155165 : Blo 1401520 3155165 := bbase (se 3 (by rfl) ⟨591593, by rfl⟩ : syracuseStep 3155165 = 1183187) (by norm_num)
theorem B3155237 : Blo 1401520 3155237 := bbase (se 4 (by rfl) ⟨295803, by rfl⟩ : syracuseStep 3155237 = 591607) (by norm_num)
theorem B5326181 : Blo 1401520 5326181 := bbase (se 4 (by rfl) ⟨499329, by rfl⟩ : syracuseStep 5326181 = 998659) (by norm_num)
theorem B3155309 : Blo 1401520 3155309 := bbase (se 3 (by rfl) ⟨591620, by rfl⟩ : syracuseStep 3155309 = 1183241) (by norm_num)
theorem B7103861 : Blo 1401520 7103861 := bbase (se 5 (by rfl) ⟨332993, by rfl⟩ : syracuseStep 7103861 = 665987) (by norm_num)
theorem B3548549 : Blo 1401520 3548549 := bbase (se 4 (by rfl) ⟨332676, by rfl⟩ : syracuseStep 3548549 = 665353) (by norm_num)
theorem B4105637 : Blo 1401520 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B1598897 : Blo 1401520 1598897 := bbase (se 2 (by rfl) ⟨599586, by rfl⟩ : syracuseStep 1598897 = 1199173) (by norm_num)
theorem B3155381 : Blo 1401520 3155381 := bbase (se 5 (by rfl) ⟨147908, by rfl⟩ : syracuseStep 3155381 = 295817) (by norm_num)
theorem B5400037 : Blo 1401520 5400037 := bbase (se 4 (by rfl) ⟨506253, by rfl⟩ : syracuseStep 5400037 = 1012507) (by norm_num)
theorem B3368429 : Blo 1401520 3368429 := bbase (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) (by norm_num)
theorem B4736501 : Blo 1401520 4736501 := bbase (se 5 (by rfl) ⟨222023, by rfl⟩ : syracuseStep 4736501 = 444047) (by norm_num)
theorem B3155453 : Blo 1401520 3155453 := bbase (se 3 (by rfl) ⟨591647, by rfl⟩ : syracuseStep 3155453 = 1183295) (by norm_num)
theorem B2024957 : Blo 1401520 2024957 := bbase (se 3 (by rfl) ⟨379679, by rfl⟩ : syracuseStep 2024957 = 759359) (by norm_num)
theorem B2663941 : Blo 1401520 2663941 := bbase (se 4 (by rfl) ⟨249744, by rfl⟩ : syracuseStep 2663941 = 499489) (by norm_num)
theorem B6735413 : Blo 1401520 6735413 := bbase (se 5 (by rfl) ⟨315722, by rfl⟩ : syracuseStep 6735413 = 631445) (by norm_num)
theorem B3155525 : Blo 1401520 3155525 := bbase (se 4 (by rfl) ⟨295830, by rfl⟩ : syracuseStep 3155525 = 591661) (by norm_num)
theorem B5326469 : Blo 1401520 5326469 := bbase (se 4 (by rfl) ⟨499356, by rfl⟩ : syracuseStep 5326469 = 998713) (by norm_num)
theorem B2246285 : Blo 1401520 2246285 := bbase (se 3 (by rfl) ⟨421178, by rfl⟩ : syracuseStep 2246285 = 842357) (by norm_num)
theorem B3155597 : Blo 1401520 3155597 := bbase (se 3 (by rfl) ⟨591674, by rfl⟩ : syracuseStep 3155597 = 1183349) (by norm_num)
theorem B2664085 : Blo 1401520 2664085 := bbase (se 6 (by rfl) ⟨62439, by rfl⟩ : syracuseStep 2664085 = 124879) (by norm_num)
theorem B3155669 : Blo 1401520 3155669 := bbase (se 7 (by rfl) ⟨36980, by rfl⟩ : syracuseStep 3155669 = 73961) (by norm_num)
theorem B3548893 : Blo 1401520 3548893 := bbase (se 3 (by rfl) ⟨665417, by rfl⟩ : syracuseStep 3548893 = 1330835) (by norm_num)
theorem B1730317 : Blo 1401520 1730317 := bbase (se 3 (by rfl) ⟨324434, by rfl⟩ : syracuseStep 1730317 = 648869) (by norm_num)
theorem B7096085 : Blo 1401520 7096085 := bbase (se 6 (by rfl) ⟨166314, by rfl⟩ : syracuseStep 7096085 = 332629) (by norm_num)
theorem B3155741 : Blo 1401520 3155741 := bbase (se 3 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 3155741 = 1183403) (by norm_num)
theorem B2664245 : Blo 1401520 2664245 := bbase (se 5 (by rfl) ⟨124886, by rfl⟩ : syracuseStep 2664245 = 249773) (by norm_num)
theorem B3549005 : Blo 1401520 3549005 := bbase (se 3 (by rfl) ⟨665438, by rfl⟩ : syracuseStep 3549005 = 1330877) (by norm_num)
theorem B3155813 : Blo 1401520 3155813 := bbase (se 4 (by rfl) ⟨295857, by rfl⟩ : syracuseStep 3155813 = 591715) (by norm_num)
theorem B3368861 : Blo 1401520 3368861 := bbase (se 3 (by rfl) ⟨631661, by rfl⟩ : syracuseStep 3368861 = 1263323) (by norm_num)
theorem B2246573 : Blo 1401520 2246573 := bbase (se 3 (by rfl) ⟨421232, by rfl⟩ : syracuseStep 2246573 = 842465) (by norm_num)
theorem B3155885 : Blo 1401520 3155885 := bbase (se 3 (by rfl) ⟨591728, by rfl⟩ : syracuseStep 3155885 = 1183457) (by norm_num)
theorem B2664389 : Blo 1401520 2664389 := bbase (se 4 (by rfl) ⟨249786, by rfl⟩ : syracuseStep 2664389 = 499573) (by norm_num)
theorem B3155957 : Blo 1401520 3155957 := bbase (se 5 (by rfl) ⟨147935, by rfl⟩ : syracuseStep 3155957 = 295871) (by norm_num)
theorem B3549197 : Blo 1401520 3549197 := bbase (se 3 (by rfl) ⟨665474, by rfl⟩ : syracuseStep 3549197 = 1330949) (by norm_num)
theorem B4491301 : Blo 1401520 4491301 := bbase (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) (by norm_num)
theorem B3156029 : Blo 1401520 3156029 := bbase (se 3 (by rfl) ⟨591755, by rfl⟩ : syracuseStep 3156029 = 1183511) (by norm_num)
theorem B3156101 : Blo 1401520 3156101 := bbase (se 4 (by rfl) ⟨295884, by rfl⟩ : syracuseStep 3156101 = 591769) (by norm_num)
theorem B3156173 : Blo 1401520 3156173 := bbase (se 3 (by rfl) ⟨591782, by rfl⟩ : syracuseStep 3156173 = 1183565) (by norm_num)
theorem B2844877 : Blo 1401520 2844877 := bbase (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) (by norm_num)
theorem B11987189 : Blo 1401520 11987189 := bbase (se 5 (by rfl) ⟨561899, by rfl⟩ : syracuseStep 11987189 = 1123799) (by norm_num)
theorem B3156245 : Blo 1401520 3156245 := bbase (se 6 (by rfl) ⟨73974, by rfl⟩ : syracuseStep 3156245 = 147949) (by norm_num)
theorem B2246989 : Blo 1401520 2246989 := bbase (se 3 (by rfl) ⟨421310, by rfl⟩ : syracuseStep 2246989 = 842621) (by norm_num)
theorem B3156317 : Blo 1401520 3156317 := bbase (se 3 (by rfl) ⟨591809, by rfl⟩ : syracuseStep 3156317 = 1183619) (by norm_num)
theorem B3549541 : Blo 1401520 3549541 := bbase (se 4 (by rfl) ⟨332769, by rfl⟩ : syracuseStep 3549541 = 665539) (by norm_num)
theorem B3156389 : Blo 1401520 3156389 := bbase (se 4 (by rfl) ⟨295911, by rfl⟩ : syracuseStep 3156389 = 591823) (by norm_num)
theorem B3549653 : Blo 1401520 3549653 := bbase (se 7 (by rfl) ⟨41597, by rfl⟩ : syracuseStep 3549653 = 83195) (by norm_num)
theorem B4491749 : Blo 1401520 4491749 := bbase (se 4 (by rfl) ⟨421101, by rfl⟩ : syracuseStep 4491749 = 842203) (by norm_num)
theorem B3156461 : Blo 1401520 3156461 := bbase (se 3 (by rfl) ⟨591836, by rfl⟩ : syracuseStep 3156461 = 1183673) (by norm_num)
theorem B7989749 : Blo 1401520 7989749 := bbase (se 5 (by rfl) ⟨374519, by rfl⟩ : syracuseStep 7989749 = 749039) (by norm_num)
theorem B4262453 : Blo 1401520 4262453 := bbase (se 5 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 4262453 = 399605) (by norm_num)
theorem B3156533 : Blo 1401520 3156533 := bbase (se 5 (by rfl) ⟨147962, by rfl⟩ : syracuseStep 3156533 = 295925) (by norm_num)
theorem B4262485 : Blo 1401520 4262485 := bbase (se 8 (by rfl) ⟨24975, by rfl⟩ : syracuseStep 4262485 = 49951) (by norm_num)
theorem B5991013 : Blo 1401520 5991013 := bbase (se 4 (by rfl) ⟨561657, by rfl⟩ : syracuseStep 5991013 = 1123315) (by norm_num)
theorem B3156605 : Blo 1401520 3156605 := bbase (se 3 (by rfl) ⟨591863, by rfl⟩ : syracuseStep 3156605 = 1183727) (by norm_num)
theorem B7105157 : Blo 1401520 7105157 := bbase (se 4 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 7105157 = 1332217) (by norm_num)
theorem B2525845 : Blo 1401520 2525845 := bbase (se 6 (by rfl) ⟨59199, by rfl⟩ : syracuseStep 2525845 = 118399) (by norm_num)
theorem B3549845 : Blo 1401520 3549845 := bbase (se 6 (by rfl) ⟨83199, by rfl⟩ : syracuseStep 3549845 = 166399) (by norm_num)
theorem B3156677 : Blo 1401520 3156677 := bbase (se 4 (by rfl) ⟨295938, by rfl⟩ : syracuseStep 3156677 = 591877) (by norm_num)
theorem B3156749 : Blo 1401520 3156749 := bbase (se 3 (by rfl) ⟨591890, by rfl⟩ : syracuseStep 3156749 = 1183781) (by norm_num)
theorem B5327653 : Blo 1401520 5327653 := bbase (se 4 (by rfl) ⟨499467, by rfl⟩ : syracuseStep 5327653 = 998935) (by norm_num)
theorem B2132813 : Blo 1401520 2132813 := bbase (se 3 (by rfl) ⟨399902, by rfl⟩ : syracuseStep 2132813 = 799805) (by norm_num)
theorem B3156821 : Blo 1401520 3156821 := bbase (se 9 (by rfl) ⟨9248, by rfl⟩ : syracuseStep 3156821 = 18497) (by norm_num)
theorem B3156893 : Blo 1401520 3156893 := bbase (se 3 (by rfl) ⟨591917, by rfl⟩ : syracuseStep 3156893 = 1183835) (by norm_num)
theorem B3156965 : Blo 1401520 3156965 := bbase (se 4 (by rfl) ⟨295965, by rfl⟩ : syracuseStep 3156965 = 591931) (by norm_num)
theorem B3550189 : Blo 1401520 3550189 := bbase (se 3 (by rfl) ⟨665660, by rfl⟩ : syracuseStep 3550189 = 1331321) (by norm_num)
theorem B3992597 : Blo 1401520 3992597 := bbase (se 6 (by rfl) ⟨93576, by rfl⟩ : syracuseStep 3992597 = 187153) (by norm_num)
theorem B7097381 : Blo 1401520 7097381 := bbase (se 4 (by rfl) ⟨665379, by rfl⟩ : syracuseStep 7097381 = 1330759) (by norm_num)
theorem B3157037 : Blo 1401520 3157037 := bbase (se 3 (by rfl) ⟨591944, by rfl⟩ : syracuseStep 3157037 = 1183889) (by norm_num)
theorem B3370061 : Blo 1401520 3370061 := bbase (se 3 (by rfl) ⟨631886, by rfl⟩ : syracuseStep 3370061 = 1263773) (by norm_num)
theorem B5327957 : Blo 1401520 5327957 := bbase (se 8 (by rfl) ⟨31218, by rfl⟩ : syracuseStep 5327957 = 62437) (by norm_num)
theorem B3550301 : Blo 1401520 3550301 := bbase (se 3 (by rfl) ⟨665681, by rfl⟩ : syracuseStep 3550301 = 1331363) (by norm_num)
theorem B3157109 : Blo 1401520 3157109 := bbase (se 5 (by rfl) ⟨147989, by rfl⟩ : syracuseStep 3157109 = 295979) (by norm_num)
theorem B3157181 : Blo 1401520 3157181 := bbase (se 3 (by rfl) ⟨591971, by rfl⟩ : syracuseStep 3157181 = 1183943) (by norm_num)
theorem B11365589 : Blo 1401520 11365589 := bbase (se 7 (by rfl) ⟨133190, by rfl⟩ : syracuseStep 11365589 = 266381) (by norm_num)
theorem B2526421 : Blo 1401520 2526421 := bbase (se 7 (by rfl) ⟨29606, by rfl⟩ : syracuseStep 2526421 = 59213) (by norm_num)
theorem B1518809 : Blo 1401520 1518809 := bbase (se 2 (by rfl) ⟨569553, by rfl⟩ : syracuseStep 1518809 = 1139107) (by norm_num)
theorem B12791029 : Blo 1401520 12791029 := bbase (se 5 (by rfl) ⟨599579, by rfl⟩ : syracuseStep 12791029 = 1199159) (by norm_num)
theorem B2247925 : Blo 1401520 2247925 := bbase (se 5 (by rfl) ⟨105371, by rfl⟩ : syracuseStep 2247925 = 210743) (by norm_num)
theorem B3157253 : Blo 1401520 3157253 := bbase (se 4 (by rfl) ⟨295992, by rfl⟩ : syracuseStep 3157253 = 591985) (by norm_num)
theorem B3550493 : Blo 1401520 3550493 := bbase (se 3 (by rfl) ⟨665717, by rfl⟩ : syracuseStep 3550493 = 1331435) (by norm_num)
theorem B3599677 : Blo 1401520 3599677 := bbase (se 3 (by rfl) ⟨674939, by rfl⟩ : syracuseStep 3599677 = 1349879) (by norm_num)
theorem B3157325 : Blo 1401520 3157325 := bbase (se 3 (by rfl) ⟨591998, by rfl⟩ : syracuseStep 3157325 = 1183997) (by norm_num)
theorem B2993525 : Blo 1401520 2993525 := bbase (se 5 (by rfl) ⟨140321, by rfl⟩ : syracuseStep 2993525 = 280643) (by norm_num)
theorem B7196021 : Blo 1401520 7196021 := bbase (se 5 (by rfl) ⟨337313, by rfl⟩ : syracuseStep 7196021 = 674627) (by norm_num)
theorem B3157397 : Blo 1401520 3157397 := bbase (se 6 (by rfl) ⟨74001, by rfl⟩ : syracuseStep 3157397 = 148003) (by norm_num)
theorem B3157469 : Blo 1401520 3157469 := bbase (se 3 (by rfl) ⟨592025, by rfl⟩ : syracuseStep 3157469 = 1184051) (by norm_num)
theorem B3157541 : Blo 1401520 3157541 := bbase (se 4 (by rfl) ⟨296019, by rfl⟩ : syracuseStep 3157541 = 592039) (by norm_num)
theorem B4730453 : Blo 1401520 4730453 := bbase (se 8 (by rfl) ⟨27717, by rfl⟩ : syracuseStep 4730453 = 55435) (by norm_num)
theorem B3157613 : Blo 1401520 3157613 := bbase (se 3 (by rfl) ⟨592052, by rfl⟩ : syracuseStep 3157613 = 1184105) (by norm_num)
theorem B3550837 : Blo 1401520 3550837 := bbase (se 5 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 3550837 = 332891) (by norm_num)
theorem B7990933 : Blo 1401520 7990933 := bbase (se 6 (by rfl) ⟨187287, by rfl⟩ : syracuseStep 7990933 = 374575) (by norm_num)
theorem B3157685 : Blo 1401520 3157685 := bbase (se 5 (by rfl) ⟨148016, by rfl⟩ : syracuseStep 3157685 = 296033) (by norm_num)
theorem B1560253 : Blo 1401520 1560253 := bbase (se 3 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 1560253 = 585095) (by norm_num)
theorem B10104533 : Blo 1401520 10104533 := bbase (se 7 (by rfl) ⟨118412, by rfl⟩ : syracuseStep 10104533 = 236825) (by norm_num)
theorem B3550949 : Blo 1401520 3550949 := bbase (se 4 (by rfl) ⟨332901, by rfl⟩ : syracuseStep 3550949 = 665803) (by norm_num)
theorem B3157757 : Blo 1401520 3157757 := bbase (se 3 (by rfl) ⟨592079, by rfl⟩ : syracuseStep 3157757 = 1184159) (by norm_num)
theorem B1576741 : Blo 1401520 1576741 := bbase (se 4 (by rfl) ⟨147819, by rfl⟩ : syracuseStep 1576741 = 295639) (by norm_num)
theorem B3157829 : Blo 1401520 3157829 := bbase (se 4 (by rfl) ⟨296046, by rfl⟩ : syracuseStep 3157829 = 592093) (by norm_num)
theorem B1576777 : Blo 1401520 1576777 := bbase (se 2 (by rfl) ⟨591291, by rfl⟩ : syracuseStep 1576777 = 1182583) (by norm_num)
theorem B1576813 : Blo 1401520 1576813 := bbase (se 3 (by rfl) ⟨295652, by rfl⟩ : syracuseStep 1576813 = 591305) (by norm_num)
theorem B2527085 : Blo 1401520 2527085 := bbase (se 3 (by rfl) ⟨473828, by rfl⟩ : syracuseStep 2527085 = 947657) (by norm_num)
theorem B3157901 : Blo 1401520 3157901 := bbase (se 3 (by rfl) ⟨592106, by rfl⟩ : syracuseStep 3157901 = 1184213) (by norm_num)
theorem B1576849 : Blo 1401520 1576849 := bbase (se 2 (by rfl) ⟨591318, by rfl⟩ : syracuseStep 1576849 = 1182637) (by norm_num)
theorem B3551141 : Blo 1401520 3551141 := bbase (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) (by norm_num)
theorem B1576885 : Blo 1401520 1576885 := bbase (se 5 (by rfl) ⟨73916, by rfl⟩ : syracuseStep 1576885 = 147833) (by norm_num)
theorem B1896373 : Blo 1401520 1896373 := bbase (se 5 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 1896373 = 177785) (by norm_num)
theorem B1576921 : Blo 1401520 1576921 := bbase (se 2 (by rfl) ⟨591345, by rfl⟩ : syracuseStep 1576921 = 1182691) (by norm_num)
theorem B1576957 : Blo 1401520 1576957 := bbase (se 3 (by rfl) ⟨295679, by rfl⟩ : syracuseStep 1576957 = 591359) (by norm_num)
theorem B4730885 : Blo 1401520 4730885 := bbase (se 4 (by rfl) ⟨443520, by rfl⟩ : syracuseStep 4730885 = 887041) (by norm_num)
theorem B1576993 : Blo 1401520 1576993 := bbase (se 2 (by rfl) ⟨591372, by rfl⟩ : syracuseStep 1576993 = 1182745) (by norm_num)
theorem B5992501 : Blo 1401520 5992501 := bbase (se 5 (by rfl) ⟨280898, by rfl⟩ : syracuseStep 5992501 = 561797) (by norm_num)
theorem B1577029 : Blo 1401520 1577029 := bbase (se 4 (by rfl) ⟨147846, by rfl⟩ : syracuseStep 1577029 = 295693) (by norm_num)
theorem B2527301 : Blo 1401520 2527301 := bbase (se 4 (by rfl) ⟨236934, by rfl⟩ : syracuseStep 2527301 = 473869) (by norm_num)
theorem B5992517 : Blo 1401520 5992517 := bbase (se 4 (by rfl) ⟨561798, by rfl⟩ : syracuseStep 5992517 = 1123597) (by norm_num)
theorem B1577065 : Blo 1401520 1577065 := bbase (se 2 (by rfl) ⟨591399, by rfl⟩ : syracuseStep 1577065 = 1182799) (by norm_num)
theorem B1577101 : Blo 1401520 1577101 := bbase (se 3 (by rfl) ⟨295706, by rfl⟩ : syracuseStep 1577101 = 591413) (by norm_num)
theorem B8982677 : Blo 1401520 8982677 := bbase (se 6 (by rfl) ⟨210531, by rfl⟩ : syracuseStep 8982677 = 421063) (by norm_num)
theorem B1577137 : Blo 1401520 1577137 := bbase (se 2 (by rfl) ⟨591426, by rfl⟩ : syracuseStep 1577137 = 1182853) (by norm_num)
theorem B3993781 : Blo 1401520 3993781 := bbase (se 5 (by rfl) ⟨187208, by rfl⟩ : syracuseStep 3993781 = 374417) (by norm_num)
theorem B1421501 : Blo 1401520 1421501 := bbase (se 3 (by rfl) ⟨266531, by rfl⟩ : syracuseStep 1421501 = 533063) (by norm_num)
theorem B5689541 : Blo 1401520 5689541 := bbase (se 4 (by rfl) ⟨533394, by rfl⟩ : syracuseStep 5689541 = 1066789) (by norm_num)
theorem B1577173 : Blo 1401520 1577173 := bbase (se 7 (by rfl) ⟨18482, by rfl⟩ : syracuseStep 1577173 = 36965) (by norm_num)
theorem B2994413 : Blo 1401520 2994413 := bbase (se 3 (by rfl) ⟨561452, by rfl⟩ : syracuseStep 2994413 = 1122905) (by norm_num)
theorem B1577209 : Blo 1401520 1577209 := bbase (se 2 (by rfl) ⟨591453, by rfl⟩ : syracuseStep 1577209 = 1182907) (by norm_num)
theorem B3551485 : Blo 1401520 3551485 := bbase (se 3 (by rfl) ⟨665903, by rfl⟩ : syracuseStep 3551485 = 1331807) (by norm_num)
theorem B1773829 : Blo 1401520 1773829 := bbase (se 4 (by rfl) ⟨166296, by rfl⟩ : syracuseStep 1773829 = 332593) (by norm_num)
theorem B1577245 : Blo 1401520 1577245 := bbase (se 3 (by rfl) ⟨295733, by rfl⟩ : syracuseStep 1577245 = 591467) (by norm_num)
theorem B7098677 : Blo 1401520 7098677 := bbase (se 5 (by rfl) ⟨332750, by rfl⟩ : syracuseStep 7098677 = 665501) (by norm_num)
theorem B1577281 : Blo 1401520 1577281 := bbase (se 2 (by rfl) ⟨591480, by rfl⟩ : syracuseStep 1577281 = 1182961) (by norm_num)
theorem B3993941 : Blo 1401520 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B2773333 : Blo 1401520 2773333 := bbase (se 10 (by rfl) ⟨4062, by rfl⟩ : syracuseStep 2773333 = 8125) (by norm_num)
theorem B1577317 : Blo 1401520 1577317 := bbase (se 4 (by rfl) ⟨147873, by rfl⟩ : syracuseStep 1577317 = 295747) (by norm_num)
theorem B3551597 : Blo 1401520 3551597 := bbase (se 3 (by rfl) ⟨665924, by rfl⟩ : syracuseStep 3551597 = 1331849) (by norm_num)
theorem B1577353 : Blo 1401520 1577353 := bbase (se 2 (by rfl) ⟨591507, by rfl⟩ : syracuseStep 1577353 = 1183015) (by norm_num)
theorem B1577389 : Blo 1401520 1577389 := bbase (se 3 (by rfl) ⟨295760, by rfl⟩ : syracuseStep 1577389 = 591521) (by norm_num)
theorem B1774001 : Blo 1401520 1774001 := bbase (se 2 (by rfl) ⟨665250, by rfl⟩ : syracuseStep 1774001 = 1330501) (by norm_num)
theorem B1708465 : Blo 1401520 1708465 := bbase (se 2 (by rfl) ⟨640674, by rfl⟩ : syracuseStep 1708465 = 1281349) (by norm_num)
theorem B4731317 : Blo 1401520 4731317 := bbase (se 5 (by rfl) ⟨221780, by rfl⟩ : syracuseStep 4731317 = 443561) (by norm_num)
theorem B1708489 : Blo 1401520 1708489 := bbase (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) (by norm_num)
theorem B1577425 : Blo 1401520 1577425 := bbase (se 2 (by rfl) ⟨591534, by rfl⟩ : syracuseStep 1577425 = 1183069) (by norm_num)
theorem B2994653 : Blo 1401520 2994653 := bbase (se 3 (by rfl) ⟨561497, by rfl⟩ : syracuseStep 2994653 = 1122995) (by norm_num)
theorem B2699741 : Blo 1401520 2699741 := bbase (se 3 (by rfl) ⟨506201, by rfl⟩ : syracuseStep 2699741 = 1012403) (by norm_num)
theorem B1774057 : Blo 1401520 1774057 := bbase (se 2 (by rfl) ⟨665271, by rfl⟩ : syracuseStep 1774057 = 1330543) (by norm_num)
theorem B1798633 : Blo 1401520 1798633 := bbase (se 2 (by rfl) ⟨674487, by rfl⟩ : syracuseStep 1798633 = 1348975) (by norm_num)
theorem B1577461 : Blo 1401520 1577461 := bbase (se 5 (by rfl) ⟨73943, by rfl⟩ : syracuseStep 1577461 = 147887) (by norm_num)
theorem B1683973 : Blo 1401520 1683973 := bbase (se 4 (by rfl) ⟨157872, by rfl⟩ : syracuseStep 1683973 = 315745) (by norm_num)
theorem B1577497 : Blo 1401520 1577497 := bbase (se 2 (by rfl) ⟨591561, by rfl⟩ : syracuseStep 1577497 = 1183123) (by norm_num)
theorem B3551789 : Blo 1401520 3551789 := bbase (se 3 (by rfl) ⟨665960, by rfl⟩ : syracuseStep 3551789 = 1331921) (by norm_num)
theorem B1577533 : Blo 1401520 1577533 := bbase (se 3 (by rfl) ⟨295787, by rfl⟩ : syracuseStep 1577533 = 591575) (by norm_num)
theorem B2527805 : Blo 1401520 2527805 := bbase (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) (by norm_num)
theorem B3330629 : Blo 1401520 3330629 := bbase (se 4 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 3330629 = 624493) (by norm_num)
theorem B3994181 : Blo 1401520 3994181 := bbase (se 4 (by rfl) ⟨374454, by rfl⟩ : syracuseStep 3994181 = 748909) (by norm_num)
theorem B1774153 : Blo 1401520 1774153 := bbase (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) (by norm_num)
theorem B1577569 : Blo 1401520 1577569 := bbase (se 2 (by rfl) ⟨591588, by rfl⟩ : syracuseStep 1577569 = 1183177) (by norm_num)
theorem B1577605 : Blo 1401520 1577605 := bbase (se 4 (by rfl) ⟨147900, by rfl⟩ : syracuseStep 1577605 = 295801) (by norm_num)
theorem B1577641 : Blo 1401520 1577641 := bbase (se 2 (by rfl) ⟨591615, by rfl⟩ : syracuseStep 1577641 = 1183231) (by norm_num)
theorem B6394549 : Blo 1401520 6394549 := bbase (se 5 (by rfl) ⟨299744, by rfl⟩ : syracuseStep 6394549 = 599489) (by norm_num)
theorem B4494005 : Blo 1401520 4494005 := bbase (se 5 (by rfl) ⟨210656, by rfl⟩ : syracuseStep 4494005 = 421313) (by norm_num)
theorem B1798853 : Blo 1401520 1798853 := bbase (se 4 (by rfl) ⟨168642, by rfl⟩ : syracuseStep 1798853 = 337285) (by norm_num)
theorem B3601093 : Blo 1401520 3601093 := bbase (se 4 (by rfl) ⟨337602, by rfl⟩ : syracuseStep 3601093 = 675205) (by norm_num)
theorem B1577677 : Blo 1401520 1577677 := bbase (se 3 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 1577677 = 591629) (by norm_num)
theorem B1577713 : Blo 1401520 1577713 := bbase (se 2 (by rfl) ⟨591642, by rfl⟩ : syracuseStep 1577713 = 1183285) (by norm_num)
theorem B1774325 : Blo 1401520 1774325 := bbase (se 5 (by rfl) ⟨83171, by rfl⟩ : syracuseStep 1774325 = 166343) (by norm_num)
theorem B3994373 : Blo 1401520 3994373 := bbase (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) (by norm_num)
theorem B1577749 : Blo 1401520 1577749 := bbase (se 6 (by rfl) ⟨36978, by rfl⟩ : syracuseStep 1577749 = 73957) (by norm_num)
theorem B1774381 : Blo 1401520 1774381 := bbase (se 3 (by rfl) ⟨332696, by rfl⟩ : syracuseStep 1774381 = 665393) (by norm_num)
theorem B1577785 : Blo 1401520 1577785 := bbase (se 2 (by rfl) ⟨591669, by rfl⟩ : syracuseStep 1577785 = 1183339) (by norm_num)
theorem B1577821 : Blo 1401520 1577821 := bbase (se 3 (by rfl) ⟨295841, by rfl⟩ : syracuseStep 1577821 = 591683) (by norm_num)
theorem B4731749 : Blo 1401520 4731749 := bbase (se 4 (by rfl) ⟨443601, by rfl⟩ : syracuseStep 4731749 = 887203) (by norm_num)
theorem B1577857 : Blo 1401520 1577857 := bbase (se 2 (by rfl) ⟨591696, by rfl⟩ : syracuseStep 1577857 = 1183393) (by norm_num)
theorem B3552133 : Blo 1401520 3552133 := bbase (se 4 (by rfl) ⟨333012, by rfl⟩ : syracuseStep 3552133 = 666025) (by norm_num)
theorem B1774477 : Blo 1401520 1774477 := bbase (se 3 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 1774477 = 665429) (by norm_num)
theorem B1577893 : Blo 1401520 1577893 := bbase (se 4 (by rfl) ⟨147927, by rfl⟩ : syracuseStep 1577893 = 295855) (by norm_num)
theorem B1577929 : Blo 1401520 1577929 := bbase (se 2 (by rfl) ⟨591723, by rfl⟩ : syracuseStep 1577929 = 1183447) (by norm_num)
theorem B53892053 : Blo 1401520 53892053 := bbase (se 7 (by rfl) ⟨631547, by rfl⟩ : syracuseStep 53892053 = 1263095) (by norm_num)
theorem B2995157 : Blo 1401520 2995157 := bbase (se 7 (by rfl) ⟨35099, by rfl⟩ : syracuseStep 2995157 = 70199) (by norm_num)
theorem B2995165 : Blo 1401520 2995165 := bbase (se 3 (by rfl) ⟨561593, by rfl⟩ : syracuseStep 2995165 = 1123187) (by norm_num)
theorem B1577965 : Blo 1401520 1577965 := bbase (se 3 (by rfl) ⟨295868, by rfl⟩ : syracuseStep 1577965 = 591737) (by norm_num)
theorem B3552245 : Blo 1401520 3552245 := bbase (se 5 (by rfl) ⟨166511, by rfl⟩ : syracuseStep 3552245 = 333023) (by norm_num)
theorem B2102285 : Blo 1401520 2102285 := bbase (se 3 (by rfl) ⟨394178, by rfl⟩ : syracuseStep 2102285 = 788357) (by norm_num)
theorem B1578001 : Blo 1401520 1578001 := bbase (se 2 (by rfl) ⟨591750, by rfl⟩ : syracuseStep 1578001 = 1183501) (by norm_num)
theorem B1995797 : Blo 1401520 1995797 := bbase (se 6 (by rfl) ⟨46776, by rfl⟩ : syracuseStep 1995797 = 93553) (by norm_num)
theorem B2102309 : Blo 1401520 2102309 := bbase (se 4 (by rfl) ⟨197091, by rfl⟩ : syracuseStep 2102309 = 394183) (by norm_num)
theorem B1578037 : Blo 1401520 1578037 := bbase (se 5 (by rfl) ⟨73970, by rfl⟩ : syracuseStep 1578037 = 147941) (by norm_num)
theorem B1774649 : Blo 1401520 1774649 := bbase (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) (by norm_num)
theorem B2102333 : Blo 1401520 2102333 := bbase (se 3 (by rfl) ⟨394187, by rfl⟩ : syracuseStep 2102333 = 788375) (by norm_num)
theorem B3200077 : Blo 1401520 3200077 := bbase (se 3 (by rfl) ⟨600014, by rfl⟩ : syracuseStep 3200077 = 1200029) (by norm_num)
theorem B2102357 : Blo 1401520 2102357 := bbase (se 8 (by rfl) ⟨12318, by rfl⟩ : syracuseStep 2102357 = 24637) (by norm_num)
theorem B1578073 : Blo 1401520 1578073 := bbase (se 2 (by rfl) ⟨591777, by rfl⟩ : syracuseStep 1578073 = 1183555) (by norm_num)
theorem B1995877 : Blo 1401520 1995877 := bbase (se 4 (by rfl) ⟨187113, by rfl⟩ : syracuseStep 1995877 = 374227) (by norm_num)
theorem B2102381 : Blo 1401520 2102381 := bbase (se 3 (by rfl) ⟨394196, by rfl⟩ : syracuseStep 2102381 = 788393) (by norm_num)
theorem B1774705 : Blo 1401520 1774705 := bbase (se 2 (by rfl) ⟨665514, by rfl⟩ : syracuseStep 1774705 = 1331029) (by norm_num)
theorem B1578109 : Blo 1401520 1578109 := bbase (se 3 (by rfl) ⟨295895, by rfl⟩ : syracuseStep 1578109 = 591791) (by norm_num)
theorem B2102405 : Blo 1401520 2102405 := bbase (se 4 (by rfl) ⟨197100, by rfl⟩ : syracuseStep 2102405 = 394201) (by norm_num)
theorem B2102429 : Blo 1401520 2102429 := bbase (se 3 (by rfl) ⟨394205, by rfl⟩ : syracuseStep 2102429 = 788411) (by norm_num)
theorem B1578145 : Blo 1401520 1578145 := bbase (se 2 (by rfl) ⟨591804, by rfl⟩ : syracuseStep 1578145 = 1183609) (by norm_num)
theorem B5690533 : Blo 1401520 5690533 := bbase (se 4 (by rfl) ⟨533487, by rfl⟩ : syracuseStep 5690533 = 1066975) (by norm_num)
theorem B2102453 : Blo 1401520 2102453 := bbase (se 5 (by rfl) ⟨98552, by rfl⟩ : syracuseStep 2102453 = 197105) (by norm_num)
theorem B3552437 : Blo 1401520 3552437 := bbase (se 5 (by rfl) ⟨166520, by rfl⟩ : syracuseStep 3552437 = 333041) (by norm_num)
theorem B1578181 : Blo 1401520 1578181 := bbase (se 4 (by rfl) ⟨147954, by rfl⟩ : syracuseStep 1578181 = 295909) (by norm_num)
theorem B2102477 : Blo 1401520 2102477 := bbase (se 3 (by rfl) ⟨394214, by rfl⟩ : syracuseStep 2102477 = 788429) (by norm_num)
theorem B1684685 : Blo 1401520 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B1774801 : Blo 1401520 1774801 := bbase (se 2 (by rfl) ⟨665550, by rfl⟩ : syracuseStep 1774801 = 1331101) (by norm_num)
theorem B1995997 : Blo 1401520 1995997 := bbase (se 3 (by rfl) ⟨374249, by rfl⟩ : syracuseStep 1995997 = 748499) (by norm_num)
theorem B2102501 : Blo 1401520 2102501 := bbase (se 4 (by rfl) ⟨197109, by rfl⟩ : syracuseStep 2102501 = 394219) (by norm_num)
theorem B1578217 : Blo 1401520 1578217 := bbase (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) (by norm_num)
theorem B2102525 : Blo 1401520 2102525 := bbase (se 3 (by rfl) ⟨394223, by rfl⟩ : syracuseStep 2102525 = 788447) (by norm_num)
theorem B1578253 : Blo 1401520 1578253 := bbase (se 3 (by rfl) ⟨295922, by rfl⟩ : syracuseStep 1578253 = 591845) (by norm_num)
theorem B2102549 : Blo 1401520 2102549 := bbase (se 6 (by rfl) ⟨49278, by rfl⟩ : syracuseStep 2102549 = 98557) (by norm_num)
theorem B4732181 : Blo 1401520 4732181 := bbase (se 6 (by rfl) ⟨110910, by rfl⟩ : syracuseStep 4732181 = 221821) (by norm_num)
theorem B2102573 : Blo 1401520 2102573 := bbase (se 3 (by rfl) ⟨394232, by rfl⟩ : syracuseStep 2102573 = 788465) (by norm_num)
theorem B1578289 : Blo 1401520 1578289 := bbase (se 2 (by rfl) ⟨591858, by rfl⟩ : syracuseStep 1578289 = 1183717) (by norm_num)
theorem B1996093 : Blo 1401520 1996093 := bbase (se 3 (by rfl) ⟨374267, by rfl⟩ : syracuseStep 1996093 = 748535) (by norm_num)
theorem B2102597 : Blo 1401520 2102597 := bbase (se 4 (by rfl) ⟨197118, by rfl⟩ : syracuseStep 2102597 = 394237) (by norm_num)
theorem B1578325 : Blo 1401520 1578325 := bbase (se 14 (by rfl) ⟨144, by rfl⟩ : syracuseStep 1578325 = 289) (by norm_num)
theorem B2102621 : Blo 1401520 2102621 := bbase (se 3 (by rfl) ⟨394241, by rfl⟩ : syracuseStep 2102621 = 788483) (by norm_num)
theorem B2102645 : Blo 1401520 2102645 := bbase (se 5 (by rfl) ⟨98561, by rfl⟩ : syracuseStep 2102645 = 197123) (by norm_num)
theorem B1578361 : Blo 1401520 1578361 := bbase (se 2 (by rfl) ⟨591885, by rfl⟩ : syracuseStep 1578361 = 1183771) (by norm_num)
theorem B1774973 : Blo 1401520 1774973 := bbase (se 3 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 1774973 = 665615) (by norm_num)
theorem B2102669 : Blo 1401520 2102669 := bbase (se 3 (by rfl) ⟨394250, by rfl⟩ : syracuseStep 2102669 = 788501) (by norm_num)
theorem B1578397 : Blo 1401520 1578397 := bbase (se 3 (by rfl) ⟨295949, by rfl⟩ : syracuseStep 1578397 = 591899) (by norm_num)
theorem B2102693 : Blo 1401520 2102693 := bbase (se 4 (by rfl) ⟨197127, by rfl⟩ : syracuseStep 2102693 = 394255) (by norm_num)
theorem B1775029 : Blo 1401520 1775029 := bbase (se 5 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 1775029 = 166409) (by norm_num)
theorem B2102717 : Blo 1401520 2102717 := bbase (se 3 (by rfl) ⟨394259, by rfl⟩ : syracuseStep 2102717 = 788519) (by norm_num)
theorem B1578433 : Blo 1401520 1578433 := bbase (se 2 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 1578433 = 1183825) (by norm_num)
theorem B2102741 : Blo 1401520 2102741 := bbase (se 7 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 2102741 = 49283) (by norm_num)
theorem B1578469 : Blo 1401520 1578469 := bbase (se 4 (by rfl) ⟨147981, by rfl⟩ : syracuseStep 1578469 = 295963) (by norm_num)
theorem B2102765 : Blo 1401520 2102765 := bbase (se 3 (by rfl) ⟨394268, by rfl⟩ : syracuseStep 2102765 = 788537) (by norm_num)
theorem B2102789 : Blo 1401520 2102789 := bbase (se 4 (by rfl) ⟨197136, by rfl⟩ : syracuseStep 2102789 = 394273) (by norm_num)
theorem B1578505 : Blo 1401520 1578505 := bbase (se 2 (by rfl) ⟨591939, by rfl⟩ : syracuseStep 1578505 = 1183879) (by norm_num)
theorem B1775125 : Blo 1401520 1775125 := bbase (se 6 (by rfl) ⟨41604, by rfl⟩ : syracuseStep 1775125 = 83209) (by norm_num)
theorem B2102813 : Blo 1401520 2102813 := bbase (se 3 (by rfl) ⟨394277, by rfl⟩ : syracuseStep 2102813 = 788555) (by norm_num)
theorem B1685021 : Blo 1401520 1685021 := bbase (se 3 (by rfl) ⟨315941, by rfl⟩ : syracuseStep 1685021 = 631883) (by norm_num)
theorem B1578541 : Blo 1401520 1578541 := bbase (se 3 (by rfl) ⟨295976, by rfl⟩ : syracuseStep 1578541 = 591953) (by norm_num)
theorem B5322293 : Blo 1401520 5322293 := bbase (se 5 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 5322293 = 498965) (by norm_num)
theorem B2102837 : Blo 1401520 2102837 := bbase (se 5 (by rfl) ⟨98570, by rfl⟩ : syracuseStep 2102837 = 197141) (by norm_num)
theorem B7099973 : Blo 1401520 7099973 := bbase (se 4 (by rfl) ⟨665622, by rfl⟩ : syracuseStep 7099973 = 1331245) (by norm_num)
theorem B2102861 : Blo 1401520 2102861 := bbase (se 3 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 2102861 = 788573) (by norm_num)
theorem B1578577 : Blo 1401520 1578577 := bbase (se 2 (by rfl) ⟨591966, by rfl⟩ : syracuseStep 1578577 = 1183933) (by norm_num)
theorem B7992917 : Blo 1401520 7992917 := bbase (se 8 (by rfl) ⟨46833, by rfl⟩ : syracuseStep 7992917 = 93667) (by norm_num)
theorem B2102885 : Blo 1401520 2102885 := bbase (se 4 (by rfl) ⟨197145, by rfl⟩ : syracuseStep 2102885 = 394291) (by norm_num)
theorem B1578613 : Blo 1401520 1578613 := bbase (se 5 (by rfl) ⟨73997, by rfl⟩ : syracuseStep 1578613 = 147995) (by norm_num)
theorem B2102909 : Blo 1401520 2102909 := bbase (se 3 (by rfl) ⟨394295, by rfl⟩ : syracuseStep 2102909 = 788591) (by norm_num)
theorem B1685137 : Blo 1401520 1685137 := bbase (se 2 (by rfl) ⟨631926, by rfl⟩ : syracuseStep 1685137 = 1263853) (by norm_num)
theorem B2102933 : Blo 1401520 2102933 := bbase (se 6 (by rfl) ⟨49287, by rfl⟩ : syracuseStep 2102933 = 98575) (by norm_num)
theorem B1578649 : Blo 1401520 1578649 := bbase (se 2 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 1578649 = 1183987) (by norm_num)
theorem B2365085 : Blo 1401520 2365085 := bbase (se 3 (by rfl) ⟨443453, by rfl⟩ : syracuseStep 2365085 = 886907) (by norm_num)
theorem B1685161 : Blo 1401520 1685161 := bbase (se 2 (by rfl) ⟨631935, by rfl⟩ : syracuseStep 1685161 = 1263871) (by norm_num)
theorem B2102957 : Blo 1401520 2102957 := bbase (se 3 (by rfl) ⟨394304, by rfl⟩ : syracuseStep 2102957 = 788609) (by norm_num)
theorem B11368117 : Blo 1401520 11368117 := bbase (se 5 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 11368117 = 1065761) (by norm_num)
theorem B1578685 : Blo 1401520 1578685 := bbase (se 3 (by rfl) ⟨296003, by rfl⟩ : syracuseStep 1578685 = 592007) (by norm_num)
theorem B1775297 : Blo 1401520 1775297 := bbase (se 2 (by rfl) ⟨665736, by rfl⟩ : syracuseStep 1775297 = 1331473) (by norm_num)
theorem B2102981 : Blo 1401520 2102981 := bbase (se 4 (by rfl) ⟨197154, by rfl⟩ : syracuseStep 2102981 = 394309) (by norm_num)
theorem B4732613 : Blo 1401520 4732613 := bbase (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) (by norm_num)
theorem B2103005 : Blo 1401520 2103005 := bbase (se 3 (by rfl) ⟨394313, by rfl⟩ : syracuseStep 2103005 = 788627) (by norm_num)
theorem B1578721 : Blo 1401520 1578721 := bbase (se 2 (by rfl) ⟨592020, by rfl⟩ : syracuseStep 1578721 = 1184041) (by norm_num)
theorem B3995365 : Blo 1401520 3995365 := bbase (se 4 (by rfl) ⟨374565, by rfl⟩ : syracuseStep 3995365 = 749131) (by norm_num)
theorem B2103029 : Blo 1401520 2103029 := bbase (se 5 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 2103029 = 197159) (by norm_num)
theorem B8763125 : Blo 1401520 8763125 := bbase (se 5 (by rfl) ⟨410771, by rfl⟩ : syracuseStep 8763125 = 821543) (by norm_num)
theorem B1775353 : Blo 1401520 1775353 := bbase (se 2 (by rfl) ⟨665757, by rfl⟩ : syracuseStep 1775353 = 1331515) (by norm_num)
theorem B1578757 : Blo 1401520 1578757 := bbase (se 4 (by rfl) ⟨148008, by rfl⟩ : syracuseStep 1578757 = 296017) (by norm_num)
theorem B2103053 : Blo 1401520 2103053 := bbase (se 3 (by rfl) ⟨394322, by rfl⟩ : syracuseStep 2103053 = 788645) (by norm_num)
theorem B2365213 : Blo 1401520 2365213 := bbase (se 3 (by rfl) ⟨443477, by rfl⟩ : syracuseStep 2365213 = 886955) (by norm_num)
theorem B2103077 : Blo 1401520 2103077 := bbase (se 4 (by rfl) ⟨197163, by rfl⟩ : syracuseStep 2103077 = 394327) (by norm_num)
theorem B1578793 : Blo 1401520 1578793 := bbase (se 2 (by rfl) ⟨592047, by rfl⟩ : syracuseStep 1578793 = 1184095) (by norm_num)
theorem B1996589 : Blo 1401520 1996589 := bbase (se 3 (by rfl) ⟨374360, by rfl⟩ : syracuseStep 1996589 = 748721) (by norm_num)
theorem B2103101 : Blo 1401520 2103101 := bbase (se 3 (by rfl) ⟨394331, by rfl⟩ : syracuseStep 2103101 = 788663) (by norm_num)
theorem B1578829 : Blo 1401520 1578829 := bbase (se 3 (by rfl) ⟨296030, by rfl⟩ : syracuseStep 1578829 = 592061) (by norm_num)
theorem B5322581 : Blo 1401520 5322581 := bbase (se 9 (by rfl) ⟨15593, by rfl⟩ : syracuseStep 5322581 = 31187) (by norm_num)
theorem B2103125 : Blo 1401520 2103125 := bbase (se 9 (by rfl) ⟨6161, by rfl⟩ : syracuseStep 2103125 = 12323) (by norm_num)
theorem B1775449 : Blo 1401520 1775449 := bbase (se 2 (by rfl) ⟨665793, by rfl⟩ : syracuseStep 1775449 = 1331587) (by norm_num)
theorem B2103149 : Blo 1401520 2103149 := bbase (se 3 (by rfl) ⟨394340, by rfl⟩ : syracuseStep 2103149 = 788681) (by norm_num)
theorem B1578865 : Blo 1401520 1578865 := bbase (se 2 (by rfl) ⟨592074, by rfl⟩ : syracuseStep 1578865 = 1184149) (by norm_num)
theorem B2365301 : Blo 1401520 2365301 := bbase (se 5 (by rfl) ⟨110873, by rfl⟩ : syracuseStep 2365301 = 221747) (by norm_num)
theorem B2103173 : Blo 1401520 2103173 := bbase (se 4 (by rfl) ⟨197172, by rfl⟩ : syracuseStep 2103173 = 394345) (by norm_num)
theorem B1578901 : Blo 1401520 1578901 := bbase (se 6 (by rfl) ⟨37005, by rfl⟩ : syracuseStep 1578901 = 74011) (by norm_num)
theorem B2103197 : Blo 1401520 2103197 := bbase (se 3 (by rfl) ⟨394349, by rfl⟩ : syracuseStep 2103197 = 788699) (by norm_num)
theorem B2103221 : Blo 1401520 2103221 := bbase (se 5 (by rfl) ⟨98588, by rfl⟩ : syracuseStep 2103221 = 197177) (by norm_num)
theorem B1578937 : Blo 1401520 1578937 := bbase (se 2 (by rfl) ⟨592101, by rfl⟩ : syracuseStep 1578937 = 1184203) (by norm_num)
theorem B2103245 : Blo 1401520 2103245 := bbase (se 3 (by rfl) ⟨394358, by rfl⟩ : syracuseStep 2103245 = 788717) (by norm_num)
theorem B1497053 : Blo 1401520 1497053 := bbase (se 3 (by rfl) ⟨280697, by rfl⟩ : syracuseStep 1497053 = 561395) (by norm_num)
theorem B2103269 : Blo 1401520 2103269 := bbase (se 4 (by rfl) ⟨197181, by rfl⟩ : syracuseStep 2103269 = 394363) (by norm_num)
theorem B3201005 : Blo 1401520 3201005 := bbase (se 3 (by rfl) ⟨600188, by rfl⟩ : syracuseStep 3201005 = 1200377) (by norm_num)
theorem B2365429 : Blo 1401520 2365429 := bbase (se 5 (by rfl) ⟨110879, by rfl⟩ : syracuseStep 2365429 = 221759) (by norm_num)
theorem B2103293 : Blo 1401520 2103293 := bbase (se 3 (by rfl) ⟨394367, by rfl⟩ : syracuseStep 2103293 = 788735) (by norm_num)
theorem B1775621 : Blo 1401520 1775621 := bbase (se 4 (by rfl) ⟨166464, by rfl⟩ : syracuseStep 1775621 = 332929) (by norm_num)
theorem B2103317 : Blo 1401520 2103317 := bbase (se 6 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 2103317 = 98593) (by norm_num)
theorem B2103341 : Blo 1401520 2103341 := bbase (se 3 (by rfl) ⟨394376, by rfl⟩ : syracuseStep 2103341 = 788753) (by norm_num)
theorem B8534069 : Blo 1401520 8534069 := bbase (se 5 (by rfl) ⟨400034, by rfl⟩ : syracuseStep 8534069 = 800069) (by norm_num)
theorem B1775677 : Blo 1401520 1775677 := bbase (se 3 (by rfl) ⟨332939, by rfl⟩ : syracuseStep 1775677 = 665879) (by norm_num)
theorem B2103365 : Blo 1401520 2103365 := bbase (se 4 (by rfl) ⟨197190, by rfl⟩ : syracuseStep 2103365 = 394381) (by norm_num)
theorem B2996293 : Blo 1401520 2996293 := bbase (se 4 (by rfl) ⟨280902, by rfl⟩ : syracuseStep 2996293 = 561805) (by norm_num)
theorem B2365517 : Blo 1401520 2365517 := bbase (se 3 (by rfl) ⟨443534, by rfl⟩ : syracuseStep 2365517 = 887069) (by norm_num)
theorem B2103389 : Blo 1401520 2103389 := bbase (se 3 (by rfl) ⟨394385, by rfl⟩ : syracuseStep 2103389 = 788771) (by norm_num)
theorem B2103413 : Blo 1401520 2103413 := bbase (se 5 (by rfl) ⟨98597, by rfl⟩ : syracuseStep 2103413 = 197195) (by norm_num)
theorem B4733045 : Blo 1401520 4733045 := bbase (se 5 (by rfl) ⟨221861, by rfl⟩ : syracuseStep 4733045 = 443723) (by norm_num)
theorem B2103437 : Blo 1401520 2103437 := bbase (se 3 (by rfl) ⟨394394, by rfl⟩ : syracuseStep 2103437 = 788789) (by norm_num)
theorem B1497241 : Blo 1401520 1497241 := bbase (se 2 (by rfl) ⟨561465, by rfl⟩ : syracuseStep 1497241 = 1122931) (by norm_num)
theorem B1775773 : Blo 1401520 1775773 := bbase (se 3 (by rfl) ⟨332957, by rfl⟩ : syracuseStep 1775773 = 665915) (by norm_num)
theorem B1824925 : Blo 1401520 1824925 := bbase (se 3 (by rfl) ⟨342173, by rfl⟩ : syracuseStep 1824925 = 684347) (by norm_num)
theorem B2103461 : Blo 1401520 2103461 := bbase (se 4 (by rfl) ⟨197199, by rfl⟩ : syracuseStep 2103461 = 394399) (by norm_num)
theorem B2103485 : Blo 1401520 2103485 := bbase (se 3 (by rfl) ⟨394403, by rfl⟩ : syracuseStep 2103485 = 788807) (by norm_num)
theorem B2365645 : Blo 1401520 2365645 := bbase (se 3 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 2365645 = 887117) (by norm_num)
theorem B2103509 : Blo 1401520 2103509 := bbase (se 7 (by rfl) ⟨24650, by rfl⟩ : syracuseStep 2103509 = 49301) (by norm_num)
theorem B2103533 : Blo 1401520 2103533 := bbase (se 3 (by rfl) ⟨394412, by rfl⟩ : syracuseStep 2103533 = 788825) (by norm_num)
theorem B2103557 : Blo 1401520 2103557 := bbase (se 4 (by rfl) ⟨197208, by rfl⟩ : syracuseStep 2103557 = 394417) (by norm_num)
theorem B5994773 : Blo 1401520 5994773 := bbase (se 6 (by rfl) ⟨140502, by rfl⟩ : syracuseStep 5994773 = 281005) (by norm_num)
theorem B2103581 : Blo 1401520 2103581 := bbase (se 3 (by rfl) ⟨394421, by rfl⟩ : syracuseStep 2103581 = 788843) (by norm_num)
theorem B2365733 : Blo 1401520 2365733 := bbase (se 4 (by rfl) ⟨221787, by rfl⟩ : syracuseStep 2365733 = 443575) (by norm_num)
theorem B2103605 : Blo 1401520 2103605 := bbase (se 5 (by rfl) ⟨98606, by rfl⟩ : syracuseStep 2103605 = 197213) (by norm_num)
theorem B1775945 : Blo 1401520 1775945 := bbase (se 2 (by rfl) ⟨665979, by rfl⟩ : syracuseStep 1775945 = 1331959) (by norm_num)
theorem B2103629 : Blo 1401520 2103629 := bbase (se 3 (by rfl) ⟨394430, by rfl⟩ : syracuseStep 2103629 = 788861) (by norm_num)
theorem B1997141 : Blo 1401520 1997141 := bbase (se 10 (by rfl) ⟨2925, by rfl⟩ : syracuseStep 1997141 = 5851) (by norm_num)
theorem B1685857 : Blo 1401520 1685857 := bbase (se 2 (by rfl) ⟨632196, by rfl⟩ : syracuseStep 1685857 = 1264393) (by norm_num)
theorem B2103653 : Blo 1401520 2103653 := bbase (se 4 (by rfl) ⟨197217, by rfl⟩ : syracuseStep 2103653 = 394435) (by norm_num)
theorem B2103677 : Blo 1401520 2103677 := bbase (se 3 (by rfl) ⟨394439, by rfl⟩ : syracuseStep 2103677 = 788879) (by norm_num)
theorem B1776001 : Blo 1401520 1776001 := bbase (se 2 (by rfl) ⟨666000, by rfl⟩ : syracuseStep 1776001 = 1332001) (by norm_num)
theorem B5986709 : Blo 1401520 5986709 := bbase (se 6 (by rfl) ⟨140313, by rfl⟩ : syracuseStep 5986709 = 280627) (by norm_num)
theorem B2103701 : Blo 1401520 2103701 := bbase (se 6 (by rfl) ⟨49305, by rfl⟩ : syracuseStep 2103701 = 98611) (by norm_num)
theorem B3037589 : Blo 1401520 3037589 := bbase (se 6 (by rfl) ⟨71193, by rfl⟩ : syracuseStep 3037589 = 142387) (by norm_num)
theorem B2365861 : Blo 1401520 2365861 := bbase (se 4 (by rfl) ⟨221799, by rfl⟩ : syracuseStep 2365861 = 443599) (by norm_num)
theorem B2103725 : Blo 1401520 2103725 := bbase (se 3 (by rfl) ⟨394448, by rfl⟩ : syracuseStep 2103725 = 788897) (by norm_num)
theorem B2660789 : Blo 1401520 2660789 := bbase (se 5 (by rfl) ⟨124724, by rfl⟩ : syracuseStep 2660789 = 249449) (by norm_num)
theorem B2996669 : Blo 1401520 2996669 := bbase (se 3 (by rfl) ⟨561875, by rfl⟩ : syracuseStep 2996669 = 1123751) (by norm_num)
theorem B1685953 : Blo 1401520 1685953 := bbase (se 2 (by rfl) ⟨632232, by rfl⟩ : syracuseStep 1685953 = 1264465) (by norm_num)
theorem B2103749 : Blo 1401520 2103749 := bbase (se 4 (by rfl) ⟨197226, by rfl⟩ : syracuseStep 2103749 = 394453) (by norm_num)
theorem B3332549 : Blo 1401520 3332549 := bbase (se 4 (by rfl) ⟨312426, by rfl⟩ : syracuseStep 3332549 = 624853) (by norm_num)
theorem B4323797 : Blo 1401520 4323797 := bbase (se 7 (by rfl) ⟨50669, by rfl⟩ : syracuseStep 4323797 = 101339) (by norm_num)
theorem B2103773 : Blo 1401520 2103773 := bbase (se 3 (by rfl) ⟨394457, by rfl⟩ : syracuseStep 2103773 = 788915) (by norm_num)
theorem B1776097 : Blo 1401520 1776097 := bbase (se 2 (by rfl) ⟨666036, by rfl⟩ : syracuseStep 1776097 = 1332073) (by norm_num)
theorem B2103797 : Blo 1401520 2103797 := bbase (se 5 (by rfl) ⟨98615, by rfl⟩ : syracuseStep 2103797 = 197231) (by norm_num)
theorem B2365949 : Blo 1401520 2365949 := bbase (se 3 (by rfl) ⟨443615, by rfl⟩ : syracuseStep 2365949 = 887231) (by norm_num)
theorem B2103821 : Blo 1401520 2103821 := bbase (se 3 (by rfl) ⟨394466, by rfl⟩ : syracuseStep 2103821 = 788933) (by norm_num)
theorem B4733477 : Blo 1401520 4733477 := bbase (se 4 (by rfl) ⟨443763, by rfl⟩ : syracuseStep 4733477 = 887527) (by norm_num)
theorem B2103845 : Blo 1401520 2103845 := bbase (se 4 (by rfl) ⟨197235, by rfl⟩ : syracuseStep 2103845 = 394471) (by norm_num)
theorem B2103869 : Blo 1401520 2103869 := bbase (se 3 (by rfl) ⟨394475, by rfl⟩ : syracuseStep 2103869 = 788951) (by norm_num)
theorem B2660941 : Blo 1401520 2660941 := bbase (se 3 (by rfl) ⟨498926, by rfl⟩ : syracuseStep 2660941 = 997853) (by norm_num)
theorem B2103893 : Blo 1401520 2103893 := bbase (se 8 (by rfl) ⟨12327, by rfl⟩ : syracuseStep 2103893 = 24655) (by norm_num)
theorem B2103917 : Blo 1401520 2103917 := bbase (se 3 (by rfl) ⟨394484, by rfl⟩ : syracuseStep 2103917 = 788969) (by norm_num)
theorem B2366077 : Blo 1401520 2366077 := bbase (se 3 (by rfl) ⟨443639, by rfl⟩ : syracuseStep 2366077 = 887279) (by norm_num)
theorem B2103941 : Blo 1401520 2103941 := bbase (se 4 (by rfl) ⟨197244, by rfl⟩ : syracuseStep 2103941 = 394489) (by norm_num)
theorem B1776269 : Blo 1401520 1776269 := bbase (se 3 (by rfl) ⟨333050, by rfl⟩ : syracuseStep 1776269 = 666101) (by norm_num)
theorem B2103965 : Blo 1401520 2103965 := bbase (se 3 (by rfl) ⟨394493, by rfl⟩ : syracuseStep 2103965 = 788987) (by norm_num)
theorem B2103989 : Blo 1401520 2103989 := bbase (se 5 (by rfl) ⟨98624, by rfl⟩ : syracuseStep 2103989 = 197249) (by norm_num)
theorem B1776325 : Blo 1401520 1776325 := bbase (se 4 (by rfl) ⟨166530, by rfl⟩ : syracuseStep 1776325 = 333061) (by norm_num)
theorem B2104013 : Blo 1401520 2104013 := bbase (se 3 (by rfl) ⟨394502, by rfl⟩ : syracuseStep 2104013 = 789005) (by norm_num)
theorem B2366165 : Blo 1401520 2366165 := bbase (se 7 (by rfl) ⟨27728, by rfl⟩ : syracuseStep 2366165 = 55457) (by norm_num)
theorem B2104037 : Blo 1401520 2104037 := bbase (se 4 (by rfl) ⟨197253, by rfl⟩ : syracuseStep 2104037 = 394507) (by norm_num)
theorem B2104061 : Blo 1401520 2104061 := bbase (se 3 (by rfl) ⟨394511, by rfl⟩ : syracuseStep 2104061 = 789023) (by norm_num)
theorem B2104085 : Blo 1401520 2104085 := bbase (se 6 (by rfl) ⟨49314, by rfl⟩ : syracuseStep 2104085 = 98629) (by norm_num)
theorem B2104109 : Blo 1401520 2104109 := bbase (se 3 (by rfl) ⟨394520, by rfl⟩ : syracuseStep 2104109 = 789041) (by norm_num)
theorem B3996469 : Blo 1401520 3996469 := bbase (se 5 (by rfl) ⟨187334, by rfl⟩ : syracuseStep 3996469 = 374669) (by norm_num)
theorem B2841413 : Blo 1401520 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B2104133 : Blo 1401520 2104133 := bbase (se 4 (by rfl) ⟨197262, by rfl⟩ : syracuseStep 2104133 = 394525) (by norm_num)
theorem B2366293 : Blo 1401520 2366293 := bbase (se 9 (by rfl) ⟨6932, by rfl⟩ : syracuseStep 2366293 = 13865) (by norm_num)
theorem B7101269 : Blo 1401520 7101269 := bbase (se 9 (by rfl) ⟨20804, by rfl⟩ : syracuseStep 7101269 = 41609) (by norm_num)
theorem B2104157 : Blo 1401520 2104157 := bbase (se 3 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 2104157 = 789059) (by norm_num)
theorem B2841445 : Blo 1401520 2841445 := bbase (se 4 (by rfl) ⟨266385, by rfl⟩ : syracuseStep 2841445 = 532771) (by norm_num)
theorem B2104181 : Blo 1401520 2104181 := bbase (se 5 (by rfl) ⟨98633, by rfl⟩ : syracuseStep 2104181 = 197267) (by norm_num)
theorem B2661245 : Blo 1401520 2661245 := bbase (se 3 (by rfl) ⟨498983, by rfl⟩ : syracuseStep 2661245 = 997967) (by norm_num)
theorem B3038077 : Blo 1401520 3038077 := bbase (se 3 (by rfl) ⟨569639, by rfl⟩ : syracuseStep 3038077 = 1139279) (by norm_num)
theorem B2104205 : Blo 1401520 2104205 := bbase (se 3 (by rfl) ⟨394538, by rfl⟩ : syracuseStep 2104205 = 789077) (by norm_num)
theorem B2399141 : Blo 1401520 2399141 := bbase (se 4 (by rfl) ⟨224919, by rfl⟩ : syracuseStep 2399141 = 449839) (by norm_num)
theorem B2104229 : Blo 1401520 2104229 := bbase (se 4 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 2104229 = 394543) (by norm_num)
theorem B2366381 : Blo 1401520 2366381 := bbase (se 3 (by rfl) ⟨443696, by rfl⟩ : syracuseStep 2366381 = 887393) (by norm_num)
theorem B2104253 : Blo 1401520 2104253 := bbase (se 3 (by rfl) ⟨394547, by rfl⟩ : syracuseStep 2104253 = 789095) (by norm_num)
theorem B1498061 : Blo 1401520 1498061 := bbase (se 3 (by rfl) ⟨280886, by rfl⟩ : syracuseStep 1498061 = 561773) (by norm_num)
theorem B4733909 : Blo 1401520 4733909 := bbase (se 7 (by rfl) ⟨55475, by rfl⟩ : syracuseStep 4733909 = 110951) (by norm_num)
theorem B2104277 : Blo 1401520 2104277 := bbase (se 7 (by rfl) ⟨24659, by rfl⟩ : syracuseStep 2104277 = 49319) (by norm_num)
theorem B2104301 : Blo 1401520 2104301 := bbase (se 3 (by rfl) ⟨394556, by rfl⟩ : syracuseStep 2104301 = 789113) (by norm_num)
theorem B5323765 : Blo 1401520 5323765 := bbase (se 5 (by rfl) ⟨249551, by rfl⟩ : syracuseStep 5323765 = 499103) (by norm_num)
theorem B3947525 : Blo 1401520 3947525 := bbase (se 4 (by rfl) ⟨370080, by rfl⟩ : syracuseStep 3947525 = 740161) (by norm_num)
theorem B2104325 : Blo 1401520 2104325 := bbase (se 4 (by rfl) ⟨197280, by rfl⟩ : syracuseStep 2104325 = 394561) (by norm_num)
theorem B8526869 : Blo 1401520 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B2104349 : Blo 1401520 2104349 := bbase (se 3 (by rfl) ⟨394565, by rfl⟩ : syracuseStep 2104349 = 789131) (by norm_num)
theorem B2366509 : Blo 1401520 2366509 := bbase (se 3 (by rfl) ⟨443720, by rfl⟩ : syracuseStep 2366509 = 887441) (by norm_num)
theorem B2104373 : Blo 1401520 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B1997893 : Blo 1401520 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B2104397 : Blo 1401520 2104397 := bbase (se 3 (by rfl) ⟨394574, by rfl⟩ : syracuseStep 2104397 = 789149) (by norm_num)
theorem B2104421 : Blo 1401520 2104421 := bbase (se 4 (by rfl) ⟨197289, by rfl⟩ : syracuseStep 2104421 = 394579) (by norm_num)
theorem B2104445 : Blo 1401520 2104445 := bbase (se 3 (by rfl) ⟨394583, by rfl⟩ : syracuseStep 2104445 = 789167) (by norm_num)
theorem B2366597 : Blo 1401520 2366597 := bbase (se 4 (by rfl) ⟨221868, by rfl⟩ : syracuseStep 2366597 = 443737) (by norm_num)
theorem B2104469 : Blo 1401520 2104469 := bbase (se 6 (by rfl) ⟨49323, by rfl⟩ : syracuseStep 2104469 = 98647) (by norm_num)
theorem B6577301 : Blo 1401520 6577301 := bbase (se 6 (by rfl) ⟨154155, by rfl⟩ : syracuseStep 6577301 = 308311) (by norm_num)
theorem B2104493 : Blo 1401520 2104493 := bbase (se 3 (by rfl) ⟨394592, by rfl⟩ : syracuseStep 2104493 = 789185) (by norm_num)
theorem B2104517 : Blo 1401520 2104517 := bbase (se 4 (by rfl) ⟨197298, by rfl⟩ : syracuseStep 2104517 = 394597) (by norm_num)
theorem B1621193 : Blo 1401520 1621193 := bbase (se 2 (by rfl) ⟨607947, by rfl⟩ : syracuseStep 1621193 = 1215895) (by norm_num)
theorem B2104541 : Blo 1401520 2104541 := bbase (se 3 (by rfl) ⟨394601, by rfl⟩ : syracuseStep 2104541 = 789203) (by norm_num)
theorem B2104565 : Blo 1401520 2104565 := bbase (se 5 (by rfl) ⟨98651, by rfl⟩ : syracuseStep 2104565 = 197303) (by norm_num)
theorem B2366725 : Blo 1401520 2366725 := bbase (se 4 (by rfl) ⟨221880, by rfl⟩ : syracuseStep 2366725 = 443761) (by norm_num)
theorem B2104589 : Blo 1401520 2104589 := bbase (se 3 (by rfl) ⟨394610, by rfl⟩ : syracuseStep 2104589 = 789221) (by norm_num)
theorem B5324069 : Blo 1401520 5324069 := bbase (se 4 (by rfl) ⟨499131, by rfl⟩ : syracuseStep 5324069 = 998263) (by norm_num)
theorem B2104613 : Blo 1401520 2104613 := bbase (se 4 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 2104613 = 394615) (by norm_num)
theorem B2104637 : Blo 1401520 2104637 := bbase (se 3 (by rfl) ⟨394619, by rfl⟩ : syracuseStep 2104637 = 789239) (by norm_num)
theorem B5053765 : Blo 1401520 5053765 := bbase (se 4 (by rfl) ⟨473790, by rfl⟩ : syracuseStep 5053765 = 947581) (by norm_num)
theorem B11984213 : Blo 1401520 11984213 := bbase (se 11 (by rfl) ⟨8777, by rfl⟩ : syracuseStep 11984213 = 17555) (by norm_num)
theorem B2104661 : Blo 1401520 2104661 := bbase (se 11 (by rfl) ⟨1541, by rfl⟩ : syracuseStep 2104661 = 3083) (by norm_num)
theorem B2366813 : Blo 1401520 2366813 := bbase (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) (by norm_num)
theorem B2104685 : Blo 1401520 2104685 := bbase (se 3 (by rfl) ⟨394628, by rfl⟩ : syracuseStep 2104685 = 789257) (by norm_num)
theorem B2022773 : Blo 1401520 2022773 := bbase (se 5 (by rfl) ⟨94817, by rfl⟩ : syracuseStep 2022773 = 189635) (by norm_num)
theorem B4734341 : Blo 1401520 4734341 := bbase (se 4 (by rfl) ⟨443844, by rfl⟩ : syracuseStep 4734341 = 887689) (by norm_num)
theorem B2104709 : Blo 1401520 2104709 := bbase (se 4 (by rfl) ⟨197316, by rfl⟩ : syracuseStep 2104709 = 394633) (by norm_num)
theorem B1498505 : Blo 1401520 1498505 := bbase (se 2 (by rfl) ⟨561939, by rfl⟩ : syracuseStep 1498505 = 1123879) (by norm_num)
theorem B2104733 : Blo 1401520 2104733 := bbase (se 3 (by rfl) ⟨394637, by rfl⟩ : syracuseStep 2104733 = 789275) (by norm_num)
theorem B6741413 : Blo 1401520 6741413 := bbase (se 4 (by rfl) ⟨632007, by rfl⟩ : syracuseStep 6741413 = 1264015) (by norm_num)
theorem B2104757 : Blo 1401520 2104757 := bbase (se 5 (by rfl) ⟨98660, by rfl⟩ : syracuseStep 2104757 = 197321) (by norm_num)
theorem B2104781 : Blo 1401520 2104781 := bbase (se 3 (by rfl) ⟨394646, by rfl⟩ : syracuseStep 2104781 = 789293) (by norm_num)
theorem B2366941 : Blo 1401520 2366941 := bbase (se 3 (by rfl) ⟨443801, by rfl⟩ : syracuseStep 2366941 = 887603) (by norm_num)
theorem B2104805 : Blo 1401520 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B2104829 : Blo 1401520 2104829 := bbase (se 3 (by rfl) ⟨394655, by rfl⟩ : syracuseStep 2104829 = 789311) (by norm_num)
theorem B4554245 : Blo 1401520 4554245 := bbase (se 4 (by rfl) ⟨426960, by rfl⟩ : syracuseStep 4554245 = 853921) (by norm_num)
theorem B2104853 : Blo 1401520 2104853 := bbase (se 6 (by rfl) ⟨49332, by rfl⟩ : syracuseStep 2104853 = 98665) (by norm_num)
theorem B3153437 : Blo 1401520 3153437 := bbase (se 3 (by rfl) ⟨591269, by rfl⟩ : syracuseStep 3153437 = 1182539) (by norm_num)
theorem B2104877 : Blo 1401520 2104877 := bbase (se 3 (by rfl) ⟨394664, by rfl⟩ : syracuseStep 2104877 = 789329) (by norm_num)
theorem B2367029 : Blo 1401520 2367029 := bbase (se 5 (by rfl) ⟨110954, by rfl⟩ : syracuseStep 2367029 = 221909) (by norm_num)
theorem B2104901 : Blo 1401520 2104901 := bbase (se 4 (by rfl) ⟨197334, by rfl⟩ : syracuseStep 2104901 = 394669) (by norm_num)
theorem B2104925 : Blo 1401520 2104925 := bbase (se 3 (by rfl) ⟨394673, by rfl⟩ : syracuseStep 2104925 = 789347) (by norm_num)
theorem B3153509 : Blo 1401520 3153509 := bbase (se 4 (by rfl) ⟨295641, by rfl⟩ : syracuseStep 3153509 = 591283) (by norm_num)
theorem B2661997 : Blo 1401520 2661997 := bbase (se 3 (by rfl) ⟨499124, by rfl⟩ : syracuseStep 2661997 = 998249) (by norm_num)
theorem B2104949 : Blo 1401520 2104949 := bbase (se 5 (by rfl) ⟨98669, by rfl⟩ : syracuseStep 2104949 = 197339) (by norm_num)
theorem B1498753 : Blo 1401520 1498753 := bbase (se 2 (by rfl) ⟨562032, by rfl⟩ : syracuseStep 1498753 = 1124065) (by norm_num)
theorem B2104973 : Blo 1401520 2104973 := bbase (se 3 (by rfl) ⟨394682, by rfl⟩ : syracuseStep 2104973 = 789365) (by norm_num)
theorem B14384789 : Blo 1401520 14384789 := bbase (se 6 (by rfl) ⟨337143, by rfl⟩ : syracuseStep 14384789 = 674287) (by norm_num)
theorem B2104997 : Blo 1401520 2104997 := bbase (se 4 (by rfl) ⟨197343, by rfl⟩ : syracuseStep 2104997 = 394687) (by norm_num)
theorem B3153581 : Blo 1401520 3153581 := bbase (se 3 (by rfl) ⟨591296, by rfl⟩ : syracuseStep 3153581 = 1182593) (by norm_num)
theorem B2367157 : Blo 1401520 2367157 := bbase (se 5 (by rfl) ⟨110960, by rfl⟩ : syracuseStep 2367157 = 221921) (by norm_num)
theorem B2399933 : Blo 1401520 2399933 := bbase (se 3 (by rfl) ⟨449987, by rfl⟩ : syracuseStep 2399933 = 899975) (by norm_num)
theorem B2105021 : Blo 1401520 2105021 := bbase (se 3 (by rfl) ⟨394691, by rfl⟩ : syracuseStep 2105021 = 789383) (by norm_num)
theorem B2105045 : Blo 1401520 2105045 := bbase (se 7 (by rfl) ⟨24668, by rfl⟩ : syracuseStep 2105045 = 49337) (by norm_num)
theorem B10657493 : Blo 1401520 10657493 := bbase (se 7 (by rfl) ⟨124892, by rfl⟩ : syracuseStep 10657493 = 249785) (by norm_num)
theorem B2105069 : Blo 1401520 2105069 := bbase (se 3 (by rfl) ⟨394700, by rfl⟩ : syracuseStep 2105069 = 789401) (by norm_num)
theorem B3153653 : Blo 1401520 3153653 := bbase (se 5 (by rfl) ⟨147827, by rfl⟩ : syracuseStep 3153653 = 295655) (by norm_num)
theorem B2662141 : Blo 1401520 2662141 := bbase (se 3 (by rfl) ⟨499151, by rfl⟩ : syracuseStep 2662141 = 998303) (by norm_num)
theorem B2105093 : Blo 1401520 2105093 := bbase (se 4 (by rfl) ⟨197352, by rfl⟩ : syracuseStep 2105093 = 394705) (by norm_num)
theorem B2367245 : Blo 1401520 2367245 := bbase (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) (by norm_num)
theorem B1441553 : Blo 1401520 1441553 := bbase (se 2 (by rfl) ⟨540582, by rfl⟩ : syracuseStep 1441553 = 1081165) (by norm_num)
theorem B2105117 : Blo 1401520 2105117 := bbase (se 3 (by rfl) ⟨394709, by rfl⟩ : syracuseStep 2105117 = 789419) (by norm_num)
theorem B4734773 : Blo 1401520 4734773 := bbase (se 5 (by rfl) ⟨221942, by rfl⟩ : syracuseStep 4734773 = 443885) (by norm_num)
theorem B2105141 : Blo 1401520 2105141 := bbase (se 5 (by rfl) ⟨98678, by rfl⟩ : syracuseStep 2105141 = 197357) (by norm_num)
theorem B3153725 : Blo 1401520 3153725 := bbase (se 3 (by rfl) ⟨591323, by rfl⟩ : syracuseStep 3153725 = 1182647) (by norm_num)
theorem B2105165 : Blo 1401520 2105165 := bbase (se 3 (by rfl) ⟨394718, by rfl⟩ : syracuseStep 2105165 = 789437) (by norm_num)
theorem B5193557 : Blo 1401520 5193557 := bbase (se 9 (by rfl) ⟨15215, by rfl⟩ : syracuseStep 5193557 = 30431) (by norm_num)
theorem B2105189 : Blo 1401520 2105189 := bbase (se 4 (by rfl) ⟨197361, by rfl⟩ : syracuseStep 2105189 = 394723) (by norm_num)
theorem B2105213 : Blo 1401520 2105213 := bbase (se 3 (by rfl) ⟨394727, by rfl⟩ : syracuseStep 2105213 = 789455) (by norm_num)
theorem B3153797 : Blo 1401520 3153797 := bbase (se 4 (by rfl) ⟨295668, by rfl⟩ : syracuseStep 3153797 = 591337) (by norm_num)
theorem B2367373 : Blo 1401520 2367373 := bbase (se 3 (by rfl) ⟨443882, by rfl⟩ : syracuseStep 2367373 = 887765) (by norm_num)
theorem B2105237 : Blo 1401520 2105237 := bbase (se 6 (by rfl) ⟨49341, by rfl⟩ : syracuseStep 2105237 = 98683) (by norm_num)
theorem B2662301 : Blo 1401520 2662301 := bbase (se 3 (by rfl) ⟨499181, by rfl⟩ : syracuseStep 2662301 = 998363) (by norm_num)
theorem B2842541 : Blo 1401520 2842541 := bbase (se 3 (by rfl) ⟨532976, by rfl⟩ : syracuseStep 2842541 = 1065953) (by norm_num)
theorem B2105261 : Blo 1401520 2105261 := bbase (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) (by norm_num)
theorem B3153869 : Blo 1401520 3153869 := bbase (se 3 (by rfl) ⟨591350, by rfl⟩ : syracuseStep 3153869 = 1182701) (by norm_num)
theorem B2367461 : Blo 1401520 2367461 := bbase (se 4 (by rfl) ⟨221949, by rfl⟩ : syracuseStep 2367461 = 443899) (by norm_num)
theorem B3153923 : Blo 1401520 3153923 := bstep (se 1 (by rfl) ⟨2365442, by rfl⟩ : syracuseStep 3153923 = 4730885) B4730885
theorem B4734989 : Blo 1401520 4734989 := bstep (se 3 (by rfl) ⟨887810, by rfl⟩ : syracuseStep 4734989 = 1775621) B1775621
theorem B5988401 : Blo 1401520 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B4735043 : Blo 1401520 4735043 := bstep (se 1 (by rfl) ⟨3551282, by rfl⟩ : syracuseStep 4735043 = 7102565) B7102565
theorem B2367569 : Blo 1401520 2367569 := bstep (se 2 (by rfl) ⟨887838, by rfl⟩ : syracuseStep 2367569 = 1775677) B1775677
theorem B5988451 : Blo 1401520 5988451 := bstep (se 1 (by rfl) ⟨4491338, by rfl⟩ : syracuseStep 5988451 = 8982677) B8982677
theorem B2367697 : Blo 1401520 2367697 := bstep (se 2 (by rfl) ⟨887886, by rfl⟩ : syracuseStep 2367697 = 1775773) B1775773
theorem B2433233 : Blo 1401520 2433233 := bstep (se 2 (by rfl) ⟨912462, by rfl⟩ : syracuseStep 2433233 = 1824925) B1824925
theorem B2662627 : Blo 1401520 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B5325041 : Blo 1401520 5325041 := bstep (se 2 (by rfl) ⟨1996890, by rfl⟩ : syracuseStep 5325041 = 3993781) B3993781
theorem B2367731 : Blo 1401520 2367731 := bstep (se 1 (by rfl) ⟨1775798, by rfl⟩ : syracuseStep 2367731 = 3551597) B3551597
theorem B3154193 : Blo 1401520 3154193 := bstep (se 2 (by rfl) ⟨1182822, by rfl⟩ : syracuseStep 3154193 = 2365645) B2365645
theorem B3793169 : Blo 1401520 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B3154211 : Blo 1401520 3154211 := bstep (se 1 (by rfl) ⟨2365658, by rfl⟩ : syracuseStep 3154211 = 4731317) B4731317
theorem B4735313 : Blo 1401520 4735313 := bstep (se 2 (by rfl) ⟨1775742, by rfl⟩ : syracuseStep 4735313 = 3551485) B3551485
theorem B2367859 : Blo 1401520 2367859 := bstep (se 1 (by rfl) ⟨1775894, by rfl⟩ : syracuseStep 2367859 = 3551789) B3551789
theorem B2220419 : Blo 1401520 2220419 := bstep (se 1 (by rfl) ⟨1665314, by rfl⟩ : syracuseStep 2220419 = 3330629) B3330629
theorem B2662787 : Blo 1401520 2662787 := bstep (se 1 (by rfl) ⟨1997090, by rfl⟩ : syracuseStep 2662787 = 3994181) B3994181
theorem B2368001 : Blo 1401520 2368001 := bstep (se 2 (by rfl) ⟨888000, by rfl⟩ : syracuseStep 2368001 = 1776001) B1776001
theorem B15172109 : Blo 1401520 15172109 := bstep (se 3 (by rfl) ⟨2844770, by rfl⟩ : syracuseStep 15172109 = 5689541) B5689541
theorem B3154481 : Blo 1401520 3154481 := bstep (se 2 (by rfl) ⟨1182930, by rfl⟩ : syracuseStep 3154481 = 2365861) B2365861
theorem B2277953 : Blo 1401520 2277953 := bstep (se 2 (by rfl) ⟨854232, by rfl⟩ : syracuseStep 2277953 = 1708465) B1708465
theorem B3154499 : Blo 1401520 3154499 := bstep (se 1 (by rfl) ⟨2365874, by rfl⟩ : syracuseStep 3154499 = 4731749) B4731749
theorem B2277985 : Blo 1401520 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B17973859 : Blo 1401520 17973859 := bstep (se 1 (by rfl) ⟨13480394, by rfl⟩ : syracuseStep 17973859 = 26960789) B26960789
theorem B9732707 : Blo 1401520 9732707 := bstep (se 1 (by rfl) ⟨7299530, by rfl⟩ : syracuseStep 9732707 = 14599061) B14599061
theorem B2368129 : Blo 1401520 2368129 := bstep (se 2 (by rfl) ⟨888048, by rfl⟩ : syracuseStep 2368129 = 1776097) B1776097
theorem B2368163 : Blo 1401520 2368163 := bstep (se 1 (by rfl) ⟨1776122, by rfl⟩ : syracuseStep 2368163 = 3552245) B3552245
theorem B1401523 : Blo 1401520 1401523 := bstep (se 1 (by rfl) ⟨1051142, by rfl⟩ : syracuseStep 1401523 = 2102285) B2102285
theorem B1401539 : Blo 1401520 1401539 := bstep (se 1 (by rfl) ⟨1051154, by rfl⟩ : syracuseStep 1401539 = 2102309) B2102309
theorem B1401555 : Blo 1401520 1401555 := bstep (se 1 (by rfl) ⟨1051166, by rfl⟩ : syracuseStep 1401555 = 2102333) B2102333
theorem B1401571 : Blo 1401520 1401571 := bstep (se 1 (by rfl) ⟨1051178, by rfl⟩ : syracuseStep 1401571 = 2102357) B2102357
theorem B1401587 : Blo 1401520 1401587 := bstep (se 1 (by rfl) ⟨1051190, by rfl⟩ : syracuseStep 1401587 = 2102381) B2102381
theorem B1401603 : Blo 1401520 1401603 := bstep (se 1 (by rfl) ⟨1051202, by rfl⟩ : syracuseStep 1401603 = 2102405) B2102405
theorem B3547921 : Blo 1401520 3547921 := bstep (se 2 (by rfl) ⟨1330470, by rfl⟩ : syracuseStep 3547921 = 2660941) B2660941
theorem B1401619 : Blo 1401520 1401619 := bstep (se 1 (by rfl) ⟨1051214, by rfl⟩ : syracuseStep 1401619 = 2102429) B2102429
theorem B1401635 : Blo 1401520 1401635 := bstep (se 1 (by rfl) ⟨1051226, by rfl⟩ : syracuseStep 1401635 = 2102453) B2102453
theorem B2368291 : Blo 1401520 2368291 := bstep (se 1 (by rfl) ⟨1776218, by rfl⟩ : syracuseStep 2368291 = 3552437) B3552437
theorem B7988017 : Blo 1401520 7988017 := bstep (se 2 (by rfl) ⟨2995506, by rfl⟩ : syracuseStep 7988017 = 5991013) B5991013
theorem B1401651 : Blo 1401520 1401651 := bstep (se 1 (by rfl) ⟨1051238, by rfl⟩ : syracuseStep 1401651 = 2102477) B2102477
theorem B1401667 : Blo 1401520 1401667 := bstep (se 1 (by rfl) ⟨1051250, by rfl⟩ : syracuseStep 1401667 = 2102501) B2102501
theorem B3154769 : Blo 1401520 3154769 := bstep (se 2 (by rfl) ⟨1183038, by rfl⟩ : syracuseStep 3154769 = 2366077) B2366077
theorem B1401683 : Blo 1401520 1401683 := bstep (se 1 (by rfl) ⟨1051262, by rfl⟩ : syracuseStep 1401683 = 2102525) B2102525
theorem B1401699 : Blo 1401520 1401699 := bstep (se 1 (by rfl) ⟨1051274, by rfl⟩ : syracuseStep 1401699 = 2102549) B2102549
theorem B3154787 : Blo 1401520 3154787 := bstep (se 1 (by rfl) ⟨2366090, by rfl⟩ : syracuseStep 3154787 = 4732181) B4732181
theorem B4735853 : Blo 1401520 4735853 := bstep (se 3 (by rfl) ⟨887972, by rfl⟩ : syracuseStep 4735853 = 1775945) B1775945
theorem B3367793 : Blo 1401520 3367793 := bstep (se 2 (by rfl) ⟨1262922, by rfl⟩ : syracuseStep 3367793 = 2525845) B2525845
theorem B1401715 : Blo 1401520 1401715 := bstep (se 1 (by rfl) ⟨1051286, by rfl⟩ : syracuseStep 1401715 = 2102573) B2102573
theorem B1401731 : Blo 1401520 1401731 := bstep (se 1 (by rfl) ⟨1051298, by rfl⟩ : syracuseStep 1401731 = 2102597) B2102597
theorem B5325709 : Blo 1401520 5325709 := bstep (se 3 (by rfl) ⟨998570, by rfl⟩ : syracuseStep 5325709 = 1997141) B1997141
theorem B1401747 : Blo 1401520 1401747 := bstep (se 1 (by rfl) ⟨1051310, by rfl⟩ : syracuseStep 1401747 = 2102621) B2102621
theorem B1401763 : Blo 1401520 1401763 := bstep (se 1 (by rfl) ⟨1051322, by rfl⟩ : syracuseStep 1401763 = 2102645) B2102645
theorem B4735907 : Blo 1401520 4735907 := bstep (se 1 (by rfl) ⟨3551930, by rfl⟩ : syracuseStep 4735907 = 7103861) B7103861
theorem B4801457 : Blo 1401520 4801457 := bstep (se 2 (by rfl) ⟨1800546, by rfl⟩ : syracuseStep 4801457 = 3601093) B3601093
theorem B2368433 : Blo 1401520 2368433 := bstep (se 2 (by rfl) ⟨888162, by rfl⟩ : syracuseStep 2368433 = 1776325) B1776325
theorem B1401779 : Blo 1401520 1401779 := bstep (se 1 (by rfl) ⟨1051334, by rfl⟩ : syracuseStep 1401779 = 2102669) B2102669
theorem B1401795 : Blo 1401520 1401795 := bstep (se 1 (by rfl) ⟨1051346, by rfl⟩ : syracuseStep 1401795 = 2102693) B2102693
theorem B2737091 : Blo 1401520 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B1401811 : Blo 1401520 1401811 := bstep (se 1 (by rfl) ⟨1051358, by rfl⟩ : syracuseStep 1401811 = 2102717) B2102717
theorem B1401827 : Blo 1401520 1401827 := bstep (se 1 (by rfl) ⟨1051370, by rfl⟩ : syracuseStep 1401827 = 2102741) B2102741
theorem B1401843 : Blo 1401520 1401843 := bstep (se 1 (by rfl) ⟨1051382, by rfl⟩ : syracuseStep 1401843 = 2102765) B2102765
theorem B2245619 : Blo 1401520 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B1401859 : Blo 1401520 1401859 := bstep (se 1 (by rfl) ⟨1051394, by rfl⟩ : syracuseStep 1401859 = 2102789) B2102789
theorem B1401875 : Blo 1401520 1401875 := bstep (se 1 (by rfl) ⟨1051406, by rfl⟩ : syracuseStep 1401875 = 2102813) B2102813
theorem B3548195 : Blo 1401520 3548195 := bstep (se 1 (by rfl) ⟨2661146, by rfl⟩ : syracuseStep 3548195 = 5322293) B5322293
theorem B1401891 : Blo 1401520 1401891 := bstep (se 1 (by rfl) ⟨1051418, by rfl⟩ : syracuseStep 1401891 = 2102837) B2102837
theorem B7103537 : Blo 1401520 7103537 := bstep (se 2 (by rfl) ⟨2663826, by rfl⟩ : syracuseStep 7103537 = 5327653) B5327653
theorem B1401907 : Blo 1401520 1401907 := bstep (se 1 (by rfl) ⟨1051430, by rfl⟩ : syracuseStep 1401907 = 2102861) B2102861
theorem B1401923 : Blo 1401520 1401923 := bstep (se 1 (by rfl) ⟨1051442, by rfl⟩ : syracuseStep 1401923 = 2102885) B2102885
theorem B1401939 : Blo 1401520 1401939 := bstep (se 1 (by rfl) ⟨1051454, by rfl⟩ : syracuseStep 1401939 = 2102909) B2102909
theorem B1401955 : Blo 1401520 1401955 := bstep (se 1 (by rfl) ⟨1051466, by rfl⟩ : syracuseStep 1401955 = 2102933) B2102933
theorem B3155057 : Blo 1401520 3155057 := bstep (se 2 (by rfl) ⟨1183146, by rfl⟩ : syracuseStep 3155057 = 2366293) B2366293
theorem B276661361 : Blo 1401520 276661361 := bstep (se 2 (by rfl) ⟨103748010, by rfl⟩ : syracuseStep 276661361 = 207496021) B207496021
theorem B1401971 : Blo 1401520 1401971 := bstep (se 1 (by rfl) ⟨1051478, by rfl⟩ : syracuseStep 1401971 = 2102957) B2102957
theorem B1401987 : Blo 1401520 1401987 := bstep (se 1 (by rfl) ⟨1051490, by rfl⟩ : syracuseStep 1401987 = 2102981) B2102981
theorem B3155075 : Blo 1401520 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B7095437 : Blo 1401520 7095437 := bstep (se 3 (by rfl) ⟨1330394, by rfl⟩ : syracuseStep 7095437 = 2660789) B2660789
theorem B1402003 : Blo 1401520 1402003 := bstep (se 1 (by rfl) ⟨1051502, by rfl⟩ : syracuseStep 1402003 = 2103005) B2103005
theorem B1402019 : Blo 1401520 1402019 := bstep (se 1 (by rfl) ⟨1051514, by rfl⟩ : syracuseStep 1402019 = 2103029) B2103029
theorem B4490417 : Blo 1401520 4490417 := bstep (se 2 (by rfl) ⟨1683906, by rfl⟩ : syracuseStep 4490417 = 3367813) B3367813
theorem B4736177 : Blo 1401520 4736177 := bstep (se 2 (by rfl) ⟨1776066, by rfl⟩ : syracuseStep 4736177 = 3552133) B3552133
theorem B1402035 : Blo 1401520 1402035 := bstep (se 1 (by rfl) ⟨1051526, by rfl⟩ : syracuseStep 1402035 = 2103053) B2103053
theorem B1402051 : Blo 1401520 1402051 := bstep (se 1 (by rfl) ⟨1051538, by rfl⟩ : syracuseStep 1402051 = 2103077) B2103077
theorem B1402067 : Blo 1401520 1402067 := bstep (se 1 (by rfl) ⟨1051550, by rfl⟩ : syracuseStep 1402067 = 2103101) B2103101
theorem B3548387 : Blo 1401520 3548387 := bstep (se 1 (by rfl) ⟨2661290, by rfl⟩ : syracuseStep 3548387 = 5322581) B5322581
theorem B1402083 : Blo 1401520 1402083 := bstep (se 1 (by rfl) ⟨1051562, by rfl⟩ : syracuseStep 1402083 = 2103125) B2103125
theorem B1402099 : Blo 1401520 1402099 := bstep (se 1 (by rfl) ⟨1051574, by rfl⟩ : syracuseStep 1402099 = 2103149) B2103149
theorem B1402115 : Blo 1401520 1402115 := bstep (se 1 (by rfl) ⟨1051586, by rfl⟩ : syracuseStep 1402115 = 2103173) B2103173
theorem B2245907 : Blo 1401520 2245907 := bstep (se 1 (by rfl) ⟨1684430, by rfl⟩ : syracuseStep 2245907 = 3368861) B3368861
theorem B1402131 : Blo 1401520 1402131 := bstep (se 1 (by rfl) ⟨1051598, by rfl⟩ : syracuseStep 1402131 = 2103197) B2103197
theorem B1402147 : Blo 1401520 1402147 := bstep (se 1 (by rfl) ⟨1051610, by rfl⟩ : syracuseStep 1402147 = 2103221) B2103221
theorem B1402163 : Blo 1401520 1402163 := bstep (se 1 (by rfl) ⟨1051622, by rfl⟩ : syracuseStep 1402163 = 2103245) B2103245
theorem B1402179 : Blo 1401520 1402179 := bstep (se 1 (by rfl) ⟨1051634, by rfl⟩ : syracuseStep 1402179 = 2103269) B2103269
theorem B5399885 : Blo 1401520 5399885 := bstep (se 3 (by rfl) ⟨1012478, by rfl⟩ : syracuseStep 5399885 = 2024957) B2024957
theorem B1402195 : Blo 1401520 1402195 := bstep (se 1 (by rfl) ⟨1051646, by rfl⟩ : syracuseStep 1402195 = 2103293) B2103293
theorem B1402211 : Blo 1401520 1402211 := bstep (se 1 (by rfl) ⟨1051658, by rfl⟩ : syracuseStep 1402211 = 2103317) B2103317
theorem B1402227 : Blo 1401520 1402227 := bstep (se 1 (by rfl) ⟨1051670, by rfl⟩ : syracuseStep 1402227 = 2103341) B2103341
theorem B1402243 : Blo 1401520 1402243 := bstep (se 1 (by rfl) ⟨1051682, by rfl⟩ : syracuseStep 1402243 = 2103365) B2103365
theorem B3155345 : Blo 1401520 3155345 := bstep (se 2 (by rfl) ⟨1183254, by rfl⟩ : syracuseStep 3155345 = 2366509) B2366509
theorem B1402259 : Blo 1401520 1402259 := bstep (se 1 (by rfl) ⟨1051694, by rfl⟩ : syracuseStep 1402259 = 2103389) B2103389
theorem B1402275 : Blo 1401520 1402275 := bstep (se 1 (by rfl) ⟨1051706, by rfl⟩ : syracuseStep 1402275 = 2103413) B2103413
theorem B3155363 : Blo 1401520 3155363 := bstep (se 1 (by rfl) ⟨2366522, by rfl⟩ : syracuseStep 3155363 = 4733045) B4733045
theorem B2663857 : Blo 1401520 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B1402291 : Blo 1401520 1402291 := bstep (se 1 (by rfl) ⟨1051718, by rfl⟩ : syracuseStep 1402291 = 2103437) B2103437
theorem B15984053 : Blo 1401520 15984053 := bstep (se 5 (by rfl) ⟨749252, by rfl⟩ : syracuseStep 15984053 = 1498505) B1498505
theorem B1402307 : Blo 1401520 1402307 := bstep (se 1 (by rfl) ⟨1051730, by rfl⟩ : syracuseStep 1402307 = 2103461) B2103461
theorem B1402323 : Blo 1401520 1402323 := bstep (se 1 (by rfl) ⟨1051742, by rfl⟩ : syracuseStep 1402323 = 2103485) B2103485
theorem B1402339 : Blo 1401520 1402339 := bstep (se 1 (by rfl) ⟨1051754, by rfl⟩ : syracuseStep 1402339 = 2103509) B2103509
theorem B1402355 : Blo 1401520 1402355 := bstep (se 1 (by rfl) ⟨1051766, by rfl⟩ : syracuseStep 1402355 = 2103533) B2103533
theorem B1402371 : Blo 1401520 1402371 := bstep (se 1 (by rfl) ⟨1051778, by rfl⟩ : syracuseStep 1402371 = 2103557) B2103557
theorem B1402387 : Blo 1401520 1402387 := bstep (se 1 (by rfl) ⟨1051790, by rfl⟩ : syracuseStep 1402387 = 2103581) B2103581
theorem B1402403 : Blo 1401520 1402403 := bstep (se 1 (by rfl) ⟨1051802, by rfl⟩ : syracuseStep 1402403 = 2103605) B2103605
theorem B7587377 : Blo 1401520 7587377 := bstep (se 2 (by rfl) ⟨2845266, by rfl⟩ : syracuseStep 7587377 = 5690533) B5690533
theorem B1402419 : Blo 1401520 1402419 := bstep (se 1 (by rfl) ⟨1051814, by rfl⟩ : syracuseStep 1402419 = 2103629) B2103629
theorem B1402435 : Blo 1401520 1402435 := bstep (se 1 (by rfl) ⟨1051826, by rfl⟩ : syracuseStep 1402435 = 2103653) B2103653
theorem B1402451 : Blo 1401520 1402451 := bstep (se 1 (by rfl) ⟨1051838, by rfl⟩ : syracuseStep 1402451 = 2103677) B2103677
theorem B3991139 : Blo 1401520 3991139 := bstep (se 1 (by rfl) ⟨2993354, by rfl⟩ : syracuseStep 3991139 = 5986709) B5986709
theorem B1402467 : Blo 1401520 1402467 := bstep (se 1 (by rfl) ⟨1051850, by rfl⟩ : syracuseStep 1402467 = 2103701) B2103701
theorem B2025059 : Blo 1401520 2025059 := bstep (se 1 (by rfl) ⟨1518794, by rfl⟩ : syracuseStep 2025059 = 3037589) B3037589
theorem B3368561 : Blo 1401520 3368561 := bstep (se 2 (by rfl) ⟨1263210, by rfl⟩ : syracuseStep 3368561 = 2526421) B2526421
theorem B1402483 : Blo 1401520 1402483 := bstep (se 1 (by rfl) ⟨1051862, by rfl⟩ : syracuseStep 1402483 = 2103725) B2103725
theorem B1402499 : Blo 1401520 1402499 := bstep (se 1 (by rfl) ⟨1051874, by rfl⟩ : syracuseStep 1402499 = 2103749) B2103749
theorem B1402515 : Blo 1401520 1402515 := bstep (se 1 (by rfl) ⟨1051886, by rfl⟩ : syracuseStep 1402515 = 2103773) B2103773
theorem B1402531 : Blo 1401520 1402531 := bstep (se 1 (by rfl) ⟨1051898, by rfl⟩ : syracuseStep 1402531 = 2103797) B2103797
theorem B5326499 : Blo 1401520 5326499 := bstep (se 1 (by rfl) ⟨3994874, by rfl⟩ : syracuseStep 5326499 = 7989749) B7989749
theorem B3155633 : Blo 1401520 3155633 := bstep (se 2 (by rfl) ⟨1183362, by rfl⟩ : syracuseStep 3155633 = 2366725) B2366725
theorem B1402547 : Blo 1401520 1402547 := bstep (se 1 (by rfl) ⟨1051910, by rfl⟩ : syracuseStep 1402547 = 2103821) B2103821
theorem B3155651 : Blo 1401520 3155651 := bstep (se 1 (by rfl) ⟨2366738, by rfl⟩ : syracuseStep 3155651 = 4733477) B4733477
theorem B1402563 : Blo 1401520 1402563 := bstep (se 1 (by rfl) ⟨1051922, by rfl⟩ : syracuseStep 1402563 = 2103845) B2103845
theorem B4736717 : Blo 1401520 4736717 := bstep (se 3 (by rfl) ⟨888134, by rfl⟩ : syracuseStep 4736717 = 1776269) B1776269
theorem B1402579 : Blo 1401520 1402579 := bstep (se 1 (by rfl) ⟨1051934, by rfl⟩ : syracuseStep 1402579 = 2103869) B2103869
theorem B1402595 : Blo 1401520 1402595 := bstep (se 1 (by rfl) ⟨1051946, by rfl⟩ : syracuseStep 1402595 = 2103893) B2103893
theorem B1402611 : Blo 1401520 1402611 := bstep (se 1 (by rfl) ⟨1051958, by rfl⟩ : syracuseStep 1402611 = 2103917) B2103917
theorem B1402627 : Blo 1401520 1402627 := bstep (se 1 (by rfl) ⟨1051970, by rfl⟩ : syracuseStep 1402627 = 2103941) B2103941
theorem B4736771 : Blo 1401520 4736771 := bstep (se 1 (by rfl) ⟨3552578, by rfl⟩ : syracuseStep 4736771 = 7105157) B7105157
theorem B1402643 : Blo 1401520 1402643 := bstep (se 1 (by rfl) ⟨1051982, by rfl⟩ : syracuseStep 1402643 = 2103965) B2103965
theorem B1402659 : Blo 1401520 1402659 := bstep (se 1 (by rfl) ⟨1051994, by rfl⟩ : syracuseStep 1402659 = 2103989) B2103989
theorem B1402675 : Blo 1401520 1402675 := bstep (se 1 (by rfl) ⟨1052006, by rfl⟩ : syracuseStep 1402675 = 2104013) B2104013
theorem B1402691 : Blo 1401520 1402691 := bstep (se 1 (by rfl) ⟨1052018, by rfl⟩ : syracuseStep 1402691 = 2104037) B2104037
theorem B1402707 : Blo 1401520 1402707 := bstep (se 1 (by rfl) ⟨1052030, by rfl⟩ : syracuseStep 1402707 = 2104061) B2104061
theorem B1402723 : Blo 1401520 1402723 := bstep (se 1 (by rfl) ⟨1052042, by rfl⟩ : syracuseStep 1402723 = 2104085) B2104085
theorem B1402739 : Blo 1401520 1402739 := bstep (se 1 (by rfl) ⟨1052054, by rfl⟩ : syracuseStep 1402739 = 2104109) B2104109
theorem B1402755 : Blo 1401520 1402755 := bstep (se 1 (by rfl) ⟨1052066, by rfl⟩ : syracuseStep 1402755 = 2104133) B2104133
theorem B1402771 : Blo 1401520 1402771 := bstep (se 1 (by rfl) ⟨1052078, by rfl⟩ : syracuseStep 1402771 = 2104157) B2104157
theorem B1402787 : Blo 1401520 1402787 := bstep (se 1 (by rfl) ⟨1052090, by rfl⟩ : syracuseStep 1402787 = 2104181) B2104181
theorem B1402803 : Blo 1401520 1402803 := bstep (se 1 (by rfl) ⟨1052102, by rfl⟩ : syracuseStep 1402803 = 2104205) B2104205
theorem B1599427 : Blo 1401520 1599427 := bstep (se 1 (by rfl) ⟨1199570, by rfl⟩ : syracuseStep 1599427 = 2399141) B2399141
theorem B1402819 : Blo 1401520 1402819 := bstep (se 1 (by rfl) ⟨1052114, by rfl⟩ : syracuseStep 1402819 = 2104229) B2104229
theorem B3155921 : Blo 1401520 3155921 := bstep (se 2 (by rfl) ⟨1183470, by rfl⟩ : syracuseStep 3155921 = 2366941) B2366941
theorem B1402835 : Blo 1401520 1402835 := bstep (se 1 (by rfl) ⟨1052126, by rfl⟩ : syracuseStep 1402835 = 2104253) B2104253
theorem B3155939 : Blo 1401520 3155939 := bstep (se 1 (by rfl) ⟨2366954, by rfl⟩ : syracuseStep 3155939 = 4733909) B4733909
theorem B1402851 : Blo 1401520 1402851 := bstep (se 1 (by rfl) ⟨1052138, by rfl⟩ : syracuseStep 1402851 = 2104277) B2104277
theorem B1402867 : Blo 1401520 1402867 := bstep (se 1 (by rfl) ⟨1052150, by rfl⟩ : syracuseStep 1402867 = 2104301) B2104301
theorem B2631683 : Blo 1401520 2631683 := bstep (se 1 (by rfl) ⟨1973762, by rfl⟩ : syracuseStep 2631683 = 3947525) B3947525
theorem B1402883 : Blo 1401520 1402883 := bstep (se 1 (by rfl) ⟨1052162, by rfl⟩ : syracuseStep 1402883 = 2104325) B2104325
theorem B10651661 : Blo 1401520 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B1402899 : Blo 1401520 1402899 := bstep (se 1 (by rfl) ⟨1052174, by rfl⟩ : syracuseStep 1402899 = 2104349) B2104349
theorem B1402915 : Blo 1401520 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B3844141 : Blo 1401520 3844141 := bstep (se 3 (by rfl) ⟨720776, by rfl⟩ : syracuseStep 3844141 = 1441553) B1441553
theorem B2246707 : Blo 1401520 2246707 := bstep (se 1 (by rfl) ⟨1685030, by rfl⟩ : syracuseStep 2246707 = 3370061) B3370061
theorem B1402931 : Blo 1401520 1402931 := bstep (se 1 (by rfl) ⟨1052198, by rfl⟩ : syracuseStep 1402931 = 2104397) B2104397
theorem B1402947 : Blo 1401520 1402947 := bstep (se 1 (by rfl) ⟨1052210, by rfl⟩ : syracuseStep 1402947 = 2104421) B2104421
theorem B1402963 : Blo 1401520 1402963 := bstep (se 1 (by rfl) ⟨1052222, by rfl⟩ : syracuseStep 1402963 = 2104445) B2104445
theorem B1402979 : Blo 1401520 1402979 := bstep (se 1 (by rfl) ⟨1052234, by rfl⟩ : syracuseStep 1402979 = 2104469) B2104469
theorem B4384867 : Blo 1401520 4384867 := bstep (se 1 (by rfl) ⟨3288650, by rfl⟩ : syracuseStep 4384867 = 6577301) B6577301
theorem B1402995 : Blo 1401520 1402995 := bstep (se 1 (by rfl) ⟨1052246, by rfl⟩ : syracuseStep 1402995 = 2104493) B2104493
theorem B1403011 : Blo 1401520 1403011 := bstep (se 1 (by rfl) ⟨1052258, by rfl⟩ : syracuseStep 1403011 = 2104517) B2104517
theorem B3549329 : Blo 1401520 3549329 := bstep (se 2 (by rfl) ⟨1330998, by rfl⟩ : syracuseStep 3549329 = 2661997) B2661997
theorem B1403027 : Blo 1401520 1403027 := bstep (se 1 (by rfl) ⟨1052270, by rfl⟩ : syracuseStep 1403027 = 2104541) B2104541
theorem B1403043 : Blo 1401520 1403043 := bstep (se 1 (by rfl) ⟨1052282, by rfl⟩ : syracuseStep 1403043 = 2104565) B2104565
theorem B1403059 : Blo 1401520 1403059 := bstep (se 1 (by rfl) ⟨1052294, by rfl⟩ : syracuseStep 1403059 = 2104589) B2104589
theorem B2246849 : Blo 1401520 2246849 := bstep (se 2 (by rfl) ⟨842568, by rfl⟩ : syracuseStep 2246849 = 1685137) B1685137
theorem B3549379 : Blo 1401520 3549379 := bstep (se 1 (by rfl) ⟨2662034, by rfl⟩ : syracuseStep 3549379 = 5324069) B5324069
theorem B1403075 : Blo 1401520 1403075 := bstep (se 1 (by rfl) ⟨1052306, by rfl⟩ : syracuseStep 1403075 = 2104613) B2104613
theorem B1403091 : Blo 1401520 1403091 := bstep (se 1 (by rfl) ⟨1052318, by rfl⟩ : syracuseStep 1403091 = 2104637) B2104637
theorem B2246881 : Blo 1401520 2246881 := bstep (se 2 (by rfl) ⟨842580, by rfl⟩ : syracuseStep 2246881 = 1685161) B1685161
theorem B7989475 : Blo 1401520 7989475 := bstep (se 1 (by rfl) ⟨5992106, by rfl⟩ : syracuseStep 7989475 = 11984213) B11984213
theorem B1403107 : Blo 1401520 1403107 := bstep (se 1 (by rfl) ⟨1052330, by rfl⟩ : syracuseStep 1403107 = 2104661) B2104661
theorem B15157489 : Blo 1401520 15157489 := bstep (se 2 (by rfl) ⟨5684058, by rfl⟩ : syracuseStep 15157489 = 11368117) B11368117
theorem B3156209 : Blo 1401520 3156209 := bstep (se 2 (by rfl) ⟨1183578, by rfl⟩ : syracuseStep 3156209 = 2367157) B2367157
theorem B1403123 : Blo 1401520 1403123 := bstep (se 1 (by rfl) ⟨1052342, by rfl⟩ : syracuseStep 1403123 = 2104685) B2104685
theorem B3156227 : Blo 1401520 3156227 := bstep (se 1 (by rfl) ⟨2367170, by rfl⟩ : syracuseStep 3156227 = 4734341) B4734341
theorem B1403139 : Blo 1401520 1403139 := bstep (se 1 (by rfl) ⟨1052354, by rfl⟩ : syracuseStep 1403139 = 2104709) B2104709
theorem B1403155 : Blo 1401520 1403155 := bstep (se 1 (by rfl) ⟨1052366, by rfl⟩ : syracuseStep 1403155 = 2104733) B2104733
theorem B1403171 : Blo 1401520 1403171 := bstep (se 1 (by rfl) ⟨1052378, by rfl⟩ : syracuseStep 1403171 = 2104757) B2104757
theorem B5327153 : Blo 1401520 5327153 := bstep (se 2 (by rfl) ⟨1997682, by rfl⟩ : syracuseStep 5327153 = 3995365) B3995365
theorem B1403187 : Blo 1401520 1403187 := bstep (se 1 (by rfl) ⟨1052390, by rfl⟩ : syracuseStep 1403187 = 2104781) B2104781
theorem B1403203 : Blo 1401520 1403203 := bstep (se 1 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 1403203 = 2104805) B2104805
theorem B3549521 : Blo 1401520 3549521 := bstep (se 2 (by rfl) ⟨1331070, by rfl⟩ : syracuseStep 3549521 = 2662141) B2662141
theorem B1403219 : Blo 1401520 1403219 := bstep (se 1 (by rfl) ⟨1052414, by rfl⟩ : syracuseStep 1403219 = 2104829) B2104829
theorem B1403235 : Blo 1401520 1403235 := bstep (se 1 (by rfl) ⟨1052426, by rfl⟩ : syracuseStep 1403235 = 2104853) B2104853
theorem B1403251 : Blo 1401520 1403251 := bstep (se 1 (by rfl) ⟨1052438, by rfl⟩ : syracuseStep 1403251 = 2104877) B2104877
theorem B1403267 : Blo 1401520 1403267 := bstep (se 1 (by rfl) ⟨1052450, by rfl⟩ : syracuseStep 1403267 = 2104901) B2104901
theorem B1403283 : Blo 1401520 1403283 := bstep (se 1 (by rfl) ⟨1052462, by rfl⟩ : syracuseStep 1403283 = 2104925) B2104925
theorem B1403299 : Blo 1401520 1403299 := bstep (se 1 (by rfl) ⟨1052474, by rfl⟩ : syracuseStep 1403299 = 2104949) B2104949
theorem B1403315 : Blo 1401520 1403315 := bstep (se 1 (by rfl) ⟨1052486, by rfl⟩ : syracuseStep 1403315 = 2104973) B2104973
theorem B1403331 : Blo 1401520 1403331 := bstep (se 1 (by rfl) ⟨1052498, by rfl⟩ : syracuseStep 1403331 = 2104997) B2104997
theorem B5990861 : Blo 1401520 5990861 := bstep (se 3 (by rfl) ⟨1123286, by rfl⟩ : syracuseStep 5990861 = 2246573) B2246573
theorem B1599955 : Blo 1401520 1599955 := bstep (se 1 (by rfl) ⟨1199966, by rfl⟩ : syracuseStep 1599955 = 2399933) B2399933
theorem B1403347 : Blo 1401520 1403347 := bstep (se 1 (by rfl) ⟨1052510, by rfl⟩ : syracuseStep 1403347 = 2105021) B2105021
theorem B6736355 : Blo 1401520 6736355 := bstep (se 1 (by rfl) ⟨5052266, by rfl⟩ : syracuseStep 6736355 = 10104533) B10104533
theorem B1403363 : Blo 1401520 1403363 := bstep (se 1 (by rfl) ⟨1052522, by rfl⟩ : syracuseStep 1403363 = 2105045) B2105045
theorem B7104995 : Blo 1401520 7104995 := bstep (se 1 (by rfl) ⟨5328746, by rfl⟩ : syracuseStep 7104995 = 10657493) B10657493
theorem B1403379 : Blo 1401520 1403379 := bstep (se 1 (by rfl) ⟨1052534, by rfl⟩ : syracuseStep 1403379 = 2105069) B2105069
theorem B1403395 : Blo 1401520 1403395 := bstep (se 1 (by rfl) ⟨1052546, by rfl⟩ : syracuseStep 1403395 = 2105093) B2105093
theorem B3156497 : Blo 1401520 3156497 := bstep (se 2 (by rfl) ⟨1183686, by rfl⟩ : syracuseStep 3156497 = 2367373) B2367373
theorem B1403411 : Blo 1401520 1403411 := bstep (se 1 (by rfl) ⟨1052558, by rfl⟩ : syracuseStep 1403411 = 2105117) B2105117
theorem B3156515 : Blo 1401520 3156515 := bstep (se 1 (by rfl) ⟨2367386, by rfl⟩ : syracuseStep 3156515 = 4734773) B4734773
theorem B1403427 : Blo 1401520 1403427 := bstep (se 1 (by rfl) ⟨1052570, by rfl⟩ : syracuseStep 1403427 = 2105141) B2105141
theorem B1403443 : Blo 1401520 1403443 := bstep (se 1 (by rfl) ⟨1052582, by rfl⟩ : syracuseStep 1403443 = 2105165) B2105165
theorem B1403459 : Blo 1401520 1403459 := bstep (se 1 (by rfl) ⟨1052594, by rfl⟩ : syracuseStep 1403459 = 2105189) B2105189
theorem B3992141 : Blo 1401520 3992141 := bstep (se 3 (by rfl) ⟨748526, by rfl⟩ : syracuseStep 3992141 = 1497053) B1497053
theorem B1403475 : Blo 1401520 1403475 := bstep (se 1 (by rfl) ⟨1052606, by rfl⟩ : syracuseStep 1403475 = 2105213) B2105213
theorem B1403491 : Blo 1401520 1403491 := bstep (se 1 (by rfl) ⟨1052618, by rfl⟩ : syracuseStep 1403491 = 2105237) B2105237
theorem B1895027 : Blo 1401520 1895027 := bstep (se 1 (by rfl) ⟨1421270, by rfl⟩ : syracuseStep 1895027 = 2842541) B2842541
theorem B1403507 : Blo 1401520 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B8981189 : Blo 1401520 8981189 := bstep (se 4 (by rfl) ⟨841986, by rfl⟩ : syracuseStep 8981189 = 1683973) B1683973
theorem B7990001 : Blo 1401520 7990001 := bstep (se 2 (by rfl) ⟨2996250, by rfl⟩ : syracuseStep 7990001 = 5992501) B5992501
theorem B3992323 : Blo 1401520 3992323 := bstep (se 1 (by rfl) ⟨2994242, by rfl⟩ : syracuseStep 3992323 = 5988485) B5988485
theorem B3156785 : Blo 1401520 3156785 := bstep (se 2 (by rfl) ⟨1183794, by rfl⟩ : syracuseStep 3156785 = 2367589) B2367589
theorem B3156803 : Blo 1401520 3156803 := bstep (se 1 (by rfl) ⟨2367602, by rfl⟩ : syracuseStep 3156803 = 4735205) B4735205
theorem B3992483 : Blo 1401520 3992483 := bstep (se 1 (by rfl) ⟨2994362, by rfl⟩ : syracuseStep 3992483 = 5988725) B5988725
theorem B3157073 : Blo 1401520 3157073 := bstep (se 2 (by rfl) ⟨1183902, by rfl⟩ : syracuseStep 3157073 = 2367805) B2367805
theorem B3157091 : Blo 1401520 3157091 := bstep (se 1 (by rfl) ⟨2367818, by rfl⟩ : syracuseStep 3157091 = 4735637) B4735637
theorem B3697777 : Blo 1401520 3697777 := bstep (se 2 (by rfl) ⟨1386666, by rfl⟩ : syracuseStep 3697777 = 2773333) B2773333
theorem B2247809 : Blo 1401520 2247809 := bstep (se 2 (by rfl) ⟨842928, by rfl⟩ : syracuseStep 2247809 = 1685857) B1685857
theorem B4492493 : Blo 1401520 4492493 := bstep (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) B1684685
theorem B4050157 : Blo 1401520 4050157 := bstep (se 3 (by rfl) ⟨759404, by rfl⟩ : syracuseStep 4050157 = 1518809) B1518809
theorem B3550513 : Blo 1401520 3550513 := bstep (se 2 (by rfl) ⟨1331442, by rfl⟩ : syracuseStep 3550513 = 2662885) B2662885
theorem B3157361 : Blo 1401520 3157361 := bstep (se 2 (by rfl) ⟨1184010, by rfl⟩ : syracuseStep 3157361 = 2368021) B2368021
theorem B3157379 : Blo 1401520 3157379 := bstep (se 1 (by rfl) ⟨2368034, by rfl⟩ : syracuseStep 3157379 = 4736069) B4736069
theorem B3550787 : Blo 1401520 3550787 := bstep (se 1 (by rfl) ⟨2663090, by rfl⟩ : syracuseStep 3550787 = 5326181) B5326181
theorem B5394061 : Blo 1401520 5394061 := bstep (se 3 (by rfl) ⟨1011386, by rfl⟩ : syracuseStep 5394061 = 2022773) B2022773
theorem B3157649 : Blo 1401520 3157649 := bstep (se 2 (by rfl) ⟨1184118, by rfl⟩ : syracuseStep 3157649 = 2368237) B2368237
theorem B3157667 : Blo 1401520 3157667 := bstep (se 1 (by rfl) ⟨2368250, by rfl⟩ : syracuseStep 3157667 = 4736501) B4736501
theorem B5328611 : Blo 1401520 5328611 := bstep (se 1 (by rfl) ⟨3996458, by rfl⟩ : syracuseStep 5328611 = 7992917) B7992917
theorem B5328625 : Blo 1401520 5328625 := bstep (se 2 (by rfl) ⟨1998234, by rfl⟩ : syracuseStep 5328625 = 3996469) B3996469
theorem B3550979 : Blo 1401520 3550979 := bstep (se 1 (by rfl) ⟨2663234, by rfl⟩ : syracuseStep 3550979 = 5326469) B5326469
theorem B1576723 : Blo 1401520 1576723 := bstep (se 1 (by rfl) ⟨1182542, by rfl⟩ : syracuseStep 1576723 = 2365085) B2365085
theorem B4730669 : Blo 1401520 4730669 := bstep (se 3 (by rfl) ⟨887000, by rfl⟩ : syracuseStep 4730669 = 1774001) B1774001
theorem B4263725 : Blo 1401520 4263725 := bstep (se 3 (by rfl) ⟨799448, by rfl⟩ : syracuseStep 4263725 = 1598897) B1598897
theorem B2993969 : Blo 1401520 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B4050769 : Blo 1401520 4050769 := bstep (se 2 (by rfl) ⟨1519038, by rfl⟩ : syracuseStep 4050769 = 3038077) B3038077
theorem B4730723 : Blo 1401520 4730723 := bstep (se 1 (by rfl) ⟨3548042, by rfl⟩ : syracuseStep 4730723 = 7096085) B7096085
theorem B1576867 : Blo 1401520 1576867 := bstep (se 1 (by rfl) ⟨1182650, by rfl⟩ : syracuseStep 1576867 = 2365301) B2365301
theorem B3993553 : Blo 1401520 3993553 := bstep (se 2 (by rfl) ⟨1497582, by rfl⟩ : syracuseStep 3993553 = 2995165) B2995165
theorem B7098353 : Blo 1401520 7098353 := bstep (se 2 (by rfl) ⟨2661882, by rfl⟩ : syracuseStep 7098353 = 5323765) B5323765
theorem B12144653 : Blo 1401520 12144653 := bstep (se 3 (by rfl) ⟨2277122, by rfl⟩ : syracuseStep 12144653 = 4554245) B4554245
theorem B5689379 : Blo 1401520 5689379 := bstep (se 1 (by rfl) ⟨4267034, by rfl⟩ : syracuseStep 5689379 = 8534069) B8534069
theorem B1577011 : Blo 1401520 1577011 := bstep (se 1 (by rfl) ⟨1182758, by rfl⟩ : syracuseStep 1577011 = 2365517) B2365517
theorem B4493389 : Blo 1401520 4493389 := bstep (se 3 (by rfl) ⟨842510, by rfl⟩ : syracuseStep 4493389 = 1685021) B1685021
theorem B4730993 : Blo 1401520 4730993 := bstep (se 2 (by rfl) ⟨1774122, by rfl⟩ : syracuseStep 4730993 = 3548245) B3548245
theorem B17961101 : Blo 1401520 17961101 := bstep (se 3 (by rfl) ⟨3367706, by rfl⟩ : syracuseStep 17961101 = 6735413) B6735413
theorem B7991459 : Blo 1401520 7991459 := bstep (se 1 (by rfl) ⟨5993594, by rfl⟩ : syracuseStep 7991459 = 11987189) B11987189
theorem B1577155 : Blo 1401520 1577155 := bstep (se 1 (by rfl) ⟨1182866, by rfl⟩ : syracuseStep 1577155 = 2365733) B2365733
theorem B2994499 : Blo 1401520 2994499 := bstep (se 1 (by rfl) ⟨2245874, by rfl⟩ : syracuseStep 2994499 = 4491749) B4491749
theorem B10645829 : Blo 1401520 10645829 := bstep (se 4 (by rfl) ⟨998046, by rfl⟩ : syracuseStep 10645829 = 1996093) B1996093
theorem B1577299 : Blo 1401520 1577299 := bstep (se 1 (by rfl) ⟨1182974, by rfl⟩ : syracuseStep 1577299 = 2365949) B2365949
theorem B6738353 : Blo 1401520 6738353 := bstep (se 2 (by rfl) ⟨2526882, by rfl⟩ : syracuseStep 6738353 = 5053765) B5053765
theorem B1577443 : Blo 1401520 1577443 := bstep (se 1 (by rfl) ⟨1183082, by rfl⟩ : syracuseStep 1577443 = 2366165) B2366165
theorem B4796941 : Blo 1401520 4796941 := bstep (se 3 (by rfl) ⟨899426, by rfl⟩ : syracuseStep 4796941 = 1798853) B1798853
theorem B1421875 : Blo 1401520 1421875 := bstep (se 1 (by rfl) ⟨1066406, by rfl⟩ : syracuseStep 1421875 = 2132813) B2132813
theorem B1774163 : Blo 1401520 1774163 := bstep (se 1 (by rfl) ⟨1330622, by rfl⟩ : syracuseStep 1774163 = 2661245) B2661245
theorem B1577587 : Blo 1401520 1577587 := bstep (se 1 (by rfl) ⟨1183190, by rfl⟩ : syracuseStep 1577587 = 2366381) B2366381
theorem B4731533 : Blo 1401520 4731533 := bstep (se 3 (by rfl) ⟨887162, by rfl⟩ : syracuseStep 4731533 = 1774325) B1774325
theorem B23368333 : Blo 1401520 23368333 := bstep (se 3 (by rfl) ⟨4381562, by rfl⟩ : syracuseStep 23368333 = 8763125) B8763125
theorem B3551921 : Blo 1401520 3551921 := bstep (se 2 (by rfl) ⟨1331970, by rfl⟩ : syracuseStep 3551921 = 2663941) B2663941
theorem B4731587 : Blo 1401520 4731587 := bstep (se 1 (by rfl) ⟨3548690, by rfl⟩ : syracuseStep 4731587 = 7097381) B7097381
theorem B3551971 : Blo 1401520 3551971 := bstep (se 1 (by rfl) ⟨2663978, by rfl⟩ : syracuseStep 3551971 = 5327957) B5327957
theorem B1577731 : Blo 1401520 1577731 := bstep (se 1 (by rfl) ⟨1183298, by rfl⟩ : syracuseStep 1577731 = 2366597) B2366597
theorem B10654577 : Blo 1401520 10654577 := bstep (se 2 (by rfl) ⟨3995466, by rfl⟩ : syracuseStep 10654577 = 7990933) B7990933
theorem B3552113 : Blo 1401520 3552113 := bstep (se 2 (by rfl) ⟨1332042, by rfl⟩ : syracuseStep 3552113 = 2664085) B2664085
theorem B1577875 : Blo 1401520 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B1995683 : Blo 1401520 1995683 := bstep (se 1 (by rfl) ⟨1496762, by rfl⟩ : syracuseStep 1995683 = 2993525) B2993525
theorem B4797347 : Blo 1401520 4797347 := bstep (se 1 (by rfl) ⟨3598010, by rfl⟩ : syracuseStep 4797347 = 7196021) B7196021
theorem B4494275 : Blo 1401520 4494275 := bstep (se 1 (by rfl) ⟨3370706, by rfl⟩ : syracuseStep 4494275 = 6741413) B6741413
theorem B4731857 : Blo 1401520 4731857 := bstep (se 2 (by rfl) ⟨1774446, by rfl⟩ : syracuseStep 4731857 = 3548893) B3548893
theorem B8991749 : Blo 1401520 8991749 := bstep (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) B1685953
theorem B2307089 : Blo 1401520 2307089 := bstep (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) B1730317
theorem B2102291 : Blo 1401520 2102291 := bstep (se 1 (by rfl) ⟨1576718, by rfl⟩ : syracuseStep 2102291 = 3153437) B3153437
theorem B1578019 : Blo 1401520 1578019 := bstep (se 1 (by rfl) ⟨1183514, by rfl⟩ : syracuseStep 1578019 = 2367029) B2367029
theorem B2102321 : Blo 1401520 2102321 := bstep (se 2 (by rfl) ⟨788370, by rfl⟩ : syracuseStep 2102321 = 1576741) B1576741
theorem B2102339 : Blo 1401520 2102339 := bstep (se 1 (by rfl) ⟨1576754, by rfl⟩ : syracuseStep 2102339 = 3153509) B3153509
theorem B2102369 : Blo 1401520 2102369 := bstep (se 2 (by rfl) ⟨788388, by rfl⟩ : syracuseStep 2102369 = 1576777) B1576777
theorem B9589859 : Blo 1401520 9589859 := bstep (se 1 (by rfl) ⟨7192394, by rfl⟩ : syracuseStep 9589859 = 14384789) B14384789
theorem B2102387 : Blo 1401520 2102387 := bstep (se 1 (by rfl) ⟨1576790, by rfl⟩ : syracuseStep 2102387 = 3153581) B3153581
theorem B2102417 : Blo 1401520 2102417 := bstep (se 2 (by rfl) ⟨788406, by rfl⟩ : syracuseStep 2102417 = 1576813) B1576813
theorem B2102435 : Blo 1401520 2102435 := bstep (se 1 (by rfl) ⟨1576826, by rfl⟩ : syracuseStep 2102435 = 3153653) B3153653
theorem B1578163 : Blo 1401520 1578163 := bstep (se 1 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 1578163 = 2367245) B2367245
theorem B2102465 : Blo 1401520 2102465 := bstep (se 2 (by rfl) ⟨788424, by rfl⟩ : syracuseStep 2102465 = 1576849) B1576849
theorem B3994829 : Blo 1401520 3994829 := bstep (se 3 (by rfl) ⟨749030, by rfl⟩ : syracuseStep 3994829 = 1498061) B1498061
theorem B2102483 : Blo 1401520 2102483 := bstep (se 1 (by rfl) ⟨1576862, by rfl⟩ : syracuseStep 2102483 = 3153725) B3153725
theorem B3462371 : Blo 1401520 3462371 := bstep (se 1 (by rfl) ⟨2596778, by rfl⟩ : syracuseStep 3462371 = 5193557) B5193557
theorem B2102513 : Blo 1401520 2102513 := bstep (se 2 (by rfl) ⟨788442, by rfl⟩ : syracuseStep 2102513 = 1576885) B1576885
theorem B2528497 : Blo 1401520 2528497 := bstep (se 2 (by rfl) ⟨948186, by rfl⟩ : syracuseStep 2528497 = 1896373) B1896373
theorem B1684723 : Blo 1401520 1684723 := bstep (se 1 (by rfl) ⟨1263542, by rfl⟩ : syracuseStep 1684723 = 2527085) B2527085
theorem B2102531 : Blo 1401520 2102531 := bstep (se 1 (by rfl) ⟨1576898, by rfl⟩ : syracuseStep 2102531 = 3153797) B3153797
theorem B1774867 : Blo 1401520 1774867 := bstep (se 1 (by rfl) ⟨1331150, by rfl⟩ : syracuseStep 1774867 = 2662301) B2662301
theorem B2102561 : Blo 1401520 2102561 := bstep (se 2 (by rfl) ⟨788460, by rfl⟩ : syracuseStep 2102561 = 1576921) B1576921
theorem B2102579 : Blo 1401520 2102579 := bstep (se 1 (by rfl) ⟨1576934, by rfl⟩ : syracuseStep 2102579 = 3153869) B3153869
theorem B1578307 : Blo 1401520 1578307 := bstep (se 1 (by rfl) ⟨1183730, by rfl⟩ : syracuseStep 1578307 = 2367461) B2367461
theorem B2102609 : Blo 1401520 2102609 := bstep (se 2 (by rfl) ⟨788478, by rfl⟩ : syracuseStep 2102609 = 1576957) B1576957
theorem B2102627 : Blo 1401520 2102627 := bstep (se 1 (by rfl) ⟨1576970, by rfl⟩ : syracuseStep 2102627 = 3153941) B3153941
theorem B1774963 : Blo 1401520 1774963 := bstep (se 1 (by rfl) ⟨1331222, by rfl⟩ : syracuseStep 1774963 = 2662445) B2662445
theorem B2102657 : Blo 1401520 2102657 := bstep (se 2 (by rfl) ⟨788496, by rfl⟩ : syracuseStep 2102657 = 1576993) B1576993
theorem B3995011 : Blo 1401520 3995011 := bstep (se 1 (by rfl) ⟨2996258, by rfl⟩ : syracuseStep 3995011 = 5992517) B5992517
theorem B5322125 : Blo 1401520 5322125 := bstep (se 3 (by rfl) ⟨997898, by rfl⟩ : syracuseStep 5322125 = 1995797) B1995797
theorem B2102675 : Blo 1401520 2102675 := bstep (se 1 (by rfl) ⟨1577006, by rfl⟩ : syracuseStep 2102675 = 3154013) B3154013
theorem B7099811 : Blo 1401520 7099811 := bstep (se 1 (by rfl) ⟨5324858, by rfl⟩ : syracuseStep 7099811 = 10649717) B10649717
theorem B2102705 : Blo 1401520 2102705 := bstep (se 2 (by rfl) ⟨788514, by rfl⟩ : syracuseStep 2102705 = 1577029) B1577029
theorem B3995057 : Blo 1401520 3995057 := bstep (se 2 (by rfl) ⟨1498146, by rfl⟩ : syracuseStep 3995057 = 2996293) B2996293
theorem B2102723 : Blo 1401520 2102723 := bstep (se 1 (by rfl) ⟨1577042, by rfl⟩ : syracuseStep 2102723 = 3154085) B3154085
theorem B1578451 : Blo 1401520 1578451 := bstep (se 1 (by rfl) ⟨1183838, by rfl⟩ : syracuseStep 1578451 = 2367677) B2367677
theorem B2102753 : Blo 1401520 2102753 := bstep (se 2 (by rfl) ⟨788532, by rfl⟩ : syracuseStep 2102753 = 1577065) B1577065
theorem B4732397 : Blo 1401520 4732397 := bstep (se 3 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 4732397 = 1774649) B1774649
theorem B2102771 : Blo 1401520 2102771 := bstep (se 1 (by rfl) ⟨1577078, by rfl⟩ : syracuseStep 2102771 = 3154157) B3154157
theorem B6739469 : Blo 1401520 6739469 := bstep (se 3 (by rfl) ⟨1263650, by rfl⟩ : syracuseStep 6739469 = 2527301) B2527301
theorem B2102801 : Blo 1401520 2102801 := bstep (se 2 (by rfl) ⟨788550, by rfl⟩ : syracuseStep 2102801 = 1577101) B1577101
theorem B1996321 : Blo 1401520 1996321 := bstep (se 2 (by rfl) ⟨748620, by rfl⟩ : syracuseStep 1996321 = 1497241) B1497241
theorem B2102819 : Blo 1401520 2102819 := bstep (se 1 (by rfl) ⟨1577114, by rfl⟩ : syracuseStep 2102819 = 3154229) B3154229
theorem B4732451 : Blo 1401520 4732451 := bstep (se 1 (by rfl) ⟨3549338, by rfl⟩ : syracuseStep 4732451 = 7098677) B7098677
theorem B2102849 : Blo 1401520 2102849 := bstep (se 2 (by rfl) ⟨788568, by rfl⟩ : syracuseStep 2102849 = 1577137) B1577137
theorem B2102867 : Blo 1401520 2102867 := bstep (se 1 (by rfl) ⟨1577150, by rfl⟩ : syracuseStep 2102867 = 3154301) B3154301
theorem B1578595 : Blo 1401520 1578595 := bstep (se 1 (by rfl) ⟨1183946, by rfl⟩ : syracuseStep 1578595 = 2367893) B2367893
theorem B2102897 : Blo 1401520 2102897 := bstep (se 2 (by rfl) ⟨788586, by rfl⟩ : syracuseStep 2102897 = 1577173) B1577173
theorem B2102915 : Blo 1401520 2102915 := bstep (se 1 (by rfl) ⟨1577186, by rfl⟩ : syracuseStep 2102915 = 3154373) B3154373
theorem B1996435 : Blo 1401520 1996435 := bstep (se 1 (by rfl) ⟨1497326, by rfl⟩ : syracuseStep 1996435 = 2994653) B2994653
theorem B1799827 : Blo 1401520 1799827 := bstep (se 1 (by rfl) ⟨1349870, by rfl⟩ : syracuseStep 1799827 = 2699741) B2699741
theorem B2102945 : Blo 1401520 2102945 := bstep (se 2 (by rfl) ⟨788604, by rfl⟩ : syracuseStep 2102945 = 1577209) B1577209
theorem B2365105 : Blo 1401520 2365105 := bstep (se 2 (by rfl) ⟨886914, by rfl⟩ : syracuseStep 2365105 = 1773829) B1773829
theorem B2102963 : Blo 1401520 2102963 := bstep (se 1 (by rfl) ⟨1577222, by rfl⟩ : syracuseStep 2102963 = 3154445) B3154445
theorem B2102993 : Blo 1401520 2102993 := bstep (se 2 (by rfl) ⟨788622, by rfl⟩ : syracuseStep 2102993 = 1577245) B1577245
theorem B2365139 : Blo 1401520 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B2103011 : Blo 1401520 2103011 := bstep (se 1 (by rfl) ⟨1577258, by rfl⟩ : syracuseStep 2103011 = 3154517) B3154517
theorem B1578739 : Blo 1401520 1578739 := bstep (se 1 (by rfl) ⟨1184054, by rfl⟩ : syracuseStep 1578739 = 2368109) B2368109
theorem B2103041 : Blo 1401520 2103041 := bstep (se 2 (by rfl) ⟨788640, by rfl⟩ : syracuseStep 2103041 = 1577281) B1577281
theorem B2995985 : Blo 1401520 2995985 := bstep (se 2 (by rfl) ⟨1123494, by rfl⟩ : syracuseStep 2995985 = 2246989) B2246989
theorem B2103059 : Blo 1401520 2103059 := bstep (se 1 (by rfl) ⟨1577294, by rfl⟩ : syracuseStep 2103059 = 3154589) B3154589
theorem B2996003 : Blo 1401520 2996003 := bstep (se 1 (by rfl) ⟨2247002, by rfl⟩ : syracuseStep 2996003 = 4494005) B4494005
theorem B2103089 : Blo 1401520 2103089 := bstep (se 2 (by rfl) ⟨788658, by rfl⟩ : syracuseStep 2103089 = 1577317) B1577317
theorem B4732721 : Blo 1401520 4732721 := bstep (se 2 (by rfl) ⟨1774770, by rfl⟩ : syracuseStep 4732721 = 3549541) B3549541
theorem B1496899 : Blo 1401520 1496899 := bstep (se 1 (by rfl) ⟨1122674, by rfl⟩ : syracuseStep 1496899 = 2245349) B2245349
theorem B2103107 : Blo 1401520 2103107 := bstep (se 1 (by rfl) ⟨1577330, by rfl⟩ : syracuseStep 2103107 = 3154661) B3154661
theorem B2365267 : Blo 1401520 2365267 := bstep (se 1 (by rfl) ⟨1773950, by rfl⟩ : syracuseStep 2365267 = 3547901) B3547901
theorem B2103137 : Blo 1401520 2103137 := bstep (se 2 (by rfl) ⟨788676, by rfl⟩ : syracuseStep 2103137 = 1577353) B1577353
theorem B1775459 : Blo 1401520 1775459 := bstep (se 1 (by rfl) ⟨1331594, by rfl⟩ : syracuseStep 1775459 = 2663189) B2663189
theorem B4323181 : Blo 1401520 4323181 := bstep (se 3 (by rfl) ⟨810596, by rfl⟩ : syracuseStep 4323181 = 1621193) B1621193
theorem B2103155 : Blo 1401520 2103155 := bstep (se 1 (by rfl) ⟨1577366, by rfl⟩ : syracuseStep 2103155 = 3154733) B3154733
theorem B1578883 : Blo 1401520 1578883 := bstep (se 1 (by rfl) ⟨1184162, by rfl⟩ : syracuseStep 1578883 = 2368325) B2368325
theorem B2103185 : Blo 1401520 2103185 := bstep (se 2 (by rfl) ⟨788694, by rfl⟩ : syracuseStep 2103185 = 1577389) B1577389
theorem B2103203 : Blo 1401520 2103203 := bstep (se 1 (by rfl) ⟨1577402, by rfl⟩ : syracuseStep 2103203 = 3154805) B3154805
theorem B2103233 : Blo 1401520 2103233 := bstep (se 2 (by rfl) ⟨788712, by rfl⟩ : syracuseStep 2103233 = 1577425) B1577425
theorem B7985101 : Blo 1401520 7985101 := bstep (se 3 (by rfl) ⟨1497206, by rfl⟩ : syracuseStep 7985101 = 2994413) B2994413
theorem B2103251 : Blo 1401520 2103251 := bstep (se 1 (by rfl) ⟨1577438, by rfl⟩ : syracuseStep 2103251 = 3154877) B3154877
theorem B2365409 : Blo 1401520 2365409 := bstep (se 2 (by rfl) ⟨887028, by rfl⟩ : syracuseStep 2365409 = 1774057) B1774057
theorem B2398177 : Blo 1401520 2398177 := bstep (se 2 (by rfl) ⟨899316, by rfl⟩ : syracuseStep 2398177 = 1798633) B1798633
theorem B35928035 : Blo 1401520 35928035 := bstep (se 1 (by rfl) ⟨26946026, by rfl⟩ : syracuseStep 35928035 = 53892053) B53892053
theorem B2103281 : Blo 1401520 2103281 := bstep (se 2 (by rfl) ⟨788730, by rfl⟩ : syracuseStep 2103281 = 1577461) B1577461
theorem B2103299 : Blo 1401520 2103299 := bstep (se 1 (by rfl) ⟨1577474, by rfl⟩ : syracuseStep 2103299 = 3154949) B3154949
theorem B7993349 : Blo 1401520 7993349 := bstep (se 4 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 7993349 = 1498753) B1498753
theorem B2103329 : Blo 1401520 2103329 := bstep (se 2 (by rfl) ⟨788748, by rfl⟩ : syracuseStep 2103329 = 1577497) B1577497
theorem B2103347 : Blo 1401520 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B2103377 : Blo 1401520 2103377 := bstep (se 2 (by rfl) ⟨788766, by rfl⟩ : syracuseStep 2103377 = 1577533) B1577533
theorem B2365537 : Blo 1401520 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B2103395 : Blo 1401520 2103395 := bstep (se 1 (by rfl) ⟨1577546, by rfl⟩ : syracuseStep 2103395 = 3155093) B3155093
theorem B8984675 : Blo 1401520 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B5683313 : Blo 1401520 5683313 := bstep (se 2 (by rfl) ⟨2131242, by rfl⟩ : syracuseStep 5683313 = 4262485) B4262485
theorem B2103425 : Blo 1401520 2103425 := bstep (se 2 (by rfl) ⟨788784, by rfl⟩ : syracuseStep 2103425 = 1577569) B1577569
theorem B2365571 : Blo 1401520 2365571 := bstep (se 1 (by rfl) ⟨1774178, by rfl⟩ : syracuseStep 2365571 = 3548357) B3548357
theorem B2103443 : Blo 1401520 2103443 := bstep (se 1 (by rfl) ⟨1577582, by rfl⟩ : syracuseStep 2103443 = 3155165) B3155165
theorem B2103473 : Blo 1401520 2103473 := bstep (se 2 (by rfl) ⟨788802, by rfl⟩ : syracuseStep 2103473 = 1577605) B1577605
theorem B2103491 : Blo 1401520 2103491 := bstep (se 1 (by rfl) ⟨1577618, by rfl⟩ : syracuseStep 2103491 = 3155237) B3155237
theorem B7100621 : Blo 1401520 7100621 := bstep (se 3 (by rfl) ⟨1331366, by rfl⟩ : syracuseStep 7100621 = 2662733) B2662733
theorem B2103521 : Blo 1401520 2103521 := bstep (se 2 (by rfl) ⟨788820, by rfl⟩ : syracuseStep 2103521 = 1577641) B1577641
theorem B8526065 : Blo 1401520 8526065 := bstep (se 2 (by rfl) ⟨3197274, by rfl⟩ : syracuseStep 8526065 = 6394549) B6394549
theorem B2103539 : Blo 1401520 2103539 := bstep (se 1 (by rfl) ⟨1577654, by rfl⟩ : syracuseStep 2103539 = 3155309) B3155309
theorem B2365699 : Blo 1401520 2365699 := bstep (se 1 (by rfl) ⟨1774274, by rfl⟩ : syracuseStep 2365699 = 3548549) B3548549
theorem B2103569 : Blo 1401520 2103569 := bstep (se 2 (by rfl) ⟨788838, by rfl⟩ : syracuseStep 2103569 = 1577677) B1577677
theorem B2103587 : Blo 1401520 2103587 := bstep (se 1 (by rfl) ⟨1577690, by rfl⟩ : syracuseStep 2103587 = 3155381) B3155381
theorem B2103617 : Blo 1401520 2103617 := bstep (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) B1577713
theorem B4733261 : Blo 1401520 4733261 := bstep (se 3 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 4733261 = 1774973) B1774973
theorem B2103635 : Blo 1401520 2103635 := bstep (se 1 (by rfl) ⟨1577726, by rfl⟩ : syracuseStep 2103635 = 3155453) B3155453
theorem B2103665 : Blo 1401520 2103665 := bstep (se 2 (by rfl) ⟨788874, by rfl⟩ : syracuseStep 2103665 = 1577749) B1577749
theorem B2103683 : Blo 1401520 2103683 := bstep (se 1 (by rfl) ⟨1577762, by rfl⟩ : syracuseStep 2103683 = 3155525) B3155525
theorem B4733315 : Blo 1401520 4733315 := bstep (se 1 (by rfl) ⟨3549986, by rfl⟩ : syracuseStep 4733315 = 7099973) B7099973
theorem B2365841 : Blo 1401520 2365841 := bstep (se 2 (by rfl) ⟨887190, by rfl⟩ : syracuseStep 2365841 = 1774381) B1774381
theorem B2103713 : Blo 1401520 2103713 := bstep (se 2 (by rfl) ⟨788892, by rfl⟩ : syracuseStep 2103713 = 1577785) B1577785
theorem B1497523 : Blo 1401520 1497523 := bstep (se 1 (by rfl) ⟨1123142, by rfl⟩ : syracuseStep 1497523 = 2246285) B2246285
theorem B2103731 : Blo 1401520 2103731 := bstep (se 1 (by rfl) ⟨1577798, by rfl⟩ : syracuseStep 2103731 = 3155597) B3155597
theorem B2103761 : Blo 1401520 2103761 := bstep (se 2 (by rfl) ⟨788910, by rfl⟩ : syracuseStep 2103761 = 1577821) B1577821
theorem B2103779 : Blo 1401520 2103779 := bstep (se 1 (by rfl) ⟨1577834, by rfl⟩ : syracuseStep 2103779 = 3155669) B3155669
theorem B2103809 : Blo 1401520 2103809 := bstep (se 2 (by rfl) ⟨788928, by rfl⟩ : syracuseStep 2103809 = 1577857) B1577857
theorem B8886797 : Blo 1401520 8886797 := bstep (se 3 (by rfl) ⟨1666274, by rfl⟩ : syracuseStep 8886797 = 3332549) B3332549
theorem B2365969 : Blo 1401520 2365969 := bstep (se 2 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 2365969 = 1774477) B1774477
theorem B2103827 : Blo 1401520 2103827 := bstep (se 1 (by rfl) ⟨1577870, by rfl⟩ : syracuseStep 2103827 = 3155741) B3155741
theorem B1776163 : Blo 1401520 1776163 := bstep (se 1 (by rfl) ⟨1332122, by rfl⟩ : syracuseStep 1776163 = 2664245) B2664245
theorem B2103857 : Blo 1401520 2103857 := bstep (se 2 (by rfl) ⟨788946, by rfl⟩ : syracuseStep 2103857 = 1577893) B1577893
theorem B2366003 : Blo 1401520 2366003 := bstep (se 1 (by rfl) ⟨1774502, by rfl⟩ : syracuseStep 2366003 = 3549005) B3549005
theorem B2103875 : Blo 1401520 2103875 := bstep (se 1 (by rfl) ⟨1577906, by rfl⟩ : syracuseStep 2103875 = 3155813) B3155813
theorem B2103905 : Blo 1401520 2103905 := bstep (se 2 (by rfl) ⟨788964, by rfl⟩ : syracuseStep 2103905 = 1577929) B1577929
theorem B2103923 : Blo 1401520 2103923 := bstep (se 1 (by rfl) ⟨1577942, by rfl⟩ : syracuseStep 2103923 = 3155885) B3155885
theorem B1776259 : Blo 1401520 1776259 := bstep (se 1 (by rfl) ⟨1332194, by rfl⟩ : syracuseStep 1776259 = 2664389) B2664389
theorem B4733585 : Blo 1401520 4733585 := bstep (se 2 (by rfl) ⟨1775094, by rfl⟩ : syracuseStep 4733585 = 3550189) B3550189
theorem B2103953 : Blo 1401520 2103953 := bstep (se 2 (by rfl) ⟨788982, by rfl⟩ : syracuseStep 2103953 = 1577965) B1577965
theorem B2103971 : Blo 1401520 2103971 := bstep (se 1 (by rfl) ⟨1577978, by rfl⟩ : syracuseStep 2103971 = 3155957) B3155957
theorem B2366131 : Blo 1401520 2366131 := bstep (se 1 (by rfl) ⟨1774598, by rfl⟩ : syracuseStep 2366131 = 3549197) B3549197
theorem B2104001 : Blo 1401520 2104001 := bstep (se 2 (by rfl) ⟨789000, by rfl⟩ : syracuseStep 2104001 = 1578001) B1578001
theorem B2104019 : Blo 1401520 2104019 := bstep (se 1 (by rfl) ⟨1578014, by rfl⟩ : syracuseStep 2104019 = 3156029) B3156029
theorem B2104049 : Blo 1401520 2104049 := bstep (se 2 (by rfl) ⟨789018, by rfl⟩ : syracuseStep 2104049 = 1578037) B1578037
theorem B2104067 : Blo 1401520 2104067 := bstep (se 1 (by rfl) ⟨1578050, by rfl⟩ : syracuseStep 2104067 = 3156101) B3156101
theorem B4266769 : Blo 1401520 4266769 := bstep (se 2 (by rfl) ⟨1600038, by rfl⟩ : syracuseStep 4266769 = 3200077) B3200077
theorem B2104097 : Blo 1401520 2104097 := bstep (se 2 (by rfl) ⟨789036, by rfl⟩ : syracuseStep 2104097 = 1578073) B1578073
theorem B2661169 : Blo 1401520 2661169 := bstep (se 2 (by rfl) ⟨997938, by rfl⟩ : syracuseStep 2661169 = 1995877) B1995877
theorem B2104115 : Blo 1401520 2104115 := bstep (se 1 (by rfl) ⟨1578086, by rfl⟩ : syracuseStep 2104115 = 3156173) B3156173
theorem B2366273 : Blo 1401520 2366273 := bstep (se 2 (by rfl) ⟨887352, by rfl⟩ : syracuseStep 2366273 = 1774705) B1774705
theorem B6740813 : Blo 1401520 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B2104145 : Blo 1401520 2104145 := bstep (se 2 (by rfl) ⟨789054, by rfl⟩ : syracuseStep 2104145 = 1578109) B1578109
theorem B2104163 : Blo 1401520 2104163 := bstep (se 1 (by rfl) ⟨1578122, by rfl⟩ : syracuseStep 2104163 = 3156245) B3156245
theorem B3996515 : Blo 1401520 3996515 := bstep (se 1 (by rfl) ⟨2997386, by rfl⟩ : syracuseStep 3996515 = 5994773) B5994773
theorem B2104193 : Blo 1401520 2104193 := bstep (se 2 (by rfl) ⟨789072, by rfl⟩ : syracuseStep 2104193 = 1578145) B1578145
theorem B2104211 : Blo 1401520 2104211 := bstep (se 1 (by rfl) ⟨1578158, by rfl⟩ : syracuseStep 2104211 = 3156317) B3156317
theorem B2104241 : Blo 1401520 2104241 := bstep (se 2 (by rfl) ⟨789090, by rfl⟩ : syracuseStep 2104241 = 1578181) B1578181
theorem B2366401 : Blo 1401520 2366401 := bstep (se 2 (by rfl) ⟨887400, by rfl⟩ : syracuseStep 2366401 = 1774801) B1774801
theorem B2104259 : Blo 1401520 2104259 := bstep (se 1 (by rfl) ⟨1578194, by rfl⟩ : syracuseStep 2104259 = 3156389) B3156389
theorem B2661329 : Blo 1401520 2661329 := bstep (se 2 (by rfl) ⟨997998, by rfl⟩ : syracuseStep 2661329 = 1995997) B1995997
theorem B1997779 : Blo 1401520 1997779 := bstep (se 1 (by rfl) ⟨1498334, by rfl⟩ : syracuseStep 1997779 = 2996669) B2996669
theorem B2104289 : Blo 1401520 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B2366435 : Blo 1401520 2366435 := bstep (se 1 (by rfl) ⟨1774826, by rfl⟩ : syracuseStep 2366435 = 3549653) B3549653
theorem B2882531 : Blo 1401520 2882531 := bstep (se 1 (by rfl) ⟨2161898, by rfl⟩ : syracuseStep 2882531 = 4323797) B4323797
theorem B17054705 : Blo 1401520 17054705 := bstep (se 2 (by rfl) ⟨6395514, by rfl⟩ : syracuseStep 17054705 = 12791029) B12791029
theorem B2104307 : Blo 1401520 2104307 := bstep (se 1 (by rfl) ⟨1578230, by rfl⟩ : syracuseStep 2104307 = 3156461) B3156461
theorem B2997233 : Blo 1401520 2997233 := bstep (se 2 (by rfl) ⟨1123962, by rfl⟩ : syracuseStep 2997233 = 2247925) B2247925
theorem B2104337 : Blo 1401520 2104337 := bstep (se 2 (by rfl) ⟨789126, by rfl⟩ : syracuseStep 2104337 = 1578253) B1578253
theorem B2841635 : Blo 1401520 2841635 := bstep (se 1 (by rfl) ⟨2131226, by rfl⟩ : syracuseStep 2841635 = 4262453) B4262453
theorem B2104355 : Blo 1401520 2104355 := bstep (se 1 (by rfl) ⟨1578266, by rfl⟩ : syracuseStep 2104355 = 3156533) B3156533
theorem B2104385 : Blo 1401520 2104385 := bstep (se 2 (by rfl) ⟨789144, by rfl⟩ : syracuseStep 2104385 = 1578289) B1578289
theorem B4799569 : Blo 1401520 4799569 := bstep (se 2 (by rfl) ⟨1799838, by rfl⟩ : syracuseStep 4799569 = 3599677) B3599677
theorem B2104403 : Blo 1401520 2104403 := bstep (se 1 (by rfl) ⟨1578302, by rfl⟩ : syracuseStep 2104403 = 3156605) B3156605
theorem B2366563 : Blo 1401520 2366563 := bstep (se 1 (by rfl) ⟨1774922, by rfl⟩ : syracuseStep 2366563 = 3549845) B3549845
theorem B2104433 : Blo 1401520 2104433 := bstep (se 2 (by rfl) ⟨789162, by rfl⟩ : syracuseStep 2104433 = 1578325) B1578325
theorem B2104451 : Blo 1401520 2104451 := bstep (se 1 (by rfl) ⟨1578338, by rfl⟩ : syracuseStep 2104451 = 3156677) B3156677
theorem B2104481 : Blo 1401520 2104481 := bstep (se 2 (by rfl) ⟨789180, by rfl⟩ : syracuseStep 2104481 = 1578361) B1578361
theorem B4734125 : Blo 1401520 4734125 := bstep (se 3 (by rfl) ⟨887648, by rfl⟩ : syracuseStep 4734125 = 1775297) B1775297
theorem B2104499 : Blo 1401520 2104499 := bstep (se 1 (by rfl) ⟨1578374, by rfl⟩ : syracuseStep 2104499 = 3156749) B3156749
theorem B15154373 : Blo 1401520 15154373 := bstep (se 4 (by rfl) ⟨1420722, by rfl⟩ : syracuseStep 15154373 = 2841445) B2841445
theorem B2104529 : Blo 1401520 2104529 := bstep (se 2 (by rfl) ⟨789198, by rfl⟩ : syracuseStep 2104529 = 1578397) B1578397
theorem B4734179 : Blo 1401520 4734179 := bstep (se 1 (by rfl) ⟨3550634, by rfl⟩ : syracuseStep 4734179 = 7101269) B7101269
theorem B2104547 : Blo 1401520 2104547 := bstep (se 1 (by rfl) ⟨1578410, by rfl⟩ : syracuseStep 2104547 = 3156821) B3156821
theorem B2366705 : Blo 1401520 2366705 := bstep (se 2 (by rfl) ⟨887514, by rfl⟩ : syracuseStep 2366705 = 1775029) B1775029
theorem B2104577 : Blo 1401520 2104577 := bstep (se 2 (by rfl) ⟨789216, by rfl⟩ : syracuseStep 2104577 = 1578433) B1578433
theorem B2104595 : Blo 1401520 2104595 := bstep (se 1 (by rfl) ⟨1578446, by rfl⟩ : syracuseStep 2104595 = 3156893) B3156893
theorem B2104625 : Blo 1401520 2104625 := bstep (se 2 (by rfl) ⟨789234, by rfl⟩ : syracuseStep 2104625 = 1578469) B1578469
theorem B7200049 : Blo 1401520 7200049 := bstep (se 2 (by rfl) ⟨2700018, by rfl⟩ : syracuseStep 7200049 = 5400037) B5400037
theorem B15162677 : Blo 1401520 15162677 := bstep (se 5 (by rfl) ⟨710750, by rfl⟩ : syracuseStep 15162677 = 1421501) B1421501
theorem B2104643 : Blo 1401520 2104643 := bstep (se 1 (by rfl) ⟨1578482, by rfl⟩ : syracuseStep 2104643 = 3156965) B3156965
theorem B2104673 : Blo 1401520 2104673 := bstep (se 2 (by rfl) ⟨789252, by rfl⟩ : syracuseStep 2104673 = 1578505) B1578505
theorem B5684579 : Blo 1401520 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B2661731 : Blo 1401520 2661731 := bstep (se 1 (by rfl) ⟨1996298, by rfl⟩ : syracuseStep 2661731 = 3992597) B3992597
theorem B2366833 : Blo 1401520 2366833 := bstep (se 2 (by rfl) ⟨887562, by rfl⟩ : syracuseStep 2366833 = 1775125) B1775125
theorem B2104691 : Blo 1401520 2104691 := bstep (se 1 (by rfl) ⟨1578518, by rfl⟩ : syracuseStep 2104691 = 3157037) B3157037
theorem B2104721 : Blo 1401520 2104721 := bstep (se 2 (by rfl) ⟨789270, by rfl⟩ : syracuseStep 2104721 = 1578541) B1578541
theorem B2366867 : Blo 1401520 2366867 := bstep (se 1 (by rfl) ⟨1775150, by rfl⟩ : syracuseStep 2366867 = 3550301) B3550301
theorem B2104739 : Blo 1401520 2104739 := bstep (se 1 (by rfl) ⟨1578554, by rfl⟩ : syracuseStep 2104739 = 3157109) B3157109
theorem B2104769 : Blo 1401520 2104769 := bstep (se 2 (by rfl) ⟨789288, by rfl⟩ : syracuseStep 2104769 = 1578577) B1578577
theorem B5324237 : Blo 1401520 5324237 := bstep (se 3 (by rfl) ⟨998294, by rfl⟩ : syracuseStep 5324237 = 1996589) B1996589
theorem B2104787 : Blo 1401520 2104787 := bstep (se 1 (by rfl) ⟨1578590, by rfl⟩ : syracuseStep 2104787 = 3157181) B3157181
theorem B7577059 : Blo 1401520 7577059 := bstep (se 1 (by rfl) ⟨5682794, by rfl⟩ : syracuseStep 7577059 = 11365589) B11365589
theorem B4734449 : Blo 1401520 4734449 := bstep (se 2 (by rfl) ⟨1775418, by rfl⟩ : syracuseStep 4734449 = 3550837) B3550837
theorem B2104817 : Blo 1401520 2104817 := bstep (se 2 (by rfl) ⟨789306, by rfl⟩ : syracuseStep 2104817 = 1578613) B1578613
theorem B2104835 : Blo 1401520 2104835 := bstep (se 1 (by rfl) ⟨1578626, by rfl⟩ : syracuseStep 2104835 = 3157253) B3157253
theorem B7577101 : Blo 1401520 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B2366995 : Blo 1401520 2366995 := bstep (se 1 (by rfl) ⟨1775246, by rfl⟩ : syracuseStep 2366995 = 3550493) B3550493
theorem B2104865 : Blo 1401520 2104865 := bstep (se 2 (by rfl) ⟨789324, by rfl⟩ : syracuseStep 2104865 = 1578649) B1578649
theorem B2104883 : Blo 1401520 2104883 := bstep (se 1 (by rfl) ⟨1578662, by rfl⟩ : syracuseStep 2104883 = 3157325) B3157325
theorem B2080337 : Blo 1401520 2080337 := bstep (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) B1560253
theorem B2104913 : Blo 1401520 2104913 := bstep (se 2 (by rfl) ⟨789342, by rfl⟩ : syracuseStep 2104913 = 1578685) B1578685
theorem B2104931 : Blo 1401520 2104931 := bstep (se 1 (by rfl) ⟨1578698, by rfl⟩ : syracuseStep 2104931 = 3157397) B3157397
theorem B2104961 : Blo 1401520 2104961 := bstep (se 2 (by rfl) ⟨789360, by rfl⟩ : syracuseStep 2104961 = 1578721) B1578721
theorem B2104979 : Blo 1401520 2104979 := bstep (se 1 (by rfl) ⟨1578734, by rfl⟩ : syracuseStep 2104979 = 3157469) B3157469
theorem B2367137 : Blo 1401520 2367137 := bstep (se 2 (by rfl) ⟨887676, by rfl⟩ : syracuseStep 2367137 = 1775353) B1775353
theorem B2105009 : Blo 1401520 2105009 := bstep (se 2 (by rfl) ⟨789378, by rfl⟩ : syracuseStep 2105009 = 1578757) B1578757
theorem B2105027 : Blo 1401520 2105027 := bstep (se 1 (by rfl) ⟨1578770, by rfl⟩ : syracuseStep 2105027 = 3157541) B3157541
theorem B3153617 : Blo 1401520 3153617 := bstep (se 2 (by rfl) ⟨1182606, by rfl⟩ : syracuseStep 3153617 = 2365213) B2365213
theorem B2105057 : Blo 1401520 2105057 := bstep (se 2 (by rfl) ⟨789396, by rfl⟩ : syracuseStep 2105057 = 1578793) B1578793
theorem B3153635 : Blo 1401520 3153635 := bstep (se 1 (by rfl) ⟨2365226, by rfl⟩ : syracuseStep 3153635 = 4730453) B4730453
theorem B2105075 : Blo 1401520 2105075 := bstep (se 1 (by rfl) ⟨1578806, by rfl⟩ : syracuseStep 2105075 = 3157613) B3157613
theorem B2105105 : Blo 1401520 2105105 := bstep (se 2 (by rfl) ⟨789414, by rfl⟩ : syracuseStep 2105105 = 1578829) B1578829
theorem B2367265 : Blo 1401520 2367265 := bstep (se 2 (by rfl) ⟨887724, by rfl⟩ : syracuseStep 2367265 = 1775449) B1775449
theorem B2105123 : Blo 1401520 2105123 := bstep (se 1 (by rfl) ⟨1578842, by rfl⟩ : syracuseStep 2105123 = 3157685) B3157685
theorem B2105153 : Blo 1401520 2105153 := bstep (se 2 (by rfl) ⟨789432, by rfl⟩ : syracuseStep 2105153 = 1578865) B1578865
theorem B2367299 : Blo 1401520 2367299 := bstep (se 1 (by rfl) ⟨1775474, by rfl⟩ : syracuseStep 2367299 = 3550949) B3550949
theorem B2105171 : Blo 1401520 2105171 := bstep (se 1 (by rfl) ⟨1578878, by rfl⟩ : syracuseStep 2105171 = 3157757) B3157757
theorem B2105201 : Blo 1401520 2105201 := bstep (se 2 (by rfl) ⟨789450, by rfl⟩ : syracuseStep 2105201 = 1578901) B1578901
theorem B2105219 : Blo 1401520 2105219 := bstep (se 1 (by rfl) ⟨1578914, by rfl⟩ : syracuseStep 2105219 = 3157829) B3157829
theorem B7987085 : Blo 1401520 7987085 := bstep (se 3 (by rfl) ⟨1497578, by rfl⟩ : syracuseStep 7987085 = 2995157) B2995157
theorem B2105249 : Blo 1401520 2105249 := bstep (se 2 (by rfl) ⟨789468, by rfl⟩ : syracuseStep 2105249 = 1578937) B1578937
theorem B2105267 : Blo 1401520 2105267 := bstep (se 1 (by rfl) ⟨1578950, by rfl⟩ : syracuseStep 2105267 = 3157901) B3157901
theorem B2367427 : Blo 1401520 2367427 := bstep (se 1 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 2367427 = 3551141) B3551141
theorem B8536013 : Blo 1401520 8536013 := bstep (se 3 (by rfl) ⟨1600502, by rfl⟩ : syracuseStep 8536013 = 3201005) B3201005
theorem B3153905 : Blo 1401520 3153905 := bstep (se 2 (by rfl) ⟨1182714, by rfl⟩ : syracuseStep 3153905 = 2365429) B2365429
theorem B3792919 : Blo 1401520 3792919 := bstep (se 1 (by rfl) ⟨2844689, by rfl⟩ : syracuseStep 3792919 = 5689379) B5689379
theorem B6152237 : Blo 1401520 6152237 := bstep (se 3 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 6152237 = 2307089) B2307089
theorem B3153995 : Blo 1401520 3153995 := bstep (se 1 (by rfl) ⟨2365496, by rfl⟩ : syracuseStep 3153995 = 4730993) B4730993
theorem B3154049 : Blo 1401520 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B1622155 : Blo 1401520 1622155 := bstep (se 1 (by rfl) ⟨1216616, by rfl⟩ : syracuseStep 1622155 = 2433233) B2433233
theorem B20209985 : Blo 1401520 20209985 := bstep (se 2 (by rfl) ⟨7578744, by rfl⟩ : syracuseStep 20209985 = 15157489) B15157489
theorem B3154265 : Blo 1401520 3154265 := bstep (se 2 (by rfl) ⟨1182849, by rfl⟩ : syracuseStep 3154265 = 2365699) B2365699
theorem B6488471 : Blo 1401520 6488471 := bstep (se 1 (by rfl) ⟨4866353, by rfl⟩ : syracuseStep 6488471 = 9732707) B9732707
theorem B3154355 : Blo 1401520 3154355 := bstep (se 1 (by rfl) ⟨2365766, by rfl⟩ : syracuseStep 3154355 = 4731533) B4731533
theorem B2367947 : Blo 1401520 2367947 := bstep (se 1 (by rfl) ⟨1775960, by rfl⟩ : syracuseStep 2367947 = 3551921) B3551921
theorem B3154391 : Blo 1401520 3154391 := bstep (se 1 (by rfl) ⟨2365793, by rfl⟩ : syracuseStep 3154391 = 4731587) B4731587
theorem B2245195 : Blo 1401520 2245195 := bstep (se 1 (by rfl) ⟨1683896, by rfl⟩ : syracuseStep 2245195 = 3367793) B3367793
theorem B7103051 : Blo 1401520 7103051 := bstep (se 1 (by rfl) ⟨5327288, by rfl⟩ : syracuseStep 7103051 = 10654577) B10654577
theorem B2368075 : Blo 1401520 2368075 := bstep (se 1 (by rfl) ⟨1776056, by rfl⟩ : syracuseStep 2368075 = 3552113) B3552113
theorem B3154571 : Blo 1401520 3154571 := bstep (se 1 (by rfl) ⟨2365928, by rfl⟩ : syracuseStep 3154571 = 4731857) B4731857
theorem B1401527 : Blo 1401520 1401527 := bstep (se 1 (by rfl) ⟨1051145, by rfl⟩ : syracuseStep 1401527 = 2102291) B2102291
theorem B3154625 : Blo 1401520 3154625 := bstep (se 2 (by rfl) ⟨1182984, by rfl⟩ : syracuseStep 3154625 = 2365969) B2365969
theorem B1401547 : Blo 1401520 1401547 := bstep (se 1 (by rfl) ⟨1051160, by rfl⟩ : syracuseStep 1401547 = 2102321) B2102321
theorem B4735691 : Blo 1401520 4735691 := bstep (se 1 (by rfl) ⟨3551768, by rfl⟩ : syracuseStep 4735691 = 7103537) B7103537
theorem B1401559 : Blo 1401520 1401559 := bstep (se 1 (by rfl) ⟨1051169, by rfl⟩ : syracuseStep 1401559 = 2102339) B2102339
theorem B2368217 : Blo 1401520 2368217 := bstep (se 2 (by rfl) ⟨888081, by rfl⟩ : syracuseStep 2368217 = 1776163) B1776163
theorem B5989085 : Blo 1401520 5989085 := bstep (se 3 (by rfl) ⟨1122953, by rfl⟩ : syracuseStep 5989085 = 2245907) B2245907
theorem B1401579 : Blo 1401520 1401579 := bstep (se 1 (by rfl) ⟨1051184, by rfl⟩ : syracuseStep 1401579 = 2102369) B2102369
theorem B1401591 : Blo 1401520 1401591 := bstep (se 1 (by rfl) ⟨1051193, by rfl⟩ : syracuseStep 1401591 = 2102387) B2102387
theorem B1401611 : Blo 1401520 1401611 := bstep (se 1 (by rfl) ⟨1051208, by rfl⟩ : syracuseStep 1401611 = 2102417) B2102417
theorem B1401623 : Blo 1401520 1401623 := bstep (se 1 (by rfl) ⟨1051217, by rfl⟩ : syracuseStep 1401623 = 2102435) B2102435
theorem B1401643 : Blo 1401520 1401643 := bstep (se 1 (by rfl) ⟨1051232, by rfl⟩ : syracuseStep 1401643 = 2102465) B2102465
theorem B2663219 : Blo 1401520 2663219 := bstep (se 1 (by rfl) ⟨1997414, by rfl⟩ : syracuseStep 2663219 = 3994829) B3994829
theorem B1401655 : Blo 1401520 1401655 := bstep (se 1 (by rfl) ⟨1051241, by rfl⟩ : syracuseStep 1401655 = 2102483) B2102483
theorem B1401675 : Blo 1401520 1401675 := bstep (se 1 (by rfl) ⟨1051256, by rfl⟩ : syracuseStep 1401675 = 2102513) B2102513
theorem B1401687 : Blo 1401520 1401687 := bstep (se 1 (by rfl) ⟨1051265, by rfl⟩ : syracuseStep 1401687 = 2102531) B2102531
theorem B2368345 : Blo 1401520 2368345 := bstep (se 2 (by rfl) ⟨888129, by rfl⟩ : syracuseStep 2368345 = 1776259) B1776259
theorem B1401707 : Blo 1401520 1401707 := bstep (se 1 (by rfl) ⟨1051280, by rfl⟩ : syracuseStep 1401707 = 2102561) B2102561
theorem B1401719 : Blo 1401520 1401719 := bstep (se 1 (by rfl) ⟨1051289, by rfl⟩ : syracuseStep 1401719 = 2102579) B2102579
theorem B1401739 : Blo 1401520 1401739 := bstep (se 1 (by rfl) ⟨1051304, by rfl⟩ : syracuseStep 1401739 = 2102609) B2102609
theorem B1401751 : Blo 1401520 1401751 := bstep (se 1 (by rfl) ⟨1051313, by rfl⟩ : syracuseStep 1401751 = 2102627) B2102627
theorem B3154841 : Blo 1401520 3154841 := bstep (se 2 (by rfl) ⟨1183065, by rfl⟩ : syracuseStep 3154841 = 2366131) B2366131
theorem B1401771 : Blo 1401520 1401771 := bstep (se 1 (by rfl) ⟨1051328, by rfl⟩ : syracuseStep 1401771 = 2102657) B2102657
theorem B3548083 : Blo 1401520 3548083 := bstep (se 1 (by rfl) ⟨2661062, by rfl⟩ : syracuseStep 3548083 = 5322125) B5322125
theorem B1401783 : Blo 1401520 1401783 := bstep (se 1 (by rfl) ⟨1051337, by rfl⟩ : syracuseStep 1401783 = 2102675) B2102675
theorem B1401803 : Blo 1401520 1401803 := bstep (se 1 (by rfl) ⟨1051352, by rfl⟩ : syracuseStep 1401803 = 2102705) B2102705
theorem B2663371 : Blo 1401520 2663371 := bstep (se 1 (by rfl) ⟨1997528, by rfl⟩ : syracuseStep 2663371 = 3995057) B3995057
theorem B1401815 : Blo 1401520 1401815 := bstep (se 1 (by rfl) ⟨1051361, by rfl⟩ : syracuseStep 1401815 = 2102723) B2102723
theorem B4735961 : Blo 1401520 4735961 := bstep (se 2 (by rfl) ⟨1775985, by rfl⟩ : syracuseStep 4735961 = 3551971) B3551971
theorem B1401835 : Blo 1401520 1401835 := bstep (se 1 (by rfl) ⟨1051376, by rfl⟩ : syracuseStep 1401835 = 2102753) B2102753
theorem B3154931 : Blo 1401520 3154931 := bstep (se 1 (by rfl) ⟨2366198, by rfl⟩ : syracuseStep 3154931 = 4732397) B4732397
theorem B1401847 : Blo 1401520 1401847 := bstep (se 1 (by rfl) ⟨1051385, by rfl⟩ : syracuseStep 1401847 = 2102771) B2102771
theorem B1401867 : Blo 1401520 1401867 := bstep (se 1 (by rfl) ⟨1051400, by rfl⟩ : syracuseStep 1401867 = 2102801) B2102801
theorem B1401879 : Blo 1401520 1401879 := bstep (se 1 (by rfl) ⟨1051409, by rfl⟩ : syracuseStep 1401879 = 2102819) B2102819
theorem B3154967 : Blo 1401520 3154967 := bstep (se 1 (by rfl) ⟨2366225, by rfl⟩ : syracuseStep 3154967 = 4732451) B4732451
theorem B1401899 : Blo 1401520 1401899 := bstep (se 1 (by rfl) ⟨1051424, by rfl⟩ : syracuseStep 1401899 = 2102849) B2102849
theorem B1401911 : Blo 1401520 1401911 := bstep (se 1 (by rfl) ⟨1051433, by rfl⟩ : syracuseStep 1401911 = 2102867) B2102867
theorem B3548225 : Blo 1401520 3548225 := bstep (se 2 (by rfl) ⟨1330584, by rfl⟩ : syracuseStep 3548225 = 2661169) B2661169
theorem B10650689 : Blo 1401520 10650689 := bstep (se 2 (by rfl) ⟨3994008, by rfl⟩ : syracuseStep 10650689 = 7988017) B7988017
theorem B1401931 : Blo 1401520 1401931 := bstep (se 1 (by rfl) ⟨1051448, by rfl⟩ : syracuseStep 1401931 = 2102897) B2102897
theorem B1401943 : Blo 1401520 1401943 := bstep (se 1 (by rfl) ⟨1051457, by rfl⟩ : syracuseStep 1401943 = 2102915) B2102915
theorem B1401963 : Blo 1401520 1401963 := bstep (se 1 (by rfl) ⟨1051472, by rfl⟩ : syracuseStep 1401963 = 2102945) B2102945
theorem B1401975 : Blo 1401520 1401975 := bstep (se 1 (by rfl) ⟨1051481, by rfl⟩ : syracuseStep 1401975 = 2102963) B2102963
theorem B1401995 : Blo 1401520 1401995 := bstep (se 1 (by rfl) ⟨1051496, by rfl⟩ : syracuseStep 1401995 = 2102993) B2102993
theorem B1402007 : Blo 1401520 1402007 := bstep (se 1 (by rfl) ⟨1051505, by rfl⟩ : syracuseStep 1402007 = 2103011) B2103011
theorem B1402027 : Blo 1401520 1402027 := bstep (se 1 (by rfl) ⟨1051520, by rfl⟩ : syracuseStep 1402027 = 2103041) B2103041
theorem B1402039 : Blo 1401520 1402039 := bstep (se 1 (by rfl) ⟨1051529, by rfl⟩ : syracuseStep 1402039 = 2103059) B2103059
theorem B1402059 : Blo 1401520 1402059 := bstep (se 1 (by rfl) ⟨1051544, by rfl⟩ : syracuseStep 1402059 = 2103089) B2103089
theorem B3155147 : Blo 1401520 3155147 := bstep (se 1 (by rfl) ⟨2366360, by rfl⟩ : syracuseStep 3155147 = 4732721) B4732721
theorem B1402071 : Blo 1401520 1402071 := bstep (se 1 (by rfl) ⟨1051553, by rfl⟩ : syracuseStep 1402071 = 2103107) B2103107
theorem B1402091 : Blo 1401520 1402091 := bstep (se 1 (by rfl) ⟨1051568, by rfl⟩ : syracuseStep 1402091 = 2103137) B2103137
theorem B1402103 : Blo 1401520 1402103 := bstep (se 1 (by rfl) ⟨1051577, by rfl⟩ : syracuseStep 1402103 = 2103155) B2103155
theorem B3155201 : Blo 1401520 3155201 := bstep (se 2 (by rfl) ⟨1183200, by rfl⟩ : syracuseStep 3155201 = 2366401) B2366401
theorem B1402123 : Blo 1401520 1402123 := bstep (se 1 (by rfl) ⟨1051592, by rfl⟩ : syracuseStep 1402123 = 2103185) B2103185
theorem B1402135 : Blo 1401520 1402135 := bstep (se 1 (by rfl) ⟨1051601, by rfl⟩ : syracuseStep 1402135 = 2103203) B2103203
theorem B2663705 : Blo 1401520 2663705 := bstep (se 2 (by rfl) ⟨998889, by rfl⟩ : syracuseStep 2663705 = 1997779) B1997779
theorem B1402155 : Blo 1401520 1402155 := bstep (se 1 (by rfl) ⟨1051616, by rfl⟩ : syracuseStep 1402155 = 2103233) B2103233
theorem B1402167 : Blo 1401520 1402167 := bstep (se 1 (by rfl) ⟨1051625, by rfl⟩ : syracuseStep 1402167 = 2103251) B2103251
theorem B1402187 : Blo 1401520 1402187 := bstep (se 1 (by rfl) ⟨1051640, by rfl⟩ : syracuseStep 1402187 = 2103281) B2103281
theorem B1402199 : Blo 1401520 1402199 := bstep (se 1 (by rfl) ⟨1051649, by rfl⟩ : syracuseStep 1402199 = 2103299) B2103299
theorem B1754455 : Blo 1401520 1754455 := bstep (se 1 (by rfl) ⟨1315841, by rfl⟩ : syracuseStep 1754455 = 2631683) B2631683
theorem B1402219 : Blo 1401520 1402219 := bstep (se 1 (by rfl) ⟨1051664, by rfl⟩ : syracuseStep 1402219 = 2103329) B2103329
theorem B1402231 : Blo 1401520 1402231 := bstep (se 1 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 1402231 = 2103347) B2103347
theorem B1402251 : Blo 1401520 1402251 := bstep (se 1 (by rfl) ⟨1051688, by rfl⟩ : syracuseStep 1402251 = 2103377) B2103377
theorem B1402263 : Blo 1401520 1402263 := bstep (se 1 (by rfl) ⟨1051697, by rfl⟩ : syracuseStep 1402263 = 2103395) B2103395
theorem B5989783 : Blo 1401520 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B1402283 : Blo 1401520 1402283 := bstep (se 1 (by rfl) ⟨1051712, by rfl⟩ : syracuseStep 1402283 = 2103425) B2103425
theorem B1402295 : Blo 1401520 1402295 := bstep (se 1 (by rfl) ⟨1051721, by rfl⟩ : syracuseStep 1402295 = 2103443) B2103443
theorem B6399425 : Blo 1401520 6399425 := bstep (se 2 (by rfl) ⟨2399784, by rfl⟩ : syracuseStep 6399425 = 4799569) B4799569
theorem B1402315 : Blo 1401520 1402315 := bstep (se 1 (by rfl) ⟨1051736, by rfl⟩ : syracuseStep 1402315 = 2103473) B2103473
theorem B1402327 : Blo 1401520 1402327 := bstep (se 1 (by rfl) ⟨1051745, by rfl⟩ : syracuseStep 1402327 = 2103491) B2103491
theorem B3155417 : Blo 1401520 3155417 := bstep (se 2 (by rfl) ⟨1183281, by rfl⟩ : syracuseStep 3155417 = 2366563) B2366563
theorem B1402347 : Blo 1401520 1402347 := bstep (se 1 (by rfl) ⟨1051760, by rfl⟩ : syracuseStep 1402347 = 2103521) B2103521
theorem B1402359 : Blo 1401520 1402359 := bstep (se 1 (by rfl) ⟨1051769, by rfl⟩ : syracuseStep 1402359 = 2103539) B2103539
theorem B1402379 : Blo 1401520 1402379 := bstep (se 1 (by rfl) ⟨1051784, by rfl⟩ : syracuseStep 1402379 = 2103569) B2103569
theorem B1402391 : Blo 1401520 1402391 := bstep (se 1 (by rfl) ⟨1051793, by rfl⟩ : syracuseStep 1402391 = 2103587) B2103587
theorem B1402411 : Blo 1401520 1402411 := bstep (se 1 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 1402411 = 2103617) B2103617
theorem B5547565 : Blo 1401520 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B3155507 : Blo 1401520 3155507 := bstep (se 1 (by rfl) ⟨2366630, by rfl⟩ : syracuseStep 3155507 = 4733261) B4733261
theorem B1402423 : Blo 1401520 1402423 := bstep (se 1 (by rfl) ⟨1051817, by rfl⟩ : syracuseStep 1402423 = 2103635) B2103635
theorem B1402443 : Blo 1401520 1402443 := bstep (se 1 (by rfl) ⟨1051832, by rfl⟩ : syracuseStep 1402443 = 2103665) B2103665
theorem B1402455 : Blo 1401520 1402455 := bstep (se 1 (by rfl) ⟨1051841, by rfl⟩ : syracuseStep 1402455 = 2103683) B2103683
theorem B3155543 : Blo 1401520 3155543 := bstep (se 1 (by rfl) ⟨2366657, by rfl⟩ : syracuseStep 3155543 = 4733315) B4733315
theorem B5400157 : Blo 1401520 5400157 := bstep (se 3 (by rfl) ⟨1012529, by rfl⟩ : syracuseStep 5400157 = 2025059) B2025059
theorem B1402475 : Blo 1401520 1402475 := bstep (se 1 (by rfl) ⟨1051856, by rfl⟩ : syracuseStep 1402475 = 2103713) B2103713
theorem B1402487 : Blo 1401520 1402487 := bstep (se 1 (by rfl) ⟨1051865, by rfl⟩ : syracuseStep 1402487 = 2103731) B2103731
theorem B1402507 : Blo 1401520 1402507 := bstep (se 1 (by rfl) ⟨1051880, by rfl⟩ : syracuseStep 1402507 = 2103761) B2103761
theorem B5400209 : Blo 1401520 5400209 := bstep (se 2 (by rfl) ⟨2025078, by rfl⟩ : syracuseStep 5400209 = 4050157) B4050157
theorem B4490903 : Blo 1401520 4490903 := bstep (se 1 (by rfl) ⟨3368177, by rfl⟩ : syracuseStep 4490903 = 6736355) B6736355
theorem B1402519 : Blo 1401520 1402519 := bstep (se 1 (by rfl) ⟨1051889, by rfl⟩ : syracuseStep 1402519 = 2103779) B2103779
theorem B2246297 : Blo 1401520 2246297 := bstep (se 2 (by rfl) ⟨842361, by rfl⟩ : syracuseStep 2246297 = 1684723) B1684723
theorem B4736663 : Blo 1401520 4736663 := bstep (se 1 (by rfl) ⟨3552497, by rfl⟩ : syracuseStep 4736663 = 7104995) B7104995
theorem B1402539 : Blo 1401520 1402539 := bstep (se 1 (by rfl) ⟨1051904, by rfl⟩ : syracuseStep 1402539 = 2103809) B2103809
theorem B5924531 : Blo 1401520 5924531 := bstep (se 1 (by rfl) ⟨4443398, by rfl⟩ : syracuseStep 5924531 = 8886797) B8886797
theorem B1402551 : Blo 1401520 1402551 := bstep (se 1 (by rfl) ⟨1051913, by rfl⟩ : syracuseStep 1402551 = 2103827) B2103827
theorem B1402571 : Blo 1401520 1402571 := bstep (se 1 (by rfl) ⟨1051928, by rfl⟩ : syracuseStep 1402571 = 2103857) B2103857
theorem B1402583 : Blo 1401520 1402583 := bstep (se 1 (by rfl) ⟨1051937, by rfl⟩ : syracuseStep 1402583 = 2103875) B2103875
theorem B1402603 : Blo 1401520 1402603 := bstep (se 1 (by rfl) ⟨1051952, by rfl⟩ : syracuseStep 1402603 = 2103905) B2103905
theorem B1402615 : Blo 1401520 1402615 := bstep (se 1 (by rfl) ⟨1051961, by rfl⟩ : syracuseStep 1402615 = 2103923) B2103923
theorem B3155723 : Blo 1401520 3155723 := bstep (se 1 (by rfl) ⟨2366792, by rfl⟩ : syracuseStep 3155723 = 4733585) B4733585
theorem B1402635 : Blo 1401520 1402635 := bstep (se 1 (by rfl) ⟨1051976, by rfl⟩ : syracuseStep 1402635 = 2103953) B2103953
theorem B1402647 : Blo 1401520 1402647 := bstep (se 1 (by rfl) ⟨1051985, by rfl⟩ : syracuseStep 1402647 = 2103971) B2103971
theorem B1402667 : Blo 1401520 1402667 := bstep (se 1 (by rfl) ⟨1052000, by rfl⟩ : syracuseStep 1402667 = 2104001) B2104001
theorem B1402679 : Blo 1401520 1402679 := bstep (se 1 (by rfl) ⟨1052009, by rfl⟩ : syracuseStep 1402679 = 2104019) B2104019
theorem B3155777 : Blo 1401520 3155777 := bstep (se 2 (by rfl) ⟨1183416, by rfl⟩ : syracuseStep 3155777 = 2366833) B2366833
theorem B1402699 : Blo 1401520 1402699 := bstep (se 1 (by rfl) ⟨1052024, by rfl⟩ : syracuseStep 1402699 = 2104049) B2104049
theorem B5326667 : Blo 1401520 5326667 := bstep (se 1 (by rfl) ⟨3995000, by rfl⟩ : syracuseStep 5326667 = 7990001) B7990001
theorem B1402711 : Blo 1401520 1402711 := bstep (se 1 (by rfl) ⟨1052033, by rfl⟩ : syracuseStep 1402711 = 2104067) B2104067
theorem B5326681 : Blo 1401520 5326681 := bstep (se 2 (by rfl) ⟨1997505, by rfl⟩ : syracuseStep 5326681 = 3995011) B3995011
theorem B1402731 : Blo 1401520 1402731 := bstep (se 1 (by rfl) ⟨1052048, by rfl⟩ : syracuseStep 1402731 = 2104097) B2104097
theorem B1402743 : Blo 1401520 1402743 := bstep (se 1 (by rfl) ⟨1052057, by rfl⟩ : syracuseStep 1402743 = 2104115) B2104115
theorem B1402763 : Blo 1401520 1402763 := bstep (se 1 (by rfl) ⟨1052072, by rfl⟩ : syracuseStep 1402763 = 2104145) B2104145
theorem B1402775 : Blo 1401520 1402775 := bstep (se 1 (by rfl) ⟨1052081, by rfl⟩ : syracuseStep 1402775 = 2104163) B2104163
theorem B2664343 : Blo 1401520 2664343 := bstep (se 1 (by rfl) ⟨1998257, by rfl⟩ : syracuseStep 2664343 = 3996515) B3996515
theorem B1402795 : Blo 1401520 1402795 := bstep (se 1 (by rfl) ⟨1052096, by rfl⟩ : syracuseStep 1402795 = 2104193) B2104193
theorem B1402807 : Blo 1401520 1402807 := bstep (se 1 (by rfl) ⟨1052105, by rfl⟩ : syracuseStep 1402807 = 2104211) B2104211
theorem B1402827 : Blo 1401520 1402827 := bstep (se 1 (by rfl) ⟨1052120, by rfl⟩ : syracuseStep 1402827 = 2104241) B2104241
theorem B1402839 : Blo 1401520 1402839 := bstep (se 1 (by rfl) ⟨1052129, by rfl⟩ : syracuseStep 1402839 = 2104259) B2104259
theorem B10102745 : Blo 1401520 10102745 := bstep (se 2 (by rfl) ⟨3788529, by rfl⟩ : syracuseStep 10102745 = 7577059) B7577059
theorem B1402859 : Blo 1401520 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B1402871 : Blo 1401520 1402871 := bstep (se 1 (by rfl) ⟨1052153, by rfl⟩ : syracuseStep 1402871 = 2104307) B2104307
theorem B1402891 : Blo 1401520 1402891 := bstep (se 1 (by rfl) ⟨1052168, by rfl⟩ : syracuseStep 1402891 = 2104337) B2104337
theorem B10102801 : Blo 1401520 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B1894423 : Blo 1401520 1894423 := bstep (se 1 (by rfl) ⟨1420817, by rfl⟩ : syracuseStep 1894423 = 2841635) B2841635
theorem B1402903 : Blo 1401520 1402903 := bstep (se 1 (by rfl) ⟨1052177, by rfl⟩ : syracuseStep 1402903 = 2104355) B2104355
theorem B3155993 : Blo 1401520 3155993 := bstep (se 2 (by rfl) ⟨1183497, by rfl⟩ : syracuseStep 3155993 = 2366995) B2366995
theorem B1402923 : Blo 1401520 1402923 := bstep (se 1 (by rfl) ⟨1052192, by rfl⟩ : syracuseStep 1402923 = 2104385) B2104385
theorem B7989293 : Blo 1401520 7989293 := bstep (se 3 (by rfl) ⟨1497992, by rfl⟩ : syracuseStep 7989293 = 2995985) B2995985
theorem B1402935 : Blo 1401520 1402935 := bstep (se 1 (by rfl) ⟨1052201, by rfl⟩ : syracuseStep 1402935 = 2104403) B2104403
theorem B1402955 : Blo 1401520 1402955 := bstep (se 1 (by rfl) ⟨1052216, by rfl⟩ : syracuseStep 1402955 = 2104433) B2104433
theorem B1402967 : Blo 1401520 1402967 := bstep (se 1 (by rfl) ⟨1052225, by rfl⟩ : syracuseStep 1402967 = 2104451) B2104451
theorem B1402987 : Blo 1401520 1402987 := bstep (se 1 (by rfl) ⟨1052240, by rfl⟩ : syracuseStep 1402987 = 2104481) B2104481
theorem B3156083 : Blo 1401520 3156083 := bstep (se 1 (by rfl) ⟨2367062, by rfl⟩ : syracuseStep 3156083 = 4734125) B4734125
theorem B1402999 : Blo 1401520 1402999 := bstep (se 1 (by rfl) ⟨1052249, by rfl⟩ : syracuseStep 1402999 = 2104499) B2104499
theorem B10102915 : Blo 1401520 10102915 := bstep (se 1 (by rfl) ⟨7577186, by rfl⟩ : syracuseStep 10102915 = 15154373) B15154373
theorem B1403019 : Blo 1401520 1403019 := bstep (se 1 (by rfl) ⟨1052264, by rfl⟩ : syracuseStep 1403019 = 2104529) B2104529
theorem B3156119 : Blo 1401520 3156119 := bstep (se 1 (by rfl) ⟨2367089, by rfl⟩ : syracuseStep 3156119 = 4734179) B4734179
theorem B1403031 : Blo 1401520 1403031 := bstep (se 1 (by rfl) ⟨1052273, by rfl⟩ : syracuseStep 1403031 = 2104547) B2104547
theorem B1403051 : Blo 1401520 1403051 := bstep (se 1 (by rfl) ⟨1052288, by rfl⟩ : syracuseStep 1403051 = 2104577) B2104577
theorem B1403063 : Blo 1401520 1403063 := bstep (se 1 (by rfl) ⟨1052297, by rfl⟩ : syracuseStep 1403063 = 2104595) B2104595
theorem B1403083 : Blo 1401520 1403083 := bstep (se 1 (by rfl) ⟨1052312, by rfl⟩ : syracuseStep 1403083 = 2104625) B2104625
theorem B1403095 : Blo 1401520 1403095 := bstep (se 1 (by rfl) ⟨1052321, by rfl⟩ : syracuseStep 1403095 = 2104643) B2104643
theorem B1403115 : Blo 1401520 1403115 := bstep (se 1 (by rfl) ⟨1052336, by rfl⟩ : syracuseStep 1403115 = 2104673) B2104673
theorem B1403127 : Blo 1401520 1403127 := bstep (se 1 (by rfl) ⟨1052345, by rfl⟩ : syracuseStep 1403127 = 2104691) B2104691
theorem B1403147 : Blo 1401520 1403147 := bstep (se 1 (by rfl) ⟨1052360, by rfl⟩ : syracuseStep 1403147 = 2104721) B2104721
theorem B1403159 : Blo 1401520 1403159 := bstep (se 1 (by rfl) ⟨1052369, by rfl⟩ : syracuseStep 1403159 = 2104739) B2104739
theorem B1403179 : Blo 1401520 1403179 := bstep (se 1 (by rfl) ⟨1052384, by rfl⟩ : syracuseStep 1403179 = 2104769) B2104769
theorem B3549491 : Blo 1401520 3549491 := bstep (se 1 (by rfl) ⟨2662118, by rfl⟩ : syracuseStep 3549491 = 5324237) B5324237
theorem B1403191 : Blo 1401520 1403191 := bstep (se 1 (by rfl) ⟨1052393, by rfl⟩ : syracuseStep 1403191 = 2104787) B2104787
theorem B7104833 : Blo 1401520 7104833 := bstep (se 2 (by rfl) ⟨2664312, by rfl⟩ : syracuseStep 7104833 = 5328625) B5328625
theorem B3156299 : Blo 1401520 3156299 := bstep (se 1 (by rfl) ⟨2367224, by rfl⟩ : syracuseStep 3156299 = 4734449) B4734449
theorem B1403211 : Blo 1401520 1403211 := bstep (se 1 (by rfl) ⟨1052408, by rfl⟩ : syracuseStep 1403211 = 2104817) B2104817
theorem B1403223 : Blo 1401520 1403223 := bstep (se 1 (by rfl) ⟨1052417, by rfl⟩ : syracuseStep 1403223 = 2104835) B2104835
theorem B1403243 : Blo 1401520 1403243 := bstep (se 1 (by rfl) ⟨1052432, by rfl⟩ : syracuseStep 1403243 = 2104865) B2104865
theorem B1403255 : Blo 1401520 1403255 := bstep (se 1 (by rfl) ⟨1052441, by rfl⟩ : syracuseStep 1403255 = 2104883) B2104883
theorem B3156353 : Blo 1401520 3156353 := bstep (se 2 (by rfl) ⟨1183632, by rfl⟩ : syracuseStep 3156353 = 2367265) B2367265
theorem B1403275 : Blo 1401520 1403275 := bstep (se 1 (by rfl) ⟨1052456, by rfl⟩ : syracuseStep 1403275 = 2104913) B2104913
theorem B1403287 : Blo 1401520 1403287 := bstep (se 1 (by rfl) ⟨1052465, by rfl⟩ : syracuseStep 1403287 = 2104931) B2104931
theorem B1403307 : Blo 1401520 1403307 := bstep (se 1 (by rfl) ⟨1052480, by rfl⟩ : syracuseStep 1403307 = 2104961) B2104961
theorem B1403319 : Blo 1401520 1403319 := bstep (se 1 (by rfl) ⟨1052489, by rfl⟩ : syracuseStep 1403319 = 2104979) B2104979
theorem B5401025 : Blo 1401520 5401025 := bstep (se 2 (by rfl) ⟨2025384, by rfl⟩ : syracuseStep 5401025 = 4050769) B4050769
theorem B1403339 : Blo 1401520 1403339 := bstep (se 1 (by rfl) ⟨1052504, by rfl⟩ : syracuseStep 1403339 = 2105009) B2105009
theorem B1403351 : Blo 1401520 1403351 := bstep (se 1 (by rfl) ⟨1052513, by rfl⟩ : syracuseStep 1403351 = 2105027) B2105027
theorem B1403371 : Blo 1401520 1403371 := bstep (se 1 (by rfl) ⟨1052528, by rfl⟩ : syracuseStep 1403371 = 2105057) B2105057
theorem B1403383 : Blo 1401520 1403383 := bstep (se 1 (by rfl) ⟨1052537, by rfl⟩ : syracuseStep 1403383 = 2105075) B2105075
theorem B1403403 : Blo 1401520 1403403 := bstep (se 1 (by rfl) ⟨1052552, by rfl⟩ : syracuseStep 1403403 = 2105105) B2105105
theorem B1403415 : Blo 1401520 1403415 := bstep (se 1 (by rfl) ⟨1052561, by rfl⟩ : syracuseStep 1403415 = 2105123) B2105123
theorem B1403435 : Blo 1401520 1403435 := bstep (se 1 (by rfl) ⟨1052576, by rfl⟩ : syracuseStep 1403435 = 2105153) B2105153
theorem B1403447 : Blo 1401520 1403447 := bstep (se 1 (by rfl) ⟨1052585, by rfl⟩ : syracuseStep 1403447 = 2105171) B2105171
theorem B1403467 : Blo 1401520 1403467 := bstep (se 1 (by rfl) ⟨1052600, by rfl⟩ : syracuseStep 1403467 = 2105201) B2105201
theorem B1403479 : Blo 1401520 1403479 := bstep (se 1 (by rfl) ⟨1052609, by rfl⟩ : syracuseStep 1403479 = 2105219) B2105219
theorem B2132569 : Blo 1401520 2132569 := bstep (se 2 (by rfl) ⟨799713, by rfl⟩ : syracuseStep 2132569 = 1599427) B1599427
theorem B3156569 : Blo 1401520 3156569 := bstep (se 2 (by rfl) ⟨1183713, by rfl⟩ : syracuseStep 3156569 = 2367427) B2367427
theorem B1403499 : Blo 1401520 1403499 := bstep (se 1 (by rfl) ⟨1052624, by rfl⟩ : syracuseStep 1403499 = 2105249) B2105249
theorem B1403511 : Blo 1401520 1403511 := bstep (se 1 (by rfl) ⟨1052633, by rfl⟩ : syracuseStep 1403511 = 2105267) B2105267
theorem B3197569 : Blo 1401520 3197569 := bstep (se 2 (by rfl) ⟨1199088, by rfl⟩ : syracuseStep 3197569 = 2398177) B2398177
theorem B8096435 : Blo 1401520 8096435 := bstep (se 1 (by rfl) ⟨6072326, by rfl⟩ : syracuseStep 8096435 = 12144653) B12144653
theorem B3156659 : Blo 1401520 3156659 := bstep (se 1 (by rfl) ⟨2367494, by rfl⟩ : syracuseStep 3156659 = 4734989) B4734989
theorem B3992267 : Blo 1401520 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B3156695 : Blo 1401520 3156695 := bstep (se 1 (by rfl) ⟨2367521, by rfl⟩ : syracuseStep 3156695 = 4735043) B4735043
theorem B5991185 : Blo 1401520 5991185 := bstep (se 2 (by rfl) ⟨2246694, by rfl⟩ : syracuseStep 5991185 = 4493389) B4493389
theorem B5327639 : Blo 1401520 5327639 := bstep (se 1 (by rfl) ⟨3995729, by rfl⟩ : syracuseStep 5327639 = 7991459) B7991459
theorem B3550027 : Blo 1401520 3550027 := bstep (se 1 (by rfl) ⟨2662520, by rfl⟩ : syracuseStep 3550027 = 5325041) B5325041
theorem B7097219 : Blo 1401520 7097219 := bstep (se 1 (by rfl) ⟨5322914, by rfl⟩ : syracuseStep 7097219 = 10645829) B10645829
theorem B3156875 : Blo 1401520 3156875 := bstep (se 1 (by rfl) ⟨2367656, by rfl⟩ : syracuseStep 3156875 = 4735313) B4735313
theorem B3156929 : Blo 1401520 3156929 := bstep (se 2 (by rfl) ⟨1183848, by rfl⟩ : syracuseStep 3156929 = 2367697) B2367697
theorem B4492235 : Blo 1401520 4492235 := bstep (se 1 (by rfl) ⟨3369176, by rfl⟩ : syracuseStep 4492235 = 6738353) B6738353
theorem B3550169 : Blo 1401520 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B10652633 : Blo 1401520 10652633 := bstep (se 2 (by rfl) ⟨3994737, by rfl⟩ : syracuseStep 10652633 = 7989475) B7989475
theorem B1518635 : Blo 1401520 1518635 := bstep (se 1 (by rfl) ⟨1138976, by rfl⟩ : syracuseStep 1518635 = 2277953) B2277953
theorem B3992665 : Blo 1401520 3992665 := bstep (se 2 (by rfl) ⟨1497249, by rfl⟩ : syracuseStep 3992665 = 2994499) B2994499
theorem B3157145 : Blo 1401520 3157145 := bstep (se 2 (by rfl) ⟨1183929, by rfl⟩ : syracuseStep 3157145 = 2367859) B2367859
theorem B3157235 : Blo 1401520 3157235 := bstep (se 1 (by rfl) ⟨2367926, by rfl⟩ : syracuseStep 3157235 = 4735853) B4735853
theorem B19721477 : Blo 1401520 19721477 := bstep (se 4 (by rfl) ⟨1848888, by rfl⟩ : syracuseStep 19721477 = 3697777) B3697777
theorem B3157271 : Blo 1401520 3157271 := bstep (se 1 (by rfl) ⟨2367953, by rfl⟩ : syracuseStep 3157271 = 4735907) B4735907
theorem B22736173 : Blo 1401520 22736173 := bstep (se 3 (by rfl) ⟨4263032, by rfl⟩ : syracuseStep 22736173 = 8526065) B8526065
theorem B6393239 : Blo 1401520 6393239 := bstep (se 1 (by rfl) ⟨4794929, by rfl⟩ : syracuseStep 6393239 = 9589859) B9589859
theorem B1895833 : Blo 1401520 1895833 := bstep (se 2 (by rfl) ⟨710937, by rfl⟩ : syracuseStep 1895833 = 1421875) B1421875
theorem B4730291 : Blo 1401520 4730291 := bstep (se 1 (by rfl) ⟨3547718, by rfl⟩ : syracuseStep 4730291 = 7095437) B7095437
theorem B2993611 : Blo 1401520 2993611 := bstep (se 1 (by rfl) ⟨2245208, by rfl⟩ : syracuseStep 2993611 = 4490417) B4490417
theorem B3157451 : Blo 1401520 3157451 := bstep (se 1 (by rfl) ⟨2368088, by rfl⟩ : syracuseStep 3157451 = 4736177) B4736177
theorem B23965145 : Blo 1401520 23965145 := bstep (se 2 (by rfl) ⟨8986929, by rfl⟩ : syracuseStep 23965145 = 17973859) B17973859
theorem B3157505 : Blo 1401520 3157505 := bstep (se 2 (by rfl) ⟨1184064, by rfl⟩ : syracuseStep 3157505 = 2368129) B2368129
theorem B31157777 : Blo 1401520 31157777 := bstep (se 2 (by rfl) ⟨11684166, by rfl⟩ : syracuseStep 31157777 = 23368333) B23368333
theorem B3599923 : Blo 1401520 3599923 := bstep (se 1 (by rfl) ⟨2699942, by rfl⟩ : syracuseStep 3599923 = 5399885) B5399885
theorem B4492979 : Blo 1401520 4492979 := bstep (se 1 (by rfl) ⟨3369734, by rfl⟩ : syracuseStep 4492979 = 6739469) B6739469
theorem B4730561 : Blo 1401520 4730561 := bstep (se 2 (by rfl) ⟨1773960, by rfl⟩ : syracuseStep 4730561 = 3547921) B3547921
theorem B5689025 : Blo 1401520 5689025 := bstep (se 2 (by rfl) ⟨2133384, by rfl⟩ : syracuseStep 5689025 = 4266769) B4266769
theorem B5058251 : Blo 1401520 5058251 := bstep (se 1 (by rfl) ⟨3793688, by rfl⟩ : syracuseStep 5058251 = 7587377) B7587377
theorem B3157721 : Blo 1401520 3157721 := bstep (se 2 (by rfl) ⟨1184145, by rfl⟩ : syracuseStep 3157721 = 2368291) B2368291
theorem B3550999 : Blo 1401520 3550999 := bstep (se 1 (by rfl) ⟨2663249, by rfl⟩ : syracuseStep 3550999 = 5326499) B5326499
theorem B3157811 : Blo 1401520 3157811 := bstep (se 1 (by rfl) ⟨2368358, by rfl⟩ : syracuseStep 3157811 = 4736717) B4736717
theorem B1576759 : Blo 1401520 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B3157847 : Blo 1401520 3157847 := bstep (se 1 (by rfl) ⟨2368385, by rfl⟩ : syracuseStep 3157847 = 4736771) B4736771
theorem B20213621 : Blo 1401520 20213621 := bstep (se 5 (by rfl) ⟨947513, by rfl⟩ : syracuseStep 20213621 = 1895027) B1895027
theorem B1576939 : Blo 1401520 1576939 := bstep (se 1 (by rfl) ⟨1182704, by rfl⟩ : syracuseStep 1576939 = 2365409) B2365409
theorem B5328899 : Blo 1401520 5328899 := bstep (se 1 (by rfl) ⟨3996674, by rfl⟩ : syracuseStep 5328899 = 7993349) B7993349
theorem B3788875 : Blo 1401520 3788875 := bstep (se 1 (by rfl) ⟨2841656, by rfl⟩ : syracuseStep 3788875 = 5683313) B5683313
theorem B1577047 : Blo 1401520 1577047 := bstep (se 1 (by rfl) ⟨1182785, by rfl⟩ : syracuseStep 1577047 = 2365571) B2365571
theorem B3551435 : Blo 1401520 3551435 := bstep (se 1 (by rfl) ⟨2663576, by rfl⟩ : syracuseStep 3551435 = 5327153) B5327153
theorem B4731101 : Blo 1401520 4731101 := bstep (se 3 (by rfl) ⟨887081, by rfl⟩ : syracuseStep 4731101 = 1774163) B1774163
theorem B1577227 : Blo 1401520 1577227 := bstep (se 1 (by rfl) ⟨1182920, by rfl⟩ : syracuseStep 1577227 = 2365841) B2365841
theorem B8982829 : Blo 1401520 8982829 := bstep (se 3 (by rfl) ⟨1684280, by rfl⟩ : syracuseStep 8982829 = 3368561) B3368561
theorem B3993907 : Blo 1401520 3993907 := bstep (se 1 (by rfl) ⟨2995430, by rfl⟩ : syracuseStep 3993907 = 5990861) B5990861
theorem B3371329 : Blo 1401520 3371329 := bstep (se 2 (by rfl) ⟨1264248, by rfl⟩ : syracuseStep 3371329 = 2528497) B2528497
theorem B7983461 : Blo 1401520 7983461 := bstep (se 4 (by rfl) ⟨748449, by rfl⟩ : syracuseStep 7983461 = 1496899) B1496899
theorem B1577335 : Blo 1401520 1577335 := bstep (se 1 (by rfl) ⟨1183001, by rfl⟩ : syracuseStep 1577335 = 2366003) B2366003
theorem B34132373 : Blo 1401520 34132373 := bstep (se 6 (by rfl) ⟨799977, by rfl⟩ : syracuseStep 34132373 = 1599955) B1599955
theorem B1577515 : Blo 1401520 1577515 := bstep (se 1 (by rfl) ⟨1183136, by rfl⟩ : syracuseStep 1577515 = 2366273) B2366273
theorem B4493875 : Blo 1401520 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B3551809 : Blo 1401520 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B1774219 : Blo 1401520 1774219 := bstep (se 1 (by rfl) ⟨1330664, by rfl⟩ : syracuseStep 1774219 = 2661329) B2661329
theorem B1577623 : Blo 1401520 1577623 := bstep (se 1 (by rfl) ⟨1183217, by rfl⟩ : syracuseStep 1577623 = 2366435) B2366435
theorem B1921687 : Blo 1401520 1921687 := bstep (se 1 (by rfl) ⟨1441265, by rfl⟩ : syracuseStep 1921687 = 2882531) B2882531
theorem B7983917 : Blo 1401520 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B2994995 : Blo 1401520 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B1577803 : Blo 1401520 1577803 := bstep (se 1 (by rfl) ⟨1183352, by rfl⟩ : syracuseStep 1577803 = 2366705) B2366705
theorem B3789719 : Blo 1401520 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B1774487 : Blo 1401520 1774487 := bstep (se 1 (by rfl) ⟨1330865, by rfl⟩ : syracuseStep 1774487 = 2661731) B2661731
theorem B1577911 : Blo 1401520 1577911 := bstep (se 1 (by rfl) ⟨1183433, by rfl⟩ : syracuseStep 1577911 = 2366867) B2366867
theorem B2102297 : Blo 1401520 2102297 := bstep (se 2 (by rfl) ⟨788361, by rfl⟩ : syracuseStep 2102297 = 1576723) B1576723
theorem B5321821 : Blo 1401520 5321821 := bstep (se 3 (by rfl) ⟨997841, by rfl⟩ : syracuseStep 5321821 = 1995683) B1995683
theorem B12792925 : Blo 1401520 12792925 := bstep (se 3 (by rfl) ⟨2398673, by rfl⟩ : syracuseStep 12792925 = 4797347) B4797347
theorem B1578091 : Blo 1401520 1578091 := bstep (se 1 (by rfl) ⟨1183568, by rfl⟩ : syracuseStep 1578091 = 2367137) B2367137
theorem B2102411 : Blo 1401520 2102411 := bstep (se 1 (by rfl) ⟨1576808, by rfl⟩ : syracuseStep 2102411 = 3153617) B3153617
theorem B5764241 : Blo 1401520 5764241 := bstep (se 2 (by rfl) ⟨2161590, by rfl⟩ : syracuseStep 5764241 = 4323181) B4323181
theorem B2102423 : Blo 1401520 2102423 := bstep (se 1 (by rfl) ⟨1576817, by rfl⟩ : syracuseStep 2102423 = 3153635) B3153635
theorem B3552407 : Blo 1401520 3552407 := bstep (se 1 (by rfl) ⟨2664305, by rfl⟩ : syracuseStep 3552407 = 5328611) B5328611
theorem B1578199 : Blo 1401520 1578199 := bstep (se 1 (by rfl) ⟨1183649, by rfl⟩ : syracuseStep 1578199 = 2367299) B2367299
theorem B2102489 : Blo 1401520 2102489 := bstep (se 2 (by rfl) ⟨788433, by rfl⟩ : syracuseStep 2102489 = 1576867) B1576867
theorem B10646801 : Blo 1401520 10646801 := bstep (se 2 (by rfl) ⟨3992550, by rfl⟩ : syracuseStep 10646801 = 7985101) B7985101
theorem B5690675 : Blo 1401520 5690675 := bstep (se 1 (by rfl) ⟨4268006, by rfl⟩ : syracuseStep 5690675 = 8536013) B8536013
theorem B2102603 : Blo 1401520 2102603 := bstep (se 1 (by rfl) ⟨1576952, by rfl⟩ : syracuseStep 2102603 = 3153905) B3153905
theorem B4732235 : Blo 1401520 4732235 := bstep (se 1 (by rfl) ⟨3549176, by rfl⟩ : syracuseStep 4732235 = 7098353) B7098353
theorem B2102615 : Blo 1401520 2102615 := bstep (se 1 (by rfl) ⟨1576961, by rfl⟩ : syracuseStep 2102615 = 3153923) B3153923
theorem B1578379 : Blo 1401520 1578379 := bstep (se 1 (by rfl) ⟨1183784, by rfl⟩ : syracuseStep 1578379 = 2367569) B2367569
theorem B2102681 : Blo 1401520 2102681 := bstep (se 2 (by rfl) ⟨788505, by rfl⟩ : syracuseStep 2102681 = 1577011) B1577011
theorem B11974067 : Blo 1401520 11974067 := bstep (se 1 (by rfl) ⟨8980550, by rfl⟩ : syracuseStep 11974067 = 17961101) B17961101
theorem B7984601 : Blo 1401520 7984601 := bstep (se 2 (by rfl) ⟨2994225, by rfl⟩ : syracuseStep 7984601 = 5988451) B5988451
theorem B5846489 : Blo 1401520 5846489 := bstep (se 2 (by rfl) ⟨2192433, by rfl⟩ : syracuseStep 5846489 = 4384867) B4384867
theorem B1578487 : Blo 1401520 1578487 := bstep (se 1 (by rfl) ⟨1183865, by rfl⟩ : syracuseStep 1578487 = 2367731) B2367731
theorem B2102795 : Blo 1401520 2102795 := bstep (se 1 (by rfl) ⟨1577096, by rfl⟩ : syracuseStep 2102795 = 3154193) B3154193
theorem B2102807 : Blo 1401520 2102807 := bstep (se 1 (by rfl) ⟨1577105, by rfl⟩ : syracuseStep 2102807 = 3154211) B3154211
theorem B20502085 : Blo 1401520 20502085 := bstep (se 4 (by rfl) ⟨1922070, by rfl⟩ : syracuseStep 20502085 = 3844141) B3844141
theorem B1480279 : Blo 1401520 1480279 := bstep (se 1 (by rfl) ⟨1110209, by rfl⟩ : syracuseStep 1480279 = 2220419) B2220419
theorem B1775191 : Blo 1401520 1775191 := bstep (se 1 (by rfl) ⟨1331393, by rfl⟩ : syracuseStep 1775191 = 2662787) B2662787
theorem B2102873 : Blo 1401520 2102873 := bstep (se 2 (by rfl) ⟨788577, by rfl⟩ : syracuseStep 2102873 = 1577155) B1577155
theorem B4732505 : Blo 1401520 4732505 := bstep (se 2 (by rfl) ⟨1774689, by rfl⟩ : syracuseStep 4732505 = 3549379) B3549379
theorem B11982437 : Blo 1401520 11982437 := bstep (se 4 (by rfl) ⟨1123353, by rfl⟩ : syracuseStep 11982437 = 2246707) B2246707
theorem B2995841 : Blo 1401520 2995841 := bstep (se 2 (by rfl) ⟨1123440, by rfl⟩ : syracuseStep 2995841 = 2246881) B2246881
theorem B1578667 : Blo 1401520 1578667 := bstep (se 1 (by rfl) ⟨1184000, by rfl⟩ : syracuseStep 1578667 = 2368001) B2368001
theorem B5994157 : Blo 1401520 5994157 := bstep (se 3 (by rfl) ⟨1123904, by rfl⟩ : syracuseStep 5994157 = 2247809) B2247809
theorem B10114739 : Blo 1401520 10114739 := bstep (se 1 (by rfl) ⟨7586054, by rfl⟩ : syracuseStep 10114739 = 15172109) B15172109
theorem B2102987 : Blo 1401520 2102987 := bstep (se 1 (by rfl) ⟨1577240, by rfl⟩ : syracuseStep 2102987 = 3154481) B3154481
theorem B2102999 : Blo 1401520 2102999 := bstep (se 1 (by rfl) ⟨1577249, by rfl⟩ : syracuseStep 2102999 = 3154499) B3154499
theorem B1578775 : Blo 1401520 1578775 := bstep (se 1 (by rfl) ⟨1184081, by rfl⟩ : syracuseStep 1578775 = 2368163) B2368163
theorem B2103065 : Blo 1401520 2103065 := bstep (se 2 (by rfl) ⟨788649, by rfl⟩ : syracuseStep 2103065 = 1577299) B1577299
theorem B2103179 : Blo 1401520 2103179 := bstep (se 1 (by rfl) ⟨1577384, by rfl⟩ : syracuseStep 2103179 = 3154769) B3154769
theorem B2103191 : Blo 1401520 2103191 := bstep (se 1 (by rfl) ⟨1577393, by rfl⟩ : syracuseStep 2103191 = 3154787) B3154787
theorem B1996697 : Blo 1401520 1996697 := bstep (se 2 (by rfl) ⟨748761, by rfl⟩ : syracuseStep 1996697 = 1497523) B1497523
theorem B3200971 : Blo 1401520 3200971 := bstep (se 1 (by rfl) ⟨2400728, by rfl⟩ : syracuseStep 3200971 = 4801457) B4801457
theorem B1578955 : Blo 1401520 1578955 := bstep (se 1 (by rfl) ⟨1184216, by rfl⟩ : syracuseStep 1578955 = 2368433) B2368433
theorem B2996183 : Blo 1401520 2996183 := bstep (se 1 (by rfl) ⟨2247137, by rfl⟩ : syracuseStep 2996183 = 4494275) B4494275
theorem B2103257 : Blo 1401520 2103257 := bstep (se 2 (by rfl) ⟨788721, by rfl⟩ : syracuseStep 2103257 = 1577443) B1577443
theorem B1497079 : Blo 1401520 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B5994499 : Blo 1401520 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B6395921 : Blo 1401520 6395921 := bstep (se 2 (by rfl) ⟨2398470, by rfl⟩ : syracuseStep 6395921 = 4796941) B4796941
theorem B2365463 : Blo 1401520 2365463 := bstep (se 1 (by rfl) ⟨1774097, by rfl⟩ : syracuseStep 2365463 = 3548195) B3548195
theorem B10115117 : Blo 1401520 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B2103371 : Blo 1401520 2103371 := bstep (se 1 (by rfl) ⟨1577528, by rfl⟩ : syracuseStep 2103371 = 3155057) B3155057
theorem B184440907 : Blo 1401520 184440907 := bstep (se 1 (by rfl) ⟨138330680, by rfl⟩ : syracuseStep 184440907 = 276661361) B276661361
theorem B2103383 : Blo 1401520 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B9599077 : Blo 1401520 9599077 := bstep (se 4 (by rfl) ⟨899913, by rfl⟩ : syracuseStep 9599077 = 1799827) B1799827
theorem B3037313 : Blo 1401520 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B2365591 : Blo 1401520 2365591 := bstep (se 1 (by rfl) ⟨1774193, by rfl⟩ : syracuseStep 2365591 = 3548387) B3548387
theorem B2308247 : Blo 1401520 2308247 := bstep (se 1 (by rfl) ⟨1731185, by rfl⟩ : syracuseStep 2308247 = 3462371) B3462371
theorem B2103449 : Blo 1401520 2103449 := bstep (se 2 (by rfl) ⟨788793, by rfl⟩ : syracuseStep 2103449 = 1577587) B1577587
theorem B2103563 : Blo 1401520 2103563 := bstep (se 1 (by rfl) ⟨1577672, by rfl⟩ : syracuseStep 2103563 = 3155345) B3155345
theorem B2103575 : Blo 1401520 2103575 := bstep (se 1 (by rfl) ⟨1577681, by rfl⟩ : syracuseStep 2103575 = 3155363) B3155363
theorem B4733207 : Blo 1401520 4733207 := bstep (se 1 (by rfl) ⟨3549905, by rfl⟩ : syracuseStep 4733207 = 7099811) B7099811
theorem B10656035 : Blo 1401520 10656035 := bstep (se 1 (by rfl) ⟨7992026, by rfl⟩ : syracuseStep 10656035 = 15984053) B15984053
theorem B5323097 : Blo 1401520 5323097 := bstep (se 2 (by rfl) ⟨1996161, by rfl⟩ : syracuseStep 5323097 = 3992323) B3992323
theorem B2103641 : Blo 1401520 2103641 := bstep (se 2 (by rfl) ⟨788865, by rfl⟩ : syracuseStep 2103641 = 1577731) B1577731
theorem B2660759 : Blo 1401520 2660759 := bstep (se 1 (by rfl) ⟨1995569, by rfl⟩ : syracuseStep 2660759 = 3991139) B3991139
theorem B2103755 : Blo 1401520 2103755 := bstep (se 1 (by rfl) ⟨1577816, by rfl⟩ : syracuseStep 2103755 = 3155633) B3155633
theorem B2103767 : Blo 1401520 2103767 := bstep (se 1 (by rfl) ⟨1577825, by rfl⟩ : syracuseStep 2103767 = 3155651) B3155651
theorem B7100945 : Blo 1401520 7100945 := bstep (se 2 (by rfl) ⟨2662854, by rfl⟩ : syracuseStep 7100945 = 5325709) B5325709
theorem B1997335 : Blo 1401520 1997335 := bstep (se 1 (by rfl) ⟨1498001, by rfl⟩ : syracuseStep 1997335 = 2996003) B2996003
theorem B2103833 : Blo 1401520 2103833 := bstep (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) B1577875
theorem B2103947 : Blo 1401520 2103947 := bstep (se 1 (by rfl) ⟨1577960, by rfl⟩ : syracuseStep 2103947 = 3155921) B3155921
theorem B23952023 : Blo 1401520 23952023 := bstep (se 1 (by rfl) ⟨17964017, by rfl⟩ : syracuseStep 23952023 = 35928035) B35928035
theorem B2103959 : Blo 1401520 2103959 := bstep (se 1 (by rfl) ⟨1577969, by rfl⟩ : syracuseStep 2103959 = 3155939) B3155939
theorem B7101107 : Blo 1401520 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B2104025 : Blo 1401520 2104025 := bstep (se 2 (by rfl) ⟨789009, by rfl⟩ : syracuseStep 2104025 = 1578019) B1578019
theorem B2366219 : Blo 1401520 2366219 := bstep (se 1 (by rfl) ⟨1774664, by rfl⟩ : syracuseStep 2366219 = 3549329) B3549329
theorem B1497899 : Blo 1401520 1497899 := bstep (se 1 (by rfl) ⟨1123424, by rfl⟩ : syracuseStep 1497899 = 2246849) B2246849
theorem B4733747 : Blo 1401520 4733747 := bstep (se 1 (by rfl) ⟨3550310, by rfl⟩ : syracuseStep 4733747 = 7100621) B7100621
theorem B2104139 : Blo 1401520 2104139 := bstep (se 1 (by rfl) ⟨1578104, by rfl⟩ : syracuseStep 2104139 = 3156209) B3156209
theorem B2104151 : Blo 1401520 2104151 := bstep (se 1 (by rfl) ⟨1578113, by rfl⟩ : syracuseStep 2104151 = 3156227) B3156227
theorem B2366347 : Blo 1401520 2366347 := bstep (se 1 (by rfl) ⟨1774760, by rfl⟩ : syracuseStep 2366347 = 3549521) B3549521
theorem B2104217 : Blo 1401520 2104217 := bstep (se 2 (by rfl) ⟨789081, by rfl⟩ : syracuseStep 2104217 = 1578163) B1578163
theorem B2104331 : Blo 1401520 2104331 := bstep (se 1 (by rfl) ⟨1578248, by rfl⟩ : syracuseStep 2104331 = 3156497) B3156497
theorem B2104343 : Blo 1401520 2104343 := bstep (se 1 (by rfl) ⟨1578257, by rfl⟩ : syracuseStep 2104343 = 3156515) B3156515
theorem B2366489 : Blo 1401520 2366489 := bstep (se 2 (by rfl) ⟨887433, by rfl⟩ : syracuseStep 2366489 = 1774867) B1774867
theorem B2661427 : Blo 1401520 2661427 := bstep (se 1 (by rfl) ⟨1996070, by rfl⟩ : syracuseStep 2661427 = 3992141) B3992141
theorem B4734017 : Blo 1401520 4734017 := bstep (se 2 (by rfl) ⟨1775256, by rfl⟩ : syracuseStep 4734017 = 3550513) B3550513
theorem B9600065 : Blo 1401520 9600065 := bstep (se 2 (by rfl) ⟨3600024, by rfl⟩ : syracuseStep 9600065 = 7200049) B7200049
theorem B2104409 : Blo 1401520 2104409 := bstep (se 2 (by rfl) ⟨789153, by rfl⟩ : syracuseStep 2104409 = 1578307) B1578307
theorem B5987459 : Blo 1401520 5987459 := bstep (se 1 (by rfl) ⟨4490594, by rfl⟩ : syracuseStep 5987459 = 8981189) B8981189
theorem B2366617 : Blo 1401520 2366617 := bstep (se 2 (by rfl) ⟨887481, by rfl⟩ : syracuseStep 2366617 = 1774963) B1774963
theorem B2104523 : Blo 1401520 2104523 := bstep (se 1 (by rfl) ⟨1578392, by rfl⟩ : syracuseStep 2104523 = 3156785) B3156785
theorem B2104535 : Blo 1401520 2104535 := bstep (se 1 (by rfl) ⟨1578401, by rfl⟩ : syracuseStep 2104535 = 3156803) B3156803
theorem B2661655 : Blo 1401520 2661655 := bstep (se 1 (by rfl) ⟨1996241, by rfl⟩ : syracuseStep 2661655 = 3992483) B3992483
theorem B2104601 : Blo 1401520 2104601 := bstep (se 2 (by rfl) ⟨789225, by rfl⟩ : syracuseStep 2104601 = 1578451) B1578451
theorem B11369803 : Blo 1401520 11369803 := bstep (se 1 (by rfl) ⟨8527352, by rfl⟩ : syracuseStep 11369803 = 17054705) B17054705
theorem B1998155 : Blo 1401520 1998155 := bstep (se 1 (by rfl) ⟨1498616, by rfl⟩ : syracuseStep 1998155 = 2997233) B2997233
theorem B2661761 : Blo 1401520 2661761 := bstep (se 2 (by rfl) ⟨998160, by rfl⟩ : syracuseStep 2661761 = 1996321) B1996321
theorem B2104715 : Blo 1401520 2104715 := bstep (se 1 (by rfl) ⟨1578536, by rfl⟩ : syracuseStep 2104715 = 3157073) B3157073
theorem B2104727 : Blo 1401520 2104727 := bstep (se 1 (by rfl) ⟨1578545, by rfl⟩ : syracuseStep 2104727 = 3157091) B3157091
theorem B11369933 : Blo 1401520 11369933 := bstep (se 3 (by rfl) ⟨2131862, by rfl⟩ : syracuseStep 11369933 = 4263725) B4263725
theorem B2104793 : Blo 1401520 2104793 := bstep (se 2 (by rfl) ⟨789297, by rfl⟩ : syracuseStep 2104793 = 1578595) B1578595
theorem B7192081 : Blo 1401520 7192081 := bstep (se 2 (by rfl) ⟨2697030, by rfl⟩ : syracuseStep 7192081 = 5394061) B5394061
theorem B2661913 : Blo 1401520 2661913 := bstep (se 2 (by rfl) ⟨998217, by rfl⟩ : syracuseStep 2661913 = 1996435) B1996435
theorem B10108451 : Blo 1401520 10108451 := bstep (se 1 (by rfl) ⟨7581338, by rfl⟩ : syracuseStep 10108451 = 15162677) B15162677
theorem B3153473 : Blo 1401520 3153473 := bstep (se 2 (by rfl) ⟨1182552, by rfl⟩ : syracuseStep 3153473 = 2365105) B2365105
theorem B2104907 : Blo 1401520 2104907 := bstep (se 1 (by rfl) ⟨1578680, by rfl⟩ : syracuseStep 2104907 = 3157361) B3157361
theorem B2104919 : Blo 1401520 2104919 := bstep (se 1 (by rfl) ⟨1578689, by rfl⟩ : syracuseStep 2104919 = 3157379) B3157379
theorem B4734557 : Blo 1401520 4734557 := bstep (se 3 (by rfl) ⟨887729, by rfl⟩ : syracuseStep 4734557 = 1775459) B1775459
theorem B2104985 : Blo 1401520 2104985 := bstep (se 2 (by rfl) ⟨789369, by rfl⟩ : syracuseStep 2104985 = 1578739) B1578739
theorem B2367191 : Blo 1401520 2367191 := bstep (se 1 (by rfl) ⟨1775393, by rfl⟩ : syracuseStep 2367191 = 3550787) B3550787
theorem B2105099 : Blo 1401520 2105099 := bstep (se 1 (by rfl) ⟨1578824, by rfl⟩ : syracuseStep 2105099 = 3157649) B3157649
theorem B2105111 : Blo 1401520 2105111 := bstep (se 1 (by rfl) ⟨1578833, by rfl⟩ : syracuseStep 2105111 = 3157667) B3157667
theorem B3153689 : Blo 1401520 3153689 := bstep (se 2 (by rfl) ⟨1182633, by rfl⟩ : syracuseStep 3153689 = 2365267) B2365267
theorem B2367319 : Blo 1401520 2367319 := bstep (se 1 (by rfl) ⟨1775489, by rfl⟩ : syracuseStep 2367319 = 3550979) B3550979
theorem B2105177 : Blo 1401520 2105177 := bstep (se 2 (by rfl) ⟨789441, by rfl⟩ : syracuseStep 2105177 = 1578883) B1578883
theorem B7298909 : Blo 1401520 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B3153779 : Blo 1401520 3153779 := bstep (se 1 (by rfl) ⟨2365334, by rfl⟩ : syracuseStep 3153779 = 4730669) B4730669
theorem B3153815 : Blo 1401520 3153815 := bstep (se 1 (by rfl) ⟨2365361, by rfl⟩ : syracuseStep 3153815 = 4730723) B4730723
theorem B5324723 : Blo 1401520 5324723 := bstep (se 1 (by rfl) ⟨3993542, by rfl⟩ : syracuseStep 5324723 = 7987085) B7987085
theorem B5324737 : Blo 1401520 5324737 := bstep (se 2 (by rfl) ⟨1996776, by rfl⟩ : syracuseStep 5324737 = 3993553) B3993553
theorem B2367623 : Blo 1401520 2367623 := bstep (se 1 (by rfl) ⟨1775717, by rfl⟩ : syracuseStep 2367623 = 3551435) B3551435
theorem B3154067 : Blo 1401520 3154067 := bstep (se 1 (by rfl) ⟨2365550, by rfl⟩ : syracuseStep 3154067 = 4731101) B4731101
theorem B2162873 : Blo 1401520 2162873 := bstep (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) B1622155
theorem B3154121 : Blo 1401520 3154121 := bstep (se 2 (by rfl) ⟨1182795, by rfl⟩ : syracuseStep 3154121 = 2365591) B2365591
theorem B4325647 : Blo 1401520 4325647 := bstep (se 1 (by rfl) ⟨3244235, by rfl⟩ : syracuseStep 4325647 = 6488471) B6488471
theorem B15966557 : Blo 1401520 15966557 := bstep (se 3 (by rfl) ⟨2993729, by rfl⟩ : syracuseStep 15966557 = 5987459) B5987459
theorem B4735367 : Blo 1401520 4735367 := bstep (se 1 (by rfl) ⟨3551525, by rfl⟩ : syracuseStep 4735367 = 7103051) B7103051
theorem B11977105 : Blo 1401520 11977105 := bstep (se 2 (by rfl) ⟨4491414, by rfl⟩ : syracuseStep 11977105 = 8982829) B8982829
theorem B5325209 : Blo 1401520 5325209 := bstep (se 2 (by rfl) ⟨1996953, by rfl⟩ : syracuseStep 5325209 = 3993907) B3993907
theorem B1401531 : Blo 1401520 1401531 := bstep (se 1 (by rfl) ⟨1051148, by rfl⟩ : syracuseStep 1401531 = 2102297) B2102297
theorem B2663113 : Blo 1401520 2663113 := bstep (se 2 (by rfl) ⟨998667, by rfl⟩ : syracuseStep 2663113 = 1997335) B1997335
theorem B7103213 : Blo 1401520 7103213 := bstep (se 3 (by rfl) ⟨1331852, by rfl⟩ : syracuseStep 7103213 = 2663705) B2663705
theorem B4735745 : Blo 1401520 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B1401607 : Blo 1401520 1401607 := bstep (se 1 (by rfl) ⟨1051205, by rfl⟩ : syracuseStep 1401607 = 2102411) B2102411
theorem B1401615 : Blo 1401520 1401615 := bstep (se 1 (by rfl) ⟨1051211, by rfl⟩ : syracuseStep 1401615 = 2102423) B2102423
theorem B2368271 : Blo 1401520 2368271 := bstep (se 1 (by rfl) ⟨1776203, by rfl⟩ : syracuseStep 2368271 = 3552407) B3552407
theorem B2843425 : Blo 1401520 2843425 := bstep (se 2 (by rfl) ⟨1066284, by rfl⟩ : syracuseStep 2843425 = 2132569) B2132569
theorem B1401659 : Blo 1401520 1401659 := bstep (se 1 (by rfl) ⟨1051244, by rfl⟩ : syracuseStep 1401659 = 2102489) B2102489
theorem B1401735 : Blo 1401520 1401735 := bstep (se 1 (by rfl) ⟨1051301, by rfl⟩ : syracuseStep 1401735 = 2102603) B2102603
theorem B3154823 : Blo 1401520 3154823 := bstep (se 1 (by rfl) ⟨2366117, by rfl⟩ : syracuseStep 3154823 = 4732235) B4732235
theorem B1401743 : Blo 1401520 1401743 := bstep (se 1 (by rfl) ⟨1051307, by rfl⟩ : syracuseStep 1401743 = 2102615) B2102615
theorem B1401787 : Blo 1401520 1401787 := bstep (se 1 (by rfl) ⟨1051340, by rfl⟩ : syracuseStep 1401787 = 2102681) B2102681
theorem B1401863 : Blo 1401520 1401863 := bstep (se 1 (by rfl) ⟨1051397, by rfl⟩ : syracuseStep 1401863 = 2102795) B2102795
theorem B1401871 : Blo 1401520 1401871 := bstep (se 1 (by rfl) ⟨1051403, by rfl⟩ : syracuseStep 1401871 = 2102807) B2102807
theorem B1401915 : Blo 1401520 1401915 := bstep (se 1 (by rfl) ⟨1051436, by rfl⟩ : syracuseStep 1401915 = 2102873) B2102873
theorem B3155003 : Blo 1401520 3155003 := bstep (se 1 (by rfl) ⟨2366252, by rfl⟩ : syracuseStep 3155003 = 4732505) B4732505
theorem B7988291 : Blo 1401520 7988291 := bstep (se 1 (by rfl) ⟨5991218, by rfl⟩ : syracuseStep 7988291 = 11982437) B11982437
theorem B3949687 : Blo 1401520 3949687 := bstep (se 1 (by rfl) ⟨2962265, by rfl⟩ : syracuseStep 3949687 = 5924531) B5924531
theorem B6743159 : Blo 1401520 6743159 := bstep (se 1 (by rfl) ⟨5057369, by rfl⟩ : syracuseStep 6743159 = 10114739) B10114739
theorem B1401991 : Blo 1401520 1401991 := bstep (se 1 (by rfl) ⟨1051493, by rfl⟩ : syracuseStep 1401991 = 2102987) B2102987
theorem B1401999 : Blo 1401520 1401999 := bstep (se 1 (by rfl) ⟨1051499, by rfl⟩ : syracuseStep 1401999 = 2102999) B2102999
theorem B3155129 : Blo 1401520 3155129 := bstep (se 2 (by rfl) ⟨1183173, by rfl⟩ : syracuseStep 3155129 = 2366347) B2366347
theorem B1402043 : Blo 1401520 1402043 := bstep (se 1 (by rfl) ⟨1051532, by rfl⟩ : syracuseStep 1402043 = 2103065) B2103065
theorem B1402119 : Blo 1401520 1402119 := bstep (se 1 (by rfl) ⟨1051589, by rfl⟩ : syracuseStep 1402119 = 2103179) B2103179
theorem B1402127 : Blo 1401520 1402127 := bstep (se 1 (by rfl) ⟨1051595, by rfl⟩ : syracuseStep 1402127 = 2103191) B2103191
theorem B6735163 : Blo 1401520 6735163 := bstep (se 1 (by rfl) ⟨5051372, by rfl⟩ : syracuseStep 6735163 = 10102745) B10102745
theorem B1402171 : Blo 1401520 1402171 := bstep (se 1 (by rfl) ⟨1051628, by rfl⟩ : syracuseStep 1402171 = 2103257) B2103257
theorem B5326195 : Blo 1401520 5326195 := bstep (se 1 (by rfl) ⟨3994646, by rfl⟩ : syracuseStep 5326195 = 7989293) B7989293
theorem B6743411 : Blo 1401520 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B1402247 : Blo 1401520 1402247 := bstep (se 1 (by rfl) ⟨1051685, by rfl⟩ : syracuseStep 1402247 = 2103371) B2103371
theorem B1402255 : Blo 1401520 1402255 := bstep (se 1 (by rfl) ⟨1051691, by rfl⟩ : syracuseStep 1402255 = 2103383) B2103383
theorem B3548569 : Blo 1401520 3548569 := bstep (se 2 (by rfl) ⟨1330713, by rfl⟩ : syracuseStep 3548569 = 2661427) B2661427
theorem B2024875 : Blo 1401520 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B1402299 : Blo 1401520 1402299 := bstep (se 1 (by rfl) ⟨1051724, by rfl⟩ : syracuseStep 1402299 = 2103449) B2103449
theorem B7095761 : Blo 1401520 7095761 := bstep (se 2 (by rfl) ⟨2660910, by rfl⟩ : syracuseStep 7095761 = 5321821) B5321821
theorem B17057233 : Blo 1401520 17057233 := bstep (se 2 (by rfl) ⟨6396462, by rfl⟩ : syracuseStep 17057233 = 12792925) B12792925
theorem B1402375 : Blo 1401520 1402375 := bstep (se 1 (by rfl) ⟨1051781, by rfl⟩ : syracuseStep 1402375 = 2103563) B2103563
theorem B1402383 : Blo 1401520 1402383 := bstep (se 1 (by rfl) ⟨1051787, by rfl⟩ : syracuseStep 1402383 = 2103575) B2103575
theorem B3155471 : Blo 1401520 3155471 := bstep (se 1 (by rfl) ⟨2366603, by rfl⟩ : syracuseStep 3155471 = 4733207) B4733207
theorem B7104023 : Blo 1401520 7104023 := bstep (se 1 (by rfl) ⟨5328017, by rfl⟩ : syracuseStep 7104023 = 10656035) B10656035
theorem B3155489 : Blo 1401520 3155489 := bstep (se 2 (by rfl) ⟨1183308, by rfl⟩ : syracuseStep 3155489 = 2366617) B2366617
theorem B4736555 : Blo 1401520 4736555 := bstep (se 1 (by rfl) ⟨3552416, by rfl⟩ : syracuseStep 4736555 = 7104833) B7104833
theorem B3548731 : Blo 1401520 3548731 := bstep (se 1 (by rfl) ⟨2661548, by rfl⟩ : syracuseStep 3548731 = 5323097) B5323097
theorem B1402427 : Blo 1401520 1402427 := bstep (se 1 (by rfl) ⟨1051820, by rfl⟩ : syracuseStep 1402427 = 2103641) B2103641
theorem B1402503 : Blo 1401520 1402503 := bstep (se 1 (by rfl) ⟨1051877, by rfl⟩ : syracuseStep 1402503 = 2103755) B2103755
theorem B1402511 : Blo 1401520 1402511 := bstep (se 1 (by rfl) ⟨1051883, by rfl⟩ : syracuseStep 1402511 = 2103767) B2103767
theorem B1402555 : Blo 1401520 1402555 := bstep (se 1 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 1402555 = 2103833) B2103833
theorem B3548873 : Blo 1401520 3548873 := bstep (se 2 (by rfl) ⟨1330827, by rfl⟩ : syracuseStep 3548873 = 2661655) B2661655
theorem B5990125 : Blo 1401520 5990125 := bstep (se 3 (by rfl) ⟨1123148, by rfl⟩ : syracuseStep 5990125 = 2246297) B2246297
theorem B1402631 : Blo 1401520 1402631 := bstep (se 1 (by rfl) ⟨1051973, by rfl⟩ : syracuseStep 1402631 = 2103947) B2103947
theorem B15968015 : Blo 1401520 15968015 := bstep (se 1 (by rfl) ⟨11976011, by rfl⟩ : syracuseStep 15968015 = 23952023) B23952023
theorem B1402639 : Blo 1401520 1402639 := bstep (se 1 (by rfl) ⟨1051979, by rfl⟩ : syracuseStep 1402639 = 2103959) B2103959
theorem B1402683 : Blo 1401520 1402683 := bstep (se 1 (by rfl) ⟨1052012, by rfl⟩ : syracuseStep 1402683 = 2104025) B2104025
theorem B3155831 : Blo 1401520 3155831 := bstep (se 1 (by rfl) ⟨2366873, by rfl⟩ : syracuseStep 3155831 = 4733747) B4733747
theorem B1402759 : Blo 1401520 1402759 := bstep (se 1 (by rfl) ⟨1052069, by rfl⟩ : syracuseStep 1402759 = 2104139) B2104139
theorem B1402767 : Blo 1401520 1402767 := bstep (se 1 (by rfl) ⟨1052075, by rfl⟩ : syracuseStep 1402767 = 2104151) B2104151
theorem B3991481 : Blo 1401520 3991481 := bstep (se 2 (by rfl) ⟨1496805, by rfl⟩ : syracuseStep 3991481 = 2993611) B2993611
theorem B1402811 : Blo 1401520 1402811 := bstep (se 1 (by rfl) ⟨1052108, by rfl⟩ : syracuseStep 1402811 = 2104217) B2104217
theorem B1402887 : Blo 1401520 1402887 := bstep (se 1 (by rfl) ⟨1052165, by rfl⟩ : syracuseStep 1402887 = 2104331) B2104331
theorem B1402895 : Blo 1401520 1402895 := bstep (se 1 (by rfl) ⟨1052171, by rfl⟩ : syracuseStep 1402895 = 2104343) B2104343
theorem B3549217 : Blo 1401520 3549217 := bstep (se 2 (by rfl) ⟨1330956, by rfl⟩ : syracuseStep 3549217 = 2661913) B2661913
theorem B3156011 : Blo 1401520 3156011 := bstep (se 1 (by rfl) ⟨2367008, by rfl⟩ : syracuseStep 3156011 = 4734017) B4734017
theorem B6400043 : Blo 1401520 6400043 := bstep (se 1 (by rfl) ⟨4800032, by rfl⟩ : syracuseStep 6400043 = 9600065) B9600065
theorem B1402939 : Blo 1401520 1402939 := bstep (se 1 (by rfl) ⟨1052204, by rfl⟩ : syracuseStep 1402939 = 2104409) B2104409
theorem B1403015 : Blo 1401520 1403015 := bstep (se 1 (by rfl) ⟨1052261, by rfl⟩ : syracuseStep 1403015 = 2104523) B2104523
theorem B1403023 : Blo 1401520 1403023 := bstep (se 1 (by rfl) ⟨1052267, by rfl⟩ : syracuseStep 1403023 = 2104535) B2104535
theorem B1403067 : Blo 1401520 1403067 := bstep (se 1 (by rfl) ⟨1052300, by rfl⟩ : syracuseStep 1403067 = 2104601) B2104601
theorem B1403143 : Blo 1401520 1403143 := bstep (se 1 (by rfl) ⟨1052357, by rfl⟩ : syracuseStep 1403143 = 2104715) B2104715
theorem B4262159 : Blo 1401520 4262159 := bstep (se 1 (by rfl) ⟨3196619, by rfl⟩ : syracuseStep 4262159 = 6393239) B6393239
theorem B1403151 : Blo 1401520 1403151 := bstep (se 1 (by rfl) ⟨1052363, by rfl⟩ : syracuseStep 1403151 = 2104727) B2104727
theorem B7579955 : Blo 1401520 7579955 := bstep (se 1 (by rfl) ⟨5684966, by rfl⟩ : syracuseStep 7579955 = 11369933) B11369933
theorem B15976763 : Blo 1401520 15976763 := bstep (se 1 (by rfl) ⟨11982572, by rfl⟩ : syracuseStep 15976763 = 23965145) B23965145
theorem B1403195 : Blo 1401520 1403195 := bstep (se 1 (by rfl) ⟨1052396, by rfl⟩ : syracuseStep 1403195 = 2104793) B2104793
theorem B1403271 : Blo 1401520 1403271 := bstep (se 1 (by rfl) ⟨1052453, by rfl⟩ : syracuseStep 1403271 = 2104907) B2104907
theorem B1403279 : Blo 1401520 1403279 := bstep (se 1 (by rfl) ⟨1052459, by rfl⟩ : syracuseStep 1403279 = 2104919) B2104919
theorem B3156371 : Blo 1401520 3156371 := bstep (se 1 (by rfl) ⟨2367278, by rfl⟩ : syracuseStep 3156371 = 4734557) B4734557
theorem B1403323 : Blo 1401520 1403323 := bstep (se 1 (by rfl) ⟨1052492, by rfl⟩ : syracuseStep 1403323 = 2104985) B2104985
theorem B3156425 : Blo 1401520 3156425 := bstep (se 2 (by rfl) ⟨1183659, by rfl⟩ : syracuseStep 3156425 = 2367319) B2367319
theorem B1403399 : Blo 1401520 1403399 := bstep (se 1 (by rfl) ⟨1052549, by rfl⟩ : syracuseStep 1403399 = 2105099) B2105099
theorem B1403407 : Blo 1401520 1403407 := bstep (se 1 (by rfl) ⟨1052555, by rfl⟩ : syracuseStep 1403407 = 2105111) B2105111
theorem B1403451 : Blo 1401520 1403451 := bstep (se 1 (by rfl) ⟨1052588, by rfl⟩ : syracuseStep 1403451 = 2105177) B2105177
theorem B3549815 : Blo 1401520 3549815 := bstep (se 1 (by rfl) ⟨2662361, by rfl⟩ : syracuseStep 3549815 = 5324723) B5324723
theorem B13470401 : Blo 1401520 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B2525897 : Blo 1401520 2525897 := bstep (se 2 (by rfl) ⟨947211, by rfl⟩ : syracuseStep 2525897 = 1894423) B1894423
theorem B5057225 : Blo 1401520 5057225 := bstep (se 2 (by rfl) ⟨1896459, by rfl⟩ : syracuseStep 5057225 = 3792919) B3792919
theorem B4049693 : Blo 1401520 4049693 := bstep (se 3 (by rfl) ⟨759317, by rfl⟩ : syracuseStep 4049693 = 1518635) B1518635
theorem B12798769 : Blo 1401520 12798769 := bstep (se 2 (by rfl) ⟨4799538, by rfl⟩ : syracuseStep 12798769 = 9599077) B9599077
theorem B13470553 : Blo 1401520 13470553 := bstep (se 2 (by rfl) ⟨5051457, by rfl⟩ : syracuseStep 13470553 = 10102915) B10102915
theorem B15371309 : Blo 1401520 15371309 := bstep (se 3 (by rfl) ⟨2882120, by rfl⟩ : syracuseStep 15371309 = 5764241) B5764241
theorem B3157127 : Blo 1401520 3157127 := bstep (se 1 (by rfl) ⟨2367845, by rfl⟩ : syracuseStep 3157127 = 4735691) B4735691
theorem B3992723 : Blo 1401520 3992723 := bstep (se 1 (by rfl) ⟨2994542, by rfl⟩ : syracuseStep 3992723 = 5989085) B5989085
theorem B40995989 : Blo 1401520 40995989 := bstep (se 6 (by rfl) ⟨960843, by rfl⟩ : syracuseStep 40995989 = 1921687) B1921687
theorem B2526479 : Blo 1401520 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B3157307 : Blo 1401520 3157307 := bstep (se 1 (by rfl) ⟨2367980, by rfl⟩ : syracuseStep 3157307 = 4735961) B4735961
theorem B5991833 : Blo 1401520 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B2993593 : Blo 1401520 2993593 := bstep (se 2 (by rfl) ⟨1122597, by rfl⟩ : syracuseStep 2993593 = 2245195) B2245195
theorem B3157433 : Blo 1401520 3157433 := bstep (se 2 (by rfl) ⟨1184037, by rfl⟩ : syracuseStep 3157433 = 2368075) B2368075
theorem B15175133 : Blo 1401520 15175133 := bstep (se 3 (by rfl) ⟨2845337, by rfl⟩ : syracuseStep 15175133 = 5690675) B5690675
theorem B4263425 : Blo 1401520 4263425 := bstep (se 2 (by rfl) ⟨1598784, by rfl⟩ : syracuseStep 4263425 = 3197569) B3197569
theorem B7097867 : Blo 1401520 7097867 := bstep (se 1 (by rfl) ⟨5323400, by rfl⟩ : syracuseStep 7097867 = 10646801) B10646801
theorem B5328413 : Blo 1401520 5328413 := bstep (se 3 (by rfl) ⟨999077, by rfl⟩ : syracuseStep 5328413 = 1998155) B1998155
theorem B7982711 : Blo 1401520 7982711 := bstep (se 1 (by rfl) ⟨5987033, by rfl⟩ : syracuseStep 7982711 = 11974067) B11974067
theorem B7098029 : Blo 1401520 7098029 := bstep (se 3 (by rfl) ⟨1330880, by rfl⟩ : syracuseStep 7098029 = 2661761) B2661761
theorem B3600139 : Blo 1401520 3600139 := bstep (se 1 (by rfl) ⟨2700104, by rfl⟩ : syracuseStep 3600139 = 5400209) B5400209
theorem B2993935 : Blo 1401520 2993935 := bstep (se 1 (by rfl) ⟨2245451, by rfl⟩ : syracuseStep 2993935 = 4490903) B4490903
theorem B3157775 : Blo 1401520 3157775 := bstep (se 1 (by rfl) ⟨2368331, by rfl⟩ : syracuseStep 3157775 = 4736663) B4736663
theorem B3157793 : Blo 1401520 3157793 := bstep (se 2 (by rfl) ⟨1184172, by rfl⟩ : syracuseStep 3157793 = 2368345) B2368345
theorem B3551111 : Blo 1401520 3551111 := bstep (se 1 (by rfl) ⟨2663333, by rfl⟩ : syracuseStep 3551111 = 5326667) B5326667
theorem B4730777 : Blo 1401520 4730777 := bstep (se 2 (by rfl) ⟨1774041, by rfl⟩ : syracuseStep 4730777 = 3548083) B3548083
theorem B3551161 : Blo 1401520 3551161 := bstep (se 2 (by rfl) ⟨1331685, by rfl⟩ : syracuseStep 3551161 = 2663371) B2663371
theorem B4263947 : Blo 1401520 4263947 := bstep (se 1 (by rfl) ⟨3197960, by rfl⟩ : syracuseStep 4263947 = 6395921) B6395921
theorem B1576975 : Blo 1401520 1576975 := bstep (se 1 (by rfl) ⟨1182731, by rfl⟩ : syracuseStep 1576975 = 2365463) B2365463
theorem B1773839 : Blo 1401520 1773839 := bstep (se 1 (by rfl) ⟨1330379, by rfl⟩ : syracuseStep 1773839 = 2660759) B2660759
theorem B3600683 : Blo 1401520 3600683 := bstep (se 1 (by rfl) ⟨2700512, by rfl⟩ : syracuseStep 3600683 = 5401025) B5401025
theorem B30314897 : Blo 1401520 30314897 := bstep (se 2 (by rfl) ⟨11368086, by rfl⟩ : syracuseStep 30314897 = 22736173) B22736173
theorem B15159737 : Blo 1401520 15159737 := bstep (se 2 (by rfl) ⟨5684901, by rfl⟩ : syracuseStep 15159737 = 11369803) B11369803
theorem B2339273 : Blo 1401520 2339273 := bstep (se 2 (by rfl) ⟨877227, by rfl⟩ : syracuseStep 2339273 = 1754455) B1754455
theorem B1577479 : Blo 1401520 1577479 := bstep (se 1 (by rfl) ⟨1183109, by rfl⟩ : syracuseStep 1577479 = 2366219) B2366219
theorem B3994123 : Blo 1401520 3994123 := bstep (se 1 (by rfl) ⟨2995592, by rfl⟩ : syracuseStep 3994123 = 5991185) B5991185
theorem B3551759 : Blo 1401520 3551759 := bstep (se 1 (by rfl) ⟨2663819, by rfl⟩ : syracuseStep 3551759 = 5327639) B5327639
theorem B2527777 : Blo 1401520 2527777 := bstep (se 2 (by rfl) ⟨947916, by rfl⟩ : syracuseStep 2527777 = 1895833) B1895833
theorem B4731479 : Blo 1401520 4731479 := bstep (se 1 (by rfl) ⟨3548609, by rfl⟩ : syracuseStep 4731479 = 7097219) B7097219
theorem B2994823 : Blo 1401520 2994823 := bstep (se 1 (by rfl) ⟨2246117, by rfl⟩ : syracuseStep 2994823 = 4492235) B4492235
theorem B1577659 : Blo 1401520 1577659 := bstep (se 1 (by rfl) ⟨1183244, by rfl⟩ : syracuseStep 1577659 = 2366489) B2366489
theorem B9589441 : Blo 1401520 9589441 := bstep (se 2 (by rfl) ⟨3596040, by rfl⟩ : syracuseStep 9589441 = 7192081) B7192081
theorem B3994397 : Blo 1401520 3994397 := bstep (se 3 (by rfl) ⟨748949, by rfl⟩ : syracuseStep 3994397 = 1497899) B1497899
theorem B7992209 : Blo 1401520 7992209 := bstep (se 2 (by rfl) ⟨2997078, by rfl⟩ : syracuseStep 7992209 = 5994157) B5994157
theorem B20771851 : Blo 1401520 20771851 := bstep (se 1 (by rfl) ⟨15578888, by rfl⟩ : syracuseStep 20771851 = 31157777) B31157777
theorem B6738967 : Blo 1401520 6738967 := bstep (se 1 (by rfl) ⟨5054225, by rfl⟩ : syracuseStep 6738967 = 10108451) B10108451
theorem B2102315 : Blo 1401520 2102315 := bstep (se 1 (by rfl) ⟨1576736, by rfl⟩ : syracuseStep 2102315 = 3153473) B3153473
theorem B4731965 : Blo 1401520 4731965 := bstep (se 3 (by rfl) ⟨887243, by rfl⟩ : syracuseStep 4731965 = 1774487) B1774487
theorem B2102345 : Blo 1401520 2102345 := bstep (se 2 (by rfl) ⟨788379, by rfl⟩ : syracuseStep 2102345 = 1576759) B1576759
theorem B2995319 : Blo 1401520 2995319 := bstep (se 1 (by rfl) ⟨2246489, by rfl⟩ : syracuseStep 2995319 = 4492979) B4492979
theorem B3372167 : Blo 1401520 3372167 := bstep (se 1 (by rfl) ⟨2529125, by rfl⟩ : syracuseStep 3372167 = 5058251) B5058251
theorem B1578127 : Blo 1401520 1578127 := bstep (se 1 (by rfl) ⟨1183595, by rfl⟩ : syracuseStep 1578127 = 2367191) B2367191
theorem B2102459 : Blo 1401520 2102459 := bstep (se 1 (by rfl) ⟨1576844, by rfl⟩ : syracuseStep 2102459 = 3153689) B3153689
theorem B3552457 : Blo 1401520 3552457 := bstep (se 2 (by rfl) ⟨1332171, by rfl⟩ : syracuseStep 3552457 = 2664343) B2664343
theorem B2102519 : Blo 1401520 2102519 := bstep (se 1 (by rfl) ⟨1576889, by rfl⟩ : syracuseStep 2102519 = 3153779) B3153779
theorem B7099649 : Blo 1401520 7099649 := bstep (se 2 (by rfl) ⟨2662368, by rfl⟩ : syracuseStep 7099649 = 5324737) B5324737
theorem B2102543 : Blo 1401520 2102543 := bstep (se 1 (by rfl) ⟨1576907, by rfl⟩ : syracuseStep 2102543 = 3153815) B3153815
theorem B2102585 : Blo 1401520 2102585 := bstep (se 2 (by rfl) ⟨788469, by rfl⟩ : syracuseStep 2102585 = 1576939) B1576939
theorem B1996105 : Blo 1401520 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B7992665 : Blo 1401520 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B3552599 : Blo 1401520 3552599 := bstep (se 1 (by rfl) ⟨2664449, by rfl⟩ : syracuseStep 3552599 = 5328899) B5328899
theorem B4101491 : Blo 1401520 4101491 := bstep (se 1 (by rfl) ⟨3076118, by rfl⟩ : syracuseStep 4101491 = 6152237) B6152237
theorem B2102663 : Blo 1401520 2102663 := bstep (se 1 (by rfl) ⟨1576997, by rfl⟩ : syracuseStep 2102663 = 3153995) B3153995
theorem B2102699 : Blo 1401520 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B2102729 : Blo 1401520 2102729 := bstep (se 2 (by rfl) ⟨788523, by rfl⟩ : syracuseStep 2102729 = 1577047) B1577047
theorem B13473323 : Blo 1401520 13473323 := bstep (se 1 (by rfl) ⟨10104992, by rfl⟩ : syracuseStep 13473323 = 20209985) B20209985
theorem B2102843 : Blo 1401520 2102843 := bstep (se 1 (by rfl) ⟨1577132, by rfl⟩ : syracuseStep 2102843 = 3154265) B3154265
theorem B5322307 : Blo 1401520 5322307 := bstep (se 1 (by rfl) ⟨3991730, by rfl⟩ : syracuseStep 5322307 = 7983461) B7983461
theorem B22754915 : Blo 1401520 22754915 := bstep (se 1 (by rfl) ⟨17066186, by rfl⟩ : syracuseStep 22754915 = 34132373) B34132373
theorem B2102903 : Blo 1401520 2102903 := bstep (se 1 (by rfl) ⟨1577177, by rfl⟩ : syracuseStep 2102903 = 3154355) B3154355
theorem B1578631 : Blo 1401520 1578631 := bstep (se 1 (by rfl) ⟨1183973, by rfl⟩ : syracuseStep 1578631 = 2367947) B2367947
theorem B2102927 : Blo 1401520 2102927 := bstep (se 1 (by rfl) ⟨1577195, by rfl⟩ : syracuseStep 2102927 = 3154391) B3154391
theorem B2102969 : Blo 1401520 2102969 := bstep (se 2 (by rfl) ⟨788613, by rfl⟩ : syracuseStep 2102969 = 1577227) B1577227
theorem B20207333 : Blo 1401520 20207333 := bstep (se 4 (by rfl) ⟨1894437, by rfl⟩ : syracuseStep 20207333 = 3788875) B3788875
theorem B983684837 : Blo 1401520 983684837 := bstep (se 4 (by rfl) ⟨92220453, by rfl⟩ : syracuseStep 983684837 = 184440907) B184440907
theorem B4495105 : Blo 1401520 4495105 := bstep (se 2 (by rfl) ⟨1685664, by rfl⟩ : syracuseStep 4495105 = 3371329) B3371329
theorem B2103047 : Blo 1401520 2103047 := bstep (se 1 (by rfl) ⟨1577285, by rfl⟩ : syracuseStep 2103047 = 3154571) B3154571
theorem B2103083 : Blo 1401520 2103083 := bstep (se 1 (by rfl) ⟨1577312, by rfl⟩ : syracuseStep 2103083 = 3154625) B3154625
theorem B1578811 : Blo 1401520 1578811 := bstep (se 1 (by rfl) ⟨1184108, by rfl⟩ : syracuseStep 1578811 = 2368217) B2368217
theorem B2103113 : Blo 1401520 2103113 := bstep (se 2 (by rfl) ⟨788667, by rfl⟩ : syracuseStep 2103113 = 1577335) B1577335
theorem B5322611 : Blo 1401520 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B1996663 : Blo 1401520 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B2103227 : Blo 1401520 2103227 := bstep (se 1 (by rfl) ⟨1577420, by rfl⟩ : syracuseStep 2103227 = 3154841) B3154841
theorem B2103287 : Blo 1401520 2103287 := bstep (se 1 (by rfl) ⟨1577465, by rfl⟩ : syracuseStep 2103287 = 3154931) B3154931
theorem B2103311 : Blo 1401520 2103311 := bstep (se 1 (by rfl) ⟨1577483, by rfl⟩ : syracuseStep 2103311 = 3154967) B3154967
theorem B2365483 : Blo 1401520 2365483 := bstep (se 1 (by rfl) ⟨1774112, by rfl⟩ : syracuseStep 2365483 = 3548225) B3548225
theorem B7100459 : Blo 1401520 7100459 := bstep (se 1 (by rfl) ⟨5325344, by rfl⟩ : syracuseStep 7100459 = 10650689) B10650689
theorem B2103353 : Blo 1401520 2103353 := bstep (se 2 (by rfl) ⟨788757, by rfl⟩ : syracuseStep 2103353 = 1577515) B1577515
theorem B2103431 : Blo 1401520 2103431 := bstep (se 1 (by rfl) ⟨1577573, by rfl⟩ : syracuseStep 2103431 = 3155147) B3155147
theorem B2103467 : Blo 1401520 2103467 := bstep (se 1 (by rfl) ⟨1577600, by rfl⟩ : syracuseStep 2103467 = 3155201) B3155201
theorem B2365625 : Blo 1401520 2365625 := bstep (se 2 (by rfl) ⟨887109, by rfl⟩ : syracuseStep 2365625 = 1774219) B1774219
theorem B2103497 : Blo 1401520 2103497 := bstep (se 2 (by rfl) ⟨788811, by rfl⟩ : syracuseStep 2103497 = 1577623) B1577623
theorem B4266283 : Blo 1401520 4266283 := bstep (se 1 (by rfl) ⟨3199712, by rfl⟩ : syracuseStep 4266283 = 6399425) B6399425
theorem B5323067 : Blo 1401520 5323067 := bstep (se 1 (by rfl) ⟨3992300, by rfl⟩ : syracuseStep 5323067 = 7984601) B7984601
theorem B2103611 : Blo 1401520 2103611 := bstep (se 1 (by rfl) ⟨1577708, by rfl⟩ : syracuseStep 2103611 = 3155417) B3155417
theorem B3897659 : Blo 1401520 3897659 := bstep (se 1 (by rfl) ⟨2923244, by rfl⟩ : syracuseStep 3897659 = 5846489) B5846489
theorem B2103671 : Blo 1401520 2103671 := bstep (se 1 (by rfl) ⟨1577753, by rfl⟩ : syracuseStep 2103671 = 3155507) B3155507
theorem B2103695 : Blo 1401520 2103695 := bstep (se 1 (by rfl) ⟨1577771, by rfl⟩ : syracuseStep 2103695 = 3155543) B3155543
theorem B1997227 : Blo 1401520 1997227 := bstep (se 1 (by rfl) ⟨1497920, by rfl⟩ : syracuseStep 1997227 = 2995841) B2995841
theorem B4733369 : Blo 1401520 4733369 := bstep (se 2 (by rfl) ⟨1775013, by rfl⟩ : syracuseStep 4733369 = 3550027) B3550027
theorem B2103737 : Blo 1401520 2103737 := bstep (se 2 (by rfl) ⟨788901, by rfl⟩ : syracuseStep 2103737 = 1577803) B1577803
theorem B2103815 : Blo 1401520 2103815 := bstep (se 1 (by rfl) ⟨1577861, by rfl⟩ : syracuseStep 2103815 = 3155723) B3155723
theorem B2103851 : Blo 1401520 2103851 := bstep (se 1 (by rfl) ⟨1577888, by rfl⟩ : syracuseStep 2103851 = 3155777) B3155777
theorem B2103881 : Blo 1401520 2103881 := bstep (se 2 (by rfl) ⟨788955, by rfl⟩ : syracuseStep 2103881 = 1577911) B1577911
theorem B1997455 : Blo 1401520 1997455 := bstep (se 1 (by rfl) ⟨1498091, by rfl⟩ : syracuseStep 1997455 = 2996183) B2996183
theorem B2103995 : Blo 1401520 2103995 := bstep (se 1 (by rfl) ⟨1577996, by rfl⟩ : syracuseStep 2103995 = 3155993) B3155993
theorem B2104055 : Blo 1401520 2104055 := bstep (se 1 (by rfl) ⟨1578041, by rfl⟩ : syracuseStep 2104055 = 3156083) B3156083
theorem B1538831 : Blo 1401520 1538831 := bstep (se 1 (by rfl) ⟨1154123, by rfl⟩ : syracuseStep 1538831 = 2308247) B2308247
theorem B2104079 : Blo 1401520 2104079 := bstep (se 1 (by rfl) ⟨1578059, by rfl⟩ : syracuseStep 2104079 = 3156119) B3156119
theorem B5323553 : Blo 1401520 5323553 := bstep (se 2 (by rfl) ⟨1996332, by rfl⟩ : syracuseStep 5323553 = 3992665) B3992665
theorem B2104121 : Blo 1401520 2104121 := bstep (se 2 (by rfl) ⟨789045, by rfl⟩ : syracuseStep 2104121 = 1578091) B1578091
theorem B2366327 : Blo 1401520 2366327 := bstep (se 1 (by rfl) ⟨1774745, by rfl⟩ : syracuseStep 2366327 = 3549491) B3549491
theorem B2104199 : Blo 1401520 2104199 := bstep (se 1 (by rfl) ⟨1578149, by rfl⟩ : syracuseStep 2104199 = 3156299) B3156299
theorem B2104235 : Blo 1401520 2104235 := bstep (se 1 (by rfl) ⟨1578176, by rfl⟩ : syracuseStep 2104235 = 3156353) B3156353
theorem B2104265 : Blo 1401520 2104265 := bstep (se 2 (by rfl) ⟨789099, by rfl⟩ : syracuseStep 2104265 = 1578199) B1578199
theorem B4733963 : Blo 1401520 4733963 := bstep (se 1 (by rfl) ⟨3550472, by rfl⟩ : syracuseStep 4733963 = 7100945) B7100945
theorem B2104379 : Blo 1401520 2104379 := bstep (se 1 (by rfl) ⟨1578284, by rfl⟩ : syracuseStep 2104379 = 3156569) B3156569
theorem B5397623 : Blo 1401520 5397623 := bstep (se 1 (by rfl) ⟨4048217, by rfl⟩ : syracuseStep 5397623 = 8096435) B8096435
theorem B4734071 : Blo 1401520 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B2104439 : Blo 1401520 2104439 := bstep (se 1 (by rfl) ⟨1578329, by rfl⟩ : syracuseStep 2104439 = 3156659) B3156659
theorem B2661511 : Blo 1401520 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B2104463 : Blo 1401520 2104463 := bstep (se 1 (by rfl) ⟨1578347, by rfl⟩ : syracuseStep 2104463 = 3156695) B3156695
theorem B2104505 : Blo 1401520 2104505 := bstep (se 2 (by rfl) ⟨789189, by rfl⟩ : syracuseStep 2104505 = 1578379) B1578379
theorem B7986377 : Blo 1401520 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B2104583 : Blo 1401520 2104583 := bstep (se 1 (by rfl) ⟨1578437, by rfl⟩ : syracuseStep 2104583 = 3156875) B3156875
theorem B2104619 : Blo 1401520 2104619 := bstep (se 1 (by rfl) ⟨1578464, by rfl⟩ : syracuseStep 2104619 = 3156929) B3156929
theorem B2366779 : Blo 1401520 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B7101755 : Blo 1401520 7101755 := bstep (se 1 (by rfl) ⟨5326316, by rfl⟩ : syracuseStep 7101755 = 10652633) B10652633
theorem B2104649 : Blo 1401520 2104649 := bstep (se 2 (by rfl) ⟨789243, by rfl⟩ : syracuseStep 2104649 = 1578487) B1578487
theorem B7396753 : Blo 1401520 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B4799897 : Blo 1401520 4799897 := bstep (se 2 (by rfl) ⟨1799961, by rfl⟩ : syracuseStep 4799897 = 3599923) B3599923
theorem B27336113 : Blo 1401520 27336113 := bstep (se 2 (by rfl) ⟨10251042, by rfl⟩ : syracuseStep 27336113 = 20502085) B20502085
theorem B2104763 : Blo 1401520 2104763 := bstep (se 1 (by rfl) ⟨1578572, by rfl⟩ : syracuseStep 2104763 = 3157145) B3157145
theorem B1973705 : Blo 1401520 1973705 := bstep (se 2 (by rfl) ⟨740139, by rfl⟩ : syracuseStep 1973705 = 1480279) B1480279
theorem B2366921 : Blo 1401520 2366921 := bstep (se 2 (by rfl) ⟨887595, by rfl⟩ : syracuseStep 2366921 = 1775191) B1775191
theorem B7200209 : Blo 1401520 7200209 := bstep (se 2 (by rfl) ⟨2700078, by rfl⟩ : syracuseStep 7200209 = 5400157) B5400157
theorem B7101917 : Blo 1401520 7101917 := bstep (se 3 (by rfl) ⟨1331609, by rfl⟩ : syracuseStep 7101917 = 2663219) B2663219
theorem B2104823 : Blo 1401520 2104823 := bstep (se 1 (by rfl) ⟨1578617, by rfl⟩ : syracuseStep 2104823 = 3157235) B3157235
theorem B13147651 : Blo 1401520 13147651 := bstep (se 1 (by rfl) ⟨9860738, by rfl⟩ : syracuseStep 13147651 = 19721477) B19721477
theorem B2104847 : Blo 1401520 2104847 := bstep (se 1 (by rfl) ⟨1578635, by rfl⟩ : syracuseStep 2104847 = 3157271) B3157271
theorem B2104889 : Blo 1401520 2104889 := bstep (se 2 (by rfl) ⟨789333, by rfl⟩ : syracuseStep 2104889 = 1578667) B1578667
theorem B3153527 : Blo 1401520 3153527 := bstep (se 1 (by rfl) ⟨2365145, by rfl⟩ : syracuseStep 3153527 = 4730291) B4730291
theorem B2104967 : Blo 1401520 2104967 := bstep (se 1 (by rfl) ⟨1578725, by rfl⟩ : syracuseStep 2104967 = 3157451) B3157451
theorem B2105003 : Blo 1401520 2105003 := bstep (se 1 (by rfl) ⟨1578752, by rfl⟩ : syracuseStep 2105003 = 3157505) B3157505
theorem B4734665 : Blo 1401520 4734665 := bstep (se 2 (by rfl) ⟨1775499, by rfl⟩ : syracuseStep 4734665 = 3550999) B3550999
theorem B2105033 : Blo 1401520 2105033 := bstep (se 2 (by rfl) ⟨789387, by rfl⟩ : syracuseStep 2105033 = 1578775) B1578775
theorem B5324525 : Blo 1401520 5324525 := bstep (se 3 (by rfl) ⟨998348, by rfl⟩ : syracuseStep 5324525 = 1996697) B1996697
theorem B7102241 : Blo 1401520 7102241 := bstep (se 2 (by rfl) ⟨2663340, by rfl⟩ : syracuseStep 7102241 = 5326681) B5326681
theorem B3153707 : Blo 1401520 3153707 := bstep (se 1 (by rfl) ⟨2365280, by rfl⟩ : syracuseStep 3153707 = 4730561) B4730561
theorem B3792683 : Blo 1401520 3792683 := bstep (se 1 (by rfl) ⟨2844512, by rfl⟩ : syracuseStep 3792683 = 5689025) B5689025
theorem B2105147 : Blo 1401520 2105147 := bstep (se 1 (by rfl) ⟨1578860, by rfl⟩ : syracuseStep 2105147 = 3157721) B3157721
theorem B2105207 : Blo 1401520 2105207 := bstep (se 1 (by rfl) ⟨1578905, by rfl⟩ : syracuseStep 2105207 = 3157811) B3157811
theorem B2105231 : Blo 1401520 2105231 := bstep (se 1 (by rfl) ⟨1578923, by rfl⟩ : syracuseStep 2105231 = 3157847) B3157847
theorem B4865939 : Blo 1401520 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B13475747 : Blo 1401520 13475747 := bstep (se 1 (by rfl) ⟨10106810, by rfl⟩ : syracuseStep 13475747 = 20213621) B20213621
theorem B4267961 : Blo 1401520 4267961 := bstep (se 2 (by rfl) ⟨1600485, by rfl⟩ : syracuseStep 4267961 = 3200971) B3200971
theorem B2105273 : Blo 1401520 2105273 := bstep (se 2 (by rfl) ⟨789477, by rfl⟩ : syracuseStep 2105273 = 1578955) B1578955
theorem B2842631 : Blo 1401520 2842631 := bstep (se 1 (by rfl) ⟨2131973, by rfl⟩ : syracuseStep 2842631 = 4263947) B4263947
theorem B3153977 : Blo 1401520 3153977 := bstep (se 2 (by rfl) ⟨1182741, by rfl⟩ : syracuseStep 3153977 = 2365483) B2365483
theorem B2400455 : Blo 1401520 2400455 := bstep (se 1 (by rfl) ⟨1800341, by rfl⟩ : syracuseStep 2400455 = 3600683) B3600683
theorem B20209931 : Blo 1401520 20209931 := bstep (se 1 (by rfl) ⟨15157448, by rfl⟩ : syracuseStep 20209931 = 30314897) B30314897
theorem B7987517 : Blo 1401520 7987517 := bstep (se 3 (by rfl) ⟨1497659, by rfl⟩ : syracuseStep 7987517 = 2995319) B2995319
theorem B2367839 : Blo 1401520 2367839 := bstep (se 1 (by rfl) ⟨1775879, by rfl⟩ : syracuseStep 2367839 = 3551759) B3551759
theorem B5767529 : Blo 1401520 5767529 := bstep (se 2 (by rfl) ⟨2162823, by rfl⟩ : syracuseStep 5767529 = 4325647) B4325647
theorem B3154319 : Blo 1401520 3154319 := bstep (se 1 (by rfl) ⟨2365739, by rfl⟩ : syracuseStep 3154319 = 4731479) B4731479
theorem B5767661 : Blo 1401520 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B4735475 : Blo 1401520 4735475 := bstep (se 1 (by rfl) ⟨3551606, by rfl⟩ : syracuseStep 4735475 = 7103213) B7103213
theorem B2662931 : Blo 1401520 2662931 := bstep (se 1 (by rfl) ⟨1997198, by rfl⟩ : syracuseStep 2662931 = 3994397) B3994397
theorem B2662969 : Blo 1401520 2662969 := bstep (se 2 (by rfl) ⟨998613, by rfl⟩ : syracuseStep 2662969 = 1997227) B1997227
theorem B5325497 : Blo 1401520 5325497 := bstep (se 2 (by rfl) ⟨1997061, by rfl⟩ : syracuseStep 5325497 = 3994123) B3994123
theorem B1401543 : Blo 1401520 1401543 := bstep (se 1 (by rfl) ⟨1051157, by rfl⟩ : syracuseStep 1401543 = 2102315) B2102315
theorem B3154643 : Blo 1401520 3154643 := bstep (se 1 (by rfl) ⟨2365982, by rfl⟩ : syracuseStep 3154643 = 4731965) B4731965
theorem B5325527 : Blo 1401520 5325527 := bstep (se 1 (by rfl) ⟨3994145, by rfl⟩ : syracuseStep 5325527 = 7988291) B7988291
theorem B1401563 : Blo 1401520 1401563 := bstep (se 1 (by rfl) ⟨1051172, by rfl⟩ : syracuseStep 1401563 = 2102345) B2102345
theorem B1401639 : Blo 1401520 1401639 := bstep (se 1 (by rfl) ⟨1051229, by rfl⟩ : syracuseStep 1401639 = 2102459) B2102459
theorem B1401679 : Blo 1401520 1401679 := bstep (se 1 (by rfl) ⟨1051259, by rfl⟩ : syracuseStep 1401679 = 2102519) B2102519
theorem B1401695 : Blo 1401520 1401695 := bstep (se 1 (by rfl) ⟨1051271, by rfl⟩ : syracuseStep 1401695 = 2102543) B2102543
theorem B2663273 : Blo 1401520 2663273 := bstep (se 2 (by rfl) ⟨998727, by rfl⟩ : syracuseStep 2663273 = 1997455) B1997455
theorem B1401723 : Blo 1401520 1401723 := bstep (se 1 (by rfl) ⟨1051292, by rfl⟩ : syracuseStep 1401723 = 2102585) B2102585
theorem B2368399 : Blo 1401520 2368399 := bstep (se 1 (by rfl) ⟨1776299, by rfl⟩ : syracuseStep 2368399 = 3552599) B3552599
theorem B1401775 : Blo 1401520 1401775 := bstep (se 1 (by rfl) ⟨1051331, by rfl⟩ : syracuseStep 1401775 = 2102663) B2102663
theorem B1401799 : Blo 1401520 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B1401819 : Blo 1401520 1401819 := bstep (se 1 (by rfl) ⟨1051364, by rfl⟩ : syracuseStep 1401819 = 2102729) B2102729
theorem B4736015 : Blo 1401520 4736015 := bstep (se 1 (by rfl) ⟨3552011, by rfl⟩ : syracuseStep 4736015 = 7104023) B7104023
theorem B1401895 : Blo 1401520 1401895 := bstep (se 1 (by rfl) ⟨1051421, by rfl⟩ : syracuseStep 1401895 = 2102843) B2102843
theorem B17065025 : Blo 1401520 17065025 := bstep (se 2 (by rfl) ⟨6399384, by rfl⟩ : syracuseStep 17065025 = 12798769) B12798769
theorem B1401935 : Blo 1401520 1401935 := bstep (se 1 (by rfl) ⟨1051451, by rfl⟩ : syracuseStep 1401935 = 2102903) B2102903
theorem B1401951 : Blo 1401520 1401951 := bstep (se 1 (by rfl) ⟨1051463, by rfl⟩ : syracuseStep 1401951 = 2102927) B2102927
theorem B1401979 : Blo 1401520 1401979 := bstep (se 1 (by rfl) ⟨1051484, by rfl⟩ : syracuseStep 1401979 = 2102969) B2102969
theorem B1402031 : Blo 1401520 1402031 := bstep (se 1 (by rfl) ⟨1051523, by rfl⟩ : syracuseStep 1402031 = 2103047) B2103047
theorem B1402055 : Blo 1401520 1402055 := bstep (se 1 (by rfl) ⟨1051541, by rfl⟩ : syracuseStep 1402055 = 2103083) B2103083
theorem B1402075 : Blo 1401520 1402075 := bstep (se 1 (by rfl) ⟨1051556, by rfl⟩ : syracuseStep 1402075 = 2103113) B2103113
theorem B3548407 : Blo 1401520 3548407 := bstep (se 1 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 3548407 = 5322611) B5322611
theorem B1402151 : Blo 1401520 1402151 := bstep (se 1 (by rfl) ⟨1051613, by rfl⟩ : syracuseStep 1402151 = 2103227) B2103227
theorem B1402191 : Blo 1401520 1402191 := bstep (se 1 (by rfl) ⟨1051643, by rfl⟩ : syracuseStep 1402191 = 2103287) B2103287
theorem B1402207 : Blo 1401520 1402207 := bstep (se 1 (by rfl) ⟨1051655, by rfl⟩ : syracuseStep 1402207 = 2103311) B2103311
theorem B1402235 : Blo 1401520 1402235 := bstep (se 1 (by rfl) ⟨1051676, by rfl⟩ : syracuseStep 1402235 = 2103353) B2103353
theorem B1402287 : Blo 1401520 1402287 := bstep (se 1 (by rfl) ⟨1051715, by rfl⟩ : syracuseStep 1402287 = 2103431) B2103431
theorem B1402311 : Blo 1401520 1402311 := bstep (se 1 (by rfl) ⟨1051733, by rfl⟩ : syracuseStep 1402311 = 2103467) B2103467
theorem B1402331 : Blo 1401520 1402331 := bstep (se 1 (by rfl) ⟨1051748, by rfl⟩ : syracuseStep 1402331 = 2103497) B2103497
theorem B3548681 : Blo 1401520 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B3548711 : Blo 1401520 3548711 := bstep (se 1 (by rfl) ⟨2661533, by rfl⟩ : syracuseStep 3548711 = 5323067) B5323067
theorem B1402407 : Blo 1401520 1402407 := bstep (se 1 (by rfl) ⟨1051805, by rfl⟩ : syracuseStep 1402407 = 2103611) B2103611
theorem B10651175 : Blo 1401520 10651175 := bstep (se 1 (by rfl) ⟨7988381, by rfl⟩ : syracuseStep 10651175 = 15976763) B15976763
theorem B2598439 : Blo 1401520 2598439 := bstep (se 1 (by rfl) ⟨1948829, by rfl⟩ : syracuseStep 2598439 = 3897659) B3897659
theorem B1402447 : Blo 1401520 1402447 := bstep (se 1 (by rfl) ⟨1051835, by rfl⟩ : syracuseStep 1402447 = 2103671) B2103671
theorem B1402463 : Blo 1401520 1402463 := bstep (se 1 (by rfl) ⟨1051847, by rfl⟩ : syracuseStep 1402463 = 2103695) B2103695
theorem B4736609 : Blo 1401520 4736609 := bstep (se 2 (by rfl) ⟨1776228, by rfl⟩ : syracuseStep 4736609 = 3552457) B3552457
theorem B3155579 : Blo 1401520 3155579 := bstep (se 1 (by rfl) ⟨2366684, by rfl⟩ : syracuseStep 3155579 = 4733369) B4733369
theorem B1402491 : Blo 1401520 1402491 := bstep (se 1 (by rfl) ⟨1051868, by rfl⟩ : syracuseStep 1402491 = 2103737) B2103737
theorem B1402543 : Blo 1401520 1402543 := bstep (se 1 (by rfl) ⟨1051907, by rfl⟩ : syracuseStep 1402543 = 2103815) B2103815
theorem B1402567 : Blo 1401520 1402567 := bstep (se 1 (by rfl) ⟨1051925, by rfl⟩ : syracuseStep 1402567 = 2103851) B2103851
theorem B1402587 : Blo 1401520 1402587 := bstep (se 1 (by rfl) ⟨1051940, by rfl⟩ : syracuseStep 1402587 = 2103881) B2103881
theorem B8980217 : Blo 1401520 8980217 := bstep (se 2 (by rfl) ⟨3367581, by rfl⟩ : syracuseStep 8980217 = 6735163) B6735163
theorem B3155705 : Blo 1401520 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B1402663 : Blo 1401520 1402663 := bstep (se 1 (by rfl) ⟨1051997, by rfl⟩ : syracuseStep 1402663 = 2103995) B2103995
theorem B8980267 : Blo 1401520 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B1402703 : Blo 1401520 1402703 := bstep (se 1 (by rfl) ⟨1052027, by rfl⟩ : syracuseStep 1402703 = 2104055) B2104055
theorem B1402719 : Blo 1401520 1402719 := bstep (se 1 (by rfl) ⟨1052039, by rfl⟩ : syracuseStep 1402719 = 2104079) B2104079
theorem B3549035 : Blo 1401520 3549035 := bstep (se 1 (by rfl) ⟨2661776, by rfl⟩ : syracuseStep 3549035 = 5323553) B5323553
theorem B1402747 : Blo 1401520 1402747 := bstep (se 1 (by rfl) ⟨1052060, by rfl⟩ : syracuseStep 1402747 = 2104121) B2104121
theorem B3991457 : Blo 1401520 3991457 := bstep (se 2 (by rfl) ⟨1496796, by rfl⟩ : syracuseStep 3991457 = 2993593) B2993593
theorem B1402799 : Blo 1401520 1402799 := bstep (se 1 (by rfl) ⟨1052099, by rfl⟩ : syracuseStep 1402799 = 2104199) B2104199
theorem B1402823 : Blo 1401520 1402823 := bstep (se 1 (by rfl) ⟨1052117, by rfl⟩ : syracuseStep 1402823 = 2104235) B2104235
theorem B1402843 : Blo 1401520 1402843 := bstep (se 1 (by rfl) ⟨1052132, by rfl⟩ : syracuseStep 1402843 = 2104265) B2104265
theorem B3155975 : Blo 1401520 3155975 := bstep (se 1 (by rfl) ⟨2366981, by rfl⟩ : syracuseStep 3155975 = 4733963) B4733963
theorem B1402919 : Blo 1401520 1402919 := bstep (se 1 (by rfl) ⟨1052189, by rfl⟩ : syracuseStep 1402919 = 2104379) B2104379
theorem B3598415 : Blo 1401520 3598415 := bstep (se 1 (by rfl) ⟨2698811, by rfl⟩ : syracuseStep 3598415 = 5397623) B5397623
theorem B3156047 : Blo 1401520 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B1402959 : Blo 1401520 1402959 := bstep (se 1 (by rfl) ⟨1052219, by rfl⟩ : syracuseStep 1402959 = 2104439) B2104439
theorem B7096409 : Blo 1401520 7096409 := bstep (se 2 (by rfl) ⟨2661153, by rfl⟩ : syracuseStep 7096409 = 5322307) B5322307
theorem B1402975 : Blo 1401520 1402975 := bstep (se 1 (by rfl) ⟨1052231, by rfl⟩ : syracuseStep 1402975 = 2104463) B2104463
theorem B27330659 : Blo 1401520 27330659 := bstep (se 1 (by rfl) ⟨20497994, by rfl⟩ : syracuseStep 27330659 = 40995989) B40995989
theorem B1403003 : Blo 1401520 1403003 := bstep (se 1 (by rfl) ⟨1052252, by rfl⟩ : syracuseStep 1403003 = 2104505) B2104505
theorem B1403055 : Blo 1401520 1403055 := bstep (se 1 (by rfl) ⟨1052291, by rfl⟩ : syracuseStep 1403055 = 2104583) B2104583
theorem B1403079 : Blo 1401520 1403079 := bstep (se 1 (by rfl) ⟨1052309, by rfl⟩ : syracuseStep 1403079 = 2104619) B2104619
theorem B1403099 : Blo 1401520 1403099 := bstep (se 1 (by rfl) ⟨1052324, by rfl⟩ : syracuseStep 1403099 = 2104649) B2104649
theorem B1403175 : Blo 1401520 1403175 := bstep (se 1 (by rfl) ⟨1052381, by rfl⟩ : syracuseStep 1403175 = 2104763) B2104763
theorem B1403215 : Blo 1401520 1403215 := bstep (se 1 (by rfl) ⟨1052411, by rfl⟩ : syracuseStep 1403215 = 2104823) B2104823
theorem B1403231 : Blo 1401520 1403231 := bstep (se 1 (by rfl) ⟨1052423, by rfl⟩ : syracuseStep 1403231 = 2104847) B2104847
theorem B3991913 : Blo 1401520 3991913 := bstep (se 2 (by rfl) ⟨1496967, by rfl⟩ : syracuseStep 3991913 = 2993935) B2993935
theorem B1403259 : Blo 1401520 1403259 := bstep (se 1 (by rfl) ⟨1052444, by rfl⟩ : syracuseStep 1403259 = 2104889) B2104889
theorem B1403311 : Blo 1401520 1403311 := bstep (se 1 (by rfl) ⟨1052483, by rfl⟩ : syracuseStep 1403311 = 2104967) B2104967
theorem B1403335 : Blo 1401520 1403335 := bstep (se 1 (by rfl) ⟨1052501, by rfl⟩ : syracuseStep 1403335 = 2105003) B2105003
theorem B3156443 : Blo 1401520 3156443 := bstep (se 1 (by rfl) ⟨2367332, by rfl⟩ : syracuseStep 3156443 = 4734665) B4734665
theorem B1403355 : Blo 1401520 1403355 := bstep (se 1 (by rfl) ⟨1052516, by rfl⟩ : syracuseStep 1403355 = 2105033) B2105033
theorem B3549683 : Blo 1401520 3549683 := bstep (se 1 (by rfl) ⟨2662262, by rfl⟩ : syracuseStep 3549683 = 5324525) B5324525
theorem B1403431 : Blo 1401520 1403431 := bstep (se 1 (by rfl) ⟨1052573, by rfl⟩ : syracuseStep 1403431 = 2105147) B2105147
theorem B1403471 : Blo 1401520 1403471 := bstep (se 1 (by rfl) ⟨1052603, by rfl⟩ : syracuseStep 1403471 = 2105207) B2105207
theorem B1403487 : Blo 1401520 1403487 := bstep (se 1 (by rfl) ⟨1052615, by rfl⟩ : syracuseStep 1403487 = 2105231) B2105231
theorem B2845307 : Blo 1401520 2845307 := bstep (se 1 (by rfl) ⟨2133980, by rfl⟩ : syracuseStep 2845307 = 4267961) B4267961
theorem B1403515 : Blo 1401520 1403515 := bstep (se 1 (by rfl) ⟨1052636, by rfl⟩ : syracuseStep 1403515 = 2105273) B2105273
theorem B35941157 : Blo 1401520 35941157 := bstep (se 4 (by rfl) ⟨3369483, by rfl⟩ : syracuseStep 35941157 = 6738967) B6738967
theorem B10644371 : Blo 1401520 10644371 := bstep (se 1 (by rfl) ⟨7983278, by rfl⟩ : syracuseStep 10644371 = 15966557) B15966557
theorem B3156911 : Blo 1401520 3156911 := bstep (se 1 (by rfl) ⟨2367683, by rfl⟩ : syracuseStep 3156911 = 4735367) B4735367
theorem B3550139 : Blo 1401520 3550139 := bstep (se 1 (by rfl) ⟨2662604, by rfl⟩ : syracuseStep 3550139 = 5325209) B5325209
theorem B5688377 : Blo 1401520 5688377 := bstep (se 2 (by rfl) ⟨2133141, by rfl⟩ : syracuseStep 5688377 = 4266283) B4266283
theorem B3157163 : Blo 1401520 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B15969473 : Blo 1401520 15969473 := bstep (se 2 (by rfl) ⟨5988552, by rfl⟩ : syracuseStep 15969473 = 11977105) B11977105
theorem B5328139 : Blo 1401520 5328139 := bstep (se 1 (by rfl) ⟨3996104, by rfl⟩ : syracuseStep 5328139 = 7992209) B7992209
theorem B21064997 : Blo 1401520 21064997 := bstep (se 4 (by rfl) ⟨1974843, by rfl⟩ : syracuseStep 21064997 = 3949687) B3949687
theorem B4730237 : Blo 1401520 4730237 := bstep (se 3 (by rfl) ⟨886919, by rfl⟩ : syracuseStep 4730237 = 1773839) B1773839
theorem B11365757 : Blo 1401520 11365757 := bstep (se 3 (by rfl) ⟨2131079, by rfl⟩ : syracuseStep 11365757 = 4262159) B4262159
theorem B3370369 : Blo 1401520 3370369 := bstep (se 2 (by rfl) ⟨1263888, by rfl⟩ : syracuseStep 3370369 = 2527777) B2527777
theorem B2248111 : Blo 1401520 2248111 := bstep (se 1 (by rfl) ⟨1686083, by rfl⟩ : syracuseStep 2248111 = 3372167) B3372167
theorem B5328443 : Blo 1401520 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B3550817 : Blo 1401520 3550817 := bstep (se 2 (by rfl) ⟨1331556, by rfl⟩ : syracuseStep 3550817 = 2663113) B2663113
theorem B4730507 : Blo 1401520 4730507 := bstep (se 1 (by rfl) ⟨3547880, by rfl⟩ : syracuseStep 4730507 = 7095761) B7095761
theorem B8982215 : Blo 1401520 8982215 := bstep (se 1 (by rfl) ⟨6736661, by rfl⟩ : syracuseStep 8982215 = 13473323) B13473323
theorem B3157703 : Blo 1401520 3157703 := bstep (se 1 (by rfl) ⟨2368277, by rfl⟩ : syracuseStep 3157703 = 4736555) B4736555
theorem B15978221 : Blo 1401520 15978221 := bstep (se 3 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 15978221 = 5991833) B5991833
theorem B17960737 : Blo 1401520 17960737 := bstep (se 2 (by rfl) ⟨6735276, by rfl⟩ : syracuseStep 17960737 = 13470553) B13470553
theorem B13471555 : Blo 1401520 13471555 := bstep (se 1 (by rfl) ⟨10103666, by rfl⟩ : syracuseStep 13471555 = 20207333) B20207333
theorem B655789891 : Blo 1401520 655789891 := bstep (se 1 (by rfl) ⟨491842418, by rfl⟩ : syracuseStep 655789891 = 983684837) B983684837
theorem B10645343 : Blo 1401520 10645343 := bstep (se 1 (by rfl) ⟨7984007, by rfl⟩ : syracuseStep 10645343 = 15968015) B15968015
theorem B6238061 : Blo 1401520 6238061 := bstep (se 3 (by rfl) ⟨1169636, by rfl⟩ : syracuseStep 6238061 = 2339273) B2339273
theorem B23973893 : Blo 1401520 23973893 := bstep (se 4 (by rfl) ⟨2247552, by rfl⟩ : syracuseStep 23973893 = 4495105) B4495105
theorem B1577083 : Blo 1401520 1577083 := bstep (se 1 (by rfl) ⟨1182812, by rfl⟩ : syracuseStep 1577083 = 2365625) B2365625
theorem B1683931 : Blo 1401520 1683931 := bstep (se 1 (by rfl) ⟨1262948, by rfl⟩ : syracuseStep 1683931 = 2525897) B2525897
theorem B3371483 : Blo 1401520 3371483 := bstep (se 1 (by rfl) ⟨2528612, by rfl⟩ : syracuseStep 3371483 = 5057225) B5057225
theorem B2699795 : Blo 1401520 2699795 := bstep (se 1 (by rfl) ⟨2024846, by rfl⟩ : syracuseStep 2699795 = 4049693) B4049693
theorem B4731425 : Blo 1401520 4731425 := bstep (se 2 (by rfl) ⟨1774284, by rfl⟩ : syracuseStep 4731425 = 3548569) B3548569
theorem B2699833 : Blo 1401520 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B1577551 : Blo 1401520 1577551 := bstep (se 1 (by rfl) ⟨1183163, by rfl⟩ : syracuseStep 1577551 = 2366327) B2366327
theorem B4731641 : Blo 1401520 4731641 := bstep (se 2 (by rfl) ⟨1774365, by rfl⟩ : syracuseStep 4731641 = 3548731) B3548731
theorem B1684319 : Blo 1401520 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B3199931 : Blo 1401520 3199931 := bstep (se 1 (by rfl) ⟨2399948, by rfl⟩ : syracuseStep 3199931 = 4799897) B4799897
theorem B18224075 : Blo 1401520 18224075 := bstep (se 1 (by rfl) ⟨13668056, by rfl⟩ : syracuseStep 18224075 = 27336113) B27336113
theorem B1577947 : Blo 1401520 1577947 := bstep (se 1 (by rfl) ⟨1183460, by rfl⟩ : syracuseStep 1577947 = 2366921) B2366921
theorem B4731911 : Blo 1401520 4731911 := bstep (se 1 (by rfl) ⟨3548933, by rfl⟩ : syracuseStep 4731911 = 7097867) B7097867
theorem B3552275 : Blo 1401520 3552275 := bstep (se 1 (by rfl) ⟨2664206, by rfl⟩ : syracuseStep 3552275 = 5328413) B5328413
theorem B2102351 : Blo 1401520 2102351 := bstep (se 1 (by rfl) ⟨1576763, by rfl⟩ : syracuseStep 2102351 = 3153527) B3153527
theorem B5321807 : Blo 1401520 5321807 := bstep (se 1 (by rfl) ⟨3991355, by rfl⟩ : syracuseStep 5321807 = 7982711) B7982711
theorem B4732019 : Blo 1401520 4732019 := bstep (se 1 (by rfl) ⟨3549014, by rfl⟩ : syracuseStep 4732019 = 7098029) B7098029
theorem B2102471 : Blo 1401520 2102471 := bstep (se 1 (by rfl) ⟨1576853, by rfl⟩ : syracuseStep 2102471 = 3153707) B3153707
theorem B2528455 : Blo 1401520 2528455 := bstep (se 1 (by rfl) ⟨1896341, by rfl⟩ : syracuseStep 2528455 = 3792683) B3792683
theorem B8983831 : Blo 1401520 8983831 := bstep (se 1 (by rfl) ⟨6737873, by rfl⟩ : syracuseStep 8983831 = 13475747) B13475747
theorem B2102633 : Blo 1401520 2102633 := bstep (se 2 (by rfl) ⟨788487, by rfl⟩ : syracuseStep 2102633 = 1576975) B1576975
theorem B4732289 : Blo 1401520 4732289 := bstep (se 2 (by rfl) ⟨1774608, by rfl⟩ : syracuseStep 4732289 = 3549217) B3549217
theorem B1578415 : Blo 1401520 1578415 := bstep (se 1 (by rfl) ⟨1183811, by rfl⟩ : syracuseStep 1578415 = 2367623) B2367623
theorem B2102711 : Blo 1401520 2102711 := bstep (se 1 (by rfl) ⟨1577033, by rfl⟩ : syracuseStep 2102711 = 3154067) B3154067
theorem B40990157 : Blo 1401520 40990157 := bstep (se 3 (by rfl) ⟨7685654, by rfl⟩ : syracuseStep 40990157 = 15371309) B15371309
theorem B2102747 : Blo 1401520 2102747 := bstep (se 1 (by rfl) ⟨1577060, by rfl⟩ : syracuseStep 2102747 = 3154121) B3154121
theorem B1578847 : Blo 1401520 1578847 := bstep (se 1 (by rfl) ⟨1184135, by rfl⟩ : syracuseStep 1578847 = 2368271) B2368271
theorem B2103215 : Blo 1401520 2103215 := bstep (se 1 (by rfl) ⟨1577411, by rfl⟩ : syracuseStep 2103215 = 3154823) B3154823
theorem B2103305 : Blo 1401520 2103305 := bstep (se 2 (by rfl) ⟨788739, by rfl⟩ : syracuseStep 2103305 = 1577479) B1577479
theorem B15972389 : Blo 1401520 15972389 := bstep (se 4 (by rfl) ⟨1497411, by rfl⟩ : syracuseStep 15972389 = 2994823) B2994823
theorem B2103335 : Blo 1401520 2103335 := bstep (se 1 (by rfl) ⟨1577501, by rfl⟩ : syracuseStep 2103335 = 3155003) B3155003
theorem B4495439 : Blo 1401520 4495439 := bstep (se 1 (by rfl) ⟨3371579, by rfl⟩ : syracuseStep 4495439 = 6743159) B6743159
theorem B2103419 : Blo 1401520 2103419 := bstep (se 1 (by rfl) ⟨1577564, by rfl⟩ : syracuseStep 2103419 = 3155129) B3155129
theorem B4733099 : Blo 1401520 4733099 := bstep (se 1 (by rfl) ⟨3549824, by rfl⟩ : syracuseStep 4733099 = 7099649) B7099649
theorem B2734327 : Blo 1401520 2734327 := bstep (se 1 (by rfl) ⟨2050745, by rfl⟩ : syracuseStep 2734327 = 4101491) B4101491
theorem B4495607 : Blo 1401520 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B2103545 : Blo 1401520 2103545 := bstep (se 2 (by rfl) ⟨788829, by rfl⟩ : syracuseStep 2103545 = 1577659) B1577659
theorem B12785921 : Blo 1401520 12785921 := bstep (se 2 (by rfl) ⟨4794720, by rfl⟩ : syracuseStep 12785921 = 9589441) B9589441
theorem B2103647 : Blo 1401520 2103647 := bstep (se 1 (by rfl) ⟨1577735, by rfl⟩ : syracuseStep 2103647 = 3155471) B3155471
theorem B2103659 : Blo 1401520 2103659 := bstep (se 1 (by rfl) ⟨1577744, by rfl⟩ : syracuseStep 2103659 = 3155489) B3155489
theorem B3791233 : Blo 1401520 3791233 := bstep (se 2 (by rfl) ⟨1421712, by rfl⟩ : syracuseStep 3791233 = 2843425) B2843425
theorem B15169943 : Blo 1401520 15169943 := bstep (se 1 (by rfl) ⟨11377457, by rfl⟩ : syracuseStep 15169943 = 22754915) B22754915
theorem B2365915 : Blo 1401520 2365915 := bstep (se 1 (by rfl) ⟨1774436, by rfl⟩ : syracuseStep 2365915 = 3548873) B3548873
theorem B40425965 : Blo 1401520 40425965 := bstep (se 3 (by rfl) ⟨7579868, by rfl⟩ : syracuseStep 40425965 = 15159737) B15159737
theorem B19200557 : Blo 1401520 19200557 := bstep (se 3 (by rfl) ⟨3600104, by rfl⟩ : syracuseStep 19200557 = 7200209) B7200209
theorem B2103887 : Blo 1401520 2103887 := bstep (se 1 (by rfl) ⟨1577915, by rfl⟩ : syracuseStep 2103887 = 3155831) B3155831
theorem B2660987 : Blo 1401520 2660987 := bstep (se 1 (by rfl) ⟨1995740, by rfl⟩ : syracuseStep 2660987 = 3991481) B3991481
theorem B27695801 : Blo 1401520 27695801 := bstep (se 2 (by rfl) ⟨10385925, by rfl⟩ : syracuseStep 27695801 = 20771851) B20771851
theorem B4733639 : Blo 1401520 4733639 := bstep (se 1 (by rfl) ⟨3550229, by rfl⟩ : syracuseStep 4733639 = 7100459) B7100459
theorem B2104007 : Blo 1401520 2104007 := bstep (se 1 (by rfl) ⟨1578005, by rfl⟩ : syracuseStep 2104007 = 3156011) B3156011
theorem B4266695 : Blo 1401520 4266695 := bstep (se 1 (by rfl) ⟨3200021, by rfl⟩ : syracuseStep 4266695 = 6400043) B6400043
theorem B2104169 : Blo 1401520 2104169 := bstep (se 2 (by rfl) ⟨789063, by rfl⟩ : syracuseStep 2104169 = 1578127) B1578127
theorem B5053303 : Blo 1401520 5053303 := bstep (se 1 (by rfl) ⟨3789977, by rfl⟩ : syracuseStep 5053303 = 7579955) B7579955
theorem B2104247 : Blo 1401520 2104247 := bstep (se 1 (by rfl) ⟨1578185, by rfl⟩ : syracuseStep 2104247 = 3156371) B3156371
theorem B2104283 : Blo 1401520 2104283 := bstep (se 1 (by rfl) ⟨1578212, by rfl⟩ : syracuseStep 2104283 = 3156425) B3156425
theorem B2366543 : Blo 1401520 2366543 := bstep (se 1 (by rfl) ⟨1774907, by rfl⟩ : syracuseStep 2366543 = 3549815) B3549815
theorem B2661473 : Blo 1401520 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B7101593 : Blo 1401520 7101593 := bstep (se 2 (by rfl) ⟨2663097, by rfl⟩ : syracuseStep 7101593 = 5326195) B5326195
theorem B9862337 : Blo 1401520 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B17530201 : Blo 1401520 17530201 := bstep (se 2 (by rfl) ⟨6573825, by rfl⟩ : syracuseStep 17530201 = 13147651) B13147651
theorem B4103549 : Blo 1401520 4103549 := bstep (se 3 (by rfl) ⟨769415, by rfl⟩ : syracuseStep 4103549 = 1538831) B1538831
theorem B2104751 : Blo 1401520 2104751 := bstep (se 1 (by rfl) ⟨1578563, by rfl⟩ : syracuseStep 2104751 = 3157127) B3157127
theorem B21052853 : Blo 1401520 21052853 := bstep (se 5 (by rfl) ⟨986852, by rfl⟩ : syracuseStep 21052853 = 1973705) B1973705
theorem B2661815 : Blo 1401520 2661815 := bstep (se 1 (by rfl) ⟨1996361, by rfl⟩ : syracuseStep 2661815 = 3992723) B3992723
theorem B5324251 : Blo 1401520 5324251 := bstep (se 1 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 5324251 = 7986377) B7986377
theorem B2104841 : Blo 1401520 2104841 := bstep (se 2 (by rfl) ⟨789315, by rfl⟩ : syracuseStep 2104841 = 1578631) B1578631
theorem B4734503 : Blo 1401520 4734503 := bstep (se 1 (by rfl) ⟨3550877, by rfl⟩ : syracuseStep 4734503 = 7101755) B7101755
theorem B2104871 : Blo 1401520 2104871 := bstep (se 1 (by rfl) ⟨1578653, by rfl⟩ : syracuseStep 2104871 = 3157307) B3157307
theorem B2104955 : Blo 1401520 2104955 := bstep (se 1 (by rfl) ⟨1578716, by rfl⟩ : syracuseStep 2104955 = 3157433) B3157433
theorem B7986833 : Blo 1401520 7986833 := bstep (se 2 (by rfl) ⟨2995062, by rfl⟩ : syracuseStep 7986833 = 5990125) B5990125
theorem B4734611 : Blo 1401520 4734611 := bstep (se 1 (by rfl) ⟨3550958, by rfl⟩ : syracuseStep 4734611 = 7101917) B7101917
theorem B10116755 : Blo 1401520 10116755 := bstep (se 1 (by rfl) ⟨7587566, by rfl⟩ : syracuseStep 10116755 = 15175133) B15175133
theorem B2842283 : Blo 1401520 2842283 := bstep (se 1 (by rfl) ⟨2131712, by rfl⟩ : syracuseStep 2842283 = 4263425) B4263425
theorem B4800185 : Blo 1401520 4800185 := bstep (se 2 (by rfl) ⟨1800069, by rfl⟩ : syracuseStep 4800185 = 3600139) B3600139
theorem B2105081 : Blo 1401520 2105081 := bstep (se 2 (by rfl) ⟨789405, by rfl⟩ : syracuseStep 2105081 = 1578811) B1578811
theorem B90971909 : Blo 1401520 90971909 := bstep (se 4 (by rfl) ⟨8528616, by rfl⟩ : syracuseStep 90971909 = 17057233) B17057233
theorem B2662217 : Blo 1401520 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B2105183 : Blo 1401520 2105183 := bstep (se 1 (by rfl) ⟨1578887, by rfl⟩ : syracuseStep 2105183 = 3157775) B3157775
theorem B4734827 : Blo 1401520 4734827 := bstep (se 1 (by rfl) ⟨3551120, by rfl⟩ : syracuseStep 4734827 = 7102241) B7102241
theorem B2105195 : Blo 1401520 2105195 := bstep (se 1 (by rfl) ⟨1578896, by rfl⟩ : syracuseStep 2105195 = 3157793) B3157793
theorem B4734881 : Blo 1401520 4734881 := bstep (se 2 (by rfl) ⟨1775580, by rfl⟩ : syracuseStep 4734881 = 3551161) B3551161
theorem B2367407 : Blo 1401520 2367407 := bstep (se 1 (by rfl) ⟨1775555, by rfl⟩ : syracuseStep 2367407 = 3551111) B3551111
theorem B3243959 : Blo 1401520 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B3153851 : Blo 1401520 3153851 := bstep (se 1 (by rfl) ⟨2365388, by rfl⟩ : syracuseStep 3153851 = 4730777) B4730777
theorem B15982595 : Blo 1401520 15982595 := bstep (se 1 (by rfl) ⟨11986946, by rfl⟩ : syracuseStep 15982595 = 23973893) B23973893
theorem B5325011 : Blo 1401520 5325011 := bstep (se 1 (by rfl) ⟨3993758, by rfl⟩ : syracuseStep 5325011 = 7987517) B7987517
theorem B3154283 : Blo 1401520 3154283 := bstep (se 1 (by rfl) ⟨2365712, by rfl⟩ : syracuseStep 3154283 = 4731425) B4731425
theorem B3154427 : Blo 1401520 3154427 := bstep (se 1 (by rfl) ⟨2365820, by rfl⟩ : syracuseStep 3154427 = 4731641) B4731641
theorem B5054977 : Blo 1401520 5054977 := bstep (se 2 (by rfl) ⟨1895616, by rfl⟩ : syracuseStep 5054977 = 3791233) B3791233
theorem B2245241 : Blo 1401520 2245241 := bstep (se 2 (by rfl) ⟨841965, by rfl⟩ : syracuseStep 2245241 = 1683931) B1683931
theorem B3154553 : Blo 1401520 3154553 := bstep (se 2 (by rfl) ⟨1182957, by rfl⟩ : syracuseStep 3154553 = 2365915) B2365915
theorem B3154607 : Blo 1401520 3154607 := bstep (se 1 (by rfl) ⟨2365955, by rfl⟩ : syracuseStep 3154607 = 4731911) B4731911
theorem B2368183 : Blo 1401520 2368183 := bstep (se 1 (by rfl) ⟨1776137, by rfl⟩ : syracuseStep 2368183 = 3552275) B3552275
theorem B1401567 : Blo 1401520 1401567 := bstep (se 1 (by rfl) ⟨1051175, by rfl⟩ : syracuseStep 1401567 = 2102351) B2102351
theorem B3547871 : Blo 1401520 3547871 := bstep (se 1 (by rfl) ⟨2660903, by rfl⟩ : syracuseStep 3547871 = 5321807) B5321807
theorem B3154679 : Blo 1401520 3154679 := bstep (se 1 (by rfl) ⟨2366009, by rfl⟩ : syracuseStep 3154679 = 4732019) B4732019
theorem B1401647 : Blo 1401520 1401647 := bstep (se 1 (by rfl) ⟨1051235, by rfl⟩ : syracuseStep 1401647 = 2102471) B2102471
theorem B1401755 : Blo 1401520 1401755 := bstep (se 1 (by rfl) ⟨1051316, by rfl⟩ : syracuseStep 1401755 = 2102633) B2102633
theorem B3154859 : Blo 1401520 3154859 := bstep (se 1 (by rfl) ⟨2366144, by rfl⟩ : syracuseStep 3154859 = 4732289) B4732289
theorem B1401807 : Blo 1401520 1401807 := bstep (se 1 (by rfl) ⟨1051355, by rfl⟩ : syracuseStep 1401807 = 2102711) B2102711
theorem B1401831 : Blo 1401520 1401831 := bstep (se 1 (by rfl) ⟨1051373, by rfl⟩ : syracuseStep 1401831 = 2102747) B2102747
theorem B17966069 : Blo 1401520 17966069 := bstep (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) B1684319
theorem B40453181 : Blo 1401520 40453181 := bstep (se 3 (by rfl) ⟨7584971, by rfl⟩ : syracuseStep 40453181 = 15169943) B15169943
theorem B1402143 : Blo 1401520 1402143 := bstep (se 1 (by rfl) ⟨1051607, by rfl⟩ : syracuseStep 1402143 = 2103215) B2103215
theorem B14583077 : Blo 1401520 14583077 := bstep (se 4 (by rfl) ⟨1367163, by rfl⟩ : syracuseStep 14583077 = 2734327) B2734327
theorem B1402203 : Blo 1401520 1402203 := bstep (se 1 (by rfl) ⟨1051652, by rfl⟩ : syracuseStep 1402203 = 2103305) B2103305
theorem B1402223 : Blo 1401520 1402223 := bstep (se 1 (by rfl) ⟨1051667, by rfl⟩ : syracuseStep 1402223 = 2103335) B2103335
theorem B18220439 : Blo 1401520 18220439 := bstep (se 1 (by rfl) ⟨13665329, by rfl⟩ : syracuseStep 18220439 = 27330659) B27330659
theorem B1402279 : Blo 1401520 1402279 := bstep (se 1 (by rfl) ⟨1051709, by rfl⟩ : syracuseStep 1402279 = 2103419) B2103419
theorem B3155399 : Blo 1401520 3155399 := bstep (se 1 (by rfl) ⟨2366549, by rfl⟩ : syracuseStep 3155399 = 4733099) B4733099
theorem B1402363 : Blo 1401520 1402363 := bstep (se 1 (by rfl) ⟨1051772, by rfl⟩ : syracuseStep 1402363 = 2103545) B2103545
theorem B1402431 : Blo 1401520 1402431 := bstep (se 1 (by rfl) ⟨1051823, by rfl⟩ : syracuseStep 1402431 = 2103647) B2103647
theorem B1402439 : Blo 1401520 1402439 := bstep (se 1 (by rfl) ⟨1051829, by rfl⟩ : syracuseStep 1402439 = 2103659) B2103659
theorem B7104185 : Blo 1401520 7104185 := bstep (se 2 (by rfl) ⟨2664069, by rfl⟩ : syracuseStep 7104185 = 5328139) B5328139
theorem B11978441 : Blo 1401520 11978441 := bstep (se 2 (by rfl) ⟨4491915, by rfl⟩ : syracuseStep 11978441 = 8983831) B8983831
theorem B1402591 : Blo 1401520 1402591 := bstep (se 1 (by rfl) ⟨1051943, by rfl⟩ : syracuseStep 1402591 = 2103887) B2103887
theorem B3155759 : Blo 1401520 3155759 := bstep (se 1 (by rfl) ⟨2366819, by rfl⟩ : syracuseStep 3155759 = 4733639) B4733639
theorem B1402671 : Blo 1401520 1402671 := bstep (se 1 (by rfl) ⟨1052003, by rfl⟩ : syracuseStep 1402671 = 2104007) B2104007
theorem B1402779 : Blo 1401520 1402779 := bstep (se 1 (by rfl) ⟨1052084, by rfl⟩ : syracuseStep 1402779 = 2104169) B2104169
theorem B7096247 : Blo 1401520 7096247 := bstep (se 1 (by rfl) ⟨5322185, by rfl⟩ : syracuseStep 7096247 = 10644371) B10644371
theorem B1402831 : Blo 1401520 1402831 := bstep (se 1 (by rfl) ⟨1052123, by rfl⟩ : syracuseStep 1402831 = 2104247) B2104247
theorem B1402855 : Blo 1401520 1402855 := bstep (se 1 (by rfl) ⟨1052141, by rfl⟩ : syracuseStep 1402855 = 2104283) B2104283
theorem B14043331 : Blo 1401520 14043331 := bstep (se 1 (by rfl) ⟨10532498, by rfl⟩ : syracuseStep 14043331 = 21064997) B21064997
theorem B1403167 : Blo 1401520 1403167 := bstep (se 1 (by rfl) ⟨1052375, by rfl⟩ : syracuseStep 1403167 = 2104751) B2104751
theorem B14035235 : Blo 1401520 14035235 := bstep (se 1 (by rfl) ⟨10526426, by rfl⟩ : syracuseStep 14035235 = 21052853) B21052853
theorem B1403227 : Blo 1401520 1403227 := bstep (se 1 (by rfl) ⟨1052420, by rfl⟩ : syracuseStep 1403227 = 2104841) B2104841
theorem B3156335 : Blo 1401520 3156335 := bstep (se 1 (by rfl) ⟨2367251, by rfl⟩ : syracuseStep 3156335 = 4734503) B4734503
theorem B1403247 : Blo 1401520 1403247 := bstep (se 1 (by rfl) ⟨1052435, by rfl⟩ : syracuseStep 1403247 = 2104871) B2104871
theorem B23947649 : Blo 1401520 23947649 := bstep (se 2 (by rfl) ⟨8980368, by rfl⟩ : syracuseStep 23947649 = 17960737) B17960737
theorem B1403303 : Blo 1401520 1403303 := bstep (se 1 (by rfl) ⟨1052477, by rfl⟩ : syracuseStep 1403303 = 2104955) B2104955
theorem B10643885 : Blo 1401520 10643885 := bstep (se 3 (by rfl) ⟨1995728, by rfl⟩ : syracuseStep 10643885 = 3991457) B3991457
theorem B3156407 : Blo 1401520 3156407 := bstep (se 1 (by rfl) ⟨2367305, by rfl⟩ : syracuseStep 3156407 = 4734611) B4734611
theorem B6744503 : Blo 1401520 6744503 := bstep (se 1 (by rfl) ⟨5058377, by rfl⟩ : syracuseStep 6744503 = 10116755) B10116755
theorem B1894855 : Blo 1401520 1894855 := bstep (se 1 (by rfl) ⟨1421141, by rfl⟩ : syracuseStep 1894855 = 2842283) B2842283
theorem B10652147 : Blo 1401520 10652147 := bstep (se 1 (by rfl) ⟨7989110, by rfl⟩ : syracuseStep 10652147 = 15978221) B15978221
theorem B1403387 : Blo 1401520 1403387 := bstep (se 1 (by rfl) ⟨1052540, by rfl⟩ : syracuseStep 1403387 = 2105081) B2105081
theorem B60647939 : Blo 1401520 60647939 := bstep (se 1 (by rfl) ⟨45485954, by rfl⟩ : syracuseStep 60647939 = 90971909) B90971909
theorem B48597533 : Blo 1401520 48597533 := bstep (se 3 (by rfl) ⟨9112037, by rfl⟩ : syracuseStep 48597533 = 18224075) B18224075
theorem B7096895 : Blo 1401520 7096895 := bstep (se 1 (by rfl) ⟨5322671, by rfl⟩ : syracuseStep 7096895 = 10645343) B10645343
theorem B1403455 : Blo 1401520 1403455 := bstep (se 1 (by rfl) ⟨1052591, by rfl⟩ : syracuseStep 1403455 = 2105183) B2105183
theorem B3156551 : Blo 1401520 3156551 := bstep (se 1 (by rfl) ⟨2367413, by rfl⟩ : syracuseStep 3156551 = 4734827) B4734827
theorem B1403463 : Blo 1401520 1403463 := bstep (se 1 (by rfl) ⟨1052597, by rfl⟩ : syracuseStep 1403463 = 2105195) B2105195
theorem B3156587 : Blo 1401520 3156587 := bstep (se 1 (by rfl) ⟨2367440, by rfl⟩ : syracuseStep 3156587 = 4734881) B4734881
theorem B1895087 : Blo 1401520 1895087 := bstep (se 1 (by rfl) ⟨1421315, by rfl⟩ : syracuseStep 1895087 = 2842631) B2842631
theorem B11987837 : Blo 1401520 11987837 := bstep (se 3 (by rfl) ⟨2247719, by rfl⟩ : syracuseStep 11987837 = 4495439) B4495439
theorem B3845107 : Blo 1401520 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B3156983 : Blo 1401520 3156983 := bstep (se 1 (by rfl) ⟨2367737, by rfl⟩ : syracuseStep 3156983 = 4735475) B4735475
theorem B3550331 : Blo 1401520 3550331 := bstep (se 1 (by rfl) ⟨2662748, by rfl⟩ : syracuseStep 3550331 = 5325497) B5325497
theorem B3550351 : Blo 1401520 3550351 := bstep (se 1 (by rfl) ⟨2662763, by rfl⟩ : syracuseStep 3550351 = 5325527) B5325527
theorem B6401213 : Blo 1401520 6401213 := bstep (se 3 (by rfl) ⟨1200227, by rfl⟩ : syracuseStep 6401213 = 2400455) B2400455
theorem B2133287 : Blo 1401520 2133287 := bstep (se 1 (by rfl) ⟨1599965, by rfl⟩ : syracuseStep 2133287 = 3199931) B3199931
theorem B3157343 : Blo 1401520 3157343 := bstep (se 1 (by rfl) ⟨2368007, by rfl⟩ : syracuseStep 3157343 = 4736015) B4736015
theorem B3550625 : Blo 1401520 3550625 := bstep (se 2 (by rfl) ⟨1331484, by rfl⟩ : syracuseStep 3550625 = 2662969) B2662969
theorem B3599777 : Blo 1401520 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B15380077 : Blo 1401520 15380077 := bstep (se 3 (by rfl) ⟨2883764, by rfl⟩ : syracuseStep 15380077 = 5767529) B5767529
theorem B3157739 : Blo 1401520 3157739 := bstep (se 1 (by rfl) ⟨2368304, by rfl⟩ : syracuseStep 3157739 = 4736609) B4736609
theorem B6737737 : Blo 1401520 6737737 := bstep (se 2 (by rfl) ⟨2526651, by rfl⟩ : syracuseStep 6737737 = 5053303) B5053303
theorem B3157865 : Blo 1401520 3157865 := bstep (se 2 (by rfl) ⟨1184199, by rfl⟩ : syracuseStep 3157865 = 2368399) B2368399
theorem B8990621 : Blo 1401520 8990621 := bstep (se 3 (by rfl) ⟨1685741, by rfl⟩ : syracuseStep 8990621 = 3371483) B3371483
theorem B4730939 : Blo 1401520 4730939 := bstep (se 1 (by rfl) ⟨3548204, by rfl⟩ : syracuseStep 4730939 = 7096409) B7096409
theorem B8523947 : Blo 1401520 8523947 := bstep (se 1 (by rfl) ⟨6392960, by rfl⟩ : syracuseStep 8523947 = 12785921) B12785921
theorem B3371273 : Blo 1401520 3371273 := bstep (se 2 (by rfl) ⟨1264227, by rfl⟩ : syracuseStep 3371273 = 2528455) B2528455
theorem B4731209 : Blo 1401520 4731209 := bstep (se 2 (by rfl) ⟨1774203, by rfl⟩ : syracuseStep 4731209 = 3548407) B3548407
theorem B12800371 : Blo 1401520 12800371 := bstep (se 1 (by rfl) ⟨9600278, by rfl⟩ : syracuseStep 12800371 = 19200557) B19200557
theorem B1773991 : Blo 1401520 1773991 := bstep (se 1 (by rfl) ⟨1330493, by rfl⟩ : syracuseStep 1773991 = 2660987) B2660987
theorem B1896871 : Blo 1401520 1896871 := bstep (se 1 (by rfl) ⟨1422653, by rfl⟩ : syracuseStep 1896871 = 2845307) B2845307
theorem B73855469 : Blo 1401520 73855469 := bstep (se 3 (by rfl) ⟨13847900, by rfl⟩ : syracuseStep 73855469 = 27695801) B27695801
theorem B4493825 : Blo 1401520 4493825 := bstep (se 2 (by rfl) ⟨1685184, by rfl⟩ : syracuseStep 4493825 = 3370369) B3370369
theorem B7099001 : Blo 1401520 7099001 := bstep (se 2 (by rfl) ⟨2662125, by rfl⟩ : syracuseStep 7099001 = 5324251) B5324251
theorem B1577695 : Blo 1401520 1577695 := bstep (se 1 (by rfl) ⟨1183271, by rfl⟩ : syracuseStep 1577695 = 2366543) B2366543
theorem B1774315 : Blo 1401520 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B10646315 : Blo 1401520 10646315 := bstep (se 1 (by rfl) ⟨7984736, by rfl⟩ : syracuseStep 10646315 = 15969473) B15969473
theorem B6574891 : Blo 1401520 6574891 := bstep (se 1 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 6574891 = 9862337) B9862337
theorem B1774543 : Blo 1401520 1774543 := bstep (se 1 (by rfl) ⟨1330907, by rfl⟩ : syracuseStep 1774543 = 2661815) B2661815
theorem B3552295 : Blo 1401520 3552295 := bstep (se 1 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 3552295 = 5328443) B5328443
theorem B11973689 : Blo 1401520 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B17962073 : Blo 1401520 17962073 := bstep (se 2 (by rfl) ⟨6735777, by rfl⟩ : syracuseStep 17962073 = 13471555) B13471555
theorem B874386521 : Blo 1401520 874386521 := bstep (se 2 (by rfl) ⟨327894945, by rfl⟩ : syracuseStep 874386521 = 655789891) B655789891
theorem B3200123 : Blo 1401520 3200123 := bstep (se 1 (by rfl) ⟨2400092, by rfl⟩ : syracuseStep 3200123 = 4800185) B4800185
theorem B1774811 : Blo 1401520 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B4158707 : Blo 1401520 4158707 := bstep (se 1 (by rfl) ⟨3119030, by rfl⟩ : syracuseStep 4158707 = 6238061) B6238061
theorem B1578271 : Blo 1401520 1578271 := bstep (se 1 (by rfl) ⟨1183703, by rfl⟩ : syracuseStep 1578271 = 2367407) B2367407
theorem B2102567 : Blo 1401520 2102567 := bstep (se 1 (by rfl) ⟨1576925, by rfl⟩ : syracuseStep 2102567 = 3153851) B3153851
theorem B2102651 : Blo 1401520 2102651 := bstep (se 1 (by rfl) ⟨1576988, by rfl⟩ : syracuseStep 2102651 = 3153977) B3153977
theorem B2102777 : Blo 1401520 2102777 := bstep (se 2 (by rfl) ⟨788541, by rfl⟩ : syracuseStep 2102777 = 1577083) B1577083
theorem B13473287 : Blo 1401520 13473287 := bstep (se 1 (by rfl) ⟨10104965, by rfl⟩ : syracuseStep 13473287 = 20209931) B20209931
theorem B1578559 : Blo 1401520 1578559 := bstep (se 1 (by rfl) ⟨1183919, by rfl⟩ : syracuseStep 1578559 = 2367839) B2367839
theorem B2102879 : Blo 1401520 2102879 := bstep (se 1 (by rfl) ⟨1577159, by rfl⟩ : syracuseStep 2102879 = 3154319) B3154319
theorem B1775287 : Blo 1401520 1775287 := bstep (se 1 (by rfl) ⟨1331465, by rfl⟩ : syracuseStep 1775287 = 2662931) B2662931
theorem B1799863 : Blo 1401520 1799863 := bstep (se 1 (by rfl) ⟨1349897, by rfl⟩ : syracuseStep 1799863 = 2699795) B2699795
theorem B2103095 : Blo 1401520 2103095 := bstep (se 1 (by rfl) ⟨1577321, by rfl⟩ : syracuseStep 2103095 = 3154643) B3154643
theorem B1775515 : Blo 1401520 1775515 := bstep (se 1 (by rfl) ⟨1331636, by rfl⟩ : syracuseStep 1775515 = 2663273) B2663273
theorem B11376683 : Blo 1401520 11376683 := bstep (se 1 (by rfl) ⟨8532512, by rfl⟩ : syracuseStep 11376683 = 17065025) B17065025
theorem B2103401 : Blo 1401520 2103401 := bstep (se 2 (by rfl) ⟨788775, by rfl⟩ : syracuseStep 2103401 = 1577551) B1577551
theorem B27326771 : Blo 1401520 27326771 := bstep (se 1 (by rfl) ⟨20495078, by rfl⟩ : syracuseStep 27326771 = 40990157) B40990157
theorem B2365787 : Blo 1401520 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B2365807 : Blo 1401520 2365807 := bstep (se 1 (by rfl) ⟨1774355, by rfl⟩ : syracuseStep 2365807 = 3548711) B3548711
theorem B7100783 : Blo 1401520 7100783 := bstep (se 1 (by rfl) ⟨5325587, by rfl⟩ : syracuseStep 7100783 = 10651175) B10651175
theorem B2103719 : Blo 1401520 2103719 := bstep (se 1 (by rfl) ⟨1577789, by rfl⟩ : syracuseStep 2103719 = 3155579) B3155579
theorem B5986811 : Blo 1401520 5986811 := bstep (se 1 (by rfl) ⟨4490108, by rfl⟩ : syracuseStep 5986811 = 8980217) B8980217
theorem B2103803 : Blo 1401520 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B2366023 : Blo 1401520 2366023 := bstep (se 1 (by rfl) ⟨1774517, by rfl⟩ : syracuseStep 2366023 = 3549035) B3549035
theorem B2103929 : Blo 1401520 2103929 := bstep (se 2 (by rfl) ⟨788973, by rfl⟩ : syracuseStep 2103929 = 1577947) B1577947
theorem B2103983 : Blo 1401520 2103983 := bstep (se 1 (by rfl) ⟨1577987, by rfl⟩ : syracuseStep 2103983 = 3155975) B3155975
theorem B10648259 : Blo 1401520 10648259 := bstep (se 1 (by rfl) ⟨7986194, by rfl⟩ : syracuseStep 10648259 = 15972389) B15972389
theorem B2398943 : Blo 1401520 2398943 := bstep (se 1 (by rfl) ⟨1799207, by rfl⟩ : syracuseStep 2398943 = 3598415) B3598415
theorem B2104031 : Blo 1401520 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B2997071 : Blo 1401520 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B2661275 : Blo 1401520 2661275 := bstep (se 1 (by rfl) ⟨1995956, by rfl⟩ : syracuseStep 2661275 = 3991913) B3991913
theorem B2104295 : Blo 1401520 2104295 := bstep (se 1 (by rfl) ⟨1578221, by rfl⟩ : syracuseStep 2104295 = 3156443) B3156443
theorem B26950643 : Blo 1401520 26950643 := bstep (se 1 (by rfl) ⟨20212982, by rfl⟩ : syracuseStep 26950643 = 40425965) B40425965
theorem B2366455 : Blo 1401520 2366455 := bstep (se 1 (by rfl) ⟨1774841, by rfl⟩ : syracuseStep 2366455 = 3549683) B3549683
theorem B93494405 : Blo 1401520 93494405 := bstep (se 4 (by rfl) ⟨8765100, by rfl⟩ : syracuseStep 93494405 = 17530201) B17530201
theorem B11377853 : Blo 1401520 11377853 := bstep (se 3 (by rfl) ⟨2133347, by rfl⟩ : syracuseStep 11377853 = 4266695) B4266695
theorem B23960771 : Blo 1401520 23960771 := bstep (se 1 (by rfl) ⟨17970578, by rfl⟩ : syracuseStep 23960771 = 35941157) B35941157
theorem B2104553 : Blo 1401520 2104553 := bstep (se 2 (by rfl) ⟨789207, by rfl⟩ : syracuseStep 2104553 = 1578415) B1578415
theorem B2997481 : Blo 1401520 2997481 := bstep (se 2 (by rfl) ⟨1124055, by rfl⟩ : syracuseStep 2997481 = 2248111) B2248111
theorem B2104607 : Blo 1401520 2104607 := bstep (se 1 (by rfl) ⟨1578455, by rfl⟩ : syracuseStep 2104607 = 3156911) B3156911
theorem B2366759 : Blo 1401520 2366759 := bstep (se 1 (by rfl) ⟨1775069, by rfl⟩ : syracuseStep 2366759 = 3550139) B3550139
theorem B3792251 : Blo 1401520 3792251 := bstep (se 1 (by rfl) ⟨2844188, by rfl⟩ : syracuseStep 3792251 = 5688377) B5688377
theorem B3464585 : Blo 1401520 3464585 := bstep (se 2 (by rfl) ⟨1299219, by rfl⟩ : syracuseStep 3464585 = 2598439) B2598439
theorem B4734395 : Blo 1401520 4734395 := bstep (se 1 (by rfl) ⟨3550796, by rfl⟩ : syracuseStep 4734395 = 7101593) B7101593
theorem B2104775 : Blo 1401520 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B3153491 : Blo 1401520 3153491 := bstep (se 1 (by rfl) ⟨2365118, by rfl⟩ : syracuseStep 3153491 = 4730237) B4730237
theorem B7577171 : Blo 1401520 7577171 := bstep (se 1 (by rfl) ⟨5682878, by rfl⟩ : syracuseStep 7577171 = 11365757) B11365757
theorem B2735699 : Blo 1401520 2735699 := bstep (se 1 (by rfl) ⟨2051774, by rfl⟩ : syracuseStep 2735699 = 4103549) B4103549
theorem B2367211 : Blo 1401520 2367211 := bstep (se 1 (by rfl) ⟨1775408, by rfl⟩ : syracuseStep 2367211 = 3550817) B3550817
theorem B3153671 : Blo 1401520 3153671 := bstep (se 1 (by rfl) ⟨2365253, by rfl⟩ : syracuseStep 3153671 = 4730507) B4730507
theorem B5324555 : Blo 1401520 5324555 := bstep (se 1 (by rfl) ⟨3993416, by rfl⟩ : syracuseStep 5324555 = 7986833) B7986833
theorem B2105129 : Blo 1401520 2105129 := bstep (se 2 (by rfl) ⟨789423, by rfl⟩ : syracuseStep 2105129 = 1578847) B1578847
theorem B5988143 : Blo 1401520 5988143 := bstep (se 1 (by rfl) ⟨4491107, by rfl⟩ : syracuseStep 5988143 = 8982215) B8982215
theorem B2105135 : Blo 1401520 2105135 := bstep (se 1 (by rfl) ⟨1578851, by rfl⟩ : syracuseStep 2105135 = 3157703) B3157703
theorem B2162639 : Blo 1401520 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B3153959 : Blo 1401520 3153959 := bstep (se 1 (by rfl) ⟨2365469, by rfl⟩ : syracuseStep 3153959 = 4730939) B4730939
theorem B3154139 : Blo 1401520 3154139 := bstep (se 1 (by rfl) ⟨2365604, by rfl⟩ : syracuseStep 3154139 = 4731209) B4731209
theorem B3154409 : Blo 1401520 3154409 := bstep (se 2 (by rfl) ⟨1182903, by rfl⟩ : syracuseStep 3154409 = 2365807) B2365807
theorem B11977379 : Blo 1401520 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B26968787 : Blo 1401520 26968787 := bstep (se 1 (by rfl) ⟨20226590, by rfl⟩ : syracuseStep 26968787 = 40453181) B40453181
theorem B3154697 : Blo 1401520 3154697 := bstep (se 2 (by rfl) ⟨1183011, by rfl⟩ : syracuseStep 3154697 = 2366023) B2366023
theorem B1401711 : Blo 1401520 1401711 := bstep (se 1 (by rfl) ⟨1051283, by rfl⟩ : syracuseStep 1401711 = 2102567) B2102567
theorem B29180789 : Blo 1401520 29180789 := bstep (se 5 (by rfl) ⟨1367849, by rfl⟩ : syracuseStep 29180789 = 2735699) B2735699
theorem B1401767 : Blo 1401520 1401767 := bstep (se 1 (by rfl) ⟨1051325, by rfl⟩ : syracuseStep 1401767 = 2102651) B2102651
theorem B1401851 : Blo 1401520 1401851 := bstep (se 1 (by rfl) ⟨1051388, by rfl⟩ : syracuseStep 1401851 = 2102777) B2102777
theorem B8766521 : Blo 1401520 8766521 := bstep (se 2 (by rfl) ⟨3287445, by rfl⟩ : syracuseStep 8766521 = 6574891) B6574891
theorem B1401919 : Blo 1401520 1401919 := bstep (se 1 (by rfl) ⟨1051439, by rfl⟩ : syracuseStep 1401919 = 2102879) B2102879
theorem B4736123 : Blo 1401520 4736123 := bstep (se 1 (by rfl) ⟨3552092, by rfl⟩ : syracuseStep 4736123 = 7104185) B7104185
theorem B38397077 : Blo 1401520 38397077 := bstep (se 6 (by rfl) ⟨899931, by rfl⟩ : syracuseStep 38397077 = 1799863) B1799863
theorem B1402063 : Blo 1401520 1402063 := bstep (se 1 (by rfl) ⟨1051547, by rfl⟩ : syracuseStep 1402063 = 2103095) B2103095
theorem B3155273 : Blo 1401520 3155273 := bstep (se 2 (by rfl) ⟨1183227, by rfl⟩ : syracuseStep 3155273 = 2366455) B2366455
theorem B4736393 : Blo 1401520 4736393 := bstep (se 2 (by rfl) ⟨1776147, by rfl⟩ : syracuseStep 4736393 = 3552295) B3552295
theorem B1402267 : Blo 1401520 1402267 := bstep (se 1 (by rfl) ⟨1051700, by rfl⟩ : syracuseStep 1402267 = 2103401) B2103401
theorem B1402479 : Blo 1401520 1402479 := bstep (se 1 (by rfl) ⟨1051859, by rfl⟩ : syracuseStep 1402479 = 2103719) B2103719
theorem B7095923 : Blo 1401520 7095923 := bstep (se 1 (by rfl) ⟨5321942, by rfl⟩ : syracuseStep 7095923 = 10643885) B10643885
theorem B3991207 : Blo 1401520 3991207 := bstep (se 1 (by rfl) ⟨2993405, by rfl⟩ : syracuseStep 3991207 = 5986811) B5986811
theorem B1402535 : Blo 1401520 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B1402619 : Blo 1401520 1402619 := bstep (se 1 (by rfl) ⟨1051964, by rfl⟩ : syracuseStep 1402619 = 2103929) B2103929
theorem B1402655 : Blo 1401520 1402655 := bstep (se 1 (by rfl) ⟨1051991, by rfl⟩ : syracuseStep 1402655 = 2103983) B2103983
theorem B1402687 : Blo 1401520 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B1402863 : Blo 1401520 1402863 := bstep (se 1 (by rfl) ⟨1052147, by rfl⟩ : syracuseStep 1402863 = 2104295) B2104295
theorem B17967095 : Blo 1401520 17967095 := bstep (se 1 (by rfl) ⟨13475321, by rfl⟩ : syracuseStep 17967095 = 26950643) B26950643
theorem B20506769 : Blo 1401520 20506769 := bstep (se 2 (by rfl) ⟨7690038, by rfl⟩ : syracuseStep 20506769 = 15380077) B15380077
theorem B1403035 : Blo 1401520 1403035 := bstep (se 1 (by rfl) ⟨1052276, by rfl⟩ : syracuseStep 1403035 = 2104553) B2104553
theorem B1403071 : Blo 1401520 1403071 := bstep (se 1 (by rfl) ⟨1052303, by rfl⟩ : syracuseStep 1403071 = 2104607) B2104607
theorem B3156263 : Blo 1401520 3156263 := bstep (se 1 (by rfl) ⟨2367197, by rfl⟩ : syracuseStep 3156263 = 4734395) B4734395
theorem B1403183 : Blo 1401520 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B3156281 : Blo 1401520 3156281 := bstep (se 2 (by rfl) ⟨1183605, by rfl⟩ : syracuseStep 3156281 = 2367211) B2367211
theorem B7096733 : Blo 1401520 7096733 := bstep (se 3 (by rfl) ⟨1330637, by rfl⟩ : syracuseStep 7096733 = 2661275) B2661275
theorem B3549703 : Blo 1401520 3549703 := bstep (se 1 (by rfl) ⟨2662277, by rfl⟩ : syracuseStep 3549703 = 5324555) B5324555
theorem B1403419 : Blo 1401520 1403419 := bstep (se 1 (by rfl) ⟨1052564, by rfl⟩ : syracuseStep 1403419 = 2105129) B2105129
theorem B3992095 : Blo 1401520 3992095 := bstep (se 1 (by rfl) ⟨2994071, by rfl⟩ : syracuseStep 3992095 = 5988143) B5988143
theorem B1403423 : Blo 1401520 1403423 := bstep (se 1 (by rfl) ⟨1052567, by rfl⟩ : syracuseStep 1403423 = 2105135) B2105135
theorem B3550007 : Blo 1401520 3550007 := bstep (se 1 (by rfl) ⟨2662505, by rfl⟩ : syracuseStep 3550007 = 5325011) B5325011
theorem B2247515 : Blo 1401520 2247515 := bstep (se 1 (by rfl) ⟨1685636, by rfl⟩ : syracuseStep 2247515 = 3371273) B3371273
theorem B49236979 : Blo 1401520 49236979 := bstep (se 1 (by rfl) ⟨36927734, by rfl⟩ : syracuseStep 49236979 = 73855469) B73855469
theorem B17067161 : Blo 1401520 17067161 := bstep (se 2 (by rfl) ⟨6400185, by rfl⟩ : syracuseStep 17067161 = 12800371) B12800371
theorem B7097543 : Blo 1401520 7097543 := bstep (se 1 (by rfl) ⟨5323157, by rfl⟩ : syracuseStep 7097543 = 10646315) B10646315
theorem B2526473 : Blo 1401520 2526473 := bstep (se 2 (by rfl) ⟨947427, by rfl⟩ : syracuseStep 2526473 = 1894855) B1894855
theorem B7982459 : Blo 1401520 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B2133415 : Blo 1401520 2133415 := bstep (se 1 (by rfl) ⟨1600061, by rfl⟩ : syracuseStep 2133415 = 3200123) B3200123
theorem B3157577 : Blo 1401520 3157577 := bstep (se 2 (by rfl) ⟨1184091, by rfl⟩ : syracuseStep 3157577 = 2368183) B2368183
theorem B8982191 : Blo 1401520 8982191 := bstep (se 1 (by rfl) ⟨6736643, by rfl⟩ : syracuseStep 8982191 = 13473287) B13473287
theorem B17985341 : Blo 1401520 17985341 := bstep (se 3 (by rfl) ⟨3372251, by rfl⟩ : syracuseStep 17985341 = 6744503) B6744503
theorem B4730831 : Blo 1401520 4730831 := bstep (se 1 (by rfl) ⟨3548123, by rfl⟩ : syracuseStep 4730831 = 7096247) B7096247
theorem B1577191 : Blo 1401520 1577191 := bstep (se 1 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 1577191 = 2365787) B2365787
theorem B40431959 : Blo 1401520 40431959 := bstep (se 1 (by rfl) ⟨30323969, by rfl⟩ : syracuseStep 40431959 = 60647939) B60647939
theorem B4731263 : Blo 1401520 4731263 := bstep (se 1 (by rfl) ⟨3548447, by rfl⟩ : syracuseStep 4731263 = 7096895) B7096895
theorem B7098839 : Blo 1401520 7098839 := bstep (se 1 (by rfl) ⟨5324129, by rfl⟩ : syracuseStep 7098839 = 10648259) B10648259
theorem B7991891 : Blo 1401520 7991891 := bstep (se 1 (by rfl) ⟨5993918, by rfl⟩ : syracuseStep 7991891 = 11987837) B11987837
theorem B62329603 : Blo 1401520 62329603 := bstep (se 1 (by rfl) ⟨46747202, by rfl⟩ : syracuseStep 62329603 = 93494405) B93494405
theorem B1577839 : Blo 1401520 1577839 := bstep (se 1 (by rfl) ⟨1183379, by rfl⟩ : syracuseStep 1577839 = 2366759) B2366759
theorem B1422191 : Blo 1401520 1422191 := bstep (se 1 (by rfl) ⟨1066643, by rfl⟩ : syracuseStep 1422191 = 2133287) B2133287
theorem B2528167 : Blo 1401520 2528167 := bstep (se 1 (by rfl) ⟨1896125, by rfl⟩ : syracuseStep 2528167 = 3792251) B3792251
theorem B2102327 : Blo 1401520 2102327 := bstep (se 1 (by rfl) ⟨1576745, by rfl⟩ : syracuseStep 2102327 = 3153491) B3153491
theorem B5051447 : Blo 1401520 5051447 := bstep (se 1 (by rfl) ⟨3788585, by rfl⟩ : syracuseStep 5051447 = 7577171) B7577171
theorem B8983649 : Blo 1401520 8983649 := bstep (se 2 (by rfl) ⟨3368868, by rfl⟩ : syracuseStep 8983649 = 6737737) B6737737
theorem B2102447 : Blo 1401520 2102447 := bstep (se 1 (by rfl) ⟨1576835, by rfl⟩ : syracuseStep 2102447 = 3153671) B3153671
theorem B5993747 : Blo 1401520 5993747 := bstep (se 1 (by rfl) ⟨4495310, by rfl⟩ : syracuseStep 5993747 = 8990621) B8990621
theorem B10655063 : Blo 1401520 10655063 := bstep (se 1 (by rfl) ⟨7991297, by rfl⟩ : syracuseStep 10655063 = 15982595) B15982595
theorem B5682631 : Blo 1401520 5682631 := bstep (se 1 (by rfl) ⟨4261973, by rfl⟩ : syracuseStep 5682631 = 8523947) B8523947
theorem B2102855 : Blo 1401520 2102855 := bstep (se 1 (by rfl) ⟨1577141, by rfl⟩ : syracuseStep 2102855 = 3154283) B3154283
theorem B18724441 : Blo 1401520 18724441 := bstep (se 2 (by rfl) ⟨7021665, by rfl⟩ : syracuseStep 18724441 = 14043331) B14043331
theorem B2102951 : Blo 1401520 2102951 := bstep (se 1 (by rfl) ⟨1577213, by rfl⟩ : syracuseStep 2102951 = 3154427) B3154427
theorem B2995883 : Blo 1401520 2995883 := bstep (se 1 (by rfl) ⟨2246912, by rfl⟩ : syracuseStep 2995883 = 4493825) B4493825
theorem B1496827 : Blo 1401520 1496827 := bstep (se 1 (by rfl) ⟨1122620, by rfl⟩ : syracuseStep 1496827 = 2245241) B2245241
theorem B2103035 : Blo 1401520 2103035 := bstep (se 1 (by rfl) ⟨1577276, by rfl⟩ : syracuseStep 2103035 = 3154553) B3154553
theorem B4732667 : Blo 1401520 4732667 := bstep (se 1 (by rfl) ⟨3549500, by rfl⟩ : syracuseStep 4732667 = 7099001) B7099001
theorem B2103071 : Blo 1401520 2103071 := bstep (se 1 (by rfl) ⟨1577303, by rfl⟩ : syracuseStep 2103071 = 3154607) B3154607
theorem B2365247 : Blo 1401520 2365247 := bstep (se 1 (by rfl) ⟨1773935, by rfl⟩ : syracuseStep 2365247 = 3547871) B3547871
theorem B2103119 : Blo 1401520 2103119 := bstep (se 1 (by rfl) ⟨1577339, by rfl⟩ : syracuseStep 2103119 = 3154679) B3154679
theorem B2365321 : Blo 1401520 2365321 := bstep (se 2 (by rfl) ⟨886995, by rfl⟩ : syracuseStep 2365321 = 1773991) B1773991
theorem B2529161 : Blo 1401520 2529161 := bstep (se 2 (by rfl) ⟨948435, by rfl⟩ : syracuseStep 2529161 = 1896871) B1896871
theorem B4732829 : Blo 1401520 4732829 := bstep (se 3 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 4732829 = 1774811) B1774811
theorem B2103239 : Blo 1401520 2103239 := bstep (se 1 (by rfl) ⟨1577429, by rfl⟩ : syracuseStep 2103239 = 3154859) B3154859
theorem B11089885 : Blo 1401520 11089885 := bstep (se 3 (by rfl) ⟨2079353, by rfl⟩ : syracuseStep 11089885 = 4158707) B4158707
theorem B6739969 : Blo 1401520 6739969 := bstep (se 2 (by rfl) ⟨2527488, by rfl⟩ : syracuseStep 6739969 = 5054977) B5054977
theorem B11974715 : Blo 1401520 11974715 := bstep (se 1 (by rfl) ⟨8981036, by rfl⟩ : syracuseStep 11974715 = 17962073) B17962073
theorem B582924347 : Blo 1401520 582924347 := bstep (se 1 (by rfl) ⟨437193260, by rfl⟩ : syracuseStep 582924347 = 874386521) B874386521
theorem B37427293 : Blo 1401520 37427293 := bstep (se 3 (by rfl) ⟨7017617, by rfl⟩ : syracuseStep 37427293 = 14035235) B14035235
theorem B9722051 : Blo 1401520 9722051 := bstep (se 1 (by rfl) ⟨7291538, by rfl⟩ : syracuseStep 9722051 = 14583077) B14583077
theorem B12146959 : Blo 1401520 12146959 := bstep (se 1 (by rfl) ⟨9110219, by rfl⟩ : syracuseStep 12146959 = 18220439) B18220439
theorem B2103593 : Blo 1401520 2103593 := bstep (se 2 (by rfl) ⟨788847, by rfl⟩ : syracuseStep 2103593 = 1577695) B1577695
theorem B2103599 : Blo 1401520 2103599 := bstep (se 1 (by rfl) ⟨1577699, by rfl⟩ : syracuseStep 2103599 = 3155399) B3155399
theorem B2365753 : Blo 1401520 2365753 := bstep (se 2 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 2365753 = 1774315) B1774315
theorem B7985627 : Blo 1401520 7985627 := bstep (se 1 (by rfl) ⟨5989220, by rfl⟩ : syracuseStep 7985627 = 11978441) B11978441
theorem B2103839 : Blo 1401520 2103839 := bstep (se 1 (by rfl) ⟨1577879, by rfl⟩ : syracuseStep 2103839 = 3155759) B3155759
theorem B2366057 : Blo 1401520 2366057 := bstep (se 2 (by rfl) ⟨887271, by rfl⟩ : syracuseStep 2366057 = 1774543) B1774543
theorem B5126809 : Blo 1401520 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B7584455 : Blo 1401520 7584455 := bstep (se 1 (by rfl) ⟨5688341, by rfl⟩ : syracuseStep 7584455 = 11376683) B11376683
theorem B4733801 : Blo 1401520 4733801 := bstep (se 2 (by rfl) ⟨1775175, by rfl⟩ : syracuseStep 4733801 = 3550351) B3550351
theorem B18217847 : Blo 1401520 18217847 := bstep (se 1 (by rfl) ⟨13663385, by rfl⟩ : syracuseStep 18217847 = 27326771) B27326771
theorem B4733855 : Blo 1401520 4733855 := bstep (se 1 (by rfl) ⟨3550391, by rfl⟩ : syracuseStep 4733855 = 7100783) B7100783
theorem B2104223 : Blo 1401520 2104223 := bstep (se 1 (by rfl) ⟨1578167, by rfl⟩ : syracuseStep 2104223 = 3156335) B3156335
theorem B15965099 : Blo 1401520 15965099 := bstep (se 1 (by rfl) ⟨11973824, by rfl⟩ : syracuseStep 15965099 = 23947649) B23947649
theorem B2104271 : Blo 1401520 2104271 := bstep (se 1 (by rfl) ⟨1578203, by rfl⟩ : syracuseStep 2104271 = 3156407) B3156407
theorem B3996641 : Blo 1401520 3996641 := bstep (se 2 (by rfl) ⟨1498740, by rfl⟩ : syracuseStep 3996641 = 2997481) B2997481
theorem B7101431 : Blo 1401520 7101431 := bstep (se 1 (by rfl) ⟨5326073, by rfl⟩ : syracuseStep 7101431 = 10652147) B10652147
theorem B32398355 : Blo 1401520 32398355 := bstep (se 1 (by rfl) ⟨24298766, by rfl⟩ : syracuseStep 32398355 = 48597533) B48597533
theorem B2104361 : Blo 1401520 2104361 := bstep (se 2 (by rfl) ⟨789135, by rfl⟩ : syracuseStep 2104361 = 1578271) B1578271
theorem B2104367 : Blo 1401520 2104367 := bstep (se 1 (by rfl) ⟨1578275, by rfl⟩ : syracuseStep 2104367 = 3156551) B3156551
theorem B2104391 : Blo 1401520 2104391 := bstep (se 1 (by rfl) ⟨1578293, by rfl⟩ : syracuseStep 2104391 = 3156587) B3156587
theorem B5053565 : Blo 1401520 5053565 := bstep (se 3 (by rfl) ⟨947543, by rfl⟩ : syracuseStep 5053565 = 1895087) B1895087
theorem B1998047 : Blo 1401520 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B6397181 : Blo 1401520 6397181 := bstep (se 3 (by rfl) ⟨1199471, by rfl⟩ : syracuseStep 6397181 = 2398943) B2398943
theorem B2104655 : Blo 1401520 2104655 := bstep (se 1 (by rfl) ⟨1578491, by rfl⟩ : syracuseStep 2104655 = 3156983) B3156983
theorem B2366887 : Blo 1401520 2366887 := bstep (se 1 (by rfl) ⟨1775165, by rfl⟩ : syracuseStep 2366887 = 3550331) B3550331
theorem B2104745 : Blo 1401520 2104745 := bstep (se 2 (by rfl) ⟨789279, by rfl⟩ : syracuseStep 2104745 = 1578559) B1578559
theorem B7585235 : Blo 1401520 7585235 := bstep (se 1 (by rfl) ⟨5688926, by rfl⟩ : syracuseStep 7585235 = 11377853) B11377853
theorem B4267475 : Blo 1401520 4267475 := bstep (se 1 (by rfl) ⟨3200606, by rfl⟩ : syracuseStep 4267475 = 6401213) B6401213
theorem B15973847 : Blo 1401520 15973847 := bstep (se 1 (by rfl) ⟨11980385, by rfl⟩ : syracuseStep 15973847 = 23960771) B23960771
theorem B2104895 : Blo 1401520 2104895 := bstep (se 1 (by rfl) ⟨1578671, by rfl⟩ : syracuseStep 2104895 = 3157343) B3157343
theorem B2367049 : Blo 1401520 2367049 := bstep (se 2 (by rfl) ⟨887643, by rfl⟩ : syracuseStep 2367049 = 1775287) B1775287
theorem B2309723 : Blo 1401520 2309723 := bstep (se 1 (by rfl) ⟨1732292, by rfl⟩ : syracuseStep 2309723 = 3464585) B3464585
theorem B2367083 : Blo 1401520 2367083 := bstep (se 1 (by rfl) ⟨1775312, by rfl⟩ : syracuseStep 2367083 = 3550625) B3550625
theorem B2399851 : Blo 1401520 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B2105159 : Blo 1401520 2105159 := bstep (se 1 (by rfl) ⟨1578869, by rfl⟩ : syracuseStep 2105159 = 3157739) B3157739
theorem B2367353 : Blo 1401520 2367353 := bstep (se 2 (by rfl) ⟨887757, by rfl⟩ : syracuseStep 2367353 = 1775515) B1775515
theorem B5767037 : Blo 1401520 5767037 := bstep (se 3 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 5767037 = 2162639) B2162639
theorem B2105243 : Blo 1401520 2105243 := bstep (se 1 (by rfl) ⟨1578932, by rfl⟩ : syracuseStep 2105243 = 3157865) B3157865
theorem B8986625 : Blo 1401520 8986625 := bstep (se 2 (by rfl) ⟨3369984, by rfl⟩ : syracuseStep 8986625 = 6739969) B6739969
theorem B3154175 : Blo 1401520 3154175 := bstep (se 1 (by rfl) ⟨2365631, by rfl⟩ : syracuseStep 3154175 = 4731263) B4731263
theorem B16195945 : Blo 1401520 16195945 := bstep (se 2 (by rfl) ⟨6073479, by rfl⟩ : syracuseStep 16195945 = 12146959) B12146959
theorem B3154337 : Blo 1401520 3154337 := bstep (se 2 (by rfl) ⟨1182876, by rfl⟩ : syracuseStep 3154337 = 2365753) B2365753
theorem B1401551 : Blo 1401520 1401551 := bstep (se 1 (by rfl) ⟨1051163, by rfl⟩ : syracuseStep 1401551 = 2102327) B2102327
theorem B3367631 : Blo 1401520 3367631 := bstep (se 1 (by rfl) ⟨2525723, by rfl⟩ : syracuseStep 3367631 = 5051447) B5051447
theorem B1401631 : Blo 1401520 1401631 := bstep (se 1 (by rfl) ⟨1051223, by rfl⟩ : syracuseStep 1401631 = 2102447) B2102447
theorem B7103375 : Blo 1401520 7103375 := bstep (se 1 (by rfl) ⟨5327531, by rfl⟩ : syracuseStep 7103375 = 10655063) B10655063
theorem B1401903 : Blo 1401520 1401903 := bstep (se 1 (by rfl) ⟨1051427, by rfl⟩ : syracuseStep 1401903 = 2102855) B2102855
theorem B1401967 : Blo 1401520 1401967 := bstep (se 1 (by rfl) ⟨1051475, by rfl⟩ : syracuseStep 1401967 = 2102951) B2102951
theorem B1402023 : Blo 1401520 1402023 := bstep (se 1 (by rfl) ⟨1051517, by rfl⟩ : syracuseStep 1402023 = 2103035) B2103035
theorem B3155111 : Blo 1401520 3155111 := bstep (se 1 (by rfl) ⟨2366333, by rfl⟩ : syracuseStep 3155111 = 4732667) B4732667
theorem B1402047 : Blo 1401520 1402047 := bstep (se 1 (by rfl) ⟨1051535, by rfl⟩ : syracuseStep 1402047 = 2103071) B2103071
theorem B1402079 : Blo 1401520 1402079 := bstep (se 1 (by rfl) ⟨1051559, by rfl⟩ : syracuseStep 1402079 = 2103119) B2103119
theorem B3155219 : Blo 1401520 3155219 := bstep (se 1 (by rfl) ⟨2366414, by rfl⟩ : syracuseStep 3155219 = 4732829) B4732829
theorem B1402159 : Blo 1401520 1402159 := bstep (se 1 (by rfl) ⟨1051619, by rfl⟩ : syracuseStep 1402159 = 2103239) B2103239
theorem B11978063 : Blo 1401520 11978063 := bstep (se 1 (by rfl) ⟨8983547, by rfl⟩ : syracuseStep 11978063 = 17967095) B17967095
theorem B6481367 : Blo 1401520 6481367 := bstep (se 1 (by rfl) ⟨4861025, by rfl⟩ : syracuseStep 6481367 = 9722051) B9722051
theorem B1402395 : Blo 1401520 1402395 := bstep (se 1 (by rfl) ⟨1051796, by rfl⟩ : syracuseStep 1402395 = 2103593) B2103593
theorem B1402399 : Blo 1401520 1402399 := bstep (se 1 (by rfl) ⟨1051799, by rfl⟩ : syracuseStep 1402399 = 2103599) B2103599
theorem B1402559 : Blo 1401520 1402559 := bstep (se 1 (by rfl) ⟨1051919, by rfl⟩ : syracuseStep 1402559 = 2103839) B2103839
theorem B5056303 : Blo 1401520 5056303 := bstep (se 1 (by rfl) ⟨3792227, by rfl⟩ : syracuseStep 5056303 = 7584455) B7584455
theorem B3155849 : Blo 1401520 3155849 := bstep (se 2 (by rfl) ⟨1183443, by rfl⟩ : syracuseStep 3155849 = 2366887) B2366887
theorem B2844553 : Blo 1401520 2844553 := bstep (se 2 (by rfl) ⟨1066707, by rfl⟩ : syracuseStep 2844553 = 2133415) B2133415
theorem B3155867 : Blo 1401520 3155867 := bstep (se 1 (by rfl) ⟨2366900, by rfl⟩ : syracuseStep 3155867 = 4733801) B4733801
theorem B3155903 : Blo 1401520 3155903 := bstep (se 1 (by rfl) ⟨2366927, by rfl⟩ : syracuseStep 3155903 = 4733855) B4733855
theorem B1402815 : Blo 1401520 1402815 := bstep (se 1 (by rfl) ⟨1052111, by rfl⟩ : syracuseStep 1402815 = 2104223) B2104223
theorem B10643399 : Blo 1401520 10643399 := bstep (se 1 (by rfl) ⟨7982549, by rfl⟩ : syracuseStep 10643399 = 15965099) B15965099
theorem B1402847 : Blo 1401520 1402847 := bstep (se 1 (by rfl) ⟨1052135, by rfl⟩ : syracuseStep 1402847 = 2104271) B2104271
theorem B2664427 : Blo 1401520 2664427 := bstep (se 1 (by rfl) ⟨1998320, by rfl⟩ : syracuseStep 2664427 = 3996641) B3996641
theorem B1402907 : Blo 1401520 1402907 := bstep (se 1 (by rfl) ⟨1052180, by rfl⟩ : syracuseStep 1402907 = 2104361) B2104361
theorem B1402911 : Blo 1401520 1402911 := bstep (se 1 (by rfl) ⟨1052183, by rfl⟩ : syracuseStep 1402911 = 2104367) B2104367
theorem B1402927 : Blo 1401520 1402927 := bstep (se 1 (by rfl) ⟨1052195, by rfl⟩ : syracuseStep 1402927 = 2104391) B2104391
theorem B3369043 : Blo 1401520 3369043 := bstep (se 1 (by rfl) ⟨2526782, by rfl⟩ : syracuseStep 3369043 = 5053565) B5053565
theorem B3156065 : Blo 1401520 3156065 := bstep (se 2 (by rfl) ⟨1183524, by rfl⟩ : syracuseStep 3156065 = 2367049) B2367049
theorem B1403103 : Blo 1401520 1403103 := bstep (se 1 (by rfl) ⟨1052327, by rfl⟩ : syracuseStep 1403103 = 2104655) B2104655
theorem B1403163 : Blo 1401520 1403163 := bstep (se 1 (by rfl) ⟨1052372, by rfl⟩ : syracuseStep 1403163 = 2104745) B2104745
theorem B5056823 : Blo 1401520 5056823 := bstep (se 1 (by rfl) ⟨3792617, by rfl⟩ : syracuseStep 5056823 = 7585235) B7585235
theorem B2844983 : Blo 1401520 2844983 := bstep (se 1 (by rfl) ⟨2133737, by rfl⟩ : syracuseStep 2844983 = 4267475) B4267475
theorem B1403263 : Blo 1401520 1403263 := bstep (se 1 (by rfl) ⟨1052447, by rfl⟩ : syracuseStep 1403263 = 2104895) B2104895
theorem B1403439 : Blo 1401520 1403439 := bstep (se 1 (by rfl) ⟨1052579, by rfl⟩ : syracuseStep 1403439 = 2105159) B2105159
theorem B3844691 : Blo 1401520 3844691 := bstep (se 1 (by rfl) ⟨2883518, by rfl⟩ : syracuseStep 3844691 = 5767037) B5767037
theorem B1403495 : Blo 1401520 1403495 := bstep (se 1 (by rfl) ⟨1052621, by rfl⟩ : syracuseStep 1403495 = 2105243) B2105243
theorem B26954639 : Blo 1401520 26954639 := bstep (se 1 (by rfl) ⟨20215979, by rfl⟩ : syracuseStep 26954639 = 40431959) B40431959
theorem B23956397 : Blo 1401520 23956397 := bstep (se 3 (by rfl) ⟨4491824, by rfl⟩ : syracuseStep 23956397 = 8983649) B8983649
theorem B5327927 : Blo 1401520 5327927 := bstep (se 1 (by rfl) ⟨3995945, by rfl⟩ : syracuseStep 5327927 = 7991891) B7991891
theorem B12799205 : Blo 1401520 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B5328125 : Blo 1401520 5328125 := bstep (se 3 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 5328125 = 1998047) B1998047
theorem B5844347 : Blo 1401520 5844347 := bstep (se 1 (by rfl) ⟨4383260, by rfl⟩ : syracuseStep 5844347 = 8766521) B8766521
theorem B3157415 : Blo 1401520 3157415 := bstep (se 1 (by rfl) ⟨2368061, by rfl⟩ : syracuseStep 3157415 = 4736123) B4736123
theorem B6835745 : Blo 1401520 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B3157595 : Blo 1401520 3157595 := bstep (se 1 (by rfl) ⟨2368196, by rfl⟩ : syracuseStep 3157595 = 4736393) B4736393
theorem B4730615 : Blo 1401520 4730615 := bstep (se 1 (by rfl) ⟨3547961, by rfl⟩ : syracuseStep 4730615 = 7095923) B7095923
theorem B1576831 : Blo 1401520 1576831 := bstep (se 1 (by rfl) ⟨1182623, by rfl⟩ : syracuseStep 1576831 = 2365247) B2365247
theorem B3370889 : Blo 1401520 3370889 := bstep (se 2 (by rfl) ⟨1264083, by rfl⟩ : syracuseStep 3370889 = 2528167) B2528167
theorem B7983143 : Blo 1401520 7983143 := bstep (se 1 (by rfl) ⟨5987357, by rfl⟩ : syracuseStep 7983143 = 11974715) B11974715
theorem B388616231 : Blo 1401520 388616231 := bstep (se 1 (by rfl) ⟨291462173, by rfl⟩ : syracuseStep 388616231 = 582924347) B582924347
theorem B4731155 : Blo 1401520 4731155 := bstep (se 1 (by rfl) ⟨3548366, by rfl⟩ : syracuseStep 4731155 = 7096733) B7096733
theorem B1577371 : Blo 1401520 1577371 := bstep (se 1 (by rfl) ⟨1183028, by rfl⟩ : syracuseStep 1577371 = 2366057) B2366057
theorem B12145231 : Blo 1401520 12145231 := bstep (se 1 (by rfl) ⟨9108923, by rfl⟩ : syracuseStep 12145231 = 18217847) B18217847
theorem B21598903 : Blo 1401520 21598903 := bstep (se 1 (by rfl) ⟨16199177, by rfl⟩ : syracuseStep 21598903 = 32398355) B32398355
theorem B24965921 : Blo 1401520 24965921 := bstep (se 2 (by rfl) ⟨9362220, by rfl⟩ : syracuseStep 24965921 = 18724441) B18724441
theorem B4731695 : Blo 1401520 4731695 := bstep (se 1 (by rfl) ⟨3548771, by rfl⟩ : syracuseStep 4731695 = 7097543) B7097543
theorem B4264787 : Blo 1401520 4264787 := bstep (se 1 (by rfl) ⟨3198590, by rfl⟩ : syracuseStep 4264787 = 6397181) B6397181
theorem B1684315 : Blo 1401520 1684315 := bstep (se 1 (by rfl) ⟨1263236, by rfl⟩ : syracuseStep 1684315 = 2526473) B2526473
theorem B5321609 : Blo 1401520 5321609 := bstep (se 2 (by rfl) ⟨1995603, by rfl⟩ : syracuseStep 5321609 = 3991207) B3991207
theorem B5321639 : Blo 1401520 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B1995769 : Blo 1401520 1995769 := bstep (se 2 (by rfl) ⟨748413, by rfl⟩ : syracuseStep 1995769 = 1496827) B1496827
theorem B1578055 : Blo 1401520 1578055 := bstep (se 1 (by rfl) ⟨1183541, by rfl⟩ : syracuseStep 1578055 = 2367083) B2367083
theorem B11990227 : Blo 1401520 11990227 := bstep (se 1 (by rfl) ⟨8992670, by rfl⟩ : syracuseStep 11990227 = 17985341) B17985341
theorem B1578235 : Blo 1401520 1578235 := bstep (se 1 (by rfl) ⟨1183676, by rfl⟩ : syracuseStep 1578235 = 2367353) B2367353
theorem B2102639 : Blo 1401520 2102639 := bstep (se 1 (by rfl) ⟨1576979, by rfl⟩ : syracuseStep 2102639 = 3153959) B3153959
theorem B49903057 : Blo 1401520 49903057 := bstep (se 2 (by rfl) ⟨18713646, by rfl⟩ : syracuseStep 49903057 = 37427293) B37427293
theorem B2102759 : Blo 1401520 2102759 := bstep (se 1 (by rfl) ⟨1577069, by rfl⟩ : syracuseStep 2102759 = 3154139) B3154139
theorem B2102921 : Blo 1401520 2102921 := bstep (se 2 (by rfl) ⟨788595, by rfl⟩ : syracuseStep 2102921 = 1577191) B1577191
theorem B4732559 : Blo 1401520 4732559 := bstep (se 1 (by rfl) ⟨3549419, by rfl⟩ : syracuseStep 4732559 = 7098839) B7098839
theorem B2102939 : Blo 1401520 2102939 := bstep (se 1 (by rfl) ⟨1577204, by rfl⟩ : syracuseStep 2102939 = 3154409) B3154409
theorem B7984919 : Blo 1401520 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B17979191 : Blo 1401520 17979191 := bstep (se 1 (by rfl) ⟨13484393, by rfl⟩ : syracuseStep 17979191 = 26968787) B26968787
theorem B2103131 : Blo 1401520 2103131 := bstep (se 1 (by rfl) ⟨1577348, by rfl⟩ : syracuseStep 2103131 = 3154697) B3154697
theorem B19453859 : Blo 1401520 19453859 := bstep (se 1 (by rfl) ⟨14590394, by rfl⟩ : syracuseStep 19453859 = 29180789) B29180789
theorem B4732937 : Blo 1401520 4732937 := bstep (se 2 (by rfl) ⟨1774851, by rfl⟩ : syracuseStep 4732937 = 3549703) B3549703
theorem B5322793 : Blo 1401520 5322793 := bstep (se 2 (by rfl) ⟨1996047, by rfl⟩ : syracuseStep 5322793 = 3992095) B3992095
theorem B25598051 : Blo 1401520 25598051 := bstep (se 1 (by rfl) ⟨19198538, by rfl⟩ : syracuseStep 25598051 = 38397077) B38397077
theorem B3995831 : Blo 1401520 3995831 := bstep (se 1 (by rfl) ⟨2996873, by rfl⟩ : syracuseStep 3995831 = 5993747) B5993747
theorem B2103515 : Blo 1401520 2103515 := bstep (se 1 (by rfl) ⟨1577636, by rfl⟩ : syracuseStep 2103515 = 3155273) B3155273
theorem B83106137 : Blo 1401520 83106137 := bstep (se 2 (by rfl) ⟨31164801, by rfl⟩ : syracuseStep 83106137 = 62329603) B62329603
theorem B1997255 : Blo 1401520 1997255 := bstep (se 1 (by rfl) ⟨1497941, by rfl⟩ : syracuseStep 1997255 = 2995883) B2995883
theorem B2103785 : Blo 1401520 2103785 := bstep (se 2 (by rfl) ⟨788919, by rfl⟩ : syracuseStep 2103785 = 1577839) B1577839
theorem B1686107 : Blo 1401520 1686107 := bstep (se 1 (by rfl) ⟨1264580, by rfl⟩ : syracuseStep 1686107 = 2529161) B2529161
theorem B65649305 : Blo 1401520 65649305 := bstep (se 2 (by rfl) ⟨24618489, by rfl⟩ : syracuseStep 65649305 = 49236979) B49236979
theorem B13671179 : Blo 1401520 13671179 := bstep (se 1 (by rfl) ⟨10253384, by rfl⟩ : syracuseStep 13671179 = 20506769) B20506769
theorem B2104175 : Blo 1401520 2104175 := bstep (se 1 (by rfl) ⟨1578131, by rfl⟩ : syracuseStep 2104175 = 3156263) B3156263
theorem B2104187 : Blo 1401520 2104187 := bstep (se 1 (by rfl) ⟨1578140, by rfl⟩ : syracuseStep 2104187 = 3156281) B3156281
theorem B5323751 : Blo 1401520 5323751 := bstep (se 1 (by rfl) ⟨3992813, by rfl⟩ : syracuseStep 5323751 = 7985627) B7985627
theorem B2366671 : Blo 1401520 2366671 := bstep (se 1 (by rfl) ⟨1775003, by rfl⟩ : syracuseStep 2366671 = 3550007) B3550007
theorem B1498343 : Blo 1401520 1498343 := bstep (se 1 (by rfl) ⟨1123757, by rfl⟩ : syracuseStep 1498343 = 2247515) B2247515
theorem B7576841 : Blo 1401520 7576841 := bstep (se 2 (by rfl) ⟨2841315, by rfl⟩ : syracuseStep 7576841 = 5682631) B5682631
theorem B4734287 : Blo 1401520 4734287 := bstep (se 1 (by rfl) ⟨3550715, by rfl⟩ : syracuseStep 4734287 = 7101431) B7101431
theorem B11378107 : Blo 1401520 11378107 := bstep (se 1 (by rfl) ⟨8533580, by rfl⟩ : syracuseStep 11378107 = 17067161) B17067161
theorem B3792509 : Blo 1401520 3792509 := bstep (se 3 (by rfl) ⟨711095, by rfl⟩ : syracuseStep 3792509 = 1422191) B1422191
theorem B10649231 : Blo 1401520 10649231 := bstep (se 1 (by rfl) ⟨7986923, by rfl⟩ : syracuseStep 10649231 = 15973847) B15973847
theorem B2105051 : Blo 1401520 2105051 := bstep (se 1 (by rfl) ⟨1578788, by rfl⟩ : syracuseStep 2105051 = 3157577) B3157577
theorem B1539815 : Blo 1401520 1539815 := bstep (se 1 (by rfl) ⟨1154861, by rfl⟩ : syracuseStep 1539815 = 2309723) B2309723
theorem B5988127 : Blo 1401520 5988127 := bstep (se 1 (by rfl) ⟨4491095, by rfl⟩ : syracuseStep 5988127 = 8982191) B8982191
theorem B3153761 : Blo 1401520 3153761 := bstep (se 2 (by rfl) ⟨1182660, by rfl⟩ : syracuseStep 3153761 = 2365321) B2365321
theorem B14786513 : Blo 1401520 14786513 := bstep (se 2 (by rfl) ⟨5544942, by rfl⟩ : syracuseStep 14786513 = 11089885) B11089885
theorem B3153887 : Blo 1401520 3153887 := bstep (se 1 (by rfl) ⟨2365415, by rfl⟩ : syracuseStep 3153887 = 4730831) B4730831
theorem B3154103 : Blo 1401520 3154103 := bstep (se 1 (by rfl) ⟨2365577, by rfl⟩ : syracuseStep 3154103 = 4731155) B4731155
theorem B2245087 : Blo 1401520 2245087 := bstep (se 1 (by rfl) ⟨1683815, by rfl⟩ : syracuseStep 2245087 = 3367631) B3367631
theorem B21594593 : Blo 1401520 21594593 := bstep (se 2 (by rfl) ⟨8097972, by rfl⟩ : syracuseStep 21594593 = 16195945) B16195945
theorem B3154463 : Blo 1401520 3154463 := bstep (se 1 (by rfl) ⟨2365847, by rfl⟩ : syracuseStep 3154463 = 4731695) B4731695
theorem B2843191 : Blo 1401520 2843191 := bstep (se 1 (by rfl) ⟨2132393, by rfl⟩ : syracuseStep 2843191 = 4264787) B4264787
theorem B3547739 : Blo 1401520 3547739 := bstep (se 1 (by rfl) ⟨2660804, by rfl⟩ : syracuseStep 3547739 = 5321609) B5321609
theorem B4735583 : Blo 1401520 4735583 := bstep (se 1 (by rfl) ⟨3551687, by rfl⟩ : syracuseStep 4735583 = 7103375) B7103375
theorem B3547759 : Blo 1401520 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B7586621 : Blo 1401520 7586621 := bstep (se 3 (by rfl) ⟨1422491, by rfl⟩ : syracuseStep 7586621 = 2844983) B2844983
theorem B1401759 : Blo 1401520 1401759 := bstep (se 1 (by rfl) ⟨1051319, by rfl⟩ : syracuseStep 1401759 = 2102639) B2102639
theorem B1401839 : Blo 1401520 1401839 := bstep (se 1 (by rfl) ⟨1051379, by rfl⟩ : syracuseStep 1401839 = 2102759) B2102759
theorem B1401947 : Blo 1401520 1401947 := bstep (se 1 (by rfl) ⟨1051460, by rfl⟩ : syracuseStep 1401947 = 2102921) B2102921
theorem B3155039 : Blo 1401520 3155039 := bstep (se 1 (by rfl) ⟨2366279, by rfl⟩ : syracuseStep 3155039 = 4732559) B4732559
theorem B1401959 : Blo 1401520 1401959 := bstep (se 1 (by rfl) ⟨1051469, by rfl⟩ : syracuseStep 1401959 = 2102939) B2102939
theorem B2245753 : Blo 1401520 2245753 := bstep (se 2 (by rfl) ⟨842157, by rfl⟩ : syracuseStep 2245753 = 1684315) B1684315
theorem B5326013 : Blo 1401520 5326013 := bstep (se 3 (by rfl) ⟨998627, by rfl⟩ : syracuseStep 5326013 = 1997255) B1997255
theorem B11986127 : Blo 1401520 11986127 := bstep (se 1 (by rfl) ⟨8989595, by rfl⟩ : syracuseStep 11986127 = 17979191) B17979191
theorem B1402087 : Blo 1401520 1402087 := bstep (se 1 (by rfl) ⟨1051565, by rfl⟩ : syracuseStep 1402087 = 2103131) B2103131
theorem B12969239 : Blo 1401520 12969239 := bstep (se 1 (by rfl) ⟨9726929, by rfl⟩ : syracuseStep 12969239 = 19453859) B19453859
theorem B7095599 : Blo 1401520 7095599 := bstep (se 1 (by rfl) ⟨5321699, by rfl⟩ : syracuseStep 7095599 = 10643399) B10643399
theorem B3155291 : Blo 1401520 3155291 := bstep (se 1 (by rfl) ⟨2366468, by rfl⟩ : syracuseStep 3155291 = 4732937) B4732937
theorem B17065367 : Blo 1401520 17065367 := bstep (se 1 (by rfl) ⟨12799025, by rfl⟩ : syracuseStep 17065367 = 25598051) B25598051
theorem B1402343 : Blo 1401520 1402343 := bstep (se 1 (by rfl) ⟨1051757, by rfl⟩ : syracuseStep 1402343 = 2103515) B2103515
theorem B55404091 : Blo 1401520 55404091 := bstep (se 1 (by rfl) ⟨41553068, by rfl⟩ : syracuseStep 55404091 = 83106137) B83106137
theorem B3155561 : Blo 1401520 3155561 := bstep (se 2 (by rfl) ⟨1183335, by rfl⟩ : syracuseStep 3155561 = 2366671) B2366671
theorem B1402523 : Blo 1401520 1402523 := bstep (se 1 (by rfl) ⟨1051892, by rfl⟩ : syracuseStep 1402523 = 2103785) B2103785
theorem B1402783 : Blo 1401520 1402783 := bstep (se 1 (by rfl) ⟨1052087, by rfl⟩ : syracuseStep 1402783 = 2104175) B2104175
theorem B1402791 : Blo 1401520 1402791 := bstep (se 1 (by rfl) ⟨1052093, by rfl⟩ : syracuseStep 1402791 = 2104187) B2104187
theorem B4106173 : Blo 1401520 4106173 := bstep (se 3 (by rfl) ⟨769907, by rfl⟩ : syracuseStep 4106173 = 1539815) B1539815
theorem B66537409 : Blo 1401520 66537409 := bstep (se 2 (by rfl) ⟨24951528, by rfl⟩ : syracuseStep 66537409 = 49903057) B49903057
theorem B3549167 : Blo 1401520 3549167 := bstep (se 1 (by rfl) ⟨2661875, by rfl⟩ : syracuseStep 3549167 = 5323751) B5323751
theorem B3156191 : Blo 1401520 3156191 := bstep (se 1 (by rfl) ⟨2367143, by rfl⟩ : syracuseStep 3156191 = 4734287) B4734287
theorem B4557163 : Blo 1401520 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B1403367 : Blo 1401520 1403367 := bstep (se 1 (by rfl) ⟨1052525, by rfl⟩ : syracuseStep 1403367 = 2105051) B2105051
theorem B2247259 : Blo 1401520 2247259 := bstep (se 1 (by rfl) ⟨1685444, by rfl⟩ : syracuseStep 2247259 = 3370889) B3370889
theorem B9857675 : Blo 1401520 9857675 := bstep (se 1 (by rfl) ⟨7393256, by rfl⟩ : syracuseStep 9857675 = 14786513) B14786513
theorem B5991083 : Blo 1401520 5991083 := bstep (se 1 (by rfl) ⟨4493312, by rfl⟩ : syracuseStep 5991083 = 8986625) B8986625
theorem B7097057 : Blo 1401520 7097057 := bstep (se 2 (by rfl) ⟨2661396, by rfl⟩ : syracuseStep 7097057 = 5322793) B5322793
theorem B4492057 : Blo 1401520 4492057 := bstep (se 2 (by rfl) ⟨1684521, by rfl⟩ : syracuseStep 4492057 = 3369043) B3369043
theorem B20204909 : Blo 1401520 20204909 := bstep (se 3 (by rfl) ⟨3788420, by rfl⟩ : syracuseStep 20204909 = 7576841) B7576841
theorem B28798537 : Blo 1401520 28798537 := bstep (se 2 (by rfl) ⟨10799451, by rfl⟩ : syracuseStep 28798537 = 21598903) B21598903
theorem B4320911 : Blo 1401520 4320911 := bstep (se 1 (by rfl) ⟨3240683, by rfl⟩ : syracuseStep 4320911 = 6481367) B6481367
theorem B3371215 : Blo 1401520 3371215 := bstep (se 1 (by rfl) ⟨2528411, by rfl⟩ : syracuseStep 3371215 = 5056823) B5056823
theorem B15986969 : Blo 1401520 15986969 := bstep (se 2 (by rfl) ⟨5995113, by rfl⟩ : syracuseStep 15986969 = 11990227) B11990227
theorem B43766203 : Blo 1401520 43766203 := bstep (se 1 (by rfl) ⟨32824652, by rfl⟩ : syracuseStep 43766203 = 65649305) B65649305
theorem B9114119 : Blo 1401520 9114119 := bstep (se 1 (by rfl) ⟨6835589, by rfl⟩ : syracuseStep 9114119 = 13671179) B13671179
theorem B17969759 : Blo 1401520 17969759 := bstep (se 1 (by rfl) ⟨13477319, by rfl⟩ : syracuseStep 17969759 = 26954639) B26954639
theorem B15970931 : Blo 1401520 15970931 := bstep (se 1 (by rfl) ⟨11978198, by rfl⟩ : syracuseStep 15970931 = 23956397) B23956397
theorem B3551951 : Blo 1401520 3551951 := bstep (se 1 (by rfl) ⟨2663963, by rfl⟩ : syracuseStep 3551951 = 5327927) B5327927
theorem B8532803 : Blo 1401520 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B3552083 : Blo 1401520 3552083 := bstep (se 1 (by rfl) ⟨2664062, by rfl⟩ : syracuseStep 3552083 = 5328125) B5328125
theorem B7984169 : Blo 1401520 7984169 := bstep (se 2 (by rfl) ⟨2994063, by rfl⟩ : syracuseStep 7984169 = 5988127) B5988127
theorem B2528339 : Blo 1401520 2528339 := bstep (se 1 (by rfl) ⟨1896254, by rfl⟩ : syracuseStep 2528339 = 3792509) B3792509
theorem B7099487 : Blo 1401520 7099487 := bstep (se 1 (by rfl) ⟨5324615, by rfl⟩ : syracuseStep 7099487 = 10649231) B10649231
theorem B2102441 : Blo 1401520 2102441 := bstep (se 2 (by rfl) ⟨788415, by rfl⟩ : syracuseStep 2102441 = 1576831) B1576831
theorem B2102507 : Blo 1401520 2102507 := bstep (se 1 (by rfl) ⟨1576880, by rfl⟩ : syracuseStep 2102507 = 3153761) B3153761
theorem B3552569 : Blo 1401520 3552569 := bstep (se 2 (by rfl) ⟨1332213, by rfl⟩ : syracuseStep 3552569 = 2664427) B2664427
theorem B2102591 : Blo 1401520 2102591 := bstep (se 1 (by rfl) ⟨1576943, by rfl⟩ : syracuseStep 2102591 = 3153887) B3153887
theorem B5322095 : Blo 1401520 5322095 := bstep (se 1 (by rfl) ⟨3991571, by rfl⟩ : syracuseStep 5322095 = 7983143) B7983143
theorem B259077487 : Blo 1401520 259077487 := bstep (se 1 (by rfl) ⟨194308115, by rfl⟩ : syracuseStep 259077487 = 388616231) B388616231
theorem B2102783 : Blo 1401520 2102783 := bstep (se 1 (by rfl) ⟨1577087, by rfl⟩ : syracuseStep 2102783 = 3154175) B3154175
theorem B2102891 : Blo 1401520 2102891 := bstep (se 1 (by rfl) ⟨1577168, by rfl⟩ : syracuseStep 2102891 = 3154337) B3154337
theorem B10655549 : Blo 1401520 10655549 := bstep (se 3 (by rfl) ⟨1997915, by rfl⟩ : syracuseStep 10655549 = 3995831) B3995831
theorem B2103161 : Blo 1401520 2103161 := bstep (se 2 (by rfl) ⟨788685, by rfl⟩ : syracuseStep 2103161 = 1577371) B1577371
theorem B3995581 : Blo 1401520 3995581 := bstep (se 3 (by rfl) ⟨749171, by rfl⟩ : syracuseStep 3995581 = 1498343) B1498343
theorem B16193641 : Blo 1401520 16193641 := bstep (se 2 (by rfl) ⟨6072615, by rfl⟩ : syracuseStep 16193641 = 12145231) B12145231
theorem B2103407 : Blo 1401520 2103407 := bstep (se 1 (by rfl) ⟨1577555, by rfl⟩ : syracuseStep 2103407 = 3155111) B3155111
theorem B2103479 : Blo 1401520 2103479 := bstep (se 1 (by rfl) ⟨1577609, by rfl⟩ : syracuseStep 2103479 = 3155219) B3155219
theorem B7985375 : Blo 1401520 7985375 := bstep (se 1 (by rfl) ⟨5989031, by rfl⟩ : syracuseStep 7985375 = 11978063) B11978063
theorem B5323279 : Blo 1401520 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B2103899 : Blo 1401520 2103899 := bstep (se 1 (by rfl) ⟨1577924, by rfl⟩ : syracuseStep 2103899 = 3155849) B3155849
theorem B2103911 : Blo 1401520 2103911 := bstep (se 1 (by rfl) ⟨1577933, by rfl⟩ : syracuseStep 2103911 = 3155867) B3155867
theorem B62339701 : Blo 1401520 62339701 := bstep (se 5 (by rfl) ⟨2922173, by rfl⟩ : syracuseStep 62339701 = 5844347) B5844347
theorem B2103935 : Blo 1401520 2103935 := bstep (se 1 (by rfl) ⟨1577951, by rfl⟩ : syracuseStep 2103935 = 3155903) B3155903
theorem B2661025 : Blo 1401520 2661025 := bstep (se 2 (by rfl) ⟨997884, by rfl⟩ : syracuseStep 2661025 = 1995769) B1995769
theorem B2104043 : Blo 1401520 2104043 := bstep (se 1 (by rfl) ⟨1578032, by rfl⟩ : syracuseStep 2104043 = 3156065) B3156065
theorem B2104073 : Blo 1401520 2104073 := bstep (se 2 (by rfl) ⟨789027, by rfl⟩ : syracuseStep 2104073 = 1578055) B1578055
theorem B4496285 : Blo 1401520 4496285 := bstep (se 3 (by rfl) ⟨843053, by rfl⟩ : syracuseStep 4496285 = 1686107) B1686107
theorem B2104313 : Blo 1401520 2104313 := bstep (se 2 (by rfl) ⟨789117, by rfl⟩ : syracuseStep 2104313 = 1578235) B1578235
theorem B2563127 : Blo 1401520 2563127 := bstep (se 1 (by rfl) ⟨1922345, by rfl⟩ : syracuseStep 2563127 = 3844691) B3844691
theorem B15170809 : Blo 1401520 15170809 := bstep (se 2 (by rfl) ⟨5689053, by rfl⟩ : syracuseStep 15170809 = 11378107) B11378107
theorem B66575789 : Blo 1401520 66575789 := bstep (se 3 (by rfl) ⟨12482960, by rfl⟩ : syracuseStep 66575789 = 24965921) B24965921
theorem B2104943 : Blo 1401520 2104943 := bstep (se 1 (by rfl) ⟨1578707, by rfl⟩ : syracuseStep 2104943 = 3157415) B3157415
theorem B2105063 : Blo 1401520 2105063 := bstep (se 1 (by rfl) ⟨1578797, by rfl⟩ : syracuseStep 2105063 = 3157595) B3157595
theorem B6741737 : Blo 1401520 6741737 := bstep (se 2 (by rfl) ⟨2528151, by rfl⟩ : syracuseStep 6741737 = 5056303) B5056303
theorem B3153743 : Blo 1401520 3153743 := bstep (se 1 (by rfl) ⟨2365307, by rfl⟩ : syracuseStep 3153743 = 4730615) B4730615
theorem B3792737 : Blo 1401520 3792737 := bstep (se 2 (by rfl) ⟨1422276, by rfl⟩ : syracuseStep 3792737 = 2844553) B2844553
theorem B10657979 : Blo 1401520 10657979 := bstep (se 1 (by rfl) ⟨7993484, by rfl⟩ : syracuseStep 10657979 = 15986969) B15986969
theorem B6742237 : Blo 1401520 6742237 := bstep (se 3 (by rfl) ⟨1264169, by rfl⟩ : syracuseStep 6742237 = 2528339) B2528339
theorem B138338549 : Blo 1401520 138338549 := bstep (se 5 (by rfl) ⟨6484619, by rfl⟩ : syracuseStep 138338549 = 12969239) B12969239
theorem B2367967 : Blo 1401520 2367967 := bstep (se 1 (by rfl) ⟨1775975, by rfl⟩ : syracuseStep 2367967 = 3551951) B3551951
theorem B2368055 : Blo 1401520 2368055 := bstep (se 1 (by rfl) ⟨1776041, by rfl⟩ : syracuseStep 2368055 = 3552083) B3552083
theorem B1401627 : Blo 1401520 1401627 := bstep (se 1 (by rfl) ⟨1051220, by rfl⟩ : syracuseStep 1401627 = 2102441) B2102441
theorem B1401671 : Blo 1401520 1401671 := bstep (se 1 (by rfl) ⟨1051253, by rfl⟩ : syracuseStep 1401671 = 2102507) B2102507
theorem B2368379 : Blo 1401520 2368379 := bstep (se 1 (by rfl) ⟨1776284, by rfl⟩ : syracuseStep 2368379 = 3552569) B3552569
theorem B1401727 : Blo 1401520 1401727 := bstep (se 1 (by rfl) ⟨1051295, by rfl⟩ : syracuseStep 1401727 = 2102591) B2102591
theorem B3548033 : Blo 1401520 3548033 := bstep (se 2 (by rfl) ⟨1330512, by rfl⟩ : syracuseStep 3548033 = 2661025) B2661025
theorem B3548063 : Blo 1401520 3548063 := bstep (se 1 (by rfl) ⟨2661047, by rfl⟩ : syracuseStep 3548063 = 5322095) B5322095
theorem B1401855 : Blo 1401520 1401855 := bstep (se 1 (by rfl) ⟨1051391, by rfl⟩ : syracuseStep 1401855 = 2102783) B2102783
theorem B5989409 : Blo 1401520 5989409 := bstep (se 2 (by rfl) ⟨2246028, by rfl⟩ : syracuseStep 5989409 = 4492057) B4492057
theorem B1401927 : Blo 1401520 1401927 := bstep (se 1 (by rfl) ⟨1051445, by rfl⟩ : syracuseStep 1401927 = 2102891) B2102891
theorem B7103699 : Blo 1401520 7103699 := bstep (se 1 (by rfl) ⟨5327774, by rfl⟩ : syracuseStep 7103699 = 10655549) B10655549
theorem B1402107 : Blo 1401520 1402107 := bstep (se 1 (by rfl) ⟨1051580, by rfl⟩ : syracuseStep 1402107 = 2103161) B2103161
theorem B1402271 : Blo 1401520 1402271 := bstep (se 1 (by rfl) ⟨1051703, by rfl⟩ : syracuseStep 1402271 = 2103407) B2103407
theorem B1402319 : Blo 1401520 1402319 := bstep (se 1 (by rfl) ⟨1051739, by rfl⟩ : syracuseStep 1402319 = 2103479) B2103479
theorem B20227745 : Blo 1401520 20227745 := bstep (se 2 (by rfl) ⟨7585404, by rfl⟩ : syracuseStep 20227745 = 15170809) B15170809
theorem B1402599 : Blo 1401520 1402599 := bstep (se 1 (by rfl) ⟨1051949, by rfl⟩ : syracuseStep 1402599 = 2103899) B2103899
theorem B1402607 : Blo 1401520 1402607 := bstep (se 1 (by rfl) ⟨1051955, by rfl⟩ : syracuseStep 1402607 = 2103911) B2103911
theorem B1402623 : Blo 1401520 1402623 := bstep (se 1 (by rfl) ⟨1051967, by rfl⟩ : syracuseStep 1402623 = 2103935) B2103935
theorem B6571783 : Blo 1401520 6571783 := bstep (se 1 (by rfl) ⟨4928837, by rfl⟩ : syracuseStep 6571783 = 9857675) B9857675
theorem B1402695 : Blo 1401520 1402695 := bstep (se 1 (by rfl) ⟨1052021, by rfl⟩ : syracuseStep 1402695 = 2104043) B2104043
theorem B1402715 : Blo 1401520 1402715 := bstep (se 1 (by rfl) ⟨1052036, by rfl⟩ : syracuseStep 1402715 = 2104073) B2104073
theorem B1402875 : Blo 1401520 1402875 := bstep (se 1 (by rfl) ⟨1052156, by rfl⟩ : syracuseStep 1402875 = 2104313) B2104313
theorem B38398049 : Blo 1401520 38398049 := bstep (se 2 (by rfl) ⟨14399268, by rfl⟩ : syracuseStep 38398049 = 28798537) B28798537
theorem B13469939 : Blo 1401520 13469939 := bstep (se 1 (by rfl) ⟨10102454, by rfl⟩ : syracuseStep 13469939 = 20204909) B20204909
theorem B1403295 : Blo 1401520 1403295 := bstep (se 1 (by rfl) ⟨1052471, by rfl⟩ : syracuseStep 1403295 = 2104943) B2104943
theorem B1403375 : Blo 1401520 1403375 := bstep (se 1 (by rfl) ⟨1052531, by rfl⟩ : syracuseStep 1403375 = 2105063) B2105063
theorem B5327441 : Blo 1401520 5327441 := bstep (se 2 (by rfl) ⟨1997790, by rfl⟩ : syracuseStep 5327441 = 3995581) B3995581
theorem B5474897 : Blo 1401520 5474897 := bstep (se 2 (by rfl) ⟨2053086, by rfl⟩ : syracuseStep 5474897 = 4106173) B4106173
theorem B14396395 : Blo 1401520 14396395 := bstep (se 1 (by rfl) ⟨10797296, by rfl⟩ : syracuseStep 14396395 = 21594593) B21594593
theorem B11979839 : Blo 1401520 11979839 := bstep (se 1 (by rfl) ⟨8984879, by rfl⟩ : syracuseStep 11979839 = 17969759) B17969759
theorem B3157055 : Blo 1401520 3157055 := bstep (se 1 (by rfl) ⟨2367791, by rfl⟩ : syracuseStep 3157055 = 4735583) B4735583
theorem B5057747 : Blo 1401520 5057747 := bstep (se 1 (by rfl) ⟨3793310, by rfl⟩ : syracuseStep 5057747 = 7586621) B7586621
theorem B27340021 : Blo 1401520 27340021 := bstep (se 5 (by rfl) ⟨1281563, by rfl⟩ : syracuseStep 27340021 = 2563127) B2563127
theorem B58354937 : Blo 1401520 58354937 := bstep (se 2 (by rfl) ⟨21883101, by rfl⟩ : syracuseStep 58354937 = 43766203) B43766203
theorem B2993449 : Blo 1401520 2993449 := bstep (se 2 (by rfl) ⟨1122543, by rfl⟩ : syracuseStep 2993449 = 2245087) B2245087
theorem B7097705 : Blo 1401520 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B3550675 : Blo 1401520 3550675 := bstep (se 1 (by rfl) ⟨2663006, by rfl⟩ : syracuseStep 3550675 = 5326013) B5326013
theorem B7990751 : Blo 1401520 7990751 := bstep (se 1 (by rfl) ⟨5993063, by rfl⟩ : syracuseStep 7990751 = 11986127) B11986127
theorem B4730345 : Blo 1401520 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B83119601 : Blo 1401520 83119601 := bstep (se 2 (by rfl) ⟨31169850, by rfl⟩ : syracuseStep 83119601 = 62339701) B62339701
theorem B4730399 : Blo 1401520 4730399 := bstep (se 1 (by rfl) ⟨3547799, by rfl⟩ : syracuseStep 4730399 = 7095599) B7095599
theorem B2994337 : Blo 1401520 2994337 := bstep (se 2 (by rfl) ⟨1122876, by rfl⟩ : syracuseStep 2994337 = 2245753) B2245753
theorem B3994055 : Blo 1401520 3994055 := bstep (se 1 (by rfl) ⟨2995541, by rfl⟩ : syracuseStep 3994055 = 5991083) B5991083
theorem B4731371 : Blo 1401520 4731371 := bstep (se 1 (by rfl) ⟨3548528, by rfl⟩ : syracuseStep 4731371 = 7097057) B7097057
theorem B345436649 : Blo 1401520 345436649 := bstep (se 2 (by rfl) ⟨129538743, by rfl⟩ : syracuseStep 345436649 = 259077487) B259077487
theorem B73872121 : Blo 1401520 73872121 := bstep (se 2 (by rfl) ⟨27702045, by rfl⟩ : syracuseStep 73872121 = 55404091) B55404091
theorem B22754141 : Blo 1401520 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B2880607 : Blo 1401520 2880607 := bstep (se 1 (by rfl) ⟨2160455, by rfl⟩ : syracuseStep 2880607 = 4320911) B4320911
theorem B4494491 : Blo 1401520 4494491 := bstep (se 1 (by rfl) ⟨3370868, by rfl⟩ : syracuseStep 4494491 = 6741737) B6741737
theorem B2102495 : Blo 1401520 2102495 := bstep (se 1 (by rfl) ⟨1576871, by rfl⟩ : syracuseStep 2102495 = 3153743) B3153743
theorem B2528491 : Blo 1401520 2528491 := bstep (se 1 (by rfl) ⟨1896368, by rfl⟩ : syracuseStep 2528491 = 3792737) B3792737
theorem B88716545 : Blo 1401520 88716545 := bstep (se 2 (by rfl) ⟨33268704, by rfl⟩ : syracuseStep 88716545 = 66537409) B66537409
theorem B2102735 : Blo 1401520 2102735 := bstep (se 1 (by rfl) ⟨1577051, by rfl⟩ : syracuseStep 2102735 = 3154103) B3154103
theorem B21591521 : Blo 1401520 21591521 := bstep (se 2 (by rfl) ⟨8096820, by rfl⟩ : syracuseStep 21591521 = 16193641) B16193641
theorem B4494953 : Blo 1401520 4494953 := bstep (se 2 (by rfl) ⟨1685607, by rfl⟩ : syracuseStep 4494953 = 3371215) B3371215
theorem B6076079 : Blo 1401520 6076079 := bstep (se 1 (by rfl) ⟨4557059, by rfl⟩ : syracuseStep 6076079 = 9114119) B9114119
theorem B2102975 : Blo 1401520 2102975 := bstep (se 1 (by rfl) ⟨1577231, by rfl⟩ : syracuseStep 2102975 = 3154463) B3154463
theorem B2365159 : Blo 1401520 2365159 := bstep (se 1 (by rfl) ⟨1773869, by rfl⟩ : syracuseStep 2365159 = 3547739) B3547739
theorem B10647287 : Blo 1401520 10647287 := bstep (se 1 (by rfl) ⟨7985465, by rfl⟩ : syracuseStep 10647287 = 15970931) B15970931
theorem B6076217 : Blo 1401520 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B5322779 : Blo 1401520 5322779 := bstep (se 1 (by rfl) ⟨3992084, by rfl⟩ : syracuseStep 5322779 = 7984169) B7984169
theorem B2103359 : Blo 1401520 2103359 := bstep (se 1 (by rfl) ⟨1577519, by rfl⟩ : syracuseStep 2103359 = 3155039) B3155039
theorem B4732991 : Blo 1401520 4732991 := bstep (se 1 (by rfl) ⟨3549743, by rfl⟩ : syracuseStep 4732991 = 7099487) B7099487
theorem B3790921 : Blo 1401520 3790921 := bstep (se 2 (by rfl) ⟨1421595, by rfl⟩ : syracuseStep 3790921 = 2843191) B2843191
theorem B2996345 : Blo 1401520 2996345 := bstep (se 2 (by rfl) ⟨1123629, by rfl⟩ : syracuseStep 2996345 = 2247259) B2247259
theorem B2103527 : Blo 1401520 2103527 := bstep (se 1 (by rfl) ⟨1577645, by rfl⟩ : syracuseStep 2103527 = 3155291) B3155291
theorem B11376911 : Blo 1401520 11376911 := bstep (se 1 (by rfl) ⟨8532683, by rfl⟩ : syracuseStep 11376911 = 17065367) B17065367
theorem B2103707 : Blo 1401520 2103707 := bstep (se 1 (by rfl) ⟨1577780, by rfl⟩ : syracuseStep 2103707 = 3155561) B3155561
theorem B2366111 : Blo 1401520 2366111 := bstep (se 1 (by rfl) ⟨1774583, by rfl⟩ : syracuseStep 2366111 = 3549167) B3549167
theorem B5323583 : Blo 1401520 5323583 := bstep (se 1 (by rfl) ⟨3992687, by rfl⟩ : syracuseStep 5323583 = 7985375) B7985375
theorem B2104127 : Blo 1401520 2104127 := bstep (se 1 (by rfl) ⟨1578095, by rfl⟩ : syracuseStep 2104127 = 3156191) B3156191
theorem B2997523 : Blo 1401520 2997523 := bstep (se 1 (by rfl) ⟨2248142, by rfl⟩ : syracuseStep 2997523 = 4496285) B4496285
theorem B44383859 : Blo 1401520 44383859 := bstep (se 1 (by rfl) ⟨33287894, by rfl⟩ : syracuseStep 44383859 = 66575789) B66575789
theorem B5054561 : Blo 1401520 5054561 := bstep (se 2 (by rfl) ⟨1895460, by rfl⟩ : syracuseStep 5054561 = 3790921) B3790921
theorem B92225699 : Blo 1401520 92225699 := bstep (se 1 (by rfl) ⟨69169274, by rfl⟩ : syracuseStep 92225699 = 138338549) B138338549
theorem B2662703 : Blo 1401520 2662703 := bstep (se 1 (by rfl) ⟨1997027, by rfl⟩ : syracuseStep 2662703 = 3994055) B3994055
theorem B3154247 : Blo 1401520 3154247 := bstep (se 1 (by rfl) ⟨2365685, by rfl⟩ : syracuseStep 3154247 = 4731371) B4731371
theorem B4735799 : Blo 1401520 4735799 := bstep (se 1 (by rfl) ⟨3551849, by rfl⟩ : syracuseStep 4735799 = 7103699) B7103699
theorem B1401663 : Blo 1401520 1401663 := bstep (se 1 (by rfl) ⟨1051247, by rfl⟩ : syracuseStep 1401663 = 2102495) B2102495
theorem B1401823 : Blo 1401520 1401823 := bstep (se 1 (by rfl) ⟨1051367, by rfl⟩ : syracuseStep 1401823 = 2102735) B2102735
theorem B14394347 : Blo 1401520 14394347 := bstep (se 1 (by rfl) ⟨10795760, by rfl⟩ : syracuseStep 14394347 = 21591521) B21591521
theorem B13485163 : Blo 1401520 13485163 := bstep (se 1 (by rfl) ⟨10113872, by rfl⟩ : syracuseStep 13485163 = 20227745) B20227745
theorem B1401983 : Blo 1401520 1401983 := bstep (se 1 (by rfl) ⟨1051487, by rfl⟩ : syracuseStep 1401983 = 2102975) B2102975
theorem B19195193 : Blo 1401520 19195193 := bstep (se 2 (by rfl) ⟨7198197, by rfl⟩ : syracuseStep 19195193 = 14396395) B14396395
theorem B3548519 : Blo 1401520 3548519 := bstep (se 1 (by rfl) ⟨2661389, by rfl⟩ : syracuseStep 3548519 = 5322779) B5322779
theorem B3155327 : Blo 1401520 3155327 := bstep (se 1 (by rfl) ⟨2366495, by rfl⟩ : syracuseStep 3155327 = 4732991) B4732991
theorem B1402239 : Blo 1401520 1402239 := bstep (se 1 (by rfl) ⟨1051679, by rfl⟩ : syracuseStep 1402239 = 2103359) B2103359
theorem B1402351 : Blo 1401520 1402351 := bstep (se 1 (by rfl) ⟨1051763, by rfl⟩ : syracuseStep 1402351 = 2103527) B2103527
theorem B8979959 : Blo 1401520 8979959 := bstep (se 1 (by rfl) ⟨6734969, by rfl⟩ : syracuseStep 8979959 = 13469939) B13469939
theorem B1402471 : Blo 1401520 1402471 := bstep (se 1 (by rfl) ⟨1051853, by rfl⟩ : syracuseStep 1402471 = 2103707) B2103707
theorem B3991265 : Blo 1401520 3991265 := bstep (se 2 (by rfl) ⟨1496724, by rfl⟩ : syracuseStep 3991265 = 2993449) B2993449
theorem B3549055 : Blo 1401520 3549055 := bstep (se 1 (by rfl) ⟨2661791, by rfl⟩ : syracuseStep 3549055 = 5323583) B5323583
theorem B1402751 : Blo 1401520 1402751 := bstep (se 1 (by rfl) ⟨1052063, by rfl⟩ : syracuseStep 1402751 = 2104127) B2104127
theorem B5327167 : Blo 1401520 5327167 := bstep (se 1 (by rfl) ⟨3995375, by rfl⟩ : syracuseStep 5327167 = 7990751) B7990751
theorem B55413067 : Blo 1401520 55413067 := bstep (se 1 (by rfl) ⟨41559800, by rfl⟩ : syracuseStep 55413067 = 83119601) B83119601
theorem B7105319 : Blo 1401520 7105319 := bstep (se 1 (by rfl) ⟨5328989, by rfl⟩ : syracuseStep 7105319 = 10657979) B10657979
theorem B3992449 : Blo 1401520 3992449 := bstep (se 2 (by rfl) ⟨1497168, by rfl⟩ : syracuseStep 3992449 = 2994337) B2994337
theorem B8989649 : Blo 1401520 8989649 := bstep (se 2 (by rfl) ⟨3371118, by rfl⟩ : syracuseStep 8989649 = 6742237) B6742237
theorem B3157289 : Blo 1401520 3157289 := bstep (se 2 (by rfl) ⟨1183983, by rfl⟩ : syracuseStep 3157289 = 2367967) B2367967
theorem B3992939 : Blo 1401520 3992939 := bstep (se 1 (by rfl) ⟨2994704, by rfl⟩ : syracuseStep 3992939 = 5989409) B5989409
theorem B98496161 : Blo 1401520 98496161 := bstep (se 2 (by rfl) ⟨36936060, by rfl⟩ : syracuseStep 98496161 = 73872121) B73872121
theorem B4050719 : Blo 1401520 4050719 := bstep (se 1 (by rfl) ⟨3038039, by rfl⟩ : syracuseStep 4050719 = 6076079) B6076079
theorem B7098191 : Blo 1401520 7098191 := bstep (se 1 (by rfl) ⟨5323643, by rfl⟩ : syracuseStep 7098191 = 10647287) B10647287
theorem B4050811 : Blo 1401520 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B3371321 : Blo 1401520 3371321 := bstep (se 2 (by rfl) ⟨1264245, by rfl⟩ : syracuseStep 3371321 = 2528491) B2528491
theorem B3551627 : Blo 1401520 3551627 := bstep (se 1 (by rfl) ⟨2663720, by rfl⟩ : syracuseStep 3551627 = 5327441) B5327441
theorem B3649931 : Blo 1401520 3649931 := bstep (se 1 (by rfl) ⟨2737448, by rfl⟩ : syracuseStep 3649931 = 5474897) B5474897
theorem B1577407 : Blo 1401520 1577407 := bstep (se 1 (by rfl) ⟨1183055, by rfl⟩ : syracuseStep 1577407 = 2366111) B2366111
theorem B3371831 : Blo 1401520 3371831 := bstep (se 1 (by rfl) ⟨2528873, by rfl⟩ : syracuseStep 3371831 = 5057747) B5057747
theorem B4731803 : Blo 1401520 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B8762377 : Blo 1401520 8762377 := bstep (se 2 (by rfl) ⟨3285891, by rfl⟩ : syracuseStep 8762377 = 6571783) B6571783
theorem B230291099 : Blo 1401520 230291099 := bstep (se 1 (by rfl) ⟨172718324, by rfl⟩ : syracuseStep 230291099 = 345436649) B345436649
theorem B1578703 : Blo 1401520 1578703 := bstep (se 1 (by rfl) ⟨1184027, by rfl⟩ : syracuseStep 1578703 = 2368055) B2368055
theorem B15169427 : Blo 1401520 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B1578919 : Blo 1401520 1578919 := bstep (se 1 (by rfl) ⟨1184189, by rfl⟩ : syracuseStep 1578919 = 2368379) B2368379
theorem B2365355 : Blo 1401520 2365355 := bstep (se 1 (by rfl) ⟨1774016, by rfl⟩ : syracuseStep 2365355 = 3548033) B3548033
theorem B2365375 : Blo 1401520 2365375 := bstep (se 1 (by rfl) ⟨1774031, by rfl⟩ : syracuseStep 2365375 = 3548063) B3548063
theorem B2996327 : Blo 1401520 2996327 := bstep (se 1 (by rfl) ⟨2247245, by rfl⟩ : syracuseStep 2996327 = 4494491) B4494491
theorem B59144363 : Blo 1401520 59144363 := bstep (se 1 (by rfl) ⟨44358272, by rfl⟩ : syracuseStep 59144363 = 88716545) B88716545
theorem B2996635 : Blo 1401520 2996635 := bstep (se 1 (by rfl) ⟨2247476, by rfl⟩ : syracuseStep 2996635 = 4494953) B4494953
theorem B25598699 : Blo 1401520 25598699 := bstep (se 1 (by rfl) ⟨19199024, by rfl⟩ : syracuseStep 25598699 = 38398049) B38398049
theorem B1997563 : Blo 1401520 1997563 := bstep (se 1 (by rfl) ⟨1498172, by rfl⟩ : syracuseStep 1997563 = 2996345) B2996345
theorem B3840809 : Blo 1401520 3840809 := bstep (se 2 (by rfl) ⟨1440303, by rfl⟩ : syracuseStep 3840809 = 2880607) B2880607
theorem B7584607 : Blo 1401520 7584607 := bstep (se 1 (by rfl) ⟨5688455, by rfl⟩ : syracuseStep 7584607 = 11376911) B11376911
theorem B36453361 : Blo 1401520 36453361 := bstep (se 2 (by rfl) ⟨13670010, by rfl⟩ : syracuseStep 36453361 = 27340021) B27340021
theorem B3996697 : Blo 1401520 3996697 := bstep (se 2 (by rfl) ⟨1498761, by rfl⟩ : syracuseStep 3996697 = 2997523) B2997523
theorem B4734233 : Blo 1401520 4734233 := bstep (se 2 (by rfl) ⟨1775337, by rfl⟩ : syracuseStep 4734233 = 3550675) B3550675
theorem B7986559 : Blo 1401520 7986559 := bstep (se 1 (by rfl) ⟨5989919, by rfl⟩ : syracuseStep 7986559 = 11979839) B11979839
theorem B2104703 : Blo 1401520 2104703 := bstep (se 1 (by rfl) ⟨1578527, by rfl⟩ : syracuseStep 2104703 = 3157055) B3157055
theorem B38903291 : Blo 1401520 38903291 := bstep (se 1 (by rfl) ⟨29177468, by rfl⟩ : syracuseStep 38903291 = 58354937) B58354937
theorem B3153545 : Blo 1401520 3153545 := bstep (se 2 (by rfl) ⟨1182579, by rfl⟩ : syracuseStep 3153545 = 2365159) B2365159
theorem B3153563 : Blo 1401520 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B3153599 : Blo 1401520 3153599 := bstep (se 1 (by rfl) ⟨2365199, by rfl⟩ : syracuseStep 3153599 = 4730399) B4730399
theorem B29589239 : Blo 1401520 29589239 := bstep (se 1 (by rfl) ⟨22191929, by rfl⟩ : syracuseStep 29589239 = 44383859) B44383859
theorem B2367751 : Blo 1401520 2367751 := bstep (se 1 (by rfl) ⟨1775813, by rfl⟩ : syracuseStep 2367751 = 3551627) B3551627
theorem B2433287 : Blo 1401520 2433287 := bstep (se 1 (by rfl) ⟨1824965, by rfl⟩ : syracuseStep 2433287 = 3649931) B3649931
theorem B7102889 : Blo 1401520 7102889 := bstep (se 2 (by rfl) ⟨2663583, by rfl⟩ : syracuseStep 7102889 = 5327167) B5327167
theorem B73884089 : Blo 1401520 73884089 := bstep (se 2 (by rfl) ⟨27706533, by rfl⟩ : syracuseStep 73884089 = 55413067) B55413067
theorem B3154535 : Blo 1401520 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B12796795 : Blo 1401520 12796795 := bstep (se 1 (by rfl) ⟨9597596, by rfl⟩ : syracuseStep 12796795 = 19195193) B19195193
theorem B2663417 : Blo 1401520 2663417 := bstep (se 2 (by rfl) ⟨998781, by rfl⟩ : syracuseStep 2663417 = 1997563) B1997563
theorem B153527399 : Blo 1401520 153527399 := bstep (se 1 (by rfl) ⟨115145549, by rfl⟩ : syracuseStep 153527399 = 230291099) B230291099
theorem B48604481 : Blo 1401520 48604481 := bstep (se 2 (by rfl) ⟨18226680, by rfl⟩ : syracuseStep 48604481 = 36453361) B36453361
theorem B11683169 : Blo 1401520 11683169 := bstep (se 2 (by rfl) ⟨4381188, by rfl⟩ : syracuseStep 11683169 = 8762377) B8762377
theorem B39429575 : Blo 1401520 39429575 := bstep (se 1 (by rfl) ⟨29572181, by rfl⟩ : syracuseStep 39429575 = 59144363) B59144363
theorem B17065799 : Blo 1401520 17065799 := bstep (se 1 (by rfl) ⟨12799349, by rfl⟩ : syracuseStep 17065799 = 25598699) B25598699
theorem B4736879 : Blo 1401520 4736879 := bstep (se 1 (by rfl) ⟨3552659, by rfl⟩ : syracuseStep 4736879 = 7105319) B7105319
theorem B10242157 : Blo 1401520 10242157 := bstep (se 3 (by rfl) ⟨1920404, by rfl⟩ : syracuseStep 10242157 = 3840809) B3840809
theorem B3156155 : Blo 1401520 3156155 := bstep (se 1 (by rfl) ⟨2367116, by rfl⟩ : syracuseStep 3156155 = 4734233) B4734233
theorem B1403135 : Blo 1401520 1403135 := bstep (se 1 (by rfl) ⟨1052351, by rfl⟩ : syracuseStep 1403135 = 2104703) B2104703
theorem B5401081 : Blo 1401520 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B3369707 : Blo 1401520 3369707 := bstep (se 1 (by rfl) ⟨2527280, by rfl⟩ : syracuseStep 3369707 = 5054561) B5054561
theorem B61483799 : Blo 1401520 61483799 := bstep (se 1 (by rfl) ⟨46112849, by rfl⟩ : syracuseStep 61483799 = 92225699) B92225699
theorem B3157199 : Blo 1401520 3157199 := bstep (se 1 (by rfl) ⟨2367899, by rfl⟩ : syracuseStep 3157199 = 4735799) B4735799
theorem B2247887 : Blo 1401520 2247887 := bstep (se 1 (by rfl) ⟨1685915, by rfl⟩ : syracuseStep 2247887 = 3371831) B3371831
theorem B9596231 : Blo 1401520 9596231 := bstep (se 1 (by rfl) ⟨7197173, by rfl⟩ : syracuseStep 9596231 = 14394347) B14394347
theorem B8990189 : Blo 1401520 8990189 := bstep (se 3 (by rfl) ⟨1685660, by rfl⟩ : syracuseStep 8990189 = 3371321) B3371321
theorem B10112809 : Blo 1401520 10112809 := bstep (se 2 (by rfl) ⟨3792303, by rfl⟩ : syracuseStep 10112809 = 7584607) B7584607
theorem B10112951 : Blo 1401520 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B1576903 : Blo 1401520 1576903 := bstep (se 1 (by rfl) ⟨1182677, by rfl⟩ : syracuseStep 1576903 = 2365355) B2365355
theorem B5328929 : Blo 1401520 5328929 := bstep (se 2 (by rfl) ⟨1998348, by rfl⟩ : syracuseStep 5328929 = 3996697) B3996697
theorem B5993099 : Blo 1401520 5993099 := bstep (se 1 (by rfl) ⟨4494824, by rfl⟩ : syracuseStep 5993099 = 8989649) B8989649
theorem B2102363 : Blo 1401520 2102363 := bstep (se 1 (by rfl) ⟨1576772, by rfl⟩ : syracuseStep 2102363 = 3153545) B3153545
theorem B2102375 : Blo 1401520 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B65664107 : Blo 1401520 65664107 := bstep (se 1 (by rfl) ⟨49248080, by rfl⟩ : syracuseStep 65664107 = 98496161) B98496161
theorem B2102399 : Blo 1401520 2102399 := bstep (se 1 (by rfl) ⟨1576799, by rfl⟩ : syracuseStep 2102399 = 3153599) B3153599
theorem B4732073 : Blo 1401520 4732073 := bstep (se 2 (by rfl) ⟨1774527, by rfl⟩ : syracuseStep 4732073 = 3549055) B3549055
theorem B2700479 : Blo 1401520 2700479 := bstep (se 1 (by rfl) ⟨2025359, by rfl⟩ : syracuseStep 2700479 = 4050719) B4050719
theorem B4732127 : Blo 1401520 4732127 := bstep (se 1 (by rfl) ⟨3549095, by rfl⟩ : syracuseStep 4732127 = 7098191) B7098191
theorem B1775135 : Blo 1401520 1775135 := bstep (se 1 (by rfl) ⟨1331351, by rfl⟩ : syracuseStep 1775135 = 2662703) B2662703
theorem B2102831 : Blo 1401520 2102831 := bstep (se 1 (by rfl) ⟨1577123, by rfl⟩ : syracuseStep 2102831 = 3154247) B3154247
theorem B3995513 : Blo 1401520 3995513 := bstep (se 2 (by rfl) ⟨1498317, by rfl⟩ : syracuseStep 3995513 = 2996635) B2996635
theorem B2103209 : Blo 1401520 2103209 := bstep (se 2 (by rfl) ⟨788703, by rfl⟩ : syracuseStep 2103209 = 1577407) B1577407
theorem B2365679 : Blo 1401520 2365679 := bstep (se 1 (by rfl) ⟨1774259, by rfl⟩ : syracuseStep 2365679 = 3548519) B3548519
theorem B2103551 : Blo 1401520 2103551 := bstep (se 1 (by rfl) ⟨1577663, by rfl⟩ : syracuseStep 2103551 = 3155327) B3155327
theorem B5986639 : Blo 1401520 5986639 := bstep (se 1 (by rfl) ⟨4489979, by rfl⟩ : syracuseStep 5986639 = 8979959) B8979959
theorem B2660843 : Blo 1401520 2660843 := bstep (se 1 (by rfl) ⟨1995632, by rfl⟩ : syracuseStep 2660843 = 3991265) B3991265
theorem B5323265 : Blo 1401520 5323265 := bstep (se 2 (by rfl) ⟨1996224, by rfl⟩ : syracuseStep 5323265 = 3992449) B3992449
theorem B1997551 : Blo 1401520 1997551 := bstep (se 1 (by rfl) ⟨1498163, by rfl⟩ : syracuseStep 1997551 = 2996327) B2996327
theorem B17980217 : Blo 1401520 17980217 := bstep (se 2 (by rfl) ⟨6742581, by rfl⟩ : syracuseStep 17980217 = 13485163) B13485163
theorem B10648745 : Blo 1401520 10648745 := bstep (se 2 (by rfl) ⟨3993279, by rfl⟩ : syracuseStep 10648745 = 7986559) B7986559
theorem B78904637 : Blo 1401520 78904637 := bstep (se 3 (by rfl) ⟨14794619, by rfl⟩ : syracuseStep 78904637 = 29589239) B29589239
theorem B2104859 : Blo 1401520 2104859 := bstep (se 1 (by rfl) ⟨1578644, by rfl⟩ : syracuseStep 2104859 = 3157289) B3157289
theorem B2661959 : Blo 1401520 2661959 := bstep (se 1 (by rfl) ⟨1996469, by rfl⟩ : syracuseStep 2661959 = 3992939) B3992939
theorem B2104937 : Blo 1401520 2104937 := bstep (se 2 (by rfl) ⟨789351, by rfl⟩ : syracuseStep 2104937 = 1578703) B1578703
theorem B25935527 : Blo 1401520 25935527 := bstep (se 1 (by rfl) ⟨19451645, by rfl⟩ : syracuseStep 25935527 = 38903291) B38903291
theorem B2105225 : Blo 1401520 2105225 := bstep (se 2 (by rfl) ⟨789459, by rfl⟩ : syracuseStep 2105225 = 1578919) B1578919
theorem B3153833 : Blo 1401520 3153833 := bstep (se 2 (by rfl) ⟨1182687, by rfl⟩ : syracuseStep 3153833 = 2365375) B2365375
theorem B13656209 : Blo 1401520 13656209 := bstep (se 2 (by rfl) ⟨5121078, by rfl⟩ : syracuseStep 13656209 = 10242157) B10242157
theorem B1622191 : Blo 1401520 1622191 := bstep (se 1 (by rfl) ⟨1216643, by rfl⟩ : syracuseStep 1622191 = 2433287) B2433287
theorem B4735259 : Blo 1401520 4735259 := bstep (se 1 (by rfl) ⟨3551444, by rfl⟩ : syracuseStep 4735259 = 7102889) B7102889
theorem B7201277 : Blo 1401520 7201277 := bstep (se 3 (by rfl) ⟨1350239, by rfl⟩ : syracuseStep 7201277 = 2700479) B2700479
theorem B7201441 : Blo 1401520 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B1401575 : Blo 1401520 1401575 := bstep (se 1 (by rfl) ⟨1051181, by rfl⟩ : syracuseStep 1401575 = 2102363) B2102363
theorem B1401583 : Blo 1401520 1401583 := bstep (se 1 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 1401583 = 2102375) B2102375
theorem B102351599 : Blo 1401520 102351599 := bstep (se 1 (by rfl) ⟨76763699, by rfl⟩ : syracuseStep 102351599 = 153527399) B153527399
theorem B1401599 : Blo 1401520 1401599 := bstep (se 1 (by rfl) ⟨1051199, by rfl⟩ : syracuseStep 1401599 = 2102399) B2102399
theorem B3154715 : Blo 1401520 3154715 := bstep (se 1 (by rfl) ⟨2366036, by rfl⟩ : syracuseStep 3154715 = 4732073) B4732073
theorem B3154751 : Blo 1401520 3154751 := bstep (se 1 (by rfl) ⟨2366063, by rfl⟩ : syracuseStep 3154751 = 4732127) B4732127
theorem B1401887 : Blo 1401520 1401887 := bstep (se 1 (by rfl) ⟨1051415, by rfl⟩ : syracuseStep 1401887 = 2102831) B2102831
theorem B2663675 : Blo 1401520 2663675 := bstep (se 1 (by rfl) ⟨1997756, by rfl⟩ : syracuseStep 2663675 = 3995513) B3995513
theorem B1402139 : Blo 1401520 1402139 := bstep (se 1 (by rfl) ⟨1051604, by rfl⟩ : syracuseStep 1402139 = 2103209) B2103209
theorem B1402367 : Blo 1401520 1402367 := bstep (se 1 (by rfl) ⟨1051775, by rfl⟩ : syracuseStep 1402367 = 2103551) B2103551
theorem B3548843 : Blo 1401520 3548843 := bstep (se 1 (by rfl) ⟨2661632, by rfl⟩ : syracuseStep 3548843 = 5323265) B5323265
theorem B2246471 : Blo 1401520 2246471 := bstep (se 1 (by rfl) ⟨1684853, by rfl⟩ : syracuseStep 2246471 = 3369707) B3369707
theorem B11986811 : Blo 1401520 11986811 := bstep (se 1 (by rfl) ⟨8990108, by rfl⟩ : syracuseStep 11986811 = 17980217) B17980217
theorem B68249573 : Blo 1401520 68249573 := bstep (se 4 (by rfl) ⟨6398397, by rfl⟩ : syracuseStep 68249573 = 12796795) B12796795
theorem B52603091 : Blo 1401520 52603091 := bstep (se 1 (by rfl) ⟨39452318, by rfl⟩ : syracuseStep 52603091 = 78904637) B78904637
theorem B1403239 : Blo 1401520 1403239 := bstep (se 1 (by rfl) ⟨1052429, by rfl⟩ : syracuseStep 1403239 = 2104859) B2104859
theorem B1403291 : Blo 1401520 1403291 := bstep (se 1 (by rfl) ⟨1052468, by rfl⟩ : syracuseStep 1403291 = 2104937) B2104937
theorem B1403483 : Blo 1401520 1403483 := bstep (se 1 (by rfl) ⟨1052612, by rfl⟩ : syracuseStep 1403483 = 2105225) B2105225
theorem B3157001 : Blo 1401520 3157001 := bstep (se 2 (by rfl) ⟨1183875, by rfl⟩ : syracuseStep 3157001 = 2367751) B2367751
theorem B7982185 : Blo 1401520 7982185 := bstep (se 2 (by rfl) ⟨2993319, by rfl⟩ : syracuseStep 7982185 = 5986639) B5986639
theorem B32402987 : Blo 1401520 32402987 := bstep (se 1 (by rfl) ⟨24302240, by rfl⟩ : syracuseStep 32402987 = 48604481) B48604481
theorem B3157919 : Blo 1401520 3157919 := bstep (se 1 (by rfl) ⟨2368439, by rfl⟩ : syracuseStep 3157919 = 4736879) B4736879
theorem B10653605 : Blo 1401520 10653605 := bstep (se 4 (by rfl) ⟨998775, by rfl⟩ : syracuseStep 10653605 = 1997551) B1997551
theorem B1577119 : Blo 1401520 1577119 := bstep (se 1 (by rfl) ⟨1182839, by rfl⟩ : syracuseStep 1577119 = 2365679) B2365679
theorem B1773895 : Blo 1401520 1773895 := bstep (se 1 (by rfl) ⟨1330421, by rfl⟩ : syracuseStep 1773895 = 2660843) B2660843
theorem B40989199 : Blo 1401520 40989199 := bstep (se 1 (by rfl) ⟨30741899, by rfl⟩ : syracuseStep 40989199 = 61483799) B61483799
theorem B7099163 : Blo 1401520 7099163 := bstep (se 1 (by rfl) ⟨5324372, by rfl⟩ : syracuseStep 7099163 = 10648745) B10648745
theorem B5993459 : Blo 1401520 5993459 := bstep (se 1 (by rfl) ⟨4495094, by rfl⟩ : syracuseStep 5993459 = 8990189) B8990189
theorem B1774639 : Blo 1401520 1774639 := bstep (se 1 (by rfl) ⟨1330979, by rfl⟩ : syracuseStep 1774639 = 2661959) B2661959
theorem B17290351 : Blo 1401520 17290351 := bstep (se 1 (by rfl) ⟨12967763, by rfl⟩ : syracuseStep 17290351 = 25935527) B25935527
theorem B2102537 : Blo 1401520 2102537 := bstep (se 2 (by rfl) ⟨788451, by rfl⟩ : syracuseStep 2102537 = 1576903) B1576903
theorem B2102555 : Blo 1401520 2102555 := bstep (se 1 (by rfl) ⟨1576916, by rfl⟩ : syracuseStep 2102555 = 3153833) B3153833
theorem B3552619 : Blo 1401520 3552619 := bstep (se 1 (by rfl) ⟨2664464, by rfl⟩ : syracuseStep 3552619 = 5328929) B5328929
theorem B49256059 : Blo 1401520 49256059 := bstep (se 1 (by rfl) ⟨36942044, by rfl⟩ : syracuseStep 49256059 = 73884089) B73884089
theorem B2103023 : Blo 1401520 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B3995399 : Blo 1401520 3995399 := bstep (se 1 (by rfl) ⟨2996549, by rfl⟩ : syracuseStep 3995399 = 5993099) B5993099
theorem B1775611 : Blo 1401520 1775611 := bstep (se 1 (by rfl) ⟨1331708, by rfl⟩ : syracuseStep 1775611 = 2663417) B2663417
theorem B43776071 : Blo 1401520 43776071 := bstep (se 1 (by rfl) ⟨32832053, by rfl⟩ : syracuseStep 43776071 = 65664107) B65664107
theorem B7788779 : Blo 1401520 7788779 := bstep (se 1 (by rfl) ⟨5841584, by rfl⟩ : syracuseStep 7788779 = 11683169) B11683169
theorem B26286383 : Blo 1401520 26286383 := bstep (se 1 (by rfl) ⟨19714787, by rfl⟩ : syracuseStep 26286383 = 39429575) B39429575
theorem B11377199 : Blo 1401520 11377199 := bstep (se 1 (by rfl) ⟨8532899, by rfl⟩ : syracuseStep 11377199 = 17065799) B17065799
theorem B4733693 : Blo 1401520 4733693 := bstep (se 3 (by rfl) ⟨887567, by rfl⟩ : syracuseStep 4733693 = 1775135) B1775135
theorem B2104103 : Blo 1401520 2104103 := bstep (se 1 (by rfl) ⟨1578077, by rfl⟩ : syracuseStep 2104103 = 3156155) B3156155
theorem B2104799 : Blo 1401520 2104799 := bstep (se 1 (by rfl) ⟨1578599, by rfl⟩ : syracuseStep 2104799 = 3157199) B3157199
theorem B1498591 : Blo 1401520 1498591 := bstep (se 1 (by rfl) ⟨1123943, by rfl⟩ : syracuseStep 1498591 = 2247887) B2247887
theorem B6397487 : Blo 1401520 6397487 := bstep (se 1 (by rfl) ⟨4798115, by rfl⟩ : syracuseStep 6397487 = 9596231) B9596231
theorem B13483745 : Blo 1401520 13483745 := bstep (se 2 (by rfl) ⟨5056404, by rfl⟩ : syracuseStep 13483745 = 10112809) B10112809
theorem B6741967 : Blo 1401520 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B2162921 : Blo 1401520 2162921 := bstep (se 2 (by rfl) ⟨811095, by rfl⟩ : syracuseStep 2162921 = 1622191) B1622191
theorem B4800851 : Blo 1401520 4800851 := bstep (se 1 (by rfl) ⟨3600638, by rfl⟩ : syracuseStep 4800851 = 7201277) B7201277
theorem B1401691 : Blo 1401520 1401691 := bstep (se 1 (by rfl) ⟨1051268, by rfl⟩ : syracuseStep 1401691 = 2102537) B2102537
theorem B1401703 : Blo 1401520 1401703 := bstep (se 1 (by rfl) ⟨1051277, by rfl⟩ : syracuseStep 1401703 = 2102555) B2102555
theorem B9601921 : Blo 1401520 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B1402015 : Blo 1401520 1402015 := bstep (se 1 (by rfl) ⟨1051511, by rfl⟩ : syracuseStep 1402015 = 2103023) B2103023
theorem B2663599 : Blo 1401520 2663599 := bstep (se 1 (by rfl) ⟨1997699, by rfl⟩ : syracuseStep 2663599 = 3995399) B3995399
theorem B45499715 : Blo 1401520 45499715 := bstep (se 1 (by rfl) ⟨34124786, by rfl⟩ : syracuseStep 45499715 = 68249573) B68249573
theorem B10642913 : Blo 1401520 10642913 := bstep (se 2 (by rfl) ⟨3991092, by rfl⟩ : syracuseStep 10642913 = 7982185) B7982185
theorem B17524255 : Blo 1401520 17524255 := bstep (se 1 (by rfl) ⟨13143191, by rfl⟩ : syracuseStep 17524255 = 26286383) B26286383
theorem B4736825 : Blo 1401520 4736825 := bstep (se 2 (by rfl) ⟨1776309, by rfl⟩ : syracuseStep 4736825 = 3552619) B3552619
theorem B3155795 : Blo 1401520 3155795 := bstep (se 1 (by rfl) ⟨2366846, by rfl⟩ : syracuseStep 3155795 = 4733693) B4733693
theorem B1402735 : Blo 1401520 1402735 := bstep (se 1 (by rfl) ⟨1052051, by rfl⟩ : syracuseStep 1402735 = 2104103) B2104103
theorem B1403199 : Blo 1401520 1403199 := bstep (se 1 (by rfl) ⟨1052399, by rfl⟩ : syracuseStep 1403199 = 2104799) B2104799
theorem B8989163 : Blo 1401520 8989163 := bstep (se 1 (by rfl) ⟨6741872, by rfl⟩ : syracuseStep 8989163 = 13483745) B13483745
theorem B8989289 : Blo 1401520 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B3156839 : Blo 1401520 3156839 := bstep (se 1 (by rfl) ⟨2367629, by rfl⟩ : syracuseStep 3156839 = 4735259) B4735259
theorem B36416557 : Blo 1401520 36416557 := bstep (se 3 (by rfl) ⟨6828104, by rfl⟩ : syracuseStep 36416557 = 13656209) B13656209
theorem B68234399 : Blo 1401520 68234399 := bstep (se 1 (by rfl) ⟨51175799, by rfl⟩ : syracuseStep 68234399 = 102351599) B102351599
theorem B54652265 : Blo 1401520 54652265 := bstep (se 2 (by rfl) ⟨20494599, by rfl⟩ : syracuseStep 54652265 = 40989199) B40989199
theorem B7991207 : Blo 1401520 7991207 := bstep (se 1 (by rfl) ⟨5993405, by rfl⟩ : syracuseStep 7991207 = 11986811) B11986811
theorem B29184047 : Blo 1401520 29184047 := bstep (se 1 (by rfl) ⟨21888035, by rfl⟩ : syracuseStep 29184047 = 43776071) B43776071
theorem B4264991 : Blo 1401520 4264991 := bstep (se 1 (by rfl) ⟨3198743, by rfl⟩ : syracuseStep 4264991 = 6397487) B6397487
theorem B2102825 : Blo 1401520 2102825 := bstep (se 2 (by rfl) ⟨788559, by rfl⟩ : syracuseStep 2102825 = 1577119) B1577119
theorem B2365193 : Blo 1401520 2365193 := bstep (se 2 (by rfl) ⟨886947, by rfl⟩ : syracuseStep 2365193 = 1773895) B1773895
theorem B2103143 : Blo 1401520 2103143 := bstep (se 1 (by rfl) ⟨1577357, by rfl⟩ : syracuseStep 2103143 = 3154715) B3154715
theorem B4732775 : Blo 1401520 4732775 := bstep (se 1 (by rfl) ⟨3549581, by rfl⟩ : syracuseStep 4732775 = 7099163) B7099163
theorem B2103167 : Blo 1401520 2103167 := bstep (se 1 (by rfl) ⟨1577375, by rfl⟩ : syracuseStep 2103167 = 3154751) B3154751
theorem B92215205 : Blo 1401520 92215205 := bstep (se 4 (by rfl) ⟨8645175, by rfl⟩ : syracuseStep 92215205 = 17290351) B17290351
theorem B3995639 : Blo 1401520 3995639 := bstep (se 1 (by rfl) ⟨2996729, by rfl⟩ : syracuseStep 3995639 = 5993459) B5993459
theorem B1775783 : Blo 1401520 1775783 := bstep (se 1 (by rfl) ⟨1331837, by rfl⟩ : syracuseStep 1775783 = 2663675) B2663675
theorem B2365895 : Blo 1401520 2365895 := bstep (se 1 (by rfl) ⟨1774421, by rfl⟩ : syracuseStep 2365895 = 3548843) B3548843
theorem B1497647 : Blo 1401520 1497647 := bstep (se 1 (by rfl) ⟨1123235, by rfl⟩ : syracuseStep 1497647 = 2246471) B2246471
theorem B2366185 : Blo 1401520 2366185 := bstep (se 2 (by rfl) ⟨887319, by rfl⟩ : syracuseStep 2366185 = 1774639) B1774639
theorem B35068727 : Blo 1401520 35068727 := bstep (se 1 (by rfl) ⟨26301545, by rfl⟩ : syracuseStep 35068727 = 52603091) B52603091
theorem B5192519 : Blo 1401520 5192519 := bstep (se 1 (by rfl) ⟨3894389, by rfl⟩ : syracuseStep 5192519 = 7788779) B7788779
theorem B7584799 : Blo 1401520 7584799 := bstep (se 1 (by rfl) ⟨5688599, by rfl⟩ : syracuseStep 7584799 = 11377199) B11377199
theorem B1998121 : Blo 1401520 1998121 := bstep (se 2 (by rfl) ⟨749295, by rfl⟩ : syracuseStep 1998121 = 1498591) B1498591
theorem B2104667 : Blo 1401520 2104667 := bstep (se 1 (by rfl) ⟨1578500, by rfl⟩ : syracuseStep 2104667 = 3157001) B3157001
theorem B65674745 : Blo 1401520 65674745 := bstep (se 2 (by rfl) ⟨24628029, by rfl⟩ : syracuseStep 65674745 = 49256059) B49256059
theorem B21601991 : Blo 1401520 21601991 := bstep (se 1 (by rfl) ⟨16201493, by rfl⟩ : syracuseStep 21601991 = 32402987) B32402987
theorem B2105279 : Blo 1401520 2105279 := bstep (se 1 (by rfl) ⟨1578959, by rfl⟩ : syracuseStep 2105279 = 3157919) B3157919
theorem B7102403 : Blo 1401520 7102403 := bstep (se 1 (by rfl) ⟨5326802, by rfl⟩ : syracuseStep 7102403 = 10653605) B10653605
theorem B2367481 : Blo 1401520 2367481 := bstep (se 2 (by rfl) ⟨887805, by rfl⟩ : syracuseStep 2367481 = 1775611) B1775611
theorem B19456031 : Blo 1401520 19456031 := bstep (se 1 (by rfl) ⟨14592023, by rfl⟩ : syracuseStep 19456031 = 29184047) B29184047
theorem B4735421 : Blo 1401520 4735421 := bstep (se 3 (by rfl) ⟨887891, by rfl⟩ : syracuseStep 4735421 = 1775783) B1775783
theorem B5767789 : Blo 1401520 5767789 := bstep (se 3 (by rfl) ⟨1081460, by rfl⟩ : syracuseStep 5767789 = 2162921) B2162921
theorem B2843327 : Blo 1401520 2843327 := bstep (se 1 (by rfl) ⟨2132495, by rfl⟩ : syracuseStep 2843327 = 4264991) B4264991
theorem B3154913 : Blo 1401520 3154913 := bstep (se 2 (by rfl) ⟨1183092, by rfl⟩ : syracuseStep 3154913 = 2366185) B2366185
theorem B7095275 : Blo 1401520 7095275 := bstep (se 1 (by rfl) ⟨5321456, by rfl⟩ : syracuseStep 7095275 = 10642913) B10642913
theorem B1401883 : Blo 1401520 1401883 := bstep (se 1 (by rfl) ⟨1051412, by rfl⟩ : syracuseStep 1401883 = 2102825) B2102825
theorem B1402095 : Blo 1401520 1402095 := bstep (se 1 (by rfl) ⟨1051571, by rfl⟩ : syracuseStep 1402095 = 2103143) B2103143
theorem B3155183 : Blo 1401520 3155183 := bstep (se 1 (by rfl) ⟨2366387, by rfl⟩ : syracuseStep 3155183 = 4732775) B4732775
theorem B1402111 : Blo 1401520 1402111 := bstep (se 1 (by rfl) ⟨1051583, by rfl⟩ : syracuseStep 1402111 = 2103167) B2103167
theorem B2663759 : Blo 1401520 2663759 := bstep (se 1 (by rfl) ⟨1997819, by rfl⟩ : syracuseStep 2663759 = 3995639) B3995639
theorem B48555409 : Blo 1401520 48555409 := bstep (se 2 (by rfl) ⟨18208278, by rfl⟩ : syracuseStep 48555409 = 36416557) B36416557
theorem B2664161 : Blo 1401520 2664161 := bstep (se 2 (by rfl) ⟨999060, by rfl⟩ : syracuseStep 2664161 = 1998121) B1998121
theorem B51210245 : Blo 1401520 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B23365673 : Blo 1401520 23365673 := bstep (se 2 (by rfl) ⟨8762127, by rfl⟩ : syracuseStep 23365673 = 17524255) B17524255
theorem B13846717 : Blo 1401520 13846717 := bstep (se 3 (by rfl) ⟨2596259, by rfl⟩ : syracuseStep 13846717 = 5192519) B5192519
theorem B1403111 : Blo 1401520 1403111 := bstep (se 1 (by rfl) ⟨1052333, by rfl⟩ : syracuseStep 1403111 = 2104667) B2104667
theorem B5327471 : Blo 1401520 5327471 := bstep (se 1 (by rfl) ⟨3995603, by rfl⟩ : syracuseStep 5327471 = 7991207) B7991207
theorem B1403519 : Blo 1401520 1403519 := bstep (se 1 (by rfl) ⟨1052639, by rfl⟩ : syracuseStep 1403519 = 2105279) B2105279
theorem B3156641 : Blo 1401520 3156641 := bstep (se 2 (by rfl) ⟨1183740, by rfl⟩ : syracuseStep 3156641 = 2367481) B2367481
theorem B1576795 : Blo 1401520 1576795 := bstep (se 1 (by rfl) ⟨1182596, by rfl⟩ : syracuseStep 1576795 = 2365193) B2365193
theorem B3157883 : Blo 1401520 3157883 := bstep (se 1 (by rfl) ⟨2368412, by rfl⟩ : syracuseStep 3157883 = 4736825) B4736825
theorem B61476803 : Blo 1401520 61476803 := bstep (se 1 (by rfl) ⟨46107602, by rfl⟩ : syracuseStep 61476803 = 92215205) B92215205
theorem B10113065 : Blo 1401520 10113065 := bstep (se 2 (by rfl) ⟨3792399, by rfl⟩ : syracuseStep 10113065 = 7584799) B7584799
theorem B3993725 : Blo 1401520 3993725 := bstep (se 3 (by rfl) ⟨748823, by rfl⟩ : syracuseStep 3993725 = 1497647) B1497647
theorem B3551465 : Blo 1401520 3551465 := bstep (se 2 (by rfl) ⟨1331799, by rfl⟩ : syracuseStep 3551465 = 2663599) B2663599
theorem B1577263 : Blo 1401520 1577263 := bstep (se 1 (by rfl) ⟨1182947, by rfl⟩ : syracuseStep 1577263 = 2365895) B2365895
theorem B5992775 : Blo 1401520 5992775 := bstep (se 1 (by rfl) ⟨4494581, by rfl⟩ : syracuseStep 5992775 = 8989163) B8989163
theorem B5992859 : Blo 1401520 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B36434843 : Blo 1401520 36434843 := bstep (se 1 (by rfl) ⟨27326132, by rfl⟩ : syracuseStep 36434843 = 54652265) B54652265
theorem B43783163 : Blo 1401520 43783163 := bstep (se 1 (by rfl) ⟨32837372, by rfl⟩ : syracuseStep 43783163 = 65674745) B65674745
theorem B3200567 : Blo 1401520 3200567 := bstep (se 1 (by rfl) ⟨2400425, by rfl⟩ : syracuseStep 3200567 = 4800851) B4800851
theorem B30333143 : Blo 1401520 30333143 := bstep (se 1 (by rfl) ⟨22749857, by rfl⟩ : syracuseStep 30333143 = 45499715) B45499715
theorem B2103863 : Blo 1401520 2103863 := bstep (se 1 (by rfl) ⟨1577897, by rfl⟩ : syracuseStep 2103863 = 3155795) B3155795
theorem B23379151 : Blo 1401520 23379151 := bstep (se 1 (by rfl) ⟨17534363, by rfl⟩ : syracuseStep 23379151 = 35068727) B35068727
theorem B2104559 : Blo 1401520 2104559 := bstep (se 1 (by rfl) ⟨1578419, by rfl⟩ : syracuseStep 2104559 = 3156839) B3156839
theorem B45489599 : Blo 1401520 45489599 := bstep (se 1 (by rfl) ⟨34117199, by rfl⟩ : syracuseStep 45489599 = 68234399) B68234399
theorem B14401327 : Blo 1401520 14401327 := bstep (se 1 (by rfl) ⟨10800995, by rfl⟩ : syracuseStep 14401327 = 21601991) B21601991
theorem B4734935 : Blo 1401520 4734935 := bstep (se 1 (by rfl) ⟨3551201, by rfl⟩ : syracuseStep 4734935 = 7102403) B7102403
theorem B6742043 : Blo 1401520 6742043 := bstep (se 1 (by rfl) ⟨5056532, by rfl⟩ : syracuseStep 6742043 = 10113065) B10113065
theorem B2662483 : Blo 1401520 2662483 := bstep (se 1 (by rfl) ⟨1996862, by rfl⟩ : syracuseStep 2662483 = 3993725) B3993725
theorem B2367643 : Blo 1401520 2367643 := bstep (se 1 (by rfl) ⟨1775732, by rfl⟩ : syracuseStep 2367643 = 3551465) B3551465
theorem B24289895 : Blo 1401520 24289895 := bstep (se 1 (by rfl) ⟨18217421, by rfl⟩ : syracuseStep 24289895 = 36434843) B36434843
theorem B29188775 : Blo 1401520 29188775 := bstep (se 1 (by rfl) ⟨21891581, by rfl⟩ : syracuseStep 29188775 = 43783163) B43783163
theorem B31172201 : Blo 1401520 31172201 := bstep (se 2 (by rfl) ⟨11689575, by rfl⟩ : syracuseStep 31172201 = 23379151) B23379151
theorem B1402575 : Blo 1401520 1402575 := bstep (se 1 (by rfl) ⟨1051931, by rfl⟩ : syracuseStep 1402575 = 2103863) B2103863
theorem B1403039 : Blo 1401520 1403039 := bstep (se 1 (by rfl) ⟨1052279, by rfl⟩ : syracuseStep 1403039 = 2104559) B2104559
theorem B3156623 : Blo 1401520 3156623 := bstep (se 1 (by rfl) ⟨2367467, by rfl⟩ : syracuseStep 3156623 = 4734935) B4734935
theorem B12970687 : Blo 1401520 12970687 := bstep (se 1 (by rfl) ⟨9728015, by rfl⟩ : syracuseStep 12970687 = 19456031) B19456031
theorem B3156947 : Blo 1401520 3156947 := bstep (se 1 (by rfl) ⟨2367710, by rfl⟩ : syracuseStep 3156947 = 4735421) B4735421
theorem B1895551 : Blo 1401520 1895551 := bstep (se 1 (by rfl) ⟨1421663, by rfl⟩ : syracuseStep 1895551 = 2843327) B2843327
theorem B4730183 : Blo 1401520 4730183 := bstep (se 1 (by rfl) ⟨3547637, by rfl⟩ : syracuseStep 4730183 = 7095275) B7095275
theorem B34140163 : Blo 1401520 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B15577115 : Blo 1401520 15577115 := bstep (se 1 (by rfl) ⟨11682836, by rfl⟩ : syracuseStep 15577115 = 23365673) B23365673
theorem B20222095 : Blo 1401520 20222095 := bstep (se 1 (by rfl) ⟨15166571, by rfl⟩ : syracuseStep 20222095 = 30333143) B30333143
theorem B3551647 : Blo 1401520 3551647 := bstep (se 1 (by rfl) ⟨2663735, by rfl⟩ : syracuseStep 3551647 = 5327471) B5327471
theorem B2102393 : Blo 1401520 2102393 := bstep (se 2 (by rfl) ⟨788397, by rfl⟩ : syracuseStep 2102393 = 1576795) B1576795
theorem B3995183 : Blo 1401520 3995183 := bstep (se 1 (by rfl) ⟨2996387, by rfl⟩ : syracuseStep 3995183 = 5992775) B5992775
theorem B3995239 : Blo 1401520 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B2103017 : Blo 1401520 2103017 := bstep (se 2 (by rfl) ⟨788631, by rfl⟩ : syracuseStep 2103017 = 1577263) B1577263
theorem B2103275 : Blo 1401520 2103275 := bstep (se 1 (by rfl) ⟨1577456, by rfl⟩ : syracuseStep 2103275 = 3154913) B3154913
theorem B7690385 : Blo 1401520 7690385 := bstep (se 2 (by rfl) ⟨2883894, by rfl⟩ : syracuseStep 7690385 = 5767789) B5767789
theorem B2103455 : Blo 1401520 2103455 := bstep (se 1 (by rfl) ⟨1577591, by rfl⟩ : syracuseStep 2103455 = 3155183) B3155183
theorem B1775839 : Blo 1401520 1775839 := bstep (se 1 (by rfl) ⟨1331879, by rfl⟩ : syracuseStep 1775839 = 2663759) B2663759
theorem B73849157 : Blo 1401520 73849157 := bstep (se 4 (by rfl) ⟨6923358, by rfl⟩ : syracuseStep 73849157 = 13846717) B13846717
theorem B1776107 : Blo 1401520 1776107 := bstep (se 1 (by rfl) ⟨1332080, by rfl⟩ : syracuseStep 1776107 = 2664161) B2664161
theorem B8534845 : Blo 1401520 8534845 := bstep (se 3 (by rfl) ⟨1600283, by rfl⟩ : syracuseStep 8534845 = 3200567) B3200567
theorem B2104427 : Blo 1401520 2104427 := bstep (se 1 (by rfl) ⟨1578320, by rfl⟩ : syracuseStep 2104427 = 3156641) B3156641
theorem B64740545 : Blo 1401520 64740545 := bstep (se 2 (by rfl) ⟨24277704, by rfl⟩ : syracuseStep 64740545 = 48555409) B48555409
theorem B30326399 : Blo 1401520 30326399 := bstep (se 1 (by rfl) ⟨22744799, by rfl⟩ : syracuseStep 30326399 = 45489599) B45489599
theorem B19201769 : Blo 1401520 19201769 := bstep (se 2 (by rfl) ⟨7200663, by rfl⟩ : syracuseStep 19201769 = 14401327) B14401327
theorem B2105255 : Blo 1401520 2105255 := bstep (se 1 (by rfl) ⟨1578941, by rfl⟩ : syracuseStep 2105255 = 3157883) B3157883
theorem B40984535 : Blo 1401520 40984535 := bstep (se 1 (by rfl) ⟨30738401, by rfl⟩ : syracuseStep 40984535 = 61476803) B61476803
theorem B2367785 : Blo 1401520 2367785 := bstep (se 2 (by rfl) ⟨887919, by rfl⟩ : syracuseStep 2367785 = 1775839) B1775839
theorem B4735529 : Blo 1401520 4735529 := bstep (se 2 (by rfl) ⟨1775823, by rfl⟩ : syracuseStep 4735529 = 3551647) B3551647
theorem B10109605 : Blo 1401520 10109605 := bstep (se 4 (by rfl) ⟨947775, by rfl⟩ : syracuseStep 10109605 = 1895551) B1895551
theorem B1401595 : Blo 1401520 1401595 := bstep (se 1 (by rfl) ⟨1051196, by rfl⟩ : syracuseStep 1401595 = 2102393) B2102393
theorem B17294249 : Blo 1401520 17294249 := bstep (se 2 (by rfl) ⟨6485343, by rfl⟩ : syracuseStep 17294249 = 12970687) B12970687
theorem B2663455 : Blo 1401520 2663455 := bstep (se 1 (by rfl) ⟨1997591, by rfl⟩ : syracuseStep 2663455 = 3995183) B3995183
theorem B11379793 : Blo 1401520 11379793 := bstep (se 2 (by rfl) ⟨4267422, by rfl⟩ : syracuseStep 11379793 = 8534845) B8534845
theorem B1402011 : Blo 1401520 1402011 := bstep (se 1 (by rfl) ⟨1051508, by rfl⟩ : syracuseStep 1402011 = 2103017) B2103017
theorem B4736285 : Blo 1401520 4736285 := bstep (se 3 (by rfl) ⟨888053, by rfl⟩ : syracuseStep 4736285 = 1776107) B1776107
theorem B1402183 : Blo 1401520 1402183 := bstep (se 1 (by rfl) ⟨1051637, by rfl⟩ : syracuseStep 1402183 = 2103275) B2103275
theorem B1402303 : Blo 1401520 1402303 := bstep (se 1 (by rfl) ⟨1051727, by rfl⟩ : syracuseStep 1402303 = 2103455) B2103455
theorem B1402951 : Blo 1401520 1402951 := bstep (se 1 (by rfl) ⟨1052213, by rfl⟩ : syracuseStep 1402951 = 2104427) B2104427
theorem B5326985 : Blo 1401520 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B1403503 : Blo 1401520 1403503 := bstep (se 1 (by rfl) ⟨1052627, by rfl⟩ : syracuseStep 1403503 = 2105255) B2105255
theorem B27323023 : Blo 1401520 27323023 := bstep (se 1 (by rfl) ⟨20492267, by rfl⟩ : syracuseStep 27323023 = 40984535) B40984535
theorem B3549977 : Blo 1401520 3549977 := bstep (se 2 (by rfl) ⟨1331241, by rfl⟩ : syracuseStep 3549977 = 2662483) B2662483
theorem B26962793 : Blo 1401520 26962793 := bstep (se 2 (by rfl) ⟨10111047, by rfl⟩ : syracuseStep 26962793 = 20222095) B20222095
theorem B3156857 : Blo 1401520 3156857 := bstep (se 2 (by rfl) ⟨1183821, by rfl⟩ : syracuseStep 3156857 = 2367643) B2367643
theorem B19459183 : Blo 1401520 19459183 := bstep (se 1 (by rfl) ⟨14594387, by rfl⟩ : syracuseStep 19459183 = 29188775) B29188775
theorem B43160363 : Blo 1401520 43160363 := bstep (se 1 (by rfl) ⟨32370272, by rfl⟩ : syracuseStep 43160363 = 64740545) B64740545
theorem B12801179 : Blo 1401520 12801179 := bstep (se 1 (by rfl) ⟨9600884, by rfl⟩ : syracuseStep 12801179 = 19201769) B19201769
theorem B45520217 : Blo 1401520 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B4494695 : Blo 1401520 4494695 := bstep (se 1 (by rfl) ⟨3371021, by rfl⟩ : syracuseStep 4494695 = 6742043) B6742043
theorem B41538973 : Blo 1401520 41538973 := bstep (se 3 (by rfl) ⟨7788557, by rfl⟩ : syracuseStep 41538973 = 15577115) B15577115
theorem B20781467 : Blo 1401520 20781467 := bstep (se 1 (by rfl) ⟨15586100, by rfl⟩ : syracuseStep 20781467 = 31172201) B31172201
theorem B5126923 : Blo 1401520 5126923 := bstep (se 1 (by rfl) ⟨3845192, by rfl⟩ : syracuseStep 5126923 = 7690385) B7690385
theorem B49232771 : Blo 1401520 49232771 := bstep (se 1 (by rfl) ⟨36924578, by rfl⟩ : syracuseStep 49232771 = 73849157) B73849157
theorem B64773053 : Blo 1401520 64773053 := bstep (se 3 (by rfl) ⟨12144947, by rfl⟩ : syracuseStep 64773053 = 24289895) B24289895
theorem B2104415 : Blo 1401520 2104415 := bstep (se 1 (by rfl) ⟨1578311, by rfl⟩ : syracuseStep 2104415 = 3156623) B3156623
theorem B2104631 : Blo 1401520 2104631 := bstep (se 1 (by rfl) ⟨1578473, by rfl⟩ : syracuseStep 2104631 = 3156947) B3156947
theorem B3153455 : Blo 1401520 3153455 := bstep (se 1 (by rfl) ⟨2365091, by rfl⟩ : syracuseStep 3153455 = 4730183) B4730183
theorem B20217599 : Blo 1401520 20217599 := bstep (se 1 (by rfl) ⟨15163199, by rfl⟩ : syracuseStep 20217599 = 30326399) B30326399
theorem B36430697 : Blo 1401520 36430697 := bstep (se 2 (by rfl) ⟨13661511, by rfl⟩ : syracuseStep 36430697 = 27323023) B27323023
theorem B11985853 : Blo 1401520 11985853 := bstep (se 3 (by rfl) ⟨2247347, by rfl⟩ : syracuseStep 11985853 = 4494695) B4494695
theorem B15173057 : Blo 1401520 15173057 := bstep (se 2 (by rfl) ⟨5689896, by rfl⟩ : syracuseStep 15173057 = 11379793) B11379793
theorem B25945577 : Blo 1401520 25945577 := bstep (se 2 (by rfl) ⟨9729591, by rfl⟩ : syracuseStep 25945577 = 19459183) B19459183
theorem B13854311 : Blo 1401520 13854311 := bstep (se 1 (by rfl) ⟨10390733, by rfl⟩ : syracuseStep 13854311 = 20781467) B20781467
theorem B17975195 : Blo 1401520 17975195 := bstep (se 1 (by rfl) ⟨13481396, by rfl⟩ : syracuseStep 17975195 = 26962793) B26962793
theorem B43182035 : Blo 1401520 43182035 := bstep (se 1 (by rfl) ⟨32386526, by rfl⟩ : syracuseStep 43182035 = 64773053) B64773053
theorem B1402943 : Blo 1401520 1402943 := bstep (se 1 (by rfl) ⟨1052207, by rfl⟩ : syracuseStep 1402943 = 2104415) B2104415
theorem B1403087 : Blo 1401520 1403087 := bstep (se 1 (by rfl) ⟨1052315, by rfl⟩ : syracuseStep 1403087 = 2104631) B2104631
theorem B13478399 : Blo 1401520 13478399 := bstep (se 1 (by rfl) ⟨10108799, by rfl⟩ : syracuseStep 13478399 = 20217599) B20217599
theorem B3157019 : Blo 1401520 3157019 := bstep (se 1 (by rfl) ⟨2367764, by rfl⟩ : syracuseStep 3157019 = 4735529) B4735529
theorem B28773575 : Blo 1401520 28773575 := bstep (se 1 (by rfl) ⟨21580181, by rfl⟩ : syracuseStep 28773575 = 43160363) B43160363
theorem B3157523 : Blo 1401520 3157523 := bstep (se 1 (by rfl) ⟨2368142, by rfl⟩ : syracuseStep 3157523 = 4736285) B4736285
theorem B13479473 : Blo 1401520 13479473 := bstep (se 2 (by rfl) ⟨5054802, by rfl⟩ : syracuseStep 13479473 = 10109605) B10109605
theorem B30346811 : Blo 1401520 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B6835897 : Blo 1401520 6835897 := bstep (se 2 (by rfl) ⟨2563461, by rfl⟩ : syracuseStep 6835897 = 5126923) B5126923
theorem B3551273 : Blo 1401520 3551273 := bstep (se 2 (by rfl) ⟨1331727, by rfl⟩ : syracuseStep 3551273 = 2663455) B2663455
theorem B3551323 : Blo 1401520 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B32821847 : Blo 1401520 32821847 := bstep (se 1 (by rfl) ⟨24616385, by rfl⟩ : syracuseStep 32821847 = 49232771) B49232771
theorem B2102303 : Blo 1401520 2102303 := bstep (se 1 (by rfl) ⟨1576727, by rfl⟩ : syracuseStep 2102303 = 3153455) B3153455
theorem B46117997 : Blo 1401520 46117997 := bstep (se 3 (by rfl) ⟨8647124, by rfl⟩ : syracuseStep 46117997 = 17294249) B17294249
theorem B1578523 : Blo 1401520 1578523 := bstep (se 1 (by rfl) ⟨1183892, by rfl⟩ : syracuseStep 1578523 = 2367785) B2367785
theorem B8534119 : Blo 1401520 8534119 := bstep (se 1 (by rfl) ⟨6400589, by rfl⟩ : syracuseStep 8534119 = 12801179) B12801179
theorem B2366651 : Blo 1401520 2366651 := bstep (se 1 (by rfl) ⟨1774988, by rfl⟩ : syracuseStep 2366651 = 3549977) B3549977
theorem B55385297 : Blo 1401520 55385297 := bstep (se 2 (by rfl) ⟨20769486, by rfl⟩ : syracuseStep 55385297 = 41538973) B41538973
theorem B2104571 : Blo 1401520 2104571 := bstep (se 1 (by rfl) ⟨1578428, by rfl⟩ : syracuseStep 2104571 = 3156857) B3156857
theorem B2367515 : Blo 1401520 2367515 := bstep (se 1 (by rfl) ⟨1775636, by rfl⟩ : syracuseStep 2367515 = 3551273) B3551273
theorem B4735097 : Blo 1401520 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B11378825 : Blo 1401520 11378825 := bstep (se 2 (by rfl) ⟨4267059, by rfl⟩ : syracuseStep 11378825 = 8534119) B8534119
theorem B21881231 : Blo 1401520 21881231 := bstep (se 1 (by rfl) ⟨16410923, by rfl⟩ : syracuseStep 21881231 = 32821847) B32821847
theorem B1401535 : Blo 1401520 1401535 := bstep (se 1 (by rfl) ⟨1051151, by rfl⟩ : syracuseStep 1401535 = 2102303) B2102303
theorem B30745331 : Blo 1401520 30745331 := bstep (se 1 (by rfl) ⟨23058998, by rfl⟩ : syracuseStep 30745331 = 46117997) B46117997
theorem B28788023 : Blo 1401520 28788023 := bstep (se 1 (by rfl) ⟨21591017, by rfl⟩ : syracuseStep 28788023 = 43182035) B43182035
theorem B36923531 : Blo 1401520 36923531 := bstep (se 1 (by rfl) ⟨27692648, by rfl⟩ : syracuseStep 36923531 = 55385297) B55385297
theorem B1403047 : Blo 1401520 1403047 := bstep (se 1 (by rfl) ⟨1052285, by rfl⟩ : syracuseStep 1403047 = 2104571) B2104571
theorem B276752821 : Blo 1401520 276752821 := bstep (se 5 (by rfl) ⟨12972788, by rfl⟩ : syracuseStep 276752821 = 25945577) B25945577
theorem B36458117 : Blo 1401520 36458117 := bstep (se 4 (by rfl) ⟨3417948, by rfl⟩ : syracuseStep 36458117 = 6835897) B6835897
theorem B9236207 : Blo 1401520 9236207 := bstep (se 1 (by rfl) ⟨6927155, by rfl⟩ : syracuseStep 9236207 = 13854311) B13854311
theorem B1577767 : Blo 1401520 1577767 := bstep (se 1 (by rfl) ⟨1183325, by rfl⟩ : syracuseStep 1577767 = 2366651) B2366651
theorem B19182383 : Blo 1401520 19182383 := bstep (se 1 (by rfl) ⟨14386787, by rfl⟩ : syracuseStep 19182383 = 28773575) B28773575
theorem B20231207 : Blo 1401520 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B24287131 : Blo 1401520 24287131 := bstep (se 1 (by rfl) ⟨18215348, by rfl⟩ : syracuseStep 24287131 = 36430697) B36430697
theorem B10115371 : Blo 1401520 10115371 := bstep (se 1 (by rfl) ⟨7586528, by rfl⟩ : syracuseStep 10115371 = 15173057) B15173057
theorem B15981137 : Blo 1401520 15981137 := bstep (se 2 (by rfl) ⟨5992926, by rfl⟩ : syracuseStep 15981137 = 11985853) B11985853
theorem B11983463 : Blo 1401520 11983463 := bstep (se 1 (by rfl) ⟨8987597, by rfl⟩ : syracuseStep 11983463 = 17975195) B17975195
theorem B8985599 : Blo 1401520 8985599 := bstep (se 1 (by rfl) ⟨6739199, by rfl⟩ : syracuseStep 8985599 = 13478399) B13478399
theorem B2104679 : Blo 1401520 2104679 := bstep (se 1 (by rfl) ⟨1578509, by rfl⟩ : syracuseStep 2104679 = 3157019) B3157019
theorem B2104697 : Blo 1401520 2104697 := bstep (se 2 (by rfl) ⟨789261, by rfl⟩ : syracuseStep 2104697 = 1578523) B1578523
theorem B2105015 : Blo 1401520 2105015 := bstep (se 1 (by rfl) ⟨1578761, by rfl⟩ : syracuseStep 2105015 = 3157523) B3157523
theorem B8986315 : Blo 1401520 8986315 := bstep (se 1 (by rfl) ⟨6739736, by rfl⟩ : syracuseStep 8986315 = 13479473) B13479473
theorem B7585883 : Blo 1401520 7585883 := bstep (se 1 (by rfl) ⟨5689412, by rfl⟩ : syracuseStep 7585883 = 11378825) B11378825
theorem B20496887 : Blo 1401520 20496887 := bstep (se 1 (by rfl) ⟨15372665, by rfl⟩ : syracuseStep 20496887 = 30745331) B30745331
theorem B12788255 : Blo 1401520 12788255 := bstep (se 1 (by rfl) ⟨9591191, by rfl⟩ : syracuseStep 12788255 = 19182383) B19182383
theorem B7988975 : Blo 1401520 7988975 := bstep (se 1 (by rfl) ⟨5991731, by rfl⟩ : syracuseStep 7988975 = 11983463) B11983463
theorem B5990399 : Blo 1401520 5990399 := bstep (se 1 (by rfl) ⟨4492799, by rfl⟩ : syracuseStep 5990399 = 8985599) B8985599
theorem B1403119 : Blo 1401520 1403119 := bstep (se 1 (by rfl) ⟨1052339, by rfl⟩ : syracuseStep 1403119 = 2104679) B2104679
theorem B1403131 : Blo 1401520 1403131 := bstep (se 1 (by rfl) ⟨1052348, by rfl⟩ : syracuseStep 1403131 = 2104697) B2104697
theorem B1403343 : Blo 1401520 1403343 := bstep (se 1 (by rfl) ⟨1052507, by rfl⟩ : syracuseStep 1403343 = 2105015) B2105015
theorem B3156731 : Blo 1401520 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B98462749 : Blo 1401520 98462749 := bstep (se 3 (by rfl) ⟨18461765, by rfl⟩ : syracuseStep 98462749 = 36923531) B36923531
theorem B13487161 : Blo 1401520 13487161 := bstep (se 2 (by rfl) ⟨5057685, by rfl⟩ : syracuseStep 13487161 = 10115371) B10115371
theorem B369003761 : Blo 1401520 369003761 := bstep (se 2 (by rfl) ⟨138376410, by rfl⟩ : syracuseStep 369003761 = 276752821) B276752821
theorem B13487471 : Blo 1401520 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B10654091 : Blo 1401520 10654091 := bstep (se 1 (by rfl) ⟨7990568, by rfl⟩ : syracuseStep 10654091 = 15981137) B15981137
theorem B11981753 : Blo 1401520 11981753 := bstep (se 2 (by rfl) ⟨4493157, by rfl⟩ : syracuseStep 11981753 = 8986315) B8986315
theorem B6157471 : Blo 1401520 6157471 := bstep (se 1 (by rfl) ⟨4618103, by rfl⟩ : syracuseStep 6157471 = 9236207) B9236207
theorem B1578343 : Blo 1401520 1578343 := bstep (se 1 (by rfl) ⟨1183757, by rfl⟩ : syracuseStep 1578343 = 2367515) B2367515
theorem B14587487 : Blo 1401520 14587487 := bstep (se 1 (by rfl) ⟨10940615, by rfl⟩ : syracuseStep 14587487 = 21881231) B21881231
theorem B19192015 : Blo 1401520 19192015 := bstep (se 1 (by rfl) ⟨14394011, by rfl⟩ : syracuseStep 19192015 = 28788023) B28788023
theorem B2103689 : Blo 1401520 2103689 := bstep (se 2 (by rfl) ⟨788883, by rfl⟩ : syracuseStep 2103689 = 1577767) B1577767
theorem B24305411 : Blo 1401520 24305411 := bstep (se 1 (by rfl) ⟨18229058, by rfl⟩ : syracuseStep 24305411 = 36458117) B36458117
theorem B32382841 : Blo 1401520 32382841 := bstep (se 2 (by rfl) ⟨12143565, by rfl⟩ : syracuseStep 32382841 = 24287131) B24287131
theorem B7102727 : Blo 1401520 7102727 := bstep (se 1 (by rfl) ⟨5327045, by rfl⟩ : syracuseStep 7102727 = 10654091) B10654091
theorem B13664591 : Blo 1401520 13664591 := bstep (se 1 (by rfl) ⟨10248443, by rfl⟩ : syracuseStep 13664591 = 20496887) B20496887
theorem B7987835 : Blo 1401520 7987835 := bstep (se 1 (by rfl) ⟨5990876, by rfl⟩ : syracuseStep 7987835 = 11981753) B11981753
theorem B9724991 : Blo 1401520 9724991 := bstep (se 1 (by rfl) ⟨7293743, by rfl⟩ : syracuseStep 9724991 = 14587487) B14587487
theorem B5325983 : Blo 1401520 5325983 := bstep (se 1 (by rfl) ⟨3994487, by rfl⟩ : syracuseStep 5325983 = 7988975) B7988975
theorem B17982881 : Blo 1401520 17982881 := bstep (se 2 (by rfl) ⟨6743580, by rfl⟩ : syracuseStep 17982881 = 13487161) B13487161
theorem B8209961 : Blo 1401520 8209961 := bstep (se 2 (by rfl) ⟨3078735, by rfl⟩ : syracuseStep 8209961 = 6157471) B6157471
theorem B1402459 : Blo 1401520 1402459 := bstep (se 1 (by rfl) ⟨1051844, by rfl⟩ : syracuseStep 1402459 = 2103689) B2103689
theorem B5057255 : Blo 1401520 5057255 := bstep (se 1 (by rfl) ⟨3792941, by rfl⟩ : syracuseStep 5057255 = 7585883) B7585883
theorem B3993599 : Blo 1401520 3993599 := bstep (se 1 (by rfl) ⟨2995199, by rfl⟩ : syracuseStep 3993599 = 5990399) B5990399
theorem B246002507 : Blo 1401520 246002507 := bstep (se 1 (by rfl) ⟨184501880, by rfl⟩ : syracuseStep 246002507 = 369003761) B369003761
theorem B8991647 : Blo 1401520 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B43177121 : Blo 1401520 43177121 := bstep (se 2 (by rfl) ⟨16191420, by rfl⟩ : syracuseStep 43177121 = 32382841) B32382841
theorem B25589353 : Blo 1401520 25589353 := bstep (se 2 (by rfl) ⟨9596007, by rfl⟩ : syracuseStep 25589353 = 19192015) B19192015
theorem B8525503 : Blo 1401520 8525503 := bstep (se 1 (by rfl) ⟨6394127, by rfl⟩ : syracuseStep 8525503 = 12788255) B12788255
theorem B131283665 : Blo 1401520 131283665 := bstep (se 2 (by rfl) ⟨49231374, by rfl⟩ : syracuseStep 131283665 = 98462749) B98462749
theorem B2104457 : Blo 1401520 2104457 := bstep (se 2 (by rfl) ⟨789171, by rfl⟩ : syracuseStep 2104457 = 1578343) B1578343
theorem B2104487 : Blo 1401520 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B16203607 : Blo 1401520 16203607 := bstep (se 1 (by rfl) ⟨12152705, by rfl⟩ : syracuseStep 16203607 = 24305411) B24305411
theorem B4735151 : Blo 1401520 4735151 := bstep (se 1 (by rfl) ⟨3551363, by rfl⟩ : syracuseStep 4735151 = 7102727) B7102727
theorem B9109727 : Blo 1401520 9109727 := bstep (se 1 (by rfl) ⟨6832295, by rfl⟩ : syracuseStep 9109727 = 13664591) B13664591
theorem B5325223 : Blo 1401520 5325223 := bstep (se 1 (by rfl) ⟨3993917, by rfl⟩ : syracuseStep 5325223 = 7987835) B7987835
theorem B5473307 : Blo 1401520 5473307 := bstep (se 1 (by rfl) ⟨4104980, by rfl⟩ : syracuseStep 5473307 = 8209961) B8209961
theorem B86419237 : Blo 1401520 86419237 := bstep (se 4 (by rfl) ⟨8101803, by rfl⟩ : syracuseStep 86419237 = 16203607) B16203607
theorem B13486013 : Blo 1401520 13486013 := bstep (se 3 (by rfl) ⟨2528627, by rfl⟩ : syracuseStep 13486013 = 5057255) B5057255
theorem B1402971 : Blo 1401520 1402971 := bstep (se 1 (by rfl) ⟨1052228, by rfl⟩ : syracuseStep 1402971 = 2104457) B2104457
theorem B1402991 : Blo 1401520 1402991 := bstep (se 1 (by rfl) ⟨1052243, by rfl⟩ : syracuseStep 1402991 = 2104487) B2104487
theorem B3550655 : Blo 1401520 3550655 := bstep (se 1 (by rfl) ⟨2662991, by rfl⟩ : syracuseStep 3550655 = 5325983) B5325983
theorem B11988587 : Blo 1401520 11988587 := bstep (se 1 (by rfl) ⟨8991440, by rfl⟩ : syracuseStep 11988587 = 17982881) B17982881
theorem B45469349 : Blo 1401520 45469349 := bstep (se 4 (by rfl) ⟨4262751, by rfl⟩ : syracuseStep 45469349 = 8525503) B8525503
theorem B164001671 : Blo 1401520 164001671 := bstep (se 1 (by rfl) ⟨123001253, by rfl⟩ : syracuseStep 164001671 = 246002507) B246002507
theorem B5994431 : Blo 1401520 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B103733237 : Blo 1401520 103733237 := bstep (se 5 (by rfl) ⟨4862495, by rfl⟩ : syracuseStep 103733237 = 9724991) B9724991
theorem B28784747 : Blo 1401520 28784747 := bstep (se 1 (by rfl) ⟨21588560, by rfl⟩ : syracuseStep 28784747 = 43177121) B43177121
theorem B87522443 : Blo 1401520 87522443 := bstep (se 1 (by rfl) ⟨65641832, by rfl⟩ : syracuseStep 87522443 = 131283665) B131283665
theorem B34119137 : Blo 1401520 34119137 := bstep (se 2 (by rfl) ⟨12794676, by rfl⟩ : syracuseStep 34119137 = 25589353) B25589353
theorem B2662399 : Blo 1401520 2662399 := bstep (se 1 (by rfl) ⟨1996799, by rfl⟩ : syracuseStep 2662399 = 3993599) B3993599
theorem B76759325 : Blo 1401520 76759325 := bstep (se 3 (by rfl) ⟨14392373, by rfl⟩ : syracuseStep 76759325 = 28784747) B28784747
theorem B30312899 : Blo 1401520 30312899 := bstep (se 1 (by rfl) ⟨22734674, by rfl⟩ : syracuseStep 30312899 = 45469349) B45469349
theorem B276621965 : Blo 1401520 276621965 := bstep (se 3 (by rfl) ⟨51866618, by rfl⟩ : syracuseStep 276621965 = 103733237) B103733237
theorem B3549865 : Blo 1401520 3549865 := bstep (se 2 (by rfl) ⟨1331199, by rfl⟩ : syracuseStep 3549865 = 2662399) B2662399
theorem B3156767 : Blo 1401520 3156767 := bstep (se 1 (by rfl) ⟨2367575, by rfl⟩ : syracuseStep 3156767 = 4735151) B4735151
theorem B6073151 : Blo 1401520 6073151 := bstep (se 1 (by rfl) ⟨4554863, by rfl⟩ : syracuseStep 6073151 = 9109727) B9109727
theorem B3648871 : Blo 1401520 3648871 := bstep (se 1 (by rfl) ⟨2736653, by rfl⟩ : syracuseStep 3648871 = 5473307) B5473307
theorem B109334447 : Blo 1401520 109334447 := bstep (se 1 (by rfl) ⟨82000835, by rfl⟩ : syracuseStep 109334447 = 164001671) B164001671
theorem B8990675 : Blo 1401520 8990675 := bstep (se 1 (by rfl) ⟨6743006, by rfl⟩ : syracuseStep 8990675 = 13486013) B13486013
theorem B58348295 : Blo 1401520 58348295 := bstep (se 1 (by rfl) ⟨43761221, by rfl⟩ : syracuseStep 58348295 = 87522443) B87522443
theorem B22746091 : Blo 1401520 22746091 := bstep (se 1 (by rfl) ⟨17059568, by rfl⟩ : syracuseStep 22746091 = 34119137) B34119137
theorem B115225649 : Blo 1401520 115225649 := bstep (se 2 (by rfl) ⟨43209618, by rfl⟩ : syracuseStep 115225649 = 86419237) B86419237
theorem B7992391 : Blo 1401520 7992391 := bstep (se 1 (by rfl) ⟨5994293, by rfl⟩ : syracuseStep 7992391 = 11988587) B11988587
theorem B7100297 : Blo 1401520 7100297 := bstep (se 2 (by rfl) ⟨2662611, by rfl⟩ : syracuseStep 7100297 = 5325223) B5325223
theorem B3996287 : Blo 1401520 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B2367103 : Blo 1401520 2367103 := bstep (se 1 (by rfl) ⟨1775327, by rfl⟩ : syracuseStep 2367103 = 3550655) B3550655
theorem B76817099 : Blo 1401520 76817099 := bstep (se 1 (by rfl) ⟨57612824, by rfl⟩ : syracuseStep 76817099 = 115225649) B115225649
theorem B30328121 : Blo 1401520 30328121 := bstep (se 2 (by rfl) ⟨11373045, by rfl⟩ : syracuseStep 30328121 = 22746091) B22746091
theorem B2664191 : Blo 1401520 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B3156137 : Blo 1401520 3156137 := bstep (se 2 (by rfl) ⟨1183551, by rfl⟩ : syracuseStep 3156137 = 2367103) B2367103
theorem B38898863 : Blo 1401520 38898863 := bstep (se 1 (by rfl) ⟨29174147, by rfl⟩ : syracuseStep 38898863 = 58348295) B58348295
theorem B184414643 : Blo 1401520 184414643 := bstep (se 1 (by rfl) ⟨138310982, by rfl⟩ : syracuseStep 184414643 = 276621965) B276621965
theorem B19460645 : Blo 1401520 19460645 := bstep (se 4 (by rfl) ⟨1824435, by rfl⟩ : syracuseStep 19460645 = 3648871) B3648871
theorem B72889631 : Blo 1401520 72889631 := bstep (se 1 (by rfl) ⟨54667223, by rfl⟩ : syracuseStep 72889631 = 109334447) B109334447
theorem B5993783 : Blo 1401520 5993783 := bstep (se 1 (by rfl) ⟨4495337, by rfl⟩ : syracuseStep 5993783 = 8990675) B8990675
theorem B51172883 : Blo 1401520 51172883 := bstep (se 1 (by rfl) ⟨38379662, by rfl⟩ : syracuseStep 51172883 = 76759325) B76759325
theorem B4733153 : Blo 1401520 4733153 := bstep (se 2 (by rfl) ⟨1774932, by rfl⟩ : syracuseStep 4733153 = 3549865) B3549865
theorem B4733531 : Blo 1401520 4733531 := bstep (se 1 (by rfl) ⟨3550148, by rfl⟩ : syracuseStep 4733531 = 7100297) B7100297
theorem B10656521 : Blo 1401520 10656521 := bstep (se 2 (by rfl) ⟨3996195, by rfl⟩ : syracuseStep 10656521 = 7992391) B7992391
theorem B20208599 : Blo 1401520 20208599 := bstep (se 1 (by rfl) ⟨15156449, by rfl⟩ : syracuseStep 20208599 = 30312899) B30312899
theorem B2104511 : Blo 1401520 2104511 := bstep (se 1 (by rfl) ⟨1578383, by rfl⟩ : syracuseStep 2104511 = 3156767) B3156767
theorem B16195069 : Blo 1401520 16195069 := bstep (se 3 (by rfl) ⟨3036575, by rfl⟩ : syracuseStep 16195069 = 6073151) B6073151
theorem B20218747 : Blo 1401520 20218747 := bstep (se 1 (by rfl) ⟨15164060, by rfl⟩ : syracuseStep 20218747 = 30328121) B30328121
theorem B3155435 : Blo 1401520 3155435 := bstep (se 1 (by rfl) ⟨2366576, by rfl⟩ : syracuseStep 3155435 = 4733153) B4733153
theorem B3155687 : Blo 1401520 3155687 := bstep (se 1 (by rfl) ⟨2366765, by rfl⟩ : syracuseStep 3155687 = 4733531) B4733531
theorem B7104347 : Blo 1401520 7104347 := bstep (se 1 (by rfl) ⟨5328260, by rfl⟩ : syracuseStep 7104347 = 10656521) B10656521
theorem B7104509 : Blo 1401520 7104509 := bstep (se 3 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 7104509 = 2664191) B2664191
theorem B1403007 : Blo 1401520 1403007 := bstep (se 1 (by rfl) ⟨1052255, by rfl⟩ : syracuseStep 1403007 = 2104511) B2104511
theorem B34115255 : Blo 1401520 34115255 := bstep (se 1 (by rfl) ⟨25586441, by rfl⟩ : syracuseStep 34115255 = 51172883) B51172883
theorem B204845597 : Blo 1401520 204845597 := bstep (se 3 (by rfl) ⟨38408549, by rfl⟩ : syracuseStep 204845597 = 76817099) B76817099
theorem B13472399 : Blo 1401520 13472399 := bstep (se 1 (by rfl) ⟨10104299, by rfl⟩ : syracuseStep 13472399 = 20208599) B20208599
theorem B25932575 : Blo 1401520 25932575 := bstep (se 1 (by rfl) ⟨19449431, by rfl⟩ : syracuseStep 25932575 = 38898863) B38898863
theorem B122943095 : Blo 1401520 122943095 := bstep (se 1 (by rfl) ⟨92207321, by rfl⟩ : syracuseStep 122943095 = 184414643) B184414643
theorem B12973763 : Blo 1401520 12973763 := bstep (se 1 (by rfl) ⟨9730322, by rfl⟩ : syracuseStep 12973763 = 19460645) B19460645
theorem B48593087 : Blo 1401520 48593087 := bstep (se 1 (by rfl) ⟨36444815, by rfl⟩ : syracuseStep 48593087 = 72889631) B72889631
theorem B3995855 : Blo 1401520 3995855 := bstep (se 1 (by rfl) ⟨2996891, by rfl⟩ : syracuseStep 3995855 = 5993783) B5993783
theorem B2104091 : Blo 1401520 2104091 := bstep (se 1 (by rfl) ⟨1578068, by rfl⟩ : syracuseStep 2104091 = 3156137) B3156137
theorem B21593425 : Blo 1401520 21593425 := bstep (se 2 (by rfl) ⟨8097534, by rfl⟩ : syracuseStep 21593425 = 16195069) B16195069
theorem B81962063 : Blo 1401520 81962063 := bstep (se 1 (by rfl) ⟨61471547, by rfl⟩ : syracuseStep 81962063 = 122943095) B122943095
theorem B4736231 : Blo 1401520 4736231 := bstep (se 1 (by rfl) ⟨3552173, by rfl⟩ : syracuseStep 4736231 = 7104347) B7104347
theorem B4736339 : Blo 1401520 4736339 := bstep (se 1 (by rfl) ⟨3552254, by rfl⟩ : syracuseStep 4736339 = 7104509) B7104509
theorem B2663903 : Blo 1401520 2663903 := bstep (se 1 (by rfl) ⟨1997927, by rfl⟩ : syracuseStep 2663903 = 3995855) B3995855
theorem B1402727 : Blo 1401520 1402727 := bstep (se 1 (by rfl) ⟨1052045, by rfl⟩ : syracuseStep 1402727 = 2104091) B2104091
theorem B22743503 : Blo 1401520 22743503 := bstep (se 1 (by rfl) ⟨17057627, by rfl⟩ : syracuseStep 22743503 = 34115255) B34115255
theorem B136563731 : Blo 1401520 136563731 := bstep (se 1 (by rfl) ⟨102422798, by rfl⟩ : syracuseStep 136563731 = 204845597) B204845597
theorem B8981599 : Blo 1401520 8981599 := bstep (se 1 (by rfl) ⟨6736199, by rfl⟩ : syracuseStep 8981599 = 13472399) B13472399
theorem B32395391 : Blo 1401520 32395391 := bstep (se 1 (by rfl) ⟨24296543, by rfl⟩ : syracuseStep 32395391 = 48593087) B48593087
theorem B28791233 : Blo 1401520 28791233 := bstep (se 2 (by rfl) ⟨10796712, by rfl⟩ : syracuseStep 28791233 = 21593425) B21593425
theorem B69153533 : Blo 1401520 69153533 := bstep (se 3 (by rfl) ⟨12966287, by rfl⟩ : syracuseStep 69153533 = 25932575) B25932575
theorem B2103623 : Blo 1401520 2103623 := bstep (se 1 (by rfl) ⟨1577717, by rfl⟩ : syracuseStep 2103623 = 3155435) B3155435
theorem B8649175 : Blo 1401520 8649175 := bstep (se 1 (by rfl) ⟨6486881, by rfl⟩ : syracuseStep 8649175 = 12973763) B12973763
theorem B2103791 : Blo 1401520 2103791 := bstep (se 1 (by rfl) ⟨1577843, by rfl⟩ : syracuseStep 2103791 = 3155687) B3155687
theorem B26958329 : Blo 1401520 26958329 := bstep (se 2 (by rfl) ⟨10109373, by rfl⟩ : syracuseStep 26958329 = 20218747) B20218747
theorem B19194155 : Blo 1401520 19194155 := bstep (se 1 (by rfl) ⟨14395616, by rfl⟩ : syracuseStep 19194155 = 28791233) B28791233
theorem B54641375 : Blo 1401520 54641375 := bstep (se 1 (by rfl) ⟨40981031, by rfl⟩ : syracuseStep 54641375 = 81962063) B81962063
theorem B1402415 : Blo 1401520 1402415 := bstep (se 1 (by rfl) ⟨1051811, by rfl⟩ : syracuseStep 1402415 = 2103623) B2103623
theorem B1402527 : Blo 1401520 1402527 := bstep (se 1 (by rfl) ⟨1051895, by rfl⟩ : syracuseStep 1402527 = 2103791) B2103791
theorem B21596927 : Blo 1401520 21596927 := bstep (se 1 (by rfl) ⟨16197695, by rfl⟩ : syracuseStep 21596927 = 32395391) B32395391
theorem B3157487 : Blo 1401520 3157487 := bstep (se 1 (by rfl) ⟨2368115, by rfl⟩ : syracuseStep 3157487 = 4736231) B4736231
theorem B3157559 : Blo 1401520 3157559 := bstep (se 1 (by rfl) ⟨2368169, by rfl⟩ : syracuseStep 3157559 = 4736339) B4736339
theorem B91042487 : Blo 1401520 91042487 := bstep (se 1 (by rfl) ⟨68281865, by rfl⟩ : syracuseStep 91042487 = 136563731) B136563731
theorem B46102355 : Blo 1401520 46102355 := bstep (se 1 (by rfl) ⟨34576766, by rfl⟩ : syracuseStep 46102355 = 69153533) B69153533
theorem B11532233 : Blo 1401520 11532233 := bstep (se 2 (by rfl) ⟨4324587, by rfl⟩ : syracuseStep 11532233 = 8649175) B8649175
theorem B1775935 : Blo 1401520 1775935 := bstep (se 1 (by rfl) ⟨1331951, by rfl⟩ : syracuseStep 1775935 = 2663903) B2663903
theorem B11975465 : Blo 1401520 11975465 := bstep (se 2 (by rfl) ⟨4490799, by rfl⟩ : syracuseStep 11975465 = 8981599) B8981599
theorem B15162335 : Blo 1401520 15162335 := bstep (se 1 (by rfl) ⟨11371751, by rfl⟩ : syracuseStep 15162335 = 22743503) B22743503
theorem B17972219 : Blo 1401520 17972219 := bstep (se 1 (by rfl) ⟨13479164, by rfl⟩ : syracuseStep 17972219 = 26958329) B26958329
theorem B12796103 : Blo 1401520 12796103 := bstep (se 1 (by rfl) ⟨9597077, by rfl⟩ : syracuseStep 12796103 = 19194155) B19194155
theorem B2367913 : Blo 1401520 2367913 := bstep (se 2 (by rfl) ⟨887967, by rfl⟩ : syracuseStep 2367913 = 1775935) B1775935
theorem B60694991 : Blo 1401520 60694991 := bstep (se 1 (by rfl) ⟨45521243, by rfl⟩ : syracuseStep 60694991 = 91042487) B91042487
theorem B57591805 : Blo 1401520 57591805 := bstep (se 3 (by rfl) ⟨10798463, by rfl⟩ : syracuseStep 57591805 = 21596927) B21596927
theorem B7688155 : Blo 1401520 7688155 := bstep (se 1 (by rfl) ⟨5766116, by rfl⟩ : syracuseStep 7688155 = 11532233) B11532233
theorem B7983643 : Blo 1401520 7983643 := bstep (se 1 (by rfl) ⟨5987732, by rfl⟩ : syracuseStep 7983643 = 11975465) B11975465
theorem B11981479 : Blo 1401520 11981479 := bstep (se 1 (by rfl) ⟨8986109, by rfl⟩ : syracuseStep 11981479 = 17972219) B17972219
theorem B36427583 : Blo 1401520 36427583 := bstep (se 1 (by rfl) ⟨27320687, by rfl⟩ : syracuseStep 36427583 = 54641375) B54641375
theorem B30734903 : Blo 1401520 30734903 := bstep (se 1 (by rfl) ⟨23051177, by rfl⟩ : syracuseStep 30734903 = 46102355) B46102355
theorem B10108223 : Blo 1401520 10108223 := bstep (se 1 (by rfl) ⟨7581167, by rfl⟩ : syracuseStep 10108223 = 15162335) B15162335
theorem B2104991 : Blo 1401520 2104991 := bstep (se 1 (by rfl) ⟨1578743, by rfl⟩ : syracuseStep 2104991 = 3157487) B3157487
theorem B2105039 : Blo 1401520 2105039 := bstep (se 1 (by rfl) ⟨1578779, by rfl⟩ : syracuseStep 2105039 = 3157559) B3157559
theorem B15975305 : Blo 1401520 15975305 := bstep (se 2 (by rfl) ⟨5990739, by rfl⟩ : syracuseStep 15975305 = 11981479) B11981479
theorem B20489935 : Blo 1401520 20489935 := bstep (se 1 (by rfl) ⟨15367451, by rfl⟩ : syracuseStep 20489935 = 30734903) B30734903
theorem B1403327 : Blo 1401520 1403327 := bstep (se 1 (by rfl) ⟨1052495, by rfl⟩ : syracuseStep 1403327 = 2104991) B2104991
theorem B1403359 : Blo 1401520 1403359 := bstep (se 1 (by rfl) ⟨1052519, by rfl⟩ : syracuseStep 1403359 = 2105039) B2105039
theorem B10250873 : Blo 1401520 10250873 := bstep (se 2 (by rfl) ⟨3844077, by rfl⟩ : syracuseStep 10250873 = 7688155) B7688155
theorem B40463327 : Blo 1401520 40463327 := bstep (se 1 (by rfl) ⟨30347495, by rfl⟩ : syracuseStep 40463327 = 60694991) B60694991
theorem B34122941 : Blo 1401520 34122941 := bstep (se 3 (by rfl) ⟨6398051, by rfl⟩ : syracuseStep 34122941 = 12796103) B12796103
theorem B3157217 : Blo 1401520 3157217 := bstep (se 2 (by rfl) ⟨1183956, by rfl⟩ : syracuseStep 3157217 = 2367913) B2367913
theorem B10644857 : Blo 1401520 10644857 := bstep (se 2 (by rfl) ⟨3991821, by rfl⟩ : syracuseStep 10644857 = 7983643) B7983643
theorem B6738815 : Blo 1401520 6738815 := bstep (se 1 (by rfl) ⟨5054111, by rfl⟩ : syracuseStep 6738815 = 10108223) B10108223
theorem B76789073 : Blo 1401520 76789073 := bstep (se 2 (by rfl) ⟨28795902, by rfl⟩ : syracuseStep 76789073 = 57591805) B57591805
theorem B97140221 : Blo 1401520 97140221 := bstep (se 3 (by rfl) ⟨18213791, by rfl⟩ : syracuseStep 97140221 = 36427583) B36427583
theorem B10650203 : Blo 1401520 10650203 := bstep (se 1 (by rfl) ⟨7987652, by rfl⟩ : syracuseStep 10650203 = 15975305) B15975305
theorem B6833915 : Blo 1401520 6833915 := bstep (se 1 (by rfl) ⟨5125436, by rfl⟩ : syracuseStep 6833915 = 10250873) B10250873
theorem B7096571 : Blo 1401520 7096571 := bstep (se 1 (by rfl) ⟨5322428, by rfl⟩ : syracuseStep 7096571 = 10644857) B10644857
theorem B64760147 : Blo 1401520 64760147 := bstep (se 1 (by rfl) ⟨48570110, by rfl⟩ : syracuseStep 64760147 = 97140221) B97140221
theorem B4492543 : Blo 1401520 4492543 := bstep (se 1 (by rfl) ⟨3369407, by rfl⟩ : syracuseStep 4492543 = 6738815) B6738815
theorem B204770861 : Blo 1401520 204770861 := bstep (se 3 (by rfl) ⟨38394536, by rfl⟩ : syracuseStep 204770861 = 76789073) B76789073
theorem B26975551 : Blo 1401520 26975551 := bstep (se 1 (by rfl) ⟨20231663, by rfl⟩ : syracuseStep 26975551 = 40463327) B40463327
theorem B22748627 : Blo 1401520 22748627 := bstep (se 1 (by rfl) ⟨17061470, by rfl⟩ : syracuseStep 22748627 = 34122941) B34122941
theorem B2104811 : Blo 1401520 2104811 := bstep (se 1 (by rfl) ⟨1578608, by rfl⟩ : syracuseStep 2104811 = 3157217) B3157217
theorem B27319913 : Blo 1401520 27319913 := bstep (se 2 (by rfl) ⟨10244967, by rfl⟩ : syracuseStep 27319913 = 20489935) B20489935
theorem B4555943 : Blo 1401520 4555943 := bstep (se 1 (by rfl) ⟨3416957, by rfl⟩ : syracuseStep 4555943 = 6833915) B6833915
theorem B60663005 : Blo 1401520 60663005 := bstep (se 3 (by rfl) ⟨11374313, by rfl⟩ : syracuseStep 60663005 = 22748627) B22748627
theorem B43173431 : Blo 1401520 43173431 := bstep (se 1 (by rfl) ⟨32380073, by rfl⟩ : syracuseStep 43173431 = 64760147) B64760147
theorem B5990057 : Blo 1401520 5990057 := bstep (se 2 (by rfl) ⟨2246271, by rfl⟩ : syracuseStep 5990057 = 4492543) B4492543
theorem B1403207 : Blo 1401520 1403207 := bstep (se 1 (by rfl) ⟨1052405, by rfl⟩ : syracuseStep 1403207 = 2104811) B2104811
theorem B136513907 : Blo 1401520 136513907 := bstep (se 1 (by rfl) ⟨102385430, by rfl⟩ : syracuseStep 136513907 = 204770861) B204770861
theorem B18213275 : Blo 1401520 18213275 := bstep (se 1 (by rfl) ⟨13659956, by rfl⟩ : syracuseStep 18213275 = 27319913) B27319913
theorem B4731047 : Blo 1401520 4731047 := bstep (se 1 (by rfl) ⟨3548285, by rfl⟩ : syracuseStep 4731047 = 7096571) B7096571
theorem B35967401 : Blo 1401520 35967401 := bstep (se 2 (by rfl) ⟨13487775, by rfl⟩ : syracuseStep 35967401 = 26975551) B26975551
theorem B7100135 : Blo 1401520 7100135 := bstep (se 1 (by rfl) ⟨5325101, by rfl⟩ : syracuseStep 7100135 = 10650203) B10650203
theorem B3154031 : Blo 1401520 3154031 := bstep (se 1 (by rfl) ⟨2365523, by rfl⟩ : syracuseStep 3154031 = 4731047) B4731047
theorem B23978267 : Blo 1401520 23978267 := bstep (se 1 (by rfl) ⟨17983700, by rfl⟩ : syracuseStep 23978267 = 35967401) B35967401
theorem B12142183 : Blo 1401520 12142183 := bstep (se 1 (by rfl) ⟨9106637, by rfl⟩ : syracuseStep 12142183 = 18213275) B18213275
theorem B28782287 : Blo 1401520 28782287 := bstep (se 1 (by rfl) ⟨21586715, by rfl⟩ : syracuseStep 28782287 = 43173431) B43173431
theorem B3993371 : Blo 1401520 3993371 := bstep (se 1 (by rfl) ⟨2995028, by rfl⟩ : syracuseStep 3993371 = 5990057) B5990057
theorem B91009271 : Blo 1401520 91009271 := bstep (se 1 (by rfl) ⟨68256953, by rfl⟩ : syracuseStep 91009271 = 136513907) B136513907
theorem B3037295 : Blo 1401520 3037295 := bstep (se 1 (by rfl) ⟨2277971, by rfl⟩ : syracuseStep 3037295 = 4555943) B4555943
theorem B40442003 : Blo 1401520 40442003 := bstep (se 1 (by rfl) ⟨30331502, by rfl⟩ : syracuseStep 40442003 = 60663005) B60663005
theorem B4733423 : Blo 1401520 4733423 := bstep (se 1 (by rfl) ⟨3550067, by rfl⟩ : syracuseStep 4733423 = 7100135) B7100135
theorem B2024863 : Blo 1401520 2024863 := bstep (se 1 (by rfl) ⟨1518647, by rfl⟩ : syracuseStep 2024863 = 3037295) B3037295
theorem B26961335 : Blo 1401520 26961335 := bstep (se 1 (by rfl) ⟨20221001, by rfl⟩ : syracuseStep 26961335 = 40442003) B40442003
theorem B3155615 : Blo 1401520 3155615 := bstep (se 1 (by rfl) ⟨2366711, by rfl⟩ : syracuseStep 3155615 = 4733423) B4733423
theorem B16189577 : Blo 1401520 16189577 := bstep (se 2 (by rfl) ⟨6071091, by rfl⟩ : syracuseStep 16189577 = 12142183) B12142183
theorem B19188191 : Blo 1401520 19188191 := bstep (se 1 (by rfl) ⟨14391143, by rfl⟩ : syracuseStep 19188191 = 28782287) B28782287
theorem B60672847 : Blo 1401520 60672847 := bstep (se 1 (by rfl) ⟨45504635, by rfl⟩ : syracuseStep 60672847 = 91009271) B91009271
theorem B15985511 : Blo 1401520 15985511 := bstep (se 1 (by rfl) ⟨11989133, by rfl⟩ : syracuseStep 15985511 = 23978267) B23978267
theorem B2102687 : Blo 1401520 2102687 := bstep (se 1 (by rfl) ⟨1577015, by rfl⟩ : syracuseStep 2102687 = 3154031) B3154031
theorem B2662247 : Blo 1401520 2662247 := bstep (se 1 (by rfl) ⟨1996685, by rfl⟩ : syracuseStep 2662247 = 3993371) B3993371
theorem B43197077 : Blo 1401520 43197077 := bstep (se 6 (by rfl) ⟨1012431, by rfl⟩ : syracuseStep 43197077 = 2024863) B2024863
theorem B1401791 : Blo 1401520 1401791 := bstep (se 1 (by rfl) ⟨1051343, by rfl⟩ : syracuseStep 1401791 = 2102687) B2102687
theorem B17974223 : Blo 1401520 17974223 := bstep (se 1 (by rfl) ⟨13480667, by rfl⟩ : syracuseStep 17974223 = 26961335) B26961335
theorem B80897129 : Blo 1401520 80897129 := bstep (se 2 (by rfl) ⟨30336423, by rfl⟩ : syracuseStep 80897129 = 60672847) B60672847
theorem B10793051 : Blo 1401520 10793051 := bstep (se 1 (by rfl) ⟨8094788, by rfl⟩ : syracuseStep 10793051 = 16189577) B16189577
theorem B12792127 : Blo 1401520 12792127 := bstep (se 1 (by rfl) ⟨9594095, by rfl⟩ : syracuseStep 12792127 = 19188191) B19188191
theorem B7099325 : Blo 1401520 7099325 := bstep (se 3 (by rfl) ⟨1331123, by rfl⟩ : syracuseStep 7099325 = 2662247) B2662247
theorem B2103743 : Blo 1401520 2103743 := bstep (se 1 (by rfl) ⟨1577807, by rfl⟩ : syracuseStep 2103743 = 3155615) B3155615
theorem B10657007 : Blo 1401520 10657007 := bstep (se 1 (by rfl) ⟨7992755, by rfl⟩ : syracuseStep 10657007 = 15985511) B15985511
theorem B17056169 : Blo 1401520 17056169 := bstep (se 2 (by rfl) ⟨6396063, by rfl⟩ : syracuseStep 17056169 = 12792127) B12792127
theorem B1402495 : Blo 1401520 1402495 := bstep (se 1 (by rfl) ⟨1051871, by rfl⟩ : syracuseStep 1402495 = 2103743) B2103743
theorem B7104671 : Blo 1401520 7104671 := bstep (se 1 (by rfl) ⟨5328503, by rfl⟩ : syracuseStep 7104671 = 10657007) B10657007
theorem B7195367 : Blo 1401520 7195367 := bstep (se 1 (by rfl) ⟨5396525, by rfl⟩ : syracuseStep 7195367 = 10793051) B10793051
theorem B28798051 : Blo 1401520 28798051 := bstep (se 1 (by rfl) ⟨21598538, by rfl⟩ : syracuseStep 28798051 = 43197077) B43197077
theorem B53931419 : Blo 1401520 53931419 := bstep (se 1 (by rfl) ⟨40448564, by rfl⟩ : syracuseStep 53931419 = 80897129) B80897129
theorem B4732883 : Blo 1401520 4732883 := bstep (se 1 (by rfl) ⟨3549662, by rfl⟩ : syracuseStep 4732883 = 7099325) B7099325
theorem B11982815 : Blo 1401520 11982815 := bstep (se 1 (by rfl) ⟨8987111, by rfl⟩ : syracuseStep 11982815 = 17974223) B17974223
theorem B11370779 : Blo 1401520 11370779 := bstep (se 1 (by rfl) ⟨8528084, by rfl⟩ : syracuseStep 11370779 = 17056169) B17056169
theorem B3155255 : Blo 1401520 3155255 := bstep (se 1 (by rfl) ⟨2366441, by rfl⟩ : syracuseStep 3155255 = 4732883) B4732883
theorem B7988543 : Blo 1401520 7988543 := bstep (se 1 (by rfl) ⟨5991407, by rfl⟩ : syracuseStep 7988543 = 11982815) B11982815
theorem B4736447 : Blo 1401520 4736447 := bstep (se 1 (by rfl) ⟨3552335, by rfl⟩ : syracuseStep 4736447 = 7104671) B7104671
theorem B38397401 : Blo 1401520 38397401 := bstep (se 2 (by rfl) ⟨14399025, by rfl⟩ : syracuseStep 38397401 = 28798051) B28798051
theorem B4796911 : Blo 1401520 4796911 := bstep (se 1 (by rfl) ⟨3597683, by rfl⟩ : syracuseStep 4796911 = 7195367) B7195367
theorem B35954279 : Blo 1401520 35954279 := bstep (se 1 (by rfl) ⟨26965709, by rfl⟩ : syracuseStep 35954279 = 53931419) B53931419
theorem B5325695 : Blo 1401520 5325695 := bstep (se 1 (by rfl) ⟨3994271, by rfl⟩ : syracuseStep 5325695 = 7988543) B7988543
theorem B7580519 : Blo 1401520 7580519 := bstep (se 1 (by rfl) ⟨5685389, by rfl⟩ : syracuseStep 7580519 = 11370779) B11370779
theorem B3157631 : Blo 1401520 3157631 := bstep (se 1 (by rfl) ⟨2368223, by rfl⟩ : syracuseStep 3157631 = 4736447) B4736447
theorem B2103503 : Blo 1401520 2103503 := bstep (se 1 (by rfl) ⟨1577627, by rfl⟩ : syracuseStep 2103503 = 3155255) B3155255
theorem B25598267 : Blo 1401520 25598267 := bstep (se 1 (by rfl) ⟨19198700, by rfl⟩ : syracuseStep 25598267 = 38397401) B38397401
theorem B23969519 : Blo 1401520 23969519 := bstep (se 1 (by rfl) ⟨17977139, by rfl⟩ : syracuseStep 23969519 = 35954279) B35954279
theorem B25583525 : Blo 1401520 25583525 := bstep (se 4 (by rfl) ⟨2398455, by rfl⟩ : syracuseStep 25583525 = 4796911) B4796911
theorem B1402335 : Blo 1401520 1402335 := bstep (se 1 (by rfl) ⟨1051751, by rfl⟩ : syracuseStep 1402335 = 2103503) B2103503
theorem B17065511 : Blo 1401520 17065511 := bstep (se 1 (by rfl) ⟨12799133, by rfl⟩ : syracuseStep 17065511 = 25598267) B25598267
theorem B3550463 : Blo 1401520 3550463 := bstep (se 1 (by rfl) ⟨2662847, by rfl⟩ : syracuseStep 3550463 = 5325695) B5325695
theorem B15979679 : Blo 1401520 15979679 := bstep (se 1 (by rfl) ⟨11984759, by rfl⟩ : syracuseStep 15979679 = 23969519) B23969519
theorem B5053679 : Blo 1401520 5053679 := bstep (se 1 (by rfl) ⟨3790259, by rfl⟩ : syracuseStep 5053679 = 7580519) B7580519
theorem B2105087 : Blo 1401520 2105087 := bstep (se 1 (by rfl) ⟨1578815, by rfl⟩ : syracuseStep 2105087 = 3157631) B3157631
theorem B17055683 : Blo 1401520 17055683 := bstep (se 1 (by rfl) ⟨12791762, by rfl⟩ : syracuseStep 17055683 = 25583525) B25583525
theorem B3369119 : Blo 1401520 3369119 := bstep (se 1 (by rfl) ⟨2526839, by rfl⟩ : syracuseStep 3369119 = 5053679) B5053679
theorem B1403391 : Blo 1401520 1403391 := bstep (se 1 (by rfl) ⟨1052543, by rfl⟩ : syracuseStep 1403391 = 2105087) B2105087
theorem B10653119 : Blo 1401520 10653119 := bstep (se 1 (by rfl) ⟨7989839, by rfl⟩ : syracuseStep 10653119 = 15979679) B15979679
theorem B11377007 : Blo 1401520 11377007 := bstep (se 1 (by rfl) ⟨8532755, by rfl⟩ : syracuseStep 11377007 = 17065511) B17065511
theorem B2366975 : Blo 1401520 2366975 := bstep (se 1 (by rfl) ⟨1775231, by rfl⟩ : syracuseStep 2366975 = 3550463) B3550463
theorem B11370455 : Blo 1401520 11370455 := bstep (se 1 (by rfl) ⟨8527841, by rfl⟩ : syracuseStep 11370455 = 17055683) B17055683
theorem B7580303 : Blo 1401520 7580303 := bstep (se 1 (by rfl) ⟨5685227, by rfl⟩ : syracuseStep 7580303 = 11370455) B11370455
theorem B1577983 : Blo 1401520 1577983 := bstep (se 1 (by rfl) ⟨1183487, by rfl⟩ : syracuseStep 1577983 = 2366975) B2366975
theorem B8984317 : Blo 1401520 8984317 := bstep (se 3 (by rfl) ⟨1684559, by rfl⟩ : syracuseStep 8984317 = 3369119) B3369119
theorem B7584671 : Blo 1401520 7584671 := bstep (se 1 (by rfl) ⟨5688503, by rfl⟩ : syracuseStep 7584671 = 11377007) B11377007
theorem B7102079 : Blo 1401520 7102079 := bstep (se 1 (by rfl) ⟨5326559, by rfl⟩ : syracuseStep 7102079 = 10653119) B10653119
theorem B5056447 : Blo 1401520 5056447 := bstep (se 1 (by rfl) ⟨3792335, by rfl⟩ : syracuseStep 5056447 = 7584671) B7584671
theorem B11979089 : Blo 1401520 11979089 := bstep (se 2 (by rfl) ⟨4492158, by rfl⟩ : syracuseStep 11979089 = 8984317) B8984317
theorem B2103977 : Blo 1401520 2103977 := bstep (se 2 (by rfl) ⟨788991, by rfl⟩ : syracuseStep 2103977 = 1577983) B1577983
theorem B5053535 : Blo 1401520 5053535 := bstep (se 1 (by rfl) ⟨3790151, by rfl⟩ : syracuseStep 5053535 = 7580303) B7580303
theorem B4734719 : Blo 1401520 4734719 := bstep (se 1 (by rfl) ⟨3551039, by rfl⟩ : syracuseStep 4734719 = 7102079) B7102079
theorem B1402651 : Blo 1401520 1402651 := bstep (se 1 (by rfl) ⟨1051988, by rfl⟩ : syracuseStep 1402651 = 2103977) B2103977
theorem B3369023 : Blo 1401520 3369023 := bstep (se 1 (by rfl) ⟨2526767, by rfl⟩ : syracuseStep 3369023 = 5053535) B5053535
theorem B3156479 : Blo 1401520 3156479 := bstep (se 1 (by rfl) ⟨2367359, by rfl⟩ : syracuseStep 3156479 = 4734719) B4734719
theorem B7986059 : Blo 1401520 7986059 := bstep (se 1 (by rfl) ⟨5989544, by rfl⟩ : syracuseStep 7986059 = 11979089) B11979089
theorem B6741929 : Blo 1401520 6741929 := bstep (se 2 (by rfl) ⟨2528223, by rfl⟩ : syracuseStep 6741929 = 5056447) B5056447
theorem B2246015 : Blo 1401520 2246015 := bstep (se 1 (by rfl) ⟨1684511, by rfl⟩ : syracuseStep 2246015 = 3369023) B3369023
theorem B4494619 : Blo 1401520 4494619 := bstep (se 1 (by rfl) ⟨3370964, by rfl⟩ : syracuseStep 4494619 = 6741929) B6741929
theorem B2104319 : Blo 1401520 2104319 := bstep (se 1 (by rfl) ⟨1578239, by rfl⟩ : syracuseStep 2104319 = 3156479) B3156479
theorem B5324039 : Blo 1401520 5324039 := bstep (se 1 (by rfl) ⟨3993029, by rfl⟩ : syracuseStep 5324039 = 7986059) B7986059
theorem B5989373 : Blo 1401520 5989373 := bstep (se 3 (by rfl) ⟨1123007, by rfl⟩ : syracuseStep 5989373 = 2246015) B2246015
theorem B1402879 : Blo 1401520 1402879 := bstep (se 1 (by rfl) ⟨1052159, by rfl⟩ : syracuseStep 1402879 = 2104319) B2104319
theorem B3549359 : Blo 1401520 3549359 := bstep (se 1 (by rfl) ⟨2662019, by rfl⟩ : syracuseStep 3549359 = 5324039) B5324039
theorem B5992825 : Blo 1401520 5992825 := bstep (se 2 (by rfl) ⟨2247309, by rfl⟩ : syracuseStep 5992825 = 4494619) B4494619
theorem B7990433 : Blo 1401520 7990433 := bstep (se 2 (by rfl) ⟨2996412, by rfl⟩ : syracuseStep 7990433 = 5992825) B5992825
theorem B3992915 : Blo 1401520 3992915 := bstep (se 1 (by rfl) ⟨2994686, by rfl⟩ : syracuseStep 3992915 = 5989373) B5989373
theorem B2366239 : Blo 1401520 2366239 := bstep (se 1 (by rfl) ⟨1774679, by rfl⟩ : syracuseStep 2366239 = 3549359) B3549359
theorem B3154985 : Blo 1401520 3154985 := bstep (se 2 (by rfl) ⟨1183119, by rfl⟩ : syracuseStep 3154985 = 2366239) B2366239
theorem B5326955 : Blo 1401520 5326955 := bstep (se 1 (by rfl) ⟨3995216, by rfl⟩ : syracuseStep 5326955 = 7990433) B7990433
theorem B10647773 : Blo 1401520 10647773 := bstep (se 3 (by rfl) ⟨1996457, by rfl⟩ : syracuseStep 10647773 = 3992915) B3992915
theorem B3551303 : Blo 1401520 3551303 := bstep (se 1 (by rfl) ⟨2663477, by rfl⟩ : syracuseStep 3551303 = 5326955) B5326955
theorem B7098515 : Blo 1401520 7098515 := bstep (se 1 (by rfl) ⟨5323886, by rfl⟩ : syracuseStep 7098515 = 10647773) B10647773
theorem B2103323 : Blo 1401520 2103323 := bstep (se 1 (by rfl) ⟨1577492, by rfl⟩ : syracuseStep 2103323 = 3154985) B3154985
theorem B2367535 : Blo 1401520 2367535 := bstep (se 1 (by rfl) ⟨1775651, by rfl⟩ : syracuseStep 2367535 = 3551303) B3551303
theorem B1402215 : Blo 1401520 1402215 := bstep (se 1 (by rfl) ⟨1051661, by rfl⟩ : syracuseStep 1402215 = 2103323) B2103323
theorem B4732343 : Blo 1401520 4732343 := bstep (se 1 (by rfl) ⟨3549257, by rfl⟩ : syracuseStep 4732343 = 7098515) B7098515
theorem B3154895 : Blo 1401520 3154895 := bstep (se 1 (by rfl) ⟨2366171, by rfl⟩ : syracuseStep 3154895 = 4732343) B4732343
theorem B3156713 : Blo 1401520 3156713 := bstep (se 2 (by rfl) ⟨1183767, by rfl⟩ : syracuseStep 3156713 = 2367535) B2367535
theorem B2103263 : Blo 1401520 2103263 := bstep (se 1 (by rfl) ⟨1577447, by rfl⟩ : syracuseStep 2103263 = 3154895) B3154895
theorem B2104475 : Blo 1401520 2104475 := bstep (se 1 (by rfl) ⟨1578356, by rfl⟩ : syracuseStep 2104475 = 3156713) B3156713
theorem B1402175 : Blo 1401520 1402175 := bstep (se 1 (by rfl) ⟨1051631, by rfl⟩ : syracuseStep 1402175 = 2103263) B2103263
theorem B1402983 : Blo 1401520 1402983 := bstep (se 1 (by rfl) ⟨1052237, by rfl⟩ : syracuseStep 1402983 = 2104475) B2104475

theorem C0 (j : ℕ) (h1 : 350380 ≤ j) (h2 : j ≤ 350879) : Blo 1401520 (4 * j + 3) := by
  interval_cases j
  · exact B1401523
  · exact B1401527
  · exact B1401531
  · exact B1401535
  · exact B1401539
  · exact B1401543
  · exact B1401547
  · exact B1401551
  · exact B1401555
  · exact B1401559
  · exact B1401563
  · exact B1401567
  · exact B1401571
  · exact B1401575
  · exact B1401579
  · exact B1401583
  · exact B1401587
  · exact B1401591
  · exact B1401595
  · exact B1401599
  · exact B1401603
  · exact B1401607
  · exact B1401611
  · exact B1401615
  · exact B1401619
  · exact B1401623
  · exact B1401627
  · exact B1401631
  · exact B1401635
  · exact B1401639
  · exact B1401643
  · exact B1401647
  · exact B1401651
  · exact B1401655
  · exact B1401659
  · exact B1401663
  · exact B1401667
  · exact B1401671
  · exact B1401675
  · exact B1401679
  · exact B1401683
  · exact B1401687
  · exact B1401691
  · exact B1401695
  · exact B1401699
  · exact B1401703
  · exact B1401707
  · exact B1401711
  · exact B1401715
  · exact B1401719
  · exact B1401723
  · exact B1401727
  · exact B1401731
  · exact B1401735
  · exact B1401739
  · exact B1401743
  · exact B1401747
  · exact B1401751
  · exact B1401755
  · exact B1401759
  · exact B1401763
  · exact B1401767
  · exact B1401771
  · exact B1401775
  · exact B1401779
  · exact B1401783
  · exact B1401787
  · exact B1401791
  · exact B1401795
  · exact B1401799
  · exact B1401803
  · exact B1401807
  · exact B1401811
  · exact B1401815
  · exact B1401819
  · exact B1401823
  · exact B1401827
  · exact B1401831
  · exact B1401835
  · exact B1401839
  · exact B1401843
  · exact B1401847
  · exact B1401851
  · exact B1401855
  · exact B1401859
  · exact B1401863
  · exact B1401867
  · exact B1401871
  · exact B1401875
  · exact B1401879
  · exact B1401883
  · exact B1401887
  · exact B1401891
  · exact B1401895
  · exact B1401899
  · exact B1401903
  · exact B1401907
  · exact B1401911
  · exact B1401915
  · exact B1401919
  · exact B1401923
  · exact B1401927
  · exact B1401931
  · exact B1401935
  · exact B1401939
  · exact B1401943
  · exact B1401947
  · exact B1401951
  · exact B1401955
  · exact B1401959
  · exact B1401963
  · exact B1401967
  · exact B1401971
  · exact B1401975
  · exact B1401979
  · exact B1401983
  · exact B1401987
  · exact B1401991
  · exact B1401995
  · exact B1401999
  · exact B1402003
  · exact B1402007
  · exact B1402011
  · exact B1402015
  · exact B1402019
  · exact B1402023
  · exact B1402027
  · exact B1402031
  · exact B1402035
  · exact B1402039
  · exact B1402043
  · exact B1402047
  · exact B1402051
  · exact B1402055
  · exact B1402059
  · exact B1402063
  · exact B1402067
  · exact B1402071
  · exact B1402075
  · exact B1402079
  · exact B1402083
  · exact B1402087
  · exact B1402091
  · exact B1402095
  · exact B1402099
  · exact B1402103
  · exact B1402107
  · exact B1402111
  · exact B1402115
  · exact B1402119
  · exact B1402123
  · exact B1402127
  · exact B1402131
  · exact B1402135
  · exact B1402139
  · exact B1402143
  · exact B1402147
  · exact B1402151
  · exact B1402155
  · exact B1402159
  · exact B1402163
  · exact B1402167
  · exact B1402171
  · exact B1402175
  · exact B1402179
  · exact B1402183
  · exact B1402187
  · exact B1402191
  · exact B1402195
  · exact B1402199
  · exact B1402203
  · exact B1402207
  · exact B1402211
  · exact B1402215
  · exact B1402219
  · exact B1402223
  · exact B1402227
  · exact B1402231
  · exact B1402235
  · exact B1402239
  · exact B1402243
  · exact B1402247
  · exact B1402251
  · exact B1402255
  · exact B1402259
  · exact B1402263
  · exact B1402267
  · exact B1402271
  · exact B1402275
  · exact B1402279
  · exact B1402283
  · exact B1402287
  · exact B1402291
  · exact B1402295
  · exact B1402299
  · exact B1402303
  · exact B1402307
  · exact B1402311
  · exact B1402315
  · exact B1402319
  · exact B1402323
  · exact B1402327
  · exact B1402331
  · exact B1402335
  · exact B1402339
  · exact B1402343
  · exact B1402347
  · exact B1402351
  · exact B1402355
  · exact B1402359
  · exact B1402363
  · exact B1402367
  · exact B1402371
  · exact B1402375
  · exact B1402379
  · exact B1402383
  · exact B1402387
  · exact B1402391
  · exact B1402395
  · exact B1402399
  · exact B1402403
  · exact B1402407
  · exact B1402411
  · exact B1402415
  · exact B1402419
  · exact B1402423
  · exact B1402427
  · exact B1402431
  · exact B1402435
  · exact B1402439
  · exact B1402443
  · exact B1402447
  · exact B1402451
  · exact B1402455
  · exact B1402459
  · exact B1402463
  · exact B1402467
  · exact B1402471
  · exact B1402475
  · exact B1402479
  · exact B1402483
  · exact B1402487
  · exact B1402491
  · exact B1402495
  · exact B1402499
  · exact B1402503
  · exact B1402507
  · exact B1402511
  · exact B1402515
  · exact B1402519
  · exact B1402523
  · exact B1402527
  · exact B1402531
  · exact B1402535
  · exact B1402539
  · exact B1402543
  · exact B1402547
  · exact B1402551
  · exact B1402555
  · exact B1402559
  · exact B1402563
  · exact B1402567
  · exact B1402571
  · exact B1402575
  · exact B1402579
  · exact B1402583
  · exact B1402587
  · exact B1402591
  · exact B1402595
  · exact B1402599
  · exact B1402603
  · exact B1402607
  · exact B1402611
  · exact B1402615
  · exact B1402619
  · exact B1402623
  · exact B1402627
  · exact B1402631
  · exact B1402635
  · exact B1402639
  · exact B1402643
  · exact B1402647
  · exact B1402651
  · exact B1402655
  · exact B1402659
  · exact B1402663
  · exact B1402667
  · exact B1402671
  · exact B1402675
  · exact B1402679
  · exact B1402683
  · exact B1402687
  · exact B1402691
  · exact B1402695
  · exact B1402699
  · exact B1402703
  · exact B1402707
  · exact B1402711
  · exact B1402715
  · exact B1402719
  · exact B1402723
  · exact B1402727
  · exact B1402731
  · exact B1402735
  · exact B1402739
  · exact B1402743
  · exact B1402747
  · exact B1402751
  · exact B1402755
  · exact B1402759
  · exact B1402763
  · exact B1402767
  · exact B1402771
  · exact B1402775
  · exact B1402779
  · exact B1402783
  · exact B1402787
  · exact B1402791
  · exact B1402795
  · exact B1402799
  · exact B1402803
  · exact B1402807
  · exact B1402811
  · exact B1402815
  · exact B1402819
  · exact B1402823
  · exact B1402827
  · exact B1402831
  · exact B1402835
  · exact B1402839
  · exact B1402843
  · exact B1402847
  · exact B1402851
  · exact B1402855
  · exact B1402859
  · exact B1402863
  · exact B1402867
  · exact B1402871
  · exact B1402875
  · exact B1402879
  · exact B1402883
  · exact B1402887
  · exact B1402891
  · exact B1402895
  · exact B1402899
  · exact B1402903
  · exact B1402907
  · exact B1402911
  · exact B1402915
  · exact B1402919
  · exact B1402923
  · exact B1402927
  · exact B1402931
  · exact B1402935
  · exact B1402939
  · exact B1402943
  · exact B1402947
  · exact B1402951
  · exact B1402955
  · exact B1402959
  · exact B1402963
  · exact B1402967
  · exact B1402971
  · exact B1402975
  · exact B1402979
  · exact B1402983
  · exact B1402987
  · exact B1402991
  · exact B1402995
  · exact B1402999
  · exact B1403003
  · exact B1403007
  · exact B1403011
  · exact B1403015
  · exact B1403019
  · exact B1403023
  · exact B1403027
  · exact B1403031
  · exact B1403035
  · exact B1403039
  · exact B1403043
  · exact B1403047
  · exact B1403051
  · exact B1403055
  · exact B1403059
  · exact B1403063
  · exact B1403067
  · exact B1403071
  · exact B1403075
  · exact B1403079
  · exact B1403083
  · exact B1403087
  · exact B1403091
  · exact B1403095
  · exact B1403099
  · exact B1403103
  · exact B1403107
  · exact B1403111
  · exact B1403115
  · exact B1403119
  · exact B1403123
  · exact B1403127
  · exact B1403131
  · exact B1403135
  · exact B1403139
  · exact B1403143
  · exact B1403147
  · exact B1403151
  · exact B1403155
  · exact B1403159
  · exact B1403163
  · exact B1403167
  · exact B1403171
  · exact B1403175
  · exact B1403179
  · exact B1403183
  · exact B1403187
  · exact B1403191
  · exact B1403195
  · exact B1403199
  · exact B1403203
  · exact B1403207
  · exact B1403211
  · exact B1403215
  · exact B1403219
  · exact B1403223
  · exact B1403227
  · exact B1403231
  · exact B1403235
  · exact B1403239
  · exact B1403243
  · exact B1403247
  · exact B1403251
  · exact B1403255
  · exact B1403259
  · exact B1403263
  · exact B1403267
  · exact B1403271
  · exact B1403275
  · exact B1403279
  · exact B1403283
  · exact B1403287
  · exact B1403291
  · exact B1403295
  · exact B1403299
  · exact B1403303
  · exact B1403307
  · exact B1403311
  · exact B1403315
  · exact B1403319
  · exact B1403323
  · exact B1403327
  · exact B1403331
  · exact B1403335
  · exact B1403339
  · exact B1403343
  · exact B1403347
  · exact B1403351
  · exact B1403355
  · exact B1403359
  · exact B1403363
  · exact B1403367
  · exact B1403371
  · exact B1403375
  · exact B1403379
  · exact B1403383
  · exact B1403387
  · exact B1403391
  · exact B1403395
  · exact B1403399
  · exact B1403403
  · exact B1403407
  · exact B1403411
  · exact B1403415
  · exact B1403419
  · exact B1403423
  · exact B1403427
  · exact B1403431
  · exact B1403435
  · exact B1403439
  · exact B1403443
  · exact B1403447
  · exact B1403451
  · exact B1403455
  · exact B1403459
  · exact B1403463
  · exact B1403467
  · exact B1403471
  · exact B1403475
  · exact B1403479
  · exact B1403483
  · exact B1403487
  · exact B1403491
  · exact B1403495
  · exact B1403499
  · exact B1403503
  · exact B1403507
  · exact B1403511
  · exact B1403515
  · exact B1403519

theorem solution (m : ℕ) (hlo : 1401520 ≤ m) (hhi : m ≤ 1403520) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 350380 ≤ j := by omega
    have hj2 : j ≤ 350879 := by omega
    have hb : Blo 1401520 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
