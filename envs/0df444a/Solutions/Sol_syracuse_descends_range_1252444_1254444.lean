-- Prove2me | solution 1 for syracuse_descends_range_1252444_1254444
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:17.978761+00:00
-- url     : https://prove2.me/submissions/c6a78dd4-5b9b-4661-97c8-67a42154c184

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


theorem B2818061 : Blo 1252444 2818061 := bbase (se 3 (by rfl) ⟨528386, by rfl⟩ : syracuseStep 2818061 = 1056773) (by norm_num)
theorem B1409053 : Blo 1252444 1409053 := bbase (se 3 (by rfl) ⟨264197, by rfl⟩ : syracuseStep 1409053 = 528395) (by norm_num)
theorem B2113573 : Blo 1252444 2113573 := bbase (se 4 (by rfl) ⟨198147, by rfl⟩ : syracuseStep 2113573 = 396295) (by norm_num)
theorem B8036405 : Blo 1252444 8036405 := bbase (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) (by norm_num)
theorem B1409089 : Blo 1252444 1409089 := bbase (se 2 (by rfl) ⟨528408, by rfl⟩ : syracuseStep 1409089 = 1056817) (by norm_num)
theorem B1785925 : Blo 1252444 1785925 := bbase (se 4 (by rfl) ⟨167430, by rfl⟩ : syracuseStep 1785925 = 334861) (by norm_num)
theorem B2818133 : Blo 1252444 2818133 := bbase (se 8 (by rfl) ⟨16512, by rfl⟩ : syracuseStep 2818133 = 33025) (by norm_num)
theorem B68591701 : Blo 1252444 68591701 := bbase (se 8 (by rfl) ⟨401904, by rfl⟩ : syracuseStep 68591701 = 803809) (by norm_num)
theorem B4227173 : Blo 1252444 4227173 := bbase (se 4 (by rfl) ⟨396297, by rfl⟩ : syracuseStep 4227173 = 792595) (by norm_num)
theorem B1409125 : Blo 1252444 1409125 := bbase (se 4 (by rfl) ⟨132105, by rfl⟩ : syracuseStep 1409125 = 264211) (by norm_num)
theorem B2113661 : Blo 1252444 2113661 := bbase (se 3 (by rfl) ⟨396311, by rfl⟩ : syracuseStep 2113661 = 792623) (by norm_num)
theorem B1409161 : Blo 1252444 1409161 := bbase (se 2 (by rfl) ⟨528435, by rfl⟩ : syracuseStep 1409161 = 1056871) (by norm_num)
theorem B3170461 : Blo 1252444 3170461 := bbase (se 3 (by rfl) ⟨594461, by rfl⟩ : syracuseStep 3170461 = 1188923) (by norm_num)
theorem B2818205 : Blo 1252444 2818205 := bbase (se 3 (by rfl) ⟨528413, by rfl⟩ : syracuseStep 2818205 = 1056827) (by norm_num)
theorem B1409197 : Blo 1252444 1409197 := bbase (se 3 (by rfl) ⟨264224, by rfl⟩ : syracuseStep 1409197 = 528449) (by norm_num)
theorem B1786045 : Blo 1252444 1786045 := bbase (se 3 (by rfl) ⟨334883, by rfl⟩ : syracuseStep 1786045 = 669767) (by norm_num)
theorem B5505221 : Blo 1252444 5505221 := bbase (se 4 (by rfl) ⟨516114, by rfl⟩ : syracuseStep 5505221 = 1032229) (by norm_num)
theorem B1409233 : Blo 1252444 1409233 := bbase (se 2 (by rfl) ⟨528462, by rfl⟩ : syracuseStep 1409233 = 1056925) (by norm_num)
theorem B2818277 : Blo 1252444 2818277 := bbase (se 4 (by rfl) ⟨264213, by rfl⟩ : syracuseStep 2818277 = 528427) (by norm_num)
theorem B1409269 : Blo 1252444 1409269 := bbase (se 5 (by rfl) ⟨66059, by rfl⟩ : syracuseStep 1409269 = 132119) (by norm_num)
theorem B2113789 : Blo 1252444 2113789 := bbase (se 3 (by rfl) ⟨396335, by rfl⟩ : syracuseStep 2113789 = 792671) (by norm_num)
theorem B3170573 : Blo 1252444 3170573 := bbase (se 3 (by rfl) ⟨594482, by rfl⟩ : syracuseStep 3170573 = 1188965) (by norm_num)
theorem B1409305 : Blo 1252444 1409305 := bbase (se 2 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 1409305 = 1056979) (by norm_num)
theorem B2818349 : Blo 1252444 2818349 := bbase (se 3 (by rfl) ⟨528440, by rfl⟩ : syracuseStep 2818349 = 1056881) (by norm_num)
theorem B1409341 : Blo 1252444 1409341 := bbase (se 3 (by rfl) ⟨264251, by rfl⟩ : syracuseStep 1409341 = 528503) (by norm_num)
theorem B2113877 : Blo 1252444 2113877 := bbase (se 10 (by rfl) ⟨3096, by rfl⟩ : syracuseStep 2113877 = 6193) (by norm_num)
theorem B6021461 : Blo 1252444 6021461 := bbase (se 10 (by rfl) ⟨8820, by rfl⟩ : syracuseStep 6021461 = 17641) (by norm_num)
theorem B26100053 : Blo 1252444 26100053 := bbase (se 10 (by rfl) ⟨38232, by rfl⟩ : syracuseStep 26100053 = 76465) (by norm_num)
theorem B1409377 : Blo 1252444 1409377 := bbase (se 2 (by rfl) ⟨528516, by rfl⟩ : syracuseStep 1409377 = 1057033) (by norm_num)
theorem B2818421 : Blo 1252444 2818421 := bbase (se 5 (by rfl) ⟨132113, by rfl⟩ : syracuseStep 2818421 = 264227) (by norm_num)
theorem B1409413 : Blo 1252444 1409413 := bbase (se 4 (by rfl) ⟨132132, by rfl⟩ : syracuseStep 1409413 = 264265) (by norm_num)
theorem B2007461 : Blo 1252444 2007461 := bbase (se 4 (by rfl) ⟨188199, by rfl⟩ : syracuseStep 2007461 = 376399) (by norm_num)
theorem B1409449 : Blo 1252444 1409449 := bbase (se 2 (by rfl) ⟨528543, by rfl⟩ : syracuseStep 1409449 = 1057087) (by norm_num)
theorem B2818493 : Blo 1252444 2818493 := bbase (se 3 (by rfl) ⟨528467, by rfl⟩ : syracuseStep 2818493 = 1056935) (by norm_num)
theorem B2539973 : Blo 1252444 2539973 := bbase (se 4 (by rfl) ⟨238122, by rfl⟩ : syracuseStep 2539973 = 476245) (by norm_num)
theorem B4760005 : Blo 1252444 4760005 := bbase (se 4 (by rfl) ⟨446250, by rfl⟩ : syracuseStep 4760005 = 892501) (by norm_num)
theorem B3170765 : Blo 1252444 3170765 := bbase (se 3 (by rfl) ⟨594518, by rfl⟩ : syracuseStep 3170765 = 1189037) (by norm_num)
theorem B1409485 : Blo 1252444 1409485 := bbase (se 3 (by rfl) ⟨264278, by rfl⟩ : syracuseStep 1409485 = 528557) (by norm_num)
theorem B2114005 : Blo 1252444 2114005 := bbase (se 7 (by rfl) ⟨24773, by rfl⟩ : syracuseStep 2114005 = 49547) (by norm_num)
theorem B1409521 : Blo 1252444 1409521 := bbase (se 2 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 1409521 = 1057141) (by norm_num)
theorem B2818565 : Blo 1252444 2818565 := bbase (se 4 (by rfl) ⟨264240, by rfl⟩ : syracuseStep 2818565 = 528481) (by norm_num)
theorem B4227605 : Blo 1252444 4227605 := bbase (se 6 (by rfl) ⟨99084, by rfl⟩ : syracuseStep 4227605 = 198169) (by norm_num)
theorem B1409557 : Blo 1252444 1409557 := bbase (se 6 (by rfl) ⟨33036, by rfl⟩ : syracuseStep 1409557 = 66073) (by norm_num)
theorem B2114093 : Blo 1252444 2114093 := bbase (se 3 (by rfl) ⟨396392, by rfl⟩ : syracuseStep 2114093 = 792785) (by norm_num)
theorem B1409593 : Blo 1252444 1409593 := bbase (se 2 (by rfl) ⟨528597, by rfl⟩ : syracuseStep 1409593 = 1057195) (by norm_num)
theorem B2818637 : Blo 1252444 2818637 := bbase (se 3 (by rfl) ⟨528494, by rfl⟩ : syracuseStep 2818637 = 1056989) (by norm_num)
theorem B1409629 : Blo 1252444 1409629 := bbase (se 3 (by rfl) ⟨264305, by rfl⟩ : syracuseStep 1409629 = 528611) (by norm_num)
theorem B2007661 : Blo 1252444 2007661 := bbase (se 3 (by rfl) ⟨376436, by rfl⟩ : syracuseStep 2007661 = 752873) (by norm_num)
theorem B1409665 : Blo 1252444 1409665 := bbase (se 2 (by rfl) ⟨528624, by rfl⟩ : syracuseStep 1409665 = 1057249) (by norm_num)
theorem B2818709 : Blo 1252444 2818709 := bbase (se 6 (by rfl) ⟨66063, by rfl⟩ : syracuseStep 2818709 = 132127) (by norm_num)
theorem B1409701 : Blo 1252444 1409701 := bbase (se 4 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 1409701 = 264319) (by norm_num)
theorem B2114221 : Blo 1252444 2114221 := bbase (se 3 (by rfl) ⟨396416, by rfl⟩ : syracuseStep 2114221 = 792833) (by norm_num)
theorem B1409737 : Blo 1252444 1409737 := bbase (se 2 (by rfl) ⟨528651, by rfl⟩ : syracuseStep 1409737 = 1057303) (by norm_num)
theorem B2818781 : Blo 1252444 2818781 := bbase (se 3 (by rfl) ⟨528521, by rfl⟩ : syracuseStep 2818781 = 1057043) (by norm_num)
theorem B1409773 : Blo 1252444 1409773 := bbase (se 3 (by rfl) ⟨264332, by rfl⟩ : syracuseStep 1409773 = 528665) (by norm_num)
theorem B4760309 : Blo 1252444 4760309 := bbase (se 5 (by rfl) ⟨223139, by rfl⟩ : syracuseStep 4760309 = 446279) (by norm_num)
theorem B2114309 : Blo 1252444 2114309 := bbase (se 4 (by rfl) ⟨198216, by rfl⟩ : syracuseStep 2114309 = 396433) (by norm_num)
theorem B1409809 : Blo 1252444 1409809 := bbase (se 2 (by rfl) ⟨528678, by rfl⟩ : syracuseStep 1409809 = 1057357) (by norm_num)
theorem B5079829 : Blo 1252444 5079829 := bbase (se 6 (by rfl) ⟨119058, by rfl⟩ : syracuseStep 5079829 = 238117) (by norm_num)
theorem B6349589 : Blo 1252444 6349589 := bbase (se 6 (by rfl) ⟨148818, by rfl⟩ : syracuseStep 6349589 = 297637) (by norm_num)
theorem B3171109 : Blo 1252444 3171109 := bbase (se 4 (by rfl) ⟨297291, by rfl⟩ : syracuseStep 3171109 = 594583) (by norm_num)
theorem B2818853 : Blo 1252444 2818853 := bbase (se 4 (by rfl) ⟨264267, by rfl⟩ : syracuseStep 2818853 = 528535) (by norm_num)
theorem B1409845 : Blo 1252444 1409845 := bbase (se 5 (by rfl) ⟨66086, by rfl⟩ : syracuseStep 1409845 = 132173) (by norm_num)
theorem B1409881 : Blo 1252444 1409881 := bbase (se 2 (by rfl) ⟨528705, by rfl⟩ : syracuseStep 1409881 = 1057411) (by norm_num)
theorem B2818925 : Blo 1252444 2818925 := bbase (se 3 (by rfl) ⟨528548, by rfl⟩ : syracuseStep 2818925 = 1057097) (by norm_num)
theorem B2007917 : Blo 1252444 2007917 := bbase (se 3 (by rfl) ⟨376484, by rfl⟩ : syracuseStep 2007917 = 752969) (by norm_num)
theorem B1409917 : Blo 1252444 1409917 := bbase (se 3 (by rfl) ⟨264359, by rfl⟩ : syracuseStep 1409917 = 528719) (by norm_num)
theorem B2114437 : Blo 1252444 2114437 := bbase (se 4 (by rfl) ⟨198228, by rfl⟩ : syracuseStep 2114437 = 396457) (by norm_num)
theorem B3171221 : Blo 1252444 3171221 := bbase (se 6 (by rfl) ⟨74325, by rfl⟩ : syracuseStep 3171221 = 148651) (by norm_num)
theorem B1409953 : Blo 1252444 1409953 := bbase (se 2 (by rfl) ⟨528732, by rfl⟩ : syracuseStep 1409953 = 1057465) (by norm_num)
theorem B2261933 : Blo 1252444 2261933 := bbase (se 3 (by rfl) ⟨424112, by rfl⟩ : syracuseStep 2261933 = 848225) (by norm_num)
theorem B2818997 : Blo 1252444 2818997 := bbase (se 5 (by rfl) ⟨132140, by rfl⟩ : syracuseStep 2818997 = 264281) (by norm_num)
theorem B2171845 : Blo 1252444 2171845 := bbase (se 4 (by rfl) ⟨203610, by rfl⟩ : syracuseStep 2171845 = 407221) (by norm_num)
theorem B4228037 : Blo 1252444 4228037 := bbase (se 4 (by rfl) ⟨396378, by rfl⟩ : syracuseStep 4228037 = 792757) (by norm_num)
theorem B1409989 : Blo 1252444 1409989 := bbase (se 4 (by rfl) ⟨132186, by rfl⟩ : syracuseStep 1409989 = 264373) (by norm_num)
theorem B2114525 : Blo 1252444 2114525 := bbase (se 3 (by rfl) ⟨396473, by rfl⟩ : syracuseStep 2114525 = 792947) (by norm_num)
theorem B1410025 : Blo 1252444 1410025 := bbase (se 2 (by rfl) ⟨528759, by rfl⟩ : syracuseStep 1410025 = 1057519) (by norm_num)
theorem B1270765 : Blo 1252444 1270765 := bbase (se 3 (by rfl) ⟨238268, by rfl⟩ : syracuseStep 1270765 = 476537) (by norm_num)
theorem B2819069 : Blo 1252444 2819069 := bbase (se 3 (by rfl) ⟨528575, by rfl⟩ : syracuseStep 2819069 = 1057151) (by norm_num)
theorem B1410061 : Blo 1252444 1410061 := bbase (se 3 (by rfl) ⟨264386, by rfl⟩ : syracuseStep 1410061 = 528773) (by norm_num)
theorem B1270801 : Blo 1252444 1270801 := bbase (se 2 (by rfl) ⟨476550, by rfl⟩ : syracuseStep 1270801 = 953101) (by norm_num)
theorem B1410097 : Blo 1252444 1410097 := bbase (se 2 (by rfl) ⟨528786, by rfl⟩ : syracuseStep 1410097 = 1057573) (by norm_num)
theorem B2819141 : Blo 1252444 2819141 := bbase (se 4 (by rfl) ⟨264294, by rfl⟩ : syracuseStep 2819141 = 528589) (by norm_num)
theorem B3171413 : Blo 1252444 3171413 := bbase (se 8 (by rfl) ⟨18582, by rfl⟩ : syracuseStep 3171413 = 37165) (by norm_num)
theorem B1410133 : Blo 1252444 1410133 := bbase (se 8 (by rfl) ⟨8262, by rfl⟩ : syracuseStep 1410133 = 16525) (by norm_num)
theorem B2114653 : Blo 1252444 2114653 := bbase (se 3 (by rfl) ⟨396497, by rfl⟩ : syracuseStep 2114653 = 792995) (by norm_num)
theorem B1410169 : Blo 1252444 1410169 := bbase (se 2 (by rfl) ⟨528813, by rfl⟩ : syracuseStep 1410169 = 1057627) (by norm_num)
theorem B2819213 : Blo 1252444 2819213 := bbase (se 3 (by rfl) ⟨528602, by rfl⟩ : syracuseStep 2819213 = 1057205) (by norm_num)
theorem B1410205 : Blo 1252444 1410205 := bbase (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) (by norm_num)
theorem B3433637 : Blo 1252444 3433637 := bbase (se 4 (by rfl) ⟨321903, by rfl⟩ : syracuseStep 3433637 = 643807) (by norm_num)
theorem B6341813 : Blo 1252444 6341813 := bbase (se 5 (by rfl) ⟨297272, by rfl⟩ : syracuseStep 6341813 = 594545) (by norm_num)
theorem B2114741 : Blo 1252444 2114741 := bbase (se 5 (by rfl) ⟨99128, by rfl⟩ : syracuseStep 2114741 = 198257) (by norm_num)
theorem B1410241 : Blo 1252444 1410241 := bbase (se 2 (by rfl) ⟨528840, by rfl⟩ : syracuseStep 1410241 = 1057681) (by norm_num)
theorem B2819285 : Blo 1252444 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B1410277 : Blo 1252444 1410277 := bbase (se 4 (by rfl) ⟨132213, by rfl⟩ : syracuseStep 1410277 = 264427) (by norm_num)
theorem B1410313 : Blo 1252444 1410313 := bbase (se 2 (by rfl) ⟨528867, by rfl⟩ : syracuseStep 1410313 = 1057735) (by norm_num)
theorem B2819357 : Blo 1252444 2819357 := bbase (se 3 (by rfl) ⟨528629, by rfl⟩ : syracuseStep 2819357 = 1057259) (by norm_num)
theorem B1410349 : Blo 1252444 1410349 := bbase (se 3 (by rfl) ⟨264440, by rfl⟩ : syracuseStep 1410349 = 528881) (by norm_num)
theorem B2114869 : Blo 1252444 2114869 := bbase (se 5 (by rfl) ⟨99134, by rfl⟩ : syracuseStep 2114869 = 198269) (by norm_num)
theorem B1410385 : Blo 1252444 1410385 := bbase (se 2 (by rfl) ⟨528894, by rfl⟩ : syracuseStep 1410385 = 1057789) (by norm_num)
theorem B4285781 : Blo 1252444 4285781 := bbase (se 12 (by rfl) ⟨1569, by rfl⟩ : syracuseStep 4285781 = 3139) (by norm_num)
theorem B1271125 : Blo 1252444 1271125 := bbase (se 12 (by rfl) ⟨465, by rfl⟩ : syracuseStep 1271125 = 931) (by norm_num)
theorem B2819429 : Blo 1252444 2819429 := bbase (se 4 (by rfl) ⟨264321, by rfl⟩ : syracuseStep 2819429 = 528643) (by norm_num)
theorem B4228469 : Blo 1252444 4228469 := bbase (se 5 (by rfl) ⟨198209, by rfl⟩ : syracuseStep 4228469 = 396419) (by norm_num)
theorem B1410421 : Blo 1252444 1410421 := bbase (se 5 (by rfl) ⟨66113, by rfl⟩ : syracuseStep 1410421 = 132227) (by norm_num)
theorem B2114957 : Blo 1252444 2114957 := bbase (se 3 (by rfl) ⟨396554, by rfl⟩ : syracuseStep 2114957 = 793109) (by norm_num)
theorem B5350805 : Blo 1252444 5350805 := bbase (se 6 (by rfl) ⟨125409, by rfl⟩ : syracuseStep 5350805 = 250819) (by norm_num)
theorem B10855829 : Blo 1252444 10855829 := bbase (se 6 (by rfl) ⟨254433, by rfl⟩ : syracuseStep 10855829 = 508867) (by norm_num)
theorem B14476693 : Blo 1252444 14476693 := bbase (se 6 (by rfl) ⟨339297, by rfl⟩ : syracuseStep 14476693 = 678595) (by norm_num)
theorem B1410457 : Blo 1252444 1410457 := bbase (se 2 (by rfl) ⟨528921, by rfl⟩ : syracuseStep 1410457 = 1057843) (by norm_num)
theorem B3171757 : Blo 1252444 3171757 := bbase (se 3 (by rfl) ⟨594704, by rfl⟩ : syracuseStep 3171757 = 1189409) (by norm_num)
theorem B2819501 : Blo 1252444 2819501 := bbase (se 3 (by rfl) ⟨528656, by rfl⟩ : syracuseStep 2819501 = 1057313) (by norm_num)
theorem B1410493 : Blo 1252444 1410493 := bbase (se 3 (by rfl) ⟨264467, by rfl⟩ : syracuseStep 1410493 = 528935) (by norm_num)
theorem B1410529 : Blo 1252444 1410529 := bbase (se 2 (by rfl) ⟨528948, by rfl⟩ : syracuseStep 1410529 = 1057897) (by norm_num)
theorem B2819573 : Blo 1252444 2819573 := bbase (se 5 (by rfl) ⟨132167, by rfl⟩ : syracuseStep 2819573 = 264335) (by norm_num)
theorem B3261941 : Blo 1252444 3261941 := bbase (se 5 (by rfl) ⟨152903, by rfl⟩ : syracuseStep 3261941 = 305807) (by norm_num)
theorem B1410565 : Blo 1252444 1410565 := bbase (se 4 (by rfl) ⟨132240, by rfl⟩ : syracuseStep 1410565 = 264481) (by norm_num)
theorem B2115085 : Blo 1252444 2115085 := bbase (se 3 (by rfl) ⟨396578, by rfl⟩ : syracuseStep 2115085 = 793157) (by norm_num)
theorem B3171869 : Blo 1252444 3171869 := bbase (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) (by norm_num)
theorem B1410601 : Blo 1252444 1410601 := bbase (se 2 (by rfl) ⟨528975, by rfl⟩ : syracuseStep 1410601 = 1057951) (by norm_num)
theorem B2819645 : Blo 1252444 2819645 := bbase (se 3 (by rfl) ⟨528683, by rfl⟩ : syracuseStep 2819645 = 1057367) (by norm_num)
theorem B1410637 : Blo 1252444 1410637 := bbase (se 3 (by rfl) ⟨264494, by rfl⟩ : syracuseStep 1410637 = 528989) (by norm_num)
theorem B2115173 : Blo 1252444 2115173 := bbase (se 4 (by rfl) ⟨198297, by rfl⟩ : syracuseStep 2115173 = 396595) (by norm_num)
theorem B1410673 : Blo 1252444 1410673 := bbase (se 2 (by rfl) ⟨529002, by rfl⟩ : syracuseStep 1410673 = 1058005) (by norm_num)
theorem B2819717 : Blo 1252444 2819717 := bbase (se 4 (by rfl) ⟨264348, by rfl⟩ : syracuseStep 2819717 = 528697) (by norm_num)
theorem B1410709 : Blo 1252444 1410709 := bbase (se 6 (by rfl) ⟨33063, by rfl⟩ : syracuseStep 1410709 = 66127) (by norm_num)
theorem B1410745 : Blo 1252444 1410745 := bbase (se 2 (by rfl) ⟨529029, by rfl⟩ : syracuseStep 1410745 = 1058059) (by norm_num)
theorem B2819789 : Blo 1252444 2819789 := bbase (se 3 (by rfl) ⟨528710, by rfl⟩ : syracuseStep 2819789 = 1057421) (by norm_num)
theorem B3172061 : Blo 1252444 3172061 := bbase (se 3 (by rfl) ⟨594761, by rfl⟩ : syracuseStep 3172061 = 1189523) (by norm_num)
theorem B2541277 : Blo 1252444 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B1410781 : Blo 1252444 1410781 := bbase (se 3 (by rfl) ⟨264521, by rfl⟩ : syracuseStep 1410781 = 529043) (by norm_num)
theorem B5080805 : Blo 1252444 5080805 := bbase (se 4 (by rfl) ⟨476325, by rfl⟩ : syracuseStep 5080805 = 952651) (by norm_num)
theorem B2115301 : Blo 1252444 2115301 := bbase (se 4 (by rfl) ⟨198309, by rfl⟩ : syracuseStep 2115301 = 396619) (by norm_num)
theorem B1410817 : Blo 1252444 1410817 := bbase (se 2 (by rfl) ⟨529056, by rfl⟩ : syracuseStep 1410817 = 1058113) (by norm_num)
theorem B2819861 : Blo 1252444 2819861 := bbase (se 6 (by rfl) ⟨66090, by rfl⟩ : syracuseStep 2819861 = 132181) (by norm_num)
theorem B4228901 : Blo 1252444 4228901 := bbase (se 4 (by rfl) ⟨396459, by rfl⟩ : syracuseStep 4228901 = 792919) (by norm_num)
theorem B1410853 : Blo 1252444 1410853 := bbase (se 4 (by rfl) ⟨132267, by rfl⟩ : syracuseStep 1410853 = 264535) (by norm_num)
theorem B3434293 : Blo 1252444 3434293 := bbase (se 5 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 3434293 = 321965) (by norm_num)
theorem B2115389 : Blo 1252444 2115389 := bbase (se 3 (by rfl) ⟨396635, by rfl⟩ : syracuseStep 2115389 = 793271) (by norm_num)
theorem B1410889 : Blo 1252444 1410889 := bbase (se 2 (by rfl) ⟨529083, by rfl⟩ : syracuseStep 1410889 = 1058167) (by norm_num)
theorem B2819933 : Blo 1252444 2819933 := bbase (se 3 (by rfl) ⟨528737, by rfl⟩ : syracuseStep 2819933 = 1057475) (by norm_num)
theorem B1410925 : Blo 1252444 1410925 := bbase (se 3 (by rfl) ⟨264548, by rfl⟩ : syracuseStep 1410925 = 529097) (by norm_num)
theorem B1410961 : Blo 1252444 1410961 := bbase (se 2 (by rfl) ⟨529110, by rfl⟩ : syracuseStep 1410961 = 1058221) (by norm_num)
theorem B2820005 : Blo 1252444 2820005 := bbase (se 4 (by rfl) ⟨264375, by rfl⟩ : syracuseStep 2820005 = 528751) (by norm_num)
theorem B1410997 : Blo 1252444 1410997 := bbase (se 5 (by rfl) ⟨66140, by rfl⟩ : syracuseStep 1410997 = 132281) (by norm_num)
theorem B2115517 : Blo 1252444 2115517 := bbase (se 3 (by rfl) ⟨396659, by rfl⟩ : syracuseStep 2115517 = 793319) (by norm_num)
theorem B2009045 : Blo 1252444 2009045 := bbase (se 7 (by rfl) ⟨23543, by rfl⟩ : syracuseStep 2009045 = 47087) (by norm_num)
theorem B1411033 : Blo 1252444 1411033 := bbase (se 2 (by rfl) ⟨529137, by rfl⟩ : syracuseStep 1411033 = 1058275) (by norm_num)
theorem B2820077 : Blo 1252444 2820077 := bbase (se 3 (by rfl) ⟨528764, by rfl⟩ : syracuseStep 2820077 = 1057529) (by norm_num)
theorem B1411069 : Blo 1252444 1411069 := bbase (se 3 (by rfl) ⟨264575, by rfl⟩ : syracuseStep 1411069 = 529151) (by norm_num)
theorem B2115605 : Blo 1252444 2115605 := bbase (se 6 (by rfl) ⟨49584, by rfl⟩ : syracuseStep 2115605 = 99169) (by norm_num)
theorem B1411105 : Blo 1252444 1411105 := bbase (se 2 (by rfl) ⟨529164, by rfl⟩ : syracuseStep 1411105 = 1058329) (by norm_num)
theorem B3172405 : Blo 1252444 3172405 := bbase (se 5 (by rfl) ⟨148706, by rfl⟩ : syracuseStep 3172405 = 297413) (by norm_num)
theorem B2820149 : Blo 1252444 2820149 := bbase (se 5 (by rfl) ⟨132194, by rfl⟩ : syracuseStep 2820149 = 264389) (by norm_num)
theorem B1411141 : Blo 1252444 1411141 := bbase (se 4 (by rfl) ⟨132294, by rfl⟩ : syracuseStep 1411141 = 264589) (by norm_num)
theorem B1411177 : Blo 1252444 1411177 := bbase (se 2 (by rfl) ⟨529191, by rfl⟩ : syracuseStep 1411177 = 1058383) (by norm_num)
theorem B7940213 : Blo 1252444 7940213 := bbase (se 5 (by rfl) ⟨372197, by rfl⟩ : syracuseStep 7940213 = 744395) (by norm_num)
theorem B2820221 : Blo 1252444 2820221 := bbase (se 3 (by rfl) ⟨528791, by rfl⟩ : syracuseStep 2820221 = 1057583) (by norm_num)
theorem B1411213 : Blo 1252444 1411213 := bbase (se 3 (by rfl) ⟨264602, by rfl⟩ : syracuseStep 1411213 = 529205) (by norm_num)
theorem B2115733 : Blo 1252444 2115733 := bbase (se 6 (by rfl) ⟨49587, by rfl⟩ : syracuseStep 2115733 = 99175) (by norm_num)
theorem B3172517 : Blo 1252444 3172517 := bbase (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) (by norm_num)
theorem B1411249 : Blo 1252444 1411249 := bbase (se 2 (by rfl) ⟨529218, by rfl⟩ : syracuseStep 1411249 = 1058437) (by norm_num)
theorem B2820293 : Blo 1252444 2820293 := bbase (se 4 (by rfl) ⟨264402, by rfl⟩ : syracuseStep 2820293 = 528805) (by norm_num)
theorem B4229333 : Blo 1252444 4229333 := bbase (se 7 (by rfl) ⟨49562, by rfl⟩ : syracuseStep 4229333 = 99125) (by norm_num)
theorem B1337573 : Blo 1252444 1337573 := bbase (se 4 (by rfl) ⟨125397, by rfl⟩ : syracuseStep 1337573 = 250795) (by norm_num)
theorem B2541797 : Blo 1252444 2541797 := bbase (se 4 (by rfl) ⟨238293, by rfl⟩ : syracuseStep 2541797 = 476587) (by norm_num)
theorem B2115821 : Blo 1252444 2115821 := bbase (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) (by norm_num)
theorem B2820365 : Blo 1252444 2820365 := bbase (se 3 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 2820365 = 1057637) (by norm_num)
theorem B2820437 : Blo 1252444 2820437 := bbase (se 10 (by rfl) ⟨4131, by rfl⟩ : syracuseStep 2820437 = 8263) (by norm_num)
theorem B3172709 : Blo 1252444 3172709 := bbase (se 4 (by rfl) ⟨297441, by rfl⟩ : syracuseStep 3172709 = 594883) (by norm_num)
theorem B2115949 : Blo 1252444 2115949 := bbase (se 3 (by rfl) ⟨396740, by rfl⟩ : syracuseStep 2115949 = 793481) (by norm_num)
theorem B14281109 : Blo 1252444 14281109 := bbase (se 6 (by rfl) ⟨334713, by rfl⟩ : syracuseStep 14281109 = 669427) (by norm_num)
theorem B2820509 : Blo 1252444 2820509 := bbase (se 3 (by rfl) ⟨528845, by rfl⟩ : syracuseStep 2820509 = 1057691) (by norm_num)
theorem B2378173 : Blo 1252444 2378173 := bbase (se 3 (by rfl) ⟨445907, by rfl⟩ : syracuseStep 2378173 = 891815) (by norm_num)
theorem B6343109 : Blo 1252444 6343109 := bbase (se 4 (by rfl) ⟨594666, by rfl⟩ : syracuseStep 6343109 = 1189333) (by norm_num)
theorem B2116037 : Blo 1252444 2116037 := bbase (se 4 (by rfl) ⟨198378, by rfl⟩ : syracuseStep 2116037 = 396757) (by norm_num)
theorem B2820581 : Blo 1252444 2820581 := bbase (se 4 (by rfl) ⟨264429, by rfl⟩ : syracuseStep 2820581 = 528859) (by norm_num)
theorem B2820653 : Blo 1252444 2820653 := bbase (se 3 (by rfl) ⟨528872, by rfl⟩ : syracuseStep 2820653 = 1057745) (by norm_num)
theorem B2116165 : Blo 1252444 2116165 := bbase (se 4 (by rfl) ⟨198390, by rfl⟩ : syracuseStep 2116165 = 396781) (by norm_num)
theorem B2378317 : Blo 1252444 2378317 := bbase (se 3 (by rfl) ⟨445934, by rfl⟩ : syracuseStep 2378317 = 891869) (by norm_num)
theorem B2820725 : Blo 1252444 2820725 := bbase (se 5 (by rfl) ⟨132221, by rfl⟩ : syracuseStep 2820725 = 264443) (by norm_num)
theorem B4229765 : Blo 1252444 4229765 := bbase (se 4 (by rfl) ⟨396540, by rfl⟩ : syracuseStep 4229765 = 793081) (by norm_num)
theorem B1878677 : Blo 1252444 1878677 := bbase (se 6 (by rfl) ⟨44031, by rfl⟩ : syracuseStep 1878677 = 88063) (by norm_num)
theorem B2116253 : Blo 1252444 2116253 := bbase (se 3 (by rfl) ⟨396797, by rfl⟩ : syracuseStep 2116253 = 793595) (by norm_num)
theorem B1338017 : Blo 1252444 1338017 := bbase (se 2 (by rfl) ⟨501756, by rfl⟩ : syracuseStep 1338017 = 1003513) (by norm_num)
theorem B1878701 : Blo 1252444 1878701 := bbase (se 3 (by rfl) ⟨352256, by rfl⟩ : syracuseStep 1878701 = 704513) (by norm_num)
theorem B3173053 : Blo 1252444 3173053 := bbase (se 3 (by rfl) ⟨594947, by rfl⟩ : syracuseStep 3173053 = 1189895) (by norm_num)
theorem B2820797 : Blo 1252444 2820797 := bbase (se 3 (by rfl) ⟨528899, by rfl⟩ : syracuseStep 2820797 = 1057799) (by norm_num)
theorem B1878725 : Blo 1252444 1878725 := bbase (se 4 (by rfl) ⟨176130, by rfl⟩ : syracuseStep 1878725 = 352261) (by norm_num)
theorem B1878749 : Blo 1252444 1878749 := bbase (se 3 (by rfl) ⟨352265, by rfl⟩ : syracuseStep 1878749 = 704531) (by norm_num)
theorem B1338077 : Blo 1252444 1338077 := bbase (se 3 (by rfl) ⟨250889, by rfl⟩ : syracuseStep 1338077 = 501779) (by norm_num)
theorem B2378477 : Blo 1252444 2378477 := bbase (se 3 (by rfl) ⟨445964, by rfl⟩ : syracuseStep 2378477 = 891929) (by norm_num)
theorem B1878773 : Blo 1252444 1878773 := bbase (se 5 (by rfl) ⟨88067, by rfl⟩ : syracuseStep 1878773 = 176135) (by norm_num)
theorem B2820869 : Blo 1252444 2820869 := bbase (se 4 (by rfl) ⟨264456, by rfl⟩ : syracuseStep 2820869 = 528913) (by norm_num)
theorem B1878797 : Blo 1252444 1878797 := bbase (se 3 (by rfl) ⟨352274, by rfl⟩ : syracuseStep 1878797 = 704549) (by norm_num)
theorem B2116381 : Blo 1252444 2116381 := bbase (se 3 (by rfl) ⟨396821, by rfl⟩ : syracuseStep 2116381 = 793643) (by norm_num)
theorem B1878821 : Blo 1252444 1878821 := bbase (se 4 (by rfl) ⟨176139, by rfl⟩ : syracuseStep 1878821 = 352279) (by norm_num)
theorem B3173165 : Blo 1252444 3173165 := bbase (se 3 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 3173165 = 1189937) (by norm_num)
theorem B4516661 : Blo 1252444 4516661 := bbase (se 5 (by rfl) ⟨211718, by rfl⟩ : syracuseStep 4516661 = 423437) (by norm_num)
theorem B4762421 : Blo 1252444 4762421 := bbase (se 5 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 4762421 = 446477) (by norm_num)
theorem B1878845 : Blo 1252444 1878845 := bbase (se 3 (by rfl) ⟨352283, by rfl⟩ : syracuseStep 1878845 = 704567) (by norm_num)
theorem B1428301 : Blo 1252444 1428301 := bbase (se 3 (by rfl) ⟨267806, by rfl⟩ : syracuseStep 1428301 = 535613) (by norm_num)
theorem B2820941 : Blo 1252444 2820941 := bbase (se 3 (by rfl) ⟨528926, by rfl⟩ : syracuseStep 2820941 = 1057853) (by norm_num)
theorem B1878869 : Blo 1252444 1878869 := bbase (se 9 (by rfl) ⟨5504, by rfl⟩ : syracuseStep 1878869 = 11009) (by norm_num)
theorem B1338205 : Blo 1252444 1338205 := bbase (se 3 (by rfl) ⟨250913, by rfl⟩ : syracuseStep 1338205 = 501827) (by norm_num)
theorem B1878893 : Blo 1252444 1878893 := bbase (se 3 (by rfl) ⟨352292, by rfl⟩ : syracuseStep 1878893 = 704585) (by norm_num)
theorem B12217205 : Blo 1252444 12217205 := bbase (se 5 (by rfl) ⟨572681, by rfl⟩ : syracuseStep 12217205 = 1145363) (by norm_num)
theorem B2116469 : Blo 1252444 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B2378621 : Blo 1252444 2378621 := bbase (se 3 (by rfl) ⟨445991, by rfl⟩ : syracuseStep 2378621 = 891983) (by norm_num)
theorem B1878917 : Blo 1252444 1878917 := bbase (se 4 (by rfl) ⟨176148, by rfl⟩ : syracuseStep 1878917 = 352297) (by norm_num)
theorem B2821013 : Blo 1252444 2821013 := bbase (se 6 (by rfl) ⟨66117, by rfl⟩ : syracuseStep 2821013 = 132235) (by norm_num)
theorem B1878941 : Blo 1252444 1878941 := bbase (se 3 (by rfl) ⟨352301, by rfl⟩ : syracuseStep 1878941 = 704603) (by norm_num)
theorem B1878965 : Blo 1252444 1878965 := bbase (se 5 (by rfl) ⟨88076, by rfl⟩ : syracuseStep 1878965 = 176153) (by norm_num)
theorem B1878989 : Blo 1252444 1878989 := bbase (se 3 (by rfl) ⟨352310, by rfl⟩ : syracuseStep 1878989 = 704621) (by norm_num)
theorem B1409017 : Blo 1252444 1409017 := bbase (se 2 (by rfl) ⟨528381, by rfl⟩ : syracuseStep 1409017 = 1056763) (by norm_num)
theorem B2821085 : Blo 1252444 2821085 := bbase (se 3 (by rfl) ⟨528953, by rfl⟩ : syracuseStep 2821085 = 1057907) (by norm_num)
theorem B1879013 : Blo 1252444 1879013 := bbase (se 4 (by rfl) ⟨176157, by rfl⟩ : syracuseStep 1879013 = 352315) (by norm_num)
theorem B3173357 : Blo 1252444 3173357 := bbase (se 3 (by rfl) ⟨595004, by rfl⟩ : syracuseStep 3173357 = 1190009) (by norm_num)
theorem B2116597 : Blo 1252444 2116597 := bbase (se 5 (by rfl) ⟨99215, by rfl⟩ : syracuseStep 2116597 = 198431) (by norm_num)
theorem B1879037 : Blo 1252444 1879037 := bbase (se 3 (by rfl) ⟨352319, by rfl⟩ : syracuseStep 1879037 = 704639) (by norm_num)
theorem B1879061 : Blo 1252444 1879061 := bbase (se 6 (by rfl) ⟨44040, by rfl⟩ : syracuseStep 1879061 = 88081) (by norm_num)
theorem B9522197 : Blo 1252444 9522197 := bbase (se 6 (by rfl) ⟨223176, by rfl⟩ : syracuseStep 9522197 = 446353) (by norm_num)
theorem B2821157 : Blo 1252444 2821157 := bbase (se 4 (by rfl) ⟨264483, by rfl⟩ : syracuseStep 2821157 = 528967) (by norm_num)
theorem B1879085 : Blo 1252444 1879085 := bbase (se 3 (by rfl) ⟨352328, by rfl⟩ : syracuseStep 1879085 = 704657) (by norm_num)
theorem B4230197 : Blo 1252444 4230197 := bbase (se 5 (by rfl) ⟨198290, by rfl⟩ : syracuseStep 4230197 = 396581) (by norm_num)
theorem B1879109 : Blo 1252444 1879109 := bbase (se 4 (by rfl) ⟨176166, by rfl⟩ : syracuseStep 1879109 = 352333) (by norm_num)
theorem B2116685 : Blo 1252444 2116685 := bbase (se 3 (by rfl) ⟨396878, by rfl⟩ : syracuseStep 2116685 = 793757) (by norm_num)
theorem B4762709 : Blo 1252444 4762709 := bbase (se 8 (by rfl) ⟨27906, by rfl⟩ : syracuseStep 4762709 = 55813) (by norm_num)
theorem B1879133 : Blo 1252444 1879133 := bbase (se 3 (by rfl) ⟨352337, by rfl⟩ : syracuseStep 1879133 = 704675) (by norm_num)
theorem B2288741 : Blo 1252444 2288741 := bbase (se 4 (by rfl) ⟨214569, by rfl⟩ : syracuseStep 2288741 = 429139) (by norm_num)
theorem B2821229 : Blo 1252444 2821229 := bbase (se 3 (by rfl) ⟨528980, by rfl⟩ : syracuseStep 2821229 = 1057961) (by norm_num)
theorem B1879157 : Blo 1252444 1879157 := bbase (se 5 (by rfl) ⟨88085, by rfl⟩ : syracuseStep 1879157 = 176171) (by norm_num)
theorem B4017269 : Blo 1252444 4017269 := bbase (se 5 (by rfl) ⟨188309, by rfl⟩ : syracuseStep 4017269 = 376619) (by norm_num)
theorem B5352581 : Blo 1252444 5352581 := bbase (se 4 (by rfl) ⟨501804, by rfl⟩ : syracuseStep 5352581 = 1003609) (by norm_num)
theorem B1879181 : Blo 1252444 1879181 := bbase (se 3 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 1879181 = 704693) (by norm_num)
theorem B1428629 : Blo 1252444 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B2378909 : Blo 1252444 2378909 := bbase (se 3 (by rfl) ⟨446045, by rfl⟩ : syracuseStep 2378909 = 892091) (by norm_num)
theorem B1879205 : Blo 1252444 1879205 := bbase (se 4 (by rfl) ⟨176175, by rfl⟩ : syracuseStep 1879205 = 352351) (by norm_num)
theorem B2821301 : Blo 1252444 2821301 := bbase (se 5 (by rfl) ⟨132248, by rfl⟩ : syracuseStep 2821301 = 264497) (by norm_num)
theorem B1879229 : Blo 1252444 1879229 := bbase (se 3 (by rfl) ⟨352355, by rfl⟩ : syracuseStep 1879229 = 704711) (by norm_num)
theorem B3214541 : Blo 1252444 3214541 := bbase (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) (by norm_num)
theorem B2116813 : Blo 1252444 2116813 := bbase (se 3 (by rfl) ⟨396902, by rfl⟩ : syracuseStep 2116813 = 793805) (by norm_num)
theorem B1879253 : Blo 1252444 1879253 := bbase (se 7 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 1879253 = 44045) (by norm_num)
theorem B1879277 : Blo 1252444 1879277 := bbase (se 3 (by rfl) ⟨352364, by rfl⟩ : syracuseStep 1879277 = 704729) (by norm_num)
theorem B2821373 : Blo 1252444 2821373 := bbase (se 3 (by rfl) ⟨529007, by rfl⟩ : syracuseStep 2821373 = 1058015) (by norm_num)
theorem B1879301 : Blo 1252444 1879301 := bbase (se 4 (by rfl) ⟨176184, by rfl⟩ : syracuseStep 1879301 = 352369) (by norm_num)
theorem B1338649 : Blo 1252444 1338649 := bbase (se 2 (by rfl) ⟨501993, by rfl⟩ : syracuseStep 1338649 = 1003987) (by norm_num)
theorem B1879325 : Blo 1252444 1879325 := bbase (se 3 (by rfl) ⟨352373, by rfl⟩ : syracuseStep 1879325 = 704747) (by norm_num)
theorem B1879349 : Blo 1252444 1879349 := bbase (se 5 (by rfl) ⟨88094, by rfl⟩ : syracuseStep 1879349 = 176189) (by norm_num)
theorem B2379061 : Blo 1252444 2379061 := bbase (se 5 (by rfl) ⟨111518, by rfl⟩ : syracuseStep 2379061 = 223037) (by norm_num)
theorem B3173701 : Blo 1252444 3173701 := bbase (se 4 (by rfl) ⟨297534, by rfl⟩ : syracuseStep 3173701 = 595069) (by norm_num)
theorem B2821445 : Blo 1252444 2821445 := bbase (se 4 (by rfl) ⟨264510, by rfl⟩ : syracuseStep 2821445 = 529021) (by norm_num)
theorem B1879373 : Blo 1252444 1879373 := bbase (se 3 (by rfl) ⟨352382, by rfl⟩ : syracuseStep 1879373 = 704765) (by norm_num)
theorem B1879397 : Blo 1252444 1879397 := bbase (se 4 (by rfl) ⟨176193, by rfl⟩ : syracuseStep 1879397 = 352387) (by norm_num)
theorem B1879421 : Blo 1252444 1879421 := bbase (se 3 (by rfl) ⟨352391, by rfl⟩ : syracuseStep 1879421 = 704783) (by norm_num)
theorem B2821517 : Blo 1252444 2821517 := bbase (se 3 (by rfl) ⟨529034, by rfl⟩ : syracuseStep 2821517 = 1058069) (by norm_num)
theorem B1338769 : Blo 1252444 1338769 := bbase (se 2 (by rfl) ⟨502038, by rfl⟩ : syracuseStep 1338769 = 1004077) (by norm_num)
theorem B1879445 : Blo 1252444 1879445 := bbase (se 6 (by rfl) ⟨44049, by rfl⟩ : syracuseStep 1879445 = 88099) (by norm_num)
theorem B1879469 : Blo 1252444 1879469 := bbase (se 3 (by rfl) ⟨352400, by rfl⟩ : syracuseStep 1879469 = 704801) (by norm_num)
theorem B9514421 : Blo 1252444 9514421 := bbase (se 5 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 9514421 = 891977) (by norm_num)
theorem B3173813 : Blo 1252444 3173813 := bbase (se 5 (by rfl) ⟨148772, by rfl⟩ : syracuseStep 3173813 = 297545) (by norm_num)
theorem B1527229 : Blo 1252444 1527229 := bbase (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) (by norm_num)
theorem B1879493 : Blo 1252444 1879493 := bbase (se 4 (by rfl) ⟨176202, by rfl⟩ : syracuseStep 1879493 = 352405) (by norm_num)
theorem B2821589 : Blo 1252444 2821589 := bbase (se 7 (by rfl) ⟨33065, by rfl⟩ : syracuseStep 2821589 = 66131) (by norm_num)
theorem B1879517 : Blo 1252444 1879517 := bbase (se 3 (by rfl) ⟨352409, by rfl⟩ : syracuseStep 1879517 = 704819) (by norm_num)
theorem B4230629 : Blo 1252444 4230629 := bbase (se 4 (by rfl) ⟨396621, by rfl⟩ : syracuseStep 4230629 = 793243) (by norm_num)
theorem B1879541 : Blo 1252444 1879541 := bbase (se 5 (by rfl) ⟨88103, by rfl⟩ : syracuseStep 1879541 = 176207) (by norm_num)
theorem B4517365 : Blo 1252444 4517365 := bbase (se 5 (by rfl) ⟨211751, by rfl⟩ : syracuseStep 4517365 = 423503) (by norm_num)
theorem B1879565 : Blo 1252444 1879565 := bbase (se 3 (by rfl) ⟨352418, by rfl⟩ : syracuseStep 1879565 = 704837) (by norm_num)
theorem B2821661 : Blo 1252444 2821661 := bbase (se 3 (by rfl) ⟨529061, by rfl⟩ : syracuseStep 2821661 = 1058123) (by norm_num)
theorem B1879589 : Blo 1252444 1879589 := bbase (se 4 (by rfl) ⟨176211, by rfl⟩ : syracuseStep 1879589 = 352423) (by norm_num)
theorem B9653813 : Blo 1252444 9653813 := bbase (se 5 (by rfl) ⟨452522, by rfl⟩ : syracuseStep 9653813 = 905045) (by norm_num)
theorem B1879613 : Blo 1252444 1879613 := bbase (se 3 (by rfl) ⟨352427, by rfl⟩ : syracuseStep 1879613 = 704855) (by norm_num)
theorem B1879637 : Blo 1252444 1879637 := bbase (se 8 (by rfl) ⟨11013, by rfl⟩ : syracuseStep 1879637 = 22027) (by norm_num)
theorem B2379365 : Blo 1252444 2379365 := bbase (se 4 (by rfl) ⟨223065, by rfl⟩ : syracuseStep 2379365 = 446131) (by norm_num)
theorem B2821733 : Blo 1252444 2821733 := bbase (se 4 (by rfl) ⟨264537, by rfl⟩ : syracuseStep 2821733 = 529075) (by norm_num)
theorem B1879661 : Blo 1252444 1879661 := bbase (se 3 (by rfl) ⟨352436, by rfl⟩ : syracuseStep 1879661 = 704873) (by norm_num)
theorem B3174005 : Blo 1252444 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B1879685 : Blo 1252444 1879685 := bbase (se 4 (by rfl) ⟨176220, by rfl⟩ : syracuseStep 1879685 = 352441) (by norm_num)
theorem B1339021 : Blo 1252444 1339021 := bbase (se 3 (by rfl) ⟨251066, by rfl⟩ : syracuseStep 1339021 = 502133) (by norm_num)
theorem B1339025 : Blo 1252444 1339025 := bbase (se 2 (by rfl) ⟨502134, by rfl⟩ : syracuseStep 1339025 = 1004269) (by norm_num)
theorem B1879709 : Blo 1252444 1879709 := bbase (se 3 (by rfl) ⟨352445, by rfl⟩ : syracuseStep 1879709 = 704891) (by norm_num)
theorem B2821805 : Blo 1252444 2821805 := bbase (se 3 (by rfl) ⟨529088, by rfl⟩ : syracuseStep 2821805 = 1058177) (by norm_num)
theorem B1879733 : Blo 1252444 1879733 := bbase (se 5 (by rfl) ⟨88112, by rfl⟩ : syracuseStep 1879733 = 176225) (by norm_num)
theorem B1879757 : Blo 1252444 1879757 := bbase (se 3 (by rfl) ⟨352454, by rfl⟩ : syracuseStep 1879757 = 704909) (by norm_num)
theorem B6344405 : Blo 1252444 6344405 := bbase (se 7 (by rfl) ⟨74348, by rfl⟩ : syracuseStep 6344405 = 148697) (by norm_num)
theorem B1879781 : Blo 1252444 1879781 := bbase (se 4 (by rfl) ⟨176229, by rfl⟩ : syracuseStep 1879781 = 352459) (by norm_num)
theorem B2821877 : Blo 1252444 2821877 := bbase (se 5 (by rfl) ⟨132275, by rfl⟩ : syracuseStep 2821877 = 264551) (by norm_num)
theorem B1879805 : Blo 1252444 1879805 := bbase (se 3 (by rfl) ⟨352463, by rfl⟩ : syracuseStep 1879805 = 704927) (by norm_num)
theorem B1879829 : Blo 1252444 1879829 := bbase (se 6 (by rfl) ⟨44058, by rfl⟩ : syracuseStep 1879829 = 88117) (by norm_num)
theorem B1879853 : Blo 1252444 1879853 := bbase (se 3 (by rfl) ⟨352472, by rfl⟩ : syracuseStep 1879853 = 704945) (by norm_num)
theorem B2821949 : Blo 1252444 2821949 := bbase (se 3 (by rfl) ⟨529115, by rfl⟩ : syracuseStep 2821949 = 1058231) (by norm_num)
theorem B1879877 : Blo 1252444 1879877 := bbase (se 4 (by rfl) ⟨176238, by rfl⟩ : syracuseStep 1879877 = 352477) (by norm_num)
theorem B36622165 : Blo 1252444 36622165 := bbase (se 9 (by rfl) ⟨107291, by rfl⟩ : syracuseStep 36622165 = 214583) (by norm_num)
theorem B2289493 : Blo 1252444 2289493 := bbase (se 9 (by rfl) ⟨6707, by rfl⟩ : syracuseStep 2289493 = 13415) (by norm_num)
theorem B1879901 : Blo 1252444 1879901 := bbase (se 3 (by rfl) ⟨352481, by rfl⟩ : syracuseStep 1879901 = 704963) (by norm_num)
theorem B1879925 : Blo 1252444 1879925 := bbase (se 5 (by rfl) ⟨88121, by rfl⟩ : syracuseStep 1879925 = 176243) (by norm_num)
theorem B2822021 : Blo 1252444 2822021 := bbase (se 4 (by rfl) ⟨264564, by rfl⟩ : syracuseStep 2822021 = 529129) (by norm_num)
theorem B1879949 : Blo 1252444 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B4820885 : Blo 1252444 4820885 := bbase (se 6 (by rfl) ⟨112989, by rfl⟩ : syracuseStep 4820885 = 225979) (by norm_num)
theorem B4231061 : Blo 1252444 4231061 := bbase (se 6 (by rfl) ⟨99165, by rfl⟩ : syracuseStep 4231061 = 198331) (by norm_num)
theorem B1879973 : Blo 1252444 1879973 := bbase (se 4 (by rfl) ⟨176247, by rfl⟩ : syracuseStep 1879973 = 352495) (by norm_num)
theorem B1879997 : Blo 1252444 1879997 := bbase (se 3 (by rfl) ⟨352499, by rfl⟩ : syracuseStep 1879997 = 704999) (by norm_num)
theorem B3174349 : Blo 1252444 3174349 := bbase (se 3 (by rfl) ⟨595190, by rfl⟩ : syracuseStep 3174349 = 1190381) (by norm_num)
theorem B2822093 : Blo 1252444 2822093 := bbase (se 3 (by rfl) ⟨529142, by rfl⟩ : syracuseStep 2822093 = 1058285) (by norm_num)
theorem B1880021 : Blo 1252444 1880021 := bbase (se 7 (by rfl) ⟨22031, by rfl⟩ : syracuseStep 1880021 = 44063) (by norm_num)
theorem B1880045 : Blo 1252444 1880045 := bbase (se 3 (by rfl) ⟨352508, by rfl⟩ : syracuseStep 1880045 = 705017) (by norm_num)
theorem B1880069 : Blo 1252444 1880069 := bbase (se 4 (by rfl) ⟨176256, by rfl⟩ : syracuseStep 1880069 = 352513) (by norm_num)
theorem B1585165 : Blo 1252444 1585165 := bbase (se 3 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 1585165 = 594437) (by norm_num)
theorem B2822165 : Blo 1252444 2822165 := bbase (se 6 (by rfl) ⟨66144, by rfl⟩ : syracuseStep 2822165 = 132289) (by norm_num)
theorem B1880093 : Blo 1252444 1880093 := bbase (se 3 (by rfl) ⟨352517, by rfl⟩ : syracuseStep 1880093 = 705035) (by norm_num)
theorem B1880117 : Blo 1252444 1880117 := bbase (se 5 (by rfl) ⟨88130, by rfl⟩ : syracuseStep 1880117 = 176261) (by norm_num)
theorem B3174461 : Blo 1252444 3174461 := bbase (se 3 (by rfl) ⟨595211, by rfl⟩ : syracuseStep 3174461 = 1190423) (by norm_num)
theorem B1880141 : Blo 1252444 1880141 := bbase (se 3 (by rfl) ⟨352526, by rfl⟩ : syracuseStep 1880141 = 705053) (by norm_num)
theorem B3010645 : Blo 1252444 3010645 := bbase (se 8 (by rfl) ⟨17640, by rfl⟩ : syracuseStep 3010645 = 35281) (by norm_num)
theorem B2822237 : Blo 1252444 2822237 := bbase (se 3 (by rfl) ⟨529169, by rfl⟩ : syracuseStep 2822237 = 1058339) (by norm_num)
theorem B1880165 : Blo 1252444 1880165 := bbase (se 4 (by rfl) ⟨176265, by rfl⟩ : syracuseStep 1880165 = 352531) (by norm_num)
theorem B1585261 : Blo 1252444 1585261 := bbase (se 3 (by rfl) ⟨297236, by rfl⟩ : syracuseStep 1585261 = 594473) (by norm_num)
theorem B1880189 : Blo 1252444 1880189 := bbase (se 3 (by rfl) ⟨352535, by rfl⟩ : syracuseStep 1880189 = 705071) (by norm_num)
theorem B1880213 : Blo 1252444 1880213 := bbase (se 6 (by rfl) ⟨44067, by rfl⟩ : syracuseStep 1880213 = 88135) (by norm_num)
theorem B1429661 : Blo 1252444 1429661 := bbase (se 3 (by rfl) ⟨268061, by rfl⟩ : syracuseStep 1429661 = 536123) (by norm_num)
theorem B2822309 : Blo 1252444 2822309 := bbase (se 4 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 2822309 = 529183) (by norm_num)
theorem B1880237 : Blo 1252444 1880237 := bbase (se 3 (by rfl) ⟨352544, by rfl⟩ : syracuseStep 1880237 = 705089) (by norm_num)
theorem B5714117 : Blo 1252444 5714117 := bbase (se 4 (by rfl) ⟨535698, by rfl⟩ : syracuseStep 5714117 = 1071397) (by norm_num)
theorem B1880261 : Blo 1252444 1880261 := bbase (se 4 (by rfl) ⟨176274, by rfl⟩ : syracuseStep 1880261 = 352549) (by norm_num)
theorem B1880285 : Blo 1252444 1880285 := bbase (se 3 (by rfl) ⟨352553, by rfl⟩ : syracuseStep 1880285 = 705107) (by norm_num)
theorem B2822381 : Blo 1252444 2822381 := bbase (se 3 (by rfl) ⟨529196, by rfl⟩ : syracuseStep 2822381 = 1058393) (by norm_num)
theorem B1880309 : Blo 1252444 1880309 := bbase (se 5 (by rfl) ⟨88139, by rfl⟩ : syracuseStep 1880309 = 176279) (by norm_num)
theorem B3174653 : Blo 1252444 3174653 := bbase (se 3 (by rfl) ⟨595247, by rfl⟩ : syracuseStep 3174653 = 1190495) (by norm_num)
theorem B1880333 : Blo 1252444 1880333 := bbase (se 3 (by rfl) ⟨352562, by rfl⟩ : syracuseStep 1880333 = 705125) (by norm_num)
theorem B1585433 : Blo 1252444 1585433 := bbase (se 2 (by rfl) ⟨594537, by rfl⟩ : syracuseStep 1585433 = 1189075) (by norm_num)
theorem B1880357 : Blo 1252444 1880357 := bbase (se 4 (by rfl) ⟨176283, by rfl⟩ : syracuseStep 1880357 = 352567) (by norm_num)
theorem B2822453 : Blo 1252444 2822453 := bbase (se 5 (by rfl) ⟨132302, by rfl⟩ : syracuseStep 2822453 = 264605) (by norm_num)
theorem B3010877 : Blo 1252444 3010877 := bbase (se 3 (by rfl) ⟨564539, by rfl⟩ : syracuseStep 3010877 = 1129079) (by norm_num)
theorem B1880381 : Blo 1252444 1880381 := bbase (se 3 (by rfl) ⟨352571, by rfl⟩ : syracuseStep 1880381 = 705143) (by norm_num)
theorem B4231493 : Blo 1252444 4231493 := bbase (se 4 (by rfl) ⟨396702, by rfl⟩ : syracuseStep 4231493 = 793405) (by norm_num)
theorem B1585489 : Blo 1252444 1585489 := bbase (se 2 (by rfl) ⟨594558, by rfl⟩ : syracuseStep 1585489 = 1189117) (by norm_num)
theorem B1880405 : Blo 1252444 1880405 := bbase (se 10 (by rfl) ⟨2754, by rfl⟩ : syracuseStep 1880405 = 5509) (by norm_num)
theorem B2380117 : Blo 1252444 2380117 := bbase (se 10 (by rfl) ⟨3486, by rfl⟩ : syracuseStep 2380117 = 6973) (by norm_num)
theorem B1880429 : Blo 1252444 1880429 := bbase (se 3 (by rfl) ⟨352580, by rfl⟩ : syracuseStep 1880429 = 705161) (by norm_num)
theorem B3567989 : Blo 1252444 3567989 := bbase (se 5 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 3567989 = 334499) (by norm_num)
theorem B1880453 : Blo 1252444 1880453 := bbase (se 4 (by rfl) ⟨176292, by rfl⟩ : syracuseStep 1880453 = 352585) (by norm_num)
theorem B1880477 : Blo 1252444 1880477 := bbase (se 3 (by rfl) ⟨352589, by rfl⟩ : syracuseStep 1880477 = 705179) (by norm_num)
theorem B1429925 : Blo 1252444 1429925 := bbase (se 4 (by rfl) ⟨134055, by rfl⟩ : syracuseStep 1429925 = 268111) (by norm_num)
theorem B1585585 : Blo 1252444 1585585 := bbase (se 2 (by rfl) ⟨594594, by rfl⟩ : syracuseStep 1585585 = 1189189) (by norm_num)
theorem B1880501 : Blo 1252444 1880501 := bbase (se 5 (by rfl) ⟨88148, by rfl⟩ : syracuseStep 1880501 = 176297) (by norm_num)
theorem B1880525 : Blo 1252444 1880525 := bbase (se 3 (by rfl) ⟨352598, by rfl⟩ : syracuseStep 1880525 = 705197) (by norm_num)
theorem B1880549 : Blo 1252444 1880549 := bbase (se 4 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 1880549 = 352603) (by norm_num)
theorem B2380261 : Blo 1252444 2380261 := bbase (se 4 (by rfl) ⟨223149, by rfl⟩ : syracuseStep 2380261 = 446299) (by norm_num)
theorem B2675197 : Blo 1252444 2675197 := bbase (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) (by norm_num)
theorem B1880573 : Blo 1252444 1880573 := bbase (se 3 (by rfl) ⟨352607, by rfl⟩ : syracuseStep 1880573 = 705215) (by norm_num)
theorem B3215893 : Blo 1252444 3215893 := bbase (se 6 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 3215893 = 150745) (by norm_num)
theorem B16282133 : Blo 1252444 16282133 := bbase (se 6 (by rfl) ⟨381612, by rfl⟩ : syracuseStep 16282133 = 763225) (by norm_num)
theorem B1880597 : Blo 1252444 1880597 := bbase (se 6 (by rfl) ⟨44076, by rfl⟩ : syracuseStep 1880597 = 88153) (by norm_num)
theorem B6107669 : Blo 1252444 6107669 := bbase (se 6 (by rfl) ⟨143148, by rfl⟩ : syracuseStep 6107669 = 286297) (by norm_num)
theorem B1880621 : Blo 1252444 1880621 := bbase (se 3 (by rfl) ⟨352616, by rfl⟩ : syracuseStep 1880621 = 705233) (by norm_num)
theorem B6427189 : Blo 1252444 6427189 := bbase (se 5 (by rfl) ⟨301274, by rfl⟩ : syracuseStep 6427189 = 602549) (by norm_num)
theorem B1880645 : Blo 1252444 1880645 := bbase (se 4 (by rfl) ⟨176310, by rfl⟩ : syracuseStep 1880645 = 352621) (by norm_num)
theorem B3174997 : Blo 1252444 3174997 := bbase (se 8 (by rfl) ⟨18603, by rfl⟩ : syracuseStep 3174997 = 37207) (by norm_num)
theorem B1585757 : Blo 1252444 1585757 := bbase (se 3 (by rfl) ⟨297329, by rfl⟩ : syracuseStep 1585757 = 594659) (by norm_num)
theorem B1880669 : Blo 1252444 1880669 := bbase (se 3 (by rfl) ⟨352625, by rfl⟩ : syracuseStep 1880669 = 705251) (by norm_num)
theorem B1880693 : Blo 1252444 1880693 := bbase (se 5 (by rfl) ⟨88157, by rfl⟩ : syracuseStep 1880693 = 176315) (by norm_num)
theorem B2380421 : Blo 1252444 2380421 := bbase (se 4 (by rfl) ⟨223164, by rfl⟩ : syracuseStep 2380421 = 446329) (by norm_num)
theorem B1880717 : Blo 1252444 1880717 := bbase (se 3 (by rfl) ⟨352634, by rfl⟩ : syracuseStep 1880717 = 705269) (by norm_num)
theorem B4756117 : Blo 1252444 4756117 := bbase (se 6 (by rfl) ⟨111471, by rfl⟩ : syracuseStep 4756117 = 222943) (by norm_num)
theorem B1585813 : Blo 1252444 1585813 := bbase (se 6 (by rfl) ⟨37167, by rfl⟩ : syracuseStep 1585813 = 74335) (by norm_num)
theorem B1880741 : Blo 1252444 1880741 := bbase (se 4 (by rfl) ⟨176319, by rfl⟩ : syracuseStep 1880741 = 352639) (by norm_num)
theorem B1880765 : Blo 1252444 1880765 := bbase (se 3 (by rfl) ⟨352643, by rfl⟩ : syracuseStep 1880765 = 705287) (by norm_num)
theorem B3011269 : Blo 1252444 3011269 := bbase (se 4 (by rfl) ⟨282306, by rfl⟩ : syracuseStep 3011269 = 564613) (by norm_num)
theorem B3175109 : Blo 1252444 3175109 := bbase (se 4 (by rfl) ⟨297666, by rfl⟩ : syracuseStep 3175109 = 595333) (by norm_num)
theorem B1880789 : Blo 1252444 1880789 := bbase (se 7 (by rfl) ⟨22040, by rfl⟩ : syracuseStep 1880789 = 44081) (by norm_num)
theorem B1430245 : Blo 1252444 1430245 := bbase (se 4 (by rfl) ⟨134085, by rfl⟩ : syracuseStep 1430245 = 268171) (by norm_num)
theorem B2257645 : Blo 1252444 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B1880813 : Blo 1252444 1880813 := bbase (se 3 (by rfl) ⟨352652, by rfl⟩ : syracuseStep 1880813 = 705305) (by norm_num)
theorem B1585909 : Blo 1252444 1585909 := bbase (se 5 (by rfl) ⟨74339, by rfl⟩ : syracuseStep 1585909 = 148679) (by norm_num)
theorem B4231925 : Blo 1252444 4231925 := bbase (se 5 (by rfl) ⟨198371, by rfl⟩ : syracuseStep 4231925 = 396743) (by norm_num)
theorem B6427397 : Blo 1252444 6427397 := bbase (se 4 (by rfl) ⟨602568, by rfl⟩ : syracuseStep 6427397 = 1205137) (by norm_num)
theorem B1880837 : Blo 1252444 1880837 := bbase (se 4 (by rfl) ⟨176328, by rfl⟩ : syracuseStep 1880837 = 352657) (by norm_num)
theorem B2380565 : Blo 1252444 2380565 := bbase (se 6 (by rfl) ⟨55794, by rfl⟩ : syracuseStep 2380565 = 111589) (by norm_num)
theorem B1880861 : Blo 1252444 1880861 := bbase (se 3 (by rfl) ⟨352661, by rfl⟩ : syracuseStep 1880861 = 705323) (by norm_num)
theorem B1880885 : Blo 1252444 1880885 := bbase (se 5 (by rfl) ⟨88166, by rfl⟩ : syracuseStep 1880885 = 176333) (by norm_num)
theorem B1880909 : Blo 1252444 1880909 := bbase (se 3 (by rfl) ⟨352670, by rfl⟩ : syracuseStep 1880909 = 705341) (by norm_num)
theorem B1880933 : Blo 1252444 1880933 := bbase (se 4 (by rfl) ⟨176337, by rfl⟩ : syracuseStep 1880933 = 352675) (by norm_num)
theorem B2257789 : Blo 1252444 2257789 := bbase (se 3 (by rfl) ⟨423335, by rfl⟩ : syracuseStep 2257789 = 846671) (by norm_num)
theorem B1880957 : Blo 1252444 1880957 := bbase (se 3 (by rfl) ⟨352679, by rfl⟩ : syracuseStep 1880957 = 705359) (by norm_num)
theorem B3175301 : Blo 1252444 3175301 := bbase (se 4 (by rfl) ⟨297684, by rfl⟩ : syracuseStep 3175301 = 595369) (by norm_num)
theorem B1880981 : Blo 1252444 1880981 := bbase (se 6 (by rfl) ⟨44085, by rfl⟩ : syracuseStep 1880981 = 88171) (by norm_num)
theorem B1586081 : Blo 1252444 1586081 := bbase (se 2 (by rfl) ⟨594780, by rfl⟩ : syracuseStep 1586081 = 1189561) (by norm_num)
theorem B1881005 : Blo 1252444 1881005 := bbase (se 3 (by rfl) ⟨352688, by rfl⟩ : syracuseStep 1881005 = 705377) (by norm_num)
theorem B4756421 : Blo 1252444 4756421 := bbase (se 4 (by rfl) ⟨445914, by rfl⟩ : syracuseStep 4756421 = 891829) (by norm_num)
theorem B1881029 : Blo 1252444 1881029 := bbase (se 4 (by rfl) ⟨176346, by rfl⟩ : syracuseStep 1881029 = 352693) (by norm_num)
theorem B1586137 : Blo 1252444 1586137 := bbase (se 2 (by rfl) ⟨594801, by rfl⟩ : syracuseStep 1586137 = 1189603) (by norm_num)
theorem B1881053 : Blo 1252444 1881053 := bbase (se 3 (by rfl) ⟨352697, by rfl⟩ : syracuseStep 1881053 = 705395) (by norm_num)
theorem B6345701 : Blo 1252444 6345701 := bbase (se 4 (by rfl) ⟨594909, by rfl⟩ : syracuseStep 6345701 = 1189819) (by norm_num)
theorem B2675693 : Blo 1252444 2675693 := bbase (se 3 (by rfl) ⟨501692, by rfl⟩ : syracuseStep 2675693 = 1003385) (by norm_num)
theorem B1881077 : Blo 1252444 1881077 := bbase (se 5 (by rfl) ⟨88175, by rfl⟩ : syracuseStep 1881077 = 176351) (by norm_num)
theorem B1881101 : Blo 1252444 1881101 := bbase (se 3 (by rfl) ⟨352706, by rfl⟩ : syracuseStep 1881101 = 705413) (by norm_num)
theorem B3568661 : Blo 1252444 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B4289557 : Blo 1252444 4289557 := bbase (se 6 (by rfl) ⟨100536, by rfl⟩ : syracuseStep 4289557 = 201073) (by norm_num)
theorem B1881125 : Blo 1252444 1881125 := bbase (se 4 (by rfl) ⟨176355, by rfl⟩ : syracuseStep 1881125 = 352711) (by norm_num)
theorem B2036773 : Blo 1252444 2036773 := bbase (se 4 (by rfl) ⟨190947, by rfl⟩ : syracuseStep 2036773 = 381895) (by norm_num)
theorem B2380853 : Blo 1252444 2380853 := bbase (se 5 (by rfl) ⟨111602, by rfl⟩ : syracuseStep 2380853 = 223205) (by norm_num)
theorem B1586233 : Blo 1252444 1586233 := bbase (se 2 (by rfl) ⟨594837, by rfl⟩ : syracuseStep 1586233 = 1189675) (by norm_num)
theorem B1881149 : Blo 1252444 1881149 := bbase (se 3 (by rfl) ⟨352715, by rfl⟩ : syracuseStep 1881149 = 705431) (by norm_num)
theorem B1881173 : Blo 1252444 1881173 := bbase (se 8 (by rfl) ⟨11022, by rfl⟩ : syracuseStep 1881173 = 22045) (by norm_num)
theorem B1881197 : Blo 1252444 1881197 := bbase (se 3 (by rfl) ⟨352724, by rfl⟩ : syracuseStep 1881197 = 705449) (by norm_num)
theorem B1881221 : Blo 1252444 1881221 := bbase (se 4 (by rfl) ⟨176364, by rfl⟩ : syracuseStep 1881221 = 352729) (by norm_num)
theorem B1881245 : Blo 1252444 1881245 := bbase (se 3 (by rfl) ⟨352733, by rfl⟩ : syracuseStep 1881245 = 705467) (by norm_num)
theorem B4232357 : Blo 1252444 4232357 := bbase (se 4 (by rfl) ⟨396783, by rfl⟩ : syracuseStep 4232357 = 793567) (by norm_num)
theorem B1881269 : Blo 1252444 1881269 := bbase (se 5 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 1881269 = 176369) (by norm_num)
theorem B2381005 : Blo 1252444 2381005 := bbase (se 3 (by rfl) ⟨446438, by rfl⟩ : syracuseStep 2381005 = 892877) (by norm_num)
theorem B1881293 : Blo 1252444 1881293 := bbase (se 3 (by rfl) ⟨352742, by rfl⟩ : syracuseStep 1881293 = 705485) (by norm_num)
theorem B1586405 : Blo 1252444 1586405 := bbase (se 4 (by rfl) ⟨148725, by rfl⟩ : syracuseStep 1586405 = 297451) (by norm_num)
theorem B1881317 : Blo 1252444 1881317 := bbase (se 4 (by rfl) ⟨176373, by rfl⟩ : syracuseStep 1881317 = 352747) (by norm_num)
theorem B1881341 : Blo 1252444 1881341 := bbase (se 3 (by rfl) ⟨352751, by rfl⟩ : syracuseStep 1881341 = 705503) (by norm_num)
theorem B3052813 : Blo 1252444 3052813 := bbase (se 3 (by rfl) ⟨572402, by rfl⟩ : syracuseStep 3052813 = 1144805) (by norm_num)
theorem B1881365 : Blo 1252444 1881365 := bbase (se 6 (by rfl) ⟨44094, by rfl⟩ : syracuseStep 1881365 = 88189) (by norm_num)
theorem B1586461 : Blo 1252444 1586461 := bbase (se 3 (by rfl) ⟨297461, by rfl⟩ : syracuseStep 1586461 = 594923) (by norm_num)
theorem B1881389 : Blo 1252444 1881389 := bbase (se 3 (by rfl) ⟨352760, by rfl⟩ : syracuseStep 1881389 = 705521) (by norm_num)
theorem B1881413 : Blo 1252444 1881413 := bbase (se 4 (by rfl) ⟨176382, by rfl⟩ : syracuseStep 1881413 = 352765) (by norm_num)
theorem B1881437 : Blo 1252444 1881437 := bbase (se 3 (by rfl) ⟨352769, by rfl⟩ : syracuseStep 1881437 = 705539) (by norm_num)
theorem B1881461 : Blo 1252444 1881461 := bbase (se 5 (by rfl) ⟨88193, by rfl⟩ : syracuseStep 1881461 = 176387) (by norm_num)
theorem B1586557 : Blo 1252444 1586557 := bbase (se 3 (by rfl) ⟨297479, by rfl⟩ : syracuseStep 1586557 = 594959) (by norm_num)
theorem B5428613 : Blo 1252444 5428613 := bbase (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) (by norm_num)
theorem B1881485 : Blo 1252444 1881485 := bbase (se 3 (by rfl) ⟨352778, by rfl⟩ : syracuseStep 1881485 = 705557) (by norm_num)
theorem B1881509 : Blo 1252444 1881509 := bbase (se 4 (by rfl) ⟨176391, by rfl⟩ : syracuseStep 1881509 = 352783) (by norm_num)
theorem B1881533 : Blo 1252444 1881533 := bbase (se 3 (by rfl) ⟨352787, by rfl⟩ : syracuseStep 1881533 = 705575) (by norm_num)
theorem B3569093 : Blo 1252444 3569093 := bbase (se 4 (by rfl) ⟨334602, by rfl⟩ : syracuseStep 3569093 = 669205) (by norm_num)
theorem B14464469 : Blo 1252444 14464469 := bbase (se 7 (by rfl) ⟨169505, by rfl⟩ : syracuseStep 14464469 = 339011) (by norm_num)
theorem B21419477 : Blo 1252444 21419477 := bbase (se 7 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 21419477 = 502019) (by norm_num)
theorem B1881557 : Blo 1252444 1881557 := bbase (se 7 (by rfl) ⟨22049, by rfl⟩ : syracuseStep 1881557 = 44099) (by norm_num)
theorem B1881581 : Blo 1252444 1881581 := bbase (se 3 (by rfl) ⟨352796, by rfl⟩ : syracuseStep 1881581 = 705593) (by norm_num)
theorem B2381309 : Blo 1252444 2381309 := bbase (se 3 (by rfl) ⟨446495, by rfl⟩ : syracuseStep 2381309 = 892991) (by norm_num)
theorem B1881605 : Blo 1252444 1881605 := bbase (se 4 (by rfl) ⟨176400, by rfl⟩ : syracuseStep 1881605 = 352801) (by norm_num)
theorem B1881629 : Blo 1252444 1881629 := bbase (se 3 (by rfl) ⟨352805, by rfl⟩ : syracuseStep 1881629 = 705611) (by norm_num)
theorem B1586729 : Blo 1252444 1586729 := bbase (se 2 (by rfl) ⟨595023, by rfl⟩ : syracuseStep 1586729 = 1190047) (by norm_num)
theorem B2856493 : Blo 1252444 2856493 := bbase (se 3 (by rfl) ⟨535592, by rfl⟩ : syracuseStep 2856493 = 1071185) (by norm_num)
theorem B1881653 : Blo 1252444 1881653 := bbase (se 5 (by rfl) ⟨88202, by rfl⟩ : syracuseStep 1881653 = 176405) (by norm_num)
theorem B4232789 : Blo 1252444 4232789 := bbase (se 8 (by rfl) ⟨24801, by rfl⟩ : syracuseStep 4232789 = 49603) (by norm_num)
theorem B1504861 : Blo 1252444 1504861 := bbase (se 3 (by rfl) ⟨282161, by rfl⟩ : syracuseStep 1504861 = 564323) (by norm_num)
theorem B1586785 : Blo 1252444 1586785 := bbase (se 2 (by rfl) ⟨595044, by rfl⟩ : syracuseStep 1586785 = 1190089) (by norm_num)
theorem B1783453 : Blo 1252444 1783453 := bbase (se 3 (by rfl) ⟨334397, by rfl⟩ : syracuseStep 1783453 = 668795) (by norm_num)
theorem B2258597 : Blo 1252444 2258597 := bbase (se 4 (by rfl) ⟨211743, by rfl⟩ : syracuseStep 2258597 = 423487) (by norm_num)
theorem B1586881 : Blo 1252444 1586881 := bbase (se 2 (by rfl) ⟨595080, by rfl⟩ : syracuseStep 1586881 = 1190161) (by norm_num)
theorem B1504981 : Blo 1252444 1504981 := bbase (se 7 (by rfl) ⟨17636, by rfl⟩ : syracuseStep 1504981 = 35273) (by norm_num)
theorem B8574677 : Blo 1252444 8574677 := bbase (se 7 (by rfl) ⟨100484, by rfl⟩ : syracuseStep 8574677 = 200969) (by norm_num)
theorem B3012365 : Blo 1252444 3012365 := bbase (se 3 (by rfl) ⟨564818, by rfl⟩ : syracuseStep 3012365 = 1129637) (by norm_num)
theorem B2258741 : Blo 1252444 2258741 := bbase (se 5 (by rfl) ⟨105878, by rfl⟩ : syracuseStep 2258741 = 211757) (by norm_num)
theorem B1718101 : Blo 1252444 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B2676581 : Blo 1252444 2676581 := bbase (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) (by norm_num)
theorem B1587053 : Blo 1252444 1587053 := bbase (se 3 (by rfl) ⟨297572, by rfl⟩ : syracuseStep 1587053 = 595145) (by norm_num)
theorem B2258813 : Blo 1252444 2258813 := bbase (se 3 (by rfl) ⟨423527, by rfl⟩ : syracuseStep 2258813 = 847055) (by norm_num)
theorem B1587109 : Blo 1252444 1587109 := bbase (se 4 (by rfl) ⟨148791, by rfl⟩ : syracuseStep 1587109 = 297583) (by norm_num)
theorem B2676701 : Blo 1252444 2676701 := bbase (se 3 (by rfl) ⟨501881, by rfl⟩ : syracuseStep 2676701 = 1003763) (by norm_num)
theorem B1587205 : Blo 1252444 1587205 := bbase (se 4 (by rfl) ⟨148800, by rfl⟩ : syracuseStep 1587205 = 297601) (by norm_num)
theorem B4233221 : Blo 1252444 4233221 := bbase (se 4 (by rfl) ⟨396864, by rfl⟩ : syracuseStep 4233221 = 793729) (by norm_num)
theorem B1783829 : Blo 1252444 1783829 := bbase (se 6 (by rfl) ⟨41808, by rfl⟩ : syracuseStep 1783829 = 83617) (by norm_num)
theorem B3012653 : Blo 1252444 3012653 := bbase (se 3 (by rfl) ⟨564872, by rfl⟩ : syracuseStep 3012653 = 1129745) (by norm_num)
theorem B2259029 : Blo 1252444 2259029 := bbase (se 8 (by rfl) ⟨13236, by rfl⟩ : syracuseStep 2259029 = 26473) (by norm_num)
theorem B1587377 : Blo 1252444 1587377 := bbase (se 2 (by rfl) ⟨595266, by rfl⟩ : syracuseStep 1587377 = 1190533) (by norm_num)
theorem B3569845 : Blo 1252444 3569845 := bbase (se 5 (by rfl) ⟨167336, by rfl⟩ : syracuseStep 3569845 = 334673) (by norm_num)
theorem B1587433 : Blo 1252444 1587433 := bbase (se 2 (by rfl) ⟨595287, by rfl⟩ : syracuseStep 1587433 = 1190575) (by norm_num)
theorem B6346997 : Blo 1252444 6346997 := bbase (se 5 (by rfl) ⟨297515, by rfl⟩ : syracuseStep 6346997 = 595031) (by norm_num)
theorem B9034037 : Blo 1252444 9034037 := bbase (se 5 (by rfl) ⟨423470, by rfl⟩ : syracuseStep 9034037 = 846941) (by norm_num)
theorem B1587529 : Blo 1252444 1587529 := bbase (se 2 (by rfl) ⟨595323, by rfl⟩ : syracuseStep 1587529 = 1190647) (by norm_num)
theorem B6863285 : Blo 1252444 6863285 := bbase (se 5 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 6863285 = 643433) (by norm_num)
theorem B4233653 : Blo 1252444 4233653 := bbase (se 5 (by rfl) ⟨198452, by rfl⟩ : syracuseStep 4233653 = 396905) (by norm_num)
theorem B1448381 : Blo 1252444 1448381 := bbase (se 3 (by rfl) ⟨271571, by rfl⟩ : syracuseStep 1448381 = 543143) (by norm_num)
theorem B6019541 : Blo 1252444 6019541 := bbase (se 7 (by rfl) ⟨70541, by rfl⟩ : syracuseStep 6019541 = 141083) (by norm_num)
theorem B7141877 : Blo 1252444 7141877 := bbase (se 5 (by rfl) ⟨334775, by rfl⟩ : syracuseStep 7141877 = 669551) (by norm_num)
theorem B1505837 : Blo 1252444 1505837 := bbase (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) (by norm_num)
theorem B3390005 : Blo 1252444 3390005 := bbase (se 5 (by rfl) ⟨158906, by rfl⟩ : syracuseStep 3390005 = 317813) (by norm_num)
theorem B2677333 : Blo 1252444 2677333 := bbase (se 8 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 2677333 = 31375) (by norm_num)
theorem B2259829 : Blo 1252444 2259829 := bbase (se 5 (by rfl) ⟨105929, by rfl⟩ : syracuseStep 2259829 = 211859) (by norm_num)
theorem B1694629 : Blo 1252444 1694629 := bbase (se 4 (by rfl) ⟨158871, by rfl⟩ : syracuseStep 1694629 = 317743) (by norm_num)
theorem B3218357 : Blo 1252444 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B4758533 : Blo 1252444 4758533 := bbase (se 4 (by rfl) ⟨446112, by rfl⟩ : syracuseStep 4758533 = 892225) (by norm_num)
theorem B4013077 : Blo 1252444 4013077 := bbase (se 6 (by rfl) ⟨94056, by rfl⟩ : syracuseStep 4013077 = 188113) (by norm_num)
theorem B2858053 : Blo 1252444 2858053 := bbase (se 4 (by rfl) ⟨267942, by rfl⟩ : syracuseStep 2858053 = 535885) (by norm_num)
theorem B18070613 : Blo 1252444 18070613 := bbase (se 8 (by rfl) ⟨105882, by rfl⟩ : syracuseStep 18070613 = 211765) (by norm_num)
theorem B2145421 : Blo 1252444 2145421 := bbase (se 3 (by rfl) ⟨402266, by rfl⟩ : syracuseStep 2145421 = 804533) (by norm_num)
theorem B1506557 : Blo 1252444 1506557 := bbase (se 3 (by rfl) ⟨282479, by rfl⟩ : syracuseStep 1506557 = 564959) (by norm_num)
theorem B4758821 : Blo 1252444 4758821 := bbase (se 4 (by rfl) ⟨446139, by rfl⟩ : syracuseStep 4758821 = 892279) (by norm_num)
theorem B5356853 : Blo 1252444 5356853 := bbase (se 5 (by rfl) ⟨251102, by rfl⟩ : syracuseStep 5356853 = 502205) (by norm_num)
theorem B5078389 : Blo 1252444 5078389 := bbase (se 5 (by rfl) ⟨238049, by rfl⟩ : syracuseStep 5078389 = 476099) (by norm_num)
theorem B1785253 : Blo 1252444 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B2678221 : Blo 1252444 2678221 := bbase (se 3 (by rfl) ⟨502166, by rfl⟩ : syracuseStep 2678221 = 1004333) (by norm_num)
theorem B5078533 : Blo 1252444 5078533 := bbase (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) (by norm_num)
theorem B6348293 : Blo 1252444 6348293 := bbase (se 4 (by rfl) ⟨595152, by rfl⟩ : syracuseStep 6348293 = 1190305) (by norm_num)
theorem B1506865 : Blo 1252444 1506865 := bbase (se 2 (by rfl) ⟨565074, by rfl⟩ : syracuseStep 1506865 = 1130149) (by norm_num)
theorem B2678341 : Blo 1252444 2678341 := bbase (se 4 (by rfl) ⟨251094, by rfl⟩ : syracuseStep 2678341 = 502189) (by norm_num)
theorem B6020693 : Blo 1252444 6020693 := bbase (se 8 (by rfl) ⟨35277, by rfl⟩ : syracuseStep 6020693 = 70555) (by norm_num)
theorem B1506961 : Blo 1252444 1506961 := bbase (se 2 (by rfl) ⟨565110, by rfl⟩ : syracuseStep 1506961 = 1130221) (by norm_num)
theorem B2064061 : Blo 1252444 2064061 := bbase (se 3 (by rfl) ⟨387011, by rfl⟩ : syracuseStep 2064061 = 774023) (by norm_num)
theorem B2678597 : Blo 1252444 2678597 := bbase (se 4 (by rfl) ⟨251118, by rfl⟩ : syracuseStep 2678597 = 502237) (by norm_num)
theorem B16064405 : Blo 1252444 16064405 := bbase (se 6 (by rfl) ⟨376509, by rfl⟩ : syracuseStep 16064405 = 753019) (by norm_num)
theorem B6340517 : Blo 1252444 6340517 := bbase (se 4 (by rfl) ⟨594423, by rfl⟩ : syracuseStep 6340517 = 1188847) (by norm_num)
theorem B2007013 : Blo 1252444 2007013 := bbase (se 4 (by rfl) ⟨188157, by rfl⟩ : syracuseStep 2007013 = 376315) (by norm_num)
theorem B3620837 : Blo 1252444 3620837 := bbase (se 4 (by rfl) ⟨339453, by rfl⟩ : syracuseStep 3620837 = 678907) (by norm_num)
theorem B1785845 : Blo 1252444 1785845 := bbase (se 5 (by rfl) ⟨83711, by rfl⟩ : syracuseStep 1785845 = 167423) (by norm_num)
theorem B1253379 : Blo 1252444 1253379 := bstep (se 1 (by rfl) ⟨940034, by rfl⟩ : syracuseStep 1253379 = 1880069) B1880069
theorem B2113553 : Blo 1252444 2113553 := bstep (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) B1585165
theorem B1253395 : Blo 1252444 1253395 := bstep (se 1 (by rfl) ⟨940046, by rfl⟩ : syracuseStep 1253395 = 1880093) B1880093
theorem B1253411 : Blo 1252444 1253411 := bstep (se 1 (by rfl) ⟨940058, by rfl⟩ : syracuseStep 1253411 = 1880117) B1880117
theorem B5357603 : Blo 1252444 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B2818097 : Blo 1252444 2818097 := bstep (se 2 (by rfl) ⟨1056786, by rfl⟩ : syracuseStep 2818097 = 2113573) B2113573
theorem B1253427 : Blo 1252444 1253427 := bstep (se 1 (by rfl) ⟨940070, by rfl⟩ : syracuseStep 1253427 = 1880141) B1880141
theorem B2818115 : Blo 1252444 2818115 := bstep (se 1 (by rfl) ⟨2113586, by rfl⟩ : syracuseStep 2818115 = 4227173) B4227173
theorem B1253443 : Blo 1252444 1253443 := bstep (se 1 (by rfl) ⟨940082, by rfl⟩ : syracuseStep 1253443 = 1880165) B1880165
theorem B1409107 : Blo 1252444 1409107 := bstep (se 1 (by rfl) ⟨1056830, by rfl⟩ : syracuseStep 1409107 = 2113661) B2113661
theorem B1253459 : Blo 1252444 1253459 := bstep (se 1 (by rfl) ⟨940094, by rfl⟩ : syracuseStep 1253459 = 1880189) B1880189
theorem B1253475 : Blo 1252444 1253475 := bstep (se 1 (by rfl) ⟨940106, by rfl⟩ : syracuseStep 1253475 = 1880213) B1880213
theorem B4014193 : Blo 1252444 4014193 := bstep (se 2 (by rfl) ⟨1505322, by rfl⟩ : syracuseStep 4014193 = 3010645) B3010645
theorem B91455601 : Blo 1252444 91455601 := bstep (se 2 (by rfl) ⟨34295850, by rfl⟩ : syracuseStep 91455601 = 68591701) B68591701
theorem B1253491 : Blo 1252444 1253491 := bstep (se 1 (by rfl) ⟨940118, by rfl⟩ : syracuseStep 1253491 = 1880237) B1880237
theorem B3809411 : Blo 1252444 3809411 := bstep (se 1 (by rfl) ⟨2857058, by rfl⟩ : syracuseStep 3809411 = 5714117) B5714117
theorem B1253507 : Blo 1252444 1253507 := bstep (se 1 (by rfl) ⟨940130, by rfl⟩ : syracuseStep 1253507 = 1880261) B1880261
theorem B3670147 : Blo 1252444 3670147 := bstep (se 1 (by rfl) ⟨2752610, by rfl⟩ : syracuseStep 3670147 = 5505221) B5505221
theorem B6348941 : Blo 1252444 6348941 := bstep (se 3 (by rfl) ⟨1190426, by rfl⟩ : syracuseStep 6348941 = 2380853) B2380853
theorem B2113681 : Blo 1252444 2113681 := bstep (se 2 (by rfl) ⟨792630, by rfl⟩ : syracuseStep 2113681 = 1585261) B1585261
theorem B1253523 : Blo 1252444 1253523 := bstep (se 1 (by rfl) ⟨940142, by rfl⟩ : syracuseStep 1253523 = 1880285) B1880285
theorem B1253539 : Blo 1252444 1253539 := bstep (se 1 (by rfl) ⟨940154, by rfl⟩ : syracuseStep 1253539 = 1880309) B1880309
theorem B2113715 : Blo 1252444 2113715 := bstep (se 1 (by rfl) ⟨1585286, by rfl⟩ : syracuseStep 2113715 = 3170573) B3170573
theorem B1253555 : Blo 1252444 1253555 := bstep (se 1 (by rfl) ⟨940166, by rfl⟩ : syracuseStep 1253555 = 1880333) B1880333
theorem B1253571 : Blo 1252444 1253571 := bstep (se 1 (by rfl) ⟨940178, by rfl⟩ : syracuseStep 1253571 = 1880357) B1880357
theorem B4227281 : Blo 1252444 4227281 := bstep (se 2 (by rfl) ⟨1585230, by rfl⟩ : syracuseStep 4227281 = 3170461) B3170461
theorem B2007251 : Blo 1252444 2007251 := bstep (se 1 (by rfl) ⟨1505438, by rfl⟩ : syracuseStep 2007251 = 3010877) B3010877
theorem B1253587 : Blo 1252444 1253587 := bstep (se 1 (by rfl) ⟨940190, by rfl⟩ : syracuseStep 1253587 = 1880381) B1880381
theorem B1409251 : Blo 1252444 1409251 := bstep (se 1 (by rfl) ⟨1056938, by rfl⟩ : syracuseStep 1409251 = 2113877) B2113877
theorem B4014307 : Blo 1252444 4014307 := bstep (se 1 (by rfl) ⟨3010730, by rfl⟩ : syracuseStep 4014307 = 6021461) B6021461
theorem B1253603 : Blo 1252444 1253603 := bstep (se 1 (by rfl) ⟨940202, by rfl⟩ : syracuseStep 1253603 = 1880405) B1880405
theorem B17400035 : Blo 1252444 17400035 := bstep (se 1 (by rfl) ⟨13050026, by rfl⟩ : syracuseStep 17400035 = 26100053) B26100053
theorem B4759793 : Blo 1252444 4759793 := bstep (se 2 (by rfl) ⟨1784922, by rfl⟩ : syracuseStep 4759793 = 3569845) B3569845
theorem B1253619 : Blo 1252444 1253619 := bstep (se 1 (by rfl) ⟨940214, by rfl⟩ : syracuseStep 1253619 = 1880429) B1880429
theorem B1253635 : Blo 1252444 1253635 := bstep (se 1 (by rfl) ⟨940226, by rfl⟩ : syracuseStep 1253635 = 1880453) B1880453
theorem B6103309 : Blo 1252444 6103309 := bstep (se 3 (by rfl) ⟨1144370, by rfl⟩ : syracuseStep 6103309 = 2288741) B2288741
theorem B1253651 : Blo 1252444 1253651 := bstep (se 1 (by rfl) ⟨940238, by rfl⟩ : syracuseStep 1253651 = 1880477) B1880477
theorem B1253667 : Blo 1252444 1253667 := bstep (se 1 (by rfl) ⟨940250, by rfl⟩ : syracuseStep 1253667 = 1880501) B1880501
theorem B2113843 : Blo 1252444 2113843 := bstep (se 1 (by rfl) ⟨1585382, by rfl⟩ : syracuseStep 2113843 = 3170765) B3170765
theorem B1253683 : Blo 1252444 1253683 := bstep (se 1 (by rfl) ⟨940262, by rfl⟩ : syracuseStep 1253683 = 1880525) B1880525
theorem B1253699 : Blo 1252444 1253699 := bstep (se 1 (by rfl) ⟨940274, by rfl⟩ : syracuseStep 1253699 = 1880549) B1880549
theorem B2818385 : Blo 1252444 2818385 := bstep (se 2 (by rfl) ⟨1056894, by rfl⟩ : syracuseStep 2818385 = 2113789) B2113789
theorem B1253715 : Blo 1252444 1253715 := bstep (se 1 (by rfl) ⟨940286, by rfl⟩ : syracuseStep 1253715 = 1880573) B1880573
theorem B2818403 : Blo 1252444 2818403 := bstep (se 1 (by rfl) ⟨2113802, by rfl⟩ : syracuseStep 2818403 = 4227605) B4227605
theorem B10854755 : Blo 1252444 10854755 := bstep (se 1 (by rfl) ⟨8141066, by rfl⟩ : syracuseStep 10854755 = 16282133) B16282133
theorem B1253731 : Blo 1252444 1253731 := bstep (se 1 (by rfl) ⟨940298, by rfl⟩ : syracuseStep 1253731 = 1880597) B1880597
theorem B4071779 : Blo 1252444 4071779 := bstep (se 1 (by rfl) ⟨3053834, by rfl⟩ : syracuseStep 4071779 = 6107669) B6107669
theorem B1409395 : Blo 1252444 1409395 := bstep (se 1 (by rfl) ⟨1057046, by rfl⟩ : syracuseStep 1409395 = 2114093) B2114093
theorem B1253747 : Blo 1252444 1253747 := bstep (se 1 (by rfl) ⟨940310, by rfl⟩ : syracuseStep 1253747 = 1880621) B1880621
theorem B1253763 : Blo 1252444 1253763 := bstep (se 1 (by rfl) ⟨940322, by rfl⟩ : syracuseStep 1253763 = 1880645) B1880645
theorem B1253779 : Blo 1252444 1253779 := bstep (se 1 (by rfl) ⟨940334, by rfl⟩ : syracuseStep 1253779 = 1880669) B1880669
theorem B1253795 : Blo 1252444 1253795 := bstep (se 1 (by rfl) ⟨940346, by rfl⟩ : syracuseStep 1253795 = 1880693) B1880693
theorem B1253811 : Blo 1252444 1253811 := bstep (se 1 (by rfl) ⟨940358, by rfl⟩ : syracuseStep 1253811 = 1880717) B1880717
theorem B2113985 : Blo 1252444 2113985 := bstep (se 2 (by rfl) ⟨792744, by rfl⟩ : syracuseStep 2113985 = 1585489) B1585489
theorem B1253827 : Blo 1252444 1253827 := bstep (se 1 (by rfl) ⟨940370, by rfl⟩ : syracuseStep 1253827 = 1880741) B1880741
theorem B1253843 : Blo 1252444 1253843 := bstep (se 1 (by rfl) ⟨940382, by rfl⟩ : syracuseStep 1253843 = 1880765) B1880765
theorem B1253859 : Blo 1252444 1253859 := bstep (se 1 (by rfl) ⟨940394, by rfl⟩ : syracuseStep 1253859 = 1880789) B1880789
theorem B1253875 : Blo 1252444 1253875 := bstep (se 1 (by rfl) ⟨940406, by rfl⟩ : syracuseStep 1253875 = 1880813) B1880813
theorem B1409539 : Blo 1252444 1409539 := bstep (se 1 (by rfl) ⟨1057154, by rfl⟩ : syracuseStep 1409539 = 2114309) B2114309
theorem B1253891 : Blo 1252444 1253891 := bstep (se 1 (by rfl) ⟨940418, by rfl⟩ : syracuseStep 1253891 = 1880837) B1880837
theorem B1253907 : Blo 1252444 1253907 := bstep (se 1 (by rfl) ⟨940430, by rfl⟩ : syracuseStep 1253907 = 1880861) B1880861
theorem B1253923 : Blo 1252444 1253923 := bstep (se 1 (by rfl) ⟨940442, by rfl⟩ : syracuseStep 1253923 = 1880885) B1880885
theorem B1253939 : Blo 1252444 1253939 := bstep (se 1 (by rfl) ⟨940454, by rfl⟩ : syracuseStep 1253939 = 1880909) B1880909
theorem B2114113 : Blo 1252444 2114113 := bstep (se 2 (by rfl) ⟨792792, by rfl⟩ : syracuseStep 2114113 = 1585585) B1585585
theorem B1253955 : Blo 1252444 1253955 := bstep (se 1 (by rfl) ⟨940466, by rfl⟩ : syracuseStep 1253955 = 1880933) B1880933
theorem B3170897 : Blo 1252444 3170897 := bstep (se 2 (by rfl) ⟨1189086, by rfl⟩ : syracuseStep 3170897 = 2378173) B2378173
theorem B1253971 : Blo 1252444 1253971 := bstep (se 1 (by rfl) ⟨940478, by rfl⟩ : syracuseStep 1253971 = 1880957) B1880957
theorem B2114147 : Blo 1252444 2114147 := bstep (se 1 (by rfl) ⟨1585610, by rfl⟩ : syracuseStep 2114147 = 3171221) B3171221
theorem B1253987 : Blo 1252444 1253987 := bstep (se 1 (by rfl) ⟨940490, by rfl⟩ : syracuseStep 1253987 = 1880981) B1880981
theorem B2818673 : Blo 1252444 2818673 := bstep (se 2 (by rfl) ⟨1057002, by rfl⟩ : syracuseStep 2818673 = 2114005) B2114005
theorem B1507955 : Blo 1252444 1507955 := bstep (se 1 (by rfl) ⟨1130966, by rfl⟩ : syracuseStep 1507955 = 2261933) B2261933
theorem B1254003 : Blo 1252444 1254003 := bstep (se 1 (by rfl) ⟨940502, by rfl⟩ : syracuseStep 1254003 = 1881005) B1881005
theorem B3170947 : Blo 1252444 3170947 := bstep (se 1 (by rfl) ⟨2378210, by rfl⟩ : syracuseStep 3170947 = 4756421) B4756421
theorem B2818691 : Blo 1252444 2818691 := bstep (se 1 (by rfl) ⟨2114018, by rfl⟩ : syracuseStep 2818691 = 4228037) B4228037
theorem B1254019 : Blo 1252444 1254019 := bstep (se 1 (by rfl) ⟨940514, by rfl⟩ : syracuseStep 1254019 = 1881029) B1881029
theorem B1409683 : Blo 1252444 1409683 := bstep (se 1 (by rfl) ⟨1057262, by rfl⟩ : syracuseStep 1409683 = 2114525) B2114525
theorem B1254035 : Blo 1252444 1254035 := bstep (se 1 (by rfl) ⟨940526, by rfl⟩ : syracuseStep 1254035 = 1881053) B1881053
theorem B1254051 : Blo 1252444 1254051 := bstep (se 1 (by rfl) ⟨940538, by rfl⟩ : syracuseStep 1254051 = 1881077) B1881077
theorem B1254067 : Blo 1252444 1254067 := bstep (se 1 (by rfl) ⟨940550, by rfl⟩ : syracuseStep 1254067 = 1881101) B1881101
theorem B1254083 : Blo 1252444 1254083 := bstep (se 1 (by rfl) ⟨940562, by rfl⟩ : syracuseStep 1254083 = 1881125) B1881125
theorem B1254099 : Blo 1252444 1254099 := bstep (se 1 (by rfl) ⟨940574, by rfl⟩ : syracuseStep 1254099 = 1881149) B1881149
theorem B2114275 : Blo 1252444 2114275 := bstep (se 1 (by rfl) ⟨1585706, by rfl⟩ : syracuseStep 2114275 = 3171413) B3171413
theorem B1254115 : Blo 1252444 1254115 := bstep (se 1 (by rfl) ⟨940586, by rfl⟩ : syracuseStep 1254115 = 1881173) B1881173
theorem B4227821 : Blo 1252444 4227821 := bstep (se 3 (by rfl) ⟨792716, by rfl⟩ : syracuseStep 4227821 = 1585433) B1585433
theorem B8569585 : Blo 1252444 8569585 := bstep (se 2 (by rfl) ⟨3213594, by rfl⟩ : syracuseStep 8569585 = 6427189) B6427189
theorem B1254131 : Blo 1252444 1254131 := bstep (se 1 (by rfl) ⟨940598, by rfl⟩ : syracuseStep 1254131 = 1881197) B1881197
theorem B1254147 : Blo 1252444 1254147 := bstep (se 1 (by rfl) ⟨940610, by rfl⟩ : syracuseStep 1254147 = 1881221) B1881221
theorem B3171089 : Blo 1252444 3171089 := bstep (se 2 (by rfl) ⟨1189158, by rfl⟩ : syracuseStep 3171089 = 2378317) B2378317
theorem B1254163 : Blo 1252444 1254163 := bstep (se 1 (by rfl) ⟨940622, by rfl⟩ : syracuseStep 1254163 = 1881245) B1881245
theorem B4227875 : Blo 1252444 4227875 := bstep (se 1 (by rfl) ⟨3170906, by rfl⟩ : syracuseStep 4227875 = 6341813) B6341813
theorem B1409827 : Blo 1252444 1409827 := bstep (se 1 (by rfl) ⟨1057370, by rfl⟩ : syracuseStep 1409827 = 2114741) B2114741
theorem B1254179 : Blo 1252444 1254179 := bstep (se 1 (by rfl) ⟨940634, by rfl⟩ : syracuseStep 1254179 = 1881269) B1881269
theorem B1254195 : Blo 1252444 1254195 := bstep (se 1 (by rfl) ⟨940646, by rfl⟩ : syracuseStep 1254195 = 1881293) B1881293
theorem B1254211 : Blo 1252444 1254211 := bstep (se 1 (by rfl) ⟨940658, by rfl⟩ : syracuseStep 1254211 = 1881317) B1881317
theorem B1254227 : Blo 1252444 1254227 := bstep (se 1 (by rfl) ⟨940670, by rfl⟩ : syracuseStep 1254227 = 1881341) B1881341
theorem B1254243 : Blo 1252444 1254243 := bstep (se 1 (by rfl) ⟨940682, by rfl⟩ : syracuseStep 1254243 = 1881365) B1881365
theorem B6341489 : Blo 1252444 6341489 := bstep (se 2 (by rfl) ⟨2378058, by rfl⟩ : syracuseStep 6341489 = 4756117) B4756117
theorem B2114417 : Blo 1252444 2114417 := bstep (se 2 (by rfl) ⟨792906, by rfl⟩ : syracuseStep 2114417 = 1585813) B1585813
theorem B1254259 : Blo 1252444 1254259 := bstep (se 1 (by rfl) ⟨940694, by rfl⟩ : syracuseStep 1254259 = 1881389) B1881389
theorem B1254275 : Blo 1252444 1254275 := bstep (se 1 (by rfl) ⟨940706, by rfl⟩ : syracuseStep 1254275 = 1881413) B1881413
theorem B2818961 : Blo 1252444 2818961 := bstep (se 2 (by rfl) ⟨1057110, by rfl⟩ : syracuseStep 2818961 = 2114221) B2114221
theorem B1254291 : Blo 1252444 1254291 := bstep (se 1 (by rfl) ⟨940718, by rfl⟩ : syracuseStep 1254291 = 1881437) B1881437
theorem B2818979 : Blo 1252444 2818979 := bstep (se 1 (by rfl) ⟨2114234, by rfl⟩ : syracuseStep 2818979 = 4228469) B4228469
theorem B1254307 : Blo 1252444 1254307 := bstep (se 1 (by rfl) ⟨940730, by rfl⟩ : syracuseStep 1254307 = 1881461) B1881461
theorem B4015025 : Blo 1252444 4015025 := bstep (se 2 (by rfl) ⟨1505634, by rfl⟩ : syracuseStep 4015025 = 3011269) B3011269
theorem B1409971 : Blo 1252444 1409971 := bstep (se 1 (by rfl) ⟨1057478, by rfl⟩ : syracuseStep 1409971 = 2114957) B2114957
theorem B1254323 : Blo 1252444 1254323 := bstep (se 1 (by rfl) ⟨940742, by rfl⟩ : syracuseStep 1254323 = 1881485) B1881485
theorem B1254339 : Blo 1252444 1254339 := bstep (se 1 (by rfl) ⟨940754, by rfl⟩ : syracuseStep 1254339 = 1881509) B1881509
theorem B1254355 : Blo 1252444 1254355 := bstep (se 1 (by rfl) ⟨940766, by rfl⟩ : syracuseStep 1254355 = 1881533) B1881533
theorem B9642979 : Blo 1252444 9642979 := bstep (se 1 (by rfl) ⟨7232234, by rfl⟩ : syracuseStep 9642979 = 14464469) B14464469
theorem B14279651 : Blo 1252444 14279651 := bstep (se 1 (by rfl) ⟨10709738, by rfl⟩ : syracuseStep 14279651 = 21419477) B21419477
theorem B1254371 : Blo 1252444 1254371 := bstep (se 1 (by rfl) ⟨940778, by rfl⟩ : syracuseStep 1254371 = 1881557) B1881557
theorem B2114545 : Blo 1252444 2114545 := bstep (se 2 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 2114545 = 1585909) B1585909
theorem B1254387 : Blo 1252444 1254387 := bstep (se 1 (by rfl) ⟨940790, by rfl⟩ : syracuseStep 1254387 = 1881581) B1881581
theorem B1254403 : Blo 1252444 1254403 := bstep (se 1 (by rfl) ⟨940802, by rfl⟩ : syracuseStep 1254403 = 1881605) B1881605
theorem B2114579 : Blo 1252444 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B1254419 : Blo 1252444 1254419 := bstep (se 1 (by rfl) ⟨940814, by rfl⟩ : syracuseStep 1254419 = 1881629) B1881629
theorem B1254435 : Blo 1252444 1254435 := bstep (se 1 (by rfl) ⟨940826, by rfl⟩ : syracuseStep 1254435 = 1881653) B1881653
theorem B4228145 : Blo 1252444 4228145 := bstep (se 2 (by rfl) ⟨1585554, by rfl⟩ : syracuseStep 4228145 = 3171109) B3171109
theorem B1410115 : Blo 1252444 1410115 := bstep (se 1 (by rfl) ⟨1057586, by rfl⟩ : syracuseStep 1410115 = 2115173) B2115173
theorem B2114707 : Blo 1252444 2114707 := bstep (se 1 (by rfl) ⟨1586030, by rfl⟩ : syracuseStep 2114707 = 3172061) B3172061
theorem B2819249 : Blo 1252444 2819249 := bstep (se 2 (by rfl) ⟨1057218, by rfl⟩ : syracuseStep 2819249 = 2114437) B2114437
theorem B2008243 : Blo 1252444 2008243 := bstep (se 1 (by rfl) ⟨1506182, by rfl⟩ : syracuseStep 2008243 = 3012365) B3012365
theorem B2819267 : Blo 1252444 2819267 := bstep (se 1 (by rfl) ⟨2114450, by rfl⟩ : syracuseStep 2819267 = 4228901) B4228901
theorem B1410259 : Blo 1252444 1410259 := bstep (se 1 (by rfl) ⟨1057694, by rfl⟩ : syracuseStep 1410259 = 2115389) B2115389
theorem B2114849 : Blo 1252444 2114849 := bstep (se 2 (by rfl) ⟨793068, by rfl⟩ : syracuseStep 2114849 = 1586137) B1586137
theorem B1410403 : Blo 1252444 1410403 := bstep (se 1 (by rfl) ⟨1057802, by rfl⟩ : syracuseStep 1410403 = 2115605) B2115605
theorem B5350769 : Blo 1252444 5350769 := bstep (se 2 (by rfl) ⟨2006538, by rfl⟩ : syracuseStep 5350769 = 4013077) B4013077
theorem B5719409 : Blo 1252444 5719409 := bstep (se 2 (by rfl) ⟨2144778, by rfl⟩ : syracuseStep 5719409 = 4289557) B4289557
theorem B2114977 : Blo 1252444 2114977 := bstep (se 2 (by rfl) ⟨793116, by rfl⟩ : syracuseStep 2114977 = 1586233) B1586233
theorem B5293475 : Blo 1252444 5293475 := bstep (se 1 (by rfl) ⟨3970106, by rfl⟩ : syracuseStep 5293475 = 7940213) B7940213
theorem B3810737 : Blo 1252444 3810737 := bstep (se 2 (by rfl) ⟨1429026, by rfl⟩ : syracuseStep 3810737 = 2858053) B2858053
theorem B2115011 : Blo 1252444 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B4015565 : Blo 1252444 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B2819537 : Blo 1252444 2819537 := bstep (se 2 (by rfl) ⟨1057326, by rfl⟩ : syracuseStep 2819537 = 2114653) B2114653
theorem B2819555 : Blo 1252444 2819555 := bstep (se 1 (by rfl) ⟨2114666, by rfl⟩ : syracuseStep 2819555 = 4229333) B4229333
theorem B1410547 : Blo 1252444 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B2860561 : Blo 1252444 2860561 := bstep (se 2 (by rfl) ⟨1072710, by rfl⟩ : syracuseStep 2860561 = 2145421) B2145421
theorem B6022691 : Blo 1252444 6022691 := bstep (se 1 (by rfl) ⟨4517018, by rfl⟩ : syracuseStep 6022691 = 9034037) B9034037
theorem B15238709 : Blo 1252444 15238709 := bstep (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) B1428629
theorem B2115139 : Blo 1252444 2115139 := bstep (se 1 (by rfl) ⟨1586354, by rfl⟩ : syracuseStep 2115139 = 3172709) B3172709
theorem B4228685 : Blo 1252444 4228685 := bstep (se 3 (by rfl) ⟨792878, by rfl⟩ : syracuseStep 4228685 = 1585757) B1585757
theorem B9520739 : Blo 1252444 9520739 := bstep (se 1 (by rfl) ⟨7140554, by rfl⟩ : syracuseStep 9520739 = 14281109) B14281109
theorem B4228739 : Blo 1252444 4228739 := bstep (se 1 (by rfl) ⟨3171554, by rfl⟩ : syracuseStep 4228739 = 6343109) B6343109
theorem B1410691 : Blo 1252444 1410691 := bstep (se 1 (by rfl) ⟨1058018, by rfl⟩ : syracuseStep 1410691 = 2116037) B2116037
theorem B4761251 : Blo 1252444 4761251 := bstep (se 1 (by rfl) ⟨3570938, by rfl⟩ : syracuseStep 4761251 = 7141877) B7141877
theorem B2115281 : Blo 1252444 2115281 := bstep (se 2 (by rfl) ⟨793230, by rfl⟩ : syracuseStep 2115281 = 1586461) B1586461
theorem B3172081 : Blo 1252444 3172081 := bstep (se 2 (by rfl) ⟨1189530, by rfl⟩ : syracuseStep 3172081 = 2379061) B2379061
theorem B2819825 : Blo 1252444 2819825 := bstep (se 2 (by rfl) ⟨1057434, by rfl⟩ : syracuseStep 2819825 = 2114869) B2114869
theorem B2819843 : Blo 1252444 2819843 := bstep (se 1 (by rfl) ⟨2114882, by rfl⟩ : syracuseStep 2819843 = 4229765) B4229765
theorem B1410835 : Blo 1252444 1410835 := bstep (se 1 (by rfl) ⟨1058126, by rfl⟩ : syracuseStep 1410835 = 2116253) B2116253
theorem B2115409 : Blo 1252444 2115409 := bstep (se 2 (by rfl) ⟨793278, by rfl⟩ : syracuseStep 2115409 = 1586557) B1586557
theorem B19302257 : Blo 1252444 19302257 := bstep (se 2 (by rfl) ⟨7238346, by rfl⟩ : syracuseStep 19302257 = 14476693) B14476693
theorem B2115443 : Blo 1252444 2115443 := bstep (se 1 (by rfl) ⟨1586582, by rfl⟩ : syracuseStep 2115443 = 3173165) B3173165
theorem B4229009 : Blo 1252444 4229009 := bstep (se 2 (by rfl) ⟨1585878, by rfl⟩ : syracuseStep 4229009 = 3171757) B3171757
theorem B8144803 : Blo 1252444 8144803 := bstep (se 1 (by rfl) ⟨6108602, by rfl⟩ : syracuseStep 8144803 = 12217205) B12217205
theorem B1410979 : Blo 1252444 1410979 := bstep (se 1 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 1410979 = 2116469) B2116469
theorem B12052421 : Blo 1252444 12052421 := bstep (se 4 (by rfl) ⟨1129914, by rfl⟩ : syracuseStep 12052421 = 2259829) B2259829
theorem B6023153 : Blo 1252444 6023153 := bstep (se 2 (by rfl) ⟨2258682, by rfl⟩ : syracuseStep 6023153 = 4517365) B4517365
theorem B2115571 : Blo 1252444 2115571 := bstep (se 1 (by rfl) ⟨1586678, by rfl⟩ : syracuseStep 2115571 = 3173357) B3173357
theorem B3172355 : Blo 1252444 3172355 := bstep (se 1 (by rfl) ⟨2379266, by rfl⟩ : syracuseStep 3172355 = 4758533) B4758533
theorem B17139725 : Blo 1252444 17139725 := bstep (se 3 (by rfl) ⟨3213698, by rfl⟩ : syracuseStep 17139725 = 6427397) B6427397
theorem B2820113 : Blo 1252444 2820113 := bstep (se 2 (by rfl) ⟨1057542, by rfl⟩ : syracuseStep 2820113 = 2115085) B2115085
theorem B2820131 : Blo 1252444 2820131 := bstep (se 1 (by rfl) ⟨2115098, by rfl⟩ : syracuseStep 2820131 = 4230197) B4230197
theorem B1411123 : Blo 1252444 1411123 := bstep (se 1 (by rfl) ⟨1058342, by rfl⟩ : syracuseStep 1411123 = 2116685) B2116685
theorem B2009153 : Blo 1252444 2009153 := bstep (se 2 (by rfl) ⟨753432, by rfl⟩ : syracuseStep 2009153 = 1506865) B1506865
theorem B2115713 : Blo 1252444 2115713 := bstep (se 2 (by rfl) ⟨793392, by rfl⟩ : syracuseStep 2115713 = 1586785) B1586785
theorem B3172547 : Blo 1252444 3172547 := bstep (se 1 (by rfl) ⟨2379410, by rfl⟩ : syracuseStep 3172547 = 4758821) B4758821
theorem B2009281 : Blo 1252444 2009281 := bstep (se 2 (by rfl) ⟨753480, by rfl⟩ : syracuseStep 2009281 = 1506961) B1506961
theorem B2377937 : Blo 1252444 2377937 := bstep (se 2 (by rfl) ⟨891726, by rfl⟩ : syracuseStep 2377937 = 1783453) B1783453
theorem B2115841 : Blo 1252444 2115841 := bstep (se 2 (by rfl) ⟨793440, by rfl⟩ : syracuseStep 2115841 = 1586881) B1586881
theorem B6342947 : Blo 1252444 6342947 := bstep (se 1 (by rfl) ⟨4757210, by rfl⟩ : syracuseStep 6342947 = 9514421) B9514421
theorem B2115875 : Blo 1252444 2115875 := bstep (se 1 (by rfl) ⟨1586906, by rfl⟩ : syracuseStep 2115875 = 3173813) B3173813
theorem B2820401 : Blo 1252444 2820401 := bstep (se 2 (by rfl) ⟨1057650, by rfl⟩ : syracuseStep 2820401 = 2115301) B2115301
theorem B2820419 : Blo 1252444 2820419 := bstep (se 1 (by rfl) ⟨2115314, by rfl⟩ : syracuseStep 2820419 = 4230629) B4230629
theorem B2116003 : Blo 1252444 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B4229549 : Blo 1252444 4229549 := bstep (se 3 (by rfl) ⟨793040, by rfl⟩ : syracuseStep 4229549 = 1586081) B1586081
theorem B4229603 : Blo 1252444 4229603 := bstep (se 1 (by rfl) ⟨3172202, by rfl⟩ : syracuseStep 4229603 = 6344405) B6344405
theorem B2116145 : Blo 1252444 2116145 := bstep (se 2 (by rfl) ⟨793554, by rfl⟩ : syracuseStep 2116145 = 1587109) B1587109
theorem B2820689 : Blo 1252444 2820689 := bstep (se 2 (by rfl) ⟨1057758, by rfl⟩ : syracuseStep 2820689 = 2115517) B2115517
theorem B3213923 : Blo 1252444 3213923 := bstep (se 1 (by rfl) ⟨2410442, by rfl⟩ : syracuseStep 3213923 = 4820885) B4820885
theorem B10709603 : Blo 1252444 10709603 := bstep (se 1 (by rfl) ⟨8032202, by rfl⟩ : syracuseStep 10709603 = 16064405) B16064405
theorem B2820707 : Blo 1252444 2820707 := bstep (se 1 (by rfl) ⟨2115530, by rfl⟩ : syracuseStep 2820707 = 4231061) B4231061
theorem B4762253 : Blo 1252444 4762253 := bstep (se 3 (by rfl) ⟨892922, by rfl⟩ : syracuseStep 4762253 = 1785845) B1785845
theorem B1878689 : Blo 1252444 1878689 := bstep (se 2 (by rfl) ⟨704508, by rfl⟩ : syracuseStep 1878689 = 1409017) B1409017
theorem B2116273 : Blo 1252444 2116273 := bstep (se 2 (by rfl) ⟨793602, by rfl⟩ : syracuseStep 2116273 = 1587205) B1587205
theorem B1878707 : Blo 1252444 1878707 := bstep (se 1 (by rfl) ⟨1409030, by rfl⟩ : syracuseStep 1878707 = 2818061) B2818061
theorem B1878737 : Blo 1252444 1878737 := bstep (se 2 (by rfl) ⟨704526, by rfl⟩ : syracuseStep 1878737 = 1409053) B1409053
theorem B2116307 : Blo 1252444 2116307 := bstep (se 1 (by rfl) ⟨1587230, by rfl⟩ : syracuseStep 2116307 = 3174461) B3174461
theorem B1878755 : Blo 1252444 1878755 := bstep (se 1 (by rfl) ⟨1409066, by rfl⟩ : syracuseStep 1878755 = 2818133) B2818133
theorem B4229873 : Blo 1252444 4229873 := bstep (se 2 (by rfl) ⟨1586202, by rfl⟩ : syracuseStep 4229873 = 3172405) B3172405
theorem B1878785 : Blo 1252444 1878785 := bstep (se 2 (by rfl) ⟨704544, by rfl⟩ : syracuseStep 1878785 = 1409089) B1409089
theorem B1878803 : Blo 1252444 1878803 := bstep (se 1 (by rfl) ⟨1409102, by rfl⟩ : syracuseStep 1878803 = 2818205) B2818205
theorem B1878833 : Blo 1252444 1878833 := bstep (se 2 (by rfl) ⟨704562, by rfl⟩ : syracuseStep 1878833 = 1409125) B1409125
theorem B1878851 : Blo 1252444 1878851 := bstep (se 1 (by rfl) ⟨1409138, by rfl⟩ : syracuseStep 1878851 = 2818277) B2818277
theorem B2116435 : Blo 1252444 2116435 := bstep (se 1 (by rfl) ⟨1587326, by rfl⟩ : syracuseStep 2116435 = 3174653) B3174653
theorem B1878881 : Blo 1252444 1878881 := bstep (se 2 (by rfl) ⟨704580, by rfl⟩ : syracuseStep 1878881 = 1409161) B1409161
theorem B2820977 : Blo 1252444 2820977 := bstep (se 2 (by rfl) ⟨1057866, by rfl⟩ : syracuseStep 2820977 = 2115733) B2115733
theorem B1878899 : Blo 1252444 1878899 := bstep (se 1 (by rfl) ⟨1409174, by rfl⟩ : syracuseStep 1878899 = 2818349) B2818349
theorem B2820995 : Blo 1252444 2820995 := bstep (se 1 (by rfl) ⟨2115746, by rfl⟩ : syracuseStep 2820995 = 4231493) B4231493
theorem B6024077 : Blo 1252444 6024077 := bstep (se 3 (by rfl) ⟨1129514, by rfl⟩ : syracuseStep 6024077 = 2259029) B2259029
theorem B1878929 : Blo 1252444 1878929 := bstep (se 2 (by rfl) ⟨704598, by rfl⟩ : syracuseStep 1878929 = 1409197) B1409197
theorem B1878947 : Blo 1252444 1878947 := bstep (se 1 (by rfl) ⟨1409210, by rfl⟩ : syracuseStep 1878947 = 2818421) B2818421
theorem B2378659 : Blo 1252444 2378659 := bstep (se 1 (by rfl) ⟨1783994, by rfl⟩ : syracuseStep 2378659 = 3567989) B3567989
theorem B1878977 : Blo 1252444 1878977 := bstep (se 2 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 1878977 = 1409233) B1409233
theorem B1878995 : Blo 1252444 1878995 := bstep (se 1 (by rfl) ⟨1409246, by rfl⟩ : syracuseStep 1878995 = 2818493) B2818493
theorem B2116577 : Blo 1252444 2116577 := bstep (se 2 (by rfl) ⟨793716, by rfl⟩ : syracuseStep 2116577 = 1587433) B1587433
theorem B1879025 : Blo 1252444 1879025 := bstep (se 2 (by rfl) ⟨704634, by rfl⟩ : syracuseStep 1879025 = 1409269) B1409269
theorem B1879043 : Blo 1252444 1879043 := bstep (se 1 (by rfl) ⟨1409282, by rfl⟩ : syracuseStep 1879043 = 2818565) B2818565
theorem B1879073 : Blo 1252444 1879073 := bstep (se 2 (by rfl) ⟨704652, by rfl⟩ : syracuseStep 1879073 = 1409305) B1409305
theorem B1879091 : Blo 1252444 1879091 := bstep (se 1 (by rfl) ⟨1409318, by rfl⟩ : syracuseStep 1879091 = 2818637) B2818637
theorem B6343757 : Blo 1252444 6343757 := bstep (se 3 (by rfl) ⟨1189454, by rfl⟩ : syracuseStep 6343757 = 2378909) B2378909
theorem B3812429 : Blo 1252444 3812429 := bstep (se 3 (by rfl) ⟨714830, by rfl⟩ : syracuseStep 3812429 = 1429661) B1429661
theorem B1879121 : Blo 1252444 1879121 := bstep (se 2 (by rfl) ⟨704670, by rfl⟩ : syracuseStep 1879121 = 1409341) B1409341
theorem B2116705 : Blo 1252444 2116705 := bstep (se 2 (by rfl) ⟨793764, by rfl⟩ : syracuseStep 2116705 = 1587529) B1587529
theorem B1879139 : Blo 1252444 1879139 := bstep (se 1 (by rfl) ⟨1409354, by rfl⟩ : syracuseStep 1879139 = 2818709) B2818709
theorem B3173489 : Blo 1252444 3173489 := bstep (se 2 (by rfl) ⟨1190058, by rfl⟩ : syracuseStep 3173489 = 2380117) B2380117
theorem B1879169 : Blo 1252444 1879169 := bstep (se 2 (by rfl) ⟨704688, by rfl⟩ : syracuseStep 1879169 = 1409377) B1409377
theorem B2116739 : Blo 1252444 2116739 := bstep (se 1 (by rfl) ⟨1587554, by rfl⟩ : syracuseStep 2116739 = 3175109) B3175109
theorem B2821265 : Blo 1252444 2821265 := bstep (se 2 (by rfl) ⟨1057974, by rfl⟩ : syracuseStep 2821265 = 2115949) B2115949
theorem B1879187 : Blo 1252444 1879187 := bstep (se 1 (by rfl) ⟨1409390, by rfl⟩ : syracuseStep 1879187 = 2818781) B2818781
theorem B3173539 : Blo 1252444 3173539 := bstep (se 1 (by rfl) ⟨2380154, by rfl⟩ : syracuseStep 3173539 = 4760309) B4760309
theorem B2821283 : Blo 1252444 2821283 := bstep (se 1 (by rfl) ⟨2115962, by rfl⟩ : syracuseStep 2821283 = 4231925) B4231925
theorem B1879217 : Blo 1252444 1879217 := bstep (se 2 (by rfl) ⟨704706, by rfl⟩ : syracuseStep 1879217 = 1409413) B1409413
theorem B1879235 : Blo 1252444 1879235 := bstep (se 1 (by rfl) ⟨1409426, by rfl⟩ : syracuseStep 1879235 = 2818853) B2818853
theorem B1879265 : Blo 1252444 1879265 := bstep (se 2 (by rfl) ⟨704724, by rfl⟩ : syracuseStep 1879265 = 1409449) B1409449
theorem B1879283 : Blo 1252444 1879283 := bstep (se 1 (by rfl) ⟨1409462, by rfl⟩ : syracuseStep 1879283 = 2818925) B2818925
theorem B1338611 : Blo 1252444 1338611 := bstep (se 1 (by rfl) ⟨1003958, by rfl⟩ : syracuseStep 1338611 = 2007917) B2007917
theorem B2116867 : Blo 1252444 2116867 := bstep (se 1 (by rfl) ⟨1587650, by rfl⟩ : syracuseStep 2116867 = 3175301) B3175301
theorem B3566861 : Blo 1252444 3566861 := bstep (se 3 (by rfl) ⟨668786, by rfl⟩ : syracuseStep 3566861 = 1337573) B1337573
theorem B4230413 : Blo 1252444 4230413 := bstep (se 3 (by rfl) ⟨793202, by rfl⟩ : syracuseStep 4230413 = 1586405) B1586405
theorem B1879313 : Blo 1252444 1879313 := bstep (se 2 (by rfl) ⟨704742, by rfl⟩ : syracuseStep 1879313 = 1409485) B1409485
theorem B1879331 : Blo 1252444 1879331 := bstep (se 1 (by rfl) ⟨1409498, by rfl⟩ : syracuseStep 1879331 = 2818997) B2818997
theorem B3173681 : Blo 1252444 3173681 := bstep (se 2 (by rfl) ⟨1190130, by rfl⟩ : syracuseStep 3173681 = 2380261) B2380261
theorem B1879361 : Blo 1252444 1879361 := bstep (se 2 (by rfl) ⟨704760, by rfl⟩ : syracuseStep 1879361 = 1409521) B1409521
theorem B4230467 : Blo 1252444 4230467 := bstep (se 1 (by rfl) ⟨3172850, by rfl⟩ : syracuseStep 4230467 = 6345701) B6345701
theorem B4017485 : Blo 1252444 4017485 := bstep (se 3 (by rfl) ⟨753278, by rfl⟩ : syracuseStep 4017485 = 1506557) B1506557
theorem B3566929 : Blo 1252444 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B1879379 : Blo 1252444 1879379 := bstep (se 1 (by rfl) ⟨1409534, by rfl⟩ : syracuseStep 1879379 = 2819069) B2819069
theorem B2379107 : Blo 1252444 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B1879409 : Blo 1252444 1879409 := bstep (se 2 (by rfl) ⟨704778, by rfl⟩ : syracuseStep 1879409 = 1409557) B1409557
theorem B4287857 : Blo 1252444 4287857 := bstep (se 2 (by rfl) ⟨1607946, by rfl⟩ : syracuseStep 4287857 = 3215893) B3215893
theorem B1879427 : Blo 1252444 1879427 := bstep (se 1 (by rfl) ⟨1409570, by rfl⟩ : syracuseStep 1879427 = 2819141) B2819141
theorem B1879457 : Blo 1252444 1879457 := bstep (se 2 (by rfl) ⟨704796, by rfl⟩ : syracuseStep 1879457 = 1409593) B1409593
theorem B2821553 : Blo 1252444 2821553 := bstep (se 2 (by rfl) ⟨1058082, by rfl⟩ : syracuseStep 2821553 = 2116165) B2116165
theorem B1879475 : Blo 1252444 1879475 := bstep (se 1 (by rfl) ⟨1409606, by rfl⟩ : syracuseStep 1879475 = 2819213) B2819213
theorem B2289091 : Blo 1252444 2289091 := bstep (se 1 (by rfl) ⟨1716818, by rfl⟩ : syracuseStep 2289091 = 3433637) B3433637
theorem B2821571 : Blo 1252444 2821571 := bstep (se 1 (by rfl) ⟨2116178, by rfl⟩ : syracuseStep 2821571 = 4232357) B4232357
theorem B1879505 : Blo 1252444 1879505 := bstep (se 2 (by rfl) ⟨704814, by rfl⟩ : syracuseStep 1879505 = 1409629) B1409629
theorem B1879523 : Blo 1252444 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B1879553 : Blo 1252444 1879553 := bstep (se 2 (by rfl) ⟨704832, by rfl⟩ : syracuseStep 1879553 = 1409665) B1409665
theorem B1879571 : Blo 1252444 1879571 := bstep (se 1 (by rfl) ⟨1409678, by rfl⟩ : syracuseStep 1879571 = 2819357) B2819357
theorem B1879601 : Blo 1252444 1879601 := bstep (se 2 (by rfl) ⟨704850, by rfl⟩ : syracuseStep 1879601 = 1409701) B1409701
theorem B1879619 : Blo 1252444 1879619 := bstep (se 1 (by rfl) ⟨1409714, by rfl⟩ : syracuseStep 1879619 = 2819429) B2819429
theorem B4230737 : Blo 1252444 4230737 := bstep (se 2 (by rfl) ⟨1586526, by rfl⟩ : syracuseStep 4230737 = 3173053) B3173053
theorem B1879649 : Blo 1252444 1879649 := bstep (se 2 (by rfl) ⟨704868, by rfl⟩ : syracuseStep 1879649 = 1409737) B1409737
theorem B3567203 : Blo 1252444 3567203 := bstep (se 1 (by rfl) ⟨2675402, by rfl⟩ : syracuseStep 3567203 = 5350805) B5350805
theorem B7237219 : Blo 1252444 7237219 := bstep (se 1 (by rfl) ⟨5427914, by rfl⟩ : syracuseStep 7237219 = 10855829) B10855829
theorem B1879667 : Blo 1252444 1879667 := bstep (se 1 (by rfl) ⟨1409750, by rfl⟩ : syracuseStep 1879667 = 2819501) B2819501
theorem B2379395 : Blo 1252444 2379395 := bstep (se 1 (by rfl) ⟨1784546, by rfl⟩ : syracuseStep 2379395 = 3569093) B3569093
theorem B3010193 : Blo 1252444 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1879697 : Blo 1252444 1879697 := bstep (se 2 (by rfl) ⟨704886, by rfl⟩ : syracuseStep 1879697 = 1409773) B1409773
theorem B1879715 : Blo 1252444 1879715 := bstep (se 1 (by rfl) ⟨1409786, by rfl⟩ : syracuseStep 1879715 = 2819573) B2819573
theorem B2174627 : Blo 1252444 2174627 := bstep (se 1 (by rfl) ⟨1630970, by rfl⟩ : syracuseStep 2174627 = 3261941) B3261941
theorem B1879745 : Blo 1252444 1879745 := bstep (se 2 (by rfl) ⟨704904, by rfl⟩ : syracuseStep 1879745 = 1409809) B1409809
theorem B2821841 : Blo 1252444 2821841 := bstep (se 2 (by rfl) ⟨1058190, by rfl⟩ : syracuseStep 2821841 = 2116381) B2116381
theorem B1879763 : Blo 1252444 1879763 := bstep (se 1 (by rfl) ⟨1409822, by rfl⟩ : syracuseStep 1879763 = 2819645) B2819645
theorem B2821859 : Blo 1252444 2821859 := bstep (se 1 (by rfl) ⟨2116394, by rfl⟩ : syracuseStep 2821859 = 4232789) B4232789
theorem B1879793 : Blo 1252444 1879793 := bstep (se 2 (by rfl) ⟨704922, by rfl⟩ : syracuseStep 1879793 = 1409845) B1409845
theorem B1879811 : Blo 1252444 1879811 := bstep (se 1 (by rfl) ⟨1409858, by rfl⟩ : syracuseStep 1879811 = 2819717) B2819717
theorem B5353229 : Blo 1252444 5353229 := bstep (se 3 (by rfl) ⟨1003730, by rfl⟩ : syracuseStep 5353229 = 2007461) B2007461
theorem B1904401 : Blo 1252444 1904401 := bstep (se 2 (by rfl) ⟨714150, by rfl⟩ : syracuseStep 1904401 = 1428301) B1428301
theorem B1879841 : Blo 1252444 1879841 := bstep (se 2 (by rfl) ⟨704940, by rfl⟩ : syracuseStep 1879841 = 1409881) B1409881
theorem B1879859 : Blo 1252444 1879859 := bstep (se 1 (by rfl) ⟨1409894, by rfl⟩ : syracuseStep 1879859 = 2819789) B2819789
theorem B3387203 : Blo 1252444 3387203 := bstep (se 1 (by rfl) ⟨2540402, by rfl⟩ : syracuseStep 3387203 = 5080805) B5080805
theorem B13553477 : Blo 1252444 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B3862349 : Blo 1252444 3862349 := bstep (se 3 (by rfl) ⟨724190, by rfl⟩ : syracuseStep 3862349 = 1448381) B1448381
theorem B3010385 : Blo 1252444 3010385 := bstep (se 2 (by rfl) ⟨1128894, by rfl⟩ : syracuseStep 3010385 = 2257789) B2257789
theorem B1879889 : Blo 1252444 1879889 := bstep (se 2 (by rfl) ⟨704958, by rfl⟩ : syracuseStep 1879889 = 1409917) B1409917
theorem B1879907 : Blo 1252444 1879907 := bstep (se 1 (by rfl) ⟨1409930, by rfl⟩ : syracuseStep 1879907 = 2819861) B2819861
theorem B1879937 : Blo 1252444 1879937 := bstep (se 2 (by rfl) ⟨704976, by rfl⟩ : syracuseStep 1879937 = 1409953) B1409953
theorem B1879955 : Blo 1252444 1879955 := bstep (se 1 (by rfl) ⟨1409966, by rfl⟩ : syracuseStep 1879955 = 2819933) B2819933
theorem B2895793 : Blo 1252444 2895793 := bstep (se 2 (by rfl) ⟨1085922, by rfl⟩ : syracuseStep 2895793 = 2171845) B2171845
theorem B1879985 : Blo 1252444 1879985 := bstep (se 2 (by rfl) ⟨704994, by rfl⟩ : syracuseStep 1879985 = 1409989) B1409989
theorem B1880003 : Blo 1252444 1880003 := bstep (se 1 (by rfl) ⟨1410002, by rfl⟩ : syracuseStep 1880003 = 2820005) B2820005
theorem B1880033 : Blo 1252444 1880033 := bstep (se 2 (by rfl) ⟨705012, by rfl⟩ : syracuseStep 1880033 = 1410025) B1410025
theorem B1339363 : Blo 1252444 1339363 := bstep (se 1 (by rfl) ⟨1004522, by rfl⟩ : syracuseStep 1339363 = 2009045) B2009045
theorem B2822129 : Blo 1252444 2822129 := bstep (se 2 (by rfl) ⟨1058298, by rfl⟩ : syracuseStep 2822129 = 2116597) B2116597
theorem B1880051 : Blo 1252444 1880051 := bstep (se 1 (by rfl) ⟨1410038, by rfl⟩ : syracuseStep 1880051 = 2820077) B2820077
theorem B2822147 : Blo 1252444 2822147 := bstep (se 1 (by rfl) ⟨2116610, by rfl⟩ : syracuseStep 2822147 = 4233221) B4233221
theorem B1880081 : Blo 1252444 1880081 := bstep (se 2 (by rfl) ⟨705030, by rfl⟩ : syracuseStep 1880081 = 1410061) B1410061
theorem B1880099 : Blo 1252444 1880099 := bstep (se 1 (by rfl) ⟨1410074, by rfl⟩ : syracuseStep 1880099 = 2820149) B2820149
theorem B2715697 : Blo 1252444 2715697 := bstep (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) B2036773
theorem B1880129 : Blo 1252444 1880129 := bstep (se 2 (by rfl) ⟨705048, by rfl⟩ : syracuseStep 1880129 = 1410097) B1410097
theorem B1880147 : Blo 1252444 1880147 := bstep (se 1 (by rfl) ⟨1410110, by rfl⟩ : syracuseStep 1880147 = 2820221) B2820221
theorem B4231277 : Blo 1252444 4231277 := bstep (se 3 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 4231277 = 1586729) B1586729
theorem B1880177 : Blo 1252444 1880177 := bstep (se 2 (by rfl) ⟨705066, by rfl⟩ : syracuseStep 1880177 = 1410133) B1410133
theorem B1880195 : Blo 1252444 1880195 := bstep (se 1 (by rfl) ⟨1410146, by rfl⟩ : syracuseStep 1880195 = 2820293) B2820293
theorem B7139461 : Blo 1252444 7139461 := bstep (se 4 (by rfl) ⟨669324, by rfl⟩ : syracuseStep 7139461 = 1338649) B1338649
theorem B1880225 : Blo 1252444 1880225 := bstep (se 2 (by rfl) ⟨705084, by rfl⟩ : syracuseStep 1880225 = 1410169) B1410169
theorem B4231331 : Blo 1252444 4231331 := bstep (se 1 (by rfl) ⟨3173498, by rfl⟩ : syracuseStep 4231331 = 6346997) B6346997
theorem B1880243 : Blo 1252444 1880243 := bstep (se 1 (by rfl) ⟨1410182, by rfl⟩ : syracuseStep 1880243 = 2820365) B2820365
theorem B1880273 : Blo 1252444 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1880291 : Blo 1252444 1880291 := bstep (se 1 (by rfl) ⟨1410218, by rfl⟩ : syracuseStep 1880291 = 2820437) B2820437
theorem B1880321 : Blo 1252444 1880321 := bstep (se 2 (by rfl) ⟨705120, by rfl⟩ : syracuseStep 1880321 = 1410241) B1410241
theorem B3174673 : Blo 1252444 3174673 := bstep (se 2 (by rfl) ⟨1190502, by rfl⟩ : syracuseStep 3174673 = 2381005) B2381005
theorem B2822417 : Blo 1252444 2822417 := bstep (se 2 (by rfl) ⟨1058406, by rfl⟩ : syracuseStep 2822417 = 2116813) B2116813
theorem B1880339 : Blo 1252444 1880339 := bstep (se 1 (by rfl) ⟨1410254, by rfl⟩ : syracuseStep 1880339 = 2820509) B2820509
theorem B4575523 : Blo 1252444 4575523 := bstep (se 1 (by rfl) ⟨3431642, by rfl⟩ : syracuseStep 4575523 = 6863285) B6863285
theorem B2822435 : Blo 1252444 2822435 := bstep (se 1 (by rfl) ⟨2116826, by rfl⟩ : syracuseStep 2822435 = 4233653) B4233653
theorem B1880369 : Blo 1252444 1880369 := bstep (se 2 (by rfl) ⟨705138, by rfl⟩ : syracuseStep 1880369 = 1410277) B1410277
theorem B1880387 : Blo 1252444 1880387 := bstep (se 1 (by rfl) ⟨1410290, by rfl⟩ : syracuseStep 1880387 = 2820581) B2820581
theorem B1880417 : Blo 1252444 1880417 := bstep (se 2 (by rfl) ⟨705156, by rfl⟩ : syracuseStep 1880417 = 1410313) B1410313
theorem B1880435 : Blo 1252444 1880435 := bstep (se 1 (by rfl) ⟨1410326, by rfl⟩ : syracuseStep 1880435 = 2820653) B2820653
theorem B1880465 : Blo 1252444 1880465 := bstep (se 2 (by rfl) ⟨705174, by rfl⟩ : syracuseStep 1880465 = 1410349) B1410349
theorem B1880483 : Blo 1252444 1880483 := bstep (se 1 (by rfl) ⟨1410362, by rfl⟩ : syracuseStep 1880483 = 2820725) B2820725
theorem B3568045 : Blo 1252444 3568045 := bstep (se 3 (by rfl) ⟨669008, by rfl⟩ : syracuseStep 3568045 = 1338017) B1338017
theorem B4231601 : Blo 1252444 4231601 := bstep (se 2 (by rfl) ⟨1586850, by rfl⟩ : syracuseStep 4231601 = 3173701) B3173701
theorem B1880513 : Blo 1252444 1880513 := bstep (se 2 (by rfl) ⟨705192, by rfl⟩ : syracuseStep 1880513 = 1410385) B1410385
theorem B6779333 : Blo 1252444 6779333 := bstep (se 4 (by rfl) ⟨635562, by rfl⟩ : syracuseStep 6779333 = 1271125) B1271125
theorem B1880531 : Blo 1252444 1880531 := bstep (se 1 (by rfl) ⟨1410398, by rfl⟩ : syracuseStep 1880531 = 2820797) B2820797
theorem B6771185 : Blo 1252444 6771185 := bstep (se 2 (by rfl) ⟨2539194, by rfl⟩ : syracuseStep 6771185 = 5078389) B5078389
theorem B1880561 : Blo 1252444 1880561 := bstep (se 2 (by rfl) ⟨705210, by rfl⟩ : syracuseStep 1880561 = 1410421) B1410421
theorem B1585651 : Blo 1252444 1585651 := bstep (se 1 (by rfl) ⟨1189238, by rfl⟩ : syracuseStep 1585651 = 2378477) B2378477
theorem B1880579 : Blo 1252444 1880579 := bstep (se 1 (by rfl) ⟨1410434, by rfl⟩ : syracuseStep 1880579 = 2820869) B2820869
theorem B1880609 : Blo 1252444 1880609 := bstep (se 2 (by rfl) ⟨705228, by rfl⟩ : syracuseStep 1880609 = 1410457) B1410457
theorem B3011107 : Blo 1252444 3011107 := bstep (se 1 (by rfl) ⟨2258330, by rfl⟩ : syracuseStep 3011107 = 4516661) B4516661
theorem B3174947 : Blo 1252444 3174947 := bstep (se 1 (by rfl) ⟨2381210, by rfl⟩ : syracuseStep 3174947 = 4762421) B4762421
theorem B2380337 : Blo 1252444 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B1880627 : Blo 1252444 1880627 := bstep (se 1 (by rfl) ⟨1410470, by rfl⟩ : syracuseStep 1880627 = 2820941) B2820941
theorem B3568205 : Blo 1252444 3568205 := bstep (se 3 (by rfl) ⟨669038, by rfl⟩ : syracuseStep 3568205 = 1338077) B1338077
theorem B1880657 : Blo 1252444 1880657 := bstep (se 2 (by rfl) ⟨705246, by rfl⟩ : syracuseStep 1880657 = 1410493) B1410493
theorem B2036305 : Blo 1252444 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B1585747 : Blo 1252444 1585747 := bstep (se 1 (by rfl) ⟨1189310, by rfl⟩ : syracuseStep 1585747 = 2378621) B2378621
theorem B1880675 : Blo 1252444 1880675 := bstep (se 1 (by rfl) ⟨1410506, by rfl⟩ : syracuseStep 1880675 = 2821013) B2821013
theorem B1880705 : Blo 1252444 1880705 := bstep (se 2 (by rfl) ⟨705264, by rfl⟩ : syracuseStep 1880705 = 1410529) B1410529
theorem B1880723 : Blo 1252444 1880723 := bstep (se 1 (by rfl) ⟨1410542, by rfl⟩ : syracuseStep 1880723 = 2821085) B2821085
theorem B6771377 : Blo 1252444 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B1880753 : Blo 1252444 1880753 := bstep (se 2 (by rfl) ⟨705282, by rfl⟩ : syracuseStep 1880753 = 1410565) B1410565
theorem B1880771 : Blo 1252444 1880771 := bstep (se 1 (by rfl) ⟨1410578, by rfl⟩ : syracuseStep 1880771 = 2821157) B2821157
theorem B1880801 : Blo 1252444 1880801 := bstep (se 2 (by rfl) ⟨705300, by rfl⟩ : syracuseStep 1880801 = 1410601) B1410601
theorem B12047075 : Blo 1252444 12047075 := bstep (se 1 (by rfl) ⟨9035306, by rfl⟩ : syracuseStep 12047075 = 18070613) B18070613
theorem B3175139 : Blo 1252444 3175139 := bstep (se 1 (by rfl) ⟨2381354, by rfl⟩ : syracuseStep 3175139 = 4762709) B4762709
theorem B1880819 : Blo 1252444 1880819 := bstep (se 1 (by rfl) ⟨1410614, by rfl⟩ : syracuseStep 1880819 = 2821229) B2821229
theorem B3568387 : Blo 1252444 3568387 := bstep (se 1 (by rfl) ⟨2676290, by rfl⟩ : syracuseStep 3568387 = 5352581) B5352581
theorem B1880849 : Blo 1252444 1880849 := bstep (se 2 (by rfl) ⟨705318, by rfl⟩ : syracuseStep 1880849 = 1410637) B1410637
theorem B1880867 : Blo 1252444 1880867 := bstep (se 1 (by rfl) ⟨1410650, by rfl⟩ : syracuseStep 1880867 = 2821301) B2821301
theorem B2143027 : Blo 1252444 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B1880897 : Blo 1252444 1880897 := bstep (se 2 (by rfl) ⟨705336, by rfl⟩ : syracuseStep 1880897 = 1410673) B1410673
theorem B1880915 : Blo 1252444 1880915 := bstep (se 1 (by rfl) ⟨1410686, by rfl⟩ : syracuseStep 1880915 = 2821373) B2821373
theorem B1880945 : Blo 1252444 1880945 := bstep (se 2 (by rfl) ⟨705354, by rfl⟩ : syracuseStep 1880945 = 1410709) B1410709
theorem B1880963 : Blo 1252444 1880963 := bstep (se 1 (by rfl) ⟨1410722, by rfl⟩ : syracuseStep 1880963 = 2821445) B2821445
theorem B1880993 : Blo 1252444 1880993 := bstep (se 2 (by rfl) ⟨705372, by rfl⟩ : syracuseStep 1880993 = 1410745) B1410745
theorem B1881011 : Blo 1252444 1881011 := bstep (se 1 (by rfl) ⟨1410758, by rfl⟩ : syracuseStep 1881011 = 2821517) B2821517
theorem B4232141 : Blo 1252444 4232141 := bstep (se 3 (by rfl) ⟨793526, by rfl⟩ : syracuseStep 4232141 = 1587053) B1587053
theorem B1881041 : Blo 1252444 1881041 := bstep (se 2 (by rfl) ⟨705390, by rfl⟩ : syracuseStep 1881041 = 1410781) B1410781
theorem B1881059 : Blo 1252444 1881059 := bstep (se 1 (by rfl) ⟨1410794, by rfl⟩ : syracuseStep 1881059 = 2821589) B2821589
theorem B1881089 : Blo 1252444 1881089 := bstep (se 2 (by rfl) ⟨705408, by rfl⟩ : syracuseStep 1881089 = 1410817) B1410817
theorem B4232195 : Blo 1252444 4232195 := bstep (se 1 (by rfl) ⟨3174146, by rfl⟩ : syracuseStep 4232195 = 6348293) B6348293
theorem B1881107 : Blo 1252444 1881107 := bstep (se 1 (by rfl) ⟨1410830, by rfl⟩ : syracuseStep 1881107 = 2821661) B2821661
theorem B6435875 : Blo 1252444 6435875 := bstep (se 1 (by rfl) ⟨4826906, by rfl⟩ : syracuseStep 6435875 = 9653813) B9653813
theorem B1881137 : Blo 1252444 1881137 := bstep (se 2 (by rfl) ⟨705426, by rfl⟩ : syracuseStep 1881137 = 1410853) B1410853
theorem B1586243 : Blo 1252444 1586243 := bstep (se 1 (by rfl) ⟨1189682, by rfl⟩ : syracuseStep 1586243 = 2379365) B2379365
theorem B1881155 : Blo 1252444 1881155 := bstep (se 1 (by rfl) ⟨1410866, by rfl⟩ : syracuseStep 1881155 = 2821733) B2821733
theorem B1881185 : Blo 1252444 1881185 := bstep (se 2 (by rfl) ⟨705444, by rfl⟩ : syracuseStep 1881185 = 1410889) B1410889
theorem B48829553 : Blo 1252444 48829553 := bstep (se 2 (by rfl) ⟨18311082, by rfl⟩ : syracuseStep 48829553 = 36622165) B36622165
theorem B3052657 : Blo 1252444 3052657 := bstep (se 2 (by rfl) ⟨1144746, by rfl⟩ : syracuseStep 3052657 = 2289493) B2289493
theorem B2290801 : Blo 1252444 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B1881203 : Blo 1252444 1881203 := bstep (se 1 (by rfl) ⟨1410902, by rfl⟩ : syracuseStep 1881203 = 2821805) B2821805
theorem B1881233 : Blo 1252444 1881233 := bstep (se 2 (by rfl) ⟨705462, by rfl⟩ : syracuseStep 1881233 = 1410925) B1410925
theorem B1881251 : Blo 1252444 1881251 := bstep (se 1 (by rfl) ⟨1410938, by rfl⟩ : syracuseStep 1881251 = 2821877) B2821877
theorem B1881281 : Blo 1252444 1881281 := bstep (se 2 (by rfl) ⟨705480, by rfl⟩ : syracuseStep 1881281 = 1410961) B1410961
theorem B1881299 : Blo 1252444 1881299 := bstep (se 1 (by rfl) ⟨1410974, by rfl⟩ : syracuseStep 1881299 = 2821949) B2821949
theorem B1881329 : Blo 1252444 1881329 := bstep (se 2 (by rfl) ⟨705498, by rfl⟩ : syracuseStep 1881329 = 1410997) B1410997
theorem B1881347 : Blo 1252444 1881347 := bstep (se 1 (by rfl) ⟨1411010, by rfl⟩ : syracuseStep 1881347 = 2822021) B2822021
theorem B4232465 : Blo 1252444 4232465 := bstep (se 2 (by rfl) ⟨1587174, by rfl⟩ : syracuseStep 4232465 = 3174349) B3174349
theorem B1881377 : Blo 1252444 1881377 := bstep (se 2 (by rfl) ⟨705516, by rfl⟩ : syracuseStep 1881377 = 1411033) B1411033
theorem B2676017 : Blo 1252444 2676017 := bstep (se 2 (by rfl) ⟨1003506, by rfl⟩ : syracuseStep 2676017 = 2007013) B2007013
theorem B1881395 : Blo 1252444 1881395 := bstep (se 1 (by rfl) ⟨1411046, by rfl⟩ : syracuseStep 1881395 = 2822093) B2822093
theorem B2413891 : Blo 1252444 2413891 := bstep (se 1 (by rfl) ⟨1810418, by rfl⟩ : syracuseStep 2413891 = 3620837) B3620837
theorem B1881425 : Blo 1252444 1881425 := bstep (se 2 (by rfl) ⟨705534, by rfl⟩ : syracuseStep 1881425 = 1411069) B1411069
theorem B1881443 : Blo 1252444 1881443 := bstep (se 1 (by rfl) ⟨1411082, by rfl⟩ : syracuseStep 1881443 = 2822165) B2822165
theorem B1881473 : Blo 1252444 1881473 := bstep (se 2 (by rfl) ⟨705552, by rfl⟩ : syracuseStep 1881473 = 1411105) B1411105
theorem B4756877 : Blo 1252444 4756877 := bstep (se 3 (by rfl) ⟨891914, by rfl⟩ : syracuseStep 4756877 = 1783829) B1783829
theorem B1881491 : Blo 1252444 1881491 := bstep (se 1 (by rfl) ⟨1411118, by rfl⟩ : syracuseStep 1881491 = 2822237) B2822237
theorem B2381233 : Blo 1252444 2381233 := bstep (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) B1785925
theorem B1881521 : Blo 1252444 1881521 := bstep (se 2 (by rfl) ⟨705570, by rfl⟩ : syracuseStep 1881521 = 1411141) B1411141
theorem B1881539 : Blo 1252444 1881539 := bstep (se 1 (by rfl) ⟨1411154, by rfl⟩ : syracuseStep 1881539 = 2822309) B2822309
theorem B8033741 : Blo 1252444 8033741 := bstep (se 3 (by rfl) ⟨1506326, by rfl⟩ : syracuseStep 8033741 = 3012653) B3012653
theorem B1881569 : Blo 1252444 1881569 := bstep (se 2 (by rfl) ⟨705588, by rfl⟩ : syracuseStep 1881569 = 1411177) B1411177
theorem B1881587 : Blo 1252444 1881587 := bstep (se 1 (by rfl) ⟨1411190, by rfl⟩ : syracuseStep 1881587 = 2822381) B2822381
theorem B1881617 : Blo 1252444 1881617 := bstep (se 2 (by rfl) ⟨705606, by rfl⟩ : syracuseStep 1881617 = 1411213) B1411213
theorem B1881635 : Blo 1252444 1881635 := bstep (se 1 (by rfl) ⟨1411226, by rfl⟩ : syracuseStep 1881635 = 2822453) B2822453
theorem B1881665 : Blo 1252444 1881665 := bstep (se 2 (by rfl) ⟨705624, by rfl⟩ : syracuseStep 1881665 = 1411249) B1411249
theorem B2381393 : Blo 1252444 2381393 := bstep (se 2 (by rfl) ⟨893022, by rfl⟩ : syracuseStep 2381393 = 1786045) B1786045
theorem B1693315 : Blo 1252444 1693315 := bstep (se 1 (by rfl) ⟨1269986, by rfl⟩ : syracuseStep 1693315 = 2539973) B2539973
theorem B1586947 : Blo 1252444 1586947 := bstep (se 1 (by rfl) ⟨1190210, by rfl⟩ : syracuseStep 1586947 = 2380421) B2380421
theorem B4233005 : Blo 1252444 4233005 := bstep (se 3 (by rfl) ⟨793688, by rfl⟩ : syracuseStep 4233005 = 1587377) B1587377
theorem B8025925 : Blo 1252444 8025925 := bstep (se 4 (by rfl) ⟨752430, by rfl⟩ : syracuseStep 8025925 = 1504861) B1504861
theorem B1587043 : Blo 1252444 1587043 := bstep (se 1 (by rfl) ⟨1190282, by rfl⟩ : syracuseStep 1587043 = 2380565) B2380565
theorem B4233059 : Blo 1252444 4233059 := bstep (se 1 (by rfl) ⟨3174794, by rfl⟩ : syracuseStep 4233059 = 6349589) B6349589
theorem B6346673 : Blo 1252444 6346673 := bstep (se 2 (by rfl) ⟨2380002, by rfl⟩ : syracuseStep 6346673 = 4760005) B4760005
theorem B1783795 : Blo 1252444 1783795 := bstep (se 1 (by rfl) ⟨1337846, by rfl⟩ : syracuseStep 1783795 = 2675693) B2675693
theorem B7141445 : Blo 1252444 7141445 := bstep (se 4 (by rfl) ⟨669510, by rfl⟩ : syracuseStep 7141445 = 1339021) B1339021
theorem B3569777 : Blo 1252444 3569777 := bstep (se 2 (by rfl) ⟨1338666, by rfl⟩ : syracuseStep 3569777 = 2677333) B2677333
theorem B4233329 : Blo 1252444 4233329 := bstep (se 2 (by rfl) ⟨1587498, by rfl⟩ : syracuseStep 4233329 = 3174997) B3174997
theorem B2676881 : Blo 1252444 2676881 := bstep (se 2 (by rfl) ⟨1003830, by rfl⟩ : syracuseStep 2676881 = 2007661) B2007661
theorem B2857187 : Blo 1252444 2857187 := bstep (se 1 (by rfl) ⟨2142890, by rfl⟩ : syracuseStep 2857187 = 4285781) B4285781
theorem B3619075 : Blo 1252444 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B1906993 : Blo 1252444 1906993 := bstep (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) B1430245
theorem B11008325 : Blo 1252444 11008325 := bstep (se 4 (by rfl) ⟨1032030, by rfl⟩ : syracuseStep 11008325 = 2064061) B2064061
theorem B1587539 : Blo 1252444 1587539 := bstep (se 1 (by rfl) ⟨1190654, by rfl⟩ : syracuseStep 1587539 = 2381309) B2381309
theorem B6773105 : Blo 1252444 6773105 := bstep (se 2 (by rfl) ⟨2539914, by rfl⟩ : syracuseStep 6773105 = 5079829) B5079829
theorem B1505731 : Blo 1252444 1505731 := bstep (se 1 (by rfl) ⟨1129298, by rfl⟩ : syracuseStep 1505731 = 2258597) B2258597
theorem B1784273 : Blo 1252444 1784273 := bstep (se 2 (by rfl) ⟨669102, by rfl⟩ : syracuseStep 1784273 = 1338205) B1338205
theorem B5716451 : Blo 1252444 5716451 := bstep (se 1 (by rfl) ⟨4287338, by rfl⟩ : syracuseStep 5716451 = 8574677) B8574677
theorem B1505827 : Blo 1252444 1505827 := bstep (se 1 (by rfl) ⟨1129370, by rfl⟩ : syracuseStep 1505827 = 2258741) B2258741
theorem B2259505 : Blo 1252444 2259505 := bstep (se 2 (by rfl) ⟨847314, by rfl⟩ : syracuseStep 2259505 = 1694629) B1694629
theorem B1784387 : Blo 1252444 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B1505875 : Blo 1252444 1505875 := bstep (se 1 (by rfl) ⟨1129406, by rfl⟩ : syracuseStep 1505875 = 2258813) B2258813
theorem B1694353 : Blo 1252444 1694353 := bstep (se 2 (by rfl) ⟨635382, by rfl⟩ : syracuseStep 1694353 = 1270765) B1270765
theorem B1784467 : Blo 1252444 1784467 := bstep (se 1 (by rfl) ⟨1338350, by rfl⟩ : syracuseStep 1784467 = 2676701) B2676701
theorem B1694401 : Blo 1252444 1694401 := bstep (se 2 (by rfl) ⟨635400, by rfl⟩ : syracuseStep 1694401 = 1270801) B1270801
theorem B1694531 : Blo 1252444 1694531 := bstep (se 1 (by rfl) ⟨1270898, by rfl⟩ : syracuseStep 1694531 = 2541797) B2541797
theorem B4013027 : Blo 1252444 4013027 := bstep (se 1 (by rfl) ⟨3009770, by rfl⟩ : syracuseStep 4013027 = 6019541) B6019541
theorem B4070417 : Blo 1252444 4070417 := bstep (se 2 (by rfl) ⟨1526406, by rfl⟩ : syracuseStep 4070417 = 3052813) B3052813
theorem B2260003 : Blo 1252444 2260003 := bstep (se 1 (by rfl) ⟨1695002, by rfl⟩ : syracuseStep 2260003 = 3390005) B3390005
theorem B3570733 : Blo 1252444 3570733 := bstep (se 3 (by rfl) ⟨669512, by rfl⟩ : syracuseStep 3570733 = 1339025) B1339025
theorem B15252533 : Blo 1252444 15252533 := bstep (se 5 (by rfl) ⟨714962, by rfl⟩ : syracuseStep 15252533 = 1429925) B1429925
theorem B1252451 : Blo 1252444 1252451 := bstep (se 1 (by rfl) ⟨939338, by rfl⟩ : syracuseStep 1252451 = 1878677) B1878677
theorem B1252467 : Blo 1252444 1252467 := bstep (se 1 (by rfl) ⟨939350, by rfl⟩ : syracuseStep 1252467 = 1878701) B1878701
theorem B1252483 : Blo 1252444 1252483 := bstep (se 1 (by rfl) ⟨939362, by rfl⟩ : syracuseStep 1252483 = 1878725) B1878725
theorem B1252499 : Blo 1252444 1252499 := bstep (se 1 (by rfl) ⟨939374, by rfl⟩ : syracuseStep 1252499 = 1878749) B1878749
theorem B1252515 : Blo 1252444 1252515 := bstep (se 1 (by rfl) ⟨939386, by rfl⟩ : syracuseStep 1252515 = 1878773) B1878773
theorem B1252531 : Blo 1252444 1252531 := bstep (se 1 (by rfl) ⟨939398, by rfl⟩ : syracuseStep 1252531 = 1878797) B1878797
theorem B1785025 : Blo 1252444 1785025 := bstep (se 2 (by rfl) ⟨669384, by rfl⟩ : syracuseStep 1785025 = 1338769) B1338769
theorem B1252547 : Blo 1252444 1252547 := bstep (se 1 (by rfl) ⟨939410, by rfl⟩ : syracuseStep 1252547 = 1878821) B1878821
theorem B1252563 : Blo 1252444 1252563 := bstep (se 1 (by rfl) ⟨939422, by rfl⟩ : syracuseStep 1252563 = 1878845) B1878845
theorem B1252579 : Blo 1252444 1252579 := bstep (se 1 (by rfl) ⟨939434, by rfl⟩ : syracuseStep 1252579 = 1878869) B1878869
theorem B1252595 : Blo 1252444 1252595 := bstep (se 1 (by rfl) ⟨939446, by rfl⟩ : syracuseStep 1252595 = 1878893) B1878893
theorem B1252611 : Blo 1252444 1252611 := bstep (se 1 (by rfl) ⟨939458, by rfl⟩ : syracuseStep 1252611 = 1878917) B1878917
theorem B3570961 : Blo 1252444 3570961 := bstep (se 2 (by rfl) ⟨1339110, by rfl⟩ : syracuseStep 3570961 = 2678221) B2678221
theorem B1252627 : Blo 1252444 1252627 := bstep (se 1 (by rfl) ⟨939470, by rfl⟩ : syracuseStep 1252627 = 1878941) B1878941
theorem B1252643 : Blo 1252444 1252643 := bstep (se 1 (by rfl) ⟨939482, by rfl⟩ : syracuseStep 1252643 = 1878965) B1878965
theorem B2145571 : Blo 1252444 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B1252659 : Blo 1252444 1252659 := bstep (se 1 (by rfl) ⟨939494, by rfl⟩ : syracuseStep 1252659 = 1878989) B1878989
theorem B1252675 : Blo 1252444 1252675 := bstep (se 1 (by rfl) ⟨939506, by rfl⟩ : syracuseStep 1252675 = 1879013) B1879013
theorem B1252691 : Blo 1252444 1252691 := bstep (se 1 (by rfl) ⟨939518, by rfl⟩ : syracuseStep 1252691 = 1879037) B1879037
theorem B1252707 : Blo 1252444 1252707 := bstep (se 1 (by rfl) ⟨939530, by rfl⟩ : syracuseStep 1252707 = 1879061) B1879061
theorem B6348131 : Blo 1252444 6348131 := bstep (se 1 (by rfl) ⟨4761098, by rfl⟩ : syracuseStep 6348131 = 9522197) B9522197
theorem B1252723 : Blo 1252444 1252723 := bstep (se 1 (by rfl) ⟨939542, by rfl⟩ : syracuseStep 1252723 = 1879085) B1879085
theorem B1252739 : Blo 1252444 1252739 := bstep (se 1 (by rfl) ⟨939554, by rfl⟩ : syracuseStep 1252739 = 1879109) B1879109
theorem B3808657 : Blo 1252444 3808657 := bstep (se 2 (by rfl) ⟨1428246, by rfl⟩ : syracuseStep 3808657 = 2856493) B2856493
theorem B1252755 : Blo 1252444 1252755 := bstep (se 1 (by rfl) ⟨939566, by rfl⟩ : syracuseStep 1252755 = 1879133) B1879133
theorem B1252771 : Blo 1252444 1252771 := bstep (se 1 (by rfl) ⟨939578, by rfl⟩ : syracuseStep 1252771 = 1879157) B1879157
theorem B2678179 : Blo 1252444 2678179 := bstep (se 1 (by rfl) ⟨2008634, by rfl⟩ : syracuseStep 2678179 = 4017269) B4017269
theorem B3571121 : Blo 1252444 3571121 := bstep (se 2 (by rfl) ⟨1339170, by rfl⟩ : syracuseStep 3571121 = 2678341) B2678341
theorem B1252787 : Blo 1252444 1252787 := bstep (se 1 (by rfl) ⟨939590, by rfl⟩ : syracuseStep 1252787 = 1879181) B1879181
theorem B1252803 : Blo 1252444 1252803 := bstep (se 1 (by rfl) ⟨939602, by rfl⟩ : syracuseStep 1252803 = 1879205) B1879205
theorem B1252819 : Blo 1252444 1252819 := bstep (se 1 (by rfl) ⟨939614, by rfl⟩ : syracuseStep 1252819 = 1879229) B1879229
theorem B1252835 : Blo 1252444 1252835 := bstep (se 1 (by rfl) ⟨939626, by rfl⟩ : syracuseStep 1252835 = 1879253) B1879253
theorem B1252851 : Blo 1252444 1252851 := bstep (se 1 (by rfl) ⟨939638, by rfl⟩ : syracuseStep 1252851 = 1879277) B1879277
theorem B1252867 : Blo 1252444 1252867 := bstep (se 1 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 1252867 = 1879301) B1879301
theorem B1252883 : Blo 1252444 1252883 := bstep (se 1 (by rfl) ⟨939662, by rfl⟩ : syracuseStep 1252883 = 1879325) B1879325
theorem B1252899 : Blo 1252444 1252899 := bstep (se 1 (by rfl) ⟨939674, by rfl⟩ : syracuseStep 1252899 = 1879349) B1879349
theorem B3571235 : Blo 1252444 3571235 := bstep (se 1 (by rfl) ⟨2678426, by rfl⟩ : syracuseStep 3571235 = 5356853) B5356853
theorem B1252915 : Blo 1252444 1252915 := bstep (se 1 (by rfl) ⟨939686, by rfl⟩ : syracuseStep 1252915 = 1879373) B1879373
theorem B1252931 : Blo 1252444 1252931 := bstep (se 1 (by rfl) ⟨939698, by rfl⟩ : syracuseStep 1252931 = 1879397) B1879397
theorem B1252947 : Blo 1252444 1252947 := bstep (se 1 (by rfl) ⟨939710, by rfl⟩ : syracuseStep 1252947 = 1879421) B1879421
theorem B1252963 : Blo 1252444 1252963 := bstep (se 1 (by rfl) ⟨939722, by rfl⟩ : syracuseStep 1252963 = 1879445) B1879445
theorem B2006641 : Blo 1252444 2006641 := bstep (se 2 (by rfl) ⟨752490, by rfl⟩ : syracuseStep 2006641 = 1504981) B1504981
theorem B1252979 : Blo 1252444 1252979 := bstep (se 1 (by rfl) ⟨939734, by rfl⟩ : syracuseStep 1252979 = 1879469) B1879469
theorem B1252995 : Blo 1252444 1252995 := bstep (se 1 (by rfl) ⟨939746, by rfl⟩ : syracuseStep 1252995 = 1879493) B1879493
theorem B1253011 : Blo 1252444 1253011 := bstep (se 1 (by rfl) ⟨939758, by rfl⟩ : syracuseStep 1253011 = 1879517) B1879517
theorem B1253027 : Blo 1252444 1253027 := bstep (se 1 (by rfl) ⟨939770, by rfl⟩ : syracuseStep 1253027 = 1879541) B1879541
theorem B1253043 : Blo 1252444 1253043 := bstep (se 1 (by rfl) ⟨939782, by rfl⟩ : syracuseStep 1253043 = 1879565) B1879565
theorem B1253059 : Blo 1252444 1253059 := bstep (se 1 (by rfl) ⟨939794, by rfl⟩ : syracuseStep 1253059 = 1879589) B1879589
theorem B1253075 : Blo 1252444 1253075 := bstep (se 1 (by rfl) ⟨939806, by rfl⟩ : syracuseStep 1253075 = 1879613) B1879613
theorem B4013795 : Blo 1252444 4013795 := bstep (se 1 (by rfl) ⟨3010346, by rfl⟩ : syracuseStep 4013795 = 6020693) B6020693
theorem B1253091 : Blo 1252444 1253091 := bstep (se 1 (by rfl) ⟨939818, by rfl⟩ : syracuseStep 1253091 = 1879637) B1879637
theorem B4579057 : Blo 1252444 4579057 := bstep (se 2 (by rfl) ⟨1717146, by rfl⟩ : syracuseStep 4579057 = 3434293) B3434293
theorem B1253107 : Blo 1252444 1253107 := bstep (se 1 (by rfl) ⟨939830, by rfl⟩ : syracuseStep 1253107 = 1879661) B1879661
theorem B1253123 : Blo 1252444 1253123 := bstep (se 1 (by rfl) ⟨939842, by rfl⟩ : syracuseStep 1253123 = 1879685) B1879685
theorem B1253139 : Blo 1252444 1253139 := bstep (se 1 (by rfl) ⟨939854, by rfl⟩ : syracuseStep 1253139 = 1879709) B1879709
theorem B1253155 : Blo 1252444 1253155 := bstep (se 1 (by rfl) ⟨939866, by rfl⟩ : syracuseStep 1253155 = 1879733) B1879733
theorem B1253171 : Blo 1252444 1253171 := bstep (se 1 (by rfl) ⟨939878, by rfl⟩ : syracuseStep 1253171 = 1879757) B1879757
theorem B1253187 : Blo 1252444 1253187 := bstep (se 1 (by rfl) ⟨939890, by rfl⟩ : syracuseStep 1253187 = 1879781) B1879781
theorem B1253203 : Blo 1252444 1253203 := bstep (se 1 (by rfl) ⟨939902, by rfl⟩ : syracuseStep 1253203 = 1879805) B1879805
theorem B1253219 : Blo 1252444 1253219 := bstep (se 1 (by rfl) ⟨939914, by rfl⟩ : syracuseStep 1253219 = 1879829) B1879829
theorem B1253235 : Blo 1252444 1253235 := bstep (se 1 (by rfl) ⟨939926, by rfl⟩ : syracuseStep 1253235 = 1879853) B1879853
theorem B1253251 : Blo 1252444 1253251 := bstep (se 1 (by rfl) ⟨939938, by rfl⟩ : syracuseStep 1253251 = 1879877) B1879877
theorem B1785731 : Blo 1252444 1785731 := bstep (se 1 (by rfl) ⟨1339298, by rfl⟩ : syracuseStep 1785731 = 2678597) B2678597
theorem B1253267 : Blo 1252444 1253267 := bstep (se 1 (by rfl) ⟨939950, by rfl⟩ : syracuseStep 1253267 = 1879901) B1879901
theorem B1253283 : Blo 1252444 1253283 := bstep (se 1 (by rfl) ⟨939962, by rfl⟩ : syracuseStep 1253283 = 1879925) B1879925
theorem B1253299 : Blo 1252444 1253299 := bstep (se 1 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 1253299 = 1879949) B1879949
theorem B4227011 : Blo 1252444 4227011 := bstep (se 1 (by rfl) ⟨3170258, by rfl⟩ : syracuseStep 4227011 = 6340517) B6340517
theorem B1253315 : Blo 1252444 1253315 := bstep (se 1 (by rfl) ⟨939986, by rfl⟩ : syracuseStep 1253315 = 1879973) B1879973
theorem B1253331 : Blo 1252444 1253331 := bstep (se 1 (by rfl) ⟨939998, by rfl⟩ : syracuseStep 1253331 = 1879997) B1879997
theorem B1253347 : Blo 1252444 1253347 := bstep (se 1 (by rfl) ⟨940010, by rfl⟩ : syracuseStep 1253347 = 1880021) B1880021
theorem B1253363 : Blo 1252444 1253363 := bstep (se 1 (by rfl) ⟨940022, by rfl⟩ : syracuseStep 1253363 = 1880045) B1880045
theorem B1409035 : Blo 1252444 1409035 := bstep (se 1 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 1409035 = 2113553) B2113553
theorem B1253387 : Blo 1252444 1253387 := bstep (se 1 (by rfl) ⟨940040, by rfl⟩ : syracuseStep 1253387 = 1880081) B1880081
theorem B1253399 : Blo 1252444 1253399 := bstep (se 1 (by rfl) ⟨940049, by rfl⟩ : syracuseStep 1253399 = 1880099) B1880099
theorem B1253419 : Blo 1252444 1253419 := bstep (se 1 (by rfl) ⟨940064, by rfl⟩ : syracuseStep 1253419 = 1880129) B1880129
theorem B1253431 : Blo 1252444 1253431 := bstep (se 1 (by rfl) ⟨940073, by rfl⟩ : syracuseStep 1253431 = 1880147) B1880147
theorem B1253451 : Blo 1252444 1253451 := bstep (se 1 (by rfl) ⟨940088, by rfl⟩ : syracuseStep 1253451 = 1880177) B1880177
theorem B2539607 : Blo 1252444 2539607 := bstep (se 1 (by rfl) ⟨1904705, by rfl⟩ : syracuseStep 2539607 = 3809411) B3809411
theorem B1253463 : Blo 1252444 1253463 := bstep (se 1 (by rfl) ⟨940097, by rfl⟩ : syracuseStep 1253463 = 1880195) B1880195
theorem B14286941 : Blo 1252444 14286941 := bstep (se 3 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 14286941 = 5357603) B5357603
theorem B1253483 : Blo 1252444 1253483 := bstep (se 1 (by rfl) ⟨940112, by rfl⟩ : syracuseStep 1253483 = 1880225) B1880225
theorem B1409143 : Blo 1252444 1409143 := bstep (se 1 (by rfl) ⟨1056857, by rfl⟩ : syracuseStep 1409143 = 2113715) B2113715
theorem B1253495 : Blo 1252444 1253495 := bstep (se 1 (by rfl) ⟨940121, by rfl⟩ : syracuseStep 1253495 = 1880243) B1880243
theorem B2818187 : Blo 1252444 2818187 := bstep (se 1 (by rfl) ⟨2113640, by rfl⟩ : syracuseStep 2818187 = 4227281) B4227281
theorem B1253515 : Blo 1252444 1253515 := bstep (se 1 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 1253515 = 1880273) B1880273
theorem B1253527 : Blo 1252444 1253527 := bstep (se 1 (by rfl) ⟨940145, by rfl⟩ : syracuseStep 1253527 = 1880291) B1880291
theorem B11600023 : Blo 1252444 11600023 := bstep (se 1 (by rfl) ⟨8700017, by rfl⟩ : syracuseStep 11600023 = 17400035) B17400035
theorem B1253547 : Blo 1252444 1253547 := bstep (se 1 (by rfl) ⟨940160, by rfl⟩ : syracuseStep 1253547 = 1880321) B1880321
theorem B9519281 : Blo 1252444 9519281 := bstep (se 2 (by rfl) ⟨3569730, by rfl⟩ : syracuseStep 9519281 = 7139461) B7139461
theorem B43417781 : Blo 1252444 43417781 := bstep (se 5 (by rfl) ⟨2035208, by rfl⟩ : syracuseStep 43417781 = 4070417) B4070417
theorem B1253559 : Blo 1252444 1253559 := bstep (se 1 (by rfl) ⟨940169, by rfl⟩ : syracuseStep 1253559 = 1880339) B1880339
theorem B2818241 : Blo 1252444 2818241 := bstep (se 2 (by rfl) ⟨1056840, by rfl⟩ : syracuseStep 2818241 = 2113681) B2113681
theorem B1253579 : Blo 1252444 1253579 := bstep (se 1 (by rfl) ⟨940184, by rfl⟩ : syracuseStep 1253579 = 1880369) B1880369
theorem B1253591 : Blo 1252444 1253591 := bstep (se 1 (by rfl) ⟨940193, by rfl⟩ : syracuseStep 1253591 = 1880387) B1880387
theorem B1253611 : Blo 1252444 1253611 := bstep (se 1 (by rfl) ⟨940208, by rfl⟩ : syracuseStep 1253611 = 1880417) B1880417
theorem B1253623 : Blo 1252444 1253623 := bstep (se 1 (by rfl) ⟨940217, by rfl⟩ : syracuseStep 1253623 = 1880435) B1880435
theorem B2679041 : Blo 1252444 2679041 := bstep (se 2 (by rfl) ⟨1004640, by rfl⟩ : syracuseStep 2679041 = 2009281) B2009281
theorem B14483717 : Blo 1252444 14483717 := bstep (se 4 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 14483717 = 2715697) B2715697
theorem B1253643 : Blo 1252444 1253643 := bstep (se 1 (by rfl) ⟨940232, by rfl⟩ : syracuseStep 1253643 = 1880465) B1880465
theorem B1253655 : Blo 1252444 1253655 := bstep (se 1 (by rfl) ⟨940241, by rfl⟩ : syracuseStep 1253655 = 1880483) B1880483
theorem B1409323 : Blo 1252444 1409323 := bstep (se 1 (by rfl) ⟨1056992, by rfl⟩ : syracuseStep 1409323 = 2113985) B2113985
theorem B1253675 : Blo 1252444 1253675 := bstep (se 1 (by rfl) ⟨940256, by rfl⟩ : syracuseStep 1253675 = 1880513) B1880513
theorem B1253687 : Blo 1252444 1253687 := bstep (se 1 (by rfl) ⟨940265, by rfl⟩ : syracuseStep 1253687 = 1880531) B1880531
theorem B4514123 : Blo 1252444 4514123 := bstep (se 1 (by rfl) ⟨3385592, by rfl⟩ : syracuseStep 4514123 = 6771185) B6771185
theorem B1253707 : Blo 1252444 1253707 := bstep (se 1 (by rfl) ⟨940280, by rfl⟩ : syracuseStep 1253707 = 1880561) B1880561
theorem B1253719 : Blo 1252444 1253719 := bstep (se 1 (by rfl) ⟨940289, by rfl⟩ : syracuseStep 1253719 = 1880579) B1880579
theorem B4825433 : Blo 1252444 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B1253739 : Blo 1252444 1253739 := bstep (se 1 (by rfl) ⟨940304, by rfl⟩ : syracuseStep 1253739 = 1880609) B1880609
theorem B1253751 : Blo 1252444 1253751 := bstep (se 1 (by rfl) ⟨940313, by rfl⟩ : syracuseStep 1253751 = 1880627) B1880627
theorem B2113931 : Blo 1252444 2113931 := bstep (se 1 (by rfl) ⟨1585448, by rfl⟩ : syracuseStep 2113931 = 3170897) B3170897
theorem B1253771 : Blo 1252444 1253771 := bstep (se 1 (by rfl) ⟨940328, by rfl⟩ : syracuseStep 1253771 = 1880657) B1880657
theorem B1409431 : Blo 1252444 1409431 := bstep (se 1 (by rfl) ⟨1057073, by rfl⟩ : syracuseStep 1409431 = 2114147) B2114147
theorem B1253783 : Blo 1252444 1253783 := bstep (se 1 (by rfl) ⟨940337, by rfl⟩ : syracuseStep 1253783 = 1880675) B1880675
theorem B2818457 : Blo 1252444 2818457 := bstep (se 2 (by rfl) ⟨1056921, by rfl⟩ : syracuseStep 2818457 = 2113843) B2113843
theorem B1253803 : Blo 1252444 1253803 := bstep (se 1 (by rfl) ⟨940352, by rfl⟩ : syracuseStep 1253803 = 1880705) B1880705
theorem B1253815 : Blo 1252444 1253815 := bstep (se 1 (by rfl) ⟨940361, by rfl⟩ : syracuseStep 1253815 = 1880723) B1880723
theorem B4514251 : Blo 1252444 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B1253835 : Blo 1252444 1253835 := bstep (se 1 (by rfl) ⟨940376, by rfl⟩ : syracuseStep 1253835 = 1880753) B1880753
theorem B1253847 : Blo 1252444 1253847 := bstep (se 1 (by rfl) ⟨940385, by rfl⟩ : syracuseStep 1253847 = 1880771) B1880771
theorem B1253867 : Blo 1252444 1253867 := bstep (se 1 (by rfl) ⟨940400, by rfl⟩ : syracuseStep 1253867 = 1880801) B1880801
theorem B2818547 : Blo 1252444 2818547 := bstep (se 1 (by rfl) ⟨2113910, by rfl⟩ : syracuseStep 2818547 = 4227821) B4227821
theorem B1253879 : Blo 1252444 1253879 := bstep (se 1 (by rfl) ⟨940409, by rfl⟩ : syracuseStep 1253879 = 1880819) B1880819
theorem B2114059 : Blo 1252444 2114059 := bstep (se 1 (by rfl) ⟨1585544, by rfl⟩ : syracuseStep 2114059 = 3171089) B3171089
theorem B1253899 : Blo 1252444 1253899 := bstep (se 1 (by rfl) ⟨940424, by rfl⟩ : syracuseStep 1253899 = 1880849) B1880849
theorem B2818583 : Blo 1252444 2818583 := bstep (se 1 (by rfl) ⟨2113937, by rfl⟩ : syracuseStep 2818583 = 4227875) B4227875
theorem B1253911 : Blo 1252444 1253911 := bstep (se 1 (by rfl) ⟨940433, by rfl⟩ : syracuseStep 1253911 = 1880867) B1880867
theorem B1253931 : Blo 1252444 1253931 := bstep (se 1 (by rfl) ⟨940448, by rfl⟩ : syracuseStep 1253931 = 1880897) B1880897
theorem B6341165 : Blo 1252444 6341165 := bstep (se 3 (by rfl) ⟨1188968, by rfl⟩ : syracuseStep 6341165 = 2377937) B2377937
theorem B1253943 : Blo 1252444 1253943 := bstep (se 1 (by rfl) ⟨940457, by rfl⟩ : syracuseStep 1253943 = 1880915) B1880915
theorem B4227659 : Blo 1252444 4227659 := bstep (se 1 (by rfl) ⟨3170744, by rfl⟩ : syracuseStep 4227659 = 6341489) B6341489
theorem B1409611 : Blo 1252444 1409611 := bstep (se 1 (by rfl) ⟨1057208, by rfl⟩ : syracuseStep 1409611 = 2114417) B2114417
theorem B1253963 : Blo 1252444 1253963 := bstep (se 1 (by rfl) ⟨940472, by rfl⟩ : syracuseStep 1253963 = 1880945) B1880945
theorem B1253975 : Blo 1252444 1253975 := bstep (se 1 (by rfl) ⟨940481, by rfl⟩ : syracuseStep 1253975 = 1880963) B1880963
theorem B2007641 : Blo 1252444 2007641 := bstep (se 2 (by rfl) ⟨752865, by rfl⟩ : syracuseStep 2007641 = 1505731) B1505731
theorem B1253995 : Blo 1252444 1253995 := bstep (se 1 (by rfl) ⟨940496, by rfl⟩ : syracuseStep 1253995 = 1880993) B1880993
theorem B1254007 : Blo 1252444 1254007 := bstep (se 1 (by rfl) ⟨940505, by rfl⟩ : syracuseStep 1254007 = 1881011) B1881011
theorem B1254027 : Blo 1252444 1254027 := bstep (se 1 (by rfl) ⟨940520, by rfl⟩ : syracuseStep 1254027 = 1881041) B1881041
theorem B9519767 : Blo 1252444 9519767 := bstep (se 1 (by rfl) ⟨7139825, by rfl⟩ : syracuseStep 9519767 = 14279651) B14279651
theorem B1254039 : Blo 1252444 1254039 := bstep (se 1 (by rfl) ⟨940529, by rfl⟩ : syracuseStep 1254039 = 1881059) B1881059
theorem B2114201 : Blo 1252444 2114201 := bstep (se 2 (by rfl) ⟨792825, by rfl⟩ : syracuseStep 2114201 = 1585651) B1585651
theorem B1254059 : Blo 1252444 1254059 := bstep (se 1 (by rfl) ⟨940544, by rfl⟩ : syracuseStep 1254059 = 1881089) B1881089
theorem B1409719 : Blo 1252444 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B1254071 : Blo 1252444 1254071 := bstep (se 1 (by rfl) ⟨940553, by rfl⟩ : syracuseStep 1254071 = 1881107) B1881107
theorem B2818763 : Blo 1252444 2818763 := bstep (se 1 (by rfl) ⟨2114072, by rfl⟩ : syracuseStep 2818763 = 4228145) B4228145
theorem B1254091 : Blo 1252444 1254091 := bstep (se 1 (by rfl) ⟨940568, by rfl⟩ : syracuseStep 1254091 = 1881137) B1881137
theorem B1254103 : Blo 1252444 1254103 := bstep (se 1 (by rfl) ⟨940577, by rfl⟩ : syracuseStep 1254103 = 1881155) B1881155
theorem B4014809 : Blo 1252444 4014809 := bstep (se 2 (by rfl) ⟨1505553, by rfl⟩ : syracuseStep 4014809 = 3011107) B3011107
theorem B2007769 : Blo 1252444 2007769 := bstep (se 2 (by rfl) ⟨752913, by rfl⟩ : syracuseStep 2007769 = 1505827) B1505827
theorem B1254123 : Blo 1252444 1254123 := bstep (se 1 (by rfl) ⟨940592, by rfl⟩ : syracuseStep 1254123 = 1881185) B1881185
theorem B1254135 : Blo 1252444 1254135 := bstep (se 1 (by rfl) ⟨940601, by rfl⟩ : syracuseStep 1254135 = 1881203) B1881203
theorem B2818817 : Blo 1252444 2818817 := bstep (se 2 (by rfl) ⟨1057056, by rfl⟩ : syracuseStep 2818817 = 2114113) B2114113
theorem B1254155 : Blo 1252444 1254155 := bstep (se 1 (by rfl) ⟨940616, by rfl⟩ : syracuseStep 1254155 = 1881233) B1881233
theorem B1254167 : Blo 1252444 1254167 := bstep (se 1 (by rfl) ⟨940625, by rfl⟩ : syracuseStep 1254167 = 1881251) B1881251
theorem B2114329 : Blo 1252444 2114329 := bstep (se 2 (by rfl) ⟨792873, by rfl⟩ : syracuseStep 2114329 = 1585747) B1585747
theorem B2007833 : Blo 1252444 2007833 := bstep (se 2 (by rfl) ⟨752937, by rfl⟩ : syracuseStep 2007833 = 1505875) B1505875
theorem B1254187 : Blo 1252444 1254187 := bstep (se 1 (by rfl) ⟨940640, by rfl⟩ : syracuseStep 1254187 = 1881281) B1881281
theorem B7136045 : Blo 1252444 7136045 := bstep (se 3 (by rfl) ⟨1338008, by rfl⟩ : syracuseStep 7136045 = 2676017) B2676017
theorem B1254199 : Blo 1252444 1254199 := bstep (se 1 (by rfl) ⟨940649, by rfl⟩ : syracuseStep 1254199 = 1881299) B1881299
theorem B1254219 : Blo 1252444 1254219 := bstep (se 1 (by rfl) ⟨940664, by rfl⟩ : syracuseStep 1254219 = 1881329) B1881329
theorem B1254231 : Blo 1252444 1254231 := bstep (se 1 (by rfl) ⟨940673, by rfl⟩ : syracuseStep 1254231 = 1881347) B1881347
theorem B4227929 : Blo 1252444 4227929 := bstep (se 2 (by rfl) ⟨1585473, by rfl⟩ : syracuseStep 4227929 = 3170947) B3170947
theorem B1409899 : Blo 1252444 1409899 := bstep (se 1 (by rfl) ⟨1057424, by rfl⟩ : syracuseStep 1409899 = 2114849) B2114849
theorem B1254251 : Blo 1252444 1254251 := bstep (se 1 (by rfl) ⟨940688, by rfl⟩ : syracuseStep 1254251 = 1881377) B1881377
theorem B1254263 : Blo 1252444 1254263 := bstep (se 1 (by rfl) ⟨940697, by rfl⟩ : syracuseStep 1254263 = 1881395) B1881395
theorem B1254283 : Blo 1252444 1254283 := bstep (se 1 (by rfl) ⟨940712, by rfl⟩ : syracuseStep 1254283 = 1881425) B1881425
theorem B1254295 : Blo 1252444 1254295 := bstep (se 1 (by rfl) ⟨940721, by rfl⟩ : syracuseStep 1254295 = 1881443) B1881443
theorem B1254315 : Blo 1252444 1254315 := bstep (se 1 (by rfl) ⟨940736, by rfl⟩ : syracuseStep 1254315 = 1881473) B1881473
theorem B3171251 : Blo 1252444 3171251 := bstep (se 1 (by rfl) ⟨2378438, by rfl⟩ : syracuseStep 3171251 = 4756877) B4756877
theorem B1254327 : Blo 1252444 1254327 := bstep (se 1 (by rfl) ⟨940745, by rfl⟩ : syracuseStep 1254327 = 1881491) B1881491
theorem B2540491 : Blo 1252444 2540491 := bstep (se 1 (by rfl) ⟨1905368, by rfl⟩ : syracuseStep 2540491 = 3810737) B3810737
theorem B1254347 : Blo 1252444 1254347 := bstep (se 1 (by rfl) ⟨940760, by rfl⟩ : syracuseStep 1254347 = 1881521) B1881521
theorem B1410007 : Blo 1252444 1410007 := bstep (se 1 (by rfl) ⟨1057505, by rfl⟩ : syracuseStep 1410007 = 2115011) B2115011
theorem B1254359 : Blo 1252444 1254359 := bstep (se 1 (by rfl) ⟨940769, by rfl⟩ : syracuseStep 1254359 = 1881539) B1881539
theorem B2819033 : Blo 1252444 2819033 := bstep (se 2 (by rfl) ⟨1057137, by rfl⟩ : syracuseStep 2819033 = 2114275) B2114275
theorem B1254379 : Blo 1252444 1254379 := bstep (se 1 (by rfl) ⟨940784, by rfl⟩ : syracuseStep 1254379 = 1881569) B1881569
theorem B1254391 : Blo 1252444 1254391 := bstep (se 1 (by rfl) ⟨940793, by rfl⟩ : syracuseStep 1254391 = 1881587) B1881587
theorem B9036805 : Blo 1252444 9036805 := bstep (se 4 (by rfl) ⟨847200, by rfl⟩ : syracuseStep 9036805 = 1694401) B1694401
theorem B1254411 : Blo 1252444 1254411 := bstep (se 1 (by rfl) ⟨940808, by rfl⟩ : syracuseStep 1254411 = 1881617) B1881617
theorem B4015127 : Blo 1252444 4015127 := bstep (se 1 (by rfl) ⟨3011345, by rfl⟩ : syracuseStep 4015127 = 6022691) B6022691
theorem B1254423 : Blo 1252444 1254423 := bstep (se 1 (by rfl) ⟨940817, by rfl⟩ : syracuseStep 1254423 = 1881635) B1881635
theorem B10159139 : Blo 1252444 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B1254443 : Blo 1252444 1254443 := bstep (se 1 (by rfl) ⟨940832, by rfl⟩ : syracuseStep 1254443 = 1881665) B1881665
theorem B2819123 : Blo 1252444 2819123 := bstep (se 1 (by rfl) ⟨2114342, by rfl⟩ : syracuseStep 2819123 = 4228685) B4228685
theorem B2819159 : Blo 1252444 2819159 := bstep (se 1 (by rfl) ⟨2114369, by rfl⟩ : syracuseStep 2819159 = 4228739) B4228739
theorem B1410187 : Blo 1252444 1410187 := bstep (se 1 (by rfl) ⟨1057640, by rfl⟩ : syracuseStep 1410187 = 2115281) B2115281
theorem B45737141 : Blo 1252444 45737141 := bstep (se 5 (by rfl) ⟨2143928, by rfl⟩ : syracuseStep 45737141 = 4287857) B4287857
theorem B3171545 : Blo 1252444 3171545 := bstep (se 2 (by rfl) ⟨1189329, by rfl⟩ : syracuseStep 3171545 = 2378659) B2378659
theorem B1410295 : Blo 1252444 1410295 := bstep (se 1 (by rfl) ⟨1057721, by rfl⟩ : syracuseStep 1410295 = 2115443) B2115443
theorem B24421637 : Blo 1252444 24421637 := bstep (se 4 (by rfl) ⟨2289528, by rfl⟩ : syracuseStep 24421637 = 4579057) B4579057
theorem B2819339 : Blo 1252444 2819339 := bstep (se 1 (by rfl) ⟨2114504, by rfl⟩ : syracuseStep 2819339 = 4229009) B4229009
theorem B2819393 : Blo 1252444 2819393 := bstep (se 2 (by rfl) ⟨1057272, by rfl⟩ : syracuseStep 2819393 = 2114545) B2114545
theorem B4015435 : Blo 1252444 4015435 := bstep (se 1 (by rfl) ⟨3011576, by rfl⟩ : syracuseStep 4015435 = 6023153) B6023153
theorem B2114903 : Blo 1252444 2114903 := bstep (se 1 (by rfl) ⟨1586177, by rfl⟩ : syracuseStep 2114903 = 3172355) B3172355
theorem B4760963 : Blo 1252444 4760963 := bstep (se 1 (by rfl) ⟨3570722, by rfl⟩ : syracuseStep 4760963 = 7141445) B7141445
theorem B4760977 : Blo 1252444 4760977 := bstep (se 2 (by rfl) ⟨1785366, by rfl⟩ : syracuseStep 4760977 = 3570733) B3570733
theorem B1410475 : Blo 1252444 1410475 := bstep (se 1 (by rfl) ⟨1057856, by rfl⟩ : syracuseStep 1410475 = 2115713) B2115713
theorem B2115031 : Blo 1252444 2115031 := bstep (se 1 (by rfl) ⟨1586273, by rfl⟩ : syracuseStep 2115031 = 3172547) B3172547
theorem B4228631 : Blo 1252444 4228631 := bstep (se 1 (by rfl) ⟨3171473, by rfl⟩ : syracuseStep 4228631 = 6342947) B6342947
theorem B1410583 : Blo 1252444 1410583 := bstep (se 1 (by rfl) ⟨1057937, by rfl⟩ : syracuseStep 1410583 = 2115875) B2115875
theorem B2819609 : Blo 1252444 2819609 := bstep (se 2 (by rfl) ⟨1057353, by rfl⟩ : syracuseStep 2819609 = 2114707) B2114707
theorem B8570461 : Blo 1252444 8570461 := bstep (se 3 (by rfl) ⟨1606961, by rfl⟩ : syracuseStep 8570461 = 3213923) B3213923
theorem B2819699 : Blo 1252444 2819699 := bstep (se 1 (by rfl) ⟨2114774, by rfl⟩ : syracuseStep 2819699 = 4229549) B4229549
theorem B2819735 : Blo 1252444 2819735 := bstep (se 1 (by rfl) ⟨2114801, by rfl⟩ : syracuseStep 2819735 = 4229603) B4229603
theorem B4761281 : Blo 1252444 4761281 := bstep (se 2 (by rfl) ⟨1785480, by rfl⟩ : syracuseStep 4761281 = 3570961) B3570961
theorem B1410763 : Blo 1252444 1410763 := bstep (se 1 (by rfl) ⟨1058072, by rfl⟩ : syracuseStep 1410763 = 2116145) B2116145
theorem B1410871 : Blo 1252444 1410871 := bstep (se 1 (by rfl) ⟨1058153, by rfl⟩ : syracuseStep 1410871 = 2116307) B2116307
theorem B2819915 : Blo 1252444 2819915 := bstep (se 1 (by rfl) ⟨2114936, by rfl⟩ : syracuseStep 2819915 = 4229873) B4229873
theorem B2819969 : Blo 1252444 2819969 := bstep (se 2 (by rfl) ⟨1057488, by rfl⟩ : syracuseStep 2819969 = 2114977) B2114977
theorem B4016051 : Blo 1252444 4016051 := bstep (se 1 (by rfl) ⟨3012038, by rfl⟩ : syracuseStep 4016051 = 6024077) B6024077
theorem B1411051 : Blo 1252444 1411051 := bstep (se 1 (by rfl) ⟨1058288, by rfl⟩ : syracuseStep 1411051 = 2116577) B2116577
theorem B10168355 : Blo 1252444 10168355 := bstep (se 1 (by rfl) ⟨7626266, by rfl⟩ : syracuseStep 10168355 = 15252533) B15252533
theorem B4229171 : Blo 1252444 4229171 := bstep (se 1 (by rfl) ⟨3171878, by rfl⟩ : syracuseStep 4229171 = 6343757) B6343757
theorem B2541619 : Blo 1252444 2541619 := bstep (se 1 (by rfl) ⟨1906214, by rfl⟩ : syracuseStep 2541619 = 3812429) B3812429
theorem B2115659 : Blo 1252444 2115659 := bstep (se 1 (by rfl) ⟨1586744, by rfl⟩ : syracuseStep 2115659 = 3173489) B3173489
theorem B1411159 : Blo 1252444 1411159 := bstep (se 1 (by rfl) ⟨1058369, by rfl⟩ : syracuseStep 1411159 = 2116739) B2116739
theorem B2820185 : Blo 1252444 2820185 := bstep (se 2 (by rfl) ⟨1057569, by rfl⟩ : syracuseStep 2820185 = 2115139) B2115139
theorem B2377907 : Blo 1252444 2377907 := bstep (se 1 (by rfl) ⟨1783430, by rfl⟩ : syracuseStep 2377907 = 3566861) B3566861
theorem B2820275 : Blo 1252444 2820275 := bstep (se 1 (by rfl) ⟨2115206, by rfl⟩ : syracuseStep 2820275 = 4230413) B4230413
theorem B2115787 : Blo 1252444 2115787 := bstep (se 1 (by rfl) ⟨1586840, by rfl⟩ : syracuseStep 2115787 = 3173681) B3173681
theorem B2820311 : Blo 1252444 2820311 := bstep (se 1 (by rfl) ⟨2115233, by rfl⟩ : syracuseStep 2820311 = 4230467) B4230467
theorem B15444229 : Blo 1252444 15444229 := bstep (se 4 (by rfl) ⟨1447896, by rfl⟩ : syracuseStep 15444229 = 2895793) B2895793
theorem B51472685 : Blo 1252444 51472685 := bstep (se 3 (by rfl) ⟨9651128, by rfl⟩ : syracuseStep 51472685 = 19302257) B19302257
theorem B4229441 : Blo 1252444 4229441 := bstep (se 2 (by rfl) ⟨1586040, by rfl⟩ : syracuseStep 4229441 = 3172081) B3172081
theorem B2115929 : Blo 1252444 2115929 := bstep (se 2 (by rfl) ⟨793473, by rfl⟩ : syracuseStep 2115929 = 1586947) B1586947
theorem B4761949 : Blo 1252444 4761949 := bstep (se 3 (by rfl) ⟨892865, by rfl⟩ : syracuseStep 4761949 = 1785731) B1785731
theorem B2820491 : Blo 1252444 2820491 := bstep (se 1 (by rfl) ⟨2115368, by rfl⟩ : syracuseStep 2820491 = 4230737) B4230737
theorem B2378135 : Blo 1252444 2378135 := bstep (se 1 (by rfl) ⟨1783601, by rfl⟩ : syracuseStep 2378135 = 3567203) B3567203
theorem B10701233 : Blo 1252444 10701233 := bstep (se 2 (by rfl) ⟨4012962, by rfl⟩ : syracuseStep 10701233 = 8025925) B8025925
theorem B2820545 : Blo 1252444 2820545 := bstep (se 2 (by rfl) ⟨1057704, by rfl⟩ : syracuseStep 2820545 = 2115409) B2115409
theorem B2116057 : Blo 1252444 2116057 := bstep (se 2 (by rfl) ⟨793521, by rfl⟩ : syracuseStep 2116057 = 1587043) B1587043
theorem B2574899 : Blo 1252444 2574899 := bstep (se 1 (by rfl) ⟨1931174, by rfl⟩ : syracuseStep 2574899 = 3862349) B3862349
theorem B2378393 : Blo 1252444 2378393 := bstep (se 2 (by rfl) ⟨891897, by rfl⟩ : syracuseStep 2378393 = 1783795) B1783795
theorem B2820761 : Blo 1252444 2820761 := bstep (se 2 (by rfl) ⟨1057785, by rfl⟩ : syracuseStep 2820761 = 2115571) B2115571
theorem B1878731 : Blo 1252444 1878731 := bstep (se 1 (by rfl) ⟨1409048, by rfl⟩ : syracuseStep 1878731 = 2818097) B2818097
theorem B1878743 : Blo 1252444 1878743 := bstep (se 1 (by rfl) ⟨1409057, by rfl⟩ : syracuseStep 1878743 = 2818115) B2818115
theorem B2820851 : Blo 1252444 2820851 := bstep (se 1 (by rfl) ⟨2115638, by rfl⟩ : syracuseStep 2820851 = 4231277) B4231277
theorem B15256325 : Blo 1252444 15256325 := bstep (se 4 (by rfl) ⟨1430280, by rfl⟩ : syracuseStep 15256325 = 2860561) B2860561
theorem B2820887 : Blo 1252444 2820887 := bstep (se 1 (by rfl) ⟨2115665, by rfl⟩ : syracuseStep 2820887 = 4231331) B4231331
theorem B1878809 : Blo 1252444 1878809 := bstep (se 2 (by rfl) ⟨704553, by rfl⟩ : syracuseStep 1878809 = 1409107) B1409107
theorem B1338167 : Blo 1252444 1338167 := bstep (se 1 (by rfl) ⟨1003625, by rfl⟩ : syracuseStep 1338167 = 2007251) B2007251
theorem B5352257 : Blo 1252444 5352257 := bstep (se 2 (by rfl) ⟨2007096, by rfl⟩ : syracuseStep 5352257 = 4014193) B4014193
theorem B121940801 : Blo 1252444 121940801 := bstep (se 2 (by rfl) ⟨45727800, by rfl⟩ : syracuseStep 121940801 = 91455601) B91455601
theorem B3173195 : Blo 1252444 3173195 := bstep (se 1 (by rfl) ⟨2379896, by rfl⟩ : syracuseStep 3173195 = 4759793) B4759793
theorem B4893529 : Blo 1252444 4893529 := bstep (se 2 (by rfl) ⟨1835073, by rfl⟩ : syracuseStep 4893529 = 3670147) B3670147
theorem B4229981 : Blo 1252444 4229981 := bstep (se 3 (by rfl) ⟨793121, by rfl⟩ : syracuseStep 4229981 = 1586243) B1586243
theorem B1878923 : Blo 1252444 1878923 := bstep (se 1 (by rfl) ⟨1409192, by rfl⟩ : syracuseStep 1878923 = 2818385) B2818385
theorem B1878935 : Blo 1252444 1878935 := bstep (se 1 (by rfl) ⟨1409201, by rfl⟩ : syracuseStep 1878935 = 2818403) B2818403
theorem B7236503 : Blo 1252444 7236503 := bstep (se 1 (by rfl) ⟨5427377, by rfl⟩ : syracuseStep 7236503 = 10854755) B10854755
theorem B2714519 : Blo 1252444 2714519 := bstep (se 1 (by rfl) ⟨2035889, by rfl⟩ : syracuseStep 2714519 = 4071779) B4071779
theorem B2821067 : Blo 1252444 2821067 := bstep (se 1 (by rfl) ⟨2115800, by rfl⟩ : syracuseStep 2821067 = 4231601) B4231601
theorem B1879001 : Blo 1252444 1879001 := bstep (se 2 (by rfl) ⟨704625, by rfl⟩ : syracuseStep 1879001 = 1409251) B1409251
theorem B5352409 : Blo 1252444 5352409 := bstep (se 2 (by rfl) ⟨2007153, by rfl⟩ : syracuseStep 5352409 = 4014307) B4014307
theorem B2821121 : Blo 1252444 2821121 := bstep (se 2 (by rfl) ⟨1057920, by rfl⟩ : syracuseStep 2821121 = 2115841) B2115841
theorem B8137745 : Blo 1252444 8137745 := bstep (se 2 (by rfl) ⟨3051654, by rfl⟩ : syracuseStep 8137745 = 6103309) B6103309
theorem B2116631 : Blo 1252444 2116631 := bstep (se 1 (by rfl) ⟨1587473, by rfl⟩ : syracuseStep 2116631 = 3174947) B3174947
theorem B2378803 : Blo 1252444 2378803 := bstep (se 1 (by rfl) ⟨1784102, by rfl⟩ : syracuseStep 2378803 = 3568205) B3568205
theorem B1879115 : Blo 1252444 1879115 := bstep (se 1 (by rfl) ⟨1409336, by rfl⟩ : syracuseStep 1879115 = 2818673) B2818673
theorem B1879127 : Blo 1252444 1879127 := bstep (se 1 (by rfl) ⟨1409345, by rfl⟩ : syracuseStep 1879127 = 2818691) B2818691
theorem B8031383 : Blo 1252444 8031383 := bstep (se 1 (by rfl) ⟨6023537, by rfl⟩ : syracuseStep 8031383 = 12047075) B12047075
theorem B2116759 : Blo 1252444 2116759 := bstep (se 1 (by rfl) ⟨1587569, by rfl⟩ : syracuseStep 2116759 = 3175139) B3175139
theorem B1879193 : Blo 1252444 1879193 := bstep (se 2 (by rfl) ⟨704697, by rfl⟩ : syracuseStep 1879193 = 1409395) B1409395
theorem B2821337 : Blo 1252444 2821337 := bstep (se 2 (by rfl) ⟨1058001, by rfl⟩ : syracuseStep 2821337 = 2116003) B2116003
theorem B1879307 : Blo 1252444 1879307 := bstep (se 1 (by rfl) ⟨1409480, by rfl⟩ : syracuseStep 1879307 = 2818961) B2818961
theorem B1879319 : Blo 1252444 1879319 := bstep (se 1 (by rfl) ⟨1409489, by rfl⟩ : syracuseStep 1879319 = 2818979) B2818979
theorem B2821427 : Blo 1252444 2821427 := bstep (se 1 (by rfl) ⟨2116070, by rfl⟩ : syracuseStep 2821427 = 4232141) B4232141
theorem B2821463 : Blo 1252444 2821463 := bstep (se 1 (by rfl) ⟨2116097, by rfl⟩ : syracuseStep 2821463 = 4232195) B4232195
theorem B1879385 : Blo 1252444 1879385 := bstep (se 2 (by rfl) ⟨704769, by rfl⟩ : syracuseStep 1879385 = 1409539) B1409539
theorem B9031013 : Blo 1252444 9031013 := bstep (se 4 (by rfl) ⟨846657, by rfl⟩ : syracuseStep 9031013 = 1693315) B1693315
theorem B1879499 : Blo 1252444 1879499 := bstep (se 1 (by rfl) ⟨1409624, by rfl⟩ : syracuseStep 1879499 = 2819249) B2819249
theorem B1879511 : Blo 1252444 1879511 := bstep (se 1 (by rfl) ⟨1409633, by rfl⟩ : syracuseStep 1879511 = 2819267) B2819267
theorem B2821643 : Blo 1252444 2821643 := bstep (se 1 (by rfl) ⟨2116232, by rfl⟩ : syracuseStep 2821643 = 4232465) B4232465
theorem B29355533 : Blo 1252444 29355533 := bstep (se 3 (by rfl) ⟨5504162, by rfl⟩ : syracuseStep 29355533 = 11008325) B11008325
theorem B1879577 : Blo 1252444 1879577 := bstep (se 2 (by rfl) ⟨704841, by rfl⟩ : syracuseStep 1879577 = 1409683) B1409683
theorem B2379289 : Blo 1252444 2379289 := bstep (se 2 (by rfl) ⟨892233, by rfl⟩ : syracuseStep 2379289 = 1784467) B1784467
theorem B2821697 : Blo 1252444 2821697 := bstep (se 2 (by rfl) ⟨1058136, by rfl⟩ : syracuseStep 2821697 = 2116273) B2116273
theorem B3567179 : Blo 1252444 3567179 := bstep (se 1 (by rfl) ⟨2675384, by rfl⟩ : syracuseStep 3567179 = 5350769) B5350769
theorem B3812939 : Blo 1252444 3812939 := bstep (se 1 (by rfl) ⟨2859704, by rfl⟩ : syracuseStep 3812939 = 5719409) B5719409
theorem B10710629 : Blo 1252444 10710629 := bstep (se 4 (by rfl) ⟨1004121, by rfl⟩ : syracuseStep 10710629 = 2008243) B2008243
theorem B1879691 : Blo 1252444 1879691 := bstep (se 1 (by rfl) ⟨1409768, by rfl⟩ : syracuseStep 1879691 = 2819537) B2819537
theorem B1879703 : Blo 1252444 1879703 := bstep (se 1 (by rfl) ⟨1409777, by rfl⟩ : syracuseStep 1879703 = 2819555) B2819555
theorem B1879769 : Blo 1252444 1879769 := bstep (se 2 (by rfl) ⟨704913, by rfl⟩ : syracuseStep 1879769 = 1409827) B1409827
theorem B3174167 : Blo 1252444 3174167 := bstep (se 1 (by rfl) ⟨2380625, by rfl⟩ : syracuseStep 3174167 = 4761251) B4761251
theorem B2821913 : Blo 1252444 2821913 := bstep (se 2 (by rfl) ⟨1058217, by rfl⟩ : syracuseStep 2821913 = 2116435) B2116435
theorem B1879883 : Blo 1252444 1879883 := bstep (se 1 (by rfl) ⟨1409912, by rfl⟩ : syracuseStep 1879883 = 2819825) B2819825
theorem B1879895 : Blo 1252444 1879895 := bstep (se 1 (by rfl) ⟨1409921, by rfl⟩ : syracuseStep 1879895 = 2819843) B2819843
theorem B2822003 : Blo 1252444 2822003 := bstep (se 1 (by rfl) ⟨2116502, by rfl⟩ : syracuseStep 2822003 = 4233005) B4233005
theorem B2822039 : Blo 1252444 2822039 := bstep (se 1 (by rfl) ⟨2116529, by rfl⟩ : syracuseStep 2822039 = 4233059) B4233059
theorem B1879961 : Blo 1252444 1879961 := bstep (se 2 (by rfl) ⟨704985, by rfl⟩ : syracuseStep 1879961 = 1409971) B1409971
theorem B4231115 : Blo 1252444 4231115 := bstep (se 1 (by rfl) ⟨3173336, by rfl⟩ : syracuseStep 4231115 = 6346673) B6346673
theorem B12857305 : Blo 1252444 12857305 := bstep (se 2 (by rfl) ⟨4821489, by rfl⟩ : syracuseStep 12857305 = 9642979) B9642979
theorem B1880075 : Blo 1252444 1880075 := bstep (se 1 (by rfl) ⟨1410056, by rfl⟩ : syracuseStep 1880075 = 2820113) B2820113
theorem B1880087 : Blo 1252444 1880087 := bstep (se 1 (by rfl) ⟨1410065, by rfl⟩ : syracuseStep 1880087 = 2820131) B2820131
theorem B1339435 : Blo 1252444 1339435 := bstep (se 1 (by rfl) ⟨1004576, by rfl⟩ : syracuseStep 1339435 = 2009153) B2009153
theorem B2379851 : Blo 1252444 2379851 := bstep (se 1 (by rfl) ⟨1784888, by rfl⟩ : syracuseStep 2379851 = 3569777) B3569777
theorem B2822219 : Blo 1252444 2822219 := bstep (se 1 (by rfl) ⟨2116664, by rfl⟩ : syracuseStep 2822219 = 4233329) B4233329
theorem B1880153 : Blo 1252444 1880153 := bstep (se 2 (by rfl) ⟨705057, by rfl⟩ : syracuseStep 1880153 = 1410115) B1410115
theorem B2822273 : Blo 1252444 2822273 := bstep (se 2 (by rfl) ⟨1058352, by rfl⟩ : syracuseStep 2822273 = 2116705) B2116705
theorem B1904791 : Blo 1252444 1904791 := bstep (se 1 (by rfl) ⟨1428593, by rfl⟩ : syracuseStep 1904791 = 2857187) B2857187
theorem B1880267 : Blo 1252444 1880267 := bstep (se 1 (by rfl) ⟨1410200, by rfl⟩ : syracuseStep 1880267 = 2820401) B2820401
theorem B1880279 : Blo 1252444 1880279 := bstep (se 1 (by rfl) ⟨1410209, by rfl⟩ : syracuseStep 1880279 = 2820419) B2820419
theorem B4231385 : Blo 1252444 4231385 := bstep (se 2 (by rfl) ⟨1586769, by rfl⟩ : syracuseStep 4231385 = 3173539) B3173539
theorem B2380033 : Blo 1252444 2380033 := bstep (se 2 (by rfl) ⟨892512, by rfl⟩ : syracuseStep 2380033 = 1785025) B1785025
theorem B10170629 : Blo 1252444 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B1880345 : Blo 1252444 1880345 := bstep (se 2 (by rfl) ⟨705129, by rfl⟩ : syracuseStep 1880345 = 1410259) B1410259
theorem B2822489 : Blo 1252444 2822489 := bstep (se 2 (by rfl) ⟨1058433, by rfl⟩ : syracuseStep 2822489 = 2116867) B2116867
theorem B6345053 : Blo 1252444 6345053 := bstep (se 3 (by rfl) ⟨1189697, by rfl⟩ : syracuseStep 6345053 = 2379395) B2379395
theorem B12874085 : Blo 1252444 12874085 := bstep (se 4 (by rfl) ⟨1206945, by rfl⟩ : syracuseStep 12874085 = 2413891) B2413891
theorem B1880459 : Blo 1252444 1880459 := bstep (se 1 (by rfl) ⟨1410344, by rfl⟩ : syracuseStep 1880459 = 2820689) B2820689
theorem B7139735 : Blo 1252444 7139735 := bstep (se 1 (by rfl) ⟨5354801, by rfl⟩ : syracuseStep 7139735 = 10709603) B10709603
theorem B1880471 : Blo 1252444 1880471 := bstep (se 1 (by rfl) ⟨1410353, by rfl⟩ : syracuseStep 1880471 = 2820707) B2820707
theorem B3174835 : Blo 1252444 3174835 := bstep (se 1 (by rfl) ⟨2381126, by rfl⟩ : syracuseStep 3174835 = 4762253) B4762253
theorem B4755905 : Blo 1252444 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B1880537 : Blo 1252444 1880537 := bstep (se 2 (by rfl) ⟨705201, by rfl⟩ : syracuseStep 1880537 = 1410403) B1410403
theorem B3174977 : Blo 1252444 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B1880651 : Blo 1252444 1880651 := bstep (se 1 (by rfl) ⟨1410488, by rfl⟩ : syracuseStep 1880651 = 2820977) B2820977
theorem B1880663 : Blo 1252444 1880663 := bstep (se 1 (by rfl) ⟨1410497, by rfl⟩ : syracuseStep 1880663 = 2820995) B2820995
theorem B3052121 : Blo 1252444 3052121 := bstep (se 2 (by rfl) ⟨1144545, by rfl⟩ : syracuseStep 3052121 = 2289091) B2289091
theorem B2675351 : Blo 1252444 2675351 := bstep (se 1 (by rfl) ⟨2006513, by rfl⟩ : syracuseStep 2675351 = 4013027) B4013027
theorem B1880729 : Blo 1252444 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B14275277 : Blo 1252444 14275277 := bstep (se 3 (by rfl) ⟨2676614, by rfl⟩ : syracuseStep 14275277 = 5353229) B5353229
theorem B1880843 : Blo 1252444 1880843 := bstep (se 1 (by rfl) ⟨1410632, by rfl⟩ : syracuseStep 1880843 = 2821265) B2821265
theorem B1880855 : Blo 1252444 1880855 := bstep (se 1 (by rfl) ⟨1410641, by rfl⟩ : syracuseStep 1880855 = 2821283) B2821283
theorem B2675521 : Blo 1252444 2675521 := bstep (se 2 (by rfl) ⟨1003320, by rfl⟩ : syracuseStep 2675521 = 2006641) B2006641
theorem B1880921 : Blo 1252444 1880921 := bstep (se 2 (by rfl) ⟨705345, by rfl⟩ : syracuseStep 1880921 = 1410691) B1410691
theorem B4518749 : Blo 1252444 4518749 := bstep (se 3 (by rfl) ⟨847265, by rfl⟩ : syracuseStep 4518749 = 1694531) B1694531
theorem B1586071 : Blo 1252444 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B4232087 : Blo 1252444 4232087 := bstep (se 1 (by rfl) ⟨3174065, by rfl⟩ : syracuseStep 4232087 = 6348131) B6348131
theorem B1881035 : Blo 1252444 1881035 := bstep (se 1 (by rfl) ⟨1410776, by rfl⟩ : syracuseStep 1881035 = 2821553) B2821553
theorem B2380747 : Blo 1252444 2380747 := bstep (se 1 (by rfl) ⟨1785560, by rfl⟩ : syracuseStep 2380747 = 3571121) B3571121
theorem B1881047 : Blo 1252444 1881047 := bstep (se 1 (by rfl) ⟨1410785, by rfl⟩ : syracuseStep 1881047 = 2821571) B2821571
theorem B2380823 : Blo 1252444 2380823 := bstep (se 1 (by rfl) ⟨1785617, by rfl⟩ : syracuseStep 2380823 = 3571235) B3571235
theorem B1881113 : Blo 1252444 1881113 := bstep (se 2 (by rfl) ⟨705417, by rfl⟩ : syracuseStep 1881113 = 1410835) B1410835
theorem B1881227 : Blo 1252444 1881227 := bstep (se 1 (by rfl) ⟨1410920, by rfl⟩ : syracuseStep 1881227 = 2821841) B2821841
theorem B2675863 : Blo 1252444 2675863 := bstep (se 1 (by rfl) ⟨2006897, by rfl⟩ : syracuseStep 2675863 = 4013795) B4013795
theorem B1881239 : Blo 1252444 1881239 := bstep (se 1 (by rfl) ⟨1410929, by rfl⟩ : syracuseStep 1881239 = 2821859) B2821859
theorem B2258135 : Blo 1252444 2258135 := bstep (se 1 (by rfl) ⟨1693601, by rfl⟩ : syracuseStep 2258135 = 3387203) B3387203
theorem B10859737 : Blo 1252444 10859737 := bstep (se 2 (by rfl) ⟨4072401, by rfl⟩ : syracuseStep 10859737 = 8144803) B8144803
theorem B1881305 : Blo 1252444 1881305 := bstep (se 2 (by rfl) ⟨705489, by rfl⟩ : syracuseStep 1881305 = 1410979) B1410979
theorem B1881419 : Blo 1252444 1881419 := bstep (se 1 (by rfl) ⟨1411064, by rfl⟩ : syracuseStep 1881419 = 2822129) B2822129
theorem B1881431 : Blo 1252444 1881431 := bstep (se 1 (by rfl) ⟨1411073, by rfl⟩ : syracuseStep 1881431 = 2822147) B2822147
theorem B1881497 : Blo 1252444 1881497 := bstep (se 2 (by rfl) ⟨705561, by rfl⟩ : syracuseStep 1881497 = 1411123) B1411123
theorem B4232627 : Blo 1252444 4232627 := bstep (se 1 (by rfl) ⟨3174470, by rfl⟩ : syracuseStep 4232627 = 6348941) B6348941
theorem B1881611 : Blo 1252444 1881611 := bstep (se 1 (by rfl) ⟨1411208, by rfl⟩ : syracuseStep 1881611 = 2822417) B2822417
theorem B1881623 : Blo 1252444 1881623 := bstep (se 1 (by rfl) ⟨1411217, by rfl⟩ : syracuseStep 1881623 = 2822435) B2822435
theorem B4232897 : Blo 1252444 4232897 := bstep (se 2 (by rfl) ⟨1587336, by rfl⟩ : syracuseStep 4232897 = 3174673) B3174673
theorem B1586891 : Blo 1252444 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B6100697 : Blo 1252444 6100697 := bstep (se 2 (by rfl) ⟨2287761, by rfl⟩ : syracuseStep 6100697 = 4575523) B4575523
theorem B10860293 : Blo 1252444 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B4757393 : Blo 1252444 4757393 := bstep (se 2 (by rfl) ⟨1784022, by rfl⟩ : syracuseStep 4757393 = 3568045) B3568045
theorem B2676683 : Blo 1252444 2676683 := bstep (se 1 (by rfl) ⟨2007512, by rfl⟩ : syracuseStep 2676683 = 4015025) B4015025
theorem B3569629 : Blo 1252444 3569629 := bstep (se 3 (by rfl) ⟨669305, by rfl⟩ : syracuseStep 3569629 = 1338611) B1338611
theorem B4290583 : Blo 1252444 4290583 := bstep (se 1 (by rfl) ⟨3217937, by rfl⟩ : syracuseStep 4290583 = 6435875) B6435875
theorem B3012673 : Blo 1252444 3012673 := bstep (se 2 (by rfl) ⟨1129752, by rfl⟩ : syracuseStep 3012673 = 2259505) B2259505
theorem B32553035 : Blo 1252444 32553035 := bstep (se 1 (by rfl) ⟨24414776, by rfl⟩ : syracuseStep 32553035 = 48829553) B48829553
theorem B2259137 : Blo 1252444 2259137 := bstep (se 2 (by rfl) ⟨847176, by rfl⟩ : syracuseStep 2259137 = 1694353) B1694353
theorem B10713293 : Blo 1252444 10713293 := bstep (se 3 (by rfl) ⟨2008742, by rfl⟩ : syracuseStep 10713293 = 4017485) B4017485
theorem B4233437 : Blo 1252444 4233437 := bstep (se 3 (by rfl) ⟨793769, by rfl⟩ : syracuseStep 4233437 = 1587539) B1587539
theorem B3528983 : Blo 1252444 3528983 := bstep (se 1 (by rfl) ⟨2646737, by rfl⟩ : syracuseStep 3528983 = 5293475) B5293475
theorem B18061613 : Blo 1252444 18061613 := bstep (se 3 (by rfl) ⟨3386552, by rfl⟩ : syracuseStep 18061613 = 6773105) B6773105
theorem B2677043 : Blo 1252444 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B5355827 : Blo 1252444 5355827 := bstep (se 1 (by rfl) ⟨4016870, by rfl⟩ : syracuseStep 5355827 = 8033741) B8033741
theorem B11426113 : Blo 1252444 11426113 := bstep (se 2 (by rfl) ⟨4284792, by rfl⟩ : syracuseStep 11426113 = 8569585) B8569585
theorem B4757849 : Blo 1252444 4757849 := bstep (se 2 (by rfl) ⟨1784193, by rfl⟩ : syracuseStep 4757849 = 3568387) B3568387
theorem B1587595 : Blo 1252444 1587595 := bstep (se 1 (by rfl) ⟨1190696, by rfl⟩ : syracuseStep 1587595 = 2381393) B2381393
theorem B6347159 : Blo 1252444 6347159 := bstep (se 1 (by rfl) ⟨4760369, by rfl⟩ : syracuseStep 6347159 = 9520739) B9520739
theorem B2857369 : Blo 1252444 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B18078221 : Blo 1252444 18078221 := bstep (se 3 (by rfl) ⟨3389666, by rfl⟩ : syracuseStep 18078221 = 6779333) B6779333
theorem B4758061 : Blo 1252444 4758061 := bstep (se 3 (by rfl) ⟨892136, by rfl⟩ : syracuseStep 4758061 = 1784273) B1784273
theorem B15243869 : Blo 1252444 15243869 := bstep (se 3 (by rfl) ⟨2858225, by rfl⟩ : syracuseStep 15243869 = 5716451) B5716451
theorem B8034947 : Blo 1252444 8034947 := bstep (se 1 (by rfl) ⟨6026210, by rfl⟩ : syracuseStep 8034947 = 12052421) B12052421
theorem B11426483 : Blo 1252444 11426483 := bstep (se 1 (by rfl) ⟨8569862, by rfl⟩ : syracuseStep 11426483 = 17139725) B17139725
theorem B3013337 : Blo 1252444 3013337 := bstep (se 2 (by rfl) ⟨1130001, by rfl⟩ : syracuseStep 3013337 = 2260003) B2260003
theorem B10156805 : Blo 1252444 10156805 := bstep (se 4 (by rfl) ⟨952200, by rfl⟩ : syracuseStep 10156805 = 1904401) B1904401
theorem B1784587 : Blo 1252444 1784587 := bstep (se 1 (by rfl) ⟨1338440, by rfl⟩ : syracuseStep 1784587 = 2676881) B2676881
theorem B4070209 : Blo 1252444 4070209 := bstep (se 2 (by rfl) ⟨1526328, by rfl⟩ : syracuseStep 4070209 = 3052657) B3052657
theorem B3054401 : Blo 1252444 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B4758365 : Blo 1252444 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B11443045 : Blo 1252444 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B4021213 : Blo 1252444 4021213 := bstep (se 3 (by rfl) ⟨753977, by rfl⟩ : syracuseStep 4021213 = 1507955) B1507955
theorem B1252459 : Blo 1252444 1252459 := bstep (se 1 (by rfl) ⟨939344, by rfl⟩ : syracuseStep 1252459 = 1878689) B1878689
theorem B1252471 : Blo 1252444 1252471 := bstep (se 1 (by rfl) ⟨939353, by rfl⟩ : syracuseStep 1252471 = 1878707) B1878707
theorem B1252491 : Blo 1252444 1252491 := bstep (se 1 (by rfl) ⟨939368, by rfl⟩ : syracuseStep 1252491 = 1878737) B1878737
theorem B1252503 : Blo 1252444 1252503 := bstep (se 1 (by rfl) ⟨939377, by rfl⟩ : syracuseStep 1252503 = 1878755) B1878755
theorem B1252523 : Blo 1252444 1252523 := bstep (se 1 (by rfl) ⟨939392, by rfl⟩ : syracuseStep 1252523 = 1878785) B1878785
theorem B1252535 : Blo 1252444 1252535 := bstep (se 1 (by rfl) ⟨939401, by rfl⟩ : syracuseStep 1252535 = 1878803) B1878803
theorem B5078209 : Blo 1252444 5078209 := bstep (se 2 (by rfl) ⟨1904328, by rfl⟩ : syracuseStep 5078209 = 3808657) B3808657
theorem B1252555 : Blo 1252444 1252555 := bstep (se 1 (by rfl) ⟨939416, by rfl⟩ : syracuseStep 1252555 = 1878833) B1878833
theorem B1252567 : Blo 1252444 1252567 := bstep (se 1 (by rfl) ⟨939425, by rfl⟩ : syracuseStep 1252567 = 1878851) B1878851
theorem B3570905 : Blo 1252444 3570905 := bstep (se 2 (by rfl) ⟨1339089, by rfl⟩ : syracuseStep 3570905 = 2678179) B2678179
theorem B1252587 : Blo 1252444 1252587 := bstep (se 1 (by rfl) ⟨939440, by rfl⟩ : syracuseStep 1252587 = 1878881) B1878881
theorem B1252599 : Blo 1252444 1252599 := bstep (se 1 (by rfl) ⟨939449, by rfl⟩ : syracuseStep 1252599 = 1878899) B1878899
theorem B1252619 : Blo 1252444 1252619 := bstep (se 1 (by rfl) ⟨939464, by rfl⟩ : syracuseStep 1252619 = 1878929) B1878929
theorem B1252631 : Blo 1252444 1252631 := bstep (se 1 (by rfl) ⟨939473, by rfl⟩ : syracuseStep 1252631 = 1878947) B1878947
theorem B1252651 : Blo 1252444 1252651 := bstep (se 1 (by rfl) ⟨939488, by rfl⟩ : syracuseStep 1252651 = 1878977) B1878977
theorem B1252663 : Blo 1252444 1252663 := bstep (se 1 (by rfl) ⟨939497, by rfl⟩ : syracuseStep 1252663 = 1878995) B1878995
theorem B1252683 : Blo 1252444 1252683 := bstep (se 1 (by rfl) ⟨939512, by rfl⟩ : syracuseStep 1252683 = 1879025) B1879025
theorem B1252695 : Blo 1252444 1252695 := bstep (se 1 (by rfl) ⟨939521, by rfl⟩ : syracuseStep 1252695 = 1879043) B1879043
theorem B1252715 : Blo 1252444 1252715 := bstep (se 1 (by rfl) ⟨939536, by rfl⟩ : syracuseStep 1252715 = 1879073) B1879073
theorem B1252727 : Blo 1252444 1252727 := bstep (se 1 (by rfl) ⟨939545, by rfl⟩ : syracuseStep 1252727 = 1879091) B1879091
theorem B1252747 : Blo 1252444 1252747 := bstep (se 1 (by rfl) ⟨939560, by rfl⟩ : syracuseStep 1252747 = 1879121) B1879121
theorem B1252759 : Blo 1252444 1252759 := bstep (se 1 (by rfl) ⟨939569, by rfl⟩ : syracuseStep 1252759 = 1879139) B1879139
theorem B1252779 : Blo 1252444 1252779 := bstep (se 1 (by rfl) ⟨939584, by rfl⟩ : syracuseStep 1252779 = 1879169) B1879169
theorem B1252791 : Blo 1252444 1252791 := bstep (se 1 (by rfl) ⟨939593, by rfl⟩ : syracuseStep 1252791 = 1879187) B1879187
theorem B1252811 : Blo 1252444 1252811 := bstep (se 1 (by rfl) ⟨939608, by rfl⟩ : syracuseStep 1252811 = 1879217) B1879217
theorem B1252823 : Blo 1252444 1252823 := bstep (se 1 (by rfl) ⟨939617, by rfl⟩ : syracuseStep 1252823 = 1879235) B1879235
theorem B9649625 : Blo 1252444 9649625 := bstep (se 2 (by rfl) ⟨3618609, by rfl⟩ : syracuseStep 9649625 = 7237219) B7237219
theorem B1252843 : Blo 1252444 1252843 := bstep (se 1 (by rfl) ⟨939632, by rfl⟩ : syracuseStep 1252843 = 1879265) B1879265
theorem B1252855 : Blo 1252444 1252855 := bstep (se 1 (by rfl) ⟨939641, by rfl⟩ : syracuseStep 1252855 = 1879283) B1879283
theorem B1252875 : Blo 1252444 1252875 := bstep (se 1 (by rfl) ⟨939656, by rfl⟩ : syracuseStep 1252875 = 1879313) B1879313
theorem B1252887 : Blo 1252444 1252887 := bstep (se 1 (by rfl) ⟨939665, by rfl⟩ : syracuseStep 1252887 = 1879331) B1879331
theorem B1252907 : Blo 1252444 1252907 := bstep (se 1 (by rfl) ⟨939680, by rfl⟩ : syracuseStep 1252907 = 1879361) B1879361
theorem B8027693 : Blo 1252444 8027693 := bstep (se 3 (by rfl) ⟨1505192, by rfl⟩ : syracuseStep 8027693 = 3010385) B3010385
theorem B1252919 : Blo 1252444 1252919 := bstep (se 1 (by rfl) ⟨939689, by rfl⟩ : syracuseStep 1252919 = 1879379) B1879379
theorem B1252939 : Blo 1252444 1252939 := bstep (se 1 (by rfl) ⟨939704, by rfl⟩ : syracuseStep 1252939 = 1879409) B1879409
theorem B1252951 : Blo 1252444 1252951 := bstep (se 1 (by rfl) ⟨939713, by rfl⟩ : syracuseStep 1252951 = 1879427) B1879427
theorem B1252971 : Blo 1252444 1252971 := bstep (se 1 (by rfl) ⟨939728, by rfl⟩ : syracuseStep 1252971 = 1879457) B1879457
theorem B1252983 : Blo 1252444 1252983 := bstep (se 1 (by rfl) ⟨939737, by rfl⟩ : syracuseStep 1252983 = 1879475) B1879475
theorem B1253003 : Blo 1252444 1253003 := bstep (se 1 (by rfl) ⟨939752, by rfl⟩ : syracuseStep 1253003 = 1879505) B1879505
theorem B1253015 : Blo 1252444 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B1253035 : Blo 1252444 1253035 := bstep (se 1 (by rfl) ⟨939776, by rfl⟩ : syracuseStep 1253035 = 1879553) B1879553
theorem B1253047 : Blo 1252444 1253047 := bstep (se 1 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 1253047 = 1879571) B1879571
theorem B1253067 : Blo 1252444 1253067 := bstep (se 1 (by rfl) ⟨939800, by rfl⟩ : syracuseStep 1253067 = 1879601) B1879601
theorem B1253079 : Blo 1252444 1253079 := bstep (se 1 (by rfl) ⟨939809, by rfl⟩ : syracuseStep 1253079 = 1879619) B1879619
theorem B1253099 : Blo 1252444 1253099 := bstep (se 1 (by rfl) ⟨939824, by rfl⟩ : syracuseStep 1253099 = 1879649) B1879649
theorem B1253111 : Blo 1252444 1253111 := bstep (se 1 (by rfl) ⟨939833, by rfl⟩ : syracuseStep 1253111 = 1879667) B1879667
theorem B2006795 : Blo 1252444 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B1253131 : Blo 1252444 1253131 := bstep (se 1 (by rfl) ⟨939848, by rfl⟩ : syracuseStep 1253131 = 1879697) B1879697
theorem B1253143 : Blo 1252444 1253143 := bstep (se 1 (by rfl) ⟨939857, by rfl⟩ : syracuseStep 1253143 = 1879715) B1879715
theorem B1449751 : Blo 1252444 1449751 := bstep (se 1 (by rfl) ⟨1087313, by rfl⟩ : syracuseStep 1449751 = 2174627) B2174627
theorem B1253163 : Blo 1252444 1253163 := bstep (se 1 (by rfl) ⟨939872, by rfl⟩ : syracuseStep 1253163 = 1879745) B1879745
theorem B1253175 : Blo 1252444 1253175 := bstep (se 1 (by rfl) ⟨939881, by rfl⟩ : syracuseStep 1253175 = 1879763) B1879763
theorem B1253195 : Blo 1252444 1253195 := bstep (se 1 (by rfl) ⟨939896, by rfl⟩ : syracuseStep 1253195 = 1879793) B1879793
theorem B1253207 : Blo 1252444 1253207 := bstep (se 1 (by rfl) ⟨939905, by rfl⟩ : syracuseStep 1253207 = 1879811) B1879811
theorem B1253227 : Blo 1252444 1253227 := bstep (se 1 (by rfl) ⟨939920, by rfl⟩ : syracuseStep 1253227 = 1879841) B1879841
theorem B1253239 : Blo 1252444 1253239 := bstep (se 1 (by rfl) ⟨939929, by rfl⟩ : syracuseStep 1253239 = 1879859) B1879859
theorem B9035651 : Blo 1252444 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B1253259 : Blo 1252444 1253259 := bstep (se 1 (by rfl) ⟨939944, by rfl⟩ : syracuseStep 1253259 = 1879889) B1879889
theorem B1253271 : Blo 1252444 1253271 := bstep (se 1 (by rfl) ⟨939953, by rfl⟩ : syracuseStep 1253271 = 1879907) B1879907
theorem B1253291 : Blo 1252444 1253291 := bstep (se 1 (by rfl) ⟨939968, by rfl⟩ : syracuseStep 1253291 = 1879937) B1879937
theorem B1253303 : Blo 1252444 1253303 := bstep (se 1 (by rfl) ⟨939977, by rfl⟩ : syracuseStep 1253303 = 1879955) B1879955
theorem B1253323 : Blo 1252444 1253323 := bstep (se 1 (by rfl) ⟨939992, by rfl⟩ : syracuseStep 1253323 = 1879985) B1879985
theorem B2818007 : Blo 1252444 2818007 := bstep (se 1 (by rfl) ⟨2113505, by rfl⟩ : syracuseStep 2818007 = 4227011) B4227011
theorem B1253335 : Blo 1252444 1253335 := bstep (se 1 (by rfl) ⟨940001, by rfl⟩ : syracuseStep 1253335 = 1880003) B1880003
theorem B1785817 : Blo 1252444 1785817 := bstep (se 2 (by rfl) ⟨669681, by rfl⟩ : syracuseStep 1785817 = 1339363) B1339363
theorem B1253355 : Blo 1252444 1253355 := bstep (se 1 (by rfl) ⟨940016, by rfl⟩ : syracuseStep 1253355 = 1880033) B1880033
theorem B1253367 : Blo 1252444 1253367 := bstep (se 1 (by rfl) ⟨940025, by rfl⟩ : syracuseStep 1253367 = 1880051) B1880051
theorem B1253383 : Blo 1252444 1253383 := bstep (se 1 (by rfl) ⟨940037, by rfl⟩ : syracuseStep 1253383 = 1880075) B1880075
theorem B1253391 : Blo 1252444 1253391 := bstep (se 1 (by rfl) ⟨940043, by rfl⟩ : syracuseStep 1253391 = 1880087) B1880087
theorem B1253435 : Blo 1252444 1253435 := bstep (se 1 (by rfl) ⟨940076, by rfl⟩ : syracuseStep 1253435 = 1880153) B1880153
theorem B10707005 : Blo 1252444 10707005 := bstep (se 3 (by rfl) ⟨2007563, by rfl⟩ : syracuseStep 10707005 = 4015127) B4015127
theorem B27091037 : Blo 1252444 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B1253511 : Blo 1252444 1253511 := bstep (se 1 (by rfl) ⟨940133, by rfl⟩ : syracuseStep 1253511 = 1880267) B1880267
theorem B1253519 : Blo 1252444 1253519 := bstep (se 1 (by rfl) ⟨940139, by rfl⟩ : syracuseStep 1253519 = 1880279) B1880279
theorem B1253563 : Blo 1252444 1253563 := bstep (se 1 (by rfl) ⟨940172, by rfl⟩ : syracuseStep 1253563 = 1880345) B1880345
theorem B2539721 : Blo 1252444 2539721 := bstep (se 2 (by rfl) ⟨952395, by rfl⟩ : syracuseStep 2539721 = 1904791) B1904791
theorem B15466697 : Blo 1252444 15466697 := bstep (se 2 (by rfl) ⟨5800011, by rfl⟩ : syracuseStep 15466697 = 11600023) B11600023
theorem B7143653 : Blo 1252444 7143653 := bstep (se 4 (by rfl) ⟨669717, by rfl⟩ : syracuseStep 7143653 = 1339435) B1339435
theorem B1409287 : Blo 1252444 1409287 := bstep (se 1 (by rfl) ⟨1056965, by rfl⟩ : syracuseStep 1409287 = 2113931) B2113931
theorem B1253639 : Blo 1252444 1253639 := bstep (se 1 (by rfl) ⟨940229, by rfl⟩ : syracuseStep 1253639 = 1880459) B1880459
theorem B4759823 : Blo 1252444 4759823 := bstep (se 1 (by rfl) ⟨3569867, by rfl⟩ : syracuseStep 4759823 = 7139735) B7139735
theorem B1253647 : Blo 1252444 1253647 := bstep (se 1 (by rfl) ⟨940235, by rfl⟩ : syracuseStep 1253647 = 1880471) B1880471
theorem B3170603 : Blo 1252444 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B1253691 : Blo 1252444 1253691 := bstep (se 1 (by rfl) ⟨940268, by rfl⟩ : syracuseStep 1253691 = 1880537) B1880537
theorem B4227443 : Blo 1252444 4227443 := bstep (se 1 (by rfl) ⟨3170582, by rfl⟩ : syracuseStep 4227443 = 6341165) B6341165
theorem B2818439 : Blo 1252444 2818439 := bstep (se 1 (by rfl) ⟨2113829, by rfl⟩ : syracuseStep 2818439 = 4227659) B4227659
theorem B1253767 : Blo 1252444 1253767 := bstep (se 1 (by rfl) ⟨940325, by rfl⟩ : syracuseStep 1253767 = 1880651) B1880651
theorem B1253775 : Blo 1252444 1253775 := bstep (se 1 (by rfl) ⟨940331, by rfl⟩ : syracuseStep 1253775 = 1880663) B1880663
theorem B1409467 : Blo 1252444 1409467 := bstep (se 1 (by rfl) ⟨1057100, by rfl⟩ : syracuseStep 1409467 = 2114201) B2114201
theorem B1253819 : Blo 1252444 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B6349265 : Blo 1252444 6349265 := bstep (se 2 (by rfl) ⟨2380974, by rfl⟩ : syracuseStep 6349265 = 4761949) B4761949
theorem B1253895 : Blo 1252444 1253895 := bstep (se 1 (by rfl) ⟨940421, by rfl⟩ : syracuseStep 1253895 = 1880843) B1880843
theorem B1253903 : Blo 1252444 1253903 := bstep (se 1 (by rfl) ⟨940427, by rfl⟩ : syracuseStep 1253903 = 1880855) B1880855
theorem B3809825 : Blo 1252444 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B2818619 : Blo 1252444 2818619 := bstep (se 1 (by rfl) ⟨2113964, by rfl⟩ : syracuseStep 2818619 = 4227929) B4227929
theorem B1253947 : Blo 1252444 1253947 := bstep (se 1 (by rfl) ⟨940460, by rfl⟩ : syracuseStep 1253947 = 1880921) B1880921
theorem B2114167 : Blo 1252444 2114167 := bstep (se 1 (by rfl) ⟨1585625, by rfl⟩ : syracuseStep 2114167 = 3171251) B3171251
theorem B1254023 : Blo 1252444 1254023 := bstep (se 1 (by rfl) ⟨940517, by rfl⟩ : syracuseStep 1254023 = 1881035) B1881035
theorem B1254031 : Blo 1252444 1254031 := bstep (se 1 (by rfl) ⟨940523, by rfl⟩ : syracuseStep 1254031 = 1881047) B1881047
theorem B7144109 : Blo 1252444 7144109 := bstep (se 3 (by rfl) ⟨1339520, by rfl⟩ : syracuseStep 7144109 = 2679041) B2679041
theorem B2818745 : Blo 1252444 2818745 := bstep (se 2 (by rfl) ⟨1057029, by rfl⟩ : syracuseStep 2818745 = 2114059) B2114059
theorem B1254075 : Blo 1252444 1254075 := bstep (se 1 (by rfl) ⟨940556, by rfl⟩ : syracuseStep 1254075 = 1881113) B1881113
theorem B1254151 : Blo 1252444 1254151 := bstep (se 1 (by rfl) ⟨940613, by rfl⟩ : syracuseStep 1254151 = 1881227) B1881227
theorem B1254159 : Blo 1252444 1254159 := bstep (se 1 (by rfl) ⟨940619, by rfl⟩ : syracuseStep 1254159 = 1881239) B1881239
theorem B2114363 : Blo 1252444 2114363 := bstep (se 1 (by rfl) ⟨1585772, by rfl⟩ : syracuseStep 2114363 = 3171545) B3171545
theorem B1254203 : Blo 1252444 1254203 := bstep (se 1 (by rfl) ⟨940652, by rfl⟩ : syracuseStep 1254203 = 1881305) B1881305
theorem B1254279 : Blo 1252444 1254279 := bstep (se 1 (by rfl) ⟨940709, by rfl⟩ : syracuseStep 1254279 = 1881419) B1881419
theorem B1409935 : Blo 1252444 1409935 := bstep (se 1 (by rfl) ⟨1057451, by rfl⟩ : syracuseStep 1409935 = 2114903) B2114903
theorem B1254287 : Blo 1252444 1254287 := bstep (se 1 (by rfl) ⟨940715, by rfl⟩ : syracuseStep 1254287 = 1881431) B1881431
theorem B1254331 : Blo 1252444 1254331 := bstep (se 1 (by rfl) ⟨940748, by rfl⟩ : syracuseStep 1254331 = 1881497) B1881497
theorem B1254407 : Blo 1252444 1254407 := bstep (se 1 (by rfl) ⟨940805, by rfl⟩ : syracuseStep 1254407 = 1881611) B1881611
theorem B2819087 : Blo 1252444 2819087 := bstep (se 1 (by rfl) ⟨2114315, by rfl⟩ : syracuseStep 2819087 = 4228631) B4228631
theorem B1254415 : Blo 1252444 1254415 := bstep (se 1 (by rfl) ⟨940811, by rfl⟩ : syracuseStep 1254415 = 1881623) B1881623
theorem B2819105 : Blo 1252444 2819105 := bstep (se 2 (by rfl) ⟨1057164, by rfl⟩ : syracuseStep 2819105 = 2114329) B2114329
theorem B2114761 : Blo 1252444 2114761 := bstep (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) B1586071
theorem B25732333 : Blo 1252444 25732333 := bstep (se 3 (by rfl) ⟨4824812, by rfl⟩ : syracuseStep 25732333 = 9649625) B9649625
theorem B3171595 : Blo 1252444 3171595 := bstep (se 1 (by rfl) ⟨2378696, by rfl⟩ : syracuseStep 3171595 = 4757393) B4757393
theorem B7136545 : Blo 1252444 7136545 := bstep (se 2 (by rfl) ⟨2676204, by rfl⟩ : syracuseStep 7136545 = 5352409) B5352409
theorem B2819447 : Blo 1252444 2819447 := bstep (se 1 (by rfl) ⟨2114585, by rfl⟩ : syracuseStep 2819447 = 4229171) B4229171
theorem B21702023 : Blo 1252444 21702023 := bstep (se 1 (by rfl) ⟨16276517, by rfl⟩ : syracuseStep 21702023 = 32553035) B32553035
theorem B1410439 : Blo 1252444 1410439 := bstep (se 1 (by rfl) ⟨1057829, by rfl⟩ : syracuseStep 1410439 = 2115659) B2115659
theorem B3171737 : Blo 1252444 3171737 := bstep (se 2 (by rfl) ⟨1189401, by rfl⟩ : syracuseStep 3171737 = 2378803) B2378803
theorem B2352655 : Blo 1252444 2352655 := bstep (se 1 (by rfl) ⟨1764491, by rfl⟩ : syracuseStep 2352655 = 3528983) B3528983
theorem B9512477 : Blo 1252444 9512477 := bstep (se 3 (by rfl) ⟨1783589, by rfl⟩ : syracuseStep 9512477 = 3567179) B3567179
theorem B2819627 : Blo 1252444 2819627 := bstep (se 1 (by rfl) ⟨2114720, by rfl⟩ : syracuseStep 2819627 = 4229441) B4229441
theorem B3171899 : Blo 1252444 3171899 := bstep (se 1 (by rfl) ⟨2378924, by rfl⟩ : syracuseStep 3171899 = 4757849) B4757849
theorem B1410619 : Blo 1252444 1410619 := bstep (se 1 (by rfl) ⟨1057964, by rfl⟩ : syracuseStep 1410619 = 2115929) B2115929
theorem B12052147 : Blo 1252444 12052147 := bstep (se 1 (by rfl) ⟨9039110, by rfl⟩ : syracuseStep 12052147 = 18078221) B18078221
theorem B2008891 : Blo 1252444 2008891 := bstep (se 1 (by rfl) ⟨1506668, by rfl⟩ : syracuseStep 2008891 = 3013337) B3013337
theorem B2115463 : Blo 1252444 2115463 := bstep (se 1 (by rfl) ⟨1586597, by rfl⟩ : syracuseStep 2115463 = 3173195) B3173195
theorem B3172243 : Blo 1252444 3172243 := bstep (se 1 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 3172243 = 4758365) B4758365
theorem B2819987 : Blo 1252444 2819987 := bstep (se 1 (by rfl) ⟨2114990, by rfl⟩ : syracuseStep 2819987 = 4229981) B4229981
theorem B2820041 : Blo 1252444 2820041 := bstep (se 2 (by rfl) ⟨1057515, by rfl⟩ : syracuseStep 2820041 = 2115031) B2115031
theorem B5425163 : Blo 1252444 5425163 := bstep (se 1 (by rfl) ⟨4068872, by rfl⟩ : syracuseStep 5425163 = 8137745) B8137745
theorem B1411087 : Blo 1252444 1411087 := bstep (se 1 (by rfl) ⟨1058315, by rfl⟩ : syracuseStep 1411087 = 2116631) B2116631
theorem B5351453 : Blo 1252444 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B3172385 : Blo 1252444 3172385 := bstep (se 2 (by rfl) ⟨1189644, by rfl⟩ : syracuseStep 3172385 = 2379289) B2379289
theorem B24095069 : Blo 1252444 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B5351795 : Blo 1252444 5351795 := bstep (se 1 (by rfl) ⟨4013846, by rfl⟩ : syracuseStep 5351795 = 8027693) B8027693
theorem B2541959 : Blo 1252444 2541959 := bstep (se 1 (by rfl) ⟨1906469, by rfl⟩ : syracuseStep 2541959 = 3812939) B3812939
theorem B2116111 : Blo 1252444 2116111 := bstep (se 1 (by rfl) ⟨1587083, by rfl⟩ : syracuseStep 2116111 = 3174167) B3174167
theorem B7137821 : Blo 1252444 7137821 := bstep (se 3 (by rfl) ⟨1338341, by rfl⟩ : syracuseStep 7137821 = 2676683) B2676683
theorem B2820743 : Blo 1252444 2820743 := bstep (se 1 (by rfl) ⟨2115557, by rfl⟩ : syracuseStep 2820743 = 4231115) B4231115
theorem B1878671 : Blo 1252444 1878671 := bstep (se 1 (by rfl) ⟨1409003, by rfl⟩ : syracuseStep 1878671 = 2818007) B2818007
theorem B1878713 : Blo 1252444 1878713 := bstep (se 2 (by rfl) ⟨704517, by rfl⟩ : syracuseStep 1878713 = 1409035) B1409035
theorem B5720777 : Blo 1252444 5720777 := bstep (se 2 (by rfl) ⟨2145291, by rfl⟩ : syracuseStep 5720777 = 4290583) B4290583
theorem B4016897 : Blo 1252444 4016897 := bstep (se 2 (by rfl) ⟨1506336, by rfl⟩ : syracuseStep 4016897 = 3012673) B3012673
theorem B1878791 : Blo 1252444 1878791 := bstep (se 1 (by rfl) ⟨1409093, by rfl⟩ : syracuseStep 1878791 = 2818187) B2818187
theorem B28945187 : Blo 1252444 28945187 := bstep (se 1 (by rfl) ⟨21708890, by rfl⟩ : syracuseStep 28945187 = 43417781) B43417781
theorem B1878827 : Blo 1252444 1878827 := bstep (se 1 (by rfl) ⟨1409120, by rfl⟩ : syracuseStep 1878827 = 2818241) B2818241
theorem B2820923 : Blo 1252444 2820923 := bstep (se 1 (by rfl) ⟨2115692, by rfl⟩ : syracuseStep 2820923 = 4231385) B4231385
theorem B1878857 : Blo 1252444 1878857 := bstep (se 2 (by rfl) ⟨704571, by rfl⟩ : syracuseStep 1878857 = 1409143) B1409143
theorem B3009415 : Blo 1252444 3009415 := bstep (se 1 (by rfl) ⟨2257061, by rfl⟩ : syracuseStep 3009415 = 4514123) B4514123
theorem B4230035 : Blo 1252444 4230035 := bstep (se 1 (by rfl) ⟨3172526, by rfl⟩ : syracuseStep 4230035 = 6345053) B6345053
theorem B2821049 : Blo 1252444 2821049 := bstep (se 2 (by rfl) ⟨1057893, by rfl⟩ : syracuseStep 2821049 = 2115787) B2115787
theorem B1878971 : Blo 1252444 1878971 := bstep (se 1 (by rfl) ⟨1409228, by rfl⟩ : syracuseStep 1878971 = 2818457) B2818457
theorem B1879031 : Blo 1252444 1879031 := bstep (se 1 (by rfl) ⟨1409273, by rfl⟩ : syracuseStep 1879031 = 2818547) B2818547
theorem B3173377 : Blo 1252444 3173377 := bstep (se 2 (by rfl) ⟨1190016, by rfl⟩ : syracuseStep 3173377 = 2380033) B2380033
theorem B1879055 : Blo 1252444 1879055 := bstep (se 1 (by rfl) ⟨1409291, by rfl⟩ : syracuseStep 1879055 = 2818583) B2818583
theorem B2116651 : Blo 1252444 2116651 := bstep (se 1 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 2116651 = 3174977) B3174977
theorem B1879097 : Blo 1252444 1879097 := bstep (se 2 (by rfl) ⟨704661, by rfl⟩ : syracuseStep 1879097 = 1409323) B1409323
theorem B1338427 : Blo 1252444 1338427 := bstep (se 1 (by rfl) ⟨1003820, by rfl⟩ : syracuseStep 1338427 = 2007641) B2007641
theorem B1879175 : Blo 1252444 1879175 := bstep (se 1 (by rfl) ⟨1409381, by rfl⟩ : syracuseStep 1879175 = 2818763) B2818763
theorem B121965709 : Blo 1252444 121965709 := bstep (se 3 (by rfl) ⟨22868570, by rfl⟩ : syracuseStep 121965709 = 45737141) B45737141
theorem B1879211 : Blo 1252444 1879211 := bstep (se 1 (by rfl) ⟨1409408, by rfl⟩ : syracuseStep 1879211 = 2818817) B2818817
theorem B6024365 : Blo 1252444 6024365 := bstep (se 3 (by rfl) ⟨1129568, by rfl⟩ : syracuseStep 6024365 = 2259137) B2259137
theorem B2116793 : Blo 1252444 2116793 := bstep (se 2 (by rfl) ⟨793797, by rfl⟩ : syracuseStep 2116793 = 1587595) B1587595
theorem B1879241 : Blo 1252444 1879241 := bstep (se 2 (by rfl) ⟨704715, by rfl⟩ : syracuseStep 1879241 = 1409431) B1409431
theorem B2821391 : Blo 1252444 2821391 := bstep (se 1 (by rfl) ⟨2116043, by rfl⟩ : syracuseStep 2821391 = 4232087) B4232087
theorem B2821409 : Blo 1252444 2821409 := bstep (se 2 (by rfl) ⟨1058028, by rfl⟩ : syracuseStep 2821409 = 2116057) B2116057
theorem B1879355 : Blo 1252444 1879355 := bstep (se 1 (by rfl) ⟨1409516, by rfl⟩ : syracuseStep 1879355 = 2819033) B2819033
theorem B1879415 : Blo 1252444 1879415 := bstep (se 1 (by rfl) ⟨1409561, by rfl⟩ : syracuseStep 1879415 = 2819123) B2819123
theorem B1879439 : Blo 1252444 1879439 := bstep (se 1 (by rfl) ⟨1409579, by rfl⟩ : syracuseStep 1879439 = 2819159) B2819159
theorem B6344081 : Blo 1252444 6344081 := bstep (se 2 (by rfl) ⟨2379030, by rfl⟩ : syracuseStep 6344081 = 4758061) B4758061
theorem B1879481 : Blo 1252444 1879481 := bstep (se 2 (by rfl) ⟨704805, by rfl⟩ : syracuseStep 1879481 = 1409611) B1409611
theorem B16281091 : Blo 1252444 16281091 := bstep (se 1 (by rfl) ⟨12210818, by rfl⟩ : syracuseStep 16281091 = 24421637) B24421637
theorem B1879559 : Blo 1252444 1879559 := bstep (se 1 (by rfl) ⟨1409669, by rfl⟩ : syracuseStep 1879559 = 2819339) B2819339
theorem B1879595 : Blo 1252444 1879595 := bstep (se 1 (by rfl) ⟨1409696, by rfl⟩ : syracuseStep 1879595 = 2819393) B2819393
theorem B1879625 : Blo 1252444 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B3173975 : Blo 1252444 3173975 := bstep (se 1 (by rfl) ⟨2380481, by rfl⟩ : syracuseStep 3173975 = 4760963) B4760963
theorem B2821751 : Blo 1252444 2821751 := bstep (se 1 (by rfl) ⟨2116313, by rfl⟩ : syracuseStep 2821751 = 4232627) B4232627
theorem B2379449 : Blo 1252444 2379449 := bstep (se 2 (by rfl) ⟨892293, by rfl⟩ : syracuseStep 2379449 = 1784587) B1784587
theorem B1879739 : Blo 1252444 1879739 := bstep (se 1 (by rfl) ⟨1409804, by rfl⟩ : syracuseStep 1879739 = 2819609) B2819609
theorem B1879799 : Blo 1252444 1879799 := bstep (se 1 (by rfl) ⟨1409849, by rfl⟩ : syracuseStep 1879799 = 2819699) B2819699
theorem B5426945 : Blo 1252444 5426945 := bstep (se 2 (by rfl) ⟨2035104, by rfl⟩ : syracuseStep 5426945 = 4070209) B4070209
theorem B1879823 : Blo 1252444 1879823 := bstep (se 1 (by rfl) ⟨1409867, by rfl⟩ : syracuseStep 1879823 = 2819735) B2819735
theorem B6524705 : Blo 1252444 6524705 := bstep (se 2 (by rfl) ⟨2446764, by rfl⟩ : syracuseStep 6524705 = 4893529) B4893529
theorem B3174187 : Blo 1252444 3174187 := bstep (se 1 (by rfl) ⟨2380640, by rfl⟩ : syracuseStep 3174187 = 4761281) B4761281
theorem B2821931 : Blo 1252444 2821931 := bstep (se 1 (by rfl) ⟨2116448, by rfl⟩ : syracuseStep 2821931 = 4232897) B4232897
theorem B15257393 : Blo 1252444 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B1879865 : Blo 1252444 1879865 := bstep (se 2 (by rfl) ⟨704949, by rfl⟩ : syracuseStep 1879865 = 1409899) B1409899
theorem B1879943 : Blo 1252444 1879943 := bstep (se 1 (by rfl) ⟨1409957, by rfl⟩ : syracuseStep 1879943 = 2819915) B2819915
theorem B1879979 : Blo 1252444 1879979 := bstep (se 1 (by rfl) ⟨1409984, by rfl⟩ : syracuseStep 1879979 = 2819969) B2819969
theorem B3174329 : Blo 1252444 3174329 := bstep (se 2 (by rfl) ⟨1190373, by rfl⟩ : syracuseStep 3174329 = 2380747) B2380747
theorem B1880009 : Blo 1252444 1880009 := bstep (se 2 (by rfl) ⟨705003, by rfl⟩ : syracuseStep 1880009 = 1410007) B1410007
theorem B5361617 : Blo 1252444 5361617 := bstep (se 2 (by rfl) ⟨2010606, by rfl⟩ : syracuseStep 5361617 = 4021213) B4021213
theorem B6778903 : Blo 1252444 6778903 := bstep (se 1 (by rfl) ⟨5084177, by rfl⟩ : syracuseStep 6778903 = 10168355) B10168355
theorem B1880123 : Blo 1252444 1880123 := bstep (se 1 (by rfl) ⟨1410092, by rfl⟩ : syracuseStep 1880123 = 2820185) B2820185
theorem B1585271 : Blo 1252444 1585271 := bstep (se 1 (by rfl) ⟨1188953, by rfl⟩ : syracuseStep 1585271 = 2377907) B2377907
theorem B1880183 : Blo 1252444 1880183 := bstep (se 1 (by rfl) ⟨1410137, by rfl⟩ : syracuseStep 1880183 = 2820275) B2820275
theorem B1880207 : Blo 1252444 1880207 := bstep (se 1 (by rfl) ⟨1410155, by rfl⟩ : syracuseStep 1880207 = 2820311) B2820311
theorem B2822291 : Blo 1252444 2822291 := bstep (se 1 (by rfl) ⟨2116718, by rfl⟩ : syracuseStep 2822291 = 4233437) B4233437
theorem B1880249 : Blo 1252444 1880249 := bstep (se 2 (by rfl) ⟨705093, by rfl⟩ : syracuseStep 1880249 = 1410187) B1410187
theorem B3567817 : Blo 1252444 3567817 := bstep (se 2 (by rfl) ⟨1337931, by rfl⟩ : syracuseStep 3567817 = 2675863) B2675863
theorem B2822345 : Blo 1252444 2822345 := bstep (se 2 (by rfl) ⟨1058379, by rfl⟩ : syracuseStep 2822345 = 2116759) B2116759
theorem B8138989 : Blo 1252444 8138989 := bstep (se 3 (by rfl) ⟨1526060, by rfl⟩ : syracuseStep 8138989 = 3052121) B3052121
theorem B6770945 : Blo 1252444 6770945 := bstep (se 2 (by rfl) ⟨2539104, by rfl⟩ : syracuseStep 6770945 = 5078209) B5078209
theorem B1880327 : Blo 1252444 1880327 := bstep (se 1 (by rfl) ⟨1410245, by rfl⟩ : syracuseStep 1880327 = 2820491) B2820491
theorem B1585423 : Blo 1252444 1585423 := bstep (se 1 (by rfl) ⟨1189067, by rfl⟩ : syracuseStep 1585423 = 2378135) B2378135
theorem B4231439 : Blo 1252444 4231439 := bstep (se 1 (by rfl) ⟨3173579, by rfl⟩ : syracuseStep 4231439 = 6347159) B6347159
theorem B14479649 : Blo 1252444 14479649 := bstep (se 2 (by rfl) ⟨5429868, by rfl⟩ : syracuseStep 14479649 = 10859737) B10859737
theorem B1880363 : Blo 1252444 1880363 := bstep (se 1 (by rfl) ⟨1410272, by rfl⟩ : syracuseStep 1880363 = 2820545) B2820545
theorem B1880393 : Blo 1252444 1880393 := bstep (se 2 (by rfl) ⟨705147, by rfl⟩ : syracuseStep 1880393 = 1410295) B1410295
theorem B1716599 : Blo 1252444 1716599 := bstep (se 1 (by rfl) ⟨1287449, by rfl⟩ : syracuseStep 1716599 = 2574899) B2574899
theorem B10162579 : Blo 1252444 10162579 := bstep (se 1 (by rfl) ⟨7621934, by rfl⟩ : syracuseStep 10162579 = 15243869) B15243869
theorem B5353913 : Blo 1252444 5353913 := bstep (se 2 (by rfl) ⟨2007717, by rfl⟩ : syracuseStep 5353913 = 4015435) B4015435
theorem B1585595 : Blo 1252444 1585595 := bstep (se 1 (by rfl) ⟨1189196, by rfl⟩ : syracuseStep 1585595 = 2378393) B2378393
theorem B1880507 : Blo 1252444 1880507 := bstep (se 1 (by rfl) ⟨1410380, by rfl⟩ : syracuseStep 1880507 = 2820761) B2820761
theorem B1880567 : Blo 1252444 1880567 := bstep (se 1 (by rfl) ⟨1410425, by rfl⟩ : syracuseStep 1880567 = 2820851) B2820851
theorem B6771203 : Blo 1252444 6771203 := bstep (se 1 (by rfl) ⟨5078402, by rfl⟩ : syracuseStep 6771203 = 10156805) B10156805
theorem B10170883 : Blo 1252444 10170883 := bstep (se 1 (by rfl) ⟨7628162, by rfl⟩ : syracuseStep 10170883 = 15256325) B15256325
theorem B1880591 : Blo 1252444 1880591 := bstep (se 1 (by rfl) ⟨1410443, by rfl⟩ : syracuseStep 1880591 = 2820887) B2820887
theorem B4231709 : Blo 1252444 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B3568171 : Blo 1252444 3568171 := bstep (se 1 (by rfl) ⟨2676128, by rfl⟩ : syracuseStep 3568171 = 5352257) B5352257
theorem B81293867 : Blo 1252444 81293867 := bstep (se 1 (by rfl) ⟨60970400, by rfl⟩ : syracuseStep 81293867 = 121940801) B121940801
theorem B2036267 : Blo 1252444 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B1880633 : Blo 1252444 1880633 := bstep (se 2 (by rfl) ⟨705237, by rfl⟩ : syracuseStep 1880633 = 1410475) B1410475
theorem B1880711 : Blo 1252444 1880711 := bstep (se 1 (by rfl) ⟨1410533, by rfl⟩ : syracuseStep 1880711 = 2821067) B2821067
theorem B1880747 : Blo 1252444 1880747 := bstep (se 1 (by rfl) ⟨1410560, by rfl⟩ : syracuseStep 1880747 = 2821121) B2821121
theorem B1880777 : Blo 1252444 1880777 := bstep (se 2 (by rfl) ⟨705291, by rfl⟩ : syracuseStep 1880777 = 1410583) B1410583
theorem B5354221 : Blo 1252444 5354221 := bstep (se 3 (by rfl) ⟨1003916, by rfl⟩ : syracuseStep 5354221 = 2007833) B2007833
theorem B5354255 : Blo 1252444 5354255 := bstep (se 1 (by rfl) ⟨4015691, by rfl⟩ : syracuseStep 5354255 = 8031383) B8031383
theorem B1880891 : Blo 1252444 1880891 := bstep (se 1 (by rfl) ⟨1410668, by rfl⟩ : syracuseStep 1880891 = 2821337) B2821337
theorem B2380603 : Blo 1252444 2380603 := bstep (se 1 (by rfl) ⟨1785452, by rfl⟩ : syracuseStep 2380603 = 3570905) B3570905
theorem B3568445 : Blo 1252444 3568445 := bstep (se 3 (by rfl) ⟨669083, by rfl⟩ : syracuseStep 3568445 = 1338167) B1338167
theorem B1880951 : Blo 1252444 1880951 := bstep (se 1 (by rfl) ⟨1410713, by rfl⟩ : syracuseStep 1880951 = 2821427) B2821427
theorem B1880975 : Blo 1252444 1880975 := bstep (se 1 (by rfl) ⟨1410731, by rfl⟩ : syracuseStep 1880975 = 2821463) B2821463
theorem B1881017 : Blo 1252444 1881017 := bstep (se 2 (by rfl) ⟨705381, by rfl⟩ : syracuseStep 1881017 = 1410763) B1410763
theorem B1881095 : Blo 1252444 1881095 := bstep (se 1 (by rfl) ⟨1410821, by rfl⟩ : syracuseStep 1881095 = 2821643) B2821643
theorem B1881131 : Blo 1252444 1881131 := bstep (se 1 (by rfl) ⟨1410848, by rfl⟩ : syracuseStep 1881131 = 2821697) B2821697
theorem B7238717 : Blo 1252444 7238717 := bstep (se 3 (by rfl) ⟨1357259, by rfl⟩ : syracuseStep 7238717 = 2714519) B2714519
theorem B7140419 : Blo 1252444 7140419 := bstep (se 1 (by rfl) ⟨5355314, by rfl⟩ : syracuseStep 7140419 = 10710629) B10710629
theorem B1881161 : Blo 1252444 1881161 := bstep (se 2 (by rfl) ⟨705435, by rfl⟩ : syracuseStep 1881161 = 1410871) B1410871
theorem B1881275 : Blo 1252444 1881275 := bstep (se 1 (by rfl) ⟨1410956, by rfl⟩ : syracuseStep 1881275 = 2821913) B2821913
theorem B1881335 : Blo 1252444 1881335 := bstep (se 1 (by rfl) ⟨1411001, by rfl⟩ : syracuseStep 1881335 = 2822003) B2822003
theorem B1881359 : Blo 1252444 1881359 := bstep (se 1 (by rfl) ⟨1411019, by rfl⟩ : syracuseStep 1881359 = 2822039) B2822039
theorem B17143073 : Blo 1252444 17143073 := bstep (se 2 (by rfl) ⟨6428652, by rfl⟩ : syracuseStep 17143073 = 12857305) B12857305
theorem B2381089 : Blo 1252444 2381089 := bstep (se 2 (by rfl) ⟨892908, by rfl⟩ : syracuseStep 2381089 = 1785817) B1785817
theorem B1881401 : Blo 1252444 1881401 := bstep (se 2 (by rfl) ⟨705525, by rfl⟩ : syracuseStep 1881401 = 1411051) B1411051
theorem B1586567 : Blo 1252444 1586567 := bstep (se 1 (by rfl) ⟨1189925, by rfl⟩ : syracuseStep 1586567 = 2379851) B2379851
theorem B1881479 : Blo 1252444 1881479 := bstep (se 1 (by rfl) ⟨1411109, by rfl⟩ : syracuseStep 1881479 = 2822219) B2822219
theorem B9524627 : Blo 1252444 9524627 := bstep (se 1 (by rfl) ⟨7143470, by rfl⟩ : syracuseStep 9524627 = 14286941) B14286941
theorem B3388825 : Blo 1252444 3388825 := bstep (se 2 (by rfl) ⟨1270809, by rfl⟩ : syracuseStep 3388825 = 2541619) B2541619
theorem B1881515 : Blo 1252444 1881515 := bstep (se 1 (by rfl) ⟨1411136, by rfl⟩ : syracuseStep 1881515 = 2822273) B2822273
theorem B1881545 : Blo 1252444 1881545 := bstep (se 2 (by rfl) ⟨705579, by rfl⟩ : syracuseStep 1881545 = 1411159) B1411159
theorem B6346187 : Blo 1252444 6346187 := bstep (se 1 (by rfl) ⟨4759640, by rfl⟩ : syracuseStep 6346187 = 9519281) B9519281
theorem B6780419 : Blo 1252444 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B9655811 : Blo 1252444 9655811 := bstep (se 1 (by rfl) ⟨7241858, by rfl⟩ : syracuseStep 9655811 = 14483717) B14483717
theorem B3216955 : Blo 1252444 3216955 := bstep (se 1 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 3216955 = 4825433) B4825433
theorem B1881659 : Blo 1252444 1881659 := bstep (se 1 (by rfl) ⟨1411244, by rfl⟩ : syracuseStep 1881659 = 2822489) B2822489
theorem B6772285 : Blo 1252444 6772285 := bstep (se 3 (by rfl) ⟨1269803, by rfl⟩ : syracuseStep 6772285 = 2539607) B2539607
theorem B8582723 : Blo 1252444 8582723 := bstep (se 1 (by rfl) ⟨6437042, by rfl⟩ : syracuseStep 8582723 = 12874085) B12874085
theorem B20592305 : Blo 1252444 20592305 := bstep (se 2 (by rfl) ⟨7722114, by rfl⟩ : syracuseStep 20592305 = 15444229) B15444229
theorem B15234817 : Blo 1252444 15234817 := bstep (se 2 (by rfl) ⟨5713056, by rfl⟩ : syracuseStep 15234817 = 11426113) B11426113
theorem B1783567 : Blo 1252444 1783567 := bstep (se 1 (by rfl) ⟨1337675, by rfl⟩ : syracuseStep 1783567 = 2675351) B2675351
theorem B6346511 : Blo 1252444 6346511 := bstep (se 1 (by rfl) ⟨4759883, by rfl⟩ : syracuseStep 6346511 = 9519767) B9519767
theorem B9516851 : Blo 1252444 9516851 := bstep (se 1 (by rfl) ⟨7137638, by rfl⟩ : syracuseStep 9516851 = 14275277) B14275277
theorem B2676539 : Blo 1252444 2676539 := bstep (se 1 (by rfl) ⟨2007404, by rfl⟩ : syracuseStep 2676539 = 4014809) B4014809
theorem B4757363 : Blo 1252444 4757363 := bstep (se 1 (by rfl) ⟨3568022, by rfl⟩ : syracuseStep 4757363 = 7136045) B7136045
theorem B3012499 : Blo 1252444 3012499 := bstep (se 1 (by rfl) ⟨2259374, by rfl⟩ : syracuseStep 3012499 = 4518749) B4518749
theorem B4233113 : Blo 1252444 4233113 := bstep (se 2 (by rfl) ⟨1587417, by rfl⟩ : syracuseStep 4233113 = 3174835) B3174835
theorem B6019001 : Blo 1252444 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B1587215 : Blo 1252444 1587215 := bstep (se 1 (by rfl) ⟨1190411, by rfl⟩ : syracuseStep 1587215 = 2380823) B2380823
theorem B1505423 : Blo 1252444 1505423 := bstep (se 1 (by rfl) ⟨1129067, by rfl⟩ : syracuseStep 1505423 = 2258135) B2258135
theorem B2677025 : Blo 1252444 2677025 := bstep (se 2 (by rfl) ⟨1003884, by rfl⟩ : syracuseStep 2677025 = 2007769) B2007769
theorem B7240195 : Blo 1252444 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B2677367 : Blo 1252444 2677367 := bstep (se 1 (by rfl) ⟨2008025, by rfl⟩ : syracuseStep 2677367 = 4016051) B4016051
theorem B12049073 : Blo 1252444 12049073 := bstep (se 2 (by rfl) ⟨4518402, by rfl⟩ : syracuseStep 12049073 = 9036805) B9036805
theorem B7142195 : Blo 1252444 7142195 := bstep (se 1 (by rfl) ⟨5356646, by rfl⟩ : syracuseStep 7142195 = 10713293) B10713293
theorem B12041075 : Blo 1252444 12041075 := bstep (se 1 (by rfl) ⟨9030806, by rfl⟩ : syracuseStep 12041075 = 18061613) B18061613
theorem B34315123 : Blo 1252444 34315123 := bstep (se 1 (by rfl) ⟨25736342, by rfl⟩ : syracuseStep 34315123 = 51472685) B51472685
theorem B1784695 : Blo 1252444 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B3570551 : Blo 1252444 3570551 := bstep (se 1 (by rfl) ⟨2677913, by rfl⟩ : syracuseStep 3570551 = 5355827) B5355827
theorem B7134155 : Blo 1252444 7134155 := bstep (se 1 (by rfl) ⟨5350616, by rfl⟩ : syracuseStep 7134155 = 10701233) B10701233
theorem B14269445 : Blo 1252444 14269445 := bstep (se 4 (by rfl) ⟨1337760, by rfl⟩ : syracuseStep 14269445 = 2675521) B2675521
theorem B5356631 : Blo 1252444 5356631 := bstep (se 1 (by rfl) ⟨4017473, by rfl⟩ : syracuseStep 5356631 = 8034947) B8034947
theorem B7617655 : Blo 1252444 7617655 := bstep (se 1 (by rfl) ⟨5713241, by rfl⟩ : syracuseStep 7617655 = 11426483) B11426483
theorem B1252487 : Blo 1252444 1252487 := bstep (se 1 (by rfl) ⟨939365, by rfl⟩ : syracuseStep 1252487 = 1878731) B1878731
theorem B1252495 : Blo 1252444 1252495 := bstep (se 1 (by rfl) ⟨939371, by rfl⟩ : syracuseStep 1252495 = 1878743) B1878743
theorem B1252539 : Blo 1252444 1252539 := bstep (se 1 (by rfl) ⟨939404, by rfl⟩ : syracuseStep 1252539 = 1878809) B1878809
theorem B6347969 : Blo 1252444 6347969 := bstep (se 2 (by rfl) ⟨2380488, by rfl⟩ : syracuseStep 6347969 = 4760977) B4760977
theorem B16268525 : Blo 1252444 16268525 := bstep (se 3 (by rfl) ⟨3050348, by rfl⟩ : syracuseStep 16268525 = 6100697) B6100697
theorem B1252615 : Blo 1252444 1252615 := bstep (se 1 (by rfl) ⟨939461, by rfl⟩ : syracuseStep 1252615 = 1878923) B1878923
theorem B1252623 : Blo 1252444 1252623 := bstep (se 1 (by rfl) ⟨939467, by rfl⟩ : syracuseStep 1252623 = 1878935) B1878935
theorem B4824335 : Blo 1252444 4824335 := bstep (se 1 (by rfl) ⟨3618251, by rfl⟩ : syracuseStep 4824335 = 7236503) B7236503
theorem B1252667 : Blo 1252444 1252667 := bstep (se 1 (by rfl) ⟨939500, by rfl⟩ : syracuseStep 1252667 = 1879001) B1879001
theorem B1252743 : Blo 1252444 1252743 := bstep (se 1 (by rfl) ⟨939557, by rfl⟩ : syracuseStep 1252743 = 1879115) B1879115
theorem B1252751 : Blo 1252444 1252751 := bstep (se 1 (by rfl) ⟨939563, by rfl⟩ : syracuseStep 1252751 = 1879127) B1879127
theorem B1252795 : Blo 1252444 1252795 := bstep (se 1 (by rfl) ⟨939596, by rfl⟩ : syracuseStep 1252795 = 1879193) B1879193
theorem B11427281 : Blo 1252444 11427281 := bstep (se 2 (by rfl) ⟨4285230, by rfl⟩ : syracuseStep 11427281 = 8570461) B8570461
theorem B1252871 : Blo 1252444 1252871 := bstep (se 1 (by rfl) ⟨939653, by rfl⟩ : syracuseStep 1252871 = 1879307) B1879307
theorem B1252879 : Blo 1252444 1252879 := bstep (se 1 (by rfl) ⟨939659, by rfl⟩ : syracuseStep 1252879 = 1879319) B1879319
theorem B1252923 : Blo 1252444 1252923 := bstep (se 1 (by rfl) ⟨939692, by rfl⟩ : syracuseStep 1252923 = 1879385) B1879385
theorem B6020675 : Blo 1252444 6020675 := bstep (se 1 (by rfl) ⟨4515506, by rfl⟩ : syracuseStep 6020675 = 9031013) B9031013
theorem B1252999 : Blo 1252444 1252999 := bstep (se 1 (by rfl) ⟨939749, by rfl⟩ : syracuseStep 1252999 = 1879499) B1879499
theorem B1253007 : Blo 1252444 1253007 := bstep (se 1 (by rfl) ⟨939755, by rfl⟩ : syracuseStep 1253007 = 1879511) B1879511
theorem B19570355 : Blo 1252444 19570355 := bstep (se 1 (by rfl) ⟨14677766, by rfl⟩ : syracuseStep 19570355 = 29355533) B29355533
theorem B1253051 : Blo 1252444 1253051 := bstep (se 1 (by rfl) ⟨939788, by rfl⟩ : syracuseStep 1253051 = 1879577) B1879577
theorem B1933001 : Blo 1252444 1933001 := bstep (se 2 (by rfl) ⟨724875, by rfl⟩ : syracuseStep 1933001 = 1449751) B1449751
theorem B13549285 : Blo 1252444 13549285 := bstep (se 4 (by rfl) ⟨1270245, by rfl⟩ : syracuseStep 13549285 = 2540491) B2540491
theorem B1253127 : Blo 1252444 1253127 := bstep (se 1 (by rfl) ⟨939845, by rfl⟩ : syracuseStep 1253127 = 1879691) B1879691
theorem B1253135 : Blo 1252444 1253135 := bstep (se 1 (by rfl) ⟨939851, by rfl⟩ : syracuseStep 1253135 = 1879703) B1879703
theorem B1253179 : Blo 1252444 1253179 := bstep (se 1 (by rfl) ⟨939884, by rfl⟩ : syracuseStep 1253179 = 1879769) B1879769
theorem B1253255 : Blo 1252444 1253255 := bstep (se 1 (by rfl) ⟨939941, by rfl⟩ : syracuseStep 1253255 = 1879883) B1879883
theorem B1253263 : Blo 1252444 1253263 := bstep (se 1 (by rfl) ⟨939947, by rfl⟩ : syracuseStep 1253263 = 1879895) B1879895
theorem B1253307 : Blo 1252444 1253307 := bstep (se 1 (by rfl) ⟨939980, by rfl⟩ : syracuseStep 1253307 = 1879961) B1879961
theorem B4759505 : Blo 1252444 4759505 := bstep (se 2 (by rfl) ⟨1784814, by rfl⟩ : syracuseStep 4759505 = 3569629) B3569629
theorem B1253415 : Blo 1252444 1253415 := bstep (se 1 (by rfl) ⟨940061, by rfl⟩ : syracuseStep 1253415 = 1880123) B1880123
theorem B1253455 : Blo 1252444 1253455 := bstep (se 1 (by rfl) ⟨940091, by rfl⟩ : syracuseStep 1253455 = 1880183) B1880183
theorem B1253471 : Blo 1252444 1253471 := bstep (se 1 (by rfl) ⟨940103, by rfl⟩ : syracuseStep 1253471 = 1880207) B1880207
theorem B1253499 : Blo 1252444 1253499 := bstep (se 1 (by rfl) ⟨940124, by rfl⟩ : syracuseStep 1253499 = 1880249) B1880249
theorem B4513963 : Blo 1252444 4513963 := bstep (se 1 (by rfl) ⟨3385472, by rfl⟩ : syracuseStep 4513963 = 6770945) B6770945
theorem B1253551 : Blo 1252444 1253551 := bstep (se 1 (by rfl) ⟨940163, by rfl⟩ : syracuseStep 1253551 = 1880327) B1880327
theorem B2113735 : Blo 1252444 2113735 := bstep (se 1 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 2113735 = 3170603) B3170603
theorem B1253575 : Blo 1252444 1253575 := bstep (se 1 (by rfl) ⟨940181, by rfl⟩ : syracuseStep 1253575 = 1880363) B1880363
theorem B1253595 : Blo 1252444 1253595 := bstep (se 1 (by rfl) ⟨940196, by rfl⟩ : syracuseStep 1253595 = 1880393) B1880393
theorem B2818295 : Blo 1252444 2818295 := bstep (se 1 (by rfl) ⟨2113721, by rfl⟩ : syracuseStep 2818295 = 4227443) B4227443
theorem B1253671 : Blo 1252444 1253671 := bstep (se 1 (by rfl) ⟨940253, by rfl⟩ : syracuseStep 1253671 = 1880507) B1880507
theorem B4227389 : Blo 1252444 4227389 := bstep (se 3 (by rfl) ⟨792635, by rfl⟩ : syracuseStep 4227389 = 1585271) B1585271
theorem B1253711 : Blo 1252444 1253711 := bstep (se 1 (by rfl) ⟨940283, by rfl⟩ : syracuseStep 1253711 = 1880567) B1880567
theorem B4514135 : Blo 1252444 4514135 := bstep (se 1 (by rfl) ⟨3385601, by rfl⟩ : syracuseStep 4514135 = 6771203) B6771203
theorem B1253727 : Blo 1252444 1253727 := bstep (se 1 (by rfl) ⟨940295, by rfl⟩ : syracuseStep 1253727 = 1880591) B1880591
theorem B2113897 : Blo 1252444 2113897 := bstep (se 2 (by rfl) ⟨792711, by rfl⟩ : syracuseStep 2113897 = 1585423) B1585423
theorem B2539883 : Blo 1252444 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B1253755 : Blo 1252444 1253755 := bstep (se 1 (by rfl) ⟨940316, by rfl⟩ : syracuseStep 1253755 = 1880633) B1880633
theorem B4014461 : Blo 1252444 4014461 := bstep (se 3 (by rfl) ⟨752711, by rfl⟩ : syracuseStep 4014461 = 1505423) B1505423
theorem B1253807 : Blo 1252444 1253807 := bstep (se 1 (by rfl) ⟨940355, by rfl⟩ : syracuseStep 1253807 = 1880711) B1880711
theorem B1253831 : Blo 1252444 1253831 := bstep (se 1 (by rfl) ⟨940373, by rfl⟩ : syracuseStep 1253831 = 1880747) B1880747
theorem B1253851 : Blo 1252444 1253851 := bstep (se 1 (by rfl) ⟨940388, by rfl⟩ : syracuseStep 1253851 = 1880777) B1880777
theorem B13550105 : Blo 1252444 13550105 := bstep (se 2 (by rfl) ⟨5081289, by rfl⟩ : syracuseStep 13550105 = 10162579) B10162579
theorem B1409575 : Blo 1252444 1409575 := bstep (se 1 (by rfl) ⟨1057181, by rfl⟩ : syracuseStep 1409575 = 2114363) B2114363
theorem B1253927 : Blo 1252444 1253927 := bstep (se 1 (by rfl) ⟨940445, by rfl⟩ : syracuseStep 1253927 = 1880891) B1880891
theorem B1253967 : Blo 1252444 1253967 := bstep (se 1 (by rfl) ⟨940475, by rfl⟩ : syracuseStep 1253967 = 1880951) B1880951
theorem B1253983 : Blo 1252444 1253983 := bstep (se 1 (by rfl) ⟨940487, by rfl⟩ : syracuseStep 1253983 = 1880975) B1880975
theorem B1254011 : Blo 1252444 1254011 := bstep (se 1 (by rfl) ⟨940508, by rfl⟩ : syracuseStep 1254011 = 1881017) B1881017
theorem B1254063 : Blo 1252444 1254063 := bstep (se 1 (by rfl) ⟨940547, by rfl⟩ : syracuseStep 1254063 = 1881095) B1881095
theorem B1254087 : Blo 1252444 1254087 := bstep (se 1 (by rfl) ⟨940565, by rfl⟩ : syracuseStep 1254087 = 1881131) B1881131
theorem B4825811 : Blo 1252444 4825811 := bstep (se 1 (by rfl) ⟨3619358, by rfl⟩ : syracuseStep 4825811 = 7238717) B7238717
theorem B4760279 : Blo 1252444 4760279 := bstep (se 1 (by rfl) ⟨3570209, by rfl⟩ : syracuseStep 4760279 = 7140419) B7140419
theorem B1254107 : Blo 1252444 1254107 := bstep (se 1 (by rfl) ⟨940580, by rfl⟩ : syracuseStep 1254107 = 1881161) B1881161
theorem B1254183 : Blo 1252444 1254183 := bstep (se 1 (by rfl) ⟨940637, by rfl⟩ : syracuseStep 1254183 = 1881275) B1881275
theorem B2818889 : Blo 1252444 2818889 := bstep (se 2 (by rfl) ⟨1057083, by rfl⟩ : syracuseStep 2818889 = 2114167) B2114167
theorem B1254223 : Blo 1252444 1254223 := bstep (se 1 (by rfl) ⟨940667, by rfl⟩ : syracuseStep 1254223 = 1881335) B1881335
theorem B1254239 : Blo 1252444 1254239 := bstep (se 1 (by rfl) ⟨940679, by rfl⟩ : syracuseStep 1254239 = 1881359) B1881359
theorem B11428715 : Blo 1252444 11428715 := bstep (se 1 (by rfl) ⟨8571536, by rfl⟩ : syracuseStep 11428715 = 17143073) B17143073
theorem B1254267 : Blo 1252444 1254267 := bstep (se 1 (by rfl) ⟨940700, by rfl⟩ : syracuseStep 1254267 = 1881401) B1881401
theorem B14468015 : Blo 1252444 14468015 := bstep (se 1 (by rfl) ⟨10851011, by rfl⟩ : syracuseStep 14468015 = 21702023) B21702023
theorem B1254319 : Blo 1252444 1254319 := bstep (se 1 (by rfl) ⟨940739, by rfl⟩ : syracuseStep 1254319 = 1881479) B1881479
theorem B6349751 : Blo 1252444 6349751 := bstep (se 1 (by rfl) ⟨4762313, by rfl⟩ : syracuseStep 6349751 = 9524627) B9524627
theorem B2114491 : Blo 1252444 2114491 := bstep (se 1 (by rfl) ⟨1585868, by rfl⟩ : syracuseStep 2114491 = 3171737) B3171737
theorem B1254343 : Blo 1252444 1254343 := bstep (se 1 (by rfl) ⟨940757, by rfl⟩ : syracuseStep 1254343 = 1881515) B1881515
theorem B1254363 : Blo 1252444 1254363 := bstep (se 1 (by rfl) ⟨940772, by rfl⟩ : syracuseStep 1254363 = 1881545) B1881545
theorem B6341651 : Blo 1252444 6341651 := bstep (se 1 (by rfl) ⟨4756238, by rfl⟩ : syracuseStep 6341651 = 9512477) B9512477
theorem B2114599 : Blo 1252444 2114599 := bstep (se 1 (by rfl) ⟨1585949, by rfl⟩ : syracuseStep 2114599 = 3171899) B3171899
theorem B1254439 : Blo 1252444 1254439 := bstep (se 1 (by rfl) ⟨940829, by rfl⟩ : syracuseStep 1254439 = 1881659) B1881659
theorem B45753497 : Blo 1252444 45753497 := bstep (se 2 (by rfl) ⟨17157561, by rfl⟩ : syracuseStep 45753497 = 34315123) B34315123
theorem B4228253 : Blo 1252444 4228253 := bstep (se 3 (by rfl) ⟨792797, by rfl⟩ : syracuseStep 4228253 = 1585595) B1585595
theorem B3171575 : Blo 1252444 3171575 := bstep (se 1 (by rfl) ⟨2378681, by rfl⟩ : syracuseStep 3171575 = 4757363) B4757363
theorem B2114923 : Blo 1252444 2114923 := bstep (se 1 (by rfl) ⟨1586192, by rfl⟩ : syracuseStep 2114923 = 3172385) B3172385
theorem B162620945 : Blo 1252444 162620945 := bstep (se 2 (by rfl) ⟨60982854, by rfl⟩ : syracuseStep 162620945 = 121965709) B121965709
theorem B2819681 : Blo 1252444 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B34309777 : Blo 1252444 34309777 := bstep (se 2 (by rfl) ⟨12866166, by rfl⟩ : syracuseStep 34309777 = 25732333) B25732333
theorem B4228793 : Blo 1252444 4228793 := bstep (se 2 (by rfl) ⟨1585797, by rfl⟩ : syracuseStep 4228793 = 3171595) B3171595
theorem B4761463 : Blo 1252444 4761463 := bstep (se 1 (by rfl) ⟨3571097, by rfl⟩ : syracuseStep 4761463 = 7142195) B7142195
theorem B2820023 : Blo 1252444 2820023 := bstep (se 1 (by rfl) ⟨2115017, by rfl⟩ : syracuseStep 2820023 = 4230035) B4230035
theorem B9512963 : Blo 1252444 9512963 := bstep (se 1 (by rfl) ⟨7134722, by rfl⟩ : syracuseStep 9512963 = 14269445) B14269445
theorem B9029713 : Blo 1252444 9029713 := bstep (se 2 (by rfl) ⟨3386142, by rfl⟩ : syracuseStep 9029713 = 6772285) B6772285
theorem B4016243 : Blo 1252444 4016243 := bstep (se 1 (by rfl) ⟨3012182, by rfl⟩ : syracuseStep 4016243 = 6024365) B6024365
theorem B1411195 : Blo 1252444 1411195 := bstep (se 1 (by rfl) ⟨1058396, by rfl⟩ : syracuseStep 1411195 = 2116793) B2116793
theorem B4229387 : Blo 1252444 4229387 := bstep (se 1 (by rfl) ⟨3172040, by rfl⟩ : syracuseStep 4229387 = 6344081) B6344081
theorem B18065713 : Blo 1252444 18065713 := bstep (se 2 (by rfl) ⟨6774642, by rfl⟩ : syracuseStep 18065713 = 13549285) B13549285
theorem B2378089 : Blo 1252444 2378089 := bstep (se 2 (by rfl) ⟨891783, by rfl⟩ : syracuseStep 2378089 = 1783567) B1783567
theorem B2115983 : Blo 1252444 2115983 := bstep (se 1 (by rfl) ⟨1586987, by rfl⟩ : syracuseStep 2115983 = 3173975) B3173975
theorem B1288667 : Blo 1252444 1288667 := bstep (se 1 (by rfl) ⟨966500, by rfl⟩ : syracuseStep 1288667 = 1933001) B1933001
theorem B2820617 : Blo 1252444 2820617 := bstep (se 2 (by rfl) ⟨1057731, by rfl⟩ : syracuseStep 2820617 = 2115463) B2115463
theorem B4229657 : Blo 1252444 4229657 := bstep (se 2 (by rfl) ⟨1586121, by rfl⟩ : syracuseStep 4229657 = 3172243) B3172243
theorem B4016665 : Blo 1252444 4016665 := bstep (se 2 (by rfl) ⟨1506249, by rfl⟩ : syracuseStep 4016665 = 3012499) B3012499
theorem B2116219 : Blo 1252444 2116219 := bstep (se 1 (by rfl) ⟨1587164, by rfl⟩ : syracuseStep 2116219 = 3174329) B3174329
theorem B3574411 : Blo 1252444 3574411 := bstep (se 1 (by rfl) ⟨2680808, by rfl⟩ : syracuseStep 3574411 = 5361617) B5361617
theorem B3173003 : Blo 1252444 3173003 := bstep (se 1 (by rfl) ⟨2379752, by rfl⟩ : syracuseStep 3173003 = 4759505) B4759505
theorem B9038537 : Blo 1252444 9038537 := bstep (se 2 (by rfl) ⟨3389451, by rfl⟩ : syracuseStep 9038537 = 6778903) B6778903
theorem B7138003 : Blo 1252444 7138003 := bstep (se 1 (by rfl) ⟨5353502, by rfl⟩ : syracuseStep 7138003 = 10707005) B10707005
theorem B4762435 : Blo 1252444 4762435 := bstep (se 1 (by rfl) ⟨3571826, by rfl⟩ : syracuseStep 4762435 = 7143653) B7143653
theorem B3173215 : Blo 1252444 3173215 := bstep (se 1 (by rfl) ⟨2379911, by rfl⟩ : syracuseStep 3173215 = 4759823) B4759823
theorem B2820959 : Blo 1252444 2820959 := bstep (se 1 (by rfl) ⟨2115719, by rfl⟩ : syracuseStep 2820959 = 4231439) B4231439
theorem B9653099 : Blo 1252444 9653099 := bstep (se 1 (by rfl) ⟨7239824, by rfl⟩ : syracuseStep 9653099 = 14479649) B14479649
theorem B1878959 : Blo 1252444 1878959 := bstep (se 1 (by rfl) ⟨1409219, by rfl⟩ : syracuseStep 1878959 = 2818439) B2818439
theorem B7138277 : Blo 1252444 7138277 := bstep (se 4 (by rfl) ⟨669213, by rfl⟩ : syracuseStep 7138277 = 1338427) B1338427
theorem B1879049 : Blo 1252444 1879049 := bstep (se 2 (by rfl) ⟨704643, by rfl⟩ : syracuseStep 1879049 = 1409287) B1409287
theorem B2821139 : Blo 1252444 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B1879079 : Blo 1252444 1879079 := bstep (se 1 (by rfl) ⟨1409309, by rfl⟩ : syracuseStep 1879079 = 2818619) B2818619
theorem B4762739 : Blo 1252444 4762739 := bstep (se 1 (by rfl) ⟨3572054, by rfl⟩ : syracuseStep 4762739 = 7144109) B7144109
theorem B1879163 : Blo 1252444 1879163 := bstep (se 1 (by rfl) ⟨1409372, by rfl⟩ : syracuseStep 1879163 = 2818745) B2818745
theorem B2378963 : Blo 1252444 2378963 := bstep (se 1 (by rfl) ⟨1784222, by rfl⟩ : syracuseStep 2378963 = 3568445) B3568445
theorem B1879289 : Blo 1252444 1879289 := bstep (se 2 (by rfl) ⟨704733, by rfl⟩ : syracuseStep 1879289 = 1409467) B1409467
theorem B9653593 : Blo 1252444 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B13561177 : Blo 1252444 13561177 := bstep (se 2 (by rfl) ⟨5085441, by rfl⟩ : syracuseStep 13561177 = 10170883) B10170883
theorem B1879391 : Blo 1252444 1879391 := bstep (se 1 (by rfl) ⟨1409543, by rfl⟩ : syracuseStep 1879391 = 2819087) B2819087
theorem B2821481 : Blo 1252444 2821481 := bstep (se 2 (by rfl) ⟨1058055, by rfl⟩ : syracuseStep 2821481 = 2116111) B2116111
theorem B1879403 : Blo 1252444 1879403 := bstep (se 1 (by rfl) ⟨1409552, by rfl⟩ : syracuseStep 1879403 = 2819105) B2819105
theorem B1879631 : Blo 1252444 1879631 := bstep (se 1 (by rfl) ⟨1409723, by rfl⟩ : syracuseStep 1879631 = 2819447) B2819447
theorem B4230791 : Blo 1252444 4230791 := bstep (se 1 (by rfl) ⟨3173093, by rfl⟩ : syracuseStep 4230791 = 6346187) B6346187
theorem B7138961 : Blo 1252444 7138961 := bstep (se 2 (by rfl) ⟨2677110, by rfl⟩ : syracuseStep 7138961 = 5354221) B5354221
theorem B4230845 : Blo 1252444 4230845 := bstep (se 3 (by rfl) ⟨793283, by rfl⟩ : syracuseStep 4230845 = 1586567) B1586567
theorem B1879751 : Blo 1252444 1879751 := bstep (se 1 (by rfl) ⟨1409813, by rfl⟩ : syracuseStep 1879751 = 2819627) B2819627
theorem B5721815 : Blo 1252444 5721815 := bstep (se 1 (by rfl) ⟨4291361, by rfl⟩ : syracuseStep 5721815 = 8582723) B8582723
theorem B3174137 : Blo 1252444 3174137 := bstep (se 2 (by rfl) ⟨1190301, by rfl⟩ : syracuseStep 3174137 = 2380603) B2380603
theorem B2379593 : Blo 1252444 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B4231007 : Blo 1252444 4231007 := bstep (se 1 (by rfl) ⟨3173255, by rfl⟩ : syracuseStep 4231007 = 6346511) B6346511
theorem B1879913 : Blo 1252444 1879913 := bstep (se 2 (by rfl) ⟨704967, by rfl⟩ : syracuseStep 1879913 = 1409935) B1409935
theorem B6344567 : Blo 1252444 6344567 := bstep (se 1 (by rfl) ⟨4758425, by rfl⟩ : syracuseStep 6344567 = 9516851) B9516851
theorem B1879991 : Blo 1252444 1879991 := bstep (se 1 (by rfl) ⟨1409993, by rfl⟩ : syracuseStep 1879991 = 2819987) B2819987
theorem B2822075 : Blo 1252444 2822075 := bstep (se 1 (by rfl) ⟨2116556, by rfl⟩ : syracuseStep 2822075 = 4233113) B4233113
theorem B1880027 : Blo 1252444 1880027 := bstep (se 1 (by rfl) ⟨1410020, by rfl⟩ : syracuseStep 1880027 = 2820041) B2820041
theorem B4231169 : Blo 1252444 4231169 := bstep (se 2 (by rfl) ⟨1586688, by rfl⟩ : syracuseStep 4231169 = 3173377) B3173377
theorem B3616775 : Blo 1252444 3616775 := bstep (se 1 (by rfl) ⟨2712581, by rfl⟩ : syracuseStep 3616775 = 5425163) B5425163
theorem B3567635 : Blo 1252444 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B2822201 : Blo 1252444 2822201 := bstep (se 2 (by rfl) ⟨1058325, by rfl⟩ : syracuseStep 2822201 = 2116651) B2116651
theorem B3567863 : Blo 1252444 3567863 := bstep (se 1 (by rfl) ⟨2675897, by rfl⟩ : syracuseStep 3567863 = 5351795) B5351795
theorem B9515393 : Blo 1252444 9515393 := bstep (se 2 (by rfl) ⟨3568272, by rfl⟩ : syracuseStep 9515393 = 7136545) B7136545
theorem B3174785 : Blo 1252444 3174785 := bstep (se 2 (by rfl) ⟨1190544, by rfl⟩ : syracuseStep 3174785 = 2381089) B2381089
theorem B1880495 : Blo 1252444 1880495 := bstep (se 1 (by rfl) ⟨1410371, by rfl⟩ : syracuseStep 1880495 = 2820743) B2820743
theorem B8032715 : Blo 1252444 8032715 := bstep (se 1 (by rfl) ⟨6024536, by rfl⟩ : syracuseStep 8032715 = 12049073) B12049073
theorem B3813851 : Blo 1252444 3813851 := bstep (se 1 (by rfl) ⟨2860388, by rfl⟩ : syracuseStep 3813851 = 5720777) B5720777
theorem B1880585 : Blo 1252444 1880585 := bstep (se 2 (by rfl) ⟨705219, by rfl⟩ : syracuseStep 1880585 = 1410439) B1410439
theorem B19296791 : Blo 1252444 19296791 := bstep (se 1 (by rfl) ⟨14472593, by rfl⟩ : syracuseStep 19296791 = 28945187) B28945187
theorem B4518433 : Blo 1252444 4518433 := bstep (se 2 (by rfl) ⟨1694412, by rfl⟩ : syracuseStep 4518433 = 3388825) B3388825
theorem B1880615 : Blo 1252444 1880615 := bstep (se 1 (by rfl) ⟨1410461, by rfl⟩ : syracuseStep 1880615 = 2820923) B2820923
theorem B2380367 : Blo 1252444 2380367 := bstep (se 1 (by rfl) ⟨1785275, by rfl⟩ : syracuseStep 2380367 = 3570551) B3570551
theorem B1880699 : Blo 1252444 1880699 := bstep (se 1 (by rfl) ⟨1410524, by rfl⟩ : syracuseStep 1880699 = 2821049) B2821049
theorem B4756103 : Blo 1252444 4756103 := bstep (se 1 (by rfl) ⟨3567077, by rfl⟩ : syracuseStep 4756103 = 7134155) B7134155
theorem B4289273 : Blo 1252444 4289273 := bstep (se 2 (by rfl) ⟨1608477, by rfl⟩ : syracuseStep 4289273 = 3216955) B3216955
theorem B1880825 : Blo 1252444 1880825 := bstep (se 2 (by rfl) ⟨705309, by rfl⟩ : syracuseStep 1880825 = 1410619) B1410619
theorem B4231979 : Blo 1252444 4231979 := bstep (se 1 (by rfl) ⟨3173984, by rfl⟩ : syracuseStep 4231979 = 6347969) B6347969
theorem B3216223 : Blo 1252444 3216223 := bstep (se 1 (by rfl) ⟨2412167, by rfl⟩ : syracuseStep 3216223 = 4824335) B4824335
theorem B1880927 : Blo 1252444 1880927 := bstep (se 1 (by rfl) ⟨1410695, by rfl⟩ : syracuseStep 1880927 = 2821391) B2821391
theorem B1880939 : Blo 1252444 1880939 := bstep (se 1 (by rfl) ⟨1410704, by rfl⟩ : syracuseStep 1880939 = 2821409) B2821409
theorem B16069529 : Blo 1252444 16069529 := bstep (se 2 (by rfl) ⟨6026073, by rfl⟩ : syracuseStep 16069529 = 12052147) B12052147
theorem B32109533 : Blo 1252444 32109533 := bstep (se 3 (by rfl) ⟨6020537, by rfl⟩ : syracuseStep 32109533 = 12041075) B12041075
theorem B20313089 : Blo 1252444 20313089 := bstep (se 2 (by rfl) ⟨7617408, by rfl⟩ : syracuseStep 20313089 = 15234817) B15234817
theorem B4232249 : Blo 1252444 4232249 := bstep (se 2 (by rfl) ⟨1587093, by rfl⟩ : syracuseStep 4232249 = 3174187) B3174187
theorem B1881167 : Blo 1252444 1881167 := bstep (se 1 (by rfl) ⟨1410875, by rfl⟩ : syracuseStep 1881167 = 2821751) B2821751
theorem B13046903 : Blo 1252444 13046903 := bstep (se 1 (by rfl) ⟨9785177, by rfl⟩ : syracuseStep 13046903 = 19570355) B19570355
theorem B1586299 : Blo 1252444 1586299 := bstep (se 1 (by rfl) ⟨1189724, by rfl⟩ : syracuseStep 1586299 = 2379449) B2379449
theorem B3617963 : Blo 1252444 3617963 := bstep (se 1 (by rfl) ⟨2713472, by rfl⟩ : syracuseStep 3617963 = 5426945) B5426945
theorem B1881287 : Blo 1252444 1881287 := bstep (se 1 (by rfl) ⟨1410965, by rfl⟩ : syracuseStep 1881287 = 2821931) B2821931
theorem B10171595 : Blo 1252444 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B1881449 : Blo 1252444 1881449 := bstep (se 2 (by rfl) ⟨705543, by rfl⟩ : syracuseStep 1881449 = 1411087) B1411087
theorem B4232573 : Blo 1252444 4232573 := bstep (se 3 (by rfl) ⟨793607, by rfl⟩ : syracuseStep 4232573 = 1587215) B1587215
theorem B18060691 : Blo 1252444 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B12547493 : Blo 1252444 12547493 := bstep (se 4 (by rfl) ⟨1176327, by rfl⟩ : syracuseStep 12547493 = 2352655) B2352655
theorem B1881527 : Blo 1252444 1881527 := bstep (se 1 (by rfl) ⟨1411145, by rfl⟩ : syracuseStep 1881527 = 2822291) B2822291
theorem B1693147 : Blo 1252444 1693147 := bstep (se 1 (by rfl) ⟨1269860, by rfl⟩ : syracuseStep 1693147 = 2539721) B2539721
theorem B1881563 : Blo 1252444 1881563 := bstep (se 1 (by rfl) ⟨1411172, by rfl⟩ : syracuseStep 1881563 = 2822345) B2822345
theorem B10311131 : Blo 1252444 10311131 := bstep (se 1 (by rfl) ⟨7733348, by rfl⟩ : syracuseStep 10311131 = 15466697) B15466697
theorem B4757089 : Blo 1252444 4757089 := bstep (se 2 (by rfl) ⟨1783908, by rfl⟩ : syracuseStep 4757089 = 3567817) B3567817
theorem B3569275 : Blo 1252444 3569275 := bstep (se 1 (by rfl) ⟨2676956, by rfl⟩ : syracuseStep 3569275 = 5353913) B5353913
theorem B4232843 : Blo 1252444 4232843 := bstep (se 1 (by rfl) ⟨3174632, by rfl⟩ : syracuseStep 4232843 = 6349265) B6349265
theorem B10851985 : Blo 1252444 10851985 := bstep (se 2 (by rfl) ⟨4069494, by rfl⟩ : syracuseStep 10851985 = 8138989) B8138989
theorem B54195911 : Blo 1252444 54195911 := bstep (se 1 (by rfl) ⟨40646933, by rfl⟩ : syracuseStep 54195911 = 81293867) B81293867
theorem B1357511 : Blo 1252444 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B3569503 : Blo 1252444 3569503 := bstep (se 1 (by rfl) ⟨2677127, by rfl⟩ : syracuseStep 3569503 = 5354255) B5354255
theorem B4757561 : Blo 1252444 4757561 := bstep (se 2 (by rfl) ⟨1784085, by rfl⟩ : syracuseStep 4757561 = 3568171) B3568171
theorem B4577597 : Blo 1252444 4577597 := bstep (se 3 (by rfl) ⟨858299, by rfl⟩ : syracuseStep 4577597 = 1716599) B1716599
theorem B4520279 : Blo 1252444 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B6437207 : Blo 1252444 6437207 := bstep (se 1 (by rfl) ⟨4827905, by rfl⟩ : syracuseStep 6437207 = 9655811) B9655811
theorem B13728203 : Blo 1252444 13728203 := bstep (se 1 (by rfl) ⟨10296152, by rfl⟩ : syracuseStep 13728203 = 20592305) B20592305
theorem B4012553 : Blo 1252444 4012553 := bstep (se 2 (by rfl) ⟨1504707, by rfl⟩ : syracuseStep 4012553 = 3009415) B3009415
theorem B1784359 : Blo 1252444 1784359 := bstep (se 1 (by rfl) ⟨1338269, by rfl⟩ : syracuseStep 1784359 = 2676539) B2676539
theorem B4012667 : Blo 1252444 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B10156873 : Blo 1252444 10156873 := bstep (se 2 (by rfl) ⟨3808827, by rfl⟩ : syracuseStep 10156873 = 7617655) B7617655
theorem B1784683 : Blo 1252444 1784683 := bstep (se 1 (by rfl) ⟨1338512, by rfl⟩ : syracuseStep 1784683 = 2677025) B2677025
theorem B16063379 : Blo 1252444 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B1694639 : Blo 1252444 1694639 := bstep (se 1 (by rfl) ⟨1270979, by rfl⟩ : syracuseStep 1694639 = 2541959) B2541959
theorem B4758547 : Blo 1252444 4758547 := bstep (se 1 (by rfl) ⟨3568910, by rfl⟩ : syracuseStep 4758547 = 7137821) B7137821
theorem B1784911 : Blo 1252444 1784911 := bstep (se 1 (by rfl) ⟨1338683, by rfl⟩ : syracuseStep 1784911 = 2677367) B2677367
theorem B1252447 : Blo 1252444 1252447 := bstep (se 1 (by rfl) ⟨939335, by rfl⟩ : syracuseStep 1252447 = 1878671) B1878671
theorem B1252475 : Blo 1252444 1252475 := bstep (se 1 (by rfl) ⟨939356, by rfl⟩ : syracuseStep 1252475 = 1878713) B1878713
theorem B2677931 : Blo 1252444 2677931 := bstep (se 1 (by rfl) ⟨2008448, by rfl⟩ : syracuseStep 2677931 = 4016897) B4016897
theorem B1252527 : Blo 1252444 1252527 := bstep (se 1 (by rfl) ⟨939395, by rfl⟩ : syracuseStep 1252527 = 1878791) B1878791
theorem B1252551 : Blo 1252444 1252551 := bstep (se 1 (by rfl) ⟨939413, by rfl⟩ : syracuseStep 1252551 = 1878827) B1878827
theorem B1252571 : Blo 1252444 1252571 := bstep (se 1 (by rfl) ⟨939428, by rfl⟩ : syracuseStep 1252571 = 1878857) B1878857
theorem B1252647 : Blo 1252444 1252647 := bstep (se 1 (by rfl) ⟨939485, by rfl⟩ : syracuseStep 1252647 = 1878971) B1878971
theorem B1252687 : Blo 1252444 1252687 := bstep (se 1 (by rfl) ⟨939515, by rfl⟩ : syracuseStep 1252687 = 1879031) B1879031
theorem B21708121 : Blo 1252444 21708121 := bstep (se 2 (by rfl) ⟨8140545, by rfl⟩ : syracuseStep 21708121 = 16281091) B16281091
theorem B1252703 : Blo 1252444 1252703 := bstep (se 1 (by rfl) ⟨939527, by rfl⟩ : syracuseStep 1252703 = 1879055) B1879055
theorem B1252731 : Blo 1252444 1252731 := bstep (se 1 (by rfl) ⟨939548, by rfl⟩ : syracuseStep 1252731 = 1879097) B1879097
theorem B3571087 : Blo 1252444 3571087 := bstep (se 1 (by rfl) ⟨2678315, by rfl⟩ : syracuseStep 3571087 = 5356631) B5356631
theorem B1252783 : Blo 1252444 1252783 := bstep (se 1 (by rfl) ⟨939587, by rfl⟩ : syracuseStep 1252783 = 1879175) B1879175
theorem B1252807 : Blo 1252444 1252807 := bstep (se 1 (by rfl) ⟨939605, by rfl⟩ : syracuseStep 1252807 = 1879211) B1879211
theorem B1252827 : Blo 1252444 1252827 := bstep (se 1 (by rfl) ⟨939620, by rfl⟩ : syracuseStep 1252827 = 1879241) B1879241
theorem B10845683 : Blo 1252444 10845683 := bstep (se 1 (by rfl) ⟨8134262, by rfl⟩ : syracuseStep 10845683 = 16268525) B16268525
theorem B1252903 : Blo 1252444 1252903 := bstep (se 1 (by rfl) ⟨939677, by rfl⟩ : syracuseStep 1252903 = 1879355) B1879355
theorem B1252943 : Blo 1252444 1252943 := bstep (se 1 (by rfl) ⟨939707, by rfl⟩ : syracuseStep 1252943 = 1879415) B1879415
theorem B1252959 : Blo 1252444 1252959 := bstep (se 1 (by rfl) ⟨939719, by rfl⟩ : syracuseStep 1252959 = 1879439) B1879439
theorem B1252987 : Blo 1252444 1252987 := bstep (se 1 (by rfl) ⟨939740, by rfl⟩ : syracuseStep 1252987 = 1879481) B1879481
theorem B7618187 : Blo 1252444 7618187 := bstep (se 1 (by rfl) ⟨5713640, by rfl⟩ : syracuseStep 7618187 = 11427281) B11427281
theorem B1253039 : Blo 1252444 1253039 := bstep (se 1 (by rfl) ⟨939779, by rfl⟩ : syracuseStep 1253039 = 1879559) B1879559
theorem B1253063 : Blo 1252444 1253063 := bstep (se 1 (by rfl) ⟨939797, by rfl⟩ : syracuseStep 1253063 = 1879595) B1879595
theorem B4013783 : Blo 1252444 4013783 := bstep (se 1 (by rfl) ⟨3010337, by rfl⟩ : syracuseStep 4013783 = 6020675) B6020675
theorem B1253083 : Blo 1252444 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B2678521 : Blo 1252444 2678521 := bstep (se 2 (by rfl) ⟨1004445, by rfl⟩ : syracuseStep 2678521 = 2008891) B2008891
theorem B1253159 : Blo 1252444 1253159 := bstep (se 1 (by rfl) ⟨939869, by rfl⟩ : syracuseStep 1253159 = 1879739) B1879739
theorem B1253199 : Blo 1252444 1253199 := bstep (se 1 (by rfl) ⟨939899, by rfl⟩ : syracuseStep 1253199 = 1879799) B1879799
theorem B1253215 : Blo 1252444 1253215 := bstep (se 1 (by rfl) ⟨939911, by rfl⟩ : syracuseStep 1253215 = 1879823) B1879823
theorem B4349803 : Blo 1252444 4349803 := bstep (se 1 (by rfl) ⟨3262352, by rfl⟩ : syracuseStep 4349803 = 6524705) B6524705
theorem B1253243 : Blo 1252444 1253243 := bstep (se 1 (by rfl) ⟨939932, by rfl⟩ : syracuseStep 1253243 = 1879865) B1879865
theorem B1253295 : Blo 1252444 1253295 := bstep (se 1 (by rfl) ⟨939971, by rfl⟩ : syracuseStep 1253295 = 1879943) B1879943
theorem B1253319 : Blo 1252444 1253319 := bstep (se 1 (by rfl) ⟨939989, by rfl⟩ : syracuseStep 1253319 = 1879979) B1879979
theorem B1253339 : Blo 1252444 1253339 := bstep (se 1 (by rfl) ⟨940004, by rfl⟩ : syracuseStep 1253339 = 1880009) B1880009
theorem B2818259 : Blo 1252444 2818259 := bstep (se 1 (by rfl) ⟨2113694, by rfl⟩ : syracuseStep 2818259 = 4227389) B4227389
theorem B2818313 : Blo 1252444 2818313 := bstep (se 2 (by rfl) ⟨1056867, by rfl⟩ : syracuseStep 2818313 = 2113735) B2113735
theorem B1253663 : Blo 1252444 1253663 := bstep (se 1 (by rfl) ⟨940247, by rfl⟩ : syracuseStep 1253663 = 1880495) B1880495
theorem B1253723 : Blo 1252444 1253723 := bstep (se 1 (by rfl) ⟨940292, by rfl⟩ : syracuseStep 1253723 = 1880585) B1880585
theorem B1253743 : Blo 1252444 1253743 := bstep (se 1 (by rfl) ⟨940307, by rfl⟩ : syracuseStep 1253743 = 1880615) B1880615
theorem B1253799 : Blo 1252444 1253799 := bstep (se 1 (by rfl) ⟨940349, by rfl⟩ : syracuseStep 1253799 = 1880699) B1880699
theorem B3170735 : Blo 1252444 3170735 := bstep (se 1 (by rfl) ⟨2378051, by rfl⟩ : syracuseStep 3170735 = 4756103) B4756103
theorem B3170785 : Blo 1252444 3170785 := bstep (se 2 (by rfl) ⟨1189044, by rfl⟩ : syracuseStep 3170785 = 2378089) B2378089
theorem B2818529 : Blo 1252444 2818529 := bstep (se 2 (by rfl) ⟨1056948, by rfl⟩ : syracuseStep 2818529 = 2113897) B2113897
theorem B2859515 : Blo 1252444 2859515 := bstep (se 1 (by rfl) ⟨2144636, by rfl⟩ : syracuseStep 2859515 = 4289273) B4289273
theorem B1253883 : Blo 1252444 1253883 := bstep (se 1 (by rfl) ⟨940412, by rfl⟩ : syracuseStep 1253883 = 1880825) B1880825
theorem B27124253 : Blo 1252444 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B1253951 : Blo 1252444 1253951 := bstep (se 1 (by rfl) ⟨940463, by rfl⟩ : syracuseStep 1253951 = 1880927) B1880927
theorem B7619143 : Blo 1252444 7619143 := bstep (se 1 (by rfl) ⟨5714357, by rfl⟩ : syracuseStep 7619143 = 11428715) B11428715
theorem B1253959 : Blo 1252444 1253959 := bstep (se 1 (by rfl) ⟨940469, by rfl⟩ : syracuseStep 1253959 = 1880939) B1880939
theorem B21406355 : Blo 1252444 21406355 := bstep (se 1 (by rfl) ⟨16054766, by rfl⟩ : syracuseStep 21406355 = 32109533) B32109533
theorem B13542059 : Blo 1252444 13542059 := bstep (se 1 (by rfl) ⟨10156544, by rfl⟩ : syracuseStep 13542059 = 20313089) B20313089
theorem B4227767 : Blo 1252444 4227767 := bstep (se 1 (by rfl) ⟨3170825, by rfl⟩ : syracuseStep 4227767 = 6341651) B6341651
theorem B1254111 : Blo 1252444 1254111 := bstep (se 1 (by rfl) ⟨940583, by rfl⟩ : syracuseStep 1254111 = 1881167) B1881167
theorem B19063525 : Blo 1252444 19063525 := bstep (se 4 (by rfl) ⟨1787205, by rfl⟩ : syracuseStep 19063525 = 3574411) B3574411
theorem B2818835 : Blo 1252444 2818835 := bstep (se 1 (by rfl) ⟨2114126, by rfl⟩ : syracuseStep 2818835 = 4228253) B4228253
theorem B1254191 : Blo 1252444 1254191 := bstep (se 1 (by rfl) ⟨940643, by rfl⟩ : syracuseStep 1254191 = 1881287) B1881287
theorem B2114383 : Blo 1252444 2114383 := bstep (se 1 (by rfl) ⟨1585787, by rfl⟩ : syracuseStep 2114383 = 3171575) B3171575
theorem B1254299 : Blo 1252444 1254299 := bstep (se 1 (by rfl) ⟨940724, by rfl⟩ : syracuseStep 1254299 = 1881449) B1881449
theorem B8364995 : Blo 1252444 8364995 := bstep (se 1 (by rfl) ⟨6273746, by rfl⟩ : syracuseStep 8364995 = 12547493) B12547493
theorem B1254351 : Blo 1252444 1254351 := bstep (se 1 (by rfl) ⟨940763, by rfl⟩ : syracuseStep 1254351 = 1881527) B1881527
theorem B1254375 : Blo 1252444 1254375 := bstep (se 1 (by rfl) ⟨940781, by rfl⟩ : syracuseStep 1254375 = 1881563) B1881563
theorem B6874087 : Blo 1252444 6874087 := bstep (se 1 (by rfl) ⟨5155565, by rfl⟩ : syracuseStep 6874087 = 10311131) B10311131
theorem B108413963 : Blo 1252444 108413963 := bstep (se 1 (by rfl) ⟨81310472, by rfl⟩ : syracuseStep 108413963 = 162620945) B162620945
theorem B6349913 : Blo 1252444 6349913 := bstep (se 2 (by rfl) ⟨2381217, by rfl⟩ : syracuseStep 6349913 = 4762435) B4762435
theorem B13542497 : Blo 1252444 13542497 := bstep (se 2 (by rfl) ⟨5078436, by rfl⟩ : syracuseStep 13542497 = 10156873) B10156873
theorem B102966389 : Blo 1252444 102966389 := bstep (se 5 (by rfl) ⟨4826549, by rfl⟩ : syracuseStep 102966389 = 9653099) B9653099
theorem B2819195 : Blo 1252444 2819195 := bstep (se 1 (by rfl) ⟨2114396, by rfl⟩ : syracuseStep 2819195 = 4228793) B4228793
theorem B2819321 : Blo 1252444 2819321 := bstep (se 2 (by rfl) ⟨1057245, by rfl⟩ : syracuseStep 2819321 = 2114491) B2114491
theorem B6341975 : Blo 1252444 6341975 := bstep (se 1 (by rfl) ⟨4756481, by rfl⟩ : syracuseStep 6341975 = 9512963) B9512963
theorem B3171707 : Blo 1252444 3171707 := bstep (se 1 (by rfl) ⟨2378780, by rfl⟩ : syracuseStep 3171707 = 4757561) B4757561
theorem B2819465 : Blo 1252444 2819465 := bstep (se 2 (by rfl) ⟨1057299, by rfl⟩ : syracuseStep 2819465 = 2114599) B2114599
theorem B2115065 : Blo 1252444 2115065 := bstep (se 2 (by rfl) ⟨793149, by rfl⟩ : syracuseStep 2115065 = 1586299) B1586299
theorem B2819591 : Blo 1252444 2819591 := bstep (se 1 (by rfl) ⟨2114693, by rfl⟩ : syracuseStep 2819591 = 4229387) B4229387
theorem B1410655 : Blo 1252444 1410655 := bstep (se 1 (by rfl) ⟨1057991, by rfl⟩ : syracuseStep 1410655 = 2115983) B2115983
theorem B9152135 : Blo 1252444 9152135 := bstep (se 1 (by rfl) ⟨6864101, by rfl⟩ : syracuseStep 9152135 = 13728203) B13728203
theorem B2819771 : Blo 1252444 2819771 := bstep (se 1 (by rfl) ⟨2114828, by rfl⟩ : syracuseStep 2819771 = 4229657) B4229657
theorem B2115335 : Blo 1252444 2115335 := bstep (se 1 (by rfl) ⟨1586501, by rfl⟩ : syracuseStep 2115335 = 3173003) B3173003
theorem B28944161 : Blo 1252444 28944161 := bstep (se 2 (by rfl) ⟨10854060, by rfl⟩ : syracuseStep 28944161 = 21708121) B21708121
theorem B12871457 : Blo 1252444 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B18081569 : Blo 1252444 18081569 := bstep (se 2 (by rfl) ⟨6780588, by rfl⟩ : syracuseStep 18081569 = 13561177) B13561177
theorem B2819897 : Blo 1252444 2819897 := bstep (se 2 (by rfl) ⟨1057461, by rfl⟩ : syracuseStep 2819897 = 2114923) B2114923
theorem B4761449 : Blo 1252444 4761449 := bstep (se 2 (by rfl) ⟨1785543, by rfl⟩ : syracuseStep 4761449 = 3571087) B3571087
theorem B10708919 : Blo 1252444 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B6342785 : Blo 1252444 6342785 := bstep (se 2 (by rfl) ⟨2378544, by rfl⟩ : syracuseStep 6342785 = 4757089) B4757089
theorem B14469313 : Blo 1252444 14469313 := bstep (se 2 (by rfl) ⟨5425992, by rfl⟩ : syracuseStep 14469313 = 10851985) B10851985
theorem B45746369 : Blo 1252444 45746369 := bstep (se 2 (by rfl) ⟨17154888, by rfl⟩ : syracuseStep 45746369 = 34309777) B34309777
theorem B2820527 : Blo 1252444 2820527 := bstep (se 1 (by rfl) ⟨2115395, by rfl⟩ : syracuseStep 2820527 = 4230791) B4230791
theorem B2820563 : Blo 1252444 2820563 := bstep (se 1 (by rfl) ⟨2115422, by rfl⟩ : syracuseStep 2820563 = 4230845) B4230845
theorem B2116091 : Blo 1252444 2116091 := bstep (se 1 (by rfl) ⟨1587068, by rfl⟩ : syracuseStep 2116091 = 3174137) B3174137
theorem B2820671 : Blo 1252444 2820671 := bstep (se 1 (by rfl) ⟨2115503, by rfl⟩ : syracuseStep 2820671 = 4231007) B4231007
theorem B4229711 : Blo 1252444 4229711 := bstep (se 1 (by rfl) ⟨3172283, by rfl⟩ : syracuseStep 4229711 = 6344567) B6344567
theorem B2820779 : Blo 1252444 2820779 := bstep (se 1 (by rfl) ⟨2115584, by rfl⟩ : syracuseStep 2820779 = 4231169) B4231169
theorem B2411183 : Blo 1252444 2411183 := bstep (se 1 (by rfl) ⟨1808387, by rfl⟩ : syracuseStep 2411183 = 3616775) B3616775
theorem B2378423 : Blo 1252444 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B1878863 : Blo 1252444 1878863 := bstep (se 1 (by rfl) ⟨1409147, by rfl⟩ : syracuseStep 1878863 = 2818295) B2818295
theorem B2378575 : Blo 1252444 2378575 := bstep (se 1 (by rfl) ⟨1783931, by rfl⟩ : syracuseStep 2378575 = 3567863) B3567863
theorem B6343595 : Blo 1252444 6343595 := bstep (se 1 (by rfl) ⟨4757696, by rfl⟩ : syracuseStep 6343595 = 9515393) B9515393
theorem B2116523 : Blo 1252444 2116523 := bstep (se 1 (by rfl) ⟨1587392, by rfl⟩ : syracuseStep 2116523 = 3174785) B3174785
theorem B10709981 : Blo 1252444 10709981 := bstep (se 3 (by rfl) ⟨2008121, by rfl⟩ : syracuseStep 10709981 = 4016243) B4016243
theorem B12864527 : Blo 1252444 12864527 := bstep (se 1 (by rfl) ⟨9648395, by rfl⟩ : syracuseStep 12864527 = 19296791) B19296791
theorem B24087617 : Blo 1252444 24087617 := bstep (se 2 (by rfl) ⟨9032856, by rfl⟩ : syracuseStep 24087617 = 18065713) B18065713
theorem B3173519 : Blo 1252444 3173519 := bstep (se 1 (by rfl) ⟨2380139, by rfl⟩ : syracuseStep 3173519 = 4760279) B4760279
theorem B2821319 : Blo 1252444 2821319 := bstep (se 1 (by rfl) ⟨2115989, by rfl⟩ : syracuseStep 2821319 = 4231979) B4231979
theorem B1879259 : Blo 1252444 1879259 := bstep (se 1 (by rfl) ⟨1409444, by rfl⟩ : syracuseStep 1879259 = 2818889) B2818889
theorem B2821499 : Blo 1252444 2821499 := bstep (se 1 (by rfl) ⟨2116124, by rfl⟩ : syracuseStep 2821499 = 4232249) B4232249
theorem B6024577 : Blo 1252444 6024577 := bstep (se 2 (by rfl) ⟨2259216, by rfl⟩ : syracuseStep 6024577 = 4518433) B4518433
theorem B1879433 : Blo 1252444 1879433 := bstep (se 2 (by rfl) ⟨704787, by rfl⟩ : syracuseStep 1879433 = 1409575) B1409575
theorem B2379145 : Blo 1252444 2379145 := bstep (se 2 (by rfl) ⟨892179, by rfl⟩ : syracuseStep 2379145 = 1784359) B1784359
theorem B30502331 : Blo 1252444 30502331 := bstep (se 1 (by rfl) ⟨22876748, by rfl⟩ : syracuseStep 30502331 = 45753497) B45753497
theorem B2411975 : Blo 1252444 2411975 := bstep (se 1 (by rfl) ⟨1808981, by rfl⟩ : syracuseStep 2411975 = 3617963) B3617963
theorem B2821625 : Blo 1252444 2821625 := bstep (se 2 (by rfl) ⟨1058109, by rfl⟩ : syracuseStep 2821625 = 2116219) B2116219
theorem B12037693 : Blo 1252444 12037693 := bstep (se 3 (by rfl) ⟨2257067, by rfl⟩ : syracuseStep 12037693 = 4514135) B4514135
theorem B2821715 : Blo 1252444 2821715 := bstep (se 1 (by rfl) ⟨2116286, by rfl⟩ : syracuseStep 2821715 = 4232573) B4232573
theorem B1879787 : Blo 1252444 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B2821895 : Blo 1252444 2821895 := bstep (se 1 (by rfl) ⟨2116421, by rfl⟩ : syracuseStep 2821895 = 4232843) B4232843
theorem B4288297 : Blo 1252444 4288297 := bstep (se 2 (by rfl) ⟨1608111, by rfl⟩ : syracuseStep 4288297 = 3216223) B3216223
theorem B4230953 : Blo 1252444 4230953 := bstep (se 2 (by rfl) ⟨1586607, by rfl⟩ : syracuseStep 4230953 = 3173215) B3173215
theorem B36130607 : Blo 1252444 36130607 := bstep (se 1 (by rfl) ⟨27097955, by rfl⟩ : syracuseStep 36130607 = 54195911) B54195911
theorem B10170269 : Blo 1252444 10170269 := bstep (se 3 (by rfl) ⟨1906925, by rfl⟩ : syracuseStep 10170269 = 3813851) B3813851
theorem B3436445 : Blo 1252444 3436445 := bstep (se 3 (by rfl) ⟨644333, by rfl⟩ : syracuseStep 3436445 = 1288667) B1288667
theorem B1880015 : Blo 1252444 1880015 := bstep (se 1 (by rfl) ⟨1410011, by rfl⟩ : syracuseStep 1880015 = 2820023) B2820023
theorem B6344729 : Blo 1252444 6344729 := bstep (se 2 (by rfl) ⟨2379273, by rfl⟩ : syracuseStep 6344729 = 4758547) B4758547
theorem B2379881 : Blo 1252444 2379881 := bstep (se 2 (by rfl) ⟨892455, by rfl⟩ : syracuseStep 2379881 = 1784911) B1784911
theorem B3051731 : Blo 1252444 3051731 := bstep (se 1 (by rfl) ⟨2288798, by rfl⟩ : syracuseStep 3051731 = 4577597) B4577597
theorem B2675035 : Blo 1252444 2675035 := bstep (se 1 (by rfl) ⟨2006276, by rfl⟩ : syracuseStep 2675035 = 4012553) B4012553
theorem B1880411 : Blo 1252444 1880411 := bstep (se 1 (by rfl) ⟨1410308, by rfl⟩ : syracuseStep 1880411 = 2820617) B2820617
theorem B2675111 : Blo 1252444 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B6025691 : Blo 1252444 6025691 := bstep (se 1 (by rfl) ⟨4519268, by rfl⟩ : syracuseStep 6025691 = 9038537) B9038537
theorem B24080921 : Blo 1252444 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B1880639 : Blo 1252444 1880639 := bstep (se 1 (by rfl) ⟨1410479, by rfl⟩ : syracuseStep 1880639 = 2820959) B2820959
theorem B2257529 : Blo 1252444 2257529 := bstep (se 2 (by rfl) ⟨846573, by rfl⟩ : syracuseStep 2257529 = 1693147) B1693147
theorem B1880759 : Blo 1252444 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B14480117 : Blo 1252444 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B3175159 : Blo 1252444 3175159 := bstep (se 1 (by rfl) ⟨2381369, by rfl⟩ : syracuseStep 3175159 = 4762739) B4762739
theorem B1585975 : Blo 1252444 1585975 := bstep (se 1 (by rfl) ⟨1189481, by rfl⟩ : syracuseStep 1585975 = 2378963) B2378963
theorem B1880987 : Blo 1252444 1880987 := bstep (se 1 (by rfl) ⟨1410740, by rfl⟩ : syracuseStep 1880987 = 2821481) B2821481
theorem B7230455 : Blo 1252444 7230455 := bstep (se 1 (by rfl) ⟨5422841, by rfl⟩ : syracuseStep 7230455 = 10845683) B10845683
theorem B38581373 : Blo 1252444 38581373 := bstep (se 3 (by rfl) ⟨7234007, by rfl⟩ : syracuseStep 38581373 = 14468015) B14468015
theorem B4519037 : Blo 1252444 4519037 := bstep (se 3 (by rfl) ⟨847319, by rfl⟩ : syracuseStep 4519037 = 1694639) B1694639
theorem B2675855 : Blo 1252444 2675855 := bstep (se 1 (by rfl) ⟨2006891, by rfl⟩ : syracuseStep 2675855 = 4013783) B4013783
theorem B3814543 : Blo 1252444 3814543 := bstep (se 1 (by rfl) ⟨2860907, by rfl⟩ : syracuseStep 3814543 = 5721815) B5721815
theorem B1586395 : Blo 1252444 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B1881383 : Blo 1252444 1881383 := bstep (se 1 (by rfl) ⟨1411037, by rfl⟩ : syracuseStep 1881383 = 2822075) B2822075
theorem B1881467 : Blo 1252444 1881467 := bstep (se 1 (by rfl) ⟨1411100, by rfl⟩ : syracuseStep 1881467 = 2822201) B2822201
theorem B12039617 : Blo 1252444 12039617 := bstep (se 2 (by rfl) ⟨4514856, by rfl⟩ : syracuseStep 12039617 = 9029713) B9029713
theorem B1881593 : Blo 1252444 1881593 := bstep (se 2 (by rfl) ⟨705597, by rfl⟩ : syracuseStep 1881593 = 1411195) B1411195
theorem B6018617 : Blo 1252444 6018617 := bstep (se 2 (by rfl) ⟨2256981, by rfl⟩ : syracuseStep 6018617 = 4513963) B4513963
theorem B5355143 : Blo 1252444 5355143 := bstep (se 1 (by rfl) ⟨4016357, by rfl⟩ : syracuseStep 5355143 = 8032715) B8032715
theorem B3217207 : Blo 1252444 3217207 := bstep (se 1 (by rfl) ⟨2412905, by rfl⟩ : syracuseStep 3217207 = 4825811) B4825811
theorem B10713019 : Blo 1252444 10713019 := bstep (se 1 (by rfl) ⟨8034764, by rfl⟩ : syracuseStep 10713019 = 16069529) B16069529
theorem B4233167 : Blo 1252444 4233167 := bstep (se 1 (by rfl) ⟨3174875, by rfl⟩ : syracuseStep 4233167 = 6349751) B6349751
theorem B5355553 : Blo 1252444 5355553 := bstep (se 2 (by rfl) ⟨2008332, by rfl⟩ : syracuseStep 5355553 = 4016665) B4016665
theorem B8697935 : Blo 1252444 8697935 := bstep (se 1 (by rfl) ⟨6523451, by rfl⟩ : syracuseStep 8697935 = 13046903) B13046903
theorem B9517337 : Blo 1252444 9517337 := bstep (se 2 (by rfl) ⟨3569001, by rfl⟩ : syracuseStep 9517337 = 7138003) B7138003
theorem B6773021 : Blo 1252444 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B10705229 : Blo 1252444 10705229 := bstep (se 3 (by rfl) ⟨2007230, by rfl⟩ : syracuseStep 10705229 = 4014461) B4014461
theorem B36133613 : Blo 1252444 36133613 := bstep (se 3 (by rfl) ⟨6775052, by rfl⟩ : syracuseStep 36133613 = 13550105) B13550105
theorem B6347645 : Blo 1252444 6347645 := bstep (se 3 (by rfl) ⟨1190183, by rfl⟩ : syracuseStep 6347645 = 2380367) B2380367
theorem B3013519 : Blo 1252444 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B4291471 : Blo 1252444 4291471 := bstep (se 1 (by rfl) ⟨3218603, by rfl⟩ : syracuseStep 4291471 = 6437207) B6437207
theorem B9518309 : Blo 1252444 9518309 := bstep (se 4 (by rfl) ⟨892341, by rfl⟩ : syracuseStep 9518309 = 1784683) B1784683
theorem B1252639 : Blo 1252444 1252639 := bstep (se 1 (by rfl) ⟨939479, by rfl⟩ : syracuseStep 1252639 = 1878959) B1878959
theorem B4758851 : Blo 1252444 4758851 := bstep (se 1 (by rfl) ⟨3569138, by rfl⟩ : syracuseStep 4758851 = 7138277) B7138277
theorem B1252699 : Blo 1252444 1252699 := bstep (se 1 (by rfl) ⟨939524, by rfl⟩ : syracuseStep 1252699 = 1879049) B1879049
theorem B1252719 : Blo 1252444 1252719 := bstep (se 1 (by rfl) ⟨939539, by rfl⟩ : syracuseStep 1252719 = 1879079) B1879079
theorem B1252775 : Blo 1252444 1252775 := bstep (se 1 (by rfl) ⟨939581, by rfl⟩ : syracuseStep 1252775 = 1879163) B1879163
theorem B1785287 : Blo 1252444 1785287 := bstep (se 1 (by rfl) ⟨1338965, by rfl⟩ : syracuseStep 1785287 = 2677931) B2677931
theorem B4759033 : Blo 1252444 4759033 := bstep (se 2 (by rfl) ⟨1784637, by rfl⟩ : syracuseStep 4759033 = 3569275) B3569275
theorem B1252859 : Blo 1252444 1252859 := bstep (se 1 (by rfl) ⟨939644, by rfl⟩ : syracuseStep 1252859 = 1879289) B1879289
theorem B1252927 : Blo 1252444 1252927 := bstep (se 1 (by rfl) ⟨939695, by rfl⟩ : syracuseStep 1252927 = 1879391) B1879391
theorem B1252935 : Blo 1252444 1252935 := bstep (se 1 (by rfl) ⟨939701, by rfl⟩ : syracuseStep 1252935 = 1879403) B1879403
theorem B3571361 : Blo 1252444 3571361 := bstep (se 2 (by rfl) ⟨1339260, by rfl⟩ : syracuseStep 3571361 = 2678521) B2678521
theorem B1253087 : Blo 1252444 1253087 := bstep (se 1 (by rfl) ⟨939815, by rfl⟩ : syracuseStep 1253087 = 1879631) B1879631
theorem B5078791 : Blo 1252444 5078791 := bstep (se 1 (by rfl) ⟨3809093, by rfl⟩ : syracuseStep 5078791 = 7618187) B7618187
theorem B4759307 : Blo 1252444 4759307 := bstep (se 1 (by rfl) ⟨3569480, by rfl⟩ : syracuseStep 4759307 = 7138961) B7138961
theorem B4759337 : Blo 1252444 4759337 := bstep (se 2 (by rfl) ⟨1784751, by rfl⟩ : syracuseStep 4759337 = 3569503) B3569503
theorem B1253167 : Blo 1252444 1253167 := bstep (se 1 (by rfl) ⟨939875, by rfl⟩ : syracuseStep 1253167 = 1879751) B1879751
theorem B5799737 : Blo 1252444 5799737 := bstep (se 2 (by rfl) ⟨2174901, by rfl⟩ : syracuseStep 5799737 = 4349803) B4349803
theorem B6348617 : Blo 1252444 6348617 := bstep (se 2 (by rfl) ⟨2380731, by rfl⟩ : syracuseStep 6348617 = 4761463) B4761463
theorem B1253275 : Blo 1252444 1253275 := bstep (se 1 (by rfl) ⟨939956, by rfl⟩ : syracuseStep 1253275 = 1879913) B1879913
theorem B1253327 : Blo 1252444 1253327 := bstep (se 1 (by rfl) ⟨939995, by rfl⟩ : syracuseStep 1253327 = 1879991) B1879991
theorem B1253351 : Blo 1252444 1253351 := bstep (se 1 (by rfl) ⟨940013, by rfl⟩ : syracuseStep 1253351 = 1880027) B1880027
theorem B1253607 : Blo 1252444 1253607 := bstep (se 1 (by rfl) ⟨940205, by rfl⟩ : syracuseStep 1253607 = 1880411) B1880411
theorem B19292417 : Blo 1252444 19292417 := bstep (se 2 (by rfl) ⟨7234656, by rfl⟩ : syracuseStep 19292417 = 14469313) B14469313
theorem B2113823 : Blo 1252444 2113823 := bstep (se 1 (by rfl) ⟨1585367, by rfl⟩ : syracuseStep 2113823 = 3170735) B3170735
theorem B12050765 : Blo 1252444 12050765 := bstep (se 3 (by rfl) ⟨2259518, by rfl⟩ : syracuseStep 12050765 = 4519037) B4519037
theorem B7135613 : Blo 1252444 7135613 := bstep (se 3 (by rfl) ⟨1337927, by rfl⟩ : syracuseStep 7135613 = 2675855) B2675855
theorem B1253759 : Blo 1252444 1253759 := bstep (se 1 (by rfl) ⟨940319, by rfl⟩ : syracuseStep 1253759 = 1880639) B1880639
theorem B14270903 : Blo 1252444 14270903 := bstep (se 1 (by rfl) ⟨10703177, by rfl⟩ : syracuseStep 14270903 = 21406355) B21406355
theorem B9028039 : Blo 1252444 9028039 := bstep (se 1 (by rfl) ⟨6771029, by rfl⟩ : syracuseStep 9028039 = 13542059) B13542059
theorem B2818511 : Blo 1252444 2818511 := bstep (se 1 (by rfl) ⟨2113883, by rfl⟩ : syracuseStep 2818511 = 4227767) B4227767
theorem B1253839 : Blo 1252444 1253839 := bstep (se 1 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 1253839 = 1880759) B1880759
theorem B1253991 : Blo 1252444 1253991 := bstep (se 1 (by rfl) ⟨940493, by rfl⟩ : syracuseStep 1253991 = 1880987) B1880987
theorem B4227713 : Blo 1252444 4227713 := bstep (se 2 (by rfl) ⟨1585392, by rfl⟩ : syracuseStep 4227713 = 3170785) B3170785
theorem B9028331 : Blo 1252444 9028331 := bstep (se 1 (by rfl) ⟨6771248, by rfl⟩ : syracuseStep 9028331 = 13542497) B13542497
theorem B10158857 : Blo 1252444 10158857 := bstep (se 2 (by rfl) ⟨3809571, by rfl⟩ : syracuseStep 10158857 = 7619143) B7619143
theorem B1254255 : Blo 1252444 1254255 := bstep (se 1 (by rfl) ⟨940691, by rfl⟩ : syracuseStep 1254255 = 1881383) B1881383
theorem B4227983 : Blo 1252444 4227983 := bstep (se 1 (by rfl) ⟨3170987, by rfl⟩ : syracuseStep 4227983 = 6341975) B6341975
theorem B2114471 : Blo 1252444 2114471 := bstep (se 1 (by rfl) ⟨1585853, by rfl⟩ : syracuseStep 2114471 = 3171707) B3171707
theorem B1254311 : Blo 1252444 1254311 := bstep (se 1 (by rfl) ⟨940733, by rfl⟩ : syracuseStep 1254311 = 1881467) B1881467
theorem B1410043 : Blo 1252444 1410043 := bstep (se 1 (by rfl) ⟨1057532, by rfl⟩ : syracuseStep 1410043 = 2115065) B2115065
theorem B1254395 : Blo 1252444 1254395 := bstep (se 1 (by rfl) ⟨940796, by rfl⟩ : syracuseStep 1254395 = 1881593) B1881593
theorem B2114633 : Blo 1252444 2114633 := bstep (se 2 (by rfl) ⟨792987, by rfl⟩ : syracuseStep 2114633 = 1585975) B1585975
theorem B3171433 : Blo 1252444 3171433 := bstep (se 2 (by rfl) ⟨1189287, by rfl⟩ : syracuseStep 3171433 = 2378575) B2378575
theorem B2819177 : Blo 1252444 2819177 := bstep (se 2 (by rfl) ⟨1057191, by rfl⟩ : syracuseStep 2819177 = 2114383) B2114383
theorem B1410223 : Blo 1252444 1410223 := bstep (se 1 (by rfl) ⟨1057667, by rfl⟩ : syracuseStep 1410223 = 2115335) B2115335
theorem B6431933 : Blo 1252444 6431933 := bstep (se 3 (by rfl) ⟨1205987, by rfl⟩ : syracuseStep 6431933 = 2411975) B2411975
theorem B4760765 : Blo 1252444 4760765 := bstep (se 3 (by rfl) ⟨892643, by rfl⟩ : syracuseStep 4760765 = 1785287) B1785287
theorem B4228523 : Blo 1252444 4228523 := bstep (se 1 (by rfl) ⟨3171392, by rfl⟩ : syracuseStep 4228523 = 6342785) B6342785
theorem B4515347 : Blo 1252444 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B7136819 : Blo 1252444 7136819 := bstep (se 1 (by rfl) ⟨5352614, by rfl⟩ : syracuseStep 7136819 = 10705229) B10705229
theorem B2115193 : Blo 1252444 2115193 := bstep (se 2 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 2115193 = 1586395) B1586395
theorem B1410727 : Blo 1252444 1410727 := bstep (se 1 (by rfl) ⟨1058045, by rfl⟩ : syracuseStep 1410727 = 2116091) B2116091
theorem B2819807 : Blo 1252444 2819807 := bstep (se 1 (by rfl) ⟨2114855, by rfl⟩ : syracuseStep 2819807 = 4229711) B4229711
theorem B1607455 : Blo 1252444 1607455 := bstep (se 1 (by rfl) ⟨1205591, by rfl⟩ : syracuseStep 1607455 = 2411183) B2411183
theorem B6342461 : Blo 1252444 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B3172193 : Blo 1252444 3172193 := bstep (se 2 (by rfl) ⟨1189572, by rfl⟩ : syracuseStep 3172193 = 2379145) B2379145
theorem B4229063 : Blo 1252444 4229063 := bstep (se 1 (by rfl) ⟨3171797, by rfl⟩ : syracuseStep 4229063 = 6343595) B6343595
theorem B1411015 : Blo 1252444 1411015 := bstep (se 1 (by rfl) ⟨1058261, by rfl⟩ : syracuseStep 1411015 = 2116523) B2116523
theorem B16058411 : Blo 1252444 16058411 := bstep (se 1 (by rfl) ⟨12043808, by rfl⟩ : syracuseStep 16058411 = 24087617) B24087617
theorem B16050257 : Blo 1252444 16050257 := bstep (se 2 (by rfl) ⟨6018846, by rfl⟩ : syracuseStep 16050257 = 12037693) B12037693
theorem B2115679 : Blo 1252444 2115679 := bstep (se 1 (by rfl) ⟨1586759, by rfl⟩ : syracuseStep 2115679 = 3173519) B3173519
theorem B3172567 : Blo 1252444 3172567 := bstep (se 1 (by rfl) ⟨2379425, by rfl⟩ : syracuseStep 3172567 = 4758851) B4758851
theorem B20334887 : Blo 1252444 20334887 := bstep (se 1 (by rfl) ⟨15251165, by rfl⟩ : syracuseStep 20334887 = 30502331) B30502331
theorem B3172871 : Blo 1252444 3172871 := bstep (se 1 (by rfl) ⟨2379653, by rfl⟩ : syracuseStep 3172871 = 4759307) B4759307
theorem B3172891 : Blo 1252444 3172891 := bstep (se 1 (by rfl) ⟨2379668, by rfl⟩ : syracuseStep 3172891 = 4759337) B4759337
theorem B2820635 : Blo 1252444 2820635 := bstep (se 1 (by rfl) ⟨2115476, by rfl⟩ : syracuseStep 2820635 = 4230953) B4230953
theorem B24087071 : Blo 1252444 24087071 := bstep (se 1 (by rfl) ⟨18065303, by rfl⟩ : syracuseStep 24087071 = 36130607) B36130607
theorem B4229819 : Blo 1252444 4229819 := bstep (se 1 (by rfl) ⟨3172364, by rfl⟩ : syracuseStep 4229819 = 6344729) B6344729
theorem B1878839 : Blo 1252444 1878839 := bstep (se 1 (by rfl) ⟨1409129, by rfl⟩ : syracuseStep 1878839 = 2818259) B2818259
theorem B2034487 : Blo 1252444 2034487 := bstep (se 1 (by rfl) ⟨1525865, by rfl⟩ : syracuseStep 2034487 = 3051731) B3051731
theorem B1878875 : Blo 1252444 1878875 := bstep (se 1 (by rfl) ⟨1409156, by rfl⟩ : syracuseStep 1878875 = 2818313) B2818313
theorem B4017127 : Blo 1252444 4017127 := bstep (se 1 (by rfl) ⟨3012845, by rfl⟩ : syracuseStep 4017127 = 6025691) B6025691
theorem B1879019 : Blo 1252444 1879019 := bstep (se 1 (by rfl) ⟨1409264, by rfl⟩ : syracuseStep 1879019 = 2818529) B2818529
theorem B18082835 : Blo 1252444 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B3566713 : Blo 1252444 3566713 := bstep (se 2 (by rfl) ⟨1337517, by rfl⟩ : syracuseStep 3566713 = 2675035) B2675035
theorem B9653411 : Blo 1252444 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B1879223 : Blo 1252444 1879223 := bstep (se 1 (by rfl) ⟨1409417, by rfl⟩ : syracuseStep 1879223 = 2818835) B2818835
theorem B4820303 : Blo 1252444 4820303 := bstep (se 1 (by rfl) ⟨3615227, by rfl⟩ : syracuseStep 4820303 = 7230455) B7230455
theorem B68644259 : Blo 1252444 68644259 := bstep (se 1 (by rfl) ⟨51483194, by rfl⟩ : syracuseStep 68644259 = 102966389) B102966389
theorem B1879463 : Blo 1252444 1879463 := bstep (se 1 (by rfl) ⟨1409597, by rfl⟩ : syracuseStep 1879463 = 2819195) B2819195
theorem B1879547 : Blo 1252444 1879547 := bstep (se 1 (by rfl) ⟨1409660, by rfl⟩ : syracuseStep 1879547 = 2819321) B2819321
theorem B1879643 : Blo 1252444 1879643 := bstep (se 1 (by rfl) ⟨1409732, by rfl⟩ : syracuseStep 1879643 = 2819465) B2819465
theorem B1879727 : Blo 1252444 1879727 := bstep (se 1 (by rfl) ⟨1409795, by rfl⟩ : syracuseStep 1879727 = 2819591) B2819591
theorem B1879847 : Blo 1252444 1879847 := bstep (se 1 (by rfl) ⟨1409885, by rfl⟩ : syracuseStep 1879847 = 2819771) B2819771
theorem B4018025 : Blo 1252444 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B19296107 : Blo 1252444 19296107 := bstep (se 1 (by rfl) ⟨14472080, by rfl⟩ : syracuseStep 19296107 = 28944161) B28944161
theorem B8580971 : Blo 1252444 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B12054379 : Blo 1252444 12054379 := bstep (se 1 (by rfl) ⟨9040784, by rfl⟩ : syracuseStep 12054379 = 18081569) B18081569
theorem B1879931 : Blo 1252444 1879931 := bstep (se 1 (by rfl) ⟨1409948, by rfl⟩ : syracuseStep 1879931 = 2819897) B2819897
theorem B3174299 : Blo 1252444 3174299 := bstep (se 1 (by rfl) ⟨2380724, by rfl⟩ : syracuseStep 3174299 = 4761449) B4761449
theorem B7139279 : Blo 1252444 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B2822111 : Blo 1252444 2822111 := bstep (se 1 (by rfl) ⟨2116583, by rfl⟩ : syracuseStep 2822111 = 4233167) B4233167
theorem B27086885 : Blo 1252444 27086885 := bstep (se 4 (by rfl) ⟨2539395, by rfl⟩ : syracuseStep 27086885 = 5078791) B5078791
theorem B6344891 : Blo 1252444 6344891 := bstep (se 1 (by rfl) ⟨4758668, by rfl⟩ : syracuseStep 6344891 = 9517337) B9517337
theorem B1880351 : Blo 1252444 1880351 := bstep (se 1 (by rfl) ⟨1410263, by rfl⟩ : syracuseStep 1880351 = 2820527) B2820527
theorem B1880375 : Blo 1252444 1880375 := bstep (se 1 (by rfl) ⟨1410281, by rfl⟩ : syracuseStep 1880375 = 2820563) B2820563
theorem B1880447 : Blo 1252444 1880447 := bstep (se 1 (by rfl) ⟨1410335, by rfl⟩ : syracuseStep 1880447 = 2820671) B2820671
theorem B1880519 : Blo 1252444 1880519 := bstep (se 1 (by rfl) ⟨1410389, by rfl⟩ : syracuseStep 1880519 = 2820779) B2820779
theorem B24089075 : Blo 1252444 24089075 := bstep (se 1 (by rfl) ⟨18066806, by rfl⟩ : syracuseStep 24089075 = 36133613) B36133613
theorem B8032769 : Blo 1252444 8032769 := bstep (se 2 (by rfl) ⟨3012288, by rfl⟩ : syracuseStep 8032769 = 6024577) B6024577
theorem B4231763 : Blo 1252444 4231763 := bstep (se 1 (by rfl) ⟨3173822, by rfl⟩ : syracuseStep 4231763 = 6347645) B6347645
theorem B7139987 : Blo 1252444 7139987 := bstep (se 1 (by rfl) ⟨5354990, by rfl⟩ : syracuseStep 7139987 = 10709981) B10709981
theorem B6345377 : Blo 1252444 6345377 := bstep (se 2 (by rfl) ⟨2379516, by rfl⟩ : syracuseStep 6345377 = 4759033) B4759033
theorem B1880873 : Blo 1252444 1880873 := bstep (se 2 (by rfl) ⟨705327, by rfl⟩ : syracuseStep 1880873 = 1410655) B1410655
theorem B1880879 : Blo 1252444 1880879 := bstep (se 1 (by rfl) ⟨1410659, by rfl⟩ : syracuseStep 1880879 = 2821319) B2821319
theorem B6345539 : Blo 1252444 6345539 := bstep (se 1 (by rfl) ⟨4759154, by rfl⟩ : syracuseStep 6345539 = 9518309) B9518309
theorem B1880999 : Blo 1252444 1880999 := bstep (se 1 (by rfl) ⟨1410749, by rfl⟩ : syracuseStep 1880999 = 2821499) B2821499
theorem B1881083 : Blo 1252444 1881083 := bstep (se 1 (by rfl) ⟨1410812, by rfl⟩ : syracuseStep 1881083 = 2821625) B2821625
theorem B1881143 : Blo 1252444 1881143 := bstep (se 1 (by rfl) ⟨1410857, by rfl⟩ : syracuseStep 1881143 = 2821715) B2821715
theorem B4289609 : Blo 1252444 4289609 := bstep (se 2 (by rfl) ⟨1608603, by rfl⟩ : syracuseStep 4289609 = 3217207) B3217207
theorem B2380907 : Blo 1252444 2380907 := bstep (se 1 (by rfl) ⟨1785680, by rfl⟩ : syracuseStep 2380907 = 3571361) B3571361
theorem B1881263 : Blo 1252444 1881263 := bstep (se 1 (by rfl) ⟨1410947, by rfl⟩ : syracuseStep 1881263 = 2821895) B2821895
theorem B4232411 : Blo 1252444 4232411 := bstep (se 1 (by rfl) ⟨3174308, by rfl⟩ : syracuseStep 4232411 = 6348617) B6348617
theorem B14284025 : Blo 1252444 14284025 := bstep (se 2 (by rfl) ⟨5356509, by rfl⟩ : syracuseStep 14284025 = 10713019) B10713019
theorem B6780179 : Blo 1252444 6780179 := bstep (se 1 (by rfl) ⟨5085134, by rfl⟩ : syracuseStep 6780179 = 10170269) B10170269
theorem B2290963 : Blo 1252444 2290963 := bstep (se 1 (by rfl) ⟨1718222, by rfl⟩ : syracuseStep 2290963 = 3436445) B3436445
theorem B7140737 : Blo 1252444 7140737 := bstep (se 2 (by rfl) ⟨2677776, by rfl⟩ : syracuseStep 7140737 = 5355553) B5355553
theorem B6346349 : Blo 1252444 6346349 := bstep (se 3 (by rfl) ⟨1189940, by rfl⟩ : syracuseStep 6346349 = 2379881) B2379881
theorem B1906343 : Blo 1252444 1906343 := bstep (se 1 (by rfl) ⟨1429757, by rfl⟩ : syracuseStep 1906343 = 2859515) B2859515
theorem B16053947 : Blo 1252444 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B5576663 : Blo 1252444 5576663 := bstep (se 1 (by rfl) ⟨4182497, by rfl⟩ : syracuseStep 5576663 = 8364995) B8364995
theorem B72275975 : Blo 1252444 72275975 := bstep (se 1 (by rfl) ⟨54206981, by rfl⟩ : syracuseStep 72275975 = 108413963) B108413963
theorem B4233275 : Blo 1252444 4233275 := bstep (se 1 (by rfl) ⟨3174956, by rfl⟩ : syracuseStep 4233275 = 6349913) B6349913
theorem B25720915 : Blo 1252444 25720915 := bstep (se 1 (by rfl) ⟨19290686, by rfl⟩ : syracuseStep 25720915 = 38581373) B38581373
theorem B8026411 : Blo 1252444 8026411 := bstep (se 1 (by rfl) ⟨6019808, by rfl⟩ : syracuseStep 8026411 = 12039617) B12039617
theorem B25418033 : Blo 1252444 25418033 := bstep (se 2 (by rfl) ⟨9531762, by rfl⟩ : syracuseStep 25418033 = 19063525) B19063525
theorem B4233545 : Blo 1252444 4233545 := bstep (se 2 (by rfl) ⟨1587579, by rfl⟩ : syracuseStep 4233545 = 3175159) B3175159
theorem B4012411 : Blo 1252444 4012411 := bstep (se 1 (by rfl) ⟨3009308, by rfl⟩ : syracuseStep 4012411 = 6018617) B6018617
theorem B6101423 : Blo 1252444 6101423 := bstep (se 1 (by rfl) ⟨4576067, by rfl⟩ : syracuseStep 6101423 = 9152135) B9152135
theorem B3570095 : Blo 1252444 3570095 := bstep (se 1 (by rfl) ⟨2677571, by rfl⟩ : syracuseStep 3570095 = 5355143) B5355143
theorem B7133629 : Blo 1252444 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B9165449 : Blo 1252444 9165449 := bstep (se 2 (by rfl) ⟨3437043, by rfl⟩ : syracuseStep 9165449 = 6874087) B6874087
theorem B5798623 : Blo 1252444 5798623 := bstep (se 1 (by rfl) ⟨4348967, by rfl⟩ : syracuseStep 5798623 = 8697935) B8697935
theorem B30497579 : Blo 1252444 30497579 := bstep (se 1 (by rfl) ⟨22873184, by rfl⟩ : syracuseStep 30497579 = 45746369) B45746369
theorem B5086057 : Blo 1252444 5086057 := bstep (se 2 (by rfl) ⟨1907271, by rfl⟩ : syracuseStep 5086057 = 3814543) B3814543
theorem B6020077 : Blo 1252444 6020077 := bstep (se 3 (by rfl) ⟨1128764, by rfl⟩ : syracuseStep 6020077 = 2257529) B2257529
theorem B1252575 : Blo 1252444 1252575 := bstep (se 1 (by rfl) ⟨939431, by rfl⟩ : syracuseStep 1252575 = 1878863) B1878863
theorem B8576351 : Blo 1252444 8576351 := bstep (se 1 (by rfl) ⟨6432263, by rfl⟩ : syracuseStep 8576351 = 12864527) B12864527
theorem B22887845 : Blo 1252444 22887845 := bstep (se 4 (by rfl) ⟨2145735, by rfl⟩ : syracuseStep 22887845 = 4291471) B4291471
theorem B1252839 : Blo 1252444 1252839 := bstep (se 1 (by rfl) ⟨939629, by rfl⟩ : syracuseStep 1252839 = 1879259) B1879259
theorem B1252955 : Blo 1252444 1252955 := bstep (se 1 (by rfl) ⟨939716, by rfl⟩ : syracuseStep 1252955 = 1879433) B1879433
theorem B5717729 : Blo 1252444 5717729 := bstep (se 2 (by rfl) ⟨2144148, by rfl⟩ : syracuseStep 5717729 = 4288297) B4288297
theorem B1253191 : Blo 1252444 1253191 := bstep (se 1 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 1253191 = 1879787) B1879787
theorem B3866491 : Blo 1252444 3866491 := bstep (se 1 (by rfl) ⟨2899868, by rfl⟩ : syracuseStep 3866491 = 5799737) B5799737
theorem B1253343 : Blo 1252444 1253343 := bstep (se 1 (by rfl) ⟨940007, by rfl⟩ : syracuseStep 1253343 = 1880015) B1880015
theorem B12861611 : Blo 1252444 12861611 := bstep (se 1 (by rfl) ⟨9646208, by rfl⟩ : syracuseStep 12861611 = 19292417) B19292417
theorem B1409215 : Blo 1252444 1409215 := bstep (se 1 (by rfl) ⟨1056911, by rfl⟩ : syracuseStep 1409215 = 2113823) B2113823
theorem B1253567 : Blo 1252444 1253567 := bstep (se 1 (by rfl) ⟨940175, by rfl⟩ : syracuseStep 1253567 = 1880351) B1880351
theorem B1253583 : Blo 1252444 1253583 := bstep (se 1 (by rfl) ⟨940187, by rfl⟩ : syracuseStep 1253583 = 1880375) B1880375
theorem B1253631 : Blo 1252444 1253631 := bstep (se 1 (by rfl) ⟨940223, by rfl⟩ : syracuseStep 1253631 = 1880447) B1880447
theorem B1253679 : Blo 1252444 1253679 := bstep (se 1 (by rfl) ⟨940259, by rfl⟩ : syracuseStep 1253679 = 1880519) B1880519
theorem B2818475 : Blo 1252444 2818475 := bstep (se 1 (by rfl) ⟨2113856, by rfl⟩ : syracuseStep 2818475 = 4227713) B4227713
theorem B4759991 : Blo 1252444 4759991 := bstep (se 1 (by rfl) ⟨3569993, by rfl⟩ : syracuseStep 4759991 = 7139987) B7139987
theorem B5349881 : Blo 1252444 5349881 := bstep (se 2 (by rfl) ⟨2006205, by rfl⟩ : syracuseStep 5349881 = 4012411) B4012411
theorem B1253915 : Blo 1252444 1253915 := bstep (se 1 (by rfl) ⟨940436, by rfl⟩ : syracuseStep 1253915 = 1880873) B1880873
theorem B1253919 : Blo 1252444 1253919 := bstep (se 1 (by rfl) ⟨940439, by rfl⟩ : syracuseStep 1253919 = 1880879) B1880879
theorem B9511505 : Blo 1252444 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B2818655 : Blo 1252444 2818655 := bstep (se 1 (by rfl) ⟨2113991, by rfl⟩ : syracuseStep 2818655 = 4227983) B4227983
theorem B1409647 : Blo 1252444 1409647 := bstep (se 1 (by rfl) ⟨1057235, by rfl⟩ : syracuseStep 1409647 = 2114471) B2114471
theorem B1253999 : Blo 1252444 1253999 := bstep (se 1 (by rfl) ⟨940499, by rfl⟩ : syracuseStep 1253999 = 1880999) B1880999
theorem B1254055 : Blo 1252444 1254055 := bstep (se 1 (by rfl) ⟨940541, by rfl⟩ : syracuseStep 1254055 = 1881083) B1881083
theorem B1254095 : Blo 1252444 1254095 := bstep (se 1 (by rfl) ⟨940571, by rfl⟩ : syracuseStep 1254095 = 1881143) B1881143
theorem B1409755 : Blo 1252444 1409755 := bstep (se 1 (by rfl) ⟨1057316, by rfl⟩ : syracuseStep 1409755 = 2114633) B2114633
theorem B1254175 : Blo 1252444 1254175 := bstep (se 1 (by rfl) ⟨940631, by rfl⟩ : syracuseStep 1254175 = 1881263) B1881263
theorem B4760491 : Blo 1252444 4760491 := bstep (se 1 (by rfl) ⟨3570368, by rfl⟩ : syracuseStep 4760491 = 7140737) B7140737
theorem B2819015 : Blo 1252444 2819015 := bstep (se 1 (by rfl) ⟨2114261, by rfl⟩ : syracuseStep 2819015 = 4228523) B4228523
theorem B1270895 : Blo 1252444 1270895 := bstep (se 1 (by rfl) ⟨953171, by rfl⟩ : syracuseStep 1270895 = 1906343) B1906343
theorem B9520253 : Blo 1252444 9520253 := bstep (se 3 (by rfl) ⟨1785047, by rfl⟩ : syracuseStep 9520253 = 3570095) B3570095
theorem B4228307 : Blo 1252444 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B2114795 : Blo 1252444 2114795 := bstep (se 1 (by rfl) ⟨1586096, by rfl⟩ : syracuseStep 2114795 = 3172193) B3172193
theorem B2819375 : Blo 1252444 2819375 := bstep (se 1 (by rfl) ⟨2114531, by rfl⟩ : syracuseStep 2819375 = 4229063) B4229063
theorem B10700171 : Blo 1252444 10700171 := bstep (se 1 (by rfl) ⟨8025128, by rfl⟩ : syracuseStep 10700171 = 16050257) B16050257
theorem B4228577 : Blo 1252444 4228577 := bstep (se 2 (by rfl) ⟨1585716, by rfl⟩ : syracuseStep 4228577 = 3171433) B3171433
theorem B2115247 : Blo 1252444 2115247 := bstep (se 1 (by rfl) ⟨1586435, by rfl⟩ : syracuseStep 2115247 = 3172871) B3172871
theorem B16058047 : Blo 1252444 16058047 := bstep (se 1 (by rfl) ⟨12043535, by rfl⟩ : syracuseStep 16058047 = 24087071) B24087071
theorem B2819879 : Blo 1252444 2819879 := bstep (se 1 (by rfl) ⟨2114909, by rfl⟩ : syracuseStep 2819879 = 4229819) B4229819
theorem B15247277 : Blo 1252444 15247277 := bstep (se 3 (by rfl) ⟨2858864, by rfl⟩ : syracuseStep 15247277 = 5717729) B5717729
theorem B2820257 : Blo 1252444 2820257 := bstep (se 2 (by rfl) ⟨1057596, by rfl⟩ : syracuseStep 2820257 = 2115193) B2115193
theorem B3213535 : Blo 1252444 3213535 := bstep (se 1 (by rfl) ⟨2410151, by rfl⟩ : syracuseStep 3213535 = 4820303) B4820303
theorem B45762839 : Blo 1252444 45762839 := bstep (se 1 (by rfl) ⟨34322129, by rfl⟩ : syracuseStep 45762839 = 68644259) B68644259
theorem B5155321 : Blo 1252444 5155321 := bstep (se 2 (by rfl) ⟨1933245, by rfl⟩ : syracuseStep 5155321 = 3866491) B3866491
theorem B12864071 : Blo 1252444 12864071 := bstep (se 1 (by rfl) ⟨9648053, by rfl⟩ : syracuseStep 12864071 = 19296107) B19296107
theorem B5720647 : Blo 1252444 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B2116199 : Blo 1252444 2116199 := bstep (se 1 (by rfl) ⟨1587149, by rfl⟩ : syracuseStep 2116199 = 3174299) B3174299
theorem B18057923 : Blo 1252444 18057923 := bstep (se 1 (by rfl) ⟨13543442, by rfl⟩ : syracuseStep 18057923 = 27086885) B27086885
theorem B34294553 : Blo 1252444 34294553 := bstep (se 2 (by rfl) ⟨12860457, by rfl⟩ : syracuseStep 34294553 = 25720915) B25720915
theorem B4229927 : Blo 1252444 4229927 := bstep (se 1 (by rfl) ⟨3172445, by rfl⟩ : syracuseStep 4229927 = 6344891) B6344891
theorem B2820905 : Blo 1252444 2820905 := bstep (se 2 (by rfl) ⟨1057839, by rfl⟩ : syracuseStep 2820905 = 2115679) B2115679
theorem B11438957 : Blo 1252444 11438957 := bstep (se 3 (by rfl) ⟨2144804, by rfl⟩ : syracuseStep 11438957 = 4289609) B4289609
theorem B4230089 : Blo 1252444 4230089 := bstep (se 2 (by rfl) ⟨1586283, by rfl⟩ : syracuseStep 4230089 = 3172567) B3172567
theorem B9513935 : Blo 1252444 9513935 := bstep (se 1 (by rfl) ⟨7135451, by rfl⟩ : syracuseStep 9513935 = 14270903) B14270903
theorem B1879007 : Blo 1252444 1879007 := bstep (se 1 (by rfl) ⟨1409255, by rfl⟩ : syracuseStep 1879007 = 2818511) B2818511
theorem B16059383 : Blo 1252444 16059383 := bstep (se 1 (by rfl) ⟨12044537, by rfl⟩ : syracuseStep 16059383 = 24089075) B24089075
theorem B2821175 : Blo 1252444 2821175 := bstep (se 1 (by rfl) ⟨2115881, by rfl⟩ : syracuseStep 2821175 = 4231763) B4231763
theorem B10701881 : Blo 1252444 10701881 := bstep (se 2 (by rfl) ⟨4013205, by rfl⟩ : syracuseStep 10701881 = 8026411) B8026411
theorem B4230251 : Blo 1252444 4230251 := bstep (se 1 (by rfl) ⟨3172688, by rfl⟩ : syracuseStep 4230251 = 6345377) B6345377
theorem B4230359 : Blo 1252444 4230359 := bstep (se 1 (by rfl) ⟨3172769, by rfl⟩ : syracuseStep 4230359 = 6345539) B6345539
theorem B12037385 : Blo 1252444 12037385 := bstep (se 2 (by rfl) ⟨4514019, by rfl⟩ : syracuseStep 12037385 = 9028039) B9028039
theorem B4230521 : Blo 1252444 4230521 := bstep (se 2 (by rfl) ⟨1586445, by rfl⟩ : syracuseStep 4230521 = 3172891) B3172891
theorem B1879451 : Blo 1252444 1879451 := bstep (se 1 (by rfl) ⟨1409588, by rfl⟩ : syracuseStep 1879451 = 2819177) B2819177
theorem B3173843 : Blo 1252444 3173843 := bstep (se 1 (by rfl) ⟨2380382, by rfl⟩ : syracuseStep 3173843 = 4760765) B4760765
theorem B2821607 : Blo 1252444 2821607 := bstep (se 1 (by rfl) ⟨2116205, by rfl⟩ : syracuseStep 2821607 = 4232411) B4232411
theorem B9522683 : Blo 1252444 9522683 := bstep (se 1 (by rfl) ⟨7142012, by rfl⟩ : syracuseStep 9522683 = 14284025) B14284025
theorem B3010231 : Blo 1252444 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B4230899 : Blo 1252444 4230899 := bstep (se 1 (by rfl) ⟨3173174, by rfl⟩ : syracuseStep 4230899 = 6346349) B6346349
theorem B10702631 : Blo 1252444 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B1879871 : Blo 1252444 1879871 := bstep (se 1 (by rfl) ⟨1409903, by rfl⟩ : syracuseStep 1879871 = 2819807) B2819807
theorem B1880057 : Blo 1252444 1880057 := bstep (se 2 (by rfl) ⟨705021, by rfl⟩ : syracuseStep 1880057 = 1410043) B1410043
theorem B2822183 : Blo 1252444 2822183 := bstep (se 1 (by rfl) ⟨2116637, by rfl⟩ : syracuseStep 2822183 = 4233275) B4233275
theorem B4755617 : Blo 1252444 4755617 := bstep (se 2 (by rfl) ⟨1783356, by rfl⟩ : syracuseStep 4755617 = 3566713) B3566713
theorem B16945355 : Blo 1252444 16945355 := bstep (se 1 (by rfl) ⟨12709016, by rfl⟩ : syracuseStep 16945355 = 25418033) B25418033
theorem B2822363 : Blo 1252444 2822363 := bstep (se 1 (by rfl) ⟨2116772, by rfl⟩ : syracuseStep 2822363 = 4233545) B4233545
theorem B1880297 : Blo 1252444 1880297 := bstep (se 2 (by rfl) ⟨705111, by rfl⟩ : syracuseStep 1880297 = 1410223) B1410223
theorem B4067615 : Blo 1252444 4067615 := bstep (se 1 (by rfl) ⟨3050711, by rfl⟩ : syracuseStep 4067615 = 6101423) B6101423
theorem B10850597 : Blo 1252444 10850597 := bstep (se 4 (by rfl) ⟨1017243, by rfl⟩ : syracuseStep 10850597 = 2034487) B2034487
theorem B1880423 : Blo 1252444 1880423 := bstep (se 1 (by rfl) ⟨1410317, by rfl⟩ : syracuseStep 1880423 = 2820635) B2820635
theorem B12055223 : Blo 1252444 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B6435607 : Blo 1252444 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B1880969 : Blo 1252444 1880969 := bstep (se 2 (by rfl) ⟨705363, by rfl⟩ : syracuseStep 1880969 = 1410727) B1410727
theorem B15258563 : Blo 1252444 15258563 := bstep (se 1 (by rfl) ⟨11443922, by rfl⟩ : syracuseStep 15258563 = 22887845) B22887845
theorem B2143273 : Blo 1252444 2143273 := bstep (se 2 (by rfl) ⟨803727, by rfl⟩ : syracuseStep 2143273 = 1607455) B1607455
theorem B1881353 : Blo 1252444 1881353 := bstep (se 2 (by rfl) ⟨705507, by rfl⟩ : syracuseStep 1881353 = 1411015) B1411015
theorem B1881407 : Blo 1252444 1881407 := bstep (se 1 (by rfl) ⟨1411055, by rfl⟩ : syracuseStep 1881407 = 2822111) B2822111
theorem B8033843 : Blo 1252444 8033843 := bstep (se 1 (by rfl) ⟨6025382, by rfl⟩ : syracuseStep 8033843 = 12050765) B12050765
theorem B4757075 : Blo 1252444 4757075 := bstep (se 1 (by rfl) ⟨3567806, by rfl⟩ : syracuseStep 4757075 = 7135613) B7135613
theorem B5355179 : Blo 1252444 5355179 := bstep (se 1 (by rfl) ⟨4016384, by rfl⟩ : syracuseStep 5355179 = 8032769) B8032769
theorem B6018887 : Blo 1252444 6018887 := bstep (se 1 (by rfl) ⟨4514165, by rfl⟩ : syracuseStep 6018887 = 9028331) B9028331
theorem B17151821 : Blo 1252444 17151821 := bstep (se 3 (by rfl) ⟨3215966, by rfl⟩ : syracuseStep 17151821 = 6431933) B6431933
theorem B6772571 : Blo 1252444 6772571 := bstep (se 1 (by rfl) ⟨5079428, by rfl⟩ : syracuseStep 6772571 = 10158857) B10158857
theorem B1587271 : Blo 1252444 1587271 := bstep (se 1 (by rfl) ⟨1190453, by rfl⟩ : syracuseStep 1587271 = 2380907) B2380907
theorem B4520119 : Blo 1252444 4520119 := bstep (se 1 (by rfl) ⟨3390089, by rfl⟩ : syracuseStep 4520119 = 6780179) B6780179
theorem B7731497 : Blo 1252444 7731497 := bstep (se 2 (by rfl) ⟨2899311, by rfl⟩ : syracuseStep 7731497 = 5798623) B5798623
theorem B4757879 : Blo 1252444 4757879 := bstep (se 1 (by rfl) ⟨3568409, by rfl⟩ : syracuseStep 4757879 = 7136819) B7136819
theorem B6781409 : Blo 1252444 6781409 := bstep (se 2 (by rfl) ⟨2543028, by rfl⟩ : syracuseStep 6781409 = 5086057) B5086057
theorem B5356169 : Blo 1252444 5356169 := bstep (se 2 (by rfl) ⟨2008563, by rfl⟩ : syracuseStep 5356169 = 4017127) B4017127
theorem B3717775 : Blo 1252444 3717775 := bstep (se 1 (by rfl) ⟨2788331, by rfl⟩ : syracuseStep 3717775 = 5576663) B5576663
theorem B8026769 : Blo 1252444 8026769 := bstep (se 2 (by rfl) ⟨3010038, by rfl⟩ : syracuseStep 8026769 = 6020077) B6020077
theorem B48183983 : Blo 1252444 48183983 := bstep (se 1 (by rfl) ⟨36137987, by rfl⟩ : syracuseStep 48183983 = 72275975) B72275975
theorem B10705607 : Blo 1252444 10705607 := bstep (se 1 (by rfl) ⟨8029205, by rfl⟩ : syracuseStep 10705607 = 16058411) B16058411
theorem B13556591 : Blo 1252444 13556591 := bstep (se 1 (by rfl) ⟨10167443, by rfl⟩ : syracuseStep 13556591 = 20334887) B20334887
theorem B3054617 : Blo 1252444 3054617 := bstep (se 2 (by rfl) ⟨1145481, by rfl⟩ : syracuseStep 3054617 = 2290963) B2290963
theorem B6110299 : Blo 1252444 6110299 := bstep (se 1 (by rfl) ⟨4582724, by rfl⟩ : syracuseStep 6110299 = 9165449) B9165449
theorem B20331719 : Blo 1252444 20331719 := bstep (se 1 (by rfl) ⟨15248789, by rfl⟩ : syracuseStep 20331719 = 30497579) B30497579
theorem B1252559 : Blo 1252444 1252559 := bstep (se 1 (by rfl) ⟨939419, by rfl⟩ : syracuseStep 1252559 = 1878839) B1878839
theorem B1252583 : Blo 1252444 1252583 := bstep (se 1 (by rfl) ⟨939437, by rfl⟩ : syracuseStep 1252583 = 1878875) B1878875
theorem B1252679 : Blo 1252444 1252679 := bstep (se 1 (by rfl) ⟨939509, by rfl⟩ : syracuseStep 1252679 = 1879019) B1879019
theorem B1252815 : Blo 1252444 1252815 := bstep (se 1 (by rfl) ⟨939611, by rfl⟩ : syracuseStep 1252815 = 1879223) B1879223
theorem B5717567 : Blo 1252444 5717567 := bstep (se 1 (by rfl) ⟨4288175, by rfl⟩ : syracuseStep 5717567 = 8576351) B8576351
theorem B1252975 : Blo 1252444 1252975 := bstep (se 1 (by rfl) ⟨939731, by rfl⟩ : syracuseStep 1252975 = 1879463) B1879463
theorem B1253031 : Blo 1252444 1253031 := bstep (se 1 (by rfl) ⟨939773, by rfl⟩ : syracuseStep 1253031 = 1879547) B1879547
theorem B1253095 : Blo 1252444 1253095 := bstep (se 1 (by rfl) ⟨939821, by rfl⟩ : syracuseStep 1253095 = 1879643) B1879643
theorem B1253151 : Blo 1252444 1253151 := bstep (se 1 (by rfl) ⟨939863, by rfl⟩ : syracuseStep 1253151 = 1879727) B1879727
theorem B16072505 : Blo 1252444 16072505 := bstep (se 2 (by rfl) ⟨6027189, by rfl⟩ : syracuseStep 16072505 = 12054379) B12054379
theorem B1253231 : Blo 1252444 1253231 := bstep (se 1 (by rfl) ⟨939923, by rfl⟩ : syracuseStep 1253231 = 1879847) B1879847
theorem B2678683 : Blo 1252444 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B1253287 : Blo 1252444 1253287 := bstep (se 1 (by rfl) ⟨939965, by rfl⟩ : syracuseStep 1253287 = 1879931) B1879931
theorem B4759519 : Blo 1252444 4759519 := bstep (se 1 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 4759519 = 7139279) B7139279
theorem B3170411 : Blo 1252444 3170411 := bstep (se 1 (by rfl) ⟨2377808, by rfl⟩ : syracuseStep 3170411 = 4755617) B4755617
theorem B11296903 : Blo 1252444 11296903 := bstep (se 1 (by rfl) ⟨8472677, by rfl⟩ : syracuseStep 11296903 = 16945355) B16945355
theorem B1253531 : Blo 1252444 1253531 := bstep (se 1 (by rfl) ⟨940148, by rfl⟩ : syracuseStep 1253531 = 1880297) B1880297
theorem B7233731 : Blo 1252444 7233731 := bstep (se 1 (by rfl) ⟨5425298, by rfl⟩ : syracuseStep 7233731 = 10850597) B10850597
theorem B1253615 : Blo 1252444 1253615 := bstep (se 1 (by rfl) ⟨940211, by rfl⟩ : syracuseStep 1253615 = 1880423) B1880423
theorem B4284713 : Blo 1252444 4284713 := bstep (se 2 (by rfl) ⟨1606767, by rfl⟩ : syracuseStep 4284713 = 3213535) B3213535
theorem B6341003 : Blo 1252444 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B8036815 : Blo 1252444 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B1253979 : Blo 1252444 1253979 := bstep (se 1 (by rfl) ⟨940484, by rfl⟩ : syracuseStep 1253979 = 1880969) B1880969
theorem B6873761 : Blo 1252444 6873761 := bstep (se 2 (by rfl) ⟨2577660, by rfl⟩ : syracuseStep 6873761 = 5155321) B5155321
theorem B10846973 : Blo 1252444 10846973 := bstep (se 3 (by rfl) ⟨2033807, by rfl⟩ : syracuseStep 10846973 = 4067615) B4067615
theorem B7627529 : Blo 1252444 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B2818871 : Blo 1252444 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B1409863 : Blo 1252444 1409863 := bstep (se 1 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 1409863 = 2114795) B2114795
theorem B1254235 : Blo 1252444 1254235 := bstep (se 1 (by rfl) ⟨940676, by rfl⟩ : syracuseStep 1254235 = 1881353) B1881353
theorem B4957033 : Blo 1252444 4957033 := bstep (se 2 (by rfl) ⟨1858887, by rfl⟩ : syracuseStep 4957033 = 3717775) B3717775
theorem B1254271 : Blo 1252444 1254271 := bstep (se 1 (by rfl) ⟨940703, by rfl⟩ : syracuseStep 1254271 = 1881407) B1881407
theorem B2819051 : Blo 1252444 2819051 := bstep (se 1 (by rfl) ⟨2114288, by rfl⟩ : syracuseStep 2819051 = 4228577) B4228577
theorem B3171383 : Blo 1252444 3171383 := bstep (se 1 (by rfl) ⟨2378537, by rfl⟩ : syracuseStep 3171383 = 4757075) B4757075
theorem B4515047 : Blo 1252444 4515047 := bstep (se 1 (by rfl) ⟨3386285, by rfl⟩ : syracuseStep 4515047 = 6772571) B6772571
theorem B30508559 : Blo 1252444 30508559 := bstep (se 1 (by rfl) ⟨22881419, by rfl⟩ : syracuseStep 30508559 = 45762839) B45762839
theorem B3171919 : Blo 1252444 3171919 := bstep (se 1 (by rfl) ⟨2378939, by rfl⟩ : syracuseStep 3171919 = 4757879) B4757879
theorem B1410799 : Blo 1252444 1410799 := bstep (se 1 (by rfl) ⟨1058099, by rfl⟩ : syracuseStep 1410799 = 2116199) B2116199
theorem B5351179 : Blo 1252444 5351179 := bstep (se 1 (by rfl) ⟨4013384, by rfl⟩ : syracuseStep 5351179 = 8026769) B8026769
theorem B32122655 : Blo 1252444 32122655 := bstep (se 1 (by rfl) ⟨24091991, by rfl⟩ : syracuseStep 32122655 = 48183983) B48183983
theorem B7137071 : Blo 1252444 7137071 := bstep (se 1 (by rfl) ⟨5352803, by rfl⟩ : syracuseStep 7137071 = 10705607) B10705607
theorem B2819951 : Blo 1252444 2819951 := bstep (se 1 (by rfl) ⟨2114963, by rfl⟩ : syracuseStep 2819951 = 4229927) B4229927
theorem B9037727 : Blo 1252444 9037727 := bstep (se 1 (by rfl) ⟨6778295, by rfl⟩ : syracuseStep 9037727 = 13556591) B13556591
theorem B2820059 : Blo 1252444 2820059 := bstep (se 1 (by rfl) ⟨2115044, by rfl⟩ : syracuseStep 2820059 = 4230089) B4230089
theorem B6342623 : Blo 1252444 6342623 := bstep (se 1 (by rfl) ⟨4756967, by rfl⟩ : syracuseStep 6342623 = 9513935) B9513935
theorem B2820167 : Blo 1252444 2820167 := bstep (se 1 (by rfl) ⟨2115125, by rfl⟩ : syracuseStep 2820167 = 4230251) B4230251
theorem B2820239 : Blo 1252444 2820239 := bstep (se 1 (by rfl) ⟨2115179, by rfl⟩ : syracuseStep 2820239 = 4230359) B4230359
theorem B2820329 : Blo 1252444 2820329 := bstep (se 2 (by rfl) ⟨1057623, by rfl⟩ : syracuseStep 2820329 = 2115247) B2115247
theorem B2820347 : Blo 1252444 2820347 := bstep (se 1 (by rfl) ⟨2115260, by rfl⟩ : syracuseStep 2820347 = 4230521) B4230521
theorem B2115895 : Blo 1252444 2115895 := bstep (se 1 (by rfl) ⟨1586921, by rfl⟩ : syracuseStep 2115895 = 3173843) B3173843
theorem B3811711 : Blo 1252444 3811711 := bstep (se 1 (by rfl) ⟨2858783, by rfl⟩ : syracuseStep 3811711 = 5717567) B5717567
theorem B2820599 : Blo 1252444 2820599 := bstep (se 1 (by rfl) ⟨2115449, by rfl⟩ : syracuseStep 2820599 = 4230899) B4230899
theorem B2116361 : Blo 1252444 2116361 := bstep (se 2 (by rfl) ⟨793635, by rfl⟩ : syracuseStep 2116361 = 1587271) B1587271
theorem B1878953 : Blo 1252444 1878953 := bstep (se 2 (by rfl) ⟨704607, by rfl⟩ : syracuseStep 1878953 = 1409215) B1409215
theorem B1878983 : Blo 1252444 1878983 := bstep (se 1 (by rfl) ⟨1409237, by rfl⟩ : syracuseStep 1878983 = 2818475) B2818475
theorem B3173327 : Blo 1252444 3173327 := bstep (se 1 (by rfl) ⟨2379995, by rfl⟩ : syracuseStep 3173327 = 4759991) B4759991
theorem B3566587 : Blo 1252444 3566587 := bstep (se 1 (by rfl) ⟨2674940, by rfl⟩ : syracuseStep 3566587 = 5349881) B5349881
theorem B1879103 : Blo 1252444 1879103 := bstep (se 1 (by rfl) ⟨1409327, by rfl⟩ : syracuseStep 1879103 = 2818655) B2818655
theorem B1879343 : Blo 1252444 1879343 := bstep (se 1 (by rfl) ⟨1409507, by rfl⟩ : syracuseStep 1879343 = 2819015) B2819015
theorem B1879529 : Blo 1252444 1879529 := bstep (se 2 (by rfl) ⟨704823, by rfl⟩ : syracuseStep 1879529 = 1409647) B1409647
theorem B1879583 : Blo 1252444 1879583 := bstep (se 1 (by rfl) ⟨1409687, by rfl⟩ : syracuseStep 1879583 = 2819375) B2819375
theorem B1879673 : Blo 1252444 1879673 := bstep (se 2 (by rfl) ⟨704877, by rfl⟩ : syracuseStep 1879673 = 1409755) B1409755
theorem B8580809 : Blo 1252444 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B1879919 : Blo 1252444 1879919 := bstep (se 1 (by rfl) ⟨1409939, by rfl⟩ : syracuseStep 1879919 = 2819879) B2819879
theorem B1880171 : Blo 1252444 1880171 := bstep (se 1 (by rfl) ⟨1410128, by rfl⟩ : syracuseStep 1880171 = 2820257) B2820257
theorem B8147065 : Blo 1252444 8147065 := bstep (se 2 (by rfl) ⟨3055149, by rfl⟩ : syracuseStep 8147065 = 6110299) B6110299
theorem B12038615 : Blo 1252444 12038615 := bstep (se 1 (by rfl) ⟨9028961, by rfl⟩ : syracuseStep 12038615 = 18057923) B18057923
theorem B1880603 : Blo 1252444 1880603 := bstep (se 1 (by rfl) ⟨1410452, by rfl⟩ : syracuseStep 1880603 = 2820905) B2820905
theorem B2036411 : Blo 1252444 2036411 := bstep (se 1 (by rfl) ⟨1527308, by rfl⟩ : syracuseStep 2036411 = 3054617) B3054617
theorem B1880783 : Blo 1252444 1880783 := bstep (se 1 (by rfl) ⟨1410587, by rfl⟩ : syracuseStep 1880783 = 2821175) B2821175
theorem B13554479 : Blo 1252444 13554479 := bstep (se 1 (by rfl) ⟨10165859, by rfl⟩ : syracuseStep 13554479 = 20331719) B20331719
theorem B8024923 : Blo 1252444 8024923 := bstep (se 1 (by rfl) ⟨6018692, by rfl⟩ : syracuseStep 8024923 = 12037385) B12037385
theorem B21410729 : Blo 1252444 21410729 := bstep (se 2 (by rfl) ⟨8029023, by rfl⟩ : syracuseStep 21410729 = 16058047) B16058047
theorem B1881071 : Blo 1252444 1881071 := bstep (se 1 (by rfl) ⟨1410803, by rfl⟩ : syracuseStep 1881071 = 2821607) B2821607
theorem B6346025 : Blo 1252444 6346025 := bstep (se 2 (by rfl) ⟨2379759, by rfl⟩ : syracuseStep 6346025 = 4759519) B4759519
theorem B1881455 : Blo 1252444 1881455 := bstep (se 1 (by rfl) ⟨1411091, by rfl⟩ : syracuseStep 1881455 = 2822183) B2822183
theorem B8574407 : Blo 1252444 8574407 := bstep (se 1 (by rfl) ⟨6430805, by rfl⟩ : syracuseStep 8574407 = 12861611) B12861611
theorem B1881575 : Blo 1252444 1881575 := bstep (se 1 (by rfl) ⟨1411181, by rfl⟩ : syracuseStep 1881575 = 2822363) B2822363
theorem B6026825 : Blo 1252444 6026825 := bstep (se 2 (by rfl) ⟨2260059, by rfl⟩ : syracuseStep 6026825 = 4520119) B4520119
theorem B3389053 : Blo 1252444 3389053 := bstep (se 3 (by rfl) ⟨635447, by rfl⟩ : syracuseStep 3389053 = 1270895) B1270895
theorem B10172375 : Blo 1252444 10172375 := bstep (se 1 (by rfl) ⟨7629281, by rfl⟩ : syracuseStep 10172375 = 15258563) B15258563
theorem B6346835 : Blo 1252444 6346835 := bstep (se 1 (by rfl) ⟨4760126, by rfl⟩ : syracuseStep 6346835 = 9520253) B9520253
theorem B20617325 : Blo 1252444 20617325 := bstep (se 3 (by rfl) ⟨3865748, by rfl⟩ : syracuseStep 20617325 = 7731497) B7731497
theorem B1253371 : Blo 1252444 1253371 := bstep (se 1 (by rfl) ⟨940028, by rfl⟩ : syracuseStep 1253371 = 1880057) B1880057
theorem B7133447 : Blo 1252444 7133447 := bstep (se 1 (by rfl) ⟨5350085, by rfl⟩ : syracuseStep 7133447 = 10700171) B10700171
theorem B5355895 : Blo 1252444 5355895 := bstep (se 1 (by rfl) ⟨4016921, by rfl⟩ : syracuseStep 5355895 = 8033843) B8033843
theorem B3570119 : Blo 1252444 3570119 := bstep (se 1 (by rfl) ⟨2677589, by rfl⟩ : syracuseStep 3570119 = 5355179) B5355179
theorem B4012591 : Blo 1252444 4012591 := bstep (se 1 (by rfl) ⟨3009443, by rfl⟩ : syracuseStep 4012591 = 6018887) B6018887
theorem B11434547 : Blo 1252444 11434547 := bstep (se 1 (by rfl) ⟨8575910, by rfl⟩ : syracuseStep 11434547 = 17151821) B17151821
theorem B6347321 : Blo 1252444 6347321 := bstep (se 2 (by rfl) ⟨2380245, by rfl⟩ : syracuseStep 6347321 = 4760491) B4760491
theorem B10164851 : Blo 1252444 10164851 := bstep (se 1 (by rfl) ⟨7623638, by rfl⟩ : syracuseStep 10164851 = 15247277) B15247277
theorem B2857697 : Blo 1252444 2857697 := bstep (se 2 (by rfl) ⟨1071636, by rfl⟩ : syracuseStep 2857697 = 2143273) B2143273
theorem B4520939 : Blo 1252444 4520939 := bstep (se 1 (by rfl) ⟨3390704, by rfl⟩ : syracuseStep 4520939 = 6781409) B6781409
theorem B8576047 : Blo 1252444 8576047 := bstep (se 1 (by rfl) ⟨6432035, by rfl⟩ : syracuseStep 8576047 = 12864071) B12864071
theorem B3570779 : Blo 1252444 3570779 := bstep (se 1 (by rfl) ⟨2678084, by rfl⟩ : syracuseStep 3570779 = 5356169) B5356169
theorem B22863035 : Blo 1252444 22863035 := bstep (se 1 (by rfl) ⟨17147276, by rfl⟩ : syracuseStep 22863035 = 34294553) B34294553
theorem B7625971 : Blo 1252444 7625971 := bstep (se 1 (by rfl) ⟨5719478, by rfl⟩ : syracuseStep 7625971 = 11438957) B11438957
theorem B1252671 : Blo 1252444 1252671 := bstep (se 1 (by rfl) ⟨939503, by rfl⟩ : syracuseStep 1252671 = 1879007) B1879007
theorem B10706255 : Blo 1252444 10706255 := bstep (se 1 (by rfl) ⟨8029691, by rfl⟩ : syracuseStep 10706255 = 16059383) B16059383
theorem B7134587 : Blo 1252444 7134587 := bstep (se 1 (by rfl) ⟨5350940, by rfl⟩ : syracuseStep 7134587 = 10701881) B10701881
theorem B4013641 : Blo 1252444 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B1252967 : Blo 1252444 1252967 := bstep (se 1 (by rfl) ⟨939725, by rfl⟩ : syracuseStep 1252967 = 1879451) B1879451
theorem B6348455 : Blo 1252444 6348455 := bstep (se 1 (by rfl) ⟨4761341, by rfl⟩ : syracuseStep 6348455 = 9522683) B9522683
theorem B7135087 : Blo 1252444 7135087 := bstep (se 1 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 7135087 = 10702631) B10702631
theorem B3571577 : Blo 1252444 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B10715003 : Blo 1252444 10715003 := bstep (se 1 (by rfl) ⟨8036252, by rfl⟩ : syracuseStep 10715003 = 16072505) B16072505
theorem B1253247 : Blo 1252444 1253247 := bstep (se 1 (by rfl) ⟨939935, by rfl⟩ : syracuseStep 1253247 = 1879871) B1879871
theorem B2113607 : Blo 1252444 2113607 := bstep (se 1 (by rfl) ⟨1585205, by rfl⟩ : syracuseStep 2113607 = 3170411) B3170411
theorem B1253447 : Blo 1252444 1253447 := bstep (se 1 (by rfl) ⟨940085, by rfl⟩ : syracuseStep 1253447 = 1880171) B1880171
theorem B10862753 : Blo 1252444 10862753 := bstep (se 2 (by rfl) ⟨4073532, by rfl⟩ : syracuseStep 10862753 = 8147065) B8147065
theorem B4227335 : Blo 1252444 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B1253735 : Blo 1252444 1253735 := bstep (se 1 (by rfl) ⟨940301, by rfl⟩ : syracuseStep 1253735 = 1880603) B1880603
theorem B1253855 : Blo 1252444 1253855 := bstep (se 1 (by rfl) ⟨940391, by rfl⟩ : syracuseStep 1253855 = 1880783) B1880783
theorem B9036319 : Blo 1252444 9036319 := bstep (se 1 (by rfl) ⟨6777239, by rfl⟩ : syracuseStep 9036319 = 13554479) B13554479
theorem B10715753 : Blo 1252444 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B1254047 : Blo 1252444 1254047 := bstep (se 1 (by rfl) ⟨940535, by rfl⟩ : syracuseStep 1254047 = 1881071) B1881071
theorem B2114255 : Blo 1252444 2114255 := bstep (se 1 (by rfl) ⟨1585691, by rfl⟩ : syracuseStep 2114255 = 3171383) B3171383
theorem B5350121 : Blo 1252444 5350121 := bstep (se 2 (by rfl) ⟨2006295, by rfl⟩ : syracuseStep 5350121 = 4012591) B4012591
theorem B1254303 : Blo 1252444 1254303 := bstep (se 1 (by rfl) ⟨940727, by rfl⟩ : syracuseStep 1254303 = 1881455) B1881455
theorem B1254383 : Blo 1252444 1254383 := bstep (se 1 (by rfl) ⟨940787, by rfl⟩ : syracuseStep 1254383 = 1881575) B1881575
theorem B10699897 : Blo 1252444 10699897 := bstep (se 2 (by rfl) ⟨4012461, by rfl⟩ : syracuseStep 10699897 = 8024923) B8024923
theorem B21415103 : Blo 1252444 21415103 := bstep (se 1 (by rfl) ⟨16061327, by rfl⟩ : syracuseStep 21415103 = 32122655) B32122655
theorem B4228415 : Blo 1252444 4228415 := bstep (se 1 (by rfl) ⟨3171311, by rfl⟩ : syracuseStep 4228415 = 6342623) B6342623
theorem B30492125 : Blo 1252444 30492125 := bstep (se 3 (by rfl) ⟨5717273, by rfl⟩ : syracuseStep 30492125 = 11434547) B11434547
theorem B6776567 : Blo 1252444 6776567 := bstep (se 1 (by rfl) ⟨5082425, by rfl⟩ : syracuseStep 6776567 = 10164851) B10164851
theorem B1410907 : Blo 1252444 1410907 := bstep (se 1 (by rfl) ⟨1058180, by rfl⟩ : syracuseStep 1410907 = 2116361) B2116361
theorem B2115551 : Blo 1252444 2115551 := bstep (se 1 (by rfl) ⟨1586663, by rfl⟩ : syracuseStep 2115551 = 3173327) B3173327
theorem B5351521 : Blo 1252444 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B4229225 : Blo 1252444 4229225 := bstep (se 2 (by rfl) ⟨1585959, by rfl⟩ : syracuseStep 4229225 = 3171919) B3171919
theorem B7137503 : Blo 1252444 7137503 := bstep (se 1 (by rfl) ⟨5353127, by rfl⟩ : syracuseStep 7137503 = 10706255) B10706255
theorem B5720539 : Blo 1252444 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B9513449 : Blo 1252444 9513449 := bstep (se 2 (by rfl) ⟨3567543, by rfl⟩ : syracuseStep 9513449 = 7135087) B7135087
theorem B45738917 : Blo 1252444 45738917 := bstep (se 4 (by rfl) ⟨4288023, by rfl⟩ : syracuseStep 45738917 = 8576047) B8576047
theorem B2821193 : Blo 1252444 2821193 := bstep (se 2 (by rfl) ⟨1057947, by rfl⟩ : syracuseStep 2821193 = 2115895) B2115895
theorem B4582507 : Blo 1252444 4582507 := bstep (se 1 (by rfl) ⟨3436880, by rfl⟩ : syracuseStep 4582507 = 6873761) B6873761
theorem B5082281 : Blo 1252444 5082281 := bstep (se 2 (by rfl) ⟨1905855, by rfl⟩ : syracuseStep 5082281 = 3811711) B3811711
theorem B1879247 : Blo 1252444 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B14273819 : Blo 1252444 14273819 := bstep (se 1 (by rfl) ⟨10705364, by rfl⟩ : syracuseStep 14273819 = 21410729) B21410729
theorem B1879367 : Blo 1252444 1879367 := bstep (se 1 (by rfl) ⟨1409525, by rfl⟩ : syracuseStep 1879367 = 2819051) B2819051
theorem B3010031 : Blo 1252444 3010031 := bstep (se 1 (by rfl) ⟨2257523, by rfl⟩ : syracuseStep 3010031 = 4515047) B4515047
theorem B4230683 : Blo 1252444 4230683 := bstep (se 1 (by rfl) ⟨3173012, by rfl⟩ : syracuseStep 4230683 = 6346025) B6346025
theorem B1879817 : Blo 1252444 1879817 := bstep (se 2 (by rfl) ⟨704931, by rfl⟩ : syracuseStep 1879817 = 1409863) B1409863
theorem B1879967 : Blo 1252444 1879967 := bstep (se 1 (by rfl) ⟨1409975, by rfl⟩ : syracuseStep 1879967 = 2819951) B2819951
theorem B6025151 : Blo 1252444 6025151 := bstep (se 1 (by rfl) ⟨4518863, by rfl⟩ : syracuseStep 6025151 = 9037727) B9037727
theorem B1880039 : Blo 1252444 1880039 := bstep (se 1 (by rfl) ⟨1410029, by rfl⟩ : syracuseStep 1880039 = 2820059) B2820059
theorem B4755449 : Blo 1252444 4755449 := bstep (se 2 (by rfl) ⟨1783293, by rfl⟩ : syracuseStep 4755449 = 3566587) B3566587
theorem B1880111 : Blo 1252444 1880111 := bstep (se 1 (by rfl) ⟨1410083, by rfl⟩ : syracuseStep 1880111 = 2820167) B2820167
theorem B4231223 : Blo 1252444 4231223 := bstep (se 1 (by rfl) ⟨3173417, by rfl⟩ : syracuseStep 4231223 = 6346835) B6346835
theorem B1880159 : Blo 1252444 1880159 := bstep (se 1 (by rfl) ⟨1410119, by rfl⟩ : syracuseStep 1880159 = 2820239) B2820239
theorem B1880219 : Blo 1252444 1880219 := bstep (se 1 (by rfl) ⟨1410164, by rfl⟩ : syracuseStep 1880219 = 2820329) B2820329
theorem B1880231 : Blo 1252444 1880231 := bstep (se 1 (by rfl) ⟨1410173, by rfl⟩ : syracuseStep 1880231 = 2820347) B2820347
theorem B4755631 : Blo 1252444 4755631 := bstep (se 1 (by rfl) ⟨3566723, by rfl⟩ : syracuseStep 4755631 = 7133447) B7133447
theorem B2380079 : Blo 1252444 2380079 := bstep (se 1 (by rfl) ⟨1785059, by rfl⟩ : syracuseStep 2380079 = 3570119) B3570119
theorem B1880399 : Blo 1252444 1880399 := bstep (se 1 (by rfl) ⟨1410299, by rfl⟩ : syracuseStep 1880399 = 2820599) B2820599
theorem B4231547 : Blo 1252444 4231547 := bstep (se 1 (by rfl) ⟨3173660, by rfl⟩ : syracuseStep 4231547 = 6347321) B6347321
theorem B1905131 : Blo 1252444 1905131 := bstep (se 1 (by rfl) ⟨1428848, by rfl⟩ : syracuseStep 1905131 = 2857697) B2857697
theorem B2380519 : Blo 1252444 2380519 := bstep (se 1 (by rfl) ⟨1785389, by rfl⟩ : syracuseStep 2380519 = 3570779) B3570779
theorem B15242023 : Blo 1252444 15242023 := bstep (se 1 (by rfl) ⟨11431517, by rfl⟩ : syracuseStep 15242023 = 22863035) B22863035
theorem B4518737 : Blo 1252444 4518737 := bstep (se 2 (by rfl) ⟨1694526, by rfl⟩ : syracuseStep 4518737 = 3389053) B3389053
theorem B4756391 : Blo 1252444 4756391 := bstep (se 1 (by rfl) ⟨3567293, by rfl⟩ : syracuseStep 4756391 = 7134587) B7134587
theorem B1881065 : Blo 1252444 1881065 := bstep (se 2 (by rfl) ⟨705399, by rfl⟩ : syracuseStep 1881065 = 1410799) B1410799
theorem B4232303 : Blo 1252444 4232303 := bstep (se 1 (by rfl) ⟨3174227, by rfl⟩ : syracuseStep 4232303 = 6348455) B6348455
theorem B48223349 : Blo 1252444 48223349 := bstep (se 5 (by rfl) ⟨2260469, by rfl⟩ : syracuseStep 48223349 = 4520939) B4520939
theorem B2381051 : Blo 1252444 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B4822487 : Blo 1252444 4822487 := bstep (se 1 (by rfl) ⟨3616865, by rfl⟩ : syracuseStep 4822487 = 7233731) B7233731
theorem B15062537 : Blo 1252444 15062537 := bstep (se 2 (by rfl) ⟨5648451, by rfl⟩ : syracuseStep 15062537 = 11296903) B11296903
theorem B2856475 : Blo 1252444 2856475 := bstep (se 1 (by rfl) ⟨2142356, by rfl⟩ : syracuseStep 2856475 = 4284713) B4284713
theorem B8025743 : Blo 1252444 8025743 := bstep (se 1 (by rfl) ⟨6019307, by rfl⟩ : syracuseStep 8025743 = 12038615) B12038615
theorem B1357607 : Blo 1252444 1357607 := bstep (se 1 (by rfl) ⟨1018205, by rfl⟩ : syracuseStep 1357607 = 2036411) B2036411
theorem B7141193 : Blo 1252444 7141193 := bstep (se 2 (by rfl) ⟨2677947, by rfl⟩ : syracuseStep 7141193 = 5355895) B5355895
theorem B7231315 : Blo 1252444 7231315 := bstep (se 1 (by rfl) ⟨5423486, by rfl⟩ : syracuseStep 7231315 = 10846973) B10846973
theorem B5085019 : Blo 1252444 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B5716271 : Blo 1252444 5716271 := bstep (se 1 (by rfl) ⟨4287203, by rfl⟩ : syracuseStep 5716271 = 8574407) B8574407
theorem B20339039 : Blo 1252444 20339039 := bstep (se 1 (by rfl) ⟨15254279, by rfl⟩ : syracuseStep 20339039 = 30508559) B30508559
theorem B6609377 : Blo 1252444 6609377 := bstep (se 2 (by rfl) ⟨2478516, by rfl⟩ : syracuseStep 6609377 = 4957033) B4957033
theorem B4758047 : Blo 1252444 4758047 := bstep (se 1 (by rfl) ⟨3568535, by rfl⟩ : syracuseStep 4758047 = 7137071) B7137071
theorem B40671845 : Blo 1252444 40671845 := bstep (se 4 (by rfl) ⟨3812985, by rfl⟩ : syracuseStep 40671845 = 7625971) B7625971
theorem B6781583 : Blo 1252444 6781583 := bstep (se 1 (by rfl) ⟨5086187, by rfl⟩ : syracuseStep 6781583 = 10172375) B10172375
theorem B13744883 : Blo 1252444 13744883 := bstep (se 1 (by rfl) ⟨10308662, by rfl⟩ : syracuseStep 13744883 = 20617325) B20617325
theorem B16071533 : Blo 1252444 16071533 := bstep (se 3 (by rfl) ⟨3013412, by rfl⟩ : syracuseStep 16071533 = 6026825) B6026825
theorem B1252635 : Blo 1252444 1252635 := bstep (se 1 (by rfl) ⟨939476, by rfl⟩ : syracuseStep 1252635 = 1878953) B1878953
theorem B1252655 : Blo 1252444 1252655 := bstep (se 1 (by rfl) ⟨939491, by rfl⟩ : syracuseStep 1252655 = 1878983) B1878983
theorem B1252735 : Blo 1252444 1252735 := bstep (se 1 (by rfl) ⟨939551, by rfl⟩ : syracuseStep 1252735 = 1879103) B1879103
theorem B1252895 : Blo 1252444 1252895 := bstep (se 1 (by rfl) ⟨939671, by rfl⟩ : syracuseStep 1252895 = 1879343) B1879343
theorem B1253019 : Blo 1252444 1253019 := bstep (se 1 (by rfl) ⟨939764, by rfl⟩ : syracuseStep 1253019 = 1879529) B1879529
theorem B7134905 : Blo 1252444 7134905 := bstep (se 2 (by rfl) ⟨2675589, by rfl⟩ : syracuseStep 7134905 = 5351179) B5351179
theorem B1253055 : Blo 1252444 1253055 := bstep (se 1 (by rfl) ⟨939791, by rfl⟩ : syracuseStep 1253055 = 1879583) B1879583
theorem B1253115 : Blo 1252444 1253115 := bstep (se 1 (by rfl) ⟨939836, by rfl⟩ : syracuseStep 1253115 = 1879673) B1879673
theorem B1253279 : Blo 1252444 1253279 := bstep (se 1 (by rfl) ⟨939959, by rfl⟩ : syracuseStep 1253279 = 1879919) B1879919
theorem B7143335 : Blo 1252444 7143335 := bstep (se 1 (by rfl) ⟨5357501, by rfl⟩ : syracuseStep 7143335 = 10715003) B10715003
theorem B1253407 : Blo 1252444 1253407 := bstep (se 1 (by rfl) ⟨940055, by rfl⟩ : syracuseStep 1253407 = 1880111) B1880111
theorem B1409071 : Blo 1252444 1409071 := bstep (se 1 (by rfl) ⟨1056803, by rfl⟩ : syracuseStep 1409071 = 2113607) B2113607
theorem B1253439 : Blo 1252444 1253439 := bstep (se 1 (by rfl) ⟨940079, by rfl⟩ : syracuseStep 1253439 = 1880159) B1880159
theorem B1253479 : Blo 1252444 1253479 := bstep (se 1 (by rfl) ⟨940109, by rfl⟩ : syracuseStep 1253479 = 1880219) B1880219
theorem B1253487 : Blo 1252444 1253487 := bstep (se 1 (by rfl) ⟨940115, by rfl⟩ : syracuseStep 1253487 = 1880231) B1880231
theorem B7135361 : Blo 1252444 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B2818223 : Blo 1252444 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B1253599 : Blo 1252444 1253599 := bstep (se 1 (by rfl) ⟨940199, by rfl⟩ : syracuseStep 1253599 = 1880399) B1880399
theorem B6340841 : Blo 1252444 6340841 := bstep (se 2 (by rfl) ⟨2377815, by rfl⟩ : syracuseStep 6340841 = 4755631) B4755631
theorem B1270087 : Blo 1252444 1270087 := bstep (se 1 (by rfl) ⟨952565, by rfl⟩ : syracuseStep 1270087 = 1905131) B1905131
theorem B7143835 : Blo 1252444 7143835 := bstep (se 1 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 7143835 = 10715753) B10715753
theorem B1409503 : Blo 1252444 1409503 := bstep (se 1 (by rfl) ⟨1057127, by rfl⟩ : syracuseStep 1409503 = 2114255) B2114255
theorem B3170927 : Blo 1252444 3170927 := bstep (se 1 (by rfl) ⟨2378195, by rfl⟩ : syracuseStep 3170927 = 4756391) B4756391
theorem B7627385 : Blo 1252444 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B1254043 : Blo 1252444 1254043 := bstep (se 1 (by rfl) ⟨940532, by rfl⟩ : syracuseStep 1254043 = 1881065) B1881065
theorem B3170299 : Blo 1252444 3170299 := bstep (se 1 (by rfl) ⟨2377724, by rfl⟩ : syracuseStep 3170299 = 4755449) B4755449
theorem B2818943 : Blo 1252444 2818943 := bstep (se 1 (by rfl) ⟨2114207, by rfl⟩ : syracuseStep 2818943 = 4228415) B4228415
theorem B4760795 : Blo 1252444 4760795 := bstep (se 1 (by rfl) ⟨3570596, by rfl⟩ : syracuseStep 4760795 = 7141193) B7141193
theorem B1410367 : Blo 1252444 1410367 := bstep (se 1 (by rfl) ⟨1057775, by rfl⟩ : syracuseStep 1410367 = 2115551) B2115551
theorem B2819483 : Blo 1252444 2819483 := bstep (se 1 (by rfl) ⟨2114612, by rfl⟩ : syracuseStep 2819483 = 4229225) B4229225
theorem B13559359 : Blo 1252444 13559359 := bstep (se 1 (by rfl) ⟨10169519, by rfl⟩ : syracuseStep 13559359 = 20339039) B20339039
theorem B6342299 : Blo 1252444 6342299 := bstep (se 1 (by rfl) ⟨4756724, by rfl⟩ : syracuseStep 6342299 = 9513449) B9513449
theorem B115869365 : Blo 1252444 115869365 := bstep (se 5 (by rfl) ⟨5431376, by rfl⟩ : syracuseStep 115869365 = 10862753) B10862753
theorem B3172031 : Blo 1252444 3172031 := bstep (se 1 (by rfl) ⟨2379023, by rfl⟩ : syracuseStep 3172031 = 4758047) B4758047
theorem B30492611 : Blo 1252444 30492611 := bstep (se 1 (by rfl) ⟨22869458, by rfl⟩ : syracuseStep 30492611 = 45738917) B45738917
theorem B2820455 : Blo 1252444 2820455 := bstep (se 1 (by rfl) ⟨2115341, by rfl⟩ : syracuseStep 2820455 = 4230683) B4230683
theorem B16067069 : Blo 1252444 16067069 := bstep (se 3 (by rfl) ⟨3012575, by rfl⟩ : syracuseStep 16067069 = 6025151) B6025151
theorem B4762223 : Blo 1252444 4762223 := bstep (se 1 (by rfl) ⟨3571667, by rfl⟩ : syracuseStep 4762223 = 7143335) B7143335
theorem B2820815 : Blo 1252444 2820815 := bstep (se 1 (by rfl) ⟨2115611, by rfl⟩ : syracuseStep 2820815 = 4231223) B4231223
theorem B2821031 : Blo 1252444 2821031 := bstep (se 1 (by rfl) ⟨2115773, by rfl⟩ : syracuseStep 2821031 = 4231547) B4231547
theorem B3566747 : Blo 1252444 3566747 := bstep (se 1 (by rfl) ⟨2675060, by rfl⟩ : syracuseStep 3566747 = 5350121) B5350121
theorem B2821535 : Blo 1252444 2821535 := bstep (se 1 (by rfl) ⟨2116151, by rfl⟩ : syracuseStep 2821535 = 4232303) B4232303
theorem B32148899 : Blo 1252444 32148899 := bstep (se 1 (by rfl) ⟨24111674, by rfl⟩ : syracuseStep 32148899 = 48223349) B48223349
theorem B3174025 : Blo 1252444 3174025 := bstep (se 2 (by rfl) ⟨1190259, by rfl⟩ : syracuseStep 3174025 = 2380519) B2380519
theorem B3214991 : Blo 1252444 3214991 := bstep (se 1 (by rfl) ⟨2411243, by rfl⟩ : syracuseStep 3214991 = 4822487) B4822487
theorem B20328083 : Blo 1252444 20328083 := bstep (se 1 (by rfl) ⟨15246062, by rfl⟩ : syracuseStep 20328083 = 30492125) B30492125
theorem B4517711 : Blo 1252444 4517711 := bstep (se 1 (by rfl) ⟨3388283, by rfl⟩ : syracuseStep 4517711 = 6776567) B6776567
theorem B14266529 : Blo 1252444 14266529 := bstep (se 2 (by rfl) ⟨5349948, by rfl⟩ : syracuseStep 14266529 = 10699897) B10699897
theorem B21401981 : Blo 1252444 21401981 := bstep (se 3 (by rfl) ⟨4012871, by rfl⟩ : syracuseStep 21401981 = 8025743) B8025743
theorem B18084221 : Blo 1252444 18084221 := bstep (se 3 (by rfl) ⟨3390791, by rfl⟩ : syracuseStep 18084221 = 6781583) B6781583
theorem B9163255 : Blo 1252444 9163255 := bstep (se 1 (by rfl) ⟨6872441, by rfl⟩ : syracuseStep 9163255 = 13744883) B13744883
theorem B1880795 : Blo 1252444 1880795 := bstep (se 1 (by rfl) ⟨1410596, by rfl⟩ : syracuseStep 1880795 = 2821193) B2821193
theorem B3388187 : Blo 1252444 3388187 := bstep (se 1 (by rfl) ⟨2541140, by rfl⟩ : syracuseStep 3388187 = 5082281) B5082281
theorem B9515879 : Blo 1252444 9515879 := bstep (se 1 (by rfl) ⟨7136909, by rfl⟩ : syracuseStep 9515879 = 14273819) B14273819
theorem B1881209 : Blo 1252444 1881209 := bstep (se 2 (by rfl) ⟨705453, by rfl⟩ : syracuseStep 1881209 = 1410907) B1410907
theorem B6780025 : Blo 1252444 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B4756603 : Blo 1252444 4756603 := bstep (se 1 (by rfl) ⟨3567452, by rfl⟩ : syracuseStep 4756603 = 7134905) B7134905
theorem B1586719 : Blo 1252444 1586719 := bstep (se 1 (by rfl) ⟨1190039, by rfl⟩ : syracuseStep 1586719 = 2380079) B2380079
theorem B3012491 : Blo 1252444 3012491 := bstep (se 1 (by rfl) ⟨2259368, by rfl⟩ : syracuseStep 3012491 = 4518737) B4518737
theorem B12048425 : Blo 1252444 12048425 := bstep (se 2 (by rfl) ⟨4518159, by rfl⟩ : syracuseStep 12048425 = 9036319) B9036319
theorem B15243389 : Blo 1252444 15243389 := bstep (se 3 (by rfl) ⟨2858135, by rfl⟩ : syracuseStep 15243389 = 5716271) B5716271
theorem B14276735 : Blo 1252444 14276735 := bstep (se 1 (by rfl) ⟨10707551, by rfl⟩ : syracuseStep 14276735 = 21415103) B21415103
theorem B1587367 : Blo 1252444 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B10041691 : Blo 1252444 10041691 := bstep (se 1 (by rfl) ⟨7531268, by rfl⟩ : syracuseStep 10041691 = 15062537) B15062537
theorem B20322697 : Blo 1252444 20322697 := bstep (se 2 (by rfl) ⟨7621011, by rfl⟩ : syracuseStep 20322697 = 15242023) B15242023
theorem B6110009 : Blo 1252444 6110009 := bstep (se 2 (by rfl) ⟨2291253, by rfl⟩ : syracuseStep 6110009 = 4582507) B4582507
theorem B4758335 : Blo 1252444 4758335 := bstep (se 1 (by rfl) ⟨3568751, by rfl⟩ : syracuseStep 4758335 = 7137503) B7137503
theorem B4406251 : Blo 1252444 4406251 := bstep (se 1 (by rfl) ⟨3304688, by rfl⟩ : syracuseStep 4406251 = 6609377) B6609377
theorem B27114563 : Blo 1252444 27114563 := bstep (se 1 (by rfl) ⟨20335922, by rfl⟩ : syracuseStep 27114563 = 40671845) B40671845
theorem B10714355 : Blo 1252444 10714355 := bstep (se 1 (by rfl) ⟨8035766, by rfl⟩ : syracuseStep 10714355 = 16071533) B16071533
theorem B3808633 : Blo 1252444 3808633 := bstep (se 2 (by rfl) ⟨1428237, by rfl⟩ : syracuseStep 3808633 = 2856475) B2856475
theorem B3620285 : Blo 1252444 3620285 := bstep (se 3 (by rfl) ⟨678803, by rfl⟩ : syracuseStep 3620285 = 1357607) B1357607
theorem B1252831 : Blo 1252444 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B1252911 : Blo 1252444 1252911 := bstep (se 1 (by rfl) ⟨939683, by rfl⟩ : syracuseStep 1252911 = 1879367) B1879367
theorem B2006687 : Blo 1252444 2006687 := bstep (se 1 (by rfl) ⟨1505015, by rfl⟩ : syracuseStep 2006687 = 3010031) B3010031
theorem B9641753 : Blo 1252444 9641753 := bstep (se 2 (by rfl) ⟨3615657, by rfl⟩ : syracuseStep 9641753 = 7231315) B7231315
theorem B1253211 : Blo 1252444 1253211 := bstep (se 1 (by rfl) ⟨939908, by rfl⟩ : syracuseStep 1253211 = 1879817) B1879817
theorem B1253311 : Blo 1252444 1253311 := bstep (se 1 (by rfl) ⟨939983, by rfl⟩ : syracuseStep 1253311 = 1879967) B1879967
theorem B1253359 : Blo 1252444 1253359 := bstep (se 1 (by rfl) ⟨940019, by rfl⟩ : syracuseStep 1253359 = 1880039) B1880039
theorem B9511019 : Blo 1252444 9511019 := bstep (se 1 (by rfl) ⟨7133264, by rfl⟩ : syracuseStep 9511019 = 14266529) B14266529
theorem B4227227 : Blo 1252444 4227227 := bstep (se 1 (by rfl) ⟨3170420, by rfl⟩ : syracuseStep 4227227 = 6340841) B6340841
theorem B2113951 : Blo 1252444 2113951 := bstep (se 1 (by rfl) ⟨1585463, by rfl⟩ : syracuseStep 2113951 = 3170927) B3170927
theorem B1253863 : Blo 1252444 1253863 := bstep (se 1 (by rfl) ⟨940397, by rfl⟩ : syracuseStep 1253863 = 1880795) B1880795
theorem B1254139 : Blo 1252444 1254139 := bstep (se 1 (by rfl) ⟨940604, by rfl⟩ : syracuseStep 1254139 = 1881209) B1881209
theorem B4228199 : Blo 1252444 4228199 := bstep (se 1 (by rfl) ⟨3171149, by rfl⟩ : syracuseStep 4228199 = 6342299) B6342299
theorem B2114687 : Blo 1252444 2114687 := bstep (se 1 (by rfl) ⟨1586015, by rfl⟩ : syracuseStep 2114687 = 3172031) B3172031
theorem B2008327 : Blo 1252444 2008327 := bstep (se 1 (by rfl) ⟨1506245, by rfl⟩ : syracuseStep 2008327 = 3012491) B3012491
theorem B5875001 : Blo 1252444 5875001 := bstep (se 2 (by rfl) ⟨2203125, by rfl⟩ : syracuseStep 5875001 = 4406251) B4406251
theorem B6342137 : Blo 1252444 6342137 := bstep (se 2 (by rfl) ⟨2378301, by rfl⟩ : syracuseStep 6342137 = 4756603) B4756603
theorem B4073339 : Blo 1252444 4073339 := bstep (se 1 (by rfl) ⟨3055004, by rfl⟩ : syracuseStep 4073339 = 6110009) B6110009
theorem B3172223 : Blo 1252444 3172223 := bstep (se 1 (by rfl) ⟨2379167, by rfl⟩ : syracuseStep 3172223 = 4758335) B4758335
theorem B2115625 : Blo 1252444 2115625 := bstep (se 2 (by rfl) ⟨793359, by rfl⟩ : syracuseStep 2115625 = 1586719) B1586719
theorem B2377831 : Blo 1252444 2377831 := bstep (se 1 (by rfl) ⟨1783373, by rfl⟩ : syracuseStep 2377831 = 3566747) B3566747
theorem B21432599 : Blo 1252444 21432599 := bstep (se 1 (by rfl) ⟨16074449, by rfl⟩ : syracuseStep 21432599 = 32148899) B32148899
theorem B13552055 : Blo 1252444 13552055 := bstep (se 1 (by rfl) ⟨10164041, by rfl⟩ : syracuseStep 13552055 = 20328083) B20328083
theorem B1337791 : Blo 1252444 1337791 := bstep (se 1 (by rfl) ⟨1003343, by rfl⟩ : syracuseStep 1337791 = 2006687) B2006687
theorem B1878761 : Blo 1252444 1878761 := bstep (se 2 (by rfl) ⟨704535, by rfl⟩ : syracuseStep 1878761 = 1409071) B1409071
theorem B1878815 : Blo 1252444 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B2116489 : Blo 1252444 2116489 := bstep (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) B1587367
theorem B13388921 : Blo 1252444 13388921 := bstep (se 2 (by rfl) ⟨5020845, by rfl⟩ : syracuseStep 13388921 = 10041691) B10041691
theorem B6343919 : Blo 1252444 6343919 := bstep (se 1 (by rfl) ⟨4757939, by rfl⟩ : syracuseStep 6343919 = 9515879) B9515879
theorem B1879295 : Blo 1252444 1879295 := bstep (se 1 (by rfl) ⟨1409471, by rfl⟩ : syracuseStep 1879295 = 2818943) B2818943
theorem B1879337 : Blo 1252444 1879337 := bstep (se 2 (by rfl) ⟨704751, by rfl⟩ : syracuseStep 1879337 = 1409503) B1409503
theorem B12217673 : Blo 1252444 12217673 := bstep (se 2 (by rfl) ⟨4581627, by rfl⟩ : syracuseStep 12217673 = 9163255) B9163255
theorem B3173863 : Blo 1252444 3173863 := bstep (se 1 (by rfl) ⟨2380397, by rfl⟩ : syracuseStep 3173863 = 4760795) B4760795
theorem B1879655 : Blo 1252444 1879655 := bstep (se 1 (by rfl) ⟨1409741, by rfl⟩ : syracuseStep 1879655 = 2819483) B2819483
theorem B77246243 : Blo 1252444 77246243 := bstep (se 1 (by rfl) ⟨57934682, by rfl⟩ : syracuseStep 77246243 = 115869365) B115869365
theorem B20328407 : Blo 1252444 20328407 := bstep (se 1 (by rfl) ⟨15246305, by rfl⟩ : syracuseStep 20328407 = 30492611) B30492611
theorem B8032283 : Blo 1252444 8032283 := bstep (se 1 (by rfl) ⟨6024212, by rfl⟩ : syracuseStep 8032283 = 12048425) B12048425
theorem B10162259 : Blo 1252444 10162259 := bstep (se 1 (by rfl) ⟨7621694, by rfl⟩ : syracuseStep 10162259 = 15243389) B15243389
theorem B9040033 : Blo 1252444 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B1880303 : Blo 1252444 1880303 := bstep (se 1 (by rfl) ⟨1410227, by rfl⟩ : syracuseStep 1880303 = 2820455) B2820455
theorem B10711379 : Blo 1252444 10711379 := bstep (se 1 (by rfl) ⟨8033534, by rfl⟩ : syracuseStep 10711379 = 16067069) B16067069
theorem B8573309 : Blo 1252444 8573309 := bstep (se 3 (by rfl) ⟨1607495, by rfl⟩ : syracuseStep 8573309 = 3214991) B3214991
theorem B3174815 : Blo 1252444 3174815 := bstep (se 1 (by rfl) ⟨2381111, by rfl⟩ : syracuseStep 3174815 = 4762223) B4762223
theorem B1880489 : Blo 1252444 1880489 := bstep (se 2 (by rfl) ⟨705183, by rfl⟩ : syracuseStep 1880489 = 1410367) B1410367
theorem B1880543 : Blo 1252444 1880543 := bstep (se 1 (by rfl) ⟨1410407, by rfl⟩ : syracuseStep 1880543 = 2820815) B2820815
theorem B1880687 : Blo 1252444 1880687 := bstep (se 1 (by rfl) ⟨1410515, by rfl⟩ : syracuseStep 1880687 = 2821031) B2821031
theorem B18076375 : Blo 1252444 18076375 := bstep (se 1 (by rfl) ⟨13557281, by rfl⟩ : syracuseStep 18076375 = 27114563) B27114563
theorem B4232033 : Blo 1252444 4232033 := bstep (se 2 (by rfl) ⟨1587012, by rfl⟩ : syracuseStep 4232033 = 3174025) B3174025
theorem B1881023 : Blo 1252444 1881023 := bstep (se 1 (by rfl) ⟨1410767, by rfl⟩ : syracuseStep 1881023 = 2821535) B2821535
theorem B2413523 : Blo 1252444 2413523 := bstep (se 1 (by rfl) ⟨1810142, by rfl⟩ : syracuseStep 2413523 = 3620285) B3620285
theorem B6427835 : Blo 1252444 6427835 := bstep (se 1 (by rfl) ⟨4820876, by rfl⟩ : syracuseStep 6427835 = 9641753) B9641753
theorem B3011807 : Blo 1252444 3011807 := bstep (se 1 (by rfl) ⟨2258855, by rfl⟩ : syracuseStep 3011807 = 4517711) B4517711
theorem B4756907 : Blo 1252444 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B14267987 : Blo 1252444 14267987 := bstep (se 1 (by rfl) ⟨10700990, by rfl⟩ : syracuseStep 14267987 = 21401981) B21401981
theorem B12056147 : Blo 1252444 12056147 := bstep (se 1 (by rfl) ⟨9042110, by rfl⟩ : syracuseStep 12056147 = 18084221) B18084221
theorem B27096929 : Blo 1252444 27096929 := bstep (se 2 (by rfl) ⟨10161348, by rfl⟩ : syracuseStep 27096929 = 20322697) B20322697
theorem B9525113 : Blo 1252444 9525113 := bstep (se 2 (by rfl) ⟨3571917, by rfl⟩ : syracuseStep 9525113 = 7143835) B7143835
theorem B9517823 : Blo 1252444 9517823 := bstep (se 1 (by rfl) ⟨7138367, by rfl⟩ : syracuseStep 9517823 = 14276735) B14276735
theorem B20339693 : Blo 1252444 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B6773797 : Blo 1252444 6773797 := bstep (se 4 (by rfl) ⟨635043, by rfl⟩ : syracuseStep 6773797 = 1270087) B1270087
theorem B5078177 : Blo 1252444 5078177 := bstep (se 2 (by rfl) ⟨1904316, by rfl⟩ : syracuseStep 5078177 = 3808633) B3808633
theorem B9035165 : Blo 1252444 9035165 := bstep (se 3 (by rfl) ⟨1694093, by rfl⟩ : syracuseStep 9035165 = 3388187) B3388187
theorem B18079145 : Blo 1252444 18079145 := bstep (se 2 (by rfl) ⟨6779679, by rfl⟩ : syracuseStep 18079145 = 13559359) B13559359
theorem B7142903 : Blo 1252444 7142903 := bstep (se 1 (by rfl) ⟨5357177, by rfl⟩ : syracuseStep 7142903 = 10714355) B10714355
theorem B4227065 : Blo 1252444 4227065 := bstep (se 2 (by rfl) ⟨1585149, by rfl⟩ : syracuseStep 4227065 = 3170299) B3170299
theorem B6774839 : Blo 1252444 6774839 := bstep (se 1 (by rfl) ⟨5081129, by rfl⟩ : syracuseStep 6774839 = 10162259) B10162259
theorem B6340679 : Blo 1252444 6340679 := bstep (se 1 (by rfl) ⟨4755509, by rfl⟩ : syracuseStep 6340679 = 9511019) B9511019
theorem B2818151 : Blo 1252444 2818151 := bstep (se 1 (by rfl) ⟨2113613, by rfl⟩ : syracuseStep 2818151 = 4227227) B4227227
theorem B3170441 : Blo 1252444 3170441 := bstep (se 2 (by rfl) ⟨1188915, by rfl⟩ : syracuseStep 3170441 = 2377831) B2377831
theorem B1253535 : Blo 1252444 1253535 := bstep (se 1 (by rfl) ⟨940151, by rfl⟩ : syracuseStep 1253535 = 1880303) B1880303
theorem B36126917 : Blo 1252444 36126917 := bstep (se 4 (by rfl) ⟨3386898, by rfl⟩ : syracuseStep 36126917 = 6773797) B6773797
theorem B1253659 : Blo 1252444 1253659 := bstep (se 1 (by rfl) ⟨940244, by rfl⟩ : syracuseStep 1253659 = 1880489) B1880489
theorem B1253695 : Blo 1252444 1253695 := bstep (se 1 (by rfl) ⟨940271, by rfl⟩ : syracuseStep 1253695 = 1880543) B1880543
theorem B1253791 : Blo 1252444 1253791 := bstep (se 1 (by rfl) ⟨940343, by rfl⟩ : syracuseStep 1253791 = 1880687) B1880687
theorem B2818601 : Blo 1252444 2818601 := bstep (se 2 (by rfl) ⟨1056975, by rfl⟩ : syracuseStep 2818601 = 2113951) B2113951
theorem B1254015 : Blo 1252444 1254015 := bstep (se 1 (by rfl) ⟨940511, by rfl⟩ : syracuseStep 1254015 = 1881023) B1881023
theorem B2818799 : Blo 1252444 2818799 := bstep (se 1 (by rfl) ⟨2114099, by rfl⟩ : syracuseStep 2818799 = 4228199) B4228199
theorem B1409791 : Blo 1252444 1409791 := bstep (se 1 (by rfl) ⟨1057343, by rfl⟩ : syracuseStep 1409791 = 2114687) B2114687
theorem B4285223 : Blo 1252444 4285223 := bstep (se 1 (by rfl) ⟨3213917, by rfl⟩ : syracuseStep 4285223 = 6427835) B6427835
theorem B2007871 : Blo 1252444 2007871 := bstep (se 1 (by rfl) ⟨1505903, by rfl⟩ : syracuseStep 2007871 = 3011807) B3011807
theorem B32580461 : Blo 1252444 32580461 := bstep (se 3 (by rfl) ⟨6108836, by rfl⟩ : syracuseStep 32580461 = 12217673) B12217673
theorem B3916667 : Blo 1252444 3916667 := bstep (se 1 (by rfl) ⟨2937500, by rfl⟩ : syracuseStep 3916667 = 5875001) B5875001
theorem B3171271 : Blo 1252444 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B24101833 : Blo 1252444 24101833 := bstep (se 2 (by rfl) ⟨9038187, by rfl⟩ : syracuseStep 24101833 = 18076375) B18076375
theorem B4228091 : Blo 1252444 4228091 := bstep (se 1 (by rfl) ⟨3171068, by rfl⟩ : syracuseStep 4228091 = 6342137) B6342137
theorem B9511991 : Blo 1252444 9511991 := bstep (se 1 (by rfl) ⟨7133993, by rfl⟩ : syracuseStep 9511991 = 14267987) B14267987
theorem B8037431 : Blo 1252444 8037431 := bstep (se 1 (by rfl) ⟨6028073, by rfl⟩ : syracuseStep 8037431 = 12056147) B12056147
theorem B18064619 : Blo 1252444 18064619 := bstep (se 1 (by rfl) ⟨13548464, by rfl⟩ : syracuseStep 18064619 = 27096929) B27096929
theorem B6350075 : Blo 1252444 6350075 := bstep (se 1 (by rfl) ⟨4762556, by rfl⟩ : syracuseStep 6350075 = 9525113) B9525113
theorem B2114815 : Blo 1252444 2114815 := bstep (se 1 (by rfl) ⟨1586111, by rfl⟩ : syracuseStep 2114815 = 3172223) B3172223
theorem B14288399 : Blo 1252444 14288399 := bstep (se 1 (by rfl) ⟨10716299, by rfl⟩ : syracuseStep 14288399 = 21432599) B21432599
theorem B13559795 : Blo 1252444 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B3385451 : Blo 1252444 3385451 := bstep (se 1 (by rfl) ⟨2539088, by rfl⟩ : syracuseStep 3385451 = 5078177) B5078177
theorem B4229279 : Blo 1252444 4229279 := bstep (se 1 (by rfl) ⟨3171959, by rfl⟩ : syracuseStep 4229279 = 6343919) B6343919
theorem B6023443 : Blo 1252444 6023443 := bstep (se 1 (by rfl) ⟨4517582, by rfl⟩ : syracuseStep 6023443 = 9035165) B9035165
theorem B12052763 : Blo 1252444 12052763 := bstep (se 1 (by rfl) ⟨9039572, by rfl⟩ : syracuseStep 12052763 = 18079145) B18079145
theorem B4761935 : Blo 1252444 4761935 := bstep (se 1 (by rfl) ⟨3571451, by rfl⟩ : syracuseStep 4761935 = 7142903) B7142903
theorem B51497495 : Blo 1252444 51497495 := bstep (se 1 (by rfl) ⟨38623121, by rfl⟩ : syracuseStep 51497495 = 77246243) B77246243
theorem B13552271 : Blo 1252444 13552271 := bstep (se 1 (by rfl) ⟨10164203, by rfl⟩ : syracuseStep 13552271 = 20328407) B20328407
theorem B2820833 : Blo 1252444 2820833 := bstep (se 2 (by rfl) ⟨1057812, by rfl⟩ : syracuseStep 2820833 = 2115625) B2115625
theorem B12053377 : Blo 1252444 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B2116543 : Blo 1252444 2116543 := bstep (se 1 (by rfl) ⟨1587407, by rfl⟩ : syracuseStep 2116543 = 3174815) B3174815
theorem B2821355 : Blo 1252444 2821355 := bstep (se 1 (by rfl) ⟨2116016, by rfl⟩ : syracuseStep 2821355 = 4232033) B4232033
theorem B2821985 : Blo 1252444 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B6345215 : Blo 1252444 6345215 := bstep (se 1 (by rfl) ⟨4758911, by rfl⟩ : syracuseStep 6345215 = 9517823) B9517823
theorem B4231817 : Blo 1252444 4231817 := bstep (se 2 (by rfl) ⟨1586931, by rfl⟩ : syracuseStep 4231817 = 3173863) B3173863
theorem B8925947 : Blo 1252444 8925947 := bstep (se 1 (by rfl) ⟨6694460, by rfl⟩ : syracuseStep 8925947 = 13388921) B13388921
theorem B6436061 : Blo 1252444 6436061 := bstep (se 3 (by rfl) ⟨1206761, by rfl⟩ : syracuseStep 6436061 = 2413523) B2413523
theorem B5354855 : Blo 1252444 5354855 := bstep (se 1 (by rfl) ⟨4016141, by rfl⟩ : syracuseStep 5354855 = 8032283) B8032283
theorem B7140919 : Blo 1252444 7140919 := bstep (se 1 (by rfl) ⟨5355689, by rfl⟩ : syracuseStep 7140919 = 10711379) B10711379
theorem B5715539 : Blo 1252444 5715539 := bstep (se 1 (by rfl) ⟨4286654, by rfl⟩ : syracuseStep 5715539 = 8573309) B8573309
theorem B1783721 : Blo 1252444 1783721 := bstep (se 2 (by rfl) ⟨668895, by rfl⟩ : syracuseStep 1783721 = 1337791) B1337791
theorem B9034703 : Blo 1252444 9034703 := bstep (se 1 (by rfl) ⟨6776027, by rfl⟩ : syracuseStep 9034703 = 13552055) B13552055
theorem B2677769 : Blo 1252444 2677769 := bstep (se 2 (by rfl) ⟨1004163, by rfl⟩ : syracuseStep 2677769 = 2008327) B2008327
theorem B1252507 : Blo 1252444 1252507 := bstep (se 1 (by rfl) ⟨939380, by rfl⟩ : syracuseStep 1252507 = 1878761) B1878761
theorem B1252543 : Blo 1252444 1252543 := bstep (se 1 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 1252543 = 1878815) B1878815
theorem B1252863 : Blo 1252444 1252863 := bstep (se 1 (by rfl) ⟨939647, by rfl⟩ : syracuseStep 1252863 = 1879295) B1879295
theorem B1252891 : Blo 1252444 1252891 := bstep (se 1 (by rfl) ⟨939668, by rfl⟩ : syracuseStep 1252891 = 1879337) B1879337
theorem B10862237 : Blo 1252444 10862237 := bstep (se 3 (by rfl) ⟨2036669, by rfl⟩ : syracuseStep 10862237 = 4073339) B4073339
theorem B1253103 : Blo 1252444 1253103 := bstep (se 1 (by rfl) ⟨939827, by rfl⟩ : syracuseStep 1253103 = 1879655) B1879655
theorem B2818043 : Blo 1252444 2818043 := bstep (se 1 (by rfl) ⟨2113532, by rfl⟩ : syracuseStep 2818043 = 4227065) B4227065
theorem B4227119 : Blo 1252444 4227119 := bstep (se 1 (by rfl) ⟨3170339, by rfl⟩ : syracuseStep 4227119 = 6340679) B6340679
theorem B2113627 : Blo 1252444 2113627 := bstep (se 1 (by rfl) ⟨1585220, by rfl⟩ : syracuseStep 2113627 = 3170441) B3170441
theorem B24084611 : Blo 1252444 24084611 := bstep (se 1 (by rfl) ⟨18063458, by rfl⟩ : syracuseStep 24084611 = 36126917) B36126917
theorem B2818727 : Blo 1252444 2818727 := bstep (se 1 (by rfl) ⟨2114045, by rfl⟩ : syracuseStep 2818727 = 4228091) B4228091
theorem B6341327 : Blo 1252444 6341327 := bstep (se 1 (by rfl) ⟨4755995, by rfl⟩ : syracuseStep 6341327 = 9511991) B9511991
theorem B5358287 : Blo 1252444 5358287 := bstep (se 1 (by rfl) ⟨4018715, by rfl⟩ : syracuseStep 5358287 = 8037431) B8037431
theorem B12043079 : Blo 1252444 12043079 := bstep (se 1 (by rfl) ⟨9032309, by rfl⟩ : syracuseStep 12043079 = 18064619) B18064619
theorem B3810359 : Blo 1252444 3810359 := bstep (se 1 (by rfl) ⟨2857769, by rfl⟩ : syracuseStep 3810359 = 5715539) B5715539
theorem B4228361 : Blo 1252444 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B2819519 : Blo 1252444 2819519 := bstep (se 1 (by rfl) ⟨2114639, by rfl⟩ : syracuseStep 2819519 = 4229279) B4229279
theorem B10708645 : Blo 1252444 10708645 := bstep (se 4 (by rfl) ⟨1003935, by rfl⟩ : syracuseStep 10708645 = 2007871) B2007871
theorem B2819753 : Blo 1252444 2819753 := bstep (se 2 (by rfl) ⟨1057407, by rfl⟩ : syracuseStep 2819753 = 2114815) B2114815
theorem B6023135 : Blo 1252444 6023135 := bstep (se 1 (by rfl) ⟨4517351, by rfl⟩ : syracuseStep 6023135 = 9034703) B9034703
theorem B9521225 : Blo 1252444 9521225 := bstep (se 2 (by rfl) ⟨3570459, by rfl⟩ : syracuseStep 9521225 = 7140919) B7140919
theorem B1878695 : Blo 1252444 1878695 := bstep (se 1 (by rfl) ⟨1409021, by rfl⟩ : syracuseStep 1878695 = 2818043) B2818043
theorem B4516559 : Blo 1252444 4516559 := bstep (se 1 (by rfl) ⟨3387419, by rfl⟩ : syracuseStep 4516559 = 6774839) B6774839
theorem B1878767 : Blo 1252444 1878767 := bstep (se 1 (by rfl) ⟨1409075, by rfl⟩ : syracuseStep 1878767 = 2818151) B2818151
theorem B4230143 : Blo 1252444 4230143 := bstep (se 1 (by rfl) ⟨3172607, by rfl⟩ : syracuseStep 4230143 = 6345215) B6345215
theorem B8031257 : Blo 1252444 8031257 := bstep (se 2 (by rfl) ⟨3011721, by rfl⟩ : syracuseStep 8031257 = 6023443) B6023443
theorem B1879067 : Blo 1252444 1879067 := bstep (se 1 (by rfl) ⟨1409300, by rfl⟩ : syracuseStep 1879067 = 2818601) B2818601
theorem B2821211 : Blo 1252444 2821211 := bstep (se 1 (by rfl) ⟨2115908, by rfl⟩ : syracuseStep 2821211 = 4231817) B4231817
theorem B1879199 : Blo 1252444 1879199 := bstep (se 1 (by rfl) ⟨1409399, by rfl⟩ : syracuseStep 1879199 = 2818799) B2818799
theorem B5950631 : Blo 1252444 5950631 := bstep (se 1 (by rfl) ⟨4462973, by rfl⟩ : syracuseStep 5950631 = 8925947) B8925947
theorem B21720307 : Blo 1252444 21720307 := bstep (se 1 (by rfl) ⟨16290230, by rfl⟩ : syracuseStep 21720307 = 32580461) B32580461
theorem B1879721 : Blo 1252444 1879721 := bstep (se 2 (by rfl) ⟨704895, by rfl⟩ : syracuseStep 1879721 = 1409791) B1409791
theorem B2822057 : Blo 1252444 2822057 := bstep (se 2 (by rfl) ⟨1058271, by rfl⟩ : syracuseStep 2822057 = 2116543) B2116543
theorem B9039863 : Blo 1252444 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B2256967 : Blo 1252444 2256967 := bstep (se 1 (by rfl) ⟨1692725, by rfl⟩ : syracuseStep 2256967 = 3385451) B3385451
theorem B3174623 : Blo 1252444 3174623 := bstep (se 1 (by rfl) ⟨2380967, by rfl⟩ : syracuseStep 3174623 = 4761935) B4761935
theorem B1880555 : Blo 1252444 1880555 := bstep (se 1 (by rfl) ⟨1410416, by rfl⟩ : syracuseStep 1880555 = 2820833) B2820833
theorem B1880903 : Blo 1252444 1880903 := bstep (se 1 (by rfl) ⟨1410677, by rfl⟩ : syracuseStep 1880903 = 2821355) B2821355
theorem B4756589 : Blo 1252444 4756589 := bstep (se 3 (by rfl) ⟨891860, by rfl⟩ : syracuseStep 4756589 = 1783721) B1783721
theorem B1881323 : Blo 1252444 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B2856815 : Blo 1252444 2856815 := bstep (se 1 (by rfl) ⟨2142611, by rfl⟩ : syracuseStep 2856815 = 4285223) B4285223
theorem B2611111 : Blo 1252444 2611111 := bstep (se 1 (by rfl) ⟨1958333, by rfl⟩ : syracuseStep 2611111 = 3916667) B3916667
theorem B4290707 : Blo 1252444 4290707 := bstep (se 1 (by rfl) ⟨3218030, by rfl⟩ : syracuseStep 4290707 = 6436061) B6436061
theorem B4233383 : Blo 1252444 4233383 := bstep (se 1 (by rfl) ⟨3175037, by rfl⟩ : syracuseStep 4233383 = 6350075) B6350075
theorem B3569903 : Blo 1252444 3569903 := bstep (se 1 (by rfl) ⟨2677427, by rfl⟩ : syracuseStep 3569903 = 5354855) B5354855
theorem B9525599 : Blo 1252444 9525599 := bstep (se 1 (by rfl) ⟨7144199, by rfl⟩ : syracuseStep 9525599 = 14288399) B14288399
theorem B16071169 : Blo 1252444 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B32135777 : Blo 1252444 32135777 := bstep (se 2 (by rfl) ⟨12050916, by rfl⟩ : syracuseStep 32135777 = 24101833) B24101833
theorem B8035175 : Blo 1252444 8035175 := bstep (se 1 (by rfl) ⟨6026381, by rfl⟩ : syracuseStep 8035175 = 12052763) B12052763
theorem B34331663 : Blo 1252444 34331663 := bstep (se 1 (by rfl) ⟨25748747, by rfl⟩ : syracuseStep 34331663 = 51497495) B51497495
theorem B9034847 : Blo 1252444 9034847 := bstep (se 1 (by rfl) ⟨6776135, by rfl⟩ : syracuseStep 9034847 = 13552271) B13552271
theorem B1785179 : Blo 1252444 1785179 := bstep (se 1 (by rfl) ⟨1338884, by rfl⟩ : syracuseStep 1785179 = 2677769) B2677769
theorem B7241491 : Blo 1252444 7241491 := bstep (se 1 (by rfl) ⟨5431118, by rfl⟩ : syracuseStep 7241491 = 10862237) B10862237
theorem B2818079 : Blo 1252444 2818079 := bstep (se 1 (by rfl) ⟨2113559, by rfl⟩ : syracuseStep 2818079 = 4227119) B4227119
theorem B16056407 : Blo 1252444 16056407 := bstep (se 1 (by rfl) ⟨12042305, by rfl⟩ : syracuseStep 16056407 = 24084611) B24084611
theorem B2818169 : Blo 1252444 2818169 := bstep (se 2 (by rfl) ⟨1056813, by rfl⟩ : syracuseStep 2818169 = 2113627) B2113627
theorem B1253703 : Blo 1252444 1253703 := bstep (se 1 (by rfl) ⟨940277, by rfl⟩ : syracuseStep 1253703 = 1880555) B1880555
theorem B15868349 : Blo 1252444 15868349 := bstep (se 3 (by rfl) ⟨2975315, by rfl⟩ : syracuseStep 15868349 = 5950631) B5950631
theorem B4227551 : Blo 1252444 4227551 := bstep (se 1 (by rfl) ⟨3170663, by rfl⟩ : syracuseStep 4227551 = 6341327) B6341327
theorem B3572191 : Blo 1252444 3572191 := bstep (se 1 (by rfl) ⟨2679143, by rfl⟩ : syracuseStep 3572191 = 5358287) B5358287
theorem B8028719 : Blo 1252444 8028719 := bstep (se 1 (by rfl) ⟨6021539, by rfl⟩ : syracuseStep 8028719 = 12043079) B12043079
theorem B1253935 : Blo 1252444 1253935 := bstep (se 1 (by rfl) ⟨940451, by rfl⟩ : syracuseStep 1253935 = 1880903) B1880903
theorem B3171059 : Blo 1252444 3171059 := bstep (se 1 (by rfl) ⟨2378294, by rfl⟩ : syracuseStep 3171059 = 4756589) B4756589
theorem B1254215 : Blo 1252444 1254215 := bstep (se 1 (by rfl) ⟨940661, by rfl⟩ : syracuseStep 1254215 = 1881323) B1881323
theorem B2818907 : Blo 1252444 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B4760477 : Blo 1252444 4760477 := bstep (se 3 (by rfl) ⟨892589, by rfl⟩ : syracuseStep 4760477 = 1785179) B1785179
theorem B4015423 : Blo 1252444 4015423 := bstep (se 1 (by rfl) ⟨3011567, by rfl⟩ : syracuseStep 4015423 = 6023135) B6023135
theorem B2860471 : Blo 1252444 2860471 := bstep (se 1 (by rfl) ⟨2145353, by rfl⟩ : syracuseStep 2860471 = 4290707) B4290707
theorem B6350399 : Blo 1252444 6350399 := bstep (se 1 (by rfl) ⟨4762799, by rfl⟩ : syracuseStep 6350399 = 9525599) B9525599
theorem B28960409 : Blo 1252444 28960409 := bstep (se 2 (by rfl) ⟨10860153, by rfl⟩ : syracuseStep 28960409 = 21720307) B21720307
theorem B21423851 : Blo 1252444 21423851 := bstep (se 1 (by rfl) ⟨16067888, by rfl⟩ : syracuseStep 21423851 = 32135777) B32135777
theorem B2820095 : Blo 1252444 2820095 := bstep (se 1 (by rfl) ⟨2115071, by rfl⟩ : syracuseStep 2820095 = 4230143) B4230143
theorem B6023231 : Blo 1252444 6023231 := bstep (se 1 (by rfl) ⟨4517423, by rfl⟩ : syracuseStep 6023231 = 9034847) B9034847
theorem B10160957 : Blo 1252444 10160957 := bstep (se 3 (by rfl) ⟨1905179, by rfl⟩ : syracuseStep 10160957 = 3810359) B3810359
theorem B2116415 : Blo 1252444 2116415 := bstep (se 1 (by rfl) ⟨1587311, by rfl⟩ : syracuseStep 2116415 = 3174623) B3174623
theorem B12037157 : Blo 1252444 12037157 := bstep (se 4 (by rfl) ⟨1128483, by rfl⟩ : syracuseStep 12037157 = 2256967) B2256967
theorem B1879151 : Blo 1252444 1879151 := bstep (se 1 (by rfl) ⟨1409363, by rfl⟩ : syracuseStep 1879151 = 2818727) B2818727
theorem B1879679 : Blo 1252444 1879679 := bstep (se 1 (by rfl) ⟨1409759, by rfl⟩ : syracuseStep 1879679 = 2819519) B2819519
theorem B1879835 : Blo 1252444 1879835 := bstep (se 1 (by rfl) ⟨1409876, by rfl⟩ : syracuseStep 1879835 = 2819753) B2819753
theorem B1904543 : Blo 1252444 1904543 := bstep (se 1 (by rfl) ⟨1428407, by rfl⟩ : syracuseStep 1904543 = 2856815) B2856815
theorem B2822255 : Blo 1252444 2822255 := bstep (se 1 (by rfl) ⟨2116691, by rfl⟩ : syracuseStep 2822255 = 4233383) B4233383
theorem B2379935 : Blo 1252444 2379935 := bstep (se 1 (by rfl) ⟨1784951, by rfl⟩ : syracuseStep 2379935 = 3569903) B3569903
theorem B3011039 : Blo 1252444 3011039 := bstep (se 1 (by rfl) ⟨2258279, by rfl⟩ : syracuseStep 3011039 = 4516559) B4516559
theorem B5354171 : Blo 1252444 5354171 := bstep (se 1 (by rfl) ⟨4015628, by rfl⟩ : syracuseStep 5354171 = 8031257) B8031257
theorem B1880807 : Blo 1252444 1880807 := bstep (se 1 (by rfl) ⟨1410605, by rfl⟩ : syracuseStep 1880807 = 2821211) B2821211
theorem B9655321 : Blo 1252444 9655321 := bstep (se 2 (by rfl) ⟨3620745, by rfl⟩ : syracuseStep 9655321 = 7241491) B7241491
theorem B1881371 : Blo 1252444 1881371 := bstep (se 1 (by rfl) ⟨1411028, by rfl⟩ : syracuseStep 1881371 = 2822057) B2822057
theorem B6026575 : Blo 1252444 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B21428225 : Blo 1252444 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B6347483 : Blo 1252444 6347483 := bstep (se 1 (by rfl) ⟨4760612, by rfl⟩ : syracuseStep 6347483 = 9521225) B9521225
theorem B1252463 : Blo 1252444 1252463 := bstep (se 1 (by rfl) ⟨939347, by rfl⟩ : syracuseStep 1252463 = 1878695) B1878695
theorem B1252511 : Blo 1252444 1252511 := bstep (se 1 (by rfl) ⟨939383, by rfl⟩ : syracuseStep 1252511 = 1878767) B1878767
theorem B5356783 : Blo 1252444 5356783 := bstep (se 1 (by rfl) ⟨4017587, by rfl⟩ : syracuseStep 5356783 = 8035175) B8035175
theorem B22887775 : Blo 1252444 22887775 := bstep (se 1 (by rfl) ⟨17165831, by rfl⟩ : syracuseStep 22887775 = 34331663) B34331663
theorem B1252711 : Blo 1252444 1252711 := bstep (se 1 (by rfl) ⟨939533, by rfl⟩ : syracuseStep 1252711 = 1879067) B1879067
theorem B1252799 : Blo 1252444 1252799 := bstep (se 1 (by rfl) ⟨939599, by rfl⟩ : syracuseStep 1252799 = 1879199) B1879199
theorem B14278193 : Blo 1252444 14278193 := bstep (se 2 (by rfl) ⟨5354322, by rfl⟩ : syracuseStep 14278193 = 10708645) B10708645
theorem B1253147 : Blo 1252444 1253147 := bstep (se 1 (by rfl) ⟨939860, by rfl⟩ : syracuseStep 1253147 = 1879721) B1879721
theorem B3481481 : Blo 1252444 3481481 := bstep (se 2 (by rfl) ⟨1305555, by rfl⟩ : syracuseStep 3481481 = 2611111) B2611111
theorem B2818367 : Blo 1252444 2818367 := bstep (se 1 (by rfl) ⟨2113775, by rfl⟩ : syracuseStep 2818367 = 4227551) B4227551
theorem B2007359 : Blo 1252444 2007359 := bstep (se 1 (by rfl) ⟨1505519, by rfl⟩ : syracuseStep 2007359 = 3011039) B3011039
theorem B1253871 : Blo 1252444 1253871 := bstep (se 1 (by rfl) ⟨940403, by rfl⟩ : syracuseStep 1253871 = 1880807) B1880807
theorem B2114039 : Blo 1252444 2114039 := bstep (se 1 (by rfl) ⟨1585529, by rfl⟩ : syracuseStep 2114039 = 3171059) B3171059
theorem B1254247 : Blo 1252444 1254247 := bstep (se 1 (by rfl) ⟨940685, by rfl⟩ : syracuseStep 1254247 = 1881371) B1881371
theorem B4015487 : Blo 1252444 4015487 := bstep (se 1 (by rfl) ⟨3011615, by rfl⟩ : syracuseStep 4015487 = 6023231) B6023231
theorem B30517033 : Blo 1252444 30517033 := bstep (se 2 (by rfl) ⟨11443887, by rfl⟩ : syracuseStep 30517033 = 22887775) B22887775
theorem B1410943 : Blo 1252444 1410943 := bstep (se 1 (by rfl) ⟨1058207, by rfl⟩ : syracuseStep 1410943 = 2116415) B2116415
theorem B9283949 : Blo 1252444 9283949 := bstep (se 3 (by rfl) ⟨1740740, by rfl⟩ : syracuseStep 9283949 = 3481481) B3481481
theorem B1878719 : Blo 1252444 1878719 := bstep (se 1 (by rfl) ⟨1409039, by rfl⟩ : syracuseStep 1878719 = 2818079) B2818079
theorem B1878779 : Blo 1252444 1878779 := bstep (se 1 (by rfl) ⟨1409084, by rfl⟩ : syracuseStep 1878779 = 2818169) B2818169
theorem B10578899 : Blo 1252444 10578899 := bstep (se 1 (by rfl) ⟨7934174, by rfl⟩ : syracuseStep 10578899 = 15868349) B15868349
theorem B5352479 : Blo 1252444 5352479 := bstep (se 1 (by rfl) ⟨4014359, by rfl⟩ : syracuseStep 5352479 = 8028719) B8028719
theorem B1879271 : Blo 1252444 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B3173651 : Blo 1252444 3173651 := bstep (se 1 (by rfl) ⟨2380238, by rfl⟩ : syracuseStep 3173651 = 4760477) B4760477
theorem B4762921 : Blo 1252444 4762921 := bstep (se 2 (by rfl) ⟨1786095, by rfl⟩ : syracuseStep 4762921 = 3572191) B3572191
theorem B14282567 : Blo 1252444 14282567 := bstep (se 1 (by rfl) ⟨10711925, by rfl⟩ : syracuseStep 14282567 = 21423851) B21423851
theorem B1880063 : Blo 1252444 1880063 := bstep (se 1 (by rfl) ⟨1410047, by rfl⟩ : syracuseStep 1880063 = 2820095) B2820095
theorem B12873761 : Blo 1252444 12873761 := bstep (se 2 (by rfl) ⟨4827660, by rfl⟩ : syracuseStep 12873761 = 9655321) B9655321
theorem B5353897 : Blo 1252444 5353897 := bstep (se 2 (by rfl) ⟨2007711, by rfl⟩ : syracuseStep 5353897 = 4015423) B4015423
theorem B4231655 : Blo 1252444 4231655 := bstep (se 1 (by rfl) ⟨3173741, by rfl⟩ : syracuseStep 4231655 = 6347483) B6347483
theorem B3813961 : Blo 1252444 3813961 := bstep (se 2 (by rfl) ⟨1430235, by rfl⟩ : syracuseStep 3813961 = 2860471) B2860471
theorem B8024771 : Blo 1252444 8024771 := bstep (se 1 (by rfl) ⟨6018578, by rfl⟩ : syracuseStep 8024771 = 12037157) B12037157
theorem B10704271 : Blo 1252444 10704271 := bstep (se 1 (by rfl) ⟨8028203, by rfl⟩ : syracuseStep 10704271 = 16056407) B16056407
theorem B1881503 : Blo 1252444 1881503 := bstep (se 1 (by rfl) ⟨1411127, by rfl⟩ : syracuseStep 1881503 = 2822255) B2822255
theorem B1586623 : Blo 1252444 1586623 := bstep (se 1 (by rfl) ⟨1189967, by rfl⟩ : syracuseStep 1586623 = 2379935) B2379935
theorem B3569447 : Blo 1252444 3569447 := bstep (se 1 (by rfl) ⟨2677085, by rfl⟩ : syracuseStep 3569447 = 5354171) B5354171
theorem B4233599 : Blo 1252444 4233599 := bstep (se 1 (by rfl) ⟨3175199, by rfl⟩ : syracuseStep 4233599 = 6350399) B6350399
theorem B19306939 : Blo 1252444 19306939 := bstep (se 1 (by rfl) ⟨14480204, by rfl⟩ : syracuseStep 19306939 = 28960409) B28960409
theorem B14285483 : Blo 1252444 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B7142377 : Blo 1252444 7142377 := bstep (se 2 (by rfl) ⟨2678391, by rfl⟩ : syracuseStep 7142377 = 5356783) B5356783
theorem B8035433 : Blo 1252444 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B6773971 : Blo 1252444 6773971 := bstep (se 1 (by rfl) ⟨5080478, by rfl⟩ : syracuseStep 6773971 = 10160957) B10160957
theorem B1252767 : Blo 1252444 1252767 := bstep (se 1 (by rfl) ⟨939575, by rfl⟩ : syracuseStep 1252767 = 1879151) B1879151
theorem B9518795 : Blo 1252444 9518795 := bstep (se 1 (by rfl) ⟨7139096, by rfl⟩ : syracuseStep 9518795 = 14278193) B14278193
theorem B1253119 : Blo 1252444 1253119 := bstep (se 1 (by rfl) ⟨939839, by rfl⟩ : syracuseStep 1253119 = 1879679) B1879679
theorem B1253223 : Blo 1252444 1253223 := bstep (se 1 (by rfl) ⟨939917, by rfl⟩ : syracuseStep 1253223 = 1879835) B1879835
theorem B1269695 : Blo 1252444 1269695 := bstep (se 1 (by rfl) ⟨952271, by rfl⟩ : syracuseStep 1269695 = 1904543) B1904543
theorem B1409359 : Blo 1252444 1409359 := bstep (se 1 (by rfl) ⟨1057019, by rfl⟩ : syracuseStep 1409359 = 2114039) B2114039
theorem B5349847 : Blo 1252444 5349847 := bstep (se 1 (by rfl) ⟨4012385, by rfl⟩ : syracuseStep 5349847 = 8024771) B8024771
theorem B1254335 : Blo 1252444 1254335 := bstep (se 1 (by rfl) ⟨940751, by rfl⟩ : syracuseStep 1254335 = 1881503) B1881503
theorem B6350561 : Blo 1252444 6350561 := bstep (se 2 (by rfl) ⟨2381460, by rfl⟩ : syracuseStep 6350561 = 4762921) B4762921
theorem B14272361 : Blo 1252444 14272361 := bstep (se 2 (by rfl) ⟨5352135, by rfl⟩ : syracuseStep 14272361 = 10704271) B10704271
theorem B2115497 : Blo 1252444 2115497 := bstep (se 2 (by rfl) ⟨793311, by rfl⟩ : syracuseStep 2115497 = 1586623) B1586623
theorem B2115767 : Blo 1252444 2115767 := bstep (se 1 (by rfl) ⟨1586825, by rfl⟩ : syracuseStep 2115767 = 3173651) B3173651
theorem B3385853 : Blo 1252444 3385853 := bstep (se 3 (by rfl) ⟨634847, by rfl⟩ : syracuseStep 3385853 = 1269695) B1269695
theorem B9521711 : Blo 1252444 9521711 := bstep (se 1 (by rfl) ⟨7141283, by rfl⟩ : syracuseStep 9521711 = 14282567) B14282567
theorem B1878911 : Blo 1252444 1878911 := bstep (se 1 (by rfl) ⟨1409183, by rfl⟩ : syracuseStep 1878911 = 2818367) B2818367
theorem B1338239 : Blo 1252444 1338239 := bstep (se 1 (by rfl) ⟨1003679, by rfl⟩ : syracuseStep 1338239 = 2007359) B2007359
theorem B2821103 : Blo 1252444 2821103 := bstep (se 1 (by rfl) ⟨2115827, by rfl⟩ : syracuseStep 2821103 = 4231655) B4231655
theorem B7138529 : Blo 1252444 7138529 := bstep (se 2 (by rfl) ⟨2676948, by rfl⟩ : syracuseStep 7138529 = 5353897) B5353897
theorem B25742585 : Blo 1252444 25742585 := bstep (se 2 (by rfl) ⟨9653469, by rfl⟩ : syracuseStep 25742585 = 19306939) B19306939
theorem B2379631 : Blo 1252444 2379631 := bstep (se 1 (by rfl) ⟨1784723, by rfl⟩ : syracuseStep 2379631 = 3569447) B3569447
theorem B9523169 : Blo 1252444 9523169 := bstep (se 2 (by rfl) ⟨3571188, by rfl⟩ : syracuseStep 9523169 = 7142377) B7142377
theorem B6189299 : Blo 1252444 6189299 := bstep (se 1 (by rfl) ⟨4641974, by rfl⟩ : syracuseStep 6189299 = 9283949) B9283949
theorem B2822399 : Blo 1252444 2822399 := bstep (se 1 (by rfl) ⟨2116799, by rfl⟩ : syracuseStep 2822399 = 4233599) B4233599
theorem B9031961 : Blo 1252444 9031961 := bstep (se 2 (by rfl) ⟨3386985, by rfl⟩ : syracuseStep 9031961 = 6773971) B6773971
theorem B9523655 : Blo 1252444 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B3568319 : Blo 1252444 3568319 := bstep (se 1 (by rfl) ⟨2676239, by rfl⟩ : syracuseStep 3568319 = 5352479) B5352479
theorem B6345863 : Blo 1252444 6345863 := bstep (se 1 (by rfl) ⟨4759397, by rfl⟩ : syracuseStep 6345863 = 9518795) B9518795
theorem B1881257 : Blo 1252444 1881257 := bstep (se 2 (by rfl) ⟨705471, by rfl⟩ : syracuseStep 1881257 = 1410943) B1410943
theorem B8582507 : Blo 1252444 8582507 := bstep (se 1 (by rfl) ⟨6436880, by rfl⟩ : syracuseStep 8582507 = 12873761) B12873761
theorem B5085281 : Blo 1252444 5085281 := bstep (se 2 (by rfl) ⟨1906980, by rfl⟩ : syracuseStep 5085281 = 3813961) B3813961
theorem B2676991 : Blo 1252444 2676991 := bstep (se 1 (by rfl) ⟨2007743, by rfl⟩ : syracuseStep 2676991 = 4015487) B4015487
theorem B1252479 : Blo 1252444 1252479 := bstep (se 1 (by rfl) ⟨939359, by rfl⟩ : syracuseStep 1252479 = 1878719) B1878719
theorem B1252519 : Blo 1252444 1252519 := bstep (se 1 (by rfl) ⟨939389, by rfl⟩ : syracuseStep 1252519 = 1878779) B1878779
theorem B7052599 : Blo 1252444 7052599 := bstep (se 1 (by rfl) ⟨5289449, by rfl⟩ : syracuseStep 7052599 = 10578899) B10578899
theorem B5356955 : Blo 1252444 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B1252847 : Blo 1252444 1252847 := bstep (se 1 (by rfl) ⟨939635, by rfl⟩ : syracuseStep 1252847 = 1879271) B1879271
theorem B40689377 : Blo 1252444 40689377 := bstep (se 2 (by rfl) ⟨15258516, by rfl⟩ : syracuseStep 40689377 = 30517033) B30517033
theorem B1253375 : Blo 1252444 1253375 := bstep (se 1 (by rfl) ⟨940031, by rfl⟩ : syracuseStep 1253375 = 1880063) B1880063
theorem B6021307 : Blo 1252444 6021307 := bstep (se 1 (by rfl) ⟨4515980, by rfl⟩ : syracuseStep 6021307 = 9031961) B9031961
theorem B6349103 : Blo 1252444 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B1254171 : Blo 1252444 1254171 := bstep (se 1 (by rfl) ⟨940628, by rfl⟩ : syracuseStep 1254171 = 1881257) B1881257
theorem B1410331 : Blo 1252444 1410331 := bstep (se 1 (by rfl) ⟨1057748, by rfl⟩ : syracuseStep 1410331 = 2115497) B2115497
theorem B1410511 : Blo 1252444 1410511 := bstep (se 1 (by rfl) ⟨1057883, by rfl⟩ : syracuseStep 1410511 = 2115767) B2115767
theorem B3172841 : Blo 1252444 3172841 := bstep (se 2 (by rfl) ⟨1189815, by rfl⟩ : syracuseStep 3172841 = 2379631) B2379631
theorem B27126251 : Blo 1252444 27126251 := bstep (se 1 (by rfl) ⟨20344688, by rfl⟩ : syracuseStep 27126251 = 40689377) B40689377
theorem B1879145 : Blo 1252444 1879145 := bstep (se 2 (by rfl) ⟨704679, by rfl⟩ : syracuseStep 1879145 = 1409359) B1409359
theorem B2378879 : Blo 1252444 2378879 := bstep (se 1 (by rfl) ⟨1784159, by rfl⟩ : syracuseStep 2378879 = 3568319) B3568319
theorem B4230575 : Blo 1252444 4230575 := bstep (se 1 (by rfl) ⟨3172931, by rfl⟩ : syracuseStep 4230575 = 6345863) B6345863
theorem B5721671 : Blo 1252444 5721671 := bstep (se 1 (by rfl) ⟨4291253, by rfl⟩ : syracuseStep 5721671 = 8582507) B8582507
theorem B9514907 : Blo 1252444 9514907 := bstep (se 1 (by rfl) ⟨7136180, by rfl⟩ : syracuseStep 9514907 = 14272361) B14272361
theorem B2257235 : Blo 1252444 2257235 := bstep (se 1 (by rfl) ⟨1692926, by rfl⟩ : syracuseStep 2257235 = 3385853) B3385853
theorem B1880735 : Blo 1252444 1880735 := bstep (se 1 (by rfl) ⟨1410551, by rfl⟩ : syracuseStep 1880735 = 2821103) B2821103
theorem B3568637 : Blo 1252444 3568637 := bstep (se 3 (by rfl) ⟨669119, by rfl⟩ : syracuseStep 3568637 = 1338239) B1338239
theorem B4126199 : Blo 1252444 4126199 := bstep (se 1 (by rfl) ⟨3094649, by rfl⟩ : syracuseStep 4126199 = 6189299) B6189299
theorem B1881599 : Blo 1252444 1881599 := bstep (se 1 (by rfl) ⟨1411199, by rfl⟩ : syracuseStep 1881599 = 2822399) B2822399
theorem B3569321 : Blo 1252444 3569321 := bstep (se 2 (by rfl) ⟨1338495, by rfl⟩ : syracuseStep 3569321 = 2676991) B2676991
theorem B7133129 : Blo 1252444 7133129 := bstep (se 2 (by rfl) ⟨2674923, by rfl⟩ : syracuseStep 7133129 = 5349847) B5349847
theorem B4233707 : Blo 1252444 4233707 := bstep (se 1 (by rfl) ⟨3175280, by rfl⟩ : syracuseStep 4233707 = 6350561) B6350561
theorem B3390187 : Blo 1252444 3390187 := bstep (se 1 (by rfl) ⟨2542640, by rfl⟩ : syracuseStep 3390187 = 5085281) B5085281
theorem B6347807 : Blo 1252444 6347807 := bstep (se 1 (by rfl) ⟨4760855, by rfl⟩ : syracuseStep 6347807 = 9521711) B9521711
theorem B9403465 : Blo 1252444 9403465 := bstep (se 2 (by rfl) ⟨3526299, by rfl⟩ : syracuseStep 9403465 = 7052599) B7052599
theorem B1252607 : Blo 1252444 1252607 := bstep (se 1 (by rfl) ⟨939455, by rfl⟩ : syracuseStep 1252607 = 1878911) B1878911
theorem B4759019 : Blo 1252444 4759019 := bstep (se 1 (by rfl) ⟨3569264, by rfl⟩ : syracuseStep 4759019 = 7138529) B7138529
theorem B17161723 : Blo 1252444 17161723 := bstep (se 1 (by rfl) ⟨12871292, by rfl⟩ : syracuseStep 17161723 = 25742585) B25742585
theorem B3571303 : Blo 1252444 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B6348779 : Blo 1252444 6348779 := bstep (se 1 (by rfl) ⟨4761584, by rfl⟩ : syracuseStep 6348779 = 9523169) B9523169
theorem B8028409 : Blo 1252444 8028409 := bstep (se 2 (by rfl) ⟨3010653, by rfl⟩ : syracuseStep 8028409 = 6021307) B6021307
theorem B1253823 : Blo 1252444 1253823 := bstep (se 1 (by rfl) ⟨940367, by rfl⟩ : syracuseStep 1253823 = 1880735) B1880735
theorem B1254399 : Blo 1252444 1254399 := bstep (se 1 (by rfl) ⟨940799, by rfl⟩ : syracuseStep 1254399 = 1881599) B1881599
theorem B2115227 : Blo 1252444 2115227 := bstep (se 1 (by rfl) ⟨1586420, by rfl⟩ : syracuseStep 2115227 = 3172841) B3172841
theorem B22882297 : Blo 1252444 22882297 := bstep (se 2 (by rfl) ⟨8580861, by rfl⟩ : syracuseStep 22882297 = 17161723) B17161723
theorem B4761737 : Blo 1252444 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B2820383 : Blo 1252444 2820383 := bstep (se 1 (by rfl) ⟨2115287, by rfl⟩ : syracuseStep 2820383 = 4230575) B4230575
theorem B3172679 : Blo 1252444 3172679 := bstep (se 1 (by rfl) ⟨2379509, by rfl⟩ : syracuseStep 3172679 = 4759019) B4759019
theorem B6343271 : Blo 1252444 6343271 := bstep (se 1 (by rfl) ⟨4757453, by rfl⟩ : syracuseStep 6343271 = 9514907) B9514907
theorem B2379547 : Blo 1252444 2379547 := bstep (se 1 (by rfl) ⟨1784660, by rfl⟩ : syracuseStep 2379547 = 3569321) B3569321
theorem B4755419 : Blo 1252444 4755419 := bstep (se 1 (by rfl) ⟨3566564, by rfl⟩ : syracuseStep 4755419 = 7133129) B7133129
theorem B12537953 : Blo 1252444 12537953 := bstep (se 2 (by rfl) ⟨4701732, by rfl⟩ : syracuseStep 12537953 = 9403465) B9403465
theorem B18084167 : Blo 1252444 18084167 := bstep (se 1 (by rfl) ⟨13563125, by rfl⟩ : syracuseStep 18084167 = 27126251) B27126251
theorem B2822471 : Blo 1252444 2822471 := bstep (se 1 (by rfl) ⟨2116853, by rfl⟩ : syracuseStep 2822471 = 4233707) B4233707
theorem B1880441 : Blo 1252444 1880441 := bstep (se 2 (by rfl) ⟨705165, by rfl⟩ : syracuseStep 1880441 = 1410331) B1410331
theorem B1880681 : Blo 1252444 1880681 := bstep (se 2 (by rfl) ⟨705255, by rfl⟩ : syracuseStep 1880681 = 1410511) B1410511
theorem B4231871 : Blo 1252444 4231871 := bstep (se 1 (by rfl) ⟨3173903, by rfl⟩ : syracuseStep 4231871 = 6347807) B6347807
theorem B1585919 : Blo 1252444 1585919 := bstep (se 1 (by rfl) ⟨1189439, by rfl⟩ : syracuseStep 1585919 = 2378879) B2378879
theorem B3814447 : Blo 1252444 3814447 := bstep (se 1 (by rfl) ⟨2860835, by rfl⟩ : syracuseStep 3814447 = 5721671) B5721671
theorem B44012789 : Blo 1252444 44012789 := bstep (se 5 (by rfl) ⟨2063099, by rfl⟩ : syracuseStep 44012789 = 4126199) B4126199
theorem B4232519 : Blo 1252444 4232519 := bstep (se 1 (by rfl) ⟨3174389, by rfl⟩ : syracuseStep 4232519 = 6348779) B6348779
theorem B9516365 : Blo 1252444 9516365 := bstep (se 3 (by rfl) ⟨1784318, by rfl⟩ : syracuseStep 9516365 = 3568637) B3568637
theorem B4232735 : Blo 1252444 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B1504823 : Blo 1252444 1504823 := bstep (se 1 (by rfl) ⟨1128617, by rfl⟩ : syracuseStep 1504823 = 2257235) B2257235
theorem B4520249 : Blo 1252444 4520249 := bstep (se 2 (by rfl) ⟨1695093, by rfl⟩ : syracuseStep 4520249 = 3390187) B3390187
theorem B1252763 : Blo 1252444 1252763 := bstep (se 1 (by rfl) ⟨939572, by rfl⟩ : syracuseStep 1252763 = 1879145) B1879145
theorem B1253627 : Blo 1252444 1253627 := bstep (se 1 (by rfl) ⟨940220, by rfl⟩ : syracuseStep 1253627 = 1880441) B1880441
theorem B1253787 : Blo 1252444 1253787 := bstep (se 1 (by rfl) ⟨940340, by rfl⟩ : syracuseStep 1253787 = 1880681) B1880681
theorem B1410151 : Blo 1252444 1410151 := bstep (se 1 (by rfl) ⟨1057613, by rfl⟩ : syracuseStep 1410151 = 2115227) B2115227
theorem B2115119 : Blo 1252444 2115119 := bstep (se 1 (by rfl) ⟨1586339, by rfl⟩ : syracuseStep 2115119 = 3172679) B3172679
theorem B4228847 : Blo 1252444 4228847 := bstep (se 1 (by rfl) ⟨3171635, by rfl⟩ : syracuseStep 4228847 = 6343271) B6343271
theorem B4229117 : Blo 1252444 4229117 := bstep (se 3 (by rfl) ⟨792959, by rfl⟩ : syracuseStep 4229117 = 1585919) B1585919
theorem B3172729 : Blo 1252444 3172729 := bstep (se 2 (by rfl) ⟨1189773, by rfl⟩ : syracuseStep 3172729 = 2379547) B2379547
theorem B30509729 : Blo 1252444 30509729 := bstep (se 2 (by rfl) ⟨11441148, by rfl⟩ : syracuseStep 30509729 = 22882297) B22882297
theorem B8358635 : Blo 1252444 8358635 := bstep (se 1 (by rfl) ⟨6268976, by rfl⟩ : syracuseStep 8358635 = 12537953) B12537953
theorem B2821247 : Blo 1252444 2821247 := bstep (se 1 (by rfl) ⟨2115935, by rfl⟩ : syracuseStep 2821247 = 4231871) B4231871
theorem B2821679 : Blo 1252444 2821679 := bstep (se 1 (by rfl) ⟨2116259, by rfl⟩ : syracuseStep 2821679 = 4232519) B4232519
theorem B6344243 : Blo 1252444 6344243 := bstep (se 1 (by rfl) ⟨4758182, by rfl⟩ : syracuseStep 6344243 = 9516365) B9516365
theorem B2821823 : Blo 1252444 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B3174491 : Blo 1252444 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B1880255 : Blo 1252444 1880255 := bstep (se 1 (by rfl) ⟨1410191, by rfl⟩ : syracuseStep 1880255 = 2820383) B2820383
theorem B12056111 : Blo 1252444 12056111 := bstep (se 1 (by rfl) ⟨9042083, by rfl⟩ : syracuseStep 12056111 = 18084167) B18084167
theorem B1881647 : Blo 1252444 1881647 := bstep (se 1 (by rfl) ⟨1411235, by rfl⟩ : syracuseStep 1881647 = 2822471) B2822471
theorem B10704545 : Blo 1252444 10704545 := bstep (se 2 (by rfl) ⟨4014204, by rfl⟩ : syracuseStep 10704545 = 8028409) B8028409
theorem B29341859 : Blo 1252444 29341859 := bstep (se 1 (by rfl) ⟨22006394, by rfl⟩ : syracuseStep 29341859 = 44012789) B44012789
theorem B5085929 : Blo 1252444 5085929 := bstep (se 2 (by rfl) ⟨1907223, by rfl⟩ : syracuseStep 5085929 = 3814447) B3814447
theorem B4012861 : Blo 1252444 4012861 := bstep (se 3 (by rfl) ⟨752411, by rfl⟩ : syracuseStep 4012861 = 1504823) B1504823
theorem B3013499 : Blo 1252444 3013499 := bstep (se 1 (by rfl) ⟨2260124, by rfl⟩ : syracuseStep 3013499 = 4520249) B4520249
theorem B3170279 : Blo 1252444 3170279 := bstep (se 1 (by rfl) ⟨2377709, by rfl⟩ : syracuseStep 3170279 = 4755419) B4755419
theorem B1253503 : Blo 1252444 1253503 := bstep (se 1 (by rfl) ⟨940127, by rfl⟩ : syracuseStep 1253503 = 1880255) B1880255
theorem B1410079 : Blo 1252444 1410079 := bstep (se 1 (by rfl) ⟨1057559, by rfl⟩ : syracuseStep 1410079 = 2115119) B2115119
theorem B8037407 : Blo 1252444 8037407 := bstep (se 1 (by rfl) ⟨6028055, by rfl⟩ : syracuseStep 8037407 = 12056111) B12056111
theorem B1254431 : Blo 1252444 1254431 := bstep (se 1 (by rfl) ⟨940823, by rfl⟩ : syracuseStep 1254431 = 1881647) B1881647
theorem B5350481 : Blo 1252444 5350481 := bstep (se 2 (by rfl) ⟨2006430, by rfl⟩ : syracuseStep 5350481 = 4012861) B4012861
theorem B7136363 : Blo 1252444 7136363 := bstep (se 1 (by rfl) ⟨5352272, by rfl⟩ : syracuseStep 7136363 = 10704545) B10704545
theorem B2819231 : Blo 1252444 2819231 := bstep (se 1 (by rfl) ⟨2114423, by rfl⟩ : syracuseStep 2819231 = 4228847) B4228847
theorem B2819411 : Blo 1252444 2819411 := bstep (se 1 (by rfl) ⟨2114558, by rfl⟩ : syracuseStep 2819411 = 4229117) B4229117
theorem B5572423 : Blo 1252444 5572423 := bstep (se 1 (by rfl) ⟨4179317, by rfl⟩ : syracuseStep 5572423 = 8358635) B8358635
theorem B2008999 : Blo 1252444 2008999 := bstep (se 1 (by rfl) ⟨1506749, by rfl⟩ : syracuseStep 2008999 = 3013499) B3013499
theorem B4229495 : Blo 1252444 4229495 := bstep (se 1 (by rfl) ⟨3172121, by rfl⟩ : syracuseStep 4229495 = 6344243) B6344243
theorem B2116327 : Blo 1252444 2116327 := bstep (se 1 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 2116327 = 3174491) B3174491
theorem B78244957 : Blo 1252444 78244957 := bstep (se 3 (by rfl) ⟨14670929, by rfl⟩ : syracuseStep 78244957 = 29341859) B29341859
theorem B4230305 : Blo 1252444 4230305 := bstep (se 2 (by rfl) ⟨1586364, by rfl⟩ : syracuseStep 4230305 = 3172729) B3172729
theorem B1880201 : Blo 1252444 1880201 := bstep (se 2 (by rfl) ⟨705075, by rfl⟩ : syracuseStep 1880201 = 1410151) B1410151
theorem B13562477 : Blo 1252444 13562477 := bstep (se 3 (by rfl) ⟨2542964, by rfl⟩ : syracuseStep 13562477 = 5085929) B5085929
theorem B1880831 : Blo 1252444 1880831 := bstep (se 1 (by rfl) ⟨1410623, by rfl⟩ : syracuseStep 1880831 = 2821247) B2821247
theorem B1881119 : Blo 1252444 1881119 := bstep (se 1 (by rfl) ⟨1410839, by rfl⟩ : syracuseStep 1881119 = 2821679) B2821679
theorem B1881215 : Blo 1252444 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B20339819 : Blo 1252444 20339819 := bstep (se 1 (by rfl) ⟨15254864, by rfl⟩ : syracuseStep 20339819 = 30509729) B30509729
theorem B2113519 : Blo 1252444 2113519 := bstep (se 1 (by rfl) ⟨1585139, by rfl⟩ : syracuseStep 2113519 = 3170279) B3170279
theorem B1253467 : Blo 1252444 1253467 := bstep (se 1 (by rfl) ⟨940100, by rfl⟩ : syracuseStep 1253467 = 1880201) B1880201
theorem B1253887 : Blo 1252444 1253887 := bstep (se 1 (by rfl) ⟨940415, by rfl⟩ : syracuseStep 1253887 = 1880831) B1880831
theorem B1254079 : Blo 1252444 1254079 := bstep (se 1 (by rfl) ⟨940559, by rfl⟩ : syracuseStep 1254079 = 1881119) B1881119
theorem B5358271 : Blo 1252444 5358271 := bstep (se 1 (by rfl) ⟨4018703, by rfl⟩ : syracuseStep 5358271 = 8037407) B8037407
theorem B1254143 : Blo 1252444 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B2819663 : Blo 1252444 2819663 := bstep (se 1 (by rfl) ⟨2114747, by rfl⟩ : syracuseStep 2819663 = 4229495) B4229495
theorem B13559879 : Blo 1252444 13559879 := bstep (se 1 (by rfl) ⟨10169909, by rfl⟩ : syracuseStep 13559879 = 20339819) B20339819
theorem B2820203 : Blo 1252444 2820203 := bstep (se 1 (by rfl) ⟨2115152, by rfl⟩ : syracuseStep 2820203 = 4230305) B4230305
theorem B3566987 : Blo 1252444 3566987 := bstep (se 1 (by rfl) ⟨2675240, by rfl⟩ : syracuseStep 3566987 = 5350481) B5350481
theorem B1879487 : Blo 1252444 1879487 := bstep (se 1 (by rfl) ⟨1409615, by rfl⟩ : syracuseStep 1879487 = 2819231) B2819231
theorem B1879607 : Blo 1252444 1879607 := bstep (se 1 (by rfl) ⟨1409705, by rfl⟩ : syracuseStep 1879607 = 2819411) B2819411
theorem B2821769 : Blo 1252444 2821769 := bstep (se 2 (by rfl) ⟨1058163, by rfl⟩ : syracuseStep 2821769 = 2116327) B2116327
theorem B1880105 : Blo 1252444 1880105 := bstep (se 2 (by rfl) ⟨705039, by rfl⟩ : syracuseStep 1880105 = 1410079) B1410079
theorem B9041651 : Blo 1252444 9041651 := bstep (se 1 (by rfl) ⟨6781238, by rfl⟩ : syracuseStep 9041651 = 13562477) B13562477
theorem B417306437 : Blo 1252444 417306437 := bstep (se 4 (by rfl) ⟨39122478, by rfl⟩ : syracuseStep 417306437 = 78244957) B78244957
theorem B4757575 : Blo 1252444 4757575 := bstep (se 1 (by rfl) ⟨3568181, by rfl⟩ : syracuseStep 4757575 = 7136363) B7136363
theorem B7429897 : Blo 1252444 7429897 := bstep (se 2 (by rfl) ⟨2786211, by rfl⟩ : syracuseStep 7429897 = 5572423) B5572423
theorem B2678665 : Blo 1252444 2678665 := bstep (se 2 (by rfl) ⟨1004499, by rfl⟩ : syracuseStep 2678665 = 2008999) B2008999
theorem B2818025 : Blo 1252444 2818025 := bstep (se 2 (by rfl) ⟨1056759, by rfl⟩ : syracuseStep 2818025 = 2113519) B2113519
theorem B1253403 : Blo 1252444 1253403 := bstep (se 1 (by rfl) ⟨940052, by rfl⟩ : syracuseStep 1253403 = 1880105) B1880105
theorem B7144361 : Blo 1252444 7144361 := bstep (se 2 (by rfl) ⟨2679135, by rfl⟩ : syracuseStep 7144361 = 5358271) B5358271
theorem B2377991 : Blo 1252444 2377991 := bstep (se 1 (by rfl) ⟨1783493, by rfl⟩ : syracuseStep 2377991 = 3566987) B3566987
theorem B9906529 : Blo 1252444 9906529 := bstep (se 2 (by rfl) ⟨3714948, by rfl⟩ : syracuseStep 9906529 = 7429897) B7429897
theorem B1878683 : Blo 1252444 1878683 := bstep (se 1 (by rfl) ⟨1409012, by rfl⟩ : syracuseStep 1878683 = 2818025) B2818025
theorem B6343433 : Blo 1252444 6343433 := bstep (se 2 (by rfl) ⟨2378787, by rfl⟩ : syracuseStep 6343433 = 4757575) B4757575
theorem B1879775 : Blo 1252444 1879775 := bstep (se 1 (by rfl) ⟨1409831, by rfl⟩ : syracuseStep 1879775 = 2819663) B2819663
theorem B278204291 : Blo 1252444 278204291 := bstep (se 1 (by rfl) ⟨208653218, by rfl⟩ : syracuseStep 278204291 = 417306437) B417306437
theorem B9039919 : Blo 1252444 9039919 := bstep (se 1 (by rfl) ⟨6779939, by rfl⟩ : syracuseStep 9039919 = 13559879) B13559879
theorem B1880135 : Blo 1252444 1880135 := bstep (se 1 (by rfl) ⟨1410101, by rfl⟩ : syracuseStep 1880135 = 2820203) B2820203
theorem B1881179 : Blo 1252444 1881179 := bstep (se 1 (by rfl) ⟨1410884, by rfl⟩ : syracuseStep 1881179 = 2821769) B2821769
theorem B6027767 : Blo 1252444 6027767 := bstep (se 1 (by rfl) ⟨4520825, by rfl⟩ : syracuseStep 6027767 = 9041651) B9041651
theorem B1252991 : Blo 1252444 1252991 := bstep (se 1 (by rfl) ⟨939743, by rfl⟩ : syracuseStep 1252991 = 1879487) B1879487
theorem B1253071 : Blo 1252444 1253071 := bstep (se 1 (by rfl) ⟨939803, by rfl⟩ : syracuseStep 1253071 = 1879607) B1879607
theorem B3571553 : Blo 1252444 3571553 := bstep (se 2 (by rfl) ⟨1339332, by rfl⟩ : syracuseStep 3571553 = 2678665) B2678665
theorem B1253423 : Blo 1252444 1253423 := bstep (se 1 (by rfl) ⟨940067, by rfl⟩ : syracuseStep 1253423 = 1880135) B1880135
theorem B1254119 : Blo 1252444 1254119 := bstep (se 1 (by rfl) ⟨940589, by rfl⟩ : syracuseStep 1254119 = 1881179) B1881179
theorem B4228955 : Blo 1252444 4228955 := bstep (se 1 (by rfl) ⟨3171716, by rfl⟩ : syracuseStep 4228955 = 6343433) B6343433
theorem B185469527 : Blo 1252444 185469527 := bstep (se 1 (by rfl) ⟨139102145, by rfl⟩ : syracuseStep 185469527 = 278204291) B278204291
theorem B12053225 : Blo 1252444 12053225 := bstep (se 2 (by rfl) ⟨4519959, by rfl⟩ : syracuseStep 12053225 = 9039919) B9039919
theorem B13208705 : Blo 1252444 13208705 := bstep (se 2 (by rfl) ⟨4953264, by rfl⟩ : syracuseStep 13208705 = 9906529) B9906529
theorem B4762907 : Blo 1252444 4762907 := bstep (se 1 (by rfl) ⟨3572180, by rfl⟩ : syracuseStep 4762907 = 7144361) B7144361
theorem B1585327 : Blo 1252444 1585327 := bstep (se 1 (by rfl) ⟨1188995, by rfl⟩ : syracuseStep 1585327 = 2377991) B2377991
theorem B4018511 : Blo 1252444 4018511 := bstep (se 1 (by rfl) ⟨3013883, by rfl⟩ : syracuseStep 4018511 = 6027767) B6027767
theorem B9524141 : Blo 1252444 9524141 := bstep (se 3 (by rfl) ⟨1785776, by rfl⟩ : syracuseStep 9524141 = 3571553) B3571553
theorem B1252455 : Blo 1252444 1252455 := bstep (se 1 (by rfl) ⟨939341, by rfl⟩ : syracuseStep 1252455 = 1878683) B1878683
theorem B1253183 : Blo 1252444 1253183 := bstep (se 1 (by rfl) ⟨939887, by rfl⟩ : syracuseStep 1253183 = 1879775) B1879775
theorem B2679007 : Blo 1252444 2679007 := bstep (se 1 (by rfl) ⟨2009255, by rfl⟩ : syracuseStep 2679007 = 4018511) B4018511
theorem B2113769 : Blo 1252444 2113769 := bstep (se 2 (by rfl) ⟨792663, by rfl⟩ : syracuseStep 2113769 = 1585327) B1585327
theorem B6349427 : Blo 1252444 6349427 := bstep (se 1 (by rfl) ⟨4762070, by rfl⟩ : syracuseStep 6349427 = 9524141) B9524141
theorem B2819303 : Blo 1252444 2819303 := bstep (se 1 (by rfl) ⟨2114477, by rfl⟩ : syracuseStep 2819303 = 4228955) B4228955
theorem B123646351 : Blo 1252444 123646351 := bstep (se 1 (by rfl) ⟨92734763, by rfl⟩ : syracuseStep 123646351 = 185469527) B185469527
theorem B3175271 : Blo 1252444 3175271 := bstep (se 1 (by rfl) ⟨2381453, by rfl⟩ : syracuseStep 3175271 = 4762907) B4762907
theorem B8035483 : Blo 1252444 8035483 := bstep (se 1 (by rfl) ⟨6026612, by rfl⟩ : syracuseStep 8035483 = 12053225) B12053225
theorem B8805803 : Blo 1252444 8805803 := bstep (se 1 (by rfl) ⟨6604352, by rfl⟩ : syracuseStep 8805803 = 13208705) B13208705
theorem B1409179 : Blo 1252444 1409179 := bstep (se 1 (by rfl) ⟨1056884, by rfl⟩ : syracuseStep 1409179 = 2113769) B2113769
theorem B3572009 : Blo 1252444 3572009 := bstep (se 2 (by rfl) ⟨1339503, by rfl⟩ : syracuseStep 3572009 = 2679007) B2679007
theorem B2116847 : Blo 1252444 2116847 := bstep (se 1 (by rfl) ⟨1587635, by rfl⟩ : syracuseStep 2116847 = 3175271) B3175271
theorem B1879535 : Blo 1252444 1879535 := bstep (se 1 (by rfl) ⟨1409651, by rfl⟩ : syracuseStep 1879535 = 2819303) B2819303
theorem B4232951 : Blo 1252444 4232951 := bstep (se 1 (by rfl) ⟨3174713, by rfl⟩ : syracuseStep 4232951 = 6349427) B6349427
theorem B164861801 : Blo 1252444 164861801 := bstep (se 2 (by rfl) ⟨61823175, by rfl⟩ : syracuseStep 164861801 = 123646351) B123646351
theorem B10713977 : Blo 1252444 10713977 := bstep (se 2 (by rfl) ⟨4017741, by rfl⟩ : syracuseStep 10713977 = 8035483) B8035483
theorem B93928565 : Blo 1252444 93928565 := bstep (se 5 (by rfl) ⟨4402901, by rfl⟩ : syracuseStep 93928565 = 8805803) B8805803
theorem B1411231 : Blo 1252444 1411231 := bstep (se 1 (by rfl) ⟨1058423, by rfl⟩ : syracuseStep 1411231 = 2116847) B2116847
theorem B1878905 : Blo 1252444 1878905 := bstep (se 2 (by rfl) ⟨704589, by rfl⟩ : syracuseStep 1878905 = 1409179) B1409179
theorem B2821967 : Blo 1252444 2821967 := bstep (se 1 (by rfl) ⟨2116475, by rfl⟩ : syracuseStep 2821967 = 4232951) B4232951
theorem B109907867 : Blo 1252444 109907867 := bstep (se 1 (by rfl) ⟨82430900, by rfl⟩ : syracuseStep 109907867 = 164861801) B164861801
theorem B2381339 : Blo 1252444 2381339 := bstep (se 1 (by rfl) ⟨1786004, by rfl⟩ : syracuseStep 2381339 = 3572009) B3572009
theorem B7142651 : Blo 1252444 7142651 := bstep (se 1 (by rfl) ⟨5356988, by rfl⟩ : syracuseStep 7142651 = 10713977) B10713977
theorem B62619043 : Blo 1252444 62619043 := bstep (se 1 (by rfl) ⟨46964282, by rfl⟩ : syracuseStep 62619043 = 93928565) B93928565
theorem B1253023 : Blo 1252444 1253023 := bstep (se 1 (by rfl) ⟨939767, by rfl⟩ : syracuseStep 1253023 = 1879535) B1879535
theorem B6350237 : Blo 1252444 6350237 := bstep (se 3 (by rfl) ⟨1190669, by rfl⟩ : syracuseStep 6350237 = 2381339) B2381339
theorem B4761767 : Blo 1252444 4761767 := bstep (se 1 (by rfl) ⟨3571325, by rfl⟩ : syracuseStep 4761767 = 7142651) B7142651
theorem B73271911 : Blo 1252444 73271911 := bstep (se 1 (by rfl) ⟨54953933, by rfl⟩ : syracuseStep 73271911 = 109907867) B109907867
theorem B1881311 : Blo 1252444 1881311 := bstep (se 1 (by rfl) ⟨1410983, by rfl⟩ : syracuseStep 1881311 = 2821967) B2821967
theorem B1881641 : Blo 1252444 1881641 := bstep (se 2 (by rfl) ⟨705615, by rfl⟩ : syracuseStep 1881641 = 1411231) B1411231
theorem B83492057 : Blo 1252444 83492057 := bstep (se 2 (by rfl) ⟨31309521, by rfl⟩ : syracuseStep 83492057 = 62619043) B62619043
theorem B1252603 : Blo 1252444 1252603 := bstep (se 1 (by rfl) ⟨939452, by rfl⟩ : syracuseStep 1252603 = 1878905) B1878905
theorem B1254207 : Blo 1252444 1254207 := bstep (se 1 (by rfl) ⟨940655, by rfl⟩ : syracuseStep 1254207 = 1881311) B1881311
theorem B1254427 : Blo 1252444 1254427 := bstep (se 1 (by rfl) ⟨940820, by rfl⟩ : syracuseStep 1254427 = 1881641) B1881641
theorem B222645485 : Blo 1252444 222645485 := bstep (se 3 (by rfl) ⟨41746028, by rfl⟩ : syracuseStep 222645485 = 83492057) B83492057
theorem B3174511 : Blo 1252444 3174511 := bstep (se 1 (by rfl) ⟨2380883, by rfl⟩ : syracuseStep 3174511 = 4761767) B4761767
theorem B97695881 : Blo 1252444 97695881 := bstep (se 2 (by rfl) ⟨36635955, by rfl⟩ : syracuseStep 97695881 = 73271911) B73271911
theorem B4233491 : Blo 1252444 4233491 := bstep (se 1 (by rfl) ⟨3175118, by rfl⟩ : syracuseStep 4233491 = 6350237) B6350237
theorem B65130587 : Blo 1252444 65130587 := bstep (se 1 (by rfl) ⟨48847940, by rfl⟩ : syracuseStep 65130587 = 97695881) B97695881
theorem B2822327 : Blo 1252444 2822327 := bstep (se 1 (by rfl) ⟨2116745, by rfl⟩ : syracuseStep 2822327 = 4233491) B4233491
theorem B4232681 : Blo 1252444 4232681 := bstep (se 2 (by rfl) ⟨1587255, by rfl⟩ : syracuseStep 4232681 = 3174511) B3174511
theorem B148430323 : Blo 1252444 148430323 := bstep (se 1 (by rfl) ⟨111322742, by rfl⟩ : syracuseStep 148430323 = 222645485) B222645485
theorem B43420391 : Blo 1252444 43420391 := bstep (se 1 (by rfl) ⟨32565293, by rfl⟩ : syracuseStep 43420391 = 65130587) B65130587
theorem B2821787 : Blo 1252444 2821787 := bstep (se 1 (by rfl) ⟨2116340, by rfl⟩ : syracuseStep 2821787 = 4232681) B4232681
theorem B197907097 : Blo 1252444 197907097 := bstep (se 2 (by rfl) ⟨74215161, by rfl⟩ : syracuseStep 197907097 = 148430323) B148430323
theorem B1881551 : Blo 1252444 1881551 := bstep (se 1 (by rfl) ⟨1411163, by rfl⟩ : syracuseStep 1881551 = 2822327) B2822327
theorem B1254367 : Blo 1252444 1254367 := bstep (se 1 (by rfl) ⟨940775, by rfl⟩ : syracuseStep 1254367 = 1881551) B1881551
theorem B263876129 : Blo 1252444 263876129 := bstep (se 2 (by rfl) ⟨98953548, by rfl⟩ : syracuseStep 263876129 = 197907097) B197907097
theorem B28946927 : Blo 1252444 28946927 := bstep (se 1 (by rfl) ⟨21710195, by rfl⟩ : syracuseStep 28946927 = 43420391) B43420391
theorem B1881191 : Blo 1252444 1881191 := bstep (se 1 (by rfl) ⟨1410893, by rfl⟩ : syracuseStep 1881191 = 2821787) B2821787
theorem B1254127 : Blo 1252444 1254127 := bstep (se 1 (by rfl) ⟨940595, by rfl⟩ : syracuseStep 1254127 = 1881191) B1881191
theorem B175917419 : Blo 1252444 175917419 := bstep (se 1 (by rfl) ⟨131938064, by rfl⟩ : syracuseStep 175917419 = 263876129) B263876129
theorem B77191805 : Blo 1252444 77191805 := bstep (se 3 (by rfl) ⟨14473463, by rfl⟩ : syracuseStep 77191805 = 28946927) B28946927
theorem B117278279 : Blo 1252444 117278279 := bstep (se 1 (by rfl) ⟨87958709, by rfl⟩ : syracuseStep 117278279 = 175917419) B175917419
theorem B205844813 : Blo 1252444 205844813 := bstep (se 3 (by rfl) ⟨38595902, by rfl⟩ : syracuseStep 205844813 = 77191805) B77191805
theorem B78185519 : Blo 1252444 78185519 := bstep (se 1 (by rfl) ⟨58639139, by rfl⟩ : syracuseStep 78185519 = 117278279) B117278279
theorem B137229875 : Blo 1252444 137229875 := bstep (se 1 (by rfl) ⟨102922406, by rfl⟩ : syracuseStep 137229875 = 205844813) B205844813
theorem B52123679 : Blo 1252444 52123679 := bstep (se 1 (by rfl) ⟨39092759, by rfl⟩ : syracuseStep 52123679 = 78185519) B78185519
theorem B91486583 : Blo 1252444 91486583 := bstep (se 1 (by rfl) ⟨68614937, by rfl⟩ : syracuseStep 91486583 = 137229875) B137229875
theorem B60991055 : Blo 1252444 60991055 := bstep (se 1 (by rfl) ⟨45743291, by rfl⟩ : syracuseStep 60991055 = 91486583) B91486583
theorem B34749119 : Blo 1252444 34749119 := bstep (se 1 (by rfl) ⟨26061839, by rfl⟩ : syracuseStep 34749119 = 52123679) B52123679
theorem B40660703 : Blo 1252444 40660703 := bstep (se 1 (by rfl) ⟨30495527, by rfl⟩ : syracuseStep 40660703 = 60991055) B60991055
theorem B92664317 : Blo 1252444 92664317 := bstep (se 3 (by rfl) ⟨17374559, by rfl⟩ : syracuseStep 92664317 = 34749119) B34749119
theorem B61776211 : Blo 1252444 61776211 := bstep (se 1 (by rfl) ⟨46332158, by rfl⟩ : syracuseStep 61776211 = 92664317) B92664317
theorem B27107135 : Blo 1252444 27107135 := bstep (se 1 (by rfl) ⟨20330351, by rfl⟩ : syracuseStep 27107135 = 40660703) B40660703
theorem B82368281 : Blo 1252444 82368281 := bstep (se 2 (by rfl) ⟨30888105, by rfl⟩ : syracuseStep 82368281 = 61776211) B61776211
theorem B18071423 : Blo 1252444 18071423 := bstep (se 1 (by rfl) ⟨13553567, by rfl⟩ : syracuseStep 18071423 = 27107135) B27107135
theorem B54912187 : Blo 1252444 54912187 := bstep (se 1 (by rfl) ⟨41184140, by rfl⟩ : syracuseStep 54912187 = 82368281) B82368281
theorem B12047615 : Blo 1252444 12047615 := bstep (se 1 (by rfl) ⟨9035711, by rfl⟩ : syracuseStep 12047615 = 18071423) B18071423
theorem B292864997 : Blo 1252444 292864997 := bstep (se 4 (by rfl) ⟨27456093, by rfl⟩ : syracuseStep 292864997 = 54912187) B54912187
theorem B8031743 : Blo 1252444 8031743 := bstep (se 1 (by rfl) ⟨6023807, by rfl⟩ : syracuseStep 8031743 = 12047615) B12047615
theorem B195243331 : Blo 1252444 195243331 := bstep (se 1 (by rfl) ⟨146432498, by rfl⟩ : syracuseStep 195243331 = 292864997) B292864997
theorem B5354495 : Blo 1252444 5354495 := bstep (se 1 (by rfl) ⟨4015871, by rfl⟩ : syracuseStep 5354495 = 8031743) B8031743
theorem B3569663 : Blo 1252444 3569663 := bstep (se 1 (by rfl) ⟨2677247, by rfl⟩ : syracuseStep 3569663 = 5354495) B5354495
theorem B260324441 : Blo 1252444 260324441 := bstep (se 2 (by rfl) ⟨97621665, by rfl⟩ : syracuseStep 260324441 = 195243331) B195243331
theorem B173549627 : Blo 1252444 173549627 := bstep (se 1 (by rfl) ⟨130162220, by rfl⟩ : syracuseStep 173549627 = 260324441) B260324441
theorem B2379775 : Blo 1252444 2379775 := bstep (se 1 (by rfl) ⟨1784831, by rfl⟩ : syracuseStep 2379775 = 3569663) B3569663
theorem B3173033 : Blo 1252444 3173033 := bstep (se 2 (by rfl) ⟨1189887, by rfl⟩ : syracuseStep 3173033 = 2379775) B2379775
theorem B115699751 : Blo 1252444 115699751 := bstep (se 1 (by rfl) ⟨86774813, by rfl⟩ : syracuseStep 115699751 = 173549627) B173549627
theorem B2115355 : Blo 1252444 2115355 := bstep (se 1 (by rfl) ⟨1586516, by rfl⟩ : syracuseStep 2115355 = 3173033) B3173033
theorem B77133167 : Blo 1252444 77133167 := bstep (se 1 (by rfl) ⟨57849875, by rfl⟩ : syracuseStep 77133167 = 115699751) B115699751
theorem B51422111 : Blo 1252444 51422111 := bstep (se 1 (by rfl) ⟨38566583, by rfl⟩ : syracuseStep 51422111 = 77133167) B77133167
theorem B2820473 : Blo 1252444 2820473 := bstep (se 2 (by rfl) ⟨1057677, by rfl⟩ : syracuseStep 2820473 = 2115355) B2115355
theorem B1880315 : Blo 1252444 1880315 := bstep (se 1 (by rfl) ⟨1410236, by rfl⟩ : syracuseStep 1880315 = 2820473) B2820473
theorem B34281407 : Blo 1252444 34281407 := bstep (se 1 (by rfl) ⟨25711055, by rfl⟩ : syracuseStep 34281407 = 51422111) B51422111
theorem B1253543 : Blo 1252444 1253543 := bstep (se 1 (by rfl) ⟨940157, by rfl⟩ : syracuseStep 1253543 = 1880315) B1880315
theorem B22854271 : Blo 1252444 22854271 := bstep (se 1 (by rfl) ⟨17140703, by rfl⟩ : syracuseStep 22854271 = 34281407) B34281407
theorem B30472361 : Blo 1252444 30472361 := bstep (se 2 (by rfl) ⟨11427135, by rfl⟩ : syracuseStep 30472361 = 22854271) B22854271
theorem B20314907 : Blo 1252444 20314907 := bstep (se 1 (by rfl) ⟨15236180, by rfl⟩ : syracuseStep 20314907 = 30472361) B30472361
theorem B13543271 : Blo 1252444 13543271 := bstep (se 1 (by rfl) ⟨10157453, by rfl⟩ : syracuseStep 13543271 = 20314907) B20314907
theorem B9028847 : Blo 1252444 9028847 := bstep (se 1 (by rfl) ⟨6771635, by rfl⟩ : syracuseStep 9028847 = 13543271) B13543271
theorem B24076925 : Blo 1252444 24076925 := bstep (se 3 (by rfl) ⟨4514423, by rfl⟩ : syracuseStep 24076925 = 9028847) B9028847
theorem B16051283 : Blo 1252444 16051283 := bstep (se 1 (by rfl) ⟨12038462, by rfl⟩ : syracuseStep 16051283 = 24076925) B24076925
theorem B10700855 : Blo 1252444 10700855 := bstep (se 1 (by rfl) ⟨8025641, by rfl⟩ : syracuseStep 10700855 = 16051283) B16051283
theorem B7133903 : Blo 1252444 7133903 := bstep (se 1 (by rfl) ⟨5350427, by rfl⟩ : syracuseStep 7133903 = 10700855) B10700855
theorem B4755935 : Blo 1252444 4755935 := bstep (se 1 (by rfl) ⟨3566951, by rfl⟩ : syracuseStep 4755935 = 7133903) B7133903
theorem B3170623 : Blo 1252444 3170623 := bstep (se 1 (by rfl) ⟨2377967, by rfl⟩ : syracuseStep 3170623 = 4755935) B4755935
theorem B4227497 : Blo 1252444 4227497 := bstep (se 2 (by rfl) ⟨1585311, by rfl⟩ : syracuseStep 4227497 = 3170623) B3170623
theorem B2818331 : Blo 1252444 2818331 := bstep (se 1 (by rfl) ⟨2113748, by rfl⟩ : syracuseStep 2818331 = 4227497) B4227497
theorem B1878887 : Blo 1252444 1878887 := bstep (se 1 (by rfl) ⟨1409165, by rfl⟩ : syracuseStep 1878887 = 2818331) B2818331
theorem B1252591 : Blo 1252444 1252591 := bstep (se 1 (by rfl) ⟨939443, by rfl⟩ : syracuseStep 1252591 = 1878887) B1878887

theorem C0 (j : ℕ) (h1 : 313111 ≤ j) (h2 : j ≤ 313610) : Blo 1252444 (4 * j + 3) := by
  interval_cases j
  · exact B1252447
  · exact B1252451
  · exact B1252455
  · exact B1252459
  · exact B1252463
  · exact B1252467
  · exact B1252471
  · exact B1252475
  · exact B1252479
  · exact B1252483
  · exact B1252487
  · exact B1252491
  · exact B1252495
  · exact B1252499
  · exact B1252503
  · exact B1252507
  · exact B1252511
  · exact B1252515
  · exact B1252519
  · exact B1252523
  · exact B1252527
  · exact B1252531
  · exact B1252535
  · exact B1252539
  · exact B1252543
  · exact B1252547
  · exact B1252551
  · exact B1252555
  · exact B1252559
  · exact B1252563
  · exact B1252567
  · exact B1252571
  · exact B1252575
  · exact B1252579
  · exact B1252583
  · exact B1252587
  · exact B1252591
  · exact B1252595
  · exact B1252599
  · exact B1252603
  · exact B1252607
  · exact B1252611
  · exact B1252615
  · exact B1252619
  · exact B1252623
  · exact B1252627
  · exact B1252631
  · exact B1252635
  · exact B1252639
  · exact B1252643
  · exact B1252647
  · exact B1252651
  · exact B1252655
  · exact B1252659
  · exact B1252663
  · exact B1252667
  · exact B1252671
  · exact B1252675
  · exact B1252679
  · exact B1252683
  · exact B1252687
  · exact B1252691
  · exact B1252695
  · exact B1252699
  · exact B1252703
  · exact B1252707
  · exact B1252711
  · exact B1252715
  · exact B1252719
  · exact B1252723
  · exact B1252727
  · exact B1252731
  · exact B1252735
  · exact B1252739
  · exact B1252743
  · exact B1252747
  · exact B1252751
  · exact B1252755
  · exact B1252759
  · exact B1252763
  · exact B1252767
  · exact B1252771
  · exact B1252775
  · exact B1252779
  · exact B1252783
  · exact B1252787
  · exact B1252791
  · exact B1252795
  · exact B1252799
  · exact B1252803
  · exact B1252807
  · exact B1252811
  · exact B1252815
  · exact B1252819
  · exact B1252823
  · exact B1252827
  · exact B1252831
  · exact B1252835
  · exact B1252839
  · exact B1252843
  · exact B1252847
  · exact B1252851
  · exact B1252855
  · exact B1252859
  · exact B1252863
  · exact B1252867
  · exact B1252871
  · exact B1252875
  · exact B1252879
  · exact B1252883
  · exact B1252887
  · exact B1252891
  · exact B1252895
  · exact B1252899
  · exact B1252903
  · exact B1252907
  · exact B1252911
  · exact B1252915
  · exact B1252919
  · exact B1252923
  · exact B1252927
  · exact B1252931
  · exact B1252935
  · exact B1252939
  · exact B1252943
  · exact B1252947
  · exact B1252951
  · exact B1252955
  · exact B1252959
  · exact B1252963
  · exact B1252967
  · exact B1252971
  · exact B1252975
  · exact B1252979
  · exact B1252983
  · exact B1252987
  · exact B1252991
  · exact B1252995
  · exact B1252999
  · exact B1253003
  · exact B1253007
  · exact B1253011
  · exact B1253015
  · exact B1253019
  · exact B1253023
  · exact B1253027
  · exact B1253031
  · exact B1253035
  · exact B1253039
  · exact B1253043
  · exact B1253047
  · exact B1253051
  · exact B1253055
  · exact B1253059
  · exact B1253063
  · exact B1253067
  · exact B1253071
  · exact B1253075
  · exact B1253079
  · exact B1253083
  · exact B1253087
  · exact B1253091
  · exact B1253095
  · exact B1253099
  · exact B1253103
  · exact B1253107
  · exact B1253111
  · exact B1253115
  · exact B1253119
  · exact B1253123
  · exact B1253127
  · exact B1253131
  · exact B1253135
  · exact B1253139
  · exact B1253143
  · exact B1253147
  · exact B1253151
  · exact B1253155
  · exact B1253159
  · exact B1253163
  · exact B1253167
  · exact B1253171
  · exact B1253175
  · exact B1253179
  · exact B1253183
  · exact B1253187
  · exact B1253191
  · exact B1253195
  · exact B1253199
  · exact B1253203
  · exact B1253207
  · exact B1253211
  · exact B1253215
  · exact B1253219
  · exact B1253223
  · exact B1253227
  · exact B1253231
  · exact B1253235
  · exact B1253239
  · exact B1253243
  · exact B1253247
  · exact B1253251
  · exact B1253255
  · exact B1253259
  · exact B1253263
  · exact B1253267
  · exact B1253271
  · exact B1253275
  · exact B1253279
  · exact B1253283
  · exact B1253287
  · exact B1253291
  · exact B1253295
  · exact B1253299
  · exact B1253303
  · exact B1253307
  · exact B1253311
  · exact B1253315
  · exact B1253319
  · exact B1253323
  · exact B1253327
  · exact B1253331
  · exact B1253335
  · exact B1253339
  · exact B1253343
  · exact B1253347
  · exact B1253351
  · exact B1253355
  · exact B1253359
  · exact B1253363
  · exact B1253367
  · exact B1253371
  · exact B1253375
  · exact B1253379
  · exact B1253383
  · exact B1253387
  · exact B1253391
  · exact B1253395
  · exact B1253399
  · exact B1253403
  · exact B1253407
  · exact B1253411
  · exact B1253415
  · exact B1253419
  · exact B1253423
  · exact B1253427
  · exact B1253431
  · exact B1253435
  · exact B1253439
  · exact B1253443
  · exact B1253447
  · exact B1253451
  · exact B1253455
  · exact B1253459
  · exact B1253463
  · exact B1253467
  · exact B1253471
  · exact B1253475
  · exact B1253479
  · exact B1253483
  · exact B1253487
  · exact B1253491
  · exact B1253495
  · exact B1253499
  · exact B1253503
  · exact B1253507
  · exact B1253511
  · exact B1253515
  · exact B1253519
  · exact B1253523
  · exact B1253527
  · exact B1253531
  · exact B1253535
  · exact B1253539
  · exact B1253543
  · exact B1253547
  · exact B1253551
  · exact B1253555
  · exact B1253559
  · exact B1253563
  · exact B1253567
  · exact B1253571
  · exact B1253575
  · exact B1253579
  · exact B1253583
  · exact B1253587
  · exact B1253591
  · exact B1253595
  · exact B1253599
  · exact B1253603
  · exact B1253607
  · exact B1253611
  · exact B1253615
  · exact B1253619
  · exact B1253623
  · exact B1253627
  · exact B1253631
  · exact B1253635
  · exact B1253639
  · exact B1253643
  · exact B1253647
  · exact B1253651
  · exact B1253655
  · exact B1253659
  · exact B1253663
  · exact B1253667
  · exact B1253671
  · exact B1253675
  · exact B1253679
  · exact B1253683
  · exact B1253687
  · exact B1253691
  · exact B1253695
  · exact B1253699
  · exact B1253703
  · exact B1253707
  · exact B1253711
  · exact B1253715
  · exact B1253719
  · exact B1253723
  · exact B1253727
  · exact B1253731
  · exact B1253735
  · exact B1253739
  · exact B1253743
  · exact B1253747
  · exact B1253751
  · exact B1253755
  · exact B1253759
  · exact B1253763
  · exact B1253767
  · exact B1253771
  · exact B1253775
  · exact B1253779
  · exact B1253783
  · exact B1253787
  · exact B1253791
  · exact B1253795
  · exact B1253799
  · exact B1253803
  · exact B1253807
  · exact B1253811
  · exact B1253815
  · exact B1253819
  · exact B1253823
  · exact B1253827
  · exact B1253831
  · exact B1253835
  · exact B1253839
  · exact B1253843
  · exact B1253847
  · exact B1253851
  · exact B1253855
  · exact B1253859
  · exact B1253863
  · exact B1253867
  · exact B1253871
  · exact B1253875
  · exact B1253879
  · exact B1253883
  · exact B1253887
  · exact B1253891
  · exact B1253895
  · exact B1253899
  · exact B1253903
  · exact B1253907
  · exact B1253911
  · exact B1253915
  · exact B1253919
  · exact B1253923
  · exact B1253927
  · exact B1253931
  · exact B1253935
  · exact B1253939
  · exact B1253943
  · exact B1253947
  · exact B1253951
  · exact B1253955
  · exact B1253959
  · exact B1253963
  · exact B1253967
  · exact B1253971
  · exact B1253975
  · exact B1253979
  · exact B1253983
  · exact B1253987
  · exact B1253991
  · exact B1253995
  · exact B1253999
  · exact B1254003
  · exact B1254007
  · exact B1254011
  · exact B1254015
  · exact B1254019
  · exact B1254023
  · exact B1254027
  · exact B1254031
  · exact B1254035
  · exact B1254039
  · exact B1254043
  · exact B1254047
  · exact B1254051
  · exact B1254055
  · exact B1254059
  · exact B1254063
  · exact B1254067
  · exact B1254071
  · exact B1254075
  · exact B1254079
  · exact B1254083
  · exact B1254087
  · exact B1254091
  · exact B1254095
  · exact B1254099
  · exact B1254103
  · exact B1254107
  · exact B1254111
  · exact B1254115
  · exact B1254119
  · exact B1254123
  · exact B1254127
  · exact B1254131
  · exact B1254135
  · exact B1254139
  · exact B1254143
  · exact B1254147
  · exact B1254151
  · exact B1254155
  · exact B1254159
  · exact B1254163
  · exact B1254167
  · exact B1254171
  · exact B1254175
  · exact B1254179
  · exact B1254183
  · exact B1254187
  · exact B1254191
  · exact B1254195
  · exact B1254199
  · exact B1254203
  · exact B1254207
  · exact B1254211
  · exact B1254215
  · exact B1254219
  · exact B1254223
  · exact B1254227
  · exact B1254231
  · exact B1254235
  · exact B1254239
  · exact B1254243
  · exact B1254247
  · exact B1254251
  · exact B1254255
  · exact B1254259
  · exact B1254263
  · exact B1254267
  · exact B1254271
  · exact B1254275
  · exact B1254279
  · exact B1254283
  · exact B1254287
  · exact B1254291
  · exact B1254295
  · exact B1254299
  · exact B1254303
  · exact B1254307
  · exact B1254311
  · exact B1254315
  · exact B1254319
  · exact B1254323
  · exact B1254327
  · exact B1254331
  · exact B1254335
  · exact B1254339
  · exact B1254343
  · exact B1254347
  · exact B1254351
  · exact B1254355
  · exact B1254359
  · exact B1254363
  · exact B1254367
  · exact B1254371
  · exact B1254375
  · exact B1254379
  · exact B1254383
  · exact B1254387
  · exact B1254391
  · exact B1254395
  · exact B1254399
  · exact B1254403
  · exact B1254407
  · exact B1254411
  · exact B1254415
  · exact B1254419
  · exact B1254423
  · exact B1254427
  · exact B1254431
  · exact B1254435
  · exact B1254439
  · exact B1254443

theorem solution (m : ℕ) (hlo : 1252444 ≤ m) (hhi : m ≤ 1254444) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 313111 ≤ j := by omega
    have hj2 : j ≤ 313610 := by omega
    have hb : Blo 1252444 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
