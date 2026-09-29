-- Prove2me | solution 1 for syracuse_descends_range_1672036_1674036
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:21:06.099706+00:00
-- url     : https://prove2.me/submissions/0fb31064-bb7f-45be-ad11-4abb7339a91c

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


theorem B7143461 : Blo 1672036 7143461 := bbase (se 4 (by rfl) ⟨669699, by rfl⟩ : syracuseStep 7143461 = 1339399) (by norm_num)
theorem B3817525 : Blo 1672036 3817525 := bbase (se 5 (by rfl) ⟨178946, by rfl⟩ : syracuseStep 3817525 = 357893) (by norm_num)
theorem B3571781 : Blo 1672036 3571781 := bbase (se 4 (by rfl) ⟨334854, by rfl⟩ : syracuseStep 3571781 = 669709) (by norm_num)
theorem B1785925 : Blo 1672036 1785925 := bbase (se 4 (by rfl) ⟨167430, by rfl⟩ : syracuseStep 1785925 = 334861) (by norm_num)
theorem B3219589 : Blo 1672036 3219589 := bbase (se 4 (by rfl) ⟨301836, by rfl⟩ : syracuseStep 3219589 = 603673) (by norm_num)
theorem B2678933 : Blo 1672036 2678933 := bbase (se 6 (by rfl) ⟨62787, by rfl⟩ : syracuseStep 2678933 = 125575) (by norm_num)
theorem B4235429 : Blo 1672036 4235429 := bbase (se 4 (by rfl) ⟨397071, by rfl⟩ : syracuseStep 4235429 = 794143) (by norm_num)
theorem B6349013 : Blo 1672036 6349013 := bbase (se 7 (by rfl) ⟨74402, by rfl⟩ : syracuseStep 6349013 = 148805) (by norm_num)
theorem B10174709 : Blo 1672036 10174709 := bbase (se 5 (by rfl) ⟨476939, by rfl⟩ : syracuseStep 10174709 = 953879) (by norm_num)
theorem B5644565 : Blo 1672036 5644565 := bbase (se 6 (by rfl) ⟨132294, by rfl⟩ : syracuseStep 5644565 = 264589) (by norm_num)
theorem B3572021 : Blo 1672036 3572021 := bbase (se 5 (by rfl) ⟨167438, by rfl⟩ : syracuseStep 3572021 = 334877) (by norm_num)
theorem B7242133 : Blo 1672036 7242133 := bbase (se 6 (by rfl) ⟨169737, by rfl⟩ : syracuseStep 7242133 = 339475) (by norm_num)
theorem B2146721 : Blo 1672036 2146721 := bbase (se 2 (by rfl) ⟨805020, by rfl⟩ : syracuseStep 2146721 = 1610041) (by norm_num)
theorem B20341205 : Blo 1672036 20341205 := bbase (se 7 (by rfl) ⟨238373, by rfl⟩ : syracuseStep 20341205 = 476747) (by norm_num)
theorem B4235773 : Blo 1672036 4235773 := bbase (se 3 (by rfl) ⟨794207, by rfl⟩ : syracuseStep 4235773 = 1588415) (by norm_num)
theorem B1810993 : Blo 1672036 1810993 := bbase (se 2 (by rfl) ⟨679122, by rfl⟩ : syracuseStep 1810993 = 1358245) (by norm_num)
theorem B4522549 : Blo 1672036 4522549 := bbase (se 5 (by rfl) ⟨211994, by rfl⟩ : syracuseStep 4522549 = 423989) (by norm_num)
theorem B8471141 : Blo 1672036 8471141 := bbase (se 4 (by rfl) ⟨794169, by rfl⟩ : syracuseStep 8471141 = 1588339) (by norm_num)
theorem B3621485 : Blo 1672036 3621485 := bbase (se 3 (by rfl) ⟨679028, by rfl⟩ : syracuseStep 3621485 = 1358057) (by norm_num)
theorem B4235885 : Blo 1672036 4235885 := bbase (se 3 (by rfl) ⟨794228, by rfl⟩ : syracuseStep 4235885 = 1588457) (by norm_num)
theorem B5644997 : Blo 1672036 5644997 := bbase (se 4 (by rfl) ⟨529218, by rfl⟩ : syracuseStep 5644997 = 1058437) (by norm_num)
theorem B3572525 : Blo 1672036 3572525 := bbase (se 3 (by rfl) ⟨669848, by rfl⟩ : syracuseStep 3572525 = 1339697) (by norm_num)
theorem B4236077 : Blo 1672036 4236077 := bbase (se 3 (by rfl) ⟨794264, by rfl⟩ : syracuseStep 4236077 = 1588529) (by norm_num)
theorem B3572533 : Blo 1672036 3572533 := bbase (se 5 (by rfl) ⟨167462, by rfl⟩ : syracuseStep 3572533 = 334925) (by norm_num)
theorem B1786745 : Blo 1672036 1786745 := bbase (se 2 (by rfl) ⟨670029, by rfl⟩ : syracuseStep 1786745 = 1340059) (by norm_num)
theorem B2147213 : Blo 1672036 2147213 := bbase (se 3 (by rfl) ⟨402602, by rfl⟩ : syracuseStep 2147213 = 805205) (by norm_num)
theorem B2679733 : Blo 1672036 2679733 := bbase (se 5 (by rfl) ⟨125612, by rfl⟩ : syracuseStep 2679733 = 251225) (by norm_num)
theorem B1811417 : Blo 1672036 1811417 := bbase (se 2 (by rfl) ⟨679281, by rfl⟩ : syracuseStep 1811417 = 1358563) (by norm_num)
theorem B2262053 : Blo 1672036 2262053 := bbase (se 4 (by rfl) ⟨212067, by rfl⟩ : syracuseStep 2262053 = 424135) (by norm_num)
theorem B5645429 : Blo 1672036 5645429 := bbase (se 5 (by rfl) ⟨264629, by rfl⟩ : syracuseStep 5645429 = 529259) (by norm_num)
theorem B4236421 : Blo 1672036 4236421 := bbase (se 4 (by rfl) ⟨397164, by rfl⟩ : syracuseStep 4236421 = 794329) (by norm_num)
theorem B6784165 : Blo 1672036 6784165 := bbase (se 4 (by rfl) ⟨636015, by rfl⟩ : syracuseStep 6784165 = 1272031) (by norm_num)
theorem B4236533 : Blo 1672036 4236533 := bbase (se 5 (by rfl) ⟨198587, by rfl⟩ : syracuseStep 4236533 = 397175) (by norm_num)
theorem B2508077 : Blo 1672036 2508077 := bbase (se 3 (by rfl) ⟨470264, by rfl⟩ : syracuseStep 2508077 = 940529) (by norm_num)
theorem B1787189 : Blo 1672036 1787189 := bbase (se 5 (by rfl) ⟨83774, by rfl⟩ : syracuseStep 1787189 = 167549) (by norm_num)
theorem B3015997 : Blo 1672036 3015997 := bbase (se 3 (by rfl) ⟨565499, by rfl⟩ : syracuseStep 3015997 = 1130999) (by norm_num)
theorem B2508101 : Blo 1672036 2508101 := bbase (se 4 (by rfl) ⟨235134, by rfl⟩ : syracuseStep 2508101 = 470269) (by norm_num)
theorem B2508125 : Blo 1672036 2508125 := bbase (se 3 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 2508125 = 940547) (by norm_num)
theorem B2508149 : Blo 1672036 2508149 := bbase (se 5 (by rfl) ⟨117569, by rfl⟩ : syracuseStep 2508149 = 235139) (by norm_num)
theorem B6350197 : Blo 1672036 6350197 := bbase (se 5 (by rfl) ⟨297665, by rfl⟩ : syracuseStep 6350197 = 595331) (by norm_num)
theorem B1860989 : Blo 1672036 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B2508173 : Blo 1672036 2508173 := bbase (se 3 (by rfl) ⟨470282, by rfl⟩ : syracuseStep 2508173 = 940565) (by norm_num)
theorem B2508197 : Blo 1672036 2508197 := bbase (se 4 (by rfl) ⟨235143, by rfl⟩ : syracuseStep 2508197 = 470287) (by norm_num)
theorem B4236725 : Blo 1672036 4236725 := bbase (se 5 (by rfl) ⟨198596, by rfl⟩ : syracuseStep 4236725 = 397193) (by norm_num)
theorem B2508221 : Blo 1672036 2508221 := bbase (se 3 (by rfl) ⟨470291, by rfl⟩ : syracuseStep 2508221 = 940583) (by norm_num)
theorem B2508245 : Blo 1672036 2508245 := bbase (se 7 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 2508245 = 58787) (by norm_num)
theorem B2680285 : Blo 1672036 2680285 := bbase (se 3 (by rfl) ⟨502553, by rfl⟩ : syracuseStep 2680285 = 1005107) (by norm_num)
theorem B2508269 : Blo 1672036 2508269 := bbase (se 3 (by rfl) ⟨470300, by rfl⟩ : syracuseStep 2508269 = 940601) (by norm_num)
theorem B2508293 : Blo 1672036 2508293 := bbase (se 4 (by rfl) ⟨235152, by rfl⟩ : syracuseStep 2508293 = 470305) (by norm_num)
theorem B8037893 : Blo 1672036 8037893 := bbase (se 4 (by rfl) ⟨753552, by rfl⟩ : syracuseStep 8037893 = 1507105) (by norm_num)
theorem B2508317 : Blo 1672036 2508317 := bbase (se 3 (by rfl) ⟨470309, by rfl⟩ : syracuseStep 2508317 = 940619) (by norm_num)
theorem B5645861 : Blo 1672036 5645861 := bbase (se 4 (by rfl) ⟨529299, by rfl⟩ : syracuseStep 5645861 = 1058599) (by norm_num)
theorem B1787437 : Blo 1672036 1787437 := bbase (se 3 (by rfl) ⟨335144, by rfl⟩ : syracuseStep 1787437 = 670289) (by norm_num)
theorem B2508341 : Blo 1672036 2508341 := bbase (se 5 (by rfl) ⟨117578, by rfl⟩ : syracuseStep 2508341 = 235157) (by norm_num)
theorem B2508365 : Blo 1672036 2508365 := bbase (se 3 (by rfl) ⟨470318, by rfl⟩ : syracuseStep 2508365 = 940637) (by norm_num)
theorem B14296661 : Blo 1672036 14296661 := bbase (se 8 (by rfl) ⟨83769, by rfl⟩ : syracuseStep 14296661 = 167539) (by norm_num)
theorem B2508389 : Blo 1672036 2508389 := bbase (se 4 (by rfl) ⟨235161, by rfl⟩ : syracuseStep 2508389 = 470323) (by norm_num)
theorem B2508413 : Blo 1672036 2508413 := bbase (se 3 (by rfl) ⟨470327, by rfl⟩ : syracuseStep 2508413 = 940655) (by norm_num)
theorem B2508437 : Blo 1672036 2508437 := bbase (se 6 (by rfl) ⟨58791, by rfl⟩ : syracuseStep 2508437 = 117583) (by norm_num)
theorem B6350501 : Blo 1672036 6350501 := bbase (se 4 (by rfl) ⟨595359, by rfl⟩ : syracuseStep 6350501 = 1190719) (by norm_num)
theorem B2508461 : Blo 1672036 2508461 := bbase (se 3 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 2508461 = 940673) (by norm_num)
theorem B2508485 : Blo 1672036 2508485 := bbase (se 4 (by rfl) ⟨235170, by rfl⟩ : syracuseStep 2508485 = 470341) (by norm_num)
theorem B2508509 : Blo 1672036 2508509 := bbase (se 3 (by rfl) ⟨470345, by rfl⟩ : syracuseStep 2508509 = 940691) (by norm_num)
theorem B2680541 : Blo 1672036 2680541 := bbase (se 3 (by rfl) ⟨502601, by rfl⟩ : syracuseStep 2680541 = 1005203) (by norm_num)
theorem B2508533 : Blo 1672036 2508533 := bbase (se 5 (by rfl) ⟨117587, by rfl⟩ : syracuseStep 2508533 = 235175) (by norm_num)
theorem B2508557 : Blo 1672036 2508557 := bbase (se 3 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 2508557 = 940709) (by norm_num)
theorem B4237069 : Blo 1672036 4237069 := bbase (se 3 (by rfl) ⟨794450, by rfl⟩ : syracuseStep 4237069 = 1588901) (by norm_num)
theorem B15255317 : Blo 1672036 15255317 := bbase (se 6 (by rfl) ⟨357546, by rfl⟩ : syracuseStep 15255317 = 715093) (by norm_num)
theorem B2508581 : Blo 1672036 2508581 := bbase (se 4 (by rfl) ⟨235179, by rfl⟩ : syracuseStep 2508581 = 470359) (by norm_num)
theorem B2508605 : Blo 1672036 2508605 := bbase (se 3 (by rfl) ⟨470363, by rfl⟩ : syracuseStep 2508605 = 940727) (by norm_num)
theorem B2508629 : Blo 1672036 2508629 := bbase (se 9 (by rfl) ⟨7349, by rfl⟩ : syracuseStep 2508629 = 14699) (by norm_num)
theorem B2508653 : Blo 1672036 2508653 := bbase (se 3 (by rfl) ⟨470372, by rfl⟩ : syracuseStep 2508653 = 940745) (by norm_num)
theorem B8472437 : Blo 1672036 8472437 := bbase (se 5 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 8472437 = 794291) (by norm_num)
theorem B4237181 : Blo 1672036 4237181 := bbase (se 3 (by rfl) ⟨794471, by rfl⟩ : syracuseStep 4237181 = 1588943) (by norm_num)
theorem B2508677 : Blo 1672036 2508677 := bbase (se 4 (by rfl) ⟨235188, by rfl⟩ : syracuseStep 2508677 = 470377) (by norm_num)
theorem B27142037 : Blo 1672036 27142037 := bbase (se 6 (by rfl) ⟨636141, by rfl⟩ : syracuseStep 27142037 = 1272283) (by norm_num)
theorem B2508701 : Blo 1672036 2508701 := bbase (se 3 (by rfl) ⟨470381, by rfl⟩ : syracuseStep 2508701 = 940763) (by norm_num)
theorem B3573661 : Blo 1672036 3573661 := bbase (se 3 (by rfl) ⟨670061, by rfl⟩ : syracuseStep 3573661 = 1340123) (by norm_num)
theorem B2508725 : Blo 1672036 2508725 := bbase (se 5 (by rfl) ⟨117596, by rfl⟩ : syracuseStep 2508725 = 235193) (by norm_num)
theorem B3762125 : Blo 1672036 3762125 := bbase (se 3 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 3762125 = 1410797) (by norm_num)
theorem B2508749 : Blo 1672036 2508749 := bbase (se 3 (by rfl) ⟨470390, by rfl⟩ : syracuseStep 2508749 = 940781) (by norm_num)
theorem B5646293 : Blo 1672036 5646293 := bbase (se 7 (by rfl) ⟨66167, by rfl⟩ : syracuseStep 5646293 = 132335) (by norm_num)
theorem B2508773 : Blo 1672036 2508773 := bbase (se 4 (by rfl) ⟨235197, by rfl⟩ : syracuseStep 2508773 = 470395) (by norm_num)
theorem B2508797 : Blo 1672036 2508797 := bbase (se 3 (by rfl) ⟨470399, by rfl⟩ : syracuseStep 2508797 = 940799) (by norm_num)
theorem B3762197 : Blo 1672036 3762197 := bbase (se 6 (by rfl) ⟨88176, by rfl⟩ : syracuseStep 3762197 = 176353) (by norm_num)
theorem B2508821 : Blo 1672036 2508821 := bbase (se 6 (by rfl) ⟨58800, by rfl⟩ : syracuseStep 2508821 = 117601) (by norm_num)
theorem B2508845 : Blo 1672036 2508845 := bbase (se 3 (by rfl) ⟨470408, by rfl⟩ : syracuseStep 2508845 = 940817) (by norm_num)
theorem B9529397 : Blo 1672036 9529397 := bbase (se 5 (by rfl) ⟨446690, by rfl⟩ : syracuseStep 9529397 = 893381) (by norm_num)
theorem B4237373 : Blo 1672036 4237373 := bbase (se 3 (by rfl) ⟨794507, by rfl⟩ : syracuseStep 4237373 = 1589015) (by norm_num)
theorem B2508869 : Blo 1672036 2508869 := bbase (se 4 (by rfl) ⟨235206, by rfl⟩ : syracuseStep 2508869 = 470413) (by norm_num)
theorem B3762269 : Blo 1672036 3762269 := bbase (se 3 (by rfl) ⟨705425, by rfl⟩ : syracuseStep 3762269 = 1410851) (by norm_num)
theorem B2508893 : Blo 1672036 2508893 := bbase (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) (by norm_num)
theorem B2508917 : Blo 1672036 2508917 := bbase (se 5 (by rfl) ⟨117605, by rfl⟩ : syracuseStep 2508917 = 235211) (by norm_num)
theorem B2861173 : Blo 1672036 2861173 := bbase (se 5 (by rfl) ⟨134117, by rfl⟩ : syracuseStep 2861173 = 268235) (by norm_num)
theorem B10725493 : Blo 1672036 10725493 := bbase (se 5 (by rfl) ⟨502757, by rfl⟩ : syracuseStep 10725493 = 1005515) (by norm_num)
theorem B2508941 : Blo 1672036 2508941 := bbase (se 3 (by rfl) ⟨470426, by rfl⟩ : syracuseStep 2508941 = 940853) (by norm_num)
theorem B3762341 : Blo 1672036 3762341 := bbase (se 4 (by rfl) ⟨352719, by rfl⟩ : syracuseStep 3762341 = 705439) (by norm_num)
theorem B2508965 : Blo 1672036 2508965 := bbase (se 4 (by rfl) ⟨235215, by rfl⟩ : syracuseStep 2508965 = 470431) (by norm_num)
theorem B2508989 : Blo 1672036 2508989 := bbase (se 3 (by rfl) ⟨470435, by rfl⟩ : syracuseStep 2508989 = 940871) (by norm_num)
theorem B2009281 : Blo 1672036 2009281 := bbase (se 2 (by rfl) ⟨753480, by rfl⟩ : syracuseStep 2009281 = 1506961) (by norm_num)
theorem B2509013 : Blo 1672036 2509013 := bbase (se 7 (by rfl) ⟨29402, by rfl⟩ : syracuseStep 2509013 = 58805) (by norm_num)
theorem B3762413 : Blo 1672036 3762413 := bbase (se 3 (by rfl) ⟨705452, by rfl⟩ : syracuseStep 3762413 = 1410905) (by norm_num)
theorem B2509037 : Blo 1672036 2509037 := bbase (se 3 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 2509037 = 940889) (by norm_num)
theorem B2009329 : Blo 1672036 2009329 := bbase (se 2 (by rfl) ⟨753498, by rfl⟩ : syracuseStep 2009329 = 1506997) (by norm_num)
theorem B2509061 : Blo 1672036 2509061 := bbase (se 4 (by rfl) ⟨235224, by rfl⟩ : syracuseStep 2509061 = 470449) (by norm_num)
theorem B5359877 : Blo 1672036 5359877 := bbase (se 4 (by rfl) ⟨502488, by rfl⟩ : syracuseStep 5359877 = 1004977) (by norm_num)
theorem B7145749 : Blo 1672036 7145749 := bbase (se 6 (by rfl) ⟨167478, by rfl⟩ : syracuseStep 7145749 = 334957) (by norm_num)
theorem B3574037 : Blo 1672036 3574037 := bbase (se 6 (by rfl) ⟨83766, by rfl⟩ : syracuseStep 3574037 = 167533) (by norm_num)
theorem B2509085 : Blo 1672036 2509085 := bbase (se 3 (by rfl) ⟨470453, by rfl⟩ : syracuseStep 2509085 = 940907) (by norm_num)
theorem B3762485 : Blo 1672036 3762485 := bbase (se 5 (by rfl) ⟨176366, by rfl⟩ : syracuseStep 3762485 = 352733) (by norm_num)
theorem B2509109 : Blo 1672036 2509109 := bbase (se 5 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 2509109 = 235229) (by norm_num)
theorem B2509133 : Blo 1672036 2509133 := bbase (se 3 (by rfl) ⟨470462, by rfl⟩ : syracuseStep 2509133 = 940925) (by norm_num)
theorem B2509157 : Blo 1672036 2509157 := bbase (se 4 (by rfl) ⟨235233, by rfl⟩ : syracuseStep 2509157 = 470467) (by norm_num)
theorem B3762557 : Blo 1672036 3762557 := bbase (se 3 (by rfl) ⟨705479, by rfl⟩ : syracuseStep 3762557 = 1410959) (by norm_num)
theorem B2509181 : Blo 1672036 2509181 := bbase (se 3 (by rfl) ⟨470471, by rfl⟩ : syracuseStep 2509181 = 940943) (by norm_num)
theorem B5646725 : Blo 1672036 5646725 := bbase (se 4 (by rfl) ⟨529380, by rfl⟩ : syracuseStep 5646725 = 1058761) (by norm_num)
theorem B2509205 : Blo 1672036 2509205 := bbase (se 6 (by rfl) ⟨58809, by rfl⟩ : syracuseStep 2509205 = 117619) (by norm_num)
theorem B2681245 : Blo 1672036 2681245 := bbase (se 3 (by rfl) ⟨502733, by rfl⟩ : syracuseStep 2681245 = 1005467) (by norm_num)
theorem B2509229 : Blo 1672036 2509229 := bbase (se 3 (by rfl) ⟨470480, by rfl⟩ : syracuseStep 2509229 = 940961) (by norm_num)
theorem B3762629 : Blo 1672036 3762629 := bbase (se 4 (by rfl) ⟨352746, by rfl⟩ : syracuseStep 3762629 = 705493) (by norm_num)
theorem B2509253 : Blo 1672036 2509253 := bbase (se 4 (by rfl) ⟨235242, by rfl⟩ : syracuseStep 2509253 = 470485) (by norm_num)
theorem B6785477 : Blo 1672036 6785477 := bbase (se 4 (by rfl) ⟨636138, by rfl⟩ : syracuseStep 6785477 = 1272277) (by norm_num)
theorem B11446741 : Blo 1672036 11446741 := bbase (se 7 (by rfl) ⟨134141, by rfl⟩ : syracuseStep 11446741 = 268283) (by norm_num)
theorem B2509277 : Blo 1672036 2509277 := bbase (se 3 (by rfl) ⟨470489, by rfl⟩ : syracuseStep 2509277 = 940979) (by norm_num)
theorem B2509301 : Blo 1672036 2509301 := bbase (se 5 (by rfl) ⟨117623, by rfl⟩ : syracuseStep 2509301 = 235247) (by norm_num)
theorem B3762701 : Blo 1672036 3762701 := bbase (se 3 (by rfl) ⟨705506, by rfl⟩ : syracuseStep 3762701 = 1411013) (by norm_num)
theorem B2509325 : Blo 1672036 2509325 := bbase (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) (by norm_num)
theorem B2509349 : Blo 1672036 2509349 := bbase (se 4 (by rfl) ⟨235251, by rfl⟩ : syracuseStep 2509349 = 470503) (by norm_num)
theorem B2509373 : Blo 1672036 2509373 := bbase (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) (by norm_num)
theorem B3762773 : Blo 1672036 3762773 := bbase (se 8 (by rfl) ⟨22047, by rfl⟩ : syracuseStep 3762773 = 44095) (by norm_num)
theorem B2509397 : Blo 1672036 2509397 := bbase (se 8 (by rfl) ⟨14703, by rfl⟩ : syracuseStep 2509397 = 29407) (by norm_num)
theorem B2116201 : Blo 1672036 2116201 := bbase (se 2 (by rfl) ⟨793575, by rfl⟩ : syracuseStep 2116201 = 1587151) (by norm_num)
theorem B2509421 : Blo 1672036 2509421 := bbase (se 3 (by rfl) ⟨470516, by rfl⟩ : syracuseStep 2509421 = 941033) (by norm_num)
theorem B2509445 : Blo 1672036 2509445 := bbase (se 4 (by rfl) ⟨235260, by rfl⟩ : syracuseStep 2509445 = 470521) (by norm_num)
theorem B3762845 : Blo 1672036 3762845 := bbase (se 3 (by rfl) ⟨705533, by rfl⟩ : syracuseStep 3762845 = 1411067) (by norm_num)
theorem B2509469 : Blo 1672036 2509469 := bbase (se 3 (by rfl) ⟨470525, by rfl⟩ : syracuseStep 2509469 = 941051) (by norm_num)
theorem B2509493 : Blo 1672036 2509493 := bbase (se 5 (by rfl) ⟨117632, by rfl⟩ : syracuseStep 2509493 = 235265) (by norm_num)
theorem B2116297 : Blo 1672036 2116297 := bbase (se 2 (by rfl) ⟨793611, by rfl⟩ : syracuseStep 2116297 = 1587223) (by norm_num)
theorem B2509517 : Blo 1672036 2509517 := bbase (se 3 (by rfl) ⟨470534, by rfl⟩ : syracuseStep 2509517 = 941069) (by norm_num)
theorem B3762917 : Blo 1672036 3762917 := bbase (se 4 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 3762917 = 705547) (by norm_num)
theorem B2509541 : Blo 1672036 2509541 := bbase (se 4 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 2509541 = 470539) (by norm_num)
theorem B2509565 : Blo 1672036 2509565 := bbase (se 3 (by rfl) ⟨470543, by rfl⟩ : syracuseStep 2509565 = 941087) (by norm_num)
theorem B2509589 : Blo 1672036 2509589 := bbase (se 6 (by rfl) ⟨58818, by rfl⟩ : syracuseStep 2509589 = 117637) (by norm_num)
theorem B3762989 : Blo 1672036 3762989 := bbase (se 3 (by rfl) ⟨705560, by rfl⟩ : syracuseStep 3762989 = 1411121) (by norm_num)
theorem B2509613 : Blo 1672036 2509613 := bbase (se 3 (by rfl) ⟨470552, by rfl⟩ : syracuseStep 2509613 = 941105) (by norm_num)
theorem B4762421 : Blo 1672036 4762421 := bbase (se 5 (by rfl) ⟨223238, by rfl⟩ : syracuseStep 4762421 = 446477) (by norm_num)
theorem B5647157 : Blo 1672036 5647157 := bbase (se 5 (by rfl) ⟨264710, by rfl⟩ : syracuseStep 5647157 = 529421) (by norm_num)
theorem B2509637 : Blo 1672036 2509637 := bbase (se 4 (by rfl) ⟨235278, by rfl⟩ : syracuseStep 2509637 = 470557) (by norm_num)
theorem B2509661 : Blo 1672036 2509661 := bbase (se 3 (by rfl) ⟨470561, by rfl⟩ : syracuseStep 2509661 = 941123) (by norm_num)
theorem B2116469 : Blo 1672036 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B3763061 : Blo 1672036 3763061 := bbase (se 5 (by rfl) ⟨176393, by rfl⟩ : syracuseStep 3763061 = 352787) (by norm_num)
theorem B2509685 : Blo 1672036 2509685 := bbase (se 5 (by rfl) ⟨117641, by rfl⟩ : syracuseStep 2509685 = 235283) (by norm_num)
theorem B2509709 : Blo 1672036 2509709 := bbase (se 3 (by rfl) ⟨470570, by rfl⟩ : syracuseStep 2509709 = 941141) (by norm_num)
theorem B2509733 : Blo 1672036 2509733 := bbase (se 4 (by rfl) ⟨235287, by rfl⟩ : syracuseStep 2509733 = 470575) (by norm_num)
theorem B2116525 : Blo 1672036 2116525 := bbase (se 3 (by rfl) ⟨396848, by rfl⟩ : syracuseStep 2116525 = 793697) (by norm_num)
theorem B3763133 : Blo 1672036 3763133 := bbase (se 3 (by rfl) ⟨705587, by rfl⟩ : syracuseStep 3763133 = 1411175) (by norm_num)
theorem B2509757 : Blo 1672036 2509757 := bbase (se 3 (by rfl) ⟨470579, by rfl⟩ : syracuseStep 2509757 = 941159) (by norm_num)
theorem B2509781 : Blo 1672036 2509781 := bbase (se 7 (by rfl) ⟨29411, by rfl⟩ : syracuseStep 2509781 = 58823) (by norm_num)
theorem B2509805 : Blo 1672036 2509805 := bbase (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) (by norm_num)
theorem B3763205 : Blo 1672036 3763205 := bbase (se 4 (by rfl) ⟨352800, by rfl⟩ : syracuseStep 3763205 = 705601) (by norm_num)
theorem B2509829 : Blo 1672036 2509829 := bbase (se 4 (by rfl) ⟨235296, by rfl⟩ : syracuseStep 2509829 = 470593) (by norm_num)
theorem B2116621 : Blo 1672036 2116621 := bbase (se 3 (by rfl) ⟨396866, by rfl⟩ : syracuseStep 2116621 = 793733) (by norm_num)
theorem B2509853 : Blo 1672036 2509853 := bbase (se 3 (by rfl) ⟨470597, by rfl⟩ : syracuseStep 2509853 = 941195) (by norm_num)
theorem B2509877 : Blo 1672036 2509877 := bbase (se 5 (by rfl) ⟨117650, by rfl⟩ : syracuseStep 2509877 = 235301) (by norm_num)
theorem B3763277 : Blo 1672036 3763277 := bbase (se 3 (by rfl) ⟨705614, by rfl⟩ : syracuseStep 3763277 = 1411229) (by norm_num)
theorem B2509901 : Blo 1672036 2509901 := bbase (se 3 (by rfl) ⟨470606, by rfl⟩ : syracuseStep 2509901 = 941213) (by norm_num)
theorem B2509925 : Blo 1672036 2509925 := bbase (se 4 (by rfl) ⟨235305, by rfl⟩ : syracuseStep 2509925 = 470611) (by norm_num)
theorem B2509949 : Blo 1672036 2509949 := bbase (se 3 (by rfl) ⟨470615, by rfl⟩ : syracuseStep 2509949 = 941231) (by norm_num)
theorem B8473733 : Blo 1672036 8473733 := bbase (se 4 (by rfl) ⟨794412, by rfl⟩ : syracuseStep 8473733 = 1588825) (by norm_num)
theorem B3763349 : Blo 1672036 3763349 := bbase (se 6 (by rfl) ⟨88203, by rfl⟩ : syracuseStep 3763349 = 176407) (by norm_num)
theorem B2509973 : Blo 1672036 2509973 := bbase (se 6 (by rfl) ⟨58827, by rfl⟩ : syracuseStep 2509973 = 117655) (by norm_num)
theorem B2509997 : Blo 1672036 2509997 := bbase (se 3 (by rfl) ⟨470624, by rfl⟩ : syracuseStep 2509997 = 941249) (by norm_num)
theorem B2116793 : Blo 1672036 2116793 := bbase (se 2 (by rfl) ⟨793797, by rfl⟩ : syracuseStep 2116793 = 1587595) (by norm_num)
theorem B2510021 : Blo 1672036 2510021 := bbase (se 4 (by rfl) ⟨235314, by rfl⟩ : syracuseStep 2510021 = 470629) (by norm_num)
theorem B9530581 : Blo 1672036 9530581 := bbase (se 7 (by rfl) ⟨111686, by rfl⟩ : syracuseStep 9530581 = 223373) (by norm_num)
theorem B3763421 : Blo 1672036 3763421 := bbase (se 3 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 3763421 = 1411283) (by norm_num)
theorem B2510045 : Blo 1672036 2510045 := bbase (se 3 (by rfl) ⟨470633, by rfl⟩ : syracuseStep 2510045 = 941267) (by norm_num)
theorem B5647589 : Blo 1672036 5647589 := bbase (se 4 (by rfl) ⟨529461, by rfl⟩ : syracuseStep 5647589 = 1058923) (by norm_num)
theorem B2116849 : Blo 1672036 2116849 := bbase (se 2 (by rfl) ⟨793818, by rfl⟩ : syracuseStep 2116849 = 1587637) (by norm_num)
theorem B2510069 : Blo 1672036 2510069 := bbase (se 5 (by rfl) ⟨117659, by rfl⟩ : syracuseStep 2510069 = 235319) (by norm_num)
theorem B7630085 : Blo 1672036 7630085 := bbase (se 4 (by rfl) ⟨715320, by rfl⟩ : syracuseStep 7630085 = 1430641) (by norm_num)
theorem B2010377 : Blo 1672036 2010377 := bbase (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) (by norm_num)
theorem B2510093 : Blo 1672036 2510093 := bbase (se 3 (by rfl) ⟨470642, by rfl⟩ : syracuseStep 2510093 = 941285) (by norm_num)
theorem B12061973 : Blo 1672036 12061973 := bbase (se 6 (by rfl) ⟨282702, by rfl⟩ : syracuseStep 12061973 = 565405) (by norm_num)
theorem B3763493 : Blo 1672036 3763493 := bbase (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) (by norm_num)
theorem B2510117 : Blo 1672036 2510117 := bbase (se 4 (by rfl) ⟨235323, by rfl⟩ : syracuseStep 2510117 = 470647) (by norm_num)
theorem B2510141 : Blo 1672036 2510141 := bbase (se 3 (by rfl) ⟨470651, by rfl⟩ : syracuseStep 2510141 = 941303) (by norm_num)
theorem B4017485 : Blo 1672036 4017485 := bbase (se 3 (by rfl) ⟨753278, by rfl⟩ : syracuseStep 4017485 = 1506557) (by norm_num)
theorem B2116945 : Blo 1672036 2116945 := bbase (se 2 (by rfl) ⟨793854, by rfl⟩ : syracuseStep 2116945 = 1587709) (by norm_num)
theorem B2510165 : Blo 1672036 2510165 := bbase (se 11 (by rfl) ⟨1838, by rfl⟩ : syracuseStep 2510165 = 3677) (by norm_num)
theorem B3763565 : Blo 1672036 3763565 := bbase (se 3 (by rfl) ⟨705668, by rfl⟩ : syracuseStep 3763565 = 1411337) (by norm_num)
theorem B2510189 : Blo 1672036 2510189 := bbase (se 3 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 2510189 = 941321) (by norm_num)
theorem B2510213 : Blo 1672036 2510213 := bbase (se 4 (by rfl) ⟨235332, by rfl⟩ : syracuseStep 2510213 = 470665) (by norm_num)
theorem B6032789 : Blo 1672036 6032789 := bbase (se 6 (by rfl) ⟨141393, by rfl⟩ : syracuseStep 6032789 = 282787) (by norm_num)
theorem B2510237 : Blo 1672036 2510237 := bbase (se 3 (by rfl) ⟨470669, by rfl⟩ : syracuseStep 2510237 = 941339) (by norm_num)
theorem B3763637 : Blo 1672036 3763637 := bbase (se 5 (by rfl) ⟨176420, by rfl⟩ : syracuseStep 3763637 = 352841) (by norm_num)
theorem B2510261 : Blo 1672036 2510261 := bbase (se 5 (by rfl) ⟨117668, by rfl⟩ : syracuseStep 2510261 = 235337) (by norm_num)
theorem B2510285 : Blo 1672036 2510285 := bbase (se 3 (by rfl) ⟨470678, by rfl⟩ : syracuseStep 2510285 = 941357) (by norm_num)
theorem B2510309 : Blo 1672036 2510309 := bbase (se 4 (by rfl) ⟨235341, by rfl⟩ : syracuseStep 2510309 = 470683) (by norm_num)
theorem B2821621 : Blo 1672036 2821621 := bbase (se 5 (by rfl) ⟨132263, by rfl⟩ : syracuseStep 2821621 = 264527) (by norm_num)
theorem B2715125 : Blo 1672036 2715125 := bbase (se 5 (by rfl) ⟨127271, by rfl⟩ : syracuseStep 2715125 = 254543) (by norm_num)
theorem B3763709 : Blo 1672036 3763709 := bbase (se 3 (by rfl) ⟨705695, by rfl⟩ : syracuseStep 3763709 = 1411391) (by norm_num)
theorem B2117117 : Blo 1672036 2117117 := bbase (se 3 (by rfl) ⟨396959, by rfl⟩ : syracuseStep 2117117 = 793919) (by norm_num)
theorem B2510333 : Blo 1672036 2510333 := bbase (se 3 (by rfl) ⟨470687, by rfl⟩ : syracuseStep 2510333 = 941375) (by norm_num)
theorem B5361157 : Blo 1672036 5361157 := bbase (se 4 (by rfl) ⟨502608, by rfl⟩ : syracuseStep 5361157 = 1005217) (by norm_num)
theorem B2510357 : Blo 1672036 2510357 := bbase (se 6 (by rfl) ⟨58836, by rfl⟩ : syracuseStep 2510357 = 117673) (by norm_num)
theorem B6032917 : Blo 1672036 6032917 := bbase (se 6 (by rfl) ⟨141396, by rfl⟩ : syracuseStep 6032917 = 282793) (by norm_num)
theorem B8465957 : Blo 1672036 8465957 := bbase (se 4 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 8465957 = 1587367) (by norm_num)
theorem B2510381 : Blo 1672036 2510381 := bbase (se 3 (by rfl) ⟨470696, by rfl⟩ : syracuseStep 2510381 = 941393) (by norm_num)
theorem B2117173 : Blo 1672036 2117173 := bbase (se 5 (by rfl) ⟨99242, by rfl⟩ : syracuseStep 2117173 = 198485) (by norm_num)
theorem B2010685 : Blo 1672036 2010685 := bbase (se 3 (by rfl) ⟨377003, by rfl⟩ : syracuseStep 2010685 = 754007) (by norm_num)
theorem B3763781 : Blo 1672036 3763781 := bbase (se 4 (by rfl) ⟨352854, by rfl⟩ : syracuseStep 3763781 = 705709) (by norm_num)
theorem B2510405 : Blo 1672036 2510405 := bbase (se 4 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 2510405 = 470701) (by norm_num)
theorem B2821709 : Blo 1672036 2821709 := bbase (se 3 (by rfl) ⟨529070, by rfl⟩ : syracuseStep 2821709 = 1058141) (by norm_num)
theorem B3264077 : Blo 1672036 3264077 := bbase (se 3 (by rfl) ⟨612014, by rfl⟩ : syracuseStep 3264077 = 1224029) (by norm_num)
theorem B2510429 : Blo 1672036 2510429 := bbase (se 3 (by rfl) ⟨470705, by rfl⟩ : syracuseStep 2510429 = 941411) (by norm_num)
theorem B2510453 : Blo 1672036 2510453 := bbase (se 5 (by rfl) ⟨117677, by rfl⟩ : syracuseStep 2510453 = 235355) (by norm_num)
theorem B3763853 : Blo 1672036 3763853 := bbase (se 3 (by rfl) ⟨705722, by rfl⟩ : syracuseStep 3763853 = 1411445) (by norm_num)
theorem B2510477 : Blo 1672036 2510477 := bbase (se 3 (by rfl) ⟨470714, by rfl⟩ : syracuseStep 2510477 = 941429) (by norm_num)
theorem B2117269 : Blo 1672036 2117269 := bbase (se 6 (by rfl) ⟨49623, by rfl⟩ : syracuseStep 2117269 = 99247) (by norm_num)
theorem B5648021 : Blo 1672036 5648021 := bbase (se 6 (by rfl) ⟨132375, by rfl⟩ : syracuseStep 5648021 = 264751) (by norm_num)
theorem B2510501 : Blo 1672036 2510501 := bbase (se 4 (by rfl) ⟨235359, by rfl⟩ : syracuseStep 2510501 = 470719) (by norm_num)
theorem B4411061 : Blo 1672036 4411061 := bbase (se 5 (by rfl) ⟨206768, by rfl⟩ : syracuseStep 4411061 = 413537) (by norm_num)
theorem B3534517 : Blo 1672036 3534517 := bbase (se 5 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 3534517 = 331361) (by norm_num)
theorem B2510525 : Blo 1672036 2510525 := bbase (se 3 (by rfl) ⟨470723, by rfl⟩ : syracuseStep 2510525 = 941447) (by norm_num)
theorem B2821837 : Blo 1672036 2821837 := bbase (se 3 (by rfl) ⟨529094, by rfl⟩ : syracuseStep 2821837 = 1058189) (by norm_num)
theorem B3763925 : Blo 1672036 3763925 := bbase (se 7 (by rfl) ⟨44108, by rfl⟩ : syracuseStep 3763925 = 88217) (by norm_num)
theorem B2510549 : Blo 1672036 2510549 := bbase (se 7 (by rfl) ⟨29420, by rfl⟩ : syracuseStep 2510549 = 58841) (by norm_num)
theorem B6786773 : Blo 1672036 6786773 := bbase (se 7 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 6786773 = 159065) (by norm_num)
theorem B6352613 : Blo 1672036 6352613 := bbase (se 4 (by rfl) ⟨595557, by rfl⟩ : syracuseStep 6352613 = 1191115) (by norm_num)
theorem B7147237 : Blo 1672036 7147237 := bbase (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) (by norm_num)
theorem B2010853 : Blo 1672036 2010853 := bbase (se 4 (by rfl) ⟨188517, by rfl⟩ : syracuseStep 2010853 = 377035) (by norm_num)
theorem B2510573 : Blo 1672036 2510573 := bbase (se 3 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 2510573 = 941465) (by norm_num)
theorem B7147253 : Blo 1672036 7147253 := bbase (se 5 (by rfl) ⟨335027, by rfl⟩ : syracuseStep 7147253 = 670055) (by norm_num)
theorem B2510597 : Blo 1672036 2510597 := bbase (se 4 (by rfl) ⟨235368, by rfl⟩ : syracuseStep 2510597 = 470737) (by norm_num)
theorem B3763997 : Blo 1672036 3763997 := bbase (se 3 (by rfl) ⟨705749, by rfl⟩ : syracuseStep 3763997 = 1411499) (by norm_num)
theorem B2510621 : Blo 1672036 2510621 := bbase (se 3 (by rfl) ⟨470741, by rfl⟩ : syracuseStep 2510621 = 941483) (by norm_num)
theorem B2821925 : Blo 1672036 2821925 := bbase (se 4 (by rfl) ⟨264555, by rfl⟩ : syracuseStep 2821925 = 529111) (by norm_num)
theorem B2510645 : Blo 1672036 2510645 := bbase (se 5 (by rfl) ⟨117686, by rfl⟩ : syracuseStep 2510645 = 235373) (by norm_num)
theorem B2117441 : Blo 1672036 2117441 := bbase (se 2 (by rfl) ⟨794040, by rfl⟩ : syracuseStep 2117441 = 1588081) (by norm_num)
theorem B2510669 : Blo 1672036 2510669 := bbase (se 3 (by rfl) ⟨470750, by rfl⟩ : syracuseStep 2510669 = 941501) (by norm_num)
theorem B3764069 : Blo 1672036 3764069 := bbase (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) (by norm_num)
theorem B2510693 : Blo 1672036 2510693 := bbase (se 4 (by rfl) ⟨235377, by rfl⟩ : syracuseStep 2510693 = 470755) (by norm_num)
theorem B2117497 : Blo 1672036 2117497 := bbase (se 2 (by rfl) ⟨794061, by rfl⟩ : syracuseStep 2117497 = 1588123) (by norm_num)
theorem B2510717 : Blo 1672036 2510717 := bbase (se 3 (by rfl) ⟨470759, by rfl⟩ : syracuseStep 2510717 = 941519) (by norm_num)
theorem B2510741 : Blo 1672036 2510741 := bbase (se 6 (by rfl) ⟨58845, by rfl⟩ : syracuseStep 2510741 = 117691) (by norm_num)
theorem B2822053 : Blo 1672036 2822053 := bbase (se 4 (by rfl) ⟨264567, by rfl⟩ : syracuseStep 2822053 = 529135) (by norm_num)
theorem B2011049 : Blo 1672036 2011049 := bbase (se 2 (by rfl) ⟨754143, by rfl⟩ : syracuseStep 2011049 = 1508287) (by norm_num)
theorem B3764141 : Blo 1672036 3764141 := bbase (se 3 (by rfl) ⟨705776, by rfl⟩ : syracuseStep 3764141 = 1411553) (by norm_num)
theorem B2510765 : Blo 1672036 2510765 := bbase (se 3 (by rfl) ⟨470768, by rfl⟩ : syracuseStep 2510765 = 941537) (by norm_num)
theorem B2510789 : Blo 1672036 2510789 := bbase (se 4 (by rfl) ⟨235386, by rfl⟩ : syracuseStep 2510789 = 470773) (by norm_num)
theorem B4763605 : Blo 1672036 4763605 := bbase (se 7 (by rfl) ⟨55823, by rfl⟩ : syracuseStep 4763605 = 111647) (by norm_num)
theorem B2117593 : Blo 1672036 2117593 := bbase (se 2 (by rfl) ⟨794097, by rfl⟩ : syracuseStep 2117593 = 1588195) (by norm_num)
theorem B2510813 : Blo 1672036 2510813 := bbase (se 3 (by rfl) ⟨470777, by rfl⟩ : syracuseStep 2510813 = 941555) (by norm_num)
theorem B2543605 : Blo 1672036 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B3764213 : Blo 1672036 3764213 := bbase (se 5 (by rfl) ⟨176447, by rfl⟩ : syracuseStep 3764213 = 352895) (by norm_num)
theorem B2510837 : Blo 1672036 2510837 := bbase (se 5 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 2510837 = 235391) (by norm_num)
theorem B2822141 : Blo 1672036 2822141 := bbase (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) (by norm_num)
theorem B6352901 : Blo 1672036 6352901 := bbase (se 4 (by rfl) ⟨595584, by rfl⟩ : syracuseStep 6352901 = 1191169) (by norm_num)
theorem B2510861 : Blo 1672036 2510861 := bbase (se 3 (by rfl) ⟨470786, by rfl⟩ : syracuseStep 2510861 = 941573) (by norm_num)
theorem B2510885 : Blo 1672036 2510885 := bbase (se 4 (by rfl) ⟨235395, by rfl⟩ : syracuseStep 2510885 = 470791) (by norm_num)
theorem B3174461 : Blo 1672036 3174461 := bbase (se 3 (by rfl) ⟨595211, by rfl⟩ : syracuseStep 3174461 = 1190423) (by norm_num)
theorem B3764285 : Blo 1672036 3764285 := bbase (se 3 (by rfl) ⟨705803, by rfl⟩ : syracuseStep 3764285 = 1411607) (by norm_num)
theorem B2510909 : Blo 1672036 2510909 := bbase (se 3 (by rfl) ⟨470795, by rfl⟩ : syracuseStep 2510909 = 941591) (by norm_num)
theorem B5648453 : Blo 1672036 5648453 := bbase (se 4 (by rfl) ⟨529542, by rfl⟩ : syracuseStep 5648453 = 1059085) (by norm_num)
theorem B2510933 : Blo 1672036 2510933 := bbase (se 8 (by rfl) ⟨14712, by rfl⟩ : syracuseStep 2510933 = 29425) (by norm_num)
theorem B2510957 : Blo 1672036 2510957 := bbase (se 3 (by rfl) ⟨470804, by rfl⟩ : syracuseStep 2510957 = 941609) (by norm_num)
theorem B4763765 : Blo 1672036 4763765 := bbase (se 5 (by rfl) ⟨223301, by rfl⟩ : syracuseStep 4763765 = 446603) (by norm_num)
theorem B2822269 : Blo 1672036 2822269 := bbase (se 3 (by rfl) ⟨529175, by rfl⟩ : syracuseStep 2822269 = 1058351) (by norm_num)
theorem B3764357 : Blo 1672036 3764357 := bbase (se 4 (by rfl) ⟨352908, by rfl⟩ : syracuseStep 3764357 = 705817) (by norm_num)
theorem B2117765 : Blo 1672036 2117765 := bbase (se 4 (by rfl) ⟨198540, by rfl⟩ : syracuseStep 2117765 = 397081) (by norm_num)
theorem B2510981 : Blo 1672036 2510981 := bbase (se 4 (by rfl) ⟨235404, by rfl⟩ : syracuseStep 2510981 = 470809) (by norm_num)
theorem B2511005 : Blo 1672036 2511005 := bbase (se 3 (by rfl) ⟨470813, by rfl⟩ : syracuseStep 2511005 = 941627) (by norm_num)
theorem B2511029 : Blo 1672036 2511029 := bbase (se 5 (by rfl) ⟨117704, by rfl⟩ : syracuseStep 2511029 = 235409) (by norm_num)
theorem B2117821 : Blo 1672036 2117821 := bbase (se 3 (by rfl) ⟨397091, by rfl⟩ : syracuseStep 2117821 = 794183) (by norm_num)
theorem B3764429 : Blo 1672036 3764429 := bbase (se 3 (by rfl) ⟨705830, by rfl⟩ : syracuseStep 3764429 = 1411661) (by norm_num)
theorem B2511053 : Blo 1672036 2511053 := bbase (se 3 (by rfl) ⟨470822, by rfl⟩ : syracuseStep 2511053 = 941645) (by norm_num)
theorem B2822357 : Blo 1672036 2822357 := bbase (se 7 (by rfl) ⟨33074, by rfl⟩ : syracuseStep 2822357 = 66149) (by norm_num)
theorem B3764501 : Blo 1672036 3764501 := bbase (se 6 (by rfl) ⟨88230, by rfl⟩ : syracuseStep 3764501 = 176461) (by norm_num)
theorem B2117917 : Blo 1672036 2117917 := bbase (se 3 (by rfl) ⟨397109, by rfl⟩ : syracuseStep 2117917 = 794219) (by norm_num)
theorem B2822485 : Blo 1672036 2822485 := bbase (se 10 (by rfl) ⟨4134, by rfl⟩ : syracuseStep 2822485 = 8269) (by norm_num)
theorem B3764573 : Blo 1672036 3764573 := bbase (se 3 (by rfl) ⟨705857, by rfl⟩ : syracuseStep 3764573 = 1411715) (by norm_num)
theorem B4764005 : Blo 1672036 4764005 := bbase (se 4 (by rfl) ⟨446625, by rfl⟩ : syracuseStep 4764005 = 893251) (by norm_num)
theorem B3764645 : Blo 1672036 3764645 := bbase (se 4 (by rfl) ⟨352935, by rfl⟩ : syracuseStep 3764645 = 705871) (by norm_num)
theorem B2822573 : Blo 1672036 2822573 := bbase (se 3 (by rfl) ⟨529232, by rfl⟩ : syracuseStep 2822573 = 1058465) (by norm_num)
theorem B2118089 : Blo 1672036 2118089 := bbase (se 2 (by rfl) ⟨794283, by rfl⟩ : syracuseStep 2118089 = 1588567) (by norm_num)
theorem B12710357 : Blo 1672036 12710357 := bbase (se 7 (by rfl) ⟨148949, by rfl⟩ : syracuseStep 12710357 = 297899) (by norm_num)
theorem B3764717 : Blo 1672036 3764717 := bbase (se 3 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 3764717 = 1411769) (by norm_num)
theorem B5648885 : Blo 1672036 5648885 := bbase (se 5 (by rfl) ⟨264791, by rfl⟩ : syracuseStep 5648885 = 529583) (by norm_num)
theorem B2118145 : Blo 1672036 2118145 := bbase (se 2 (by rfl) ⟨794304, by rfl⟩ : syracuseStep 2118145 = 1588609) (by norm_num)
theorem B4764197 : Blo 1672036 4764197 := bbase (se 4 (by rfl) ⟨446643, by rfl⟩ : syracuseStep 4764197 = 893287) (by norm_num)
theorem B2822701 : Blo 1672036 2822701 := bbase (se 3 (by rfl) ⟨529256, by rfl⟩ : syracuseStep 2822701 = 1058513) (by norm_num)
theorem B3764789 : Blo 1672036 3764789 := bbase (se 5 (by rfl) ⟨176474, by rfl⟩ : syracuseStep 3764789 = 352949) (by norm_num)
theorem B2036305 : Blo 1672036 2036305 := bbase (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) (by norm_num)
theorem B8041045 : Blo 1672036 8041045 := bbase (se 8 (by rfl) ⟨47115, by rfl⟩ : syracuseStep 8041045 = 94231) (by norm_num)
theorem B2118241 : Blo 1672036 2118241 := bbase (se 2 (by rfl) ⟨794340, by rfl⟩ : syracuseStep 2118241 = 1588681) (by norm_num)
theorem B3764861 : Blo 1672036 3764861 := bbase (se 3 (by rfl) ⟨705911, by rfl⟩ : syracuseStep 3764861 = 1411823) (by norm_num)
theorem B2822789 : Blo 1672036 2822789 := bbase (se 4 (by rfl) ⟨264636, by rfl⟩ : syracuseStep 2822789 = 529273) (by norm_num)
theorem B5722757 : Blo 1672036 5722757 := bbase (se 4 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 5722757 = 1073017) (by norm_num)
theorem B15463061 : Blo 1672036 15463061 := bbase (se 6 (by rfl) ⟨362415, by rfl⟩ : syracuseStep 15463061 = 724831) (by norm_num)
theorem B3764933 : Blo 1672036 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B2413261 : Blo 1672036 2413261 := bbase (se 3 (by rfl) ⟨452486, by rfl⟩ : syracuseStep 2413261 = 904973) (by norm_num)
theorem B4018909 : Blo 1672036 4018909 := bbase (se 3 (by rfl) ⟨753545, by rfl⟩ : syracuseStep 4018909 = 1507091) (by norm_num)
theorem B14480117 : Blo 1672036 14480117 := bbase (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) (by norm_num)
theorem B2822917 : Blo 1672036 2822917 := bbase (se 4 (by rfl) ⟨264648, by rfl⟩ : syracuseStep 2822917 = 529297) (by norm_num)
theorem B3765005 : Blo 1672036 3765005 := bbase (se 3 (by rfl) ⟨705938, by rfl⟩ : syracuseStep 3765005 = 1411877) (by norm_num)
theorem B2118413 : Blo 1672036 2118413 := bbase (se 3 (by rfl) ⟨397202, by rfl⟩ : syracuseStep 2118413 = 794405) (by norm_num)
theorem B2036497 : Blo 1672036 2036497 := bbase (se 2 (by rfl) ⟨763686, by rfl⟩ : syracuseStep 2036497 = 1527373) (by norm_num)
theorem B3175213 : Blo 1672036 3175213 := bbase (se 3 (by rfl) ⟨595352, by rfl⟩ : syracuseStep 3175213 = 1190705) (by norm_num)
theorem B8467253 : Blo 1672036 8467253 := bbase (se 5 (by rfl) ⟨396902, by rfl⟩ : syracuseStep 8467253 = 793805) (by norm_num)
theorem B2118469 : Blo 1672036 2118469 := bbase (se 4 (by rfl) ⟨198606, by rfl⟩ : syracuseStep 2118469 = 397213) (by norm_num)
theorem B3765077 : Blo 1672036 3765077 := bbase (se 9 (by rfl) ⟨11030, by rfl⟩ : syracuseStep 3765077 = 22061) (by norm_num)
theorem B5362517 : Blo 1672036 5362517 := bbase (se 9 (by rfl) ⟨15710, by rfl⟩ : syracuseStep 5362517 = 31421) (by norm_num)
theorem B2823005 : Blo 1672036 2823005 := bbase (se 3 (by rfl) ⟨529313, by rfl⟩ : syracuseStep 2823005 = 1058627) (by norm_num)
theorem B12702581 : Blo 1672036 12702581 := bbase (se 5 (by rfl) ⟨595433, by rfl⟩ : syracuseStep 12702581 = 1190867) (by norm_num)
theorem B7246709 : Blo 1672036 7246709 := bbase (se 5 (by rfl) ⟨339689, by rfl⟩ : syracuseStep 7246709 = 679379) (by norm_num)
theorem B7631765 : Blo 1672036 7631765 := bbase (se 6 (by rfl) ⟨178869, by rfl⟩ : syracuseStep 7631765 = 357739) (by norm_num)
theorem B3765149 : Blo 1672036 3765149 := bbase (se 3 (by rfl) ⟨705965, by rfl⟩ : syracuseStep 3765149 = 1411931) (by norm_num)
theorem B2380709 : Blo 1672036 2380709 := bbase (se 4 (by rfl) ⟨223191, by rfl⟩ : syracuseStep 2380709 = 446383) (by norm_num)
theorem B5649317 : Blo 1672036 5649317 := bbase (se 4 (by rfl) ⟨529623, by rfl⟩ : syracuseStep 5649317 = 1059247) (by norm_num)
theorem B2118565 : Blo 1672036 2118565 := bbase (se 4 (by rfl) ⟨198615, by rfl⟩ : syracuseStep 2118565 = 397231) (by norm_num)
theorem B3175357 : Blo 1672036 3175357 := bbase (se 3 (by rfl) ⟨595379, by rfl⟩ : syracuseStep 3175357 = 1190759) (by norm_num)
theorem B5362645 : Blo 1672036 5362645 := bbase (se 7 (by rfl) ⟨62843, by rfl⟩ : syracuseStep 5362645 = 125687) (by norm_num)
theorem B1881049 : Blo 1672036 1881049 := bbase (se 2 (by rfl) ⟨705393, by rfl⟩ : syracuseStep 1881049 = 1410787) (by norm_num)
theorem B2823133 : Blo 1672036 2823133 := bbase (se 3 (by rfl) ⟨529337, by rfl⟩ : syracuseStep 2823133 = 1058675) (by norm_num)
theorem B3765221 : Blo 1672036 3765221 := bbase (se 4 (by rfl) ⟨352989, by rfl⟩ : syracuseStep 3765221 = 705979) (by norm_num)
theorem B2380789 : Blo 1672036 2380789 := bbase (se 5 (by rfl) ⟨111599, by rfl⟩ : syracuseStep 2380789 = 223199) (by norm_num)
theorem B1881085 : Blo 1672036 1881085 := bbase (se 3 (by rfl) ⟨352703, by rfl⟩ : syracuseStep 1881085 = 705407) (by norm_num)
theorem B8582165 : Blo 1672036 8582165 := bbase (se 6 (by rfl) ⟨201144, by rfl⟩ : syracuseStep 8582165 = 402289) (by norm_num)
theorem B1881121 : Blo 1672036 1881121 := bbase (se 2 (by rfl) ⟨705420, by rfl⟩ : syracuseStep 1881121 = 1410841) (by norm_num)
theorem B2036773 : Blo 1672036 2036773 := bbase (se 4 (by rfl) ⟨190947, by rfl⟩ : syracuseStep 2036773 = 381895) (by norm_num)
theorem B3765293 : Blo 1672036 3765293 := bbase (se 3 (by rfl) ⟨705992, by rfl⟩ : syracuseStep 3765293 = 1411985) (by norm_num)
theorem B2823221 : Blo 1672036 2823221 := bbase (se 5 (by rfl) ⟨132338, by rfl⟩ : syracuseStep 2823221 = 264677) (by norm_num)
theorem B1881157 : Blo 1672036 1881157 := bbase (se 4 (by rfl) ⟨176358, by rfl⟩ : syracuseStep 1881157 = 352717) (by norm_num)
theorem B3175517 : Blo 1672036 3175517 := bbase (se 3 (by rfl) ⟨595409, by rfl⟩ : syracuseStep 3175517 = 1190819) (by norm_num)
theorem B1881193 : Blo 1672036 1881193 := bbase (se 2 (by rfl) ⟨705447, by rfl⟩ : syracuseStep 1881193 = 1410895) (by norm_num)
theorem B2380909 : Blo 1672036 2380909 := bbase (se 3 (by rfl) ⟨446420, by rfl⟩ : syracuseStep 2380909 = 892841) (by norm_num)
theorem B3765365 : Blo 1672036 3765365 := bbase (se 5 (by rfl) ⟨176501, by rfl⟩ : syracuseStep 3765365 = 353003) (by norm_num)
theorem B1881229 : Blo 1672036 1881229 := bbase (se 3 (by rfl) ⟨352730, by rfl⟩ : syracuseStep 1881229 = 705461) (by norm_num)
theorem B9532565 : Blo 1672036 9532565 := bbase (se 6 (by rfl) ⟨223419, by rfl⟩ : syracuseStep 9532565 = 446839) (by norm_num)
theorem B6354085 : Blo 1672036 6354085 := bbase (se 4 (by rfl) ⟨595695, by rfl⟩ : syracuseStep 6354085 = 1191391) (by norm_num)
theorem B1881265 : Blo 1672036 1881265 := bbase (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) (by norm_num)
theorem B2823349 : Blo 1672036 2823349 := bbase (se 5 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 2823349 = 264689) (by norm_num)
theorem B3765437 : Blo 1672036 3765437 := bbase (se 3 (by rfl) ⟨706019, by rfl⟩ : syracuseStep 3765437 = 1412039) (by norm_num)
theorem B2381005 : Blo 1672036 2381005 := bbase (se 3 (by rfl) ⟨446438, by rfl⟩ : syracuseStep 2381005 = 892877) (by norm_num)
theorem B1881301 : Blo 1672036 1881301 := bbase (se 7 (by rfl) ⟨22046, by rfl⟩ : syracuseStep 1881301 = 44093) (by norm_num)
theorem B5362901 : Blo 1672036 5362901 := bbase (se 7 (by rfl) ⟨62846, by rfl⟩ : syracuseStep 5362901 = 125693) (by norm_num)
theorem B3175661 : Blo 1672036 3175661 := bbase (se 3 (by rfl) ⟨595436, by rfl⟩ : syracuseStep 3175661 = 1190873) (by norm_num)
theorem B1881337 : Blo 1672036 1881337 := bbase (se 2 (by rfl) ⟨705501, by rfl⟩ : syracuseStep 1881337 = 1411003) (by norm_num)
theorem B3765509 : Blo 1672036 3765509 := bbase (se 4 (by rfl) ⟨353016, by rfl⟩ : syracuseStep 3765509 = 706033) (by norm_num)
theorem B2823437 : Blo 1672036 2823437 := bbase (se 3 (by rfl) ⟨529394, by rfl⟩ : syracuseStep 2823437 = 1058789) (by norm_num)
theorem B1881373 : Blo 1672036 1881373 := bbase (se 3 (by rfl) ⟨352757, by rfl⟩ : syracuseStep 1881373 = 705515) (by norm_num)
theorem B2176313 : Blo 1672036 2176313 := bbase (se 2 (by rfl) ⟨816117, by rfl⟩ : syracuseStep 2176313 = 1632235) (by norm_num)
theorem B1881409 : Blo 1672036 1881409 := bbase (se 2 (by rfl) ⟨705528, by rfl⟩ : syracuseStep 1881409 = 1411057) (by norm_num)
theorem B3765581 : Blo 1672036 3765581 := bbase (se 3 (by rfl) ⟨706046, by rfl⟩ : syracuseStep 3765581 = 1412093) (by norm_num)
theorem B4232533 : Blo 1672036 4232533 := bbase (se 14 (by rfl) ⟨387, by rfl⟩ : syracuseStep 4232533 = 775) (by norm_num)
theorem B5649749 : Blo 1672036 5649749 := bbase (se 13 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 5649749 = 2069) (by norm_num)
theorem B1881445 : Blo 1672036 1881445 := bbase (se 4 (by rfl) ⟨176385, by rfl⟩ : syracuseStep 1881445 = 352771) (by norm_num)
theorem B4019581 : Blo 1672036 4019581 := bbase (se 3 (by rfl) ⟨753671, by rfl⟩ : syracuseStep 4019581 = 1507343) (by norm_num)
theorem B1881481 : Blo 1672036 1881481 := bbase (se 2 (by rfl) ⟨705555, by rfl⟩ : syracuseStep 1881481 = 1411111) (by norm_num)
theorem B2823565 : Blo 1672036 2823565 := bbase (se 3 (by rfl) ⟨529418, by rfl⟩ : syracuseStep 2823565 = 1058837) (by norm_num)
theorem B3765653 : Blo 1672036 3765653 := bbase (se 6 (by rfl) ⟨88257, by rfl⟩ : syracuseStep 3765653 = 176515) (by norm_num)
theorem B1881517 : Blo 1672036 1881517 := bbase (se 3 (by rfl) ⟨352784, by rfl⟩ : syracuseStep 1881517 = 705569) (by norm_num)
theorem B4232645 : Blo 1672036 4232645 := bbase (se 4 (by rfl) ⟨396810, by rfl⟩ : syracuseStep 4232645 = 793621) (by norm_num)
theorem B1881553 : Blo 1672036 1881553 := bbase (se 2 (by rfl) ⟨705582, by rfl⟩ : syracuseStep 1881553 = 1411165) (by norm_num)
theorem B6354389 : Blo 1672036 6354389 := bbase (se 7 (by rfl) ⟨74465, by rfl⟩ : syracuseStep 6354389 = 148931) (by norm_num)
theorem B3765725 : Blo 1672036 3765725 := bbase (se 3 (by rfl) ⟨706073, by rfl⟩ : syracuseStep 3765725 = 1412147) (by norm_num)
theorem B2823653 : Blo 1672036 2823653 := bbase (se 4 (by rfl) ⟨264717, by rfl⟩ : syracuseStep 2823653 = 529435) (by norm_num)
theorem B1881589 : Blo 1672036 1881589 := bbase (se 5 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 1881589 = 176399) (by norm_num)
theorem B4765189 : Blo 1672036 4765189 := bbase (se 4 (by rfl) ⟨446736, by rfl⟩ : syracuseStep 4765189 = 893473) (by norm_num)
theorem B3175949 : Blo 1672036 3175949 := bbase (se 3 (by rfl) ⟨595490, by rfl⟩ : syracuseStep 3175949 = 1190981) (by norm_num)
theorem B3814933 : Blo 1672036 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B1881625 : Blo 1672036 1881625 := bbase (se 2 (by rfl) ⟨705609, by rfl⟩ : syracuseStep 1881625 = 1411219) (by norm_num)
theorem B3765797 : Blo 1672036 3765797 := bbase (se 4 (by rfl) ⟨353043, by rfl⟩ : syracuseStep 3765797 = 706087) (by norm_num)
theorem B1881661 : Blo 1672036 1881661 := bbase (se 3 (by rfl) ⟨352811, by rfl⟩ : syracuseStep 1881661 = 705623) (by norm_num)
theorem B1881697 : Blo 1672036 1881697 := bbase (se 2 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 1881697 = 1411273) (by norm_num)
theorem B4019813 : Blo 1672036 4019813 := bbase (se 4 (by rfl) ⟨376857, by rfl⟩ : syracuseStep 4019813 = 753715) (by norm_num)
theorem B2823781 : Blo 1672036 2823781 := bbase (se 4 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 2823781 = 529459) (by norm_num)
theorem B3765869 : Blo 1672036 3765869 := bbase (se 3 (by rfl) ⟨706100, by rfl⟩ : syracuseStep 3765869 = 1412201) (by norm_num)
theorem B4232837 : Blo 1672036 4232837 := bbase (se 4 (by rfl) ⟨396828, by rfl⟩ : syracuseStep 4232837 = 793657) (by norm_num)
theorem B1881733 : Blo 1672036 1881733 := bbase (se 4 (by rfl) ⟨176412, by rfl⟩ : syracuseStep 1881733 = 352825) (by norm_num)
theorem B4019861 : Blo 1672036 4019861 := bbase (se 6 (by rfl) ⟨94215, by rfl⟩ : syracuseStep 4019861 = 188431) (by norm_num)
theorem B3176101 : Blo 1672036 3176101 := bbase (se 4 (by rfl) ⟨297759, by rfl⟩ : syracuseStep 3176101 = 595519) (by norm_num)
theorem B1881769 : Blo 1672036 1881769 := bbase (se 2 (by rfl) ⟨705663, by rfl⟩ : syracuseStep 1881769 = 1411327) (by norm_num)
theorem B3765941 : Blo 1672036 3765941 := bbase (se 5 (by rfl) ⟨176528, by rfl⟩ : syracuseStep 3765941 = 353057) (by norm_num)
theorem B2381501 : Blo 1672036 2381501 := bbase (se 3 (by rfl) ⟨446531, by rfl⟩ : syracuseStep 2381501 = 893063) (by norm_num)
theorem B2823869 : Blo 1672036 2823869 := bbase (se 3 (by rfl) ⟨529475, by rfl⟩ : syracuseStep 2823869 = 1058951) (by norm_num)
theorem B1881805 : Blo 1672036 1881805 := bbase (se 3 (by rfl) ⟨352838, by rfl⟩ : syracuseStep 1881805 = 705677) (by norm_num)
theorem B1881841 : Blo 1672036 1881841 := bbase (se 2 (by rfl) ⟨705690, by rfl⟩ : syracuseStep 1881841 = 1411381) (by norm_num)
theorem B3766013 : Blo 1672036 3766013 := bbase (se 3 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 3766013 = 1412255) (by norm_num)
theorem B1881877 : Blo 1672036 1881877 := bbase (se 6 (by rfl) ⟨44106, by rfl⟩ : syracuseStep 1881877 = 88213) (by norm_num)
theorem B1881913 : Blo 1672036 1881913 := bbase (se 2 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 1881913 = 1411435) (by norm_num)
theorem B2823997 : Blo 1672036 2823997 := bbase (se 3 (by rfl) ⟨529499, by rfl⟩ : syracuseStep 2823997 = 1058999) (by norm_num)
theorem B3766085 : Blo 1672036 3766085 := bbase (se 4 (by rfl) ⟨353070, by rfl⟩ : syracuseStep 3766085 = 706141) (by norm_num)
theorem B1881949 : Blo 1672036 1881949 := bbase (se 3 (by rfl) ⟨352865, by rfl⟩ : syracuseStep 1881949 = 705731) (by norm_num)
theorem B1881985 : Blo 1672036 1881985 := bbase (se 2 (by rfl) ⟨705744, by rfl⟩ : syracuseStep 1881985 = 1411489) (by norm_num)
theorem B3766157 : Blo 1672036 3766157 := bbase (se 3 (by rfl) ⟨706154, by rfl⟩ : syracuseStep 3766157 = 1412309) (by norm_num)
theorem B2824085 : Blo 1672036 2824085 := bbase (se 6 (by rfl) ⟨66189, by rfl⟩ : syracuseStep 2824085 = 132379) (by norm_num)
theorem B1882021 : Blo 1672036 1882021 := bbase (se 4 (by rfl) ⟨176439, by rfl⟩ : syracuseStep 1882021 = 352879) (by norm_num)
theorem B7149509 : Blo 1672036 7149509 := bbase (se 4 (by rfl) ⟨670266, by rfl⟩ : syracuseStep 7149509 = 1340533) (by norm_num)
theorem B1882057 : Blo 1672036 1882057 := bbase (se 2 (by rfl) ⟨705771, by rfl⟩ : syracuseStep 1882057 = 1411543) (by norm_num)
theorem B3176405 : Blo 1672036 3176405 := bbase (se 7 (by rfl) ⟨37223, by rfl⟩ : syracuseStep 3176405 = 74447) (by norm_num)
theorem B3766229 : Blo 1672036 3766229 := bbase (se 7 (by rfl) ⟨44135, by rfl⟩ : syracuseStep 3766229 = 88271) (by norm_num)
theorem B4233181 : Blo 1672036 4233181 := bbase (se 3 (by rfl) ⟨793721, by rfl⟩ : syracuseStep 4233181 = 1587443) (by norm_num)
theorem B1882093 : Blo 1672036 1882093 := bbase (se 3 (by rfl) ⟨352892, by rfl⟩ : syracuseStep 1882093 = 705785) (by norm_num)
theorem B1882129 : Blo 1672036 1882129 := bbase (se 2 (by rfl) ⟨705798, by rfl⟩ : syracuseStep 1882129 = 1411597) (by norm_num)
theorem B1906709 : Blo 1672036 1906709 := bbase (se 6 (by rfl) ⟨44688, by rfl⟩ : syracuseStep 1906709 = 89377) (by norm_num)
theorem B2824213 : Blo 1672036 2824213 := bbase (se 6 (by rfl) ⟨66192, by rfl⟩ : syracuseStep 2824213 = 132385) (by norm_num)
theorem B3766301 : Blo 1672036 3766301 := bbase (se 3 (by rfl) ⟨706181, by rfl⟩ : syracuseStep 3766301 = 1412363) (by norm_num)
theorem B1882165 : Blo 1672036 1882165 := bbase (se 5 (by rfl) ⟨88226, by rfl⟩ : syracuseStep 1882165 = 176453) (by norm_num)
theorem B8468549 : Blo 1672036 8468549 := bbase (se 4 (by rfl) ⟨793926, by rfl⟩ : syracuseStep 8468549 = 1587853) (by norm_num)
theorem B4233293 : Blo 1672036 4233293 := bbase (se 3 (by rfl) ⟨793742, by rfl⟩ : syracuseStep 4233293 = 1587485) (by norm_num)
theorem B1882201 : Blo 1672036 1882201 := bbase (se 2 (by rfl) ⟨705825, by rfl⟩ : syracuseStep 1882201 = 1411651) (by norm_num)
theorem B3766373 : Blo 1672036 3766373 := bbase (se 4 (by rfl) ⟨353097, by rfl⟩ : syracuseStep 3766373 = 706195) (by norm_num)
theorem B2824301 : Blo 1672036 2824301 := bbase (se 3 (by rfl) ⟨529556, by rfl⟩ : syracuseStep 2824301 = 1059113) (by norm_num)
theorem B1882237 : Blo 1672036 1882237 := bbase (se 3 (by rfl) ⟨352919, by rfl⟩ : syracuseStep 1882237 = 705839) (by norm_num)
theorem B1718425 : Blo 1672036 1718425 := bbase (se 2 (by rfl) ⟨644409, by rfl⟩ : syracuseStep 1718425 = 1288819) (by norm_num)
theorem B1882273 : Blo 1672036 1882273 := bbase (se 2 (by rfl) ⟨705852, by rfl⟩ : syracuseStep 1882273 = 1411705) (by norm_num)
theorem B3766445 : Blo 1672036 3766445 := bbase (se 3 (by rfl) ⟨706208, by rfl⟩ : syracuseStep 3766445 = 1412417) (by norm_num)
theorem B1882309 : Blo 1672036 1882309 := bbase (se 4 (by rfl) ⟨176466, by rfl⟩ : syracuseStep 1882309 = 352933) (by norm_num)
theorem B2382053 : Blo 1672036 2382053 := bbase (se 4 (by rfl) ⟨223317, by rfl⟩ : syracuseStep 2382053 = 446635) (by norm_num)
theorem B1882345 : Blo 1672036 1882345 := bbase (se 2 (by rfl) ⟨705879, by rfl⟩ : syracuseStep 1882345 = 1411759) (by norm_num)
theorem B2824429 : Blo 1672036 2824429 := bbase (se 3 (by rfl) ⟨529580, by rfl⟩ : syracuseStep 2824429 = 1059161) (by norm_num)
theorem B3766517 : Blo 1672036 3766517 := bbase (se 5 (by rfl) ⟨176555, by rfl⟩ : syracuseStep 3766517 = 353111) (by norm_num)
theorem B4233485 : Blo 1672036 4233485 := bbase (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) (by norm_num)
theorem B1882381 : Blo 1672036 1882381 := bbase (se 3 (by rfl) ⟨352946, by rfl⟩ : syracuseStep 1882381 = 705893) (by norm_num)
theorem B1882417 : Blo 1672036 1882417 := bbase (se 2 (by rfl) ⟨705906, by rfl⟩ : syracuseStep 1882417 = 1411813) (by norm_num)
theorem B2824517 : Blo 1672036 2824517 := bbase (se 4 (by rfl) ⟨264798, by rfl⟩ : syracuseStep 2824517 = 529597) (by norm_num)
theorem B1882453 : Blo 1672036 1882453 := bbase (se 10 (by rfl) ⟨2757, by rfl⟩ : syracuseStep 1882453 = 5515) (by norm_num)
theorem B1882489 : Blo 1672036 1882489 := bbase (se 2 (by rfl) ⟨705933, by rfl⟩ : syracuseStep 1882489 = 1411867) (by norm_num)
theorem B1882525 : Blo 1672036 1882525 := bbase (se 3 (by rfl) ⟨352973, by rfl⟩ : syracuseStep 1882525 = 705947) (by norm_num)
theorem B1882561 : Blo 1672036 1882561 := bbase (se 2 (by rfl) ⟨705960, by rfl⟩ : syracuseStep 1882561 = 1411921) (by norm_num)
theorem B2824645 : Blo 1672036 2824645 := bbase (se 4 (by rfl) ⟨264810, by rfl⟩ : syracuseStep 2824645 = 529621) (by norm_num)
theorem B1882597 : Blo 1672036 1882597 := bbase (se 4 (by rfl) ⟨176493, by rfl⟩ : syracuseStep 1882597 = 352987) (by norm_num)
theorem B1882633 : Blo 1672036 1882633 := bbase (se 2 (by rfl) ⟨705987, by rfl⟩ : syracuseStep 1882633 = 1411975) (by norm_num)
theorem B2824733 : Blo 1672036 2824733 := bbase (se 3 (by rfl) ⟨529637, by rfl⟩ : syracuseStep 2824733 = 1059275) (by norm_num)
theorem B1882669 : Blo 1672036 1882669 := bbase (se 3 (by rfl) ⟨353000, by rfl⟩ : syracuseStep 1882669 = 706001) (by norm_num)
theorem B5085749 : Blo 1672036 5085749 := bbase (se 5 (by rfl) ⟨238394, by rfl⟩ : syracuseStep 5085749 = 476789) (by norm_num)
theorem B1882705 : Blo 1672036 1882705 := bbase (se 2 (by rfl) ⟨706014, by rfl⟩ : syracuseStep 1882705 = 1412029) (by norm_num)
theorem B4766293 : Blo 1672036 4766293 := bbase (se 8 (by rfl) ⟨27927, by rfl⟩ : syracuseStep 4766293 = 55855) (by norm_num)
theorem B4233829 : Blo 1672036 4233829 := bbase (se 4 (by rfl) ⟨396921, by rfl⟩ : syracuseStep 4233829 = 793843) (by norm_num)
theorem B1882741 : Blo 1672036 1882741 := bbase (se 5 (by rfl) ⟨88253, by rfl⟩ : syracuseStep 1882741 = 176507) (by norm_num)
theorem B2292373 : Blo 1672036 2292373 := bbase (se 6 (by rfl) ⟨53727, by rfl⟩ : syracuseStep 2292373 = 107455) (by norm_num)
theorem B1882777 : Blo 1672036 1882777 := bbase (se 2 (by rfl) ⟨706041, by rfl⟩ : syracuseStep 1882777 = 1412083) (by norm_num)
theorem B2824861 : Blo 1672036 2824861 := bbase (se 3 (by rfl) ⟨529661, by rfl⟩ : syracuseStep 2824861 = 1059323) (by norm_num)
theorem B14293685 : Blo 1672036 14293685 := bbase (se 5 (by rfl) ⟨670016, by rfl⟩ : syracuseStep 14293685 = 1340033) (by norm_num)
theorem B1882813 : Blo 1672036 1882813 := bbase (se 3 (by rfl) ⟨353027, by rfl⟩ : syracuseStep 1882813 = 706055) (by norm_num)
theorem B3177157 : Blo 1672036 3177157 := bbase (se 4 (by rfl) ⟨297858, by rfl⟩ : syracuseStep 3177157 = 595717) (by norm_num)
theorem B4233941 : Blo 1672036 4233941 := bbase (se 7 (by rfl) ⟨49616, by rfl⟩ : syracuseStep 4233941 = 99233) (by norm_num)
theorem B1882849 : Blo 1672036 1882849 := bbase (se 2 (by rfl) ⟨706068, by rfl⟩ : syracuseStep 1882849 = 1412137) (by norm_num)
theorem B9042677 : Blo 1672036 9042677 := bbase (se 5 (by rfl) ⟨423875, by rfl⟩ : syracuseStep 9042677 = 847751) (by norm_num)
theorem B11451125 : Blo 1672036 11451125 := bbase (se 5 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 11451125 = 1073543) (by norm_num)
theorem B3054341 : Blo 1672036 3054341 := bbase (se 4 (by rfl) ⟨286344, by rfl⟩ : syracuseStep 3054341 = 572689) (by norm_num)
theorem B1882885 : Blo 1672036 1882885 := bbase (se 4 (by rfl) ⟨176520, by rfl⟩ : syracuseStep 1882885 = 353041) (by norm_num)
theorem B1882921 : Blo 1672036 1882921 := bbase (se 2 (by rfl) ⟨706095, by rfl⟩ : syracuseStep 1882921 = 1412191) (by norm_num)
theorem B1882957 : Blo 1672036 1882957 := bbase (se 3 (by rfl) ⟨353054, by rfl⟩ : syracuseStep 1882957 = 706109) (by norm_num)
theorem B3177301 : Blo 1672036 3177301 := bbase (se 9 (by rfl) ⟨9308, by rfl⟩ : syracuseStep 3177301 = 18617) (by norm_num)
theorem B1882993 : Blo 1672036 1882993 := bbase (se 2 (by rfl) ⟨706122, by rfl⟩ : syracuseStep 1882993 = 1412245) (by norm_num)
theorem B4234133 : Blo 1672036 4234133 := bbase (se 6 (by rfl) ⟨99237, by rfl⟩ : syracuseStep 4234133 = 198475) (by norm_num)
theorem B1883029 : Blo 1672036 1883029 := bbase (se 6 (by rfl) ⟨44133, by rfl⟩ : syracuseStep 1883029 = 88267) (by norm_num)
theorem B3218357 : Blo 1672036 3218357 := bbase (se 5 (by rfl) ⟨150860, by rfl⟩ : syracuseStep 3218357 = 301721) (by norm_num)
theorem B1883065 : Blo 1672036 1883065 := bbase (se 2 (by rfl) ⟨706149, by rfl⟩ : syracuseStep 1883065 = 1412299) (by norm_num)
theorem B1907645 : Blo 1672036 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B2382805 : Blo 1672036 2382805 := bbase (se 7 (by rfl) ⟨27923, by rfl⟩ : syracuseStep 2382805 = 55847) (by norm_num)
theorem B1883101 : Blo 1672036 1883101 := bbase (se 3 (by rfl) ⟨353081, by rfl⟩ : syracuseStep 1883101 = 706163) (by norm_num)
theorem B10722293 : Blo 1672036 10722293 := bbase (se 5 (by rfl) ⟨502607, by rfl⟩ : syracuseStep 10722293 = 1005215) (by norm_num)
theorem B3177461 : Blo 1672036 3177461 := bbase (se 5 (by rfl) ⟨148943, by rfl⟩ : syracuseStep 3177461 = 297887) (by norm_num)
theorem B1883137 : Blo 1672036 1883137 := bbase (se 2 (by rfl) ⟨706176, by rfl⟩ : syracuseStep 1883137 = 1412353) (by norm_num)
theorem B5643269 : Blo 1672036 5643269 := bbase (se 4 (by rfl) ⟨529056, by rfl⟩ : syracuseStep 5643269 = 1058113) (by norm_num)
theorem B4021253 : Blo 1672036 4021253 := bbase (se 4 (by rfl) ⟨376992, by rfl⟩ : syracuseStep 4021253 = 753985) (by norm_num)
theorem B1883173 : Blo 1672036 1883173 := bbase (se 4 (by rfl) ⟨176547, by rfl⟩ : syracuseStep 1883173 = 353095) (by norm_num)
theorem B1883209 : Blo 1672036 1883209 := bbase (se 2 (by rfl) ⟨706203, by rfl⟩ : syracuseStep 1883209 = 1412407) (by norm_num)
theorem B2145377 : Blo 1672036 2145377 := bbase (se 2 (by rfl) ⟨804516, by rfl⟩ : syracuseStep 2145377 = 1609033) (by norm_num)
theorem B1883245 : Blo 1672036 1883245 := bbase (se 3 (by rfl) ⟨353108, by rfl⟩ : syracuseStep 1883245 = 706217) (by norm_num)
theorem B3177605 : Blo 1672036 3177605 := bbase (se 4 (by rfl) ⟨297900, by rfl⟩ : syracuseStep 3177605 = 595801) (by norm_num)
theorem B1883281 : Blo 1672036 1883281 := bbase (se 2 (by rfl) ⟨706230, by rfl⟩ : syracuseStep 1883281 = 1412461) (by norm_num)
theorem B4021445 : Blo 1672036 4021445 := bbase (se 4 (by rfl) ⟨377010, by rfl⟩ : syracuseStep 4021445 = 754021) (by norm_num)
theorem B6110437 : Blo 1672036 6110437 := bbase (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) (by norm_num)
theorem B4234477 : Blo 1672036 4234477 := bbase (se 3 (by rfl) ⟨793964, by rfl⟩ : syracuseStep 4234477 = 1587929) (by norm_num)
theorem B8469845 : Blo 1672036 8469845 := bbase (se 11 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 8469845 = 12407) (by norm_num)
theorem B41278805 : Blo 1672036 41278805 := bbase (se 11 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 41278805 = 60467) (by norm_num)
theorem B4234589 : Blo 1672036 4234589 := bbase (se 3 (by rfl) ⟨793985, by rfl⟩ : syracuseStep 4234589 = 1587971) (by norm_num)
theorem B16301429 : Blo 1672036 16301429 := bbase (se 5 (by rfl) ⟨764129, by rfl⟩ : syracuseStep 16301429 = 1528259) (by norm_num)
theorem B3177893 : Blo 1672036 3177893 := bbase (se 4 (by rfl) ⟨297927, by rfl⟩ : syracuseStep 3177893 = 595855) (by norm_num)
theorem B5643701 : Blo 1672036 5643701 := bbase (se 5 (by rfl) ⟨264548, by rfl⟩ : syracuseStep 5643701 = 529097) (by norm_num)
theorem B1695169 : Blo 1672036 1695169 := bbase (se 2 (by rfl) ⟨635688, by rfl⟩ : syracuseStep 1695169 = 1271377) (by norm_num)
theorem B2260453 : Blo 1672036 2260453 := bbase (se 4 (by rfl) ⟨211917, by rfl⟩ : syracuseStep 2260453 = 423835) (by norm_num)
theorem B4234781 : Blo 1672036 4234781 := bbase (se 3 (by rfl) ⟨794021, by rfl⟩ : syracuseStep 4234781 = 1588043) (by norm_num)
theorem B3178045 : Blo 1672036 3178045 := bbase (se 3 (by rfl) ⟨595883, by rfl⟩ : syracuseStep 3178045 = 1191767) (by norm_num)
theorem B8044181 : Blo 1672036 8044181 := bbase (se 6 (by rfl) ⟨188535, by rfl⟩ : syracuseStep 8044181 = 377071) (by norm_num)
theorem B4521653 : Blo 1672036 4521653 := bbase (se 5 (by rfl) ⟨211952, by rfl⟩ : syracuseStep 4521653 = 423905) (by norm_num)
theorem B7143221 : Blo 1672036 7143221 := bbase (se 5 (by rfl) ⟨334838, by rfl⟩ : syracuseStep 7143221 = 669677) (by norm_num)
theorem B10714933 : Blo 1672036 10714933 := bbase (se 5 (by rfl) ⟨502262, by rfl⟩ : syracuseStep 10714933 = 1004525) (by norm_num)
theorem B2146105 : Blo 1672036 2146105 := bbase (se 2 (by rfl) ⟨804789, by rfl⟩ : syracuseStep 2146105 = 1609579) (by norm_num)
theorem B5644133 : Blo 1672036 5644133 := bbase (se 4 (by rfl) ⟨529137, by rfl⟩ : syracuseStep 5644133 = 1058275) (by norm_num)
theorem B2678645 : Blo 1672036 2678645 := bbase (se 5 (by rfl) ⟨125561, by rfl⟩ : syracuseStep 2678645 = 251123) (by norm_num)
theorem B4235125 : Blo 1672036 4235125 := bbase (se 5 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 4235125 = 397043) (by norm_num)
theorem B1785737 : Blo 1672036 1785737 := bbase (se 2 (by rfl) ⟨669651, by rfl⟩ : syracuseStep 1785737 = 1339303) (by norm_num)
theorem B6348725 : Blo 1672036 6348725 := bbase (se 5 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 6348725 = 595193) (by norm_num)
theorem B4235237 : Blo 1672036 4235237 := bbase (se 4 (by rfl) ⟨397053, by rfl⟩ : syracuseStep 4235237 = 794107) (by norm_num)
theorem B4235267 : Blo 1672036 4235267 := bstep (se 1 (by rfl) ⟨3176450, by rfl⟩ : syracuseStep 4235267 = 6352901) B6352901
theorem B6783139 : Blo 1672036 6783139 := bstep (se 1 (by rfl) ⟨5087354, by rfl⟩ : syracuseStep 6783139 = 10174709) B10174709
theorem B4292785 : Blo 1672036 4292785 := bstep (se 2 (by rfl) ⟨1609794, by rfl⟩ : syracuseStep 4292785 = 3219589) B3219589
theorem B2679041 : Blo 1672036 2679041 := bstep (se 2 (by rfl) ⟨1004640, by rfl⟩ : syracuseStep 2679041 = 2009281) B2009281
theorem B9527665 : Blo 1672036 9527665 := bstep (se 2 (by rfl) ⟨3572874, by rfl⟩ : syracuseStep 9527665 = 7145749) B7145749
theorem B7143821 : Blo 1672036 7143821 := bstep (se 3 (by rfl) ⟨1339466, by rfl⟩ : syracuseStep 7143821 = 2678933) B2678933
theorem B5644781 : Blo 1672036 5644781 := bstep (se 3 (by rfl) ⟨1058396, by rfl⟩ : syracuseStep 5644781 = 2116793) B2116793
theorem B10723853 : Blo 1672036 10723853 := bstep (se 3 (by rfl) ⟨2010722, by rfl⟩ : syracuseStep 10723853 = 4021445) B4021445
theorem B5644835 : Blo 1672036 5644835 := bstep (se 1 (by rfl) ⟨4233626, by rfl⟩ : syracuseStep 5644835 = 8467253) B8467253
theorem B19063349 : Blo 1672036 19063349 := bstep (se 5 (by rfl) ⟨893594, by rfl⟩ : syracuseStep 19063349 = 1787189) B1787189
theorem B5087843 : Blo 1672036 5087843 := bstep (se 1 (by rfl) ⟨3815882, by rfl⟩ : syracuseStep 5087843 = 7631765) B7631765
theorem B6030065 : Blo 1672036 6030065 := bstep (se 2 (by rfl) ⟨2261274, by rfl⟩ : syracuseStep 6030065 = 4522549) B4522549
theorem B5645105 : Blo 1672036 5645105 := bstep (se 2 (by rfl) ⟨2116914, by rfl⟩ : syracuseStep 5645105 = 4233829) B4233829
theorem B3056497 : Blo 1672036 3056497 := bstep (se 2 (by rfl) ⟨1146186, by rfl⟩ : syracuseStep 3056497 = 2292373) B2292373
theorem B1672051 : Blo 1672036 1672051 := bstep (se 1 (by rfl) ⟨1254038, by rfl⟩ : syracuseStep 1672051 = 2508077) B2508077
theorem B1672067 : Blo 1672036 1672067 := bstep (se 1 (by rfl) ⟨1254050, by rfl⟩ : syracuseStep 1672067 = 2508101) B2508101
theorem B1672083 : Blo 1672036 1672083 := bstep (se 1 (by rfl) ⟨1254062, by rfl⟩ : syracuseStep 1672083 = 2508125) B2508125
theorem B1672099 : Blo 1672036 1672099 := bstep (se 1 (by rfl) ⟨1254074, by rfl⟩ : syracuseStep 1672099 = 2508149) B2508149
theorem B4236209 : Blo 1672036 4236209 := bstep (se 2 (by rfl) ⟨1588578, by rfl⟩ : syracuseStep 4236209 = 3177157) B3177157
theorem B1672115 : Blo 1672036 1672115 := bstep (se 1 (by rfl) ⟨1254086, by rfl⟩ : syracuseStep 1672115 = 2508173) B2508173
theorem B1672131 : Blo 1672036 1672131 := bstep (se 1 (by rfl) ⟨1254098, by rfl⟩ : syracuseStep 1672131 = 2508197) B2508197
theorem B5358545 : Blo 1672036 5358545 := bstep (se 2 (by rfl) ⟨2009454, by rfl⟩ : syracuseStep 5358545 = 4018909) B4018909
theorem B1672147 : Blo 1672036 1672147 := bstep (se 1 (by rfl) ⟨1254110, by rfl⟩ : syracuseStep 1672147 = 2508221) B2508221
theorem B1672163 : Blo 1672036 1672163 := bstep (se 1 (by rfl) ⟨1254122, by rfl⟩ : syracuseStep 1672163 = 2508245) B2508245
theorem B4236259 : Blo 1672036 4236259 := bstep (se 1 (by rfl) ⟨3177194, by rfl⟩ : syracuseStep 4236259 = 6354389) B6354389
theorem B1672179 : Blo 1672036 1672179 := bstep (se 1 (by rfl) ⟨1254134, by rfl⟩ : syracuseStep 1672179 = 2508269) B2508269
theorem B1672195 : Blo 1672036 1672195 := bstep (se 1 (by rfl) ⟨1254146, by rfl⟩ : syracuseStep 1672195 = 2508293) B2508293
theorem B5358595 : Blo 1672036 5358595 := bstep (se 1 (by rfl) ⟨4018946, by rfl⟩ : syracuseStep 5358595 = 8037893) B8037893
theorem B1672211 : Blo 1672036 1672211 := bstep (se 1 (by rfl) ⟨1254158, by rfl⟩ : syracuseStep 1672211 = 2508317) B2508317
theorem B1672227 : Blo 1672036 1672227 := bstep (se 1 (by rfl) ⟨1254170, by rfl⟩ : syracuseStep 1672227 = 2508341) B2508341
theorem B1672243 : Blo 1672036 1672243 := bstep (se 1 (by rfl) ⟨1254182, by rfl⟩ : syracuseStep 1672243 = 2508365) B2508365
theorem B1672259 : Blo 1672036 1672259 := bstep (se 1 (by rfl) ⟨1254194, by rfl⟩ : syracuseStep 1672259 = 2508389) B2508389
theorem B2679875 : Blo 1672036 2679875 := bstep (se 1 (by rfl) ⟨2009906, by rfl⟩ : syracuseStep 2679875 = 4019813) B4019813
theorem B12698693 : Blo 1672036 12698693 := bstep (se 4 (by rfl) ⟨1190502, by rfl⟩ : syracuseStep 12698693 = 2381005) B2381005
theorem B1672275 : Blo 1672036 1672275 := bstep (se 1 (by rfl) ⟨1254206, by rfl⟩ : syracuseStep 1672275 = 2508413) B2508413
theorem B1672291 : Blo 1672036 1672291 := bstep (se 1 (by rfl) ⟨1254218, by rfl⟩ : syracuseStep 1672291 = 2508437) B2508437
theorem B2679907 : Blo 1672036 2679907 := bstep (se 1 (by rfl) ⟨2009930, by rfl⟩ : syracuseStep 2679907 = 4019861) B4019861
theorem B4236401 : Blo 1672036 4236401 := bstep (se 2 (by rfl) ⟨1588650, by rfl⟩ : syracuseStep 4236401 = 3177301) B3177301
theorem B1672307 : Blo 1672036 1672307 := bstep (se 1 (by rfl) ⟨1254230, by rfl⟩ : syracuseStep 1672307 = 2508461) B2508461
theorem B1672323 : Blo 1672036 1672323 := bstep (se 1 (by rfl) ⟨1254242, by rfl⟩ : syracuseStep 1672323 = 2508485) B2508485
theorem B1672339 : Blo 1672036 1672339 := bstep (se 1 (by rfl) ⟨1254254, by rfl⟩ : syracuseStep 1672339 = 2508509) B2508509
theorem B1787027 : Blo 1672036 1787027 := bstep (se 1 (by rfl) ⟨1340270, by rfl⟩ : syracuseStep 1787027 = 2680541) B2680541
theorem B1672355 : Blo 1672036 1672355 := bstep (se 1 (by rfl) ⟨1254266, by rfl⟩ : syracuseStep 1672355 = 2508533) B2508533
theorem B1672371 : Blo 1672036 1672371 := bstep (se 1 (by rfl) ⟨1254278, by rfl⟩ : syracuseStep 1672371 = 2508557) B2508557
theorem B1672387 : Blo 1672036 1672387 := bstep (se 1 (by rfl) ⟨1254290, by rfl⟩ : syracuseStep 1672387 = 2508581) B2508581
theorem B1672403 : Blo 1672036 1672403 := bstep (se 1 (by rfl) ⟨1254302, by rfl⟩ : syracuseStep 1672403 = 2508605) B2508605
theorem B1672419 : Blo 1672036 1672419 := bstep (se 1 (by rfl) ⟨1254314, by rfl⟩ : syracuseStep 1672419 = 2508629) B2508629
theorem B1672435 : Blo 1672036 1672435 := bstep (se 1 (by rfl) ⟨1254326, by rfl⟩ : syracuseStep 1672435 = 2508653) B2508653
theorem B1672451 : Blo 1672036 1672451 := bstep (se 1 (by rfl) ⟨1254338, by rfl⟩ : syracuseStep 1672451 = 2508677) B2508677
theorem B10716421 : Blo 1672036 10716421 := bstep (se 4 (by rfl) ⟨1004664, by rfl⟩ : syracuseStep 10716421 = 2009329) B2009329
theorem B1672467 : Blo 1672036 1672467 := bstep (se 1 (by rfl) ⟨1254350, by rfl⟩ : syracuseStep 1672467 = 2508701) B2508701
theorem B2508065 : Blo 1672036 2508065 := bstep (se 2 (by rfl) ⟨940524, by rfl⟩ : syracuseStep 2508065 = 1881049) B1881049
theorem B1672483 : Blo 1672036 1672483 := bstep (se 1 (by rfl) ⟨1254362, by rfl⟩ : syracuseStep 1672483 = 2508725) B2508725
theorem B2508083 : Blo 1672036 2508083 := bstep (se 1 (by rfl) ⟨1881062, by rfl⟩ : syracuseStep 2508083 = 3762125) B3762125
theorem B1672499 : Blo 1672036 1672499 := bstep (se 1 (by rfl) ⟨1254374, by rfl⟩ : syracuseStep 1672499 = 2508749) B2508749
theorem B1672515 : Blo 1672036 1672515 := bstep (se 1 (by rfl) ⟨1254386, by rfl⟩ : syracuseStep 1672515 = 2508773) B2508773
theorem B5645645 : Blo 1672036 5645645 := bstep (se 3 (by rfl) ⟨1058558, by rfl⟩ : syracuseStep 5645645 = 2117117) B2117117
theorem B2508113 : Blo 1672036 2508113 := bstep (se 2 (by rfl) ⟨940542, by rfl⟩ : syracuseStep 2508113 = 1881085) B1881085
theorem B1672531 : Blo 1672036 1672531 := bstep (se 1 (by rfl) ⟨1254398, by rfl⟩ : syracuseStep 1672531 = 2508797) B2508797
theorem B2508131 : Blo 1672036 2508131 := bstep (se 1 (by rfl) ⟨1881098, by rfl⟩ : syracuseStep 2508131 = 3762197) B3762197
theorem B1672547 : Blo 1672036 1672547 := bstep (se 1 (by rfl) ⟨1254410, by rfl⟩ : syracuseStep 1672547 = 2508821) B2508821
theorem B1672563 : Blo 1672036 1672563 := bstep (se 1 (by rfl) ⟨1254422, by rfl⟩ : syracuseStep 1672563 = 2508845) B2508845
theorem B2508161 : Blo 1672036 2508161 := bstep (se 2 (by rfl) ⟨940560, by rfl⟩ : syracuseStep 2508161 = 1881121) B1881121
theorem B1672579 : Blo 1672036 1672579 := bstep (se 1 (by rfl) ⟨1254434, by rfl⟩ : syracuseStep 1672579 = 2508869) B2508869
theorem B5645699 : Blo 1672036 5645699 := bstep (se 1 (by rfl) ⟨4234274, by rfl⟩ : syracuseStep 5645699 = 8468549) B8468549
theorem B2508179 : Blo 1672036 2508179 := bstep (se 1 (by rfl) ⟨1881134, by rfl⟩ : syracuseStep 2508179 = 3762269) B3762269
theorem B1672595 : Blo 1672036 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B1672611 : Blo 1672036 1672611 := bstep (se 1 (by rfl) ⟨1254458, by rfl⟩ : syracuseStep 1672611 = 2508917) B2508917
theorem B2508209 : Blo 1672036 2508209 := bstep (se 2 (by rfl) ⟨940578, by rfl⟩ : syracuseStep 2508209 = 1881157) B1881157
theorem B1672627 : Blo 1672036 1672627 := bstep (se 1 (by rfl) ⟨1254470, by rfl⟩ : syracuseStep 1672627 = 2508941) B2508941
theorem B2508227 : Blo 1672036 2508227 := bstep (se 1 (by rfl) ⟨1881170, by rfl⟩ : syracuseStep 2508227 = 3762341) B3762341
theorem B1672643 : Blo 1672036 1672643 := bstep (se 1 (by rfl) ⟨1254482, by rfl⟩ : syracuseStep 1672643 = 2508965) B2508965
theorem B1672659 : Blo 1672036 1672659 := bstep (se 1 (by rfl) ⟨1254494, by rfl⟩ : syracuseStep 1672659 = 2508989) B2508989
theorem B2508257 : Blo 1672036 2508257 := bstep (se 2 (by rfl) ⟨940596, by rfl⟩ : syracuseStep 2508257 = 1881193) B1881193
theorem B1672675 : Blo 1672036 1672675 := bstep (se 1 (by rfl) ⟨1254506, by rfl⟩ : syracuseStep 1672675 = 2509013) B2509013
theorem B2508275 : Blo 1672036 2508275 := bstep (se 1 (by rfl) ⟨1881206, by rfl⟩ : syracuseStep 2508275 = 3762413) B3762413
theorem B1672691 : Blo 1672036 1672691 := bstep (se 1 (by rfl) ⟨1254518, by rfl⟩ : syracuseStep 1672691 = 2509037) B2509037
theorem B1672707 : Blo 1672036 1672707 := bstep (se 1 (by rfl) ⟨1254530, by rfl⟩ : syracuseStep 1672707 = 2509061) B2509061
theorem B3573251 : Blo 1672036 3573251 := bstep (se 1 (by rfl) ⟨2679938, by rfl⟩ : syracuseStep 3573251 = 5359877) B5359877
theorem B2508305 : Blo 1672036 2508305 := bstep (se 2 (by rfl) ⟨940614, by rfl⟩ : syracuseStep 2508305 = 1881229) B1881229
theorem B1672723 : Blo 1672036 1672723 := bstep (se 1 (by rfl) ⟨1254542, by rfl⟩ : syracuseStep 1672723 = 2509085) B2509085
theorem B2508323 : Blo 1672036 2508323 := bstep (se 1 (by rfl) ⟨1881242, by rfl⟩ : syracuseStep 2508323 = 3762485) B3762485
theorem B1672739 : Blo 1672036 1672739 := bstep (se 1 (by rfl) ⟨1254554, by rfl⟩ : syracuseStep 1672739 = 2509109) B2509109
theorem B9045553 : Blo 1672036 9045553 := bstep (se 2 (by rfl) ⟨3392082, by rfl⟩ : syracuseStep 9045553 = 6784165) B6784165
theorem B8472113 : Blo 1672036 8472113 := bstep (se 2 (by rfl) ⟨3177042, by rfl⟩ : syracuseStep 8472113 = 6354085) B6354085
theorem B1672755 : Blo 1672036 1672755 := bstep (se 1 (by rfl) ⟨1254566, by rfl⟩ : syracuseStep 1672755 = 2509133) B2509133
theorem B2508353 : Blo 1672036 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B1672771 : Blo 1672036 1672771 := bstep (se 1 (by rfl) ⟨1254578, by rfl⟩ : syracuseStep 1672771 = 2509157) B2509157
theorem B2508371 : Blo 1672036 2508371 := bstep (se 1 (by rfl) ⟨1881278, by rfl⟩ : syracuseStep 2508371 = 3762557) B3762557
theorem B1672787 : Blo 1672036 1672787 := bstep (se 1 (by rfl) ⟨1254590, by rfl⟩ : syracuseStep 1672787 = 2509181) B2509181
theorem B1672803 : Blo 1672036 1672803 := bstep (se 1 (by rfl) ⟨1254602, by rfl⟩ : syracuseStep 1672803 = 2509205) B2509205
theorem B2508401 : Blo 1672036 2508401 := bstep (se 2 (by rfl) ⟨940650, by rfl⟩ : syracuseStep 2508401 = 1881301) B1881301
theorem B12707441 : Blo 1672036 12707441 := bstep (se 2 (by rfl) ⟨4765290, by rfl⟩ : syracuseStep 12707441 = 9530581) B9530581
theorem B1672819 : Blo 1672036 1672819 := bstep (se 1 (by rfl) ⟨1254614, by rfl⟩ : syracuseStep 1672819 = 2509229) B2509229
theorem B2508419 : Blo 1672036 2508419 := bstep (se 1 (by rfl) ⟨1881314, by rfl⟩ : syracuseStep 2508419 = 3762629) B3762629
theorem B1672835 : Blo 1672036 1672835 := bstep (se 1 (by rfl) ⟨1254626, by rfl⟩ : syracuseStep 1672835 = 2509253) B2509253
theorem B11445893 : Blo 1672036 11445893 := bstep (se 4 (by rfl) ⟨1073052, by rfl⟩ : syracuseStep 11445893 = 2146105) B2146105
theorem B4523651 : Blo 1672036 4523651 := bstep (se 1 (by rfl) ⟨3392738, by rfl⟩ : syracuseStep 4523651 = 6785477) B6785477
theorem B5645969 : Blo 1672036 5645969 := bstep (se 2 (by rfl) ⟨2117238, by rfl⟩ : syracuseStep 5645969 = 4234477) B4234477
theorem B1672851 : Blo 1672036 1672851 := bstep (se 1 (by rfl) ⟨1254638, by rfl⟩ : syracuseStep 1672851 = 2509277) B2509277
theorem B2508449 : Blo 1672036 2508449 := bstep (se 2 (by rfl) ⟨940668, by rfl⟩ : syracuseStep 2508449 = 1881337) B1881337
theorem B1672867 : Blo 1672036 1672867 := bstep (se 1 (by rfl) ⟨1254650, by rfl⟩ : syracuseStep 1672867 = 2509301) B2509301
theorem B2508467 : Blo 1672036 2508467 := bstep (se 1 (by rfl) ⟨1881350, by rfl⟩ : syracuseStep 2508467 = 3762701) B3762701
theorem B1672883 : Blo 1672036 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B1672899 : Blo 1672036 1672899 := bstep (se 1 (by rfl) ⟨1254674, by rfl⟩ : syracuseStep 1672899 = 2509349) B2509349
theorem B2508497 : Blo 1672036 2508497 := bstep (se 2 (by rfl) ⟨940686, by rfl⟩ : syracuseStep 2508497 = 1881373) B1881373
theorem B1672915 : Blo 1672036 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B2508515 : Blo 1672036 2508515 := bstep (se 1 (by rfl) ⟨1881386, by rfl⟩ : syracuseStep 2508515 = 3762773) B3762773
theorem B1672931 : Blo 1672036 1672931 := bstep (se 1 (by rfl) ⟨1254698, by rfl⟩ : syracuseStep 1672931 = 2509397) B2509397
theorem B1672947 : Blo 1672036 1672947 := bstep (se 1 (by rfl) ⟨1254710, by rfl⟩ : syracuseStep 1672947 = 2509421) B2509421
theorem B2508545 : Blo 1672036 2508545 := bstep (se 2 (by rfl) ⟨940704, by rfl⟩ : syracuseStep 2508545 = 1881409) B1881409
theorem B1672963 : Blo 1672036 1672963 := bstep (se 1 (by rfl) ⟨1254722, by rfl⟩ : syracuseStep 1672963 = 2509445) B2509445
theorem B2508563 : Blo 1672036 2508563 := bstep (se 1 (by rfl) ⟨1881422, by rfl⟩ : syracuseStep 2508563 = 3762845) B3762845
theorem B1672979 : Blo 1672036 1672979 := bstep (se 1 (by rfl) ⟨1254734, by rfl⟩ : syracuseStep 1672979 = 2509469) B2509469
theorem B1672995 : Blo 1672036 1672995 := bstep (se 1 (by rfl) ⟨1254746, by rfl⟩ : syracuseStep 1672995 = 2509493) B2509493
theorem B9529123 : Blo 1672036 9529123 := bstep (se 1 (by rfl) ⟨7146842, by rfl⟩ : syracuseStep 9529123 = 14293685) B14293685
theorem B2508593 : Blo 1672036 2508593 := bstep (se 2 (by rfl) ⟨940722, by rfl⟩ : syracuseStep 2508593 = 1881445) B1881445
theorem B1673011 : Blo 1672036 1673011 := bstep (se 1 (by rfl) ⟨1254758, by rfl⟩ : syracuseStep 1673011 = 2509517) B2509517
theorem B2508611 : Blo 1672036 2508611 := bstep (se 1 (by rfl) ⟨1881458, by rfl⟩ : syracuseStep 2508611 = 3762917) B3762917
theorem B1673027 : Blo 1672036 1673027 := bstep (se 1 (by rfl) ⟨1254770, by rfl⟩ : syracuseStep 1673027 = 2509541) B2509541
theorem B6350669 : Blo 1672036 6350669 := bstep (se 3 (by rfl) ⟨1190750, by rfl⟩ : syracuseStep 6350669 = 2381501) B2381501
theorem B5359441 : Blo 1672036 5359441 := bstep (se 2 (by rfl) ⟨2009790, by rfl⟩ : syracuseStep 5359441 = 4019581) B4019581
theorem B1673043 : Blo 1672036 1673043 := bstep (se 1 (by rfl) ⟨1254782, by rfl⟩ : syracuseStep 1673043 = 2509565) B2509565
theorem B2508641 : Blo 1672036 2508641 := bstep (se 2 (by rfl) ⟨940740, by rfl⟩ : syracuseStep 2508641 = 1881481) B1881481
theorem B1673059 : Blo 1672036 1673059 := bstep (se 1 (by rfl) ⟨1254794, by rfl⟩ : syracuseStep 1673059 = 2509589) B2509589
theorem B2508659 : Blo 1672036 2508659 := bstep (se 1 (by rfl) ⟨1881494, by rfl⟩ : syracuseStep 2508659 = 3762989) B3762989
theorem B1673075 : Blo 1672036 1673075 := bstep (se 1 (by rfl) ⟨1254806, by rfl⟩ : syracuseStep 1673075 = 2509613) B2509613
theorem B1673091 : Blo 1672036 1673091 := bstep (se 1 (by rfl) ⟨1254818, by rfl⟩ : syracuseStep 1673091 = 2509637) B2509637
theorem B2508689 : Blo 1672036 2508689 := bstep (se 2 (by rfl) ⟨940758, by rfl⟩ : syracuseStep 2508689 = 1881517) B1881517
theorem B1673107 : Blo 1672036 1673107 := bstep (se 1 (by rfl) ⟨1254830, by rfl⟩ : syracuseStep 1673107 = 2509661) B2509661
theorem B2508707 : Blo 1672036 2508707 := bstep (se 1 (by rfl) ⟨1881530, by rfl⟩ : syracuseStep 2508707 = 3763061) B3763061
theorem B1673123 : Blo 1672036 1673123 := bstep (se 1 (by rfl) ⟨1254842, by rfl⟩ : syracuseStep 1673123 = 2509685) B2509685
theorem B1673139 : Blo 1672036 1673139 := bstep (se 1 (by rfl) ⟨1254854, by rfl⟩ : syracuseStep 1673139 = 2509709) B2509709
theorem B2508737 : Blo 1672036 2508737 := bstep (se 2 (by rfl) ⟨940776, by rfl⟩ : syracuseStep 2508737 = 1881553) B1881553
theorem B1673155 : Blo 1672036 1673155 := bstep (se 1 (by rfl) ⟨1254866, by rfl⟩ : syracuseStep 1673155 = 2509733) B2509733
theorem B3573713 : Blo 1672036 3573713 := bstep (se 2 (by rfl) ⟨1340142, by rfl⟩ : syracuseStep 3573713 = 2680285) B2680285
theorem B2508755 : Blo 1672036 2508755 := bstep (se 1 (by rfl) ⟨1881566, by rfl⟩ : syracuseStep 2508755 = 3763133) B3763133
theorem B1673171 : Blo 1672036 1673171 := bstep (se 1 (by rfl) ⟨1254878, by rfl⟩ : syracuseStep 1673171 = 2509757) B2509757
theorem B1673187 : Blo 1672036 1673187 := bstep (se 1 (by rfl) ⟨1254890, by rfl⟩ : syracuseStep 1673187 = 2509781) B2509781
theorem B3762161 : Blo 1672036 3762161 := bstep (se 2 (by rfl) ⟨1410810, by rfl⟩ : syracuseStep 3762161 = 2821621) B2821621
theorem B2508785 : Blo 1672036 2508785 := bstep (se 2 (by rfl) ⟨940794, by rfl⟩ : syracuseStep 2508785 = 1881589) B1881589
theorem B1673203 : Blo 1672036 1673203 := bstep (se 1 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 1673203 = 2509805) B2509805
theorem B3762179 : Blo 1672036 3762179 := bstep (se 1 (by rfl) ⟨2821634, by rfl⟩ : syracuseStep 3762179 = 5643269) B5643269
theorem B2508803 : Blo 1672036 2508803 := bstep (se 1 (by rfl) ⟨1881602, by rfl⟩ : syracuseStep 2508803 = 3763205) B3763205
theorem B1673219 : Blo 1672036 1673219 := bstep (se 1 (by rfl) ⟨1254914, by rfl⟩ : syracuseStep 1673219 = 2509829) B2509829
theorem B2680835 : Blo 1672036 2680835 := bstep (se 1 (by rfl) ⟨2010626, by rfl⟩ : syracuseStep 2680835 = 4021253) B4021253
theorem B1673235 : Blo 1672036 1673235 := bstep (se 1 (by rfl) ⟨1254926, by rfl⟩ : syracuseStep 1673235 = 2509853) B2509853
theorem B2508833 : Blo 1672036 2508833 := bstep (se 2 (by rfl) ⟨940812, by rfl⟩ : syracuseStep 2508833 = 1881625) B1881625
theorem B1673251 : Blo 1672036 1673251 := bstep (se 1 (by rfl) ⟨1254938, by rfl⟩ : syracuseStep 1673251 = 2509877) B2509877
theorem B2508851 : Blo 1672036 2508851 := bstep (se 1 (by rfl) ⟨1881638, by rfl⟩ : syracuseStep 2508851 = 3763277) B3763277
theorem B1673267 : Blo 1672036 1673267 := bstep (se 1 (by rfl) ⟨1254950, by rfl⟩ : syracuseStep 1673267 = 2509901) B2509901
theorem B1673283 : Blo 1672036 1673283 := bstep (se 1 (by rfl) ⟨1254962, by rfl⟩ : syracuseStep 1673283 = 2509925) B2509925
theorem B2508881 : Blo 1672036 2508881 := bstep (se 2 (by rfl) ⟨940830, by rfl⟩ : syracuseStep 2508881 = 1881661) B1881661
theorem B2680913 : Blo 1672036 2680913 := bstep (se 2 (by rfl) ⟨1005342, by rfl⟩ : syracuseStep 2680913 = 2010685) B2010685
theorem B1673299 : Blo 1672036 1673299 := bstep (se 1 (by rfl) ⟨1254974, by rfl⟩ : syracuseStep 1673299 = 2509949) B2509949
theorem B4237393 : Blo 1672036 4237393 := bstep (se 2 (by rfl) ⟨1589022, by rfl⟩ : syracuseStep 4237393 = 3178045) B3178045
theorem B2508899 : Blo 1672036 2508899 := bstep (se 1 (by rfl) ⟨1881674, by rfl⟩ : syracuseStep 2508899 = 3763349) B3763349
theorem B1673315 : Blo 1672036 1673315 := bstep (se 1 (by rfl) ⟨1254986, by rfl⟩ : syracuseStep 1673315 = 2509973) B2509973
theorem B1673331 : Blo 1672036 1673331 := bstep (se 1 (by rfl) ⟨1254998, by rfl⟩ : syracuseStep 1673331 = 2509997) B2509997
theorem B2508929 : Blo 1672036 2508929 := bstep (se 2 (by rfl) ⟨940848, by rfl⟩ : syracuseStep 2508929 = 1881697) B1881697
theorem B1673347 : Blo 1672036 1673347 := bstep (se 1 (by rfl) ⟨1255010, by rfl⟩ : syracuseStep 1673347 = 2510021) B2510021
theorem B2508947 : Blo 1672036 2508947 := bstep (se 1 (by rfl) ⟨1881710, by rfl⟩ : syracuseStep 2508947 = 3763421) B3763421
theorem B1673363 : Blo 1672036 1673363 := bstep (se 1 (by rfl) ⟨1255022, by rfl⟩ : syracuseStep 1673363 = 2510045) B2510045
theorem B1673379 : Blo 1672036 1673379 := bstep (se 1 (by rfl) ⟨1255034, by rfl⟩ : syracuseStep 1673379 = 2510069) B2510069
theorem B5646509 : Blo 1672036 5646509 := bstep (se 3 (by rfl) ⟨1058720, by rfl⟩ : syracuseStep 5646509 = 2117441) B2117441
theorem B2508977 : Blo 1672036 2508977 := bstep (se 2 (by rfl) ⟨940866, by rfl⟩ : syracuseStep 2508977 = 1881733) B1881733
theorem B1673395 : Blo 1672036 1673395 := bstep (se 1 (by rfl) ⟨1255046, by rfl⟩ : syracuseStep 1673395 = 2510093) B2510093
theorem B2508995 : Blo 1672036 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B1673411 : Blo 1672036 1673411 := bstep (se 1 (by rfl) ⟨1255058, by rfl⟩ : syracuseStep 1673411 = 2510117) B2510117
theorem B1673427 : Blo 1672036 1673427 := bstep (se 1 (by rfl) ⟨1255070, by rfl⟩ : syracuseStep 1673427 = 2510141) B2510141
theorem B2509025 : Blo 1672036 2509025 := bstep (se 2 (by rfl) ⟨940884, by rfl⟩ : syracuseStep 2509025 = 1881769) B1881769
theorem B5646563 : Blo 1672036 5646563 := bstep (se 1 (by rfl) ⟨4234922, by rfl⟩ : syracuseStep 5646563 = 8469845) B8469845
theorem B1673443 : Blo 1672036 1673443 := bstep (se 1 (by rfl) ⟨1255082, by rfl⟩ : syracuseStep 1673443 = 2510165) B2510165
theorem B27519203 : Blo 1672036 27519203 := bstep (se 1 (by rfl) ⟨20639402, by rfl⟩ : syracuseStep 27519203 = 41278805) B41278805
theorem B4712689 : Blo 1672036 4712689 := bstep (se 2 (by rfl) ⟨1767258, by rfl⟩ : syracuseStep 4712689 = 3534517) B3534517
theorem B2509043 : Blo 1672036 2509043 := bstep (se 1 (by rfl) ⟨1881782, by rfl⟩ : syracuseStep 2509043 = 3763565) B3763565
theorem B1673459 : Blo 1672036 1673459 := bstep (se 1 (by rfl) ⟨1255094, by rfl⟩ : syracuseStep 1673459 = 2510189) B2510189
theorem B1673475 : Blo 1672036 1673475 := bstep (se 1 (by rfl) ⟨1255106, by rfl⟩ : syracuseStep 1673475 = 2510213) B2510213
theorem B3762449 : Blo 1672036 3762449 := bstep (se 2 (by rfl) ⟨1410918, by rfl⟩ : syracuseStep 3762449 = 2821837) B2821837
theorem B2509073 : Blo 1672036 2509073 := bstep (se 2 (by rfl) ⟨940902, by rfl⟩ : syracuseStep 2509073 = 1881805) B1881805
theorem B1673491 : Blo 1672036 1673491 := bstep (se 1 (by rfl) ⟨1255118, by rfl⟩ : syracuseStep 1673491 = 2510237) B2510237
theorem B3762467 : Blo 1672036 3762467 := bstep (se 1 (by rfl) ⟨2821850, by rfl⟩ : syracuseStep 3762467 = 5643701) B5643701
theorem B2509091 : Blo 1672036 2509091 := bstep (se 1 (by rfl) ⟨1881818, by rfl⟩ : syracuseStep 2509091 = 3763637) B3763637
theorem B1673507 : Blo 1672036 1673507 := bstep (se 1 (by rfl) ⟨1255130, by rfl⟩ : syracuseStep 1673507 = 2510261) B2510261
theorem B9529649 : Blo 1672036 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B2681137 : Blo 1672036 2681137 := bstep (se 2 (by rfl) ⟨1005426, by rfl⟩ : syracuseStep 2681137 = 2010853) B2010853
theorem B1673523 : Blo 1672036 1673523 := bstep (se 1 (by rfl) ⟨1255142, by rfl⟩ : syracuseStep 1673523 = 2510285) B2510285
theorem B2509121 : Blo 1672036 2509121 := bstep (se 2 (by rfl) ⟨940920, by rfl⟩ : syracuseStep 2509121 = 1881841) B1881841
theorem B1673539 : Blo 1672036 1673539 := bstep (se 1 (by rfl) ⟨1255154, by rfl⟩ : syracuseStep 1673539 = 2510309) B2510309
theorem B2509139 : Blo 1672036 2509139 := bstep (se 1 (by rfl) ⟨1881854, by rfl⟩ : syracuseStep 2509139 = 3763709) B3763709
theorem B1673555 : Blo 1672036 1673555 := bstep (se 1 (by rfl) ⟨1255166, by rfl⟩ : syracuseStep 1673555 = 2510333) B2510333
theorem B1673571 : Blo 1672036 1673571 := bstep (se 1 (by rfl) ⟨1255178, by rfl⟩ : syracuseStep 1673571 = 2510357) B2510357
theorem B4761965 : Blo 1672036 4761965 := bstep (se 3 (by rfl) ⟨892868, by rfl⟩ : syracuseStep 4761965 = 1785737) B1785737
theorem B2509169 : Blo 1672036 2509169 := bstep (se 2 (by rfl) ⟨940938, by rfl⟩ : syracuseStep 2509169 = 1881877) B1881877
theorem B1673587 : Blo 1672036 1673587 := bstep (se 1 (by rfl) ⟨1255190, by rfl⟩ : syracuseStep 1673587 = 2510381) B2510381
theorem B2509187 : Blo 1672036 2509187 := bstep (se 1 (by rfl) ⟨1881890, by rfl⟩ : syracuseStep 2509187 = 3763781) B3763781
theorem B1673603 : Blo 1672036 1673603 := bstep (se 1 (by rfl) ⟨1255202, by rfl⟩ : syracuseStep 1673603 = 2510405) B2510405
theorem B1673619 : Blo 1672036 1673619 := bstep (se 1 (by rfl) ⟨1255214, by rfl⟩ : syracuseStep 1673619 = 2510429) B2510429
theorem B2509217 : Blo 1672036 2509217 := bstep (se 2 (by rfl) ⟨940956, by rfl⟩ : syracuseStep 2509217 = 1881913) B1881913
theorem B1673635 : Blo 1672036 1673635 := bstep (se 1 (by rfl) ⟨1255226, by rfl⟩ : syracuseStep 1673635 = 2510453) B2510453
theorem B2509235 : Blo 1672036 2509235 := bstep (se 1 (by rfl) ⟨1881926, by rfl⟩ : syracuseStep 2509235 = 3763853) B3763853
theorem B1673651 : Blo 1672036 1673651 := bstep (se 1 (by rfl) ⟨1255238, by rfl⟩ : syracuseStep 1673651 = 2510477) B2510477
theorem B1673667 : Blo 1672036 1673667 := bstep (se 1 (by rfl) ⟨1255250, by rfl⟩ : syracuseStep 1673667 = 2510501) B2510501
theorem B61049285 : Blo 1672036 61049285 := bstep (se 4 (by rfl) ⟨5723370, by rfl⟩ : syracuseStep 61049285 = 11446741) B11446741
theorem B2509265 : Blo 1672036 2509265 := bstep (se 2 (by rfl) ⟨940974, by rfl⟩ : syracuseStep 2509265 = 1881949) B1881949
theorem B1673683 : Blo 1672036 1673683 := bstep (se 1 (by rfl) ⟨1255262, by rfl⟩ : syracuseStep 1673683 = 2510525) B2510525
theorem B2509283 : Blo 1672036 2509283 := bstep (se 1 (by rfl) ⟨1881962, by rfl⟩ : syracuseStep 2509283 = 3763925) B3763925
theorem B1673699 : Blo 1672036 1673699 := bstep (se 1 (by rfl) ⟨1255274, by rfl⟩ : syracuseStep 1673699 = 2510549) B2510549
theorem B4524515 : Blo 1672036 4524515 := bstep (se 1 (by rfl) ⟨3393386, by rfl⟩ : syracuseStep 4524515 = 6786773) B6786773
theorem B5646833 : Blo 1672036 5646833 := bstep (se 2 (by rfl) ⟨2117562, by rfl⟩ : syracuseStep 5646833 = 4235125) B4235125
theorem B1673715 : Blo 1672036 1673715 := bstep (se 1 (by rfl) ⟨1255286, by rfl⟩ : syracuseStep 1673715 = 2510573) B2510573
theorem B2509313 : Blo 1672036 2509313 := bstep (se 2 (by rfl) ⟨940992, by rfl⟩ : syracuseStep 2509313 = 1881985) B1881985
theorem B1673731 : Blo 1672036 1673731 := bstep (se 1 (by rfl) ⟨1255298, by rfl⟩ : syracuseStep 1673731 = 2510597) B2510597
theorem B2509331 : Blo 1672036 2509331 := bstep (se 1 (by rfl) ⟨1881998, by rfl⟩ : syracuseStep 2509331 = 3763997) B3763997
theorem B1673747 : Blo 1672036 1673747 := bstep (se 1 (by rfl) ⟨1255310, by rfl⟩ : syracuseStep 1673747 = 2510621) B2510621
theorem B4762147 : Blo 1672036 4762147 := bstep (se 1 (by rfl) ⟨3571610, by rfl⟩ : syracuseStep 4762147 = 7143221) B7143221
theorem B1673763 : Blo 1672036 1673763 := bstep (se 1 (by rfl) ⟨1255322, by rfl⟩ : syracuseStep 1673763 = 2510645) B2510645
theorem B3762737 : Blo 1672036 3762737 := bstep (se 2 (by rfl) ⟨1411026, by rfl⟩ : syracuseStep 3762737 = 2822053) B2822053
theorem B2509361 : Blo 1672036 2509361 := bstep (se 2 (by rfl) ⟨941010, by rfl⟩ : syracuseStep 2509361 = 1882021) B1882021
theorem B1673779 : Blo 1672036 1673779 := bstep (se 1 (by rfl) ⟨1255334, by rfl⟩ : syracuseStep 1673779 = 2510669) B2510669
theorem B28961333 : Blo 1672036 28961333 := bstep (se 5 (by rfl) ⟨1357562, by rfl⟩ : syracuseStep 28961333 = 2715125) B2715125
theorem B3762755 : Blo 1672036 3762755 := bstep (se 1 (by rfl) ⟨2822066, by rfl⟩ : syracuseStep 3762755 = 5644133) B5644133
theorem B2509379 : Blo 1672036 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B1673795 : Blo 1672036 1673795 := bstep (se 1 (by rfl) ⟨1255346, by rfl⟩ : syracuseStep 1673795 = 2510693) B2510693
theorem B1673811 : Blo 1672036 1673811 := bstep (se 1 (by rfl) ⟨1255358, by rfl⟩ : syracuseStep 1673811 = 2510717) B2510717
theorem B2509409 : Blo 1672036 2509409 := bstep (se 2 (by rfl) ⟨941028, by rfl⟩ : syracuseStep 2509409 = 1882057) B1882057
theorem B1673827 : Blo 1672036 1673827 := bstep (se 1 (by rfl) ⟨1255370, by rfl⟩ : syracuseStep 1673827 = 2510741) B2510741
theorem B6351473 : Blo 1672036 6351473 := bstep (se 2 (by rfl) ⟨2381802, by rfl⟩ : syracuseStep 6351473 = 4763605) B4763605
theorem B2509427 : Blo 1672036 2509427 := bstep (se 1 (by rfl) ⟨1882070, by rfl⟩ : syracuseStep 2509427 = 3764141) B3764141
theorem B1673843 : Blo 1672036 1673843 := bstep (se 1 (by rfl) ⟨1255382, by rfl⟩ : syracuseStep 1673843 = 2510765) B2510765
theorem B1673859 : Blo 1672036 1673859 := bstep (se 1 (by rfl) ⟨1255394, by rfl⟩ : syracuseStep 1673859 = 2510789) B2510789
theorem B2509457 : Blo 1672036 2509457 := bstep (se 2 (by rfl) ⟨941046, by rfl⟩ : syracuseStep 2509457 = 1882093) B1882093
theorem B1673875 : Blo 1672036 1673875 := bstep (se 1 (by rfl) ⟨1255406, by rfl⟩ : syracuseStep 1673875 = 2510813) B2510813
theorem B2509475 : Blo 1672036 2509475 := bstep (se 1 (by rfl) ⟨1882106, by rfl⟩ : syracuseStep 2509475 = 3764213) B3764213
theorem B1673891 : Blo 1672036 1673891 := bstep (se 1 (by rfl) ⟨1255418, by rfl⟩ : syracuseStep 1673891 = 2510837) B2510837
theorem B1673907 : Blo 1672036 1673907 := bstep (se 1 (by rfl) ⟨1255430, by rfl⟩ : syracuseStep 1673907 = 2510861) B2510861
theorem B2509505 : Blo 1672036 2509505 := bstep (se 2 (by rfl) ⟨941064, by rfl⟩ : syracuseStep 2509505 = 1882129) B1882129
theorem B4762307 : Blo 1672036 4762307 := bstep (se 1 (by rfl) ⟨3571730, by rfl⟩ : syracuseStep 4762307 = 7143461) B7143461
theorem B1673923 : Blo 1672036 1673923 := bstep (se 1 (by rfl) ⟨1255442, by rfl⟩ : syracuseStep 1673923 = 2510885) B2510885
theorem B28592837 : Blo 1672036 28592837 := bstep (se 4 (by rfl) ⟨2680578, by rfl⟩ : syracuseStep 28592837 = 5361157) B5361157
theorem B2116307 : Blo 1672036 2116307 := bstep (se 1 (by rfl) ⟨1587230, by rfl⟩ : syracuseStep 2116307 = 3174461) B3174461
theorem B2509523 : Blo 1672036 2509523 := bstep (se 1 (by rfl) ⟨1882142, by rfl⟩ : syracuseStep 2509523 = 3764285) B3764285
theorem B1673939 : Blo 1672036 1673939 := bstep (se 1 (by rfl) ⟨1255454, by rfl⟩ : syracuseStep 1673939 = 2510909) B2510909
theorem B1673955 : Blo 1672036 1673955 := bstep (se 1 (by rfl) ⟨1255466, by rfl⟩ : syracuseStep 1673955 = 2510933) B2510933
theorem B2509553 : Blo 1672036 2509553 := bstep (se 2 (by rfl) ⟨941082, by rfl⟩ : syracuseStep 2509553 = 1882165) B1882165
theorem B5090033 : Blo 1672036 5090033 := bstep (se 2 (by rfl) ⟨1908762, by rfl⟩ : syracuseStep 5090033 = 3817525) B3817525
theorem B1673971 : Blo 1672036 1673971 := bstep (se 1 (by rfl) ⟨1255478, by rfl⟩ : syracuseStep 1673971 = 2510957) B2510957
theorem B2509571 : Blo 1672036 2509571 := bstep (se 1 (by rfl) ⟨1882178, by rfl⟩ : syracuseStep 2509571 = 3764357) B3764357
theorem B1673987 : Blo 1672036 1673987 := bstep (se 1 (by rfl) ⟨1255490, by rfl⟩ : syracuseStep 1673987 = 2510981) B2510981
theorem B6032141 : Blo 1672036 6032141 := bstep (se 3 (by rfl) ⟨1131026, by rfl⟩ : syracuseStep 6032141 = 2262053) B2262053
theorem B1674003 : Blo 1672036 1674003 := bstep (se 1 (by rfl) ⟨1255502, by rfl⟩ : syracuseStep 1674003 = 2511005) B2511005
theorem B2509601 : Blo 1672036 2509601 := bstep (se 2 (by rfl) ⟨941100, by rfl⟩ : syracuseStep 2509601 = 1882201) B1882201
theorem B1674019 : Blo 1672036 1674019 := bstep (se 1 (by rfl) ⟨1255514, by rfl⟩ : syracuseStep 1674019 = 2511029) B2511029
theorem B2509619 : Blo 1672036 2509619 := bstep (se 1 (by rfl) ⟨1882214, by rfl⟩ : syracuseStep 2509619 = 3764429) B3764429
theorem B1674035 : Blo 1672036 1674035 := bstep (se 1 (by rfl) ⟨1255526, by rfl⟩ : syracuseStep 1674035 = 2511053) B2511053
theorem B3763025 : Blo 1672036 3763025 := bstep (se 2 (by rfl) ⟨1411134, by rfl⟩ : syracuseStep 3763025 = 2822269) B2822269
theorem B2509649 : Blo 1672036 2509649 := bstep (se 2 (by rfl) ⟨941118, by rfl⟩ : syracuseStep 2509649 = 1882237) B1882237
theorem B3763043 : Blo 1672036 3763043 := bstep (se 1 (by rfl) ⟨2822282, by rfl⟩ : syracuseStep 3763043 = 5644565) B5644565
theorem B2509667 : Blo 1672036 2509667 := bstep (se 1 (by rfl) ⟨1882250, by rfl⟩ : syracuseStep 2509667 = 3764501) B3764501
theorem B2509697 : Blo 1672036 2509697 := bstep (se 2 (by rfl) ⟨941136, by rfl⟩ : syracuseStep 2509697 = 1882273) B1882273
theorem B2509715 : Blo 1672036 2509715 := bstep (se 1 (by rfl) ⟨1882286, by rfl⟩ : syracuseStep 2509715 = 3764573) B3764573
theorem B5721005 : Blo 1672036 5721005 := bstep (se 3 (by rfl) ⟨1072688, by rfl⟩ : syracuseStep 5721005 = 2145377) B2145377
theorem B2509745 : Blo 1672036 2509745 := bstep (se 2 (by rfl) ⟨941154, by rfl⟩ : syracuseStep 2509745 = 1882309) B1882309
theorem B2509763 : Blo 1672036 2509763 := bstep (se 1 (by rfl) ⟨1882322, by rfl⟩ : syracuseStep 2509763 = 3764645) B3764645
theorem B2509793 : Blo 1672036 2509793 := bstep (se 2 (by rfl) ⟨941172, by rfl⟩ : syracuseStep 2509793 = 1882345) B1882345
theorem B13560803 : Blo 1672036 13560803 := bstep (se 1 (by rfl) ⟨10170602, by rfl⟩ : syracuseStep 13560803 = 20341205) B20341205
theorem B8473571 : Blo 1672036 8473571 := bstep (se 1 (by rfl) ⟨6355178, by rfl⟩ : syracuseStep 8473571 = 12710357) B12710357
theorem B2509811 : Blo 1672036 2509811 := bstep (se 1 (by rfl) ⟨1882358, by rfl⟩ : syracuseStep 2509811 = 3764717) B3764717
theorem B5647373 : Blo 1672036 5647373 := bstep (se 3 (by rfl) ⟨1058882, by rfl⟩ : syracuseStep 5647373 = 2117765) B2117765
theorem B2509841 : Blo 1672036 2509841 := bstep (se 2 (by rfl) ⟨941190, by rfl⟩ : syracuseStep 2509841 = 1882381) B1882381
theorem B2509859 : Blo 1672036 2509859 := bstep (se 1 (by rfl) ⟨1882394, by rfl⟩ : syracuseStep 2509859 = 3764789) B3764789
theorem B2509889 : Blo 1672036 2509889 := bstep (se 2 (by rfl) ⟨941208, by rfl⟩ : syracuseStep 2509889 = 1882417) B1882417
theorem B5647427 : Blo 1672036 5647427 := bstep (se 1 (by rfl) ⟨4235570, by rfl⟩ : syracuseStep 5647427 = 8471141) B8471141
theorem B2509907 : Blo 1672036 2509907 := bstep (se 1 (by rfl) ⟨1882430, by rfl⟩ : syracuseStep 2509907 = 3764861) B3764861
theorem B10308707 : Blo 1672036 10308707 := bstep (se 1 (by rfl) ⟨7731530, by rfl⟩ : syracuseStep 10308707 = 15463061) B15463061
theorem B3763313 : Blo 1672036 3763313 := bstep (se 2 (by rfl) ⟨1411242, by rfl⟩ : syracuseStep 3763313 = 2822485) B2822485
theorem B2509937 : Blo 1672036 2509937 := bstep (se 2 (by rfl) ⟨941226, by rfl⟩ : syracuseStep 2509937 = 1882453) B1882453
theorem B3763331 : Blo 1672036 3763331 := bstep (se 1 (by rfl) ⟨2822498, by rfl⟩ : syracuseStep 3763331 = 5644997) B5644997
theorem B2509955 : Blo 1672036 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B2509985 : Blo 1672036 2509985 := bstep (se 2 (by rfl) ⟨941244, by rfl⟩ : syracuseStep 2509985 = 1882489) B1882489
theorem B9653411 : Blo 1672036 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B2510003 : Blo 1672036 2510003 := bstep (se 1 (by rfl) ⟨1882502, by rfl⟩ : syracuseStep 2510003 = 3765005) B3765005
theorem B2510033 : Blo 1672036 2510033 := bstep (se 2 (by rfl) ⟨941262, by rfl⟩ : syracuseStep 2510033 = 1882525) B1882525
theorem B2510051 : Blo 1672036 2510051 := bstep (se 1 (by rfl) ⟨1882538, by rfl⟩ : syracuseStep 2510051 = 3765077) B3765077
theorem B3575011 : Blo 1672036 3575011 := bstep (se 1 (by rfl) ⟨2681258, by rfl⟩ : syracuseStep 3575011 = 5362517) B5362517
theorem B2510081 : Blo 1672036 2510081 := bstep (se 2 (by rfl) ⟨941280, by rfl⟩ : syracuseStep 2510081 = 1882561) B1882561
theorem B6352141 : Blo 1672036 6352141 := bstep (se 3 (by rfl) ⟨1191026, by rfl⟩ : syracuseStep 6352141 = 2382053) B2382053
theorem B2510099 : Blo 1672036 2510099 := bstep (se 1 (by rfl) ⟨1882574, by rfl⟩ : syracuseStep 2510099 = 3765149) B3765149
theorem B2510129 : Blo 1672036 2510129 := bstep (se 2 (by rfl) ⟨941298, by rfl⟩ : syracuseStep 2510129 = 1882597) B1882597
theorem B2510147 : Blo 1672036 2510147 := bstep (se 1 (by rfl) ⟨1882610, by rfl⟩ : syracuseStep 2510147 = 3765221) B3765221
theorem B5647697 : Blo 1672036 5647697 := bstep (se 2 (by rfl) ⟨2117886, by rfl⟩ : syracuseStep 5647697 = 4235773) B4235773
theorem B2510177 : Blo 1672036 2510177 := bstep (se 2 (by rfl) ⟨941316, by rfl⟩ : syracuseStep 2510177 = 1882633) B1882633
theorem B5721443 : Blo 1672036 5721443 := bstep (se 1 (by rfl) ⟨4291082, by rfl⟩ : syracuseStep 5721443 = 8582165) B8582165
theorem B5361005 : Blo 1672036 5361005 := bstep (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) B2010377
theorem B2510195 : Blo 1672036 2510195 := bstep (se 1 (by rfl) ⟨1882646, by rfl⟩ : syracuseStep 2510195 = 3765293) B3765293
theorem B3763601 : Blo 1672036 3763601 := bstep (se 2 (by rfl) ⟨1411350, by rfl⟩ : syracuseStep 3763601 = 2822701) B2822701
theorem B2510225 : Blo 1672036 2510225 := bstep (se 2 (by rfl) ⟨941334, by rfl⟩ : syracuseStep 2510225 = 1882669) B1882669
theorem B2117011 : Blo 1672036 2117011 := bstep (se 1 (by rfl) ⟨1587758, by rfl⟩ : syracuseStep 2117011 = 3175517) B3175517
theorem B3763619 : Blo 1672036 3763619 := bstep (se 1 (by rfl) ⟨2822714, by rfl⟩ : syracuseStep 3763619 = 5645429) B5645429
theorem B2510243 : Blo 1672036 2510243 := bstep (se 1 (by rfl) ⟨1882682, by rfl⟩ : syracuseStep 2510243 = 3765365) B3765365
theorem B2510273 : Blo 1672036 2510273 := bstep (se 2 (by rfl) ⟨941352, by rfl⟩ : syracuseStep 2510273 = 1882705) B1882705
theorem B2510291 : Blo 1672036 2510291 := bstep (se 1 (by rfl) ⟨1882718, by rfl⟩ : syracuseStep 2510291 = 3765437) B3765437
theorem B2821601 : Blo 1672036 2821601 := bstep (se 2 (by rfl) ⟨1058100, by rfl⟩ : syracuseStep 2821601 = 2116201) B2116201
theorem B3575267 : Blo 1672036 3575267 := bstep (se 1 (by rfl) ⟨2681450, by rfl⟩ : syracuseStep 3575267 = 5362901) B5362901
theorem B5803501 : Blo 1672036 5803501 := bstep (se 3 (by rfl) ⟨1088156, by rfl⟩ : syracuseStep 5803501 = 2176313) B2176313
theorem B2510321 : Blo 1672036 2510321 := bstep (se 2 (by rfl) ⟨941370, by rfl⟩ : syracuseStep 2510321 = 1882741) B1882741
theorem B2117107 : Blo 1672036 2117107 := bstep (se 1 (by rfl) ⟨1587830, by rfl⟩ : syracuseStep 2117107 = 3175661) B3175661
theorem B2510339 : Blo 1672036 2510339 := bstep (se 1 (by rfl) ⟨1882754, by rfl⟩ : syracuseStep 2510339 = 3765509) B3765509
theorem B2510369 : Blo 1672036 2510369 := bstep (se 2 (by rfl) ⟨941388, by rfl⟩ : syracuseStep 2510369 = 1882777) B1882777
theorem B2510387 : Blo 1672036 2510387 := bstep (se 1 (by rfl) ⟨1882790, by rfl⟩ : syracuseStep 2510387 = 3765581) B3765581
theorem B2510417 : Blo 1672036 2510417 := bstep (se 2 (by rfl) ⟨941406, by rfl⟩ : syracuseStep 2510417 = 1882813) B1882813
theorem B2821729 : Blo 1672036 2821729 := bstep (se 2 (by rfl) ⟨1058148, by rfl⟩ : syracuseStep 2821729 = 2116297) B2116297
theorem B2510435 : Blo 1672036 2510435 := bstep (se 1 (by rfl) ⟨1882826, by rfl⟩ : syracuseStep 2510435 = 3765653) B3765653
theorem B2510465 : Blo 1672036 2510465 := bstep (se 2 (by rfl) ⟨941424, by rfl⟩ : syracuseStep 2510465 = 1882849) B1882849
theorem B2821763 : Blo 1672036 2821763 := bstep (se 1 (by rfl) ⟨2116322, by rfl⟩ : syracuseStep 2821763 = 4232645) B4232645
theorem B2510483 : Blo 1672036 2510483 := bstep (se 1 (by rfl) ⟨1882862, by rfl⟩ : syracuseStep 2510483 = 3765725) B3765725
theorem B3763889 : Blo 1672036 3763889 := bstep (se 2 (by rfl) ⟨1411458, by rfl⟩ : syracuseStep 3763889 = 2822917) B2822917
theorem B2510513 : Blo 1672036 2510513 := bstep (se 2 (by rfl) ⟨941442, by rfl⟩ : syracuseStep 2510513 = 1882885) B1882885
theorem B2715329 : Blo 1672036 2715329 := bstep (se 2 (by rfl) ⟨1018248, by rfl⟩ : syracuseStep 2715329 = 2036497) B2036497
theorem B3763907 : Blo 1672036 3763907 := bstep (se 1 (by rfl) ⟨2822930, by rfl⟩ : syracuseStep 3763907 = 5645861) B5645861
theorem B2510531 : Blo 1672036 2510531 := bstep (se 1 (by rfl) ⟨1882898, by rfl⟩ : syracuseStep 2510531 = 3765797) B3765797
theorem B2510561 : Blo 1672036 2510561 := bstep (se 2 (by rfl) ⟨941460, by rfl⟩ : syracuseStep 2510561 = 1882921) B1882921
theorem B9531107 : Blo 1672036 9531107 := bstep (se 1 (by rfl) ⟨7148330, by rfl⟩ : syracuseStep 9531107 = 14296661) B14296661
theorem B4763377 : Blo 1672036 4763377 := bstep (se 2 (by rfl) ⟨1786266, by rfl⟩ : syracuseStep 4763377 = 3572533) B3572533
theorem B2510579 : Blo 1672036 2510579 := bstep (se 1 (by rfl) ⟨1882934, by rfl⟩ : syracuseStep 2510579 = 3765869) B3765869
theorem B2821891 : Blo 1672036 2821891 := bstep (se 1 (by rfl) ⟨2116418, by rfl⟩ : syracuseStep 2821891 = 4232837) B4232837
theorem B8474381 : Blo 1672036 8474381 := bstep (se 3 (by rfl) ⟨1588946, by rfl⟩ : syracuseStep 8474381 = 3177893) B3177893
theorem B2510609 : Blo 1672036 2510609 := bstep (se 2 (by rfl) ⟨941478, by rfl⟩ : syracuseStep 2510609 = 1882957) B1882957
theorem B2510627 : Blo 1672036 2510627 := bstep (se 1 (by rfl) ⟨1882970, by rfl⟩ : syracuseStep 2510627 = 3765941) B3765941
theorem B2510657 : Blo 1672036 2510657 := bstep (se 2 (by rfl) ⟨941496, by rfl⟩ : syracuseStep 2510657 = 1882993) B1882993
theorem B2510675 : Blo 1672036 2510675 := bstep (se 1 (by rfl) ⟨1883006, by rfl⟩ : syracuseStep 2510675 = 3766013) B3766013
theorem B10170211 : Blo 1672036 10170211 := bstep (se 1 (by rfl) ⟨7627658, by rfl⟩ : syracuseStep 10170211 = 15255317) B15255317
theorem B5648237 : Blo 1672036 5648237 := bstep (se 3 (by rfl) ⟨1059044, by rfl⟩ : syracuseStep 5648237 = 2118089) B2118089
theorem B2510705 : Blo 1672036 2510705 := bstep (se 2 (by rfl) ⟨941514, by rfl⟩ : syracuseStep 2510705 = 1883029) B1883029
theorem B2510723 : Blo 1672036 2510723 := bstep (se 1 (by rfl) ⟨1883042, by rfl⟩ : syracuseStep 2510723 = 3766085) B3766085
theorem B2822033 : Blo 1672036 2822033 := bstep (se 2 (by rfl) ⟨1058262, by rfl⟩ : syracuseStep 2822033 = 2116525) B2116525
theorem B2510753 : Blo 1672036 2510753 := bstep (se 2 (by rfl) ⟨941532, by rfl⟩ : syracuseStep 2510753 = 1883065) B1883065
theorem B5648291 : Blo 1672036 5648291 := bstep (se 1 (by rfl) ⟨4236218, by rfl⟩ : syracuseStep 5648291 = 8472437) B8472437
theorem B2510771 : Blo 1672036 2510771 := bstep (se 1 (by rfl) ⟨1883078, by rfl⟩ : syracuseStep 2510771 = 3766157) B3766157
theorem B3764177 : Blo 1672036 3764177 := bstep (se 2 (by rfl) ⟨1411566, by rfl⟩ : syracuseStep 3764177 = 2823133) B2823133
theorem B2510801 : Blo 1672036 2510801 := bstep (se 2 (by rfl) ⟨941550, by rfl⟩ : syracuseStep 2510801 = 1883101) B1883101
theorem B3764195 : Blo 1672036 3764195 := bstep (se 1 (by rfl) ⟨2823146, by rfl⟩ : syracuseStep 3764195 = 5646293) B5646293
theorem B2117603 : Blo 1672036 2117603 := bstep (se 1 (by rfl) ⟨1588202, by rfl⟩ : syracuseStep 2117603 = 3176405) B3176405
theorem B2510819 : Blo 1672036 2510819 := bstep (se 1 (by rfl) ⟨1883114, by rfl⟩ : syracuseStep 2510819 = 3766229) B3766229
theorem B3174385 : Blo 1672036 3174385 := bstep (se 2 (by rfl) ⟨1190394, by rfl⟩ : syracuseStep 3174385 = 2380789) B2380789
theorem B2510849 : Blo 1672036 2510849 := bstep (se 2 (by rfl) ⟨941568, by rfl⟩ : syracuseStep 2510849 = 1883137) B1883137
theorem B2822161 : Blo 1672036 2822161 := bstep (se 2 (by rfl) ⟨1058310, by rfl⟩ : syracuseStep 2822161 = 2116621) B2116621
theorem B2510867 : Blo 1672036 2510867 := bstep (se 1 (by rfl) ⟨1883150, by rfl⟩ : syracuseStep 2510867 = 3766301) B3766301
theorem B6352931 : Blo 1672036 6352931 := bstep (se 1 (by rfl) ⟨4764698, by rfl⟩ : syracuseStep 6352931 = 9529397) B9529397
theorem B2715697 : Blo 1672036 2715697 := bstep (se 2 (by rfl) ⟨1018386, by rfl⟩ : syracuseStep 2715697 = 2036773) B2036773
theorem B2510897 : Blo 1672036 2510897 := bstep (se 2 (by rfl) ⟨941586, by rfl⟩ : syracuseStep 2510897 = 1883173) B1883173
theorem B2822195 : Blo 1672036 2822195 := bstep (se 1 (by rfl) ⟨2116646, by rfl⟩ : syracuseStep 2822195 = 4233293) B4233293
theorem B2510915 : Blo 1672036 2510915 := bstep (se 1 (by rfl) ⟨1883186, by rfl⟩ : syracuseStep 2510915 = 3766373) B3766373
theorem B2510945 : Blo 1672036 2510945 := bstep (se 2 (by rfl) ⟨941604, by rfl⟩ : syracuseStep 2510945 = 1883209) B1883209
theorem B2510963 : Blo 1672036 2510963 := bstep (se 1 (by rfl) ⟨1883222, by rfl⟩ : syracuseStep 2510963 = 3766445) B3766445
theorem B13561997 : Blo 1672036 13561997 := bstep (se 3 (by rfl) ⟨2542874, by rfl⟩ : syracuseStep 13561997 = 5085749) B5085749
theorem B3174545 : Blo 1672036 3174545 := bstep (se 2 (by rfl) ⟨1190454, by rfl⟩ : syracuseStep 3174545 = 2380909) B2380909
theorem B2510993 : Blo 1672036 2510993 := bstep (se 2 (by rfl) ⟨941622, by rfl⟩ : syracuseStep 2510993 = 1883245) B1883245
theorem B2511011 : Blo 1672036 2511011 := bstep (se 1 (by rfl) ⟨1883258, by rfl⟩ : syracuseStep 2511011 = 3766517) B3766517
theorem B5648561 : Blo 1672036 5648561 := bstep (se 2 (by rfl) ⟨2118210, by rfl⟩ : syracuseStep 5648561 = 4236421) B4236421
theorem B2822323 : Blo 1672036 2822323 := bstep (se 1 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 2822323 = 4233485) B4233485
theorem B2511041 : Blo 1672036 2511041 := bstep (se 2 (by rfl) ⟨941640, by rfl⟩ : syracuseStep 2511041 = 1883281) B1883281
theorem B8704205 : Blo 1672036 8704205 := bstep (se 3 (by rfl) ⟨1632038, by rfl⟩ : syracuseStep 8704205 = 3264077) B3264077
theorem B3764465 : Blo 1672036 3764465 := bstep (se 2 (by rfl) ⟨1411674, by rfl⟩ : syracuseStep 3764465 = 2823349) B2823349
theorem B3764483 : Blo 1672036 3764483 := bstep (se 1 (by rfl) ⟨2823362, by rfl⟩ : syracuseStep 3764483 = 5646725) B5646725
theorem B8147249 : Blo 1672036 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B2822465 : Blo 1672036 2822465 := bstep (se 2 (by rfl) ⟨1058424, by rfl⟩ : syracuseStep 2822465 = 2116849) B2116849
theorem B16085317 : Blo 1672036 16085317 := bstep (se 4 (by rfl) ⟨1507998, by rfl⟩ : syracuseStep 16085317 = 3015997) B3015997
theorem B21451189 : Blo 1672036 21451189 := bstep (se 5 (by rfl) ⟨1005524, by rfl⟩ : syracuseStep 21451189 = 2011049) B2011049
theorem B2822593 : Blo 1672036 2822593 := bstep (se 2 (by rfl) ⟨1058472, by rfl⟩ : syracuseStep 2822593 = 2116945) B2116945
theorem B2822627 : Blo 1672036 2822627 := bstep (se 1 (by rfl) ⟨2116970, by rfl⟩ : syracuseStep 2822627 = 4233941) B4233941
theorem B8466929 : Blo 1672036 8466929 := bstep (se 2 (by rfl) ⟨3175098, by rfl⟩ : syracuseStep 8466929 = 6350197) B6350197
theorem B2036227 : Blo 1672036 2036227 := bstep (se 1 (by rfl) ⟨1527170, by rfl⟩ : syracuseStep 2036227 = 3054341) B3054341
theorem B3764753 : Blo 1672036 3764753 := bstep (se 2 (by rfl) ⟨1411782, by rfl⟩ : syracuseStep 3764753 = 2823565) B2823565
theorem B3174947 : Blo 1672036 3174947 := bstep (se 1 (by rfl) ⟨2381210, by rfl⟩ : syracuseStep 3174947 = 4762421) B4762421
theorem B3764771 : Blo 1672036 3764771 := bstep (se 1 (by rfl) ⟨2823578, by rfl⟩ : syracuseStep 3764771 = 5647157) B5647157
theorem B2822755 : Blo 1672036 2822755 := bstep (se 1 (by rfl) ⟨2117066, by rfl⟩ : syracuseStep 2822755 = 4234133) B4234133
theorem B7148195 : Blo 1672036 7148195 := bstep (se 1 (by rfl) ⟨5361146, by rfl⟩ : syracuseStep 7148195 = 10722293) B10722293
theorem B2118307 : Blo 1672036 2118307 := bstep (se 1 (by rfl) ⟨1588730, by rfl⟩ : syracuseStep 2118307 = 3177461) B3177461
theorem B6353585 : Blo 1672036 6353585 := bstep (se 2 (by rfl) ⟨2382594, by rfl⟩ : syracuseStep 6353585 = 4765189) B4765189
theorem B5649101 : Blo 1672036 5649101 := bstep (se 3 (by rfl) ⟨1059206, by rfl⟩ : syracuseStep 5649101 = 2118413) B2118413
theorem B2822897 : Blo 1672036 2822897 := bstep (se 2 (by rfl) ⟨1058586, by rfl⟩ : syracuseStep 2822897 = 2117173) B2117173
theorem B2118403 : Blo 1672036 2118403 := bstep (se 1 (by rfl) ⟨1588802, by rfl⟩ : syracuseStep 2118403 = 3177605) B3177605
theorem B5649155 : Blo 1672036 5649155 := bstep (se 1 (by rfl) ⟨4236866, by rfl⟩ : syracuseStep 5649155 = 8473733) B8473733
theorem B3765041 : Blo 1672036 3765041 := bstep (se 2 (by rfl) ⟨1411890, by rfl⟩ : syracuseStep 3765041 = 2823781) B2823781
theorem B3765059 : Blo 1672036 3765059 := bstep (se 1 (by rfl) ⟨2823794, by rfl⟩ : syracuseStep 3765059 = 5647589) B5647589
theorem B14299973 : Blo 1672036 14299973 := bstep (se 4 (by rfl) ⟨1340622, by rfl⟩ : syracuseStep 14299973 = 2681245) B2681245
theorem B8041315 : Blo 1672036 8041315 := bstep (se 1 (by rfl) ⟨6030986, by rfl⟩ : syracuseStep 8041315 = 12061973) B12061973
theorem B2823025 : Blo 1672036 2823025 := bstep (se 2 (by rfl) ⟨1058634, by rfl⟩ : syracuseStep 2823025 = 2117269) B2117269
theorem B2823059 : Blo 1672036 2823059 := bstep (se 1 (by rfl) ⟨2117294, by rfl⟩ : syracuseStep 2823059 = 4234589) B4234589
theorem B10867619 : Blo 1672036 10867619 := bstep (se 1 (by rfl) ⟨8150714, by rfl⟩ : syracuseStep 10867619 = 16301429) B16301429
theorem B14291909 : Blo 1672036 14291909 := bstep (se 4 (by rfl) ⟨1339866, by rfl⟩ : syracuseStep 14291909 = 2679733) B2679733
theorem B4764653 : Blo 1672036 4764653 := bstep (se 3 (by rfl) ⟨893372, by rfl⟩ : syracuseStep 4764653 = 1786745) B1786745
theorem B5649425 : Blo 1672036 5649425 := bstep (se 2 (by rfl) ⟨2118534, by rfl⟩ : syracuseStep 5649425 = 4237069) B4237069
theorem B2823187 : Blo 1672036 2823187 := bstep (se 1 (by rfl) ⟨2117390, by rfl⟩ : syracuseStep 2823187 = 4234781) B4234781
theorem B1881139 : Blo 1672036 1881139 := bstep (se 1 (by rfl) ⟨1410854, by rfl⟩ : syracuseStep 1881139 = 2821709) B2821709
theorem B3765329 : Blo 1672036 3765329 := bstep (se 2 (by rfl) ⟨1411998, by rfl⟩ : syracuseStep 3765329 = 2823997) B2823997
theorem B3765347 : Blo 1672036 3765347 := bstep (se 1 (by rfl) ⟨2824010, by rfl⟩ : syracuseStep 3765347 = 5648021) B5648021
theorem B5362787 : Blo 1672036 5362787 := bstep (se 1 (by rfl) ⟨4022090, by rfl⟩ : syracuseStep 5362787 = 8044181) B8044181
theorem B2823329 : Blo 1672036 2823329 := bstep (se 2 (by rfl) ⟨1058748, by rfl⟩ : syracuseStep 2823329 = 2117497) B2117497
theorem B4764835 : Blo 1672036 4764835 := bstep (se 1 (by rfl) ⟨3573626, by rfl⟩ : syracuseStep 4764835 = 7147253) B7147253
theorem B1881283 : Blo 1672036 1881283 := bstep (se 1 (by rfl) ⟨1410962, by rfl⟩ : syracuseStep 1881283 = 2821925) B2821925
theorem B4764881 : Blo 1672036 4764881 := bstep (se 2 (by rfl) ⟨1786830, by rfl⟩ : syracuseStep 4764881 = 3573661) B3573661
theorem B4830445 : Blo 1672036 4830445 := bstep (se 3 (by rfl) ⟨905708, by rfl⟩ : syracuseStep 4830445 = 1811417) B1811417
theorem B2823457 : Blo 1672036 2823457 := bstep (se 2 (by rfl) ⟨1058796, by rfl⟩ : syracuseStep 2823457 = 2117593) B2117593
theorem B4232483 : Blo 1672036 4232483 := bstep (se 1 (by rfl) ⟨3174362, by rfl⟩ : syracuseStep 4232483 = 6348725) B6348725
theorem B2823491 : Blo 1672036 2823491 := bstep (se 1 (by rfl) ⟨2117618, by rfl⟩ : syracuseStep 2823491 = 4235237) B4235237
theorem B1881427 : Blo 1672036 1881427 := bstep (se 1 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 1881427 = 2822141) B2822141
theorem B3765617 : Blo 1672036 3765617 := bstep (se 2 (by rfl) ⟨1412106, by rfl⟩ : syracuseStep 3765617 = 2824213) B2824213
theorem B3765635 : Blo 1672036 3765635 := bstep (se 1 (by rfl) ⟨2824226, by rfl⟩ : syracuseStep 3765635 = 5648453) B5648453
theorem B3175843 : Blo 1672036 3175843 := bstep (se 1 (by rfl) ⟨2381882, by rfl⟩ : syracuseStep 3175843 = 4763765) B4763765
theorem B2381233 : Blo 1672036 2381233 := bstep (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) B1785925
theorem B2823619 : Blo 1672036 2823619 := bstep (se 1 (by rfl) ⟨2117714, by rfl⟩ : syracuseStep 2823619 = 4235429) B4235429
theorem B4232675 : Blo 1672036 4232675 := bstep (se 1 (by rfl) ⟨3174506, by rfl⟩ : syracuseStep 4232675 = 6349013) B6349013
theorem B1881571 : Blo 1672036 1881571 := bstep (se 1 (by rfl) ⟨1411178, by rfl⟩ : syracuseStep 1881571 = 2822357) B2822357
theorem B14300657 : Blo 1672036 14300657 := bstep (se 2 (by rfl) ⟨5362746, by rfl⟩ : syracuseStep 14300657 = 10725493) B10725493
theorem B9524749 : Blo 1672036 9524749 := bstep (se 3 (by rfl) ⟨1785890, by rfl⟩ : syracuseStep 9524749 = 3571781) B3571781
theorem B2381347 : Blo 1672036 2381347 := bstep (se 1 (by rfl) ⟨1786010, by rfl⟩ : syracuseStep 2381347 = 3572021) B3572021
theorem B20338229 : Blo 1672036 20338229 := bstep (se 5 (by rfl) ⟨953354, by rfl⟩ : syracuseStep 20338229 = 1906709) B1906709
theorem B3176003 : Blo 1672036 3176003 := bstep (se 1 (by rfl) ⟨2382002, by rfl⟩ : syracuseStep 3176003 = 4764005) B4764005
theorem B9532997 : Blo 1672036 9532997 := bstep (se 4 (by rfl) ⟨893718, by rfl⟩ : syracuseStep 9532997 = 1787437) B1787437
theorem B2823761 : Blo 1672036 2823761 := bstep (se 2 (by rfl) ⟨1058910, by rfl⟩ : syracuseStep 2823761 = 2117821) B2117821
theorem B1881715 : Blo 1672036 1881715 := bstep (se 1 (by rfl) ⟨1411286, by rfl⟩ : syracuseStep 1881715 = 2822573) B2822573
theorem B3765905 : Blo 1672036 3765905 := bstep (se 2 (by rfl) ⟨1412214, by rfl⟩ : syracuseStep 3765905 = 2824429) B2824429
theorem B3765923 : Blo 1672036 3765923 := bstep (se 1 (by rfl) ⟨2824442, by rfl⟩ : syracuseStep 3765923 = 5648885) B5648885
theorem B2823889 : Blo 1672036 2823889 := bstep (se 2 (by rfl) ⟨1058958, by rfl⟩ : syracuseStep 2823889 = 2117917) B2117917
theorem B2414323 : Blo 1672036 2414323 := bstep (se 1 (by rfl) ⟨1810742, by rfl⟩ : syracuseStep 2414323 = 3621485) B3621485
theorem B2823923 : Blo 1672036 2823923 := bstep (se 1 (by rfl) ⟨2117942, by rfl⟩ : syracuseStep 2823923 = 4235885) B4235885
theorem B1881859 : Blo 1672036 1881859 := bstep (se 1 (by rfl) ⟨1411394, by rfl⟩ : syracuseStep 1881859 = 2822789) B2822789
theorem B3815171 : Blo 1672036 3815171 := bstep (se 1 (by rfl) ⟨2861378, by rfl⟩ : syracuseStep 3815171 = 5722757) B5722757
theorem B10860293 : Blo 1672036 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B9656177 : Blo 1672036 9656177 := bstep (se 2 (by rfl) ⟨3621066, by rfl⟩ : syracuseStep 9656177 = 7242133) B7242133
theorem B2824051 : Blo 1672036 2824051 := bstep (se 1 (by rfl) ⟨2118038, by rfl⟩ : syracuseStep 2824051 = 4236077) B4236077
theorem B1882003 : Blo 1672036 1882003 := bstep (se 1 (by rfl) ⟨1411502, by rfl⟩ : syracuseStep 1882003 = 2823005) B2823005
theorem B8468387 : Blo 1672036 8468387 := bstep (se 1 (by rfl) ⟨6351290, by rfl⟩ : syracuseStep 8468387 = 12702581) B12702581
theorem B4831139 : Blo 1672036 4831139 := bstep (se 1 (by rfl) ⟨3623354, by rfl⟩ : syracuseStep 4831139 = 7246709) B7246709
theorem B3766193 : Blo 1672036 3766193 := bstep (se 2 (by rfl) ⟨1412322, by rfl⟩ : syracuseStep 3766193 = 2824645) B2824645
theorem B3766211 : Blo 1672036 3766211 := bstep (se 1 (by rfl) ⟨2824658, by rfl⟩ : syracuseStep 3766211 = 5649317) B5649317
theorem B15259589 : Blo 1672036 15259589 := bstep (se 4 (by rfl) ⟨1430586, by rfl⟩ : syracuseStep 15259589 = 2861173) B2861173
theorem B2824193 : Blo 1672036 2824193 := bstep (se 2 (by rfl) ⟨1059072, by rfl⟩ : syracuseStep 2824193 = 2118145) B2118145
theorem B1882147 : Blo 1672036 1882147 := bstep (se 1 (by rfl) ⟨1411610, by rfl⟩ : syracuseStep 1882147 = 2823221) B2823221
theorem B2414657 : Blo 1672036 2414657 := bstep (se 2 (by rfl) ⟨905496, by rfl⟩ : syracuseStep 2414657 = 1810993) B1810993
theorem B6355043 : Blo 1672036 6355043 := bstep (se 1 (by rfl) ⟨4766282, by rfl⟩ : syracuseStep 6355043 = 9532565) B9532565
theorem B10721393 : Blo 1672036 10721393 := bstep (se 2 (by rfl) ⟨4020522, by rfl⟩ : syracuseStep 10721393 = 8041045) B8041045
theorem B6355057 : Blo 1672036 6355057 := bstep (se 2 (by rfl) ⟨2383146, by rfl⟩ : syracuseStep 6355057 = 4766293) B4766293
theorem B2824321 : Blo 1672036 2824321 := bstep (se 2 (by rfl) ⟨1059120, by rfl⟩ : syracuseStep 2824321 = 2118241) B2118241
theorem B9164933 : Blo 1672036 9164933 := bstep (se 4 (by rfl) ⟨859212, by rfl⟩ : syracuseStep 9164933 = 1718425) B1718425
theorem B2824355 : Blo 1672036 2824355 := bstep (se 1 (by rfl) ⟨2118266, by rfl⟩ : syracuseStep 2824355 = 4236533) B4236533
theorem B1882291 : Blo 1672036 1882291 := bstep (se 1 (by rfl) ⟨1411718, by rfl⟩ : syracuseStep 1882291 = 2823437) B2823437
theorem B10713293 : Blo 1672036 10713293 := bstep (se 3 (by rfl) ⟨2008742, by rfl⟩ : syracuseStep 10713293 = 4017485) B4017485
theorem B3766481 : Blo 1672036 3766481 := bstep (se 2 (by rfl) ⟨1412430, by rfl⟩ : syracuseStep 3766481 = 2824861) B2824861
theorem B3766499 : Blo 1672036 3766499 := bstep (se 1 (by rfl) ⟨2824874, by rfl⟩ : syracuseStep 3766499 = 5649749) B5649749
theorem B3217681 : Blo 1672036 3217681 := bstep (se 2 (by rfl) ⟨1206630, by rfl⟩ : syracuseStep 3217681 = 2413261) B2413261
theorem B2824483 : Blo 1672036 2824483 := bstep (se 1 (by rfl) ⟨2118362, by rfl⟩ : syracuseStep 2824483 = 4236725) B4236725
theorem B1882435 : Blo 1672036 1882435 := bstep (se 1 (by rfl) ⟨1411826, by rfl⟩ : syracuseStep 1882435 = 2823653) B2823653
theorem B4962637 : Blo 1672036 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B4233617 : Blo 1672036 4233617 := bstep (se 2 (by rfl) ⟨1587606, by rfl⟩ : syracuseStep 4233617 = 3175213) B3175213
theorem B5724589 : Blo 1672036 5724589 := bstep (se 3 (by rfl) ⟨1073360, by rfl⟩ : syracuseStep 5724589 = 2146721) B2146721
theorem B2824625 : Blo 1672036 2824625 := bstep (se 2 (by rfl) ⟨1059234, by rfl⟩ : syracuseStep 2824625 = 2118469) B2118469
theorem B4233667 : Blo 1672036 4233667 := bstep (se 1 (by rfl) ⟨3175250, by rfl⟩ : syracuseStep 4233667 = 6350501) B6350501
theorem B1882579 : Blo 1672036 1882579 := bstep (se 1 (by rfl) ⟨1411934, by rfl⟩ : syracuseStep 1882579 = 2823869) B2823869
theorem B2824753 : Blo 1672036 2824753 := bstep (se 2 (by rfl) ⟨1059282, by rfl⟩ : syracuseStep 2824753 = 2118565) B2118565
theorem B4233809 : Blo 1672036 4233809 := bstep (se 2 (by rfl) ⟨1587678, by rfl⟩ : syracuseStep 4233809 = 3175357) B3175357
theorem B2824787 : Blo 1672036 2824787 := bstep (se 1 (by rfl) ⟨2118590, by rfl⟩ : syracuseStep 2824787 = 4237181) B4237181
theorem B1882723 : Blo 1672036 1882723 := bstep (se 1 (by rfl) ⟨1412042, by rfl⟩ : syracuseStep 1882723 = 2824085) B2824085
theorem B18094691 : Blo 1672036 18094691 := bstep (se 1 (by rfl) ⟨13571018, by rfl⟩ : syracuseStep 18094691 = 27142037) B27142037
theorem B3177073 : Blo 1672036 3177073 := bstep (se 2 (by rfl) ⟨1191402, by rfl⟩ : syracuseStep 3177073 = 2382805) B2382805
theorem B7150193 : Blo 1672036 7150193 := bstep (se 2 (by rfl) ⟨2681322, by rfl⟩ : syracuseStep 7150193 = 5362645) B5362645
theorem B4766339 : Blo 1672036 4766339 := bstep (se 1 (by rfl) ⟨3574754, by rfl⟩ : syracuseStep 4766339 = 7149509) B7149509
theorem B8469197 : Blo 1672036 8469197 := bstep (se 3 (by rfl) ⟨1587974, by rfl⟩ : syracuseStep 8469197 = 3175949) B3175949
theorem B2824915 : Blo 1672036 2824915 := bstep (se 1 (by rfl) ⟨2118686, by rfl⟩ : syracuseStep 2824915 = 4237373) B4237373
theorem B1882867 : Blo 1672036 1882867 := bstep (se 1 (by rfl) ⟨1412150, by rfl⟩ : syracuseStep 1882867 = 2824301) B2824301
theorem B12704525 : Blo 1672036 12704525 := bstep (se 3 (by rfl) ⟨2382098, by rfl⟩ : syracuseStep 12704525 = 4764197) B4764197
theorem B2382691 : Blo 1672036 2382691 := bstep (se 1 (by rfl) ⟨1787018, by rfl⟩ : syracuseStep 2382691 = 3574037) B3574037
theorem B1883011 : Blo 1672036 1883011 := bstep (se 1 (by rfl) ⟨1412258, by rfl⟩ : syracuseStep 1883011 = 2824517) B2824517
theorem B1883155 : Blo 1672036 1883155 := bstep (se 1 (by rfl) ⟨1412366, by rfl⟩ : syracuseStep 1883155 = 2824733) B2824733
theorem B5643377 : Blo 1672036 5643377 := bstep (se 2 (by rfl) ⟨2116266, by rfl⟩ : syracuseStep 5643377 = 4232533) B4232533
theorem B6028451 : Blo 1672036 6028451 := bstep (se 1 (by rfl) ⟨4521338, by rfl⟩ : syracuseStep 6028451 = 9042677) B9042677
theorem B7634083 : Blo 1672036 7634083 := bstep (se 1 (by rfl) ⟨5725562, by rfl⟩ : syracuseStep 7634083 = 11451125) B11451125
theorem B2260225 : Blo 1672036 2260225 := bstep (se 2 (by rfl) ⟨847584, by rfl⟩ : syracuseStep 2260225 = 1695169) B1695169
theorem B2145571 : Blo 1672036 2145571 := bstep (se 1 (by rfl) ⟨1609178, by rfl⟩ : syracuseStep 2145571 = 3218357) B3218357
theorem B3013937 : Blo 1672036 3013937 := bstep (se 2 (by rfl) ⟨1130226, by rfl⟩ : syracuseStep 3013937 = 2260453) B2260453
theorem B5086577 : Blo 1672036 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B8043889 : Blo 1672036 8043889 := bstep (se 2 (by rfl) ⟨3016458, by rfl⟩ : syracuseStep 8043889 = 6032917) B6032917
theorem B9526733 : Blo 1672036 9526733 := bstep (se 3 (by rfl) ⟨1786262, by rfl⟩ : syracuseStep 9526733 = 3572525) B3572525
theorem B5086723 : Blo 1672036 5086723 := bstep (se 1 (by rfl) ⟨3815042, by rfl⟩ : syracuseStep 5086723 = 7630085) B7630085
theorem B4234801 : Blo 1672036 4234801 := bstep (se 2 (by rfl) ⟨1588050, by rfl⟩ : syracuseStep 4234801 = 3176101) B3176101
theorem B4021859 : Blo 1672036 4021859 := bstep (se 1 (by rfl) ⟨3016394, by rfl⟩ : syracuseStep 4021859 = 6032789) B6032789
theorem B5643917 : Blo 1672036 5643917 := bstep (se 3 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 5643917 = 2116469) B2116469
theorem B5643971 : Blo 1672036 5643971 := bstep (se 1 (by rfl) ⟨4232978, by rfl⟩ : syracuseStep 5643971 = 8465957) B8465957
theorem B5725901 : Blo 1672036 5725901 := bstep (se 3 (by rfl) ⟨1073606, by rfl⟩ : syracuseStep 5725901 = 2147213) B2147213
theorem B14286577 : Blo 1672036 14286577 := bstep (se 2 (by rfl) ⟨5357466, by rfl⟩ : syracuseStep 14286577 = 10714933) B10714933
theorem B6348557 : Blo 1672036 6348557 := bstep (se 3 (by rfl) ⟨1190354, by rfl⟩ : syracuseStep 6348557 = 2380709) B2380709
theorem B3014435 : Blo 1672036 3014435 := bstep (se 1 (by rfl) ⟨2260826, by rfl⟩ : syracuseStep 3014435 = 4521653) B4521653
theorem B2940707 : Blo 1672036 2940707 := bstep (se 1 (by rfl) ⟨2205530, by rfl⟩ : syracuseStep 2940707 = 4411061) B4411061
theorem B4235075 : Blo 1672036 4235075 := bstep (se 1 (by rfl) ⟨3176306, by rfl⟩ : syracuseStep 4235075 = 6352613) B6352613
theorem B5087053 : Blo 1672036 5087053 := bstep (se 3 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 5087053 = 1907645) B1907645
theorem B1785763 : Blo 1672036 1785763 := bstep (se 1 (by rfl) ⟨1339322, by rfl⟩ : syracuseStep 1785763 = 2678645) B2678645
theorem B13565893 : Blo 1672036 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B5644241 : Blo 1672036 5644241 := bstep (se 2 (by rfl) ⟨2116590, by rfl⟩ : syracuseStep 5644241 = 4233181) B4233181
theorem B4235287 : Blo 1672036 4235287 := bstep (se 1 (by rfl) ⟨3176465, by rfl⟩ : syracuseStep 4235287 = 6352931) B6352931
theorem B6439085 : Blo 1672036 6439085 := bstep (se 3 (by rfl) ⟨1207328, by rfl⟩ : syracuseStep 6439085 = 2414657) B2414657
theorem B5431499 : Blo 1672036 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B9044185 : Blo 1672036 9044185 := bstep (se 2 (by rfl) ⟨3391569, by rfl⟩ : syracuseStep 9044185 = 6783139) B6783139
theorem B14483717 : Blo 1672036 14483717 := bstep (se 4 (by rfl) ⟨1357848, by rfl⟩ : syracuseStep 14483717 = 2715697) B2715697
theorem B6283585 : Blo 1672036 6283585 := bstep (se 2 (by rfl) ⟨2356344, by rfl⟩ : syracuseStep 6283585 = 4712689) B4712689
theorem B5644619 : Blo 1672036 5644619 := bstep (se 1 (by rfl) ⟨4233464, by rfl⟩ : syracuseStep 5644619 = 8466929) B8466929
theorem B3391895 : Blo 1672036 3391895 := bstep (se 1 (by rfl) ⟨2543921, by rfl⟩ : syracuseStep 3391895 = 5087843) B5087843
theorem B21447089 : Blo 1672036 21447089 := bstep (se 2 (by rfl) ⟨8042658, by rfl⟩ : syracuseStep 21447089 = 16085317) B16085317
theorem B4235723 : Blo 1672036 4235723 := bstep (se 1 (by rfl) ⟨3176792, by rfl⟩ : syracuseStep 4235723 = 6353585) B6353585
theorem B5644889 : Blo 1672036 5644889 := bstep (se 2 (by rfl) ⟨2116833, by rfl⟩ : syracuseStep 5644889 = 4233667) B4233667
theorem B9527939 : Blo 1672036 9527939 := bstep (se 1 (by rfl) ⟨7145954, by rfl⟩ : syracuseStep 9527939 = 14291909) B14291909
theorem B3572363 : Blo 1672036 3572363 := bstep (se 1 (by rfl) ⟨2679272, by rfl⟩ : syracuseStep 3572363 = 5358545) B5358545
theorem B7144109 : Blo 1672036 7144109 := bstep (se 3 (by rfl) ⟨1339520, by rfl⟩ : syracuseStep 7144109 = 2679041) B2679041
theorem B1786583 : Blo 1672036 1786583 := bstep (se 1 (by rfl) ⟨1339937, by rfl⟩ : syracuseStep 1786583 = 2679875) B2679875
theorem B6349529 : Blo 1672036 6349529 := bstep (se 2 (by rfl) ⟨2381073, by rfl⟩ : syracuseStep 6349529 = 4762147) B4762147
theorem B4236097 : Blo 1672036 4236097 := bstep (se 2 (by rfl) ⟨1588536, by rfl⟩ : syracuseStep 4236097 = 3177073) B3177073
theorem B1672043 : Blo 1672036 1672043 := bstep (se 1 (by rfl) ⟨1254032, by rfl⟩ : syracuseStep 1672043 = 2508065) B2508065
theorem B1672055 : Blo 1672036 1672055 := bstep (se 1 (by rfl) ⟨1254041, by rfl⟩ : syracuseStep 1672055 = 2508083) B2508083
theorem B1672075 : Blo 1672036 1672075 := bstep (se 1 (by rfl) ⟨1254056, by rfl⟩ : syracuseStep 1672075 = 2508113) B2508113
theorem B1672087 : Blo 1672036 1672087 := bstep (se 1 (by rfl) ⟨1254065, by rfl⟩ : syracuseStep 1672087 = 2508131) B2508131
theorem B1672107 : Blo 1672036 1672107 := bstep (se 1 (by rfl) ⟨1254080, by rfl⟩ : syracuseStep 1672107 = 2508161) B2508161
theorem B1672119 : Blo 1672036 1672119 := bstep (se 1 (by rfl) ⟨1254089, by rfl⟩ : syracuseStep 1672119 = 2508179) B2508179
theorem B1672139 : Blo 1672036 1672139 := bstep (se 1 (by rfl) ⟨1254104, by rfl⟩ : syracuseStep 1672139 = 2508209) B2508209
theorem B1672151 : Blo 1672036 1672151 := bstep (se 1 (by rfl) ⟨1254113, by rfl⟩ : syracuseStep 1672151 = 2508227) B2508227
theorem B1672171 : Blo 1672036 1672171 := bstep (se 1 (by rfl) ⟨1254128, by rfl⟩ : syracuseStep 1672171 = 2508257) B2508257
theorem B1672183 : Blo 1672036 1672183 := bstep (se 1 (by rfl) ⟨1254137, by rfl⟩ : syracuseStep 1672183 = 2508275) B2508275
theorem B1672203 : Blo 1672036 1672203 := bstep (se 1 (by rfl) ⟨1254152, by rfl⟩ : syracuseStep 1672203 = 2508305) B2508305
theorem B1672215 : Blo 1672036 1672215 := bstep (se 1 (by rfl) ⟨1254161, by rfl⟩ : syracuseStep 1672215 = 2508323) B2508323
theorem B1672235 : Blo 1672036 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B1672247 : Blo 1672036 1672247 := bstep (se 1 (by rfl) ⟨1254185, by rfl⟩ : syracuseStep 1672247 = 2508371) B2508371
theorem B1672267 : Blo 1672036 1672267 := bstep (se 1 (by rfl) ⟨1254200, by rfl⟩ : syracuseStep 1672267 = 2508401) B2508401
theorem B8471627 : Blo 1672036 8471627 := bstep (se 1 (by rfl) ⟨6353720, by rfl⟩ : syracuseStep 8471627 = 12707441) B12707441
theorem B1672279 : Blo 1672036 1672279 := bstep (se 1 (by rfl) ⟨1254209, by rfl⟩ : syracuseStep 1672279 = 2508419) B2508419
theorem B3015767 : Blo 1672036 3015767 := bstep (se 1 (by rfl) ⟨2261825, by rfl⟩ : syracuseStep 3015767 = 4523651) B4523651
theorem B1672299 : Blo 1672036 1672299 := bstep (se 1 (by rfl) ⟨1254224, by rfl⟩ : syracuseStep 1672299 = 2508449) B2508449
theorem B1672311 : Blo 1672036 1672311 := bstep (se 1 (by rfl) ⟨1254233, by rfl⟩ : syracuseStep 1672311 = 2508467) B2508467
theorem B1672331 : Blo 1672036 1672331 := bstep (se 1 (by rfl) ⟨1254248, by rfl⟩ : syracuseStep 1672331 = 2508497) B2508497
theorem B1672343 : Blo 1672036 1672343 := bstep (se 1 (by rfl) ⟨1254257, by rfl⟩ : syracuseStep 1672343 = 2508515) B2508515
theorem B1672363 : Blo 1672036 1672363 := bstep (se 1 (by rfl) ⟨1254272, by rfl⟩ : syracuseStep 1672363 = 2508545) B2508545
theorem B1672375 : Blo 1672036 1672375 := bstep (se 1 (by rfl) ⟨1254281, by rfl⟩ : syracuseStep 1672375 = 2508563) B2508563
theorem B1672395 : Blo 1672036 1672395 := bstep (se 1 (by rfl) ⟨1254296, by rfl⟩ : syracuseStep 1672395 = 2508593) B2508593
theorem B1672407 : Blo 1672036 1672407 := bstep (se 1 (by rfl) ⟨1254305, by rfl⟩ : syracuseStep 1672407 = 2508611) B2508611
theorem B1672427 : Blo 1672036 1672427 := bstep (se 1 (by rfl) ⟨1254320, by rfl⟩ : syracuseStep 1672427 = 2508641) B2508641
theorem B1672439 : Blo 1672036 1672439 := bstep (se 1 (by rfl) ⟨1254329, by rfl⟩ : syracuseStep 1672439 = 2508659) B2508659
theorem B1672459 : Blo 1672036 1672459 := bstep (se 1 (by rfl) ⟨1254344, by rfl⟩ : syracuseStep 1672459 = 2508689) B2508689
theorem B1672471 : Blo 1672036 1672471 := bstep (se 1 (by rfl) ⟨1254353, by rfl⟩ : syracuseStep 1672471 = 2508707) B2508707
theorem B5645591 : Blo 1672036 5645591 := bstep (se 1 (by rfl) ⟨4234193, by rfl⟩ : syracuseStep 5645591 = 8468387) B8468387
theorem B3220759 : Blo 1672036 3220759 := bstep (se 1 (by rfl) ⟨2415569, by rfl⟩ : syracuseStep 3220759 = 4831139) B4831139
theorem B1672491 : Blo 1672036 1672491 := bstep (se 1 (by rfl) ⟨1254368, by rfl⟩ : syracuseStep 1672491 = 2508737) B2508737
theorem B1672503 : Blo 1672036 1672503 := bstep (se 1 (by rfl) ⟨1254377, by rfl⟩ : syracuseStep 1672503 = 2508755) B2508755
theorem B2508107 : Blo 1672036 2508107 := bstep (se 1 (by rfl) ⟨1881080, by rfl⟩ : syracuseStep 2508107 = 3762161) B3762161
theorem B1672523 : Blo 1672036 1672523 := bstep (se 1 (by rfl) ⟨1254392, by rfl⟩ : syracuseStep 1672523 = 2508785) B2508785
theorem B2508119 : Blo 1672036 2508119 := bstep (se 1 (by rfl) ⟨1881089, by rfl⟩ : syracuseStep 2508119 = 3762179) B3762179
theorem B1672535 : Blo 1672036 1672535 := bstep (se 1 (by rfl) ⟨1254401, by rfl⟩ : syracuseStep 1672535 = 2508803) B2508803
theorem B7144793 : Blo 1672036 7144793 := bstep (se 2 (by rfl) ⟨2679297, by rfl⟩ : syracuseStep 7144793 = 5358595) B5358595
theorem B1672555 : Blo 1672036 1672555 := bstep (se 1 (by rfl) ⟨1254416, by rfl⟩ : syracuseStep 1672555 = 2508833) B2508833
theorem B1672567 : Blo 1672036 1672567 := bstep (se 1 (by rfl) ⟨1254425, by rfl⟩ : syracuseStep 1672567 = 2508851) B2508851
theorem B1672587 : Blo 1672036 1672587 := bstep (se 1 (by rfl) ⟨1254440, by rfl⟩ : syracuseStep 1672587 = 2508881) B2508881
theorem B1787275 : Blo 1672036 1787275 := bstep (se 1 (by rfl) ⟨1340456, by rfl⟩ : syracuseStep 1787275 = 2680913) B2680913
theorem B1672599 : Blo 1672036 1672599 := bstep (se 1 (by rfl) ⟨1254449, by rfl⟩ : syracuseStep 1672599 = 2508899) B2508899
theorem B4236695 : Blo 1672036 4236695 := bstep (se 1 (by rfl) ⟨3177521, by rfl⟩ : syracuseStep 4236695 = 6355043) B6355043
theorem B2508185 : Blo 1672036 2508185 := bstep (se 2 (by rfl) ⟨940569, by rfl⟩ : syracuseStep 2508185 = 1881139) B1881139
theorem B1672619 : Blo 1672036 1672619 := bstep (se 1 (by rfl) ⟨1254464, by rfl⟩ : syracuseStep 1672619 = 2508929) B2508929
theorem B1672631 : Blo 1672036 1672631 := bstep (se 1 (by rfl) ⟨1254473, by rfl⟩ : syracuseStep 1672631 = 2508947) B2508947
theorem B1672651 : Blo 1672036 1672651 := bstep (se 1 (by rfl) ⟨1254488, by rfl⟩ : syracuseStep 1672651 = 2508977) B2508977
theorem B1672663 : Blo 1672036 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B3573209 : Blo 1672036 3573209 := bstep (se 2 (by rfl) ⟨1339953, by rfl⟩ : syracuseStep 3573209 = 2679907) B2679907
theorem B1672683 : Blo 1672036 1672683 := bstep (se 1 (by rfl) ⟨1254512, by rfl⟩ : syracuseStep 1672683 = 2509025) B2509025
theorem B1672695 : Blo 1672036 1672695 := bstep (se 1 (by rfl) ⟨1254521, by rfl⟩ : syracuseStep 1672695 = 2509043) B2509043
theorem B2508299 : Blo 1672036 2508299 := bstep (se 1 (by rfl) ⟨1881224, by rfl⟩ : syracuseStep 2508299 = 3762449) B3762449
theorem B1672715 : Blo 1672036 1672715 := bstep (se 1 (by rfl) ⟨1254536, by rfl⟩ : syracuseStep 1672715 = 2509073) B2509073
theorem B2508311 : Blo 1672036 2508311 := bstep (se 1 (by rfl) ⟨1881233, by rfl⟩ : syracuseStep 2508311 = 3762467) B3762467
theorem B1672727 : Blo 1672036 1672727 := bstep (se 1 (by rfl) ⟨1254545, by rfl⟩ : syracuseStep 1672727 = 2509091) B2509091
theorem B1672747 : Blo 1672036 1672747 := bstep (se 1 (by rfl) ⟨1254560, by rfl⟩ : syracuseStep 1672747 = 2509121) B2509121
theorem B1672759 : Blo 1672036 1672759 := bstep (se 1 (by rfl) ⟨1254569, by rfl⟩ : syracuseStep 1672759 = 2509139) B2509139
theorem B1672779 : Blo 1672036 1672779 := bstep (se 1 (by rfl) ⟨1254584, by rfl⟩ : syracuseStep 1672779 = 2509169) B2509169
theorem B1672791 : Blo 1672036 1672791 := bstep (se 1 (by rfl) ⟨1254593, by rfl⟩ : syracuseStep 1672791 = 2509187) B2509187
theorem B2508377 : Blo 1672036 2508377 := bstep (se 2 (by rfl) ⟨940641, by rfl⟩ : syracuseStep 2508377 = 1881283) B1881283
theorem B10724957 : Blo 1672036 10724957 := bstep (se 3 (by rfl) ⟨2010929, by rfl⟩ : syracuseStep 10724957 = 4021859) B4021859
theorem B1672811 : Blo 1672036 1672811 := bstep (se 1 (by rfl) ⟨1254608, by rfl⟩ : syracuseStep 1672811 = 2509217) B2509217
theorem B1672823 : Blo 1672036 1672823 := bstep (se 1 (by rfl) ⟨1254617, by rfl⟩ : syracuseStep 1672823 = 2509235) B2509235
theorem B40699523 : Blo 1672036 40699523 := bstep (se 1 (by rfl) ⟨30524642, by rfl⟩ : syracuseStep 40699523 = 61049285) B61049285
theorem B1672843 : Blo 1672036 1672843 := bstep (se 1 (by rfl) ⟨1254632, by rfl⟩ : syracuseStep 1672843 = 2509265) B2509265
theorem B1672855 : Blo 1672036 1672855 := bstep (se 1 (by rfl) ⟨1254641, by rfl⟩ : syracuseStep 1672855 = 2509283) B2509283
theorem B3016343 : Blo 1672036 3016343 := bstep (se 1 (by rfl) ⟨2262257, by rfl⟩ : syracuseStep 3016343 = 4524515) B4524515
theorem B1672875 : Blo 1672036 1672875 := bstep (se 1 (by rfl) ⟨1254656, by rfl⟩ : syracuseStep 1672875 = 2509313) B2509313
theorem B14288561 : Blo 1672036 14288561 := bstep (se 2 (by rfl) ⟨5358210, by rfl⟩ : syracuseStep 14288561 = 10716421) B10716421
theorem B1672887 : Blo 1672036 1672887 := bstep (se 1 (by rfl) ⟨1254665, by rfl⟩ : syracuseStep 1672887 = 2509331) B2509331
theorem B2508491 : Blo 1672036 2508491 := bstep (se 1 (by rfl) ⟨1881368, by rfl⟩ : syracuseStep 2508491 = 3762737) B3762737
theorem B1672907 : Blo 1672036 1672907 := bstep (se 1 (by rfl) ⟨1254680, by rfl⟩ : syracuseStep 1672907 = 2509361) B2509361
theorem B2508503 : Blo 1672036 2508503 := bstep (se 1 (by rfl) ⟨1881377, by rfl⟩ : syracuseStep 2508503 = 3762755) B3762755
theorem B1672919 : Blo 1672036 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B1672939 : Blo 1672036 1672939 := bstep (se 1 (by rfl) ⟨1254704, by rfl⟩ : syracuseStep 1672939 = 2509409) B2509409
theorem B1672951 : Blo 1672036 1672951 := bstep (se 1 (by rfl) ⟨1254713, by rfl⟩ : syracuseStep 1672951 = 2509427) B2509427
theorem B1672971 : Blo 1672036 1672971 := bstep (se 1 (by rfl) ⟨1254728, by rfl⟩ : syracuseStep 1672971 = 2509457) B2509457
theorem B1672983 : Blo 1672036 1672983 := bstep (se 1 (by rfl) ⟨1254737, by rfl⟩ : syracuseStep 1672983 = 2509475) B2509475
theorem B2508569 : Blo 1672036 2508569 := bstep (se 2 (by rfl) ⟨940713, by rfl⟩ : syracuseStep 2508569 = 1881427) B1881427
theorem B1673003 : Blo 1672036 1673003 := bstep (se 1 (by rfl) ⟨1254752, by rfl⟩ : syracuseStep 1673003 = 2509505) B2509505
theorem B5646131 : Blo 1672036 5646131 := bstep (se 1 (by rfl) ⟨4234598, by rfl⟩ : syracuseStep 5646131 = 8469197) B8469197
theorem B1673015 : Blo 1672036 1673015 := bstep (se 1 (by rfl) ⟨1254761, by rfl⟩ : syracuseStep 1673015 = 2509523) B2509523
theorem B10725185 : Blo 1672036 10725185 := bstep (se 2 (by rfl) ⟨4021944, by rfl⟩ : syracuseStep 10725185 = 8043889) B8043889
theorem B1673035 : Blo 1672036 1673035 := bstep (se 1 (by rfl) ⟨1254776, by rfl⟩ : syracuseStep 1673035 = 2509553) B2509553
theorem B3393355 : Blo 1672036 3393355 := bstep (se 1 (by rfl) ⟨2545016, by rfl⟩ : syracuseStep 3393355 = 5090033) B5090033
theorem B1673047 : Blo 1672036 1673047 := bstep (se 1 (by rfl) ⟨1254785, by rfl⟩ : syracuseStep 1673047 = 2509571) B2509571
theorem B1673067 : Blo 1672036 1673067 := bstep (se 1 (by rfl) ⟨1254800, by rfl⟩ : syracuseStep 1673067 = 2509601) B2509601
theorem B1673079 : Blo 1672036 1673079 := bstep (se 1 (by rfl) ⟨1254809, by rfl⟩ : syracuseStep 1673079 = 2509619) B2509619
theorem B2508683 : Blo 1672036 2508683 := bstep (se 1 (by rfl) ⟨1881512, by rfl⟩ : syracuseStep 2508683 = 3763025) B3763025
theorem B1673099 : Blo 1672036 1673099 := bstep (se 1 (by rfl) ⟨1254824, by rfl⟩ : syracuseStep 1673099 = 2509649) B2509649
theorem B2508695 : Blo 1672036 2508695 := bstep (se 1 (by rfl) ⟨1881521, by rfl⟩ : syracuseStep 2508695 = 3763043) B3763043
theorem B1673111 : Blo 1672036 1673111 := bstep (se 1 (by rfl) ⟨1254833, by rfl⟩ : syracuseStep 1673111 = 2509667) B2509667
theorem B1673131 : Blo 1672036 1673131 := bstep (se 1 (by rfl) ⟨1254848, by rfl⟩ : syracuseStep 1673131 = 2509697) B2509697
theorem B1673143 : Blo 1672036 1673143 := bstep (se 1 (by rfl) ⟨1254857, by rfl⟩ : syracuseStep 1673143 = 2509715) B2509715
theorem B1673163 : Blo 1672036 1673163 := bstep (se 1 (by rfl) ⟨1254872, by rfl⟩ : syracuseStep 1673163 = 2509745) B2509745
theorem B1673175 : Blo 1672036 1673175 := bstep (se 1 (by rfl) ⟨1254881, by rfl⟩ : syracuseStep 1673175 = 2509763) B2509763
theorem B2508761 : Blo 1672036 2508761 := bstep (se 2 (by rfl) ⟨940785, by rfl⟩ : syracuseStep 2508761 = 1881571) B1881571
theorem B1673195 : Blo 1672036 1673195 := bstep (se 1 (by rfl) ⟨1254896, by rfl⟩ : syracuseStep 1673195 = 2509793) B2509793
theorem B1673207 : Blo 1672036 1673207 := bstep (se 1 (by rfl) ⟨1254905, by rfl⟩ : syracuseStep 1673207 = 2509811) B2509811
theorem B1673227 : Blo 1672036 1673227 := bstep (se 1 (by rfl) ⟨1254920, by rfl⟩ : syracuseStep 1673227 = 2509841) B2509841
theorem B12699665 : Blo 1672036 12699665 := bstep (se 2 (by rfl) ⟨4762374, by rfl⟩ : syracuseStep 12699665 = 9524749) B9524749
theorem B1673239 : Blo 1672036 1673239 := bstep (se 1 (by rfl) ⟨1254929, by rfl⟩ : syracuseStep 1673239 = 2509859) B2509859
theorem B1673259 : Blo 1672036 1673259 := bstep (se 1 (by rfl) ⟨1254944, by rfl⟩ : syracuseStep 1673259 = 2509889) B2509889
theorem B1673271 : Blo 1672036 1673271 := bstep (se 1 (by rfl) ⟨1254953, by rfl⟩ : syracuseStep 1673271 = 2509907) B2509907
theorem B5646401 : Blo 1672036 5646401 := bstep (se 2 (by rfl) ⟨2117400, by rfl⟩ : syracuseStep 5646401 = 4234801) B4234801
theorem B12060737 : Blo 1672036 12060737 := bstep (se 2 (by rfl) ⟨4522776, by rfl⟩ : syracuseStep 12060737 = 9045553) B9045553
theorem B3762251 : Blo 1672036 3762251 := bstep (se 1 (by rfl) ⟨2821688, by rfl⟩ : syracuseStep 3762251 = 5643377) B5643377
theorem B2508875 : Blo 1672036 2508875 := bstep (se 1 (by rfl) ⟨1881656, by rfl⟩ : syracuseStep 2508875 = 3763313) B3763313
theorem B1673291 : Blo 1672036 1673291 := bstep (se 1 (by rfl) ⟨1254968, by rfl⟩ : syracuseStep 1673291 = 2509937) B2509937
theorem B2508887 : Blo 1672036 2508887 := bstep (se 1 (by rfl) ⟨1881665, by rfl⟩ : syracuseStep 2508887 = 3763331) B3763331
theorem B1673303 : Blo 1672036 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B1673323 : Blo 1672036 1673323 := bstep (se 1 (by rfl) ⟨1254992, by rfl⟩ : syracuseStep 1673323 = 2509985) B2509985
theorem B1673335 : Blo 1672036 1673335 := bstep (se 1 (by rfl) ⟨1255001, by rfl⟩ : syracuseStep 1673335 = 2510003) B2510003
theorem B3762305 : Blo 1672036 3762305 := bstep (se 2 (by rfl) ⟨1410864, by rfl⟩ : syracuseStep 3762305 = 2821729) B2821729
theorem B1673355 : Blo 1672036 1673355 := bstep (se 1 (by rfl) ⟨1255016, by rfl⟩ : syracuseStep 1673355 = 2510033) B2510033
theorem B1673367 : Blo 1672036 1673367 := bstep (se 1 (by rfl) ⟨1255025, by rfl⟩ : syracuseStep 1673367 = 2510051) B2510051
theorem B2508953 : Blo 1672036 2508953 := bstep (se 2 (by rfl) ⟨940857, by rfl⟩ : syracuseStep 2508953 = 1881715) B1881715
theorem B1673387 : Blo 1672036 1673387 := bstep (se 1 (by rfl) ⟨1255040, by rfl⟩ : syracuseStep 1673387 = 2510081) B2510081
theorem B1673399 : Blo 1672036 1673399 := bstep (se 1 (by rfl) ⟨1255049, by rfl⟩ : syracuseStep 1673399 = 2510099) B2510099
theorem B2009291 : Blo 1672036 2009291 := bstep (se 1 (by rfl) ⟨1506968, by rfl⟩ : syracuseStep 2009291 = 3013937) B3013937
theorem B1673419 : Blo 1672036 1673419 := bstep (se 1 (by rfl) ⟨1255064, by rfl⟩ : syracuseStep 1673419 = 2510129) B2510129
theorem B1673431 : Blo 1672036 1673431 := bstep (se 1 (by rfl) ⟨1255073, by rfl⟩ : syracuseStep 1673431 = 2510147) B2510147
theorem B1673451 : Blo 1672036 1673451 := bstep (se 1 (by rfl) ⟨1255088, by rfl⟩ : syracuseStep 1673451 = 2510177) B2510177
theorem B3574003 : Blo 1672036 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B1673463 : Blo 1672036 1673463 := bstep (se 1 (by rfl) ⟨1255097, by rfl⟩ : syracuseStep 1673463 = 2510195) B2510195
theorem B2509067 : Blo 1672036 2509067 := bstep (se 1 (by rfl) ⟨1881800, by rfl⟩ : syracuseStep 2509067 = 3763601) B3763601
theorem B1673483 : Blo 1672036 1673483 := bstep (se 1 (by rfl) ⟨1255112, by rfl⟩ : syracuseStep 1673483 = 2510225) B2510225
theorem B2509079 : Blo 1672036 2509079 := bstep (se 1 (by rfl) ⟨1881809, by rfl⟩ : syracuseStep 2509079 = 3763619) B3763619
theorem B1673495 : Blo 1672036 1673495 := bstep (se 1 (by rfl) ⟨1255121, by rfl⟩ : syracuseStep 1673495 = 2510243) B2510243
theorem B1673515 : Blo 1672036 1673515 := bstep (se 1 (by rfl) ⟨1255136, by rfl⟩ : syracuseStep 1673515 = 2510273) B2510273
theorem B25749805 : Blo 1672036 25749805 := bstep (se 3 (by rfl) ⟨4828088, by rfl⟩ : syracuseStep 25749805 = 9656177) B9656177
theorem B6351155 : Blo 1672036 6351155 := bstep (se 1 (by rfl) ⟨4763366, by rfl⟩ : syracuseStep 6351155 = 9526733) B9526733
theorem B1673527 : Blo 1672036 1673527 := bstep (se 1 (by rfl) ⟨1255145, by rfl⟩ : syracuseStep 1673527 = 2510291) B2510291
theorem B19048769 : Blo 1672036 19048769 := bstep (se 2 (by rfl) ⟨7143288, by rfl⟩ : syracuseStep 19048769 = 14286577) B14286577
theorem B6351169 : Blo 1672036 6351169 := bstep (se 2 (by rfl) ⟨2381688, by rfl⟩ : syracuseStep 6351169 = 4763377) B4763377
theorem B1673547 : Blo 1672036 1673547 := bstep (se 1 (by rfl) ⟨1255160, by rfl⟩ : syracuseStep 1673547 = 2510321) B2510321
theorem B1673559 : Blo 1672036 1673559 := bstep (se 1 (by rfl) ⟨1255169, by rfl⟩ : syracuseStep 1673559 = 2510339) B2510339
theorem B3762521 : Blo 1672036 3762521 := bstep (se 2 (by rfl) ⟨1410945, by rfl⟩ : syracuseStep 3762521 = 2821891) B2821891
theorem B2509145 : Blo 1672036 2509145 := bstep (se 2 (by rfl) ⟨940929, by rfl⟩ : syracuseStep 2509145 = 1881859) B1881859
theorem B1673579 : Blo 1672036 1673579 := bstep (se 1 (by rfl) ⟨1255184, by rfl⟩ : syracuseStep 1673579 = 2510369) B2510369
theorem B1673591 : Blo 1672036 1673591 := bstep (se 1 (by rfl) ⟨1255193, by rfl⟩ : syracuseStep 1673591 = 2510387) B2510387
theorem B1673611 : Blo 1672036 1673611 := bstep (se 1 (by rfl) ⟨1255208, by rfl⟩ : syracuseStep 1673611 = 2510417) B2510417
theorem B1673623 : Blo 1672036 1673623 := bstep (se 1 (by rfl) ⟨1255217, by rfl⟩ : syracuseStep 1673623 = 2510435) B2510435
theorem B1673643 : Blo 1672036 1673643 := bstep (se 1 (by rfl) ⟨1255232, by rfl⟩ : syracuseStep 1673643 = 2510465) B2510465
theorem B3762611 : Blo 1672036 3762611 := bstep (se 1 (by rfl) ⟨2821958, by rfl⟩ : syracuseStep 3762611 = 5643917) B5643917
theorem B1673655 : Blo 1672036 1673655 := bstep (se 1 (by rfl) ⟨1255241, by rfl⟩ : syracuseStep 1673655 = 2510483) B2510483
theorem B7145921 : Blo 1672036 7145921 := bstep (se 2 (by rfl) ⟨2679720, by rfl⟩ : syracuseStep 7145921 = 5359441) B5359441
theorem B2509259 : Blo 1672036 2509259 := bstep (se 1 (by rfl) ⟨1881944, by rfl⟩ : syracuseStep 2509259 = 3763889) B3763889
theorem B1673675 : Blo 1672036 1673675 := bstep (se 1 (by rfl) ⟨1255256, by rfl⟩ : syracuseStep 1673675 = 2510513) B2510513
theorem B3762647 : Blo 1672036 3762647 := bstep (se 1 (by rfl) ⟨2821985, by rfl⟩ : syracuseStep 3762647 = 5643971) B5643971
theorem B2509271 : Blo 1672036 2509271 := bstep (se 1 (by rfl) ⟨1881953, by rfl⟩ : syracuseStep 2509271 = 3763907) B3763907
theorem B13560281 : Blo 1672036 13560281 := bstep (se 2 (by rfl) ⟨5085105, by rfl⟩ : syracuseStep 13560281 = 10170211) B10170211
theorem B1673687 : Blo 1672036 1673687 := bstep (se 1 (by rfl) ⟨1255265, by rfl⟩ : syracuseStep 1673687 = 2510531) B2510531
theorem B1673707 : Blo 1672036 1673707 := bstep (se 1 (by rfl) ⟨1255280, by rfl⟩ : syracuseStep 1673707 = 2510561) B2510561
theorem B1673719 : Blo 1672036 1673719 := bstep (se 1 (by rfl) ⟨1255289, by rfl⟩ : syracuseStep 1673719 = 2510579) B2510579
theorem B1673739 : Blo 1672036 1673739 := bstep (se 1 (by rfl) ⟨1255304, by rfl⟩ : syracuseStep 1673739 = 2510609) B2510609
theorem B2009623 : Blo 1672036 2009623 := bstep (se 1 (by rfl) ⟨1507217, by rfl⟩ : syracuseStep 2009623 = 3014435) B3014435
theorem B1960471 : Blo 1672036 1960471 := bstep (se 1 (by rfl) ⟨1470353, by rfl⟩ : syracuseStep 1960471 = 2940707) B2940707
theorem B2509337 : Blo 1672036 2509337 := bstep (se 2 (by rfl) ⟨941001, by rfl⟩ : syracuseStep 2509337 = 1882003) B1882003
theorem B1673751 : Blo 1672036 1673751 := bstep (se 1 (by rfl) ⟨1255313, by rfl⟩ : syracuseStep 1673751 = 2510627) B2510627
theorem B1673771 : Blo 1672036 1673771 := bstep (se 1 (by rfl) ⟨1255328, by rfl⟩ : syracuseStep 1673771 = 2510657) B2510657
theorem B1673783 : Blo 1672036 1673783 := bstep (se 1 (by rfl) ⟨1255337, by rfl⟩ : syracuseStep 1673783 = 2510675) B2510675
theorem B1673803 : Blo 1672036 1673803 := bstep (se 1 (by rfl) ⟨1255352, by rfl⟩ : syracuseStep 1673803 = 2510705) B2510705
theorem B1673815 : Blo 1672036 1673815 := bstep (se 1 (by rfl) ⟨1255361, by rfl⟩ : syracuseStep 1673815 = 2510723) B2510723
theorem B5646941 : Blo 1672036 5646941 := bstep (se 3 (by rfl) ⟨1058801, by rfl⟩ : syracuseStep 5646941 = 2117603) B2117603
theorem B1673835 : Blo 1672036 1673835 := bstep (se 1 (by rfl) ⟨1255376, by rfl⟩ : syracuseStep 1673835 = 2510753) B2510753
theorem B1673847 : Blo 1672036 1673847 := bstep (se 1 (by rfl) ⟨1255385, by rfl⟩ : syracuseStep 1673847 = 2510771) B2510771
theorem B3762827 : Blo 1672036 3762827 := bstep (se 1 (by rfl) ⟨2822120, by rfl⟩ : syracuseStep 3762827 = 5644241) B5644241
theorem B2509451 : Blo 1672036 2509451 := bstep (se 1 (by rfl) ⟨1882088, by rfl⟩ : syracuseStep 2509451 = 3764177) B3764177
theorem B1673867 : Blo 1672036 1673867 := bstep (se 1 (by rfl) ⟨1255400, by rfl⟩ : syracuseStep 1673867 = 2510801) B2510801
theorem B2509463 : Blo 1672036 2509463 := bstep (se 1 (by rfl) ⟨1882097, by rfl⟩ : syracuseStep 2509463 = 3764195) B3764195
theorem B1673879 : Blo 1672036 1673879 := bstep (se 1 (by rfl) ⟨1255409, by rfl⟩ : syracuseStep 1673879 = 2510819) B2510819
theorem B1673899 : Blo 1672036 1673899 := bstep (se 1 (by rfl) ⟨1255424, by rfl⟩ : syracuseStep 1673899 = 2510849) B2510849
theorem B1673911 : Blo 1672036 1673911 := bstep (se 1 (by rfl) ⟨1255433, by rfl⟩ : syracuseStep 1673911 = 2510867) B2510867
theorem B3762881 : Blo 1672036 3762881 := bstep (se 2 (by rfl) ⟨1411080, by rfl⟩ : syracuseStep 3762881 = 2822161) B2822161
theorem B1673931 : Blo 1672036 1673931 := bstep (se 1 (by rfl) ⟨1255448, by rfl⟩ : syracuseStep 1673931 = 2510897) B2510897
theorem B1673943 : Blo 1672036 1673943 := bstep (se 1 (by rfl) ⟨1255457, by rfl⟩ : syracuseStep 1673943 = 2510915) B2510915
theorem B2509529 : Blo 1672036 2509529 := bstep (se 2 (by rfl) ⟨941073, by rfl⟩ : syracuseStep 2509529 = 1882147) B1882147
theorem B1673963 : Blo 1672036 1673963 := bstep (se 1 (by rfl) ⟨1255472, by rfl⟩ : syracuseStep 1673963 = 2510945) B2510945
theorem B1673975 : Blo 1672036 1673975 := bstep (se 1 (by rfl) ⟨1255481, by rfl⟩ : syracuseStep 1673975 = 2510963) B2510963
theorem B2116363 : Blo 1672036 2116363 := bstep (se 1 (by rfl) ⟨1587272, by rfl⟩ : syracuseStep 2116363 = 3174545) B3174545
theorem B1673995 : Blo 1672036 1673995 := bstep (se 1 (by rfl) ⟨1255496, by rfl⟩ : syracuseStep 1673995 = 2510993) B2510993
theorem B1674007 : Blo 1672036 1674007 := bstep (se 1 (by rfl) ⟨1255505, by rfl⟩ : syracuseStep 1674007 = 2511011) B2511011
theorem B1674027 : Blo 1672036 1674027 := bstep (se 1 (by rfl) ⟨1255520, by rfl⟩ : syracuseStep 1674027 = 2511041) B2511041
theorem B5802803 : Blo 1672036 5802803 := bstep (se 1 (by rfl) ⟨4352102, by rfl⟩ : syracuseStep 5802803 = 8704205) B8704205
theorem B8473409 : Blo 1672036 8473409 := bstep (se 2 (by rfl) ⟨3177528, by rfl⟩ : syracuseStep 8473409 = 6355057) B6355057
theorem B2509643 : Blo 1672036 2509643 := bstep (se 1 (by rfl) ⟨1882232, by rfl⟩ : syracuseStep 2509643 = 3764465) B3764465
theorem B2509655 : Blo 1672036 2509655 := bstep (se 1 (by rfl) ⟨1882241, by rfl⟩ : syracuseStep 2509655 = 3764483) B3764483
theorem B3763097 : Blo 1672036 3763097 := bstep (se 2 (by rfl) ⟨1411161, by rfl⟩ : syracuseStep 3763097 = 2822323) B2822323
theorem B2509721 : Blo 1672036 2509721 := bstep (se 2 (by rfl) ⟨941145, by rfl⟩ : syracuseStep 2509721 = 1882291) B1882291
theorem B4762547 : Blo 1672036 4762547 := bstep (se 1 (by rfl) ⟨3571910, by rfl⟩ : syracuseStep 4762547 = 7143821) B7143821
theorem B3763187 : Blo 1672036 3763187 := bstep (se 1 (by rfl) ⟨2822390, by rfl⟩ : syracuseStep 3763187 = 5644781) B5644781
theorem B2509835 : Blo 1672036 2509835 := bstep (se 1 (by rfl) ⟨1882376, by rfl⟩ : syracuseStep 2509835 = 3764753) B3764753
theorem B2116631 : Blo 1672036 2116631 := bstep (se 1 (by rfl) ⟨1587473, by rfl⟩ : syracuseStep 2116631 = 3174947) B3174947
theorem B3763223 : Blo 1672036 3763223 := bstep (se 1 (by rfl) ⟨2822417, by rfl⟩ : syracuseStep 3763223 = 5644835) B5644835
theorem B2509847 : Blo 1672036 2509847 := bstep (se 1 (by rfl) ⟨1882385, by rfl⟩ : syracuseStep 2509847 = 3764771) B3764771
theorem B12708899 : Blo 1672036 12708899 := bstep (se 1 (by rfl) ⟨9531674, by rfl⟩ : syracuseStep 12708899 = 19063349) B19063349
theorem B3574849 : Blo 1672036 3574849 := bstep (se 2 (by rfl) ⟨1340568, by rfl⟩ : syracuseStep 3574849 = 2681137) B2681137
theorem B2509913 : Blo 1672036 2509913 := bstep (se 2 (by rfl) ⟨941217, by rfl⟩ : syracuseStep 2509913 = 1882435) B1882435
theorem B3763403 : Blo 1672036 3763403 := bstep (se 1 (by rfl) ⟨2822552, by rfl⟩ : syracuseStep 3763403 = 5645105) B5645105
theorem B2510027 : Blo 1672036 2510027 := bstep (se 1 (by rfl) ⟨1882520, by rfl⟩ : syracuseStep 2510027 = 3765041) B3765041
theorem B2510039 : Blo 1672036 2510039 := bstep (se 1 (by rfl) ⟨1882529, by rfl⟩ : syracuseStep 2510039 = 3765059) B3765059
theorem B28601585 : Blo 1672036 28601585 := bstep (se 2 (by rfl) ⟨10725594, by rfl⟩ : syracuseStep 28601585 = 21451189) B21451189
theorem B3763457 : Blo 1672036 3763457 := bstep (se 2 (by rfl) ⟨1411296, by rfl⟩ : syracuseStep 3763457 = 2822593) B2822593
theorem B2510105 : Blo 1672036 2510105 := bstep (se 2 (by rfl) ⟨941289, by rfl⟩ : syracuseStep 2510105 = 1882579) B1882579
theorem B2714969 : Blo 1672036 2714969 := bstep (se 2 (by rfl) ⟨1018113, by rfl⟩ : syracuseStep 2714969 = 2036227) B2036227
theorem B8465795 : Blo 1672036 8465795 := bstep (se 1 (by rfl) ⟨6349346, by rfl⟩ : syracuseStep 8465795 = 12698693) B12698693
theorem B2510219 : Blo 1672036 2510219 := bstep (se 1 (by rfl) ⟨1882664, by rfl⟩ : syracuseStep 2510219 = 3765329) B3765329
theorem B2510231 : Blo 1672036 2510231 := bstep (se 1 (by rfl) ⟨1882673, by rfl⟩ : syracuseStep 2510231 = 3765347) B3765347
theorem B3575191 : Blo 1672036 3575191 := bstep (se 1 (by rfl) ⟨2681393, by rfl⟩ : syracuseStep 3575191 = 5362787) B5362787
theorem B3763673 : Blo 1672036 3763673 := bstep (se 2 (by rfl) ⟨1411377, by rfl⟩ : syracuseStep 3763673 = 2822755) B2822755
theorem B2510297 : Blo 1672036 2510297 := bstep (se 2 (by rfl) ⟨941361, by rfl⟩ : syracuseStep 2510297 = 1882723) B1882723
theorem B2821655 : Blo 1672036 2821655 := bstep (se 1 (by rfl) ⟨2116241, by rfl⟩ : syracuseStep 2821655 = 4232483) B4232483
theorem B3763763 : Blo 1672036 3763763 := bstep (se 1 (by rfl) ⟨2822822, by rfl⟩ : syracuseStep 3763763 = 5645645) B5645645
theorem B2510411 : Blo 1672036 2510411 := bstep (se 1 (by rfl) ⟨1882808, by rfl⟩ : syracuseStep 2510411 = 3765617) B3765617
theorem B3763799 : Blo 1672036 3763799 := bstep (se 1 (by rfl) ⟨2822849, by rfl⟩ : syracuseStep 3763799 = 5645699) B5645699
theorem B2510423 : Blo 1672036 2510423 := bstep (se 1 (by rfl) ⟨1882817, by rfl⟩ : syracuseStep 2510423 = 3765635) B3765635
theorem B2821783 : Blo 1672036 2821783 := bstep (se 1 (by rfl) ⟨2116337, by rfl⟩ : syracuseStep 2821783 = 4232675) B4232675
theorem B2510489 : Blo 1672036 2510489 := bstep (se 2 (by rfl) ⟨941433, by rfl⟩ : syracuseStep 2510489 = 1882867) B1882867
theorem B5648075 : Blo 1672036 5648075 := bstep (se 1 (by rfl) ⟨4236056, by rfl⟩ : syracuseStep 5648075 = 8472113) B8472113
theorem B2117335 : Blo 1672036 2117335 := bstep (se 1 (by rfl) ⟨1588001, by rfl⟩ : syracuseStep 2117335 = 3176003) B3176003
theorem B7630595 : Blo 1672036 7630595 := bstep (se 1 (by rfl) ⟨5722946, by rfl⟩ : syracuseStep 7630595 = 11445893) B11445893
theorem B3763979 : Blo 1672036 3763979 := bstep (se 1 (by rfl) ⟨2822984, by rfl⟩ : syracuseStep 3763979 = 5645969) B5645969
theorem B2510603 : Blo 1672036 2510603 := bstep (se 1 (by rfl) ⟨1882952, by rfl⟩ : syracuseStep 2510603 = 3765905) B3765905
theorem B2510615 : Blo 1672036 2510615 := bstep (se 1 (by rfl) ⟨1882961, by rfl⟩ : syracuseStep 2510615 = 3765923) B3765923
theorem B3764033 : Blo 1672036 3764033 := bstep (se 2 (by rfl) ⟨1411512, by rfl⟩ : syracuseStep 3764033 = 2823025) B2823025
theorem B2543447 : Blo 1672036 2543447 := bstep (se 1 (by rfl) ⟨1907585, by rfl⟩ : syracuseStep 2543447 = 3815171) B3815171
theorem B2510681 : Blo 1672036 2510681 := bstep (se 2 (by rfl) ⟨941505, by rfl⟩ : syracuseStep 2510681 = 1883011) B1883011
theorem B2510795 : Blo 1672036 2510795 := bstep (se 1 (by rfl) ⟨1883096, by rfl⟩ : syracuseStep 2510795 = 3766193) B3766193
theorem B2510807 : Blo 1672036 2510807 := bstep (se 1 (by rfl) ⟨1883105, by rfl⟩ : syracuseStep 2510807 = 3766211) B3766211
theorem B5648345 : Blo 1672036 5648345 := bstep (se 2 (by rfl) ⟨2118129, by rfl⟩ : syracuseStep 5648345 = 4236259) B4236259
theorem B3764249 : Blo 1672036 3764249 := bstep (se 2 (by rfl) ⟨1411593, by rfl⟩ : syracuseStep 3764249 = 2823187) B2823187
theorem B2510873 : Blo 1672036 2510873 := bstep (se 2 (by rfl) ⟨941577, by rfl⟩ : syracuseStep 2510873 = 1883155) B1883155
theorem B7147595 : Blo 1672036 7147595 := bstep (se 1 (by rfl) ⟨5360696, by rfl⟩ : syracuseStep 7147595 = 10721393) B10721393
theorem B3764339 : Blo 1672036 3764339 := bstep (se 1 (by rfl) ⟨2823254, by rfl⟩ : syracuseStep 3764339 = 5646509) B5646509
theorem B2510987 : Blo 1672036 2510987 := bstep (se 1 (by rfl) ⟨1883240, by rfl⟩ : syracuseStep 2510987 = 3766481) B3766481
theorem B54235277 : Blo 1672036 54235277 := bstep (se 3 (by rfl) ⟨10169114, by rfl⟩ : syracuseStep 54235277 = 20338229) B20338229
theorem B3764375 : Blo 1672036 3764375 := bstep (se 1 (by rfl) ⟨2823281, by rfl⟩ : syracuseStep 3764375 = 5646563) B5646563
theorem B18346135 : Blo 1672036 18346135 := bstep (se 1 (by rfl) ⟨13759601, by rfl⟩ : syracuseStep 18346135 = 27519203) B27519203
theorem B2510999 : Blo 1672036 2510999 := bstep (se 1 (by rfl) ⟨1883249, by rfl⟩ : syracuseStep 2510999 = 3766499) B3766499
theorem B6353099 : Blo 1672036 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B6353113 : Blo 1672036 6353113 := bstep (se 2 (by rfl) ⟨2382417, by rfl⟩ : syracuseStep 6353113 = 4764835) B4764835
theorem B10178777 : Blo 1672036 10178777 := bstep (se 2 (by rfl) ⟨3817041, by rfl⟩ : syracuseStep 10178777 = 7634083) B7634083
theorem B3174643 : Blo 1672036 3174643 := bstep (se 1 (by rfl) ⟨2380982, by rfl⟩ : syracuseStep 3174643 = 4761965) B4761965
theorem B2822411 : Blo 1672036 2822411 := bstep (se 1 (by rfl) ⟨2116808, by rfl⟩ : syracuseStep 2822411 = 4233617) B4233617
theorem B3764555 : Blo 1672036 3764555 := bstep (se 1 (by rfl) ⟨2823416, by rfl⟩ : syracuseStep 3764555 = 5646833) B5646833
theorem B3764609 : Blo 1672036 3764609 := bstep (se 2 (by rfl) ⟨1411728, by rfl⟩ : syracuseStep 3764609 = 2823457) B2823457
theorem B2822539 : Blo 1672036 2822539 := bstep (se 1 (by rfl) ⟨2116904, by rfl⟩ : syracuseStep 2822539 = 4233809) B4233809
theorem B12063127 : Blo 1672036 12063127 := bstep (se 1 (by rfl) ⟨9047345, by rfl⟩ : syracuseStep 12063127 = 18094691) B18094691
theorem B3174871 : Blo 1672036 3174871 := bstep (se 1 (by rfl) ⟨2381153, by rfl⟩ : syracuseStep 3174871 = 4762307) B4762307
theorem B2822681 : Blo 1672036 2822681 := bstep (se 2 (by rfl) ⟨1058505, by rfl⟩ : syracuseStep 2822681 = 2117011) B2117011
theorem B3174977 : Blo 1672036 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B3764825 : Blo 1672036 3764825 := bstep (se 2 (by rfl) ⟨1411809, by rfl⟩ : syracuseStep 3764825 = 2823619) B2823619
theorem B3814003 : Blo 1672036 3814003 := bstep (se 1 (by rfl) ⟨2860502, by rfl⟩ : syracuseStep 3814003 = 5721005) B5721005
theorem B7738001 : Blo 1672036 7738001 := bstep (se 2 (by rfl) ⟨2901750, by rfl⟩ : syracuseStep 7738001 = 5803501) B5803501
theorem B9040535 : Blo 1672036 9040535 := bstep (se 1 (by rfl) ⟨6780401, by rfl⟩ : syracuseStep 9040535 = 13560803) B13560803
theorem B5649047 : Blo 1672036 5649047 := bstep (se 1 (by rfl) ⟨4236785, by rfl⟩ : syracuseStep 5649047 = 8473571) B8473571
theorem B2822809 : Blo 1672036 2822809 := bstep (se 2 (by rfl) ⟨1058553, by rfl⟩ : syracuseStep 2822809 = 2117107) B2117107
theorem B3764915 : Blo 1672036 3764915 := bstep (se 1 (by rfl) ⟨2823686, by rfl⟩ : syracuseStep 3764915 = 5647373) B5647373
theorem B3764951 : Blo 1672036 3764951 := bstep (se 1 (by rfl) ⟨2823713, by rfl⟩ : syracuseStep 3764951 = 5647427) B5647427
theorem B3175129 : Blo 1672036 3175129 := bstep (se 2 (by rfl) ⟨1190673, by rfl⟩ : syracuseStep 3175129 = 2381347) B2381347
theorem B6435607 : Blo 1672036 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B4018967 : Blo 1672036 4018967 := bstep (se 1 (by rfl) ⟨3014225, by rfl⟩ : syracuseStep 4018967 = 6028451) B6028451
theorem B3765131 : Blo 1672036 3765131 := bstep (se 1 (by rfl) ⟨2823848, by rfl⟩ : syracuseStep 3765131 = 5647697) B5647697
theorem B3814295 : Blo 1672036 3814295 := bstep (se 1 (by rfl) ⟨2860721, by rfl⟩ : syracuseStep 3814295 = 5721443) B5721443
theorem B3765185 : Blo 1672036 3765185 := bstep (se 2 (by rfl) ⟨1411944, by rfl⟩ : syracuseStep 3765185 = 2823889) B2823889
theorem B1881067 : Blo 1672036 1881067 := bstep (se 1 (by rfl) ⟨1410800, by rfl⟩ : syracuseStep 1881067 = 2821601) B2821601
theorem B65205269 : Blo 1672036 65205269 := bstep (se 6 (by rfl) ⟨1528248, by rfl⟩ : syracuseStep 65205269 = 3056497) B3056497
theorem B1881175 : Blo 1672036 1881175 := bstep (se 1 (by rfl) ⟨1410881, by rfl⟩ : syracuseStep 1881175 = 2821763) B2821763
theorem B28980317 : Blo 1672036 28980317 := bstep (se 3 (by rfl) ⟨5433809, by rfl⟩ : syracuseStep 28980317 = 10867619) B10867619
theorem B6354071 : Blo 1672036 6354071 := bstep (se 1 (by rfl) ⟨4765553, by rfl⟩ : syracuseStep 6354071 = 9531107) B9531107
theorem B3765401 : Blo 1672036 3765401 := bstep (se 2 (by rfl) ⟨1412025, by rfl⟩ : syracuseStep 3765401 = 2824051) B2824051
theorem B4232371 : Blo 1672036 4232371 := bstep (se 1 (by rfl) ⟨3174278, by rfl⟩ : syracuseStep 4232371 = 6348557) B6348557
theorem B5649587 : Blo 1672036 5649587 := bstep (se 1 (by rfl) ⟨4237190, by rfl⟩ : syracuseStep 5649587 = 8474381) B8474381
theorem B2823383 : Blo 1672036 2823383 := bstep (se 1 (by rfl) ⟨2117537, by rfl⟩ : syracuseStep 2823383 = 4235075) B4235075
theorem B2381017 : Blo 1672036 2381017 := bstep (se 2 (by rfl) ⟨892881, by rfl⟩ : syracuseStep 2381017 = 1785763) B1785763
theorem B3765491 : Blo 1672036 3765491 := bstep (se 1 (by rfl) ⟨2824118, by rfl⟩ : syracuseStep 3765491 = 5648237) B5648237
theorem B1881355 : Blo 1672036 1881355 := bstep (se 1 (by rfl) ⟨1411016, by rfl⟩ : syracuseStep 1881355 = 2822033) B2822033
theorem B3765527 : Blo 1672036 3765527 := bstep (se 1 (by rfl) ⟨2824145, by rfl⟩ : syracuseStep 3765527 = 5648291) B5648291
theorem B4232513 : Blo 1672036 4232513 := bstep (se 2 (by rfl) ⟨1587192, by rfl⟩ : syracuseStep 4232513 = 3174385) B3174385
theorem B2823511 : Blo 1672036 2823511 := bstep (se 1 (by rfl) ⟨2117633, by rfl⟩ : syracuseStep 2823511 = 4235267) B4235267
theorem B7148893 : Blo 1672036 7148893 := bstep (se 3 (by rfl) ⟨1340417, by rfl⟩ : syracuseStep 7148893 = 2680835) B2680835
theorem B1881463 : Blo 1672036 1881463 := bstep (se 1 (by rfl) ⟨1411097, by rfl⟩ : syracuseStep 1881463 = 2822195) B2822195
theorem B5649857 : Blo 1672036 5649857 := bstep (se 2 (by rfl) ⟨2118696, by rfl⟩ : syracuseStep 5649857 = 4237393) B4237393
theorem B3765707 : Blo 1672036 3765707 := bstep (se 1 (by rfl) ⟨2824280, by rfl⟩ : syracuseStep 3765707 = 5648561) B5648561
theorem B3765761 : Blo 1672036 3765761 := bstep (se 2 (by rfl) ⟨1412160, by rfl⟩ : syracuseStep 3765761 = 2824321) B2824321
theorem B1881643 : Blo 1672036 1881643 := bstep (se 1 (by rfl) ⟨1411232, by rfl⟩ : syracuseStep 1881643 = 2822465) B2822465
theorem B5723713 : Blo 1672036 5723713 := bstep (se 2 (by rfl) ⟨2146392, by rfl⟩ : syracuseStep 5723713 = 4292785) B4292785
theorem B1881751 : Blo 1672036 1881751 := bstep (se 1 (by rfl) ⟨1411313, by rfl⟩ : syracuseStep 1881751 = 2822627) B2822627
theorem B7149235 : Blo 1672036 7149235 := bstep (se 1 (by rfl) ⟨5361926, by rfl⟩ : syracuseStep 7149235 = 10723853) B10723853
theorem B4290241 : Blo 1672036 4290241 := bstep (se 2 (by rfl) ⟨1608840, by rfl⟩ : syracuseStep 4290241 = 3217681) B3217681
theorem B36165325 : Blo 1672036 36165325 := bstep (se 3 (by rfl) ⟨6780998, by rfl⟩ : syracuseStep 36165325 = 13561997) B13561997
theorem B3765977 : Blo 1672036 3765977 := bstep (se 2 (by rfl) ⟨1412241, by rfl⟩ : syracuseStep 3765977 = 2824483) B2824483
theorem B4765405 : Blo 1672036 4765405 := bstep (se 3 (by rfl) ⟨893513, by rfl⟩ : syracuseStep 4765405 = 1787027) B1787027
theorem B6616849 : Blo 1672036 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B4765463 : Blo 1672036 4765463 := bstep (se 1 (by rfl) ⟨3574097, by rfl⟩ : syracuseStep 4765463 = 7148195) B7148195
theorem B3766067 : Blo 1672036 3766067 := bstep (se 1 (by rfl) ⟨2824550, by rfl⟩ : syracuseStep 3766067 = 5649101) B5649101
theorem B12703553 : Blo 1672036 12703553 := bstep (se 2 (by rfl) ⟨4763832, by rfl⟩ : syracuseStep 12703553 = 9527665) B9527665
theorem B1881931 : Blo 1672036 1881931 := bstep (se 1 (by rfl) ⟨1411448, by rfl⟩ : syracuseStep 1881931 = 2822897) B2822897
theorem B4020043 : Blo 1672036 4020043 := bstep (se 1 (by rfl) ⟨3015032, by rfl⟩ : syracuseStep 4020043 = 6030065) B6030065
theorem B3766103 : Blo 1672036 3766103 := bstep (se 1 (by rfl) ⟨2824577, by rfl⟩ : syracuseStep 3766103 = 5649155) B5649155
theorem B9533315 : Blo 1672036 9533315 := bstep (se 1 (by rfl) ⟨7149986, by rfl⟩ : syracuseStep 9533315 = 14299973) B14299973
theorem B7632785 : Blo 1672036 7632785 := bstep (se 2 (by rfl) ⟨2862294, by rfl⟩ : syracuseStep 7632785 = 5724589) B5724589
theorem B1882039 : Blo 1672036 1882039 := bstep (se 1 (by rfl) ⟨1411529, by rfl⟩ : syracuseStep 1882039 = 2823059) B2823059
theorem B2824139 : Blo 1672036 2824139 := bstep (se 1 (by rfl) ⟨2118104, by rfl⟩ : syracuseStep 2824139 = 4236209) B4236209
theorem B3176435 : Blo 1672036 3176435 := bstep (se 1 (by rfl) ⟨2382326, by rfl⟩ : syracuseStep 3176435 = 4764653) B4764653
theorem B3766283 : Blo 1672036 3766283 := bstep (se 1 (by rfl) ⟨2824712, by rfl⟩ : syracuseStep 3766283 = 5649425) B5649425
theorem B3766337 : Blo 1672036 3766337 := bstep (se 2 (by rfl) ⟨1412376, by rfl⟩ : syracuseStep 3766337 = 2824753) B2824753
theorem B2824267 : Blo 1672036 2824267 := bstep (se 1 (by rfl) ⟨2118200, by rfl⟩ : syracuseStep 2824267 = 4236401) B4236401
theorem B1882219 : Blo 1672036 1882219 := bstep (se 1 (by rfl) ⟨1411664, by rfl⟩ : syracuseStep 1882219 = 2823329) B2823329
theorem B3176587 : Blo 1672036 3176587 := bstep (se 1 (by rfl) ⟨2382440, by rfl⟩ : syracuseStep 3176587 = 4764881) B4764881
theorem B1882327 : Blo 1672036 1882327 := bstep (se 1 (by rfl) ⟨1411745, by rfl⟩ : syracuseStep 1882327 = 2823491) B2823491
theorem B2824409 : Blo 1672036 2824409 := bstep (se 2 (by rfl) ⟨1059153, by rfl⟩ : syracuseStep 2824409 = 2118307) B2118307
theorem B3766553 : Blo 1672036 3766553 := bstep (se 2 (by rfl) ⟨1412457, by rfl⟩ : syracuseStep 3766553 = 2824915) B2824915
theorem B9533771 : Blo 1672036 9533771 := bstep (se 1 (by rfl) ⟨7150328, by rfl⟩ : syracuseStep 9533771 = 14300657) B14300657
theorem B2382167 : Blo 1672036 2382167 := bstep (se 1 (by rfl) ⟨1786625, by rfl⟩ : syracuseStep 2382167 = 3573251) B3573251
theorem B2824537 : Blo 1672036 2824537 := bstep (se 2 (by rfl) ⟨1059201, by rfl⟩ : syracuseStep 2824537 = 2118403) B2118403
theorem B6355331 : Blo 1672036 6355331 := bstep (se 1 (by rfl) ⟨4766498, by rfl⟩ : syracuseStep 6355331 = 9532997) B9532997
theorem B1882507 : Blo 1672036 1882507 := bstep (se 1 (by rfl) ⟨1411880, by rfl⟩ : syracuseStep 1882507 = 2823761) B2823761
theorem B10721753 : Blo 1672036 10721753 := bstep (se 2 (by rfl) ⟨4020657, by rfl⟩ : syracuseStep 10721753 = 8041315) B8041315
theorem B3176921 : Blo 1672036 3176921 := bstep (se 2 (by rfl) ⟨1191345, by rfl⟩ : syracuseStep 3176921 = 2382691) B2382691
theorem B1882615 : Blo 1672036 1882615 := bstep (se 1 (by rfl) ⟨1411961, by rfl⟩ : syracuseStep 1882615 = 2823923) B2823923
theorem B7240195 : Blo 1672036 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B4233779 : Blo 1672036 4233779 := bstep (se 1 (by rfl) ⟨3175334, by rfl⟩ : syracuseStep 4233779 = 6350669) B6350669
theorem B25762373 : Blo 1672036 25762373 := bstep (se 4 (by rfl) ⟨2415222, by rfl⟩ : syracuseStep 25762373 = 4830445) B4830445
theorem B10173059 : Blo 1672036 10173059 := bstep (se 1 (by rfl) ⟨7629794, by rfl⟩ : syracuseStep 10173059 = 15259589) B15259589
theorem B2382475 : Blo 1672036 2382475 := bstep (se 1 (by rfl) ⟨1786856, by rfl⟩ : syracuseStep 2382475 = 3573713) B3573713
theorem B1882795 : Blo 1672036 1882795 := bstep (se 1 (by rfl) ⟨1412096, by rfl⟩ : syracuseStep 1882795 = 2824193) B2824193
theorem B6109955 : Blo 1672036 6109955 := bstep (se 1 (by rfl) ⟨4582466, by rfl⟩ : syracuseStep 6109955 = 9164933) B9164933
theorem B1882903 : Blo 1672036 1882903 := bstep (se 1 (by rfl) ⟨1412177, by rfl⟩ : syracuseStep 1882903 = 2824355) B2824355
theorem B7142195 : Blo 1672036 7142195 := bstep (se 1 (by rfl) ⟨5356646, by rfl⟩ : syracuseStep 7142195 = 10713293) B10713293
theorem B11443045 : Blo 1672036 11443045 := bstep (se 4 (by rfl) ⟨1072785, by rfl⟩ : syracuseStep 11443045 = 2145571) B2145571
theorem B1883083 : Blo 1672036 1883083 := bstep (se 1 (by rfl) ⟨1412312, by rfl⟩ : syracuseStep 1883083 = 2824625) B2824625
theorem B4766681 : Blo 1672036 4766681 := bstep (se 2 (by rfl) ⟨1787505, by rfl⟩ : syracuseStep 4766681 = 3575011) B3575011
theorem B3013633 : Blo 1672036 3013633 := bstep (se 2 (by rfl) ⟨1130112, by rfl⟩ : syracuseStep 3013633 = 2260225) B2260225
theorem B8469521 : Blo 1672036 8469521 := bstep (se 2 (by rfl) ⟨3176070, by rfl⟩ : syracuseStep 8469521 = 6352141) B6352141
theorem B19307555 : Blo 1672036 19307555 := bstep (se 1 (by rfl) ⟨14480666, by rfl⟩ : syracuseStep 19307555 = 28961333) B28961333
theorem B1883191 : Blo 1672036 1883191 := bstep (se 1 (by rfl) ⟨1412393, by rfl⟩ : syracuseStep 1883191 = 2824787) B2824787
theorem B4234315 : Blo 1672036 4234315 := bstep (se 1 (by rfl) ⟨3175736, by rfl⟩ : syracuseStep 4234315 = 6351473) B6351473
theorem B4766795 : Blo 1672036 4766795 := bstep (se 1 (by rfl) ⟨3575096, by rfl⟩ : syracuseStep 4766795 = 7150193) B7150193
theorem B3177559 : Blo 1672036 3177559 := bstep (se 1 (by rfl) ⟨2383169, by rfl⟩ : syracuseStep 3177559 = 4766339) B4766339
theorem B19061891 : Blo 1672036 19061891 := bstep (se 1 (by rfl) ⟨14296418, by rfl⟩ : syracuseStep 19061891 = 28592837) B28592837
theorem B7240877 : Blo 1672036 7240877 := bstep (se 3 (by rfl) ⟨1357664, by rfl⟩ : syracuseStep 7240877 = 2715329) B2715329
theorem B8469683 : Blo 1672036 8469683 := bstep (se 1 (by rfl) ⟨6352262, by rfl⟩ : syracuseStep 8469683 = 12704525) B12704525
theorem B4021427 : Blo 1672036 4021427 := bstep (se 1 (by rfl) ⟨3016070, by rfl⟩ : syracuseStep 4021427 = 6032141) B6032141
theorem B15269069 : Blo 1672036 15269069 := bstep (se 3 (by rfl) ⟨2862950, by rfl⟩ : syracuseStep 15269069 = 5725901) B5725901
theorem B4234457 : Blo 1672036 4234457 := bstep (se 2 (by rfl) ⟨1587921, by rfl⟩ : syracuseStep 4234457 = 3175843) B3175843
theorem B5643485 : Blo 1672036 5643485 := bstep (se 3 (by rfl) ⟨1058153, by rfl⟩ : syracuseStep 5643485 = 2116307) B2116307
theorem B6782297 : Blo 1672036 6782297 := bstep (se 2 (by rfl) ⟨2543361, by rfl⟩ : syracuseStep 6782297 = 5086723) B5086723
theorem B6872471 : Blo 1672036 6872471 := bstep (se 1 (by rfl) ⟨5154353, by rfl⟩ : syracuseStep 6872471 = 10308707) B10308707
theorem B3391051 : Blo 1672036 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B2383511 : Blo 1672036 2383511 := bstep (se 1 (by rfl) ⟨1787633, by rfl⟩ : syracuseStep 2383511 = 3575267) B3575267
theorem B3219097 : Blo 1672036 3219097 := bstep (se 2 (by rfl) ⟨1207161, by rfl⟩ : syracuseStep 3219097 = 2414323) B2414323
theorem B12705497 : Blo 1672036 12705497 := bstep (se 2 (by rfl) ⟨4764561, by rfl⟩ : syracuseStep 12705497 = 9529123) B9529123
theorem B6782737 : Blo 1672036 6782737 := bstep (se 2 (by rfl) ⟨2543526, by rfl⟩ : syracuseStep 6782737 = 5087053) B5087053
theorem B18087857 : Blo 1672036 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B5644349 : Blo 1672036 5644349 := bstep (se 3 (by rfl) ⟨1058315, by rfl⟩ : syracuseStep 5644349 = 2116631) B2116631
theorem B4292723 : Blo 1672036 4292723 := bstep (se 1 (by rfl) ⟨3219542, by rfl⟩ : syracuseStep 4292723 = 6439085) B6439085
theorem B3620999 : Blo 1672036 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B4235399 : Blo 1672036 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B4235449 : Blo 1672036 4235449 := bstep (se 2 (by rfl) ⟨1588293, by rfl⟩ : syracuseStep 4235449 = 3176587) B3176587
theorem B24461513 : Blo 1672036 24461513 := bstep (se 2 (by rfl) ⟨9173067, by rfl⟩ : syracuseStep 24461513 = 18346135) B18346135
theorem B12058913 : Blo 1672036 12058913 := bstep (se 2 (by rfl) ⟨4522092, by rfl⟩ : syracuseStep 12058913 = 9044185) B9044185
theorem B8470817 : Blo 1672036 8470817 := bstep (se 2 (by rfl) ⟨3176556, by rfl⟩ : syracuseStep 8470817 = 6353113) B6353113
theorem B34333073 : Blo 1672036 34333073 := bstep (se 2 (by rfl) ⟨12874902, by rfl⟩ : syracuseStep 34333073 = 25749805) B25749805
theorem B2679311 : Blo 1672036 2679311 := bstep (se 1 (by rfl) ⟨2009483, by rfl⟩ : syracuseStep 2679311 = 4018967) B4018967
theorem B5358109 : Blo 1672036 5358109 := bstep (se 3 (by rfl) ⟨1004645, by rfl⟩ : syracuseStep 5358109 = 2009291) B2009291
theorem B2679497 : Blo 1672036 2679497 := bstep (se 2 (by rfl) ⟨1004811, by rfl⟩ : syracuseStep 2679497 = 2009623) B2009623
theorem B2613961 : Blo 1672036 2613961 := bstep (se 2 (by rfl) ⟨980235, by rfl⟩ : syracuseStep 2613961 = 1960471) B1960471
theorem B4236047 : Blo 1672036 4236047 := bstep (se 1 (by rfl) ⟨3177035, by rfl⟩ : syracuseStep 4236047 = 6354071) B6354071
theorem B1672071 : Blo 1672036 1672071 := bstep (se 1 (by rfl) ⟨1254053, by rfl⟩ : syracuseStep 1672071 = 2508107) B2508107
theorem B1672079 : Blo 1672036 1672079 := bstep (se 1 (by rfl) ⟨1254059, by rfl⟩ : syracuseStep 1672079 = 2508119) B2508119
theorem B1672123 : Blo 1672036 1672123 := bstep (se 1 (by rfl) ⟨1254092, by rfl⟩ : syracuseStep 1672123 = 2508185) B2508185
theorem B1672199 : Blo 1672036 1672199 := bstep (se 1 (by rfl) ⟨1254149, by rfl⟩ : syracuseStep 1672199 = 2508299) B2508299
theorem B1672207 : Blo 1672036 1672207 := bstep (se 1 (by rfl) ⟨1254155, by rfl⟩ : syracuseStep 1672207 = 2508311) B2508311
theorem B1672251 : Blo 1672036 1672251 := bstep (se 1 (by rfl) ⟨1254188, by rfl⟩ : syracuseStep 1672251 = 2508377) B2508377
theorem B9045053 : Blo 1672036 9045053 := bstep (se 3 (by rfl) ⟨1695947, by rfl⟩ : syracuseStep 9045053 = 3391895) B3391895
theorem B1672327 : Blo 1672036 1672327 := bstep (se 1 (by rfl) ⟨1254245, by rfl⟩ : syracuseStep 1672327 = 2508491) B2508491
theorem B1672335 : Blo 1672036 1672335 := bstep (se 1 (by rfl) ⟨1254251, by rfl⟩ : syracuseStep 1672335 = 2508503) B2508503
theorem B1672379 : Blo 1672036 1672379 := bstep (se 1 (by rfl) ⟨1254284, by rfl⟩ : syracuseStep 1672379 = 2508569) B2508569
theorem B8471789 : Blo 1672036 8471789 := bstep (se 3 (by rfl) ⟨1588460, by rfl⟩ : syracuseStep 8471789 = 3176921) B3176921
theorem B1672455 : Blo 1672036 1672455 := bstep (se 1 (by rfl) ⟨1254341, by rfl⟩ : syracuseStep 1672455 = 2508683) B2508683
theorem B5088523 : Blo 1672036 5088523 := bstep (se 1 (by rfl) ⟨3816392, by rfl⟩ : syracuseStep 5088523 = 7632785) B7632785
theorem B1672463 : Blo 1672036 1672463 := bstep (se 1 (by rfl) ⟨1254347, by rfl⟩ : syracuseStep 1672463 = 2508695) B2508695
theorem B2508089 : Blo 1672036 2508089 := bstep (se 2 (by rfl) ⟨940533, by rfl⟩ : syracuseStep 2508089 = 1881067) B1881067
theorem B1672507 : Blo 1672036 1672507 := bstep (se 1 (by rfl) ⟨1254380, by rfl⟩ : syracuseStep 1672507 = 2508761) B2508761
theorem B2508167 : Blo 1672036 2508167 := bstep (se 1 (by rfl) ⟨1881125, by rfl⟩ : syracuseStep 2508167 = 3762251) B3762251
theorem B1672583 : Blo 1672036 1672583 := bstep (se 1 (by rfl) ⟨1254437, by rfl⟩ : syracuseStep 1672583 = 2508875) B2508875
theorem B1672591 : Blo 1672036 1672591 := bstep (se 1 (by rfl) ⟨1254443, by rfl⟩ : syracuseStep 1672591 = 2508887) B2508887
theorem B2508203 : Blo 1672036 2508203 := bstep (se 1 (by rfl) ⟨1881152, by rfl⟩ : syracuseStep 2508203 = 3762305) B3762305
theorem B5645753 : Blo 1672036 5645753 := bstep (se 2 (by rfl) ⟨2117157, by rfl⟩ : syracuseStep 5645753 = 4234315) B4234315
theorem B1672635 : Blo 1672036 1672635 := bstep (se 1 (by rfl) ⟨1254476, by rfl⟩ : syracuseStep 1672635 = 2508953) B2508953
theorem B2508233 : Blo 1672036 2508233 := bstep (se 2 (by rfl) ⟨940587, by rfl⟩ : syracuseStep 2508233 = 1881175) B1881175
theorem B4236745 : Blo 1672036 4236745 := bstep (se 2 (by rfl) ⟨1588779, by rfl⟩ : syracuseStep 4236745 = 3177559) B3177559
theorem B1672711 : Blo 1672036 1672711 := bstep (se 1 (by rfl) ⟨1254533, by rfl⟩ : syracuseStep 1672711 = 2509067) B2509067
theorem B1672719 : Blo 1672036 1672719 := bstep (se 1 (by rfl) ⟨1254539, by rfl⟩ : syracuseStep 1672719 = 2509079) B2509079
theorem B12699179 : Blo 1672036 12699179 := bstep (se 1 (by rfl) ⟨9524384, by rfl⟩ : syracuseStep 12699179 = 19048769) B19048769
theorem B2508347 : Blo 1672036 2508347 := bstep (se 1 (by rfl) ⟨1881260, by rfl⟩ : syracuseStep 2508347 = 3762521) B3762521
theorem B1672763 : Blo 1672036 1672763 := bstep (se 1 (by rfl) ⟨1254572, by rfl⟩ : syracuseStep 1672763 = 2509145) B2509145
theorem B4236887 : Blo 1672036 4236887 := bstep (se 1 (by rfl) ⟨3177665, by rfl⟩ : syracuseStep 4236887 = 6355331) B6355331
theorem B2508407 : Blo 1672036 2508407 := bstep (se 1 (by rfl) ⟨1881305, by rfl⟩ : syracuseStep 2508407 = 3762611) B3762611
theorem B1672839 : Blo 1672036 1672839 := bstep (se 1 (by rfl) ⟨1254629, by rfl⟩ : syracuseStep 1672839 = 2509259) B2509259
theorem B2508431 : Blo 1672036 2508431 := bstep (se 1 (by rfl) ⟨1881323, by rfl⟩ : syracuseStep 2508431 = 3762647) B3762647
theorem B1672847 : Blo 1672036 1672847 := bstep (se 1 (by rfl) ⟨1254635, by rfl⟩ : syracuseStep 1672847 = 2509271) B2509271
theorem B2508473 : Blo 1672036 2508473 := bstep (se 2 (by rfl) ⟨940677, by rfl⟩ : syracuseStep 2508473 = 1881355) B1881355
theorem B1672891 : Blo 1672036 1672891 := bstep (se 1 (by rfl) ⟨1254668, by rfl⟩ : syracuseStep 1672891 = 2509337) B2509337
theorem B4294345 : Blo 1672036 4294345 := bstep (se 2 (by rfl) ⟨1610379, by rfl⟩ : syracuseStep 4294345 = 3220759) B3220759
theorem B2508551 : Blo 1672036 2508551 := bstep (se 1 (by rfl) ⟨1881413, by rfl⟩ : syracuseStep 2508551 = 3762827) B3762827
theorem B1672967 : Blo 1672036 1672967 := bstep (se 1 (by rfl) ⟨1254725, by rfl⟩ : syracuseStep 1672967 = 2509451) B2509451
theorem B1672975 : Blo 1672036 1672975 := bstep (se 1 (by rfl) ⟨1254731, by rfl⟩ : syracuseStep 1672975 = 2509463) B2509463
theorem B2508587 : Blo 1672036 2508587 := bstep (se 1 (by rfl) ⟨1881440, by rfl⟩ : syracuseStep 2508587 = 3762881) B3762881
theorem B1673019 : Blo 1672036 1673019 := bstep (se 1 (by rfl) ⟨1254764, by rfl⟩ : syracuseStep 1673019 = 2509529) B2509529
theorem B2508617 : Blo 1672036 2508617 := bstep (se 2 (by rfl) ⟨940731, by rfl⟩ : syracuseStep 2508617 = 1881463) B1881463
theorem B4073303 : Blo 1672036 4073303 := bstep (se 1 (by rfl) ⟨3054977, by rfl⟩ : syracuseStep 4073303 = 6109955) B6109955
theorem B3868535 : Blo 1672036 3868535 := bstep (se 1 (by rfl) ⟨2901401, by rfl⟩ : syracuseStep 3868535 = 5802803) B5802803
theorem B1673095 : Blo 1672036 1673095 := bstep (se 1 (by rfl) ⟨1254821, by rfl⟩ : syracuseStep 1673095 = 2509643) B2509643
theorem B1673103 : Blo 1672036 1673103 := bstep (se 1 (by rfl) ⟨1254827, by rfl⟩ : syracuseStep 1673103 = 2509655) B2509655
theorem B2508731 : Blo 1672036 2508731 := bstep (se 1 (by rfl) ⟨1881548, by rfl⟩ : syracuseStep 2508731 = 3763097) B3763097
theorem B1673147 : Blo 1672036 1673147 := bstep (se 1 (by rfl) ⟨1254860, by rfl⟩ : syracuseStep 1673147 = 2509721) B2509721
theorem B2508791 : Blo 1672036 2508791 := bstep (se 1 (by rfl) ⟨1881593, by rfl⟩ : syracuseStep 2508791 = 3763187) B3763187
theorem B1673223 : Blo 1672036 1673223 := bstep (se 1 (by rfl) ⟨1254917, by rfl⟩ : syracuseStep 1673223 = 2509835) B2509835
theorem B5646347 : Blo 1672036 5646347 := bstep (se 1 (by rfl) ⟨4234760, by rfl⟩ : syracuseStep 5646347 = 8469521) B8469521
theorem B2508815 : Blo 1672036 2508815 := bstep (se 1 (by rfl) ⟨1881611, by rfl⟩ : syracuseStep 2508815 = 3763223) B3763223
theorem B1673231 : Blo 1672036 1673231 := bstep (se 1 (by rfl) ⟨1254923, by rfl⟩ : syracuseStep 1673231 = 2509847) B2509847
theorem B12871703 : Blo 1672036 12871703 := bstep (se 1 (by rfl) ⟨9653777, by rfl⟩ : syracuseStep 12871703 = 19307555) B19307555
theorem B8472599 : Blo 1672036 8472599 := bstep (se 1 (by rfl) ⟨6354449, by rfl⟩ : syracuseStep 8472599 = 12708899) B12708899
theorem B2508857 : Blo 1672036 2508857 := bstep (se 2 (by rfl) ⟨940821, by rfl⟩ : syracuseStep 2508857 = 1881643) B1881643
theorem B1673275 : Blo 1672036 1673275 := bstep (se 1 (by rfl) ⟨1254956, by rfl⟩ : syracuseStep 1673275 = 2509913) B2509913
theorem B12707927 : Blo 1672036 12707927 := bstep (se 1 (by rfl) ⟨9530945, by rfl⟩ : syracuseStep 12707927 = 19061891) B19061891
theorem B4827251 : Blo 1672036 4827251 := bstep (se 1 (by rfl) ⟨3620438, by rfl⟩ : syracuseStep 4827251 = 7240877) B7240877
theorem B5646455 : Blo 1672036 5646455 := bstep (se 1 (by rfl) ⟨4234841, by rfl⟩ : syracuseStep 5646455 = 8469683) B8469683
theorem B2680951 : Blo 1672036 2680951 := bstep (se 1 (by rfl) ⟨2010713, by rfl⟩ : syracuseStep 2680951 = 4021427) B4021427
theorem B2508935 : Blo 1672036 2508935 := bstep (se 1 (by rfl) ⟨1881701, by rfl⟩ : syracuseStep 2508935 = 3763403) B3763403
theorem B1673351 : Blo 1672036 1673351 := bstep (se 1 (by rfl) ⟨1255013, by rfl⟩ : syracuseStep 1673351 = 2510027) B2510027
theorem B1673359 : Blo 1672036 1673359 := bstep (se 1 (by rfl) ⟨1255019, by rfl⟩ : syracuseStep 1673359 = 2510039) B2510039
theorem B3762323 : Blo 1672036 3762323 := bstep (se 1 (by rfl) ⟨2821742, by rfl⟩ : syracuseStep 3762323 = 5643485) B5643485
theorem B2508971 : Blo 1672036 2508971 := bstep (se 1 (by rfl) ⟨1881728, by rfl⟩ : syracuseStep 2508971 = 3763457) B3763457
theorem B1673403 : Blo 1672036 1673403 := bstep (se 1 (by rfl) ⟨1255052, by rfl⟩ : syracuseStep 1673403 = 2510105) B2510105
theorem B3762377 : Blo 1672036 3762377 := bstep (se 2 (by rfl) ⟨1410891, by rfl⟩ : syracuseStep 3762377 = 2821783) B2821783
theorem B2509001 : Blo 1672036 2509001 := bstep (se 2 (by rfl) ⟨940875, by rfl⟩ : syracuseStep 2509001 = 1881751) B1881751
theorem B5720321 : Blo 1672036 5720321 := bstep (se 2 (by rfl) ⟨2145120, by rfl⟩ : syracuseStep 5720321 = 4290241) B4290241
theorem B1673479 : Blo 1672036 1673479 := bstep (se 1 (by rfl) ⟨1255109, by rfl⟩ : syracuseStep 1673479 = 2510219) B2510219
theorem B4581647 : Blo 1672036 4581647 := bstep (se 1 (by rfl) ⟨3436235, by rfl⟩ : syracuseStep 4581647 = 6872471) B6872471
theorem B1673487 : Blo 1672036 1673487 := bstep (se 1 (by rfl) ⟨1255115, by rfl⟩ : syracuseStep 1673487 = 2510231) B2510231
theorem B48220433 : Blo 1672036 48220433 := bstep (se 2 (by rfl) ⟨18082662, by rfl⟩ : syracuseStep 48220433 = 36165325) B36165325
theorem B2509115 : Blo 1672036 2509115 := bstep (se 1 (by rfl) ⟨1881836, by rfl⟩ : syracuseStep 2509115 = 3763673) B3763673
theorem B1673531 : Blo 1672036 1673531 := bstep (se 1 (by rfl) ⟨1255148, by rfl⟩ : syracuseStep 1673531 = 2510297) B2510297
theorem B2509175 : Blo 1672036 2509175 := bstep (se 1 (by rfl) ⟨1881881, by rfl⟩ : syracuseStep 2509175 = 3763763) B3763763
theorem B1673607 : Blo 1672036 1673607 := bstep (se 1 (by rfl) ⟨1255205, by rfl⟩ : syracuseStep 1673607 = 2510411) B2510411
theorem B2509199 : Blo 1672036 2509199 := bstep (se 1 (by rfl) ⟨1881899, by rfl⟩ : syracuseStep 2509199 = 3763799) B3763799
theorem B1673615 : Blo 1672036 1673615 := bstep (se 1 (by rfl) ⟨1255211, by rfl⟩ : syracuseStep 1673615 = 2510423) B2510423
theorem B2509241 : Blo 1672036 2509241 := bstep (se 2 (by rfl) ⟨940965, by rfl⟩ : syracuseStep 2509241 = 1881931) B1881931
theorem B5360057 : Blo 1672036 5360057 := bstep (se 2 (by rfl) ⟨2010021, by rfl⟩ : syracuseStep 5360057 = 4020043) B4020043
theorem B1673659 : Blo 1672036 1673659 := bstep (se 1 (by rfl) ⟨1255244, by rfl⟩ : syracuseStep 1673659 = 2510489) B2510489
theorem B4524473 : Blo 1672036 4524473 := bstep (se 2 (by rfl) ⟨1696677, by rfl⟩ : syracuseStep 4524473 = 3393355) B3393355
theorem B2509319 : Blo 1672036 2509319 := bstep (se 1 (by rfl) ⟨1881989, by rfl⟩ : syracuseStep 2509319 = 3763979) B3763979
theorem B1673735 : Blo 1672036 1673735 := bstep (se 1 (by rfl) ⟨1255301, by rfl⟩ : syracuseStep 1673735 = 2510603) B2510603
theorem B1673743 : Blo 1672036 1673743 := bstep (se 1 (by rfl) ⟨1255307, by rfl⟩ : syracuseStep 1673743 = 2510615) B2510615
theorem B2509355 : Blo 1672036 2509355 := bstep (se 1 (by rfl) ⟨1882016, by rfl⟩ : syracuseStep 2509355 = 3764033) B3764033
theorem B1673787 : Blo 1672036 1673787 := bstep (se 1 (by rfl) ⟨1255340, by rfl⟩ : syracuseStep 1673787 = 2510681) B2510681
theorem B2509385 : Blo 1672036 2509385 := bstep (se 2 (by rfl) ⟨941019, by rfl⟩ : syracuseStep 2509385 = 1882039) B1882039
theorem B1673863 : Blo 1672036 1673863 := bstep (se 1 (by rfl) ⟨1255397, by rfl⟩ : syracuseStep 1673863 = 2510795) B2510795
theorem B1673871 : Blo 1672036 1673871 := bstep (se 1 (by rfl) ⟨1255403, by rfl⟩ : syracuseStep 1673871 = 2510807) B2510807
theorem B2509499 : Blo 1672036 2509499 := bstep (se 1 (by rfl) ⟨1882124, by rfl⟩ : syracuseStep 2509499 = 3764249) B3764249
theorem B1673915 : Blo 1672036 1673915 := bstep (se 1 (by rfl) ⟨1255436, by rfl⟩ : syracuseStep 1673915 = 2510873) B2510873
theorem B5647049 : Blo 1672036 5647049 := bstep (se 2 (by rfl) ⟨2117643, by rfl⟩ : syracuseStep 5647049 = 4235287) B4235287
theorem B2509559 : Blo 1672036 2509559 := bstep (se 1 (by rfl) ⟨1882169, by rfl⟩ : syracuseStep 2509559 = 3764339) B3764339
theorem B1673991 : Blo 1672036 1673991 := bstep (se 1 (by rfl) ⟨1255493, by rfl⟩ : syracuseStep 1673991 = 2510987) B2510987
theorem B2509583 : Blo 1672036 2509583 := bstep (se 1 (by rfl) ⟨1882187, by rfl⟩ : syracuseStep 2509583 = 3764375) B3764375
theorem B1673999 : Blo 1672036 1673999 := bstep (se 1 (by rfl) ⟨1255499, by rfl⟩ : syracuseStep 1673999 = 2510999) B2510999
theorem B2509625 : Blo 1672036 2509625 := bstep (se 2 (by rfl) ⟨941109, by rfl⟩ : syracuseStep 2509625 = 1882219) B1882219
theorem B6785851 : Blo 1672036 6785851 := bstep (se 1 (by rfl) ⟨5089388, by rfl⟩ : syracuseStep 6785851 = 10178777) B10178777
theorem B3763079 : Blo 1672036 3763079 := bstep (se 1 (by rfl) ⟨2822309, by rfl⟩ : syracuseStep 3763079 = 5644619) B5644619
theorem B2509703 : Blo 1672036 2509703 := bstep (se 1 (by rfl) ⟨1882277, by rfl⟩ : syracuseStep 2509703 = 3764555) B3764555
theorem B2509739 : Blo 1672036 2509739 := bstep (se 1 (by rfl) ⟨1882304, by rfl⟩ : syracuseStep 2509739 = 3764609) B3764609
theorem B2509769 : Blo 1672036 2509769 := bstep (se 2 (by rfl) ⟨941163, by rfl⟩ : syracuseStep 2509769 = 1882327) B1882327
theorem B14298059 : Blo 1672036 14298059 := bstep (se 1 (by rfl) ⟨10723544, by rfl⟩ : syracuseStep 14298059 = 21447089) B21447089
theorem B3763259 : Blo 1672036 3763259 := bstep (se 1 (by rfl) ⟨2822444, by rfl⟩ : syracuseStep 3763259 = 5644889) B5644889
theorem B2509883 : Blo 1672036 2509883 := bstep (se 1 (by rfl) ⟨1882412, by rfl⟩ : syracuseStep 2509883 = 3764825) B3764825
theorem B6351959 : Blo 1672036 6351959 := bstep (se 1 (by rfl) ⟨4763969, by rfl⟩ : syracuseStep 6351959 = 9527939) B9527939
theorem B4762739 : Blo 1672036 4762739 := bstep (se 1 (by rfl) ⟨3572054, by rfl⟩ : syracuseStep 4762739 = 7144109) B7144109
theorem B2509943 : Blo 1672036 2509943 := bstep (se 1 (by rfl) ⟨1882457, by rfl⟩ : syracuseStep 2509943 = 3764915) B3764915
theorem B2509967 : Blo 1672036 2509967 := bstep (se 1 (by rfl) ⟨1882475, by rfl⟩ : syracuseStep 2509967 = 3764951) B3764951
theorem B3763385 : Blo 1672036 3763385 := bstep (se 2 (by rfl) ⟨1411269, by rfl⟩ : syracuseStep 3763385 = 2822539) B2822539
theorem B2510009 : Blo 1672036 2510009 := bstep (se 2 (by rfl) ⟨941253, by rfl⟩ : syracuseStep 2510009 = 1882507) B1882507
theorem B16084169 : Blo 1672036 16084169 := bstep (se 2 (by rfl) ⟨6031563, by rfl⟩ : syracuseStep 16084169 = 12063127) B12063127
theorem B2510087 : Blo 1672036 2510087 := bstep (se 1 (by rfl) ⟨1882565, by rfl⟩ : syracuseStep 2510087 = 3765131) B3765131
theorem B2510123 : Blo 1672036 2510123 := bstep (se 1 (by rfl) ⟨1882592, by rfl⟩ : syracuseStep 2510123 = 3765185) B3765185
theorem B2510153 : Blo 1672036 2510153 := bstep (se 2 (by rfl) ⟨941307, by rfl⟩ : syracuseStep 2510153 = 1882615) B1882615
theorem B9653593 : Blo 1672036 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B43470179 : Blo 1672036 43470179 := bstep (se 1 (by rfl) ⟨32602634, by rfl⟩ : syracuseStep 43470179 = 65205269) B65205269
theorem B5647751 : Blo 1672036 5647751 := bstep (se 1 (by rfl) ⟨4235813, by rfl⟩ : syracuseStep 5647751 = 8471627) B8471627
theorem B2010511 : Blo 1672036 2010511 := bstep (se 1 (by rfl) ⟨1507883, by rfl⟩ : syracuseStep 2010511 = 3015767) B3015767
theorem B19320211 : Blo 1672036 19320211 := bstep (se 1 (by rfl) ⟨14490158, by rfl⟩ : syracuseStep 19320211 = 28980317) B28980317
theorem B2510267 : Blo 1672036 2510267 := bstep (se 1 (by rfl) ⟨1882700, by rfl⟩ : syracuseStep 2510267 = 3765401) B3765401
theorem B2510327 : Blo 1672036 2510327 := bstep (se 1 (by rfl) ⟨1882745, by rfl⟩ : syracuseStep 2510327 = 3765491) B3765491
theorem B3763727 : Blo 1672036 3763727 := bstep (se 1 (by rfl) ⟨2822795, by rfl⟩ : syracuseStep 3763727 = 5645591) B5645591
theorem B2510351 : Blo 1672036 2510351 := bstep (se 1 (by rfl) ⟨1882763, by rfl⟩ : syracuseStep 2510351 = 3765527) B3765527
theorem B3763745 : Blo 1672036 3763745 := bstep (se 2 (by rfl) ⟨1411404, by rfl⟩ : syracuseStep 3763745 = 2822809) B2822809
theorem B2821675 : Blo 1672036 2821675 := bstep (se 1 (by rfl) ⟨2116256, by rfl⟩ : syracuseStep 2821675 = 4232513) B4232513
theorem B2510393 : Blo 1672036 2510393 := bstep (se 2 (by rfl) ⟨941397, by rfl⟩ : syracuseStep 2510393 = 1882795) B1882795
theorem B4763195 : Blo 1672036 4763195 := bstep (se 1 (by rfl) ⟨3572396, by rfl⟩ : syracuseStep 4763195 = 7144793) B7144793
theorem B6352445 : Blo 1672036 6352445 := bstep (se 3 (by rfl) ⟨1191083, by rfl⟩ : syracuseStep 6352445 = 2382167) B2382167
theorem B2510471 : Blo 1672036 2510471 := bstep (se 1 (by rfl) ⟨1882853, by rfl⟩ : syracuseStep 2510471 = 3765707) B3765707
theorem B2510507 : Blo 1672036 2510507 := bstep (se 1 (by rfl) ⟨1882880, by rfl⟩ : syracuseStep 2510507 = 3765761) B3765761
theorem B2821817 : Blo 1672036 2821817 := bstep (se 2 (by rfl) ⟨1058181, by rfl⟩ : syracuseStep 2821817 = 2116363) B2116363
theorem B8580809 : Blo 1672036 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B2510537 : Blo 1672036 2510537 := bstep (se 2 (by rfl) ⟨941451, by rfl⟩ : syracuseStep 2510537 = 1882903) B1882903
theorem B5648129 : Blo 1672036 5648129 := bstep (se 2 (by rfl) ⟨2118048, by rfl⟩ : syracuseStep 5648129 = 4236097) B4236097
theorem B15257393 : Blo 1672036 15257393 := bstep (se 2 (by rfl) ⟨5721522, by rfl⟩ : syracuseStep 15257393 = 11443045) B11443045
theorem B2510651 : Blo 1672036 2510651 := bstep (se 1 (by rfl) ⟨1882988, by rfl⟩ : syracuseStep 2510651 = 3765977) B3765977
theorem B3764087 : Blo 1672036 3764087 := bstep (se 1 (by rfl) ⟨2823065, by rfl⟩ : syracuseStep 3764087 = 5646131) B5646131
theorem B2510711 : Blo 1672036 2510711 := bstep (se 1 (by rfl) ⟨1883033, by rfl⟩ : syracuseStep 2510711 = 3766067) B3766067
theorem B2510735 : Blo 1672036 2510735 := bstep (se 1 (by rfl) ⟨1883051, by rfl⟩ : syracuseStep 2510735 = 3766103) B3766103
theorem B2510777 : Blo 1672036 2510777 := bstep (se 2 (by rfl) ⟨941541, by rfl⟩ : syracuseStep 2510777 = 1883083) B1883083
theorem B4018177 : Blo 1672036 4018177 := bstep (se 2 (by rfl) ⟨1506816, by rfl⟩ : syracuseStep 4018177 = 3013633) B3013633
theorem B2510855 : Blo 1672036 2510855 := bstep (se 1 (by rfl) ⟨1883141, by rfl⟩ : syracuseStep 2510855 = 3766283) B3766283
theorem B8466443 : Blo 1672036 8466443 := bstep (se 1 (by rfl) ⟨6349832, by rfl⟩ : syracuseStep 8466443 = 12699665) B12699665
theorem B3764267 : Blo 1672036 3764267 := bstep (se 1 (by rfl) ⟨2823200, by rfl⟩ : syracuseStep 3764267 = 5646401) B5646401
theorem B8040491 : Blo 1672036 8040491 := bstep (se 1 (by rfl) ⟨6030368, by rfl⟩ : syracuseStep 8040491 = 12060737) B12060737
theorem B2510891 : Blo 1672036 2510891 := bstep (se 1 (by rfl) ⟨1883168, by rfl⟩ : syracuseStep 2510891 = 3766337) B3766337
theorem B2510921 : Blo 1672036 2510921 := bstep (se 2 (by rfl) ⟨941595, by rfl⟩ : syracuseStep 2510921 = 1883191) B1883191
theorem B8466605 : Blo 1672036 8466605 := bstep (se 3 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 8466605 = 3174977) B3174977
theorem B2511035 : Blo 1672036 2511035 := bstep (se 1 (by rfl) ⟨1883276, by rfl⟩ : syracuseStep 2511035 = 3766553) B3766553
theorem B3174689 : Blo 1672036 3174689 := bstep (se 2 (by rfl) ⟨1190508, by rfl⟩ : syracuseStep 3174689 = 2381017) B2381017
theorem B4763947 : Blo 1672036 4763947 := bstep (se 1 (by rfl) ⟨3572960, by rfl⟩ : syracuseStep 4763947 = 7145921) B7145921
theorem B9040187 : Blo 1672036 9040187 := bstep (se 1 (by rfl) ⟨6780140, by rfl⟩ : syracuseStep 9040187 = 13560281) B13560281
theorem B7147835 : Blo 1672036 7147835 := bstep (se 1 (by rfl) ⟨5360876, by rfl⟩ : syracuseStep 7147835 = 10721753) B10721753
theorem B108532061 : Blo 1672036 108532061 := bstep (se 3 (by rfl) ⟨20349761, by rfl⟩ : syracuseStep 108532061 = 40699523) B40699523
theorem B2822519 : Blo 1672036 2822519 := bstep (se 1 (by rfl) ⟨2116889, by rfl⟩ : syracuseStep 2822519 = 4233779) B4233779
theorem B17174915 : Blo 1672036 17174915 := bstep (se 1 (by rfl) ⟨12881186, by rfl⟩ : syracuseStep 17174915 = 25762373) B25762373
theorem B3764627 : Blo 1672036 3764627 := bstep (se 1 (by rfl) ⟨2823470, by rfl⟩ : syracuseStep 3764627 = 5646941) B5646941
theorem B3764681 : Blo 1672036 3764681 := bstep (se 2 (by rfl) ⟨1411755, by rfl⟩ : syracuseStep 3764681 = 2823511) B2823511
theorem B9531857 : Blo 1672036 9531857 := bstep (se 2 (by rfl) ⟨3574446, by rfl⟩ : syracuseStep 9531857 = 7148893) B7148893
theorem B5648939 : Blo 1672036 5648939 := bstep (se 1 (by rfl) ⟨4236704, by rfl⟩ : syracuseStep 5648939 = 8473409) B8473409
theorem B4764221 : Blo 1672036 4764221 := bstep (se 3 (by rfl) ⟨893291, by rfl⟩ : syracuseStep 4764221 = 1786583) B1786583
theorem B3175031 : Blo 1672036 3175031 := bstep (se 1 (by rfl) ⟨2381273, by rfl⟩ : syracuseStep 3175031 = 4762547) B4762547
theorem B7631617 : Blo 1672036 7631617 := bstep (se 2 (by rfl) ⟨2861856, by rfl⟩ : syracuseStep 7631617 = 5723713) B5723713
theorem B10179379 : Blo 1672036 10179379 := bstep (se 1 (by rfl) ⟨7634534, by rfl⟩ : syracuseStep 10179379 = 15269069) B15269069
theorem B2822971 : Blo 1672036 2822971 := bstep (se 1 (by rfl) ⟨2117228, by rfl⟩ : syracuseStep 2822971 = 4234457) B4234457
theorem B19067723 : Blo 1672036 19067723 := bstep (se 1 (by rfl) ⟨14300792, by rfl⟩ : syracuseStep 19067723 = 28601585) B28601585
theorem B9532313 : Blo 1672036 9532313 := bstep (se 2 (by rfl) ⟨3574617, by rfl⟩ : syracuseStep 9532313 = 7149235) B7149235
theorem B2823113 : Blo 1672036 2823113 := bstep (se 2 (by rfl) ⟨1058667, by rfl⟩ : syracuseStep 2823113 = 2117335) B2117335
theorem B6353873 : Blo 1672036 6353873 := bstep (se 2 (by rfl) ⟨2382702, by rfl⟩ : syracuseStep 6353873 = 4765405) B4765405
theorem B1881103 : Blo 1672036 1881103 := bstep (se 1 (by rfl) ⟨1410827, by rfl⟩ : syracuseStep 1881103 = 2821655) B2821655
theorem B10171453 : Blo 1672036 10171453 := bstep (se 3 (by rfl) ⟨1907147, by rfl⟩ : syracuseStep 10171453 = 3814295) B3814295
theorem B3765383 : Blo 1672036 3765383 := bstep (se 1 (by rfl) ⟨2824037, by rfl⟩ : syracuseStep 3765383 = 5648075) B5648075
theorem B3765563 : Blo 1672036 3765563 := bstep (se 1 (by rfl) ⟨2824172, by rfl⟩ : syracuseStep 3765563 = 5648345) B5648345
theorem B4765063 : Blo 1672036 4765063 := bstep (se 1 (by rfl) ⟨3573797, by rfl⟩ : syracuseStep 4765063 = 7147595) B7147595
theorem B36156851 : Blo 1672036 36156851 := bstep (se 1 (by rfl) ⟨27117638, by rfl⟩ : syracuseStep 36156851 = 54235277) B54235277
theorem B3765689 : Blo 1672036 3765689 := bstep (se 2 (by rfl) ⟨1412133, by rfl⟩ : syracuseStep 3765689 = 2824267) B2824267
theorem B9655811 : Blo 1672036 9655811 := bstep (se 1 (by rfl) ⟨7241858, by rfl⟩ : syracuseStep 9655811 = 14483717) B14483717
theorem B1881607 : Blo 1672036 1881607 := bstep (se 1 (by rfl) ⟨1411205, by rfl⟩ : syracuseStep 1881607 = 2822411) B2822411
theorem B2823815 : Blo 1672036 2823815 := bstep (se 1 (by rfl) ⟨2117861, by rfl⟩ : syracuseStep 2823815 = 4235723) B4235723
theorem B4232857 : Blo 1672036 4232857 := bstep (se 2 (by rfl) ⟨1587321, by rfl⟩ : syracuseStep 4232857 = 3174643) B3174643
theorem B4765337 : Blo 1672036 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B1881787 : Blo 1672036 1881787 := bstep (se 1 (by rfl) ⟨1411340, by rfl⟩ : syracuseStep 1881787 = 2822681) B2822681
theorem B8468225 : Blo 1672036 8468225 := bstep (se 2 (by rfl) ⟨3175584, by rfl⟩ : syracuseStep 8468225 = 6351169) B6351169
theorem B8378113 : Blo 1672036 8378113 := bstep (se 2 (by rfl) ⟨3141792, by rfl⟩ : syracuseStep 8378113 = 6283585) B6283585
theorem B2381575 : Blo 1672036 2381575 := bstep (se 1 (by rfl) ⟨1786181, by rfl⟩ : syracuseStep 2381575 = 3572363) B3572363
theorem B5158667 : Blo 1672036 5158667 := bstep (se 1 (by rfl) ⟨3869000, by rfl⟩ : syracuseStep 5158667 = 7738001) B7738001
theorem B6027023 : Blo 1672036 6027023 := bstep (se 1 (by rfl) ⟨4520267, by rfl⟩ : syracuseStep 6027023 = 9040535) B9040535
theorem B3766031 : Blo 1672036 3766031 := bstep (se 1 (by rfl) ⟨2824523, by rfl⟩ : syracuseStep 3766031 = 5649047) B5649047
theorem B3766049 : Blo 1672036 3766049 := bstep (se 2 (by rfl) ⟨1412268, by rfl⟩ : syracuseStep 3766049 = 2824537) B2824537
theorem B4233019 : Blo 1672036 4233019 := bstep (se 1 (by rfl) ⟨3174764, by rfl⟩ : syracuseStep 4233019 = 6349529) B6349529
theorem B4233161 : Blo 1672036 4233161 := bstep (se 2 (by rfl) ⟨1587435, by rfl⟩ : syracuseStep 4233161 = 3174871) B3174871
theorem B3766391 : Blo 1672036 3766391 := bstep (se 1 (by rfl) ⟨2824793, by rfl⟩ : syracuseStep 3766391 = 5649587) B5649587
theorem B1882255 : Blo 1672036 1882255 := bstep (se 1 (by rfl) ⟨1411691, by rfl⟩ : syracuseStep 1882255 = 2823383) B2823383
theorem B5085337 : Blo 1672036 5085337 := bstep (se 2 (by rfl) ⟨1907001, by rfl⟩ : syracuseStep 5085337 = 3814003) B3814003
theorem B3176633 : Blo 1672036 3176633 := bstep (se 2 (by rfl) ⟨1191237, by rfl⟩ : syracuseStep 3176633 = 2382475) B2382475
theorem B7239917 : Blo 1672036 7239917 := bstep (se 3 (by rfl) ⟨1357484, by rfl⟩ : syracuseStep 7239917 = 2714969) B2714969
theorem B18086125 : Blo 1672036 18086125 := bstep (se 3 (by rfl) ⟨3391148, by rfl⟩ : syracuseStep 18086125 = 6782297) B6782297
theorem B2824463 : Blo 1672036 2824463 := bstep (se 1 (by rfl) ⟨2118347, by rfl⟩ : syracuseStep 2824463 = 4236695) B4236695
theorem B4233505 : Blo 1672036 4233505 := bstep (se 2 (by rfl) ⟨1587564, by rfl⟩ : syracuseStep 4233505 = 3175129) B3175129
theorem B3766571 : Blo 1672036 3766571 := bstep (se 1 (by rfl) ⟨2824928, by rfl⟩ : syracuseStep 3766571 = 5649857) B5649857
theorem B2382139 : Blo 1672036 2382139 := bstep (se 1 (by rfl) ⟨1786604, by rfl⟩ : syracuseStep 2382139 = 3573209) B3573209
theorem B7149971 : Blo 1672036 7149971 := bstep (se 1 (by rfl) ⟨5362478, by rfl⟩ : syracuseStep 7149971 = 10724957) B10724957
theorem B9525707 : Blo 1672036 9525707 := bstep (se 1 (by rfl) ⟨7144280, by rfl⟩ : syracuseStep 9525707 = 14288561) B14288561
theorem B3176975 : Blo 1672036 3176975 := bstep (se 1 (by rfl) ⟨2382731, by rfl⟩ : syracuseStep 3176975 = 4765463) B4765463
theorem B8469035 : Blo 1672036 8469035 := bstep (se 1 (by rfl) ⟨6351776, by rfl⟩ : syracuseStep 8469035 = 12703553) B12703553
theorem B7150123 : Blo 1672036 7150123 := bstep (se 1 (by rfl) ⟨5362592, by rfl⟩ : syracuseStep 7150123 = 10725185) B10725185
theorem B6355543 : Blo 1672036 6355543 := bstep (se 1 (by rfl) ⟨4766657, by rfl⟩ : syracuseStep 6355543 = 9533315) B9533315
theorem B1882759 : Blo 1672036 1882759 := bstep (se 1 (by rfl) ⟨1412069, by rfl⟩ : syracuseStep 1882759 = 2824139) B2824139
theorem B4766465 : Blo 1672036 4766465 := bstep (se 2 (by rfl) ⟨1787424, by rfl⟩ : syracuseStep 4766465 = 3574849) B3574849
theorem B1882939 : Blo 1672036 1882939 := bstep (se 1 (by rfl) ⟨1412204, by rfl⟩ : syracuseStep 1882939 = 2824409) B2824409
theorem B4234103 : Blo 1672036 4234103 := bstep (se 1 (by rfl) ⟨3175577, by rfl⟩ : syracuseStep 4234103 = 6351155) B6351155
theorem B6355847 : Blo 1672036 6355847 := bstep (se 1 (by rfl) ⟨4766885, by rfl⟩ : syracuseStep 6355847 = 9533771) B9533771
theorem B5643161 : Blo 1672036 5643161 := bstep (se 2 (by rfl) ⟨2116185, by rfl⟩ : syracuseStep 5643161 = 4232371) B4232371
theorem B8043581 : Blo 1672036 8043581 := bstep (se 3 (by rfl) ⟨1508171, by rfl⟩ : syracuseStep 8043581 = 3016343) B3016343
theorem B6356029 : Blo 1672036 6356029 := bstep (se 3 (by rfl) ⟨1191755, by rfl⟩ : syracuseStep 6356029 = 2383511) B2383511
theorem B6782039 : Blo 1672036 6782039 := bstep (se 1 (by rfl) ⟨5086529, by rfl⟩ : syracuseStep 6782039 = 10173059) B10173059
theorem B2383033 : Blo 1672036 2383033 := bstep (se 2 (by rfl) ⟨893637, by rfl⟩ : syracuseStep 2383033 = 1787275) B1787275
theorem B4766921 : Blo 1672036 4766921 := bstep (se 2 (by rfl) ⟨1787595, by rfl⟩ : syracuseStep 4766921 = 3575191) B3575191
theorem B3177787 : Blo 1672036 3177787 := bstep (se 1 (by rfl) ⟨2383340, by rfl⟩ : syracuseStep 3177787 = 4766681) B4766681
theorem B3177863 : Blo 1672036 3177863 := bstep (se 1 (by rfl) ⟨2383397, by rfl⟩ : syracuseStep 3177863 = 4766795) B4766795
theorem B4521401 : Blo 1672036 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B19045853 : Blo 1672036 19045853 := bstep (se 3 (by rfl) ⟨3571097, by rfl⟩ : syracuseStep 19045853 = 7142195) B7142195
theorem B4292129 : Blo 1672036 4292129 := bstep (se 2 (by rfl) ⟨1609548, by rfl⟩ : syracuseStep 4292129 = 3219097) B3219097
theorem B6782525 : Blo 1672036 6782525 := bstep (se 3 (by rfl) ⟨1271723, by rfl⟩ : syracuseStep 6782525 = 2543447) B2543447
theorem B5643863 : Blo 1672036 5643863 := bstep (se 1 (by rfl) ⟨4232897, by rfl⟩ : syracuseStep 5643863 = 8465795) B8465795
theorem B9043649 : Blo 1672036 9043649 := bstep (se 2 (by rfl) ⟨3391368, by rfl⟩ : syracuseStep 9043649 = 6782737) B6782737
theorem B8822465 : Blo 1672036 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B8470331 : Blo 1672036 8470331 := bstep (se 1 (by rfl) ⟨6352748, by rfl⟩ : syracuseStep 8470331 = 12705497) B12705497
theorem B5087063 : Blo 1672036 5087063 := bstep (se 1 (by rfl) ⟨3815297, by rfl⟩ : syracuseStep 5087063 = 7630595) B7630595
theorem B12058571 : Blo 1672036 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B8470493 : Blo 1672036 8470493 := bstep (se 3 (by rfl) ⟨1588217, by rfl⟩ : syracuseStep 8470493 = 3176435) B3176435
theorem B21430277 : Blo 1672036 21430277 := bstep (se 4 (by rfl) ⟨2009088, by rfl⟩ : syracuseStep 21430277 = 4018177) B4018177
theorem B5644295 : Blo 1672036 5644295 := bstep (se 1 (by rfl) ⟨4233221, by rfl⟩ : syracuseStep 5644295 = 8466443) B8466443
theorem B5644403 : Blo 1672036 5644403 := bstep (se 1 (by rfl) ⟨4233302, by rfl⟩ : syracuseStep 5644403 = 8466605) B8466605
theorem B22888715 : Blo 1672036 22888715 := bstep (se 1 (by rfl) ⟨17166536, by rfl⟩ : syracuseStep 22888715 = 34333073) B34333073
theorem B1786207 : Blo 1672036 1786207 := bstep (se 1 (by rfl) ⟨1339655, by rfl⟩ : syracuseStep 1786207 = 2679311) B2679311
theorem B5644673 : Blo 1672036 5644673 := bstep (se 2 (by rfl) ⟨2116752, by rfl⟩ : syracuseStep 5644673 = 4233505) B4233505
theorem B1786331 : Blo 1672036 1786331 := bstep (se 1 (by rfl) ⟨1339748, by rfl⟩ : syracuseStep 1786331 = 2679497) B2679497
theorem B4235915 : Blo 1672036 4235915 := bstep (se 1 (by rfl) ⟨3176936, by rfl⟩ : syracuseStep 4235915 = 6353873) B6353873
theorem B15254189 : Blo 1672036 15254189 := bstep (se 3 (by rfl) ⟨2860160, by rfl⟩ : syracuseStep 15254189 = 5720321) B5720321
theorem B7144145 : Blo 1672036 7144145 := bstep (se 2 (by rfl) ⟨2679054, by rfl⟩ : syracuseStep 7144145 = 5358109) B5358109
theorem B6030035 : Blo 1672036 6030035 := bstep (se 1 (by rfl) ⟨4522526, by rfl⟩ : syracuseStep 6030035 = 9045053) B9045053
theorem B1672059 : Blo 1672036 1672059 := bstep (se 1 (by rfl) ⟨1254044, by rfl⟩ : syracuseStep 1672059 = 2508089) B2508089
theorem B1672111 : Blo 1672036 1672111 := bstep (se 1 (by rfl) ⟨1254083, by rfl⟩ : syracuseStep 1672111 = 2508167) B2508167
theorem B1672135 : Blo 1672036 1672135 := bstep (se 1 (by rfl) ⟨1254101, by rfl⟩ : syracuseStep 1672135 = 2508203) B2508203
theorem B1672155 : Blo 1672036 1672155 := bstep (se 1 (by rfl) ⟨1254116, by rfl⟩ : syracuseStep 1672155 = 2508233) B2508233
theorem B10175489 : Blo 1672036 10175489 := bstep (se 2 (by rfl) ⟨3815808, by rfl⟩ : syracuseStep 10175489 = 7631617) B7631617
theorem B1672231 : Blo 1672036 1672231 := bstep (se 1 (by rfl) ⟨1254173, by rfl⟩ : syracuseStep 1672231 = 2508347) B2508347
theorem B1672271 : Blo 1672036 1672271 := bstep (se 1 (by rfl) ⟨1254203, by rfl⟩ : syracuseStep 1672271 = 2508407) B2508407
theorem B1672287 : Blo 1672036 1672287 := bstep (se 1 (by rfl) ⟨1254215, by rfl⟩ : syracuseStep 1672287 = 2508431) B2508431
theorem B1672315 : Blo 1672036 1672315 := bstep (se 1 (by rfl) ⟨1254236, by rfl⟩ : syracuseStep 1672315 = 2508473) B2508473
theorem B5645483 : Blo 1672036 5645483 := bstep (se 1 (by rfl) ⟨4234112, by rfl⟩ : syracuseStep 5645483 = 8468225) B8468225
theorem B1672367 : Blo 1672036 1672367 := bstep (se 1 (by rfl) ⟨1254275, by rfl⟩ : syracuseStep 1672367 = 2508551) B2508551
theorem B1672391 : Blo 1672036 1672391 := bstep (se 1 (by rfl) ⟨1254293, by rfl⟩ : syracuseStep 1672391 = 2508587) B2508587
theorem B1672411 : Blo 1672036 1672411 := bstep (se 1 (by rfl) ⟨1254308, by rfl⟩ : syracuseStep 1672411 = 2508617) B2508617
theorem B1672487 : Blo 1672036 1672487 := bstep (se 1 (by rfl) ⟨1254365, by rfl⟩ : syracuseStep 1672487 = 2508731) B2508731
theorem B1672527 : Blo 1672036 1672527 := bstep (se 1 (by rfl) ⟨1254395, by rfl⟩ : syracuseStep 1672527 = 2508791) B2508791
theorem B1672543 : Blo 1672036 1672543 := bstep (se 1 (by rfl) ⟨1254407, by rfl⟩ : syracuseStep 1672543 = 2508815) B2508815
theorem B2508137 : Blo 1672036 2508137 := bstep (se 2 (by rfl) ⟨940551, by rfl⟩ : syracuseStep 2508137 = 1881103) B1881103
theorem B1672571 : Blo 1672036 1672571 := bstep (se 1 (by rfl) ⟨1254428, by rfl⟩ : syracuseStep 1672571 = 2508857) B2508857
theorem B8471951 : Blo 1672036 8471951 := bstep (se 1 (by rfl) ⟨6353963, by rfl⟩ : syracuseStep 8471951 = 12707927) B12707927
theorem B1672623 : Blo 1672036 1672623 := bstep (se 1 (by rfl) ⟨1254467, by rfl⟩ : syracuseStep 1672623 = 2508935) B2508935
theorem B2508215 : Blo 1672036 2508215 := bstep (se 1 (by rfl) ⟨1881161, by rfl⟩ : syracuseStep 2508215 = 3762323) B3762323
theorem B1672647 : Blo 1672036 1672647 := bstep (se 1 (by rfl) ⟨1254485, by rfl⟩ : syracuseStep 1672647 = 2508971) B2508971
theorem B2508251 : Blo 1672036 2508251 := bstep (se 1 (by rfl) ⟨1881188, by rfl⟩ : syracuseStep 2508251 = 3762377) B3762377
theorem B1672667 : Blo 1672036 1672667 := bstep (se 1 (by rfl) ⟨1254500, by rfl⟩ : syracuseStep 1672667 = 2509001) B2509001
theorem B4826611 : Blo 1672036 4826611 := bstep (se 1 (by rfl) ⟨3619958, by rfl⟩ : syracuseStep 4826611 = 7239917) B7239917
theorem B32146955 : Blo 1672036 32146955 := bstep (se 1 (by rfl) ⟨24110216, by rfl⟩ : syracuseStep 32146955 = 48220433) B48220433
theorem B1672743 : Blo 1672036 1672743 := bstep (se 1 (by rfl) ⟨1254557, by rfl⟩ : syracuseStep 1672743 = 2509115) B2509115
theorem B1672783 : Blo 1672036 1672783 := bstep (se 1 (by rfl) ⟨1254587, by rfl⟩ : syracuseStep 1672783 = 2509175) B2509175
theorem B1672799 : Blo 1672036 1672799 := bstep (se 1 (by rfl) ⟨1254599, by rfl⟩ : syracuseStep 1672799 = 2509199) B2509199
theorem B1672827 : Blo 1672036 1672827 := bstep (se 1 (by rfl) ⟨1254620, by rfl⟩ : syracuseStep 1672827 = 2509241) B2509241
theorem B3573371 : Blo 1672036 3573371 := bstep (se 1 (by rfl) ⟨2680028, by rfl⟩ : syracuseStep 3573371 = 5360057) B5360057
theorem B3016315 : Blo 1672036 3016315 := bstep (se 1 (by rfl) ⟨2262236, by rfl⟩ : syracuseStep 3016315 = 4524473) B4524473
theorem B6350471 : Blo 1672036 6350471 := bstep (se 1 (by rfl) ⟨4762853, by rfl⟩ : syracuseStep 6350471 = 9525707) B9525707
theorem B1672879 : Blo 1672036 1672879 := bstep (se 1 (by rfl) ⟨1254659, by rfl⟩ : syracuseStep 1672879 = 2509319) B2509319
theorem B6784697 : Blo 1672036 6784697 := bstep (se 2 (by rfl) ⟨2544261, by rfl⟩ : syracuseStep 6784697 = 5088523) B5088523
theorem B5646023 : Blo 1672036 5646023 := bstep (se 1 (by rfl) ⟨4234517, by rfl⟩ : syracuseStep 5646023 = 8469035) B8469035
theorem B1672903 : Blo 1672036 1672903 := bstep (se 1 (by rfl) ⟨1254677, by rfl⟩ : syracuseStep 1672903 = 2509355) B2509355
theorem B1672923 : Blo 1672036 1672923 := bstep (se 1 (by rfl) ⟨1254692, by rfl⟩ : syracuseStep 1672923 = 2509385) B2509385
theorem B4237049 : Blo 1672036 4237049 := bstep (se 2 (by rfl) ⟨1588893, by rfl⟩ : syracuseStep 4237049 = 3177787) B3177787
theorem B12871457 : Blo 1672036 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B1672999 : Blo 1672036 1672999 := bstep (se 1 (by rfl) ⟨1254749, by rfl⟩ : syracuseStep 1672999 = 2509499) B2509499
theorem B1673039 : Blo 1672036 1673039 := bstep (se 1 (by rfl) ⟨1254779, by rfl⟩ : syracuseStep 1673039 = 2509559) B2509559
theorem B1673055 : Blo 1672036 1673055 := bstep (se 1 (by rfl) ⟨1254791, by rfl⟩ : syracuseStep 1673055 = 2509583) B2509583
theorem B1673083 : Blo 1672036 1673083 := bstep (se 1 (by rfl) ⟨1254812, by rfl⟩ : syracuseStep 1673083 = 2509625) B2509625
theorem B2508719 : Blo 1672036 2508719 := bstep (se 1 (by rfl) ⟨1881539, by rfl⟩ : syracuseStep 2508719 = 3763079) B3763079
theorem B1673135 : Blo 1672036 1673135 := bstep (se 1 (by rfl) ⟨1254851, by rfl⟩ : syracuseStep 1673135 = 2509703) B2509703
theorem B4237231 : Blo 1672036 4237231 := bstep (se 1 (by rfl) ⟨3177923, by rfl⟩ : syracuseStep 4237231 = 6355847) B6355847
theorem B3762107 : Blo 1672036 3762107 := bstep (se 1 (by rfl) ⟨2821580, by rfl⟩ : syracuseStep 3762107 = 5643161) B5643161
theorem B1673159 : Blo 1672036 1673159 := bstep (se 1 (by rfl) ⟨1254869, by rfl⟩ : syracuseStep 1673159 = 2509739) B2509739
theorem B1673179 : Blo 1672036 1673179 := bstep (se 1 (by rfl) ⟨1254884, by rfl⟩ : syracuseStep 1673179 = 2509769) B2509769
theorem B2508809 : Blo 1672036 2508809 := bstep (se 2 (by rfl) ⟨940803, by rfl⟩ : syracuseStep 2508809 = 1881607) B1881607
theorem B2508839 : Blo 1672036 2508839 := bstep (se 1 (by rfl) ⟨1881629, by rfl⟩ : syracuseStep 2508839 = 3763259) B3763259
theorem B1673255 : Blo 1672036 1673255 := bstep (se 1 (by rfl) ⟨1254941, by rfl⟩ : syracuseStep 1673255 = 2509883) B2509883
theorem B3762233 : Blo 1672036 3762233 := bstep (se 2 (by rfl) ⟨1410837, by rfl⟩ : syracuseStep 3762233 = 2821675) B2821675
theorem B1673295 : Blo 1672036 1673295 := bstep (se 1 (by rfl) ⟨1254971, by rfl⟩ : syracuseStep 1673295 = 2509943) B2509943
theorem B1673311 : Blo 1672036 1673311 := bstep (se 1 (by rfl) ⟨1254983, by rfl⟩ : syracuseStep 1673311 = 2509967) B2509967
theorem B2508923 : Blo 1672036 2508923 := bstep (se 1 (by rfl) ⟨1881692, by rfl⟩ : syracuseStep 2508923 = 3763385) B3763385
theorem B1673339 : Blo 1672036 1673339 := bstep (se 1 (by rfl) ⟨1255004, by rfl⟩ : syracuseStep 1673339 = 2510009) B2510009
theorem B1673391 : Blo 1672036 1673391 := bstep (se 1 (by rfl) ⟨1255043, by rfl⟩ : syracuseStep 1673391 = 2510087) B2510087
theorem B1673415 : Blo 1672036 1673415 := bstep (se 1 (by rfl) ⟨1255061, by rfl⟩ : syracuseStep 1673415 = 2510123) B2510123
theorem B1673435 : Blo 1672036 1673435 := bstep (se 1 (by rfl) ⟨1255076, by rfl⟩ : syracuseStep 1673435 = 2510153) B2510153
theorem B2509049 : Blo 1672036 2509049 := bstep (se 2 (by rfl) ⟨940893, by rfl⟩ : syracuseStep 2509049 = 1881787) B1881787
theorem B1673511 : Blo 1672036 1673511 := bstep (se 1 (by rfl) ⟨1255133, by rfl⟩ : syracuseStep 1673511 = 2510267) B2510267
theorem B1673551 : Blo 1672036 1673551 := bstep (se 1 (by rfl) ⟨1255163, by rfl⟩ : syracuseStep 1673551 = 2510327) B2510327
theorem B2509151 : Blo 1672036 2509151 := bstep (se 1 (by rfl) ⟨1881863, by rfl⟩ : syracuseStep 2509151 = 3763727) B3763727
theorem B1673567 : Blo 1672036 1673567 := bstep (se 1 (by rfl) ⟨1255175, by rfl⟩ : syracuseStep 1673567 = 2510351) B2510351
theorem B2509163 : Blo 1672036 2509163 := bstep (se 1 (by rfl) ⟨1881872, by rfl⟩ : syracuseStep 2509163 = 3763745) B3763745
theorem B2861419 : Blo 1672036 2861419 := bstep (se 1 (by rfl) ⟨2146064, by rfl⟩ : syracuseStep 2861419 = 4292129) B4292129
theorem B1673595 : Blo 1672036 1673595 := bstep (se 1 (by rfl) ⟨1255196, by rfl⟩ : syracuseStep 1673595 = 2510393) B2510393
theorem B3762575 : Blo 1672036 3762575 := bstep (se 1 (by rfl) ⟨2821931, by rfl⟩ : syracuseStep 3762575 = 5643863) B5643863
theorem B1673647 : Blo 1672036 1673647 := bstep (se 1 (by rfl) ⟨1255235, by rfl⟩ : syracuseStep 1673647 = 2510471) B2510471
theorem B1673671 : Blo 1672036 1673671 := bstep (se 1 (by rfl) ⟨1255253, by rfl⟩ : syracuseStep 1673671 = 2510507) B2510507
theorem B5720539 : Blo 1672036 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B1673691 : Blo 1672036 1673691 := bstep (se 1 (by rfl) ⟨1255268, by rfl⟩ : syracuseStep 1673691 = 2510537) B2510537
theorem B5646887 : Blo 1672036 5646887 := bstep (se 1 (by rfl) ⟨4235165, by rfl⟩ : syracuseStep 5646887 = 8470331) B8470331
theorem B1673767 : Blo 1672036 1673767 := bstep (se 1 (by rfl) ⟨1255325, by rfl⟩ : syracuseStep 1673767 = 2510651) B2510651
theorem B2509391 : Blo 1672036 2509391 := bstep (se 1 (by rfl) ⟨1882043, by rfl⟩ : syracuseStep 2509391 = 3764087) B3764087
theorem B1673807 : Blo 1672036 1673807 := bstep (se 1 (by rfl) ⟨1255355, by rfl⟩ : syracuseStep 1673807 = 2510711) B2510711
theorem B1673823 : Blo 1672036 1673823 := bstep (se 1 (by rfl) ⟨1255367, by rfl⟩ : syracuseStep 1673823 = 2510735) B2510735
theorem B1673851 : Blo 1672036 1673851 := bstep (se 1 (by rfl) ⟨1255388, by rfl⟩ : syracuseStep 1673851 = 2510777) B2510777
theorem B8039047 : Blo 1672036 8039047 := bstep (se 1 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 8039047 = 12058571) B12058571
theorem B5646995 : Blo 1672036 5646995 := bstep (se 1 (by rfl) ⟨4235246, by rfl⟩ : syracuseStep 5646995 = 8470493) B8470493
theorem B1673903 : Blo 1672036 1673903 := bstep (se 1 (by rfl) ⟨1255427, by rfl⟩ : syracuseStep 1673903 = 2510855) B2510855
theorem B2509511 : Blo 1672036 2509511 := bstep (se 1 (by rfl) ⟨1882133, by rfl⟩ : syracuseStep 2509511 = 3764267) B3764267
theorem B5360327 : Blo 1672036 5360327 := bstep (se 1 (by rfl) ⟨4020245, by rfl⟩ : syracuseStep 5360327 = 8040491) B8040491
theorem B1673927 : Blo 1672036 1673927 := bstep (se 1 (by rfl) ⟨1255445, by rfl⟩ : syracuseStep 1673927 = 2510891) B2510891
theorem B3762899 : Blo 1672036 3762899 := bstep (se 1 (by rfl) ⟨2822174, by rfl⟩ : syracuseStep 3762899 = 5644349) B5644349
theorem B1673947 : Blo 1672036 1673947 := bstep (se 1 (by rfl) ⟨1255460, by rfl⟩ : syracuseStep 1673947 = 2510921) B2510921
theorem B1674023 : Blo 1672036 1674023 := bstep (se 1 (by rfl) ⟨1255517, by rfl⟩ : syracuseStep 1674023 = 2511035) B2511035
theorem B3574601 : Blo 1672036 3574601 := bstep (se 2 (by rfl) ⟨1340475, by rfl⟩ : syracuseStep 3574601 = 2680951) B2680951
theorem B21449549 : Blo 1672036 21449549 := bstep (se 3 (by rfl) ⟨4021790, by rfl⟩ : syracuseStep 21449549 = 8043581) B8043581
theorem B2509673 : Blo 1672036 2509673 := bstep (se 2 (by rfl) ⟨941127, by rfl⟩ : syracuseStep 2509673 = 1882255) B1882255
theorem B2116459 : Blo 1672036 2116459 := bstep (se 1 (by rfl) ⟨1587344, by rfl⟩ : syracuseStep 2116459 = 3174689) B3174689
theorem B5647211 : Blo 1672036 5647211 := bstep (se 1 (by rfl) ⟨4235408, by rfl⟩ : syracuseStep 5647211 = 8470817) B8470817
theorem B72354707 : Blo 1672036 72354707 := bstep (se 1 (by rfl) ⟨54266030, by rfl⟩ : syracuseStep 72354707 = 108532061) B108532061
theorem B5647265 : Blo 1672036 5647265 := bstep (se 2 (by rfl) ⟨2117724, by rfl⟩ : syracuseStep 5647265 = 4235449) B4235449
theorem B2509751 : Blo 1672036 2509751 := bstep (se 1 (by rfl) ⟨1882313, by rfl⟩ : syracuseStep 2509751 = 3764627) B3764627
theorem B2509787 : Blo 1672036 2509787 := bstep (se 1 (by rfl) ⟨1882340, by rfl⟩ : syracuseStep 2509787 = 3764681) B3764681
theorem B12700637 : Blo 1672036 12700637 := bstep (se 3 (by rfl) ⟨2381369, by rfl⟩ : syracuseStep 12700637 = 4762739) B4762739
theorem B11447261 : Blo 1672036 11447261 := bstep (se 3 (by rfl) ⟨2146361, by rfl⟩ : syracuseStep 11447261 = 4292723) B4292723
theorem B6351929 : Blo 1672036 6351929 := bstep (se 2 (by rfl) ⟨2381973, by rfl⟩ : syracuseStep 6351929 = 4763947) B4763947
theorem B2116687 : Blo 1672036 2116687 := bstep (se 1 (by rfl) ⟨1587515, by rfl⟩ : syracuseStep 2116687 = 3175031) B3175031
theorem B32157101 : Blo 1672036 32157101 := bstep (se 3 (by rfl) ⟨6029456, by rfl⟩ : syracuseStep 32157101 = 12058913) B12058913
theorem B2510255 : Blo 1672036 2510255 := bstep (se 1 (by rfl) ⟨1882691, by rfl⟩ : syracuseStep 2510255 = 3765383) B3765383
theorem B8474057 : Blo 1672036 8474057 := bstep (se 2 (by rfl) ⟨3177771, by rfl⟩ : syracuseStep 8474057 = 6355543) B6355543
theorem B5647859 : Blo 1672036 5647859 := bstep (se 1 (by rfl) ⟨4235894, by rfl⟩ : syracuseStep 5647859 = 8471789) B8471789
theorem B2510345 : Blo 1672036 2510345 := bstep (se 2 (by rfl) ⟨941379, by rfl⟩ : syracuseStep 2510345 = 1882759) B1882759
theorem B2510375 : Blo 1672036 2510375 := bstep (se 1 (by rfl) ⟨1882781, by rfl⟩ : syracuseStep 2510375 = 3765563) B3765563
theorem B3485281 : Blo 1672036 3485281 := bstep (se 2 (by rfl) ⟨1306980, by rfl⟩ : syracuseStep 3485281 = 2613961) B2613961
theorem B24104567 : Blo 1672036 24104567 := bstep (se 1 (by rfl) ⟨18078425, by rfl⟩ : syracuseStep 24104567 = 36156851) B36156851
theorem B3763835 : Blo 1672036 3763835 := bstep (se 1 (by rfl) ⟨2822876, by rfl⟩ : syracuseStep 3763835 = 5645753) B5645753
theorem B2510459 : Blo 1672036 2510459 := bstep (se 1 (by rfl) ⟨1882844, by rfl⟩ : syracuseStep 2510459 = 3765689) B3765689
theorem B8466119 : Blo 1672036 8466119 := bstep (se 1 (by rfl) ⟨6349589, by rfl⟩ : syracuseStep 8466119 = 12699179) B12699179
theorem B3763961 : Blo 1672036 3763961 := bstep (se 2 (by rfl) ⟨1411485, by rfl⟩ : syracuseStep 3763961 = 2822971) B2822971
theorem B9047801 : Blo 1672036 9047801 := bstep (se 2 (by rfl) ⟨3392925, by rfl⟩ : syracuseStep 9047801 = 6785851) B6785851
theorem B2510585 : Blo 1672036 2510585 := bstep (se 2 (by rfl) ⟨941469, by rfl⟩ : syracuseStep 2510585 = 1882939) B1882939
theorem B4018015 : Blo 1672036 4018015 := bstep (se 1 (by rfl) ⟨3013511, by rfl⟩ : syracuseStep 4018015 = 6027023) B6027023
theorem B2510687 : Blo 1672036 2510687 := bstep (se 1 (by rfl) ⟨1883015, by rfl⟩ : syracuseStep 2510687 = 3766031) B3766031
theorem B2510699 : Blo 1672036 2510699 := bstep (se 1 (by rfl) ⟨1883024, by rfl⟩ : syracuseStep 2510699 = 3766049) B3766049
theorem B2715535 : Blo 1672036 2715535 := bstep (se 1 (by rfl) ⟨2036651, by rfl⟩ : syracuseStep 2715535 = 4073303) B4073303
theorem B2822107 : Blo 1672036 2822107 := bstep (se 1 (by rfl) ⟨2116580, by rfl⟩ : syracuseStep 2822107 = 4233161) B4233161
theorem B3764231 : Blo 1672036 3764231 := bstep (se 1 (by rfl) ⟨2823173, by rfl⟩ : syracuseStep 3764231 = 5646347) B5646347
theorem B8581135 : Blo 1672036 8581135 := bstep (se 1 (by rfl) ⟨6435851, by rfl⟩ : syracuseStep 8581135 = 12871703) B12871703
theorem B5648399 : Blo 1672036 5648399 := bstep (se 1 (by rfl) ⟨4236299, by rfl⟩ : syracuseStep 5648399 = 8472599) B8472599
theorem B3764303 : Blo 1672036 3764303 := bstep (se 1 (by rfl) ⟨2823227, by rfl⟩ : syracuseStep 3764303 = 5646455) B5646455
theorem B2510927 : Blo 1672036 2510927 := bstep (se 1 (by rfl) ⟨1883195, by rfl⟩ : syracuseStep 2510927 = 3766391) B3766391
theorem B13561937 : Blo 1672036 13561937 := bstep (se 2 (by rfl) ⟨5085726, by rfl⟩ : syracuseStep 13561937 = 10171453) B10171453
theorem B8474705 : Blo 1672036 8474705 := bstep (se 2 (by rfl) ⟨3178014, by rfl⟩ : syracuseStep 8474705 = 6356029) B6356029
theorem B2117755 : Blo 1672036 2117755 := bstep (se 1 (by rfl) ⟨1588316, by rfl⟩ : syracuseStep 2117755 = 3176633) B3176633
theorem B2511047 : Blo 1672036 2511047 := bstep (se 1 (by rfl) ⟨1883285, by rfl⟩ : syracuseStep 2511047 = 3766571) B3766571
theorem B2117983 : Blo 1672036 2117983 := bstep (se 1 (by rfl) ⟨1588487, by rfl⟩ : syracuseStep 2117983 = 3176975) B3176975
theorem B3764699 : Blo 1672036 3764699 := bstep (se 1 (by rfl) ⟨2823524, by rfl⟩ : syracuseStep 3764699 = 5647049) B5647049
theorem B6353417 : Blo 1672036 6353417 := bstep (se 2 (by rfl) ⟨2382531, by rfl⟩ : syracuseStep 6353417 = 4765063) B4765063
theorem B25760281 : Blo 1672036 25760281 := bstep (se 2 (by rfl) ⟨9660105, by rfl⟩ : syracuseStep 25760281 = 19320211) B19320211
theorem B2822735 : Blo 1672036 2822735 := bstep (se 1 (by rfl) ⟨2117051, by rfl⟩ : syracuseStep 2822735 = 4234103) B4234103
theorem B5648993 : Blo 1672036 5648993 := bstep (se 2 (by rfl) ⟨2118372, by rfl⟩ : syracuseStep 5648993 = 4236745) B4236745
theorem B9532039 : Blo 1672036 9532039 := bstep (se 1 (by rfl) ⟨7149029, by rfl⟩ : syracuseStep 9532039 = 14298059) B14298059
theorem B28980119 : Blo 1672036 28980119 := bstep (se 1 (by rfl) ⟨21735089, by rfl⟩ : syracuseStep 28980119 = 43470179) B43470179
theorem B3765167 : Blo 1672036 3765167 := bstep (se 1 (by rfl) ⟨2823875, by rfl⟩ : syracuseStep 3765167 = 5647751) B5647751
theorem B2118575 : Blo 1672036 2118575 := bstep (se 1 (by rfl) ⟨1588931, by rfl⟩ : syracuseStep 2118575 = 3177863) B3177863
theorem B11170817 : Blo 1672036 11170817 := bstep (se 2 (by rfl) ⟨4189056, by rfl⟩ : syracuseStep 11170817 = 8378113) B8378113
theorem B3175433 : Blo 1672036 3175433 := bstep (se 2 (by rfl) ⟨1190787, by rfl⟩ : syracuseStep 3175433 = 2381575) B2381575
theorem B3175463 : Blo 1672036 3175463 := bstep (se 1 (by rfl) ⟨2381597, by rfl⟩ : syracuseStep 3175463 = 4763195) B4763195
theorem B1881211 : Blo 1672036 1881211 := bstep (se 1 (by rfl) ⟨1410908, by rfl⟩ : syracuseStep 1881211 = 2821817) B2821817
theorem B3765419 : Blo 1672036 3765419 := bstep (se 1 (by rfl) ⟨2824064, by rfl⟩ : syracuseStep 3765419 = 5648129) B5648129
theorem B10171595 : Blo 1672036 10171595 := bstep (se 1 (by rfl) ⟨7628696, by rfl⟩ : syracuseStep 10171595 = 15257393) B15257393
theorem B2413999 : Blo 1672036 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B2823599 : Blo 1672036 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B16307675 : Blo 1672036 16307675 := bstep (se 1 (by rfl) ⟨12230756, by rfl⟩ : syracuseStep 16307675 = 24461513) B24461513
theorem B6780449 : Blo 1672036 6780449 := bstep (se 2 (by rfl) ⟨2542668, by rfl⟩ : syracuseStep 6780449 = 5085337) B5085337
theorem B4765223 : Blo 1672036 4765223 := bstep (se 1 (by rfl) ⟨3573917, by rfl⟩ : syracuseStep 4765223 = 7147835) B7147835
theorem B1881679 : Blo 1672036 1881679 := bstep (se 1 (by rfl) ⟨1411259, by rfl⟩ : syracuseStep 1881679 = 2822519) B2822519
theorem B11449943 : Blo 1672036 11449943 := bstep (se 1 (by rfl) ⟨8587457, by rfl⟩ : syracuseStep 11449943 = 17174915) B17174915
theorem B6354571 : Blo 1672036 6354571 := bstep (se 1 (by rfl) ⟨4765928, by rfl⟩ : syracuseStep 6354571 = 9531857) B9531857
theorem B24114833 : Blo 1672036 24114833 := bstep (se 2 (by rfl) ⟨9043062, by rfl⟩ : syracuseStep 24114833 = 18086125) B18086125
theorem B3765959 : Blo 1672036 3765959 := bstep (se 1 (by rfl) ⟨2824469, by rfl⟩ : syracuseStep 3765959 = 5648939) B5648939
theorem B3176147 : Blo 1672036 3176147 := bstep (se 1 (by rfl) ⟨2382110, by rfl⟩ : syracuseStep 3176147 = 4764221) B4764221
theorem B3176185 : Blo 1672036 3176185 := bstep (se 2 (by rfl) ⟨1191069, by rfl⟩ : syracuseStep 3176185 = 2382139) B2382139
theorem B2824031 : Blo 1672036 2824031 := bstep (se 1 (by rfl) ⟨2118023, by rfl⟩ : syracuseStep 2824031 = 4236047) B4236047
theorem B12711815 : Blo 1672036 12711815 := bstep (se 1 (by rfl) ⟨9533861, by rfl⟩ : syracuseStep 12711815 = 19067723) B19067723
theorem B6354875 : Blo 1672036 6354875 := bstep (se 1 (by rfl) ⟨4766156, by rfl⟩ : syracuseStep 6354875 = 9532313) B9532313
theorem B1882075 : Blo 1672036 1882075 := bstep (se 1 (by rfl) ⟨1411556, by rfl⟩ : syracuseStep 1882075 = 2823113) B2823113
theorem B9533497 : Blo 1672036 9533497 := bstep (se 2 (by rfl) ⟨3575061, by rfl⟩ : syracuseStep 9533497 = 7150123) B7150123
theorem B24107165 : Blo 1672036 24107165 := bstep (se 3 (by rfl) ⟨4520093, by rfl⟩ : syracuseStep 24107165 = 9040187) B9040187
theorem B6437207 : Blo 1672036 6437207 := bstep (se 1 (by rfl) ⟨4827905, by rfl⟩ : syracuseStep 6437207 = 9655811) B9655811
theorem B2824591 : Blo 1672036 2824591 := bstep (se 1 (by rfl) ⟨2118443, by rfl⟩ : syracuseStep 2824591 = 4236887) B4236887
theorem B13572505 : Blo 1672036 13572505 := bstep (se 2 (by rfl) ⟨5089689, by rfl⟩ : syracuseStep 13572505 = 10179379) B10179379
theorem B1882543 : Blo 1672036 1882543 := bstep (se 1 (by rfl) ⟨1411907, by rfl⟩ : syracuseStep 1882543 = 2823815) B2823815
theorem B3176891 : Blo 1672036 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B3439111 : Blo 1672036 3439111 := bstep (se 1 (by rfl) ⟨2579333, by rfl⟩ : syracuseStep 3439111 = 5158667) B5158667
theorem B2579023 : Blo 1672036 2579023 := bstep (se 1 (by rfl) ⟨1934267, by rfl⟩ : syracuseStep 2579023 = 3868535) B3868535
theorem B3218167 : Blo 1672036 3218167 := bstep (se 1 (by rfl) ⟨2413625, by rfl⟩ : syracuseStep 3218167 = 4827251) B4827251
theorem B3054431 : Blo 1672036 3054431 := bstep (se 1 (by rfl) ⟨2290823, by rfl⟩ : syracuseStep 3054431 = 4581647) B4581647
theorem B1882975 : Blo 1672036 1882975 := bstep (se 1 (by rfl) ⟨1412231, by rfl⟩ : syracuseStep 1882975 = 2824463) B2824463
theorem B3177377 : Blo 1672036 3177377 := bstep (se 2 (by rfl) ⟨1191516, by rfl⟩ : syracuseStep 3177377 = 2383033) B2383033
theorem B4766647 : Blo 1672036 4766647 := bstep (se 1 (by rfl) ⟨3574985, by rfl⟩ : syracuseStep 4766647 = 7149971) B7149971
theorem B3177643 : Blo 1672036 3177643 := bstep (se 1 (by rfl) ⟨2383232, by rfl⟩ : syracuseStep 3177643 = 4766465) B4766465
theorem B4521359 : Blo 1672036 4521359 := bstep (se 1 (by rfl) ⟨3391019, by rfl⟩ : syracuseStep 4521359 = 6782039) B6782039
theorem B4234639 : Blo 1672036 4234639 := bstep (se 1 (by rfl) ⟨3175979, by rfl⟩ : syracuseStep 4234639 = 6351959) B6351959
theorem B10722725 : Blo 1672036 10722725 := bstep (se 4 (by rfl) ⟨1005255, by rfl⟩ : syracuseStep 10722725 = 2010511) B2010511
theorem B10722779 : Blo 1672036 10722779 := bstep (se 1 (by rfl) ⟨8042084, by rfl⟩ : syracuseStep 10722779 = 16084169) B16084169
theorem B3177947 : Blo 1672036 3177947 := bstep (se 1 (by rfl) ⟨2383460, by rfl⟩ : syracuseStep 3177947 = 4766921) B4766921
theorem B5643809 : Blo 1672036 5643809 := bstep (se 2 (by rfl) ⟨2116428, by rfl⟩ : syracuseStep 5643809 = 4232857) B4232857
theorem B13565501 : Blo 1672036 13565501 := bstep (se 3 (by rfl) ⟨2543531, by rfl⟩ : syracuseStep 13565501 = 5087063) B5087063
theorem B5725793 : Blo 1672036 5725793 := bstep (se 2 (by rfl) ⟨2147172, by rfl⟩ : syracuseStep 5725793 = 4294345) B4294345
theorem B3014267 : Blo 1672036 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B12697235 : Blo 1672036 12697235 := bstep (se 1 (by rfl) ⟨9522926, by rfl⟩ : syracuseStep 12697235 = 19045853) B19045853
theorem B4521683 : Blo 1672036 4521683 := bstep (se 1 (by rfl) ⟨3391262, by rfl⟩ : syracuseStep 4521683 = 6782525) B6782525
theorem B4234963 : Blo 1672036 4234963 := bstep (se 1 (by rfl) ⟨3176222, by rfl⟩ : syracuseStep 4234963 = 6352445) B6352445
theorem B5644025 : Blo 1672036 5644025 := bstep (se 2 (by rfl) ⟨2116509, by rfl⟩ : syracuseStep 5644025 = 4233019) B4233019
theorem B6029099 : Blo 1672036 6029099 := bstep (se 1 (by rfl) ⟨4521824, by rfl⟩ : syracuseStep 6029099 = 9043649) B9043649
theorem B5881643 : Blo 1672036 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B14286851 : Blo 1672036 14286851 := bstep (se 1 (by rfl) ⟨10715138, by rfl⟩ : syracuseStep 14286851 = 21430277) B21430277
theorem B4235611 : Blo 1672036 4235611 := bstep (se 1 (by rfl) ⟨3176708, by rfl⟩ : syracuseStep 4235611 = 6353417) B6353417
theorem B27124253 : Blo 1672036 27124253 := bstep (se 3 (by rfl) ⟨5085797, by rfl⟩ : syracuseStep 27124253 = 10171595) B10171595
theorem B7627385 : Blo 1672036 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B6783659 : Blo 1672036 6783659 := bstep (se 1 (by rfl) ⟨5087744, by rfl⟩ : syracuseStep 6783659 = 10175489) B10175489
theorem B7447211 : Blo 1672036 7447211 := bstep (se 1 (by rfl) ⟨5585408, by rfl⟩ : syracuseStep 7447211 = 11170817) B11170817
theorem B1672091 : Blo 1672036 1672091 := bstep (se 1 (by rfl) ⟨1254068, by rfl⟩ : syracuseStep 1672091 = 2508137) B2508137
theorem B1672143 : Blo 1672036 1672143 := bstep (se 1 (by rfl) ⟨1254107, by rfl⟩ : syracuseStep 1672143 = 2508215) B2508215
theorem B1672167 : Blo 1672036 1672167 := bstep (se 1 (by rfl) ⟨1254125, by rfl⟩ : syracuseStep 1672167 = 2508251) B2508251
theorem B10871783 : Blo 1672036 10871783 := bstep (se 1 (by rfl) ⟨8153837, by rfl⟩ : syracuseStep 10871783 = 16307675) B16307675
theorem B21431303 : Blo 1672036 21431303 := bstep (se 1 (by rfl) ⟨16073477, by rfl⟩ : syracuseStep 21431303 = 32146955) B32146955
theorem B4523131 : Blo 1672036 4523131 := bstep (se 1 (by rfl) ⟨3392348, by rfl⟩ : syracuseStep 4523131 = 6784697) B6784697
theorem B1672479 : Blo 1672036 1672479 := bstep (se 1 (by rfl) ⟨1254359, by rfl⟩ : syracuseStep 1672479 = 2508719) B2508719
theorem B2508071 : Blo 1672036 2508071 := bstep (se 1 (by rfl) ⟨1881053, by rfl⟩ : syracuseStep 2508071 = 3762107) B3762107
theorem B4236583 : Blo 1672036 4236583 := bstep (se 1 (by rfl) ⟨3177437, by rfl⟩ : syracuseStep 4236583 = 6354875) B6354875
theorem B1672539 : Blo 1672036 1672539 := bstep (se 1 (by rfl) ⟨1254404, by rfl⟩ : syracuseStep 1672539 = 2508809) B2508809
theorem B1672559 : Blo 1672036 1672559 := bstep (se 1 (by rfl) ⟨1254419, by rfl⟩ : syracuseStep 1672559 = 2508839) B2508839
theorem B2508155 : Blo 1672036 2508155 := bstep (se 1 (by rfl) ⟨1881116, by rfl⟩ : syracuseStep 2508155 = 3762233) B3762233
theorem B1672615 : Blo 1672036 1672615 := bstep (se 1 (by rfl) ⟨1254461, by rfl⟩ : syracuseStep 1672615 = 2508923) B2508923
theorem B2508281 : Blo 1672036 2508281 := bstep (se 2 (by rfl) ⟨940605, by rfl⟩ : syracuseStep 2508281 = 1881211) B1881211
theorem B1672699 : Blo 1672036 1672699 := bstep (se 1 (by rfl) ⟨1254524, by rfl⟩ : syracuseStep 1672699 = 2509049) B2509049
theorem B4236857 : Blo 1672036 4236857 := bstep (se 2 (by rfl) ⟨1588821, by rfl⟩ : syracuseStep 4236857 = 3177643) B3177643
theorem B1672767 : Blo 1672036 1672767 := bstep (se 1 (by rfl) ⟨1254575, by rfl⟩ : syracuseStep 1672767 = 2509151) B2509151
theorem B1672775 : Blo 1672036 1672775 := bstep (se 1 (by rfl) ⟨1254581, by rfl⟩ : syracuseStep 1672775 = 2509163) B2509163
theorem B2508383 : Blo 1672036 2508383 := bstep (se 1 (by rfl) ⟨1881287, by rfl⟩ : syracuseStep 2508383 = 3762575) B3762575
theorem B8038045 : Blo 1672036 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B1672927 : Blo 1672036 1672927 := bstep (se 1 (by rfl) ⟨1254695, by rfl⟩ : syracuseStep 1672927 = 2509391) B2509391
theorem B1673007 : Blo 1672036 1673007 := bstep (se 1 (by rfl) ⟨1254755, by rfl⟩ : syracuseStep 1673007 = 2509511) B2509511
theorem B3573551 : Blo 1672036 3573551 := bstep (se 1 (by rfl) ⟨2680163, by rfl⟩ : syracuseStep 3573551 = 5360327) B5360327
theorem B2508599 : Blo 1672036 2508599 := bstep (se 1 (by rfl) ⟨1881449, by rfl⟩ : syracuseStep 2508599 = 3762899) B3762899
theorem B5646185 : Blo 1672036 5646185 := bstep (se 2 (by rfl) ⟨2117319, by rfl⟩ : syracuseStep 5646185 = 4234639) B4234639
theorem B1673115 : Blo 1672036 1673115 := bstep (se 1 (by rfl) ⟨1254836, by rfl⟩ : syracuseStep 1673115 = 2509673) B2509673
theorem B48236471 : Blo 1672036 48236471 := bstep (se 1 (by rfl) ⟨36177353, by rfl⟩ : syracuseStep 48236471 = 72354707) B72354707
theorem B1673167 : Blo 1672036 1673167 := bstep (se 1 (by rfl) ⟨1254875, by rfl⟩ : syracuseStep 1673167 = 2509751) B2509751
theorem B1673191 : Blo 1672036 1673191 := bstep (se 1 (by rfl) ⟨1254893, by rfl⟩ : syracuseStep 1673191 = 2509787) B2509787
theorem B2508905 : Blo 1672036 2508905 := bstep (se 2 (by rfl) ⟨940839, by rfl⟩ : syracuseStep 2508905 = 1881679) B1881679
theorem B4647041 : Blo 1672036 4647041 := bstep (se 2 (by rfl) ⟨1742640, by rfl⟩ : syracuseStep 4647041 = 3485281) B3485281
theorem B72386693 : Blo 1672036 72386693 := bstep (se 4 (by rfl) ⟨6786252, by rfl⟩ : syracuseStep 72386693 = 13572505) B13572505
theorem B8472761 : Blo 1672036 8472761 := bstep (se 2 (by rfl) ⟨3177285, by rfl⟩ : syracuseStep 8472761 = 6354571) B6354571
theorem B5646617 : Blo 1672036 5646617 := bstep (se 2 (by rfl) ⟨2117481, by rfl⟩ : syracuseStep 5646617 = 4234963) B4234963
theorem B1673503 : Blo 1672036 1673503 := bstep (se 1 (by rfl) ⟨1255127, by rfl⟩ : syracuseStep 1673503 = 2510255) B2510255
theorem B1673563 : Blo 1672036 1673563 := bstep (se 1 (by rfl) ⟨1255172, by rfl⟩ : syracuseStep 1673563 = 2510345) B2510345
theorem B3762539 : Blo 1672036 3762539 := bstep (se 1 (by rfl) ⟨2821904, by rfl⟩ : syracuseStep 3762539 = 5643809) B5643809
theorem B1673583 : Blo 1672036 1673583 := bstep (se 1 (by rfl) ⟨1255187, by rfl⟩ : syracuseStep 1673583 = 2510375) B2510375
theorem B2509223 : Blo 1672036 2509223 := bstep (se 1 (by rfl) ⟨1881917, by rfl⟩ : syracuseStep 2509223 = 3763835) B3763835
theorem B1673639 : Blo 1672036 1673639 := bstep (se 1 (by rfl) ⟨1255229, by rfl⟩ : syracuseStep 1673639 = 2510459) B2510459
theorem B8464823 : Blo 1672036 8464823 := bstep (se 1 (by rfl) ⟨6348617, by rfl⟩ : syracuseStep 8464823 = 12697235) B12697235
theorem B3762683 : Blo 1672036 3762683 := bstep (se 1 (by rfl) ⟨2822012, by rfl⟩ : syracuseStep 3762683 = 5644025) B5644025
theorem B2509307 : Blo 1672036 2509307 := bstep (se 1 (by rfl) ⟨1881980, by rfl⟩ : syracuseStep 2509307 = 3763961) B3763961
theorem B6031867 : Blo 1672036 6031867 := bstep (se 1 (by rfl) ⟨4523900, by rfl⟩ : syracuseStep 6031867 = 9047801) B9047801
theorem B1673723 : Blo 1672036 1673723 := bstep (se 1 (by rfl) ⟨1255292, by rfl⟩ : syracuseStep 1673723 = 2510585) B2510585
theorem B1673791 : Blo 1672036 1673791 := bstep (se 1 (by rfl) ⟨1255343, by rfl⟩ : syracuseStep 1673791 = 2510687) B2510687
theorem B1673799 : Blo 1672036 1673799 := bstep (se 1 (by rfl) ⟨1255349, by rfl⟩ : syracuseStep 1673799 = 2510699) B2510699
theorem B25741925 : Blo 1672036 25741925 := bstep (se 4 (by rfl) ⟨2413305, by rfl⟩ : syracuseStep 25741925 = 4826611) B4826611
theorem B3762809 : Blo 1672036 3762809 := bstep (se 2 (by rfl) ⟨1411053, by rfl⟩ : syracuseStep 3762809 = 2822107) B2822107
theorem B2509433 : Blo 1672036 2509433 := bstep (se 2 (by rfl) ⟨941037, by rfl⟩ : syracuseStep 2509433 = 1882075) B1882075
theorem B3762863 : Blo 1672036 3762863 := bstep (se 1 (by rfl) ⟨2822147, by rfl⟩ : syracuseStep 3762863 = 5644295) B5644295
theorem B2509487 : Blo 1672036 2509487 := bstep (se 1 (by rfl) ⟨1882115, by rfl⟩ : syracuseStep 2509487 = 3764231) B3764231
theorem B2509535 : Blo 1672036 2509535 := bstep (se 1 (by rfl) ⟨1882151, by rfl⟩ : syracuseStep 2509535 = 3764303) B3764303
theorem B1673951 : Blo 1672036 1673951 := bstep (se 1 (by rfl) ⟨1255463, by rfl⟩ : syracuseStep 1673951 = 2510927) B2510927
theorem B3762935 : Blo 1672036 3762935 := bstep (se 1 (by rfl) ⟨2822201, by rfl⟩ : syracuseStep 3762935 = 5644403) B5644403
theorem B1674031 : Blo 1672036 1674031 := bstep (se 1 (by rfl) ⟨1255523, by rfl⟩ : syracuseStep 1674031 = 2511047) B2511047
theorem B3763115 : Blo 1672036 3763115 := bstep (se 1 (by rfl) ⟨2822336, by rfl⟩ : syracuseStep 3763115 = 5644673) B5644673
theorem B2509799 : Blo 1672036 2509799 := bstep (se 1 (by rfl) ⟨1882349, by rfl⟩ : syracuseStep 2509799 = 3764699) B3764699
theorem B10169459 : Blo 1672036 10169459 := bstep (se 1 (by rfl) ⟨7627094, by rfl⟩ : syracuseStep 10169459 = 15254189) B15254189
theorem B4762763 : Blo 1672036 4762763 := bstep (se 1 (by rfl) ⟨3572072, by rfl⟩ : syracuseStep 4762763 = 7144145) B7144145
theorem B2510057 : Blo 1672036 2510057 := bstep (se 2 (by rfl) ⟨941271, by rfl⟩ : syracuseStep 2510057 = 1882543) B1882543
theorem B19320079 : Blo 1672036 19320079 := bstep (se 1 (by rfl) ⟨14490059, by rfl⟩ : syracuseStep 19320079 = 28980119) B28980119
theorem B2510111 : Blo 1672036 2510111 := bstep (se 1 (by rfl) ⟨1882583, by rfl⟩ : syracuseStep 2510111 = 3765167) B3765167
theorem B2116955 : Blo 1672036 2116955 := bstep (se 1 (by rfl) ⟨1587716, by rfl⟩ : syracuseStep 2116955 = 3175433) B3175433
theorem B3763655 : Blo 1672036 3763655 := bstep (se 1 (by rfl) ⟨2822741, by rfl⟩ : syracuseStep 3763655 = 5645483) B5645483
theorem B2510279 : Blo 1672036 2510279 := bstep (se 1 (by rfl) ⟨1882709, by rfl⟩ : syracuseStep 2510279 = 3765419) B3765419
theorem B10718729 : Blo 1672036 10718729 := bstep (se 2 (by rfl) ⟨4019523, by rfl⟩ : syracuseStep 10718729 = 8039047) B8039047
theorem B12709385 : Blo 1672036 12709385 := bstep (se 2 (by rfl) ⟨4766019, by rfl⟩ : syracuseStep 12709385 = 9532039) B9532039
theorem B5647967 : Blo 1672036 5647967 := bstep (se 1 (by rfl) ⟨4235975, by rfl⟩ : syracuseStep 5647967 = 8471951) B8471951
theorem B16076555 : Blo 1672036 16076555 := bstep (se 1 (by rfl) ⟨12057416, by rfl⟩ : syracuseStep 16076555 = 24114833) B24114833
theorem B2510633 : Blo 1672036 2510633 := bstep (se 2 (by rfl) ⟨941487, by rfl⟩ : syracuseStep 2510633 = 1882975) B1882975
theorem B3764015 : Blo 1672036 3764015 := bstep (se 1 (by rfl) ⟨2823011, by rfl⟩ : syracuseStep 3764015 = 5646023) B5646023
theorem B2510639 : Blo 1672036 2510639 := bstep (se 1 (by rfl) ⟨1882979, by rfl⟩ : syracuseStep 2510639 = 3765959) B3765959
theorem B2117431 : Blo 1672036 2117431 := bstep (se 1 (by rfl) ⟨1588073, by rfl⟩ : syracuseStep 2117431 = 3176147) B3176147
theorem B2821945 : Blo 1672036 2821945 := bstep (se 2 (by rfl) ⟨1058229, by rfl⟩ : syracuseStep 2821945 = 2116459) B2116459
theorem B8580971 : Blo 1672036 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B4763549 : Blo 1672036 4763549 := bstep (se 3 (by rfl) ⟨893165, by rfl⟩ : syracuseStep 4763549 = 1786331) B1786331
theorem B8474543 : Blo 1672036 8474543 := bstep (se 1 (by rfl) ⟨6355907, by rfl⟩ : syracuseStep 8474543 = 12711815) B12711815
theorem B2822249 : Blo 1672036 2822249 := bstep (se 2 (by rfl) ⟨1058343, by rfl⟩ : syracuseStep 2822249 = 2116687) B2116687
theorem B2117927 : Blo 1672036 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B3764591 : Blo 1672036 3764591 := bstep (se 1 (by rfl) ⟨2823443, by rfl⟩ : syracuseStep 3764591 = 5646887) B5646887
theorem B3764663 : Blo 1672036 3764663 := bstep (se 1 (by rfl) ⟨2823497, by rfl⟩ : syracuseStep 3764663 = 5646995) B5646995
theorem B14299699 : Blo 1672036 14299699 := bstep (se 1 (by rfl) ⟨10724774, by rfl⟩ : syracuseStep 14299699 = 21449549) B21449549
theorem B2036287 : Blo 1672036 2036287 := bstep (se 1 (by rfl) ⟨1527215, by rfl⟩ : syracuseStep 2036287 = 3054431) B3054431
theorem B3764807 : Blo 1672036 3764807 := bstep (se 1 (by rfl) ⟨2823605, by rfl⟩ : syracuseStep 3764807 = 5647211) B5647211
theorem B3764843 : Blo 1672036 3764843 := bstep (se 1 (by rfl) ⟨2823632, by rfl⟩ : syracuseStep 3764843 = 5647265) B5647265
theorem B2118251 : Blo 1672036 2118251 := bstep (se 1 (by rfl) ⟨1588688, by rfl⟩ : syracuseStep 2118251 = 3177377) B3177377
theorem B8467091 : Blo 1672036 8467091 := bstep (se 1 (by rfl) ⟨6350318, by rfl⟩ : syracuseStep 8467091 = 12700637) B12700637
theorem B7631507 : Blo 1672036 7631507 := bstep (se 1 (by rfl) ⟨5723630, by rfl⟩ : syracuseStep 7631507 = 11447261) B11447261
theorem B7148483 : Blo 1672036 7148483 := bstep (se 1 (by rfl) ⟨5361362, by rfl⟩ : syracuseStep 7148483 = 10722725) B10722725
theorem B5649371 : Blo 1672036 5649371 := bstep (se 1 (by rfl) ⟨4237028, by rfl⟩ : syracuseStep 5649371 = 8474057) B8474057
theorem B7148519 : Blo 1672036 7148519 := bstep (se 1 (by rfl) ⟨5361389, by rfl⟩ : syracuseStep 7148519 = 10722779) B10722779
theorem B2118631 : Blo 1672036 2118631 := bstep (se 1 (by rfl) ⟨1588973, by rfl⟩ : syracuseStep 2118631 = 3177947) B3177947
theorem B3765239 : Blo 1672036 3765239 := bstep (se 1 (by rfl) ⟨2823929, by rfl⟩ : syracuseStep 3765239 = 5647859) B5647859
theorem B16069711 : Blo 1672036 16069711 := bstep (se 1 (by rfl) ⟨12052283, by rfl⟩ : syracuseStep 16069711 = 24104567) B24104567
theorem B5649533 : Blo 1672036 5649533 := bstep (se 3 (by rfl) ⟨1059287, by rfl⟩ : syracuseStep 5649533 = 2118575) B2118575
theorem B4019399 : Blo 1672036 4019399 := bstep (se 1 (by rfl) ⟨3014549, by rfl⟩ : syracuseStep 4019399 = 6029099) B6029099
theorem B3921095 : Blo 1672036 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B5649641 : Blo 1672036 5649641 := bstep (se 2 (by rfl) ⟨2118615, by rfl⟩ : syracuseStep 5649641 = 4237231) B4237231
theorem B3765599 : Blo 1672036 3765599 := bstep (se 1 (by rfl) ⟨2824199, by rfl⟩ : syracuseStep 3765599 = 5648399) B5648399
theorem B11441513 : Blo 1672036 11441513 := bstep (se 2 (by rfl) ⟨4290567, by rfl⟩ : syracuseStep 11441513 = 8581135) B8581135
theorem B9041291 : Blo 1672036 9041291 := bstep (se 1 (by rfl) ⟨6780968, by rfl⟩ : syracuseStep 9041291 = 13561937) B13561937
theorem B5649803 : Blo 1672036 5649803 := bstep (se 1 (by rfl) ⟨4237352, by rfl⟩ : syracuseStep 5649803 = 8474705) B8474705
theorem B12711329 : Blo 1672036 12711329 := bstep (se 2 (by rfl) ⟨4766748, by rfl⟩ : syracuseStep 12711329 = 9533497) B9533497
theorem B8467901 : Blo 1672036 8467901 := bstep (se 3 (by rfl) ⟨1587731, by rfl⟩ : syracuseStep 8467901 = 3175463) B3175463
theorem B2823673 : Blo 1672036 2823673 := bstep (se 2 (by rfl) ⟨1058877, by rfl⟩ : syracuseStep 2823673 = 2117755) B2117755
theorem B1881823 : Blo 1672036 1881823 := bstep (se 1 (by rfl) ⟨1411367, by rfl⟩ : syracuseStep 1881823 = 2822735) B2822735
theorem B3765995 : Blo 1672036 3765995 := bstep (se 1 (by rfl) ⟨2824496, by rfl⟩ : syracuseStep 3765995 = 5648993) B5648993
theorem B2823943 : Blo 1672036 2823943 := bstep (se 1 (by rfl) ⟨2117957, by rfl⟩ : syracuseStep 2823943 = 4235915) B4235915
theorem B2381609 : Blo 1672036 2381609 := bstep (se 2 (by rfl) ⟨893103, by rfl⟩ : syracuseStep 2381609 = 1786207) B1786207
theorem B2823977 : Blo 1672036 2823977 := bstep (se 2 (by rfl) ⟨1058991, by rfl⟩ : syracuseStep 2823977 = 2117983) B2117983
theorem B4020023 : Blo 1672036 4020023 := bstep (se 1 (by rfl) ⟨3015017, by rfl⟩ : syracuseStep 4020023 = 6030035) B6030035
theorem B3815225 : Blo 1672036 3815225 := bstep (se 2 (by rfl) ⟨1430709, by rfl⟩ : syracuseStep 3815225 = 2861419) B2861419
theorem B3766121 : Blo 1672036 3766121 := bstep (se 2 (by rfl) ⟨1412295, by rfl⟩ : syracuseStep 3766121 = 2824591) B2824591
theorem B4585481 : Blo 1672036 4585481 := bstep (se 2 (by rfl) ⟨1719555, by rfl⟩ : syracuseStep 4585481 = 3439111) B3439111
theorem B61036573 : Blo 1672036 61036573 := bstep (se 3 (by rfl) ⟨11444357, by rfl⟩ : syracuseStep 61036573 = 22888715) B22888715
theorem B34347041 : Blo 1672036 34347041 := bstep (se 2 (by rfl) ⟨12880140, by rfl⟩ : syracuseStep 34347041 = 25760281) B25760281
theorem B3438697 : Blo 1672036 3438697 := bstep (se 2 (by rfl) ⟨1289511, by rfl⟩ : syracuseStep 3438697 = 2579023) B2579023
theorem B1882399 : Blo 1672036 1882399 := bstep (se 1 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 1882399 = 2823599) B2823599
theorem B4290889 : Blo 1672036 4290889 := bstep (se 2 (by rfl) ⟨1609083, by rfl⟩ : syracuseStep 4290889 = 3218167) B3218167
theorem B4520299 : Blo 1672036 4520299 := bstep (se 1 (by rfl) ⟨3390224, by rfl⟩ : syracuseStep 4520299 = 6780449) B6780449
theorem B3176815 : Blo 1672036 3176815 := bstep (se 1 (by rfl) ⟨2382611, by rfl⟩ : syracuseStep 3176815 = 4765223) B4765223
theorem B7633295 : Blo 1672036 7633295 := bstep (se 1 (by rfl) ⟨5724971, by rfl⟩ : syracuseStep 7633295 = 11449943) B11449943
theorem B2382247 : Blo 1672036 2382247 := bstep (se 1 (by rfl) ⟨1786685, by rfl⟩ : syracuseStep 2382247 = 3573371) B3573371
theorem B4233647 : Blo 1672036 4233647 := bstep (se 1 (by rfl) ⟨3175235, by rfl⟩ : syracuseStep 4233647 = 6350471) B6350471
theorem B2824699 : Blo 1672036 2824699 := bstep (se 1 (by rfl) ⟨2118524, by rfl⟩ : syracuseStep 2824699 = 4237049) B4237049
theorem B1882687 : Blo 1672036 1882687 := bstep (se 1 (by rfl) ⟨1412015, by rfl⟩ : syracuseStep 1882687 = 2824031) B2824031
theorem B6355529 : Blo 1672036 6355529 := bstep (se 2 (by rfl) ⟨2383323, by rfl⟩ : syracuseStep 6355529 = 4766647) B4766647
theorem B16071443 : Blo 1672036 16071443 := bstep (se 1 (by rfl) ⟨12053582, by rfl⟩ : syracuseStep 16071443 = 24107165) B24107165
theorem B4291471 : Blo 1672036 4291471 := bstep (se 1 (by rfl) ⟨3218603, by rfl⟩ : syracuseStep 4291471 = 6437207) B6437207
theorem B2383067 : Blo 1672036 2383067 := bstep (se 1 (by rfl) ⟨1787300, by rfl⟩ : syracuseStep 2383067 = 3574601) B3574601
theorem B12057821 : Blo 1672036 12057821 := bstep (se 3 (by rfl) ⟨2260841, by rfl⟩ : syracuseStep 12057821 = 4521683) B4521683
theorem B3218665 : Blo 1672036 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B4234619 : Blo 1672036 4234619 := bstep (se 1 (by rfl) ⟨3175964, by rfl⟩ : syracuseStep 4234619 = 6351929) B6351929
theorem B4021753 : Blo 1672036 4021753 := bstep (se 2 (by rfl) ⟨1508157, by rfl⟩ : syracuseStep 4021753 = 3016315) B3016315
theorem B3014239 : Blo 1672036 3014239 := bstep (se 1 (by rfl) ⟨2260679, by rfl⟩ : syracuseStep 3014239 = 4521359) B4521359
theorem B21438067 : Blo 1672036 21438067 := bstep (se 1 (by rfl) ⟨16078550, by rfl⟩ : syracuseStep 21438067 = 32157101) B32157101
theorem B4234913 : Blo 1672036 4234913 := bstep (se 2 (by rfl) ⟨1588092, by rfl⟩ : syracuseStep 4234913 = 3176185) B3176185
theorem B9043667 : Blo 1672036 9043667 := bstep (se 1 (by rfl) ⟨6782750, by rfl⟩ : syracuseStep 9043667 = 13565501) B13565501
theorem B3817195 : Blo 1672036 3817195 := bstep (se 1 (by rfl) ⟨2862896, by rfl⟩ : syracuseStep 3817195 = 5725793) B5725793
theorem B5357353 : Blo 1672036 5357353 := bstep (se 2 (by rfl) ⟨2009007, by rfl⟩ : syracuseStep 5357353 = 4018015) B4018015
theorem B5644079 : Blo 1672036 5644079 := bstep (se 1 (by rfl) ⟨4233059, by rfl⟩ : syracuseStep 5644079 = 8466119) B8466119
theorem B3620713 : Blo 1672036 3620713 := bstep (se 2 (by rfl) ⟨1357767, by rfl⟩ : syracuseStep 3620713 = 2715535) B2715535
theorem B5644727 : Blo 1672036 5644727 := bstep (se 1 (by rfl) ⟨4233545, by rfl⟩ : syracuseStep 5644727 = 8467091) B8467091
theorem B4522439 : Blo 1672036 4522439 := bstep (se 1 (by rfl) ⟨3391829, by rfl⟩ : syracuseStep 4522439 = 6783659) B6783659
theorem B4964807 : Blo 1672036 4964807 := bstep (se 1 (by rfl) ⟨3723605, by rfl⟩ : syracuseStep 4964807 = 7447211) B7447211
theorem B4235753 : Blo 1672036 4235753 := bstep (se 2 (by rfl) ⟨1588407, by rfl⟩ : syracuseStep 4235753 = 3176815) B3176815
theorem B14287535 : Blo 1672036 14287535 := bstep (se 1 (by rfl) ⟨10715651, by rfl⟩ : syracuseStep 14287535 = 21431303) B21431303
theorem B2679599 : Blo 1672036 2679599 := bstep (se 1 (by rfl) ⟨2009699, by rfl⟩ : syracuseStep 2679599 = 4019399) B4019399
theorem B42869573 : Blo 1672036 42869573 := bstep (se 4 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 42869573 = 8038045) B8038045
theorem B1672047 : Blo 1672036 1672047 := bstep (se 1 (by rfl) ⟨1254035, by rfl⟩ : syracuseStep 1672047 = 2508071) B2508071
theorem B5645213 : Blo 1672036 5645213 := bstep (se 3 (by rfl) ⟨1058477, by rfl⟩ : syracuseStep 5645213 = 2116955) B2116955
theorem B1672103 : Blo 1672036 1672103 := bstep (se 1 (by rfl) ⟨1254077, by rfl⟩ : syracuseStep 1672103 = 2508155) B2508155
theorem B5645267 : Blo 1672036 5645267 := bstep (se 1 (by rfl) ⟨4233950, by rfl⟩ : syracuseStep 5645267 = 8467901) B8467901
theorem B1672187 : Blo 1672036 1672187 := bstep (se 1 (by rfl) ⟨1254140, by rfl⟩ : syracuseStep 1672187 = 2508281) B2508281
theorem B1672255 : Blo 1672036 1672255 := bstep (se 1 (by rfl) ⟨1254191, by rfl⟩ : syracuseStep 1672255 = 2508383) B2508383
theorem B1672399 : Blo 1672036 1672399 := bstep (se 1 (by rfl) ⟨1254299, by rfl⟩ : syracuseStep 1672399 = 2508599) B2508599
theorem B2680015 : Blo 1672036 2680015 := bstep (se 1 (by rfl) ⟨2010011, by rfl⟩ : syracuseStep 2680015 = 4020023) B4020023
theorem B20358373 : Blo 1672036 20358373 := bstep (se 4 (by rfl) ⟨1908597, by rfl⟩ : syracuseStep 20358373 = 3817195) B3817195
theorem B3056987 : Blo 1672036 3056987 := bstep (se 1 (by rfl) ⟨2292740, by rfl⟩ : syracuseStep 3056987 = 4585481) B4585481
theorem B22898027 : Blo 1672036 22898027 := bstep (se 1 (by rfl) ⟨17173520, by rfl⟩ : syracuseStep 22898027 = 34347041) B34347041
theorem B1672603 : Blo 1672036 1672603 := bstep (se 1 (by rfl) ⟨1254452, by rfl⟩ : syracuseStep 1672603 = 2508905) B2508905
theorem B3098027 : Blo 1672036 3098027 := bstep (se 1 (by rfl) ⟨2323520, by rfl⟩ : syracuseStep 3098027 = 4647041) B4647041
theorem B6030841 : Blo 1672036 6030841 := bstep (se 2 (by rfl) ⟨2261565, by rfl⟩ : syracuseStep 6030841 = 4523131) B4523131
theorem B2508359 : Blo 1672036 2508359 := bstep (se 1 (by rfl) ⟨1881269, by rfl⟩ : syracuseStep 2508359 = 3762539) B3762539
theorem B5088863 : Blo 1672036 5088863 := bstep (se 1 (by rfl) ⟨3816647, by rfl⟩ : syracuseStep 5088863 = 7633295) B7633295
theorem B1672815 : Blo 1672036 1672815 := bstep (se 1 (by rfl) ⟨1254611, by rfl⟩ : syracuseStep 1672815 = 2509223) B2509223
theorem B2508455 : Blo 1672036 2508455 := bstep (se 1 (by rfl) ⟨1881341, by rfl⟩ : syracuseStep 2508455 = 3762683) B3762683
theorem B1672871 : Blo 1672036 1672871 := bstep (se 1 (by rfl) ⟨1254653, by rfl⟩ : syracuseStep 1672871 = 2509307) B2509307
theorem B4237019 : Blo 1672036 4237019 := bstep (se 1 (by rfl) ⟨3177764, by rfl⟩ : syracuseStep 4237019 = 6355529) B6355529
theorem B20350685 : Blo 1672036 20350685 := bstep (se 3 (by rfl) ⟨3815753, by rfl⟩ : syracuseStep 20350685 = 7631507) B7631507
theorem B2508539 : Blo 1672036 2508539 := bstep (se 1 (by rfl) ⟨1881404, by rfl⟩ : syracuseStep 2508539 = 3762809) B3762809
theorem B1672955 : Blo 1672036 1672955 := bstep (se 1 (by rfl) ⟨1254716, by rfl⟩ : syracuseStep 1672955 = 2509433) B2509433
theorem B2508575 : Blo 1672036 2508575 := bstep (se 1 (by rfl) ⟨1881431, by rfl⟩ : syracuseStep 2508575 = 3762863) B3762863
theorem B1672991 : Blo 1672036 1672991 := bstep (se 1 (by rfl) ⟨1254743, by rfl⟩ : syracuseStep 1672991 = 2509487) B2509487
theorem B1673023 : Blo 1672036 1673023 := bstep (se 1 (by rfl) ⟨1254767, by rfl⟩ : syracuseStep 1673023 = 2509535) B2509535
theorem B2508623 : Blo 1672036 2508623 := bstep (se 1 (by rfl) ⟨1881467, by rfl⟩ : syracuseStep 2508623 = 3762935) B3762935
theorem B2508743 : Blo 1672036 2508743 := bstep (se 1 (by rfl) ⟨1881557, by rfl⟩ : syracuseStep 2508743 = 3763115) B3763115
theorem B1673199 : Blo 1672036 1673199 := bstep (se 1 (by rfl) ⟨1254899, by rfl⟩ : syracuseStep 1673199 = 2509799) B2509799
theorem B6350957 : Blo 1672036 6350957 := bstep (se 3 (by rfl) ⟨1190804, by rfl⟩ : syracuseStep 6350957 = 2381609) B2381609
theorem B8038547 : Blo 1672036 8038547 := bstep (se 1 (by rfl) ⟨6028910, by rfl⟩ : syracuseStep 8038547 = 12057821) B12057821
theorem B28584089 : Blo 1672036 28584089 := bstep (se 2 (by rfl) ⟨10719033, by rfl⟩ : syracuseStep 28584089 = 21438067) B21438067
theorem B1673371 : Blo 1672036 1673371 := bstep (se 1 (by rfl) ⟨1255028, by rfl⟩ : syracuseStep 1673371 = 2510057) B2510057
theorem B1673407 : Blo 1672036 1673407 := bstep (se 1 (by rfl) ⟨1255055, by rfl⟩ : syracuseStep 1673407 = 2510111) B2510111
theorem B2509097 : Blo 1672036 2509097 := bstep (se 2 (by rfl) ⟨940911, by rfl⟩ : syracuseStep 2509097 = 1881823) B1881823
theorem B2509103 : Blo 1672036 2509103 := bstep (se 1 (by rfl) ⟨1881827, by rfl⟩ : syracuseStep 2509103 = 3763655) B3763655
theorem B1673519 : Blo 1672036 1673519 := bstep (se 1 (by rfl) ⟨1255139, by rfl⟩ : syracuseStep 1673519 = 2510279) B2510279
theorem B7145819 : Blo 1672036 7145819 := bstep (se 1 (by rfl) ⟨5359364, by rfl⟩ : syracuseStep 7145819 = 10718729) B10718729
theorem B8472923 : Blo 1672036 8472923 := bstep (se 1 (by rfl) ⟨6354692, by rfl⟩ : syracuseStep 8472923 = 12709385) B12709385
theorem B3762593 : Blo 1672036 3762593 := bstep (se 2 (by rfl) ⟨1410972, by rfl⟩ : syracuseStep 3762593 = 2821945) B2821945
theorem B4827617 : Blo 1672036 4827617 := bstep (se 2 (by rfl) ⟨1810356, by rfl⟩ : syracuseStep 4827617 = 3620713) B3620713
theorem B10717703 : Blo 1672036 10717703 := bstep (se 1 (by rfl) ⟨8038277, by rfl⟩ : syracuseStep 10717703 = 16076555) B16076555
theorem B1673755 : Blo 1672036 1673755 := bstep (se 1 (by rfl) ⟨1255316, by rfl⟩ : syracuseStep 1673755 = 2510633) B2510633
theorem B3762719 : Blo 1672036 3762719 := bstep (se 1 (by rfl) ⟨2822039, by rfl⟩ : syracuseStep 3762719 = 5644079) B5644079
theorem B2509343 : Blo 1672036 2509343 := bstep (se 1 (by rfl) ⟨1882007, by rfl⟩ : syracuseStep 2509343 = 3764015) B3764015
theorem B1673759 : Blo 1672036 1673759 := bstep (se 1 (by rfl) ⟨1255319, by rfl⟩ : syracuseStep 1673759 = 2510639) B2510639
theorem B5720647 : Blo 1672036 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B81382097 : Blo 1672036 81382097 := bstep (se 2 (by rfl) ⟨30518286, by rfl⟩ : syracuseStep 81382097 = 61036573) B61036573
theorem B2509727 : Blo 1672036 2509727 := bstep (se 1 (by rfl) ⟨1882295, by rfl⟩ : syracuseStep 2509727 = 3764591) B3764591
theorem B2509775 : Blo 1672036 2509775 := bstep (se 1 (by rfl) ⟨1882331, by rfl⟩ : syracuseStep 2509775 = 3764663) B3764663
theorem B18082835 : Blo 1672036 18082835 := bstep (se 1 (by rfl) ⟨13562126, by rfl⟩ : syracuseStep 18082835 = 27124253) B27124253
theorem B2509865 : Blo 1672036 2509865 := bstep (se 2 (by rfl) ⟨941199, by rfl⟩ : syracuseStep 2509865 = 1882399) B1882399
theorem B2509871 : Blo 1672036 2509871 := bstep (se 1 (by rfl) ⟨1882403, by rfl⟩ : syracuseStep 2509871 = 3764807) B3764807
theorem B2509895 : Blo 1672036 2509895 := bstep (se 1 (by rfl) ⟨1882421, by rfl⟩ : syracuseStep 2509895 = 3764843) B3764843
theorem B5721185 : Blo 1672036 5721185 := bstep (se 2 (by rfl) ⟨2145444, by rfl⟩ : syracuseStep 5721185 = 4290889) B4290889
theorem B5647481 : Blo 1672036 5647481 := bstep (se 2 (by rfl) ⟨2117805, by rfl⟩ : syracuseStep 5647481 = 4235611) B4235611
theorem B10456253 : Blo 1672036 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B2510159 : Blo 1672036 2510159 := bstep (se 1 (by rfl) ⟨1882619, by rfl⟩ : syracuseStep 2510159 = 3765239) B3765239
theorem B19066265 : Blo 1672036 19066265 := bstep (se 2 (by rfl) ⟨7149849, by rfl⟩ : syracuseStep 19066265 = 14299699) B14299699
theorem B2715049 : Blo 1672036 2715049 := bstep (se 2 (by rfl) ⟨1018143, by rfl⟩ : syracuseStep 2715049 = 2036287) B2036287
theorem B2510249 : Blo 1672036 2510249 := bstep (se 2 (by rfl) ⟨941343, by rfl⟩ : syracuseStep 2510249 = 1882687) B1882687
theorem B5647805 : Blo 1672036 5647805 := bstep (se 3 (by rfl) ⟨1058963, by rfl⟩ : syracuseStep 5647805 = 2117927) B2117927
theorem B2510399 : Blo 1672036 2510399 := bstep (se 1 (by rfl) ⟨1882799, by rfl⟩ : syracuseStep 2510399 = 3765599) B3765599
theorem B8474219 : Blo 1672036 8474219 := bstep (se 1 (by rfl) ⟨6355664, by rfl⟩ : syracuseStep 8474219 = 12711329) B12711329
theorem B30510701 : Blo 1672036 30510701 := bstep (se 3 (by rfl) ⟨5720756, by rfl⟩ : syracuseStep 30510701 = 11441513) B11441513
theorem B2510663 : Blo 1672036 2510663 := bstep (se 1 (by rfl) ⟨1882997, by rfl⟩ : syracuseStep 2510663 = 3765995) B3765995
theorem B2543483 : Blo 1672036 2543483 := bstep (se 1 (by rfl) ⟨1907612, by rfl⟩ : syracuseStep 2543483 = 3815225) B3815225
theorem B3764123 : Blo 1672036 3764123 := bstep (se 1 (by rfl) ⟨2823092, by rfl⟩ : syracuseStep 3764123 = 5646185) B5646185
theorem B2510747 : Blo 1672036 2510747 := bstep (se 1 (by rfl) ⟨1883060, by rfl⟩ : syracuseStep 2510747 = 3766121) B3766121
theorem B32157647 : Blo 1672036 32157647 := bstep (se 1 (by rfl) ⟨24118235, by rfl⟩ : syracuseStep 32157647 = 48236471) B48236471
theorem B21426281 : Blo 1672036 21426281 := bstep (se 2 (by rfl) ⟨8034855, by rfl⟩ : syracuseStep 21426281 = 16069711) B16069711
theorem B5648507 : Blo 1672036 5648507 := bstep (se 1 (by rfl) ⟨4236380, by rfl⟩ : syracuseStep 5648507 = 8472761) B8472761
theorem B3764411 : Blo 1672036 3764411 := bstep (se 1 (by rfl) ⟨2823308, by rfl⟩ : syracuseStep 3764411 = 5646617) B5646617
theorem B5648669 : Blo 1672036 5648669 := bstep (se 3 (by rfl) ⟨1059125, by rfl⟩ : syracuseStep 5648669 = 2118251) B2118251
theorem B2822431 : Blo 1672036 2822431 := bstep (se 1 (by rfl) ⟨2116823, by rfl⟩ : syracuseStep 2822431 = 4233647) B4233647
theorem B25760105 : Blo 1672036 25760105 := bstep (se 2 (by rfl) ⟨9660039, by rfl⟩ : syracuseStep 25760105 = 19320079) B19320079
theorem B5648777 : Blo 1672036 5648777 := bstep (se 2 (by rfl) ⟨2118291, by rfl⟩ : syracuseStep 5648777 = 4236583) B4236583
theorem B3764897 : Blo 1672036 3764897 := bstep (se 2 (by rfl) ⟨1411836, by rfl⟩ : syracuseStep 3764897 = 2823673) B2823673
theorem B5362337 : Blo 1672036 5362337 := bstep (se 2 (by rfl) ⟨2010876, by rfl⟩ : syracuseStep 5362337 = 4021753) B4021753
theorem B6779639 : Blo 1672036 6779639 := bstep (se 1 (by rfl) ⟨5084729, by rfl⟩ : syracuseStep 6779639 = 10169459) B10169459
theorem B3175175 : Blo 1672036 3175175 := bstep (se 1 (by rfl) ⟨2381381, by rfl⟩ : syracuseStep 3175175 = 4762763) B4762763
theorem B4018985 : Blo 1672036 4018985 := bstep (se 2 (by rfl) ⟨1507119, by rfl⟩ : syracuseStep 4018985 = 3014239) B3014239
theorem B2823079 : Blo 1672036 2823079 := bstep (se 1 (by rfl) ⟨2117309, by rfl⟩ : syracuseStep 2823079 = 4234619) B4234619
theorem B3765257 : Blo 1672036 3765257 := bstep (se 2 (by rfl) ⟨1411971, by rfl⟩ : syracuseStep 3765257 = 2823943) B2823943
theorem B3765311 : Blo 1672036 3765311 := bstep (se 1 (by rfl) ⟨2823983, by rfl⟩ : syracuseStep 3765311 = 5647967) B5647967
theorem B2823241 : Blo 1672036 2823241 := bstep (se 2 (by rfl) ⟨1058715, by rfl⟩ : syracuseStep 2823241 = 2117431) B2117431
theorem B2823275 : Blo 1672036 2823275 := bstep (se 1 (by rfl) ⟨2117456, by rfl⟩ : syracuseStep 2823275 = 4234913) B4234913
theorem B3175699 : Blo 1672036 3175699 := bstep (se 1 (by rfl) ⟨2381774, by rfl⟩ : syracuseStep 3175699 = 4763549) B4763549
theorem B5649695 : Blo 1672036 5649695 := bstep (se 1 (by rfl) ⟨4237271, by rfl⟩ : syracuseStep 5649695 = 8474543) B8474543
theorem B9524567 : Blo 1672036 9524567 := bstep (se 1 (by rfl) ⟨7143425, by rfl⟩ : syracuseStep 9524567 = 14286851) B14286851
theorem B1881499 : Blo 1672036 1881499 := bstep (se 1 (by rfl) ⟨1411124, by rfl⟩ : syracuseStep 1881499 = 2822249) B2822249
theorem B4584929 : Blo 1672036 4584929 := bstep (se 2 (by rfl) ⟨1719348, by rfl⟩ : syracuseStep 4584929 = 3438697) B3438697
theorem B6027065 : Blo 1672036 6027065 := bstep (se 2 (by rfl) ⟨2260149, by rfl⟩ : syracuseStep 6027065 = 4520299) B4520299
theorem B3176329 : Blo 1672036 3176329 := bstep (se 2 (by rfl) ⟨1191123, by rfl⟩ : syracuseStep 3176329 = 2382247) B2382247
theorem B6354845 : Blo 1672036 6354845 := bstep (se 3 (by rfl) ⟨1191533, by rfl⟩ : syracuseStep 6354845 = 2383067) B2383067
theorem B4765655 : Blo 1672036 4765655 := bstep (se 1 (by rfl) ⟨3574241, by rfl⟩ : syracuseStep 4765655 = 7148483) B7148483
theorem B3766247 : Blo 1672036 3766247 := bstep (se 1 (by rfl) ⟨2824685, by rfl⟩ : syracuseStep 3766247 = 5649371) B5649371
theorem B4765679 : Blo 1672036 4765679 := bstep (se 1 (by rfl) ⟨3574259, by rfl⟩ : syracuseStep 4765679 = 7148519) B7148519
theorem B7247855 : Blo 1672036 7247855 := bstep (se 1 (by rfl) ⟨5435891, by rfl⟩ : syracuseStep 7247855 = 10871783) B10871783
theorem B8042489 : Blo 1672036 8042489 := bstep (se 2 (by rfl) ⟨3015933, by rfl⟩ : syracuseStep 8042489 = 6031867) B6031867
theorem B3766265 : Blo 1672036 3766265 := bstep (se 2 (by rfl) ⟨1412349, by rfl⟩ : syracuseStep 3766265 = 2824699) B2824699
theorem B3766355 : Blo 1672036 3766355 := bstep (se 1 (by rfl) ⟨2824766, by rfl⟩ : syracuseStep 3766355 = 5649533) B5649533
theorem B3766427 : Blo 1672036 3766427 := bstep (se 1 (by rfl) ⟨2824820, by rfl⟩ : syracuseStep 3766427 = 5649641) B5649641
theorem B6027527 : Blo 1672036 6027527 := bstep (se 1 (by rfl) ⟨4520645, by rfl⟩ : syracuseStep 6027527 = 9041291) B9041291
theorem B3766535 : Blo 1672036 3766535 := bstep (se 1 (by rfl) ⟨2824901, by rfl⟩ : syracuseStep 3766535 = 5649803) B5649803
theorem B2824571 : Blo 1672036 2824571 := bstep (se 1 (by rfl) ⟨2118428, by rfl⟩ : syracuseStep 2824571 = 4236857) B4236857
theorem B1882651 : Blo 1672036 1882651 := bstep (se 1 (by rfl) ⟨1411988, by rfl⟩ : syracuseStep 1882651 = 2823977) B2823977
theorem B2382367 : Blo 1672036 2382367 := bstep (se 1 (by rfl) ⟨1786775, by rfl⟩ : syracuseStep 2382367 = 3573551) B3573551
theorem B2824841 : Blo 1672036 2824841 := bstep (se 2 (by rfl) ⟨1059315, by rfl⟩ : syracuseStep 2824841 = 2118631) B2118631
theorem B48257795 : Blo 1672036 48257795 := bstep (se 1 (by rfl) ⟨36193346, by rfl⟩ : syracuseStep 48257795 = 72386693) B72386693
theorem B5643215 : Blo 1672036 5643215 := bstep (se 1 (by rfl) ⟨4232411, by rfl⟩ : syracuseStep 5643215 = 8464823) B8464823
theorem B4291553 : Blo 1672036 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B20339693 : Blo 1672036 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B17161283 : Blo 1672036 17161283 := bstep (se 1 (by rfl) ⟨12870962, by rfl⟩ : syracuseStep 17161283 = 25741925) B25741925
theorem B10714295 : Blo 1672036 10714295 := bstep (se 1 (by rfl) ⟨8035721, by rfl⟩ : syracuseStep 10714295 = 16071443) B16071443
theorem B22887845 : Blo 1672036 22887845 := bstep (se 4 (by rfl) ⟨2145735, by rfl⟩ : syracuseStep 22887845 = 4291471) B4291471
theorem B7143137 : Blo 1672036 7143137 := bstep (se 2 (by rfl) ⟨2678676, by rfl⟩ : syracuseStep 7143137 = 5357353) B5357353
theorem B6029111 : Blo 1672036 6029111 := bstep (se 1 (by rfl) ⟨4521833, by rfl⟩ : syracuseStep 6029111 = 9043667) B9043667
theorem B3309871 : Blo 1672036 3309871 := bstep (se 1 (by rfl) ⟨2482403, by rfl⟩ : syracuseStep 3309871 = 4964807) B4964807
theorem B2679323 : Blo 1672036 2679323 := bstep (se 1 (by rfl) ⟨2009492, by rfl⟩ : syracuseStep 2679323 = 4018985) B4018985
theorem B7627529 : Blo 1672036 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B6349711 : Blo 1672036 6349711 := bstep (se 1 (by rfl) ⟨4762283, by rfl⟩ : syracuseStep 6349711 = 9524567) B9524567
theorem B1672239 : Blo 1672036 1672239 := bstep (se 1 (by rfl) ⟨1254179, by rfl⟩ : syracuseStep 1672239 = 2508359) B2508359
theorem B1672303 : Blo 1672036 1672303 := bstep (se 1 (by rfl) ⟨1254227, by rfl⟩ : syracuseStep 1672303 = 2508455) B2508455
theorem B13567123 : Blo 1672036 13567123 := bstep (se 1 (by rfl) ⟨10175342, by rfl⟩ : syracuseStep 13567123 = 20350685) B20350685
theorem B1672359 : Blo 1672036 1672359 := bstep (se 1 (by rfl) ⟨1254269, by rfl⟩ : syracuseStep 1672359 = 2508539) B2508539
theorem B12059837 : Blo 1672036 12059837 := bstep (se 3 (by rfl) ⟨2261219, by rfl⟩ : syracuseStep 12059837 = 4522439) B4522439
theorem B1672383 : Blo 1672036 1672383 := bstep (se 1 (by rfl) ⟨1254287, by rfl⟩ : syracuseStep 1672383 = 2508575) B2508575
theorem B1672415 : Blo 1672036 1672415 := bstep (se 1 (by rfl) ⟨1254311, by rfl⟩ : syracuseStep 1672415 = 2508623) B2508623
theorem B4236563 : Blo 1672036 4236563 := bstep (se 1 (by rfl) ⟨3177422, by rfl⟩ : syracuseStep 4236563 = 6354845) B6354845
theorem B1672495 : Blo 1672036 1672495 := bstep (se 1 (by rfl) ⟨1254371, by rfl⟩ : syracuseStep 1672495 = 2508743) B2508743
theorem B5359031 : Blo 1672036 5359031 := bstep (se 1 (by rfl) ⟨4019273, by rfl⟩ : syracuseStep 5359031 = 8038547) B8038547
theorem B19056059 : Blo 1672036 19056059 := bstep (se 1 (by rfl) ⟨14292044, by rfl⟩ : syracuseStep 19056059 = 28584089) B28584089
theorem B1672731 : Blo 1672036 1672731 := bstep (se 1 (by rfl) ⟨1254548, by rfl⟩ : syracuseStep 1672731 = 2509097) B2509097
theorem B1672735 : Blo 1672036 1672735 := bstep (se 1 (by rfl) ⟨1254551, by rfl⟩ : syracuseStep 1672735 = 2509103) B2509103
theorem B3573353 : Blo 1672036 3573353 := bstep (se 2 (by rfl) ⟨1340007, by rfl⟩ : syracuseStep 3573353 = 2680015) B2680015
theorem B2508395 : Blo 1672036 2508395 := bstep (se 1 (by rfl) ⟨1881296, by rfl⟩ : syracuseStep 2508395 = 3762593) B3762593
theorem B7145135 : Blo 1672036 7145135 := bstep (se 1 (by rfl) ⟨5358851, by rfl⟩ : syracuseStep 7145135 = 10717703) B10717703
theorem B2508479 : Blo 1672036 2508479 := bstep (se 1 (by rfl) ⟨1881359, by rfl⟩ : syracuseStep 2508479 = 3762719) B3762719
theorem B1672895 : Blo 1672036 1672895 := bstep (se 1 (by rfl) ⟨1254671, by rfl⟩ : syracuseStep 1672895 = 2509343) B2509343
theorem B32171863 : Blo 1672036 32171863 := bstep (se 1 (by rfl) ⟨24128897, by rfl⟩ : syracuseStep 32171863 = 48257795) B48257795
theorem B2508665 : Blo 1672036 2508665 := bstep (se 2 (by rfl) ⟨940749, by rfl⟩ : syracuseStep 2508665 = 1881499) B1881499
theorem B1673151 : Blo 1672036 1673151 := bstep (se 1 (by rfl) ⟨1254863, by rfl⟩ : syracuseStep 1673151 = 2509727) B2509727
theorem B3762143 : Blo 1672036 3762143 := bstep (se 1 (by rfl) ⟨2821607, by rfl⟩ : syracuseStep 3762143 = 5643215) B5643215
theorem B1673183 : Blo 1672036 1673183 := bstep (se 1 (by rfl) ⟨1254887, by rfl⟩ : syracuseStep 1673183 = 2509775) B2509775
theorem B13559795 : Blo 1672036 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B1673243 : Blo 1672036 1673243 := bstep (se 1 (by rfl) ⟨1254932, by rfl⟩ : syracuseStep 1673243 = 2509865) B2509865
theorem B1673247 : Blo 1672036 1673247 := bstep (se 1 (by rfl) ⟨1254935, by rfl⟩ : syracuseStep 1673247 = 2509871) B2509871
theorem B1673263 : Blo 1672036 1673263 := bstep (se 1 (by rfl) ⟨1254947, by rfl⟩ : syracuseStep 1673263 = 2509895) B2509895
theorem B7145597 : Blo 1672036 7145597 := bstep (se 3 (by rfl) ⟨1339799, by rfl⟩ : syracuseStep 7145597 = 2679599) B2679599
theorem B1673439 : Blo 1672036 1673439 := bstep (se 1 (by rfl) ⟨1255079, by rfl⟩ : syracuseStep 1673439 = 2510159) B2510159
theorem B1673499 : Blo 1672036 1673499 := bstep (se 1 (by rfl) ⟨1255124, by rfl⟩ : syracuseStep 1673499 = 2510249) B2510249
theorem B1673599 : Blo 1672036 1673599 := bstep (se 1 (by rfl) ⟨1255199, by rfl⟩ : syracuseStep 1673599 = 2510399) B2510399
theorem B4762091 : Blo 1672036 4762091 := bstep (se 1 (by rfl) ⟨3571568, by rfl⟩ : syracuseStep 4762091 = 7143137) B7143137
theorem B1673775 : Blo 1672036 1673775 := bstep (se 1 (by rfl) ⟨1255331, by rfl⟩ : syracuseStep 1673775 = 2510663) B2510663
theorem B12708413 : Blo 1672036 12708413 := bstep (se 3 (by rfl) ⟨2382827, by rfl⟩ : syracuseStep 12708413 = 4765655) B4765655
theorem B2509415 : Blo 1672036 2509415 := bstep (se 1 (by rfl) ⟨1882061, by rfl⟩ : syracuseStep 2509415 = 3764123) B3764123
theorem B1673831 : Blo 1672036 1673831 := bstep (se 1 (by rfl) ⟨1255373, by rfl⟩ : syracuseStep 1673831 = 2510747) B2510747
theorem B2509607 : Blo 1672036 2509607 := bstep (se 1 (by rfl) ⟨1882205, by rfl⟩ : syracuseStep 2509607 = 3764411) B3764411
theorem B17173403 : Blo 1672036 17173403 := bstep (se 1 (by rfl) ⟨12880052, by rfl⟩ : syracuseStep 17173403 = 25760105) B25760105
theorem B3763151 : Blo 1672036 3763151 := bstep (se 1 (by rfl) ⟨2822363, by rfl⟩ : syracuseStep 3763151 = 5644727) B5644727
theorem B3763241 : Blo 1672036 3763241 := bstep (se 2 (by rfl) ⟨1411215, by rfl⟩ : syracuseStep 3763241 = 2822431) B2822431
theorem B2509931 : Blo 1672036 2509931 := bstep (se 1 (by rfl) ⟨1882448, by rfl⟩ : syracuseStep 2509931 = 3764897) B3764897
theorem B3574891 : Blo 1672036 3574891 := bstep (se 1 (by rfl) ⟨2681168, by rfl⟩ : syracuseStep 3574891 = 5362337) B5362337
theorem B2116783 : Blo 1672036 2116783 := bstep (se 1 (by rfl) ⟨1587587, by rfl⟩ : syracuseStep 2116783 = 3175175) B3175175
theorem B3763475 : Blo 1672036 3763475 := bstep (se 1 (by rfl) ⟨2822606, by rfl⟩ : syracuseStep 3763475 = 5645213) B5645213
theorem B3763511 : Blo 1672036 3763511 := bstep (se 1 (by rfl) ⟨2822633, by rfl⟩ : syracuseStep 3763511 = 5645267) B5645267
theorem B2510171 : Blo 1672036 2510171 := bstep (se 1 (by rfl) ⟨1882628, by rfl⟩ : syracuseStep 2510171 = 3765257) B3765257
theorem B2510201 : Blo 1672036 2510201 := bstep (se 2 (by rfl) ⟨941325, by rfl⟩ : syracuseStep 2510201 = 1882651) B1882651
theorem B2510207 : Blo 1672036 2510207 := bstep (se 1 (by rfl) ⟨1882655, by rfl⟩ : syracuseStep 2510207 = 3765311) B3765311
theorem B15265351 : Blo 1672036 15265351 := bstep (se 1 (by rfl) ⟨11449013, by rfl⟩ : syracuseStep 15265351 = 22898027) B22898027
theorem B8261405 : Blo 1672036 8261405 := bstep (se 3 (by rfl) ⟨1549013, by rfl⟩ : syracuseStep 8261405 = 3098027) B3098027
theorem B4018043 : Blo 1672036 4018043 := bstep (se 1 (by rfl) ⟨3013532, by rfl⟩ : syracuseStep 4018043 = 6027065) B6027065
theorem B3764105 : Blo 1672036 3764105 := bstep (se 2 (by rfl) ⟨1411539, by rfl⟩ : syracuseStep 3764105 = 2823079) B2823079
theorem B2510831 : Blo 1672036 2510831 := bstep (se 1 (by rfl) ⟨1883123, by rfl⟩ : syracuseStep 2510831 = 3766247) B3766247
theorem B5361659 : Blo 1672036 5361659 := bstep (se 1 (by rfl) ⟨4021244, by rfl⟩ : syracuseStep 5361659 = 8042489) B8042489
theorem B2510843 : Blo 1672036 2510843 := bstep (se 1 (by rfl) ⟨1883132, by rfl⟩ : syracuseStep 2510843 = 3766265) B3766265
theorem B2510903 : Blo 1672036 2510903 := bstep (se 1 (by rfl) ⟨1883177, by rfl⟩ : syracuseStep 2510903 = 3766355) B3766355
theorem B3764321 : Blo 1672036 3764321 := bstep (se 2 (by rfl) ⟨1411620, by rfl⟩ : syracuseStep 3764321 = 2823241) B2823241
theorem B2510951 : Blo 1672036 2510951 := bstep (se 1 (by rfl) ⟨1883213, by rfl⟩ : syracuseStep 2510951 = 3766427) B3766427
theorem B4018351 : Blo 1672036 4018351 := bstep (se 1 (by rfl) ⟨3013763, by rfl⟩ : syracuseStep 4018351 = 6027527) B6027527
theorem B2511023 : Blo 1672036 2511023 := bstep (se 1 (by rfl) ⟨1883267, by rfl⟩ : syracuseStep 2511023 = 3766535) B3766535
theorem B4763879 : Blo 1672036 4763879 := bstep (se 1 (by rfl) ⟨3572909, by rfl⟩ : syracuseStep 4763879 = 7145819) B7145819
theorem B5648615 : Blo 1672036 5648615 := bstep (se 1 (by rfl) ⟨4236461, by rfl⟩ : syracuseStep 5648615 = 8472923) B8472923
theorem B13570301 : Blo 1672036 13570301 := bstep (se 3 (by rfl) ⟨2544431, by rfl⟩ : syracuseStep 13570301 = 5088863) B5088863
theorem B27144497 : Blo 1672036 27144497 := bstep (se 2 (by rfl) ⟨10179186, by rfl⟩ : syracuseStep 27144497 = 20358373) B20358373
theorem B8041121 : Blo 1672036 8041121 := bstep (se 2 (by rfl) ⟨3015420, by rfl⟩ : syracuseStep 8041121 = 6030841) B6030841
theorem B12055223 : Blo 1672036 12055223 := bstep (se 1 (by rfl) ⟨9041417, by rfl⟩ : syracuseStep 12055223 = 18082835) B18082835
theorem B11440855 : Blo 1672036 11440855 := bstep (se 1 (by rfl) ⟨8580641, by rfl⟩ : syracuseStep 11440855 = 17161283) B17161283
theorem B3814123 : Blo 1672036 3814123 := bstep (se 1 (by rfl) ⟨2860592, by rfl⟩ : syracuseStep 3814123 = 5721185) B5721185
theorem B3764987 : Blo 1672036 3764987 := bstep (se 1 (by rfl) ⟨2823740, by rfl⟩ : syracuseStep 3764987 = 5647481) B5647481
theorem B16077629 : Blo 1672036 16077629 := bstep (se 3 (by rfl) ⟨3014555, by rfl⟩ : syracuseStep 16077629 = 6029111) B6029111
theorem B12710843 : Blo 1672036 12710843 := bstep (se 1 (by rfl) ⟨9533132, by rfl⟩ : syracuseStep 12710843 = 19066265) B19066265
theorem B15258563 : Blo 1672036 15258563 := bstep (se 1 (by rfl) ⟨11443922, by rfl⟩ : syracuseStep 15258563 = 22887845) B22887845
theorem B3765203 : Blo 1672036 3765203 := bstep (se 1 (by rfl) ⟨2823902, by rfl⟩ : syracuseStep 3765203 = 5647805) B5647805
theorem B5649479 : Blo 1672036 5649479 := bstep (se 1 (by rfl) ⟨4237109, by rfl⟩ : syracuseStep 5649479 = 8474219) B8474219
theorem B14284187 : Blo 1672036 14284187 := bstep (se 1 (by rfl) ⟨10713140, by rfl⟩ : syracuseStep 14284187 = 21426281) B21426281
theorem B3765671 : Blo 1672036 3765671 := bstep (se 1 (by rfl) ⟨2824253, by rfl⟩ : syracuseStep 3765671 = 5648507) B5648507
theorem B3765779 : Blo 1672036 3765779 := bstep (se 1 (by rfl) ⟨2824334, by rfl⟩ : syracuseStep 3765779 = 5648669) B5648669
theorem B3765851 : Blo 1672036 3765851 := bstep (se 1 (by rfl) ⟨2824388, by rfl⟩ : syracuseStep 3765851 = 5648777) B5648777
theorem B2823835 : Blo 1672036 2823835 := bstep (se 1 (by rfl) ⟨2117876, by rfl⟩ : syracuseStep 2823835 = 4235753) B4235753
theorem B9525023 : Blo 1672036 9525023 := bstep (se 1 (by rfl) ⟨7143767, by rfl⟩ : syracuseStep 9525023 = 14287535) B14287535
theorem B4519759 : Blo 1672036 4519759 := bstep (se 1 (by rfl) ⟨3389819, by rfl⟩ : syracuseStep 4519759 = 6779639) B6779639
theorem B28579715 : Blo 1672036 28579715 := bstep (se 1 (by rfl) ⟨21434786, by rfl⟩ : syracuseStep 28579715 = 42869573) B42869573
theorem B3176489 : Blo 1672036 3176489 := bstep (se 2 (by rfl) ⟨1191183, by rfl⟩ : syracuseStep 3176489 = 2382367) B2382367
theorem B1882183 : Blo 1672036 1882183 := bstep (se 1 (by rfl) ⟨1411637, by rfl⟩ : syracuseStep 1882183 = 2823275) B2823275
theorem B3766463 : Blo 1672036 3766463 := bstep (se 1 (by rfl) ⟨2824847, by rfl⟩ : syracuseStep 3766463 = 5649695) B5649695
theorem B2037991 : Blo 1672036 2037991 := bstep (se 1 (by rfl) ⟨1528493, by rfl⟩ : syracuseStep 2037991 = 3056987) B3056987
theorem B2824679 : Blo 1672036 2824679 := bstep (se 1 (by rfl) ⟨2118509, by rfl⟩ : syracuseStep 2824679 = 4237019) B4237019
theorem B3177119 : Blo 1672036 3177119 := bstep (se 1 (by rfl) ⟨2382839, by rfl⟩ : syracuseStep 3177119 = 4765679) B4765679
theorem B4831903 : Blo 1672036 4831903 := bstep (se 1 (by rfl) ⟨3623927, by rfl⟩ : syracuseStep 4831903 = 7247855) B7247855
theorem B4233971 : Blo 1672036 4233971 := bstep (se 1 (by rfl) ⟨3175478, by rfl⟩ : syracuseStep 4233971 = 6350957) B6350957
theorem B1883047 : Blo 1672036 1883047 := bstep (se 1 (by rfl) ⟨1412285, by rfl⟩ : syracuseStep 1883047 = 2824571) B2824571
theorem B3218411 : Blo 1672036 3218411 := bstep (se 1 (by rfl) ⟨2413808, by rfl⟩ : syracuseStep 3218411 = 4827617) B4827617
theorem B4234265 : Blo 1672036 4234265 := bstep (se 2 (by rfl) ⟨1587849, by rfl⟩ : syracuseStep 4234265 = 3175699) B3175699
theorem B1883227 : Blo 1672036 1883227 := bstep (se 1 (by rfl) ⟨1412420, by rfl⟩ : syracuseStep 1883227 = 2824841) B2824841
theorem B54254731 : Blo 1672036 54254731 := bstep (se 1 (by rfl) ⟨40691048, by rfl⟩ : syracuseStep 54254731 = 81382097) B81382097
theorem B3620065 : Blo 1672036 3620065 := bstep (se 2 (by rfl) ⟨1357524, by rfl⟩ : syracuseStep 3620065 = 2715049) B2715049
theorem B7142863 : Blo 1672036 7142863 := bstep (se 1 (by rfl) ⟨5357147, by rfl⟩ : syracuseStep 7142863 = 10714295) B10714295
theorem B6970835 : Blo 1672036 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B48905909 : Blo 1672036 48905909 := bstep (se 5 (by rfl) ⟨2292464, by rfl⟩ : syracuseStep 48905909 = 4584929) B4584929
theorem B20340467 : Blo 1672036 20340467 := bstep (se 1 (by rfl) ⟨15255350, by rfl⟩ : syracuseStep 20340467 = 30510701) B30510701
theorem B4235105 : Blo 1672036 4235105 := bstep (se 2 (by rfl) ⟨1588164, by rfl⟩ : syracuseStep 4235105 = 3176329) B3176329
theorem B1695655 : Blo 1672036 1695655 := bstep (se 1 (by rfl) ⟨1271741, by rfl⟩ : syracuseStep 1695655 = 2543483) B2543483
theorem B11444141 : Blo 1672036 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B21438431 : Blo 1672036 21438431 := bstep (se 1 (by rfl) ⟨16078823, by rfl⟩ : syracuseStep 21438431 = 32157647) B32157647
theorem B18096331 : Blo 1672036 18096331 := bstep (se 1 (by rfl) ⟨13572248, by rfl⟩ : syracuseStep 18096331 = 27144497) B27144497
theorem B5357801 : Blo 1672036 5357801 := bstep (se 2 (by rfl) ⟨2009175, by rfl⟩ : syracuseStep 5357801 = 4018351) B4018351
theorem B8036815 : Blo 1672036 8036815 := bstep (se 1 (by rfl) ⟨6027611, by rfl⟩ : syracuseStep 8036815 = 12055223) B12055223
theorem B3572687 : Blo 1672036 3572687 := bstep (se 1 (by rfl) ⟨2679515, by rfl⟩ : syracuseStep 3572687 = 5359031) B5359031
theorem B1672263 : Blo 1672036 1672263 := bstep (se 1 (by rfl) ⟨1254197, by rfl⟩ : syracuseStep 1672263 = 2508395) B2508395
theorem B1672319 : Blo 1672036 1672319 := bstep (se 1 (by rfl) ⟨1254239, by rfl⟩ : syracuseStep 1672319 = 2508479) B2508479
theorem B6350015 : Blo 1672036 6350015 := bstep (se 1 (by rfl) ⟨4762511, by rfl⟩ : syracuseStep 6350015 = 9525023) B9525023
theorem B1672443 : Blo 1672036 1672443 := bstep (se 1 (by rfl) ⟨1254332, by rfl⟩ : syracuseStep 1672443 = 2508665) B2508665
theorem B2508095 : Blo 1672036 2508095 := bstep (se 1 (by rfl) ⟨1881071, by rfl⟩ : syracuseStep 2508095 = 3762143) B3762143
theorem B7144861 : Blo 1672036 7144861 := bstep (se 3 (by rfl) ⟨1339661, by rfl⟩ : syracuseStep 7144861 = 2679323) B2679323
theorem B18089497 : Blo 1672036 18089497 := bstep (se 2 (by rfl) ⟨6783561, by rfl⟩ : syracuseStep 18089497 = 13567123) B13567123
theorem B9528941 : Blo 1672036 9528941 := bstep (se 3 (by rfl) ⟨1786676, by rfl⟩ : syracuseStep 9528941 = 3573353) B3573353
theorem B4826753 : Blo 1672036 4826753 := bstep (se 2 (by rfl) ⟨1810032, by rfl⟩ : syracuseStep 4826753 = 3620065) B3620065
theorem B8472275 : Blo 1672036 8472275 := bstep (se 1 (by rfl) ⟨6354206, by rfl⟩ : syracuseStep 8472275 = 12708413) B12708413
theorem B1672943 : Blo 1672036 1672943 := bstep (se 1 (by rfl) ⟨1254707, by rfl⟩ : syracuseStep 1672943 = 2509415) B2509415
theorem B1673071 : Blo 1672036 1673071 := bstep (se 1 (by rfl) ⟨1254803, by rfl⟩ : syracuseStep 1673071 = 2509607) B2509607
theorem B2508767 : Blo 1672036 2508767 := bstep (se 1 (by rfl) ⟨1881575, by rfl⟩ : syracuseStep 2508767 = 3763151) B3763151
theorem B2508827 : Blo 1672036 2508827 := bstep (se 1 (by rfl) ⟨1881620, by rfl⟩ : syracuseStep 2508827 = 3763241) B3763241
theorem B1673287 : Blo 1672036 1673287 := bstep (se 1 (by rfl) ⟨1254965, by rfl⟩ : syracuseStep 1673287 = 2509931) B2509931
theorem B2508983 : Blo 1672036 2508983 := bstep (se 1 (by rfl) ⟨1881737, by rfl⟩ : syracuseStep 2508983 = 3763475) B3763475
theorem B2509007 : Blo 1672036 2509007 := bstep (se 1 (by rfl) ⟨1881755, by rfl⟩ : syracuseStep 2509007 = 3763511) B3763511
theorem B1673447 : Blo 1672036 1673447 := bstep (se 1 (by rfl) ⟨1255085, by rfl⟩ : syracuseStep 1673447 = 2510171) B2510171
theorem B1673467 : Blo 1672036 1673467 := bstep (se 1 (by rfl) ⟨1255100, by rfl⟩ : syracuseStep 1673467 = 2510201) B2510201
theorem B1673471 : Blo 1672036 1673471 := bstep (se 1 (by rfl) ⟨1255103, by rfl⟩ : syracuseStep 1673471 = 2510207) B2510207
theorem B4647223 : Blo 1672036 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B42895817 : Blo 1672036 42895817 := bstep (se 2 (by rfl) ⟨16085931, by rfl⟩ : syracuseStep 42895817 = 32171863) B32171863
theorem B13560311 : Blo 1672036 13560311 := bstep (se 1 (by rfl) ⟨10170233, by rfl⟩ : syracuseStep 13560311 = 20340467) B20340467
theorem B5507603 : Blo 1672036 5507603 := bstep (se 1 (by rfl) ⟨4130702, by rfl⟩ : syracuseStep 5507603 = 8261405) B8261405
theorem B2509403 : Blo 1672036 2509403 := bstep (se 1 (by rfl) ⟨1882052, by rfl⟩ : syracuseStep 2509403 = 3764105) B3764105
theorem B7629427 : Blo 1672036 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B1673887 : Blo 1672036 1673887 := bstep (se 1 (by rfl) ⟨1255415, by rfl⟩ : syracuseStep 1673887 = 2510831) B2510831
theorem B3574439 : Blo 1672036 3574439 := bstep (se 1 (by rfl) ⟨2680829, by rfl⟩ : syracuseStep 3574439 = 5361659) B5361659
theorem B1673895 : Blo 1672036 1673895 := bstep (se 1 (by rfl) ⟨1255421, by rfl⟩ : syracuseStep 1673895 = 2510843) B2510843
theorem B1673935 : Blo 1672036 1673935 := bstep (se 1 (by rfl) ⟨1255451, by rfl⟩ : syracuseStep 1673935 = 2510903) B2510903
theorem B2509547 : Blo 1672036 2509547 := bstep (se 1 (by rfl) ⟨1882160, by rfl⟩ : syracuseStep 2509547 = 3764321) B3764321
theorem B1673967 : Blo 1672036 1673967 := bstep (se 1 (by rfl) ⟨1255475, by rfl⟩ : syracuseStep 1673967 = 2510951) B2510951
theorem B2509577 : Blo 1672036 2509577 := bstep (se 2 (by rfl) ⟨941091, by rfl⟩ : syracuseStep 2509577 = 1882183) B1882183
theorem B1674015 : Blo 1672036 1674015 := bstep (se 1 (by rfl) ⟨1255511, by rfl⟩ : syracuseStep 1674015 = 2511023) B2511023
theorem B5360747 : Blo 1672036 5360747 := bstep (se 1 (by rfl) ⟨4020560, by rfl⟩ : syracuseStep 5360747 = 8041121) B8041121
theorem B2509991 : Blo 1672036 2509991 := bstep (se 1 (by rfl) ⟨1882493, by rfl⟩ : syracuseStep 2509991 = 3764987) B3764987
theorem B10718419 : Blo 1672036 10718419 := bstep (se 1 (by rfl) ⟨8038814, by rfl⟩ : syracuseStep 10718419 = 16077629) B16077629
theorem B8473895 : Blo 1672036 8473895 := bstep (se 1 (by rfl) ⟨6355421, by rfl⟩ : syracuseStep 8473895 = 12710843) B12710843
theorem B2510135 : Blo 1672036 2510135 := bstep (se 1 (by rfl) ⟨1882601, by rfl⟩ : syracuseStep 2510135 = 3765203) B3765203
theorem B36187469 : Blo 1672036 36187469 := bstep (se 3 (by rfl) ⟨6785150, by rfl⟩ : syracuseStep 36187469 = 13570301) B13570301
theorem B8039891 : Blo 1672036 8039891 := bstep (se 1 (by rfl) ⟨6029918, by rfl⟩ : syracuseStep 8039891 = 12059837) B12059837
theorem B6442537 : Blo 1672036 6442537 := bstep (se 2 (by rfl) ⟨2415951, by rfl⟩ : syracuseStep 6442537 = 4831903) B4831903
theorem B9522791 : Blo 1672036 9522791 := bstep (se 1 (by rfl) ⟨7142093, by rfl⟩ : syracuseStep 9522791 = 14284187) B14284187
theorem B2510447 : Blo 1672036 2510447 := bstep (se 1 (by rfl) ⟨1882835, by rfl⟩ : syracuseStep 2510447 = 3765671) B3765671
theorem B2510519 : Blo 1672036 2510519 := bstep (se 1 (by rfl) ⟨1882889, by rfl⟩ : syracuseStep 2510519 = 3765779) B3765779
theorem B2510567 : Blo 1672036 2510567 := bstep (se 1 (by rfl) ⟨1882925, by rfl⟩ : syracuseStep 2510567 = 3765851) B3765851
theorem B4763423 : Blo 1672036 4763423 := bstep (se 1 (by rfl) ⟨3572567, by rfl⟩ : syracuseStep 4763423 = 7145135) B7145135
theorem B61017893 : Blo 1672036 61017893 := bstep (se 4 (by rfl) ⟨5720427, by rfl⟩ : syracuseStep 61017893 = 11440855) B11440855
theorem B8466281 : Blo 1672036 8466281 := bstep (se 2 (by rfl) ⟨3174855, by rfl⟩ : syracuseStep 8466281 = 6349711) B6349711
theorem B2510729 : Blo 1672036 2510729 := bstep (se 2 (by rfl) ⟨941523, by rfl⟩ : syracuseStep 2510729 = 1883047) B1883047
theorem B9039863 : Blo 1672036 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B2117659 : Blo 1672036 2117659 := bstep (se 1 (by rfl) ⟨1588244, by rfl⟩ : syracuseStep 2117659 = 3176489) B3176489
theorem B4763731 : Blo 1672036 4763731 := bstep (se 1 (by rfl) ⟨3572798, by rfl⟩ : syracuseStep 4763731 = 7145597) B7145597
theorem B2510969 : Blo 1672036 2510969 := bstep (se 2 (by rfl) ⟨941613, by rfl⟩ : syracuseStep 2510969 = 1883227) B1883227
theorem B2510975 : Blo 1672036 2510975 := bstep (se 1 (by rfl) ⟨1883231, by rfl⟩ : syracuseStep 2510975 = 3766463) B3766463
theorem B72339641 : Blo 1672036 72339641 := bstep (se 2 (by rfl) ⟨27127365, by rfl⟩ : syracuseStep 72339641 = 54254731) B54254731
theorem B2822377 : Blo 1672036 2822377 := bstep (se 2 (by rfl) ⟨1058391, by rfl⟩ : syracuseStep 2822377 = 2116783) B2116783
theorem B3174727 : Blo 1672036 3174727 := bstep (se 1 (by rfl) ⟨2381045, by rfl⟩ : syracuseStep 3174727 = 4762091) B4762091
theorem B2118079 : Blo 1672036 2118079 := bstep (se 1 (by rfl) ⟨1588559, by rfl⟩ : syracuseStep 2118079 = 3177119) B3177119
theorem B2822647 : Blo 1672036 2822647 := bstep (se 1 (by rfl) ⟨2116985, by rfl⟩ : syracuseStep 2822647 = 4233971) B4233971
theorem B11448935 : Blo 1672036 11448935 := bstep (se 1 (by rfl) ⟨8586701, by rfl⟩ : syracuseStep 11448935 = 17173403) B17173403
theorem B9523817 : Blo 1672036 9523817 := bstep (se 2 (by rfl) ⟨3571431, by rfl⟩ : syracuseStep 9523817 = 7142863) B7142863
theorem B2822843 : Blo 1672036 2822843 := bstep (se 1 (by rfl) ⟨2117132, by rfl⟩ : syracuseStep 2822843 = 4234265) B4234265
theorem B20353801 : Blo 1672036 20353801 := bstep (se 2 (by rfl) ⟨7632675, by rfl⟩ : syracuseStep 20353801 = 15265351) B15265351
theorem B3765113 : Blo 1672036 3765113 := bstep (se 2 (by rfl) ⟨1411917, by rfl⟩ : syracuseStep 3765113 = 2823835) B2823835
theorem B6026345 : Blo 1672036 6026345 := bstep (se 2 (by rfl) ⟨2259879, by rfl⟩ : syracuseStep 6026345 = 4519759) B4519759
theorem B2823403 : Blo 1672036 2823403 := bstep (se 1 (by rfl) ⟨2117552, by rfl⟩ : syracuseStep 2823403 = 4235105) B4235105
theorem B8582429 : Blo 1672036 8582429 := bstep (se 3 (by rfl) ⟨1609205, by rfl⟩ : syracuseStep 8582429 = 3218411) B3218411
theorem B14292287 : Blo 1672036 14292287 := bstep (se 1 (by rfl) ⟨10719215, by rfl⟩ : syracuseStep 14292287 = 21438431) B21438431
theorem B3175919 : Blo 1672036 3175919 := bstep (se 1 (by rfl) ⟨2381939, by rfl⟩ : syracuseStep 3175919 = 4763879) B4763879
theorem B3765743 : Blo 1672036 3765743 := bstep (se 1 (by rfl) ⟨2824307, by rfl⟩ : syracuseStep 3765743 = 5648615) B5648615
theorem B2717321 : Blo 1672036 2717321 := bstep (se 2 (by rfl) ⟨1018995, by rfl⟩ : syracuseStep 2717321 = 2037991) B2037991
theorem B4413161 : Blo 1672036 4413161 := bstep (se 2 (by rfl) ⟨1654935, by rfl⟩ : syracuseStep 4413161 = 3309871) B3309871
theorem B5085019 : Blo 1672036 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B10172375 : Blo 1672036 10172375 := bstep (se 1 (by rfl) ⟨7629281, by rfl⟩ : syracuseStep 10172375 = 15258563) B15258563
theorem B3766319 : Blo 1672036 3766319 := bstep (se 1 (by rfl) ⟨2824739, by rfl⟩ : syracuseStep 3766319 = 5649479) B5649479
theorem B2824375 : Blo 1672036 2824375 := bstep (se 1 (by rfl) ⟨2118281, by rfl⟩ : syracuseStep 2824375 = 4236563) B4236563
theorem B12704039 : Blo 1672036 12704039 := bstep (se 1 (by rfl) ⟨9528029, by rfl⟩ : syracuseStep 12704039 = 19056059) B19056059
theorem B5085497 : Blo 1672036 5085497 := bstep (se 2 (by rfl) ⟨1907061, by rfl⟩ : syracuseStep 5085497 = 3814123) B3814123
theorem B19053143 : Blo 1672036 19053143 := bstep (se 1 (by rfl) ⟨14289857, by rfl⟩ : syracuseStep 19053143 = 28579715) B28579715
theorem B4766521 : Blo 1672036 4766521 := bstep (se 2 (by rfl) ⟨1787445, by rfl⟩ : syracuseStep 4766521 = 3574891) B3574891
theorem B1883119 : Blo 1672036 1883119 := bstep (se 1 (by rfl) ⟨1412339, by rfl⟩ : syracuseStep 1883119 = 2824679) B2824679
theorem B9043493 : Blo 1672036 9043493 := bstep (se 4 (by rfl) ⟨847827, by rfl⟩ : syracuseStep 9043493 = 1695655) B1695655
theorem B10714781 : Blo 1672036 10714781 := bstep (se 3 (by rfl) ⟨2009021, by rfl⟩ : syracuseStep 10714781 = 4018043) B4018043
theorem B32603939 : Blo 1672036 32603939 := bstep (se 1 (by rfl) ⟨24452954, by rfl⟩ : syracuseStep 32603939 = 48905909) B48905909
theorem B48226427 : Blo 1672036 48226427 := bstep (se 1 (by rfl) ⟨36169820, by rfl⟩ : syracuseStep 48226427 = 72339641) B72339641
theorem B3571867 : Blo 1672036 3571867 := bstep (se 1 (by rfl) ⟨2678900, by rfl⟩ : syracuseStep 3571867 = 5357801) B5357801
theorem B14295325 : Blo 1672036 14295325 := bstep (se 3 (by rfl) ⟨2680373, by rfl⟩ : syracuseStep 14295325 = 5360747) B5360747
theorem B6349211 : Blo 1672036 6349211 := bstep (se 1 (by rfl) ⟨4761908, by rfl⟩ : syracuseStep 6349211 = 9523817) B9523817
theorem B10715753 : Blo 1672036 10715753 := bstep (se 2 (by rfl) ⟨4018407, by rfl⟩ : syracuseStep 10715753 = 8036815) B8036815
theorem B1672063 : Blo 1672036 1672063 := bstep (se 1 (by rfl) ⟨1254047, by rfl⟩ : syracuseStep 1672063 = 2508095) B2508095
theorem B9528191 : Blo 1672036 9528191 := bstep (se 1 (by rfl) ⟨7146143, by rfl⟩ : syracuseStep 9528191 = 14292287) B14292287
theorem B36160829 : Blo 1672036 36160829 := bstep (se 3 (by rfl) ⟨6780155, by rfl⟩ : syracuseStep 36160829 = 13560311) B13560311
theorem B1672511 : Blo 1672036 1672511 := bstep (se 1 (by rfl) ⟨1254383, by rfl⟩ : syracuseStep 1672511 = 2508767) B2508767
theorem B1672551 : Blo 1672036 1672551 := bstep (se 1 (by rfl) ⟨1254413, by rfl⟩ : syracuseStep 1672551 = 2508827) B2508827
theorem B1672655 : Blo 1672036 1672655 := bstep (se 1 (by rfl) ⟨1254491, by rfl⟩ : syracuseStep 1672655 = 2508983) B2508983
theorem B1672671 : Blo 1672036 1672671 := bstep (se 1 (by rfl) ⟨1254503, by rfl⟩ : syracuseStep 1672671 = 2509007) B2509007
theorem B3671735 : Blo 1672036 3671735 := bstep (se 1 (by rfl) ⟨2753801, by rfl⟩ : syracuseStep 3671735 = 5507603) B5507603
theorem B1672935 : Blo 1672036 1672935 := bstep (se 1 (by rfl) ⟨1254701, by rfl⟩ : syracuseStep 1672935 = 2509403) B2509403
theorem B1673031 : Blo 1672036 1673031 := bstep (se 1 (by rfl) ⟨1254773, by rfl⟩ : syracuseStep 1673031 = 2509547) B2509547
theorem B1673051 : Blo 1672036 1673051 := bstep (se 1 (by rfl) ⟨1254788, by rfl⟩ : syracuseStep 1673051 = 2509577) B2509577
theorem B24119329 : Blo 1672036 24119329 := bstep (se 2 (by rfl) ⟨9044748, by rfl⟩ : syracuseStep 24119329 = 18089497) B18089497
theorem B1673327 : Blo 1672036 1673327 := bstep (se 1 (by rfl) ⟨1254995, by rfl⟩ : syracuseStep 1673327 = 2509991) B2509991
theorem B1673423 : Blo 1672036 1673423 := bstep (se 1 (by rfl) ⟨1255067, by rfl⟩ : syracuseStep 1673423 = 2510135) B2510135
theorem B5359927 : Blo 1672036 5359927 := bstep (se 1 (by rfl) ⟨4019945, by rfl⟩ : syracuseStep 5359927 = 8039891) B8039891
theorem B1673631 : Blo 1672036 1673631 := bstep (se 1 (by rfl) ⟨1255223, by rfl⟩ : syracuseStep 1673631 = 2510447) B2510447
theorem B1673679 : Blo 1672036 1673679 := bstep (se 1 (by rfl) ⟨1255259, by rfl⟩ : syracuseStep 1673679 = 2510519) B2510519
theorem B1673711 : Blo 1672036 1673711 := bstep (se 1 (by rfl) ⟨1255283, by rfl⟩ : syracuseStep 1673711 = 2510567) B2510567
theorem B21735959 : Blo 1672036 21735959 := bstep (se 1 (by rfl) ⟨16301969, by rfl⟩ : syracuseStep 21735959 = 32603939) B32603939
theorem B1673819 : Blo 1672036 1673819 := bstep (se 1 (by rfl) ⟨1255364, by rfl⟩ : syracuseStep 1673819 = 2510729) B2510729
theorem B1673979 : Blo 1672036 1673979 := bstep (se 1 (by rfl) ⟨1255484, by rfl⟩ : syracuseStep 1673979 = 2510969) B2510969
theorem B1673983 : Blo 1672036 1673983 := bstep (se 1 (by rfl) ⟨1255487, by rfl⟩ : syracuseStep 1673983 = 2510975) B2510975
theorem B6351641 : Blo 1672036 6351641 := bstep (se 2 (by rfl) ⟨2381865, by rfl⟩ : syracuseStep 6351641 = 4763731) B4763731
theorem B24128441 : Blo 1672036 24128441 := bstep (se 2 (by rfl) ⟨9048165, by rfl⟩ : syracuseStep 24128441 = 18096331) B18096331
theorem B3763169 : Blo 1672036 3763169 := bstep (se 2 (by rfl) ⟨1411188, by rfl⟩ : syracuseStep 3763169 = 2822377) B2822377
theorem B2510075 : Blo 1672036 2510075 := bstep (se 1 (by rfl) ⟨1882556, by rfl⟩ : syracuseStep 2510075 = 3765113) B3765113
theorem B3763529 : Blo 1672036 3763529 := bstep (se 2 (by rfl) ⟨1411323, by rfl⟩ : syracuseStep 3763529 = 2822647) B2822647
theorem B4017563 : Blo 1672036 4017563 := bstep (se 1 (by rfl) ⟨3013172, by rfl⟩ : syracuseStep 4017563 = 6026345) B6026345
theorem B2117279 : Blo 1672036 2117279 := bstep (se 1 (by rfl) ⟨1587959, by rfl⟩ : syracuseStep 2117279 = 3175919) B3175919
theorem B2510495 : Blo 1672036 2510495 := bstep (se 1 (by rfl) ⟨1882871, by rfl⟩ : syracuseStep 2510495 = 3765743) B3765743
theorem B6352627 : Blo 1672036 6352627 := bstep (se 1 (by rfl) ⟨4764470, by rfl⟩ : syracuseStep 6352627 = 9528941) B9528941
theorem B5648183 : Blo 1672036 5648183 := bstep (se 1 (by rfl) ⟨4236137, by rfl⟩ : syracuseStep 5648183 = 8472275) B8472275
theorem B2510825 : Blo 1672036 2510825 := bstep (se 2 (by rfl) ⟨941559, by rfl⟩ : syracuseStep 2510825 = 1883119) B1883119
theorem B2510879 : Blo 1672036 2510879 := bstep (se 1 (by rfl) ⟨1883159, by rfl⟩ : syracuseStep 2510879 = 3766319) B3766319
theorem B14291225 : Blo 1672036 14291225 := bstep (se 2 (by rfl) ⟨5359209, by rfl⟩ : syracuseStep 14291225 = 10718419) B10718419
theorem B24785189 : Blo 1672036 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B3764537 : Blo 1672036 3764537 := bstep (se 2 (by rfl) ⟨1411701, by rfl⟩ : syracuseStep 3764537 = 2823403) B2823403
theorem B7246189 : Blo 1672036 7246189 := bstep (se 3 (by rfl) ⟨1358660, by rfl⟩ : syracuseStep 7246189 = 2717321) B2717321
theorem B12702095 : Blo 1672036 12702095 := bstep (se 1 (by rfl) ⟨9526571, by rfl⟩ : syracuseStep 12702095 = 19053143) B19053143
theorem B11768429 : Blo 1672036 11768429 := bstep (se 3 (by rfl) ⟨2206580, by rfl⟩ : syracuseStep 11768429 = 4413161) B4413161
theorem B8590049 : Blo 1672036 8590049 := bstep (se 2 (by rfl) ⟨3221268, by rfl⟩ : syracuseStep 8590049 = 6442537) B6442537
theorem B5649263 : Blo 1672036 5649263 := bstep (se 1 (by rfl) ⟨4236947, by rfl⟩ : syracuseStep 5649263 = 8473895) B8473895
theorem B6780025 : Blo 1672036 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B3175615 : Blo 1672036 3175615 := bstep (se 1 (by rfl) ⟨2381711, by rfl⟩ : syracuseStep 3175615 = 4763423) B4763423
theorem B40678595 : Blo 1672036 40678595 := bstep (se 1 (by rfl) ⟨30508946, by rfl⟩ : syracuseStep 40678595 = 61017893) B61017893
theorem B6026575 : Blo 1672036 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B2823545 : Blo 1672036 2823545 := bstep (se 2 (by rfl) ⟨1058829, by rfl⟩ : syracuseStep 2823545 = 2117659) B2117659
theorem B3765833 : Blo 1672036 3765833 := bstep (se 2 (by rfl) ⟨1412187, by rfl⟩ : syracuseStep 3765833 = 2824375) B2824375
theorem B7632623 : Blo 1672036 7632623 := bstep (se 1 (by rfl) ⟨5724467, by rfl⟩ : syracuseStep 7632623 = 11448935) B11448935
theorem B4232969 : Blo 1672036 4232969 := bstep (se 2 (by rfl) ⟨1587363, by rfl⟩ : syracuseStep 4232969 = 3174727) B3174727
theorem B1881895 : Blo 1672036 1881895 := bstep (se 1 (by rfl) ⟨1411421, by rfl⟩ : syracuseStep 1881895 = 2822843) B2822843
theorem B2824105 : Blo 1672036 2824105 := bstep (se 2 (by rfl) ⟨1059039, by rfl⟩ : syracuseStep 2824105 = 2118079) B2118079
theorem B22886477 : Blo 1672036 22886477 := bstep (se 3 (by rfl) ⟨4291214, by rfl⟩ : syracuseStep 22886477 = 8582429) B8582429
theorem B4233343 : Blo 1672036 4233343 := bstep (se 1 (by rfl) ⟨3175007, by rfl⟩ : syracuseStep 4233343 = 6350015) B6350015
theorem B10172569 : Blo 1672036 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B27138401 : Blo 1672036 27138401 := bstep (se 2 (by rfl) ⟨10176900, by rfl⟩ : syracuseStep 27138401 = 20353801) B20353801
theorem B6355361 : Blo 1672036 6355361 := bstep (se 2 (by rfl) ⟨2383260, by rfl⟩ : syracuseStep 6355361 = 4766521) B4766521
theorem B3217835 : Blo 1672036 3217835 := bstep (se 1 (by rfl) ⟨2413376, by rfl⟩ : syracuseStep 3217835 = 4826753) B4826753
theorem B6781583 : Blo 1672036 6781583 := bstep (se 1 (by rfl) ⟨5086187, by rfl⟩ : syracuseStep 6781583 = 10172375) B10172375
theorem B24115981 : Blo 1672036 24115981 := bstep (se 3 (by rfl) ⟨4521746, by rfl⟩ : syracuseStep 24115981 = 9043493) B9043493
theorem B8469359 : Blo 1672036 8469359 := bstep (se 1 (by rfl) ⟨6352019, by rfl⟩ : syracuseStep 8469359 = 12704039) B12704039
theorem B3390331 : Blo 1672036 3390331 := bstep (se 1 (by rfl) ⟨2542748, by rfl⟩ : syracuseStep 3390331 = 5085497) B5085497
theorem B28597211 : Blo 1672036 28597211 := bstep (se 1 (by rfl) ⟨21447908, by rfl⟩ : syracuseStep 28597211 = 42895817) B42895817
theorem B2382959 : Blo 1672036 2382959 := bstep (se 1 (by rfl) ⟨1787219, by rfl⟩ : syracuseStep 2382959 = 3574439) B3574439
theorem B9526481 : Blo 1672036 9526481 := bstep (se 2 (by rfl) ⟨3572430, by rfl⟩ : syracuseStep 9526481 = 7144861) B7144861
theorem B24124979 : Blo 1672036 24124979 := bstep (se 1 (by rfl) ⟨18093734, by rfl⟩ : syracuseStep 24124979 = 36187469) B36187469
theorem B6348527 : Blo 1672036 6348527 := bstep (se 1 (by rfl) ⟨4761395, by rfl⟩ : syracuseStep 6348527 = 9522791) B9522791
theorem B7143187 : Blo 1672036 7143187 := bstep (se 1 (by rfl) ⟨5357390, by rfl⟩ : syracuseStep 7143187 = 10714781) B10714781
theorem B9527165 : Blo 1672036 9527165 := bstep (se 3 (by rfl) ⟨1786343, by rfl⟩ : syracuseStep 9527165 = 3572687) B3572687
theorem B5644187 : Blo 1672036 5644187 := bstep (se 1 (by rfl) ⟨4233140, by rfl⟩ : syracuseStep 5644187 = 8466281) B8466281
theorem B5644457 : Blo 1672036 5644457 := bstep (se 2 (by rfl) ⟨2116671, by rfl⟩ : syracuseStep 5644457 = 4233343) B4233343
theorem B9527483 : Blo 1672036 9527483 := bstep (se 1 (by rfl) ⟨7145612, by rfl⟩ : syracuseStep 9527483 = 14291225) B14291225
theorem B16523459 : Blo 1672036 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B5726699 : Blo 1672036 5726699 := bstep (se 1 (by rfl) ⟨4295024, by rfl⟩ : syracuseStep 5726699 = 8590049) B8590049
theorem B32154641 : Blo 1672036 32154641 := bstep (se 2 (by rfl) ⟨12057990, by rfl⟩ : syracuseStep 32154641 = 24115981) B24115981
theorem B5088415 : Blo 1672036 5088415 := bstep (se 1 (by rfl) ⟨3816311, by rfl⟩ : syracuseStep 5088415 = 7632623) B7632623
theorem B28575341 : Blo 1672036 28575341 := bstep (se 3 (by rfl) ⟨5357876, by rfl⟩ : syracuseStep 28575341 = 10715753) B10715753
theorem B4236907 : Blo 1672036 4236907 := bstep (se 1 (by rfl) ⟨3177680, by rfl⟩ : syracuseStep 4236907 = 6355361) B6355361
theorem B5646077 : Blo 1672036 5646077 := bstep (se 3 (by rfl) ⟨1058639, by rfl⟩ : syracuseStep 5646077 = 2117279) B2117279
theorem B9791293 : Blo 1672036 9791293 := bstep (se 3 (by rfl) ⟨1835867, by rfl⟩ : syracuseStep 9791293 = 3671735) B3671735
theorem B5646239 : Blo 1672036 5646239 := bstep (se 1 (by rfl) ⟨4234679, by rfl⟩ : syracuseStep 5646239 = 8469359) B8469359
theorem B19064807 : Blo 1672036 19064807 := bstep (se 1 (by rfl) ⟨14298605, by rfl⟩ : syracuseStep 19064807 = 28597211) B28597211
theorem B2508779 : Blo 1672036 2508779 := bstep (se 1 (by rfl) ⟨1881584, by rfl⟩ : syracuseStep 2508779 = 3763169) B3763169
theorem B6350987 : Blo 1672036 6350987 := bstep (se 1 (by rfl) ⟨4763240, by rfl⟩ : syracuseStep 6350987 = 9526481) B9526481
theorem B1673383 : Blo 1672036 1673383 := bstep (se 1 (by rfl) ⟨1255037, by rfl⟩ : syracuseStep 1673383 = 2510075) B2510075
theorem B2509019 : Blo 1672036 2509019 := bstep (se 1 (by rfl) ⟨1881764, by rfl⟩ : syracuseStep 2509019 = 3763529) B3763529
theorem B16083319 : Blo 1672036 16083319 := bstep (se 1 (by rfl) ⟨12062489, by rfl⟩ : syracuseStep 16083319 = 24124979) B24124979
theorem B2509193 : Blo 1672036 2509193 := bstep (se 2 (by rfl) ⟨940947, by rfl⟩ : syracuseStep 2509193 = 1881895) B1881895
theorem B1673663 : Blo 1672036 1673663 := bstep (se 1 (by rfl) ⟨1255247, by rfl⟩ : syracuseStep 1673663 = 2510495) B2510495
theorem B6351443 : Blo 1672036 6351443 := bstep (se 1 (by rfl) ⟨4763582, by rfl⟩ : syracuseStep 6351443 = 9527165) B9527165
theorem B3762791 : Blo 1672036 3762791 := bstep (se 1 (by rfl) ⟨2822093, by rfl⟩ : syracuseStep 3762791 = 5644187) B5644187
theorem B1673883 : Blo 1672036 1673883 := bstep (se 1 (by rfl) ⟨1255412, by rfl⟩ : syracuseStep 1673883 = 2510825) B2510825
theorem B1673919 : Blo 1672036 1673919 := bstep (se 1 (by rfl) ⟨1255439, by rfl⟩ : syracuseStep 1673919 = 2510879) B2510879
theorem B4762489 : Blo 1672036 4762489 := bstep (se 2 (by rfl) ⟨1785933, by rfl⟩ : syracuseStep 4762489 = 3571867) B3571867
theorem B2509691 : Blo 1672036 2509691 := bstep (se 1 (by rfl) ⟨1882268, by rfl⟩ : syracuseStep 2509691 = 3764537) B3764537
theorem B7146569 : Blo 1672036 7146569 := bstep (se 2 (by rfl) ⟨2679963, by rfl⟩ : syracuseStep 7146569 = 5359927) B5359927
theorem B6352127 : Blo 1672036 6352127 := bstep (se 1 (by rfl) ⟨4764095, by rfl⟩ : syracuseStep 6352127 = 9528191) B9528191
theorem B27119063 : Blo 1672036 27119063 := bstep (se 1 (by rfl) ⟨20339297, by rfl⟩ : syracuseStep 27119063 = 40678595) B40678595
theorem B2510555 : Blo 1672036 2510555 := bstep (se 1 (by rfl) ⟨1882916, by rfl⟩ : syracuseStep 2510555 = 3765833) B3765833
theorem B2821979 : Blo 1672036 2821979 := bstep (se 1 (by rfl) ⟨2116484, by rfl⟩ : syracuseStep 2821979 = 4232969) B4232969
theorem B15257651 : Blo 1672036 15257651 := bstep (se 1 (by rfl) ⟨11443238, by rfl⟩ : syracuseStep 15257651 = 22886477) B22886477
theorem B57962557 : Blo 1672036 57962557 := bstep (se 3 (by rfl) ⟨10867979, by rfl⟩ : syracuseStep 57962557 = 21735959) B21735959
theorem B9040033 : Blo 1672036 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B18092267 : Blo 1672036 18092267 := bstep (se 1 (by rfl) ⟨13569200, by rfl⟩ : syracuseStep 18092267 = 27138401) B27138401
theorem B18084221 : Blo 1672036 18084221 := bstep (se 3 (by rfl) ⟨3390791, by rfl⟩ : syracuseStep 18084221 = 6781583) B6781583
theorem B38646341 : Blo 1672036 38646341 := bstep (se 4 (by rfl) ⟨3623094, by rfl⟩ : syracuseStep 38646341 = 7246189) B7246189
theorem B16085627 : Blo 1672036 16085627 := bstep (se 1 (by rfl) ⟨12064220, by rfl⟩ : syracuseStep 16085627 = 24128441) B24128441
theorem B9524249 : Blo 1672036 9524249 := bstep (se 2 (by rfl) ⟨3571593, by rfl⟩ : syracuseStep 9524249 = 7143187) B7143187
theorem B4232351 : Blo 1672036 4232351 := bstep (se 1 (by rfl) ⟨3174263, by rfl⟩ : syracuseStep 4232351 = 6348527) B6348527
theorem B3765455 : Blo 1672036 3765455 := bstep (se 1 (by rfl) ⟨2824091, by rfl⟩ : syracuseStep 3765455 = 5648183) B5648183
theorem B3765473 : Blo 1672036 3765473 := bstep (se 2 (by rfl) ⟨1412052, by rfl⟩ : syracuseStep 3765473 = 2824105) B2824105
theorem B32159105 : Blo 1672036 32159105 := bstep (se 2 (by rfl) ⟨12059664, by rfl⟩ : syracuseStep 32159105 = 24119329) B24119329
theorem B32150951 : Blo 1672036 32150951 := bstep (se 1 (by rfl) ⟨24113213, by rfl⟩ : syracuseStep 32150951 = 48226427) B48226427
theorem B13563425 : Blo 1672036 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B8468063 : Blo 1672036 8468063 := bstep (se 1 (by rfl) ⟨6351047, by rfl⟩ : syracuseStep 8468063 = 12702095) B12702095
theorem B4232807 : Blo 1672036 4232807 := bstep (se 1 (by rfl) ⟨3174605, by rfl⟩ : syracuseStep 4232807 = 6349211) B6349211
theorem B6354557 : Blo 1672036 6354557 := bstep (se 3 (by rfl) ⟨1191479, by rfl⟩ : syracuseStep 6354557 = 2382959) B2382959
theorem B19060433 : Blo 1672036 19060433 := bstep (se 2 (by rfl) ⟨7147662, by rfl⟩ : syracuseStep 19060433 = 14295325) B14295325
theorem B7845619 : Blo 1672036 7845619 := bstep (se 1 (by rfl) ⟨5884214, by rfl⟩ : syracuseStep 7845619 = 11768429) B11768429
theorem B3766175 : Blo 1672036 3766175 := bstep (se 1 (by rfl) ⟨2824631, by rfl⟩ : syracuseStep 3766175 = 5649263) B5649263
theorem B24107219 : Blo 1672036 24107219 := bstep (se 1 (by rfl) ⟨18080414, by rfl⟩ : syracuseStep 24107219 = 36160829) B36160829
theorem B1882363 : Blo 1672036 1882363 := bstep (se 1 (by rfl) ⟨1411772, by rfl⟩ : syracuseStep 1882363 = 2823545) B2823545
theorem B4520441 : Blo 1672036 4520441 := bstep (se 2 (by rfl) ⟨1695165, by rfl⟩ : syracuseStep 4520441 = 3390331) B3390331
theorem B4234153 : Blo 1672036 4234153 := bstep (se 2 (by rfl) ⟨1587807, by rfl⟩ : syracuseStep 4234153 = 3175615) B3175615
theorem B2145223 : Blo 1672036 2145223 := bstep (se 1 (by rfl) ⟨1608917, by rfl⟩ : syracuseStep 2145223 = 3217835) B3217835
theorem B8035433 : Blo 1672036 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B4234427 : Blo 1672036 4234427 := bstep (se 1 (by rfl) ⟨3175820, by rfl⟩ : syracuseStep 4234427 = 6351641) B6351641
theorem B2678375 : Blo 1672036 2678375 := bstep (se 1 (by rfl) ⟨2008781, by rfl⟩ : syracuseStep 2678375 = 4017563) B4017563
theorem B8470169 : Blo 1672036 8470169 := bstep (se 2 (by rfl) ⟨3176313, by rfl⟩ : syracuseStep 8470169 = 6352627) B6352627
theorem B77283409 : Blo 1672036 77283409 := bstep (se 2 (by rfl) ⟨28981278, by rfl⟩ : syracuseStep 77283409 = 57962557) B57962557
theorem B3817799 : Blo 1672036 3817799 := bstep (se 1 (by rfl) ⟨2863349, by rfl⟩ : syracuseStep 3817799 = 5726699) B5726699
theorem B25764227 : Blo 1672036 25764227 := bstep (se 1 (by rfl) ⟨19323170, by rfl⟩ : syracuseStep 25764227 = 38646341) B38646341
theorem B10723751 : Blo 1672036 10723751 := bstep (se 1 (by rfl) ⟨8042813, by rfl⟩ : syracuseStep 10723751 = 16085627) B16085627
theorem B6349499 : Blo 1672036 6349499 := bstep (se 1 (by rfl) ⟨4762124, by rfl⟩ : syracuseStep 6349499 = 9524249) B9524249
theorem B21439403 : Blo 1672036 21439403 := bstep (se 1 (by rfl) ⟨16079552, by rfl⟩ : syracuseStep 21439403 = 32159105) B32159105
theorem B5645375 : Blo 1672036 5645375 := bstep (se 1 (by rfl) ⟨4234031, by rfl⟩ : syracuseStep 5645375 = 8468063) B8468063
theorem B4236371 : Blo 1672036 4236371 := bstep (se 1 (by rfl) ⟨3177278, by rfl⟩ : syracuseStep 4236371 = 6354557) B6354557
theorem B12706955 : Blo 1672036 12706955 := bstep (se 1 (by rfl) ⟨9530216, by rfl⟩ : syracuseStep 12706955 = 19060433) B19060433
theorem B6349985 : Blo 1672036 6349985 := bstep (se 2 (by rfl) ⟨2381244, by rfl⟩ : syracuseStep 6349985 = 4762489) B4762489
theorem B5645537 : Blo 1672036 5645537 := bstep (se 2 (by rfl) ⟨2117076, by rfl⟩ : syracuseStep 5645537 = 4234153) B4234153
theorem B1672519 : Blo 1672036 1672519 := bstep (se 1 (by rfl) ⟨1254389, by rfl⟩ : syracuseStep 1672519 = 2508779) B2508779
theorem B1672679 : Blo 1672036 1672679 := bstep (se 1 (by rfl) ⟨1254509, by rfl⟩ : syracuseStep 1672679 = 2509019) B2509019
theorem B6784553 : Blo 1672036 6784553 := bstep (se 2 (by rfl) ⟨2544207, by rfl⟩ : syracuseStep 6784553 = 5088415) B5088415
theorem B1672795 : Blo 1672036 1672795 := bstep (se 1 (by rfl) ⟨1254596, by rfl⟩ : syracuseStep 1672795 = 2509193) B2509193
theorem B2508527 : Blo 1672036 2508527 := bstep (se 1 (by rfl) ⟨1881395, by rfl⟩ : syracuseStep 2508527 = 3762791) B3762791
theorem B1673127 : Blo 1672036 1673127 := bstep (se 1 (by rfl) ⟨1254845, by rfl⟩ : syracuseStep 1673127 = 2509691) B2509691
theorem B5646779 : Blo 1672036 5646779 := bstep (se 1 (by rfl) ⟨4235084, by rfl⟩ : syracuseStep 5646779 = 8470169) B8470169
theorem B1673703 : Blo 1672036 1673703 := bstep (se 1 (by rfl) ⟨1255277, by rfl⟩ : syracuseStep 1673703 = 2510555) B2510555
theorem B3762971 : Blo 1672036 3762971 := bstep (se 1 (by rfl) ⟨2822228, by rfl⟩ : syracuseStep 3762971 = 5644457) B5644457
theorem B6351655 : Blo 1672036 6351655 := bstep (se 1 (by rfl) ⟨4763741, by rfl⟩ : syracuseStep 6351655 = 9527483) B9527483
theorem B12061511 : Blo 1672036 12061511 := bstep (se 1 (by rfl) ⟨9046133, by rfl⟩ : syracuseStep 12061511 = 18092267) B18092267
theorem B19057517 : Blo 1672036 19057517 := bstep (se 3 (by rfl) ⟨3573284, by rfl⟩ : syracuseStep 19057517 = 7146569) B7146569
theorem B12053377 : Blo 1672036 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B2509817 : Blo 1672036 2509817 := bstep (se 2 (by rfl) ⟨941181, by rfl⟩ : syracuseStep 2509817 = 1882363) B1882363
theorem B2821567 : Blo 1672036 2821567 := bstep (se 1 (by rfl) ⟨2116175, by rfl⟩ : syracuseStep 2821567 = 4232351) B4232351
theorem B2510303 : Blo 1672036 2510303 := bstep (se 1 (by rfl) ⟨1882727, by rfl⟩ : syracuseStep 2510303 = 3765455) B3765455
theorem B2510315 : Blo 1672036 2510315 := bstep (se 1 (by rfl) ⟨1882736, by rfl⟩ : syracuseStep 2510315 = 3765473) B3765473
theorem B21433967 : Blo 1672036 21433967 := bstep (se 1 (by rfl) ⟨16075475, by rfl⟩ : syracuseStep 21433967 = 32150951) B32150951
theorem B2821871 : Blo 1672036 2821871 := bstep (se 1 (by rfl) ⟨2116403, by rfl⟩ : syracuseStep 2821871 = 4232807) B4232807
theorem B19050227 : Blo 1672036 19050227 := bstep (se 1 (by rfl) ⟨14287670, by rfl⟩ : syracuseStep 19050227 = 28575341) B28575341
theorem B3764051 : Blo 1672036 3764051 := bstep (se 1 (by rfl) ⟨2823038, by rfl⟩ : syracuseStep 3764051 = 5646077) B5646077
theorem B3764159 : Blo 1672036 3764159 := bstep (se 1 (by rfl) ⟨2823119, by rfl⟩ : syracuseStep 3764159 = 5646239) B5646239
theorem B2510783 : Blo 1672036 2510783 := bstep (se 1 (by rfl) ⟨1883087, by rfl⟩ : syracuseStep 2510783 = 3766175) B3766175
theorem B12709871 : Blo 1672036 12709871 := bstep (se 1 (by rfl) ⟨9532403, by rfl⟩ : syracuseStep 12709871 = 19064807) B19064807
theorem B2822951 : Blo 1672036 2822951 := bstep (se 1 (by rfl) ⟨2117213, by rfl⟩ : syracuseStep 2822951 = 4234427) B4234427
theorem B5649209 : Blo 1672036 5649209 := bstep (se 2 (by rfl) ⟨2118453, by rfl⟩ : syracuseStep 5649209 = 4236907) B4236907
theorem B11441189 : Blo 1672036 11441189 := bstep (se 4 (by rfl) ⟨1072611, by rfl⟩ : syracuseStep 11441189 = 2145223) B2145223
theorem B13055057 : Blo 1672036 13055057 := bstep (se 2 (by rfl) ⟨4895646, by rfl⟩ : syracuseStep 13055057 = 9791293) B9791293
theorem B1881319 : Blo 1672036 1881319 := bstep (se 1 (by rfl) ⟨1410989, by rfl⟩ : syracuseStep 1881319 = 2821979) B2821979
theorem B11015639 : Blo 1672036 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B40687069 : Blo 1672036 40687069 := bstep (se 3 (by rfl) ⟨7628825, by rfl⟩ : syracuseStep 40687069 = 15257651) B15257651
theorem B12056147 : Blo 1672036 12056147 := bstep (se 1 (by rfl) ⟨9042110, by rfl⟩ : syracuseStep 12056147 = 18084221) B18084221
theorem B21444425 : Blo 1672036 21444425 := bstep (se 2 (by rfl) ⟨8041659, by rfl⟩ : syracuseStep 21444425 = 16083319) B16083319
theorem B21436427 : Blo 1672036 21436427 := bstep (se 1 (by rfl) ⟨16077320, by rfl⟩ : syracuseStep 21436427 = 32154641) B32154641
theorem B9042283 : Blo 1672036 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B4233991 : Blo 1672036 4233991 := bstep (se 1 (by rfl) ⟨3175493, by rfl⟩ : syracuseStep 4233991 = 6350987) B6350987
theorem B16071479 : Blo 1672036 16071479 := bstep (se 1 (by rfl) ⟨12053609, by rfl⟩ : syracuseStep 16071479 = 24107219) B24107219
theorem B3013627 : Blo 1672036 3013627 := bstep (se 1 (by rfl) ⟨2260220, by rfl⟩ : syracuseStep 3013627 = 4520441) B4520441
theorem B4234295 : Blo 1672036 4234295 := bstep (se 1 (by rfl) ⟨3175721, by rfl⟩ : syracuseStep 4234295 = 6351443) B6351443
theorem B5356955 : Blo 1672036 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B4234751 : Blo 1672036 4234751 := bstep (se 1 (by rfl) ⟨3176063, by rfl⟩ : syracuseStep 4234751 = 6352127) B6352127
theorem B18079375 : Blo 1672036 18079375 := bstep (se 1 (by rfl) ⟨13559531, by rfl⟩ : syracuseStep 18079375 = 27119063) B27119063
theorem B10460825 : Blo 1672036 10460825 := bstep (se 2 (by rfl) ⟨3922809, by rfl⟩ : syracuseStep 10460825 = 7845619) B7845619
theorem B1785583 : Blo 1672036 1785583 := bstep (se 1 (by rfl) ⟨1339187, by rfl⟩ : syracuseStep 1785583 = 2678375) B2678375
theorem B7627459 : Blo 1672036 7627459 := bstep (se 1 (by rfl) ⟨5720594, by rfl⟩ : syracuseStep 7627459 = 11441189) B11441189
theorem B8471303 : Blo 1672036 8471303 := bstep (se 1 (by rfl) ⟨6353477, by rfl⟩ : syracuseStep 8471303 = 12706955) B12706955
theorem B5645321 : Blo 1672036 5645321 := bstep (se 2 (by rfl) ⟨2116995, by rfl⟩ : syracuseStep 5645321 = 4233991) B4233991
theorem B4523035 : Blo 1672036 4523035 := bstep (se 1 (by rfl) ⟨3392276, by rfl⟩ : syracuseStep 4523035 = 6784553) B6784553
theorem B8037431 : Blo 1672036 8037431 := bstep (se 1 (by rfl) ⟨6028073, by rfl⟩ : syracuseStep 8037431 = 12056147) B12056147
theorem B1672351 : Blo 1672036 1672351 := bstep (se 1 (by rfl) ⟨1254263, by rfl⟩ : syracuseStep 1672351 = 2508527) B2508527
theorem B14296283 : Blo 1672036 14296283 := bstep (se 1 (by rfl) ⟨10722212, by rfl⟩ : syracuseStep 14296283 = 21444425) B21444425
theorem B2508425 : Blo 1672036 2508425 := bstep (se 2 (by rfl) ⟨940659, by rfl⟩ : syracuseStep 2508425 = 1881319) B1881319
theorem B2508647 : Blo 1672036 2508647 := bstep (se 1 (by rfl) ⟨1881485, by rfl⟩ : syracuseStep 2508647 = 3762971) B3762971
theorem B3762089 : Blo 1672036 3762089 := bstep (se 2 (by rfl) ⟨1410783, by rfl⟩ : syracuseStep 3762089 = 2821567) B2821567
theorem B54249425 : Blo 1672036 54249425 := bstep (se 2 (by rfl) ⟨20343534, by rfl⟩ : syracuseStep 54249425 = 40687069) B40687069
theorem B1673211 : Blo 1672036 1673211 := bstep (se 1 (by rfl) ⟨1254908, by rfl⟩ : syracuseStep 1673211 = 2509817) B2509817
theorem B64284677 : Blo 1672036 64284677 := bstep (se 4 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 64284677 = 12053377) B12053377
theorem B1673535 : Blo 1672036 1673535 := bstep (se 1 (by rfl) ⟨1255151, by rfl⟩ : syracuseStep 1673535 = 2510303) B2510303
theorem B1673543 : Blo 1672036 1673543 := bstep (se 1 (by rfl) ⟨1255157, by rfl⟩ : syracuseStep 1673543 = 2510315) B2510315
theorem B14289311 : Blo 1672036 14289311 := bstep (se 1 (by rfl) ⟨10716983, by rfl⟩ : syracuseStep 14289311 = 21433967) B21433967
theorem B6973883 : Blo 1672036 6973883 := bstep (se 1 (by rfl) ⟨5230412, by rfl⟩ : syracuseStep 6973883 = 10460825) B10460825
theorem B12700151 : Blo 1672036 12700151 := bstep (se 1 (by rfl) ⟨9525113, by rfl⟩ : syracuseStep 12700151 = 19050227) B19050227
theorem B2509367 : Blo 1672036 2509367 := bstep (se 1 (by rfl) ⟨1882025, by rfl⟩ : syracuseStep 2509367 = 3764051) B3764051
theorem B2509439 : Blo 1672036 2509439 := bstep (se 1 (by rfl) ⟨1882079, by rfl⟩ : syracuseStep 2509439 = 3764159) B3764159
theorem B1673855 : Blo 1672036 1673855 := bstep (se 1 (by rfl) ⟨1255391, by rfl⟩ : syracuseStep 1673855 = 2510783) B2510783
theorem B8473247 : Blo 1672036 8473247 := bstep (se 1 (by rfl) ⟨6354935, by rfl⟩ : syracuseStep 8473247 = 12709871) B12709871
theorem B3763583 : Blo 1672036 3763583 := bstep (se 1 (by rfl) ⟨2822687, by rfl⟩ : syracuseStep 3763583 = 5645375) B5645375
theorem B8703371 : Blo 1672036 8703371 := bstep (se 1 (by rfl) ⟨6527528, by rfl⟩ : syracuseStep 8703371 = 13055057) B13055057
theorem B3763691 : Blo 1672036 3763691 := bstep (se 1 (by rfl) ⟨2822768, by rfl⟩ : syracuseStep 3763691 = 5645537) B5645537
theorem B7343759 : Blo 1672036 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B9523109 : Blo 1672036 9523109 := bstep (se 4 (by rfl) ⟨892791, by rfl⟩ : syracuseStep 9523109 = 1785583) B1785583
theorem B4018169 : Blo 1672036 4018169 := bstep (se 2 (by rfl) ⟨1506813, by rfl⟩ : syracuseStep 4018169 = 3013627) B3013627
theorem B14290951 : Blo 1672036 14290951 := bstep (se 1 (by rfl) ⟨10718213, by rfl⟩ : syracuseStep 14290951 = 21436427) B21436427
theorem B3764519 : Blo 1672036 3764519 := bstep (se 1 (by rfl) ⟨2823389, by rfl⟩ : syracuseStep 3764519 = 5646779) B5646779
theorem B8041007 : Blo 1672036 8041007 := bstep (se 1 (by rfl) ⟨6030755, by rfl⟩ : syracuseStep 8041007 = 12061511) B12061511
theorem B2822863 : Blo 1672036 2822863 := bstep (se 1 (by rfl) ⟨2117147, by rfl⟩ : syracuseStep 2822863 = 4234295) B4234295
theorem B24105833 : Blo 1672036 24105833 := bstep (se 2 (by rfl) ⟨9039687, by rfl⟩ : syracuseStep 24105833 = 18079375) B18079375
theorem B2823167 : Blo 1672036 2823167 := bstep (se 1 (by rfl) ⟨2117375, by rfl⟩ : syracuseStep 2823167 = 4234751) B4234751
theorem B1881247 : Blo 1672036 1881247 := bstep (se 1 (by rfl) ⟨1410935, by rfl⟩ : syracuseStep 1881247 = 2821871) B2821871
theorem B103044545 : Blo 1672036 103044545 := bstep (se 2 (by rfl) ⟨38641704, by rfl⟩ : syracuseStep 103044545 = 77283409) B77283409
theorem B2545199 : Blo 1672036 2545199 := bstep (se 1 (by rfl) ⟨1908899, by rfl⟩ : syracuseStep 2545199 = 3817799) B3817799
theorem B17176151 : Blo 1672036 17176151 := bstep (se 1 (by rfl) ⟨12882113, by rfl⟩ : syracuseStep 17176151 = 25764227) B25764227
theorem B7149167 : Blo 1672036 7149167 := bstep (se 1 (by rfl) ⟨5361875, by rfl⟩ : syracuseStep 7149167 = 10723751) B10723751
theorem B4232999 : Blo 1672036 4232999 := bstep (se 1 (by rfl) ⟨3174749, by rfl⟩ : syracuseStep 4232999 = 6349499) B6349499
theorem B12056377 : Blo 1672036 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B1881967 : Blo 1672036 1881967 := bstep (se 1 (by rfl) ⟨1411475, by rfl⟩ : syracuseStep 1881967 = 2822951) B2822951
theorem B3766139 : Blo 1672036 3766139 := bstep (se 1 (by rfl) ⟨2824604, by rfl⟩ : syracuseStep 3766139 = 5649209) B5649209
theorem B14292935 : Blo 1672036 14292935 := bstep (se 1 (by rfl) ⟨10719701, by rfl⟩ : syracuseStep 14292935 = 21439403) B21439403
theorem B2824247 : Blo 1672036 2824247 := bstep (se 1 (by rfl) ⟨2118185, by rfl⟩ : syracuseStep 2824247 = 4236371) B4236371
theorem B4233323 : Blo 1672036 4233323 := bstep (se 1 (by rfl) ⟨3174992, by rfl⟩ : syracuseStep 4233323 = 6349985) B6349985
theorem B8468873 : Blo 1672036 8468873 := bstep (se 2 (by rfl) ⟨3175827, by rfl⟩ : syracuseStep 8468873 = 6351655) B6351655
theorem B10714319 : Blo 1672036 10714319 := bstep (se 1 (by rfl) ⟨8035739, by rfl⟩ : syracuseStep 10714319 = 16071479) B16071479
theorem B12705011 : Blo 1672036 12705011 := bstep (se 1 (by rfl) ⟨9528758, by rfl⟩ : syracuseStep 12705011 = 19057517) B19057517
theorem B3571303 : Blo 1672036 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B19054601 : Blo 1672036 19054601 := bstep (se 2 (by rfl) ⟨7145475, by rfl⟩ : syracuseStep 19054601 = 14290951) B14290951
theorem B5358287 : Blo 1672036 5358287 := bstep (se 1 (by rfl) ⟨4018715, by rfl⟩ : syracuseStep 5358287 = 8037431) B8037431
theorem B1696799 : Blo 1672036 1696799 := bstep (se 1 (by rfl) ⟨1272599, by rfl⟩ : syracuseStep 1696799 = 2545199) B2545199
theorem B1672283 : Blo 1672036 1672283 := bstep (se 1 (by rfl) ⟨1254212, by rfl⟩ : syracuseStep 1672283 = 2508425) B2508425
theorem B1672431 : Blo 1672036 1672431 := bstep (se 1 (by rfl) ⟨1254323, by rfl⟩ : syracuseStep 1672431 = 2508647) B2508647
theorem B2508059 : Blo 1672036 2508059 := bstep (se 1 (by rfl) ⟨1881044, by rfl⟩ : syracuseStep 2508059 = 3762089) B3762089
theorem B9528623 : Blo 1672036 9528623 := bstep (se 1 (by rfl) ⟨7146467, by rfl⟩ : syracuseStep 9528623 = 14292935) B14292935
theorem B6030713 : Blo 1672036 6030713 := bstep (se 2 (by rfl) ⟨2261517, by rfl⟩ : syracuseStep 6030713 = 4523035) B4523035
theorem B2508329 : Blo 1672036 2508329 := bstep (se 2 (by rfl) ⟨940623, by rfl⟩ : syracuseStep 2508329 = 1881247) B1881247
theorem B5645915 : Blo 1672036 5645915 := bstep (se 1 (by rfl) ⟨4234436, by rfl⟩ : syracuseStep 5645915 = 8468873) B8468873
theorem B1672911 : Blo 1672036 1672911 := bstep (se 1 (by rfl) ⟨1254683, by rfl⟩ : syracuseStep 1672911 = 2509367) B2509367
theorem B1672959 : Blo 1672036 1672959 := bstep (se 1 (by rfl) ⟨1254719, by rfl⟩ : syracuseStep 1672959 = 2509439) B2509439
theorem B4761737 : Blo 1672036 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B2509055 : Blo 1672036 2509055 := bstep (se 1 (by rfl) ⟨1881791, by rfl⟩ : syracuseStep 2509055 = 3763583) B3763583
theorem B5802247 : Blo 1672036 5802247 := bstep (se 1 (by rfl) ⟨4351685, by rfl⟩ : syracuseStep 5802247 = 8703371) B8703371
theorem B2509127 : Blo 1672036 2509127 := bstep (se 1 (by rfl) ⟨1881845, by rfl⟩ : syracuseStep 2509127 = 3763691) B3763691
theorem B16075169 : Blo 1672036 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B2509289 : Blo 1672036 2509289 := bstep (se 2 (by rfl) ⟨940983, by rfl⟩ : syracuseStep 2509289 = 1881967) B1881967
theorem B2509679 : Blo 1672036 2509679 := bstep (se 1 (by rfl) ⟨1882259, by rfl⟩ : syracuseStep 2509679 = 3764519) B3764519
theorem B5360671 : Blo 1672036 5360671 := bstep (se 1 (by rfl) ⟨4020503, by rfl⟩ : syracuseStep 5360671 = 8041007) B8041007
theorem B5647535 : Blo 1672036 5647535 := bstep (se 1 (by rfl) ⟨4235651, by rfl⟩ : syracuseStep 5647535 = 8471303) B8471303
theorem B3763547 : Blo 1672036 3763547 := bstep (se 1 (by rfl) ⟨2822660, by rfl⟩ : syracuseStep 3763547 = 5645321) B5645321
theorem B9530855 : Blo 1672036 9530855 := bstep (se 1 (by rfl) ⟨7148141, by rfl⟩ : syracuseStep 9530855 = 14296283) B14296283
theorem B10169945 : Blo 1672036 10169945 := bstep (se 2 (by rfl) ⟨3813729, by rfl⟩ : syracuseStep 10169945 = 7627459) B7627459
theorem B3763817 : Blo 1672036 3763817 := bstep (se 2 (by rfl) ⟨1411431, by rfl⟩ : syracuseStep 3763817 = 2822863) B2822863
theorem B2821999 : Blo 1672036 2821999 := bstep (se 1 (by rfl) ⟨2116499, by rfl⟩ : syracuseStep 2821999 = 4232999) B4232999
theorem B2510759 : Blo 1672036 2510759 := bstep (se 1 (by rfl) ⟨1883069, by rfl⟩ : syracuseStep 2510759 = 3766139) B3766139
theorem B42856451 : Blo 1672036 42856451 := bstep (se 1 (by rfl) ⟨32142338, by rfl⟩ : syracuseStep 42856451 = 64284677) B64284677
theorem B2822215 : Blo 1672036 2822215 := bstep (se 1 (by rfl) ⟨2116661, by rfl⟩ : syracuseStep 2822215 = 4233323) B4233323
theorem B4649255 : Blo 1672036 4649255 := bstep (se 1 (by rfl) ⟨3486941, by rfl⟩ : syracuseStep 4649255 = 6973883) B6973883
theorem B8466767 : Blo 1672036 8466767 := bstep (se 1 (by rfl) ⟨6350075, by rfl⟩ : syracuseStep 8466767 = 12700151) B12700151
theorem B5648831 : Blo 1672036 5648831 := bstep (se 1 (by rfl) ⟨4236623, by rfl⟩ : syracuseStep 5648831 = 8473247) B8473247
theorem B4895839 : Blo 1672036 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B16070555 : Blo 1672036 16070555 := bstep (se 1 (by rfl) ⟨12052916, by rfl⟩ : syracuseStep 16070555 = 24105833) B24105833
theorem B1882111 : Blo 1672036 1882111 := bstep (se 1 (by rfl) ⟨1411583, by rfl⟩ : syracuseStep 1882111 = 2823167) B2823167
theorem B68696363 : Blo 1672036 68696363 := bstep (se 1 (by rfl) ⟨51522272, by rfl⟩ : syracuseStep 68696363 = 103044545) B103044545
theorem B11450767 : Blo 1672036 11450767 := bstep (se 1 (by rfl) ⟨8588075, by rfl⟩ : syracuseStep 11450767 = 17176151) B17176151
theorem B4766111 : Blo 1672036 4766111 := bstep (se 1 (by rfl) ⟨3574583, by rfl⟩ : syracuseStep 4766111 = 7149167) B7149167
theorem B36166283 : Blo 1672036 36166283 := bstep (se 1 (by rfl) ⟨27124712, by rfl⟩ : syracuseStep 36166283 = 54249425) B54249425
theorem B1882831 : Blo 1672036 1882831 := bstep (se 1 (by rfl) ⟨1412123, by rfl⟩ : syracuseStep 1882831 = 2824247) B2824247
theorem B9526207 : Blo 1672036 9526207 := bstep (se 1 (by rfl) ⟨7144655, by rfl⟩ : syracuseStep 9526207 = 14289311) B14289311
theorem B7142879 : Blo 1672036 7142879 := bstep (se 1 (by rfl) ⟨5357159, by rfl⟩ : syracuseStep 7142879 = 10714319) B10714319
theorem B8470007 : Blo 1672036 8470007 := bstep (se 1 (by rfl) ⟨6352505, by rfl⟩ : syracuseStep 8470007 = 12705011) B12705011
theorem B6348739 : Blo 1672036 6348739 := bstep (se 1 (by rfl) ⟨4761554, by rfl⟩ : syracuseStep 6348739 = 9523109) B9523109
theorem B2678779 : Blo 1672036 2678779 := bstep (se 1 (by rfl) ⟨2009084, by rfl⟩ : syracuseStep 2678779 = 4018169) B4018169
theorem B5644511 : Blo 1672036 5644511 := bstep (se 1 (by rfl) ⟨4233383, by rfl⟩ : syracuseStep 5644511 = 8466767) B8466767
theorem B3572191 : Blo 1672036 3572191 := bstep (se 1 (by rfl) ⟨2679143, by rfl⟩ : syracuseStep 3572191 = 5358287) B5358287
theorem B1672039 : Blo 1672036 1672039 := bstep (se 1 (by rfl) ⟨1254029, by rfl⟩ : syracuseStep 1672039 = 2508059) B2508059
theorem B16081901 : Blo 1672036 16081901 := bstep (se 3 (by rfl) ⟨3015356, by rfl⟩ : syracuseStep 16081901 = 6030713) B6030713
theorem B1672219 : Blo 1672036 1672219 := bstep (se 1 (by rfl) ⟨1254164, by rfl⟩ : syracuseStep 1672219 = 2508329) B2508329
theorem B1672703 : Blo 1672036 1672703 := bstep (se 1 (by rfl) ⟨1254527, by rfl⟩ : syracuseStep 1672703 = 2509055) B2509055
theorem B1672751 : Blo 1672036 1672751 := bstep (se 1 (by rfl) ⟨1254563, by rfl⟩ : syracuseStep 1672751 = 2509127) B2509127
theorem B10716779 : Blo 1672036 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B1672859 : Blo 1672036 1672859 := bstep (se 1 (by rfl) ⟨1254644, by rfl⟩ : syracuseStep 1672859 = 2509289) B2509289
theorem B24110855 : Blo 1672036 24110855 := bstep (se 1 (by rfl) ⟨18083141, by rfl⟩ : syracuseStep 24110855 = 36166283) B36166283
theorem B1673119 : Blo 1672036 1673119 := bstep (se 1 (by rfl) ⟨1254839, by rfl⟩ : syracuseStep 1673119 = 2509679) B2509679
theorem B2509031 : Blo 1672036 2509031 := bstep (se 1 (by rfl) ⟨1881773, by rfl⟩ : syracuseStep 2509031 = 3763547) B3763547
theorem B4761919 : Blo 1672036 4761919 := bstep (se 1 (by rfl) ⟨3571439, by rfl⟩ : syracuseStep 4761919 = 7142879) B7142879
theorem B5646671 : Blo 1672036 5646671 := bstep (se 1 (by rfl) ⟨4235003, by rfl⟩ : syracuseStep 5646671 = 8470007) B8470007
theorem B2509211 : Blo 1672036 2509211 := bstep (se 1 (by rfl) ⟨1881908, by rfl⟩ : syracuseStep 2509211 = 3763817) B3763817
theorem B3762665 : Blo 1672036 3762665 := bstep (se 2 (by rfl) ⟨1410999, by rfl⟩ : syracuseStep 3762665 = 2821999) B2821999
theorem B8464985 : Blo 1672036 8464985 := bstep (se 2 (by rfl) ⟨3174369, by rfl⟩ : syracuseStep 8464985 = 6348739) B6348739
theorem B1673839 : Blo 1672036 1673839 := bstep (se 1 (by rfl) ⟨1255379, by rfl⟩ : syracuseStep 1673839 = 2510759) B2510759
theorem B2509481 : Blo 1672036 2509481 := bstep (se 2 (by rfl) ⟨941055, by rfl⟩ : syracuseStep 2509481 = 1882111) B1882111
theorem B4524797 : Blo 1672036 4524797 := bstep (se 3 (by rfl) ⟨848399, by rfl⟩ : syracuseStep 4524797 = 1696799) B1696799
theorem B3762953 : Blo 1672036 3762953 := bstep (se 2 (by rfl) ⟨1411107, by rfl⟩ : syracuseStep 3762953 = 2822215) B2822215
theorem B3099503 : Blo 1672036 3099503 := bstep (se 1 (by rfl) ⟨2324627, by rfl⟩ : syracuseStep 3099503 = 4649255) B4649255
theorem B7736329 : Blo 1672036 7736329 := bstep (se 2 (by rfl) ⟨2901123, by rfl⟩ : syracuseStep 7736329 = 5802247) B5802247
theorem B6352415 : Blo 1672036 6352415 := bstep (se 1 (by rfl) ⟨4764311, by rfl⟩ : syracuseStep 6352415 = 9528623) B9528623
theorem B2510441 : Blo 1672036 2510441 := bstep (se 2 (by rfl) ⟨941415, by rfl⟩ : syracuseStep 2510441 = 1882831) B1882831
theorem B3763943 : Blo 1672036 3763943 := bstep (se 1 (by rfl) ⟨2822957, by rfl⟩ : syracuseStep 3763943 = 5645915) B5645915
theorem B12701609 : Blo 1672036 12701609 := bstep (se 2 (by rfl) ⟨4763103, by rfl⟩ : syracuseStep 12701609 = 9526207) B9526207
theorem B7147561 : Blo 1672036 7147561 := bstep (se 2 (by rfl) ⟨2680335, by rfl⟩ : syracuseStep 7147561 = 5360671) B5360671
theorem B3174491 : Blo 1672036 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B45797575 : Blo 1672036 45797575 := bstep (se 1 (by rfl) ⟨34348181, by rfl⟩ : syracuseStep 45797575 = 68696363) B68696363
theorem B3765023 : Blo 1672036 3765023 := bstep (se 1 (by rfl) ⟨2823767, by rfl⟩ : syracuseStep 3765023 = 5647535) B5647535
theorem B6353903 : Blo 1672036 6353903 := bstep (se 1 (by rfl) ⟨4765427, by rfl⟩ : syracuseStep 6353903 = 9530855) B9530855
theorem B6779963 : Blo 1672036 6779963 := bstep (se 1 (by rfl) ⟨5084972, by rfl⟩ : syracuseStep 6779963 = 10169945) B10169945
theorem B28570967 : Blo 1672036 28570967 := bstep (se 1 (by rfl) ⟨21428225, by rfl⟩ : syracuseStep 28570967 = 42856451) B42856451
theorem B12703067 : Blo 1672036 12703067 := bstep (se 1 (by rfl) ⟨9527300, by rfl⟩ : syracuseStep 12703067 = 19054601) B19054601
theorem B3765887 : Blo 1672036 3765887 := bstep (se 1 (by rfl) ⟨2824415, by rfl⟩ : syracuseStep 3765887 = 5648831) B5648831
theorem B15267689 : Blo 1672036 15267689 := bstep (se 2 (by rfl) ⟨5725383, by rfl⟩ : syracuseStep 15267689 = 11450767) B11450767
theorem B10713703 : Blo 1672036 10713703 := bstep (se 1 (by rfl) ⟨8035277, by rfl⟩ : syracuseStep 10713703 = 16070555) B16070555
theorem B6527785 : Blo 1672036 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B3177407 : Blo 1672036 3177407 := bstep (se 1 (by rfl) ⟨2383055, by rfl⟩ : syracuseStep 3177407 = 4766111) B4766111
theorem B3571705 : Blo 1672036 3571705 := bstep (se 2 (by rfl) ⟨1339389, by rfl⟩ : syracuseStep 3571705 = 2678779) B2678779
theorem B61063433 : Blo 1672036 61063433 := bstep (se 2 (by rfl) ⟨22898787, by rfl⟩ : syracuseStep 61063433 = 45797575) B45797575
theorem B6349225 : Blo 1672036 6349225 := bstep (se 2 (by rfl) ⟨2380959, by rfl⟩ : syracuseStep 6349225 = 4761919) B4761919
theorem B4235935 : Blo 1672036 4235935 := bstep (se 1 (by rfl) ⟨3176951, by rfl⟩ : syracuseStep 4235935 = 6353903) B6353903
theorem B19047311 : Blo 1672036 19047311 := bstep (se 1 (by rfl) ⟨14285483, by rfl⟩ : syracuseStep 19047311 = 28570967) B28570967
theorem B7144519 : Blo 1672036 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B16073903 : Blo 1672036 16073903 := bstep (se 1 (by rfl) ⟨12055427, by rfl⟩ : syracuseStep 16073903 = 24110855) B24110855
theorem B1672687 : Blo 1672036 1672687 := bstep (se 1 (by rfl) ⟨1254515, by rfl⟩ : syracuseStep 1672687 = 2509031) B2509031
theorem B1672807 : Blo 1672036 1672807 := bstep (se 1 (by rfl) ⟨1254605, by rfl⟩ : syracuseStep 1672807 = 2509211) B2509211
theorem B2508443 : Blo 1672036 2508443 := bstep (se 1 (by rfl) ⟨1881332, by rfl⟩ : syracuseStep 2508443 = 3762665) B3762665
theorem B1672987 : Blo 1672036 1672987 := bstep (se 1 (by rfl) ⟨1254740, by rfl⟩ : syracuseStep 1672987 = 2509481) B2509481
theorem B3016531 : Blo 1672036 3016531 := bstep (se 1 (by rfl) ⟨2262398, by rfl⟩ : syracuseStep 3016531 = 4524797) B4524797
theorem B2508635 : Blo 1672036 2508635 := bstep (se 1 (by rfl) ⟨1881476, by rfl⟩ : syracuseStep 2508635 = 3762953) B3762953
theorem B1673627 : Blo 1672036 1673627 := bstep (se 1 (by rfl) ⟨1255220, by rfl⟩ : syracuseStep 1673627 = 2510441) B2510441
theorem B2509295 : Blo 1672036 2509295 := bstep (se 1 (by rfl) ⟨1881971, by rfl⟩ : syracuseStep 2509295 = 3763943) B3763943
theorem B8473085 : Blo 1672036 8473085 := bstep (se 3 (by rfl) ⟨1588703, by rfl⟩ : syracuseStep 8473085 = 3177407) B3177407
theorem B4762273 : Blo 1672036 4762273 := bstep (se 2 (by rfl) ⟨1785852, by rfl⟩ : syracuseStep 4762273 = 3571705) B3571705
theorem B9530081 : Blo 1672036 9530081 := bstep (se 2 (by rfl) ⟨3573780, by rfl⟩ : syracuseStep 9530081 = 7147561) B7147561
theorem B3763007 : Blo 1672036 3763007 := bstep (se 1 (by rfl) ⟨2822255, by rfl⟩ : syracuseStep 3763007 = 5644511) B5644511
theorem B8465309 : Blo 1672036 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B2510015 : Blo 1672036 2510015 := bstep (se 1 (by rfl) ⟨1882511, by rfl⟩ : syracuseStep 2510015 = 3765023) B3765023
theorem B8703713 : Blo 1672036 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B2510591 : Blo 1672036 2510591 := bstep (se 1 (by rfl) ⟨1882943, by rfl⟩ : syracuseStep 2510591 = 3765887) B3765887
theorem B10178459 : Blo 1672036 10178459 := bstep (se 1 (by rfl) ⟨7633844, by rfl⟩ : syracuseStep 10178459 = 15267689) B15267689
theorem B3764447 : Blo 1672036 3764447 := bstep (se 1 (by rfl) ⟨2823335, by rfl⟩ : syracuseStep 3764447 = 5646671) B5646671
theorem B19051685 : Blo 1672036 19051685 := bstep (se 4 (by rfl) ⟨1786095, by rfl⟩ : syracuseStep 19051685 = 3572191) B3572191
theorem B8467739 : Blo 1672036 8467739 := bstep (se 1 (by rfl) ⟨6350804, by rfl⟩ : syracuseStep 8467739 = 12701609) B12701609
theorem B41260421 : Blo 1672036 41260421 := bstep (se 4 (by rfl) ⟨3868164, by rfl⟩ : syracuseStep 41260421 = 7736329) B7736329
theorem B10721267 : Blo 1672036 10721267 := bstep (se 1 (by rfl) ⟨8040950, by rfl⟩ : syracuseStep 10721267 = 16081901) B16081901
theorem B4519975 : Blo 1672036 4519975 := bstep (se 1 (by rfl) ⟨3389981, by rfl⟩ : syracuseStep 4519975 = 6779963) B6779963
theorem B14284937 : Blo 1672036 14284937 := bstep (se 2 (by rfl) ⟨5356851, by rfl⟩ : syracuseStep 14284937 = 10713703) B10713703
theorem B8468711 : Blo 1672036 8468711 := bstep (se 1 (by rfl) ⟨6351533, by rfl⟩ : syracuseStep 8468711 = 12703067) B12703067
theorem B5643323 : Blo 1672036 5643323 := bstep (se 1 (by rfl) ⟨4232492, by rfl⟩ : syracuseStep 5643323 = 8464985) B8464985
theorem B8265341 : Blo 1672036 8265341 := bstep (se 3 (by rfl) ⟨1549751, by rfl⟩ : syracuseStep 8265341 = 3099503) B3099503
theorem B4234943 : Blo 1672036 4234943 := bstep (se 1 (by rfl) ⟨3176207, by rfl⟩ : syracuseStep 4234943 = 6352415) B6352415
theorem B12698207 : Blo 1672036 12698207 := bstep (se 1 (by rfl) ⟨9523655, by rfl⟩ : syracuseStep 12698207 = 19047311) B19047311
theorem B10715935 : Blo 1672036 10715935 := bstep (se 1 (by rfl) ⟨8036951, by rfl⟩ : syracuseStep 10715935 = 16073903) B16073903
theorem B5645159 : Blo 1672036 5645159 := bstep (se 1 (by rfl) ⟨4233869, by rfl⟩ : syracuseStep 5645159 = 8467739) B8467739
theorem B6349697 : Blo 1672036 6349697 := bstep (se 2 (by rfl) ⟨2381136, by rfl⟩ : syracuseStep 6349697 = 4762273) B4762273
theorem B1672295 : Blo 1672036 1672295 := bstep (se 1 (by rfl) ⟨1254221, by rfl⟩ : syracuseStep 1672295 = 2508443) B2508443
theorem B1672423 : Blo 1672036 1672423 := bstep (se 1 (by rfl) ⟨1254317, by rfl⟩ : syracuseStep 1672423 = 2508635) B2508635
theorem B5645807 : Blo 1672036 5645807 := bstep (se 1 (by rfl) ⟨4234355, by rfl⟩ : syracuseStep 5645807 = 8468711) B8468711
theorem B1672863 : Blo 1672036 1672863 := bstep (se 1 (by rfl) ⟨1254647, by rfl⟩ : syracuseStep 1672863 = 2509295) B2509295
theorem B2508671 : Blo 1672036 2508671 := bstep (se 1 (by rfl) ⟨1881503, by rfl⟩ : syracuseStep 2508671 = 3763007) B3763007
theorem B23209901 : Blo 1672036 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B3762215 : Blo 1672036 3762215 := bstep (se 1 (by rfl) ⟨2821661, by rfl⟩ : syracuseStep 3762215 = 5643323) B5643323
theorem B1673343 : Blo 1672036 1673343 := bstep (se 1 (by rfl) ⟨1255007, by rfl⟩ : syracuseStep 1673343 = 2510015) B2510015
theorem B1673727 : Blo 1672036 1673727 := bstep (se 1 (by rfl) ⟨1255295, by rfl⟩ : syracuseStep 1673727 = 2510591) B2510591
theorem B6785639 : Blo 1672036 6785639 := bstep (se 1 (by rfl) ⟨5089229, by rfl⟩ : syracuseStep 6785639 = 10178459) B10178459
theorem B2509631 : Blo 1672036 2509631 := bstep (se 1 (by rfl) ⟨1882223, by rfl⟩ : syracuseStep 2509631 = 3764447) B3764447
theorem B40708955 : Blo 1672036 40708955 := bstep (se 1 (by rfl) ⟨30531716, by rfl⟩ : syracuseStep 40708955 = 61063433) B61063433
theorem B8465633 : Blo 1672036 8465633 := bstep (se 2 (by rfl) ⟨3174612, by rfl⟩ : syracuseStep 8465633 = 6349225) B6349225
theorem B12701123 : Blo 1672036 12701123 := bstep (se 1 (by rfl) ⟨9525842, by rfl⟩ : syracuseStep 12701123 = 19051685) B19051685
theorem B5647913 : Blo 1672036 5647913 := bstep (se 2 (by rfl) ⟨2117967, by rfl⟩ : syracuseStep 5647913 = 4235935) B4235935
theorem B7147511 : Blo 1672036 7147511 := bstep (se 1 (by rfl) ⟨5360633, by rfl⟩ : syracuseStep 7147511 = 10721267) B10721267
theorem B9523291 : Blo 1672036 9523291 := bstep (se 1 (by rfl) ⟨7142468, by rfl⟩ : syracuseStep 9523291 = 14284937) B14284937
theorem B5648723 : Blo 1672036 5648723 := bstep (se 1 (by rfl) ⟨4236542, by rfl⟩ : syracuseStep 5648723 = 8473085) B8473085
theorem B6353387 : Blo 1672036 6353387 := bstep (se 1 (by rfl) ⟨4765040, by rfl⟩ : syracuseStep 6353387 = 9530081) B9530081
theorem B5510227 : Blo 1672036 5510227 := bstep (se 1 (by rfl) ⟨4132670, by rfl⟩ : syracuseStep 5510227 = 8265341) B8265341
theorem B2823295 : Blo 1672036 2823295 := bstep (se 1 (by rfl) ⟨2117471, by rfl⟩ : syracuseStep 2823295 = 4234943) B4234943
theorem B6026633 : Blo 1672036 6026633 := bstep (se 2 (by rfl) ⟨2259987, by rfl⟩ : syracuseStep 6026633 = 4519975) B4519975
theorem B27506947 : Blo 1672036 27506947 := bstep (se 1 (by rfl) ⟨20630210, by rfl⟩ : syracuseStep 27506947 = 41260421) B41260421
theorem B9526025 : Blo 1672036 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B16088165 : Blo 1672036 16088165 := bstep (se 4 (by rfl) ⟨1508265, by rfl⟩ : syracuseStep 16088165 = 3016531) B3016531
theorem B5643539 : Blo 1672036 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B12697721 : Blo 1672036 12697721 := bstep (se 2 (by rfl) ⟨4761645, by rfl⟩ : syracuseStep 12697721 = 9523291) B9523291
theorem B4235591 : Blo 1672036 4235591 := bstep (se 1 (by rfl) ⟨3176693, by rfl⟩ : syracuseStep 4235591 = 6353387) B6353387
theorem B36675929 : Blo 1672036 36675929 := bstep (se 2 (by rfl) ⟨13753473, by rfl⟩ : syracuseStep 36675929 = 27506947) B27506947
theorem B14287913 : Blo 1672036 14287913 := bstep (se 2 (by rfl) ⟨5357967, by rfl⟩ : syracuseStep 14287913 = 10715935) B10715935
theorem B1672447 : Blo 1672036 1672447 := bstep (se 1 (by rfl) ⟨1254335, by rfl⟩ : syracuseStep 1672447 = 2508671) B2508671
theorem B2508143 : Blo 1672036 2508143 := bstep (se 1 (by rfl) ⟨1881107, by rfl⟩ : syracuseStep 2508143 = 3762215) B3762215
theorem B4523759 : Blo 1672036 4523759 := bstep (se 1 (by rfl) ⟨3392819, by rfl⟩ : syracuseStep 4523759 = 6785639) B6785639
theorem B6350683 : Blo 1672036 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B1673087 : Blo 1672036 1673087 := bstep (se 1 (by rfl) ⟨1254815, by rfl⟩ : syracuseStep 1673087 = 2509631) B2509631
theorem B10725443 : Blo 1672036 10725443 := bstep (se 1 (by rfl) ⟨8044082, by rfl⟩ : syracuseStep 10725443 = 16088165) B16088165
theorem B3762359 : Blo 1672036 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B8465471 : Blo 1672036 8465471 := bstep (se 1 (by rfl) ⟨6349103, by rfl⟩ : syracuseStep 8465471 = 12698207) B12698207
theorem B3763439 : Blo 1672036 3763439 := bstep (se 1 (by rfl) ⟨2822579, by rfl⟩ : syracuseStep 3763439 = 5645159) B5645159
theorem B4017755 : Blo 1672036 4017755 := bstep (se 1 (by rfl) ⟨3013316, by rfl⟩ : syracuseStep 4017755 = 6026633) B6026633
theorem B3763871 : Blo 1672036 3763871 := bstep (se 1 (by rfl) ⟨2822903, by rfl⟩ : syracuseStep 3763871 = 5645807) B5645807
theorem B3764393 : Blo 1672036 3764393 := bstep (se 2 (by rfl) ⟨1411647, by rfl⟩ : syracuseStep 3764393 = 2823295) B2823295
theorem B8467415 : Blo 1672036 8467415 := bstep (se 1 (by rfl) ⟨6350561, by rfl⟩ : syracuseStep 8467415 = 12701123) B12701123
theorem B3765275 : Blo 1672036 3765275 := bstep (se 1 (by rfl) ⟨2823956, by rfl⟩ : syracuseStep 3765275 = 5647913) B5647913
theorem B4765007 : Blo 1672036 4765007 := bstep (se 1 (by rfl) ⟨3573755, by rfl⟩ : syracuseStep 4765007 = 7147511) B7147511
theorem B3765815 : Blo 1672036 3765815 := bstep (se 1 (by rfl) ⟨2824361, by rfl⟩ : syracuseStep 3765815 = 5648723) B5648723
theorem B4233131 : Blo 1672036 4233131 := bstep (se 1 (by rfl) ⟨3174848, by rfl⟩ : syracuseStep 4233131 = 6349697) B6349697
theorem B15473267 : Blo 1672036 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B7346969 : Blo 1672036 7346969 := bstep (se 2 (by rfl) ⟨2755113, by rfl⟩ : syracuseStep 7346969 = 5510227) B5510227
theorem B27139303 : Blo 1672036 27139303 := bstep (se 1 (by rfl) ⟨20354477, by rfl⟩ : syracuseStep 27139303 = 40708955) B40708955
theorem B5643755 : Blo 1672036 5643755 := bstep (se 1 (by rfl) ⟨4232816, by rfl⟩ : syracuseStep 5643755 = 8465633) B8465633
theorem B5644943 : Blo 1672036 5644943 := bstep (se 1 (by rfl) ⟨4233707, by rfl⟩ : syracuseStep 5644943 = 8467415) B8467415
theorem B1672095 : Blo 1672036 1672095 := bstep (se 1 (by rfl) ⟨1254071, by rfl⟩ : syracuseStep 1672095 = 2508143) B2508143
theorem B3015839 : Blo 1672036 3015839 := bstep (se 1 (by rfl) ⟨2261879, by rfl⟩ : syracuseStep 3015839 = 4523759) B4523759
theorem B2508239 : Blo 1672036 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B36185737 : Blo 1672036 36185737 := bstep (se 2 (by rfl) ⟨13569651, by rfl⟩ : syracuseStep 36185737 = 27139303) B27139303
theorem B10315511 : Blo 1672036 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B2508959 : Blo 1672036 2508959 := bstep (se 1 (by rfl) ⟨1881719, by rfl⟩ : syracuseStep 2508959 = 3763439) B3763439
theorem B3762503 : Blo 1672036 3762503 := bstep (se 1 (by rfl) ⟨2821877, by rfl⟩ : syracuseStep 3762503 = 5643755) B5643755
theorem B2509247 : Blo 1672036 2509247 := bstep (se 1 (by rfl) ⟨1881935, by rfl⟩ : syracuseStep 2509247 = 3763871) B3763871
theorem B8465147 : Blo 1672036 8465147 := bstep (se 1 (by rfl) ⟨6348860, by rfl⟩ : syracuseStep 8465147 = 12697721) B12697721
theorem B2509595 : Blo 1672036 2509595 := bstep (se 1 (by rfl) ⟨1882196, by rfl⟩ : syracuseStep 2509595 = 3764393) B3764393
theorem B2510183 : Blo 1672036 2510183 := bstep (se 1 (by rfl) ⟨1882637, by rfl⟩ : syracuseStep 2510183 = 3765275) B3765275
theorem B2510543 : Blo 1672036 2510543 := bstep (se 1 (by rfl) ⟨1882907, by rfl⟩ : syracuseStep 2510543 = 3765815) B3765815
theorem B2822087 : Blo 1672036 2822087 := bstep (se 1 (by rfl) ⟨2116565, by rfl⟩ : syracuseStep 2822087 = 4233131) B4233131
theorem B8467577 : Blo 1672036 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B2823727 : Blo 1672036 2823727 := bstep (se 1 (by rfl) ⟨2117795, by rfl⟩ : syracuseStep 2823727 = 4235591) B4235591
theorem B24450619 : Blo 1672036 24450619 := bstep (se 1 (by rfl) ⟨18337964, by rfl⟩ : syracuseStep 24450619 = 36675929) B36675929
theorem B9525275 : Blo 1672036 9525275 := bstep (se 1 (by rfl) ⟨7143956, by rfl⟩ : syracuseStep 9525275 = 14287913) B14287913
theorem B3176671 : Blo 1672036 3176671 := bstep (se 1 (by rfl) ⟨2382503, by rfl⟩ : syracuseStep 3176671 = 4765007) B4765007
theorem B7150295 : Blo 1672036 7150295 := bstep (se 1 (by rfl) ⟨5362721, by rfl⟩ : syracuseStep 7150295 = 10725443) B10725443
theorem B4897979 : Blo 1672036 4897979 := bstep (se 1 (by rfl) ⟨3673484, by rfl⟩ : syracuseStep 4897979 = 7346969) B7346969
theorem B5643647 : Blo 1672036 5643647 := bstep (se 1 (by rfl) ⟨4232735, by rfl⟩ : syracuseStep 5643647 = 8465471) B8465471
theorem B2678503 : Blo 1672036 2678503 := bstep (se 1 (by rfl) ⟨2008877, by rfl⟩ : syracuseStep 2678503 = 4017755) B4017755
theorem B4235561 : Blo 1672036 4235561 := bstep (se 2 (by rfl) ⟨1588335, by rfl⟩ : syracuseStep 4235561 = 3176671) B3176671
theorem B5645051 : Blo 1672036 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B1672159 : Blo 1672036 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B6350183 : Blo 1672036 6350183 := bstep (se 1 (by rfl) ⟨4762637, by rfl⟩ : syracuseStep 6350183 = 9525275) B9525275
theorem B1672639 : Blo 1672036 1672639 := bstep (se 1 (by rfl) ⟨1254479, by rfl⟩ : syracuseStep 1672639 = 2508959) B2508959
theorem B2508335 : Blo 1672036 2508335 := bstep (se 1 (by rfl) ⟨1881251, by rfl⟩ : syracuseStep 2508335 = 3762503) B3762503
theorem B1672831 : Blo 1672036 1672831 := bstep (se 1 (by rfl) ⟨1254623, by rfl⟩ : syracuseStep 1672831 = 2509247) B2509247
theorem B1673063 : Blo 1672036 1673063 := bstep (se 1 (by rfl) ⟨1254797, by rfl⟩ : syracuseStep 1673063 = 2509595) B2509595
theorem B1673455 : Blo 1672036 1673455 := bstep (se 1 (by rfl) ⟨1255091, by rfl⟩ : syracuseStep 1673455 = 2510183) B2510183
theorem B3762431 : Blo 1672036 3762431 := bstep (se 1 (by rfl) ⟨2821823, by rfl⟩ : syracuseStep 3762431 = 5643647) B5643647
theorem B1673695 : Blo 1672036 1673695 := bstep (se 1 (by rfl) ⟨1255271, by rfl⟩ : syracuseStep 1673695 = 2510543) B2510543
theorem B3763295 : Blo 1672036 3763295 := bstep (se 1 (by rfl) ⟨2822471, by rfl⟩ : syracuseStep 3763295 = 5644943) B5644943
theorem B6877007 : Blo 1672036 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B3764969 : Blo 1672036 3764969 := bstep (se 2 (by rfl) ⟨1411863, by rfl⟩ : syracuseStep 3764969 = 2823727) B2823727
theorem B32600825 : Blo 1672036 32600825 := bstep (se 2 (by rfl) ⟨12225309, by rfl⟩ : syracuseStep 32600825 = 24450619) B24450619
theorem B3265319 : Blo 1672036 3265319 := bstep (se 1 (by rfl) ⟨2448989, by rfl⟩ : syracuseStep 3265319 = 4897979) B4897979
theorem B48247649 : Blo 1672036 48247649 := bstep (se 2 (by rfl) ⟨18092868, by rfl⟩ : syracuseStep 48247649 = 36185737) B36185737
theorem B1881391 : Blo 1672036 1881391 := bstep (se 1 (by rfl) ⟨1411043, by rfl⟩ : syracuseStep 1881391 = 2822087) B2822087
theorem B8042237 : Blo 1672036 8042237 := bstep (se 3 (by rfl) ⟨1507919, by rfl⟩ : syracuseStep 8042237 = 3015839) B3015839
theorem B4766863 : Blo 1672036 4766863 := bstep (se 1 (by rfl) ⟨3575147, by rfl⟩ : syracuseStep 4766863 = 7150295) B7150295
theorem B5643431 : Blo 1672036 5643431 := bstep (se 1 (by rfl) ⟨4232573, by rfl⟩ : syracuseStep 5643431 = 8465147) B8465147
theorem B3571337 : Blo 1672036 3571337 := bstep (se 2 (by rfl) ⟨1339251, by rfl⟩ : syracuseStep 3571337 = 2678503) B2678503
theorem B21733883 : Blo 1672036 21733883 := bstep (se 1 (by rfl) ⟨16300412, by rfl⟩ : syracuseStep 21733883 = 32600825) B32600825
theorem B1672223 : Blo 1672036 1672223 := bstep (se 1 (by rfl) ⟨1254167, by rfl⟩ : syracuseStep 1672223 = 2508335) B2508335
theorem B2508287 : Blo 1672036 2508287 := bstep (se 1 (by rfl) ⟨1881215, by rfl⟩ : syracuseStep 2508287 = 3762431) B3762431
theorem B2508521 : Blo 1672036 2508521 := bstep (se 2 (by rfl) ⟨940695, by rfl⟩ : syracuseStep 2508521 = 1881391) B1881391
theorem B2508863 : Blo 1672036 2508863 := bstep (se 1 (by rfl) ⟨1881647, by rfl⟩ : syracuseStep 2508863 = 3763295) B3763295
theorem B3762287 : Blo 1672036 3762287 := bstep (se 1 (by rfl) ⟨2821715, by rfl⟩ : syracuseStep 3762287 = 5643431) B5643431
theorem B2509979 : Blo 1672036 2509979 := bstep (se 1 (by rfl) ⟨1882484, by rfl⟩ : syracuseStep 2509979 = 3764969) B3764969
theorem B3763367 : Blo 1672036 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B32165099 : Blo 1672036 32165099 := bstep (se 1 (by rfl) ⟨24123824, by rfl⟩ : syracuseStep 32165099 = 48247649) B48247649
theorem B5361491 : Blo 1672036 5361491 := bstep (se 1 (by rfl) ⟨4021118, by rfl⟩ : syracuseStep 5361491 = 8042237) B8042237
theorem B9523565 : Blo 1672036 9523565 := bstep (se 3 (by rfl) ⟨1785668, by rfl⟩ : syracuseStep 9523565 = 3571337) B3571337
theorem B4584671 : Blo 1672036 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B2823707 : Blo 1672036 2823707 := bstep (se 1 (by rfl) ⟨2117780, by rfl⟩ : syracuseStep 2823707 = 4235561) B4235561
theorem B2176879 : Blo 1672036 2176879 := bstep (se 1 (by rfl) ⟨1632659, by rfl⟩ : syracuseStep 2176879 = 3265319) B3265319
theorem B4233455 : Blo 1672036 4233455 := bstep (se 1 (by rfl) ⟨3175091, by rfl⟩ : syracuseStep 4233455 = 6350183) B6350183
theorem B6355817 : Blo 1672036 6355817 := bstep (se 2 (by rfl) ⟨2383431, by rfl⟩ : syracuseStep 6355817 = 4766863) B4766863
theorem B6349043 : Blo 1672036 6349043 := bstep (se 1 (by rfl) ⟨4761782, by rfl⟩ : syracuseStep 6349043 = 9523565) B9523565
theorem B3056447 : Blo 1672036 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B1672191 : Blo 1672036 1672191 := bstep (se 1 (by rfl) ⟨1254143, by rfl⟩ : syracuseStep 1672191 = 2508287) B2508287
theorem B1672347 : Blo 1672036 1672347 := bstep (se 1 (by rfl) ⟨1254260, by rfl⟩ : syracuseStep 1672347 = 2508521) B2508521
theorem B1672575 : Blo 1672036 1672575 := bstep (se 1 (by rfl) ⟨1254431, by rfl⟩ : syracuseStep 1672575 = 2508863) B2508863
theorem B2508191 : Blo 1672036 2508191 := bstep (se 1 (by rfl) ⟨1881143, by rfl⟩ : syracuseStep 2508191 = 3762287) B3762287
theorem B4237211 : Blo 1672036 4237211 := bstep (se 1 (by rfl) ⟨3177908, by rfl⟩ : syracuseStep 4237211 = 6355817) B6355817
theorem B1673319 : Blo 1672036 1673319 := bstep (se 1 (by rfl) ⟨1254989, by rfl⟩ : syracuseStep 1673319 = 2509979) B2509979
theorem B2508911 : Blo 1672036 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B14297309 : Blo 1672036 14297309 := bstep (se 3 (by rfl) ⟨2680745, by rfl⟩ : syracuseStep 14297309 = 5361491) B5361491
theorem B2902505 : Blo 1672036 2902505 := bstep (se 2 (by rfl) ⟨1088439, by rfl⟩ : syracuseStep 2902505 = 2176879) B2176879
theorem B2822303 : Blo 1672036 2822303 := bstep (se 1 (by rfl) ⟨2116727, by rfl⟩ : syracuseStep 2822303 = 4233455) B4233455
theorem B21443399 : Blo 1672036 21443399 := bstep (se 1 (by rfl) ⟨16082549, by rfl⟩ : syracuseStep 21443399 = 32165099) B32165099
theorem B14489255 : Blo 1672036 14489255 := bstep (se 1 (by rfl) ⟨10866941, by rfl⟩ : syracuseStep 14489255 = 21733883) B21733883
theorem B1882471 : Blo 1672036 1882471 := bstep (se 1 (by rfl) ⟨1411853, by rfl⟩ : syracuseStep 1882471 = 2823707) B2823707
theorem B14295599 : Blo 1672036 14295599 := bstep (se 1 (by rfl) ⟨10721699, by rfl⟩ : syracuseStep 14295599 = 21443399) B21443399
theorem B1672127 : Blo 1672036 1672127 := bstep (se 1 (by rfl) ⟨1254095, by rfl⟩ : syracuseStep 1672127 = 2508191) B2508191
theorem B9659503 : Blo 1672036 9659503 := bstep (se 1 (by rfl) ⟨7244627, by rfl⟩ : syracuseStep 9659503 = 14489255) B14489255
theorem B1672607 : Blo 1672036 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B30960053 : Blo 1672036 30960053 := bstep (se 5 (by rfl) ⟨1451252, by rfl⟩ : syracuseStep 30960053 = 2902505) B2902505
theorem B2509961 : Blo 1672036 2509961 := bstep (se 2 (by rfl) ⟨941235, by rfl⟩ : syracuseStep 2509961 = 1882471) B1882471
theorem B9531539 : Blo 1672036 9531539 := bstep (se 1 (by rfl) ⟨7148654, by rfl⟩ : syracuseStep 9531539 = 14297309) B14297309
theorem B1881535 : Blo 1672036 1881535 := bstep (se 1 (by rfl) ⟨1411151, by rfl⟩ : syracuseStep 1881535 = 2822303) B2822303
theorem B4232695 : Blo 1672036 4232695 := bstep (se 1 (by rfl) ⟨3174521, by rfl⟩ : syracuseStep 4232695 = 6349043) B6349043
theorem B2037631 : Blo 1672036 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B2824807 : Blo 1672036 2824807 := bstep (se 1 (by rfl) ⟨2118605, by rfl⟩ : syracuseStep 2824807 = 4237211) B4237211
theorem B12879337 : Blo 1672036 12879337 := bstep (se 2 (by rfl) ⟨4829751, by rfl⟩ : syracuseStep 12879337 = 9659503) B9659503
theorem B2508713 : Blo 1672036 2508713 := bstep (se 2 (by rfl) ⟨940767, by rfl⟩ : syracuseStep 2508713 = 1881535) B1881535
theorem B1673307 : Blo 1672036 1673307 := bstep (se 1 (by rfl) ⟨1254980, by rfl⟩ : syracuseStep 1673307 = 2509961) B2509961
theorem B9530399 : Blo 1672036 9530399 := bstep (se 1 (by rfl) ⟨7147799, by rfl⟩ : syracuseStep 9530399 = 14295599) B14295599
theorem B20640035 : Blo 1672036 20640035 := bstep (se 1 (by rfl) ⟨15480026, by rfl⟩ : syracuseStep 20640035 = 30960053) B30960053
theorem B2716841 : Blo 1672036 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B6354359 : Blo 1672036 6354359 := bstep (se 1 (by rfl) ⟨4765769, by rfl⟩ : syracuseStep 6354359 = 9531539) B9531539
theorem B3766409 : Blo 1672036 3766409 := bstep (se 2 (by rfl) ⟨1412403, by rfl⟩ : syracuseStep 3766409 = 2824807) B2824807
theorem B5643593 : Blo 1672036 5643593 := bstep (se 2 (by rfl) ⟨2116347, by rfl⟩ : syracuseStep 5643593 = 4232695) B4232695
theorem B4236239 : Blo 1672036 4236239 := bstep (se 1 (by rfl) ⟨3177179, by rfl⟩ : syracuseStep 4236239 = 6354359) B6354359
theorem B1672475 : Blo 1672036 1672475 := bstep (se 1 (by rfl) ⟨1254356, by rfl⟩ : syracuseStep 1672475 = 2508713) B2508713
theorem B17172449 : Blo 1672036 17172449 := bstep (se 2 (by rfl) ⟨6439668, by rfl⟩ : syracuseStep 17172449 = 12879337) B12879337
theorem B3762395 : Blo 1672036 3762395 := bstep (se 1 (by rfl) ⟨2821796, by rfl⟩ : syracuseStep 3762395 = 5643593) B5643593
theorem B7244909 : Blo 1672036 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B2510939 : Blo 1672036 2510939 := bstep (se 1 (by rfl) ⟨1883204, by rfl⟩ : syracuseStep 2510939 = 3766409) B3766409
theorem B6353599 : Blo 1672036 6353599 := bstep (se 1 (by rfl) ⟨4765199, by rfl⟩ : syracuseStep 6353599 = 9530399) B9530399
theorem B55040093 : Blo 1672036 55040093 := bstep (se 3 (by rfl) ⟨10320017, by rfl⟩ : syracuseStep 55040093 = 20640035) B20640035
theorem B8471465 : Blo 1672036 8471465 := bstep (se 2 (by rfl) ⟨3176799, by rfl⟩ : syracuseStep 8471465 = 6353599) B6353599
theorem B36693395 : Blo 1672036 36693395 := bstep (se 1 (by rfl) ⟨27520046, by rfl⟩ : syracuseStep 36693395 = 55040093) B55040093
theorem B2508263 : Blo 1672036 2508263 := bstep (se 1 (by rfl) ⟨1881197, by rfl⟩ : syracuseStep 2508263 = 3762395) B3762395
theorem B1673959 : Blo 1672036 1673959 := bstep (se 1 (by rfl) ⟨1255469, by rfl⟩ : syracuseStep 1673959 = 2510939) B2510939
theorem B11448299 : Blo 1672036 11448299 := bstep (se 1 (by rfl) ⟨8586224, by rfl⟩ : syracuseStep 11448299 = 17172449) B17172449
theorem B4829939 : Blo 1672036 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B2824159 : Blo 1672036 2824159 := bstep (se 1 (by rfl) ⟨2118119, by rfl⟩ : syracuseStep 2824159 = 4236239) B4236239
theorem B3219959 : Blo 1672036 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B24462263 : Blo 1672036 24462263 := bstep (se 1 (by rfl) ⟨18346697, by rfl⟩ : syracuseStep 24462263 = 36693395) B36693395
theorem B1672175 : Blo 1672036 1672175 := bstep (se 1 (by rfl) ⟨1254131, by rfl⟩ : syracuseStep 1672175 = 2508263) B2508263
theorem B5647643 : Blo 1672036 5647643 := bstep (se 1 (by rfl) ⟨4235732, by rfl⟩ : syracuseStep 5647643 = 8471465) B8471465
theorem B3765545 : Blo 1672036 3765545 := bstep (se 2 (by rfl) ⟨1412079, by rfl⟩ : syracuseStep 3765545 = 2824159) B2824159
theorem B7632199 : Blo 1672036 7632199 := bstep (se 1 (by rfl) ⟨5724149, by rfl⟩ : syracuseStep 7632199 = 11448299) B11448299
theorem B2146639 : Blo 1672036 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B10176265 : Blo 1672036 10176265 := bstep (se 2 (by rfl) ⟨3816099, by rfl⟩ : syracuseStep 10176265 = 7632199) B7632199
theorem B2510363 : Blo 1672036 2510363 := bstep (se 1 (by rfl) ⟨1882772, by rfl⟩ : syracuseStep 2510363 = 3765545) B3765545
theorem B3765095 : Blo 1672036 3765095 := bstep (se 1 (by rfl) ⟨2823821, by rfl⟩ : syracuseStep 3765095 = 5647643) B5647643
theorem B16308175 : Blo 1672036 16308175 := bstep (se 1 (by rfl) ⟨12231131, by rfl⟩ : syracuseStep 16308175 = 24462263) B24462263
theorem B13568353 : Blo 1672036 13568353 := bstep (se 2 (by rfl) ⟨5088132, by rfl⟩ : syracuseStep 13568353 = 10176265) B10176265
theorem B1673575 : Blo 1672036 1673575 := bstep (se 1 (by rfl) ⟨1255181, by rfl⟩ : syracuseStep 1673575 = 2510363) B2510363
theorem B21744233 : Blo 1672036 21744233 := bstep (se 2 (by rfl) ⟨8154087, by rfl⟩ : syracuseStep 21744233 = 16308175) B16308175
theorem B2862185 : Blo 1672036 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B2510063 : Blo 1672036 2510063 := bstep (se 1 (by rfl) ⟨1882547, by rfl⟩ : syracuseStep 2510063 = 3765095) B3765095
theorem B1673375 : Blo 1672036 1673375 := bstep (se 1 (by rfl) ⟨1255031, by rfl⟩ : syracuseStep 1673375 = 2510063) B2510063
theorem B14496155 : Blo 1672036 14496155 := bstep (se 1 (by rfl) ⟨10872116, by rfl⟩ : syracuseStep 14496155 = 21744233) B21744233
theorem B72364549 : Blo 1672036 72364549 := bstep (se 4 (by rfl) ⟨6784176, by rfl⟩ : syracuseStep 72364549 = 13568353) B13568353
theorem B30529973 : Blo 1672036 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B96486065 : Blo 1672036 96486065 := bstep (se 2 (by rfl) ⟨36182274, by rfl⟩ : syracuseStep 96486065 = 72364549) B72364549
theorem B20353315 : Blo 1672036 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B9664103 : Blo 1672036 9664103 := bstep (se 1 (by rfl) ⟨7248077, by rfl⟩ : syracuseStep 9664103 = 14496155) B14496155
theorem B64324043 : Blo 1672036 64324043 := bstep (se 1 (by rfl) ⟨48243032, by rfl⟩ : syracuseStep 64324043 = 96486065) B96486065
theorem B6442735 : Blo 1672036 6442735 := bstep (se 1 (by rfl) ⟨4832051, by rfl⟩ : syracuseStep 6442735 = 9664103) B9664103
theorem B27137753 : Blo 1672036 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B18091835 : Blo 1672036 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B8590313 : Blo 1672036 8590313 := bstep (se 2 (by rfl) ⟨3221367, by rfl⟩ : syracuseStep 8590313 = 6442735) B6442735
theorem B42882695 : Blo 1672036 42882695 := bstep (se 1 (by rfl) ⟨32162021, by rfl⟩ : syracuseStep 42882695 = 64324043) B64324043
theorem B5726875 : Blo 1672036 5726875 := bstep (se 1 (by rfl) ⟨4295156, by rfl⟩ : syracuseStep 5726875 = 8590313) B8590313
theorem B12061223 : Blo 1672036 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B28588463 : Blo 1672036 28588463 := bstep (se 1 (by rfl) ⟨21441347, by rfl⟩ : syracuseStep 28588463 = 42882695) B42882695
theorem B7635833 : Blo 1672036 7635833 := bstep (se 2 (by rfl) ⟨2863437, by rfl⟩ : syracuseStep 7635833 = 5726875) B5726875
theorem B19058975 : Blo 1672036 19058975 := bstep (se 1 (by rfl) ⟨14294231, by rfl⟩ : syracuseStep 19058975 = 28588463) B28588463
theorem B8040815 : Blo 1672036 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B12705983 : Blo 1672036 12705983 := bstep (se 1 (by rfl) ⟨9529487, by rfl⟩ : syracuseStep 12705983 = 19058975) B19058975
theorem B5360543 : Blo 1672036 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B5090555 : Blo 1672036 5090555 := bstep (se 1 (by rfl) ⟨3817916, by rfl⟩ : syracuseStep 5090555 = 7635833) B7635833
theorem B8470655 : Blo 1672036 8470655 := bstep (se 1 (by rfl) ⟨6352991, by rfl⟩ : syracuseStep 8470655 = 12705983) B12705983
theorem B3573695 : Blo 1672036 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B3393703 : Blo 1672036 3393703 := bstep (se 1 (by rfl) ⟨2545277, by rfl⟩ : syracuseStep 3393703 = 5090555) B5090555
theorem B5647103 : Blo 1672036 5647103 := bstep (se 1 (by rfl) ⟨4235327, by rfl⟩ : syracuseStep 5647103 = 8470655) B8470655
theorem B18099749 : Blo 1672036 18099749 := bstep (se 4 (by rfl) ⟨1696851, by rfl⟩ : syracuseStep 18099749 = 3393703) B3393703
theorem B2382463 : Blo 1672036 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B12706469 : Blo 1672036 12706469 := bstep (se 4 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 12706469 = 2382463) B2382463
theorem B3764735 : Blo 1672036 3764735 := bstep (se 1 (by rfl) ⟨2823551, by rfl⟩ : syracuseStep 3764735 = 5647103) B5647103
theorem B12066499 : Blo 1672036 12066499 := bstep (se 1 (by rfl) ⟨9049874, by rfl⟩ : syracuseStep 12066499 = 18099749) B18099749
theorem B8470979 : Blo 1672036 8470979 := bstep (se 1 (by rfl) ⟨6353234, by rfl⟩ : syracuseStep 8470979 = 12706469) B12706469
theorem B2509823 : Blo 1672036 2509823 := bstep (se 1 (by rfl) ⟨1882367, by rfl⟩ : syracuseStep 2509823 = 3764735) B3764735
theorem B16088665 : Blo 1672036 16088665 := bstep (se 2 (by rfl) ⟨6033249, by rfl⟩ : syracuseStep 16088665 = 12066499) B12066499
theorem B1673215 : Blo 1672036 1673215 := bstep (se 1 (by rfl) ⟨1254911, by rfl⟩ : syracuseStep 1673215 = 2509823) B2509823
theorem B5647319 : Blo 1672036 5647319 := bstep (se 1 (by rfl) ⟨4235489, by rfl⟩ : syracuseStep 5647319 = 8470979) B8470979
theorem B21451553 : Blo 1672036 21451553 := bstep (se 2 (by rfl) ⟨8044332, by rfl⟩ : syracuseStep 21451553 = 16088665) B16088665
theorem B3764879 : Blo 1672036 3764879 := bstep (se 1 (by rfl) ⟨2823659, by rfl⟩ : syracuseStep 3764879 = 5647319) B5647319
theorem B14301035 : Blo 1672036 14301035 := bstep (se 1 (by rfl) ⟨10725776, by rfl⟩ : syracuseStep 14301035 = 21451553) B21451553
theorem B2509919 : Blo 1672036 2509919 := bstep (se 1 (by rfl) ⟨1882439, by rfl⟩ : syracuseStep 2509919 = 3764879) B3764879
theorem B9534023 : Blo 1672036 9534023 := bstep (se 1 (by rfl) ⟨7150517, by rfl⟩ : syracuseStep 9534023 = 14301035) B14301035
theorem B1673279 : Blo 1672036 1673279 := bstep (se 1 (by rfl) ⟨1254959, by rfl⟩ : syracuseStep 1673279 = 2509919) B2509919
theorem B6356015 : Blo 1672036 6356015 := bstep (se 1 (by rfl) ⟨4767011, by rfl⟩ : syracuseStep 6356015 = 9534023) B9534023
theorem B4237343 : Blo 1672036 4237343 := bstep (se 1 (by rfl) ⟨3178007, by rfl⟩ : syracuseStep 4237343 = 6356015) B6356015
theorem B2824895 : Blo 1672036 2824895 := bstep (se 1 (by rfl) ⟨2118671, by rfl⟩ : syracuseStep 2824895 = 4237343) B4237343
theorem B1883263 : Blo 1672036 1883263 := bstep (se 1 (by rfl) ⟨1412447, by rfl⟩ : syracuseStep 1883263 = 2824895) B2824895
theorem B2511017 : Blo 1672036 2511017 := bstep (se 2 (by rfl) ⟨941631, by rfl⟩ : syracuseStep 2511017 = 1883263) B1883263
theorem B1674011 : Blo 1672036 1674011 := bstep (se 1 (by rfl) ⟨1255508, by rfl⟩ : syracuseStep 1674011 = 2511017) B2511017

theorem C0 (j : ℕ) (h1 : 418009 ≤ j) (h2 : j ≤ 418508) : Blo 1672036 (4 * j + 3) := by
  interval_cases j
  · exact B1672039
  · exact B1672043
  · exact B1672047
  · exact B1672051
  · exact B1672055
  · exact B1672059
  · exact B1672063
  · exact B1672067
  · exact B1672071
  · exact B1672075
  · exact B1672079
  · exact B1672083
  · exact B1672087
  · exact B1672091
  · exact B1672095
  · exact B1672099
  · exact B1672103
  · exact B1672107
  · exact B1672111
  · exact B1672115
  · exact B1672119
  · exact B1672123
  · exact B1672127
  · exact B1672131
  · exact B1672135
  · exact B1672139
  · exact B1672143
  · exact B1672147
  · exact B1672151
  · exact B1672155
  · exact B1672159
  · exact B1672163
  · exact B1672167
  · exact B1672171
  · exact B1672175
  · exact B1672179
  · exact B1672183
  · exact B1672187
  · exact B1672191
  · exact B1672195
  · exact B1672199
  · exact B1672203
  · exact B1672207
  · exact B1672211
  · exact B1672215
  · exact B1672219
  · exact B1672223
  · exact B1672227
  · exact B1672231
  · exact B1672235
  · exact B1672239
  · exact B1672243
  · exact B1672247
  · exact B1672251
  · exact B1672255
  · exact B1672259
  · exact B1672263
  · exact B1672267
  · exact B1672271
  · exact B1672275
  · exact B1672279
  · exact B1672283
  · exact B1672287
  · exact B1672291
  · exact B1672295
  · exact B1672299
  · exact B1672303
  · exact B1672307
  · exact B1672311
  · exact B1672315
  · exact B1672319
  · exact B1672323
  · exact B1672327
  · exact B1672331
  · exact B1672335
  · exact B1672339
  · exact B1672343
  · exact B1672347
  · exact B1672351
  · exact B1672355
  · exact B1672359
  · exact B1672363
  · exact B1672367
  · exact B1672371
  · exact B1672375
  · exact B1672379
  · exact B1672383
  · exact B1672387
  · exact B1672391
  · exact B1672395
  · exact B1672399
  · exact B1672403
  · exact B1672407
  · exact B1672411
  · exact B1672415
  · exact B1672419
  · exact B1672423
  · exact B1672427
  · exact B1672431
  · exact B1672435
  · exact B1672439
  · exact B1672443
  · exact B1672447
  · exact B1672451
  · exact B1672455
  · exact B1672459
  · exact B1672463
  · exact B1672467
  · exact B1672471
  · exact B1672475
  · exact B1672479
  · exact B1672483
  · exact B1672487
  · exact B1672491
  · exact B1672495
  · exact B1672499
  · exact B1672503
  · exact B1672507
  · exact B1672511
  · exact B1672515
  · exact B1672519
  · exact B1672523
  · exact B1672527
  · exact B1672531
  · exact B1672535
  · exact B1672539
  · exact B1672543
  · exact B1672547
  · exact B1672551
  · exact B1672555
  · exact B1672559
  · exact B1672563
  · exact B1672567
  · exact B1672571
  · exact B1672575
  · exact B1672579
  · exact B1672583
  · exact B1672587
  · exact B1672591
  · exact B1672595
  · exact B1672599
  · exact B1672603
  · exact B1672607
  · exact B1672611
  · exact B1672615
  · exact B1672619
  · exact B1672623
  · exact B1672627
  · exact B1672631
  · exact B1672635
  · exact B1672639
  · exact B1672643
  · exact B1672647
  · exact B1672651
  · exact B1672655
  · exact B1672659
  · exact B1672663
  · exact B1672667
  · exact B1672671
  · exact B1672675
  · exact B1672679
  · exact B1672683
  · exact B1672687
  · exact B1672691
  · exact B1672695
  · exact B1672699
  · exact B1672703
  · exact B1672707
  · exact B1672711
  · exact B1672715
  · exact B1672719
  · exact B1672723
  · exact B1672727
  · exact B1672731
  · exact B1672735
  · exact B1672739
  · exact B1672743
  · exact B1672747
  · exact B1672751
  · exact B1672755
  · exact B1672759
  · exact B1672763
  · exact B1672767
  · exact B1672771
  · exact B1672775
  · exact B1672779
  · exact B1672783
  · exact B1672787
  · exact B1672791
  · exact B1672795
  · exact B1672799
  · exact B1672803
  · exact B1672807
  · exact B1672811
  · exact B1672815
  · exact B1672819
  · exact B1672823
  · exact B1672827
  · exact B1672831
  · exact B1672835
  · exact B1672839
  · exact B1672843
  · exact B1672847
  · exact B1672851
  · exact B1672855
  · exact B1672859
  · exact B1672863
  · exact B1672867
  · exact B1672871
  · exact B1672875
  · exact B1672879
  · exact B1672883
  · exact B1672887
  · exact B1672891
  · exact B1672895
  · exact B1672899
  · exact B1672903
  · exact B1672907
  · exact B1672911
  · exact B1672915
  · exact B1672919
  · exact B1672923
  · exact B1672927
  · exact B1672931
  · exact B1672935
  · exact B1672939
  · exact B1672943
  · exact B1672947
  · exact B1672951
  · exact B1672955
  · exact B1672959
  · exact B1672963
  · exact B1672967
  · exact B1672971
  · exact B1672975
  · exact B1672979
  · exact B1672983
  · exact B1672987
  · exact B1672991
  · exact B1672995
  · exact B1672999
  · exact B1673003
  · exact B1673007
  · exact B1673011
  · exact B1673015
  · exact B1673019
  · exact B1673023
  · exact B1673027
  · exact B1673031
  · exact B1673035
  · exact B1673039
  · exact B1673043
  · exact B1673047
  · exact B1673051
  · exact B1673055
  · exact B1673059
  · exact B1673063
  · exact B1673067
  · exact B1673071
  · exact B1673075
  · exact B1673079
  · exact B1673083
  · exact B1673087
  · exact B1673091
  · exact B1673095
  · exact B1673099
  · exact B1673103
  · exact B1673107
  · exact B1673111
  · exact B1673115
  · exact B1673119
  · exact B1673123
  · exact B1673127
  · exact B1673131
  · exact B1673135
  · exact B1673139
  · exact B1673143
  · exact B1673147
  · exact B1673151
  · exact B1673155
  · exact B1673159
  · exact B1673163
  · exact B1673167
  · exact B1673171
  · exact B1673175
  · exact B1673179
  · exact B1673183
  · exact B1673187
  · exact B1673191
  · exact B1673195
  · exact B1673199
  · exact B1673203
  · exact B1673207
  · exact B1673211
  · exact B1673215
  · exact B1673219
  · exact B1673223
  · exact B1673227
  · exact B1673231
  · exact B1673235
  · exact B1673239
  · exact B1673243
  · exact B1673247
  · exact B1673251
  · exact B1673255
  · exact B1673259
  · exact B1673263
  · exact B1673267
  · exact B1673271
  · exact B1673275
  · exact B1673279
  · exact B1673283
  · exact B1673287
  · exact B1673291
  · exact B1673295
  · exact B1673299
  · exact B1673303
  · exact B1673307
  · exact B1673311
  · exact B1673315
  · exact B1673319
  · exact B1673323
  · exact B1673327
  · exact B1673331
  · exact B1673335
  · exact B1673339
  · exact B1673343
  · exact B1673347
  · exact B1673351
  · exact B1673355
  · exact B1673359
  · exact B1673363
  · exact B1673367
  · exact B1673371
  · exact B1673375
  · exact B1673379
  · exact B1673383
  · exact B1673387
  · exact B1673391
  · exact B1673395
  · exact B1673399
  · exact B1673403
  · exact B1673407
  · exact B1673411
  · exact B1673415
  · exact B1673419
  · exact B1673423
  · exact B1673427
  · exact B1673431
  · exact B1673435
  · exact B1673439
  · exact B1673443
  · exact B1673447
  · exact B1673451
  · exact B1673455
  · exact B1673459
  · exact B1673463
  · exact B1673467
  · exact B1673471
  · exact B1673475
  · exact B1673479
  · exact B1673483
  · exact B1673487
  · exact B1673491
  · exact B1673495
  · exact B1673499
  · exact B1673503
  · exact B1673507
  · exact B1673511
  · exact B1673515
  · exact B1673519
  · exact B1673523
  · exact B1673527
  · exact B1673531
  · exact B1673535
  · exact B1673539
  · exact B1673543
  · exact B1673547
  · exact B1673551
  · exact B1673555
  · exact B1673559
  · exact B1673563
  · exact B1673567
  · exact B1673571
  · exact B1673575
  · exact B1673579
  · exact B1673583
  · exact B1673587
  · exact B1673591
  · exact B1673595
  · exact B1673599
  · exact B1673603
  · exact B1673607
  · exact B1673611
  · exact B1673615
  · exact B1673619
  · exact B1673623
  · exact B1673627
  · exact B1673631
  · exact B1673635
  · exact B1673639
  · exact B1673643
  · exact B1673647
  · exact B1673651
  · exact B1673655
  · exact B1673659
  · exact B1673663
  · exact B1673667
  · exact B1673671
  · exact B1673675
  · exact B1673679
  · exact B1673683
  · exact B1673687
  · exact B1673691
  · exact B1673695
  · exact B1673699
  · exact B1673703
  · exact B1673707
  · exact B1673711
  · exact B1673715
  · exact B1673719
  · exact B1673723
  · exact B1673727
  · exact B1673731
  · exact B1673735
  · exact B1673739
  · exact B1673743
  · exact B1673747
  · exact B1673751
  · exact B1673755
  · exact B1673759
  · exact B1673763
  · exact B1673767
  · exact B1673771
  · exact B1673775
  · exact B1673779
  · exact B1673783
  · exact B1673787
  · exact B1673791
  · exact B1673795
  · exact B1673799
  · exact B1673803
  · exact B1673807
  · exact B1673811
  · exact B1673815
  · exact B1673819
  · exact B1673823
  · exact B1673827
  · exact B1673831
  · exact B1673835
  · exact B1673839
  · exact B1673843
  · exact B1673847
  · exact B1673851
  · exact B1673855
  · exact B1673859
  · exact B1673863
  · exact B1673867
  · exact B1673871
  · exact B1673875
  · exact B1673879
  · exact B1673883
  · exact B1673887
  · exact B1673891
  · exact B1673895
  · exact B1673899
  · exact B1673903
  · exact B1673907
  · exact B1673911
  · exact B1673915
  · exact B1673919
  · exact B1673923
  · exact B1673927
  · exact B1673931
  · exact B1673935
  · exact B1673939
  · exact B1673943
  · exact B1673947
  · exact B1673951
  · exact B1673955
  · exact B1673959
  · exact B1673963
  · exact B1673967
  · exact B1673971
  · exact B1673975
  · exact B1673979
  · exact B1673983
  · exact B1673987
  · exact B1673991
  · exact B1673995
  · exact B1673999
  · exact B1674003
  · exact B1674007
  · exact B1674011
  · exact B1674015
  · exact B1674019
  · exact B1674023
  · exact B1674027
  · exact B1674031
  · exact B1674035

theorem solution (m : ℕ) (hlo : 1672036 ≤ m) (hhi : m ≤ 1674036) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 418009 ≤ j := by omega
    have hj2 : j ≤ 418508 := by omega
    have hb : Blo 1672036 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
