-- Prove2me | solution 1 for syracuse_descends_range_742328_746328
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:13.916824+00:00
-- url     : https://prove2.me/submissions/1285ec0e-91bf-43f6-a752-38cecdeee355

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


theorem B1671173 : Blo 742328 1671173 := bbase (se 4 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 1671173 = 313345) (by norm_num)
theorem B753673 : Blo 742328 753673 := bbase (se 2 (by rfl) ⟨282627, by rfl⟩ : syracuseStep 753673 = 565255) (by norm_num)
theorem B1114133 : Blo 742328 1114133 := bbase (se 6 (by rfl) ⟨26112, by rfl⟩ : syracuseStep 1114133 = 52225) (by norm_num)
theorem B1114157 : Blo 742328 1114157 := bbase (se 3 (by rfl) ⟨208904, by rfl⟩ : syracuseStep 1114157 = 417809) (by norm_num)
theorem B1114181 : Blo 742328 1114181 := bbase (se 4 (by rfl) ⟨104454, by rfl⟩ : syracuseStep 1114181 = 208909) (by norm_num)
theorem B1671245 : Blo 742328 1671245 := bbase (se 3 (by rfl) ⟨313358, by rfl⟩ : syracuseStep 1671245 = 626717) (by norm_num)
theorem B1114205 : Blo 742328 1114205 := bbase (se 3 (by rfl) ⟨208913, by rfl⟩ : syracuseStep 1114205 = 417827) (by norm_num)
theorem B1114229 : Blo 742328 1114229 := bbase (se 5 (by rfl) ⟨52229, by rfl⟩ : syracuseStep 1114229 = 104459) (by norm_num)
theorem B1114253 : Blo 742328 1114253 := bbase (se 3 (by rfl) ⟨208922, by rfl⟩ : syracuseStep 1114253 = 417845) (by norm_num)
theorem B1671317 : Blo 742328 1671317 := bbase (se 6 (by rfl) ⟨39171, by rfl⟩ : syracuseStep 1671317 = 78343) (by norm_num)
theorem B1114277 : Blo 742328 1114277 := bbase (se 4 (by rfl) ⟨104463, by rfl⟩ : syracuseStep 1114277 = 208927) (by norm_num)
theorem B1114301 : Blo 742328 1114301 := bbase (se 3 (by rfl) ⟨208931, by rfl⟩ : syracuseStep 1114301 = 417863) (by norm_num)
theorem B1114325 : Blo 742328 1114325 := bbase (se 7 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 1114325 = 26117) (by norm_num)
theorem B1671389 : Blo 742328 1671389 := bbase (se 3 (by rfl) ⟨313385, by rfl⟩ : syracuseStep 1671389 = 626771) (by norm_num)
theorem B1114349 : Blo 742328 1114349 := bbase (se 3 (by rfl) ⟨208940, by rfl⟩ : syracuseStep 1114349 = 417881) (by norm_num)
theorem B1114373 : Blo 742328 1114373 := bbase (se 4 (by rfl) ⟨104472, by rfl⟩ : syracuseStep 1114373 = 208945) (by norm_num)
theorem B1409309 : Blo 742328 1409309 := bbase (se 3 (by rfl) ⟨264245, by rfl⟩ : syracuseStep 1409309 = 528491) (by norm_num)
theorem B1114397 : Blo 742328 1114397 := bbase (se 3 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 1114397 = 417899) (by norm_num)
theorem B1671461 : Blo 742328 1671461 := bbase (se 4 (by rfl) ⟨156699, by rfl⟩ : syracuseStep 1671461 = 313399) (by norm_num)
theorem B1507621 : Blo 742328 1507621 := bbase (se 4 (by rfl) ⟨141339, by rfl⟩ : syracuseStep 1507621 = 282679) (by norm_num)
theorem B1114421 : Blo 742328 1114421 := bbase (se 5 (by rfl) ⟨52238, by rfl⟩ : syracuseStep 1114421 = 104477) (by norm_num)
theorem B1114445 : Blo 742328 1114445 := bbase (se 3 (by rfl) ⟨208958, by rfl⟩ : syracuseStep 1114445 = 417917) (by norm_num)
theorem B1114469 : Blo 742328 1114469 := bbase (se 4 (by rfl) ⟨104481, by rfl⟩ : syracuseStep 1114469 = 208963) (by norm_num)
theorem B754021 : Blo 742328 754021 := bbase (se 4 (by rfl) ⟨70689, by rfl⟩ : syracuseStep 754021 = 141379) (by norm_num)
theorem B1671533 : Blo 742328 1671533 := bbase (se 3 (by rfl) ⟨313412, by rfl⟩ : syracuseStep 1671533 = 626825) (by norm_num)
theorem B1114493 : Blo 742328 1114493 := bbase (se 3 (by rfl) ⟨208967, by rfl⟩ : syracuseStep 1114493 = 417935) (by norm_num)
theorem B1114517 : Blo 742328 1114517 := bbase (se 6 (by rfl) ⟨26121, by rfl⟩ : syracuseStep 1114517 = 52243) (by norm_num)
theorem B1114541 : Blo 742328 1114541 := bbase (se 3 (by rfl) ⟨208976, by rfl⟩ : syracuseStep 1114541 = 417953) (by norm_num)
theorem B1671605 : Blo 742328 1671605 := bbase (se 5 (by rfl) ⟨78356, by rfl⟩ : syracuseStep 1671605 = 156713) (by norm_num)
theorem B1114565 : Blo 742328 1114565 := bbase (se 4 (by rfl) ⟨104490, by rfl⟩ : syracuseStep 1114565 = 208981) (by norm_num)
theorem B1343957 : Blo 742328 1343957 := bbase (se 7 (by rfl) ⟨15749, by rfl⟩ : syracuseStep 1343957 = 31499) (by norm_num)
theorem B1114589 : Blo 742328 1114589 := bbase (se 3 (by rfl) ⟨208985, by rfl⟩ : syracuseStep 1114589 = 417971) (by norm_num)
theorem B1114613 : Blo 742328 1114613 := bbase (se 5 (by rfl) ⟨52247, by rfl⟩ : syracuseStep 1114613 = 104495) (by norm_num)
theorem B1671677 : Blo 742328 1671677 := bbase (se 3 (by rfl) ⟨313439, by rfl⟩ : syracuseStep 1671677 = 626879) (by norm_num)
theorem B1114637 : Blo 742328 1114637 := bbase (se 3 (by rfl) ⟨208994, by rfl⟩ : syracuseStep 1114637 = 417989) (by norm_num)
theorem B1114661 : Blo 742328 1114661 := bbase (se 4 (by rfl) ⟨104499, by rfl⟩ : syracuseStep 1114661 = 208999) (by norm_num)
theorem B1114685 : Blo 742328 1114685 := bbase (se 3 (by rfl) ⟨209003, by rfl⟩ : syracuseStep 1114685 = 418007) (by norm_num)
theorem B1671749 : Blo 742328 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B1114709 : Blo 742328 1114709 := bbase (se 8 (by rfl) ⟨6531, by rfl⟩ : syracuseStep 1114709 = 13063) (by norm_num)
theorem B1114733 : Blo 742328 1114733 := bbase (se 3 (by rfl) ⟨209012, by rfl⟩ : syracuseStep 1114733 = 418025) (by norm_num)
theorem B1344109 : Blo 742328 1344109 := bbase (se 3 (by rfl) ⟨252020, by rfl⟩ : syracuseStep 1344109 = 504041) (by norm_num)
theorem B1114757 : Blo 742328 1114757 := bbase (se 4 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 1114757 = 209017) (by norm_num)
theorem B1671821 : Blo 742328 1671821 := bbase (se 3 (by rfl) ⟨313466, by rfl⟩ : syracuseStep 1671821 = 626933) (by norm_num)
theorem B2818709 : Blo 742328 2818709 := bbase (se 6 (by rfl) ⟨66063, by rfl⟩ : syracuseStep 2818709 = 132127) (by norm_num)
theorem B5374613 : Blo 742328 5374613 := bbase (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) (by norm_num)
theorem B1114781 : Blo 742328 1114781 := bbase (se 3 (by rfl) ⟨209021, by rfl⟩ : syracuseStep 1114781 = 418043) (by norm_num)
theorem B1114805 : Blo 742328 1114805 := bbase (se 5 (by rfl) ⟨52256, by rfl⟩ : syracuseStep 1114805 = 104513) (by norm_num)
theorem B1114829 : Blo 742328 1114829 := bbase (se 3 (by rfl) ⟨209030, by rfl⟩ : syracuseStep 1114829 = 418061) (by norm_num)
theorem B1671893 : Blo 742328 1671893 := bbase (se 7 (by rfl) ⟨19592, by rfl⟩ : syracuseStep 1671893 = 39185) (by norm_num)
theorem B1114853 : Blo 742328 1114853 := bbase (se 4 (by rfl) ⟨104517, by rfl⟩ : syracuseStep 1114853 = 209035) (by norm_num)
theorem B1114877 : Blo 742328 1114877 := bbase (se 3 (by rfl) ⟨209039, by rfl⟩ : syracuseStep 1114877 = 418079) (by norm_num)
theorem B1114901 : Blo 742328 1114901 := bbase (se 6 (by rfl) ⟨26130, by rfl⟩ : syracuseStep 1114901 = 52261) (by norm_num)
theorem B1671965 : Blo 742328 1671965 := bbase (se 3 (by rfl) ⟨313493, by rfl⟩ : syracuseStep 1671965 = 626987) (by norm_num)
theorem B1114925 : Blo 742328 1114925 := bbase (se 3 (by rfl) ⟨209048, by rfl⟩ : syracuseStep 1114925 = 418097) (by norm_num)
theorem B1114949 : Blo 742328 1114949 := bbase (se 4 (by rfl) ⟨104526, by rfl⟩ : syracuseStep 1114949 = 209053) (by norm_num)
theorem B1114973 : Blo 742328 1114973 := bbase (se 3 (by rfl) ⟨209057, by rfl⟩ : syracuseStep 1114973 = 418115) (by norm_num)
theorem B1672037 : Blo 742328 1672037 := bbase (se 4 (by rfl) ⟨156753, by rfl⟩ : syracuseStep 1672037 = 313507) (by norm_num)
theorem B1114997 : Blo 742328 1114997 := bbase (se 5 (by rfl) ⟨52265, by rfl⟩ : syracuseStep 1114997 = 104531) (by norm_num)
theorem B1115021 : Blo 742328 1115021 := bbase (se 3 (by rfl) ⟨209066, by rfl⟩ : syracuseStep 1115021 = 418133) (by norm_num)
theorem B1115045 : Blo 742328 1115045 := bbase (se 4 (by rfl) ⟨104535, by rfl⟩ : syracuseStep 1115045 = 209071) (by norm_num)
theorem B3769253 : Blo 742328 3769253 := bbase (se 4 (by rfl) ⟨353367, by rfl⟩ : syracuseStep 3769253 = 706735) (by norm_num)
theorem B1672109 : Blo 742328 1672109 := bbase (se 3 (by rfl) ⟨313520, by rfl⟩ : syracuseStep 1672109 = 627041) (by norm_num)
theorem B1115069 : Blo 742328 1115069 := bbase (se 3 (by rfl) ⟨209075, by rfl⟩ : syracuseStep 1115069 = 418151) (by norm_num)
theorem B1115093 : Blo 742328 1115093 := bbase (se 7 (by rfl) ⟨13067, by rfl⟩ : syracuseStep 1115093 = 26135) (by norm_num)
theorem B1115117 : Blo 742328 1115117 := bbase (se 3 (by rfl) ⟨209084, by rfl⟩ : syracuseStep 1115117 = 418169) (by norm_num)
theorem B1672181 : Blo 742328 1672181 := bbase (se 5 (by rfl) ⟨78383, by rfl⟩ : syracuseStep 1672181 = 156767) (by norm_num)
theorem B1115141 : Blo 742328 1115141 := bbase (se 4 (by rfl) ⟨104544, by rfl⟩ : syracuseStep 1115141 = 209089) (by norm_num)
theorem B1410061 : Blo 742328 1410061 := bbase (se 3 (by rfl) ⟨264386, by rfl⟩ : syracuseStep 1410061 = 528773) (by norm_num)
theorem B1115165 : Blo 742328 1115165 := bbase (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) (by norm_num)
theorem B1115189 : Blo 742328 1115189 := bbase (se 5 (by rfl) ⟨52274, by rfl⟩ : syracuseStep 1115189 = 104549) (by norm_num)
theorem B1672253 : Blo 742328 1672253 := bbase (se 3 (by rfl) ⟨313547, by rfl⟩ : syracuseStep 1672253 = 627095) (by norm_num)
theorem B1115213 : Blo 742328 1115213 := bbase (se 3 (by rfl) ⟨209102, by rfl⟩ : syracuseStep 1115213 = 418205) (by norm_num)
theorem B1115237 : Blo 742328 1115237 := bbase (se 4 (by rfl) ⟨104553, by rfl⟩ : syracuseStep 1115237 = 209107) (by norm_num)
theorem B1115261 : Blo 742328 1115261 := bbase (se 3 (by rfl) ⟨209111, by rfl⟩ : syracuseStep 1115261 = 418223) (by norm_num)
theorem B1672325 : Blo 742328 1672325 := bbase (se 4 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 1672325 = 313561) (by norm_num)
theorem B1115285 : Blo 742328 1115285 := bbase (se 6 (by rfl) ⟨26139, by rfl⟩ : syracuseStep 1115285 = 52279) (by norm_num)
theorem B1410205 : Blo 742328 1410205 := bbase (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) (by norm_num)
theorem B1115309 : Blo 742328 1115309 := bbase (se 3 (by rfl) ⟨209120, by rfl⟩ : syracuseStep 1115309 = 418241) (by norm_num)
theorem B1115333 : Blo 742328 1115333 := bbase (se 4 (by rfl) ⟨104562, by rfl⟩ : syracuseStep 1115333 = 209125) (by norm_num)
theorem B1672397 : Blo 742328 1672397 := bbase (se 3 (by rfl) ⟨313574, by rfl⟩ : syracuseStep 1672397 = 627149) (by norm_num)
theorem B1115357 : Blo 742328 1115357 := bbase (se 3 (by rfl) ⟨209129, by rfl⟩ : syracuseStep 1115357 = 418259) (by norm_num)
theorem B1115381 : Blo 742328 1115381 := bbase (se 5 (by rfl) ⟨52283, by rfl⟩ : syracuseStep 1115381 = 104567) (by norm_num)
theorem B1115405 : Blo 742328 1115405 := bbase (se 3 (by rfl) ⟨209138, by rfl⟩ : syracuseStep 1115405 = 418277) (by norm_num)
theorem B1672469 : Blo 742328 1672469 := bbase (se 6 (by rfl) ⟨39198, by rfl⟩ : syracuseStep 1672469 = 78397) (by norm_num)
theorem B1115429 : Blo 742328 1115429 := bbase (se 4 (by rfl) ⟨104571, by rfl⟩ : syracuseStep 1115429 = 209143) (by norm_num)
theorem B1410365 : Blo 742328 1410365 := bbase (se 3 (by rfl) ⟨264443, by rfl⟩ : syracuseStep 1410365 = 528887) (by norm_num)
theorem B1115453 : Blo 742328 1115453 := bbase (se 3 (by rfl) ⟨209147, by rfl⟩ : syracuseStep 1115453 = 418295) (by norm_num)
theorem B1115477 : Blo 742328 1115477 := bbase (se 12 (by rfl) ⟨408, by rfl⟩ : syracuseStep 1115477 = 817) (by norm_num)
theorem B1672541 : Blo 742328 1672541 := bbase (se 3 (by rfl) ⟨313601, by rfl⟩ : syracuseStep 1672541 = 627203) (by norm_num)
theorem B1115501 : Blo 742328 1115501 := bbase (se 3 (by rfl) ⟨209156, by rfl⟩ : syracuseStep 1115501 = 418313) (by norm_num)
theorem B1115525 : Blo 742328 1115525 := bbase (se 4 (by rfl) ⟨104580, by rfl⟩ : syracuseStep 1115525 = 209161) (by norm_num)
theorem B1115549 : Blo 742328 1115549 := bbase (se 3 (by rfl) ⟨209165, by rfl⟩ : syracuseStep 1115549 = 418331) (by norm_num)
theorem B1672613 : Blo 742328 1672613 := bbase (se 4 (by rfl) ⟨156807, by rfl⟩ : syracuseStep 1672613 = 313615) (by norm_num)
theorem B1115573 : Blo 742328 1115573 := bbase (se 5 (by rfl) ⟨52292, by rfl⟩ : syracuseStep 1115573 = 104585) (by norm_num)
theorem B1410509 : Blo 742328 1410509 := bbase (se 3 (by rfl) ⟨264470, by rfl⟩ : syracuseStep 1410509 = 528941) (by norm_num)
theorem B1115597 : Blo 742328 1115597 := bbase (se 3 (by rfl) ⟨209174, by rfl⟩ : syracuseStep 1115597 = 418349) (by norm_num)
theorem B1115621 : Blo 742328 1115621 := bbase (se 4 (by rfl) ⟨104589, by rfl⟩ : syracuseStep 1115621 = 209179) (by norm_num)
theorem B755173 : Blo 742328 755173 := bbase (se 4 (by rfl) ⟨70797, by rfl⟩ : syracuseStep 755173 = 141595) (by norm_num)
theorem B1672685 : Blo 742328 1672685 := bbase (se 3 (by rfl) ⟨313628, by rfl⟩ : syracuseStep 1672685 = 627257) (by norm_num)
theorem B1115645 : Blo 742328 1115645 := bbase (se 3 (by rfl) ⟨209183, by rfl⟩ : syracuseStep 1115645 = 418367) (by norm_num)
theorem B1115669 : Blo 742328 1115669 := bbase (se 6 (by rfl) ⟨26148, by rfl⟩ : syracuseStep 1115669 = 52297) (by norm_num)
theorem B1115693 : Blo 742328 1115693 := bbase (se 3 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 1115693 = 418385) (by norm_num)
theorem B1672757 : Blo 742328 1672757 := bbase (se 5 (by rfl) ⟨78410, by rfl⟩ : syracuseStep 1672757 = 156821) (by norm_num)
theorem B1115717 : Blo 742328 1115717 := bbase (se 4 (by rfl) ⟨104598, by rfl⟩ : syracuseStep 1115717 = 209197) (by norm_num)
theorem B1115741 : Blo 742328 1115741 := bbase (se 3 (by rfl) ⟨209201, by rfl⟩ : syracuseStep 1115741 = 418403) (by norm_num)
theorem B1115765 : Blo 742328 1115765 := bbase (se 5 (by rfl) ⟨52301, by rfl⟩ : syracuseStep 1115765 = 104603) (by norm_num)
theorem B1672829 : Blo 742328 1672829 := bbase (se 3 (by rfl) ⟨313655, by rfl⟩ : syracuseStep 1672829 = 627311) (by norm_num)
theorem B1115789 : Blo 742328 1115789 := bbase (se 3 (by rfl) ⟨209210, by rfl⟩ : syracuseStep 1115789 = 418421) (by norm_num)
theorem B1115813 : Blo 742328 1115813 := bbase (se 4 (by rfl) ⟨104607, by rfl⟩ : syracuseStep 1115813 = 209215) (by norm_num)
theorem B1115837 : Blo 742328 1115837 := bbase (se 3 (by rfl) ⟨209219, by rfl⟩ : syracuseStep 1115837 = 418439) (by norm_num)
theorem B1672901 : Blo 742328 1672901 := bbase (se 4 (by rfl) ⟨156834, by rfl⟩ : syracuseStep 1672901 = 313669) (by norm_num)
theorem B1115861 : Blo 742328 1115861 := bbase (se 7 (by rfl) ⟨13076, by rfl⟩ : syracuseStep 1115861 = 26153) (by norm_num)
theorem B1410797 : Blo 742328 1410797 := bbase (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) (by norm_num)
theorem B1115885 : Blo 742328 1115885 := bbase (se 3 (by rfl) ⟨209228, by rfl⟩ : syracuseStep 1115885 = 418457) (by norm_num)
theorem B1115909 : Blo 742328 1115909 := bbase (se 4 (by rfl) ⟨104616, by rfl⟩ : syracuseStep 1115909 = 209233) (by norm_num)
theorem B3180293 : Blo 742328 3180293 := bbase (se 4 (by rfl) ⟨298152, by rfl⟩ : syracuseStep 3180293 = 596305) (by norm_num)
theorem B1672973 : Blo 742328 1672973 := bbase (se 3 (by rfl) ⟨313682, by rfl⟩ : syracuseStep 1672973 = 627365) (by norm_num)
theorem B1115933 : Blo 742328 1115933 := bbase (se 3 (by rfl) ⟨209237, by rfl⟩ : syracuseStep 1115933 = 418475) (by norm_num)
theorem B755489 : Blo 742328 755489 := bbase (se 2 (by rfl) ⟨283308, by rfl⟩ : syracuseStep 755489 = 566617) (by norm_num)
theorem B2819893 : Blo 742328 2819893 := bbase (se 5 (by rfl) ⟨132182, by rfl⟩ : syracuseStep 2819893 = 264365) (by norm_num)
theorem B1115957 : Blo 742328 1115957 := bbase (se 5 (by rfl) ⟨52310, by rfl⟩ : syracuseStep 1115957 = 104621) (by norm_num)
theorem B1115981 : Blo 742328 1115981 := bbase (se 3 (by rfl) ⟨209246, by rfl⟩ : syracuseStep 1115981 = 418493) (by norm_num)
theorem B1673045 : Blo 742328 1673045 := bbase (se 9 (by rfl) ⟨4901, by rfl⟩ : syracuseStep 1673045 = 9803) (by norm_num)
theorem B1509205 : Blo 742328 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B1116005 : Blo 742328 1116005 := bbase (se 4 (by rfl) ⟨104625, by rfl⟩ : syracuseStep 1116005 = 209251) (by norm_num)
theorem B1116029 : Blo 742328 1116029 := bbase (se 3 (by rfl) ⟨209255, by rfl⟩ : syracuseStep 1116029 = 418511) (by norm_num)
theorem B1410949 : Blo 742328 1410949 := bbase (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) (by norm_num)
theorem B1116053 : Blo 742328 1116053 := bbase (se 6 (by rfl) ⟨26157, by rfl⟩ : syracuseStep 1116053 = 52315) (by norm_num)
theorem B1673117 : Blo 742328 1673117 := bbase (se 3 (by rfl) ⟨313709, by rfl⟩ : syracuseStep 1673117 = 627419) (by norm_num)
theorem B1116077 : Blo 742328 1116077 := bbase (se 3 (by rfl) ⟨209264, by rfl⟩ : syracuseStep 1116077 = 418529) (by norm_num)
theorem B1116101 : Blo 742328 1116101 := bbase (se 4 (by rfl) ⟨104634, by rfl⟩ : syracuseStep 1116101 = 209269) (by norm_num)
theorem B1116125 : Blo 742328 1116125 := bbase (se 3 (by rfl) ⟨209273, by rfl⟩ : syracuseStep 1116125 = 418547) (by norm_num)
theorem B1673189 : Blo 742328 1673189 := bbase (se 4 (by rfl) ⟨156861, by rfl⟩ : syracuseStep 1673189 = 313723) (by norm_num)
theorem B1116149 : Blo 742328 1116149 := bbase (se 5 (by rfl) ⟨52319, by rfl⟩ : syracuseStep 1116149 = 104639) (by norm_num)
theorem B1116173 : Blo 742328 1116173 := bbase (se 3 (by rfl) ⟨209282, by rfl⟩ : syracuseStep 1116173 = 418565) (by norm_num)
theorem B1116197 : Blo 742328 1116197 := bbase (se 4 (by rfl) ⟨104643, by rfl⟩ : syracuseStep 1116197 = 209287) (by norm_num)
theorem B1673261 : Blo 742328 1673261 := bbase (se 3 (by rfl) ⟨313736, by rfl⟩ : syracuseStep 1673261 = 627473) (by norm_num)
theorem B1116221 : Blo 742328 1116221 := bbase (se 3 (by rfl) ⟨209291, by rfl⟩ : syracuseStep 1116221 = 418583) (by norm_num)
theorem B1116245 : Blo 742328 1116245 := bbase (se 8 (by rfl) ⟨6540, by rfl⟩ : syracuseStep 1116245 = 13081) (by norm_num)
theorem B2820197 : Blo 742328 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B1116269 : Blo 742328 1116269 := bbase (se 3 (by rfl) ⟨209300, by rfl⟩ : syracuseStep 1116269 = 418601) (by norm_num)
theorem B1673333 : Blo 742328 1673333 := bbase (se 5 (by rfl) ⟨78437, by rfl⟩ : syracuseStep 1673333 = 156875) (by norm_num)
theorem B1116293 : Blo 742328 1116293 := bbase (se 4 (by rfl) ⟨104652, by rfl⟩ : syracuseStep 1116293 = 209305) (by norm_num)
theorem B1116317 : Blo 742328 1116317 := bbase (se 3 (by rfl) ⟨209309, by rfl⟩ : syracuseStep 1116317 = 418619) (by norm_num)
theorem B1411253 : Blo 742328 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B1116341 : Blo 742328 1116341 := bbase (se 5 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 1116341 = 104657) (by norm_num)
theorem B3770549 : Blo 742328 3770549 := bbase (se 5 (by rfl) ⟨176744, by rfl⟩ : syracuseStep 3770549 = 353489) (by norm_num)
theorem B1673405 : Blo 742328 1673405 := bbase (se 3 (by rfl) ⟨313763, by rfl⟩ : syracuseStep 1673405 = 627527) (by norm_num)
theorem B1116365 : Blo 742328 1116365 := bbase (se 3 (by rfl) ⟨209318, by rfl⟩ : syracuseStep 1116365 = 418637) (by norm_num)
theorem B9537749 : Blo 742328 9537749 := bbase (se 7 (by rfl) ⟨111770, by rfl⟩ : syracuseStep 9537749 = 223541) (by norm_num)
theorem B1116389 : Blo 742328 1116389 := bbase (se 4 (by rfl) ⟨104661, by rfl⟩ : syracuseStep 1116389 = 209323) (by norm_num)
theorem B1116413 : Blo 742328 1116413 := bbase (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) (by norm_num)
theorem B1673477 : Blo 742328 1673477 := bbase (se 4 (by rfl) ⟨156888, by rfl⟩ : syracuseStep 1673477 = 313777) (by norm_num)
theorem B1116437 : Blo 742328 1116437 := bbase (se 6 (by rfl) ⟨26166, by rfl⟩ : syracuseStep 1116437 = 52333) (by norm_num)
theorem B1116461 : Blo 742328 1116461 := bbase (se 3 (by rfl) ⟨209336, by rfl⟩ : syracuseStep 1116461 = 418673) (by norm_num)
theorem B1116485 : Blo 742328 1116485 := bbase (se 4 (by rfl) ⟨104670, by rfl⟩ : syracuseStep 1116485 = 209341) (by norm_num)
theorem B1673549 : Blo 742328 1673549 := bbase (se 3 (by rfl) ⟨313790, by rfl⟩ : syracuseStep 1673549 = 627581) (by norm_num)
theorem B1116509 : Blo 742328 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B756065 : Blo 742328 756065 := bbase (se 2 (by rfl) ⟨283524, by rfl⟩ : syracuseStep 756065 = 567049) (by norm_num)
theorem B1116533 : Blo 742328 1116533 := bbase (se 5 (by rfl) ⟨52337, by rfl⟩ : syracuseStep 1116533 = 104675) (by norm_num)
theorem B756097 : Blo 742328 756097 := bbase (se 2 (by rfl) ⟨283536, by rfl⟩ : syracuseStep 756097 = 567073) (by norm_num)
theorem B1116557 : Blo 742328 1116557 := bbase (se 3 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 1116557 = 418709) (by norm_num)
theorem B1673621 : Blo 742328 1673621 := bbase (se 6 (by rfl) ⟨39225, by rfl⟩ : syracuseStep 1673621 = 78451) (by norm_num)
theorem B1116581 : Blo 742328 1116581 := bbase (se 4 (by rfl) ⟨104679, by rfl⟩ : syracuseStep 1116581 = 209359) (by norm_num)
theorem B1116605 : Blo 742328 1116605 := bbase (se 3 (by rfl) ⟨209363, by rfl⟩ : syracuseStep 1116605 = 418727) (by norm_num)
theorem B1116629 : Blo 742328 1116629 := bbase (se 7 (by rfl) ⟨13085, by rfl⟩ : syracuseStep 1116629 = 26171) (by norm_num)
theorem B1673693 : Blo 742328 1673693 := bbase (se 3 (by rfl) ⟨313817, by rfl⟩ : syracuseStep 1673693 = 627635) (by norm_num)
theorem B3017189 : Blo 742328 3017189 := bbase (se 4 (by rfl) ⟨282861, by rfl⟩ : syracuseStep 3017189 = 565723) (by norm_num)
theorem B1116653 : Blo 742328 1116653 := bbase (se 3 (by rfl) ⟨209372, by rfl⟩ : syracuseStep 1116653 = 418745) (by norm_num)
theorem B1116677 : Blo 742328 1116677 := bbase (se 4 (by rfl) ⟨104688, by rfl⟩ : syracuseStep 1116677 = 209377) (by norm_num)
theorem B1116701 : Blo 742328 1116701 := bbase (se 3 (by rfl) ⟨209381, by rfl⟩ : syracuseStep 1116701 = 418763) (by norm_num)
theorem B1673765 : Blo 742328 1673765 := bbase (se 4 (by rfl) ⟨156915, by rfl⟩ : syracuseStep 1673765 = 313831) (by norm_num)
theorem B1116725 : Blo 742328 1116725 := bbase (se 5 (by rfl) ⟨52346, by rfl⟩ : syracuseStep 1116725 = 104693) (by norm_num)
theorem B2263621 : Blo 742328 2263621 := bbase (se 4 (by rfl) ⟨212214, by rfl⟩ : syracuseStep 2263621 = 424429) (by norm_num)
theorem B1116749 : Blo 742328 1116749 := bbase (se 3 (by rfl) ⟨209390, by rfl⟩ : syracuseStep 1116749 = 418781) (by norm_num)
theorem B1116773 : Blo 742328 1116773 := bbase (se 4 (by rfl) ⟨104697, by rfl⟩ : syracuseStep 1116773 = 209395) (by norm_num)
theorem B1673837 : Blo 742328 1673837 := bbase (se 3 (by rfl) ⟨313844, by rfl⟩ : syracuseStep 1673837 = 627689) (by norm_num)
theorem B1116797 : Blo 742328 1116797 := bbase (se 3 (by rfl) ⟨209399, by rfl⟩ : syracuseStep 1116797 = 418799) (by norm_num)
theorem B1116821 : Blo 742328 1116821 := bbase (se 6 (by rfl) ⟨26175, by rfl⟩ : syracuseStep 1116821 = 52351) (by norm_num)
theorem B1116845 : Blo 742328 1116845 := bbase (se 3 (by rfl) ⟨209408, by rfl⟩ : syracuseStep 1116845 = 418817) (by norm_num)
theorem B1673909 : Blo 742328 1673909 := bbase (se 5 (by rfl) ⟨78464, by rfl⟩ : syracuseStep 1673909 = 156929) (by norm_num)
theorem B1116869 : Blo 742328 1116869 := bbase (se 4 (by rfl) ⟨104706, by rfl⟩ : syracuseStep 1116869 = 209413) (by norm_num)
theorem B1116893 : Blo 742328 1116893 := bbase (se 3 (by rfl) ⟨209417, by rfl⟩ : syracuseStep 1116893 = 418835) (by norm_num)
theorem B1116917 : Blo 742328 1116917 := bbase (se 5 (by rfl) ⟨52355, by rfl⟩ : syracuseStep 1116917 = 104711) (by norm_num)
theorem B3181301 : Blo 742328 3181301 := bbase (se 5 (by rfl) ⟨149123, by rfl⟩ : syracuseStep 3181301 = 298247) (by norm_num)
theorem B1673981 : Blo 742328 1673981 := bbase (se 3 (by rfl) ⟨313871, by rfl⟩ : syracuseStep 1673981 = 627743) (by norm_num)
theorem B1116941 : Blo 742328 1116941 := bbase (se 3 (by rfl) ⟨209426, by rfl⟩ : syracuseStep 1116941 = 418853) (by norm_num)
theorem B1116965 : Blo 742328 1116965 := bbase (se 4 (by rfl) ⟨104715, by rfl⟩ : syracuseStep 1116965 = 209431) (by norm_num)
theorem B1116989 : Blo 742328 1116989 := bbase (se 3 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 1116989 = 418871) (by norm_num)
theorem B1674053 : Blo 742328 1674053 := bbase (se 4 (by rfl) ⟨156942, by rfl⟩ : syracuseStep 1674053 = 313885) (by norm_num)
theorem B1117013 : Blo 742328 1117013 := bbase (se 9 (by rfl) ⟨3272, by rfl⟩ : syracuseStep 1117013 = 6545) (by norm_num)
theorem B1117037 : Blo 742328 1117037 := bbase (se 3 (by rfl) ⟨209444, by rfl⟩ : syracuseStep 1117037 = 418889) (by norm_num)
theorem B1117061 : Blo 742328 1117061 := bbase (se 4 (by rfl) ⟨104724, by rfl⟩ : syracuseStep 1117061 = 209449) (by norm_num)
theorem B1674125 : Blo 742328 1674125 := bbase (se 3 (by rfl) ⟨313898, by rfl⟩ : syracuseStep 1674125 = 627797) (by norm_num)
theorem B1117085 : Blo 742328 1117085 := bbase (se 3 (by rfl) ⟨209453, by rfl⟩ : syracuseStep 1117085 = 418907) (by norm_num)
theorem B1412005 : Blo 742328 1412005 := bbase (se 4 (by rfl) ⟨132375, by rfl⟩ : syracuseStep 1412005 = 264751) (by norm_num)
theorem B1117109 : Blo 742328 1117109 := bbase (se 5 (by rfl) ⟨52364, by rfl⟩ : syracuseStep 1117109 = 104729) (by norm_num)
theorem B1117133 : Blo 742328 1117133 := bbase (se 3 (by rfl) ⟨209462, by rfl⟩ : syracuseStep 1117133 = 418925) (by norm_num)
theorem B1674197 : Blo 742328 1674197 := bbase (se 7 (by rfl) ⟨19619, by rfl⟩ : syracuseStep 1674197 = 39239) (by norm_num)
theorem B1117157 : Blo 742328 1117157 := bbase (se 4 (by rfl) ⟨104733, by rfl⟩ : syracuseStep 1117157 = 209467) (by norm_num)
theorem B1117181 : Blo 742328 1117181 := bbase (se 3 (by rfl) ⟨209471, by rfl⟩ : syracuseStep 1117181 = 418943) (by norm_num)
theorem B1117205 : Blo 742328 1117205 := bbase (se 6 (by rfl) ⟨26184, by rfl⟩ : syracuseStep 1117205 = 52369) (by norm_num)
theorem B1674269 : Blo 742328 1674269 := bbase (se 3 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 1674269 = 627851) (by norm_num)
theorem B1117229 : Blo 742328 1117229 := bbase (se 3 (by rfl) ⟨209480, by rfl⟩ : syracuseStep 1117229 = 418961) (by norm_num)
theorem B1412149 : Blo 742328 1412149 := bbase (se 5 (by rfl) ⟨66194, by rfl⟩ : syracuseStep 1412149 = 132389) (by norm_num)
theorem B1117253 : Blo 742328 1117253 := bbase (se 4 (by rfl) ⟨104742, by rfl⟩ : syracuseStep 1117253 = 209485) (by norm_num)
theorem B1117277 : Blo 742328 1117277 := bbase (se 3 (by rfl) ⟨209489, by rfl⟩ : syracuseStep 1117277 = 418979) (by norm_num)
theorem B1674341 : Blo 742328 1674341 := bbase (se 4 (by rfl) ⟨156969, by rfl⟩ : syracuseStep 1674341 = 313939) (by norm_num)
theorem B1117301 : Blo 742328 1117301 := bbase (se 5 (by rfl) ⟨52373, by rfl⟩ : syracuseStep 1117301 = 104747) (by norm_num)
theorem B1117325 : Blo 742328 1117325 := bbase (se 3 (by rfl) ⟨209498, by rfl⟩ : syracuseStep 1117325 = 418997) (by norm_num)
theorem B1117349 : Blo 742328 1117349 := bbase (se 4 (by rfl) ⟨104751, by rfl⟩ : syracuseStep 1117349 = 209503) (by norm_num)
theorem B1674413 : Blo 742328 1674413 := bbase (se 3 (by rfl) ⟨313952, by rfl⟩ : syracuseStep 1674413 = 627905) (by norm_num)
theorem B1117373 : Blo 742328 1117373 := bbase (se 3 (by rfl) ⟨209507, by rfl⟩ : syracuseStep 1117373 = 419015) (by norm_num)
theorem B1412309 : Blo 742328 1412309 := bbase (se 7 (by rfl) ⟨16550, by rfl⟩ : syracuseStep 1412309 = 33101) (by norm_num)
theorem B1117397 : Blo 742328 1117397 := bbase (se 7 (by rfl) ⟨13094, by rfl⟩ : syracuseStep 1117397 = 26189) (by norm_num)
theorem B1117421 : Blo 742328 1117421 := bbase (se 3 (by rfl) ⟨209516, by rfl⟩ : syracuseStep 1117421 = 419033) (by norm_num)
theorem B1674485 : Blo 742328 1674485 := bbase (se 5 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 1674485 = 156983) (by norm_num)
theorem B1117445 : Blo 742328 1117445 := bbase (se 4 (by rfl) ⟨104760, by rfl⟩ : syracuseStep 1117445 = 209521) (by norm_num)
theorem B1117469 : Blo 742328 1117469 := bbase (se 3 (by rfl) ⟨209525, by rfl⟩ : syracuseStep 1117469 = 419051) (by norm_num)
theorem B1117493 : Blo 742328 1117493 := bbase (se 5 (by rfl) ⟨52382, by rfl⟩ : syracuseStep 1117493 = 104765) (by norm_num)
theorem B1674557 : Blo 742328 1674557 := bbase (se 3 (by rfl) ⟨313979, by rfl⟩ : syracuseStep 1674557 = 627959) (by norm_num)
theorem B1117517 : Blo 742328 1117517 := bbase (se 3 (by rfl) ⟨209534, by rfl⟩ : syracuseStep 1117517 = 419069) (by norm_num)
theorem B1412453 : Blo 742328 1412453 := bbase (se 4 (by rfl) ⟨132417, by rfl⟩ : syracuseStep 1412453 = 264835) (by norm_num)
theorem B1117541 : Blo 742328 1117541 := bbase (se 4 (by rfl) ⟨104769, by rfl⟩ : syracuseStep 1117541 = 209539) (by norm_num)
theorem B1117565 : Blo 742328 1117565 := bbase (se 3 (by rfl) ⟨209543, by rfl⟩ : syracuseStep 1117565 = 419087) (by norm_num)
theorem B1674629 : Blo 742328 1674629 := bbase (se 4 (by rfl) ⟨156996, by rfl⟩ : syracuseStep 1674629 = 313993) (by norm_num)
theorem B1117589 : Blo 742328 1117589 := bbase (se 6 (by rfl) ⟨26193, by rfl⟩ : syracuseStep 1117589 = 52387) (by norm_num)
theorem B1117613 : Blo 742328 1117613 := bbase (se 3 (by rfl) ⟨209552, by rfl⟩ : syracuseStep 1117613 = 419105) (by norm_num)
theorem B3771845 : Blo 742328 3771845 := bbase (se 4 (by rfl) ⟨353610, by rfl⟩ : syracuseStep 3771845 = 707221) (by norm_num)
theorem B1117637 : Blo 742328 1117637 := bbase (se 4 (by rfl) ⟨104778, by rfl⟩ : syracuseStep 1117637 = 209557) (by norm_num)
theorem B1674701 : Blo 742328 1674701 := bbase (se 3 (by rfl) ⟨314006, by rfl⟩ : syracuseStep 1674701 = 628013) (by norm_num)
theorem B1117661 : Blo 742328 1117661 := bbase (se 3 (by rfl) ⟨209561, by rfl⟩ : syracuseStep 1117661 = 419123) (by norm_num)
theorem B1117685 : Blo 742328 1117685 := bbase (se 5 (by rfl) ⟨52391, by rfl⟩ : syracuseStep 1117685 = 104783) (by norm_num)
theorem B1117709 : Blo 742328 1117709 := bbase (se 3 (by rfl) ⟨209570, by rfl⟩ : syracuseStep 1117709 = 419141) (by norm_num)
theorem B1674773 : Blo 742328 1674773 := bbase (se 6 (by rfl) ⟨39252, by rfl⟩ : syracuseStep 1674773 = 78505) (by norm_num)
theorem B1117733 : Blo 742328 1117733 := bbase (se 4 (by rfl) ⟨104787, by rfl⟩ : syracuseStep 1117733 = 209575) (by norm_num)
theorem B3018293 : Blo 742328 3018293 := bbase (se 5 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 3018293 = 282965) (by norm_num)
theorem B1117757 : Blo 742328 1117757 := bbase (se 3 (by rfl) ⟨209579, by rfl⟩ : syracuseStep 1117757 = 419159) (by norm_num)
theorem B2068037 : Blo 742328 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B1117781 : Blo 742328 1117781 := bbase (se 8 (by rfl) ⟨6549, by rfl⟩ : syracuseStep 1117781 = 13099) (by norm_num)
theorem B1674845 : Blo 742328 1674845 := bbase (se 3 (by rfl) ⟨314033, by rfl⟩ : syracuseStep 1674845 = 628067) (by norm_num)
theorem B1117805 : Blo 742328 1117805 := bbase (se 3 (by rfl) ⟨209588, by rfl⟩ : syracuseStep 1117805 = 419177) (by norm_num)
theorem B1412741 : Blo 742328 1412741 := bbase (se 4 (by rfl) ⟨132444, by rfl⟩ : syracuseStep 1412741 = 264889) (by norm_num)
theorem B1117829 : Blo 742328 1117829 := bbase (se 4 (by rfl) ⟨104796, by rfl⟩ : syracuseStep 1117829 = 209593) (by norm_num)
theorem B954001 : Blo 742328 954001 := bbase (se 2 (by rfl) ⟨357750, by rfl⟩ : syracuseStep 954001 = 715501) (by norm_num)
theorem B1117853 : Blo 742328 1117853 := bbase (se 3 (by rfl) ⟨209597, by rfl⟩ : syracuseStep 1117853 = 419195) (by norm_num)
theorem B1674917 : Blo 742328 1674917 := bbase (se 4 (by rfl) ⟨157023, by rfl⟩ : syracuseStep 1674917 = 314047) (by norm_num)
theorem B1117877 : Blo 742328 1117877 := bbase (se 5 (by rfl) ⟨52400, by rfl⟩ : syracuseStep 1117877 = 104801) (by norm_num)
theorem B1117901 : Blo 742328 1117901 := bbase (se 3 (by rfl) ⟨209606, by rfl⟩ : syracuseStep 1117901 = 419213) (by norm_num)
theorem B6786773 : Blo 742328 6786773 := bbase (se 7 (by rfl) ⟨79532, by rfl⟩ : syracuseStep 6786773 = 159065) (by norm_num)
theorem B1117925 : Blo 742328 1117925 := bbase (se 4 (by rfl) ⟨104805, by rfl⟩ : syracuseStep 1117925 = 209611) (by norm_num)
theorem B1674989 : Blo 742328 1674989 := bbase (se 3 (by rfl) ⟨314060, by rfl⟩ : syracuseStep 1674989 = 628121) (by norm_num)
theorem B1117949 : Blo 742328 1117949 := bbase (se 3 (by rfl) ⟨209615, by rfl⟩ : syracuseStep 1117949 = 419231) (by norm_num)
theorem B1117973 : Blo 742328 1117973 := bbase (se 6 (by rfl) ⟨26202, by rfl⟩ : syracuseStep 1117973 = 52405) (by norm_num)
theorem B1412893 : Blo 742328 1412893 := bbase (se 3 (by rfl) ⟨264917, by rfl⟩ : syracuseStep 1412893 = 529835) (by norm_num)
theorem B1117997 : Blo 742328 1117997 := bbase (se 3 (by rfl) ⟨209624, by rfl⟩ : syracuseStep 1117997 = 419249) (by norm_num)
theorem B1675061 : Blo 742328 1675061 := bbase (se 5 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 1675061 = 157037) (by norm_num)
theorem B1118021 : Blo 742328 1118021 := bbase (se 4 (by rfl) ⟨104814, by rfl⟩ : syracuseStep 1118021 = 209629) (by norm_num)
theorem B1118045 : Blo 742328 1118045 := bbase (se 3 (by rfl) ⟨209633, by rfl⟩ : syracuseStep 1118045 = 419267) (by norm_num)
theorem B1118069 : Blo 742328 1118069 := bbase (se 5 (by rfl) ⟨52409, by rfl⟩ : syracuseStep 1118069 = 104819) (by norm_num)
theorem B1675133 : Blo 742328 1675133 := bbase (se 3 (by rfl) ⟨314087, by rfl⟩ : syracuseStep 1675133 = 628175) (by norm_num)
theorem B1118093 : Blo 742328 1118093 := bbase (se 3 (by rfl) ⟨209642, by rfl⟩ : syracuseStep 1118093 = 419285) (by norm_num)
theorem B1118117 : Blo 742328 1118117 := bbase (se 4 (by rfl) ⟨104823, by rfl⟩ : syracuseStep 1118117 = 209647) (by norm_num)
theorem B1118141 : Blo 742328 1118141 := bbase (se 3 (by rfl) ⟨209651, by rfl⟩ : syracuseStep 1118141 = 419303) (by norm_num)
theorem B1675205 : Blo 742328 1675205 := bbase (se 4 (by rfl) ⟨157050, by rfl⟩ : syracuseStep 1675205 = 314101) (by norm_num)
theorem B1118165 : Blo 742328 1118165 := bbase (se 7 (by rfl) ⟨13103, by rfl⟩ : syracuseStep 1118165 = 26207) (by norm_num)
theorem B1118189 : Blo 742328 1118189 := bbase (se 3 (by rfl) ⟨209660, by rfl⟩ : syracuseStep 1118189 = 419321) (by norm_num)
theorem B1118213 : Blo 742328 1118213 := bbase (se 4 (by rfl) ⟨104832, by rfl⟩ : syracuseStep 1118213 = 209665) (by norm_num)
theorem B1675277 : Blo 742328 1675277 := bbase (se 3 (by rfl) ⟨314114, by rfl⟩ : syracuseStep 1675277 = 628229) (by norm_num)
theorem B1118237 : Blo 742328 1118237 := bbase (se 3 (by rfl) ⟨209669, by rfl⟩ : syracuseStep 1118237 = 419339) (by norm_num)
theorem B1118261 : Blo 742328 1118261 := bbase (se 5 (by rfl) ⟨52418, by rfl⟩ : syracuseStep 1118261 = 104837) (by norm_num)
theorem B1413197 : Blo 742328 1413197 := bbase (se 3 (by rfl) ⟨264974, by rfl⟩ : syracuseStep 1413197 = 529949) (by norm_num)
theorem B1118285 : Blo 742328 1118285 := bbase (se 3 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 1118285 = 419357) (by norm_num)
theorem B1675349 : Blo 742328 1675349 := bbase (se 8 (by rfl) ⟨9816, by rfl⟩ : syracuseStep 1675349 = 19633) (by norm_num)
theorem B1118309 : Blo 742328 1118309 := bbase (se 4 (by rfl) ⟨104841, by rfl⟩ : syracuseStep 1118309 = 209683) (by norm_num)
theorem B1118333 : Blo 742328 1118333 := bbase (se 3 (by rfl) ⟨209687, by rfl⟩ : syracuseStep 1118333 = 419375) (by norm_num)
theorem B1118357 : Blo 742328 1118357 := bbase (se 6 (by rfl) ⟨26211, by rfl⟩ : syracuseStep 1118357 = 52423) (by norm_num)
theorem B1675421 : Blo 742328 1675421 := bbase (se 3 (by rfl) ⟨314141, by rfl⟩ : syracuseStep 1675421 = 628283) (by norm_num)
theorem B2822309 : Blo 742328 2822309 := bbase (se 4 (by rfl) ⟨264591, by rfl⟩ : syracuseStep 2822309 = 529183) (by norm_num)
theorem B1118381 : Blo 742328 1118381 := bbase (se 3 (by rfl) ⟨209696, by rfl⟩ : syracuseStep 1118381 = 419393) (by norm_num)
theorem B1118405 : Blo 742328 1118405 := bbase (se 4 (by rfl) ⟨104850, by rfl⟩ : syracuseStep 1118405 = 209701) (by norm_num)
theorem B1118429 : Blo 742328 1118429 := bbase (se 3 (by rfl) ⟨209705, by rfl⟩ : syracuseStep 1118429 = 419411) (by norm_num)
theorem B1675493 : Blo 742328 1675493 := bbase (se 4 (by rfl) ⟨157077, by rfl⟩ : syracuseStep 1675493 = 314155) (by norm_num)
theorem B1118453 : Blo 742328 1118453 := bbase (se 5 (by rfl) ⟨52427, by rfl⟩ : syracuseStep 1118453 = 104855) (by norm_num)
theorem B1118477 : Blo 742328 1118477 := bbase (se 3 (by rfl) ⟨209714, by rfl⟩ : syracuseStep 1118477 = 419429) (by norm_num)
theorem B1118501 : Blo 742328 1118501 := bbase (se 4 (by rfl) ⟨104859, by rfl⟩ : syracuseStep 1118501 = 209719) (by norm_num)
theorem B1675565 : Blo 742328 1675565 := bbase (se 3 (by rfl) ⟨314168, by rfl⟩ : syracuseStep 1675565 = 628337) (by norm_num)
theorem B1118525 : Blo 742328 1118525 := bbase (se 3 (by rfl) ⟨209723, by rfl⟩ : syracuseStep 1118525 = 419447) (by norm_num)
theorem B1511741 : Blo 742328 1511741 := bbase (se 3 (by rfl) ⟨283451, by rfl⟩ : syracuseStep 1511741 = 566903) (by norm_num)
theorem B1118549 : Blo 742328 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B1118573 : Blo 742328 1118573 := bbase (se 3 (by rfl) ⟨209732, by rfl⟩ : syracuseStep 1118573 = 419465) (by norm_num)
theorem B1675637 : Blo 742328 1675637 := bbase (se 5 (by rfl) ⟨78545, by rfl⟩ : syracuseStep 1675637 = 157091) (by norm_num)
theorem B1118597 : Blo 742328 1118597 := bbase (se 4 (by rfl) ⟨104868, by rfl⟩ : syracuseStep 1118597 = 209737) (by norm_num)
theorem B1118621 : Blo 742328 1118621 := bbase (se 3 (by rfl) ⟨209741, by rfl⟩ : syracuseStep 1118621 = 419483) (by norm_num)
theorem B1118645 : Blo 742328 1118645 := bbase (se 5 (by rfl) ⟨52436, by rfl⟩ : syracuseStep 1118645 = 104873) (by norm_num)
theorem B1675709 : Blo 742328 1675709 := bbase (se 3 (by rfl) ⟨314195, by rfl⟩ : syracuseStep 1675709 = 628391) (by norm_num)
theorem B2822597 : Blo 742328 2822597 := bbase (se 4 (by rfl) ⟨264618, by rfl⟩ : syracuseStep 2822597 = 529237) (by norm_num)
theorem B1118669 : Blo 742328 1118669 := bbase (se 3 (by rfl) ⟨209750, by rfl⟩ : syracuseStep 1118669 = 419501) (by norm_num)
theorem B3183077 : Blo 742328 3183077 := bbase (se 4 (by rfl) ⟨298413, by rfl⟩ : syracuseStep 3183077 = 596827) (by norm_num)
theorem B1118693 : Blo 742328 1118693 := bbase (se 4 (by rfl) ⟨104877, by rfl⟩ : syracuseStep 1118693 = 209755) (by norm_num)
theorem B1118717 : Blo 742328 1118717 := bbase (se 3 (by rfl) ⟨209759, by rfl⟩ : syracuseStep 1118717 = 419519) (by norm_num)
theorem B1675781 : Blo 742328 1675781 := bbase (se 4 (by rfl) ⟨157104, by rfl⟩ : syracuseStep 1675781 = 314209) (by norm_num)
theorem B1118741 : Blo 742328 1118741 := bbase (se 6 (by rfl) ⟨26220, by rfl⟩ : syracuseStep 1118741 = 52441) (by norm_num)
theorem B1118765 : Blo 742328 1118765 := bbase (se 3 (by rfl) ⟨209768, by rfl⟩ : syracuseStep 1118765 = 419537) (by norm_num)
theorem B1118789 : Blo 742328 1118789 := bbase (se 4 (by rfl) ⟨104886, by rfl⟩ : syracuseStep 1118789 = 209773) (by norm_num)
theorem B1675853 : Blo 742328 1675853 := bbase (se 3 (by rfl) ⟨314222, by rfl⟩ : syracuseStep 1675853 = 628445) (by norm_num)
theorem B1118813 : Blo 742328 1118813 := bbase (se 3 (by rfl) ⟨209777, by rfl⟩ : syracuseStep 1118813 = 419555) (by norm_num)
theorem B1118837 : Blo 742328 1118837 := bbase (se 5 (by rfl) ⟨52445, by rfl⟩ : syracuseStep 1118837 = 104891) (by norm_num)
theorem B1118861 : Blo 742328 1118861 := bbase (se 3 (by rfl) ⟨209786, by rfl⟩ : syracuseStep 1118861 = 419573) (by norm_num)
theorem B1675925 : Blo 742328 1675925 := bbase (se 6 (by rfl) ⟨39279, by rfl⟩ : syracuseStep 1675925 = 78559) (by norm_num)
theorem B1118885 : Blo 742328 1118885 := bbase (se 4 (by rfl) ⟨104895, by rfl⟩ : syracuseStep 1118885 = 209791) (by norm_num)
theorem B1118909 : Blo 742328 1118909 := bbase (se 3 (by rfl) ⟨209795, by rfl⟩ : syracuseStep 1118909 = 419591) (by norm_num)
theorem B3773141 : Blo 742328 3773141 := bbase (se 7 (by rfl) ⟨44216, by rfl⟩ : syracuseStep 3773141 = 88433) (by norm_num)
theorem B1118933 : Blo 742328 1118933 := bbase (se 7 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 1118933 = 26225) (by norm_num)
theorem B1675997 : Blo 742328 1675997 := bbase (se 3 (by rfl) ⟨314249, by rfl⟩ : syracuseStep 1675997 = 628499) (by norm_num)
theorem B1118957 : Blo 742328 1118957 := bbase (se 3 (by rfl) ⟨209804, by rfl⟩ : syracuseStep 1118957 = 419609) (by norm_num)
theorem B1118981 : Blo 742328 1118981 := bbase (se 4 (by rfl) ⟨104904, by rfl⟩ : syracuseStep 1118981 = 209809) (by norm_num)
theorem B1119005 : Blo 742328 1119005 := bbase (se 3 (by rfl) ⟨209813, by rfl⟩ : syracuseStep 1119005 = 419627) (by norm_num)
theorem B1676069 : Blo 742328 1676069 := bbase (se 4 (by rfl) ⟨157131, by rfl⟩ : syracuseStep 1676069 = 314263) (by norm_num)
theorem B1119029 : Blo 742328 1119029 := bbase (se 5 (by rfl) ⟨52454, by rfl⟩ : syracuseStep 1119029 = 104909) (by norm_num)
theorem B1413949 : Blo 742328 1413949 := bbase (se 3 (by rfl) ⟨265115, by rfl⟩ : syracuseStep 1413949 = 530231) (by norm_num)
theorem B1119053 : Blo 742328 1119053 := bbase (se 3 (by rfl) ⟨209822, by rfl⟩ : syracuseStep 1119053 = 419645) (by norm_num)
theorem B1119077 : Blo 742328 1119077 := bbase (se 4 (by rfl) ⟨104913, by rfl⟩ : syracuseStep 1119077 = 209827) (by norm_num)
theorem B1676141 : Blo 742328 1676141 := bbase (se 3 (by rfl) ⟨314276, by rfl⟩ : syracuseStep 1676141 = 628553) (by norm_num)
theorem B1119101 : Blo 742328 1119101 := bbase (se 3 (by rfl) ⟨209831, by rfl⟩ : syracuseStep 1119101 = 419663) (by norm_num)
theorem B1119125 : Blo 742328 1119125 := bbase (se 6 (by rfl) ⟨26229, by rfl⟩ : syracuseStep 1119125 = 52459) (by norm_num)
theorem B1119149 : Blo 742328 1119149 := bbase (se 3 (by rfl) ⟨209840, by rfl⟩ : syracuseStep 1119149 = 419681) (by norm_num)
theorem B1676213 : Blo 742328 1676213 := bbase (se 5 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 1676213 = 157145) (by norm_num)
theorem B1119173 : Blo 742328 1119173 := bbase (se 4 (by rfl) ⟨104922, by rfl⟩ : syracuseStep 1119173 = 209845) (by norm_num)
theorem B1414093 : Blo 742328 1414093 := bbase (se 3 (by rfl) ⟨265142, by rfl⟩ : syracuseStep 1414093 = 530285) (by norm_num)
theorem B2331605 : Blo 742328 2331605 := bbase (se 7 (by rfl) ⟨27323, by rfl⟩ : syracuseStep 2331605 = 54647) (by norm_num)
theorem B1119197 : Blo 742328 1119197 := bbase (se 3 (by rfl) ⟨209849, by rfl⟩ : syracuseStep 1119197 = 419699) (by norm_num)
theorem B1119221 : Blo 742328 1119221 := bbase (se 5 (by rfl) ⟨52463, by rfl⟩ : syracuseStep 1119221 = 104927) (by norm_num)
theorem B1676285 : Blo 742328 1676285 := bbase (se 3 (by rfl) ⟨314303, by rfl⟩ : syracuseStep 1676285 = 628607) (by norm_num)
theorem B1119245 : Blo 742328 1119245 := bbase (se 3 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 1119245 = 419717) (by norm_num)
theorem B1119269 : Blo 742328 1119269 := bbase (se 4 (by rfl) ⟨104931, by rfl⟩ : syracuseStep 1119269 = 209863) (by norm_num)
theorem B1119293 : Blo 742328 1119293 := bbase (se 3 (by rfl) ⟨209867, by rfl⟩ : syracuseStep 1119293 = 419735) (by norm_num)
theorem B1676357 : Blo 742328 1676357 := bbase (se 4 (by rfl) ⟨157158, by rfl⟩ : syracuseStep 1676357 = 314317) (by norm_num)
theorem B1119317 : Blo 742328 1119317 := bbase (se 8 (by rfl) ⟨6558, by rfl⟩ : syracuseStep 1119317 = 13117) (by norm_num)
theorem B1414253 : Blo 742328 1414253 := bbase (se 3 (by rfl) ⟨265172, by rfl⟩ : syracuseStep 1414253 = 530345) (by norm_num)
theorem B1119341 : Blo 742328 1119341 := bbase (se 3 (by rfl) ⟨209876, by rfl⟩ : syracuseStep 1119341 = 419753) (by norm_num)
theorem B1119365 : Blo 742328 1119365 := bbase (se 4 (by rfl) ⟨104940, by rfl⟩ : syracuseStep 1119365 = 209881) (by norm_num)
theorem B1676429 : Blo 742328 1676429 := bbase (se 3 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 1676429 = 628661) (by norm_num)
theorem B1119389 : Blo 742328 1119389 := bbase (se 3 (by rfl) ⟨209885, by rfl⟩ : syracuseStep 1119389 = 419771) (by norm_num)
theorem B1119413 : Blo 742328 1119413 := bbase (se 5 (by rfl) ⟨52472, by rfl⟩ : syracuseStep 1119413 = 104945) (by norm_num)
theorem B1119437 : Blo 742328 1119437 := bbase (se 3 (by rfl) ⟨209894, by rfl⟩ : syracuseStep 1119437 = 419789) (by norm_num)
theorem B1676501 : Blo 742328 1676501 := bbase (se 7 (by rfl) ⟨19646, by rfl⟩ : syracuseStep 1676501 = 39293) (by norm_num)
theorem B1119461 : Blo 742328 1119461 := bbase (se 4 (by rfl) ⟨104949, by rfl⟩ : syracuseStep 1119461 = 209899) (by norm_num)
theorem B1414397 : Blo 742328 1414397 := bbase (se 3 (by rfl) ⟨265199, by rfl⟩ : syracuseStep 1414397 = 530399) (by norm_num)
theorem B1119485 : Blo 742328 1119485 := bbase (se 3 (by rfl) ⟨209903, by rfl⟩ : syracuseStep 1119485 = 419807) (by norm_num)
theorem B1611037 : Blo 742328 1611037 := bbase (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) (by norm_num)
theorem B1676573 : Blo 742328 1676573 := bbase (se 3 (by rfl) ⟨314357, by rfl⟩ : syracuseStep 1676573 = 628715) (by norm_num)
theorem B955741 : Blo 742328 955741 := bbase (se 3 (by rfl) ⟨179201, by rfl⟩ : syracuseStep 955741 = 358403) (by norm_num)
theorem B1676645 : Blo 742328 1676645 := bbase (se 4 (by rfl) ⟨157185, by rfl⟩ : syracuseStep 1676645 = 314371) (by norm_num)
theorem B1611149 : Blo 742328 1611149 := bbase (se 3 (by rfl) ⟨302090, by rfl⟩ : syracuseStep 1611149 = 604181) (by norm_num)
theorem B1676717 : Blo 742328 1676717 := bbase (se 3 (by rfl) ⟨314384, by rfl⟩ : syracuseStep 1676717 = 628769) (by norm_num)
theorem B1021397 : Blo 742328 1021397 := bbase (se 7 (by rfl) ⟨11969, by rfl⟩ : syracuseStep 1021397 = 23939) (by norm_num)
theorem B1676789 : Blo 742328 1676789 := bbase (se 5 (by rfl) ⟨78599, by rfl⟩ : syracuseStep 1676789 = 157199) (by norm_num)
theorem B1414685 : Blo 742328 1414685 := bbase (se 3 (by rfl) ⟨265253, by rfl⟩ : syracuseStep 1414685 = 530507) (by norm_num)
theorem B1676861 : Blo 742328 1676861 := bbase (se 3 (by rfl) ⟨314411, by rfl⟩ : syracuseStep 1676861 = 628823) (by norm_num)
theorem B2823781 : Blo 742328 2823781 := bbase (se 4 (by rfl) ⟨264729, by rfl⟩ : syracuseStep 2823781 = 529459) (by norm_num)
theorem B1676933 : Blo 742328 1676933 := bbase (se 4 (by rfl) ⟨157212, by rfl⟩ : syracuseStep 1676933 = 314425) (by norm_num)
theorem B1414837 : Blo 742328 1414837 := bbase (se 5 (by rfl) ⟨66320, by rfl⟩ : syracuseStep 1414837 = 132641) (by norm_num)
theorem B1677005 : Blo 742328 1677005 := bbase (se 3 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 1677005 = 628877) (by norm_num)
theorem B5641973 : Blo 742328 5641973 := bbase (se 5 (by rfl) ⟨264467, by rfl⟩ : syracuseStep 5641973 = 528935) (by norm_num)
theorem B1677077 : Blo 742328 1677077 := bbase (se 6 (by rfl) ⟨39306, by rfl⟩ : syracuseStep 1677077 = 78613) (by norm_num)
theorem B1677149 : Blo 742328 1677149 := bbase (se 3 (by rfl) ⟨314465, by rfl⟩ : syracuseStep 1677149 = 628931) (by norm_num)
theorem B2824085 : Blo 742328 2824085 := bbase (se 6 (by rfl) ⟨66189, by rfl⟩ : syracuseStep 2824085 = 132379) (by norm_num)
theorem B1677221 : Blo 742328 1677221 := bbase (se 4 (by rfl) ⟨157239, by rfl⟩ : syracuseStep 1677221 = 314479) (by norm_num)
theorem B1415141 : Blo 742328 1415141 := bbase (se 4 (by rfl) ⟨132669, by rfl⟩ : syracuseStep 1415141 = 265339) (by norm_num)
theorem B3774437 : Blo 742328 3774437 := bbase (se 4 (by rfl) ⟨353853, by rfl⟩ : syracuseStep 3774437 = 707707) (by norm_num)
theorem B1677293 : Blo 742328 1677293 := bbase (se 3 (by rfl) ⟨314492, by rfl⟩ : syracuseStep 1677293 = 628985) (by norm_num)
theorem B6789109 : Blo 742328 6789109 := bbase (se 5 (by rfl) ⟨318239, by rfl⟩ : syracuseStep 6789109 = 636479) (by norm_num)
theorem B2857013 : Blo 742328 2857013 := bbase (se 5 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 2857013 = 267845) (by norm_num)
theorem B1677365 : Blo 742328 1677365 := bbase (se 5 (by rfl) ⟨78626, by rfl⟩ : syracuseStep 1677365 = 157253) (by norm_num)
theorem B3577925 : Blo 742328 3577925 := bbase (se 4 (by rfl) ⟨335430, by rfl⟩ : syracuseStep 3577925 = 670861) (by norm_num)
theorem B1677437 : Blo 742328 1677437 := bbase (se 3 (by rfl) ⟨314519, by rfl⟩ : syracuseStep 1677437 = 629039) (by norm_num)
theorem B1677509 : Blo 742328 1677509 := bbase (se 4 (by rfl) ⟨157266, by rfl⟩ : syracuseStep 1677509 = 314533) (by norm_num)
theorem B5445845 : Blo 742328 5445845 := bbase (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) (by norm_num)
theorem B1677581 : Blo 742328 1677581 := bbase (se 3 (by rfl) ⟨314546, by rfl⟩ : syracuseStep 1677581 = 629093) (by norm_num)
theorem B792865 : Blo 742328 792865 := bbase (se 2 (by rfl) ⟨297324, by rfl⟩ : syracuseStep 792865 = 594649) (by norm_num)
theorem B1677653 : Blo 742328 1677653 := bbase (se 10 (by rfl) ⟨2457, by rfl⟩ : syracuseStep 1677653 = 4915) (by norm_num)
theorem B1677725 : Blo 742328 1677725 := bbase (se 3 (by rfl) ⟨314573, by rfl⟩ : syracuseStep 1677725 = 629147) (by norm_num)
theorem B3578309 : Blo 742328 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B1677797 : Blo 742328 1677797 := bbase (se 4 (by rfl) ⟨157293, by rfl⟩ : syracuseStep 1677797 = 314587) (by norm_num)
theorem B1677869 : Blo 742328 1677869 := bbase (se 3 (by rfl) ⟨314600, by rfl⟩ : syracuseStep 1677869 = 629201) (by norm_num)
theorem B1677941 : Blo 742328 1677941 := bbase (se 5 (by rfl) ⟨78653, by rfl⟩ : syracuseStep 1677941 = 157307) (by norm_num)
theorem B1940149 : Blo 742328 1940149 := bbase (se 5 (by rfl) ⟨90944, by rfl⟩ : syracuseStep 1940149 = 181889) (by norm_num)
theorem B1678013 : Blo 742328 1678013 := bbase (se 3 (by rfl) ⟨314627, by rfl⟩ : syracuseStep 1678013 = 629255) (by norm_num)
theorem B4233941 : Blo 742328 4233941 := bbase (se 7 (by rfl) ⟨49616, by rfl⟩ : syracuseStep 4233941 = 99233) (by norm_num)
theorem B1415893 : Blo 742328 1415893 := bbase (se 7 (by rfl) ⟨16592, by rfl⟩ : syracuseStep 1415893 = 33185) (by norm_num)
theorem B793309 : Blo 742328 793309 := bbase (se 3 (by rfl) ⟨148745, by rfl⟩ : syracuseStep 793309 = 297491) (by norm_num)
theorem B3054341 : Blo 742328 3054341 := bbase (se 4 (by rfl) ⟨286344, by rfl⟩ : syracuseStep 3054341 = 572689) (by norm_num)
theorem B1678085 : Blo 742328 1678085 := bbase (se 4 (by rfl) ⟨157320, by rfl⟩ : syracuseStep 1678085 = 314641) (by norm_num)
theorem B1678157 : Blo 742328 1678157 := bbase (se 3 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 1678157 = 629309) (by norm_num)
theorem B793433 : Blo 742328 793433 := bbase (se 2 (by rfl) ⟨297537, by rfl⟩ : syracuseStep 793433 = 595075) (by norm_num)
theorem B1416037 : Blo 742328 1416037 := bbase (se 4 (by rfl) ⟨132753, by rfl⟩ : syracuseStep 1416037 = 265507) (by norm_num)
theorem B1678229 : Blo 742328 1678229 := bbase (se 6 (by rfl) ⟨39333, by rfl⟩ : syracuseStep 1678229 = 78667) (by norm_num)
theorem B1678301 : Blo 742328 1678301 := bbase (se 3 (by rfl) ⟨314681, by rfl⟩ : syracuseStep 1678301 = 629363) (by norm_num)
theorem B1416197 : Blo 742328 1416197 := bbase (se 4 (by rfl) ⟨132768, by rfl⟩ : syracuseStep 1416197 = 265537) (by norm_num)
theorem B1678373 : Blo 742328 1678373 := bbase (se 4 (by rfl) ⟨157347, by rfl⟩ : syracuseStep 1678373 = 314695) (by norm_num)
theorem B793685 : Blo 742328 793685 := bbase (se 8 (by rfl) ⟨4650, by rfl⟩ : syracuseStep 793685 = 9301) (by norm_num)
theorem B1678445 : Blo 742328 1678445 := bbase (se 3 (by rfl) ⟨314708, by rfl⟩ : syracuseStep 1678445 = 629417) (by norm_num)
theorem B892021 : Blo 742328 892021 := bbase (se 5 (by rfl) ⟨41813, by rfl⟩ : syracuseStep 892021 = 83627) (by norm_num)
theorem B1416341 : Blo 742328 1416341 := bbase (se 6 (by rfl) ⟨33195, by rfl⟩ : syracuseStep 1416341 = 66391) (by norm_num)
theorem B1678517 : Blo 742328 1678517 := bbase (se 5 (by rfl) ⟨78680, by rfl⟩ : syracuseStep 1678517 = 157361) (by norm_num)
theorem B892117 : Blo 742328 892117 := bbase (se 7 (by rfl) ⟨10454, by rfl⟩ : syracuseStep 892117 = 20909) (by norm_num)
theorem B1613029 : Blo 742328 1613029 := bbase (se 4 (by rfl) ⟨151221, by rfl⟩ : syracuseStep 1613029 = 302443) (by norm_num)
theorem B3775733 : Blo 742328 3775733 := bbase (se 5 (by rfl) ⟨176987, by rfl⟩ : syracuseStep 3775733 = 353975) (by norm_num)
theorem B1678589 : Blo 742328 1678589 := bbase (se 3 (by rfl) ⟨314735, by rfl⟩ : syracuseStep 1678589 = 629471) (by norm_num)
theorem B1678661 : Blo 742328 1678661 := bbase (se 4 (by rfl) ⟨157374, by rfl⟩ : syracuseStep 1678661 = 314749) (by norm_num)
theorem B1252685 : Blo 742328 1252685 := bbase (se 3 (by rfl) ⟨234878, by rfl⟩ : syracuseStep 1252685 = 469757) (by norm_num)
theorem B1678733 : Blo 742328 1678733 := bbase (se 3 (by rfl) ⟨314762, by rfl⟩ : syracuseStep 1678733 = 629525) (by norm_num)
theorem B1416629 : Blo 742328 1416629 := bbase (se 5 (by rfl) ⟨66404, by rfl⟩ : syracuseStep 1416629 = 132809) (by norm_num)
theorem B1252813 : Blo 742328 1252813 := bbase (se 3 (by rfl) ⟨234902, by rfl⟩ : syracuseStep 1252813 = 469805) (by norm_num)
theorem B1678805 : Blo 742328 1678805 := bbase (se 7 (by rfl) ⟨19673, by rfl⟩ : syracuseStep 1678805 = 39347) (by norm_num)
theorem B794129 : Blo 742328 794129 := bbase (se 2 (by rfl) ⟨297798, by rfl⟩ : syracuseStep 794129 = 595597) (by norm_num)
theorem B1678877 : Blo 742328 1678877 := bbase (se 3 (by rfl) ⟨314789, by rfl⟩ : syracuseStep 1678877 = 629579) (by norm_num)
theorem B1252901 : Blo 742328 1252901 := bbase (se 4 (by rfl) ⟨117459, by rfl⟩ : syracuseStep 1252901 = 234919) (by norm_num)
theorem B1416781 : Blo 742328 1416781 := bbase (se 3 (by rfl) ⟨265646, by rfl⟩ : syracuseStep 1416781 = 531293) (by norm_num)
theorem B892501 : Blo 742328 892501 := bbase (se 8 (by rfl) ⟨5229, by rfl⟩ : syracuseStep 892501 = 10459) (by norm_num)
theorem B1678949 : Blo 742328 1678949 := bbase (se 4 (by rfl) ⟨157401, by rfl⟩ : syracuseStep 1678949 = 314803) (by norm_num)
theorem B1253029 : Blo 742328 1253029 := bbase (se 4 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 1253029 = 234943) (by norm_num)
theorem B1679021 : Blo 742328 1679021 := bbase (se 3 (by rfl) ⟨314816, by rfl⟩ : syracuseStep 1679021 = 629633) (by norm_num)
theorem B1679093 : Blo 742328 1679093 := bbase (se 5 (by rfl) ⟨78707, by rfl⟩ : syracuseStep 1679093 = 157415) (by norm_num)
theorem B1253117 : Blo 742328 1253117 := bbase (se 3 (by rfl) ⟨234959, by rfl⟩ : syracuseStep 1253117 = 469919) (by norm_num)
theorem B794377 : Blo 742328 794377 := bbase (se 2 (by rfl) ⟨297891, by rfl⟩ : syracuseStep 794377 = 595783) (by norm_num)
theorem B1679165 : Blo 742328 1679165 := bbase (se 3 (by rfl) ⟨314843, by rfl⟩ : syracuseStep 1679165 = 629687) (by norm_num)
theorem B4235125 : Blo 742328 4235125 := bbase (se 5 (by rfl) ⟨198521, by rfl⟩ : syracuseStep 4235125 = 397043) (by norm_num)
theorem B1253245 : Blo 742328 1253245 := bbase (se 3 (by rfl) ⟨234983, by rfl⟩ : syracuseStep 1253245 = 469967) (by norm_num)
theorem B1679237 : Blo 742328 1679237 := bbase (se 4 (by rfl) ⟨157428, by rfl⟩ : syracuseStep 1679237 = 314857) (by norm_num)
theorem B1253333 : Blo 742328 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B2826197 : Blo 742328 2826197 := bbase (se 7 (by rfl) ⟨33119, by rfl⟩ : syracuseStep 2826197 = 66239) (by norm_num)
theorem B1253461 : Blo 742328 1253461 := bbase (se 8 (by rfl) ⟨7344, by rfl⟩ : syracuseStep 1253461 = 14689) (by norm_num)
theorem B1253549 : Blo 742328 1253549 := bbase (se 3 (by rfl) ⟨235040, by rfl⟩ : syracuseStep 1253549 = 470081) (by norm_num)
theorem B6037685 : Blo 742328 6037685 := bbase (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) (by norm_num)
theorem B794821 : Blo 742328 794821 := bbase (se 4 (by rfl) ⟨74514, by rfl⟩ : syracuseStep 794821 = 149029) (by norm_num)
theorem B2826485 : Blo 742328 2826485 := bbase (se 5 (by rfl) ⟨132491, by rfl⟩ : syracuseStep 2826485 = 264983) (by norm_num)
theorem B794881 : Blo 742328 794881 := bbase (se 2 (by rfl) ⟨298080, by rfl⟩ : syracuseStep 794881 = 596161) (by norm_num)
theorem B1057045 : Blo 742328 1057045 := bbase (se 6 (by rfl) ⟨24774, by rfl⟩ : syracuseStep 1057045 = 49549) (by norm_num)
theorem B1253677 : Blo 742328 1253677 := bbase (se 3 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 1253677 = 470129) (by norm_num)
theorem B860513 : Blo 742328 860513 := bbase (se 2 (by rfl) ⟨322692, by rfl⟩ : syracuseStep 860513 = 645385) (by norm_num)
theorem B1057141 : Blo 742328 1057141 := bbase (se 5 (by rfl) ⟨49553, by rfl⟩ : syracuseStep 1057141 = 99107) (by norm_num)
theorem B6037877 : Blo 742328 6037877 := bbase (se 5 (by rfl) ⟨283025, by rfl⟩ : syracuseStep 6037877 = 566051) (by norm_num)
theorem B1253765 : Blo 742328 1253765 := bbase (se 4 (by rfl) ⟨117540, by rfl⟩ : syracuseStep 1253765 = 235081) (by norm_num)
theorem B1253893 : Blo 742328 1253893 := bbase (se 4 (by rfl) ⟨117552, by rfl⟩ : syracuseStep 1253893 = 235105) (by norm_num)
theorem B3777029 : Blo 742328 3777029 := bbase (se 4 (by rfl) ⟨354096, by rfl⟩ : syracuseStep 3777029 = 708193) (by norm_num)
theorem B3809845 : Blo 742328 3809845 := bbase (se 5 (by rfl) ⟨178586, by rfl⟩ : syracuseStep 3809845 = 357173) (by norm_num)
theorem B795197 : Blo 742328 795197 := bbase (se 3 (by rfl) ⟨149099, by rfl⟩ : syracuseStep 795197 = 298199) (by norm_num)
theorem B1253981 : Blo 742328 1253981 := bbase (se 3 (by rfl) ⟨235121, by rfl⟩ : syracuseStep 1253981 = 470243) (by norm_num)
theorem B893549 : Blo 742328 893549 := bbase (se 3 (by rfl) ⟨167540, by rfl⟩ : syracuseStep 893549 = 335081) (by norm_num)
theorem B8495765 : Blo 742328 8495765 := bbase (se 6 (by rfl) ⟨199119, by rfl⟩ : syracuseStep 8495765 = 398239) (by norm_num)
theorem B3187349 : Blo 742328 3187349 := bbase (se 6 (by rfl) ⟨74703, by rfl⟩ : syracuseStep 3187349 = 149407) (by norm_num)
theorem B3875525 : Blo 742328 3875525 := bbase (se 4 (by rfl) ⟨363330, by rfl⟩ : syracuseStep 3875525 = 726661) (by norm_num)
theorem B1254109 : Blo 742328 1254109 := bbase (se 3 (by rfl) ⟨235145, by rfl⟩ : syracuseStep 1254109 = 470291) (by norm_num)
theorem B1254197 : Blo 742328 1254197 := bbase (se 5 (by rfl) ⟨58790, by rfl⟩ : syracuseStep 1254197 = 117581) (by norm_num)
theorem B828245 : Blo 742328 828245 := bbase (se 9 (by rfl) ⟨2426, by rfl⟩ : syracuseStep 828245 = 4853) (by norm_num)
theorem B1057637 : Blo 742328 1057637 := bbase (se 4 (by rfl) ⟨99153, by rfl⟩ : syracuseStep 1057637 = 198307) (by norm_num)
theorem B893857 : Blo 742328 893857 := bbase (se 2 (by rfl) ⟨335196, by rfl⟩ : syracuseStep 893857 = 670393) (by norm_num)
theorem B1254325 : Blo 742328 1254325 := bbase (se 5 (by rfl) ⟨58796, by rfl⟩ : syracuseStep 1254325 = 117593) (by norm_num)
theorem B893885 : Blo 742328 893885 := bbase (se 3 (by rfl) ⟨167603, by rfl⟩ : syracuseStep 893885 = 335207) (by norm_num)
theorem B795641 : Blo 742328 795641 := bbase (se 2 (by rfl) ⟨298365, by rfl⟩ : syracuseStep 795641 = 596731) (by norm_num)
theorem B1254413 : Blo 742328 1254413 := bbase (se 3 (by rfl) ⟨235202, by rfl⟩ : syracuseStep 1254413 = 470405) (by norm_num)
theorem B795701 : Blo 742328 795701 := bbase (se 5 (by rfl) ⟨37298, by rfl⟩ : syracuseStep 795701 = 74597) (by norm_num)
theorem B1254541 : Blo 742328 1254541 := bbase (se 3 (by rfl) ⟨235226, by rfl⟩ : syracuseStep 1254541 = 470453) (by norm_num)
theorem B795829 : Blo 742328 795829 := bbase (se 5 (by rfl) ⟨37304, by rfl⟩ : syracuseStep 795829 = 74609) (by norm_num)
theorem B1254629 : Blo 742328 1254629 := bbase (se 4 (by rfl) ⟨117621, by rfl⟩ : syracuseStep 1254629 = 235243) (by norm_num)
theorem B1254757 : Blo 742328 1254757 := bbase (se 4 (by rfl) ⟨117633, by rfl⟩ : syracuseStep 1254757 = 235267) (by norm_num)
theorem B1058189 : Blo 742328 1058189 := bbase (se 3 (by rfl) ⟨198410, by rfl⟩ : syracuseStep 1058189 = 396821) (by norm_num)
theorem B2827669 : Blo 742328 2827669 := bbase (se 6 (by rfl) ⟨66273, by rfl⟩ : syracuseStep 2827669 = 132547) (by norm_num)
theorem B894385 : Blo 742328 894385 := bbase (se 2 (by rfl) ⟨335394, by rfl⟩ : syracuseStep 894385 = 670789) (by norm_num)
theorem B1254845 : Blo 742328 1254845 := bbase (se 3 (by rfl) ⟨235283, by rfl⟩ : syracuseStep 1254845 = 470567) (by norm_num)
theorem B1254973 : Blo 742328 1254973 := bbase (se 3 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 1254973 = 470615) (by norm_num)
theorem B796273 : Blo 742328 796273 := bbase (se 2 (by rfl) ⟨298602, by rfl⟩ : syracuseStep 796273 = 597205) (by norm_num)
theorem B763537 : Blo 742328 763537 := bbase (se 2 (by rfl) ⟨286326, by rfl⟩ : syracuseStep 763537 = 572653) (by norm_num)
theorem B1255061 : Blo 742328 1255061 := bbase (se 6 (by rfl) ⟨29415, by rfl⟩ : syracuseStep 1255061 = 58831) (by norm_num)
theorem B1189541 : Blo 742328 1189541 := bbase (se 4 (by rfl) ⟨111519, by rfl⟩ : syracuseStep 1189541 = 223039) (by norm_num)
theorem B2827973 : Blo 742328 2827973 := bbase (se 4 (by rfl) ⟨265122, by rfl⟩ : syracuseStep 2827973 = 530245) (by norm_num)
theorem B24094421 : Blo 742328 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B796393 : Blo 742328 796393 := bbase (se 2 (by rfl) ⟨298647, by rfl⟩ : syracuseStep 796393 = 597295) (by norm_num)
theorem B1255189 : Blo 742328 1255189 := bbase (se 6 (by rfl) ⟨29418, by rfl⟩ : syracuseStep 1255189 = 58837) (by norm_num)
theorem B1189669 : Blo 742328 1189669 := bbase (se 4 (by rfl) ⟨111531, by rfl⟩ : syracuseStep 1189669 = 223063) (by norm_num)
theorem B4237109 : Blo 742328 4237109 := bbase (se 5 (by rfl) ⟨198614, by rfl⟩ : syracuseStep 4237109 = 397229) (by norm_num)
theorem B1255277 : Blo 742328 1255277 := bbase (se 3 (by rfl) ⟨235364, by rfl⟩ : syracuseStep 1255277 = 470729) (by norm_num)
theorem B796645 : Blo 742328 796645 := bbase (se 4 (by rfl) ⟨74685, by rfl⟩ : syracuseStep 796645 = 149371) (by norm_num)
theorem B796649 : Blo 742328 796649 := bbase (se 2 (by rfl) ⟨298743, by rfl⟩ : syracuseStep 796649 = 597487) (by norm_num)
theorem B1255405 : Blo 742328 1255405 := bbase (se 3 (by rfl) ⟨235388, by rfl⟩ : syracuseStep 1255405 = 470777) (by norm_num)
theorem B1255493 : Blo 742328 1255493 := bbase (se 4 (by rfl) ⟨117702, by rfl⟩ : syracuseStep 1255493 = 235405) (by norm_num)
theorem B1058941 : Blo 742328 1058941 := bbase (se 3 (by rfl) ⟨198551, by rfl⟩ : syracuseStep 1058941 = 397103) (by norm_num)
theorem B1190053 : Blo 742328 1190053 := bbase (se 4 (by rfl) ⟨111567, by rfl⟩ : syracuseStep 1190053 = 223135) (by norm_num)
theorem B1255621 : Blo 742328 1255621 := bbase (se 4 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 1255621 = 235429) (by norm_num)
theorem B1255709 : Blo 742328 1255709 := bbase (se 3 (by rfl) ⟨235445, by rfl⟩ : syracuseStep 1255709 = 470891) (by norm_num)
theorem B12069269 : Blo 742328 12069269 := bbase (se 6 (by rfl) ⟨282873, by rfl⟩ : syracuseStep 12069269 = 565747) (by norm_num)
theorem B1255837 : Blo 742328 1255837 := bbase (se 3 (by rfl) ⟨235469, by rfl⟩ : syracuseStep 1255837 = 470939) (by norm_num)
theorem B1190309 : Blo 742328 1190309 := bbase (se 4 (by rfl) ⟨111591, by rfl⟩ : syracuseStep 1190309 = 223183) (by norm_num)
theorem B1255925 : Blo 742328 1255925 := bbase (se 5 (by rfl) ⟨58871, by rfl⟩ : syracuseStep 1255925 = 117743) (by norm_num)
theorem B895573 : Blo 742328 895573 := bbase (se 8 (by rfl) ⟨5247, by rfl⟩ : syracuseStep 895573 = 10495) (by norm_num)
theorem B1256053 : Blo 742328 1256053 := bbase (se 5 (by rfl) ⟨58877, by rfl⟩ : syracuseStep 1256053 = 117755) (by norm_num)
theorem B1288885 : Blo 742328 1288885 := bbase (se 5 (by rfl) ⟨60416, by rfl⟩ : syracuseStep 1288885 = 120833) (by norm_num)
theorem B1256141 : Blo 742328 1256141 := bbase (se 3 (by rfl) ⟨235526, by rfl⟩ : syracuseStep 1256141 = 471053) (by norm_num)
theorem B3025621 : Blo 742328 3025621 := bbase (se 7 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 3025621 = 70913) (by norm_num)
theorem B895765 : Blo 742328 895765 := bbase (se 6 (by rfl) ⟨20994, by rfl⟩ : syracuseStep 895765 = 41989) (by norm_num)
theorem B3025685 : Blo 742328 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B1256269 : Blo 742328 1256269 := bbase (se 3 (by rfl) ⟨235550, by rfl⟩ : syracuseStep 1256269 = 471101) (by norm_num)
theorem B895865 : Blo 742328 895865 := bbase (se 2 (by rfl) ⟨335949, by rfl⟩ : syracuseStep 895865 = 671899) (by norm_num)
theorem B6433685 : Blo 742328 6433685 := bbase (se 6 (by rfl) ⟨150789, by rfl⟩ : syracuseStep 6433685 = 301579) (by norm_num)
theorem B1059733 : Blo 742328 1059733 := bbase (se 6 (by rfl) ⟨24837, by rfl⟩ : syracuseStep 1059733 = 49675) (by norm_num)
theorem B1256357 : Blo 742328 1256357 := bbase (se 4 (by rfl) ⟨117783, by rfl⟩ : syracuseStep 1256357 = 235567) (by norm_num)
theorem B1256485 : Blo 742328 1256485 := bbase (se 4 (by rfl) ⟨117795, by rfl⟩ : syracuseStep 1256485 = 235591) (by norm_num)
theorem B1879109 : Blo 742328 1879109 := bbase (se 4 (by rfl) ⟨176166, by rfl⟩ : syracuseStep 1879109 = 352333) (by norm_num)
theorem B1256573 : Blo 742328 1256573 := bbase (se 3 (by rfl) ⟨235607, by rfl⟩ : syracuseStep 1256573 = 471215) (by norm_num)
theorem B1060069 : Blo 742328 1060069 := bbase (se 4 (by rfl) ⟨99381, by rfl⟩ : syracuseStep 1060069 = 198763) (by norm_num)
theorem B1256701 : Blo 742328 1256701 := bbase (se 3 (by rfl) ⟨235631, by rfl⟩ : syracuseStep 1256701 = 471263) (by norm_num)
theorem B1879301 : Blo 742328 1879301 := bbase (se 4 (by rfl) ⟨176184, by rfl⟩ : syracuseStep 1879301 = 352369) (by norm_num)
theorem B1191181 : Blo 742328 1191181 := bbase (se 3 (by rfl) ⟨223346, by rfl⟩ : syracuseStep 1191181 = 446693) (by norm_num)
theorem B1256789 : Blo 742328 1256789 := bbase (se 11 (by rfl) ⟨920, by rfl⟩ : syracuseStep 1256789 = 1841) (by norm_num)
theorem B1191277 : Blo 742328 1191277 := bbase (se 3 (by rfl) ⟨223364, by rfl⟩ : syracuseStep 1191277 = 446729) (by norm_num)
theorem B1060285 : Blo 742328 1060285 := bbase (se 3 (by rfl) ⟨198803, by rfl⟩ : syracuseStep 1060285 = 397607) (by norm_num)
theorem B1256917 : Blo 742328 1256917 := bbase (se 7 (by rfl) ⟨14729, by rfl⟩ : syracuseStep 1256917 = 29459) (by norm_num)
theorem B1191437 : Blo 742328 1191437 := bbase (se 3 (by rfl) ⟨223394, by rfl⟩ : syracuseStep 1191437 = 446789) (by norm_num)
theorem B1257005 : Blo 742328 1257005 := bbase (se 3 (by rfl) ⟨235688, by rfl⟩ : syracuseStep 1257005 = 471377) (by norm_num)
theorem B1879645 : Blo 742328 1879645 := bbase (se 3 (by rfl) ⟨352433, by rfl⟩ : syracuseStep 1879645 = 704867) (by norm_num)
theorem B1257133 : Blo 742328 1257133 := bbase (se 3 (by rfl) ⟨235712, by rfl⟩ : syracuseStep 1257133 = 471425) (by norm_num)
theorem B1879757 : Blo 742328 1879757 := bbase (se 3 (by rfl) ⟨352454, by rfl⟩ : syracuseStep 1879757 = 704909) (by norm_num)
theorem B2010853 : Blo 742328 2010853 := bbase (se 4 (by rfl) ⟨188517, by rfl⟩ : syracuseStep 2010853 = 377035) (by norm_num)
theorem B1257221 : Blo 742328 1257221 := bbase (se 4 (by rfl) ⟨117864, by rfl⟩ : syracuseStep 1257221 = 235729) (by norm_num)
theorem B2830085 : Blo 742328 2830085 := bbase (se 4 (by rfl) ⟨265320, by rfl⟩ : syracuseStep 2830085 = 530641) (by norm_num)
theorem B1060661 : Blo 742328 1060661 := bbase (se 5 (by rfl) ⟨49718, by rfl⟩ : syracuseStep 1060661 = 99437) (by norm_num)
theorem B1257349 : Blo 742328 1257349 := bbase (se 4 (by rfl) ⟨117876, by rfl⟩ : syracuseStep 1257349 = 235753) (by norm_num)
theorem B1879949 : Blo 742328 1879949 := bbase (se 3 (by rfl) ⟨352490, by rfl⟩ : syracuseStep 1879949 = 704981) (by norm_num)
theorem B1224661 : Blo 742328 1224661 := bbase (se 7 (by rfl) ⟨14351, by rfl⟩ : syracuseStep 1224661 = 28703) (by norm_num)
theorem B4239317 : Blo 742328 4239317 := bbase (se 7 (by rfl) ⟨49679, by rfl⟩ : syracuseStep 4239317 = 99359) (by norm_num)
theorem B1257437 : Blo 742328 1257437 := bbase (se 3 (by rfl) ⟨235769, by rfl⟩ : syracuseStep 1257437 = 471539) (by norm_num)
theorem B2830373 : Blo 742328 2830373 := bbase (se 4 (by rfl) ⟨265347, by rfl⟩ : syracuseStep 2830373 = 530695) (by norm_num)
theorem B1257565 : Blo 742328 1257565 := bbase (se 3 (by rfl) ⟨235793, by rfl⟩ : syracuseStep 1257565 = 471587) (by norm_num)
theorem B1257653 : Blo 742328 1257653 := bbase (se 5 (by rfl) ⟨58952, by rfl⟩ : syracuseStep 1257653 = 117905) (by norm_num)
theorem B5353685 : Blo 742328 5353685 := bbase (se 7 (by rfl) ⟨62738, by rfl⟩ : syracuseStep 5353685 = 125477) (by norm_num)
theorem B1880293 : Blo 742328 1880293 := bbase (se 4 (by rfl) ⟨176277, by rfl⟩ : syracuseStep 1880293 = 352555) (by norm_num)
theorem B1257781 : Blo 742328 1257781 := bbase (se 5 (by rfl) ⟨58958, by rfl⟩ : syracuseStep 1257781 = 117917) (by norm_num)
theorem B1880405 : Blo 742328 1880405 := bbase (se 10 (by rfl) ⟨2754, by rfl⟩ : syracuseStep 1880405 = 5509) (by norm_num)
theorem B7647605 : Blo 742328 7647605 := bbase (se 5 (by rfl) ⟨358481, by rfl⟩ : syracuseStep 7647605 = 716963) (by norm_num)
theorem B1585541 : Blo 742328 1585541 := bbase (se 4 (by rfl) ⟨148644, by rfl⟩ : syracuseStep 1585541 = 297289) (by norm_num)
theorem B1257869 : Blo 742328 1257869 := bbase (se 3 (by rfl) ⟨235850, by rfl⟩ : syracuseStep 1257869 = 471701) (by norm_num)
theorem B1356277 : Blo 742328 1356277 := bbase (se 5 (by rfl) ⟨63575, by rfl⟩ : syracuseStep 1356277 = 127151) (by norm_num)
theorem B1257997 : Blo 742328 1257997 := bbase (se 3 (by rfl) ⟨235874, by rfl⟩ : syracuseStep 1257997 = 471749) (by norm_num)
theorem B1880597 : Blo 742328 1880597 := bbase (se 6 (by rfl) ⟨44076, by rfl⟩ : syracuseStep 1880597 = 88153) (by norm_num)
theorem B7156309 : Blo 742328 7156309 := bbase (se 8 (by rfl) ⟨41931, by rfl⟩ : syracuseStep 7156309 = 83863) (by norm_num)
theorem B1258085 : Blo 742328 1258085 := bbase (se 4 (by rfl) ⟨117945, by rfl⟩ : syracuseStep 1258085 = 235891) (by norm_num)
theorem B1913453 : Blo 742328 1913453 := bbase (se 3 (by rfl) ⟨358772, by rfl⟩ : syracuseStep 1913453 = 717545) (by norm_num)
theorem B1192565 : Blo 742328 1192565 := bbase (se 5 (by rfl) ⟨55901, by rfl⟩ : syracuseStep 1192565 = 111803) (by norm_num)
theorem B1258213 : Blo 742328 1258213 := bbase (se 4 (by rfl) ⟨117957, by rfl⟩ : syracuseStep 1258213 = 235915) (by norm_num)
theorem B1585909 : Blo 742328 1585909 := bbase (se 5 (by rfl) ⟨74339, by rfl⟩ : syracuseStep 1585909 = 148679) (by norm_num)
theorem B13611797 : Blo 742328 13611797 := bbase (se 6 (by rfl) ⟨319026, by rfl⟩ : syracuseStep 13611797 = 638053) (by norm_num)
theorem B1258301 : Blo 742328 1258301 := bbase (se 3 (by rfl) ⟨235931, by rfl⟩ : syracuseStep 1258301 = 471863) (by norm_num)
theorem B3683141 : Blo 742328 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B1880941 : Blo 742328 1880941 := bbase (se 3 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 1880941 = 705353) (by norm_num)
theorem B1258429 : Blo 742328 1258429 := bbase (se 3 (by rfl) ⟨235955, by rfl⟩ : syracuseStep 1258429 = 471911) (by norm_num)
theorem B1881053 : Blo 742328 1881053 := bbase (se 3 (by rfl) ⟨352697, by rfl⟩ : syracuseStep 1881053 = 705395) (by norm_num)
theorem B1258517 : Blo 742328 1258517 := bbase (se 6 (by rfl) ⟨29496, by rfl⟩ : syracuseStep 1258517 = 58993) (by norm_num)
theorem B1193077 : Blo 742328 1193077 := bbase (se 5 (by rfl) ⟨55925, by rfl⟩ : syracuseStep 1193077 = 111851) (by norm_num)
theorem B1258645 : Blo 742328 1258645 := bbase (se 6 (by rfl) ⟨29499, by rfl⟩ : syracuseStep 1258645 = 58999) (by norm_num)
theorem B1881245 : Blo 742328 1881245 := bbase (se 3 (by rfl) ⟨352733, by rfl⟩ : syracuseStep 1881245 = 705467) (by norm_num)
theorem B2012357 : Blo 742328 2012357 := bbase (se 4 (by rfl) ⟨188658, by rfl⟩ : syracuseStep 2012357 = 377317) (by norm_num)
theorem B2831557 : Blo 742328 2831557 := bbase (se 4 (by rfl) ⟨265458, by rfl⟩ : syracuseStep 2831557 = 530917) (by norm_num)
theorem B1062085 : Blo 742328 1062085 := bbase (se 4 (by rfl) ⟨99570, by rfl⟩ : syracuseStep 1062085 = 199141) (by norm_num)
theorem B1258733 : Blo 742328 1258733 := bbase (se 3 (by rfl) ⟨236012, by rfl⟩ : syracuseStep 1258733 = 472025) (by norm_num)
theorem B5649749 : Blo 742328 5649749 := bbase (se 13 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 5649749 = 2069) (by norm_num)
theorem B1258861 : Blo 742328 1258861 := bbase (se 3 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 1258861 = 472073) (by norm_num)
theorem B1258949 : Blo 742328 1258949 := bbase (se 4 (by rfl) ⟨118026, by rfl⟩ : syracuseStep 1258949 = 236053) (by norm_num)
theorem B1881589 : Blo 742328 1881589 := bbase (se 5 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 1881589 = 176399) (by norm_num)
theorem B2831861 : Blo 742328 2831861 := bbase (se 5 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 2831861 = 265487) (by norm_num)
theorem B3814933 : Blo 742328 3814933 := bbase (se 6 (by rfl) ⟨89412, by rfl⟩ : syracuseStep 3814933 = 178825) (by norm_num)
theorem B1259077 : Blo 742328 1259077 := bbase (se 4 (by rfl) ⟨118038, by rfl⟩ : syracuseStep 1259077 = 236077) (by norm_num)
theorem B1881701 : Blo 742328 1881701 := bbase (se 4 (by rfl) ⟨176409, by rfl⟩ : syracuseStep 1881701 = 352819) (by norm_num)
theorem B1259165 : Blo 742328 1259165 := bbase (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) (by norm_num)
theorem B1259293 : Blo 742328 1259293 := bbase (se 3 (by rfl) ⟨236117, by rfl⟩ : syracuseStep 1259293 = 472235) (by norm_num)
theorem B1881893 : Blo 742328 1881893 := bbase (se 4 (by rfl) ⟨176427, by rfl⟩ : syracuseStep 1881893 = 352855) (by norm_num)
theorem B1259381 : Blo 742328 1259381 := bbase (se 5 (by rfl) ⟨59033, by rfl⟩ : syracuseStep 1259381 = 118067) (by norm_num)
theorem B3586133 : Blo 742328 3586133 := bbase (se 8 (by rfl) ⟨21012, by rfl⟩ : syracuseStep 3586133 = 42025) (by norm_num)
theorem B1194077 : Blo 742328 1194077 := bbase (se 3 (by rfl) ⟨223889, by rfl⟩ : syracuseStep 1194077 = 447779) (by norm_num)
theorem B1882237 : Blo 742328 1882237 := bbase (se 3 (by rfl) ⟨352919, by rfl⟩ : syracuseStep 1882237 = 705839) (by norm_num)
theorem B1587413 : Blo 742328 1587413 := bbase (se 7 (by rfl) ⟨18602, by rfl⟩ : syracuseStep 1587413 = 37205) (by norm_num)
theorem B1194205 : Blo 742328 1194205 := bbase (se 3 (by rfl) ⟨223913, by rfl⟩ : syracuseStep 1194205 = 447827) (by norm_num)
theorem B1882349 : Blo 742328 1882349 := bbase (se 3 (by rfl) ⟨352940, by rfl⟩ : syracuseStep 1882349 = 705881) (by norm_num)
theorem B1194269 : Blo 742328 1194269 := bbase (se 3 (by rfl) ⟨223925, by rfl⟩ : syracuseStep 1194269 = 447851) (by norm_num)
theorem B36256085 : Blo 742328 36256085 := bbase (se 10 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 36256085 = 106219) (by norm_num)
theorem B1587557 : Blo 742328 1587557 := bbase (se 4 (by rfl) ⟨148833, by rfl⟩ : syracuseStep 1587557 = 297667) (by norm_num)
theorem B1358245 : Blo 742328 1358245 := bbase (se 4 (by rfl) ⟨127335, by rfl⟩ : syracuseStep 1358245 = 254671) (by norm_num)
theorem B1882541 : Blo 742328 1882541 := bbase (se 3 (by rfl) ⟨352976, by rfl⟩ : syracuseStep 1882541 = 705953) (by norm_num)
theorem B1129037 : Blo 742328 1129037 := bbase (se 3 (by rfl) ⟨211694, by rfl⟩ : syracuseStep 1129037 = 423389) (by norm_num)
theorem B1587917 : Blo 742328 1587917 := bbase (se 3 (by rfl) ⟨297734, by rfl⟩ : syracuseStep 1587917 = 595469) (by norm_num)
theorem B1817309 : Blo 742328 1817309 := bbase (se 3 (by rfl) ⟨340745, by rfl⟩ : syracuseStep 1817309 = 681491) (by norm_num)
theorem B1882885 : Blo 742328 1882885 := bbase (se 4 (by rfl) ⟨176520, by rfl⟩ : syracuseStep 1882885 = 353041) (by norm_num)
theorem B1817405 : Blo 742328 1817405 := bbase (se 3 (by rfl) ⟨340763, by rfl⟩ : syracuseStep 1817405 = 681527) (by norm_num)
theorem B1882997 : Blo 742328 1882997 := bbase (se 5 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 1882997 = 176531) (by norm_num)
theorem B2505653 : Blo 742328 2505653 := bbase (se 5 (by rfl) ⟨117452, by rfl⟩ : syracuseStep 2505653 = 234905) (by norm_num)
theorem B7650229 : Blo 742328 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B1883189 : Blo 742328 1883189 := bbase (se 5 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 1883189 = 176549) (by norm_num)
theorem B2506085 : Blo 742328 2506085 := bbase (se 4 (by rfl) ⟨234945, by rfl⟩ : syracuseStep 2506085 = 469891) (by norm_num)
theorem B1883533 : Blo 742328 1883533 := bbase (se 3 (by rfl) ⟨353162, by rfl⟩ : syracuseStep 1883533 = 706325) (by norm_num)
theorem B1785253 : Blo 742328 1785253 := bbase (se 4 (by rfl) ⟨167367, by rfl⟩ : syracuseStep 1785253 = 334735) (by norm_num)
theorem B1883645 : Blo 742328 1883645 := bbase (se 3 (by rfl) ⟨353183, by rfl⟩ : syracuseStep 1883645 = 706367) (by norm_num)
theorem B2014789 : Blo 742328 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B835141 : Blo 742328 835141 := bbase (se 4 (by rfl) ⟨78294, by rfl⟩ : syracuseStep 835141 = 156589) (by norm_num)
theorem B1588805 : Blo 742328 1588805 := bbase (se 4 (by rfl) ⟨148950, by rfl⟩ : syracuseStep 1588805 = 297901) (by norm_num)
theorem B835177 : Blo 742328 835177 := bbase (se 2 (by rfl) ⟨313191, by rfl⟩ : syracuseStep 835177 = 626383) (by norm_num)
theorem B835213 : Blo 742328 835213 := bbase (se 3 (by rfl) ⟨156602, by rfl⟩ : syracuseStep 835213 = 313205) (by norm_num)
theorem B835249 : Blo 742328 835249 := bbase (se 2 (by rfl) ⟨313218, by rfl⟩ : syracuseStep 835249 = 626437) (by norm_num)
theorem B1883837 : Blo 742328 1883837 := bbase (se 3 (by rfl) ⟨353219, by rfl⟩ : syracuseStep 1883837 = 706439) (by norm_num)
theorem B835285 : Blo 742328 835285 := bbase (se 7 (by rfl) ⟨9788, by rfl⟩ : syracuseStep 835285 = 19577) (by norm_num)
theorem B835321 : Blo 742328 835321 := bbase (se 2 (by rfl) ⟨313245, by rfl⟩ : syracuseStep 835321 = 626491) (by norm_num)
theorem B2506517 : Blo 742328 2506517 := bbase (se 6 (by rfl) ⟨58746, by rfl⟩ : syracuseStep 2506517 = 117493) (by norm_num)
theorem B835357 : Blo 742328 835357 := bbase (se 3 (by rfl) ⟨156629, by rfl⟩ : syracuseStep 835357 = 313259) (by norm_num)
theorem B1589053 : Blo 742328 1589053 := bbase (se 3 (by rfl) ⟨297947, by rfl⟩ : syracuseStep 1589053 = 595895) (by norm_num)
theorem B835393 : Blo 742328 835393 := bbase (se 2 (by rfl) ⟨313272, by rfl⟩ : syracuseStep 835393 = 626545) (by norm_num)
theorem B835429 : Blo 742328 835429 := bbase (se 4 (by rfl) ⟨78321, by rfl⟩ : syracuseStep 835429 = 156643) (by norm_num)
theorem B835465 : Blo 742328 835465 := bbase (se 2 (by rfl) ⟨313299, by rfl⟩ : syracuseStep 835465 = 626599) (by norm_num)
theorem B835501 : Blo 742328 835501 := bbase (se 3 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 835501 = 313313) (by norm_num)
theorem B835537 : Blo 742328 835537 := bbase (se 2 (by rfl) ⟨313326, by rfl⟩ : syracuseStep 835537 = 626653) (by norm_num)
theorem B835573 : Blo 742328 835573 := bbase (se 5 (by rfl) ⟨39167, by rfl⟩ : syracuseStep 835573 = 78335) (by norm_num)
theorem B1884181 : Blo 742328 1884181 := bbase (se 6 (by rfl) ⟨44160, by rfl⟩ : syracuseStep 1884181 = 88321) (by norm_num)
theorem B835609 : Blo 742328 835609 := bbase (se 2 (by rfl) ⟨313353, by rfl⟩ : syracuseStep 835609 = 626707) (by norm_num)
theorem B4767797 : Blo 742328 4767797 := bbase (se 5 (by rfl) ⟨223490, by rfl⟩ : syracuseStep 4767797 = 446981) (by norm_num)
theorem B835645 : Blo 742328 835645 := bbase (se 3 (by rfl) ⟨156683, by rfl⟩ : syracuseStep 835645 = 313367) (by norm_num)
theorem B1785925 : Blo 742328 1785925 := bbase (se 4 (by rfl) ⟨167430, by rfl⟩ : syracuseStep 1785925 = 334861) (by norm_num)
theorem B835681 : Blo 742328 835681 := bbase (se 2 (by rfl) ⟨313380, by rfl⟩ : syracuseStep 835681 = 626761) (by norm_num)
theorem B835717 : Blo 742328 835717 := bbase (se 4 (by rfl) ⟨78348, by rfl⟩ : syracuseStep 835717 = 156697) (by norm_num)
theorem B1884293 : Blo 742328 1884293 := bbase (se 4 (by rfl) ⟨176652, by rfl⟩ : syracuseStep 1884293 = 353305) (by norm_num)
theorem B835753 : Blo 742328 835753 := bbase (se 2 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 835753 = 626815) (by norm_num)
theorem B2506949 : Blo 742328 2506949 := bbase (se 4 (by rfl) ⟨235026, by rfl⟩ : syracuseStep 2506949 = 470053) (by norm_num)
theorem B835789 : Blo 742328 835789 := bbase (se 3 (by rfl) ⟨156710, by rfl⟩ : syracuseStep 835789 = 313421) (by norm_num)
theorem B835825 : Blo 742328 835825 := bbase (se 2 (by rfl) ⟨313434, by rfl⟩ : syracuseStep 835825 = 626869) (by norm_num)
theorem B5095669 : Blo 742328 5095669 := bbase (se 5 (by rfl) ⟨238859, by rfl⟩ : syracuseStep 5095669 = 477719) (by norm_num)
theorem B835861 : Blo 742328 835861 := bbase (se 6 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 835861 = 39181) (by norm_num)
theorem B1786157 : Blo 742328 1786157 := bbase (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) (by norm_num)
theorem B1589557 : Blo 742328 1589557 := bbase (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) (by norm_num)
theorem B835897 : Blo 742328 835897 := bbase (se 2 (by rfl) ⟨313461, by rfl⟩ : syracuseStep 835897 = 626923) (by norm_num)
theorem B1884485 : Blo 742328 1884485 := bbase (se 4 (by rfl) ⟨176670, by rfl⟩ : syracuseStep 1884485 = 353341) (by norm_num)
theorem B835933 : Blo 742328 835933 := bbase (se 3 (by rfl) ⟨156737, by rfl⟩ : syracuseStep 835933 = 313475) (by norm_num)
theorem B835969 : Blo 742328 835969 := bbase (se 2 (by rfl) ⟨313488, by rfl⟩ : syracuseStep 835969 = 626977) (by norm_num)
theorem B836005 : Blo 742328 836005 := bbase (se 4 (by rfl) ⟨78375, by rfl⟩ : syracuseStep 836005 = 156751) (by norm_num)
theorem B1786301 : Blo 742328 1786301 := bbase (se 3 (by rfl) ⟨334931, by rfl⟩ : syracuseStep 1786301 = 669863) (by norm_num)
theorem B836041 : Blo 742328 836041 := bbase (se 2 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 836041 = 627031) (by norm_num)
theorem B836077 : Blo 742328 836077 := bbase (se 3 (by rfl) ⟨156764, by rfl⟩ : syracuseStep 836077 = 313529) (by norm_num)
theorem B1786349 : Blo 742328 1786349 := bbase (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) (by norm_num)
theorem B836113 : Blo 742328 836113 := bbase (se 2 (by rfl) ⟨313542, by rfl⟩ : syracuseStep 836113 = 627085) (by norm_num)
theorem B836149 : Blo 742328 836149 := bbase (se 5 (by rfl) ⟨39194, by rfl⟩ : syracuseStep 836149 = 78389) (by norm_num)
theorem B836185 : Blo 742328 836185 := bbase (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) (by norm_num)
theorem B2507381 : Blo 742328 2507381 := bbase (se 5 (by rfl) ⟨117533, by rfl⟩ : syracuseStep 2507381 = 235067) (by norm_num)
theorem B836221 : Blo 742328 836221 := bbase (se 3 (by rfl) ⟨156791, by rfl⟩ : syracuseStep 836221 = 313583) (by norm_num)
theorem B1884829 : Blo 742328 1884829 := bbase (se 3 (by rfl) ⟨353405, by rfl⟩ : syracuseStep 1884829 = 706811) (by norm_num)
theorem B836257 : Blo 742328 836257 := bbase (se 2 (by rfl) ⟨313596, by rfl⟩ : syracuseStep 836257 = 627193) (by norm_num)
theorem B836293 : Blo 742328 836293 := bbase (se 4 (by rfl) ⟨78402, by rfl⟩ : syracuseStep 836293 = 156805) (by norm_num)
theorem B836329 : Blo 742328 836329 := bbase (se 2 (by rfl) ⟨313623, by rfl⟩ : syracuseStep 836329 = 627247) (by norm_num)
theorem B836365 : Blo 742328 836365 := bbase (se 3 (by rfl) ⟨156818, by rfl⟩ : syracuseStep 836365 = 313637) (by norm_num)
theorem B1786637 : Blo 742328 1786637 := bbase (se 3 (by rfl) ⟨334994, by rfl⟩ : syracuseStep 1786637 = 669989) (by norm_num)
theorem B1884941 : Blo 742328 1884941 := bbase (se 3 (by rfl) ⟨353426, by rfl⟩ : syracuseStep 1884941 = 706853) (by norm_num)
theorem B836401 : Blo 742328 836401 := bbase (se 2 (by rfl) ⟨313650, by rfl⟩ : syracuseStep 836401 = 627301) (by norm_num)
theorem B836437 : Blo 742328 836437 := bbase (se 9 (by rfl) ⟨2450, by rfl⟩ : syracuseStep 836437 = 4901) (by norm_num)
theorem B836473 : Blo 742328 836473 := bbase (se 2 (by rfl) ⟨313677, by rfl⟩ : syracuseStep 836473 = 627355) (by norm_num)
theorem B836509 : Blo 742328 836509 := bbase (se 3 (by rfl) ⟨156845, by rfl⟩ : syracuseStep 836509 = 313691) (by norm_num)
theorem B836545 : Blo 742328 836545 := bbase (se 2 (by rfl) ⟨313704, by rfl⟩ : syracuseStep 836545 = 627409) (by norm_num)
theorem B1885133 : Blo 742328 1885133 := bbase (se 3 (by rfl) ⟨353462, by rfl⟩ : syracuseStep 1885133 = 706925) (by norm_num)
theorem B836581 : Blo 742328 836581 := bbase (se 4 (by rfl) ⟨78429, by rfl⟩ : syracuseStep 836581 = 156859) (by norm_num)
theorem B836617 : Blo 742328 836617 := bbase (se 2 (by rfl) ⟨313731, by rfl⟩ : syracuseStep 836617 = 627463) (by norm_num)
theorem B2507813 : Blo 742328 2507813 := bbase (se 4 (by rfl) ⟨235107, by rfl⟩ : syracuseStep 2507813 = 470215) (by norm_num)
theorem B836653 : Blo 742328 836653 := bbase (se 3 (by rfl) ⟨156872, by rfl⟩ : syracuseStep 836653 = 313745) (by norm_num)
theorem B836689 : Blo 742328 836689 := bbase (se 2 (by rfl) ⟨313758, by rfl⟩ : syracuseStep 836689 = 627517) (by norm_num)
theorem B836725 : Blo 742328 836725 := bbase (se 5 (by rfl) ⟨39221, by rfl⟩ : syracuseStep 836725 = 78443) (by norm_num)
theorem B2114693 : Blo 742328 2114693 := bbase (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) (by norm_num)
theorem B2016389 : Blo 742328 2016389 := bbase (se 4 (by rfl) ⟨189036, by rfl⟩ : syracuseStep 2016389 = 378073) (by norm_num)
theorem B836761 : Blo 742328 836761 := bbase (se 2 (by rfl) ⟨313785, by rfl⟩ : syracuseStep 836761 = 627571) (by norm_num)
theorem B1590445 : Blo 742328 1590445 := bbase (se 3 (by rfl) ⟨298208, by rfl⟩ : syracuseStep 1590445 = 596417) (by norm_num)
theorem B836797 : Blo 742328 836797 := bbase (se 3 (by rfl) ⟨156899, by rfl⟩ : syracuseStep 836797 = 313799) (by norm_num)
theorem B836833 : Blo 742328 836833 := bbase (se 2 (by rfl) ⟨313812, by rfl⟩ : syracuseStep 836833 = 627625) (by norm_num)
theorem B836869 : Blo 742328 836869 := bbase (se 4 (by rfl) ⟨78456, by rfl⟩ : syracuseStep 836869 = 156913) (by norm_num)
theorem B804125 : Blo 742328 804125 := bbase (se 3 (by rfl) ⟨150773, by rfl⟩ : syracuseStep 804125 = 301547) (by norm_num)
theorem B1885477 : Blo 742328 1885477 := bbase (se 4 (by rfl) ⟨176763, by rfl⟩ : syracuseStep 1885477 = 353527) (by norm_num)
theorem B836905 : Blo 742328 836905 := bbase (se 2 (by rfl) ⟨313839, by rfl⟩ : syracuseStep 836905 = 627679) (by norm_num)
theorem B836941 : Blo 742328 836941 := bbase (se 3 (by rfl) ⟨156926, by rfl⟩ : syracuseStep 836941 = 313853) (by norm_num)
theorem B836977 : Blo 742328 836977 := bbase (se 2 (by rfl) ⟨313866, by rfl⟩ : syracuseStep 836977 = 627733) (by norm_num)
theorem B837013 : Blo 742328 837013 := bbase (se 6 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 837013 = 39235) (by norm_num)
theorem B1885589 : Blo 742328 1885589 := bbase (se 6 (by rfl) ⟨44193, by rfl⟩ : syracuseStep 1885589 = 88387) (by norm_num)
theorem B837049 : Blo 742328 837049 := bbase (se 2 (by rfl) ⟨313893, by rfl⟩ : syracuseStep 837049 = 627787) (by norm_num)
theorem B2508245 : Blo 742328 2508245 := bbase (se 7 (by rfl) ⟨29393, by rfl⟩ : syracuseStep 2508245 = 58787) (by norm_num)
theorem B837085 : Blo 742328 837085 := bbase (se 3 (by rfl) ⟨156953, by rfl⟩ : syracuseStep 837085 = 313907) (by norm_num)
theorem B837121 : Blo 742328 837121 := bbase (se 2 (by rfl) ⟨313920, by rfl⟩ : syracuseStep 837121 = 627841) (by norm_num)
theorem B837157 : Blo 742328 837157 := bbase (se 4 (by rfl) ⟨78483, by rfl⟩ : syracuseStep 837157 = 156967) (by norm_num)
theorem B837193 : Blo 742328 837193 := bbase (se 2 (by rfl) ⟨313947, by rfl⟩ : syracuseStep 837193 = 627895) (by norm_num)
theorem B1885781 : Blo 742328 1885781 := bbase (se 8 (by rfl) ⟨11049, by rfl⟩ : syracuseStep 1885781 = 22099) (by norm_num)
theorem B837229 : Blo 742328 837229 := bbase (se 3 (by rfl) ⟨156980, by rfl⟩ : syracuseStep 837229 = 313961) (by norm_num)
theorem B837265 : Blo 742328 837265 := bbase (se 2 (by rfl) ⟨313974, by rfl⟩ : syracuseStep 837265 = 627949) (by norm_num)
theorem B1590941 : Blo 742328 1590941 := bbase (se 3 (by rfl) ⟨298301, by rfl⟩ : syracuseStep 1590941 = 596603) (by norm_num)
theorem B837301 : Blo 742328 837301 := bbase (se 5 (by rfl) ⟨39248, by rfl⟩ : syracuseStep 837301 = 78497) (by norm_num)
theorem B837337 : Blo 742328 837337 := bbase (se 2 (by rfl) ⟨314001, by rfl⟩ : syracuseStep 837337 = 628003) (by norm_num)
theorem B837373 : Blo 742328 837373 := bbase (se 3 (by rfl) ⟨157007, by rfl⟩ : syracuseStep 837373 = 314015) (by norm_num)
theorem B837409 : Blo 742328 837409 := bbase (se 2 (by rfl) ⟨314028, by rfl⟩ : syracuseStep 837409 = 628057) (by norm_num)
theorem B837445 : Blo 742328 837445 := bbase (se 4 (by rfl) ⟨78510, by rfl⟩ : syracuseStep 837445 = 157021) (by norm_num)
theorem B837481 : Blo 742328 837481 := bbase (se 2 (by rfl) ⟨314055, by rfl⟩ : syracuseStep 837481 = 628111) (by norm_num)
theorem B2508677 : Blo 742328 2508677 := bbase (se 4 (by rfl) ⟨235188, by rfl⟩ : syracuseStep 2508677 = 470377) (by norm_num)
theorem B837517 : Blo 742328 837517 := bbase (se 3 (by rfl) ⟨157034, by rfl⟩ : syracuseStep 837517 = 314069) (by norm_num)
theorem B1886125 : Blo 742328 1886125 := bbase (se 3 (by rfl) ⟨353648, by rfl⟩ : syracuseStep 1886125 = 707297) (by norm_num)
theorem B837553 : Blo 742328 837553 := bbase (se 2 (by rfl) ⟨314082, by rfl⟩ : syracuseStep 837553 = 628165) (by norm_num)
theorem B837589 : Blo 742328 837589 := bbase (se 7 (by rfl) ⟨9815, by rfl⟩ : syracuseStep 837589 = 19631) (by norm_num)
theorem B837625 : Blo 742328 837625 := bbase (se 2 (by rfl) ⟨314109, by rfl⟩ : syracuseStep 837625 = 628219) (by norm_num)
theorem B837661 : Blo 742328 837661 := bbase (se 3 (by rfl) ⟨157061, by rfl⟩ : syracuseStep 837661 = 314123) (by norm_num)
theorem B1886237 : Blo 742328 1886237 := bbase (se 3 (by rfl) ⟨353669, by rfl⟩ : syracuseStep 1886237 = 707339) (by norm_num)
theorem B837697 : Blo 742328 837697 := bbase (se 2 (by rfl) ⟨314136, by rfl⟩ : syracuseStep 837697 = 628273) (by norm_num)
theorem B837733 : Blo 742328 837733 := bbase (se 4 (by rfl) ⟨78537, by rfl⟩ : syracuseStep 837733 = 157075) (by norm_num)
theorem B837769 : Blo 742328 837769 := bbase (se 2 (by rfl) ⟨314163, by rfl⟩ : syracuseStep 837769 = 628327) (by norm_num)
theorem B837805 : Blo 742328 837805 := bbase (se 3 (by rfl) ⟨157088, by rfl⟩ : syracuseStep 837805 = 314177) (by norm_num)
theorem B837841 : Blo 742328 837841 := bbase (se 2 (by rfl) ⟨314190, by rfl⟩ : syracuseStep 837841 = 628381) (by norm_num)
theorem B1886429 : Blo 742328 1886429 := bbase (se 3 (by rfl) ⟨353705, by rfl⟩ : syracuseStep 1886429 = 707411) (by norm_num)
theorem B837877 : Blo 742328 837877 := bbase (se 5 (by rfl) ⟨39275, by rfl⟩ : syracuseStep 837877 = 78551) (by norm_num)
theorem B837913 : Blo 742328 837913 := bbase (se 2 (by rfl) ⟨314217, by rfl⟩ : syracuseStep 837913 = 628435) (by norm_num)
theorem B2115877 : Blo 742328 2115877 := bbase (se 4 (by rfl) ⟨198363, by rfl⟩ : syracuseStep 2115877 = 396727) (by norm_num)
theorem B2509109 : Blo 742328 2509109 := bbase (se 5 (by rfl) ⟨117614, by rfl⟩ : syracuseStep 2509109 = 235229) (by norm_num)
theorem B837949 : Blo 742328 837949 := bbase (se 3 (by rfl) ⟨157115, by rfl⟩ : syracuseStep 837949 = 314231) (by norm_num)
theorem B837985 : Blo 742328 837985 := bbase (se 2 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 837985 = 628489) (by norm_num)
theorem B838021 : Blo 742328 838021 := bbase (se 4 (by rfl) ⟨78564, by rfl⟩ : syracuseStep 838021 = 157129) (by norm_num)
theorem B838057 : Blo 742328 838057 := bbase (se 2 (by rfl) ⟨314271, by rfl⟩ : syracuseStep 838057 = 628543) (by norm_num)
theorem B2116037 : Blo 742328 2116037 := bbase (se 4 (by rfl) ⟨198378, by rfl⟩ : syracuseStep 2116037 = 396757) (by norm_num)
theorem B838093 : Blo 742328 838093 := bbase (se 3 (by rfl) ⟨157142, by rfl⟩ : syracuseStep 838093 = 314285) (by norm_num)
theorem B838129 : Blo 742328 838129 := bbase (se 2 (by rfl) ⟨314298, by rfl⟩ : syracuseStep 838129 = 628597) (by norm_num)
theorem B2542085 : Blo 742328 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B2378261 : Blo 742328 2378261 := bbase (se 6 (by rfl) ⟨55740, by rfl⟩ : syracuseStep 2378261 = 111481) (by norm_num)
theorem B838165 : Blo 742328 838165 := bbase (se 6 (by rfl) ⟨19644, by rfl⟩ : syracuseStep 838165 = 39289) (by norm_num)
theorem B1591829 : Blo 742328 1591829 := bbase (se 6 (by rfl) ⟨37308, by rfl⟩ : syracuseStep 1591829 = 74617) (by norm_num)
theorem B1886773 : Blo 742328 1886773 := bbase (se 5 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 1886773 = 176885) (by norm_num)
theorem B838201 : Blo 742328 838201 := bbase (se 2 (by rfl) ⟨314325, by rfl⟩ : syracuseStep 838201 = 628651) (by norm_num)
theorem B838237 : Blo 742328 838237 := bbase (se 3 (by rfl) ⟨157169, by rfl⟩ : syracuseStep 838237 = 314339) (by norm_num)
theorem B838273 : Blo 742328 838273 := bbase (se 2 (by rfl) ⟨314352, by rfl⟩ : syracuseStep 838273 = 628705) (by norm_num)
theorem B1591949 : Blo 742328 1591949 := bbase (se 3 (by rfl) ⟨298490, by rfl⟩ : syracuseStep 1591949 = 596981) (by norm_num)
theorem B838309 : Blo 742328 838309 := bbase (se 4 (by rfl) ⟨78591, by rfl⟩ : syracuseStep 838309 = 157183) (by norm_num)
theorem B1886885 : Blo 742328 1886885 := bbase (se 4 (by rfl) ⟨176895, by rfl⟩ : syracuseStep 1886885 = 353791) (by norm_num)
theorem B2116277 : Blo 742328 2116277 := bbase (se 5 (by rfl) ⟨99200, by rfl⟩ : syracuseStep 2116277 = 198401) (by norm_num)
theorem B838345 : Blo 742328 838345 := bbase (se 2 (by rfl) ⟨314379, by rfl⟩ : syracuseStep 838345 = 628759) (by norm_num)
theorem B2509541 : Blo 742328 2509541 := bbase (se 4 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 2509541 = 470539) (by norm_num)
theorem B838381 : Blo 742328 838381 := bbase (se 3 (by rfl) ⟨157196, by rfl⟩ : syracuseStep 838381 = 314393) (by norm_num)
theorem B838417 : Blo 742328 838417 := bbase (se 2 (by rfl) ⟨314406, by rfl⟩ : syracuseStep 838417 = 628813) (by norm_num)
theorem B838453 : Blo 742328 838453 := bbase (se 5 (by rfl) ⟨39302, by rfl⟩ : syracuseStep 838453 = 78605) (by norm_num)
theorem B838489 : Blo 742328 838489 := bbase (se 2 (by rfl) ⟨314433, by rfl⟩ : syracuseStep 838489 = 628867) (by norm_num)
theorem B1887077 : Blo 742328 1887077 := bbase (se 4 (by rfl) ⟨176913, by rfl⟩ : syracuseStep 1887077 = 353827) (by norm_num)
theorem B2116469 : Blo 742328 2116469 := bbase (se 5 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 2116469 = 198419) (by norm_num)
theorem B838525 : Blo 742328 838525 := bbase (se 3 (by rfl) ⟨157223, by rfl⟩ : syracuseStep 838525 = 314447) (by norm_num)
theorem B838561 : Blo 742328 838561 := bbase (se 2 (by rfl) ⟨314460, by rfl⟩ : syracuseStep 838561 = 628921) (by norm_num)
theorem B838597 : Blo 742328 838597 := bbase (se 4 (by rfl) ⟨78618, by rfl⟩ : syracuseStep 838597 = 157237) (by norm_num)
theorem B838633 : Blo 742328 838633 := bbase (se 2 (by rfl) ⟨314487, by rfl⟩ : syracuseStep 838633 = 628975) (by norm_num)
theorem B838669 : Blo 742328 838669 := bbase (se 3 (by rfl) ⟨157250, by rfl⟩ : syracuseStep 838669 = 314501) (by norm_num)
theorem B838705 : Blo 742328 838705 := bbase (se 2 (by rfl) ⟨314514, by rfl⟩ : syracuseStep 838705 = 629029) (by norm_num)
theorem B838741 : Blo 742328 838741 := bbase (se 8 (by rfl) ⟨4914, by rfl⟩ : syracuseStep 838741 = 9829) (by norm_num)
theorem B838777 : Blo 742328 838777 := bbase (se 2 (by rfl) ⟨314541, by rfl⟩ : syracuseStep 838777 = 629083) (by norm_num)
theorem B1789069 : Blo 742328 1789069 := bbase (se 3 (by rfl) ⟨335450, by rfl⟩ : syracuseStep 1789069 = 670901) (by norm_num)
theorem B1428629 : Blo 742328 1428629 := bbase (se 6 (by rfl) ⟨33483, by rfl⟩ : syracuseStep 1428629 = 66967) (by norm_num)
theorem B2509973 : Blo 742328 2509973 := bbase (se 6 (by rfl) ⟨58827, by rfl⟩ : syracuseStep 2509973 = 117655) (by norm_num)
theorem B838813 : Blo 742328 838813 := bbase (se 3 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 838813 = 314555) (by norm_num)
theorem B1887421 : Blo 742328 1887421 := bbase (se 3 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 1887421 = 707783) (by norm_num)
theorem B838849 : Blo 742328 838849 := bbase (se 2 (by rfl) ⟨314568, by rfl⟩ : syracuseStep 838849 = 629137) (by norm_num)
theorem B838885 : Blo 742328 838885 := bbase (se 4 (by rfl) ⟨78645, by rfl⟩ : syracuseStep 838885 = 157291) (by norm_num)
theorem B1592581 : Blo 742328 1592581 := bbase (se 4 (by rfl) ⟨149304, by rfl⟩ : syracuseStep 1592581 = 298609) (by norm_num)
theorem B838921 : Blo 742328 838921 := bbase (se 2 (by rfl) ⟨314595, by rfl⟩ : syracuseStep 838921 = 629191) (by norm_num)
theorem B4640021 : Blo 742328 4640021 := bbase (se 6 (by rfl) ⟨108750, by rfl⟩ : syracuseStep 4640021 = 217501) (by norm_num)
theorem B1887533 : Blo 742328 1887533 := bbase (se 3 (by rfl) ⟨353912, by rfl⟩ : syracuseStep 1887533 = 707825) (by norm_num)
theorem B838957 : Blo 742328 838957 := bbase (se 3 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 838957 = 314609) (by norm_num)
theorem B838993 : Blo 742328 838993 := bbase (se 2 (by rfl) ⟨314622, by rfl⟩ : syracuseStep 838993 = 629245) (by norm_num)
theorem B5098837 : Blo 742328 5098837 := bbase (se 11 (by rfl) ⟨3734, by rfl⟩ : syracuseStep 5098837 = 7469) (by norm_num)
theorem B839029 : Blo 742328 839029 := bbase (se 5 (by rfl) ⟨39329, by rfl⟩ : syracuseStep 839029 = 78659) (by norm_num)
theorem B839065 : Blo 742328 839065 := bbase (se 2 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 839065 = 629299) (by norm_num)
theorem B1527229 : Blo 742328 1527229 := bbase (se 3 (by rfl) ⟨286355, by rfl⟩ : syracuseStep 1527229 = 572711) (by norm_num)
theorem B1134013 : Blo 742328 1134013 := bbase (se 3 (by rfl) ⟨212627, by rfl⟩ : syracuseStep 1134013 = 425255) (by norm_num)
theorem B839101 : Blo 742328 839101 := bbase (se 3 (by rfl) ⟨157331, by rfl⟩ : syracuseStep 839101 = 314663) (by norm_num)
theorem B839137 : Blo 742328 839137 := bbase (se 2 (by rfl) ⟨314676, by rfl⟩ : syracuseStep 839137 = 629353) (by norm_num)
theorem B1887725 : Blo 742328 1887725 := bbase (se 3 (by rfl) ⟨353948, by rfl⟩ : syracuseStep 1887725 = 707897) (by norm_num)
theorem B839173 : Blo 742328 839173 := bbase (se 4 (by rfl) ⟨78672, by rfl⟩ : syracuseStep 839173 = 157345) (by norm_num)
theorem B839209 : Blo 742328 839209 := bbase (se 2 (by rfl) ⟨314703, by rfl⟩ : syracuseStep 839209 = 629407) (by norm_num)
theorem B2510405 : Blo 742328 2510405 := bbase (se 4 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 2510405 = 470701) (by norm_num)
theorem B3395141 : Blo 742328 3395141 := bbase (se 4 (by rfl) ⟨318294, by rfl⟩ : syracuseStep 3395141 = 636589) (by norm_num)
theorem B839245 : Blo 742328 839245 := bbase (se 3 (by rfl) ⟨157358, by rfl⟩ : syracuseStep 839245 = 314717) (by norm_num)
theorem B839281 : Blo 742328 839281 := bbase (se 2 (by rfl) ⟨314730, by rfl⟩ : syracuseStep 839281 = 629461) (by norm_num)
theorem B839317 : Blo 742328 839317 := bbase (se 6 (by rfl) ⟨19671, by rfl⟩ : syracuseStep 839317 = 39343) (by norm_num)
theorem B839353 : Blo 742328 839353 := bbase (se 2 (by rfl) ⟨314757, by rfl⟩ : syracuseStep 839353 = 629515) (by norm_num)
theorem B839389 : Blo 742328 839389 := bbase (se 3 (by rfl) ⟨157385, by rfl⟩ : syracuseStep 839389 = 314771) (by norm_num)
theorem B1789685 : Blo 742328 1789685 := bbase (se 5 (by rfl) ⟨83891, by rfl⟩ : syracuseStep 1789685 = 167783) (by norm_num)
theorem B839425 : Blo 742328 839425 := bbase (se 2 (by rfl) ⟨314784, by rfl⟩ : syracuseStep 839425 = 629569) (by norm_num)
theorem B839461 : Blo 742328 839461 := bbase (se 4 (by rfl) ⟨78699, by rfl⟩ : syracuseStep 839461 = 157399) (by norm_num)
theorem B1888069 : Blo 742328 1888069 := bbase (se 4 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 1888069 = 354013) (by norm_num)
theorem B839497 : Blo 742328 839497 := bbase (se 2 (by rfl) ⟨314811, by rfl⟩ : syracuseStep 839497 = 629623) (by norm_num)
theorem B2117461 : Blo 742328 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B4771669 : Blo 742328 4771669 := bbase (se 9 (by rfl) ⟨13979, by rfl⟩ : syracuseStep 4771669 = 27959) (by norm_num)
theorem B839533 : Blo 742328 839533 := bbase (se 3 (by rfl) ⟨157412, by rfl⟩ : syracuseStep 839533 = 314825) (by norm_num)
theorem B839569 : Blo 742328 839569 := bbase (se 2 (by rfl) ⟨314838, by rfl⟩ : syracuseStep 839569 = 629677) (by norm_num)
theorem B1888181 : Blo 742328 1888181 := bbase (se 5 (by rfl) ⟨88508, by rfl⟩ : syracuseStep 1888181 = 177017) (by norm_num)
theorem B839605 : Blo 742328 839605 := bbase (se 5 (by rfl) ⟨39356, by rfl⟩ : syracuseStep 839605 = 78713) (by norm_num)
theorem B1789885 : Blo 742328 1789885 := bbase (se 3 (by rfl) ⟨335603, by rfl⟩ : syracuseStep 1789885 = 671207) (by norm_num)
theorem B2543605 : Blo 742328 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B2510837 : Blo 742328 2510837 := bbase (se 5 (by rfl) ⟨117695, by rfl⟩ : syracuseStep 2510837 = 235391) (by norm_num)
theorem B1888373 : Blo 742328 1888373 := bbase (se 5 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 1888373 = 177035) (by norm_num)
theorem B2871413 : Blo 742328 2871413 := bbase (se 5 (by rfl) ⟨134597, by rfl⟩ : syracuseStep 2871413 = 269195) (by norm_num)
theorem B1593469 : Blo 742328 1593469 := bbase (se 3 (by rfl) ⟨298775, by rfl⟩ : syracuseStep 1593469 = 597551) (by norm_num)
theorem B1593589 : Blo 742328 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B2511269 : Blo 742328 2511269 := bbase (se 4 (by rfl) ⟨235431, by rfl⟩ : syracuseStep 2511269 = 470863) (by norm_num)
theorem B1888717 : Blo 742328 1888717 := bbase (se 3 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 1888717 = 708269) (by norm_num)
theorem B1593845 : Blo 742328 1593845 := bbase (se 5 (by rfl) ⟨74711, by rfl⟩ : syracuseStep 1593845 = 149423) (by norm_num)
theorem B1888829 : Blo 742328 1888829 := bbase (se 3 (by rfl) ⟨354155, by rfl⟩ : syracuseStep 1888829 = 708311) (by norm_num)
theorem B1790693 : Blo 742328 1790693 := bbase (se 4 (by rfl) ⟨167877, by rfl⟩ : syracuseStep 1790693 = 335755) (by norm_num)
theorem B1889021 : Blo 742328 1889021 := bbase (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) (by norm_num)
theorem B2511701 : Blo 742328 2511701 := bbase (se 9 (by rfl) ⟨7358, by rfl⟩ : syracuseStep 2511701 = 14717) (by norm_num)
theorem B2118565 : Blo 742328 2118565 := bbase (se 4 (by rfl) ⟨198615, by rfl⟩ : syracuseStep 2118565 = 397231) (by norm_num)
theorem B5657525 : Blo 742328 5657525 := bbase (se 5 (by rfl) ⟨265196, by rfl⟩ : syracuseStep 5657525 = 530393) (by norm_num)
theorem B906277 : Blo 742328 906277 := bbase (se 4 (by rfl) ⟨84963, by rfl⟩ : syracuseStep 906277 = 169927) (by norm_num)
theorem B2512133 : Blo 742328 2512133 := bbase (se 4 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 2512133 = 471025) (by norm_num)
theorem B1791461 : Blo 742328 1791461 := bbase (se 4 (by rfl) ⟨167949, by rfl⟩ : syracuseStep 1791461 = 335899) (by norm_num)
theorem B939529 : Blo 742328 939529 := bbase (se 2 (by rfl) ⟨352323, by rfl⟩ : syracuseStep 939529 = 704647) (by norm_num)
theorem B4249205 : Blo 742328 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B939701 : Blo 742328 939701 := bbase (se 5 (by rfl) ⟨44048, by rfl⟩ : syracuseStep 939701 = 88097) (by norm_num)
theorem B2512565 : Blo 742328 2512565 := bbase (se 5 (by rfl) ⟨117776, by rfl⟩ : syracuseStep 2512565 = 235553) (by norm_num)
theorem B939757 : Blo 742328 939757 := bbase (se 3 (by rfl) ⟨176204, by rfl⟩ : syracuseStep 939757 = 352409) (by norm_num)
theorem B939853 : Blo 742328 939853 := bbase (se 3 (by rfl) ⟨176222, by rfl⟩ : syracuseStep 939853 = 352445) (by norm_num)
theorem B2676581 : Blo 742328 2676581 := bbase (se 4 (by rfl) ⟨250929, by rfl⟩ : syracuseStep 2676581 = 501859) (by norm_num)
theorem B3397621 : Blo 742328 3397621 := bbase (se 5 (by rfl) ⟨159263, by rfl⟩ : syracuseStep 3397621 = 318527) (by norm_num)
theorem B940025 : Blo 742328 940025 := bbase (se 2 (by rfl) ⟨352509, by rfl⟩ : syracuseStep 940025 = 705019) (by norm_num)
theorem B940081 : Blo 742328 940081 := bbase (se 2 (by rfl) ⟨352530, by rfl⟩ : syracuseStep 940081 = 705061) (by norm_num)
theorem B2512997 : Blo 742328 2512997 := bbase (se 4 (by rfl) ⟨235593, by rfl⟩ : syracuseStep 2512997 = 471187) (by norm_num)
theorem B940177 : Blo 742328 940177 := bbase (se 2 (by rfl) ⟨352566, by rfl⟩ : syracuseStep 940177 = 705133) (by norm_num)
theorem B2382053 : Blo 742328 2382053 := bbase (se 4 (by rfl) ⟨223317, by rfl⟩ : syracuseStep 2382053 = 446635) (by norm_num)
theorem B940349 : Blo 742328 940349 := bbase (se 3 (by rfl) ⟨176315, by rfl⟩ : syracuseStep 940349 = 352631) (by norm_num)
theorem B940405 : Blo 742328 940405 := bbase (se 5 (by rfl) ⟨44081, by rfl⟩ : syracuseStep 940405 = 88163) (by norm_num)
theorem B2120069 : Blo 742328 2120069 := bbase (se 4 (by rfl) ⟨198756, by rfl⟩ : syracuseStep 2120069 = 397513) (by norm_num)
theorem B940501 : Blo 742328 940501 := bbase (se 7 (by rfl) ⟨11021, by rfl⟩ : syracuseStep 940501 = 22043) (by norm_num)
theorem B1694213 : Blo 742328 1694213 := bbase (se 4 (by rfl) ⟨158832, by rfl⟩ : syracuseStep 1694213 = 317665) (by norm_num)
theorem B2513429 : Blo 742328 2513429 := bbase (se 6 (by rfl) ⟨58908, by rfl⟩ : syracuseStep 2513429 = 117817) (by norm_num)
theorem B2677333 : Blo 742328 2677333 := bbase (se 8 (by rfl) ⟨15687, by rfl⟩ : syracuseStep 2677333 = 31375) (by norm_num)
theorem B940673 : Blo 742328 940673 := bbase (se 2 (by rfl) ⟨352752, by rfl⟩ : syracuseStep 940673 = 705505) (by norm_num)
theorem B940729 : Blo 742328 940729 := bbase (se 2 (by rfl) ⟨352773, by rfl⟩ : syracuseStep 940729 = 705547) (by norm_num)
theorem B940825 : Blo 742328 940825 := bbase (se 2 (by rfl) ⟨352809, by rfl⟩ : syracuseStep 940825 = 705619) (by norm_num)
theorem B3758885 : Blo 742328 3758885 := bbase (se 4 (by rfl) ⟨352395, by rfl⟩ : syracuseStep 3758885 = 704791) (by norm_num)
theorem B940997 : Blo 742328 940997 := bbase (se 4 (by rfl) ⟨88218, by rfl⟩ : syracuseStep 940997 = 176437) (by norm_num)
theorem B2513861 : Blo 742328 2513861 := bbase (se 4 (by rfl) ⟨235674, by rfl⟩ : syracuseStep 2513861 = 471349) (by norm_num)
theorem B1006573 : Blo 742328 1006573 := bbase (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) (by norm_num)
theorem B941053 : Blo 742328 941053 := bbase (se 3 (by rfl) ⟨176447, by rfl⟩ : syracuseStep 941053 = 352895) (by norm_num)
theorem B941149 : Blo 742328 941149 := bbase (se 3 (by rfl) ⟨176465, by rfl⟩ : syracuseStep 941149 = 352931) (by norm_num)
theorem B2382965 : Blo 742328 2382965 := bbase (se 5 (by rfl) ⟨111701, by rfl⟩ : syracuseStep 2382965 = 223403) (by norm_num)
theorem B3398773 : Blo 742328 3398773 := bbase (se 5 (by rfl) ⟨159317, by rfl⟩ : syracuseStep 3398773 = 318635) (by norm_num)
theorem B1793173 : Blo 742328 1793173 := bbase (se 6 (by rfl) ⟨42027, by rfl⟩ : syracuseStep 1793173 = 84055) (by norm_num)
theorem B2579653 : Blo 742328 2579653 := bbase (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) (by norm_num)
theorem B941321 : Blo 742328 941321 := bbase (se 2 (by rfl) ⟨352995, by rfl⟩ : syracuseStep 941321 = 705991) (by norm_num)
theorem B941377 : Blo 742328 941377 := bbase (se 2 (by rfl) ⟨353016, by rfl⟩ : syracuseStep 941377 = 706033) (by norm_num)
theorem B96722261 : Blo 742328 96722261 := bbase (se 11 (by rfl) ⟨70841, by rfl⟩ : syracuseStep 96722261 = 141683) (by norm_num)
theorem B2514293 : Blo 742328 2514293 := bbase (se 5 (by rfl) ⟨117857, by rfl⟩ : syracuseStep 2514293 = 235715) (by norm_num)
theorem B941473 : Blo 742328 941473 := bbase (se 2 (by rfl) ⟨353052, by rfl⟩ : syracuseStep 941473 = 706105) (by norm_num)
theorem B2678341 : Blo 742328 2678341 := bbase (se 4 (by rfl) ⟨251094, by rfl⟩ : syracuseStep 2678341 = 502189) (by norm_num)
theorem B941645 : Blo 742328 941645 := bbase (se 3 (by rfl) ⟨176558, by rfl⟩ : syracuseStep 941645 = 353117) (by norm_num)
theorem B941701 : Blo 742328 941701 := bbase (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) (by norm_num)
theorem B941797 : Blo 742328 941797 := bbase (se 4 (by rfl) ⟨88293, by rfl⟩ : syracuseStep 941797 = 176587) (by norm_num)
theorem B2514725 : Blo 742328 2514725 := bbase (se 4 (by rfl) ⟨235755, by rfl⟩ : syracuseStep 2514725 = 471511) (by norm_num)
theorem B941969 : Blo 742328 941969 := bbase (se 2 (by rfl) ⟨353238, by rfl⟩ : syracuseStep 941969 = 706477) (by norm_num)
theorem B6348725 : Blo 742328 6348725 := bbase (se 5 (by rfl) ⟨297596, by rfl⟩ : syracuseStep 6348725 = 595193) (by norm_num)
theorem B2121653 : Blo 742328 2121653 := bbase (se 5 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 2121653 = 198905) (by norm_num)
theorem B942025 : Blo 742328 942025 := bbase (se 2 (by rfl) ⟨353259, by rfl⟩ : syracuseStep 942025 = 706519) (by norm_num)
theorem B942121 : Blo 742328 942121 := bbase (se 2 (by rfl) ⟨353295, by rfl⟩ : syracuseStep 942121 = 706591) (by norm_num)
theorem B3760181 : Blo 742328 3760181 := bbase (se 5 (by rfl) ⟨176258, by rfl⟩ : syracuseStep 3760181 = 352517) (by norm_num)
theorem B1531973 : Blo 742328 1531973 := bbase (se 4 (by rfl) ⟨143622, by rfl⟩ : syracuseStep 1531973 = 287245) (by norm_num)
theorem B942293 : Blo 742328 942293 := bbase (se 7 (by rfl) ⟨11042, by rfl⟩ : syracuseStep 942293 = 22085) (by norm_num)
theorem B2515157 : Blo 742328 2515157 := bbase (se 7 (by rfl) ⟨29474, by rfl⟩ : syracuseStep 2515157 = 58949) (by norm_num)
theorem B1073413 : Blo 742328 1073413 := bbase (se 4 (by rfl) ⟨100632, by rfl⟩ : syracuseStep 1073413 = 201265) (by norm_num)
theorem B942349 : Blo 742328 942349 := bbase (se 3 (by rfl) ⟨176690, by rfl⟩ : syracuseStep 942349 = 353381) (by norm_num)
theorem B8053013 : Blo 742328 8053013 := bbase (se 6 (by rfl) ⟨188742, by rfl⟩ : syracuseStep 8053013 = 377485) (by norm_num)
theorem B942445 : Blo 742328 942445 := bbase (se 3 (by rfl) ⟨176708, by rfl⟩ : syracuseStep 942445 = 353417) (by norm_num)
theorem B2384309 : Blo 742328 2384309 := bbase (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) (by norm_num)
theorem B13591061 : Blo 742328 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B942617 : Blo 742328 942617 := bbase (se 2 (by rfl) ⟨353481, by rfl⟩ : syracuseStep 942617 = 706963) (by norm_num)
theorem B1008173 : Blo 742328 1008173 := bbase (se 3 (by rfl) ⟨189032, by rfl⟩ : syracuseStep 1008173 = 378065) (by norm_num)
theorem B942673 : Blo 742328 942673 := bbase (se 2 (by rfl) ⟨353502, by rfl⟩ : syracuseStep 942673 = 707005) (by norm_num)
theorem B2122325 : Blo 742328 2122325 := bbase (se 8 (by rfl) ⟨12435, by rfl⟩ : syracuseStep 2122325 = 24871) (by norm_num)
theorem B2515589 : Blo 742328 2515589 := bbase (se 4 (by rfl) ⟨235836, by rfl⟩ : syracuseStep 2515589 = 471673) (by norm_num)
theorem B942769 : Blo 742328 942769 := bbase (se 2 (by rfl) ⟨353538, by rfl⟩ : syracuseStep 942769 = 707077) (by norm_num)
theorem B2417413 : Blo 742328 2417413 := bbase (se 4 (by rfl) ⟨226632, by rfl⟩ : syracuseStep 2417413 = 453265) (by norm_num)
theorem B1631069 : Blo 742328 1631069 := bbase (se 3 (by rfl) ⟨305825, by rfl⟩ : syracuseStep 1631069 = 611651) (by norm_num)
theorem B942941 : Blo 742328 942941 := bbase (se 3 (by rfl) ⟨176801, by rfl⟩ : syracuseStep 942941 = 353603) (by norm_num)
theorem B942997 : Blo 742328 942997 := bbase (se 6 (by rfl) ⟨22101, by rfl⟩ : syracuseStep 942997 = 44203) (by norm_num)
theorem B943093 : Blo 742328 943093 := bbase (se 5 (by rfl) ⟨44207, by rfl⟩ : syracuseStep 943093 = 88415) (by norm_num)
theorem B2122757 : Blo 742328 2122757 := bbase (se 4 (by rfl) ⟨199008, by rfl⟩ : syracuseStep 2122757 = 398017) (by norm_num)
theorem B1696805 : Blo 742328 1696805 := bbase (se 4 (by rfl) ⟨159075, by rfl⟩ : syracuseStep 1696805 = 318151) (by norm_num)
theorem B2516021 : Blo 742328 2516021 := bbase (se 5 (by rfl) ⟨117938, by rfl⟩ : syracuseStep 2516021 = 235877) (by norm_num)
theorem B1434757 : Blo 742328 1434757 := bbase (se 4 (by rfl) ⟨134508, by rfl⟩ : syracuseStep 1434757 = 269017) (by norm_num)
theorem B943265 : Blo 742328 943265 := bbase (se 2 (by rfl) ⟨353724, by rfl⟩ : syracuseStep 943265 = 707449) (by norm_num)
theorem B1205453 : Blo 742328 1205453 := bbase (se 3 (by rfl) ⟨226022, by rfl⟩ : syracuseStep 1205453 = 452045) (by norm_num)
theorem B943321 : Blo 742328 943321 := bbase (se 2 (by rfl) ⟨353745, by rfl⟩ : syracuseStep 943321 = 707491) (by norm_num)
theorem B943417 : Blo 742328 943417 := bbase (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) (by norm_num)
theorem B3761477 : Blo 742328 3761477 := bbase (se 4 (by rfl) ⟨352638, by rfl⟩ : syracuseStep 3761477 = 705277) (by norm_num)
theorem B30532949 : Blo 742328 30532949 := bbase (se 12 (by rfl) ⟨11181, by rfl⟩ : syracuseStep 30532949 = 22363) (by norm_num)
theorem B1860989 : Blo 742328 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B943589 : Blo 742328 943589 := bbase (se 4 (by rfl) ⟨88461, by rfl⟩ : syracuseStep 943589 = 176923) (by norm_num)
theorem B2516453 : Blo 742328 2516453 := bbase (se 4 (by rfl) ⟨235917, by rfl⟩ : syracuseStep 2516453 = 471835) (by norm_num)
theorem B2942453 : Blo 742328 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B943645 : Blo 742328 943645 := bbase (se 3 (by rfl) ⟨176933, by rfl⟩ : syracuseStep 943645 = 353867) (by norm_num)
theorem B2418245 : Blo 742328 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B943741 : Blo 742328 943741 := bbase (se 3 (by rfl) ⟨176951, by rfl⟩ : syracuseStep 943741 = 353903) (by norm_num)
theorem B2123509 : Blo 742328 2123509 := bbase (se 5 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 2123509 = 199079) (by norm_num)
theorem B943913 : Blo 742328 943913 := bbase (se 2 (by rfl) ⟨353967, by rfl⟩ : syracuseStep 943913 = 707935) (by norm_num)
theorem B2385733 : Blo 742328 2385733 := bbase (se 4 (by rfl) ⟨223662, by rfl⟩ : syracuseStep 2385733 = 447325) (by norm_num)
theorem B943969 : Blo 742328 943969 := bbase (se 2 (by rfl) ⟨353988, by rfl⟩ : syracuseStep 943969 = 707977) (by norm_num)
theorem B3172229 : Blo 742328 3172229 := bbase (se 4 (by rfl) ⟨297396, by rfl⟩ : syracuseStep 3172229 = 594793) (by norm_num)
theorem B2516885 : Blo 742328 2516885 := bbase (se 6 (by rfl) ⟨58989, by rfl⟩ : syracuseStep 2516885 = 117979) (by norm_num)
theorem B944065 : Blo 742328 944065 := bbase (se 2 (by rfl) ⟨354024, by rfl⟩ : syracuseStep 944065 = 708049) (by norm_num)
theorem B944237 : Blo 742328 944237 := bbase (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) (by norm_num)
theorem B3172517 : Blo 742328 3172517 := bbase (se 4 (by rfl) ⟨297423, by rfl⟩ : syracuseStep 3172517 = 594847) (by norm_num)
theorem B944293 : Blo 742328 944293 := bbase (se 4 (by rfl) ⟨88527, by rfl⟩ : syracuseStep 944293 = 177055) (by norm_num)
theorem B944389 : Blo 742328 944389 := bbase (se 4 (by rfl) ⟨88536, by rfl⟩ : syracuseStep 944389 = 177073) (by norm_num)
theorem B1272077 : Blo 742328 1272077 := bbase (se 3 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 1272077 = 477029) (by norm_num)
theorem B2517317 : Blo 742328 2517317 := bbase (se 4 (by rfl) ⟨235998, by rfl⟩ : syracuseStep 2517317 = 471997) (by norm_num)
theorem B944561 : Blo 742328 944561 := bbase (se 2 (by rfl) ⟨354210, by rfl⟩ : syracuseStep 944561 = 708421) (by norm_num)
theorem B1337917 : Blo 742328 1337917 := bbase (se 3 (by rfl) ⟨250859, by rfl⟩ : syracuseStep 1337917 = 501719) (by norm_num)
theorem B3762773 : Blo 742328 3762773 := bbase (se 8 (by rfl) ⟨22047, by rfl⟩ : syracuseStep 3762773 = 44095) (by norm_num)
theorem B2517749 : Blo 742328 2517749 := bbase (se 5 (by rfl) ⟨118019, by rfl⟩ : syracuseStep 2517749 = 236039) (by norm_num)
theorem B1338133 : Blo 742328 1338133 := bbase (se 6 (by rfl) ⟨31362, by rfl⟩ : syracuseStep 1338133 = 62725) (by norm_num)
theorem B12741461 : Blo 742328 12741461 := bbase (se 9 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 12741461 = 74657) (by norm_num)
theorem B3173269 : Blo 742328 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B2518181 : Blo 742328 2518181 := bbase (se 4 (by rfl) ⟨236079, by rfl⟩ : syracuseStep 2518181 = 472159) (by norm_num)
theorem B2387333 : Blo 742328 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B847325 : Blo 742328 847325 := bbase (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) (by norm_num)
theorem B4517365 : Blo 742328 4517365 := bbase (se 5 (by rfl) ⟨211751, by rfl⟩ : syracuseStep 4517365 = 423503) (by norm_num)
theorem B2518613 : Blo 742328 2518613 := bbase (se 8 (by rfl) ⟨14757, by rfl⟩ : syracuseStep 2518613 = 29515) (by norm_num)
theorem B3174005 : Blo 742328 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B10743637 : Blo 742328 10743637 := bbase (se 9 (by rfl) ⟨31475, by rfl⟩ : syracuseStep 10743637 = 62951) (by norm_num)
theorem B3764069 : Blo 742328 3764069 := bbase (se 4 (by rfl) ⟨352881, by rfl⟩ : syracuseStep 3764069 = 705763) (by norm_num)
theorem B6123413 : Blo 742328 6123413 := bbase (se 6 (by rfl) ⟨143517, by rfl⟩ : syracuseStep 6123413 = 287035) (by norm_num)
theorem B847837 : Blo 742328 847837 := bbase (se 3 (by rfl) ⟨158969, by rfl⟩ : syracuseStep 847837 = 317939) (by norm_num)
theorem B6451285 : Blo 742328 6451285 := bbase (se 8 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 6451285 = 75601) (by norm_num)
theorem B1339517 : Blo 742328 1339517 := bbase (se 3 (by rfl) ⟨251159, by rfl⟩ : syracuseStep 1339517 = 502319) (by norm_num)
theorem B1339669 : Blo 742328 1339669 := bbase (se 6 (by rfl) ⟨31398, by rfl⟩ : syracuseStep 1339669 = 62797) (by norm_num)
theorem B1339733 : Blo 742328 1339733 := bbase (se 10 (by rfl) ⟨1962, by rfl⟩ : syracuseStep 1339733 = 3925) (by norm_num)
theorem B3567989 : Blo 742328 3567989 := bbase (se 5 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 3567989 = 334499) (by norm_num)
theorem B2388437 : Blo 742328 2388437 := bbase (se 7 (by rfl) ⟨27989, by rfl⟩ : syracuseStep 2388437 = 55979) (by norm_num)
theorem B1339877 : Blo 742328 1339877 := bbase (se 4 (by rfl) ⟨125613, by rfl⟩ : syracuseStep 1339877 = 251227) (by norm_num)
theorem B5665301 : Blo 742328 5665301 := bbase (se 6 (by rfl) ⟨132780, by rfl⟩ : syracuseStep 5665301 = 265561) (by norm_num)
theorem B2552485 : Blo 742328 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B3011269 : Blo 742328 3011269 := bbase (se 4 (by rfl) ⟨282306, by rfl⟩ : syracuseStep 3011269 = 564613) (by norm_num)
theorem B1700581 : Blo 742328 1700581 := bbase (se 4 (by rfl) ⟨159429, by rfl⟩ : syracuseStep 1700581 = 318859) (by norm_num)
theorem B4027157 : Blo 742328 4027157 := bbase (se 6 (by rfl) ⟨94386, by rfl⟩ : syracuseStep 4027157 = 188773) (by norm_num)
theorem B1274869 : Blo 742328 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B3568661 : Blo 742328 3568661 := bbase (se 6 (by rfl) ⟨83640, by rfl⟩ : syracuseStep 3568661 = 167281) (by norm_num)
theorem B2421829 : Blo 742328 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B3765365 : Blo 742328 3765365 := bbase (se 5 (by rfl) ⟨176501, by rfl⟩ : syracuseStep 3765365 = 353003) (by norm_num)
theorem B1341053 : Blo 742328 1341053 := bbase (se 3 (by rfl) ⟨251447, by rfl⟩ : syracuseStep 1341053 = 502895) (by norm_num)
theorem B1275581 : Blo 742328 1275581 := bbase (se 3 (by rfl) ⟨239171, by rfl⟩ : syracuseStep 1275581 = 478343) (by norm_num)
theorem B849697 : Blo 742328 849697 := bbase (se 2 (by rfl) ⟨318636, by rfl⟩ : syracuseStep 849697 = 637273) (by norm_num)
theorem B9664661 : Blo 742328 9664661 := bbase (se 6 (by rfl) ⟨226515, by rfl⟩ : syracuseStep 9664661 = 453031) (by norm_num)
theorem B1931453 : Blo 742328 1931453 := bbase (se 3 (by rfl) ⟨362147, by rfl⟩ : syracuseStep 1931453 = 724295) (by norm_num)
theorem B1145029 : Blo 742328 1145029 := bbase (se 4 (by rfl) ⟨107346, by rfl⟩ : syracuseStep 1145029 = 214693) (by norm_num)
theorem B2390357 : Blo 742328 2390357 := bbase (se 10 (by rfl) ⟨3501, by rfl⟩ : syracuseStep 2390357 = 7003) (by norm_num)
theorem B3766661 : Blo 742328 3766661 := bbase (se 4 (by rfl) ⟨353124, by rfl⟩ : syracuseStep 3766661 = 706249) (by norm_num)
theorem B1505837 : Blo 742328 1505837 := bbase (se 3 (by rfl) ⟨282344, by rfl⟩ : syracuseStep 1505837 = 564689) (by norm_num)
theorem B1276573 : Blo 742328 1276573 := bbase (se 3 (by rfl) ⟨239357, by rfl⟩ : syracuseStep 1276573 = 478715) (by norm_num)
theorem B3177301 : Blo 742328 3177301 := bbase (se 9 (by rfl) ⟨9308, by rfl⟩ : syracuseStep 3177301 = 18617) (by norm_num)
theorem B2685797 : Blo 742328 2685797 := bbase (se 4 (by rfl) ⟨251793, by rfl⟩ : syracuseStep 2685797 = 503587) (by norm_num)
theorem B850861 : Blo 742328 850861 := bbase (se 3 (by rfl) ⟨159536, by rfl⟩ : syracuseStep 850861 = 319073) (by norm_num)
theorem B1670309 : Blo 742328 1670309 := bbase (se 4 (by rfl) ⟨156591, by rfl⟩ : syracuseStep 1670309 = 313183) (by norm_num)
theorem B1670381 : Blo 742328 1670381 := bbase (se 3 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 1670381 = 626393) (by norm_num)
theorem B1670453 : Blo 742328 1670453 := bbase (se 5 (by rfl) ⟨78302, by rfl⟩ : syracuseStep 1670453 = 156605) (by norm_num)
theorem B1670525 : Blo 742328 1670525 := bbase (se 3 (by rfl) ⟨313223, by rfl⟩ : syracuseStep 1670525 = 626447) (by norm_num)
theorem B1113509 : Blo 742328 1113509 := bbase (se 4 (by rfl) ⟨104391, by rfl⟩ : syracuseStep 1113509 = 208783) (by norm_num)
theorem B1113533 : Blo 742328 1113533 := bbase (se 3 (by rfl) ⟨208787, by rfl⟩ : syracuseStep 1113533 = 417575) (by norm_num)
theorem B1670597 : Blo 742328 1670597 := bbase (se 4 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 1670597 = 313237) (by norm_num)
theorem B1113557 : Blo 742328 1113557 := bbase (se 7 (by rfl) ⟨13049, by rfl⟩ : syracuseStep 1113557 = 26099) (by norm_num)
theorem B1113581 : Blo 742328 1113581 := bbase (se 3 (by rfl) ⟨208796, by rfl⟩ : syracuseStep 1113581 = 417593) (by norm_num)
theorem B1113605 : Blo 742328 1113605 := bbase (se 4 (by rfl) ⟨104400, by rfl⟩ : syracuseStep 1113605 = 208801) (by norm_num)
theorem B1670669 : Blo 742328 1670669 := bbase (se 3 (by rfl) ⟨313250, by rfl⟩ : syracuseStep 1670669 = 626501) (by norm_num)
theorem B1113629 : Blo 742328 1113629 := bbase (se 3 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 1113629 = 417611) (by norm_num)
theorem B1113653 : Blo 742328 1113653 := bbase (se 5 (by rfl) ⟨52202, by rfl⟩ : syracuseStep 1113653 = 104405) (by norm_num)
theorem B1113677 : Blo 742328 1113677 := bbase (se 3 (by rfl) ⟨208814, by rfl⟩ : syracuseStep 1113677 = 417629) (by norm_num)
theorem B1670741 : Blo 742328 1670741 := bbase (se 8 (by rfl) ⟨9789, by rfl⟩ : syracuseStep 1670741 = 19579) (by norm_num)
theorem B1113701 : Blo 742328 1113701 := bbase (se 4 (by rfl) ⟨104409, by rfl⟩ : syracuseStep 1113701 = 208819) (by norm_num)
theorem B1113725 : Blo 742328 1113725 := bbase (se 3 (by rfl) ⟨208823, by rfl⟩ : syracuseStep 1113725 = 417647) (by norm_num)
theorem B1113749 : Blo 742328 1113749 := bbase (se 6 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 1113749 = 52207) (by norm_num)
theorem B3767957 : Blo 742328 3767957 := bbase (se 6 (by rfl) ⟨88311, by rfl⟩ : syracuseStep 3767957 = 176623) (by norm_num)
theorem B1670813 : Blo 742328 1670813 := bbase (se 3 (by rfl) ⟨313277, by rfl⟩ : syracuseStep 1670813 = 626555) (by norm_num)
theorem B1113773 : Blo 742328 1113773 := bbase (se 3 (by rfl) ⟨208832, by rfl⟩ : syracuseStep 1113773 = 417665) (by norm_num)
theorem B1113797 : Blo 742328 1113797 := bbase (se 4 (by rfl) ⟨104418, by rfl⟩ : syracuseStep 1113797 = 208837) (by norm_num)
theorem B15302357 : Blo 742328 15302357 := bbase (se 7 (by rfl) ⟨179324, by rfl⟩ : syracuseStep 15302357 = 358649) (by norm_num)
theorem B1113821 : Blo 742328 1113821 := bbase (se 3 (by rfl) ⟨208841, by rfl⟩ : syracuseStep 1113821 = 417683) (by norm_num)
theorem B1670885 : Blo 742328 1670885 := bbase (se 4 (by rfl) ⟨156645, by rfl⟩ : syracuseStep 1670885 = 313291) (by norm_num)
theorem B1113845 : Blo 742328 1113845 := bbase (se 5 (by rfl) ⟨52211, by rfl⟩ : syracuseStep 1113845 = 104423) (by norm_num)
theorem B753413 : Blo 742328 753413 := bbase (se 4 (by rfl) ⟨70632, by rfl⟩ : syracuseStep 753413 = 141265) (by norm_num)
theorem B1113869 : Blo 742328 1113869 := bbase (se 3 (by rfl) ⟨208850, by rfl⟩ : syracuseStep 1113869 = 417701) (by norm_num)
theorem B1113893 : Blo 742328 1113893 := bbase (se 4 (by rfl) ⟨104427, by rfl⟩ : syracuseStep 1113893 = 208855) (by norm_num)
theorem B1670957 : Blo 742328 1670957 := bbase (se 3 (by rfl) ⟨313304, by rfl⟩ : syracuseStep 1670957 = 626609) (by norm_num)
theorem B6356789 : Blo 742328 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B1113917 : Blo 742328 1113917 := bbase (se 3 (by rfl) ⟨208859, by rfl⟩ : syracuseStep 1113917 = 417719) (by norm_num)
theorem B1113941 : Blo 742328 1113941 := bbase (se 9 (by rfl) ⟨3263, by rfl⟩ : syracuseStep 1113941 = 6527) (by norm_num)
theorem B1113965 : Blo 742328 1113965 := bbase (se 3 (by rfl) ⟨208868, by rfl⟩ : syracuseStep 1113965 = 417737) (by norm_num)
theorem B1671029 : Blo 742328 1671029 := bbase (se 5 (by rfl) ⟨78329, by rfl⟩ : syracuseStep 1671029 = 156659) (by norm_num)
theorem B1113989 : Blo 742328 1113989 := bbase (se 4 (by rfl) ⟨104436, by rfl⟩ : syracuseStep 1113989 = 208873) (by norm_num)
theorem B4030357 : Blo 742328 4030357 := bbase (se 6 (by rfl) ⟨94461, by rfl⟩ : syracuseStep 4030357 = 188923) (by norm_num)
theorem B1114013 : Blo 742328 1114013 := bbase (se 3 (by rfl) ⟨208877, by rfl⟩ : syracuseStep 1114013 = 417755) (by norm_num)
theorem B1114037 : Blo 742328 1114037 := bbase (se 5 (by rfl) ⟨52220, by rfl⟩ : syracuseStep 1114037 = 104441) (by norm_num)
theorem B1671101 : Blo 742328 1671101 := bbase (se 3 (by rfl) ⟨313331, by rfl⟩ : syracuseStep 1671101 = 626663) (by norm_num)
theorem B1114061 : Blo 742328 1114061 := bbase (se 3 (by rfl) ⟨208886, by rfl⟩ : syracuseStep 1114061 = 417773) (by norm_num)
theorem B1114085 : Blo 742328 1114085 := bbase (se 4 (by rfl) ⟨104445, by rfl⟩ : syracuseStep 1114085 = 208891) (by norm_num)
theorem B1114109 : Blo 742328 1114109 := bbase (se 3 (by rfl) ⟨208895, by rfl⟩ : syracuseStep 1114109 = 417791) (by norm_num)
theorem B1114115 : Blo 742328 1114115 := bstep (se 1 (by rfl) ⟨835586, by rfl⟩ : syracuseStep 1114115 = 1671173) B1671173
theorem B1114145 : Blo 742328 1114145 := bstep (se 2 (by rfl) ⟨417804, by rfl⟩ : syracuseStep 1114145 = 835609) B835609
theorem B3178531 : Blo 742328 3178531 := bstep (se 1 (by rfl) ⟨2383898, by rfl⟩ : syracuseStep 3178531 = 4767797) B4767797
theorem B1114163 : Blo 742328 1114163 := bstep (se 1 (by rfl) ⟨835622, by rfl⟩ : syracuseStep 1114163 = 1671245) B1671245
theorem B1114193 : Blo 742328 1114193 := bstep (se 2 (by rfl) ⟨417822, by rfl⟩ : syracuseStep 1114193 = 835645) B835645
theorem B1114211 : Blo 742328 1114211 := bstep (se 1 (by rfl) ⟨835658, by rfl⟩ : syracuseStep 1114211 = 1671317) B1671317
theorem B1671281 : Blo 742328 1671281 := bstep (se 2 (by rfl) ⟨626730, by rfl⟩ : syracuseStep 1671281 = 1253461) B1253461
theorem B1114241 : Blo 742328 1114241 := bstep (se 2 (by rfl) ⟨417840, by rfl⟩ : syracuseStep 1114241 = 835681) B835681
theorem B1671299 : Blo 742328 1671299 := bstep (se 1 (by rfl) ⟨1253474, by rfl⟩ : syracuseStep 1671299 = 2506949) B2506949
theorem B1114259 : Blo 742328 1114259 := bstep (se 1 (by rfl) ⟨835694, by rfl⟩ : syracuseStep 1114259 = 1671389) B1671389
theorem B1114289 : Blo 742328 1114289 := bstep (se 2 (by rfl) ⟨417858, by rfl⟩ : syracuseStep 1114289 = 835717) B835717
theorem B1114307 : Blo 742328 1114307 := bstep (se 1 (by rfl) ⟨835730, by rfl⟩ : syracuseStep 1114307 = 1671461) B1671461
theorem B1114337 : Blo 742328 1114337 := bstep (se 2 (by rfl) ⟨417876, by rfl⟩ : syracuseStep 1114337 = 835753) B835753
theorem B1114355 : Blo 742328 1114355 := bstep (se 1 (by rfl) ⟨835766, by rfl⟩ : syracuseStep 1114355 = 1671533) B1671533
theorem B1114385 : Blo 742328 1114385 := bstep (se 2 (by rfl) ⟨417894, by rfl⟩ : syracuseStep 1114385 = 835789) B835789
theorem B1114403 : Blo 742328 1114403 := bstep (se 1 (by rfl) ⟨835802, by rfl⟩ : syracuseStep 1114403 = 1671605) B1671605
theorem B1114433 : Blo 742328 1114433 := bstep (se 2 (by rfl) ⟨417912, by rfl⟩ : syracuseStep 1114433 = 835825) B835825
theorem B3572045 : Blo 742328 3572045 := bstep (se 3 (by rfl) ⟨669758, by rfl⟩ : syracuseStep 3572045 = 1339517) B1339517
theorem B1114451 : Blo 742328 1114451 := bstep (se 1 (by rfl) ⟨835838, by rfl⟩ : syracuseStep 1114451 = 1671677) B1671677
theorem B1409393 : Blo 742328 1409393 := bstep (se 2 (by rfl) ⟨528522, by rfl⟩ : syracuseStep 1409393 = 1057045) B1057045
theorem B1114481 : Blo 742328 1114481 := bstep (se 2 (by rfl) ⟨417930, by rfl⟩ : syracuseStep 1114481 = 835861) B835861
theorem B1114499 : Blo 742328 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B1671569 : Blo 742328 1671569 := bstep (se 2 (by rfl) ⟨626838, by rfl⟩ : syracuseStep 1671569 = 1253677) B1253677
theorem B1114529 : Blo 742328 1114529 := bstep (se 2 (by rfl) ⟨417948, by rfl⟩ : syracuseStep 1114529 = 835897) B835897
theorem B1671587 : Blo 742328 1671587 := bstep (se 1 (by rfl) ⟨1253690, by rfl⟩ : syracuseStep 1671587 = 2507381) B2507381
theorem B1114547 : Blo 742328 1114547 := bstep (se 1 (by rfl) ⟨835910, by rfl⟩ : syracuseStep 1114547 = 1671821) B1671821
theorem B1114577 : Blo 742328 1114577 := bstep (se 2 (by rfl) ⟨417966, by rfl⟩ : syracuseStep 1114577 = 835933) B835933
theorem B1114595 : Blo 742328 1114595 := bstep (se 1 (by rfl) ⟨835946, by rfl⟩ : syracuseStep 1114595 = 1671893) B1671893
theorem B1114625 : Blo 742328 1114625 := bstep (se 2 (by rfl) ⟨417984, by rfl⟩ : syracuseStep 1114625 = 835969) B835969
theorem B1114643 : Blo 742328 1114643 := bstep (se 1 (by rfl) ⟨835982, by rfl⟩ : syracuseStep 1114643 = 1671965) B1671965
theorem B1114673 : Blo 742328 1114673 := bstep (se 2 (by rfl) ⟨418002, by rfl⟩ : syracuseStep 1114673 = 836005) B836005
theorem B1114691 : Blo 742328 1114691 := bstep (se 1 (by rfl) ⟨836018, by rfl⟩ : syracuseStep 1114691 = 1672037) B1672037
theorem B1114721 : Blo 742328 1114721 := bstep (se 2 (by rfl) ⟨418020, by rfl⟩ : syracuseStep 1114721 = 836041) B836041
theorem B1114739 : Blo 742328 1114739 := bstep (se 1 (by rfl) ⟨836054, by rfl⟩ : syracuseStep 1114739 = 1672109) B1672109
theorem B1114769 : Blo 742328 1114769 := bstep (se 2 (by rfl) ⟨418038, by rfl⟩ : syracuseStep 1114769 = 836077) B836077
theorem B1114787 : Blo 742328 1114787 := bstep (se 1 (by rfl) ⟨836090, by rfl⟩ : syracuseStep 1114787 = 1672181) B1672181
theorem B1671857 : Blo 742328 1671857 := bstep (se 2 (by rfl) ⟨626946, by rfl⟩ : syracuseStep 1671857 = 1253893) B1253893
theorem B1114817 : Blo 742328 1114817 := bstep (se 2 (by rfl) ⟨418056, by rfl⟩ : syracuseStep 1114817 = 836113) B836113
theorem B1671875 : Blo 742328 1671875 := bstep (se 1 (by rfl) ⟨1253906, by rfl⟩ : syracuseStep 1671875 = 2507813) B2507813
theorem B1114835 : Blo 742328 1114835 := bstep (se 1 (by rfl) ⟨836126, by rfl⟩ : syracuseStep 1114835 = 1672253) B1672253
theorem B5079793 : Blo 742328 5079793 := bstep (se 2 (by rfl) ⟨1904922, by rfl⟩ : syracuseStep 5079793 = 3809845) B3809845
theorem B1114865 : Blo 742328 1114865 := bstep (se 2 (by rfl) ⟨418074, by rfl⟩ : syracuseStep 1114865 = 836149) B836149
theorem B1409795 : Blo 742328 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B1114883 : Blo 742328 1114883 := bstep (se 1 (by rfl) ⟨836162, by rfl⟩ : syracuseStep 1114883 = 1672325) B1672325
theorem B1344259 : Blo 742328 1344259 := bstep (se 1 (by rfl) ⟨1008194, by rfl⟩ : syracuseStep 1344259 = 2016389) B2016389
theorem B1114913 : Blo 742328 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B1114931 : Blo 742328 1114931 := bstep (se 1 (by rfl) ⟨836198, by rfl⟩ : syracuseStep 1114931 = 1672397) B1672397
theorem B4031309 : Blo 742328 4031309 := bstep (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) B1511741
theorem B1114961 : Blo 742328 1114961 := bstep (se 2 (by rfl) ⟨418110, by rfl⟩ : syracuseStep 1114961 = 836221) B836221
theorem B1114979 : Blo 742328 1114979 := bstep (se 1 (by rfl) ⟨836234, by rfl⟩ : syracuseStep 1114979 = 1672469) B1672469
theorem B1115009 : Blo 742328 1115009 := bstep (se 2 (by rfl) ⟨418128, by rfl⟩ : syracuseStep 1115009 = 836257) B836257
theorem B1115027 : Blo 742328 1115027 := bstep (se 1 (by rfl) ⟨836270, by rfl⟩ : syracuseStep 1115027 = 1672541) B1672541
theorem B1115057 : Blo 742328 1115057 := bstep (se 2 (by rfl) ⟨418146, by rfl⟩ : syracuseStep 1115057 = 836293) B836293
theorem B1115075 : Blo 742328 1115075 := bstep (se 1 (by rfl) ⟨836306, by rfl⟩ : syracuseStep 1115075 = 1672613) B1672613
theorem B1672145 : Blo 742328 1672145 := bstep (se 2 (by rfl) ⟨627054, by rfl⟩ : syracuseStep 1672145 = 1254109) B1254109
theorem B1115105 : Blo 742328 1115105 := bstep (se 2 (by rfl) ⟨418164, by rfl⟩ : syracuseStep 1115105 = 836329) B836329
theorem B1672163 : Blo 742328 1672163 := bstep (se 1 (by rfl) ⟨1254122, by rfl⟩ : syracuseStep 1672163 = 2508245) B2508245
theorem B1115123 : Blo 742328 1115123 := bstep (se 1 (by rfl) ⟨836342, by rfl⟩ : syracuseStep 1115123 = 1672685) B1672685
theorem B4228109 : Blo 742328 4228109 := bstep (se 3 (by rfl) ⟨792770, by rfl⟩ : syracuseStep 4228109 = 1585541) B1585541
theorem B1115153 : Blo 742328 1115153 := bstep (se 2 (by rfl) ⟨418182, by rfl⟩ : syracuseStep 1115153 = 836365) B836365
theorem B1115171 : Blo 742328 1115171 := bstep (se 1 (by rfl) ⟨836378, by rfl⟩ : syracuseStep 1115171 = 1672757) B1672757
theorem B1115201 : Blo 742328 1115201 := bstep (se 2 (by rfl) ⟨418200, by rfl⟩ : syracuseStep 1115201 = 836401) B836401
theorem B1115219 : Blo 742328 1115219 := bstep (se 1 (by rfl) ⟨836414, by rfl⟩ : syracuseStep 1115219 = 1672829) B1672829
theorem B1115249 : Blo 742328 1115249 := bstep (se 2 (by rfl) ⟨418218, by rfl⟩ : syracuseStep 1115249 = 836437) B836437
theorem B1115267 : Blo 742328 1115267 := bstep (se 1 (by rfl) ⟨836450, by rfl⟩ : syracuseStep 1115267 = 1672901) B1672901
theorem B1115297 : Blo 742328 1115297 := bstep (se 2 (by rfl) ⟨418236, by rfl⟩ : syracuseStep 1115297 = 836473) B836473
theorem B1115315 : Blo 742328 1115315 := bstep (se 1 (by rfl) ⟨836486, by rfl⟩ : syracuseStep 1115315 = 1672973) B1672973
theorem B1115345 : Blo 742328 1115345 := bstep (se 2 (by rfl) ⟨418254, by rfl⟩ : syracuseStep 1115345 = 836509) B836509
theorem B1115363 : Blo 742328 1115363 := bstep (se 1 (by rfl) ⟨836522, by rfl⟩ : syracuseStep 1115363 = 1673045) B1673045
theorem B1672433 : Blo 742328 1672433 := bstep (se 2 (by rfl) ⟨627162, by rfl⟩ : syracuseStep 1672433 = 1254325) B1254325
theorem B1115393 : Blo 742328 1115393 := bstep (se 2 (by rfl) ⟨418272, by rfl⟩ : syracuseStep 1115393 = 836545) B836545
theorem B1672451 : Blo 742328 1672451 := bstep (se 1 (by rfl) ⟨1254338, by rfl⟩ : syracuseStep 1672451 = 2508677) B2508677
theorem B1115411 : Blo 742328 1115411 := bstep (se 1 (by rfl) ⟨836558, by rfl⟩ : syracuseStep 1115411 = 1673117) B1673117
theorem B1115441 : Blo 742328 1115441 := bstep (se 2 (by rfl) ⟨418290, by rfl⟩ : syracuseStep 1115441 = 836581) B836581
theorem B1115459 : Blo 742328 1115459 := bstep (se 1 (by rfl) ⟨836594, by rfl⟩ : syracuseStep 1115459 = 1673189) B1673189
theorem B1115489 : Blo 742328 1115489 := bstep (se 2 (by rfl) ⟨418308, by rfl⟩ : syracuseStep 1115489 = 836617) B836617
theorem B1115507 : Blo 742328 1115507 := bstep (se 1 (by rfl) ⟨836630, by rfl⟩ : syracuseStep 1115507 = 1673261) B1673261
theorem B1115537 : Blo 742328 1115537 := bstep (se 2 (by rfl) ⟨418326, by rfl⟩ : syracuseStep 1115537 = 836653) B836653
theorem B1115555 : Blo 742328 1115555 := bstep (se 1 (by rfl) ⟨836666, by rfl⟩ : syracuseStep 1115555 = 1673333) B1673333
theorem B1115585 : Blo 742328 1115585 := bstep (se 2 (by rfl) ⟨418344, by rfl⟩ : syracuseStep 1115585 = 836689) B836689
theorem B2688461 : Blo 742328 2688461 := bstep (se 3 (by rfl) ⟨504086, by rfl⟩ : syracuseStep 2688461 = 1008173) B1008173
theorem B1115603 : Blo 742328 1115603 := bstep (se 1 (by rfl) ⟨836702, by rfl⟩ : syracuseStep 1115603 = 1673405) B1673405
theorem B6358499 : Blo 742328 6358499 := bstep (se 1 (by rfl) ⟨4768874, by rfl⟩ : syracuseStep 6358499 = 9537749) B9537749
theorem B1115633 : Blo 742328 1115633 := bstep (se 2 (by rfl) ⟨418362, by rfl⟩ : syracuseStep 1115633 = 836725) B836725
theorem B1115651 : Blo 742328 1115651 := bstep (se 1 (by rfl) ⟨836738, by rfl⟩ : syracuseStep 1115651 = 1673477) B1673477
theorem B1672721 : Blo 742328 1672721 := bstep (se 2 (by rfl) ⟨627270, by rfl⟩ : syracuseStep 1672721 = 1254541) B1254541
theorem B1115681 : Blo 742328 1115681 := bstep (se 2 (by rfl) ⟨418380, by rfl⟩ : syracuseStep 1115681 = 836761) B836761
theorem B1672739 : Blo 742328 1672739 := bstep (se 1 (by rfl) ⟨1254554, by rfl⟩ : syracuseStep 1672739 = 2509109) B2509109
theorem B1115699 : Blo 742328 1115699 := bstep (se 1 (by rfl) ⟨836774, by rfl⟩ : syracuseStep 1115699 = 1673549) B1673549
theorem B15238709 : Blo 742328 15238709 := bstep (se 5 (by rfl) ⟨714314, by rfl⟩ : syracuseStep 15238709 = 1428629) B1428629
theorem B1115729 : Blo 742328 1115729 := bstep (se 2 (by rfl) ⟨418398, by rfl⟩ : syracuseStep 1115729 = 836797) B836797
theorem B1115747 : Blo 742328 1115747 := bstep (se 1 (by rfl) ⟨836810, by rfl⟩ : syracuseStep 1115747 = 1673621) B1673621
theorem B1115777 : Blo 742328 1115777 := bstep (se 2 (by rfl) ⟨418416, by rfl⟩ : syracuseStep 1115777 = 836833) B836833
theorem B1410691 : Blo 742328 1410691 := bstep (se 1 (by rfl) ⟨1058018, by rfl⟩ : syracuseStep 1410691 = 2116037) B2116037
theorem B1115795 : Blo 742328 1115795 := bstep (se 1 (by rfl) ⟨836846, by rfl⟩ : syracuseStep 1115795 = 1673693) B1673693
theorem B1115825 : Blo 742328 1115825 := bstep (se 2 (by rfl) ⟨418434, by rfl⟩ : syracuseStep 1115825 = 836869) B836869
theorem B1115843 : Blo 742328 1115843 := bstep (se 1 (by rfl) ⟨836882, by rfl⟩ : syracuseStep 1115843 = 1673765) B1673765
theorem B1115873 : Blo 742328 1115873 := bstep (se 2 (by rfl) ⟨418452, by rfl⟩ : syracuseStep 1115873 = 836905) B836905
theorem B1115891 : Blo 742328 1115891 := bstep (se 1 (by rfl) ⟨836918, by rfl⟩ : syracuseStep 1115891 = 1673837) B1673837
theorem B1115921 : Blo 742328 1115921 := bstep (se 2 (by rfl) ⟨418470, by rfl⟩ : syracuseStep 1115921 = 836941) B836941
theorem B19040021 : Blo 742328 19040021 := bstep (se 6 (by rfl) ⟨446250, by rfl⟩ : syracuseStep 19040021 = 892501) B892501
theorem B1410851 : Blo 742328 1410851 := bstep (se 1 (by rfl) ⟨1058138, by rfl⟩ : syracuseStep 1410851 = 2116277) B2116277
theorem B1115939 : Blo 742328 1115939 := bstep (se 1 (by rfl) ⟨836954, by rfl⟩ : syracuseStep 1115939 = 1673909) B1673909
theorem B1673009 : Blo 742328 1673009 := bstep (se 2 (by rfl) ⟨627378, by rfl⟩ : syracuseStep 1673009 = 1254757) B1254757
theorem B1115969 : Blo 742328 1115969 := bstep (se 2 (by rfl) ⟨418488, by rfl⟩ : syracuseStep 1115969 = 836977) B836977
theorem B1673027 : Blo 742328 1673027 := bstep (se 1 (by rfl) ⟨1254770, by rfl⟩ : syracuseStep 1673027 = 2509541) B2509541
theorem B1115987 : Blo 742328 1115987 := bstep (se 1 (by rfl) ⟨836990, by rfl⟩ : syracuseStep 1115987 = 1673981) B1673981
theorem B1116017 : Blo 742328 1116017 := bstep (se 2 (by rfl) ⟨418506, by rfl⟩ : syracuseStep 1116017 = 837013) B837013
theorem B3770225 : Blo 742328 3770225 := bstep (se 2 (by rfl) ⟨1413834, by rfl⟩ : syracuseStep 3770225 = 2827669) B2827669
theorem B1116035 : Blo 742328 1116035 := bstep (se 1 (by rfl) ⟨837026, by rfl⟩ : syracuseStep 1116035 = 1674053) B1674053
theorem B1116065 : Blo 742328 1116065 := bstep (se 2 (by rfl) ⟨418524, by rfl⟩ : syracuseStep 1116065 = 837049) B837049
theorem B1116083 : Blo 742328 1116083 := bstep (se 1 (by rfl) ⟨837062, by rfl⟩ : syracuseStep 1116083 = 1674125) B1674125
theorem B5638085 : Blo 742328 5638085 := bstep (se 4 (by rfl) ⟨528570, by rfl⟩ : syracuseStep 5638085 = 1057141) B1057141
theorem B1116113 : Blo 742328 1116113 := bstep (se 2 (by rfl) ⟨418542, by rfl⟩ : syracuseStep 1116113 = 837085) B837085
theorem B1116131 : Blo 742328 1116131 := bstep (se 1 (by rfl) ⟨837098, by rfl⟩ : syracuseStep 1116131 = 1674197) B1674197
theorem B1116161 : Blo 742328 1116161 := bstep (se 2 (by rfl) ⟨418560, by rfl⟩ : syracuseStep 1116161 = 837121) B837121
theorem B4032517 : Blo 742328 4032517 := bstep (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) B756097
theorem B1116179 : Blo 742328 1116179 := bstep (se 1 (by rfl) ⟨837134, by rfl⟩ : syracuseStep 1116179 = 1674269) B1674269
theorem B1116209 : Blo 742328 1116209 := bstep (se 2 (by rfl) ⟨418578, by rfl⟩ : syracuseStep 1116209 = 837157) B837157
theorem B1116227 : Blo 742328 1116227 := bstep (se 1 (by rfl) ⟨837170, by rfl⟩ : syracuseStep 1116227 = 1674341) B1674341
theorem B1673297 : Blo 742328 1673297 := bstep (se 2 (by rfl) ⟨627486, by rfl⟩ : syracuseStep 1673297 = 1254973) B1254973
theorem B1116257 : Blo 742328 1116257 := bstep (se 2 (by rfl) ⟨418596, by rfl⟩ : syracuseStep 1116257 = 837193) B837193
theorem B1673315 : Blo 742328 1673315 := bstep (se 1 (by rfl) ⟨1254986, by rfl⟩ : syracuseStep 1673315 = 2509973) B2509973
theorem B1116275 : Blo 742328 1116275 := bstep (se 1 (by rfl) ⟨837206, by rfl⟩ : syracuseStep 1116275 = 1674413) B1674413
theorem B1116305 : Blo 742328 1116305 := bstep (se 2 (by rfl) ⟨418614, by rfl⟩ : syracuseStep 1116305 = 837229) B837229
theorem B1116323 : Blo 742328 1116323 := bstep (se 1 (by rfl) ⟨837242, by rfl⟩ : syracuseStep 1116323 = 1674485) B1674485
theorem B1018049 : Blo 742328 1018049 := bstep (se 2 (by rfl) ⟨381768, by rfl⟩ : syracuseStep 1018049 = 763537) B763537
theorem B1116353 : Blo 742328 1116353 := bstep (se 2 (by rfl) ⟨418632, by rfl⟩ : syracuseStep 1116353 = 837265) B837265
theorem B1116371 : Blo 742328 1116371 := bstep (se 1 (by rfl) ⟨837278, by rfl⟩ : syracuseStep 1116371 = 1674557) B1674557
theorem B1116401 : Blo 742328 1116401 := bstep (se 2 (by rfl) ⟨418650, by rfl⟩ : syracuseStep 1116401 = 837301) B837301
theorem B1116419 : Blo 742328 1116419 := bstep (se 1 (by rfl) ⟨837314, by rfl⟩ : syracuseStep 1116419 = 1674629) B1674629
theorem B2820365 : Blo 742328 2820365 := bstep (se 3 (by rfl) ⟨528818, by rfl⟩ : syracuseStep 2820365 = 1057637) B1057637
theorem B1116449 : Blo 742328 1116449 := bstep (se 2 (by rfl) ⟨418668, by rfl⟩ : syracuseStep 1116449 = 837337) B837337
theorem B1116467 : Blo 742328 1116467 := bstep (se 1 (by rfl) ⟨837350, by rfl⟩ : syracuseStep 1116467 = 1674701) B1674701
theorem B1116497 : Blo 742328 1116497 := bstep (se 2 (by rfl) ⟨418686, by rfl⟩ : syracuseStep 1116497 = 837373) B837373
theorem B1116515 : Blo 742328 1116515 := bstep (se 1 (by rfl) ⟨837386, by rfl⟩ : syracuseStep 1116515 = 1674773) B1674773
theorem B1673585 : Blo 742328 1673585 := bstep (se 2 (by rfl) ⟨627594, by rfl⟩ : syracuseStep 1673585 = 1255189) B1255189
theorem B1116545 : Blo 742328 1116545 := bstep (se 2 (by rfl) ⟨418704, by rfl⟩ : syracuseStep 1116545 = 837409) B837409
theorem B1673603 : Blo 742328 1673603 := bstep (se 1 (by rfl) ⟨1255202, by rfl⟩ : syracuseStep 1673603 = 2510405) B2510405
theorem B2263427 : Blo 742328 2263427 := bstep (se 1 (by rfl) ⟨1697570, by rfl⟩ : syracuseStep 2263427 = 3395141) B3395141
theorem B1378691 : Blo 742328 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B1116563 : Blo 742328 1116563 := bstep (se 1 (by rfl) ⟨837422, by rfl⟩ : syracuseStep 1116563 = 1674845) B1674845
theorem B1116593 : Blo 742328 1116593 := bstep (se 2 (by rfl) ⟨418722, by rfl⟩ : syracuseStep 1116593 = 837445) B837445
theorem B3180977 : Blo 742328 3180977 := bstep (se 2 (by rfl) ⟨1192866, by rfl⟩ : syracuseStep 3180977 = 2385733) B2385733
theorem B1116611 : Blo 742328 1116611 := bstep (se 1 (by rfl) ⟨837458, by rfl⟩ : syracuseStep 1116611 = 1674917) B1674917
theorem B1116641 : Blo 742328 1116641 := bstep (se 2 (by rfl) ⟨418740, by rfl⟩ : syracuseStep 1116641 = 837481) B837481
theorem B4524515 : Blo 742328 4524515 := bstep (se 1 (by rfl) ⟨3393386, by rfl⟩ : syracuseStep 4524515 = 6786773) B6786773
theorem B1116659 : Blo 742328 1116659 := bstep (se 1 (by rfl) ⟨837494, by rfl⟩ : syracuseStep 1116659 = 1674989) B1674989
theorem B1116689 : Blo 742328 1116689 := bstep (se 2 (by rfl) ⟨418758, by rfl⟩ : syracuseStep 1116689 = 837517) B837517
theorem B1116707 : Blo 742328 1116707 := bstep (se 1 (by rfl) ⟨837530, by rfl⟩ : syracuseStep 1116707 = 1675061) B1675061
theorem B1116737 : Blo 742328 1116737 := bstep (se 2 (by rfl) ⟨418776, by rfl⟩ : syracuseStep 1116737 = 837553) B837553
theorem B1116755 : Blo 742328 1116755 := bstep (se 1 (by rfl) ⟨837566, by rfl⟩ : syracuseStep 1116755 = 1675133) B1675133
theorem B1116785 : Blo 742328 1116785 := bstep (se 2 (by rfl) ⟨418794, by rfl⟩ : syracuseStep 1116785 = 837589) B837589
theorem B1116803 : Blo 742328 1116803 := bstep (se 1 (by rfl) ⟨837602, by rfl⟩ : syracuseStep 1116803 = 1675205) B1675205
theorem B1673873 : Blo 742328 1673873 := bstep (se 2 (by rfl) ⟨627702, by rfl⟩ : syracuseStep 1673873 = 1255405) B1255405
theorem B1116833 : Blo 742328 1116833 := bstep (se 2 (by rfl) ⟨418812, by rfl⟩ : syracuseStep 1116833 = 837625) B837625
theorem B1673891 : Blo 742328 1673891 := bstep (se 1 (by rfl) ⟨1255418, by rfl⟩ : syracuseStep 1673891 = 2510837) B2510837
theorem B1116851 : Blo 742328 1116851 := bstep (se 1 (by rfl) ⟨837638, by rfl⟩ : syracuseStep 1116851 = 1675277) B1675277
theorem B1116881 : Blo 742328 1116881 := bstep (se 2 (by rfl) ⟨418830, by rfl⟩ : syracuseStep 1116881 = 837661) B837661
theorem B1116899 : Blo 742328 1116899 := bstep (se 1 (by rfl) ⟨837674, by rfl⟩ : syracuseStep 1116899 = 1675349) B1675349
theorem B1116929 : Blo 742328 1116929 := bstep (se 2 (by rfl) ⟨418848, by rfl⟩ : syracuseStep 1116929 = 837697) B837697
theorem B1116947 : Blo 742328 1116947 := bstep (se 1 (by rfl) ⟨837710, by rfl⟩ : syracuseStep 1116947 = 1675421) B1675421
theorem B1116977 : Blo 742328 1116977 := bstep (se 2 (by rfl) ⟨418866, by rfl⟩ : syracuseStep 1116977 = 837733) B837733
theorem B1116995 : Blo 742328 1116995 := bstep (se 1 (by rfl) ⟨837746, by rfl⟩ : syracuseStep 1116995 = 1675493) B1675493
theorem B1411921 : Blo 742328 1411921 := bstep (se 2 (by rfl) ⟨529470, by rfl⟩ : syracuseStep 1411921 = 1058941) B1058941
theorem B1117025 : Blo 742328 1117025 := bstep (se 2 (by rfl) ⟨418884, by rfl⟩ : syracuseStep 1117025 = 837769) B837769
theorem B1117043 : Blo 742328 1117043 := bstep (se 1 (by rfl) ⟨837782, by rfl⟩ : syracuseStep 1117043 = 1675565) B1675565
theorem B1117073 : Blo 742328 1117073 := bstep (se 2 (by rfl) ⟨418902, by rfl⟩ : syracuseStep 1117073 = 837805) B837805
theorem B1117091 : Blo 742328 1117091 := bstep (se 1 (by rfl) ⟨837818, by rfl⟩ : syracuseStep 1117091 = 1675637) B1675637
theorem B1674161 : Blo 742328 1674161 := bstep (se 2 (by rfl) ⟨627810, by rfl⟩ : syracuseStep 1674161 = 1255621) B1255621
theorem B1117121 : Blo 742328 1117121 := bstep (se 2 (by rfl) ⟨418920, by rfl⟩ : syracuseStep 1117121 = 837841) B837841
theorem B1674179 : Blo 742328 1674179 := bstep (se 1 (by rfl) ⟨1255634, by rfl⟩ : syracuseStep 1674179 = 2511269) B2511269
theorem B1117139 : Blo 742328 1117139 := bstep (se 1 (by rfl) ⟨837854, by rfl⟩ : syracuseStep 1117139 = 1675709) B1675709
theorem B1117169 : Blo 742328 1117169 := bstep (se 2 (by rfl) ⟨418938, by rfl⟩ : syracuseStep 1117169 = 837877) B837877
theorem B1117187 : Blo 742328 1117187 := bstep (se 1 (by rfl) ⟨837890, by rfl⟩ : syracuseStep 1117187 = 1675781) B1675781
theorem B1117217 : Blo 742328 1117217 := bstep (se 2 (by rfl) ⟨418956, by rfl⟩ : syracuseStep 1117217 = 837913) B837913
theorem B2821169 : Blo 742328 2821169 := bstep (se 2 (by rfl) ⟨1057938, by rfl⟩ : syracuseStep 2821169 = 2115877) B2115877
theorem B1117235 : Blo 742328 1117235 := bstep (se 1 (by rfl) ⟨837926, by rfl⟩ : syracuseStep 1117235 = 1675853) B1675853
theorem B1117265 : Blo 742328 1117265 := bstep (se 2 (by rfl) ⟨418974, by rfl⟩ : syracuseStep 1117265 = 837949) B837949
theorem B1117283 : Blo 742328 1117283 := bstep (se 1 (by rfl) ⟨837962, by rfl⟩ : syracuseStep 1117283 = 1675925) B1675925
theorem B1117313 : Blo 742328 1117313 := bstep (se 2 (by rfl) ⟨418992, by rfl⟩ : syracuseStep 1117313 = 837985) B837985
theorem B1117331 : Blo 742328 1117331 := bstep (se 1 (by rfl) ⟨837998, by rfl⟩ : syracuseStep 1117331 = 1675997) B1675997
theorem B1117361 : Blo 742328 1117361 := bstep (se 2 (by rfl) ⟨419010, by rfl⟩ : syracuseStep 1117361 = 838021) B838021
theorem B1117379 : Blo 742328 1117379 := bstep (se 1 (by rfl) ⟨838034, by rfl⟩ : syracuseStep 1117379 = 1676069) B1676069
theorem B3214541 : Blo 742328 3214541 := bstep (se 3 (by rfl) ⟨602726, by rfl⟩ : syracuseStep 3214541 = 1205453) B1205453
theorem B1674449 : Blo 742328 1674449 := bstep (se 2 (by rfl) ⟨627918, by rfl⟩ : syracuseStep 1674449 = 1255837) B1255837
theorem B1117409 : Blo 742328 1117409 := bstep (se 2 (by rfl) ⟨419028, by rfl⟩ : syracuseStep 1117409 = 838057) B838057
theorem B1674467 : Blo 742328 1674467 := bstep (se 1 (by rfl) ⟨1255850, by rfl⟩ : syracuseStep 1674467 = 2511701) B2511701
theorem B1117427 : Blo 742328 1117427 := bstep (se 1 (by rfl) ⟨838070, by rfl⟩ : syracuseStep 1117427 = 1676141) B1676141
theorem B1117457 : Blo 742328 1117457 := bstep (se 2 (by rfl) ⟨419046, by rfl⟩ : syracuseStep 1117457 = 838093) B838093
theorem B1117475 : Blo 742328 1117475 := bstep (se 1 (by rfl) ⟨838106, by rfl⟩ : syracuseStep 1117475 = 1676213) B1676213
theorem B3771683 : Blo 742328 3771683 := bstep (se 1 (by rfl) ⟨2828762, by rfl⟩ : syracuseStep 3771683 = 5657525) B5657525
theorem B1117505 : Blo 742328 1117505 := bstep (se 2 (by rfl) ⟨419064, by rfl⟩ : syracuseStep 1117505 = 838129) B838129
theorem B1117523 : Blo 742328 1117523 := bstep (se 1 (by rfl) ⟨838142, by rfl⟩ : syracuseStep 1117523 = 1676285) B1676285
theorem B1117553 : Blo 742328 1117553 := bstep (se 2 (by rfl) ⟨419082, by rfl⟩ : syracuseStep 1117553 = 838165) B838165
theorem B1117571 : Blo 742328 1117571 := bstep (se 1 (by rfl) ⟨838178, by rfl⟩ : syracuseStep 1117571 = 1676357) B1676357
theorem B1117601 : Blo 742328 1117601 := bstep (se 2 (by rfl) ⟨419100, by rfl⟩ : syracuseStep 1117601 = 838201) B838201
theorem B3018161 : Blo 742328 3018161 := bstep (se 2 (by rfl) ⟨1131810, by rfl⟩ : syracuseStep 3018161 = 2263621) B2263621
theorem B1117619 : Blo 742328 1117619 := bstep (se 1 (by rfl) ⟨838214, by rfl⟩ : syracuseStep 1117619 = 1676429) B1676429
theorem B1117649 : Blo 742328 1117649 := bstep (se 2 (by rfl) ⟨419118, by rfl⟩ : syracuseStep 1117649 = 838237) B838237
theorem B1117667 : Blo 742328 1117667 := bstep (se 1 (by rfl) ⟨838250, by rfl⟩ : syracuseStep 1117667 = 1676501) B1676501
theorem B1674737 : Blo 742328 1674737 := bstep (se 2 (by rfl) ⟨628026, by rfl⟩ : syracuseStep 1674737 = 1256053) B1256053
theorem B1117697 : Blo 742328 1117697 := bstep (se 2 (by rfl) ⟨419136, by rfl⟩ : syracuseStep 1117697 = 838273) B838273
theorem B1674755 : Blo 742328 1674755 := bstep (se 1 (by rfl) ⟨1256066, by rfl⟩ : syracuseStep 1674755 = 2512133) B2512133
theorem B1117715 : Blo 742328 1117715 := bstep (se 1 (by rfl) ⟨838286, by rfl⟩ : syracuseStep 1117715 = 1676573) B1676573
theorem B1117745 : Blo 742328 1117745 := bstep (se 2 (by rfl) ⟨419154, by rfl⟩ : syracuseStep 1117745 = 838309) B838309
theorem B1117763 : Blo 742328 1117763 := bstep (se 1 (by rfl) ⟨838322, by rfl⟩ : syracuseStep 1117763 = 1676645) B1676645
theorem B1117793 : Blo 742328 1117793 := bstep (se 2 (by rfl) ⟨419172, by rfl⟩ : syracuseStep 1117793 = 838345) B838345
theorem B4034161 : Blo 742328 4034161 := bstep (se 2 (by rfl) ⟨1512810, by rfl⟩ : syracuseStep 4034161 = 3025621) B3025621
theorem B1117811 : Blo 742328 1117811 := bstep (se 1 (by rfl) ⟨838358, by rfl⟩ : syracuseStep 1117811 = 1676717) B1676717
theorem B1117841 : Blo 742328 1117841 := bstep (se 2 (by rfl) ⟨419190, by rfl⟩ : syracuseStep 1117841 = 838381) B838381
theorem B1117859 : Blo 742328 1117859 := bstep (se 1 (by rfl) ⟨838394, by rfl⟩ : syracuseStep 1117859 = 1676789) B1676789
theorem B9178805 : Blo 742328 9178805 := bstep (se 5 (by rfl) ⟨430256, by rfl⟩ : syracuseStep 9178805 = 860513) B860513
theorem B1117889 : Blo 742328 1117889 := bstep (se 2 (by rfl) ⟨419208, by rfl⟩ : syracuseStep 1117889 = 838417) B838417
theorem B2821837 : Blo 742328 2821837 := bstep (se 3 (by rfl) ⟨529094, by rfl⟩ : syracuseStep 2821837 = 1058189) B1058189
theorem B4296397 : Blo 742328 4296397 := bstep (se 3 (by rfl) ⟨805574, by rfl⟩ : syracuseStep 4296397 = 1611149) B1611149
theorem B1117907 : Blo 742328 1117907 := bstep (se 1 (by rfl) ⟨838430, by rfl⟩ : syracuseStep 1117907 = 1676861) B1676861
theorem B1117937 : Blo 742328 1117937 := bstep (se 2 (by rfl) ⟨419226, by rfl⟩ : syracuseStep 1117937 = 838453) B838453
theorem B1117955 : Blo 742328 1117955 := bstep (se 1 (by rfl) ⟨838466, by rfl⟩ : syracuseStep 1117955 = 1676933) B1676933
theorem B1675025 : Blo 742328 1675025 := bstep (se 2 (by rfl) ⟨628134, by rfl⟩ : syracuseStep 1675025 = 1256269) B1256269
theorem B1117985 : Blo 742328 1117985 := bstep (se 2 (by rfl) ⟨419244, by rfl⟩ : syracuseStep 1117985 = 838489) B838489
theorem B1675043 : Blo 742328 1675043 := bstep (se 1 (by rfl) ⟨1256282, by rfl⟩ : syracuseStep 1675043 = 2512565) B2512565
theorem B1118003 : Blo 742328 1118003 := bstep (se 1 (by rfl) ⟨838502, by rfl⟩ : syracuseStep 1118003 = 1677005) B1677005
theorem B1118033 : Blo 742328 1118033 := bstep (se 2 (by rfl) ⟨419262, by rfl⟩ : syracuseStep 1118033 = 838525) B838525
theorem B1118051 : Blo 742328 1118051 := bstep (se 1 (by rfl) ⟨838538, by rfl⟩ : syracuseStep 1118051 = 1677077) B1677077
theorem B4231025 : Blo 742328 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B1412977 : Blo 742328 1412977 := bstep (se 2 (by rfl) ⟨529866, by rfl⟩ : syracuseStep 1412977 = 1059733) B1059733
theorem B1118081 : Blo 742328 1118081 := bstep (se 2 (by rfl) ⟨419280, by rfl⟩ : syracuseStep 1118081 = 838561) B838561
theorem B2723725 : Blo 742328 2723725 := bstep (se 3 (by rfl) ⟨510698, by rfl⟩ : syracuseStep 2723725 = 1021397) B1021397
theorem B1118099 : Blo 742328 1118099 := bstep (se 1 (by rfl) ⟨838574, by rfl⟩ : syracuseStep 1118099 = 1677149) B1677149
theorem B1118129 : Blo 742328 1118129 := bstep (se 2 (by rfl) ⟨419298, by rfl⟩ : syracuseStep 1118129 = 838597) B838597
theorem B1118147 : Blo 742328 1118147 := bstep (se 1 (by rfl) ⟨838610, by rfl⟩ : syracuseStep 1118147 = 1677221) B1677221
theorem B1118177 : Blo 742328 1118177 := bstep (se 2 (by rfl) ⟨419316, by rfl⟩ : syracuseStep 1118177 = 838633) B838633
theorem B1118195 : Blo 742328 1118195 := bstep (se 1 (by rfl) ⟨838646, by rfl⟩ : syracuseStep 1118195 = 1677293) B1677293
theorem B1118225 : Blo 742328 1118225 := bstep (se 2 (by rfl) ⟨419334, by rfl⟩ : syracuseStep 1118225 = 838669) B838669
theorem B1904675 : Blo 742328 1904675 := bstep (se 1 (by rfl) ⟨1428506, by rfl⟩ : syracuseStep 1904675 = 2857013) B2857013
theorem B1118243 : Blo 742328 1118243 := bstep (se 1 (by rfl) ⟨838682, by rfl⟩ : syracuseStep 1118243 = 1677365) B1677365
theorem B1675313 : Blo 742328 1675313 := bstep (se 2 (by rfl) ⟨628242, by rfl⟩ : syracuseStep 1675313 = 1256485) B1256485
theorem B1118273 : Blo 742328 1118273 := bstep (se 2 (by rfl) ⟨419352, by rfl⟩ : syracuseStep 1118273 = 838705) B838705
theorem B1675331 : Blo 742328 1675331 := bstep (se 1 (by rfl) ⟨1256498, by rfl⟩ : syracuseStep 1675331 = 2512997) B2512997
theorem B3772493 : Blo 742328 3772493 := bstep (se 3 (by rfl) ⟨707342, by rfl⟩ : syracuseStep 3772493 = 1414685) B1414685
theorem B1118291 : Blo 742328 1118291 := bstep (se 1 (by rfl) ⟨838718, by rfl⟩ : syracuseStep 1118291 = 1677437) B1677437
theorem B1118321 : Blo 742328 1118321 := bstep (se 2 (by rfl) ⟨419370, by rfl⟩ : syracuseStep 1118321 = 838741) B838741
theorem B1118339 : Blo 742328 1118339 := bstep (se 1 (by rfl) ⟨838754, by rfl⟩ : syracuseStep 1118339 = 1677509) B1677509
theorem B1118369 : Blo 742328 1118369 := bstep (se 2 (by rfl) ⟨419388, by rfl⟩ : syracuseStep 1118369 = 838777) B838777
theorem B1118387 : Blo 742328 1118387 := bstep (se 1 (by rfl) ⟨838790, by rfl⟩ : syracuseStep 1118387 = 1677581) B1677581
theorem B1118417 : Blo 742328 1118417 := bstep (se 2 (by rfl) ⟨419406, by rfl⟩ : syracuseStep 1118417 = 838813) B838813
theorem B1118435 : Blo 742328 1118435 := bstep (se 1 (by rfl) ⟨838826, by rfl⟩ : syracuseStep 1118435 = 1677653) B1677653
theorem B1118465 : Blo 742328 1118465 := bstep (se 2 (by rfl) ⟨419424, by rfl⟩ : syracuseStep 1118465 = 838849) B838849
theorem B1413379 : Blo 742328 1413379 := bstep (se 1 (by rfl) ⟨1060034, by rfl⟩ : syracuseStep 1413379 = 2120069) B2120069
theorem B1118483 : Blo 742328 1118483 := bstep (se 1 (by rfl) ⟨838862, by rfl⟩ : syracuseStep 1118483 = 1677725) B1677725
theorem B1413425 : Blo 742328 1413425 := bstep (se 2 (by rfl) ⟨530034, by rfl⟩ : syracuseStep 1413425 = 1060069) B1060069
theorem B1118513 : Blo 742328 1118513 := bstep (se 2 (by rfl) ⟨419442, by rfl⟩ : syracuseStep 1118513 = 838885) B838885
theorem B1118531 : Blo 742328 1118531 := bstep (se 1 (by rfl) ⟨838898, by rfl⟩ : syracuseStep 1118531 = 1677797) B1677797
theorem B1675601 : Blo 742328 1675601 := bstep (se 2 (by rfl) ⟨628350, by rfl⟩ : syracuseStep 1675601 = 1256701) B1256701
theorem B1118561 : Blo 742328 1118561 := bstep (se 2 (by rfl) ⟨419460, by rfl⟩ : syracuseStep 1118561 = 838921) B838921
theorem B1675619 : Blo 742328 1675619 := bstep (se 1 (by rfl) ⟨1256714, by rfl⟩ : syracuseStep 1675619 = 2513429) B2513429
theorem B1118579 : Blo 742328 1118579 := bstep (se 1 (by rfl) ⟨838934, by rfl⟩ : syracuseStep 1118579 = 1677869) B1677869
theorem B1118609 : Blo 742328 1118609 := bstep (se 2 (by rfl) ⟨419478, by rfl⟩ : syracuseStep 1118609 = 838957) B838957
theorem B1118627 : Blo 742328 1118627 := bstep (se 1 (by rfl) ⟨838970, by rfl⟩ : syracuseStep 1118627 = 1677941) B1677941
theorem B1118657 : Blo 742328 1118657 := bstep (se 2 (by rfl) ⟨419496, by rfl⟩ : syracuseStep 1118657 = 838993) B838993
theorem B1118675 : Blo 742328 1118675 := bstep (se 1 (by rfl) ⟨839006, by rfl⟩ : syracuseStep 1118675 = 1678013) B1678013
theorem B2822627 : Blo 742328 2822627 := bstep (se 1 (by rfl) ⟨2116970, by rfl⟩ : syracuseStep 2822627 = 4233941) B4233941
theorem B1118705 : Blo 742328 1118705 := bstep (se 2 (by rfl) ⟨419514, by rfl⟩ : syracuseStep 1118705 = 839029) B839029
theorem B2036227 : Blo 742328 2036227 := bstep (se 1 (by rfl) ⟨1527170, by rfl⟩ : syracuseStep 2036227 = 3054341) B3054341
theorem B1118723 : Blo 742328 1118723 := bstep (se 1 (by rfl) ⟨839042, by rfl⟩ : syracuseStep 1118723 = 1678085) B1678085
theorem B1118753 : Blo 742328 1118753 := bstep (se 2 (by rfl) ⟨419532, by rfl⟩ : syracuseStep 1118753 = 839065) B839065
theorem B1118771 : Blo 742328 1118771 := bstep (se 1 (by rfl) ⟨839078, by rfl⟩ : syracuseStep 1118771 = 1678157) B1678157
theorem B2036305 : Blo 742328 2036305 := bstep (se 2 (by rfl) ⟨763614, by rfl⟩ : syracuseStep 2036305 = 1527229) B1527229
theorem B1413713 : Blo 742328 1413713 := bstep (se 2 (by rfl) ⟨530142, by rfl⟩ : syracuseStep 1413713 = 1060285) B1060285
theorem B1512017 : Blo 742328 1512017 := bstep (se 2 (by rfl) ⟨567006, by rfl⟩ : syracuseStep 1512017 = 1134013) B1134013
theorem B1118801 : Blo 742328 1118801 := bstep (se 2 (by rfl) ⟨419550, by rfl⟩ : syracuseStep 1118801 = 839101) B839101
theorem B1118819 : Blo 742328 1118819 := bstep (se 1 (by rfl) ⟨839114, by rfl⟩ : syracuseStep 1118819 = 1678229) B1678229
theorem B1675889 : Blo 742328 1675889 := bstep (se 2 (by rfl) ⟨628458, by rfl⟩ : syracuseStep 1675889 = 1256917) B1256917
theorem B1118849 : Blo 742328 1118849 := bstep (se 2 (by rfl) ⟨419568, by rfl⟩ : syracuseStep 1118849 = 839137) B839137
theorem B1675907 : Blo 742328 1675907 := bstep (se 1 (by rfl) ⟨1256930, by rfl⟩ : syracuseStep 1675907 = 2513861) B2513861
theorem B1118867 : Blo 742328 1118867 := bstep (se 1 (by rfl) ⟨839150, by rfl⟩ : syracuseStep 1118867 = 1678301) B1678301
theorem B1118897 : Blo 742328 1118897 := bstep (se 2 (by rfl) ⟨419586, by rfl⟩ : syracuseStep 1118897 = 839173) B839173
theorem B1118915 : Blo 742328 1118915 := bstep (se 1 (by rfl) ⟨839186, by rfl⟩ : syracuseStep 1118915 = 1678373) B1678373
theorem B1118945 : Blo 742328 1118945 := bstep (se 2 (by rfl) ⟨419604, by rfl⟩ : syracuseStep 1118945 = 839209) B839209
theorem B1118963 : Blo 742328 1118963 := bstep (se 1 (by rfl) ⟨839222, by rfl⟩ : syracuseStep 1118963 = 1678445) B1678445
theorem B1118993 : Blo 742328 1118993 := bstep (se 2 (by rfl) ⟨419622, by rfl⟩ : syracuseStep 1118993 = 839245) B839245
theorem B1119011 : Blo 742328 1119011 := bstep (se 1 (by rfl) ⟨839258, by rfl⟩ : syracuseStep 1119011 = 1678517) B1678517
theorem B1119041 : Blo 742328 1119041 := bstep (se 2 (by rfl) ⟨419640, by rfl⟩ : syracuseStep 1119041 = 839281) B839281
theorem B1119059 : Blo 742328 1119059 := bstep (se 1 (by rfl) ⟨839294, by rfl⟩ : syracuseStep 1119059 = 1678589) B1678589
theorem B1119089 : Blo 742328 1119089 := bstep (se 2 (by rfl) ⟨419658, by rfl⟩ : syracuseStep 1119089 = 839317) B839317
theorem B1119107 : Blo 742328 1119107 := bstep (se 1 (by rfl) ⟨839330, by rfl⟩ : syracuseStep 1119107 = 1678661) B1678661
theorem B1676177 : Blo 742328 1676177 := bstep (se 2 (by rfl) ⟨628566, by rfl⟩ : syracuseStep 1676177 = 1257133) B1257133
theorem B1119137 : Blo 742328 1119137 := bstep (se 2 (by rfl) ⟨419676, by rfl⟩ : syracuseStep 1119137 = 839353) B839353
theorem B1676195 : Blo 742328 1676195 := bstep (se 1 (by rfl) ⟨1257146, by rfl⟩ : syracuseStep 1676195 = 2514293) B2514293
theorem B1119155 : Blo 742328 1119155 := bstep (se 1 (by rfl) ⟨839366, by rfl⟩ : syracuseStep 1119155 = 1678733) B1678733
theorem B1119185 : Blo 742328 1119185 := bstep (se 2 (by rfl) ⟨419694, by rfl⟩ : syracuseStep 1119185 = 839389) B839389
theorem B1119203 : Blo 742328 1119203 := bstep (se 1 (by rfl) ⟨839402, by rfl⟩ : syracuseStep 1119203 = 1678805) B1678805
theorem B1119233 : Blo 742328 1119233 := bstep (se 2 (by rfl) ⟨419712, by rfl⟩ : syracuseStep 1119233 = 839425) B839425
theorem B1119251 : Blo 742328 1119251 := bstep (se 1 (by rfl) ⟨839438, by rfl⟩ : syracuseStep 1119251 = 1678877) B1678877
theorem B1119281 : Blo 742328 1119281 := bstep (se 2 (by rfl) ⟨419730, by rfl⟩ : syracuseStep 1119281 = 839461) B839461
theorem B1119299 : Blo 742328 1119299 := bstep (se 1 (by rfl) ⟨839474, by rfl⟩ : syracuseStep 1119299 = 1678949) B1678949
theorem B1119329 : Blo 742328 1119329 := bstep (se 2 (by rfl) ⟨419748, by rfl⟩ : syracuseStep 1119329 = 839497) B839497
theorem B2823281 : Blo 742328 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B6362225 : Blo 742328 6362225 := bstep (se 2 (by rfl) ⟨2385834, by rfl⟩ : syracuseStep 6362225 = 4771669) B4771669
theorem B14324849 : Blo 742328 14324849 := bstep (se 2 (by rfl) ⟨5371818, by rfl⟩ : syracuseStep 14324849 = 10743637) B10743637
theorem B1119347 : Blo 742328 1119347 := bstep (se 1 (by rfl) ⟨839510, by rfl⟩ : syracuseStep 1119347 = 1679021) B1679021
theorem B1119377 : Blo 742328 1119377 := bstep (se 2 (by rfl) ⟨419766, by rfl⟩ : syracuseStep 1119377 = 839533) B839533
theorem B1119395 : Blo 742328 1119395 := bstep (se 1 (by rfl) ⟨839546, by rfl⟩ : syracuseStep 1119395 = 1679093) B1679093
theorem B1676465 : Blo 742328 1676465 := bstep (se 2 (by rfl) ⟨628674, by rfl⟩ : syracuseStep 1676465 = 1257349) B1257349
theorem B1119425 : Blo 742328 1119425 := bstep (se 2 (by rfl) ⟨419784, by rfl⟩ : syracuseStep 1119425 = 839569) B839569
theorem B1676483 : Blo 742328 1676483 := bstep (se 1 (by rfl) ⟨1257362, by rfl⟩ : syracuseStep 1676483 = 2514725) B2514725
theorem B1119443 : Blo 742328 1119443 := bstep (se 1 (by rfl) ⟨839582, by rfl⟩ : syracuseStep 1119443 = 1679165) B1679165
theorem B1119473 : Blo 742328 1119473 := bstep (se 2 (by rfl) ⟨419802, by rfl⟩ : syracuseStep 1119473 = 839605) B839605
theorem B1119491 : Blo 742328 1119491 := bstep (se 1 (by rfl) ⟨839618, by rfl⟩ : syracuseStep 1119491 = 1679237) B1679237
theorem B4232483 : Blo 742328 4232483 := bstep (se 1 (by rfl) ⟨3174362, by rfl⟩ : syracuseStep 4232483 = 6348725) B6348725
theorem B1414435 : Blo 742328 1414435 := bstep (se 1 (by rfl) ⟨1060826, by rfl⟩ : syracuseStep 1414435 = 2121653) B2121653
theorem B1676753 : Blo 742328 1676753 := bstep (se 2 (by rfl) ⟨628782, by rfl⟩ : syracuseStep 1676753 = 1257565) B1257565
theorem B1676771 : Blo 742328 1676771 := bstep (se 1 (by rfl) ⟨1257578, by rfl⟩ : syracuseStep 1676771 = 2515157) B2515157
theorem B12916421 : Blo 742328 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B1414883 : Blo 742328 1414883 := bstep (se 1 (by rfl) ⟨1061162, by rfl⟩ : syracuseStep 1414883 = 2122325) B2122325
theorem B1677041 : Blo 742328 1677041 := bstep (se 2 (by rfl) ⟨628890, by rfl⟩ : syracuseStep 1677041 = 1257781) B1257781
theorem B1677059 : Blo 742328 1677059 := bstep (se 1 (by rfl) ⟨1257794, by rfl⟩ : syracuseStep 1677059 = 2515589) B2515589
theorem B1087379 : Blo 742328 1087379 := bstep (se 1 (by rfl) ⟨815534, by rfl⟩ : syracuseStep 1087379 = 1631069) B1631069
theorem B1808369 : Blo 742328 1808369 := bstep (se 2 (by rfl) ⟨678138, by rfl⟩ : syracuseStep 1808369 = 1356277) B1356277
theorem B1415171 : Blo 742328 1415171 := bstep (se 1 (by rfl) ⟨1061378, by rfl⟩ : syracuseStep 1415171 = 2122757) B2122757
theorem B1677329 : Blo 742328 1677329 := bstep (se 2 (by rfl) ⟨628998, by rfl⟩ : syracuseStep 1677329 = 1257997) B1257997
theorem B1677347 : Blo 742328 1677347 := bstep (se 1 (by rfl) ⟨1258010, by rfl⟩ : syracuseStep 1677347 = 2516021) B2516021
theorem B3184717 : Blo 742328 3184717 := bstep (se 3 (by rfl) ⟨597134, by rfl⟩ : syracuseStep 3184717 = 1194269) B1194269
theorem B9541745 : Blo 742328 9541745 := bstep (se 2 (by rfl) ⟨3578154, by rfl⟩ : syracuseStep 9541745 = 7156309) B7156309
theorem B20355299 : Blo 742328 20355299 := bstep (se 1 (by rfl) ⟨15266474, by rfl⟩ : syracuseStep 20355299 = 30532949) B30532949
theorem B4233485 : Blo 742328 4233485 := bstep (se 3 (by rfl) ⟨793778, by rfl⟩ : syracuseStep 4233485 = 1587557) B1587557
theorem B1677617 : Blo 742328 1677617 := bstep (se 2 (by rfl) ⟨629106, by rfl⟩ : syracuseStep 1677617 = 1258213) B1258213
theorem B2267441 : Blo 742328 2267441 := bstep (se 2 (by rfl) ⟨850290, by rfl⟩ : syracuseStep 2267441 = 1700581) B1700581
theorem B1677635 : Blo 742328 1677635 := bstep (se 1 (by rfl) ⟨1258226, by rfl⟩ : syracuseStep 1677635 = 2516453) B2516453
theorem B1612163 : Blo 742328 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B793027 : Blo 742328 793027 := bstep (se 1 (by rfl) ⟨594770, by rfl⟩ : syracuseStep 793027 = 1189541) B1189541
theorem B16062947 : Blo 742328 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B2824739 : Blo 742328 2824739 := bstep (se 1 (by rfl) ⟨2118554, by rfl⟩ : syracuseStep 2824739 = 4237109) B4237109
theorem B2824753 : Blo 742328 2824753 := bstep (se 2 (by rfl) ⟨1059282, by rfl⟩ : syracuseStep 2824753 = 2118565) B2118565
theorem B1677905 : Blo 742328 1677905 := bstep (se 2 (by rfl) ⟨629214, by rfl⟩ : syracuseStep 1677905 = 1258429) B1258429
theorem B1677923 : Blo 742328 1677923 := bstep (se 1 (by rfl) ⟨1258442, by rfl⟩ : syracuseStep 1677923 = 2516885) B2516885
theorem B1678193 : Blo 742328 1678193 := bstep (se 2 (by rfl) ⟨629322, by rfl⟩ : syracuseStep 1678193 = 1258645) B1258645
theorem B1678211 : Blo 742328 1678211 := bstep (se 1 (by rfl) ⟨1258658, by rfl⟩ : syracuseStep 1678211 = 2517317) B2517317
theorem B3775409 : Blo 742328 3775409 := bstep (se 2 (by rfl) ⟨1415778, by rfl⟩ : syracuseStep 3775409 = 2831557) B2831557
theorem B1416113 : Blo 742328 1416113 := bstep (se 2 (by rfl) ⟨531042, by rfl⟩ : syracuseStep 1416113 = 1062085) B1062085
theorem B1678481 : Blo 742328 1678481 := bstep (se 2 (by rfl) ⟨629430, by rfl⟩ : syracuseStep 1678481 = 1258861) B1258861
theorem B1678499 : Blo 742328 1678499 := bstep (se 1 (by rfl) ⟨1258874, by rfl⟩ : syracuseStep 1678499 = 2517749) B2517749
theorem B8494307 : Blo 742328 8494307 := bstep (se 1 (by rfl) ⟨6370730, by rfl⟩ : syracuseStep 8494307 = 12741461) B12741461
theorem B1252705 : Blo 742328 1252705 := bstep (se 2 (by rfl) ⟨469764, by rfl⟩ : syracuseStep 1252705 = 939529) B939529
theorem B5086577 : Blo 742328 5086577 := bstep (se 2 (by rfl) ⟨1907466, by rfl⟩ : syracuseStep 5086577 = 3814933) B3814933
theorem B1252739 : Blo 742328 1252739 := bstep (se 1 (by rfl) ⟨939554, by rfl⟩ : syracuseStep 1252739 = 1879109) B1879109
theorem B8068493 : Blo 742328 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B1678769 : Blo 742328 1678769 := bstep (se 2 (by rfl) ⟨629538, by rfl⟩ : syracuseStep 1678769 = 1259077) B1259077
theorem B1678787 : Blo 742328 1678787 := bstep (se 1 (by rfl) ⟨1259090, by rfl⟩ : syracuseStep 1678787 = 2518181) B2518181
theorem B1252867 : Blo 742328 1252867 := bstep (se 1 (by rfl) ⟨939650, by rfl⟩ : syracuseStep 1252867 = 1879301) B1879301
theorem B5643917 : Blo 742328 5643917 := bstep (se 3 (by rfl) ⟨1058234, by rfl⟩ : syracuseStep 5643917 = 2116469) B2116469
theorem B1253009 : Blo 742328 1253009 := bstep (se 2 (by rfl) ⟨469878, by rfl⟩ : syracuseStep 1253009 = 939757) B939757
theorem B794291 : Blo 742328 794291 := bstep (se 1 (by rfl) ⟨595718, by rfl⟩ : syracuseStep 794291 = 1191437) B1191437
theorem B1679057 : Blo 742328 1679057 := bstep (se 2 (by rfl) ⟨629646, by rfl⟩ : syracuseStep 1679057 = 1259293) B1259293
theorem B1679075 : Blo 742328 1679075 := bstep (se 1 (by rfl) ⟨1259306, by rfl⟩ : syracuseStep 1679075 = 2518613) B2518613
theorem B1253137 : Blo 742328 1253137 := bstep (se 2 (by rfl) ⟨469926, by rfl⟩ : syracuseStep 1253137 = 939853) B939853
theorem B1253171 : Blo 742328 1253171 := bstep (se 1 (by rfl) ⟨939878, by rfl⟩ : syracuseStep 1253171 = 1879757) B1879757
theorem B1253299 : Blo 742328 1253299 := bstep (se 1 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 1253299 = 1879949) B1879949
theorem B2826211 : Blo 742328 2826211 := bstep (se 1 (by rfl) ⟨2119658, by rfl⟩ : syracuseStep 2826211 = 4239317) B4239317
theorem B9052145 : Blo 742328 9052145 := bstep (se 2 (by rfl) ⟨3394554, by rfl⟩ : syracuseStep 9052145 = 6789109) B6789109
theorem B4530161 : Blo 742328 4530161 := bstep (se 2 (by rfl) ⟨1698810, by rfl⟩ : syracuseStep 4530161 = 3397621) B3397621
theorem B8036405 : Blo 742328 8036405 := bstep (se 5 (by rfl) ⟨376706, by rfl⟩ : syracuseStep 8036405 = 753413) B753413
theorem B1253441 : Blo 742328 1253441 := bstep (se 2 (by rfl) ⟨470040, by rfl⟩ : syracuseStep 1253441 = 940081) B940081
theorem B1253569 : Blo 742328 1253569 := bstep (se 2 (by rfl) ⟨470088, by rfl⟩ : syracuseStep 1253569 = 940177) B940177
theorem B1253603 : Blo 742328 1253603 := bstep (se 1 (by rfl) ⟨940202, by rfl⟩ : syracuseStep 1253603 = 1880405) B1880405
theorem B893155 : Blo 742328 893155 := bstep (se 1 (by rfl) ⟨669866, by rfl⟩ : syracuseStep 893155 = 1339733) B1339733
theorem B893251 : Blo 742328 893251 := bstep (se 1 (by rfl) ⟨669938, by rfl⟩ : syracuseStep 893251 = 1339877) B1339877
theorem B1253731 : Blo 742328 1253731 := bstep (se 1 (by rfl) ⟨940298, by rfl⟩ : syracuseStep 1253731 = 1880597) B1880597
theorem B3776867 : Blo 742328 3776867 := bstep (se 1 (by rfl) ⟨2832650, by rfl⟩ : syracuseStep 3776867 = 5665301) B5665301
theorem B1057153 : Blo 742328 1057153 := bstep (se 2 (by rfl) ⟨396432, by rfl⟩ : syracuseStep 1057153 = 792865) B792865
theorem B795043 : Blo 742328 795043 := bstep (se 1 (by rfl) ⟨596282, by rfl⟩ : syracuseStep 795043 = 1192565) B1192565
theorem B1253873 : Blo 742328 1253873 := bstep (se 2 (by rfl) ⟨470202, by rfl⟩ : syracuseStep 1253873 = 940405) B940405
theorem B1810993 : Blo 742328 1810993 := bstep (se 2 (by rfl) ⟨679122, by rfl⟩ : syracuseStep 1810993 = 1358245) B1358245
theorem B1254001 : Blo 742328 1254001 := bstep (se 2 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 1254001 = 940501) B940501
theorem B1254035 : Blo 742328 1254035 := bstep (se 1 (by rfl) ⟨940526, by rfl⟩ : syracuseStep 1254035 = 1881053) B1881053
theorem B5088005 : Blo 742328 5088005 := bstep (se 4 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 5088005 = 954001) B954001
theorem B1254163 : Blo 742328 1254163 := bstep (se 1 (by rfl) ⟨940622, by rfl⟩ : syracuseStep 1254163 = 1881245) B1881245
theorem B1254305 : Blo 742328 1254305 := bstep (se 2 (by rfl) ⟨470364, by rfl⟩ : syracuseStep 1254305 = 940729) B940729
theorem B1057745 : Blo 742328 1057745 := bstep (se 2 (by rfl) ⟨396654, by rfl⟩ : syracuseStep 1057745 = 793309) B793309
theorem B6366221 : Blo 742328 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B1254433 : Blo 742328 1254433 := bstep (se 2 (by rfl) ⟨470412, by rfl⟩ : syracuseStep 1254433 = 940825) B940825
theorem B1254467 : Blo 742328 1254467 := bstep (se 1 (by rfl) ⟨940850, by rfl⟩ : syracuseStep 1254467 = 1881701) B1881701
theorem B894035 : Blo 742328 894035 := bstep (se 1 (by rfl) ⟨670526, by rfl⟩ : syracuseStep 894035 = 1341053) B1341053
theorem B4236401 : Blo 742328 4236401 := bstep (se 2 (by rfl) ⟨1588650, by rfl⟩ : syracuseStep 4236401 = 3177301) B3177301
theorem B3777677 : Blo 742328 3777677 := bstep (se 3 (by rfl) ⟨708314, by rfl⟩ : syracuseStep 3777677 = 1416629) B1416629
theorem B1254595 : Blo 742328 1254595 := bstep (se 1 (by rfl) ⟨940946, by rfl⟩ : syracuseStep 1254595 = 1881893) B1881893
theorem B10200305 : Blo 742328 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1254737 : Blo 742328 1254737 := bstep (se 2 (by rfl) ⟨470526, by rfl⟩ : syracuseStep 1254737 = 941053) B941053
theorem B796051 : Blo 742328 796051 := bstep (se 1 (by rfl) ⟨597038, by rfl⟩ : syracuseStep 796051 = 1194077) B1194077
theorem B1254865 : Blo 742328 1254865 := bstep (se 2 (by rfl) ⟨470574, by rfl⟩ : syracuseStep 1254865 = 941149) B941149
theorem B1287635 : Blo 742328 1287635 := bstep (se 1 (by rfl) ⟨965726, by rfl⟩ : syracuseStep 1287635 = 1931453) B1931453
theorem B1058275 : Blo 742328 1058275 := bstep (se 1 (by rfl) ⟨793706, by rfl⟩ : syracuseStep 1058275 = 1587413) B1587413
theorem B1189361 : Blo 742328 1189361 := bstep (se 2 (by rfl) ⟨446010, by rfl⟩ : syracuseStep 1189361 = 892021) B892021
theorem B4531697 : Blo 742328 4531697 := bstep (se 2 (by rfl) ⟨1699386, by rfl⟩ : syracuseStep 4531697 = 3398773) B3398773
theorem B1254899 : Blo 742328 1254899 := bstep (se 1 (by rfl) ⟨941174, by rfl⟩ : syracuseStep 1254899 = 1882349) B1882349
theorem B4531717 : Blo 742328 4531717 := bstep (se 4 (by rfl) ⟨424848, by rfl⟩ : syracuseStep 4531717 = 849697) B849697
theorem B1189489 : Blo 742328 1189489 := bstep (se 2 (by rfl) ⟨446058, by rfl⟩ : syracuseStep 1189489 = 892117) B892117
theorem B1255027 : Blo 742328 1255027 := bstep (se 1 (by rfl) ⟨941270, by rfl⟩ : syracuseStep 1255027 = 1882541) B1882541
theorem B1255169 : Blo 742328 1255169 := bstep (se 2 (by rfl) ⟨470688, by rfl⟩ : syracuseStep 1255169 = 941377) B941377
theorem B1058611 : Blo 742328 1058611 := bstep (se 1 (by rfl) ⟨793958, by rfl⟩ : syracuseStep 1058611 = 1587917) B1587917
theorem B1255297 : Blo 742328 1255297 := bstep (se 2 (by rfl) ⟨470736, by rfl⟩ : syracuseStep 1255297 = 941473) B941473
theorem B1255331 : Blo 742328 1255331 := bstep (se 1 (by rfl) ⟨941498, by rfl⟩ : syracuseStep 1255331 = 1882997) B1882997
theorem B1255459 : Blo 742328 1255459 := bstep (se 1 (by rfl) ⟨941594, by rfl⟩ : syracuseStep 1255459 = 1883189) B1883189
theorem B2828429 : Blo 742328 2828429 := bstep (se 3 (by rfl) ⟨530330, by rfl⟩ : syracuseStep 2828429 = 1060661) B1060661
theorem B1255601 : Blo 742328 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B1255729 : Blo 742328 1255729 := bstep (se 2 (by rfl) ⟨470898, by rfl⟩ : syracuseStep 1255729 = 941797) B941797
theorem B1255763 : Blo 742328 1255763 := bstep (se 1 (by rfl) ⟨941822, by rfl⟩ : syracuseStep 1255763 = 1883645) B1883645
theorem B1059169 : Blo 742328 1059169 := bstep (se 2 (by rfl) ⟨397188, by rfl⟩ : syracuseStep 1059169 = 794377) B794377
theorem B1059203 : Blo 742328 1059203 := bstep (se 1 (by rfl) ⟨794402, by rfl⟩ : syracuseStep 1059203 = 1588805) B1588805
theorem B1255891 : Blo 742328 1255891 := bstep (se 1 (by rfl) ⟨941918, by rfl⟩ : syracuseStep 1255891 = 1883837) B1883837
theorem B10201571 : Blo 742328 10201571 := bstep (se 1 (by rfl) ⟨7651178, by rfl⟩ : syracuseStep 10201571 = 15302357) B15302357
theorem B5646833 : Blo 742328 5646833 := bstep (se 2 (by rfl) ⟨2117562, by rfl⟩ : syracuseStep 5646833 = 4235125) B4235125
theorem B4237859 : Blo 742328 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B1256033 : Blo 742328 1256033 := bstep (se 2 (by rfl) ⟨471012, by rfl⟩ : syracuseStep 1256033 = 942025) B942025
theorem B1256161 : Blo 742328 1256161 := bstep (se 2 (by rfl) ⟨471060, by rfl⟩ : syracuseStep 1256161 = 942121) B942121
theorem B1256195 : Blo 742328 1256195 := bstep (se 1 (by rfl) ⟨942146, by rfl⟩ : syracuseStep 1256195 = 1884293) B1884293
theorem B1190771 : Blo 742328 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B1256323 : Blo 742328 1256323 := bstep (se 1 (by rfl) ⟨942242, by rfl⟩ : syracuseStep 1256323 = 1884485) B1884485
theorem B1059761 : Blo 742328 1059761 := bstep (se 2 (by rfl) ⟨397410, by rfl⟩ : syracuseStep 1059761 = 794821) B794821
theorem B1190867 : Blo 742328 1190867 := bstep (se 1 (by rfl) ⟨893150, by rfl⟩ : syracuseStep 1190867 = 1786301) B1786301
theorem B6794225 : Blo 742328 6794225 := bstep (se 2 (by rfl) ⟨2547834, by rfl⟩ : syracuseStep 6794225 = 5095669) B5095669
theorem B1190899 : Blo 742328 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B1059841 : Blo 742328 1059841 := bstep (se 2 (by rfl) ⟨397440, by rfl⟩ : syracuseStep 1059841 = 794881) B794881
theorem B1256465 : Blo 742328 1256465 := bstep (se 2 (by rfl) ⟨471174, by rfl⟩ : syracuseStep 1256465 = 942349) B942349
theorem B2010161 : Blo 742328 2010161 := bstep (se 2 (by rfl) ⟨753810, by rfl⟩ : syracuseStep 2010161 = 1507621) B1507621
theorem B1879139 : Blo 742328 1879139 := bstep (se 1 (by rfl) ⟨1409354, by rfl⟩ : syracuseStep 1879139 = 2818709) B2818709
theorem B1256593 : Blo 742328 1256593 := bstep (se 2 (by rfl) ⟨471222, by rfl⟩ : syracuseStep 1256593 = 942445) B942445
theorem B1256627 : Blo 742328 1256627 := bstep (se 1 (by rfl) ⟨942470, by rfl⟩ : syracuseStep 1256627 = 1884941) B1884941
theorem B1256755 : Blo 742328 1256755 := bstep (se 1 (by rfl) ⟨942566, by rfl⟩ : syracuseStep 1256755 = 1885133) B1885133
theorem B1256897 : Blo 742328 1256897 := bstep (se 2 (by rfl) ⟨471336, by rfl⟩ : syracuseStep 1256897 = 942673) B942673
theorem B1257025 : Blo 742328 1257025 := bstep (se 2 (by rfl) ⟨471384, by rfl⟩ : syracuseStep 1257025 = 942769) B942769
theorem B1257059 : Blo 742328 1257059 := bstep (se 1 (by rfl) ⟨942794, by rfl⟩ : syracuseStep 1257059 = 1885589) B1885589
theorem B3223217 : Blo 742328 3223217 := bstep (se 2 (by rfl) ⟨1208706, by rfl⟩ : syracuseStep 3223217 = 2417413) B2417413
theorem B1257187 : Blo 742328 1257187 := bstep (se 1 (by rfl) ⟨942890, by rfl⟩ : syracuseStep 1257187 = 1885781) B1885781
theorem B1060627 : Blo 742328 1060627 := bstep (se 1 (by rfl) ⟨795470, by rfl⟩ : syracuseStep 1060627 = 1590941) B1590941
theorem B1257329 : Blo 742328 1257329 := bstep (se 2 (by rfl) ⟨471498, by rfl⟩ : syracuseStep 1257329 = 942997) B942997
theorem B1191809 : Blo 742328 1191809 := bstep (se 2 (by rfl) ⟨446928, by rfl⟩ : syracuseStep 1191809 = 893857) B893857
theorem B3583885 : Blo 742328 3583885 := bstep (se 3 (by rfl) ⟨671978, by rfl⟩ : syracuseStep 3583885 = 1343957) B1343957
theorem B1257457 : Blo 742328 1257457 := bstep (se 2 (by rfl) ⟨471546, by rfl⟩ : syracuseStep 1257457 = 943093) B943093
theorem B1880081 : Blo 742328 1880081 := bstep (se 2 (by rfl) ⟨705030, by rfl⟩ : syracuseStep 1880081 = 1410061) B1410061
theorem B1257491 : Blo 742328 1257491 := bstep (se 1 (by rfl) ⟨943118, by rfl⟩ : syracuseStep 1257491 = 1886237) B1886237
theorem B1880131 : Blo 742328 1880131 := bstep (se 1 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 1880131 = 2820197) B2820197
theorem B1257619 : Blo 742328 1257619 := bstep (se 1 (by rfl) ⟨943214, by rfl⟩ : syracuseStep 1257619 = 1886429) B1886429
theorem B1913009 : Blo 742328 1913009 := bstep (se 2 (by rfl) ⟨717378, by rfl⟩ : syracuseStep 1913009 = 1434757) B1434757
theorem B1880273 : Blo 742328 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1061105 : Blo 742328 1061105 := bstep (se 2 (by rfl) ⟨397914, by rfl⟩ : syracuseStep 1061105 = 795829) B795829
theorem B1257761 : Blo 742328 1257761 := bstep (se 2 (by rfl) ⟨471660, by rfl⟩ : syracuseStep 1257761 = 943321) B943321
theorem B1585507 : Blo 742328 1585507 := bstep (se 1 (by rfl) ⟨1189130, by rfl⟩ : syracuseStep 1585507 = 2378261) B2378261
theorem B1061219 : Blo 742328 1061219 := bstep (se 1 (by rfl) ⟨795914, by rfl⟩ : syracuseStep 1061219 = 1591829) B1591829
theorem B14332301 : Blo 742328 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B1257889 : Blo 742328 1257889 := bstep (se 2 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 1257889 = 943417) B943417
theorem B1061299 : Blo 742328 1061299 := bstep (se 1 (by rfl) ⟨795974, by rfl⟩ : syracuseStep 1061299 = 1591949) B1591949
theorem B1257923 : Blo 742328 1257923 := bstep (se 1 (by rfl) ⟨943442, by rfl⟩ : syracuseStep 1257923 = 1886885) B1886885
theorem B1258051 : Blo 742328 1258051 := bstep (se 1 (by rfl) ⟨943538, by rfl⟩ : syracuseStep 1258051 = 1887077) B1887077
theorem B4764365 : Blo 742328 4764365 := bstep (se 3 (by rfl) ⟨893318, by rfl⟩ : syracuseStep 4764365 = 1786637) B1786637
theorem B1258193 : Blo 742328 1258193 := bstep (se 2 (by rfl) ⟨471822, by rfl⟩ : syracuseStep 1258193 = 943645) B943645
theorem B1258321 : Blo 742328 1258321 := bstep (se 2 (by rfl) ⟨471870, by rfl⟩ : syracuseStep 1258321 = 943741) B943741
theorem B3093347 : Blo 742328 3093347 := bstep (se 1 (by rfl) ⟨2320010, by rfl⟩ : syracuseStep 3093347 = 4640021) B4640021
theorem B1258355 : Blo 742328 1258355 := bstep (se 1 (by rfl) ⟨943766, by rfl⟩ : syracuseStep 1258355 = 1887533) B1887533
theorem B2208653 : Blo 742328 2208653 := bstep (se 3 (by rfl) ⟨414122, by rfl⟩ : syracuseStep 2208653 = 828245) B828245
theorem B1061857 : Blo 742328 1061857 := bstep (se 2 (by rfl) ⟨398196, by rfl⟩ : syracuseStep 1061857 = 796393) B796393
theorem B2831345 : Blo 742328 2831345 := bstep (se 2 (by rfl) ⟨1061754, by rfl⟩ : syracuseStep 2831345 = 2123509) B2123509
theorem B1258483 : Blo 742328 1258483 := bstep (se 1 (by rfl) ⟨943862, by rfl⟩ : syracuseStep 1258483 = 1887725) B1887725
theorem B2012195 : Blo 742328 2012195 := bstep (se 1 (by rfl) ⟨1509146, by rfl⟩ : syracuseStep 2012195 = 3018293) B3018293
theorem B1586225 : Blo 742328 1586225 := bstep (se 2 (by rfl) ⟨594834, by rfl⟩ : syracuseStep 1586225 = 1189669) B1189669
theorem B2012273 : Blo 742328 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B1258625 : Blo 742328 1258625 := bstep (se 2 (by rfl) ⟨471984, by rfl⟩ : syracuseStep 1258625 = 943969) B943969
theorem B1193123 : Blo 742328 1193123 := bstep (se 1 (by rfl) ⟨894842, by rfl⟩ : syracuseStep 1193123 = 1789685) B1789685
theorem B1881265 : Blo 742328 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B1258753 : Blo 742328 1258753 := bstep (se 2 (by rfl) ⟨472032, by rfl⟩ : syracuseStep 1258753 = 944065) B944065
theorem B1258787 : Blo 742328 1258787 := bstep (se 1 (by rfl) ⟨944090, by rfl⟩ : syracuseStep 1258787 = 1888181) B1888181
theorem B1258915 : Blo 742328 1258915 := bstep (se 1 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 1258915 = 1888373) B1888373
theorem B1914275 : Blo 742328 1914275 := bstep (se 1 (by rfl) ⟨1435706, by rfl⟩ : syracuseStep 1914275 = 2871413) B2871413
theorem B1881539 : Blo 742328 1881539 := bstep (se 1 (by rfl) ⟨1411154, by rfl⟩ : syracuseStep 1881539 = 2822309) B2822309
theorem B1586737 : Blo 742328 1586737 := bstep (se 2 (by rfl) ⟨595026, by rfl⟩ : syracuseStep 1586737 = 1190053) B1190053
theorem B1259057 : Blo 742328 1259057 := bstep (se 2 (by rfl) ⟨472146, by rfl⟩ : syracuseStep 1259057 = 944293) B944293
theorem B1881731 : Blo 742328 1881731 := bstep (se 1 (by rfl) ⟨1411298, by rfl⟩ : syracuseStep 1881731 = 2822597) B2822597
theorem B1062563 : Blo 742328 1062563 := bstep (se 1 (by rfl) ⟨796922, by rfl⟩ : syracuseStep 1062563 = 1593845) B1593845
theorem B1259185 : Blo 742328 1259185 := bstep (se 2 (by rfl) ⟨472194, by rfl⟩ : syracuseStep 1259185 = 944389) B944389
theorem B1259219 : Blo 742328 1259219 := bstep (se 1 (by rfl) ⟨944414, by rfl⟩ : syracuseStep 1259219 = 1888829) B1888829
theorem B1193795 : Blo 742328 1193795 := bstep (se 1 (by rfl) ⟨895346, by rfl⟩ : syracuseStep 1193795 = 1790693) B1790693
theorem B1259347 : Blo 742328 1259347 := bstep (se 1 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 1259347 = 1889021) B1889021
theorem B1554403 : Blo 742328 1554403 := bstep (se 1 (by rfl) ⟨1165802, by rfl⟩ : syracuseStep 1554403 = 2331605) B2331605
theorem B2144333 : Blo 742328 2144333 := bstep (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) B804125
theorem B1783889 : Blo 742328 1783889 := bstep (se 2 (by rfl) ⟨668958, by rfl⟩ : syracuseStep 1783889 = 1337917) B1337917
theorem B1194097 : Blo 742328 1194097 := bstep (se 2 (by rfl) ⟨447786, by rfl⟩ : syracuseStep 1194097 = 895573) B895573
theorem B1718513 : Blo 742328 1718513 := bstep (se 2 (by rfl) ⟨644442, by rfl⟩ : syracuseStep 1718513 = 1288885) B1288885
theorem B1194307 : Blo 742328 1194307 := bstep (se 1 (by rfl) ⟨895730, by rfl⟩ : syracuseStep 1194307 = 1791461) B1791461
theorem B4962637 : Blo 742328 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1784177 : Blo 742328 1784177 := bstep (se 2 (by rfl) ⟨669066, by rfl⟩ : syracuseStep 1784177 = 1338133) B1338133
theorem B1194353 : Blo 742328 1194353 := bstep (se 2 (by rfl) ⟨447882, by rfl⟩ : syracuseStep 1194353 = 895765) B895765
theorem B2832803 : Blo 742328 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B1882673 : Blo 742328 1882673 := bstep (se 2 (by rfl) ⟨706002, by rfl⟩ : syracuseStep 1882673 = 1412005) B1412005
theorem B1784387 : Blo 742328 1784387 := bstep (se 1 (by rfl) ⟨1338290, by rfl⟩ : syracuseStep 1784387 = 2676581) B2676581
theorem B1882723 : Blo 742328 1882723 := bstep (se 1 (by rfl) ⟨1412042, by rfl⟩ : syracuseStep 1882723 = 2824085) B2824085
theorem B1882865 : Blo 742328 1882865 := bstep (se 2 (by rfl) ⟨706074, by rfl⟩ : syracuseStep 1882865 = 1412149) B1412149
theorem B1129475 : Blo 742328 1129475 := bstep (se 1 (by rfl) ⟨847106, by rfl⟩ : syracuseStep 1129475 = 1694213) B1694213
theorem B1588241 : Blo 742328 1588241 := bstep (se 2 (by rfl) ⟨595590, by rfl⟩ : syracuseStep 1588241 = 1191181) B1191181
theorem B6798449 : Blo 742328 6798449 := bstep (se 2 (by rfl) ⟨2549418, by rfl⟩ : syracuseStep 6798449 = 5098837) B5098837
theorem B2505869 : Blo 742328 2505869 := bstep (se 3 (by rfl) ⟨469850, by rfl⟩ : syracuseStep 2505869 = 939701) B939701
theorem B2505923 : Blo 742328 2505923 := bstep (se 1 (by rfl) ⟨1879442, by rfl⟩ : syracuseStep 2505923 = 3758885) B3758885
theorem B1588643 : Blo 742328 1588643 := bstep (se 1 (by rfl) ⟨1191482, by rfl⟩ : syracuseStep 1588643 = 2382965) B2382965
theorem B2014637 : Blo 742328 2014637 := bstep (se 3 (by rfl) ⟨377744, by rfl⟩ : syracuseStep 2014637 = 755489) B755489
theorem B2506193 : Blo 742328 2506193 := bstep (se 2 (by rfl) ⟨939822, by rfl⟩ : syracuseStep 2506193 = 1879645) B1879645
theorem B835123 : Blo 742328 835123 := bstep (se 1 (by rfl) ⟨626342, by rfl⟩ : syracuseStep 835123 = 1252685) B1252685
theorem B835267 : Blo 742328 835267 := bstep (se 1 (by rfl) ⟨626450, by rfl⟩ : syracuseStep 835267 = 1252901) B1252901
theorem B1883857 : Blo 742328 1883857 := bstep (se 2 (by rfl) ⟨706446, by rfl⟩ : syracuseStep 1883857 = 1412893) B1412893
theorem B835411 : Blo 742328 835411 := bstep (se 1 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 835411 = 1253117) B1253117
theorem B6799301 : Blo 742328 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B1130449 : Blo 742328 1130449 := bstep (se 2 (by rfl) ⟨423918, by rfl⟩ : syracuseStep 1130449 = 847837) B847837
theorem B835555 : Blo 742328 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B1884131 : Blo 742328 1884131 := bstep (se 1 (by rfl) ⟨1413098, by rfl⟩ : syracuseStep 1884131 = 2826197) B2826197
theorem B2506733 : Blo 742328 2506733 := bstep (se 3 (by rfl) ⟨470012, by rfl⟩ : syracuseStep 2506733 = 940025) B940025
theorem B2506787 : Blo 742328 2506787 := bstep (se 1 (by rfl) ⟨1880090, by rfl⟩ : syracuseStep 2506787 = 3760181) B3760181
theorem B8601713 : Blo 742328 8601713 := bstep (se 2 (by rfl) ⟨3225642, by rfl⟩ : syracuseStep 8601713 = 6451285) B6451285
theorem B835699 : Blo 742328 835699 := bstep (se 1 (by rfl) ⟨626774, by rfl⟩ : syracuseStep 835699 = 1253549) B1253549
theorem B1884323 : Blo 742328 1884323 := bstep (se 1 (by rfl) ⟨1413242, by rfl⟩ : syracuseStep 1884323 = 2826485) B2826485
theorem B835843 : Blo 742328 835843 := bstep (se 1 (by rfl) ⟨626882, by rfl⟩ : syracuseStep 835843 = 1253765) B1253765
theorem B1589539 : Blo 742328 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B2507057 : Blo 742328 2507057 := bstep (se 2 (by rfl) ⟨940146, by rfl⟩ : syracuseStep 2507057 = 1880293) B1880293
theorem B9060707 : Blo 742328 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B1786225 : Blo 742328 1786225 := bstep (se 2 (by rfl) ⟨669834, by rfl⟩ : syracuseStep 1786225 = 1339669) B1339669
theorem B835987 : Blo 742328 835987 := bstep (se 1 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 835987 = 1253981) B1253981
theorem B836131 : Blo 742328 836131 := bstep (se 1 (by rfl) ⟨627098, by rfl⟩ : syracuseStep 836131 = 1254197) B1254197
theorem B836275 : Blo 742328 836275 := bstep (se 1 (by rfl) ⟨627206, by rfl⟩ : syracuseStep 836275 = 1254413) B1254413
theorem B1131203 : Blo 742328 1131203 := bstep (se 1 (by rfl) ⟨848402, by rfl⟩ : syracuseStep 1131203 = 1696805) B1696805
theorem B836419 : Blo 742328 836419 := bstep (se 1 (by rfl) ⟨627314, by rfl⟩ : syracuseStep 836419 = 1254629) B1254629
theorem B2507597 : Blo 742328 2507597 := bstep (se 3 (by rfl) ⟨470174, by rfl⟩ : syracuseStep 2507597 = 940349) B940349
theorem B2507651 : Blo 742328 2507651 := bstep (se 1 (by rfl) ⟨1880738, by rfl⟩ : syracuseStep 2507651 = 3761477) B3761477
theorem B6374285 : Blo 742328 6374285 := bstep (se 3 (by rfl) ⟨1195178, by rfl⟩ : syracuseStep 6374285 = 2390357) B2390357
theorem B2016173 : Blo 742328 2016173 := bstep (se 3 (by rfl) ⟨378032, by rfl⟩ : syracuseStep 2016173 = 756065) B756065
theorem B4015025 : Blo 742328 4015025 := bstep (se 2 (by rfl) ⟨1505634, by rfl⟩ : syracuseStep 4015025 = 3011269) B3011269
theorem B836563 : Blo 742328 836563 := bstep (se 1 (by rfl) ⟨627422, by rfl⟩ : syracuseStep 836563 = 1254845) B1254845
theorem B2114545 : Blo 742328 2114545 := bstep (se 2 (by rfl) ⟨792954, by rfl⟩ : syracuseStep 2114545 = 1585909) B1585909
theorem B1885265 : Blo 742328 1885265 := bstep (se 2 (by rfl) ⟨706974, by rfl⟩ : syracuseStep 1885265 = 1413949) B1413949
theorem B836707 : Blo 742328 836707 := bstep (se 1 (by rfl) ⟨627530, by rfl⟩ : syracuseStep 836707 = 1255061) B1255061
theorem B1885315 : Blo 742328 1885315 := bstep (se 1 (by rfl) ⟨1413986, by rfl⟩ : syracuseStep 1885315 = 2827973) B2827973
theorem B2507921 : Blo 742328 2507921 := bstep (se 2 (by rfl) ⟨940470, by rfl⟩ : syracuseStep 2507921 = 1880941) B1880941
theorem B836851 : Blo 742328 836851 := bstep (se 1 (by rfl) ⟨627638, by rfl⟩ : syracuseStep 836851 = 1255277) B1255277
theorem B2114819 : Blo 742328 2114819 := bstep (se 1 (by rfl) ⟨1586114, by rfl⟩ : syracuseStep 2114819 = 3172229) B3172229
theorem B8045837 : Blo 742328 8045837 := bstep (se 3 (by rfl) ⟨1508594, by rfl⟩ : syracuseStep 8045837 = 3017189) B3017189
theorem B1885457 : Blo 742328 1885457 := bstep (se 2 (by rfl) ⟨707046, by rfl⟩ : syracuseStep 1885457 = 1414093) B1414093
theorem B836995 : Blo 742328 836995 := bstep (se 1 (by rfl) ⟨627746, by rfl⟩ : syracuseStep 836995 = 1255493) B1255493
theorem B2115011 : Blo 742328 2115011 := bstep (se 1 (by rfl) ⟨1586258, by rfl⟩ : syracuseStep 2115011 = 3172517) B3172517
theorem B4015565 : Blo 742328 4015565 := bstep (se 3 (by rfl) ⟨752918, by rfl⟩ : syracuseStep 4015565 = 1505837) B1505837
theorem B1590769 : Blo 742328 1590769 := bstep (se 2 (by rfl) ⟨596538, by rfl⟩ : syracuseStep 1590769 = 1193077) B1193077
theorem B837139 : Blo 742328 837139 := bstep (se 1 (by rfl) ⟨627854, by rfl⟩ : syracuseStep 837139 = 1255709) B1255709
theorem B8046179 : Blo 742328 8046179 := bstep (se 1 (by rfl) ⟨6034634, by rfl⟩ : syracuseStep 8046179 = 12069269) B12069269
theorem B837283 : Blo 742328 837283 := bstep (se 1 (by rfl) ⟨627962, by rfl⟩ : syracuseStep 837283 = 1255925) B1255925
theorem B2508461 : Blo 742328 2508461 := bstep (se 3 (by rfl) ⟨470336, by rfl⟩ : syracuseStep 2508461 = 940673) B940673
theorem B2148049 : Blo 742328 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B2508515 : Blo 742328 2508515 := bstep (se 1 (by rfl) ⟨1881386, by rfl⟩ : syracuseStep 2508515 = 3762773) B3762773
theorem B837427 : Blo 742328 837427 := bstep (se 1 (by rfl) ⟨628070, by rfl⟩ : syracuseStep 837427 = 1256141) B1256141
theorem B837571 : Blo 742328 837571 := bstep (se 1 (by rfl) ⟨628178, by rfl⟩ : syracuseStep 837571 = 1256357) B1256357
theorem B2508785 : Blo 742328 2508785 := bstep (se 2 (by rfl) ⟨940794, by rfl⟩ : syracuseStep 2508785 = 1881589) B1881589
theorem B837715 : Blo 742328 837715 := bstep (se 1 (by rfl) ⟨628286, by rfl⟩ : syracuseStep 837715 = 1256573) B1256573
theorem B837859 : Blo 742328 837859 := bstep (se 1 (by rfl) ⟨628394, by rfl⟩ : syracuseStep 837859 = 1256789) B1256789
theorem B2115821 : Blo 742328 2115821 := bstep (se 3 (by rfl) ⟨396716, by rfl⟩ : syracuseStep 2115821 = 793433) B793433
theorem B1886449 : Blo 742328 1886449 := bstep (se 2 (by rfl) ⟨707418, by rfl⟩ : syracuseStep 1886449 = 1414837) B1414837
theorem B4770053 : Blo 742328 4770053 := bstep (se 4 (by rfl) ⟨447192, by rfl⟩ : syracuseStep 4770053 = 894385) B894385
theorem B838003 : Blo 742328 838003 := bstep (se 1 (by rfl) ⟨628502, by rfl⟩ : syracuseStep 838003 = 1257005) B1257005
theorem B2116003 : Blo 742328 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B838147 : Blo 742328 838147 := bstep (se 1 (by rfl) ⟨628610, by rfl⟩ : syracuseStep 838147 = 1257221) B1257221
theorem B1886723 : Blo 742328 1886723 := bstep (se 1 (by rfl) ⟨1415042, by rfl⟩ : syracuseStep 1886723 = 2830085) B2830085
theorem B2509325 : Blo 742328 2509325 := bstep (se 3 (by rfl) ⟨470498, by rfl⟩ : syracuseStep 2509325 = 940997) B940997
theorem B2509379 : Blo 742328 2509379 := bstep (se 1 (by rfl) ⟨1882034, by rfl⟩ : syracuseStep 2509379 = 3764069) B3764069
theorem B4082275 : Blo 742328 4082275 := bstep (se 1 (by rfl) ⟨3061706, by rfl⟩ : syracuseStep 4082275 = 6123413) B6123413
theorem B838291 : Blo 742328 838291 := bstep (se 1 (by rfl) ⟨628718, by rfl⟩ : syracuseStep 838291 = 1257437) B1257437
theorem B1886915 : Blo 742328 1886915 := bstep (se 1 (by rfl) ⟨1415186, by rfl⟩ : syracuseStep 1886915 = 2830373) B2830373
theorem B838435 : Blo 742328 838435 := bstep (se 1 (by rfl) ⟨628826, by rfl⟩ : syracuseStep 838435 = 1257653) B1257653
theorem B2509649 : Blo 742328 2509649 := bstep (se 2 (by rfl) ⟨941118, by rfl⟩ : syracuseStep 2509649 = 1882237) B1882237
theorem B2116493 : Blo 742328 2116493 := bstep (se 3 (by rfl) ⟨396842, by rfl⟩ : syracuseStep 2116493 = 793685) B793685
theorem B2378659 : Blo 742328 2378659 := bstep (se 1 (by rfl) ⟨1783994, by rfl⟩ : syracuseStep 2378659 = 3567989) B3567989
theorem B5098403 : Blo 742328 5098403 := bstep (se 1 (by rfl) ⟨3823802, by rfl⟩ : syracuseStep 5098403 = 7647605) B7647605
theorem B1526705 : Blo 742328 1526705 := bstep (se 2 (by rfl) ⟨572514, by rfl⟩ : syracuseStep 1526705 = 1145029) B1145029
theorem B838579 : Blo 742328 838579 := bstep (se 1 (by rfl) ⟨628934, by rfl⟩ : syracuseStep 838579 = 1257869) B1257869
theorem B1592273 : Blo 742328 1592273 := bstep (se 2 (by rfl) ⟨597102, by rfl⟩ : syracuseStep 1592273 = 1194205) B1194205
theorem B1592291 : Blo 742328 1592291 := bstep (se 1 (by rfl) ⟨1194218, by rfl⟩ : syracuseStep 1592291 = 2388437) B2388437
theorem B838723 : Blo 742328 838723 := bstep (se 1 (by rfl) ⟨629042, by rfl⟩ : syracuseStep 838723 = 1258085) B1258085
theorem B838867 : Blo 742328 838867 := bstep (se 1 (by rfl) ⟨629150, by rfl⟩ : syracuseStep 838867 = 1258301) B1258301
theorem B4246789 : Blo 742328 4246789 := bstep (se 4 (by rfl) ⟨398136, by rfl⟩ : syracuseStep 4246789 = 796273) B796273
theorem B2379107 : Blo 742328 2379107 := bstep (se 1 (by rfl) ⟨1784330, by rfl⟩ : syracuseStep 2379107 = 3568661) B3568661
theorem B839011 : Blo 742328 839011 := bstep (se 1 (by rfl) ⟨629258, by rfl⟩ : syracuseStep 839011 = 1258517) B1258517
theorem B2510189 : Blo 742328 2510189 := bstep (se 3 (by rfl) ⟨470660, by rfl⟩ : syracuseStep 2510189 = 941321) B941321
theorem B2510243 : Blo 742328 2510243 := bstep (se 1 (by rfl) ⟨1882682, by rfl⟩ : syracuseStep 2510243 = 3765365) B3765365
theorem B839155 : Blo 742328 839155 := bstep (se 1 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 839155 = 1258733) B1258733
theorem B1887857 : Blo 742328 1887857 := bstep (se 2 (by rfl) ⟨707946, by rfl⟩ : syracuseStep 1887857 = 1415893) B1415893
theorem B839299 : Blo 742328 839299 := bstep (se 1 (by rfl) ⟨629474, by rfl⟩ : syracuseStep 839299 = 1258949) B1258949
theorem B1887907 : Blo 742328 1887907 := bstep (se 1 (by rfl) ⟨1415930, by rfl⟩ : syracuseStep 1887907 = 2831861) B2831861
theorem B2510513 : Blo 742328 2510513 := bstep (se 2 (by rfl) ⟨941442, by rfl⟩ : syracuseStep 2510513 = 1882885) B1882885
theorem B839443 : Blo 742328 839443 := bstep (se 1 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 839443 = 1259165) B1259165
theorem B1888049 : Blo 742328 1888049 := bstep (se 2 (by rfl) ⟨708018, by rfl⟩ : syracuseStep 1888049 = 1416037) B1416037
theorem B1134481 : Blo 742328 1134481 := bstep (se 2 (by rfl) ⟨425430, by rfl⟩ : syracuseStep 1134481 = 850861) B850861
theorem B839587 : Blo 742328 839587 := bstep (se 1 (by rfl) ⟨629690, by rfl⟩ : syracuseStep 839587 = 1259381) B1259381
theorem B9555893 : Blo 742328 9555893 := bstep (se 5 (by rfl) ⟨447932, by rfl⟩ : syracuseStep 9555893 = 895865) B895865
theorem B2117677 : Blo 742328 2117677 := bstep (se 3 (by rfl) ⟨397064, by rfl⟩ : syracuseStep 2117677 = 794129) B794129
theorem B6443107 : Blo 742328 6443107 := bstep (se 1 (by rfl) ⟨4832330, by rfl⟩ : syracuseStep 6443107 = 9664661) B9664661
theorem B2511053 : Blo 742328 2511053 := bstep (se 3 (by rfl) ⟨470822, by rfl⟩ : syracuseStep 2511053 = 941645) B941645
theorem B24170723 : Blo 742328 24170723 := bstep (se 1 (by rfl) ⟨18128042, by rfl⟩ : syracuseStep 24170723 = 36256085) B36256085
theorem B2511107 : Blo 742328 2511107 := bstep (se 1 (by rfl) ⟨1883330, by rfl⟩ : syracuseStep 2511107 = 3766661) B3766661
theorem B2150705 : Blo 742328 2150705 := bstep (se 2 (by rfl) ⟨806514, by rfl⟩ : syracuseStep 2150705 = 1613029) B1613029
theorem B2511377 : Blo 742328 2511377 := bstep (se 2 (by rfl) ⟨941766, by rfl⟩ : syracuseStep 2511377 = 1883533) B1883533
theorem B2380337 : Blo 742328 2380337 := bstep (se 2 (by rfl) ⟨892626, by rfl⟩ : syracuseStep 2380337 = 1785253) B1785253
theorem B1790531 : Blo 742328 1790531 := bstep (se 1 (by rfl) ⟨1342898, by rfl⟩ : syracuseStep 1790531 = 2685797) B2685797
theorem B1889041 : Blo 742328 1889041 := bstep (se 2 (by rfl) ⟨708390, by rfl⟩ : syracuseStep 1889041 = 1416781) B1416781
theorem B742339 : Blo 742328 742339 := bstep (se 1 (by rfl) ⟨556754, by rfl⟩ : syracuseStep 742339 = 1113509) B1113509
theorem B742355 : Blo 742328 742355 := bstep (se 1 (by rfl) ⟨556766, by rfl⟩ : syracuseStep 742355 = 1113533) B1113533
theorem B742371 : Blo 742328 742371 := bstep (se 1 (by rfl) ⟨556778, by rfl⟩ : syracuseStep 742371 = 1113557) B1113557
theorem B742387 : Blo 742328 742387 := bstep (se 1 (by rfl) ⟨556790, by rfl⟩ : syracuseStep 742387 = 1113581) B1113581
theorem B742403 : Blo 742328 742403 := bstep (se 1 (by rfl) ⟨556802, by rfl⟩ : syracuseStep 742403 = 1113605) B1113605
theorem B742419 : Blo 742328 742419 := bstep (se 1 (by rfl) ⟨556814, by rfl⟩ : syracuseStep 742419 = 1113629) B1113629
theorem B742435 : Blo 742328 742435 := bstep (se 1 (by rfl) ⟨556826, by rfl⟩ : syracuseStep 742435 = 1113653) B1113653
theorem B2511917 : Blo 742328 2511917 := bstep (se 3 (by rfl) ⟨470984, by rfl⟩ : syracuseStep 2511917 = 941969) B941969
theorem B742451 : Blo 742328 742451 := bstep (se 1 (by rfl) ⟨556838, by rfl⟩ : syracuseStep 742451 = 1113677) B1113677
theorem B742467 : Blo 742328 742467 := bstep (se 1 (by rfl) ⟨556850, by rfl⟩ : syracuseStep 742467 = 1113701) B1113701
theorem B2118737 : Blo 742328 2118737 := bstep (se 2 (by rfl) ⟨794526, by rfl⟩ : syracuseStep 2118737 = 1589053) B1589053
theorem B742483 : Blo 742328 742483 := bstep (se 1 (by rfl) ⟨556862, by rfl⟩ : syracuseStep 742483 = 1113725) B1113725
theorem B742499 : Blo 742328 742499 := bstep (se 1 (by rfl) ⟨556874, by rfl⟩ : syracuseStep 742499 = 1113749) B1113749
theorem B2511971 : Blo 742328 2511971 := bstep (se 1 (by rfl) ⟨1883978, by rfl⟩ : syracuseStep 2511971 = 3767957) B3767957
theorem B742515 : Blo 742328 742515 := bstep (se 1 (by rfl) ⟨556886, by rfl⟩ : syracuseStep 742515 = 1113773) B1113773
theorem B742531 : Blo 742328 742531 := bstep (se 1 (by rfl) ⟨556898, by rfl⟩ : syracuseStep 742531 = 1113797) B1113797
theorem B742547 : Blo 742328 742547 := bstep (se 1 (by rfl) ⟨556910, by rfl⟩ : syracuseStep 742547 = 1113821) B1113821
theorem B742563 : Blo 742328 742563 := bstep (se 1 (by rfl) ⟨556922, by rfl⟩ : syracuseStep 742563 = 1113845) B1113845
theorem B742579 : Blo 742328 742579 := bstep (se 1 (by rfl) ⟨556934, by rfl⟩ : syracuseStep 742579 = 1113869) B1113869
theorem B742595 : Blo 742328 742595 := bstep (se 1 (by rfl) ⟨556946, by rfl⟩ : syracuseStep 742595 = 1113893) B1113893
theorem B4248773 : Blo 742328 4248773 := bstep (se 4 (by rfl) ⟨398322, by rfl⟩ : syracuseStep 4248773 = 796645) B796645
theorem B742611 : Blo 742328 742611 := bstep (se 1 (by rfl) ⟨556958, by rfl⟩ : syracuseStep 742611 = 1113917) B1113917
theorem B742627 : Blo 742328 742627 := bstep (se 1 (by rfl) ⟨556970, by rfl⟩ : syracuseStep 742627 = 1113941) B1113941
theorem B742643 : Blo 742328 742643 := bstep (se 1 (by rfl) ⟨556982, by rfl⟩ : syracuseStep 742643 = 1113965) B1113965
theorem B742659 : Blo 742328 742659 := bstep (se 1 (by rfl) ⟨556994, by rfl⟩ : syracuseStep 742659 = 1113989) B1113989
theorem B742675 : Blo 742328 742675 := bstep (se 1 (by rfl) ⟨557006, by rfl⟩ : syracuseStep 742675 = 1114013) B1114013
theorem B742691 : Blo 742328 742691 := bstep (se 1 (by rfl) ⟨557018, by rfl⟩ : syracuseStep 742691 = 1114037) B1114037
theorem B742707 : Blo 742328 742707 := bstep (se 1 (by rfl) ⟨557030, by rfl⟩ : syracuseStep 742707 = 1114061) B1114061
theorem B742723 : Blo 742328 742723 := bstep (se 1 (by rfl) ⟨557042, by rfl⟩ : syracuseStep 742723 = 1114085) B1114085
theorem B742739 : Blo 742328 742739 := bstep (se 1 (by rfl) ⟨557054, by rfl⟩ : syracuseStep 742739 = 1114109) B1114109
theorem B1004897 : Blo 742328 1004897 := bstep (se 2 (by rfl) ⟨376836, by rfl⟩ : syracuseStep 1004897 = 753673) B753673
theorem B742755 : Blo 742328 742755 := bstep (se 1 (by rfl) ⟨557066, by rfl⟩ : syracuseStep 742755 = 1114133) B1114133
theorem B2512241 : Blo 742328 2512241 := bstep (se 2 (by rfl) ⟨942090, by rfl⟩ : syracuseStep 2512241 = 1884181) B1884181
theorem B742771 : Blo 742328 742771 := bstep (se 1 (by rfl) ⟨557078, by rfl⟩ : syracuseStep 742771 = 1114157) B1114157
theorem B742787 : Blo 742328 742787 := bstep (se 1 (by rfl) ⟨557090, by rfl⟩ : syracuseStep 742787 = 1114181) B1114181
theorem B742803 : Blo 742328 742803 := bstep (se 1 (by rfl) ⟨557102, by rfl⟩ : syracuseStep 742803 = 1114205) B1114205
theorem B742819 : Blo 742328 742819 := bstep (se 1 (by rfl) ⟨557114, by rfl⟩ : syracuseStep 742819 = 1114229) B1114229
theorem B2381233 : Blo 742328 2381233 := bstep (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) B1785925
theorem B742835 : Blo 742328 742835 := bstep (se 1 (by rfl) ⟨557126, by rfl⟩ : syracuseStep 742835 = 1114253) B1114253
theorem B742851 : Blo 742328 742851 := bstep (se 1 (by rfl) ⟨557138, by rfl⟩ : syracuseStep 742851 = 1114277) B1114277
theorem B742867 : Blo 742328 742867 := bstep (se 1 (by rfl) ⟨557150, by rfl⟩ : syracuseStep 742867 = 1114301) B1114301
theorem B742883 : Blo 742328 742883 := bstep (se 1 (by rfl) ⟨557162, by rfl⟩ : syracuseStep 742883 = 1114325) B1114325
theorem B742899 : Blo 742328 742899 := bstep (se 1 (by rfl) ⟨557174, by rfl⟩ : syracuseStep 742899 = 1114349) B1114349
theorem B742915 : Blo 742328 742915 := bstep (se 1 (by rfl) ⟨557186, by rfl⟩ : syracuseStep 742915 = 1114373) B1114373
theorem B4085261 : Blo 742328 4085261 := bstep (se 3 (by rfl) ⟨765986, by rfl⟩ : syracuseStep 4085261 = 1531973) B1531973
theorem B939539 : Blo 742328 939539 := bstep (se 1 (by rfl) ⟨704654, by rfl⟩ : syracuseStep 939539 = 1409309) B1409309
theorem B742931 : Blo 742328 742931 := bstep (se 1 (by rfl) ⟨557198, by rfl⟩ : syracuseStep 742931 = 1114397) B1114397
theorem B742947 : Blo 742328 742947 := bstep (se 1 (by rfl) ⟨557210, by rfl⟩ : syracuseStep 742947 = 1114421) B1114421
theorem B742963 : Blo 742328 742963 := bstep (se 1 (by rfl) ⟨557222, by rfl⟩ : syracuseStep 742963 = 1114445) B1114445
theorem B742979 : Blo 742328 742979 := bstep (se 1 (by rfl) ⟨557234, by rfl⟩ : syracuseStep 742979 = 1114469) B1114469
theorem B742995 : Blo 742328 742995 := bstep (se 1 (by rfl) ⟨557246, by rfl⟩ : syracuseStep 742995 = 1114493) B1114493
theorem B743011 : Blo 742328 743011 := bstep (se 1 (by rfl) ⟨557258, by rfl⟩ : syracuseStep 743011 = 1114517) B1114517
theorem B743027 : Blo 742328 743027 := bstep (se 1 (by rfl) ⟨557270, by rfl⟩ : syracuseStep 743027 = 1114541) B1114541
theorem B743043 : Blo 742328 743043 := bstep (se 1 (by rfl) ⟨557282, by rfl⟩ : syracuseStep 743043 = 1114565) B1114565
theorem B743059 : Blo 742328 743059 := bstep (se 1 (by rfl) ⟨557294, by rfl⟩ : syracuseStep 743059 = 1114589) B1114589
theorem B743075 : Blo 742328 743075 := bstep (se 1 (by rfl) ⟨557306, by rfl⟩ : syracuseStep 743075 = 1114613) B1114613
theorem B1431217 : Blo 742328 1431217 := bstep (se 2 (by rfl) ⟨536706, by rfl⟩ : syracuseStep 1431217 = 1073413) B1073413
theorem B743091 : Blo 742328 743091 := bstep (se 1 (by rfl) ⟨557318, by rfl⟩ : syracuseStep 743091 = 1114637) B1114637
theorem B743107 : Blo 742328 743107 := bstep (se 1 (by rfl) ⟨557330, by rfl⟩ : syracuseStep 743107 = 1114661) B1114661
theorem B743123 : Blo 742328 743123 := bstep (se 1 (by rfl) ⟨557342, by rfl⟩ : syracuseStep 743123 = 1114685) B1114685
theorem B743139 : Blo 742328 743139 := bstep (se 1 (by rfl) ⟨557354, by rfl⟩ : syracuseStep 743139 = 1114709) B1114709
theorem B2119409 : Blo 742328 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B743155 : Blo 742328 743155 := bstep (se 1 (by rfl) ⟨557366, by rfl⟩ : syracuseStep 743155 = 1114733) B1114733
theorem B743171 : Blo 742328 743171 := bstep (se 1 (by rfl) ⟨557378, by rfl⟩ : syracuseStep 743171 = 1114757) B1114757
theorem B743187 : Blo 742328 743187 := bstep (se 1 (by rfl) ⟨557390, by rfl⟩ : syracuseStep 743187 = 1114781) B1114781
theorem B743203 : Blo 742328 743203 := bstep (se 1 (by rfl) ⟨557402, by rfl⟩ : syracuseStep 743203 = 1114805) B1114805
theorem B743219 : Blo 742328 743219 := bstep (se 1 (by rfl) ⟨557414, by rfl⟩ : syracuseStep 743219 = 1114829) B1114829
theorem B743235 : Blo 742328 743235 := bstep (se 1 (by rfl) ⟨557426, by rfl⟩ : syracuseStep 743235 = 1114853) B1114853
theorem B743251 : Blo 742328 743251 := bstep (se 1 (by rfl) ⟨557438, by rfl⟩ : syracuseStep 743251 = 1114877) B1114877
theorem B743267 : Blo 742328 743267 := bstep (se 1 (by rfl) ⟨557450, by rfl⟩ : syracuseStep 743267 = 1114901) B1114901
theorem B743283 : Blo 742328 743283 := bstep (se 1 (by rfl) ⟨557462, by rfl⟩ : syracuseStep 743283 = 1114925) B1114925
theorem B743299 : Blo 742328 743299 := bstep (se 1 (by rfl) ⟨557474, by rfl⟩ : syracuseStep 743299 = 1114949) B1114949
theorem B2512781 : Blo 742328 2512781 := bstep (se 3 (by rfl) ⟨471146, by rfl⟩ : syracuseStep 2512781 = 942293) B942293
theorem B743315 : Blo 742328 743315 := bstep (se 1 (by rfl) ⟨557486, by rfl⟩ : syracuseStep 743315 = 1114973) B1114973
theorem B743331 : Blo 742328 743331 := bstep (se 1 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 743331 = 1114997) B1114997
theorem B743347 : Blo 742328 743347 := bstep (se 1 (by rfl) ⟨557510, by rfl⟩ : syracuseStep 743347 = 1115021) B1115021
theorem B743363 : Blo 742328 743363 := bstep (se 1 (by rfl) ⟨557522, by rfl⟩ : syracuseStep 743363 = 1115045) B1115045
theorem B2512835 : Blo 742328 2512835 := bstep (se 1 (by rfl) ⟨1884626, by rfl⟩ : syracuseStep 2512835 = 3769253) B3769253
theorem B743379 : Blo 742328 743379 := bstep (se 1 (by rfl) ⟨557534, by rfl⟩ : syracuseStep 743379 = 1115069) B1115069
theorem B743395 : Blo 742328 743395 := bstep (se 1 (by rfl) ⟨557546, by rfl⟩ : syracuseStep 743395 = 1115093) B1115093
theorem B743411 : Blo 742328 743411 := bstep (se 1 (by rfl) ⟨557558, by rfl⟩ : syracuseStep 743411 = 1115117) B1115117
theorem B743427 : Blo 742328 743427 := bstep (se 1 (by rfl) ⟨557570, by rfl⟩ : syracuseStep 743427 = 1115141) B1115141
theorem B743443 : Blo 742328 743443 := bstep (se 1 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 743443 = 1115165) B1115165
theorem B743459 : Blo 742328 743459 := bstep (se 1 (by rfl) ⟨557594, by rfl⟩ : syracuseStep 743459 = 1115189) B1115189
theorem B743475 : Blo 742328 743475 := bstep (se 1 (by rfl) ⟨557606, by rfl⟩ : syracuseStep 743475 = 1115213) B1115213
theorem B743491 : Blo 742328 743491 := bstep (se 1 (by rfl) ⟨557618, by rfl⟩ : syracuseStep 743491 = 1115237) B1115237
theorem B743507 : Blo 742328 743507 := bstep (se 1 (by rfl) ⟨557630, by rfl⟩ : syracuseStep 743507 = 1115261) B1115261
theorem B743523 : Blo 742328 743523 := bstep (se 1 (by rfl) ⟨557642, by rfl⟩ : syracuseStep 743523 = 1115285) B1115285
theorem B743539 : Blo 742328 743539 := bstep (se 1 (by rfl) ⟨557654, by rfl⟩ : syracuseStep 743539 = 1115309) B1115309
theorem B743555 : Blo 742328 743555 := bstep (se 1 (by rfl) ⟨557666, by rfl⟩ : syracuseStep 743555 = 1115333) B1115333
theorem B1792145 : Blo 742328 1792145 := bstep (se 2 (by rfl) ⟨672054, by rfl⟩ : syracuseStep 1792145 = 1344109) B1344109
theorem B743571 : Blo 742328 743571 := bstep (se 1 (by rfl) ⟨557678, by rfl⟩ : syracuseStep 743571 = 1115357) B1115357
theorem B743587 : Blo 742328 743587 := bstep (se 1 (by rfl) ⟨557690, by rfl⟩ : syracuseStep 743587 = 1115381) B1115381
theorem B743603 : Blo 742328 743603 := bstep (se 1 (by rfl) ⟨557702, by rfl⟩ : syracuseStep 743603 = 1115405) B1115405
theorem B743619 : Blo 742328 743619 := bstep (se 1 (by rfl) ⟨557714, by rfl⟩ : syracuseStep 743619 = 1115429) B1115429
theorem B2513105 : Blo 742328 2513105 := bstep (se 2 (by rfl) ⟨942414, by rfl⟩ : syracuseStep 2513105 = 1884829) B1884829
theorem B940243 : Blo 742328 940243 := bstep (se 1 (by rfl) ⟨705182, by rfl⟩ : syracuseStep 940243 = 1410365) B1410365
theorem B743635 : Blo 742328 743635 := bstep (se 1 (by rfl) ⟨557726, by rfl⟩ : syracuseStep 743635 = 1115453) B1115453
theorem B743651 : Blo 742328 743651 := bstep (se 1 (by rfl) ⟨557738, by rfl⟩ : syracuseStep 743651 = 1115477) B1115477
theorem B743667 : Blo 742328 743667 := bstep (se 1 (by rfl) ⟨557750, by rfl⟩ : syracuseStep 743667 = 1115501) B1115501
theorem B743683 : Blo 742328 743683 := bstep (se 1 (by rfl) ⟨557762, by rfl⟩ : syracuseStep 743683 = 1115525) B1115525
theorem B743699 : Blo 742328 743699 := bstep (se 1 (by rfl) ⟨557774, by rfl⟩ : syracuseStep 743699 = 1115549) B1115549
theorem B743715 : Blo 742328 743715 := bstep (se 1 (by rfl) ⟨557786, by rfl⟩ : syracuseStep 743715 = 1115573) B1115573
theorem B940339 : Blo 742328 940339 := bstep (se 1 (by rfl) ⟨705254, by rfl⟩ : syracuseStep 940339 = 1410509) B1410509
theorem B743731 : Blo 742328 743731 := bstep (se 1 (by rfl) ⟨557798, by rfl⟩ : syracuseStep 743731 = 1115597) B1115597
theorem B743747 : Blo 742328 743747 := bstep (se 1 (by rfl) ⟨557810, by rfl⟩ : syracuseStep 743747 = 1115621) B1115621
theorem B743763 : Blo 742328 743763 := bstep (se 1 (by rfl) ⟨557822, by rfl⟩ : syracuseStep 743763 = 1115645) B1115645
theorem B743779 : Blo 742328 743779 := bstep (se 1 (by rfl) ⟨557834, by rfl⟩ : syracuseStep 743779 = 1115669) B1115669
theorem B743795 : Blo 742328 743795 := bstep (se 1 (by rfl) ⟨557846, by rfl⟩ : syracuseStep 743795 = 1115693) B1115693
theorem B743811 : Blo 742328 743811 := bstep (se 1 (by rfl) ⟨557858, by rfl⟩ : syracuseStep 743811 = 1115717) B1115717
theorem B743827 : Blo 742328 743827 := bstep (se 1 (by rfl) ⟨557870, by rfl⟩ : syracuseStep 743827 = 1115741) B1115741
theorem B743843 : Blo 742328 743843 := bstep (se 1 (by rfl) ⟨557882, by rfl⟩ : syracuseStep 743843 = 1115765) B1115765
theorem B743859 : Blo 742328 743859 := bstep (se 1 (by rfl) ⟨557894, by rfl⟩ : syracuseStep 743859 = 1115789) B1115789
theorem B743875 : Blo 742328 743875 := bstep (se 1 (by rfl) ⟨557906, by rfl⟩ : syracuseStep 743875 = 1115813) B1115813
theorem B743891 : Blo 742328 743891 := bstep (se 1 (by rfl) ⟨557918, by rfl⟩ : syracuseStep 743891 = 1115837) B1115837
theorem B743907 : Blo 742328 743907 := bstep (se 1 (by rfl) ⟨557930, by rfl⟩ : syracuseStep 743907 = 1115861) B1115861
theorem B743923 : Blo 742328 743923 := bstep (se 1 (by rfl) ⟨557942, by rfl⟩ : syracuseStep 743923 = 1115885) B1115885
theorem B743939 : Blo 742328 743939 := bstep (se 1 (by rfl) ⟨557954, by rfl⟩ : syracuseStep 743939 = 1115909) B1115909
theorem B2120195 : Blo 742328 2120195 := bstep (se 1 (by rfl) ⟨1590146, by rfl⟩ : syracuseStep 2120195 = 3180293) B3180293
theorem B743955 : Blo 742328 743955 := bstep (se 1 (by rfl) ⟨557966, by rfl⟩ : syracuseStep 743955 = 1115933) B1115933
theorem B743971 : Blo 742328 743971 := bstep (se 1 (by rfl) ⟨557978, by rfl⟩ : syracuseStep 743971 = 1115957) B1115957
theorem B743987 : Blo 742328 743987 := bstep (se 1 (by rfl) ⟨557990, by rfl⟩ : syracuseStep 743987 = 1115981) B1115981
theorem B744003 : Blo 742328 744003 := bstep (se 1 (by rfl) ⟨558002, by rfl⟩ : syracuseStep 744003 = 1116005) B1116005
theorem B744019 : Blo 742328 744019 := bstep (se 1 (by rfl) ⟨558014, by rfl⟩ : syracuseStep 744019 = 1116029) B1116029
theorem B744035 : Blo 742328 744035 := bstep (se 1 (by rfl) ⟨558026, by rfl⟩ : syracuseStep 744035 = 1116053) B1116053
theorem B744051 : Blo 742328 744051 := bstep (se 1 (by rfl) ⟨558038, by rfl⟩ : syracuseStep 744051 = 1116077) B1116077
theorem B744067 : Blo 742328 744067 := bstep (se 1 (by rfl) ⟨558050, by rfl⟩ : syracuseStep 744067 = 1116101) B1116101
theorem B744083 : Blo 742328 744083 := bstep (se 1 (by rfl) ⟨558062, by rfl⟩ : syracuseStep 744083 = 1116125) B1116125
theorem B744099 : Blo 742328 744099 := bstep (se 1 (by rfl) ⟨558074, by rfl⟩ : syracuseStep 744099 = 1116149) B1116149
theorem B744115 : Blo 742328 744115 := bstep (se 1 (by rfl) ⟨558086, by rfl⟩ : syracuseStep 744115 = 1116173) B1116173
theorem B744131 : Blo 742328 744131 := bstep (se 1 (by rfl) ⟨558098, by rfl⟩ : syracuseStep 744131 = 1116197) B1116197
theorem B744147 : Blo 742328 744147 := bstep (se 1 (by rfl) ⟨558110, by rfl⟩ : syracuseStep 744147 = 1116221) B1116221
theorem B744163 : Blo 742328 744163 := bstep (se 1 (by rfl) ⟨558122, by rfl⟩ : syracuseStep 744163 = 1116245) B1116245
theorem B2513645 : Blo 742328 2513645 := bstep (se 3 (by rfl) ⟨471308, by rfl⟩ : syracuseStep 2513645 = 942617) B942617
theorem B744179 : Blo 742328 744179 := bstep (se 1 (by rfl) ⟨558134, by rfl⟩ : syracuseStep 744179 = 1116269) B1116269
theorem B744195 : Blo 742328 744195 := bstep (se 1 (by rfl) ⟨558146, by rfl⟩ : syracuseStep 744195 = 1116293) B1116293
theorem B744211 : Blo 742328 744211 := bstep (se 1 (by rfl) ⟨558158, by rfl⟩ : syracuseStep 744211 = 1116317) B1116317
theorem B940835 : Blo 742328 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B744227 : Blo 742328 744227 := bstep (se 1 (by rfl) ⟨558170, by rfl⟩ : syracuseStep 744227 = 1116341) B1116341
theorem B2513699 : Blo 742328 2513699 := bstep (se 1 (by rfl) ⟨1885274, by rfl⟩ : syracuseStep 2513699 = 3770549) B3770549
theorem B744243 : Blo 742328 744243 := bstep (se 1 (by rfl) ⟨558182, by rfl⟩ : syracuseStep 744243 = 1116365) B1116365
theorem B744259 : Blo 742328 744259 := bstep (se 1 (by rfl) ⟨558194, by rfl⟩ : syracuseStep 744259 = 1116389) B1116389
theorem B2120525 : Blo 742328 2120525 := bstep (se 3 (by rfl) ⟨397598, by rfl⟩ : syracuseStep 2120525 = 795197) B795197
theorem B744275 : Blo 742328 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B744291 : Blo 742328 744291 := bstep (se 1 (by rfl) ⟨558218, by rfl⟩ : syracuseStep 744291 = 1116437) B1116437
theorem B744307 : Blo 742328 744307 := bstep (se 1 (by rfl) ⟨558230, by rfl⟩ : syracuseStep 744307 = 1116461) B1116461
theorem B744323 : Blo 742328 744323 := bstep (se 1 (by rfl) ⟨558242, by rfl⟩ : syracuseStep 744323 = 1116485) B1116485
theorem B2120593 : Blo 742328 2120593 := bstep (se 2 (by rfl) ⟨795222, by rfl⟩ : syracuseStep 2120593 = 1590445) B1590445
theorem B744339 : Blo 742328 744339 := bstep (se 1 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 744339 = 1116509) B1116509
theorem B744355 : Blo 742328 744355 := bstep (se 1 (by rfl) ⟨558266, by rfl⟩ : syracuseStep 744355 = 1116533) B1116533
theorem B744371 : Blo 742328 744371 := bstep (se 1 (by rfl) ⟨558278, by rfl⟩ : syracuseStep 744371 = 1116557) B1116557
theorem B744387 : Blo 742328 744387 := bstep (se 1 (by rfl) ⟨558290, by rfl⟩ : syracuseStep 744387 = 1116581) B1116581
theorem B2382797 : Blo 742328 2382797 := bstep (se 3 (by rfl) ⟨446774, by rfl⟩ : syracuseStep 2382797 = 893549) B893549
theorem B744403 : Blo 742328 744403 := bstep (se 1 (by rfl) ⟨558302, by rfl⟩ : syracuseStep 744403 = 1116605) B1116605
theorem B744419 : Blo 742328 744419 := bstep (se 1 (by rfl) ⟨558314, by rfl⟩ : syracuseStep 744419 = 1116629) B1116629
theorem B744435 : Blo 742328 744435 := bstep (se 1 (by rfl) ⟨558326, by rfl⟩ : syracuseStep 744435 = 1116653) B1116653
theorem B1694723 : Blo 742328 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B744451 : Blo 742328 744451 := bstep (se 1 (by rfl) ⟨558338, by rfl⟩ : syracuseStep 744451 = 1116677) B1116677
theorem B744467 : Blo 742328 744467 := bstep (se 1 (by rfl) ⟨558350, by rfl⟩ : syracuseStep 744467 = 1116701) B1116701
theorem B744483 : Blo 742328 744483 := bstep (se 1 (by rfl) ⟨558362, by rfl⟩ : syracuseStep 744483 = 1116725) B1116725
theorem B2513969 : Blo 742328 2513969 := bstep (se 2 (by rfl) ⟨942738, by rfl⟩ : syracuseStep 2513969 = 1885477) B1885477
theorem B744499 : Blo 742328 744499 := bstep (se 1 (by rfl) ⟨558374, by rfl⟩ : syracuseStep 744499 = 1116749) B1116749
theorem B744515 : Blo 742328 744515 := bstep (se 1 (by rfl) ⟨558386, by rfl⟩ : syracuseStep 744515 = 1116773) B1116773
theorem B744531 : Blo 742328 744531 := bstep (se 1 (by rfl) ⟨558398, by rfl⟩ : syracuseStep 744531 = 1116797) B1116797
theorem B744547 : Blo 742328 744547 := bstep (se 1 (by rfl) ⟨558410, by rfl⟩ : syracuseStep 744547 = 1116821) B1116821
theorem B744563 : Blo 742328 744563 := bstep (se 1 (by rfl) ⟨558422, by rfl⟩ : syracuseStep 744563 = 1116845) B1116845
theorem B744579 : Blo 742328 744579 := bstep (se 1 (by rfl) ⟨558434, by rfl⟩ : syracuseStep 744579 = 1116869) B1116869
theorem B744595 : Blo 742328 744595 := bstep (se 1 (by rfl) ⟨558446, by rfl⟩ : syracuseStep 744595 = 1116893) B1116893
theorem B744611 : Blo 742328 744611 := bstep (se 1 (by rfl) ⟨558458, by rfl⟩ : syracuseStep 744611 = 1116917) B1116917
theorem B2120867 : Blo 742328 2120867 := bstep (se 1 (by rfl) ⟨1590650, by rfl⟩ : syracuseStep 2120867 = 3181301) B3181301
theorem B744627 : Blo 742328 744627 := bstep (se 1 (by rfl) ⟨558470, by rfl⟩ : syracuseStep 744627 = 1116941) B1116941
theorem B744643 : Blo 742328 744643 := bstep (se 1 (by rfl) ⟨558482, by rfl⟩ : syracuseStep 744643 = 1116965) B1116965
theorem B4021445 : Blo 742328 4021445 := bstep (se 4 (by rfl) ⟨377010, by rfl⟩ : syracuseStep 4021445 = 754021) B754021
theorem B744659 : Blo 742328 744659 := bstep (se 1 (by rfl) ⟨558494, by rfl⟩ : syracuseStep 744659 = 1116989) B1116989
theorem B744675 : Blo 742328 744675 := bstep (se 1 (by rfl) ⟨558506, by rfl⟩ : syracuseStep 744675 = 1117013) B1117013
theorem B744691 : Blo 742328 744691 := bstep (se 1 (by rfl) ⟨558518, by rfl⟩ : syracuseStep 744691 = 1117037) B1117037
theorem B744707 : Blo 742328 744707 := bstep (se 1 (by rfl) ⟨558530, by rfl⟩ : syracuseStep 744707 = 1117061) B1117061
theorem B744723 : Blo 742328 744723 := bstep (se 1 (by rfl) ⟨558542, by rfl⟩ : syracuseStep 744723 = 1117085) B1117085
theorem B744739 : Blo 742328 744739 := bstep (se 1 (by rfl) ⟨558554, by rfl⟩ : syracuseStep 744739 = 1117109) B1117109
theorem B744755 : Blo 742328 744755 := bstep (se 1 (by rfl) ⟨558566, by rfl⟩ : syracuseStep 744755 = 1117133) B1117133
theorem B744771 : Blo 742328 744771 := bstep (se 1 (by rfl) ⟨558578, by rfl⟩ : syracuseStep 744771 = 1117157) B1117157
theorem B744787 : Blo 742328 744787 := bstep (se 1 (by rfl) ⟨558590, by rfl⟩ : syracuseStep 744787 = 1117181) B1117181
theorem B744803 : Blo 742328 744803 := bstep (se 1 (by rfl) ⟨558602, by rfl⟩ : syracuseStep 744803 = 1117205) B1117205
theorem B744819 : Blo 742328 744819 := bstep (se 1 (by rfl) ⟨558614, by rfl⟩ : syracuseStep 744819 = 1117229) B1117229
theorem B744835 : Blo 742328 744835 := bstep (se 1 (by rfl) ⟨558626, by rfl⟩ : syracuseStep 744835 = 1117253) B1117253
theorem B744851 : Blo 742328 744851 := bstep (se 1 (by rfl) ⟨558638, by rfl⟩ : syracuseStep 744851 = 1117277) B1117277
theorem B744867 : Blo 742328 744867 := bstep (se 1 (by rfl) ⟨558650, by rfl⟩ : syracuseStep 744867 = 1117301) B1117301
theorem B744883 : Blo 742328 744883 := bstep (se 1 (by rfl) ⟨558662, by rfl⟩ : syracuseStep 744883 = 1117325) B1117325
theorem B744899 : Blo 742328 744899 := bstep (se 1 (by rfl) ⟨558674, by rfl⟩ : syracuseStep 744899 = 1117349) B1117349
theorem B744915 : Blo 742328 744915 := bstep (se 1 (by rfl) ⟨558686, by rfl⟩ : syracuseStep 744915 = 1117373) B1117373
theorem B941539 : Blo 742328 941539 := bstep (se 1 (by rfl) ⟨706154, by rfl⟩ : syracuseStep 941539 = 1412309) B1412309
theorem B744931 : Blo 742328 744931 := bstep (se 1 (by rfl) ⟨558698, by rfl⟩ : syracuseStep 744931 = 1117397) B1117397
theorem B744947 : Blo 742328 744947 := bstep (se 1 (by rfl) ⟨558710, by rfl⟩ : syracuseStep 744947 = 1117421) B1117421
theorem B744963 : Blo 742328 744963 := bstep (se 1 (by rfl) ⟨558722, by rfl⟩ : syracuseStep 744963 = 1117445) B1117445
theorem B744979 : Blo 742328 744979 := bstep (se 1 (by rfl) ⟨558734, by rfl⟩ : syracuseStep 744979 = 1117469) B1117469
theorem B744995 : Blo 742328 744995 := bstep (se 1 (by rfl) ⟨558746, by rfl⟩ : syracuseStep 744995 = 1117493) B1117493
theorem B745011 : Blo 742328 745011 := bstep (se 1 (by rfl) ⟨558758, by rfl⟩ : syracuseStep 745011 = 1117517) B1117517
theorem B941635 : Blo 742328 941635 := bstep (se 1 (by rfl) ⟨706226, by rfl⟩ : syracuseStep 941635 = 1412453) B1412453
theorem B745027 : Blo 742328 745027 := bstep (se 1 (by rfl) ⟨558770, by rfl⟩ : syracuseStep 745027 = 1117541) B1117541
theorem B2514509 : Blo 742328 2514509 := bstep (se 3 (by rfl) ⟨471470, by rfl⟩ : syracuseStep 2514509 = 942941) B942941
theorem B745043 : Blo 742328 745043 := bstep (se 1 (by rfl) ⟨558782, by rfl⟩ : syracuseStep 745043 = 1117565) B1117565
theorem B745059 : Blo 742328 745059 := bstep (se 1 (by rfl) ⟨558794, by rfl⟩ : syracuseStep 745059 = 1117589) B1117589
theorem B745075 : Blo 742328 745075 := bstep (se 1 (by rfl) ⟨558806, by rfl⟩ : syracuseStep 745075 = 1117613) B1117613
theorem B2514563 : Blo 742328 2514563 := bstep (se 1 (by rfl) ⟨1885922, by rfl⟩ : syracuseStep 2514563 = 3771845) B3771845
theorem B745091 : Blo 742328 745091 := bstep (se 1 (by rfl) ⟨558818, by rfl⟩ : syracuseStep 745091 = 1117637) B1117637
theorem B745107 : Blo 742328 745107 := bstep (se 1 (by rfl) ⟨558830, by rfl⟩ : syracuseStep 745107 = 1117661) B1117661
theorem B745123 : Blo 742328 745123 := bstep (se 1 (by rfl) ⟨558842, by rfl⟩ : syracuseStep 745123 = 1117685) B1117685
theorem B745139 : Blo 742328 745139 := bstep (se 1 (by rfl) ⟨558854, by rfl⟩ : syracuseStep 745139 = 1117709) B1117709
theorem B745155 : Blo 742328 745155 := bstep (se 1 (by rfl) ⟨558866, by rfl⟩ : syracuseStep 745155 = 1117733) B1117733
theorem B745171 : Blo 742328 745171 := bstep (se 1 (by rfl) ⟨558878, by rfl⟩ : syracuseStep 745171 = 1117757) B1117757
theorem B745187 : Blo 742328 745187 := bstep (se 1 (by rfl) ⟨558890, by rfl⟩ : syracuseStep 745187 = 1117781) B1117781
theorem B3759857 : Blo 742328 3759857 := bstep (se 2 (by rfl) ⟨1409946, by rfl⟩ : syracuseStep 3759857 = 2819893) B2819893
theorem B745203 : Blo 742328 745203 := bstep (se 1 (by rfl) ⟨558902, by rfl⟩ : syracuseStep 745203 = 1117805) B1117805
theorem B745219 : Blo 742328 745219 := bstep (se 1 (by rfl) ⟨558914, by rfl⟩ : syracuseStep 745219 = 1117829) B1117829
theorem B745235 : Blo 742328 745235 := bstep (se 1 (by rfl) ⟨558926, by rfl⟩ : syracuseStep 745235 = 1117853) B1117853
theorem B745251 : Blo 742328 745251 := bstep (se 1 (by rfl) ⟨558938, by rfl⟩ : syracuseStep 745251 = 1117877) B1117877
theorem B745267 : Blo 742328 745267 := bstep (se 1 (by rfl) ⟨558950, by rfl⟩ : syracuseStep 745267 = 1117901) B1117901
theorem B745283 : Blo 742328 745283 := bstep (se 1 (by rfl) ⟨558962, by rfl⟩ : syracuseStep 745283 = 1117925) B1117925
theorem B745299 : Blo 742328 745299 := bstep (se 1 (by rfl) ⟨558974, by rfl⟩ : syracuseStep 745299 = 1117949) B1117949
theorem B745315 : Blo 742328 745315 := bstep (se 1 (by rfl) ⟨558986, by rfl⟩ : syracuseStep 745315 = 1117973) B1117973
theorem B745331 : Blo 742328 745331 := bstep (se 1 (by rfl) ⟨558998, by rfl⟩ : syracuseStep 745331 = 1117997) B1117997
theorem B745347 : Blo 742328 745347 := bstep (se 1 (by rfl) ⟨559010, by rfl⟩ : syracuseStep 745347 = 1118021) B1118021
theorem B2514833 : Blo 742328 2514833 := bstep (se 2 (by rfl) ⟨943062, by rfl⟩ : syracuseStep 2514833 = 1886125) B1886125
theorem B745363 : Blo 742328 745363 := bstep (se 1 (by rfl) ⟨559022, by rfl⟩ : syracuseStep 745363 = 1118045) B1118045
theorem B745379 : Blo 742328 745379 := bstep (se 1 (by rfl) ⟨559034, by rfl⟩ : syracuseStep 745379 = 1118069) B1118069
theorem B745395 : Blo 742328 745395 := bstep (se 1 (by rfl) ⟨559046, by rfl⟩ : syracuseStep 745395 = 1118093) B1118093
theorem B745411 : Blo 742328 745411 := bstep (se 1 (by rfl) ⟨559058, by rfl⟩ : syracuseStep 745411 = 1118117) B1118117
theorem B745427 : Blo 742328 745427 := bstep (se 1 (by rfl) ⟨559070, by rfl⟩ : syracuseStep 745427 = 1118141) B1118141
theorem B745443 : Blo 742328 745443 := bstep (se 1 (by rfl) ⟨559082, by rfl⟩ : syracuseStep 745443 = 1118165) B1118165
theorem B2121709 : Blo 742328 2121709 := bstep (se 3 (by rfl) ⟨397820, by rfl⟩ : syracuseStep 2121709 = 795641) B795641
theorem B745459 : Blo 742328 745459 := bstep (se 1 (by rfl) ⟨559094, by rfl⟩ : syracuseStep 745459 = 1118189) B1118189
theorem B745475 : Blo 742328 745475 := bstep (se 1 (by rfl) ⟨559106, by rfl⟩ : syracuseStep 745475 = 1118213) B1118213
theorem B745491 : Blo 742328 745491 := bstep (se 1 (by rfl) ⟨559118, by rfl⟩ : syracuseStep 745491 = 1118237) B1118237
theorem B745507 : Blo 742328 745507 := bstep (se 1 (by rfl) ⟨559130, by rfl⟩ : syracuseStep 745507 = 1118261) B1118261
theorem B942131 : Blo 742328 942131 := bstep (se 1 (by rfl) ⟨706598, by rfl⟩ : syracuseStep 942131 = 1413197) B1413197
theorem B745523 : Blo 742328 745523 := bstep (se 1 (by rfl) ⟨559142, by rfl⟩ : syracuseStep 745523 = 1118285) B1118285
theorem B745539 : Blo 742328 745539 := bstep (se 1 (by rfl) ⟨559154, by rfl⟩ : syracuseStep 745539 = 1118309) B1118309
theorem B745555 : Blo 742328 745555 := bstep (se 1 (by rfl) ⟨559166, by rfl⟩ : syracuseStep 745555 = 1118333) B1118333
theorem B745571 : Blo 742328 745571 := bstep (se 1 (by rfl) ⟨559178, by rfl⟩ : syracuseStep 745571 = 1118357) B1118357
theorem B745587 : Blo 742328 745587 := bstep (se 1 (by rfl) ⟨559190, by rfl⟩ : syracuseStep 745587 = 1118381) B1118381
theorem B745603 : Blo 742328 745603 := bstep (se 1 (by rfl) ⟨559202, by rfl⟩ : syracuseStep 745603 = 1118405) B1118405
theorem B2121869 : Blo 742328 2121869 := bstep (se 3 (by rfl) ⟨397850, by rfl⟩ : syracuseStep 2121869 = 795701) B795701
theorem B745619 : Blo 742328 745619 := bstep (se 1 (by rfl) ⟨559214, by rfl⟩ : syracuseStep 745619 = 1118429) B1118429
theorem B745635 : Blo 742328 745635 := bstep (se 1 (by rfl) ⟨559226, by rfl⟩ : syracuseStep 745635 = 1118453) B1118453
theorem B745651 : Blo 742328 745651 := bstep (se 1 (by rfl) ⟨559238, by rfl⟩ : syracuseStep 745651 = 1118477) B1118477
theorem B745667 : Blo 742328 745667 := bstep (se 1 (by rfl) ⟨559250, by rfl⟩ : syracuseStep 745667 = 1118501) B1118501
theorem B745683 : Blo 742328 745683 := bstep (se 1 (by rfl) ⟨559262, by rfl⟩ : syracuseStep 745683 = 1118525) B1118525
theorem B745699 : Blo 742328 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B745715 : Blo 742328 745715 := bstep (se 1 (by rfl) ⟨559286, by rfl⟩ : syracuseStep 745715 = 1118573) B1118573
theorem B745731 : Blo 742328 745731 := bstep (se 1 (by rfl) ⟨559298, by rfl⟩ : syracuseStep 745731 = 1118597) B1118597
theorem B745747 : Blo 742328 745747 := bstep (se 1 (by rfl) ⟨559310, by rfl⟩ : syracuseStep 745747 = 1118621) B1118621
theorem B745763 : Blo 742328 745763 := bstep (se 1 (by rfl) ⟨559322, by rfl⟩ : syracuseStep 745763 = 1118645) B1118645
theorem B745779 : Blo 742328 745779 := bstep (se 1 (by rfl) ⟨559334, by rfl⟩ : syracuseStep 745779 = 1118669) B1118669
theorem B2122051 : Blo 742328 2122051 := bstep (se 1 (by rfl) ⟨1591538, by rfl⟩ : syracuseStep 2122051 = 3183077) B3183077
theorem B745795 : Blo 742328 745795 := bstep (se 1 (by rfl) ⟨559346, by rfl⟩ : syracuseStep 745795 = 1118693) B1118693
theorem B745811 : Blo 742328 745811 := bstep (se 1 (by rfl) ⟨559358, by rfl⟩ : syracuseStep 745811 = 1118717) B1118717
theorem B745827 : Blo 742328 745827 := bstep (se 1 (by rfl) ⟨559370, by rfl⟩ : syracuseStep 745827 = 1118741) B1118741
theorem B745843 : Blo 742328 745843 := bstep (se 1 (by rfl) ⟨559382, by rfl⟩ : syracuseStep 745843 = 1118765) B1118765
theorem B745859 : Blo 742328 745859 := bstep (se 1 (by rfl) ⟨559394, by rfl⟩ : syracuseStep 745859 = 1118789) B1118789
theorem B745875 : Blo 742328 745875 := bstep (se 1 (by rfl) ⟨559406, by rfl⟩ : syracuseStep 745875 = 1118813) B1118813
theorem B745891 : Blo 742328 745891 := bstep (se 1 (by rfl) ⟨559418, by rfl⟩ : syracuseStep 745891 = 1118837) B1118837
theorem B2515373 : Blo 742328 2515373 := bstep (se 3 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 2515373 = 943265) B943265
theorem B745907 : Blo 742328 745907 := bstep (se 1 (by rfl) ⟨559430, by rfl⟩ : syracuseStep 745907 = 1118861) B1118861
theorem B745923 : Blo 742328 745923 := bstep (se 1 (by rfl) ⟨559442, by rfl⟩ : syracuseStep 745923 = 1118885) B1118885
theorem B745939 : Blo 742328 745939 := bstep (se 1 (by rfl) ⟨559454, by rfl⟩ : syracuseStep 745939 = 1118909) B1118909
theorem B2515427 : Blo 742328 2515427 := bstep (se 1 (by rfl) ⟨1886570, by rfl⟩ : syracuseStep 2515427 = 3773141) B3773141
theorem B745955 : Blo 742328 745955 := bstep (se 1 (by rfl) ⟨559466, by rfl⟩ : syracuseStep 745955 = 1118933) B1118933
theorem B745971 : Blo 742328 745971 := bstep (se 1 (by rfl) ⟨559478, by rfl⟩ : syracuseStep 745971 = 1118957) B1118957
theorem B745987 : Blo 742328 745987 := bstep (se 1 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 745987 = 1118981) B1118981
theorem B746003 : Blo 742328 746003 := bstep (se 1 (by rfl) ⟨559502, by rfl⟩ : syracuseStep 746003 = 1119005) B1119005
theorem B746019 : Blo 742328 746019 := bstep (se 1 (by rfl) ⟨559514, by rfl⟩ : syracuseStep 746019 = 1119029) B1119029
theorem B746035 : Blo 742328 746035 := bstep (se 1 (by rfl) ⟨559526, by rfl⟩ : syracuseStep 746035 = 1119053) B1119053
theorem B746051 : Blo 742328 746051 := bstep (se 1 (by rfl) ⟨559538, by rfl⟩ : syracuseStep 746051 = 1119077) B1119077
theorem B746067 : Blo 742328 746067 := bstep (se 1 (by rfl) ⟨559550, by rfl⟩ : syracuseStep 746067 = 1119101) B1119101
theorem B746083 : Blo 742328 746083 := bstep (se 1 (by rfl) ⟨559562, by rfl⟩ : syracuseStep 746083 = 1119125) B1119125
theorem B746099 : Blo 742328 746099 := bstep (se 1 (by rfl) ⟨559574, by rfl⟩ : syracuseStep 746099 = 1119149) B1119149
theorem B746115 : Blo 742328 746115 := bstep (se 1 (by rfl) ⟨559586, by rfl⟩ : syracuseStep 746115 = 1119173) B1119173
theorem B746131 : Blo 742328 746131 := bstep (se 1 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 746131 = 1119197) B1119197
theorem B746147 : Blo 742328 746147 := bstep (se 1 (by rfl) ⟨559610, by rfl⟩ : syracuseStep 746147 = 1119221) B1119221
theorem B746163 : Blo 742328 746163 := bstep (se 1 (by rfl) ⟨559622, by rfl⟩ : syracuseStep 746163 = 1119245) B1119245
theorem B746179 : Blo 742328 746179 := bstep (se 1 (by rfl) ⟨559634, by rfl⟩ : syracuseStep 746179 = 1119269) B1119269
theorem B746195 : Blo 742328 746195 := bstep (se 1 (by rfl) ⟨559646, by rfl⟩ : syracuseStep 746195 = 1119293) B1119293
theorem B746211 : Blo 742328 746211 := bstep (se 1 (by rfl) ⟨559658, by rfl⟩ : syracuseStep 746211 = 1119317) B1119317
theorem B2515697 : Blo 742328 2515697 := bstep (se 2 (by rfl) ⟨943386, by rfl⟩ : syracuseStep 2515697 = 1886773) B1886773
theorem B942835 : Blo 742328 942835 := bstep (se 1 (by rfl) ⟨707126, by rfl⟩ : syracuseStep 942835 = 1414253) B1414253
theorem B746227 : Blo 742328 746227 := bstep (se 1 (by rfl) ⟨559670, by rfl⟩ : syracuseStep 746227 = 1119341) B1119341
theorem B746243 : Blo 742328 746243 := bstep (se 1 (by rfl) ⟨559682, by rfl⟩ : syracuseStep 746243 = 1119365) B1119365
theorem B746259 : Blo 742328 746259 := bstep (se 1 (by rfl) ⟨559694, by rfl⟩ : syracuseStep 746259 = 1119389) B1119389
theorem B746275 : Blo 742328 746275 := bstep (se 1 (by rfl) ⟨559706, by rfl⟩ : syracuseStep 746275 = 1119413) B1119413
theorem B746291 : Blo 742328 746291 := bstep (se 1 (by rfl) ⟨559718, by rfl⟩ : syracuseStep 746291 = 1119437) B1119437
theorem B746307 : Blo 742328 746307 := bstep (se 1 (by rfl) ⟨559730, by rfl⟩ : syracuseStep 746307 = 1119461) B1119461
theorem B942931 : Blo 742328 942931 := bstep (se 1 (by rfl) ⟨707198, by rfl⟩ : syracuseStep 942931 = 1414397) B1414397
theorem B746323 : Blo 742328 746323 := bstep (se 1 (by rfl) ⟨559742, by rfl⟩ : syracuseStep 746323 = 1119485) B1119485
theorem B3761315 : Blo 742328 3761315 := bstep (se 1 (by rfl) ⟨2820986, by rfl⟩ : syracuseStep 3761315 = 5641973) B5641973
theorem B2516237 : Blo 742328 2516237 := bstep (se 3 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 2516237 = 943589) B943589
theorem B943427 : Blo 742328 943427 := bstep (se 1 (by rfl) ⟨707570, by rfl⟩ : syracuseStep 943427 = 1415141) B1415141
theorem B2516291 : Blo 742328 2516291 := bstep (se 1 (by rfl) ⟨1887218, by rfl⟩ : syracuseStep 2516291 = 3774437) B3774437
theorem B2385283 : Blo 742328 2385283 := bstep (se 1 (by rfl) ⟨1788962, by rfl⟩ : syracuseStep 2385283 = 3577925) B3577925
theorem B3630563 : Blo 742328 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B2385425 : Blo 742328 2385425 := bstep (se 2 (by rfl) ⟨894534, by rfl⟩ : syracuseStep 2385425 = 1789069) B1789069
theorem B2516561 : Blo 742328 2516561 := bstep (se 2 (by rfl) ⟨943710, by rfl⟩ : syracuseStep 2516561 = 1887421) B1887421
theorem B2385539 : Blo 742328 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B2123441 : Blo 742328 2123441 := bstep (se 2 (by rfl) ⟨796290, by rfl⟩ : syracuseStep 2123441 = 1592581) B1592581
theorem B3762125 : Blo 742328 3762125 := bstep (se 3 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 3762125 = 1410797) B1410797
theorem B6023153 : Blo 742328 6023153 := bstep (se 2 (by rfl) ⟨2258682, by rfl⟩ : syracuseStep 6023153 = 4517365) B4517365
theorem B944131 : Blo 742328 944131 := bstep (se 1 (by rfl) ⟨708098, by rfl⟩ : syracuseStep 944131 = 1416197) B1416197
theorem B944227 : Blo 742328 944227 := bstep (se 1 (by rfl) ⟨708170, by rfl⟩ : syracuseStep 944227 = 1416341) B1416341
theorem B2517101 : Blo 742328 2517101 := bstep (se 3 (by rfl) ⟨471956, by rfl⟩ : syracuseStep 2517101 = 943913) B943913
theorem B2517155 : Blo 742328 2517155 := bstep (se 1 (by rfl) ⟨1887866, by rfl⟩ : syracuseStep 2517155 = 3775733) B3775733
theorem B64481507 : Blo 742328 64481507 := bstep (se 1 (by rfl) ⟨48361130, by rfl⟩ : syracuseStep 64481507 = 96722261) B96722261
theorem B2681137 : Blo 742328 2681137 := bstep (se 2 (by rfl) ⟨1005426, by rfl⟩ : syracuseStep 2681137 = 2010853) B2010853
theorem B2517425 : Blo 742328 2517425 := bstep (se 2 (by rfl) ⟨944034, by rfl⟩ : syracuseStep 2517425 = 1888069) B1888069
theorem B2386513 : Blo 742328 2386513 := bstep (se 2 (by rfl) ⟨894942, by rfl⟩ : syracuseStep 2386513 = 1789885) B1789885
theorem B2124397 : Blo 742328 2124397 := bstep (se 3 (by rfl) ⟨398324, by rfl⟩ : syracuseStep 2124397 = 796649) B796649
theorem B1632881 : Blo 742328 1632881 := bstep (se 2 (by rfl) ⟨612330, by rfl⟩ : syracuseStep 1632881 = 1224661) B1224661
theorem B4025123 : Blo 742328 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B2124625 : Blo 742328 2124625 := bstep (se 2 (by rfl) ⟨796734, by rfl⟩ : syracuseStep 2124625 = 1593469) B1593469
theorem B5368675 : Blo 742328 5368675 := bstep (se 1 (by rfl) ⟨4026506, by rfl⟩ : syracuseStep 5368675 = 8053013) B8053013
theorem B9563021 : Blo 742328 9563021 := bstep (se 3 (by rfl) ⟨1793066, by rfl⟩ : syracuseStep 9563021 = 3586133) B3586133
theorem B4025251 : Blo 742328 4025251 := bstep (se 1 (by rfl) ⟨3018938, by rfl⟩ : syracuseStep 4025251 = 6037877) B6037877
theorem B2517965 : Blo 742328 2517965 := bstep (se 3 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 2517965 = 944237) B944237
theorem B2124785 : Blo 742328 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2518019 : Blo 742328 2518019 := bstep (se 1 (by rfl) ⟨1888514, by rfl⟩ : syracuseStep 2518019 = 3777029) B3777029
theorem B5663843 : Blo 742328 5663843 := bstep (se 1 (by rfl) ⟨4247882, by rfl⟩ : syracuseStep 5663843 = 8495765) B8495765
theorem B2124899 : Blo 742328 2124899 := bstep (se 1 (by rfl) ⟨1593674, by rfl⟩ : syracuseStep 2124899 = 3187349) B3187349
theorem B2583683 : Blo 742328 2583683 := bstep (se 1 (by rfl) ⟨1937762, by rfl⟩ : syracuseStep 2583683 = 3875525) B3875525
theorem B6352141 : Blo 742328 6352141 := bstep (se 3 (by rfl) ⟨1191026, by rfl⟩ : syracuseStep 6352141 = 2382053) B2382053
theorem B2518289 : Blo 742328 2518289 := bstep (se 2 (by rfl) ⟨944358, by rfl⟩ : syracuseStep 2518289 = 1888717) B1888717
theorem B3403313 : Blo 742328 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B1961635 : Blo 742328 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B13758149 : Blo 742328 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B3174157 : Blo 742328 3174157 := bstep (se 3 (by rfl) ⟨595154, by rfl⟩ : syracuseStep 3174157 = 1190309) B1190309
theorem B2518829 : Blo 742328 2518829 := bstep (se 3 (by rfl) ⟨472280, by rfl⟩ : syracuseStep 2518829 = 944561) B944561
theorem B1208369 : Blo 742328 1208369 := bstep (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) B906277
theorem B848051 : Blo 742328 848051 := bstep (se 1 (by rfl) ⟨636038, by rfl⟩ : syracuseStep 848051 = 1272077) B1272077
theorem B3010765 : Blo 742328 3010765 := bstep (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) B1129037
theorem B1274321 : Blo 742328 1274321 := bstep (se 2 (by rfl) ⟨477870, by rfl⟩ : syracuseStep 1274321 = 955741) B955741
theorem B6353477 : Blo 742328 6353477 := bstep (se 4 (by rfl) ⟨595638, by rfl⟩ : syracuseStep 6353477 = 1191277) B1191277
theorem B4289123 : Blo 742328 4289123 := bstep (se 1 (by rfl) ⟨3216842, by rfl⟩ : syracuseStep 4289123 = 6433685) B6433685
theorem B3765041 : Blo 742328 3765041 := bstep (se 2 (by rfl) ⟨1411890, by rfl⟩ : syracuseStep 3765041 = 2823781) B2823781
theorem B4027589 : Blo 742328 4027589 := bstep (se 4 (by rfl) ⟨377586, by rfl⟩ : syracuseStep 4027589 = 755173) B755173
theorem B3569123 : Blo 742328 3569123 := bstep (se 1 (by rfl) ⟨2676842, by rfl⟩ : syracuseStep 3569123 = 5353685) B5353685
theorem B1275635 : Blo 742328 1275635 := bstep (se 1 (by rfl) ⟨956726, by rfl⟩ : syracuseStep 1275635 = 1913453) B1913453
theorem B2684771 : Blo 742328 2684771 := bstep (se 1 (by rfl) ⟨2013578, by rfl⟩ : syracuseStep 2684771 = 4027157) B4027157
theorem B9074531 : Blo 742328 9074531 := bstep (se 1 (by rfl) ⟨6805898, by rfl⟩ : syracuseStep 9074531 = 13611797) B13611797
theorem B2455427 : Blo 742328 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B3569777 : Blo 742328 3569777 := bstep (se 2 (by rfl) ⟨1338666, by rfl⟩ : syracuseStep 3569777 = 2677333) B2677333
theorem B1341571 : Blo 742328 1341571 := bstep (se 1 (by rfl) ⟨1006178, by rfl⟩ : syracuseStep 1341571 = 2012357) B2012357
theorem B1702097 : Blo 742328 1702097 := bstep (se 2 (by rfl) ⟨638286, by rfl⟩ : syracuseStep 1702097 = 1276573) B1276573
theorem B3766499 : Blo 742328 3766499 := bstep (se 1 (by rfl) ⟨2824874, by rfl⟩ : syracuseStep 3766499 = 5649749) B5649749
theorem B2586865 : Blo 742328 2586865 := bstep (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) B1940149
theorem B850387 : Blo 742328 850387 := bstep (se 1 (by rfl) ⟨637790, by rfl⟩ : syracuseStep 850387 = 1275581) B1275581
theorem B2259533 : Blo 742328 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B1342097 : Blo 742328 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B2390897 : Blo 742328 2390897 := bstep (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) B1793173
theorem B3767309 : Blo 742328 3767309 := bstep (se 3 (by rfl) ⟨706370, by rfl⟩ : syracuseStep 3767309 = 1412741) B1412741
theorem B1211539 : Blo 742328 1211539 := bstep (se 1 (by rfl) ⟨908654, by rfl⟩ : syracuseStep 1211539 = 1817309) B1817309
theorem B1211603 : Blo 742328 1211603 := bstep (se 1 (by rfl) ⟨908702, by rfl⟩ : syracuseStep 1211603 = 1817405) B1817405
theorem B1670417 : Blo 742328 1670417 := bstep (se 2 (by rfl) ⟨626406, by rfl⟩ : syracuseStep 1670417 = 1252813) B1252813
theorem B1670435 : Blo 742328 1670435 := bstep (se 1 (by rfl) ⟨1252826, by rfl⟩ : syracuseStep 1670435 = 2505653) B2505653
theorem B9534773 : Blo 742328 9534773 := bstep (se 5 (by rfl) ⟨446942, by rfl⟩ : syracuseStep 9534773 = 893885) B893885
theorem B2686385 : Blo 742328 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B1113521 : Blo 742328 1113521 := bstep (se 2 (by rfl) ⟨417570, by rfl⟩ : syracuseStep 1113521 = 835141) B835141
theorem B3571121 : Blo 742328 3571121 := bstep (se 2 (by rfl) ⟨1339170, by rfl⟩ : syracuseStep 3571121 = 2678341) B2678341
theorem B1113539 : Blo 742328 1113539 := bstep (se 1 (by rfl) ⟨835154, by rfl⟩ : syracuseStep 1113539 = 1670309) B1670309
theorem B1113569 : Blo 742328 1113569 := bstep (se 2 (by rfl) ⟨417588, by rfl⟩ : syracuseStep 1113569 = 835177) B835177
theorem B1113587 : Blo 742328 1113587 := bstep (se 1 (by rfl) ⟨835190, by rfl⟩ : syracuseStep 1113587 = 1670381) B1670381
theorem B1113617 : Blo 742328 1113617 := bstep (se 2 (by rfl) ⟨417606, by rfl⟩ : syracuseStep 1113617 = 835213) B835213
theorem B1113635 : Blo 742328 1113635 := bstep (se 1 (by rfl) ⟨835226, by rfl⟩ : syracuseStep 1113635 = 1670453) B1670453
theorem B1670705 : Blo 742328 1670705 := bstep (se 2 (by rfl) ⟨626514, by rfl⟩ : syracuseStep 1670705 = 1253029) B1253029
theorem B1113665 : Blo 742328 1113665 := bstep (se 2 (by rfl) ⟨417624, by rfl⟩ : syracuseStep 1113665 = 835249) B835249
theorem B1670723 : Blo 742328 1670723 := bstep (se 1 (by rfl) ⟨1253042, by rfl⟩ : syracuseStep 1670723 = 2506085) B2506085
theorem B1113683 : Blo 742328 1113683 := bstep (se 1 (by rfl) ⟨835262, by rfl⟩ : syracuseStep 1113683 = 1670525) B1670525
theorem B1113713 : Blo 742328 1113713 := bstep (se 2 (by rfl) ⟨417642, by rfl⟩ : syracuseStep 1113713 = 835285) B835285
theorem B1113731 : Blo 742328 1113731 := bstep (se 1 (by rfl) ⟨835298, by rfl⟩ : syracuseStep 1113731 = 1670597) B1670597
theorem B1113761 : Blo 742328 1113761 := bstep (se 2 (by rfl) ⟨417660, by rfl⟩ : syracuseStep 1113761 = 835321) B835321
theorem B1113779 : Blo 742328 1113779 := bstep (se 1 (by rfl) ⟨835334, by rfl⟩ : syracuseStep 1113779 = 1670669) B1670669
theorem B1113809 : Blo 742328 1113809 := bstep (se 2 (by rfl) ⟨417678, by rfl⟩ : syracuseStep 1113809 = 835357) B835357
theorem B1113827 : Blo 742328 1113827 := bstep (se 1 (by rfl) ⟨835370, by rfl⟩ : syracuseStep 1113827 = 1670741) B1670741
theorem B1113857 : Blo 742328 1113857 := bstep (se 2 (by rfl) ⟨417696, by rfl⟩ : syracuseStep 1113857 = 835393) B835393
theorem B1113875 : Blo 742328 1113875 := bstep (se 1 (by rfl) ⟨835406, by rfl⟩ : syracuseStep 1113875 = 1670813) B1670813
theorem B1113905 : Blo 742328 1113905 := bstep (se 2 (by rfl) ⟨417714, by rfl⟩ : syracuseStep 1113905 = 835429) B835429
theorem B1113923 : Blo 742328 1113923 := bstep (se 1 (by rfl) ⟨835442, by rfl⟩ : syracuseStep 1113923 = 1670885) B1670885
theorem B1670993 : Blo 742328 1670993 := bstep (se 2 (by rfl) ⟨626622, by rfl⟩ : syracuseStep 1670993 = 1253245) B1253245
theorem B1113953 : Blo 742328 1113953 := bstep (se 2 (by rfl) ⟨417732, by rfl⟩ : syracuseStep 1113953 = 835465) B835465
theorem B1671011 : Blo 742328 1671011 := bstep (se 1 (by rfl) ⟨1253258, by rfl⟩ : syracuseStep 1671011 = 2506517) B2506517
theorem B5373809 : Blo 742328 5373809 := bstep (se 2 (by rfl) ⟨2015178, by rfl⟩ : syracuseStep 5373809 = 4030357) B4030357
theorem B1113971 : Blo 742328 1113971 := bstep (se 1 (by rfl) ⟨835478, by rfl⟩ : syracuseStep 1113971 = 1670957) B1670957
theorem B1114001 : Blo 742328 1114001 := bstep (se 2 (by rfl) ⟨417750, by rfl⟩ : syracuseStep 1114001 = 835501) B835501
theorem B1114019 : Blo 742328 1114019 := bstep (se 1 (by rfl) ⟨835514, by rfl⟩ : syracuseStep 1114019 = 1671029) B1671029
theorem B1114049 : Blo 742328 1114049 := bstep (se 2 (by rfl) ⟨417768, by rfl⟩ : syracuseStep 1114049 = 835537) B835537
theorem B13565893 : Blo 742328 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B1114067 : Blo 742328 1114067 := bstep (se 1 (by rfl) ⟨835550, by rfl⟩ : syracuseStep 1114067 = 1671101) B1671101
theorem B1114097 : Blo 742328 1114097 := bstep (se 2 (by rfl) ⟨417786, by rfl⟩ : syracuseStep 1114097 = 835573) B835573
theorem B1671191 : Blo 742328 1671191 := bstep (se 1 (by rfl) ⟨1253393, by rfl⟩ : syracuseStep 1671191 = 2506787) B2506787
theorem B1114187 : Blo 742328 1114187 := bstep (se 1 (by rfl) ⟨835640, by rfl⟩ : syracuseStep 1114187 = 1671281) B1671281
theorem B5734475 : Blo 742328 5734475 := bstep (se 1 (by rfl) ⟨4300856, by rfl⟩ : syracuseStep 5734475 = 8601713) B8601713
theorem B1114199 : Blo 742328 1114199 := bstep (se 1 (by rfl) ⟨835649, by rfl⟩ : syracuseStep 1114199 = 1671299) B1671299
theorem B5079133 : Blo 742328 5079133 := bstep (se 3 (by rfl) ⟨952337, by rfl⟩ : syracuseStep 5079133 = 1904675) B1904675
theorem B1114265 : Blo 742328 1114265 := bstep (se 2 (by rfl) ⟨417849, by rfl⟩ : syracuseStep 1114265 = 835699) B835699
theorem B1671371 : Blo 742328 1671371 := bstep (se 1 (by rfl) ⟨1253528, by rfl⟩ : syracuseStep 1671371 = 2507057) B2507057
theorem B1671425 : Blo 742328 1671425 := bstep (se 2 (by rfl) ⟨626784, by rfl⟩ : syracuseStep 1671425 = 1253569) B1253569
theorem B1114379 : Blo 742328 1114379 := bstep (se 1 (by rfl) ⟨835784, by rfl⟩ : syracuseStep 1114379 = 1671569) B1671569
theorem B1114391 : Blo 742328 1114391 := bstep (se 1 (by rfl) ⟨835793, by rfl⟩ : syracuseStep 1114391 = 1671587) B1671587
theorem B1114457 : Blo 742328 1114457 := bstep (se 2 (by rfl) ⟨417921, by rfl⟩ : syracuseStep 1114457 = 835843) B835843
theorem B1114571 : Blo 742328 1114571 := bstep (se 1 (by rfl) ⟨835928, by rfl⟩ : syracuseStep 1114571 = 1671857) B1671857
theorem B1114583 : Blo 742328 1114583 := bstep (se 1 (by rfl) ⟨835937, by rfl⟩ : syracuseStep 1114583 = 1671875) B1671875
theorem B1671641 : Blo 742328 1671641 := bstep (se 2 (by rfl) ⟨626865, by rfl⟩ : syracuseStep 1671641 = 1253731) B1253731
theorem B1409537 : Blo 742328 1409537 := bstep (se 2 (by rfl) ⟨528576, by rfl⟩ : syracuseStep 1409537 = 1057153) B1057153
theorem B1114649 : Blo 742328 1114649 := bstep (se 2 (by rfl) ⟨417993, by rfl⟩ : syracuseStep 1114649 = 835987) B835987
theorem B1671731 : Blo 742328 1671731 := bstep (se 1 (by rfl) ⟨1253798, by rfl⟩ : syracuseStep 1671731 = 2507597) B2507597
theorem B2687539 : Blo 742328 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B1671767 : Blo 742328 1671767 := bstep (se 1 (by rfl) ⟨1253825, by rfl⟩ : syracuseStep 1671767 = 2507651) B2507651
theorem B1344115 : Blo 742328 1344115 := bstep (se 1 (by rfl) ⟨1008086, by rfl⟩ : syracuseStep 1344115 = 2016173) B2016173
theorem B1114763 : Blo 742328 1114763 := bstep (se 1 (by rfl) ⟨836072, by rfl⟩ : syracuseStep 1114763 = 1672145) B1672145
theorem B1114775 : Blo 742328 1114775 := bstep (se 1 (by rfl) ⟨836081, by rfl⟩ : syracuseStep 1114775 = 1672163) B1672163
theorem B2818739 : Blo 742328 2818739 := bstep (se 1 (by rfl) ⟨2114054, by rfl⟩ : syracuseStep 2818739 = 4228109) B4228109
theorem B1114841 : Blo 742328 1114841 := bstep (se 2 (by rfl) ⟨418065, by rfl⟩ : syracuseStep 1114841 = 836131) B836131
theorem B1671947 : Blo 742328 1671947 := bstep (se 1 (by rfl) ⟨1253960, by rfl⟩ : syracuseStep 1671947 = 2507921) B2507921
theorem B1672001 : Blo 742328 1672001 := bstep (se 2 (by rfl) ⟨627000, by rfl⟩ : syracuseStep 1672001 = 1254001) B1254001
theorem B1114955 : Blo 742328 1114955 := bstep (se 1 (by rfl) ⟨836216, by rfl⟩ : syracuseStep 1114955 = 1672433) B1672433
theorem B1409879 : Blo 742328 1409879 := bstep (se 1 (by rfl) ⟨1057409, by rfl⟩ : syracuseStep 1409879 = 2114819) B2114819
theorem B1114967 : Blo 742328 1114967 := bstep (se 1 (by rfl) ⟨836225, by rfl⟩ : syracuseStep 1114967 = 1672451) B1672451
theorem B1115033 : Blo 742328 1115033 := bstep (se 2 (by rfl) ⟨418137, by rfl⟩ : syracuseStep 1115033 = 836275) B836275
theorem B1115147 : Blo 742328 1115147 := bstep (se 1 (by rfl) ⟨836360, by rfl⟩ : syracuseStep 1115147 = 1672721) B1672721
theorem B1115159 : Blo 742328 1115159 := bstep (se 1 (by rfl) ⟨836369, by rfl⟩ : syracuseStep 1115159 = 1672739) B1672739
theorem B1672217 : Blo 742328 1672217 := bstep (se 2 (by rfl) ⟨627081, by rfl⟩ : syracuseStep 1672217 = 1254163) B1254163
theorem B10159139 : Blo 742328 10159139 := bstep (se 1 (by rfl) ⟨7619354, by rfl⟩ : syracuseStep 10159139 = 15238709) B15238709
theorem B1115225 : Blo 742328 1115225 := bstep (se 2 (by rfl) ⟨418209, by rfl⟩ : syracuseStep 1115225 = 836419) B836419
theorem B1672307 : Blo 742328 1672307 := bstep (se 1 (by rfl) ⟨1254230, by rfl⟩ : syracuseStep 1672307 = 2508461) B2508461
theorem B1672343 : Blo 742328 1672343 := bstep (se 1 (by rfl) ⟨1254257, by rfl⟩ : syracuseStep 1672343 = 2508515) B2508515
theorem B1115339 : Blo 742328 1115339 := bstep (se 1 (by rfl) ⟨836504, by rfl⟩ : syracuseStep 1115339 = 1673009) B1673009
theorem B1115351 : Blo 742328 1115351 := bstep (se 1 (by rfl) ⟨836513, by rfl⟩ : syracuseStep 1115351 = 1673027) B1673027
theorem B1115417 : Blo 742328 1115417 := bstep (se 2 (by rfl) ⟨418281, by rfl⟩ : syracuseStep 1115417 = 836563) B836563
theorem B2819393 : Blo 742328 2819393 := bstep (se 2 (by rfl) ⟨1057272, by rfl⟩ : syracuseStep 2819393 = 2114545) B2114545
theorem B1672523 : Blo 742328 1672523 := bstep (se 1 (by rfl) ⟨1254392, by rfl⟩ : syracuseStep 1672523 = 2508785) B2508785
theorem B1672577 : Blo 742328 1672577 := bstep (se 2 (by rfl) ⟨627216, by rfl⟩ : syracuseStep 1672577 = 1254433) B1254433
theorem B1115531 : Blo 742328 1115531 := bstep (se 1 (by rfl) ⟨836648, by rfl⟩ : syracuseStep 1115531 = 1673297) B1673297
theorem B1115543 : Blo 742328 1115543 := bstep (se 1 (by rfl) ⟨836657, by rfl⟩ : syracuseStep 1115543 = 1673315) B1673315
theorem B1115609 : Blo 742328 1115609 := bstep (se 2 (by rfl) ⟨418353, by rfl⟩ : syracuseStep 1115609 = 836707) B836707
theorem B1410547 : Blo 742328 1410547 := bstep (se 1 (by rfl) ⟨1057910, by rfl⟩ : syracuseStep 1410547 = 2115821) B2115821
theorem B3180035 : Blo 742328 3180035 := bstep (se 1 (by rfl) ⟨2385026, by rfl⟩ : syracuseStep 3180035 = 4770053) B4770053
theorem B3769901 : Blo 742328 3769901 := bstep (se 3 (by rfl) ⟨706856, by rfl⟩ : syracuseStep 3769901 = 1413713) B1413713
theorem B1115723 : Blo 742328 1115723 := bstep (se 1 (by rfl) ⟨836792, by rfl⟩ : syracuseStep 1115723 = 1673585) B1673585
theorem B1115735 : Blo 742328 1115735 := bstep (se 1 (by rfl) ⟨836801, by rfl⟩ : syracuseStep 1115735 = 1673603) B1673603
theorem B1508951 : Blo 742328 1508951 := bstep (se 1 (by rfl) ⟨1131713, by rfl⟩ : syracuseStep 1508951 = 2263427) B2263427
theorem B1672793 : Blo 742328 1672793 := bstep (se 2 (by rfl) ⟨627297, by rfl⟩ : syracuseStep 1672793 = 1254595) B1254595
theorem B919127 : Blo 742328 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B11437661 : Blo 742328 11437661 := bstep (se 3 (by rfl) ⟨2144561, by rfl⟩ : syracuseStep 11437661 = 4289123) B4289123
theorem B3016343 : Blo 742328 3016343 := bstep (se 1 (by rfl) ⟨2262257, by rfl⟩ : syracuseStep 3016343 = 4524515) B4524515
theorem B1115801 : Blo 742328 1115801 := bstep (se 2 (by rfl) ⟨418425, by rfl⟩ : syracuseStep 1115801 = 836851) B836851
theorem B1672883 : Blo 742328 1672883 := bstep (se 1 (by rfl) ⟨1254662, by rfl⟩ : syracuseStep 1672883 = 2509325) B2509325
theorem B1672919 : Blo 742328 1672919 := bstep (se 1 (by rfl) ⟨1254689, by rfl⟩ : syracuseStep 1672919 = 2509379) B2509379
theorem B1115915 : Blo 742328 1115915 := bstep (se 1 (by rfl) ⟨836936, by rfl⟩ : syracuseStep 1115915 = 1673873) B1673873
theorem B1115927 : Blo 742328 1115927 := bstep (se 1 (by rfl) ⟨836945, by rfl⟩ : syracuseStep 1115927 = 1673891) B1673891
theorem B1115993 : Blo 742328 1115993 := bstep (se 2 (by rfl) ⟨418497, by rfl⟩ : syracuseStep 1115993 = 836995) B836995
theorem B3180377 : Blo 742328 3180377 := bstep (se 2 (by rfl) ⟨1192641, by rfl⟩ : syracuseStep 3180377 = 2385283) B2385283
theorem B3016541 : Blo 742328 3016541 := bstep (se 3 (by rfl) ⟨565601, by rfl⟩ : syracuseStep 3016541 = 1131203) B1131203
theorem B9045877 : Blo 742328 9045877 := bstep (se 5 (by rfl) ⟨424025, by rfl⟩ : syracuseStep 9045877 = 848051) B848051
theorem B1673099 : Blo 742328 1673099 := bstep (se 1 (by rfl) ⟨1254824, by rfl⟩ : syracuseStep 1673099 = 2509649) B2509649
theorem B1410995 : Blo 742328 1410995 := bstep (se 1 (by rfl) ⟨1058246, by rfl⟩ : syracuseStep 1410995 = 2116493) B2116493
theorem B1673153 : Blo 742328 1673153 := bstep (se 2 (by rfl) ⟨627432, by rfl⟩ : syracuseStep 1673153 = 1254865) B1254865
theorem B1017803 : Blo 742328 1017803 := bstep (se 1 (by rfl) ⟨763352, by rfl⟩ : syracuseStep 1017803 = 1526705) B1526705
theorem B1116107 : Blo 742328 1116107 := bstep (se 1 (by rfl) ⟨837080, by rfl⟩ : syracuseStep 1116107 = 1674161) B1674161
theorem B1116119 : Blo 742328 1116119 := bstep (se 1 (by rfl) ⟨837089, by rfl⟩ : syracuseStep 1116119 = 1674179) B1674179
theorem B1411033 : Blo 742328 1411033 := bstep (se 2 (by rfl) ⟨529137, by rfl⟩ : syracuseStep 1411033 = 1058275) B1058275
theorem B1116185 : Blo 742328 1116185 := bstep (se 2 (by rfl) ⟨418569, by rfl⟩ : syracuseStep 1116185 = 837139) B837139
theorem B1116299 : Blo 742328 1116299 := bstep (se 1 (by rfl) ⟨837224, by rfl⟩ : syracuseStep 1116299 = 1674449) B1674449
theorem B1116311 : Blo 742328 1116311 := bstep (se 1 (by rfl) ⟨837233, by rfl⟩ : syracuseStep 1116311 = 1674467) B1674467
theorem B1673369 : Blo 742328 1673369 := bstep (se 2 (by rfl) ⟨627513, by rfl⟩ : syracuseStep 1673369 = 1255027) B1255027
theorem B1116377 : Blo 742328 1116377 := bstep (se 2 (by rfl) ⟨418641, by rfl⟩ : syracuseStep 1116377 = 837283) B837283
theorem B1673459 : Blo 742328 1673459 := bstep (se 1 (by rfl) ⟨1255094, by rfl⟩ : syracuseStep 1673459 = 2510189) B2510189
theorem B1673495 : Blo 742328 1673495 := bstep (se 1 (by rfl) ⟨1255121, by rfl⟩ : syracuseStep 1673495 = 2510243) B2510243
theorem B1116491 : Blo 742328 1116491 := bstep (se 1 (by rfl) ⟨837368, by rfl⟩ : syracuseStep 1116491 = 1674737) B1674737
theorem B1116503 : Blo 742328 1116503 := bstep (se 1 (by rfl) ⟨837377, by rfl⟩ : syracuseStep 1116503 = 1674755) B1674755
theorem B1411481 : Blo 742328 1411481 := bstep (se 2 (by rfl) ⟨529305, by rfl⟩ : syracuseStep 1411481 = 1058611) B1058611
theorem B1116569 : Blo 742328 1116569 := bstep (se 2 (by rfl) ⟨418713, by rfl⟩ : syracuseStep 1116569 = 837427) B837427
theorem B1673675 : Blo 742328 1673675 := bstep (se 1 (by rfl) ⟨1255256, by rfl⟩ : syracuseStep 1673675 = 2510513) B2510513
theorem B1673729 : Blo 742328 1673729 := bstep (se 2 (by rfl) ⟨627648, by rfl⟩ : syracuseStep 1673729 = 1255297) B1255297
theorem B1116683 : Blo 742328 1116683 := bstep (se 1 (by rfl) ⟨837512, by rfl⟩ : syracuseStep 1116683 = 1675025) B1675025
theorem B1116695 : Blo 742328 1116695 := bstep (se 1 (by rfl) ⟨837521, by rfl⟩ : syracuseStep 1116695 = 1675043) B1675043
theorem B2820653 : Blo 742328 2820653 := bstep (se 3 (by rfl) ⟨528872, by rfl⟩ : syracuseStep 2820653 = 1057745) B1057745
theorem B2820683 : Blo 742328 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B1116761 : Blo 742328 1116761 := bstep (se 2 (by rfl) ⟨418785, by rfl⟩ : syracuseStep 1116761 = 837571) B837571
theorem B5376689 : Blo 742328 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B1116875 : Blo 742328 1116875 := bstep (se 1 (by rfl) ⟨837656, by rfl⟩ : syracuseStep 1116875 = 1675313) B1675313
theorem B1116887 : Blo 742328 1116887 := bstep (se 1 (by rfl) ⟨837665, by rfl⟩ : syracuseStep 1116887 = 1675331) B1675331
theorem B1673945 : Blo 742328 1673945 := bstep (se 2 (by rfl) ⟨627729, by rfl⟩ : syracuseStep 1673945 = 1255459) B1255459
theorem B1116953 : Blo 742328 1116953 := bstep (se 2 (by rfl) ⟨418857, by rfl⟩ : syracuseStep 1116953 = 837715) B837715
theorem B1674035 : Blo 742328 1674035 := bstep (se 1 (by rfl) ⟨1255526, by rfl⟩ : syracuseStep 1674035 = 2511053) B2511053
theorem B1674071 : Blo 742328 1674071 := bstep (se 1 (by rfl) ⟨1255553, by rfl⟩ : syracuseStep 1674071 = 2511107) B2511107
theorem B1117067 : Blo 742328 1117067 := bstep (se 1 (by rfl) ⟨837800, by rfl⟩ : syracuseStep 1117067 = 1675601) B1675601
theorem B1117079 : Blo 742328 1117079 := bstep (se 1 (by rfl) ⟨837809, by rfl⟩ : syracuseStep 1117079 = 1675619) B1675619
theorem B1117145 : Blo 742328 1117145 := bstep (se 2 (by rfl) ⟨418929, by rfl⟩ : syracuseStep 1117145 = 837859) B837859
theorem B1674251 : Blo 742328 1674251 := bstep (se 1 (by rfl) ⟨1255688, by rfl⟩ : syracuseStep 1674251 = 2511377) B2511377
theorem B3574849 : Blo 742328 3574849 := bstep (se 2 (by rfl) ⟨1340568, by rfl⟩ : syracuseStep 3574849 = 2681137) B2681137
theorem B1674305 : Blo 742328 1674305 := bstep (se 2 (by rfl) ⟨627864, by rfl⟩ : syracuseStep 1674305 = 1255729) B1255729
theorem B1117259 : Blo 742328 1117259 := bstep (se 1 (by rfl) ⟨837944, by rfl⟩ : syracuseStep 1117259 = 1675889) B1675889
theorem B1117271 : Blo 742328 1117271 := bstep (se 1 (by rfl) ⟨837953, by rfl⟩ : syracuseStep 1117271 = 1675907) B1675907
theorem B1412225 : Blo 742328 1412225 := bstep (se 2 (by rfl) ⟨529584, by rfl⟩ : syracuseStep 1412225 = 1059169) B1059169
theorem B1117337 : Blo 742328 1117337 := bstep (se 2 (by rfl) ⟨419001, by rfl⟩ : syracuseStep 1117337 = 838003) B838003
theorem B2821337 : Blo 742328 2821337 := bstep (se 2 (by rfl) ⟨1058001, by rfl⟩ : syracuseStep 2821337 = 2116003) B2116003
theorem B1117451 : Blo 742328 1117451 := bstep (se 1 (by rfl) ⟨838088, by rfl⟩ : syracuseStep 1117451 = 1676177) B1676177
theorem B1117463 : Blo 742328 1117463 := bstep (se 1 (by rfl) ⟨838097, by rfl⟩ : syracuseStep 1117463 = 1676195) B1676195
theorem B1674521 : Blo 742328 1674521 := bstep (se 2 (by rfl) ⟨627945, by rfl⟩ : syracuseStep 1674521 = 1255891) B1255891
theorem B1117529 : Blo 742328 1117529 := bstep (se 2 (by rfl) ⟨419073, by rfl⟩ : syracuseStep 1117529 = 838147) B838147
theorem B1674611 : Blo 742328 1674611 := bstep (se 1 (by rfl) ⟨1255958, by rfl⟩ : syracuseStep 1674611 = 2511917) B2511917
theorem B1412491 : Blo 742328 1412491 := bstep (se 1 (by rfl) ⟨1059368, by rfl⟩ : syracuseStep 1412491 = 2118737) B2118737
theorem B1674647 : Blo 742328 1674647 := bstep (se 1 (by rfl) ⟨1255985, by rfl⟩ : syracuseStep 1674647 = 2511971) B2511971
theorem B3182017 : Blo 742328 3182017 := bstep (se 2 (by rfl) ⟨1193256, by rfl⟩ : syracuseStep 3182017 = 2386513) B2386513
theorem B1117643 : Blo 742328 1117643 := bstep (se 1 (by rfl) ⟨838232, by rfl⟩ : syracuseStep 1117643 = 1676465) B1676465
theorem B1117655 : Blo 742328 1117655 := bstep (se 1 (by rfl) ⟨838241, by rfl⟩ : syracuseStep 1117655 = 1676483) B1676483
theorem B5443033 : Blo 742328 5443033 := bstep (se 2 (by rfl) ⟨2041137, by rfl⟩ : syracuseStep 5443033 = 4082275) B4082275
theorem B2821655 : Blo 742328 2821655 := bstep (se 1 (by rfl) ⟨2116241, by rfl⟩ : syracuseStep 2821655 = 4232483) B4232483
theorem B1117721 : Blo 742328 1117721 := bstep (se 2 (by rfl) ⟨419145, by rfl⟩ : syracuseStep 1117721 = 838291) B838291
theorem B1674827 : Blo 742328 1674827 := bstep (se 1 (by rfl) ⟨1256120, by rfl⟩ : syracuseStep 1674827 = 2512241) B2512241
theorem B1674881 : Blo 742328 1674881 := bstep (se 2 (by rfl) ⟨628080, by rfl⟩ : syracuseStep 1674881 = 1256161) B1256161
theorem B1117835 : Blo 742328 1117835 := bstep (se 1 (by rfl) ⟨838376, by rfl⟩ : syracuseStep 1117835 = 1676753) B1676753
theorem B1117847 : Blo 742328 1117847 := bstep (se 1 (by rfl) ⟨838385, by rfl⟩ : syracuseStep 1117847 = 1676771) B1676771
theorem B2723507 : Blo 742328 2723507 := bstep (se 1 (by rfl) ⟨2042630, by rfl⟩ : syracuseStep 2723507 = 4085261) B4085261
theorem B1117913 : Blo 742328 1117913 := bstep (se 2 (by rfl) ⟨419217, by rfl⟩ : syracuseStep 1117913 = 838435) B838435
theorem B1412939 : Blo 742328 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B1118027 : Blo 742328 1118027 := bstep (se 1 (by rfl) ⟨838520, by rfl⟩ : syracuseStep 1118027 = 1677041) B1677041
theorem B1118039 : Blo 742328 1118039 := bstep (se 1 (by rfl) ⟨838529, by rfl⟩ : syracuseStep 1118039 = 1677059) B1677059
theorem B1675097 : Blo 742328 1675097 := bstep (se 2 (by rfl) ⟨628161, by rfl⟩ : syracuseStep 1675097 = 1256323) B1256323
theorem B5640029 : Blo 742328 5640029 := bstep (se 3 (by rfl) ⟨1057505, by rfl⟩ : syracuseStep 5640029 = 2115011) B2115011
theorem B1118105 : Blo 742328 1118105 := bstep (se 2 (by rfl) ⟨419289, by rfl⟩ : syracuseStep 1118105 = 838579) B838579
theorem B1675187 : Blo 742328 1675187 := bstep (se 1 (by rfl) ⟨1256390, by rfl⟩ : syracuseStep 1675187 = 2512781) B2512781
theorem B1675223 : Blo 742328 1675223 := bstep (se 1 (by rfl) ⟨1256417, by rfl⟩ : syracuseStep 1675223 = 2512835) B2512835
theorem B1413121 : Blo 742328 1413121 := bstep (se 2 (by rfl) ⟨529920, by rfl⟩ : syracuseStep 1413121 = 1059841) B1059841
theorem B1118219 : Blo 742328 1118219 := bstep (se 1 (by rfl) ⟨838664, by rfl⟩ : syracuseStep 1118219 = 1677329) B1677329
theorem B1118231 : Blo 742328 1118231 := bstep (se 1 (by rfl) ⟨838673, by rfl⟩ : syracuseStep 1118231 = 1677347) B1677347
theorem B6361163 : Blo 742328 6361163 := bstep (se 1 (by rfl) ⟨4770872, by rfl⟩ : syracuseStep 6361163 = 9541745) B9541745
theorem B1118297 : Blo 742328 1118297 := bstep (se 2 (by rfl) ⟨419361, by rfl⟩ : syracuseStep 1118297 = 838723) B838723
theorem B1675403 : Blo 742328 1675403 := bstep (se 1 (by rfl) ⟨1256552, by rfl⟩ : syracuseStep 1675403 = 2513105) B2513105
theorem B13570199 : Blo 742328 13570199 := bstep (se 1 (by rfl) ⟨10177649, by rfl⟩ : syracuseStep 13570199 = 20355299) B20355299
theorem B2822323 : Blo 742328 2822323 := bstep (se 1 (by rfl) ⟨2116742, by rfl⟩ : syracuseStep 2822323 = 4233485) B4233485
theorem B1675457 : Blo 742328 1675457 := bstep (se 2 (by rfl) ⟨628296, by rfl⟩ : syracuseStep 1675457 = 1256593) B1256593
theorem B1118411 : Blo 742328 1118411 := bstep (se 1 (by rfl) ⟨838808, by rfl⟩ : syracuseStep 1118411 = 1677617) B1677617
theorem B1511627 : Blo 742328 1511627 := bstep (se 1 (by rfl) ⟨1133720, by rfl⟩ : syracuseStep 1511627 = 2267441) B2267441
theorem B1118423 : Blo 742328 1118423 := bstep (se 1 (by rfl) ⟨838817, by rfl⟩ : syracuseStep 1118423 = 1677635) B1677635
theorem B1118489 : Blo 742328 1118489 := bstep (se 2 (by rfl) ⟨419433, by rfl⟩ : syracuseStep 1118489 = 838867) B838867
theorem B1413463 : Blo 742328 1413463 := bstep (se 1 (by rfl) ⟨1060097, by rfl⟩ : syracuseStep 1413463 = 2120195) B2120195
theorem B1118603 : Blo 742328 1118603 := bstep (se 1 (by rfl) ⟨838952, by rfl⟩ : syracuseStep 1118603 = 1677905) B1677905
theorem B1118615 : Blo 742328 1118615 := bstep (se 1 (by rfl) ⟨838961, by rfl⟩ : syracuseStep 1118615 = 1677923) B1677923
theorem B1675673 : Blo 742328 1675673 := bstep (se 2 (by rfl) ⟨628377, by rfl⟩ : syracuseStep 1675673 = 1256755) B1256755
theorem B1118681 : Blo 742328 1118681 := bstep (se 2 (by rfl) ⟨419505, by rfl⟩ : syracuseStep 1118681 = 839011) B839011
theorem B1675763 : Blo 742328 1675763 := bstep (se 1 (by rfl) ⟨1256822, by rfl⟩ : syracuseStep 1675763 = 2513645) B2513645
theorem B1675799 : Blo 742328 1675799 := bstep (se 1 (by rfl) ⟨1256849, by rfl⟩ : syracuseStep 1675799 = 2513699) B2513699
theorem B1413683 : Blo 742328 1413683 := bstep (se 1 (by rfl) ⟨1060262, by rfl⟩ : syracuseStep 1413683 = 2120525) B2120525
theorem B1118795 : Blo 742328 1118795 := bstep (se 1 (by rfl) ⟨839096, by rfl⟩ : syracuseStep 1118795 = 1678193) B1678193
theorem B1118807 : Blo 742328 1118807 := bstep (se 1 (by rfl) ⟨839105, by rfl⟩ : syracuseStep 1118807 = 1678211) B1678211
theorem B1118873 : Blo 742328 1118873 := bstep (se 2 (by rfl) ⟨419577, by rfl⟩ : syracuseStep 1118873 = 839155) B839155
theorem B1675979 : Blo 742328 1675979 := bstep (se 1 (by rfl) ⟨1256984, by rfl⟩ : syracuseStep 1675979 = 2513969) B2513969
theorem B1676033 : Blo 742328 1676033 := bstep (se 2 (by rfl) ⟨628512, by rfl⟩ : syracuseStep 1676033 = 1257025) B1257025
theorem B1118987 : Blo 742328 1118987 := bstep (se 1 (by rfl) ⟨839240, by rfl⟩ : syracuseStep 1118987 = 1678481) B1678481
theorem B1413911 : Blo 742328 1413911 := bstep (se 1 (by rfl) ⟨1060433, by rfl⟩ : syracuseStep 1413911 = 2120867) B2120867
theorem B1118999 : Blo 742328 1118999 := bstep (se 1 (by rfl) ⟨839249, by rfl⟩ : syracuseStep 1118999 = 1678499) B1678499
theorem B5378881 : Blo 742328 5378881 := bstep (se 2 (by rfl) ⟨2017080, by rfl⟩ : syracuseStep 5378881 = 4034161) B4034161
theorem B1119065 : Blo 742328 1119065 := bstep (se 2 (by rfl) ⟨419649, by rfl⟩ : syracuseStep 1119065 = 839299) B839299
theorem B5378995 : Blo 742328 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B1119179 : Blo 742328 1119179 := bstep (se 1 (by rfl) ⟨839384, by rfl⟩ : syracuseStep 1119179 = 1678769) B1678769
theorem B1119191 : Blo 742328 1119191 := bstep (se 1 (by rfl) ⟨839393, by rfl⟩ : syracuseStep 1119191 = 1678787) B1678787
theorem B1676249 : Blo 742328 1676249 := bstep (se 2 (by rfl) ⟨628593, by rfl⟩ : syracuseStep 1676249 = 1257187) B1257187
theorem B4232209 : Blo 742328 4232209 := bstep (se 2 (by rfl) ⟨1587078, by rfl⟩ : syracuseStep 4232209 = 3174157) B3174157
theorem B1414169 : Blo 742328 1414169 := bstep (se 2 (by rfl) ⟨530313, by rfl⟩ : syracuseStep 1414169 = 1060627) B1060627
theorem B1119257 : Blo 742328 1119257 := bstep (se 2 (by rfl) ⟨419721, by rfl⟩ : syracuseStep 1119257 = 839443) B839443
theorem B1676339 : Blo 742328 1676339 := bstep (se 1 (by rfl) ⟨1257254, by rfl⟩ : syracuseStep 1676339 = 2514509) B2514509
theorem B1676375 : Blo 742328 1676375 := bstep (se 1 (by rfl) ⟨1257281, by rfl⟩ : syracuseStep 1676375 = 2514563) B2514563
theorem B1119371 : Blo 742328 1119371 := bstep (se 1 (by rfl) ⟨839528, by rfl⟩ : syracuseStep 1119371 = 1679057) B1679057
theorem B1119383 : Blo 742328 1119383 := bstep (se 1 (by rfl) ⟨839537, by rfl⟩ : syracuseStep 1119383 = 1679075) B1679075
theorem B1512641 : Blo 742328 1512641 := bstep (se 2 (by rfl) ⟨567240, by rfl⟩ : syracuseStep 1512641 = 1134481) B1134481
theorem B1119449 : Blo 742328 1119449 := bstep (se 2 (by rfl) ⟨419793, by rfl⟩ : syracuseStep 1119449 = 839587) B839587
theorem B1676555 : Blo 742328 1676555 := bstep (se 1 (by rfl) ⟨1257416, by rfl⟩ : syracuseStep 1676555 = 2514833) B2514833
theorem B1676609 : Blo 742328 1676609 := bstep (se 2 (by rfl) ⟨628728, by rfl⟩ : syracuseStep 1676609 = 1257457) B1257457
theorem B6034763 : Blo 742328 6034763 := bstep (se 1 (by rfl) ⟨4526072, by rfl⟩ : syracuseStep 6034763 = 9052145) B9052145
theorem B3020107 : Blo 742328 3020107 := bstep (se 1 (by rfl) ⟨2265080, by rfl⟩ : syracuseStep 3020107 = 4530161) B4530161
theorem B3773789 : Blo 742328 3773789 := bstep (se 3 (by rfl) ⟨707585, by rfl⟩ : syracuseStep 3773789 = 1415171) B1415171
theorem B2823569 : Blo 742328 2823569 := bstep (se 2 (by rfl) ⟨1058838, by rfl⟩ : syracuseStep 2823569 = 2117677) B2117677
theorem B1414579 : Blo 742328 1414579 := bstep (se 1 (by rfl) ⟨1060934, by rfl⟩ : syracuseStep 1414579 = 2121869) B2121869
theorem B1676825 : Blo 742328 1676825 := bstep (se 2 (by rfl) ⟨628809, by rfl⟩ : syracuseStep 1676825 = 1257619) B1257619
theorem B1676915 : Blo 742328 1676915 := bstep (se 1 (by rfl) ⟨1257686, by rfl⟩ : syracuseStep 1676915 = 2515373) B2515373
theorem B1676951 : Blo 742328 1676951 := bstep (se 1 (by rfl) ⟨1257713, by rfl⟩ : syracuseStep 1676951 = 2515427) B2515427
theorem B1677131 : Blo 742328 1677131 := bstep (se 1 (by rfl) ⟨1257848, by rfl⟩ : syracuseStep 1677131 = 2515697) B2515697
theorem B1677185 : Blo 742328 1677185 := bstep (se 2 (by rfl) ⟨628944, by rfl⟩ : syracuseStep 1677185 = 1257889) B1257889
theorem B1415065 : Blo 742328 1415065 := bstep (se 2 (by rfl) ⟨530649, by rfl⟩ : syracuseStep 1415065 = 1061299) B1061299
theorem B2824267 : Blo 742328 2824267 := bstep (se 1 (by rfl) ⟨2118200, by rfl⟩ : syracuseStep 2824267 = 4236401) B4236401
theorem B1677401 : Blo 742328 1677401 := bstep (se 2 (by rfl) ⟨629025, by rfl⟩ : syracuseStep 1677401 = 1258051) B1258051
theorem B1677491 : Blo 742328 1677491 := bstep (se 1 (by rfl) ⟨1258118, by rfl⟩ : syracuseStep 1677491 = 2516237) B2516237
theorem B1677527 : Blo 742328 1677527 := bstep (se 1 (by rfl) ⟨1258145, by rfl⟩ : syracuseStep 1677527 = 2516291) B2516291
theorem B3021131 : Blo 742328 3021131 := bstep (se 1 (by rfl) ⟨2265848, by rfl⟩ : syracuseStep 3021131 = 4531697) B4531697
theorem B2824541 : Blo 742328 2824541 := bstep (se 3 (by rfl) ⟨529601, by rfl⟩ : syracuseStep 2824541 = 1059203) B1059203
theorem B4299101 : Blo 742328 4299101 := bstep (se 3 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 4299101 = 1612163) B1612163
theorem B1677707 : Blo 742328 1677707 := bstep (se 1 (by rfl) ⟨1258280, by rfl⟩ : syracuseStep 1677707 = 2516561) B2516561
theorem B1677761 : Blo 742328 1677761 := bstep (se 2 (by rfl) ⟨629160, by rfl⟩ : syracuseStep 1677761 = 1258321) B1258321
theorem B1415627 : Blo 742328 1415627 := bstep (se 1 (by rfl) ⟨1061720, by rfl⟩ : syracuseStep 1415627 = 2123441) B2123441
theorem B1415809 : Blo 742328 1415809 := bstep (se 2 (by rfl) ⟨530928, by rfl⟩ : syracuseStep 1415809 = 1061857) B1061857
theorem B1677977 : Blo 742328 1677977 := bstep (se 2 (by rfl) ⟨629241, by rfl⟩ : syracuseStep 1677977 = 1258483) B1258483
theorem B1678067 : Blo 742328 1678067 := bstep (se 1 (by rfl) ⟨1258550, by rfl⟩ : syracuseStep 1678067 = 2517101) B2517101
theorem B1678103 : Blo 742328 1678103 := bstep (se 1 (by rfl) ⟨1258577, by rfl⟩ : syracuseStep 1678103 = 2517155) B2517155
theorem B4758365 : Blo 742328 4758365 := bstep (se 3 (by rfl) ⟨892193, by rfl⟩ : syracuseStep 4758365 = 1784387) B1784387
theorem B1678283 : Blo 742328 1678283 := bstep (se 1 (by rfl) ⟨1258712, by rfl⟩ : syracuseStep 1678283 = 2517425) B2517425
theorem B1678337 : Blo 742328 1678337 := bstep (se 2 (by rfl) ⟨629376, by rfl⟩ : syracuseStep 1678337 = 1258753) B1258753
theorem B2825239 : Blo 742328 2825239 := bstep (se 1 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 2825239 = 4237859) B4237859
theorem B1088587 : Blo 742328 1088587 := bstep (se 1 (by rfl) ⟨816440, by rfl⟩ : syracuseStep 1088587 = 1632881) B1632881
theorem B1678553 : Blo 742328 1678553 := bstep (se 2 (by rfl) ⟨629457, by rfl⟩ : syracuseStep 1678553 = 1258915) B1258915
theorem B793847 : Blo 742328 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B1678643 : Blo 742328 1678643 := bstep (se 1 (by rfl) ⟨1258982, by rfl⟩ : syracuseStep 1678643 = 2517965) B2517965
theorem B4529483 : Blo 742328 4529483 := bstep (se 1 (by rfl) ⟨3397112, by rfl⟩ : syracuseStep 4529483 = 6794225) B6794225
theorem B1416523 : Blo 742328 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1678679 : Blo 742328 1678679 := bstep (se 1 (by rfl) ⟨1259009, by rfl⟩ : syracuseStep 1678679 = 2518019) B2518019
theorem B1252759 : Blo 742328 1252759 := bstep (se 1 (by rfl) ⟨939569, by rfl⟩ : syracuseStep 1252759 = 1879139) B1879139
theorem B3775895 : Blo 742328 3775895 := bstep (se 1 (by rfl) ⟨2831921, by rfl⟩ : syracuseStep 3775895 = 5663843) B5663843
theorem B1416599 : Blo 742328 1416599 := bstep (se 1 (by rfl) ⟨1062449, by rfl⟩ : syracuseStep 1416599 = 2124899) B2124899
theorem B1678859 : Blo 742328 1678859 := bstep (se 1 (by rfl) ⟨1259144, by rfl⟩ : syracuseStep 1678859 = 2518289) B2518289
theorem B1908289 : Blo 742328 1908289 := bstep (se 2 (by rfl) ⟨715608, by rfl⟩ : syracuseStep 1908289 = 1431217) B1431217
theorem B1678913 : Blo 742328 1678913 := bstep (se 2 (by rfl) ⟨629592, by rfl⟩ : syracuseStep 1678913 = 1259185) B1259185
theorem B2268875 : Blo 742328 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B1679129 : Blo 742328 1679129 := bstep (se 2 (by rfl) ⟨629673, by rfl⟩ : syracuseStep 1679129 = 1259347) B1259347
theorem B2826029 : Blo 742328 2826029 := bstep (se 3 (by rfl) ⟨529880, by rfl⟩ : syracuseStep 2826029 = 1059761) B1059761
theorem B1679219 : Blo 742328 1679219 := bstep (se 1 (by rfl) ⟨1259414, by rfl⟩ : syracuseStep 1679219 = 2518829) B2518829
theorem B794539 : Blo 742328 794539 := bstep (se 1 (by rfl) ⟨595904, by rfl⟩ : syracuseStep 794539 = 1191809) B1191809
theorem B2072537 : Blo 742328 2072537 := bstep (se 2 (by rfl) ⟨777201, by rfl⟩ : syracuseStep 2072537 = 1554403) B1554403
theorem B1253387 : Blo 742328 1253387 := bstep (se 1 (by rfl) ⟨940040, by rfl⟩ : syracuseStep 1253387 = 1880081) B1880081
theorem B1253515 : Blo 742328 1253515 := bstep (se 1 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 1253515 = 1880273) B1880273
theorem B1253657 : Blo 742328 1253657 := bstep (se 2 (by rfl) ⟨470121, by rfl⟩ : syracuseStep 1253657 = 940243) B940243
theorem B18129197 : Blo 742328 18129197 := bstep (se 3 (by rfl) ⟨3399224, by rfl⟩ : syracuseStep 18129197 = 6798449) B6798449
theorem B3449153 : Blo 742328 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B4235651 : Blo 742328 4235651 := bstep (se 1 (by rfl) ⟨3176738, by rfl⟩ : syracuseStep 4235651 = 6353477) B6353477
theorem B1253785 : Blo 742328 1253785 := bstep (se 2 (by rfl) ⟨470169, by rfl⟩ : syracuseStep 1253785 = 940339) B940339
theorem B10723853 : Blo 742328 10723853 := bstep (se 3 (by rfl) ⟨2010722, by rfl⟩ : syracuseStep 10723853 = 4021445) B4021445
theorem B1057369 : Blo 742328 1057369 := bstep (se 2 (by rfl) ⟨396513, by rfl⟩ : syracuseStep 1057369 = 793027) B793027
theorem B1057483 : Blo 742328 1057483 := bstep (se 1 (by rfl) ⟨793112, by rfl⟩ : syracuseStep 1057483 = 1586225) B1586225
theorem B795415 : Blo 742328 795415 := bstep (se 1 (by rfl) ⟨596561, by rfl⟩ : syracuseStep 795415 = 1193123) B1193123
theorem B1254359 : Blo 742328 1254359 := bstep (se 1 (by rfl) ⟨940769, by rfl⟩ : syracuseStep 1254359 = 1881539) B1881539
theorem B1254487 : Blo 742328 1254487 := bstep (se 1 (by rfl) ⟨940865, by rfl⟩ : syracuseStep 1254487 = 1881731) B1881731
theorem B2827457 : Blo 742328 2827457 := bstep (se 2 (by rfl) ⟨1060296, by rfl⟩ : syracuseStep 2827457 = 2120593) B2120593
theorem B795863 : Blo 742328 795863 := bstep (se 1 (by rfl) ⟨596897, by rfl⟩ : syracuseStep 795863 = 1193795) B1193795
theorem B1189259 : Blo 742328 1189259 := bstep (se 1 (by rfl) ⟨891944, by rfl⟩ : syracuseStep 1189259 = 1783889) B1783889
theorem B1615385 : Blo 742328 1615385 := bstep (se 2 (by rfl) ⟨605769, by rfl⟩ : syracuseStep 1615385 = 1211539) B1211539
theorem B1189451 : Blo 742328 1189451 := bstep (se 1 (by rfl) ⟨892088, by rfl⟩ : syracuseStep 1189451 = 1784177) B1784177
theorem B796235 : Blo 742328 796235 := bstep (se 1 (by rfl) ⟨597176, by rfl⟩ : syracuseStep 796235 = 1194353) B1194353
theorem B1255115 : Blo 742328 1255115 := bstep (se 1 (by rfl) ⟨941336, by rfl⟩ : syracuseStep 1255115 = 1882673) B1882673
theorem B894731 : Blo 742328 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B1255243 : Blo 742328 1255243 := bstep (se 1 (by rfl) ⟨941432, by rfl⟩ : syracuseStep 1255243 = 1882865) B1882865
theorem B1255385 : Blo 742328 1255385 := bstep (se 2 (by rfl) ⟨470769, by rfl⟩ : syracuseStep 1255385 = 941539) B941539
theorem B1058827 : Blo 742328 1058827 := bstep (se 1 (by rfl) ⟨794120, by rfl⟩ : syracuseStep 1058827 = 1588241) B1588241
theorem B14526533 : Blo 742328 14526533 := bstep (se 4 (by rfl) ⟨1361862, by rfl⟩ : syracuseStep 14526533 = 2723725) B2723725
theorem B1255513 : Blo 742328 1255513 := bstep (se 2 (by rfl) ⟨470817, by rfl⟩ : syracuseStep 1255513 = 941635) B941635
theorem B1059095 : Blo 742328 1059095 := bstep (se 1 (by rfl) ⟨794321, by rfl⟩ : syracuseStep 1059095 = 1588643) B1588643
theorem B3582539 : Blo 742328 3582539 := bstep (se 1 (by rfl) ⟨2686904, by rfl⟩ : syracuseStep 3582539 = 5373809) B5373809
theorem B4532867 : Blo 742328 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B2828945 : Blo 742328 2828945 := bstep (se 2 (by rfl) ⟨1060854, by rfl⟩ : syracuseStep 2828945 = 2121709) B2121709
theorem B1256087 : Blo 742328 1256087 := bstep (se 1 (by rfl) ⟨942065, by rfl⟩ : syracuseStep 1256087 = 1884131) B1884131
theorem B4238041 : Blo 742328 4238041 := bstep (se 2 (by rfl) ⟨1589265, by rfl⟩ : syracuseStep 4238041 = 3178531) B3178531
theorem B1256215 : Blo 742328 1256215 := bstep (se 1 (by rfl) ⟨942161, by rfl⟩ : syracuseStep 1256215 = 1884323) B1884323
theorem B3222317 : Blo 742328 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B1190873 : Blo 742328 1190873 := bstep (se 2 (by rfl) ⟨446577, by rfl⟩ : syracuseStep 1190873 = 893155) B893155
theorem B2829401 : Blo 742328 2829401 := bstep (se 2 (by rfl) ⟨1061025, by rfl⟩ : syracuseStep 2829401 = 2122051) B2122051
theorem B1060057 : Blo 742328 1060057 := bstep (se 2 (by rfl) ⟨397521, by rfl⟩ : syracuseStep 1060057 = 795043) B795043
theorem B2829613 : Blo 742328 2829613 := bstep (se 3 (by rfl) ⟨530552, by rfl⟩ : syracuseStep 2829613 = 1061105) B1061105
theorem B1256843 : Blo 742328 1256843 := bstep (se 1 (by rfl) ⟨942632, by rfl⟩ : syracuseStep 1256843 = 1885265) B1885265
theorem B1256971 : Blo 742328 1256971 := bstep (se 1 (by rfl) ⟨942728, by rfl⟩ : syracuseStep 1256971 = 1885457) B1885457
theorem B24161885 : Blo 742328 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B2829917 : Blo 742328 2829917 := bstep (se 3 (by rfl) ⟨530609, by rfl⟩ : syracuseStep 2829917 = 1061219) B1061219
theorem B4238999 : Blo 742328 4238999 := bstep (se 1 (by rfl) ⟨3179249, by rfl⟩ : syracuseStep 4238999 = 6358499) B6358499
theorem B1257113 : Blo 742328 1257113 := bstep (se 2 (by rfl) ⟨471417, by rfl⟩ : syracuseStep 1257113 = 942835) B942835
theorem B1257241 : Blo 742328 1257241 := bstep (se 2 (by rfl) ⟨471465, by rfl⟩ : syracuseStep 1257241 = 942931) B942931
theorem B12693347 : Blo 742328 12693347 := bstep (se 1 (by rfl) ⟨9520010, by rfl⟩ : syracuseStep 12693347 = 19040021) B19040021
theorem B1880243 : Blo 742328 1880243 := bstep (se 1 (by rfl) ⟨1410182, by rfl⟩ : syracuseStep 1880243 = 2820365) B2820365
theorem B1257815 : Blo 742328 1257815 := bstep (se 1 (by rfl) ⟨943361, by rfl⟩ : syracuseStep 1257815 = 1886723) B1886723
theorem B4764005 : Blo 742328 4764005 := bstep (se 4 (by rfl) ⟨446625, by rfl⟩ : syracuseStep 4764005 = 893251) B893251
theorem B6369637 : Blo 742328 6369637 := bstep (se 4 (by rfl) ⟨597153, by rfl⟩ : syracuseStep 6369637 = 1194307) B1194307
theorem B1257943 : Blo 742328 1257943 := bstep (se 1 (by rfl) ⟨943457, by rfl⟩ : syracuseStep 1257943 = 1886915) B1886915
theorem B1061515 : Blo 742328 1061515 := bstep (se 1 (by rfl) ⟨796136, by rfl⟩ : syracuseStep 1061515 = 1592273) B1592273
theorem B1061527 : Blo 742328 1061527 := bstep (se 1 (by rfl) ⟨796145, by rfl⟩ : syracuseStep 1061527 = 1592291) B1592291
theorem B6042289 : Blo 742328 6042289 := bstep (se 2 (by rfl) ⟨2265858, by rfl⟩ : syracuseStep 6042289 = 4531717) B4531717
theorem B1880779 : Blo 742328 1880779 := bstep (se 1 (by rfl) ⟨1410584, by rfl⟩ : syracuseStep 1880779 = 2821169) B2821169
theorem B2143027 : Blo 742328 2143027 := bstep (se 1 (by rfl) ⟨1607270, by rfl⟩ : syracuseStep 2143027 = 3214541) B3214541
theorem B1585985 : Blo 742328 1585985 := bstep (se 2 (by rfl) ⟨594744, by rfl⟩ : syracuseStep 1585985 = 1189489) B1189489
theorem B1880921 : Blo 742328 1880921 := bstep (se 2 (by rfl) ⟨705345, by rfl⟩ : syracuseStep 1880921 = 1410691) B1410691
theorem B1586071 : Blo 742328 1586071 := bstep (se 1 (by rfl) ⟨1189553, by rfl⟩ : syracuseStep 1586071 = 2379107) B2379107
theorem B2864065 : Blo 742328 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B2012107 : Blo 742328 2012107 := bstep (se 1 (by rfl) ⟨1509080, by rfl⟩ : syracuseStep 2012107 = 3018161) B3018161
theorem B1258571 : Blo 742328 1258571 := bstep (se 1 (by rfl) ⟨943928, by rfl⟩ : syracuseStep 1258571 = 1887857) B1887857
theorem B1258699 : Blo 742328 1258699 := bstep (se 1 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 1258699 = 1888049) B1888049
theorem B6370595 : Blo 742328 6370595 := bstep (se 1 (by rfl) ⟨4777946, by rfl⟩ : syracuseStep 6370595 = 9555893) B9555893
theorem B1258841 : Blo 742328 1258841 := bstep (se 2 (by rfl) ⟨472065, by rfl⟩ : syracuseStep 1258841 = 944131) B944131
theorem B1258969 : Blo 742328 1258969 := bstep (se 2 (by rfl) ⟨472113, by rfl⟩ : syracuseStep 1258969 = 944227) B944227
theorem B1881751 : Blo 742328 1881751 := bstep (se 1 (by rfl) ⟨1411313, by rfl⟩ : syracuseStep 1881751 = 2822627) B2822627
theorem B1586891 : Blo 742328 1586891 := bstep (se 1 (by rfl) ⟨1190168, by rfl⟩ : syracuseStep 1586891 = 2380337) B2380337
theorem B1193687 : Blo 742328 1193687 := bstep (se 1 (by rfl) ⟨895265, by rfl⟩ : syracuseStep 1193687 = 1790531) B1790531
theorem B10860293 : Blo 742328 10860293 := bstep (se 4 (by rfl) ⟨1018152, by rfl⟩ : syracuseStep 10860293 = 2036305) B2036305
theorem B1882187 : Blo 742328 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B4241483 : Blo 742328 4241483 := bstep (se 1 (by rfl) ⟨3181112, by rfl⟩ : syracuseStep 4241483 = 6362225) B6362225
theorem B9549899 : Blo 742328 9549899 := bstep (se 1 (by rfl) ⟨7162424, by rfl⟩ : syracuseStep 9549899 = 14324849) B14324849
theorem B2832515 : Blo 742328 2832515 := bstep (se 1 (by rfl) ⟨2124386, by rfl⟩ : syracuseStep 2832515 = 4248773) B4248773
theorem B2832529 : Blo 742328 2832529 := bstep (se 2 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 2832529 = 2124397) B2124397
theorem B1882561 : Blo 742328 1882561 := bstep (se 2 (by rfl) ⟨705960, by rfl⟩ : syracuseStep 1882561 = 1411921) B1411921
theorem B2832833 : Blo 742328 2832833 := bstep (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) B2124625
theorem B7158233 : Blo 742328 7158233 := bstep (se 2 (by rfl) ⟨2684337, by rfl⟩ : syracuseStep 7158233 = 5368675) B5368675
theorem B1587865 : Blo 742328 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B2505437 : Blo 742328 2505437 := bstep (se 3 (by rfl) ⟨469769, by rfl⟩ : syracuseStep 2505437 = 939539) B939539
theorem B1194763 : Blo 742328 1194763 := bstep (se 1 (by rfl) ⟨896072, by rfl⟩ : syracuseStep 1194763 = 1792145) B1792145
theorem B8469521 : Blo 742328 8469521 := bstep (se 2 (by rfl) ⟨3176070, by rfl⟩ : syracuseStep 8469521 = 6352141) B6352141
theorem B1883159 : Blo 742328 1883159 := bstep (se 1 (by rfl) ⟨1412369, by rfl⟩ : syracuseStep 1883159 = 2824739) B2824739
theorem B2833501 : Blo 742328 2833501 := bstep (se 3 (by rfl) ⟨531281, by rfl⟩ : syracuseStep 2833501 = 1062563) B1062563
theorem B3391051 : Blo 742328 3391051 := bstep (se 1 (by rfl) ⟨2543288, by rfl⟩ : syracuseStep 3391051 = 5086577) B5086577
theorem B835159 : Blo 742328 835159 := bstep (se 1 (by rfl) ⟨626369, by rfl⟩ : syracuseStep 835159 = 1252739) B1252739
theorem B835339 : Blo 742328 835339 := bstep (se 1 (by rfl) ⟨626504, by rfl⟩ : syracuseStep 835339 = 1253009) B1253009
theorem B1883969 : Blo 742328 1883969 := bstep (se 2 (by rfl) ⟨706488, by rfl⟩ : syracuseStep 1883969 = 1412977) B1412977
theorem B2506571 : Blo 742328 2506571 := bstep (se 1 (by rfl) ⟨1879928, by rfl⟩ : syracuseStep 2506571 = 3759857) B3759857
theorem B835447 : Blo 742328 835447 := bstep (se 1 (by rfl) ⟨626585, by rfl⟩ : syracuseStep 835447 = 1253171) B1253171
theorem B5357603 : Blo 742328 5357603 := bstep (se 1 (by rfl) ⟨4018202, by rfl⟩ : syracuseStep 5357603 = 8036405) B8036405
theorem B835627 : Blo 742328 835627 := bstep (se 1 (by rfl) ⟨626720, by rfl⟩ : syracuseStep 835627 = 1253441) B1253441
theorem B2506841 : Blo 742328 2506841 := bstep (se 2 (by rfl) ⟨940065, by rfl⟩ : syracuseStep 2506841 = 1880131) B1880131
theorem B835735 : Blo 742328 835735 := bstep (se 1 (by rfl) ⟨626801, by rfl⟩ : syracuseStep 835735 = 1253603) B1253603
theorem B5718221 : Blo 742328 5718221 := bstep (se 3 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 5718221 = 2144333) B2144333
theorem B4014353 : Blo 742328 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B835915 : Blo 742328 835915 := bstep (se 1 (by rfl) ⟨626936, by rfl⟩ : syracuseStep 835915 = 1253873) B1253873
theorem B1884505 : Blo 742328 1884505 := bstep (se 2 (by rfl) ⟨706689, by rfl⟩ : syracuseStep 1884505 = 1413379) B1413379
theorem B836023 : Blo 742328 836023 := bstep (se 1 (by rfl) ⟨627017, by rfl⟩ : syracuseStep 836023 = 1254035) B1254035
theorem B2114009 : Blo 742328 2114009 := bstep (se 2 (by rfl) ⟨792753, by rfl⟩ : syracuseStep 2114009 = 1585507) B1585507
theorem B3392003 : Blo 742328 3392003 := bstep (se 1 (by rfl) ⟨2544002, by rfl⟩ : syracuseStep 3392003 = 5088005) B5088005
theorem B836203 : Blo 742328 836203 := bstep (se 1 (by rfl) ⟨627152, by rfl⟩ : syracuseStep 836203 = 1254305) B1254305
theorem B4244147 : Blo 742328 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B836311 : Blo 742328 836311 := bstep (se 1 (by rfl) ⟨627233, by rfl⟩ : syracuseStep 836311 = 1254467) B1254467
theorem B2507543 : Blo 742328 2507543 := bstep (se 1 (by rfl) ⟨1880657, by rfl⟩ : syracuseStep 2507543 = 3761315) B3761315
theorem B6800203 : Blo 742328 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B836491 : Blo 742328 836491 := bstep (se 1 (by rfl) ⟨627368, by rfl⟩ : syracuseStep 836491 = 1254737) B1254737
theorem B836599 : Blo 742328 836599 := bstep (se 1 (by rfl) ⟨627449, by rfl⟩ : syracuseStep 836599 = 1254899) B1254899
theorem B1590283 : Blo 742328 1590283 := bstep (se 1 (by rfl) ⟨1192712, by rfl⟩ : syracuseStep 1590283 = 2385425) B2385425
theorem B1590359 : Blo 742328 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B836779 : Blo 742328 836779 := bstep (se 1 (by rfl) ⟨627584, by rfl⟩ : syracuseStep 836779 = 1255169) B1255169
theorem B836887 : Blo 742328 836887 := bstep (se 1 (by rfl) ⟨627665, by rfl⟩ : syracuseStep 836887 = 1255331) B1255331
theorem B2508083 : Blo 742328 2508083 := bstep (se 1 (by rfl) ⟨1881062, by rfl⟩ : syracuseStep 2508083 = 3762125) B3762125
theorem B4015435 : Blo 742328 4015435 := bstep (se 1 (by rfl) ⟨3011576, by rfl⟩ : syracuseStep 4015435 = 6023153) B6023153
theorem B1885619 : Blo 742328 1885619 := bstep (se 1 (by rfl) ⟨1414214, by rfl⟩ : syracuseStep 1885619 = 2828429) B2828429
theorem B837067 : Blo 742328 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B837175 : Blo 742328 837175 := bstep (se 1 (by rfl) ⟨627881, by rfl⟩ : syracuseStep 837175 = 1255763) B1255763
theorem B2508353 : Blo 742328 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B6801047 : Blo 742328 6801047 := bstep (se 1 (by rfl) ⟨5100785, by rfl⟩ : syracuseStep 6801047 = 10201571) B10201571
theorem B1885913 : Blo 742328 1885913 := bstep (se 2 (by rfl) ⟨707217, by rfl⟩ : syracuseStep 1885913 = 1414435) B1414435
theorem B837355 : Blo 742328 837355 := bstep (se 1 (by rfl) ⟨628016, by rfl⟩ : syracuseStep 837355 = 1256033) B1256033
theorem B837463 : Blo 742328 837463 := bstep (se 1 (by rfl) ⟨628097, by rfl⟩ : syracuseStep 837463 = 1256195) B1256195
theorem B8472437 : Blo 742328 8472437 := bstep (se 5 (by rfl) ⟨397145, by rfl⟩ : syracuseStep 8472437 = 794291) B794291
theorem B6375347 : Blo 742328 6375347 := bstep (se 1 (by rfl) ⟨4781510, by rfl⟩ : syracuseStep 6375347 = 9563021) B9563021
theorem B837643 : Blo 742328 837643 := bstep (se 1 (by rfl) ⟨628232, by rfl⟩ : syracuseStep 837643 = 1256465) B1256465
theorem B2115649 : Blo 742328 2115649 := bstep (se 2 (by rfl) ⟨793368, by rfl⟩ : syracuseStep 2115649 = 1586737) B1586737
theorem B1722455 : Blo 742328 1722455 := bstep (se 1 (by rfl) ⟨1291841, by rfl⟩ : syracuseStep 1722455 = 2583683) B2583683
theorem B2508893 : Blo 742328 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B4245605 : Blo 742328 4245605 := bstep (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) B796051
theorem B837751 : Blo 742328 837751 := bstep (se 1 (by rfl) ⟨628313, by rfl⟩ : syracuseStep 837751 = 1256627) B1256627
theorem B837931 : Blo 742328 837931 := bstep (se 1 (by rfl) ⟨628448, by rfl⟩ : syracuseStep 837931 = 1256897) B1256897
theorem B838039 : Blo 742328 838039 := bstep (se 1 (by rfl) ⟨628529, by rfl⟩ : syracuseStep 838039 = 1257059) B1257059
theorem B2148811 : Blo 742328 2148811 := bstep (se 1 (by rfl) ⟨1611608, by rfl⟩ : syracuseStep 2148811 = 3223217) B3223217
theorem B838219 : Blo 742328 838219 := bstep (se 1 (by rfl) ⟨628664, by rfl⟩ : syracuseStep 838219 = 1257329) B1257329
theorem B838327 : Blo 742328 838327 := bstep (se 1 (by rfl) ⟨628745, by rfl⟩ : syracuseStep 838327 = 1257491) B1257491
theorem B4246289 : Blo 742328 4246289 := bstep (se 2 (by rfl) ⟨1592358, by rfl⟩ : syracuseStep 4246289 = 3184717) B3184717
theorem B1592129 : Blo 742328 1592129 := bstep (se 2 (by rfl) ⟨597048, by rfl⟩ : syracuseStep 1592129 = 1194097) B1194097
theorem B1788761 : Blo 742328 1788761 := bstep (se 2 (by rfl) ⟨670785, by rfl⟩ : syracuseStep 1788761 = 1341571) B1341571
theorem B838507 : Blo 742328 838507 := bstep (se 1 (by rfl) ⟨628880, by rfl⟩ : syracuseStep 838507 = 1257761) B1257761
theorem B9554867 : Blo 742328 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B838615 : Blo 742328 838615 := bstep (se 1 (by rfl) ⟨628961, by rfl⟩ : syracuseStep 838615 = 1257923) B1257923
theorem B838795 : Blo 742328 838795 := bstep (se 1 (by rfl) ⟨629096, by rfl⟩ : syracuseStep 838795 = 1258193) B1258193
theorem B2510027 : Blo 742328 2510027 := bstep (se 1 (by rfl) ⟨1882520, by rfl⟩ : syracuseStep 2510027 = 3765041) B3765041
theorem B3230941 : Blo 742328 3230941 := bstep (se 3 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 3230941 = 1211603) B1211603
theorem B838903 : Blo 742328 838903 := bstep (se 1 (by rfl) ⟨629177, by rfl⟩ : syracuseStep 838903 = 1258355) B1258355
theorem B1133849 : Blo 742328 1133849 := bstep (se 2 (by rfl) ⟨425193, by rfl⟩ : syracuseStep 1133849 = 850387) B850387
theorem B1887563 : Blo 742328 1887563 := bstep (se 1 (by rfl) ⟨1415672, by rfl⟩ : syracuseStep 1887563 = 2831345) B2831345
theorem B839083 : Blo 742328 839083 := bstep (se 1 (by rfl) ⟨629312, by rfl⟩ : syracuseStep 839083 = 1258625) B1258625
theorem B2510297 : Blo 742328 2510297 := bstep (se 2 (by rfl) ⟨941361, by rfl⟩ : syracuseStep 2510297 = 1882723) B1882723
theorem B839191 : Blo 742328 839191 := bstep (se 1 (by rfl) ⟨629393, by rfl⟩ : syracuseStep 839191 = 1258787) B1258787
theorem B2379415 : Blo 742328 2379415 := bstep (se 1 (by rfl) ⟨1784561, by rfl⟩ : syracuseStep 2379415 = 3569123) B3569123
theorem B839371 : Blo 742328 839371 := bstep (se 1 (by rfl) ⟨629528, by rfl⟩ : syracuseStep 839371 = 1259057) B1259057
theorem B839479 : Blo 742328 839479 := bstep (se 1 (by rfl) ⟨629609, by rfl⟩ : syracuseStep 839479 = 1259219) B1259219
theorem B1789847 : Blo 742328 1789847 := bstep (se 1 (by rfl) ⟨1342385, by rfl⟩ : syracuseStep 1789847 = 2684771) B2684771
theorem B6049687 : Blo 742328 6049687 := bstep (se 1 (by rfl) ⟨4537265, by rfl⟩ : syracuseStep 6049687 = 9074531) B9074531
theorem B2379851 : Blo 742328 2379851 := bstep (se 1 (by rfl) ⟨1784888, by rfl⟩ : syracuseStep 2379851 = 3569777) B3569777
theorem B1134731 : Blo 742328 1134731 := bstep (se 1 (by rfl) ⟨851048, by rfl⟩ : syracuseStep 1134731 = 1702097) B1702097
theorem B2510999 : Blo 742328 2510999 := bstep (se 1 (by rfl) ⟨1883249, by rfl⟩ : syracuseStep 2510999 = 3766499) B3766499
theorem B1888535 : Blo 742328 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B1593931 : Blo 742328 1593931 := bstep (se 1 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 1593931 = 2390897) B2390897
theorem B2511539 : Blo 742328 2511539 := bstep (se 1 (by rfl) ⟨1883654, by rfl⟩ : syracuseStep 2511539 = 3767309) B3767309
theorem B2511809 : Blo 742328 2511809 := bstep (se 2 (by rfl) ⟨941928, by rfl⟩ : syracuseStep 2511809 = 1883857) B1883857
theorem B742347 : Blo 742328 742347 := bstep (se 1 (by rfl) ⟨556760, by rfl⟩ : syracuseStep 742347 = 1113521) B1113521
theorem B2380747 : Blo 742328 2380747 := bstep (se 1 (by rfl) ⟨1785560, by rfl⟩ : syracuseStep 2380747 = 3571121) B3571121
theorem B1790923 : Blo 742328 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B742359 : Blo 742328 742359 := bstep (se 1 (by rfl) ⟨556769, by rfl⟩ : syracuseStep 742359 = 1113539) B1113539
theorem B742379 : Blo 742328 742379 := bstep (se 1 (by rfl) ⟨556784, by rfl⟩ : syracuseStep 742379 = 1113569) B1113569
theorem B742391 : Blo 742328 742391 := bstep (se 1 (by rfl) ⟨556793, by rfl⟩ : syracuseStep 742391 = 1113587) B1113587
theorem B742411 : Blo 742328 742411 := bstep (se 1 (by rfl) ⟨556808, by rfl⟩ : syracuseStep 742411 = 1113617) B1113617
theorem B742423 : Blo 742328 742423 := bstep (se 1 (by rfl) ⟨556817, by rfl⟩ : syracuseStep 742423 = 1113635) B1113635
theorem B742443 : Blo 742328 742443 := bstep (se 1 (by rfl) ⟨556832, by rfl⟩ : syracuseStep 742443 = 1113665) B1113665
theorem B742455 : Blo 742328 742455 := bstep (se 1 (by rfl) ⟨556841, by rfl⟩ : syracuseStep 742455 = 1113683) B1113683
theorem B742475 : Blo 742328 742475 := bstep (se 1 (by rfl) ⟨556856, by rfl⟩ : syracuseStep 742475 = 1113713) B1113713
theorem B742487 : Blo 742328 742487 := bstep (se 1 (by rfl) ⟨556865, by rfl⟩ : syracuseStep 742487 = 1113731) B1113731
theorem B742507 : Blo 742328 742507 := bstep (se 1 (by rfl) ⟨556880, by rfl⟩ : syracuseStep 742507 = 1113761) B1113761
theorem B742519 : Blo 742328 742519 := bstep (se 1 (by rfl) ⟨556889, by rfl⟩ : syracuseStep 742519 = 1113779) B1113779
theorem B742539 : Blo 742328 742539 := bstep (se 1 (by rfl) ⟨556904, by rfl⟩ : syracuseStep 742539 = 1113809) B1113809
theorem B742551 : Blo 742328 742551 := bstep (se 1 (by rfl) ⟨556913, by rfl⟩ : syracuseStep 742551 = 1113827) B1113827
theorem B742571 : Blo 742328 742571 := bstep (se 1 (by rfl) ⟨556928, by rfl⟩ : syracuseStep 742571 = 1113857) B1113857
theorem B742583 : Blo 742328 742583 := bstep (se 1 (by rfl) ⟨556937, by rfl⟩ : syracuseStep 742583 = 1113875) B1113875
theorem B742603 : Blo 742328 742603 := bstep (se 1 (by rfl) ⟨556952, by rfl⟩ : syracuseStep 742603 = 1113905) B1113905
theorem B742615 : Blo 742328 742615 := bstep (se 1 (by rfl) ⟨556961, by rfl⟩ : syracuseStep 742615 = 1113923) B1113923
theorem B742635 : Blo 742328 742635 := bstep (se 1 (by rfl) ⟨556976, by rfl⟩ : syracuseStep 742635 = 1113953) B1113953
theorem B742647 : Blo 742328 742647 := bstep (se 1 (by rfl) ⟨556985, by rfl⟩ : syracuseStep 742647 = 1113971) B1113971
theorem B742667 : Blo 742328 742667 := bstep (se 1 (by rfl) ⟨557000, by rfl⟩ : syracuseStep 742667 = 1114001) B1114001
theorem B742679 : Blo 742328 742679 := bstep (se 1 (by rfl) ⟨557009, by rfl⟩ : syracuseStep 742679 = 1114019) B1114019
theorem B742699 : Blo 742328 742699 := bstep (se 1 (by rfl) ⟨557024, by rfl⟩ : syracuseStep 742699 = 1114049) B1114049
theorem B742711 : Blo 742328 742711 := bstep (se 1 (by rfl) ⟨557033, by rfl⟩ : syracuseStep 742711 = 1114067) B1114067
theorem B742731 : Blo 742328 742731 := bstep (se 1 (by rfl) ⟨557048, by rfl⟩ : syracuseStep 742731 = 1114097) B1114097
theorem B742743 : Blo 742328 742743 := bstep (se 1 (by rfl) ⟨557057, by rfl⟩ : syracuseStep 742743 = 1114115) B1114115
theorem B742763 : Blo 742328 742763 := bstep (se 1 (by rfl) ⟨557072, by rfl⟩ : syracuseStep 742763 = 1114145) B1114145
theorem B742775 : Blo 742328 742775 := bstep (se 1 (by rfl) ⟨557081, by rfl⟩ : syracuseStep 742775 = 1114163) B1114163
theorem B742795 : Blo 742328 742795 := bstep (se 1 (by rfl) ⟨557096, by rfl⟩ : syracuseStep 742795 = 1114193) B1114193
theorem B742807 : Blo 742328 742807 := bstep (se 1 (by rfl) ⟨557105, by rfl⟩ : syracuseStep 742807 = 1114211) B1114211
theorem B742827 : Blo 742328 742827 := bstep (se 1 (by rfl) ⟨557120, by rfl⟩ : syracuseStep 742827 = 1114241) B1114241
theorem B742839 : Blo 742328 742839 := bstep (se 1 (by rfl) ⟨557129, by rfl⟩ : syracuseStep 742839 = 1114259) B1114259
theorem B742859 : Blo 742328 742859 := bstep (se 1 (by rfl) ⟨557144, by rfl⟩ : syracuseStep 742859 = 1114289) B1114289
theorem B742871 : Blo 742328 742871 := bstep (se 1 (by rfl) ⟨557153, by rfl⟩ : syracuseStep 742871 = 1114307) B1114307
theorem B2512349 : Blo 742328 2512349 := bstep (se 3 (by rfl) ⟨471065, by rfl⟩ : syracuseStep 2512349 = 942131) B942131
theorem B742891 : Blo 742328 742891 := bstep (se 1 (by rfl) ⟨557168, by rfl⟩ : syracuseStep 742891 = 1114337) B1114337
theorem B742903 : Blo 742328 742903 := bstep (se 1 (by rfl) ⟨557177, by rfl⟩ : syracuseStep 742903 = 1114355) B1114355
theorem B742923 : Blo 742328 742923 := bstep (se 1 (by rfl) ⟨557192, by rfl⟩ : syracuseStep 742923 = 1114385) B1114385
theorem B742935 : Blo 742328 742935 := bstep (se 1 (by rfl) ⟨557201, by rfl⟩ : syracuseStep 742935 = 1114403) B1114403
theorem B742955 : Blo 742328 742955 := bstep (se 1 (by rfl) ⟨557216, by rfl⟩ : syracuseStep 742955 = 1114433) B1114433
theorem B2381363 : Blo 742328 2381363 := bstep (se 1 (by rfl) ⟨1786022, by rfl⟩ : syracuseStep 2381363 = 3572045) B3572045
theorem B742967 : Blo 742328 742967 := bstep (se 1 (by rfl) ⟨557225, by rfl⟩ : syracuseStep 742967 = 1114451) B1114451
theorem B939595 : Blo 742328 939595 := bstep (se 1 (by rfl) ⟨704696, by rfl⟩ : syracuseStep 939595 = 1409393) B1409393
theorem B742987 : Blo 742328 742987 := bstep (se 1 (by rfl) ⟨557240, by rfl⟩ : syracuseStep 742987 = 1114481) B1114481
theorem B742999 : Blo 742328 742999 := bstep (se 1 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 742999 = 1114499) B1114499
theorem B743019 : Blo 742328 743019 := bstep (se 1 (by rfl) ⟨557264, by rfl⟩ : syracuseStep 743019 = 1114529) B1114529
theorem B743031 : Blo 742328 743031 := bstep (se 1 (by rfl) ⟨557273, by rfl⟩ : syracuseStep 743031 = 1114547) B1114547
theorem B743051 : Blo 742328 743051 := bstep (se 1 (by rfl) ⟨557288, by rfl⟩ : syracuseStep 743051 = 1114577) B1114577
theorem B743063 : Blo 742328 743063 := bstep (se 1 (by rfl) ⟨557297, by rfl⟩ : syracuseStep 743063 = 1114595) B1114595
theorem B743083 : Blo 742328 743083 := bstep (se 1 (by rfl) ⟨557312, by rfl⟩ : syracuseStep 743083 = 1114625) B1114625
theorem B743095 : Blo 742328 743095 := bstep (se 1 (by rfl) ⟨557321, by rfl⟩ : syracuseStep 743095 = 1114643) B1114643
theorem B743115 : Blo 742328 743115 := bstep (se 1 (by rfl) ⟨557336, by rfl⟩ : syracuseStep 743115 = 1114673) B1114673
theorem B743127 : Blo 742328 743127 := bstep (se 1 (by rfl) ⟨557345, by rfl⟩ : syracuseStep 743127 = 1114691) B1114691
theorem B2119385 : Blo 742328 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B743147 : Blo 742328 743147 := bstep (se 1 (by rfl) ⟨557360, by rfl⟩ : syracuseStep 743147 = 1114721) B1114721
theorem B743159 : Blo 742328 743159 := bstep (se 1 (by rfl) ⟨557369, by rfl⟩ : syracuseStep 743159 = 1114739) B1114739
theorem B743179 : Blo 742328 743179 := bstep (se 1 (by rfl) ⟨557384, by rfl⟩ : syracuseStep 743179 = 1114769) B1114769
theorem B743191 : Blo 742328 743191 := bstep (se 1 (by rfl) ⟨557393, by rfl⟩ : syracuseStep 743191 = 1114787) B1114787
theorem B743211 : Blo 742328 743211 := bstep (se 1 (by rfl) ⟨557408, by rfl⟩ : syracuseStep 743211 = 1114817) B1114817
theorem B743223 : Blo 742328 743223 := bstep (se 1 (by rfl) ⟨557417, by rfl⟩ : syracuseStep 743223 = 1114835) B1114835
theorem B2381633 : Blo 742328 2381633 := bstep (se 2 (by rfl) ⟨893112, by rfl⟩ : syracuseStep 2381633 = 1786225) B1786225
theorem B743243 : Blo 742328 743243 := bstep (se 1 (by rfl) ⟨557432, by rfl⟩ : syracuseStep 743243 = 1114865) B1114865
theorem B939863 : Blo 742328 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B743255 : Blo 742328 743255 := bstep (se 1 (by rfl) ⟨557441, by rfl⟩ : syracuseStep 743255 = 1114883) B1114883
theorem B34363237 : Blo 742328 34363237 := bstep (se 4 (by rfl) ⟨3221553, by rfl⟩ : syracuseStep 34363237 = 6443107) B6443107
theorem B743275 : Blo 742328 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B743287 : Blo 742328 743287 := bstep (se 1 (by rfl) ⟨557465, by rfl⟩ : syracuseStep 743287 = 1114931) B1114931
theorem B743307 : Blo 742328 743307 := bstep (se 1 (by rfl) ⟨557480, by rfl⟩ : syracuseStep 743307 = 1114961) B1114961
theorem B743319 : Blo 742328 743319 := bstep (se 1 (by rfl) ⟨557489, by rfl⟩ : syracuseStep 743319 = 1114979) B1114979
theorem B743339 : Blo 742328 743339 := bstep (se 1 (by rfl) ⟨557504, by rfl⟩ : syracuseStep 743339 = 1115009) B1115009
theorem B4249523 : Blo 742328 4249523 := bstep (se 1 (by rfl) ⟨3187142, by rfl⟩ : syracuseStep 4249523 = 6374285) B6374285
theorem B743351 : Blo 742328 743351 := bstep (se 1 (by rfl) ⟨557513, by rfl⟩ : syracuseStep 743351 = 1115027) B1115027
theorem B2676683 : Blo 742328 2676683 := bstep (se 1 (by rfl) ⟨2007512, by rfl⟩ : syracuseStep 2676683 = 4015025) B4015025
theorem B743371 : Blo 742328 743371 := bstep (se 1 (by rfl) ⟨557528, by rfl⟩ : syracuseStep 743371 = 1115057) B1115057
theorem B743383 : Blo 742328 743383 := bstep (se 1 (by rfl) ⟨557537, by rfl⟩ : syracuseStep 743383 = 1115075) B1115075
theorem B743403 : Blo 742328 743403 := bstep (se 1 (by rfl) ⟨557552, by rfl⟩ : syracuseStep 743403 = 1115105) B1115105
theorem B743415 : Blo 742328 743415 := bstep (se 1 (by rfl) ⟨557561, by rfl⟩ : syracuseStep 743415 = 1115123) B1115123
theorem B743435 : Blo 742328 743435 := bstep (se 1 (by rfl) ⟨557576, by rfl⟩ : syracuseStep 743435 = 1115153) B1115153
theorem B743447 : Blo 742328 743447 := bstep (se 1 (by rfl) ⟨557585, by rfl⟩ : syracuseStep 743447 = 1115171) B1115171
theorem B743467 : Blo 742328 743467 := bstep (se 1 (by rfl) ⟨557600, by rfl⟩ : syracuseStep 743467 = 1115201) B1115201
theorem B743479 : Blo 742328 743479 := bstep (se 1 (by rfl) ⟨557609, by rfl⟩ : syracuseStep 743479 = 1115219) B1115219
theorem B2414657 : Blo 742328 2414657 := bstep (se 2 (by rfl) ⟨905496, by rfl⟩ : syracuseStep 2414657 = 1810993) B1810993
theorem B743499 : Blo 742328 743499 := bstep (se 1 (by rfl) ⟨557624, by rfl⟩ : syracuseStep 743499 = 1115249) B1115249
theorem B743511 : Blo 742328 743511 := bstep (se 1 (by rfl) ⟨557633, by rfl⟩ : syracuseStep 743511 = 1115267) B1115267
theorem B743531 : Blo 742328 743531 := bstep (se 1 (by rfl) ⟨557648, by rfl⟩ : syracuseStep 743531 = 1115297) B1115297
theorem B743543 : Blo 742328 743543 := bstep (se 1 (by rfl) ⟨557657, by rfl⟩ : syracuseStep 743543 = 1115315) B1115315
theorem B743563 : Blo 742328 743563 := bstep (se 1 (by rfl) ⟨557672, by rfl⟩ : syracuseStep 743563 = 1115345) B1115345
theorem B743575 : Blo 742328 743575 := bstep (se 1 (by rfl) ⟨557681, by rfl⟩ : syracuseStep 743575 = 1115363) B1115363
theorem B743595 : Blo 742328 743595 := bstep (se 1 (by rfl) ⟨557696, by rfl⟩ : syracuseStep 743595 = 1115393) B1115393
theorem B5363891 : Blo 742328 5363891 := bstep (se 1 (by rfl) ⟨4022918, by rfl⟩ : syracuseStep 5363891 = 8045837) B8045837
theorem B743607 : Blo 742328 743607 := bstep (se 1 (by rfl) ⟨557705, by rfl⟩ : syracuseStep 743607 = 1115411) B1115411
theorem B743627 : Blo 742328 743627 := bstep (se 1 (by rfl) ⟨557720, by rfl⟩ : syracuseStep 743627 = 1115441) B1115441
theorem B743639 : Blo 742328 743639 := bstep (se 1 (by rfl) ⟨557729, by rfl⟩ : syracuseStep 743639 = 1115459) B1115459
theorem B743659 : Blo 742328 743659 := bstep (se 1 (by rfl) ⟨557744, by rfl⟩ : syracuseStep 743659 = 1115489) B1115489
theorem B743671 : Blo 742328 743671 := bstep (se 1 (by rfl) ⟨557753, by rfl⟩ : syracuseStep 743671 = 1115507) B1115507
theorem B743691 : Blo 742328 743691 := bstep (se 1 (by rfl) ⟨557768, by rfl⟩ : syracuseStep 743691 = 1115537) B1115537
theorem B743703 : Blo 742328 743703 := bstep (se 1 (by rfl) ⟨557777, by rfl⟩ : syracuseStep 743703 = 1115555) B1115555
theorem B743723 : Blo 742328 743723 := bstep (se 1 (by rfl) ⟨557792, by rfl⟩ : syracuseStep 743723 = 1115585) B1115585
theorem B2677043 : Blo 742328 2677043 := bstep (se 1 (by rfl) ⟨2007782, by rfl⟩ : syracuseStep 2677043 = 4015565) B4015565
theorem B1792307 : Blo 742328 1792307 := bstep (se 1 (by rfl) ⟨1344230, by rfl⟩ : syracuseStep 1792307 = 2688461) B2688461
theorem B743735 : Blo 742328 743735 := bstep (se 1 (by rfl) ⟨557801, by rfl⟩ : syracuseStep 743735 = 1115603) B1115603
theorem B6773057 : Blo 742328 6773057 := bstep (se 2 (by rfl) ⟨2539896, by rfl⟩ : syracuseStep 6773057 = 5079793) B5079793
theorem B743755 : Blo 742328 743755 := bstep (se 1 (by rfl) ⟨557816, by rfl⟩ : syracuseStep 743755 = 1115633) B1115633
theorem B743767 : Blo 742328 743767 := bstep (se 1 (by rfl) ⟨557825, by rfl⟩ : syracuseStep 743767 = 1115651) B1115651
theorem B743787 : Blo 742328 743787 := bstep (se 1 (by rfl) ⟨557840, by rfl⟩ : syracuseStep 743787 = 1115681) B1115681
theorem B743799 : Blo 742328 743799 := bstep (se 1 (by rfl) ⟨557849, by rfl⟩ : syracuseStep 743799 = 1115699) B1115699
theorem B743819 : Blo 742328 743819 := bstep (se 1 (by rfl) ⟨557864, by rfl⟩ : syracuseStep 743819 = 1115729) B1115729
theorem B743831 : Blo 742328 743831 := bstep (se 1 (by rfl) ⟨557873, by rfl⟩ : syracuseStep 743831 = 1115747) B1115747
theorem B5364119 : Blo 742328 5364119 := bstep (se 1 (by rfl) ⟨4023089, by rfl⟩ : syracuseStep 5364119 = 8046179) B8046179
theorem B743851 : Blo 742328 743851 := bstep (se 1 (by rfl) ⟨557888, by rfl⟩ : syracuseStep 743851 = 1115777) B1115777
theorem B743863 : Blo 742328 743863 := bstep (se 1 (by rfl) ⟨557897, by rfl⟩ : syracuseStep 743863 = 1115795) B1115795
theorem B743883 : Blo 742328 743883 := bstep (se 1 (by rfl) ⟨557912, by rfl⟩ : syracuseStep 743883 = 1115825) B1115825
theorem B743895 : Blo 742328 743895 := bstep (se 1 (by rfl) ⟨557921, by rfl⟩ : syracuseStep 743895 = 1115843) B1115843
theorem B743915 : Blo 742328 743915 := bstep (se 1 (by rfl) ⟨557936, by rfl⟩ : syracuseStep 743915 = 1115873) B1115873
theorem B743927 : Blo 742328 743927 := bstep (se 1 (by rfl) ⟨557945, by rfl⟩ : syracuseStep 743927 = 1115891) B1115891
theorem B743947 : Blo 742328 743947 := bstep (se 1 (by rfl) ⟨557960, by rfl⟩ : syracuseStep 743947 = 1115921) B1115921
theorem B940567 : Blo 742328 940567 := bstep (se 1 (by rfl) ⟨705425, by rfl⟩ : syracuseStep 940567 = 1410851) B1410851
theorem B743959 : Blo 742328 743959 := bstep (se 1 (by rfl) ⟨557969, by rfl⟩ : syracuseStep 743959 = 1115939) B1115939
theorem B743979 : Blo 742328 743979 := bstep (se 1 (by rfl) ⟨557984, by rfl⟩ : syracuseStep 743979 = 1115969) B1115969
theorem B743991 : Blo 742328 743991 := bstep (se 1 (by rfl) ⟨557993, by rfl⟩ : syracuseStep 743991 = 1115987) B1115987
theorem B744011 : Blo 742328 744011 := bstep (se 1 (by rfl) ⟨558008, by rfl⟩ : syracuseStep 744011 = 1116017) B1116017
theorem B2513483 : Blo 742328 2513483 := bstep (se 1 (by rfl) ⟨1885112, by rfl⟩ : syracuseStep 2513483 = 3770225) B3770225
theorem B744023 : Blo 742328 744023 := bstep (se 1 (by rfl) ⟨558017, by rfl⟩ : syracuseStep 744023 = 1116035) B1116035
theorem B744043 : Blo 742328 744043 := bstep (se 1 (by rfl) ⟨558032, by rfl⟩ : syracuseStep 744043 = 1116065) B1116065
theorem B744055 : Blo 742328 744055 := bstep (se 1 (by rfl) ⟨558041, by rfl⟩ : syracuseStep 744055 = 1116083) B1116083
theorem B3758723 : Blo 742328 3758723 := bstep (se 1 (by rfl) ⟨2819042, by rfl⟩ : syracuseStep 3758723 = 5638085) B5638085
theorem B744075 : Blo 742328 744075 := bstep (se 1 (by rfl) ⟨558056, by rfl⟩ : syracuseStep 744075 = 1116113) B1116113
theorem B744087 : Blo 742328 744087 := bstep (se 1 (by rfl) ⟨558065, by rfl⟩ : syracuseStep 744087 = 1116131) B1116131
theorem B744107 : Blo 742328 744107 := bstep (se 1 (by rfl) ⟨558080, by rfl⟩ : syracuseStep 744107 = 1116161) B1116161
theorem B744119 : Blo 742328 744119 := bstep (se 1 (by rfl) ⟨558089, by rfl⟩ : syracuseStep 744119 = 1116179) B1116179
theorem B744139 : Blo 742328 744139 := bstep (se 1 (by rfl) ⟨558104, by rfl⟩ : syracuseStep 744139 = 1116209) B1116209
theorem B744151 : Blo 742328 744151 := bstep (se 1 (by rfl) ⟨558113, by rfl⟩ : syracuseStep 744151 = 1116227) B1116227
theorem B744171 : Blo 742328 744171 := bstep (se 1 (by rfl) ⟨558128, by rfl⟩ : syracuseStep 744171 = 1116257) B1116257
theorem B744183 : Blo 742328 744183 := bstep (se 1 (by rfl) ⟨558137, by rfl⟩ : syracuseStep 744183 = 1116275) B1116275
theorem B744203 : Blo 742328 744203 := bstep (se 1 (by rfl) ⟨558152, by rfl⟩ : syracuseStep 744203 = 1116305) B1116305
theorem B744215 : Blo 742328 744215 := bstep (se 1 (by rfl) ⟨558161, by rfl⟩ : syracuseStep 744215 = 1116323) B1116323
theorem B744235 : Blo 742328 744235 := bstep (se 1 (by rfl) ⟨558176, by rfl⟩ : syracuseStep 744235 = 1116353) B1116353
theorem B744247 : Blo 742328 744247 := bstep (se 1 (by rfl) ⟨558185, by rfl⟩ : syracuseStep 744247 = 1116371) B1116371
theorem B744267 : Blo 742328 744267 := bstep (se 1 (by rfl) ⟨558200, by rfl⟩ : syracuseStep 744267 = 1116401) B1116401
theorem B744279 : Blo 742328 744279 := bstep (se 1 (by rfl) ⟨558209, by rfl⟩ : syracuseStep 744279 = 1116419) B1116419
theorem B2513753 : Blo 742328 2513753 := bstep (se 2 (by rfl) ⟨942657, by rfl⟩ : syracuseStep 2513753 = 1885315) B1885315
theorem B744299 : Blo 742328 744299 := bstep (se 1 (by rfl) ⟨558224, by rfl⟩ : syracuseStep 744299 = 1116449) B1116449
theorem B744311 : Blo 742328 744311 := bstep (se 1 (by rfl) ⟨558233, by rfl⟩ : syracuseStep 744311 = 1116467) B1116467
theorem B744331 : Blo 742328 744331 := bstep (se 1 (by rfl) ⟨558248, by rfl⟩ : syracuseStep 744331 = 1116497) B1116497
theorem B744343 : Blo 742328 744343 := bstep (se 1 (by rfl) ⟨558257, by rfl⟩ : syracuseStep 744343 = 1116515) B1116515
theorem B744363 : Blo 742328 744363 := bstep (se 1 (by rfl) ⟨558272, by rfl⟩ : syracuseStep 744363 = 1116545) B1116545
theorem B744375 : Blo 742328 744375 := bstep (se 1 (by rfl) ⟨558281, by rfl⟩ : syracuseStep 744375 = 1116563) B1116563
theorem B744395 : Blo 742328 744395 := bstep (se 1 (by rfl) ⟨558296, by rfl⟩ : syracuseStep 744395 = 1116593) B1116593
theorem B2120651 : Blo 742328 2120651 := bstep (se 1 (by rfl) ⟨1590488, by rfl⟩ : syracuseStep 2120651 = 3180977) B3180977
theorem B744407 : Blo 742328 744407 := bstep (se 1 (by rfl) ⟨558305, by rfl⟩ : syracuseStep 744407 = 1116611) B1116611
theorem B744427 : Blo 742328 744427 := bstep (se 1 (by rfl) ⟨558320, by rfl⟩ : syracuseStep 744427 = 1116641) B1116641
theorem B744439 : Blo 742328 744439 := bstep (se 1 (by rfl) ⟨558329, by rfl⟩ : syracuseStep 744439 = 1116659) B1116659
theorem B744459 : Blo 742328 744459 := bstep (se 1 (by rfl) ⟨558344, by rfl⟩ : syracuseStep 744459 = 1116689) B1116689
theorem B744471 : Blo 742328 744471 := bstep (se 1 (by rfl) ⟨558353, by rfl⟩ : syracuseStep 744471 = 1116707) B1116707
theorem B744491 : Blo 742328 744491 := bstep (se 1 (by rfl) ⟨558368, by rfl⟩ : syracuseStep 744491 = 1116737) B1116737
theorem B744503 : Blo 742328 744503 := bstep (se 1 (by rfl) ⟨558377, by rfl⟩ : syracuseStep 744503 = 1116755) B1116755
theorem B744523 : Blo 742328 744523 := bstep (se 1 (by rfl) ⟨558392, by rfl⟩ : syracuseStep 744523 = 1116785) B1116785
theorem B744535 : Blo 742328 744535 := bstep (se 1 (by rfl) ⟨558401, by rfl⟩ : syracuseStep 744535 = 1116803) B1116803
theorem B744555 : Blo 742328 744555 := bstep (se 1 (by rfl) ⟨558416, by rfl⟩ : syracuseStep 744555 = 1116833) B1116833
theorem B744567 : Blo 742328 744567 := bstep (se 1 (by rfl) ⟨558425, by rfl⟩ : syracuseStep 744567 = 1116851) B1116851
theorem B744587 : Blo 742328 744587 := bstep (se 1 (by rfl) ⟨558440, by rfl⟩ : syracuseStep 744587 = 1116881) B1116881
theorem B744599 : Blo 742328 744599 := bstep (se 1 (by rfl) ⟨558449, by rfl⟩ : syracuseStep 744599 = 1116899) B1116899
theorem B744619 : Blo 742328 744619 := bstep (se 1 (by rfl) ⟨558464, by rfl⟩ : syracuseStep 744619 = 1116929) B1116929
theorem B20405429 : Blo 742328 20405429 := bstep (se 5 (by rfl) ⟨956504, by rfl⟩ : syracuseStep 20405429 = 1913009) B1913009
theorem B744631 : Blo 742328 744631 := bstep (se 1 (by rfl) ⟨558473, by rfl⟩ : syracuseStep 744631 = 1116947) B1116947
theorem B744651 : Blo 742328 744651 := bstep (se 1 (by rfl) ⟨558488, by rfl⟩ : syracuseStep 744651 = 1116977) B1116977
theorem B744663 : Blo 742328 744663 := bstep (se 1 (by rfl) ⟨558497, by rfl⟩ : syracuseStep 744663 = 1116995) B1116995
theorem B744683 : Blo 742328 744683 := bstep (se 1 (by rfl) ⟨558512, by rfl⟩ : syracuseStep 744683 = 1117025) B1117025
theorem B744695 : Blo 742328 744695 := bstep (se 1 (by rfl) ⟨558521, by rfl⟩ : syracuseStep 744695 = 1117043) B1117043
theorem B744715 : Blo 742328 744715 := bstep (se 1 (by rfl) ⟨558536, by rfl⟩ : syracuseStep 744715 = 1117073) B1117073
theorem B744727 : Blo 742328 744727 := bstep (se 1 (by rfl) ⟨558545, by rfl⟩ : syracuseStep 744727 = 1117091) B1117091
theorem B3398935 : Blo 742328 3398935 := bstep (se 1 (by rfl) ⟨2549201, by rfl⟩ : syracuseStep 3398935 = 5098403) B5098403
theorem B744747 : Blo 742328 744747 := bstep (se 1 (by rfl) ⟨558560, by rfl⟩ : syracuseStep 744747 = 1117121) B1117121
theorem B744759 : Blo 742328 744759 := bstep (se 1 (by rfl) ⟨558569, by rfl⟩ : syracuseStep 744759 = 1117139) B1117139
theorem B744779 : Blo 742328 744779 := bstep (se 1 (by rfl) ⟨558584, by rfl⟩ : syracuseStep 744779 = 1117169) B1117169
theorem B744791 : Blo 742328 744791 := bstep (se 1 (by rfl) ⟨558593, by rfl⟩ : syracuseStep 744791 = 1117187) B1117187
theorem B744811 : Blo 742328 744811 := bstep (se 1 (by rfl) ⟨558608, by rfl⟩ : syracuseStep 744811 = 1117217) B1117217
theorem B744823 : Blo 742328 744823 := bstep (se 1 (by rfl) ⟨558617, by rfl⟩ : syracuseStep 744823 = 1117235) B1117235
theorem B744843 : Blo 742328 744843 := bstep (se 1 (by rfl) ⟨558632, by rfl⟩ : syracuseStep 744843 = 1117265) B1117265
theorem B744855 : Blo 742328 744855 := bstep (se 1 (by rfl) ⟨558641, by rfl⟩ : syracuseStep 744855 = 1117283) B1117283
theorem B744875 : Blo 742328 744875 := bstep (se 1 (by rfl) ⟨558656, by rfl⟩ : syracuseStep 744875 = 1117313) B1117313
theorem B744887 : Blo 742328 744887 := bstep (se 1 (by rfl) ⟨558665, by rfl⟩ : syracuseStep 744887 = 1117331) B1117331
theorem B744907 : Blo 742328 744907 := bstep (se 1 (by rfl) ⟨558680, by rfl⟩ : syracuseStep 744907 = 1117361) B1117361
theorem B744919 : Blo 742328 744919 := bstep (se 1 (by rfl) ⟨558689, by rfl⟩ : syracuseStep 744919 = 1117379) B1117379
theorem B744939 : Blo 742328 744939 := bstep (se 1 (by rfl) ⟨558704, by rfl⟩ : syracuseStep 744939 = 1117409) B1117409
theorem B744951 : Blo 742328 744951 := bstep (se 1 (by rfl) ⟨558713, by rfl⟩ : syracuseStep 744951 = 1117427) B1117427
theorem B744971 : Blo 742328 744971 := bstep (se 1 (by rfl) ⟨558728, by rfl⟩ : syracuseStep 744971 = 1117457) B1117457
theorem B744983 : Blo 742328 744983 := bstep (se 1 (by rfl) ⟨558737, by rfl⟩ : syracuseStep 744983 = 1117475) B1117475
theorem B2514455 : Blo 742328 2514455 := bstep (se 1 (by rfl) ⟨1885841, by rfl⟩ : syracuseStep 2514455 = 3771683) B3771683
theorem B745003 : Blo 742328 745003 := bstep (se 1 (by rfl) ⟨558752, by rfl⟩ : syracuseStep 745003 = 1117505) B1117505
theorem B745015 : Blo 742328 745015 := bstep (se 1 (by rfl) ⟨558761, by rfl⟩ : syracuseStep 745015 = 1117523) B1117523
theorem B745035 : Blo 742328 745035 := bstep (se 1 (by rfl) ⟨558776, by rfl⟩ : syracuseStep 745035 = 1117553) B1117553
theorem B745047 : Blo 742328 745047 := bstep (se 1 (by rfl) ⟨558785, by rfl⟩ : syracuseStep 745047 = 1117571) B1117571
theorem B8248925 : Blo 742328 8248925 := bstep (se 3 (by rfl) ⟨1546673, by rfl⟩ : syracuseStep 8248925 = 3093347) B3093347
theorem B745067 : Blo 742328 745067 := bstep (se 1 (by rfl) ⟨558800, by rfl⟩ : syracuseStep 745067 = 1117601) B1117601
theorem B745079 : Blo 742328 745079 := bstep (se 1 (by rfl) ⟨558809, by rfl⟩ : syracuseStep 745079 = 1117619) B1117619
theorem B745099 : Blo 742328 745099 := bstep (se 1 (by rfl) ⟨558824, by rfl⟩ : syracuseStep 745099 = 1117649) B1117649
theorem B745111 : Blo 742328 745111 := bstep (se 1 (by rfl) ⟨558833, by rfl⟩ : syracuseStep 745111 = 1117667) B1117667
theorem B745131 : Blo 742328 745131 := bstep (se 1 (by rfl) ⟨558848, by rfl⟩ : syracuseStep 745131 = 1117697) B1117697
theorem B745143 : Blo 742328 745143 := bstep (se 1 (by rfl) ⟨558857, by rfl⟩ : syracuseStep 745143 = 1117715) B1117715
theorem B745163 : Blo 742328 745163 := bstep (se 1 (by rfl) ⟨558872, by rfl⟩ : syracuseStep 745163 = 1117745) B1117745
theorem B745175 : Blo 742328 745175 := bstep (se 1 (by rfl) ⟨558881, by rfl⟩ : syracuseStep 745175 = 1117763) B1117763
theorem B745195 : Blo 742328 745195 := bstep (se 1 (by rfl) ⟨558896, by rfl⟩ : syracuseStep 745195 = 1117793) B1117793
theorem B745207 : Blo 742328 745207 := bstep (se 1 (by rfl) ⟨558905, by rfl⟩ : syracuseStep 745207 = 1117811) B1117811
theorem B745227 : Blo 742328 745227 := bstep (se 1 (by rfl) ⟨558920, by rfl⟩ : syracuseStep 745227 = 1117841) B1117841
theorem B745239 : Blo 742328 745239 := bstep (se 1 (by rfl) ⟨558929, by rfl⟩ : syracuseStep 745239 = 1117859) B1117859
theorem B745259 : Blo 742328 745259 := bstep (se 1 (by rfl) ⟨558944, by rfl⟩ : syracuseStep 745259 = 1117889) B1117889
theorem B745271 : Blo 742328 745271 := bstep (se 1 (by rfl) ⟨558953, by rfl⟩ : syracuseStep 745271 = 1117907) B1117907
theorem B745291 : Blo 742328 745291 := bstep (se 1 (by rfl) ⟨558968, by rfl⟩ : syracuseStep 745291 = 1117937) B1117937
theorem B745303 : Blo 742328 745303 := bstep (se 1 (by rfl) ⟨558977, by rfl⟩ : syracuseStep 745303 = 1117955) B1117955
theorem B745323 : Blo 742328 745323 := bstep (se 1 (by rfl) ⟨558992, by rfl⟩ : syracuseStep 745323 = 1117985) B1117985
theorem B745335 : Blo 742328 745335 := bstep (se 1 (by rfl) ⟨559001, by rfl⟩ : syracuseStep 745335 = 1118003) B1118003
theorem B745355 : Blo 742328 745355 := bstep (se 1 (by rfl) ⟨559016, by rfl⟩ : syracuseStep 745355 = 1118033) B1118033
theorem B745367 : Blo 742328 745367 := bstep (se 1 (by rfl) ⟨559025, by rfl⟩ : syracuseStep 745367 = 1118051) B1118051
theorem B745387 : Blo 742328 745387 := bstep (se 1 (by rfl) ⟨559040, by rfl⟩ : syracuseStep 745387 = 1118081) B1118081
theorem B745399 : Blo 742328 745399 := bstep (se 1 (by rfl) ⟨559049, by rfl⟩ : syracuseStep 745399 = 1118099) B1118099
theorem B745419 : Blo 742328 745419 := bstep (se 1 (by rfl) ⟨559064, by rfl⟩ : syracuseStep 745419 = 1118129) B1118129
theorem B745431 : Blo 742328 745431 := bstep (se 1 (by rfl) ⟨559073, by rfl⟩ : syracuseStep 745431 = 1118147) B1118147
theorem B745451 : Blo 742328 745451 := bstep (se 1 (by rfl) ⟨559088, by rfl⟩ : syracuseStep 745451 = 1118177) B1118177
theorem B745463 : Blo 742328 745463 := bstep (se 1 (by rfl) ⟨559097, by rfl⟩ : syracuseStep 745463 = 1118195) B1118195
theorem B745483 : Blo 742328 745483 := bstep (se 1 (by rfl) ⟨559112, by rfl⟩ : syracuseStep 745483 = 1118225) B1118225
theorem B745495 : Blo 742328 745495 := bstep (se 1 (by rfl) ⟨559121, by rfl⟩ : syracuseStep 745495 = 1118243) B1118243
theorem B745515 : Blo 742328 745515 := bstep (se 1 (by rfl) ⟨559136, by rfl⟩ : syracuseStep 745515 = 1118273) B1118273
theorem B2514995 : Blo 742328 2514995 := bstep (se 1 (by rfl) ⟨1886246, by rfl⟩ : syracuseStep 2514995 = 3772493) B3772493
theorem B745527 : Blo 742328 745527 := bstep (se 1 (by rfl) ⟨559145, by rfl⟩ : syracuseStep 745527 = 1118291) B1118291
theorem B745547 : Blo 742328 745547 := bstep (se 1 (by rfl) ⟨559160, by rfl⟩ : syracuseStep 745547 = 1118321) B1118321
theorem B745559 : Blo 742328 745559 := bstep (se 1 (by rfl) ⟨559169, by rfl⟩ : syracuseStep 745559 = 1118339) B1118339
theorem B745579 : Blo 742328 745579 := bstep (se 1 (by rfl) ⟨559184, by rfl⟩ : syracuseStep 745579 = 1118369) B1118369
theorem B745591 : Blo 742328 745591 := bstep (se 1 (by rfl) ⟨559193, by rfl⟩ : syracuseStep 745591 = 1118387) B1118387
theorem B745611 : Blo 742328 745611 := bstep (se 1 (by rfl) ⟨559208, by rfl⟩ : syracuseStep 745611 = 1118417) B1118417
theorem B16113815 : Blo 742328 16113815 := bstep (se 1 (by rfl) ⟨12085361, by rfl⟩ : syracuseStep 16113815 = 24170723) B24170723
theorem B745623 : Blo 742328 745623 := bstep (se 1 (by rfl) ⟨559217, by rfl⟩ : syracuseStep 745623 = 1118435) B1118435
theorem B745643 : Blo 742328 745643 := bstep (se 1 (by rfl) ⟨559232, by rfl⟩ : syracuseStep 745643 = 1118465) B1118465
theorem B745655 : Blo 742328 745655 := bstep (se 1 (by rfl) ⟨559241, by rfl⟩ : syracuseStep 745655 = 1118483) B1118483
theorem B942283 : Blo 742328 942283 := bstep (se 1 (by rfl) ⟨706712, by rfl⟩ : syracuseStep 942283 = 1413425) B1413425
theorem B1433803 : Blo 742328 1433803 := bstep (se 1 (by rfl) ⟨1075352, by rfl⟩ : syracuseStep 1433803 = 2150705) B2150705
theorem B745675 : Blo 742328 745675 := bstep (se 1 (by rfl) ⟨559256, by rfl⟩ : syracuseStep 745675 = 1118513) B1118513
theorem B745687 : Blo 742328 745687 := bstep (se 1 (by rfl) ⟨559265, by rfl⟩ : syracuseStep 745687 = 1118531) B1118531
theorem B2384093 : Blo 742328 2384093 := bstep (se 3 (by rfl) ⟨447017, by rfl⟩ : syracuseStep 2384093 = 894035) B894035
theorem B745707 : Blo 742328 745707 := bstep (se 1 (by rfl) ⟨559280, by rfl⟩ : syracuseStep 745707 = 1118561) B1118561
theorem B745719 : Blo 742328 745719 := bstep (se 1 (by rfl) ⟨559289, by rfl⟩ : syracuseStep 745719 = 1118579) B1118579
theorem B745739 : Blo 742328 745739 := bstep (se 1 (by rfl) ⟨559304, by rfl⟩ : syracuseStep 745739 = 1118609) B1118609
theorem B745751 : Blo 742328 745751 := bstep (se 1 (by rfl) ⟨559313, by rfl⟩ : syracuseStep 745751 = 1118627) B1118627
theorem B745771 : Blo 742328 745771 := bstep (se 1 (by rfl) ⟨559328, by rfl⟩ : syracuseStep 745771 = 1118657) B1118657
theorem B745783 : Blo 742328 745783 := bstep (se 1 (by rfl) ⟨559337, by rfl⟩ : syracuseStep 745783 = 1118675) B1118675
theorem B2515265 : Blo 742328 2515265 := bstep (se 2 (by rfl) ⟨943224, by rfl⟩ : syracuseStep 2515265 = 1886449) B1886449
theorem B745803 : Blo 742328 745803 := bstep (se 1 (by rfl) ⟨559352, by rfl⟩ : syracuseStep 745803 = 1118705) B1118705
theorem B745815 : Blo 742328 745815 := bstep (se 1 (by rfl) ⟨559361, by rfl⟩ : syracuseStep 745815 = 1118723) B1118723
theorem B745835 : Blo 742328 745835 := bstep (se 1 (by rfl) ⟨559376, by rfl⟩ : syracuseStep 745835 = 1118753) B1118753
theorem B745847 : Blo 742328 745847 := bstep (se 1 (by rfl) ⟨559385, by rfl⟩ : syracuseStep 745847 = 1118771) B1118771
theorem B1008011 : Blo 742328 1008011 := bstep (se 1 (by rfl) ⟨756008, by rfl⟩ : syracuseStep 1008011 = 1512017) B1512017
theorem B745867 : Blo 742328 745867 := bstep (se 1 (by rfl) ⟨559400, by rfl⟩ : syracuseStep 745867 = 1118801) B1118801
theorem B745879 : Blo 742328 745879 := bstep (se 1 (by rfl) ⟨559409, by rfl⟩ : syracuseStep 745879 = 1118819) B1118819
theorem B745899 : Blo 742328 745899 := bstep (se 1 (by rfl) ⟨559424, by rfl⟩ : syracuseStep 745899 = 1118849) B1118849
theorem B745911 : Blo 742328 745911 := bstep (se 1 (by rfl) ⟨559433, by rfl⟩ : syracuseStep 745911 = 1118867) B1118867
theorem B745931 : Blo 742328 745931 := bstep (se 1 (by rfl) ⟨559448, by rfl⟩ : syracuseStep 745931 = 1118897) B1118897
theorem B745943 : Blo 742328 745943 := bstep (se 1 (by rfl) ⟨559457, by rfl⟩ : syracuseStep 745943 = 1118915) B1118915
theorem B745963 : Blo 742328 745963 := bstep (se 1 (by rfl) ⟨559472, by rfl⟩ : syracuseStep 745963 = 1118945) B1118945
theorem B745975 : Blo 742328 745975 := bstep (se 1 (by rfl) ⟨559481, by rfl⟩ : syracuseStep 745975 = 1118963) B1118963
theorem B745995 : Blo 742328 745995 := bstep (se 1 (by rfl) ⟨559496, by rfl⟩ : syracuseStep 745995 = 1118993) B1118993
theorem B746007 : Blo 742328 746007 := bstep (se 1 (by rfl) ⟨559505, by rfl⟩ : syracuseStep 746007 = 1119011) B1119011
theorem B746027 : Blo 742328 746027 := bstep (se 1 (by rfl) ⟨559520, by rfl⟩ : syracuseStep 746027 = 1119041) B1119041
theorem B746039 : Blo 742328 746039 := bstep (se 1 (by rfl) ⟨559529, by rfl⟩ : syracuseStep 746039 = 1119059) B1119059
theorem B746059 : Blo 742328 746059 := bstep (se 1 (by rfl) ⟨559544, by rfl⟩ : syracuseStep 746059 = 1119089) B1119089
theorem B746071 : Blo 742328 746071 := bstep (se 1 (by rfl) ⟨559553, by rfl⟩ : syracuseStep 746071 = 1119107) B1119107
theorem B746091 : Blo 742328 746091 := bstep (se 1 (by rfl) ⟨559568, by rfl⟩ : syracuseStep 746091 = 1119137) B1119137
theorem B746103 : Blo 742328 746103 := bstep (se 1 (by rfl) ⟨559577, by rfl⟩ : syracuseStep 746103 = 1119155) B1119155
theorem B746123 : Blo 742328 746123 := bstep (se 1 (by rfl) ⟨559592, by rfl⟩ : syracuseStep 746123 = 1119185) B1119185
theorem B746135 : Blo 742328 746135 := bstep (se 1 (by rfl) ⟨559601, by rfl⟩ : syracuseStep 746135 = 1119203) B1119203
theorem B746155 : Blo 742328 746155 := bstep (se 1 (by rfl) ⟨559616, by rfl⟩ : syracuseStep 746155 = 1119233) B1119233
theorem B746167 : Blo 742328 746167 := bstep (se 1 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 746167 = 1119251) B1119251
theorem B746187 : Blo 742328 746187 := bstep (se 1 (by rfl) ⟨559640, by rfl⟩ : syracuseStep 746187 = 1119281) B1119281
theorem B746199 : Blo 742328 746199 := bstep (se 1 (by rfl) ⟨559649, by rfl⟩ : syracuseStep 746199 = 1119299) B1119299
theorem B746219 : Blo 742328 746219 := bstep (se 1 (by rfl) ⟨559664, by rfl⟩ : syracuseStep 746219 = 1119329) B1119329
theorem B746231 : Blo 742328 746231 := bstep (se 1 (by rfl) ⟨559673, by rfl⟩ : syracuseStep 746231 = 1119347) B1119347
theorem B746251 : Blo 742328 746251 := bstep (se 1 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 746251 = 1119377) B1119377
theorem B746263 : Blo 742328 746263 := bstep (se 1 (by rfl) ⟨559697, by rfl⟩ : syracuseStep 746263 = 1119395) B1119395
theorem B746283 : Blo 742328 746283 := bstep (se 1 (by rfl) ⟨559712, by rfl⟩ : syracuseStep 746283 = 1119425) B1119425
theorem B746295 : Blo 742328 746295 := bstep (se 1 (by rfl) ⟨559721, by rfl⟩ : syracuseStep 746295 = 1119443) B1119443
theorem B746315 : Blo 742328 746315 := bstep (se 1 (by rfl) ⟨559736, by rfl⟩ : syracuseStep 746315 = 1119473) B1119473
theorem B746327 : Blo 742328 746327 := bstep (se 1 (by rfl) ⟨559745, by rfl⟩ : syracuseStep 746327 = 1119491) B1119491
theorem B2515805 : Blo 742328 2515805 := bstep (se 3 (by rfl) ⟨471713, by rfl⟩ : syracuseStep 2515805 = 943427) B943427
theorem B2679725 : Blo 742328 2679725 := bstep (se 3 (by rfl) ⟨502448, by rfl⟩ : syracuseStep 2679725 = 1004897) B1004897
theorem B8610947 : Blo 742328 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B943255 : Blo 742328 943255 := bstep (se 1 (by rfl) ⟨707441, by rfl⟩ : syracuseStep 943255 = 1414883) B1414883
theorem B3171545 : Blo 742328 3171545 := bstep (se 2 (by rfl) ⟨1189329, by rfl⟩ : syracuseStep 3171545 = 2378659) B2378659
theorem B5367001 : Blo 742328 5367001 := bstep (se 2 (by rfl) ⟨2012625, by rfl⟩ : syracuseStep 5367001 = 4025251) B4025251
theorem B3433693 : Blo 742328 3433693 := bstep (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) B1287635
theorem B3171629 : Blo 742328 3171629 := bstep (se 3 (by rfl) ⟨594680, by rfl⟩ : syracuseStep 3171629 = 1189361) B1189361
theorem B1205579 : Blo 742328 1205579 := bstep (se 1 (by rfl) ⟨904184, by rfl⟩ : syracuseStep 1205579 = 1808369) B1808369
theorem B7169381 : Blo 742328 7169381 := bstep (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) B1344259
theorem B10708631 : Blo 742328 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B5662385 : Blo 742328 5662385 := bstep (se 2 (by rfl) ⟨2123394, by rfl⟩ : syracuseStep 5662385 = 4246789) B4246789
theorem B21489461 : Blo 742328 21489461 := bstep (se 5 (by rfl) ⟨1007318, by rfl⟩ : syracuseStep 21489461 = 2014637) B2014637
theorem B2516939 : Blo 742328 2516939 := bstep (se 1 (by rfl) ⟨1887704, by rfl⟩ : syracuseStep 2516939 = 3775409) B3775409
theorem B944075 : Blo 742328 944075 := bstep (se 1 (by rfl) ⟨708056, by rfl⟩ : syracuseStep 944075 = 1416113) B1416113
theorem B5662871 : Blo 742328 5662871 := bstep (se 1 (by rfl) ⟨4247153, by rfl⟩ : syracuseStep 5662871 = 8494307) B8494307
theorem B2615513 : Blo 742328 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B2517209 : Blo 742328 2517209 := bstep (se 2 (by rfl) ⟨943953, by rfl⟩ : syracuseStep 2517209 = 1887907) B1887907
theorem B3762449 : Blo 742328 3762449 := bstep (se 2 (by rfl) ⟨1410918, by rfl⟩ : syracuseStep 3762449 = 2821837) B2821837
theorem B5728529 : Blo 742328 5728529 := bstep (se 2 (by rfl) ⟨2148198, by rfl⟩ : syracuseStep 5728529 = 4296397) B4296397
theorem B3762611 : Blo 742328 3762611 := bstep (se 1 (by rfl) ⟨2821958, by rfl⟩ : syracuseStep 3762611 = 5643917) B5643917
theorem B4778513 : Blo 742328 4778513 := bstep (se 2 (by rfl) ⟨1791942, by rfl⟩ : syracuseStep 4778513 = 3583885) B3583885
theorem B2517911 : Blo 742328 2517911 := bstep (se 1 (by rfl) ⟨1888433, by rfl⟩ : syracuseStep 2517911 = 3776867) B3776867
theorem B2714797 : Blo 742328 2714797 := bstep (se 3 (by rfl) ⟨509024, by rfl⟩ : syracuseStep 2714797 = 1018049) B1018049
theorem B2714969 : Blo 742328 2714969 := bstep (se 2 (by rfl) ⟨1018113, by rfl⟩ : syracuseStep 2714969 = 2036227) B2036227
theorem B2518451 : Blo 742328 2518451 := bstep (se 1 (by rfl) ⟨1888838, by rfl⟩ : syracuseStep 2518451 = 3777677) B3777677
theorem B2420375 : Blo 742328 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B2518721 : Blo 742328 2518721 := bstep (se 2 (by rfl) ⟨944520, by rfl⟩ : syracuseStep 2518721 = 1889041) B1889041
theorem B42987671 : Blo 742328 42987671 := bstep (se 1 (by rfl) ⟨32240753, by rfl⟩ : syracuseStep 42987671 = 64481507) B64481507
theorem B6025421 : Blo 742328 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B3764555 : Blo 742328 3764555 := bstep (se 1 (by rfl) ⟨2823416, by rfl⟩ : syracuseStep 3764555 = 5646833) B5646833
theorem B2683415 : Blo 742328 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B3174977 : Blo 742328 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B1340107 : Blo 742328 1340107 := bstep (se 1 (by rfl) ⟨1005080, by rfl⟩ : syracuseStep 1340107 = 2010161) B2010161
theorem B9172099 : Blo 742328 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B6354125 : Blo 742328 6354125 := bstep (se 3 (by rfl) ⟨1191398, by rfl⟩ : syracuseStep 6354125 = 2382797) B2382797
theorem B3175645 : Blo 742328 3175645 := bstep (se 3 (by rfl) ⟨595433, by rfl⟩ : syracuseStep 3175645 = 1190867) B1190867
theorem B8484101 : Blo 742328 8484101 := bstep (se 4 (by rfl) ⟨795384, by rfl⟩ : syracuseStep 8484101 = 1590769) B1590769
theorem B4519261 : Blo 742328 4519261 := bstep (se 3 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 4519261 = 1694723) B1694723
theorem B849547 : Blo 742328 849547 := bstep (se 1 (by rfl) ⟨637160, by rfl⟩ : syracuseStep 849547 = 1274321) B1274321
theorem B6616849 : Blo 742328 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B3176243 : Blo 742328 3176243 := bstep (se 1 (by rfl) ⟨2382182, by rfl⟩ : syracuseStep 3176243 = 4764365) B4764365
theorem B1472435 : Blo 742328 1472435 := bstep (se 1 (by rfl) ⟨1104326, by rfl⟩ : syracuseStep 1472435 = 2208653) B2208653
theorem B1341463 : Blo 742328 1341463 := bstep (se 1 (by rfl) ⟨1006097, by rfl⟩ : syracuseStep 1341463 = 2012195) B2012195
theorem B3766337 : Blo 742328 3766337 := bstep (se 2 (by rfl) ⟨1412376, by rfl⟩ : syracuseStep 3766337 = 2824753) B2824753
theorem B1341515 : Blo 742328 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B2685059 : Blo 742328 2685059 := bstep (se 1 (by rfl) ⟨2013794, by rfl⟩ : syracuseStep 2685059 = 4027589) B4027589
theorem B1276183 : Blo 742328 1276183 := bstep (se 1 (by rfl) ⟨957137, by rfl⟩ : syracuseStep 1276183 = 1914275) B1914275
theorem B850423 : Blo 742328 850423 := bstep (se 1 (by rfl) ⟨637817, by rfl⟩ : syracuseStep 850423 = 1275635) B1275635
theorem B1636951 : Blo 742328 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B1145675 : Blo 742328 1145675 := bstep (se 1 (by rfl) ⟨859256, by rfl⟩ : syracuseStep 1145675 = 1718513) B1718513
theorem B11598709 : Blo 742328 11598709 := bstep (se 5 (by rfl) ⟨543689, by rfl⟩ : syracuseStep 11598709 = 1087379) B1087379
theorem B1670273 : Blo 742328 1670273 := bstep (se 2 (by rfl) ⟨626352, by rfl⟩ : syracuseStep 1670273 = 1252705) B1252705
theorem B24476813 : Blo 742328 24476813 := bstep (se 3 (by rfl) ⟨4589402, by rfl⟩ : syracuseStep 24476813 = 9178805) B9178805
theorem B752983 : Blo 742328 752983 := bstep (se 1 (by rfl) ⟨564737, by rfl⟩ : syracuseStep 752983 = 1129475) B1129475
theorem B1670489 : Blo 742328 1670489 := bstep (se 2 (by rfl) ⟨626433, by rfl⟩ : syracuseStep 1670489 = 1252867) B1252867
theorem B1113497 : Blo 742328 1113497 := bstep (se 2 (by rfl) ⟨417561, by rfl⟩ : syracuseStep 1113497 = 835123) B835123
theorem B1670579 : Blo 742328 1670579 := bstep (se 1 (by rfl) ⟨1252934, by rfl⟩ : syracuseStep 1670579 = 2505869) B2505869
theorem B1670615 : Blo 742328 1670615 := bstep (se 1 (by rfl) ⟨1252961, by rfl⟩ : syracuseStep 1670615 = 2505923) B2505923
theorem B1113611 : Blo 742328 1113611 := bstep (se 1 (by rfl) ⟨835208, by rfl⟩ : syracuseStep 1113611 = 1670417) B1670417
theorem B1113623 : Blo 742328 1113623 := bstep (se 1 (by rfl) ⟨835217, by rfl⟩ : syracuseStep 1113623 = 1670435) B1670435
theorem B6356515 : Blo 742328 6356515 := bstep (se 1 (by rfl) ⟨4767386, by rfl⟩ : syracuseStep 6356515 = 9534773) B9534773
theorem B1113689 : Blo 742328 1113689 := bstep (se 2 (by rfl) ⟨417633, by rfl⟩ : syracuseStep 1113689 = 835267) B835267
theorem B1670795 : Blo 742328 1670795 := bstep (se 1 (by rfl) ⟨1253096, by rfl⟩ : syracuseStep 1670795 = 2506193) B2506193
theorem B1670849 : Blo 742328 1670849 := bstep (se 2 (by rfl) ⟨626568, by rfl⟩ : syracuseStep 1670849 = 1253137) B1253137
theorem B1113803 : Blo 742328 1113803 := bstep (se 1 (by rfl) ⟨835352, by rfl⟩ : syracuseStep 1113803 = 1670705) B1670705
theorem B1113815 : Blo 742328 1113815 := bstep (se 1 (by rfl) ⟨835361, by rfl⟩ : syracuseStep 1113815 = 1670723) B1670723
theorem B1113881 : Blo 742328 1113881 := bstep (se 2 (by rfl) ⟨417705, by rfl⟩ : syracuseStep 1113881 = 835411) B835411
theorem B1113995 : Blo 742328 1113995 := bstep (se 1 (by rfl) ⟨835496, by rfl⟩ : syracuseStep 1113995 = 1670993) B1670993
theorem B1114007 : Blo 742328 1114007 := bstep (se 1 (by rfl) ⟨835505, by rfl⟩ : syracuseStep 1114007 = 1671011) B1671011
theorem B1671065 : Blo 742328 1671065 := bstep (se 2 (by rfl) ⟨626649, by rfl⟩ : syracuseStep 1671065 = 1253299) B1253299
theorem B18087857 : Blo 742328 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B1507265 : Blo 742328 1507265 := bstep (se 2 (by rfl) ⟨565224, by rfl⟩ : syracuseStep 1507265 = 1130449) B1130449
theorem B1114073 : Blo 742328 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B3768281 : Blo 742328 3768281 := bstep (se 2 (by rfl) ⟨1413105, by rfl⟩ : syracuseStep 3768281 = 2826211) B2826211
theorem B1671155 : Blo 742328 1671155 := bstep (se 1 (by rfl) ⟨1253366, by rfl⟩ : syracuseStep 1671155 = 2506733) B2506733
theorem B1114127 : Blo 742328 1114127 := bstep (se 1 (by rfl) ⟨835595, by rfl⟩ : syracuseStep 1114127 = 1671191) B1671191
theorem B1114169 : Blo 742328 1114169 := bstep (se 2 (by rfl) ⟨417813, by rfl⟩ : syracuseStep 1114169 = 835627) B835627
theorem B1671227 : Blo 742328 1671227 := bstep (se 1 (by rfl) ⟨1253420, by rfl⟩ : syracuseStep 1671227 = 2506841) B2506841
theorem B14286941 : Blo 742328 14286941 := bstep (se 3 (by rfl) ⟨2678801, by rfl⟩ : syracuseStep 14286941 = 5357603) B5357603
theorem B1114247 : Blo 742328 1114247 := bstep (se 1 (by rfl) ⟨835685, by rfl⟩ : syracuseStep 1114247 = 1671371) B1671371
theorem B1114283 : Blo 742328 1114283 := bstep (se 1 (by rfl) ⟨835712, by rfl⟩ : syracuseStep 1114283 = 1671425) B1671425
theorem B1671353 : Blo 742328 1671353 := bstep (se 2 (by rfl) ⟨626757, by rfl⟩ : syracuseStep 1671353 = 1253515) B1253515
theorem B1114313 : Blo 742328 1114313 := bstep (se 2 (by rfl) ⟨417867, by rfl⟩ : syracuseStep 1114313 = 835735) B835735
theorem B1409339 : Blo 742328 1409339 := bstep (se 1 (by rfl) ⟨1057004, by rfl⟩ : syracuseStep 1409339 = 2114009) B2114009
theorem B1114427 : Blo 742328 1114427 := bstep (se 1 (by rfl) ⟨835820, by rfl⟩ : syracuseStep 1114427 = 1671641) B1671641
theorem B1114487 : Blo 742328 1114487 := bstep (se 1 (by rfl) ⟨835865, by rfl⟩ : syracuseStep 1114487 = 1671731) B1671731
theorem B1114511 : Blo 742328 1114511 := bstep (se 1 (by rfl) ⟨835883, by rfl⟩ : syracuseStep 1114511 = 1671767) B1671767
theorem B1114553 : Blo 742328 1114553 := bstep (se 2 (by rfl) ⟨417957, by rfl⟩ : syracuseStep 1114553 = 835915) B835915
theorem B1114631 : Blo 742328 1114631 := bstep (se 1 (by rfl) ⟨835973, by rfl⟩ : syracuseStep 1114631 = 1671947) B1671947
theorem B1671695 : Blo 742328 1671695 := bstep (se 1 (by rfl) ⟨1253771, by rfl⟩ : syracuseStep 1671695 = 2507543) B2507543
theorem B1671713 : Blo 742328 1671713 := bstep (se 2 (by rfl) ⟨626892, by rfl⟩ : syracuseStep 1671713 = 1253785) B1253785
theorem B1114667 : Blo 742328 1114667 := bstep (se 1 (by rfl) ⟨836000, by rfl⟩ : syracuseStep 1114667 = 1672001) B1672001
theorem B1114697 : Blo 742328 1114697 := bstep (se 2 (by rfl) ⟨418011, by rfl⟩ : syracuseStep 1114697 = 836023) B836023
theorem B1114811 : Blo 742328 1114811 := bstep (se 1 (by rfl) ⟨836108, by rfl⟩ : syracuseStep 1114811 = 1672217) B1672217
theorem B1114871 : Blo 742328 1114871 := bstep (se 1 (by rfl) ⟨836153, by rfl⟩ : syracuseStep 1114871 = 1672307) B1672307
theorem B1114895 : Blo 742328 1114895 := bstep (se 1 (by rfl) ⟨836171, by rfl⟩ : syracuseStep 1114895 = 1672343) B1672343
theorem B1409825 : Blo 742328 1409825 := bstep (se 2 (by rfl) ⟨528684, by rfl⟩ : syracuseStep 1409825 = 1057369) B1057369
theorem B1114937 : Blo 742328 1114937 := bstep (se 2 (by rfl) ⟨418101, by rfl⟩ : syracuseStep 1114937 = 836203) B836203
theorem B1672055 : Blo 742328 1672055 := bstep (se 1 (by rfl) ⟨1254041, by rfl⟩ : syracuseStep 1672055 = 2508083) B2508083
theorem B1115015 : Blo 742328 1115015 := bstep (se 1 (by rfl) ⟨836261, by rfl⟩ : syracuseStep 1115015 = 1672523) B1672523
theorem B1115051 : Blo 742328 1115051 := bstep (se 1 (by rfl) ⟨836288, by rfl⟩ : syracuseStep 1115051 = 1672577) B1672577
theorem B1409977 : Blo 742328 1409977 := bstep (se 2 (by rfl) ⟨528741, by rfl⟩ : syracuseStep 1409977 = 1057483) B1057483
theorem B1115081 : Blo 742328 1115081 := bstep (se 2 (by rfl) ⟨418155, by rfl⟩ : syracuseStep 1115081 = 836311) B836311
theorem B2688029 : Blo 742328 2688029 := bstep (se 3 (by rfl) ⟨504005, by rfl⟩ : syracuseStep 2688029 = 1008011) B1008011
theorem B1672235 : Blo 742328 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B1115195 : Blo 742328 1115195 := bstep (se 1 (by rfl) ⟨836396, by rfl⟩ : syracuseStep 1115195 = 1672793) B1672793
theorem B1115255 : Blo 742328 1115255 := bstep (se 1 (by rfl) ⟨836441, by rfl⟩ : syracuseStep 1115255 = 1672883) B1672883
theorem B1115279 : Blo 742328 1115279 := bstep (se 1 (by rfl) ⟨836459, by rfl⟩ : syracuseStep 1115279 = 1672919) B1672919
theorem B1115321 : Blo 742328 1115321 := bstep (se 2 (by rfl) ⟨418245, by rfl⟩ : syracuseStep 1115321 = 836491) B836491
theorem B1115399 : Blo 742328 1115399 := bstep (se 1 (by rfl) ⟨836549, by rfl⟩ : syracuseStep 1115399 = 1673099) B1673099
theorem B1115435 : Blo 742328 1115435 := bstep (se 1 (by rfl) ⟨836576, by rfl⟩ : syracuseStep 1115435 = 1673153) B1673153
theorem B1115465 : Blo 742328 1115465 := bstep (se 2 (by rfl) ⟨418299, by rfl⟩ : syracuseStep 1115465 = 836599) B836599
theorem B9045341 : Blo 742328 9045341 := bstep (se 3 (by rfl) ⟨1696001, by rfl⟩ : syracuseStep 9045341 = 3392003) B3392003
theorem B1148303 : Blo 742328 1148303 := bstep (se 1 (by rfl) ⟨861227, by rfl⟩ : syracuseStep 1148303 = 1722455) B1722455
theorem B1672595 : Blo 742328 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B1115579 : Blo 742328 1115579 := bstep (se 1 (by rfl) ⟨836684, by rfl⟩ : syracuseStep 1115579 = 1673369) B1673369
theorem B1672649 : Blo 742328 1672649 := bstep (se 2 (by rfl) ⟨627243, by rfl⟩ : syracuseStep 1672649 = 1254487) B1254487
theorem B1115639 : Blo 742328 1115639 := bstep (se 1 (by rfl) ⟨836729, by rfl⟩ : syracuseStep 1115639 = 1673459) B1673459
theorem B1115663 : Blo 742328 1115663 := bstep (se 1 (by rfl) ⟨836747, by rfl⟩ : syracuseStep 1115663 = 1673495) B1673495
theorem B1115705 : Blo 742328 1115705 := bstep (se 2 (by rfl) ⟨418389, by rfl⟩ : syracuseStep 1115705 = 836779) B836779
theorem B1115783 : Blo 742328 1115783 := bstep (se 1 (by rfl) ⟨836837, by rfl⟩ : syracuseStep 1115783 = 1673675) B1673675
theorem B1115819 : Blo 742328 1115819 := bstep (se 1 (by rfl) ⟨836864, by rfl⟩ : syracuseStep 1115819 = 1673729) B1673729
theorem B1115849 : Blo 742328 1115849 := bstep (se 2 (by rfl) ⟨418443, by rfl⟩ : syracuseStep 1115849 = 836887) B836887
theorem B1115963 : Blo 742328 1115963 := bstep (se 1 (by rfl) ⟨836972, by rfl⟩ : syracuseStep 1115963 = 1673945) B1673945
theorem B1116023 : Blo 742328 1116023 := bstep (se 1 (by rfl) ⟨837017, by rfl⟩ : syracuseStep 1116023 = 1674035) B1674035
theorem B1116047 : Blo 742328 1116047 := bstep (se 1 (by rfl) ⟨837035, by rfl⟩ : syracuseStep 1116047 = 1674071) B1674071
theorem B1116089 : Blo 742328 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B1116167 : Blo 742328 1116167 := bstep (se 1 (by rfl) ⟨837125, by rfl⟩ : syracuseStep 1116167 = 1674251) B1674251
theorem B1116203 : Blo 742328 1116203 := bstep (se 1 (by rfl) ⟨837152, by rfl⟩ : syracuseStep 1116203 = 1674305) B1674305
theorem B1116233 : Blo 742328 1116233 := bstep (se 2 (by rfl) ⟨418587, by rfl⟩ : syracuseStep 1116233 = 837175) B837175
theorem B16124021 : Blo 742328 16124021 := bstep (se 5 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 16124021 = 1511627) B1511627
theorem B1673351 : Blo 742328 1673351 := bstep (se 1 (by rfl) ⟨1255013, by rfl⟩ : syracuseStep 1673351 = 2510027) B2510027
theorem B4229293 : Blo 742328 4229293 := bstep (se 3 (by rfl) ⟨792992, by rfl⟩ : syracuseStep 4229293 = 1585985) B1585985
theorem B1116347 : Blo 742328 1116347 := bstep (se 1 (by rfl) ⟨837260, by rfl⟩ : syracuseStep 1116347 = 1674521) B1674521
theorem B755899 : Blo 742328 755899 := bstep (se 1 (by rfl) ⟨566924, by rfl⟩ : syracuseStep 755899 = 1133849) B1133849
theorem B1116407 : Blo 742328 1116407 := bstep (se 1 (by rfl) ⟨837305, by rfl⟩ : syracuseStep 1116407 = 1674611) B1674611
theorem B1116431 : Blo 742328 1116431 := bstep (se 1 (by rfl) ⟨837323, by rfl⟩ : syracuseStep 1116431 = 1674647) B1674647
theorem B1116473 : Blo 742328 1116473 := bstep (se 2 (by rfl) ⟨418677, by rfl⟩ : syracuseStep 1116473 = 837355) B837355
theorem B1673531 : Blo 742328 1673531 := bstep (se 1 (by rfl) ⟨1255148, by rfl⟩ : syracuseStep 1673531 = 2510297) B2510297
theorem B1116551 : Blo 742328 1116551 := bstep (se 1 (by rfl) ⟨837413, by rfl⟩ : syracuseStep 1116551 = 1674827) B1674827
theorem B1116587 : Blo 742328 1116587 := bstep (se 1 (by rfl) ⟨837440, by rfl⟩ : syracuseStep 1116587 = 1674881) B1674881
theorem B1673657 : Blo 742328 1673657 := bstep (se 2 (by rfl) ⟨627621, by rfl⟩ : syracuseStep 1673657 = 1255243) B1255243
theorem B1116617 : Blo 742328 1116617 := bstep (se 2 (by rfl) ⟨418731, by rfl⟩ : syracuseStep 1116617 = 837463) B837463
theorem B12061169 : Blo 742328 12061169 := bstep (se 2 (by rfl) ⟨4522938, by rfl⟩ : syracuseStep 12061169 = 9045877) B9045877
theorem B1116731 : Blo 742328 1116731 := bstep (se 1 (by rfl) ⟨837548, by rfl⟩ : syracuseStep 1116731 = 1675097) B1675097
theorem B1116791 : Blo 742328 1116791 := bstep (se 1 (by rfl) ⟨837593, by rfl⟩ : syracuseStep 1116791 = 1675187) B1675187
theorem B1116815 : Blo 742328 1116815 := bstep (se 1 (by rfl) ⟨837611, by rfl⟩ : syracuseStep 1116815 = 1675223) B1675223
theorem B1411769 : Blo 742328 1411769 := bstep (se 2 (by rfl) ⟨529413, by rfl⟩ : syracuseStep 1411769 = 1058827) B1058827
theorem B1116857 : Blo 742328 1116857 := bstep (se 2 (by rfl) ⟨418821, by rfl⟩ : syracuseStep 1116857 = 837643) B837643
theorem B2820865 : Blo 742328 2820865 := bstep (se 2 (by rfl) ⟨1057824, by rfl⟩ : syracuseStep 2820865 = 2115649) B2115649
theorem B1116935 : Blo 742328 1116935 := bstep (se 1 (by rfl) ⟨837701, by rfl⟩ : syracuseStep 1116935 = 1675403) B1675403
theorem B756487 : Blo 742328 756487 := bstep (se 1 (by rfl) ⟨567365, by rfl⟩ : syracuseStep 756487 = 1134731) B1134731
theorem B9046799 : Blo 742328 9046799 := bstep (se 1 (by rfl) ⟨6785099, by rfl⟩ : syracuseStep 9046799 = 13570199) B13570199
theorem B1673999 : Blo 742328 1673999 := bstep (se 1 (by rfl) ⟨1255499, by rfl⟩ : syracuseStep 1673999 = 2510999) B2510999
theorem B1674017 : Blo 742328 1674017 := bstep (se 2 (by rfl) ⟨627756, by rfl⟩ : syracuseStep 1674017 = 1255513) B1255513
theorem B1116971 : Blo 742328 1116971 := bstep (se 1 (by rfl) ⟨837728, by rfl⟩ : syracuseStep 1116971 = 1675457) B1675457
theorem B1117001 : Blo 742328 1117001 := bstep (se 2 (by rfl) ⟨418875, by rfl⟩ : syracuseStep 1117001 = 837751) B837751
theorem B1117115 : Blo 742328 1117115 := bstep (se 1 (by rfl) ⟨837836, by rfl⟩ : syracuseStep 1117115 = 1675673) B1675673
theorem B1117175 : Blo 742328 1117175 := bstep (se 1 (by rfl) ⟨837881, by rfl⟩ : syracuseStep 1117175 = 1675763) B1675763
theorem B1117199 : Blo 742328 1117199 := bstep (se 1 (by rfl) ⟨837899, by rfl⟩ : syracuseStep 1117199 = 1675799) B1675799
theorem B1117241 : Blo 742328 1117241 := bstep (se 2 (by rfl) ⟨418965, by rfl⟩ : syracuseStep 1117241 = 837931) B837931
theorem B1674359 : Blo 742328 1674359 := bstep (se 1 (by rfl) ⟨1255769, by rfl⟩ : syracuseStep 1674359 = 2511539) B2511539
theorem B1117319 : Blo 742328 1117319 := bstep (se 1 (by rfl) ⟨837989, by rfl⟩ : syracuseStep 1117319 = 1675979) B1675979
theorem B1117355 : Blo 742328 1117355 := bstep (se 1 (by rfl) ⟨838016, by rfl⟩ : syracuseStep 1117355 = 1676033) B1676033
theorem B4033709 : Blo 742328 4033709 := bstep (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) B1512641
theorem B1117385 : Blo 742328 1117385 := bstep (se 2 (by rfl) ⟨419019, by rfl⟩ : syracuseStep 1117385 = 838039) B838039
theorem B1674539 : Blo 742328 1674539 := bstep (se 1 (by rfl) ⟨1255904, by rfl⟩ : syracuseStep 1674539 = 2511809) B2511809
theorem B1117499 : Blo 742328 1117499 := bstep (se 1 (by rfl) ⟨838124, by rfl⟩ : syracuseStep 1117499 = 1676249) B1676249
theorem B1117559 : Blo 742328 1117559 := bstep (se 1 (by rfl) ⟨838169, by rfl⟩ : syracuseStep 1117559 = 1676339) B1676339
theorem B1117583 : Blo 742328 1117583 := bstep (se 1 (by rfl) ⟨838187, by rfl⟩ : syracuseStep 1117583 = 1676375) B1676375
theorem B1117625 : Blo 742328 1117625 := bstep (se 2 (by rfl) ⟨419109, by rfl⟩ : syracuseStep 1117625 = 838219) B838219
theorem B1117703 : Blo 742328 1117703 := bstep (se 1 (by rfl) ⟨838277, by rfl⟩ : syracuseStep 1117703 = 1676555) B1676555
theorem B1117739 : Blo 742328 1117739 := bstep (se 1 (by rfl) ⟨838304, by rfl⟩ : syracuseStep 1117739 = 1676609) B1676609
theorem B1117769 : Blo 742328 1117769 := bstep (se 2 (by rfl) ⟨419163, by rfl⟩ : syracuseStep 1117769 = 838327) B838327
theorem B1674899 : Blo 742328 1674899 := bstep (se 1 (by rfl) ⟨1256174, by rfl⟩ : syracuseStep 1674899 = 2512349) B2512349
theorem B1117883 : Blo 742328 1117883 := bstep (se 1 (by rfl) ⟨838412, by rfl⟩ : syracuseStep 1117883 = 1676825) B1676825
theorem B1674953 : Blo 742328 1674953 := bstep (se 2 (by rfl) ⟨628107, by rfl⟩ : syracuseStep 1674953 = 1256215) B1256215
theorem B7147237 : Blo 742328 7147237 := bstep (se 4 (by rfl) ⟨670053, by rfl⟩ : syracuseStep 7147237 = 1340107) B1340107
theorem B1117943 : Blo 742328 1117943 := bstep (se 1 (by rfl) ⟨838457, by rfl⟩ : syracuseStep 1117943 = 1676915) B1676915
theorem B1117967 : Blo 742328 1117967 := bstep (se 1 (by rfl) ⟨838475, by rfl⟩ : syracuseStep 1117967 = 1676951) B1676951
theorem B1118009 : Blo 742328 1118009 := bstep (se 2 (by rfl) ⟨419253, by rfl⟩ : syracuseStep 1118009 = 838507) B838507
theorem B1118087 : Blo 742328 1118087 := bstep (se 1 (by rfl) ⟨838565, by rfl⟩ : syracuseStep 1118087 = 1677131) B1677131
theorem B1118123 : Blo 742328 1118123 := bstep (se 1 (by rfl) ⟨838592, by rfl⟩ : syracuseStep 1118123 = 1677185) B1677185
theorem B1118153 : Blo 742328 1118153 := bstep (se 2 (by rfl) ⟨419307, by rfl⟩ : syracuseStep 1118153 = 838615) B838615
theorem B1118267 : Blo 742328 1118267 := bstep (se 1 (by rfl) ⟨838700, by rfl⟩ : syracuseStep 1118267 = 1677401) B1677401
theorem B3575927 : Blo 742328 3575927 := bstep (se 1 (by rfl) ⟨2681945, by rfl⟩ : syracuseStep 3575927 = 5363891) B5363891
theorem B1118327 : Blo 742328 1118327 := bstep (se 1 (by rfl) ⟨838745, by rfl⟩ : syracuseStep 1118327 = 1677491) B1677491
theorem B1118351 : Blo 742328 1118351 := bstep (se 1 (by rfl) ⟨838763, by rfl⟩ : syracuseStep 1118351 = 1677527) B1677527
theorem B1118393 : Blo 742328 1118393 := bstep (se 2 (by rfl) ⟨419397, by rfl⟩ : syracuseStep 1118393 = 838795) B838795
theorem B1118471 : Blo 742328 1118471 := bstep (se 1 (by rfl) ⟨838853, by rfl⟩ : syracuseStep 1118471 = 1677707) B1677707
theorem B3576079 : Blo 742328 3576079 := bstep (se 1 (by rfl) ⟨2682059, by rfl⟩ : syracuseStep 3576079 = 5364119) B5364119
theorem B1118507 : Blo 742328 1118507 := bstep (se 1 (by rfl) ⟨838880, by rfl⟩ : syracuseStep 1118507 = 1677761) B1677761
theorem B1118537 : Blo 742328 1118537 := bstep (se 2 (by rfl) ⟨419451, by rfl⟩ : syracuseStep 1118537 = 838903) B838903
theorem B1675655 : Blo 742328 1675655 := bstep (se 1 (by rfl) ⟨1256741, by rfl⟩ : syracuseStep 1675655 = 2513483) B2513483
theorem B3772817 : Blo 742328 3772817 := bstep (se 2 (by rfl) ⟨1414806, by rfl⟩ : syracuseStep 3772817 = 2829613) B2829613
theorem B1118651 : Blo 742328 1118651 := bstep (se 1 (by rfl) ⟨838988, by rfl⟩ : syracuseStep 1118651 = 1677977) B1677977
theorem B1118711 : Blo 742328 1118711 := bstep (se 1 (by rfl) ⟨839033, by rfl⟩ : syracuseStep 1118711 = 1678067) B1678067
theorem B1118735 : Blo 742328 1118735 := bstep (se 1 (by rfl) ⟨839051, by rfl⟩ : syracuseStep 1118735 = 1678103) B1678103
theorem B4231709 : Blo 742328 4231709 := bstep (se 3 (by rfl) ⟨793445, by rfl⟩ : syracuseStep 4231709 = 1586891) B1586891
theorem B1118777 : Blo 742328 1118777 := bstep (se 2 (by rfl) ⟨419541, by rfl⟩ : syracuseStep 1118777 = 839083) B839083
theorem B1675835 : Blo 742328 1675835 := bstep (se 1 (by rfl) ⟨1256876, by rfl⟩ : syracuseStep 1675835 = 2513753) B2513753
theorem B1413767 : Blo 742328 1413767 := bstep (se 1 (by rfl) ⟨1060325, by rfl⟩ : syracuseStep 1413767 = 2120651) B2120651
theorem B1118855 : Blo 742328 1118855 := bstep (se 1 (by rfl) ⟨839141, by rfl⟩ : syracuseStep 1118855 = 1678283) B1678283
theorem B1118891 : Blo 742328 1118891 := bstep (se 1 (by rfl) ⟨839168, by rfl⟩ : syracuseStep 1118891 = 1678337) B1678337
theorem B1675961 : Blo 742328 1675961 := bstep (se 2 (by rfl) ⟨628485, by rfl⟩ : syracuseStep 1675961 = 1256971) B1256971
theorem B1118921 : Blo 742328 1118921 := bstep (se 2 (by rfl) ⟨419595, by rfl⟩ : syracuseStep 1118921 = 839191) B839191
theorem B13603619 : Blo 742328 13603619 := bstep (se 1 (by rfl) ⟨10202714, by rfl⟩ : syracuseStep 13603619 = 20405429) B20405429
theorem B1119035 : Blo 742328 1119035 := bstep (se 1 (by rfl) ⟨839276, by rfl⟩ : syracuseStep 1119035 = 1678553) B1678553
theorem B1119095 : Blo 742328 1119095 := bstep (se 1 (by rfl) ⟨839321, by rfl⟩ : syracuseStep 1119095 = 1678643) B1678643
theorem B3019655 : Blo 742328 3019655 := bstep (se 1 (by rfl) ⟨2264741, by rfl⟩ : syracuseStep 3019655 = 4529483) B4529483
theorem B1119119 : Blo 742328 1119119 := bstep (se 1 (by rfl) ⟨839339, by rfl⟩ : syracuseStep 1119119 = 1678679) B1678679
theorem B1119161 : Blo 742328 1119161 := bstep (se 2 (by rfl) ⟨419685, by rfl⟩ : syracuseStep 1119161 = 839371) B839371
theorem B1119239 : Blo 742328 1119239 := bstep (se 1 (by rfl) ⟨839429, by rfl⟩ : syracuseStep 1119239 = 1678859) B1678859
theorem B1676303 : Blo 742328 1676303 := bstep (se 1 (by rfl) ⟨1257227, by rfl⟩ : syracuseStep 1676303 = 2514455) B2514455
theorem B1676321 : Blo 742328 1676321 := bstep (se 2 (by rfl) ⟨628620, by rfl⟩ : syracuseStep 1676321 = 1257241) B1257241
theorem B1119275 : Blo 742328 1119275 := bstep (se 1 (by rfl) ⟨839456, by rfl⟩ : syracuseStep 1119275 = 1678913) B1678913
theorem B1119305 : Blo 742328 1119305 := bstep (se 2 (by rfl) ⟨419739, by rfl⟩ : syracuseStep 1119305 = 839479) B839479
theorem B1512583 : Blo 742328 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B1119419 : Blo 742328 1119419 := bstep (se 1 (by rfl) ⟨839564, by rfl⟩ : syracuseStep 1119419 = 1679129) B1679129
theorem B8066249 : Blo 742328 8066249 := bstep (se 2 (by rfl) ⟨3024843, by rfl⟩ : syracuseStep 8066249 = 6049687) B6049687
theorem B1119479 : Blo 742328 1119479 := bstep (se 1 (by rfl) ⟨839609, by rfl⟩ : syracuseStep 1119479 = 1679219) B1679219
theorem B1381691 : Blo 742328 1381691 := bstep (se 1 (by rfl) ⟨1036268, by rfl⟩ : syracuseStep 1381691 = 2072537) B2072537
theorem B1676663 : Blo 742328 1676663 := bstep (se 1 (by rfl) ⟨1257497, by rfl⟩ : syracuseStep 1676663 = 2514995) B2514995
theorem B1676843 : Blo 742328 1676843 := bstep (se 1 (by rfl) ⟨1257632, by rfl⟩ : syracuseStep 1676843 = 2515265) B2515265
theorem B2299435 : Blo 742328 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem B2823767 : Blo 742328 2823767 := bstep (se 1 (by rfl) ⟨2117825, by rfl⟩ : syracuseStep 2823767 = 4235651) B4235651
theorem B7149235 : Blo 742328 7149235 := bstep (se 1 (by rfl) ⟨5361926, by rfl⟩ : syracuseStep 7149235 = 10723853) B10723853
theorem B8492849 : Blo 742328 8492849 := bstep (se 2 (by rfl) ⟨3184818, by rfl⟩ : syracuseStep 8492849 = 6369637) B6369637
theorem B1677203 : Blo 742328 1677203 := bstep (se 1 (by rfl) ⟨1257902, by rfl⟩ : syracuseStep 1677203 = 2515805) B2515805
theorem B1677257 : Blo 742328 1677257 := bstep (se 2 (by rfl) ⟨628971, by rfl⟩ : syracuseStep 1677257 = 1257943) B1257943
theorem B15276077 : Blo 742328 15276077 := bstep (se 3 (by rfl) ⟨2864264, by rfl⟩ : syracuseStep 15276077 = 5728529) B5728529
theorem B2824253 : Blo 742328 2824253 := bstep (se 3 (by rfl) ⟨529547, by rfl⟩ : syracuseStep 2824253 = 1059095) B1059095
theorem B5740631 : Blo 742328 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B1415369 : Blo 742328 1415369 := bstep (se 2 (by rfl) ⟨530763, by rfl⟩ : syracuseStep 1415369 = 1061527) B1061527
theorem B792839 : Blo 742328 792839 := bstep (se 1 (by rfl) ⟨594629, by rfl⟩ : syracuseStep 792839 = 1189259) B1189259
theorem B2857369 : Blo 742328 2857369 := bstep (se 2 (by rfl) ⟨1071513, by rfl⟩ : syracuseStep 2857369 = 2143027) B2143027
theorem B3774923 : Blo 742328 3774923 := bstep (se 1 (by rfl) ⟨2831192, by rfl⟩ : syracuseStep 3774923 = 5662385) B5662385
theorem B14326307 : Blo 742328 14326307 := bstep (se 1 (by rfl) ⟨10744730, by rfl⟩ : syracuseStep 14326307 = 21489461) B21489461
theorem B1677959 : Blo 742328 1677959 := bstep (se 1 (by rfl) ⟨1258469, by rfl⟩ : syracuseStep 1677959 = 2516939) B2516939
theorem B5642945 : Blo 742328 5642945 := bstep (se 2 (by rfl) ⟨2116104, by rfl⟩ : syracuseStep 5642945 = 4232209) B4232209
theorem B3775247 : Blo 742328 3775247 := bstep (se 1 (by rfl) ⟨2831435, by rfl⟩ : syracuseStep 3775247 = 5662871) B5662871
theorem B1678139 : Blo 742328 1678139 := bstep (se 1 (by rfl) ⟨1258604, by rfl⟩ : syracuseStep 1678139 = 2517209) B2517209
theorem B12229465 : Blo 742328 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B1678265 : Blo 742328 1678265 := bstep (se 2 (by rfl) ⟨629349, by rfl⟩ : syracuseStep 1678265 = 1258699) B1258699
theorem B4234193 : Blo 742328 4234193 := bstep (se 2 (by rfl) ⟨1587822, by rfl⟩ : syracuseStep 4234193 = 3175645) B3175645
theorem B3185675 : Blo 742328 3185675 := bstep (se 1 (by rfl) ⟨2389256, by rfl⟩ : syracuseStep 3185675 = 4778513) B4778513
theorem B3021911 : Blo 742328 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B1678607 : Blo 742328 1678607 := bstep (se 1 (by rfl) ⟨1258955, by rfl⟩ : syracuseStep 1678607 = 2517911) B2517911
theorem B1678625 : Blo 742328 1678625 := bstep (se 2 (by rfl) ⟨629484, by rfl⟩ : syracuseStep 1678625 = 1258969) B1258969
theorem B1252793 : Blo 742328 1252793 := bstep (se 2 (by rfl) ⟨469797, by rfl⟩ : syracuseStep 1252793 = 939595) B939595
theorem B3055133 : Blo 742328 3055133 := bstep (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) B1145675
theorem B12688973 : Blo 742328 12688973 := bstep (se 3 (by rfl) ⟨2379182, by rfl⟩ : syracuseStep 12688973 = 4758365) B4758365
theorem B1678967 : Blo 742328 1678967 := bstep (se 1 (by rfl) ⟨1259225, by rfl⟩ : syracuseStep 1678967 = 2518451) B2518451
theorem B8822465 : Blo 742328 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B2825999 : Blo 742328 2825999 := bstep (se 1 (by rfl) ⟨2119499, by rfl⟩ : syracuseStep 2825999 = 4238999) B4238999
theorem B1679147 : Blo 742328 1679147 := bstep (se 1 (by rfl) ⟨1259360, by rfl⟩ : syracuseStep 1679147 = 2518721) B2518721
theorem B45817649 : Blo 742328 45817649 := bstep (se 2 (by rfl) ⟨17181618, by rfl⟩ : syracuseStep 45817649 = 34363237) B34363237
theorem B8462231 : Blo 742328 8462231 := bstep (se 1 (by rfl) ⟨6346673, by rfl⟩ : syracuseStep 8462231 = 12693347) B12693347
theorem B1253495 : Blo 742328 1253495 := bstep (se 1 (by rfl) ⟨940121, by rfl⟩ : syracuseStep 1253495 = 1880243) B1880243
theorem B3776705 : Blo 742328 3776705 := bstep (se 2 (by rfl) ⟨1416264, by rfl⟩ : syracuseStep 3776705 = 2832529) B2832529
theorem B1253947 : Blo 742328 1253947 := bstep (se 1 (by rfl) ⟨940460, by rfl⟩ : syracuseStep 1253947 = 1880921) B1880921
theorem B1254089 : Blo 742328 1254089 := bstep (se 2 (by rfl) ⟨470283, by rfl⟩ : syracuseStep 1254089 = 940567) B940567
theorem B4530917 : Blo 742328 4530917 := bstep (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) B849547
theorem B4236083 : Blo 742328 4236083 := bstep (se 1 (by rfl) ⟨3177062, by rfl⟩ : syracuseStep 4236083 = 6354125) B6354125
theorem B795791 : Blo 742328 795791 := bstep (se 1 (by rfl) ⟨596843, by rfl⟩ : syracuseStep 795791 = 1193687) B1193687
theorem B1254791 : Blo 742328 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B894343 : Blo 742328 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B2827655 : Blo 742328 2827655 := bstep (se 1 (by rfl) ⟨2120741, by rfl⟩ : syracuseStep 2827655 = 4241483) B4241483
theorem B6366599 : Blo 742328 6366599 := bstep (se 1 (by rfl) ⟨4774949, by rfl⟩ : syracuseStep 6366599 = 9549899) B9549899
theorem B1451449 : Blo 742328 1451449 := bstep (se 2 (by rfl) ⟨544293, by rfl⟩ : syracuseStep 1451449 = 1088587) B1088587
theorem B3778001 : Blo 742328 3778001 := bstep (se 2 (by rfl) ⟨1416750, by rfl⟩ : syracuseStep 3778001 = 2833501) B2833501
theorem B4531913 : Blo 742328 4531913 := bstep (se 2 (by rfl) ⟨1699467, by rfl⟩ : syracuseStep 4531913 = 3398935) B3398935
theorem B5646347 : Blo 742328 5646347 := bstep (se 1 (by rfl) ⟨4234760, by rfl⟩ : syracuseStep 5646347 = 8469521) B8469521
theorem B1255439 : Blo 742328 1255439 := bstep (se 1 (by rfl) ⟨941579, by rfl⟩ : syracuseStep 1255439 = 1883159) B1883159
theorem B4237541 : Blo 742328 4237541 := bstep (se 4 (by rfl) ⟨397269, by rfl⟩ : syracuseStep 4237541 = 794539) B794539
theorem B1255979 : Blo 742328 1255979 := bstep (se 1 (by rfl) ⟨941984, by rfl⟩ : syracuseStep 1255979 = 1883969) B1883969
theorem B3812147 : Blo 742328 3812147 := bstep (se 1 (by rfl) ⟨2859110, by rfl⟩ : syracuseStep 3812147 = 5718221) B5718221
theorem B1256377 : Blo 742328 1256377 := bstep (se 2 (by rfl) ⟨471141, by rfl⟩ : syracuseStep 1256377 = 942283) B942283
theorem B1911737 : Blo 742328 1911737 := bstep (se 2 (by rfl) ⟨716901, by rfl⟩ : syracuseStep 1911737 = 1433803) B1433803
theorem B1879159 : Blo 742328 1879159 := bstep (se 1 (by rfl) ⟨1409369, by rfl⟩ : syracuseStep 1879159 = 2818739) B2818739
theorem B2829431 : Blo 742328 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B3583385 : Blo 742328 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B48344525 : Blo 742328 48344525 := bstep (se 3 (by rfl) ⟨9064598, by rfl⟩ : syracuseStep 48344525 = 18129197) B18129197
theorem B1879595 : Blo 742328 1879595 := bstep (se 1 (by rfl) ⟨1409696, by rfl⟩ : syracuseStep 1879595 = 2819393) B2819393
theorem B1257079 : Blo 742328 1257079 := bstep (se 1 (by rfl) ⟨942809, by rfl⟩ : syracuseStep 1257079 = 1885619) B1885619
theorem B1060553 : Blo 742328 1060553 := bstep (se 2 (by rfl) ⟨397707, by rfl⟩ : syracuseStep 1060553 = 795415) B795415
theorem B4534031 : Blo 742328 4534031 := bstep (se 1 (by rfl) ⟨3400523, by rfl⟩ : syracuseStep 4534031 = 6801047) B6801047
theorem B1257275 : Blo 742328 1257275 := bstep (se 1 (by rfl) ⟨942956, by rfl⟩ : syracuseStep 1257275 = 1885913) B1885913
theorem B2011027 : Blo 742328 2011027 := bstep (se 1 (by rfl) ⟨1508270, by rfl⟩ : syracuseStep 2011027 = 3016541) B3016541
theorem B5648291 : Blo 742328 5648291 := bstep (se 1 (by rfl) ⟨4236218, by rfl⟩ : syracuseStep 5648291 = 8472437) B8472437
theorem B7155773 : Blo 742328 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B2830403 : Blo 742328 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B8466605 : Blo 742328 8466605 := bstep (se 3 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 8466605 = 3174977) B3174977
theorem B1257673 : Blo 742328 1257673 := bstep (se 2 (by rfl) ⟨471627, by rfl⟩ : syracuseStep 1257673 = 943255) B943255
theorem B7156001 : Blo 742328 7156001 := bstep (se 2 (by rfl) ⟨2683500, by rfl⟩ : syracuseStep 7156001 = 5367001) B5367001
theorem B1880435 : Blo 742328 1880435 := bstep (se 1 (by rfl) ⟨1410326, by rfl⟩ : syracuseStep 1880435 = 2820653) B2820653
theorem B1880455 : Blo 742328 1880455 := bstep (se 1 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 1880455 = 2820683) B2820683
theorem B5353913 : Blo 742328 5353913 := bstep (se 2 (by rfl) ⟨2007717, by rfl⟩ : syracuseStep 5353913 = 4015435) B4015435
theorem B3584459 : Blo 742328 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B2830859 : Blo 742328 2830859 := bstep (se 1 (by rfl) ⟨2123144, by rfl⟩ : syracuseStep 2830859 = 4246289) B4246289
theorem B1061419 : Blo 742328 1061419 := bstep (se 1 (by rfl) ⟨796064, by rfl⟩ : syracuseStep 1061419 = 1592129) B1592129
theorem B6369911 : Blo 742328 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B1880729 : Blo 742328 1880729 := bstep (se 2 (by rfl) ⟨705273, by rfl⟩ : syracuseStep 1880729 = 1410547) B1410547
theorem B1880891 : Blo 742328 1880891 := bstep (se 1 (by rfl) ⟨1410668, by rfl⟩ : syracuseStep 1880891 = 2821337) B2821337
theorem B1258375 : Blo 742328 1258375 := bstep (se 1 (by rfl) ⟨943781, by rfl⟩ : syracuseStep 1258375 = 1887563) B1887563
theorem B27898805 : Blo 742328 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B1881103 : Blo 742328 1881103 := bstep (se 1 (by rfl) ⟨1410827, by rfl⟩ : syracuseStep 1881103 = 2821655) B2821655
theorem B1815671 : Blo 742328 1815671 := bstep (se 1 (by rfl) ⟨1361753, by rfl⟩ : syracuseStep 1815671 = 2723507) B2723507
theorem B1193231 : Blo 742328 1193231 := bstep (se 1 (by rfl) ⟨894923, by rfl⟩ : syracuseStep 1193231 = 1789847) B1789847
theorem B1881377 : Blo 742328 1881377 := bstep (se 2 (by rfl) ⟨705516, by rfl⟩ : syracuseStep 1881377 = 1411033) B1411033
theorem B1586567 : Blo 742328 1586567 := bstep (se 1 (by rfl) ⟨1189925, by rfl⟩ : syracuseStep 1586567 = 2379851) B2379851
theorem B4240775 : Blo 742328 4240775 := bstep (se 1 (by rfl) ⟨3180581, by rfl⟩ : syracuseStep 4240775 = 6361163) B6361163
theorem B1259023 : Blo 742328 1259023 := bstep (se 1 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 1259023 = 1888535) B1888535
theorem B4240957 : Blo 742328 4240957 := bstep (se 3 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 4240957 = 1590359) B1590359
theorem B1882379 : Blo 742328 1882379 := bstep (se 1 (by rfl) ⟨1411784, by rfl⟩ : syracuseStep 1882379 = 2823569) B2823569
theorem B5650721 : Blo 742328 5650721 := bstep (se 2 (by rfl) ⟨2119020, by rfl⟩ : syracuseStep 5650721 = 4238041) B4238041
theorem B1587575 : Blo 742328 1587575 := bstep (se 1 (by rfl) ⟨1190681, by rfl⟩ : syracuseStep 1587575 = 2381363) B2381363
theorem B1587755 : Blo 742328 1587755 := bstep (se 1 (by rfl) ⟨1190816, by rfl⟩ : syracuseStep 1587755 = 2381633) B2381633
theorem B2833015 : Blo 742328 2833015 := bstep (se 1 (by rfl) ⟨2124761, by rfl⟩ : syracuseStep 2833015 = 4249523) B4249523
theorem B4766465 : Blo 742328 4766465 := bstep (se 2 (by rfl) ⟨1787424, by rfl⟩ : syracuseStep 4766465 = 3574849) B3574849
theorem B1784695 : Blo 742328 1784695 := bstep (se 1 (by rfl) ⟨1338521, by rfl⟩ : syracuseStep 1784695 = 2677043) B2677043
theorem B2014087 : Blo 742328 2014087 := bstep (se 1 (by rfl) ⟨1510565, by rfl⟩ : syracuseStep 2014087 = 3021131) B3021131
theorem B3619729 : Blo 742328 3619729 := bstep (se 2 (by rfl) ⟨1357398, by rfl⟩ : syracuseStep 3619729 = 2714797) B2714797
theorem B1883027 : Blo 742328 1883027 := bstep (se 1 (by rfl) ⟨1412270, by rfl⟩ : syracuseStep 1883027 = 2824541) B2824541
theorem B2866067 : Blo 742328 2866067 := bstep (se 1 (by rfl) ⟨2149550, by rfl⟩ : syracuseStep 2866067 = 4299101) B4299101
theorem B4307921 : Blo 742328 4307921 := bstep (se 2 (by rfl) ⟨1615470, by rfl⟩ : syracuseStep 4307921 = 3230941) B3230941
theorem B8043581 : Blo 742328 8043581 := bstep (se 3 (by rfl) ⟨1508171, by rfl⟩ : syracuseStep 8043581 = 3016343) B3016343
theorem B2505815 : Blo 742328 2505815 := bstep (se 1 (by rfl) ⟨1879361, by rfl⟩ : syracuseStep 2505815 = 3758723) B3758723
theorem B1883321 : Blo 742328 1883321 := bstep (se 2 (by rfl) ⟨706245, by rfl⟩ : syracuseStep 1883321 = 1412491) B1412491
theorem B5651693 : Blo 742328 5651693 := bstep (se 3 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 5651693 = 2119385) B2119385
theorem B4242689 : Blo 742328 4242689 := bstep (se 2 (by rfl) ⟨1591008, by rfl⟩ : syracuseStep 4242689 = 3182017) B3182017
theorem B7257377 : Blo 742328 7257377 := bstep (se 2 (by rfl) ⟨2721516, by rfl⟩ : syracuseStep 7257377 = 5443033) B5443033
theorem B2506301 : Blo 742328 2506301 := bstep (se 3 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 2506301 = 939863) B939863
theorem B1884019 : Blo 742328 1884019 := bstep (se 1 (by rfl) ⟨1413014, by rfl⟩ : syracuseStep 1884019 = 2826029) B2826029
theorem B1884161 : Blo 742328 1884161 := bstep (se 2 (by rfl) ⟨706560, by rfl⟩ : syracuseStep 1884161 = 1413121) B1413121
theorem B835591 : Blo 742328 835591 := bstep (se 1 (by rfl) ⟨626693, by rfl⟩ : syracuseStep 835591 = 1253387) B1253387
theorem B1589395 : Blo 742328 1589395 := bstep (se 1 (by rfl) ⟨1192046, by rfl⟩ : syracuseStep 1589395 = 2384093) B2384093
theorem B6439085 : Blo 742328 6439085 := bstep (se 3 (by rfl) ⟨1207328, by rfl⟩ : syracuseStep 6439085 = 2414657) B2414657
theorem B835771 : Blo 742328 835771 := bstep (se 1 (by rfl) ⟨626828, by rfl⟩ : syracuseStep 835771 = 1253657) B1253657
theorem B1884617 : Blo 742328 1884617 := bstep (se 2 (by rfl) ⟨706731, by rfl⟩ : syracuseStep 1884617 = 1413463) B1413463
theorem B1786483 : Blo 742328 1786483 := bstep (se 1 (by rfl) ⟨1339862, by rfl⟩ : syracuseStep 1786483 = 2679725) B2679725
theorem B836239 : Blo 742328 836239 := bstep (se 1 (by rfl) ⟨627179, by rfl⟩ : syracuseStep 836239 = 1254359) B1254359
theorem B1884971 : Blo 742328 1884971 := bstep (se 1 (by rfl) ⟨1413728, by rfl⟩ : syracuseStep 1884971 = 2827457) B2827457
theorem B2114363 : Blo 742328 2114363 := bstep (se 1 (by rfl) ⟨1585772, by rfl⟩ : syracuseStep 2114363 = 3171545) B3171545
theorem B2114419 : Blo 742328 2114419 := bstep (se 1 (by rfl) ⟨1585814, by rfl⟩ : syracuseStep 2114419 = 3171629) B3171629
theorem B803719 : Blo 742328 803719 := bstep (se 1 (by rfl) ⟨602789, by rfl⟩ : syracuseStep 803719 = 1205579) B1205579
theorem B2507705 : Blo 742328 2507705 := bstep (se 2 (by rfl) ⟨940389, by rfl⟩ : syracuseStep 2507705 = 1880779) B1880779
theorem B5653637 : Blo 742328 5653637 := bstep (se 4 (by rfl) ⟨530028, by rfl⟩ : syracuseStep 5653637 = 1060057) B1060057
theorem B836743 : Blo 742328 836743 := bstep (se 1 (by rfl) ⟨627557, by rfl⟩ : syracuseStep 836743 = 1255115) B1255115
theorem B2114761 : Blo 742328 2114761 := bstep (se 2 (by rfl) ⟨793035, by rfl⟩ : syracuseStep 2114761 = 1586071) B1586071
theorem B3818753 : Blo 742328 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B836923 : Blo 742328 836923 := bstep (se 1 (by rfl) ⟨627692, by rfl⟩ : syracuseStep 836923 = 1255385) B1255385
theorem B9684355 : Blo 742328 9684355 := bstep (se 1 (by rfl) ⟨7263266, by rfl⟩ : syracuseStep 9684355 = 14526533) B14526533
theorem B2508299 : Blo 742328 2508299 := bstep (se 1 (by rfl) ⟨1881224, by rfl⟩ : syracuseStep 2508299 = 3762449) B3762449
theorem B2508407 : Blo 742328 2508407 := bstep (se 1 (by rfl) ⟨1881305, by rfl⟩ : syracuseStep 2508407 = 3762611) B3762611
theorem B1885963 : Blo 742328 1885963 := bstep (se 1 (by rfl) ⟨1414472, by rfl⟩ : syracuseStep 1885963 = 2828945) B2828945
theorem B837391 : Blo 742328 837391 := bstep (se 1 (by rfl) ⟨628043, by rfl⟩ : syracuseStep 837391 = 1256087) B1256087
theorem B4015909 : Blo 742328 4015909 := bstep (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) B752983
theorem B2148211 : Blo 742328 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B1886105 : Blo 742328 1886105 := bstep (se 2 (by rfl) ⟨707289, by rfl⟩ : syracuseStep 1886105 = 1414579) B1414579
theorem B1886267 : Blo 742328 1886267 := bstep (se 1 (by rfl) ⟨1414700, by rfl⟩ : syracuseStep 1886267 = 2829401) B2829401
theorem B2509001 : Blo 742328 2509001 := bstep (se 2 (by rfl) ⟨940875, by rfl⟩ : syracuseStep 2509001 = 1881751) B1881751
theorem B4770029 : Blo 742328 4770029 := bstep (se 3 (by rfl) ⟨894380, by rfl⟩ : syracuseStep 4770029 = 1788761) B1788761
theorem B837895 : Blo 742328 837895 := bstep (se 1 (by rfl) ⟨628421, by rfl⟩ : syracuseStep 837895 = 1256843) B1256843
theorem B16107923 : Blo 742328 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B1886611 : Blo 742328 1886611 := bstep (se 1 (by rfl) ⟨1414958, by rfl⟩ : syracuseStep 1886611 = 2829917) B2829917
theorem B838075 : Blo 742328 838075 := bstep (se 1 (by rfl) ⟨628556, by rfl⟩ : syracuseStep 838075 = 1257113) B1257113
theorem B1886753 : Blo 742328 1886753 := bstep (se 2 (by rfl) ⟨707532, by rfl⟩ : syracuseStep 1886753 = 1415065) B1415065
theorem B1788617 : Blo 742328 1788617 := bstep (se 2 (by rfl) ⟨670731, by rfl⟩ : syracuseStep 1788617 = 1341463) B1341463
theorem B28658447 : Blo 742328 28658447 := bstep (se 1 (by rfl) ⟨21493835, by rfl⟩ : syracuseStep 28658447 = 42987671) B42987671
theorem B4016947 : Blo 742328 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B2509703 : Blo 742328 2509703 := bstep (se 1 (by rfl) ⟨1882277, by rfl⟩ : syracuseStep 2509703 = 3764555) B3764555
theorem B838543 : Blo 742328 838543 := bstep (se 1 (by rfl) ⟨628907, by rfl⟩ : syracuseStep 838543 = 1257815) B1257815
theorem B2510081 : Blo 742328 2510081 := bstep (se 2 (by rfl) ⟨941280, by rfl⟩ : syracuseStep 2510081 = 1882561) B1882561
theorem B2116925 : Blo 742328 2116925 := bstep (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) B793847
theorem B1133897 : Blo 742328 1133897 := bstep (se 2 (by rfl) ⟨425211, by rfl⟩ : syracuseStep 1133897 = 850423) B850423
theorem B839047 : Blo 742328 839047 := bstep (se 1 (by rfl) ⟨629285, by rfl⟩ : syracuseStep 839047 = 1258571) B1258571
theorem B2182601 : Blo 742328 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B1887745 : Blo 742328 1887745 := bstep (se 2 (by rfl) ⟨707904, by rfl⟩ : syracuseStep 1887745 = 1415809) B1415809
theorem B5656067 : Blo 742328 5656067 := bstep (se 1 (by rfl) ⟨4242050, by rfl⟩ : syracuseStep 5656067 = 8484101) B8484101
theorem B4247063 : Blo 742328 4247063 := bstep (se 1 (by rfl) ⟨3185297, by rfl⟩ : syracuseStep 4247063 = 6370595) B6370595
theorem B2117153 : Blo 742328 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B839227 : Blo 742328 839227 := bstep (se 1 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 839227 = 1258841) B1258841
theorem B1593017 : Blo 742328 1593017 := bstep (se 2 (by rfl) ⟨597381, by rfl⟩ : syracuseStep 1593017 = 1194763) B1194763
theorem B2117495 : Blo 742328 2117495 := bstep (se 1 (by rfl) ⟨1588121, by rfl⟩ : syracuseStep 2117495 = 3176243) B3176243
theorem B2510891 : Blo 742328 2510891 := bstep (se 1 (by rfl) ⟨1883168, by rfl⟩ : syracuseStep 2510891 = 3766337) B3766337
theorem B1790039 : Blo 742328 1790039 := bstep (se 1 (by rfl) ⟨1342529, by rfl⟩ : syracuseStep 1790039 = 2685059) B2685059
theorem B1888343 : Blo 742328 1888343 := bstep (se 1 (by rfl) ⟨1416257, by rfl⟩ : syracuseStep 1888343 = 2832515) B2832515
theorem B1888555 : Blo 742328 1888555 := bstep (se 1 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 1888555 = 2832833) B2832833
theorem B4772155 : Blo 742328 4772155 := bstep (se 1 (by rfl) ⟨3579116, by rfl⟩ : syracuseStep 4772155 = 7158233) B7158233
theorem B1888697 : Blo 742328 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B8475353 : Blo 742328 8475353 := bstep (se 2 (by rfl) ⟨3178257, by rfl⟩ : syracuseStep 8475353 = 6356515) B6356515
theorem B2544385 : Blo 742328 2544385 := bstep (se 2 (by rfl) ⟨954144, by rfl⟩ : syracuseStep 2544385 = 1908289) B1908289
theorem B742331 : Blo 742328 742331 := bstep (se 1 (by rfl) ⟨556748, by rfl⟩ : syracuseStep 742331 = 1113497) B1113497
theorem B742407 : Blo 742328 742407 := bstep (se 1 (by rfl) ⟨556805, by rfl⟩ : syracuseStep 742407 = 1113611) B1113611
theorem B742415 : Blo 742328 742415 := bstep (se 1 (by rfl) ⟨556811, by rfl⟩ : syracuseStep 742415 = 1113623) B1113623
theorem B742459 : Blo 742328 742459 := bstep (se 1 (by rfl) ⟨556844, by rfl⟩ : syracuseStep 742459 = 1113689) B1113689
theorem B742535 : Blo 742328 742535 := bstep (se 1 (by rfl) ⟨556901, by rfl⟩ : syracuseStep 742535 = 1113803) B1113803
theorem B742543 : Blo 742328 742543 := bstep (se 1 (by rfl) ⟨556907, by rfl⟩ : syracuseStep 742543 = 1113815) B1113815
theorem B742587 : Blo 742328 742587 := bstep (se 1 (by rfl) ⟨556940, by rfl⟩ : syracuseStep 742587 = 1113881) B1113881
theorem B742663 : Blo 742328 742663 := bstep (se 1 (by rfl) ⟨556997, by rfl⟩ : syracuseStep 742663 = 1113995) B1113995
theorem B742671 : Blo 742328 742671 := bstep (se 1 (by rfl) ⟨557003, by rfl⟩ : syracuseStep 742671 = 1114007) B1114007
theorem B1004843 : Blo 742328 1004843 := bstep (se 1 (by rfl) ⟨753632, by rfl⟩ : syracuseStep 1004843 = 1507265) B1507265
theorem B742715 : Blo 742328 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B2512187 : Blo 742328 2512187 := bstep (se 1 (by rfl) ⟨1884140, by rfl⟩ : syracuseStep 2512187 = 3768281) B3768281
theorem B742791 : Blo 742328 742791 := bstep (se 1 (by rfl) ⟨557093, by rfl⟩ : syracuseStep 742791 = 1114187) B1114187
theorem B3822983 : Blo 742328 3822983 := bstep (se 1 (by rfl) ⟨2867237, by rfl⟩ : syracuseStep 3822983 = 5734475) B5734475
theorem B742799 : Blo 742328 742799 := bstep (se 1 (by rfl) ⟨557099, by rfl⟩ : syracuseStep 742799 = 1114199) B1114199
theorem B742843 : Blo 742328 742843 := bstep (se 1 (by rfl) ⟨557132, by rfl⟩ : syracuseStep 742843 = 1114265) B1114265
theorem B6772177 : Blo 742328 6772177 := bstep (se 2 (by rfl) ⟨2539566, by rfl⟩ : syracuseStep 6772177 = 5079133) B5079133
theorem B742919 : Blo 742328 742919 := bstep (se 1 (by rfl) ⟨557189, by rfl⟩ : syracuseStep 742919 = 1114379) B1114379
theorem B2676235 : Blo 742328 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B742927 : Blo 742328 742927 := bstep (se 1 (by rfl) ⟨557195, by rfl⟩ : syracuseStep 742927 = 1114391) B1114391
theorem B742971 : Blo 742328 742971 := bstep (se 1 (by rfl) ⟨557228, by rfl⟩ : syracuseStep 742971 = 1114457) B1114457
theorem B743047 : Blo 742328 743047 := bstep (se 1 (by rfl) ⟨557285, by rfl⟩ : syracuseStep 743047 = 1114571) B1114571
theorem B743055 : Blo 742328 743055 := bstep (se 1 (by rfl) ⟨557291, by rfl⟩ : syracuseStep 743055 = 1114583) B1114583
theorem B939691 : Blo 742328 939691 := bstep (se 1 (by rfl) ⟨704768, by rfl⟩ : syracuseStep 939691 = 1409537) B1409537
theorem B743099 : Blo 742328 743099 := bstep (se 1 (by rfl) ⟨557324, by rfl⟩ : syracuseStep 743099 = 1114649) B1114649
theorem B743175 : Blo 742328 743175 := bstep (se 1 (by rfl) ⟨557381, by rfl⟩ : syracuseStep 743175 = 1114763) B1114763
theorem B743183 : Blo 742328 743183 := bstep (se 1 (by rfl) ⟨557387, by rfl⟩ : syracuseStep 743183 = 1114775) B1114775
theorem B2512673 : Blo 742328 2512673 := bstep (se 2 (by rfl) ⟨942252, by rfl⟩ : syracuseStep 2512673 = 1884505) B1884505
theorem B743227 : Blo 742328 743227 := bstep (se 1 (by rfl) ⟨557420, by rfl⟩ : syracuseStep 743227 = 1114841) B1114841
theorem B743303 : Blo 742328 743303 := bstep (se 1 (by rfl) ⟨557477, by rfl⟩ : syracuseStep 743303 = 1114955) B1114955
theorem B939919 : Blo 742328 939919 := bstep (se 1 (by rfl) ⟨704939, by rfl⟩ : syracuseStep 939919 = 1409879) B1409879
theorem B743311 : Blo 742328 743311 := bstep (se 1 (by rfl) ⟨557483, by rfl⟩ : syracuseStep 743311 = 1114967) B1114967
theorem B743355 : Blo 742328 743355 := bstep (se 1 (by rfl) ⟨557516, by rfl⟩ : syracuseStep 743355 = 1115033) B1115033
theorem B743431 : Blo 742328 743431 := bstep (se 1 (by rfl) ⟨557573, by rfl⟩ : syracuseStep 743431 = 1115147) B1115147
theorem B743439 : Blo 742328 743439 := bstep (se 1 (by rfl) ⟨557579, by rfl⟩ : syracuseStep 743439 = 1115159) B1115159
theorem B743483 : Blo 742328 743483 := bstep (se 1 (by rfl) ⟨557612, by rfl⟩ : syracuseStep 743483 = 1115225) B1115225
theorem B743559 : Blo 742328 743559 := bstep (se 1 (by rfl) ⟨557669, by rfl⟩ : syracuseStep 743559 = 1115339) B1115339
theorem B743567 : Blo 742328 743567 := bstep (se 1 (by rfl) ⟨557675, by rfl⟩ : syracuseStep 743567 = 1115351) B1115351
theorem B1792153 : Blo 742328 1792153 := bstep (se 2 (by rfl) ⟨672057, by rfl⟩ : syracuseStep 1792153 = 1344115) B1344115
theorem B743611 : Blo 742328 743611 := bstep (se 1 (by rfl) ⟨557708, by rfl⟩ : syracuseStep 743611 = 1115417) B1115417
theorem B743687 : Blo 742328 743687 := bstep (se 1 (by rfl) ⟨557765, by rfl⟩ : syracuseStep 743687 = 1115531) B1115531
theorem B743695 : Blo 742328 743695 := bstep (se 1 (by rfl) ⟨557771, by rfl⟩ : syracuseStep 743695 = 1115543) B1115543
theorem B743739 : Blo 742328 743739 := bstep (se 1 (by rfl) ⟨557804, by rfl⟩ : syracuseStep 743739 = 1115609) B1115609
theorem B2120023 : Blo 742328 2120023 := bstep (se 1 (by rfl) ⟨1590017, by rfl⟩ : syracuseStep 2120023 = 3180035) B3180035
theorem B2513267 : Blo 742328 2513267 := bstep (se 1 (by rfl) ⟨1884950, by rfl⟩ : syracuseStep 2513267 = 3769901) B3769901
theorem B743815 : Blo 742328 743815 := bstep (se 1 (by rfl) ⟨557861, by rfl⟩ : syracuseStep 743815 = 1115723) B1115723
theorem B743823 : Blo 742328 743823 := bstep (se 1 (by rfl) ⟨557867, by rfl⟩ : syracuseStep 743823 = 1115735) B1115735
theorem B1005967 : Blo 742328 1005967 := bstep (se 1 (by rfl) ⟨754475, by rfl⟩ : syracuseStep 1005967 = 1508951) B1508951
theorem B7625107 : Blo 742328 7625107 := bstep (se 1 (by rfl) ⟨5718830, by rfl⟩ : syracuseStep 7625107 = 11437661) B11437661
theorem B9066937 : Blo 742328 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B743867 : Blo 742328 743867 := bstep (se 1 (by rfl) ⟨557900, by rfl⟩ : syracuseStep 743867 = 1115801) B1115801
theorem B743943 : Blo 742328 743943 := bstep (se 1 (by rfl) ⟨557957, by rfl⟩ : syracuseStep 743943 = 1115915) B1115915
theorem B743951 : Blo 742328 743951 := bstep (se 1 (by rfl) ⟨557963, by rfl⟩ : syracuseStep 743951 = 1115927) B1115927
theorem B743995 : Blo 742328 743995 := bstep (se 1 (by rfl) ⟨557996, by rfl⟩ : syracuseStep 743995 = 1115993) B1115993
theorem B2120251 : Blo 742328 2120251 := bstep (se 1 (by rfl) ⟨1590188, by rfl⟩ : syracuseStep 2120251 = 3180377) B3180377
theorem B940663 : Blo 742328 940663 := bstep (se 1 (by rfl) ⟨705497, by rfl⟩ : syracuseStep 940663 = 1410995) B1410995
theorem B4250231 : Blo 742328 4250231 := bstep (se 1 (by rfl) ⟨3187673, by rfl⟩ : syracuseStep 4250231 = 6375347) B6375347
theorem B744071 : Blo 742328 744071 := bstep (se 1 (by rfl) ⟨558053, by rfl⟩ : syracuseStep 744071 = 1116107) B1116107
theorem B744079 : Blo 742328 744079 := bstep (se 1 (by rfl) ⟨558059, by rfl⟩ : syracuseStep 744079 = 1116119) B1116119
theorem B2120377 : Blo 742328 2120377 := bstep (se 2 (by rfl) ⟨795141, by rfl⟩ : syracuseStep 2120377 = 1590283) B1590283
theorem B744123 : Blo 742328 744123 := bstep (se 1 (by rfl) ⟨558092, by rfl⟩ : syracuseStep 744123 = 1116185) B1116185
theorem B744199 : Blo 742328 744199 := bstep (se 1 (by rfl) ⟨558149, by rfl⟩ : syracuseStep 744199 = 1116299) B1116299
theorem B744207 : Blo 742328 744207 := bstep (se 1 (by rfl) ⟨558155, by rfl⟩ : syracuseStep 744207 = 1116311) B1116311
theorem B744251 : Blo 742328 744251 := bstep (se 1 (by rfl) ⟨558188, by rfl⟩ : syracuseStep 744251 = 1116377) B1116377
theorem B744327 : Blo 742328 744327 := bstep (se 1 (by rfl) ⟨558245, by rfl⟩ : syracuseStep 744327 = 1116491) B1116491
theorem B744335 : Blo 742328 744335 := bstep (se 1 (by rfl) ⟨558251, by rfl⟩ : syracuseStep 744335 = 1116503) B1116503
theorem B940987 : Blo 742328 940987 := bstep (se 1 (by rfl) ⟨705740, by rfl⟩ : syracuseStep 940987 = 1411481) B1411481
theorem B744379 : Blo 742328 744379 := bstep (se 1 (by rfl) ⟨558284, by rfl⟩ : syracuseStep 744379 = 1116569) B1116569
theorem B4578257 : Blo 742328 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B744455 : Blo 742328 744455 := bstep (se 1 (by rfl) ⟨558341, by rfl⟩ : syracuseStep 744455 = 1116683) B1116683
theorem B744463 : Blo 742328 744463 := bstep (se 1 (by rfl) ⟨558347, by rfl⟩ : syracuseStep 744463 = 1116695) B1116695
theorem B744507 : Blo 742328 744507 := bstep (se 1 (by rfl) ⟨558380, by rfl⟩ : syracuseStep 744507 = 1116761) B1116761
theorem B744583 : Blo 742328 744583 := bstep (se 1 (by rfl) ⟨558437, by rfl⟩ : syracuseStep 744583 = 1116875) B1116875
theorem B744591 : Blo 742328 744591 := bstep (se 1 (by rfl) ⟨558443, by rfl⟩ : syracuseStep 744591 = 1116887) B1116887
theorem B744635 : Blo 742328 744635 := bstep (se 1 (by rfl) ⟨558476, by rfl⟩ : syracuseStep 744635 = 1116953) B1116953
theorem B744711 : Blo 742328 744711 := bstep (se 1 (by rfl) ⟨558533, by rfl⟩ : syracuseStep 744711 = 1117067) B1117067
theorem B744719 : Blo 742328 744719 := bstep (se 1 (by rfl) ⟨558539, by rfl⟩ : syracuseStep 744719 = 1117079) B1117079
theorem B744763 : Blo 742328 744763 := bstep (se 1 (by rfl) ⟨558572, by rfl⟩ : syracuseStep 744763 = 1117145) B1117145
theorem B744839 : Blo 742328 744839 := bstep (se 1 (by rfl) ⟨558629, by rfl⟩ : syracuseStep 744839 = 1117259) B1117259
theorem B744847 : Blo 742328 744847 := bstep (se 1 (by rfl) ⟨558635, by rfl⟩ : syracuseStep 744847 = 1117271) B1117271
theorem B941483 : Blo 742328 941483 := bstep (se 1 (by rfl) ⟨706112, by rfl⟩ : syracuseStep 941483 = 1412225) B1412225
theorem B744891 : Blo 742328 744891 := bstep (se 1 (by rfl) ⟨558668, by rfl⟩ : syracuseStep 744891 = 1117337) B1117337
theorem B744967 : Blo 742328 744967 := bstep (se 1 (by rfl) ⟨558725, by rfl⟩ : syracuseStep 744967 = 1117451) B1117451
theorem B744975 : Blo 742328 744975 := bstep (se 1 (by rfl) ⟨558731, by rfl⟩ : syracuseStep 744975 = 1117463) B1117463
theorem B745019 : Blo 742328 745019 := bstep (se 1 (by rfl) ⟨558764, by rfl⟩ : syracuseStep 745019 = 1117529) B1117529
theorem B745095 : Blo 742328 745095 := bstep (se 1 (by rfl) ⟨558821, by rfl⟩ : syracuseStep 745095 = 1117643) B1117643
theorem B745103 : Blo 742328 745103 := bstep (se 1 (by rfl) ⟨558827, by rfl⟩ : syracuseStep 745103 = 1117655) B1117655
theorem B745147 : Blo 742328 745147 := bstep (se 1 (by rfl) ⟨558860, by rfl⟩ : syracuseStep 745147 = 1117721) B1117721
theorem B11460325 : Blo 742328 11460325 := bstep (se 4 (by rfl) ⟨1074405, by rfl⟩ : syracuseStep 11460325 = 2148811) B2148811
theorem B745223 : Blo 742328 745223 := bstep (se 1 (by rfl) ⟨558917, by rfl⟩ : syracuseStep 745223 = 1117835) B1117835
theorem B745231 : Blo 742328 745231 := bstep (se 1 (by rfl) ⟨558923, by rfl⟩ : syracuseStep 745231 = 1117847) B1117847
theorem B745275 : Blo 742328 745275 := bstep (se 1 (by rfl) ⟨558956, by rfl⟩ : syracuseStep 745275 = 1117913) B1117913
theorem B941959 : Blo 742328 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B745351 : Blo 742328 745351 := bstep (se 1 (by rfl) ⟨559013, by rfl⟩ : syracuseStep 745351 = 1118027) B1118027
theorem B745359 : Blo 742328 745359 := bstep (se 1 (by rfl) ⟨559019, by rfl⟩ : syracuseStep 745359 = 1118039) B1118039
theorem B3760019 : Blo 742328 3760019 := bstep (se 1 (by rfl) ⟨2820014, by rfl⟩ : syracuseStep 3760019 = 5640029) B5640029
theorem B745403 : Blo 742328 745403 := bstep (se 1 (by rfl) ⟨559052, by rfl⟩ : syracuseStep 745403 = 1118105) B1118105
theorem B745479 : Blo 742328 745479 := bstep (se 1 (by rfl) ⟨559109, by rfl⟩ : syracuseStep 745479 = 1118219) B1118219
theorem B745487 : Blo 742328 745487 := bstep (se 1 (by rfl) ⟨559115, by rfl⟩ : syracuseStep 745487 = 1118231) B1118231
theorem B745531 : Blo 742328 745531 := bstep (se 1 (by rfl) ⟨559148, by rfl⟩ : syracuseStep 745531 = 1118297) B1118297
theorem B27091037 : Blo 742328 27091037 := bstep (se 3 (by rfl) ⟨5079569, by rfl⟩ : syracuseStep 27091037 = 10159139) B10159139
theorem B745607 : Blo 742328 745607 := bstep (se 1 (by rfl) ⟨559205, by rfl⟩ : syracuseStep 745607 = 1118411) B1118411
theorem B745615 : Blo 742328 745615 := bstep (se 1 (by rfl) ⟨559211, by rfl⟩ : syracuseStep 745615 = 1118423) B1118423
theorem B745659 : Blo 742328 745659 := bstep (se 1 (by rfl) ⟨559244, by rfl⟩ : syracuseStep 745659 = 1118489) B1118489
theorem B745735 : Blo 742328 745735 := bstep (se 1 (by rfl) ⟨559301, by rfl⟩ : syracuseStep 745735 = 1118603) B1118603
theorem B745743 : Blo 742328 745743 := bstep (se 1 (by rfl) ⟨559307, by rfl⟩ : syracuseStep 745743 = 1118615) B1118615
theorem B745787 : Blo 742328 745787 := bstep (se 1 (by rfl) ⟨559340, by rfl⟩ : syracuseStep 745787 = 1118681) B1118681
theorem B942455 : Blo 742328 942455 := bstep (se 1 (by rfl) ⟨706841, by rfl⟩ : syracuseStep 942455 = 1413683) B1413683
theorem B745863 : Blo 742328 745863 := bstep (se 1 (by rfl) ⟨559397, by rfl⟩ : syracuseStep 745863 = 1118795) B1118795
theorem B745871 : Blo 742328 745871 := bstep (se 1 (by rfl) ⟨559403, by rfl⟩ : syracuseStep 745871 = 1118807) B1118807
theorem B745915 : Blo 742328 745915 := bstep (se 1 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 745915 = 1118873) B1118873
theorem B745991 : Blo 742328 745991 := bstep (se 1 (by rfl) ⟨559493, by rfl⟩ : syracuseStep 745991 = 1118987) B1118987
theorem B942607 : Blo 742328 942607 := bstep (se 1 (by rfl) ⟨706955, by rfl⟩ : syracuseStep 942607 = 1413911) B1413911
theorem B745999 : Blo 742328 745999 := bstep (se 1 (by rfl) ⟨559499, by rfl⟩ : syracuseStep 745999 = 1118999) B1118999
theorem B746043 : Blo 742328 746043 := bstep (se 1 (by rfl) ⟨559532, by rfl⟩ : syracuseStep 746043 = 1119065) B1119065
theorem B2122301 : Blo 742328 2122301 := bstep (se 3 (by rfl) ⟨397931, by rfl⟩ : syracuseStep 2122301 = 795863) B795863
theorem B746119 : Blo 742328 746119 := bstep (se 1 (by rfl) ⟨559589, by rfl⟩ : syracuseStep 746119 = 1119179) B1119179
theorem B746127 : Blo 742328 746127 := bstep (se 1 (by rfl) ⟨559595, by rfl⟩ : syracuseStep 746127 = 1119191) B1119191
theorem B942779 : Blo 742328 942779 := bstep (se 1 (by rfl) ⟨707084, by rfl⟩ : syracuseStep 942779 = 1414169) B1414169
theorem B746171 : Blo 742328 746171 := bstep (se 1 (by rfl) ⟨559628, by rfl⟩ : syracuseStep 746171 = 1119257) B1119257
theorem B5661413 : Blo 742328 5661413 := bstep (se 4 (by rfl) ⟨530757, by rfl⟩ : syracuseStep 5661413 = 1061515) B1061515
theorem B746247 : Blo 742328 746247 := bstep (se 1 (by rfl) ⟨559685, by rfl⟩ : syracuseStep 746247 = 1119371) B1119371
theorem B746255 : Blo 742328 746255 := bstep (se 1 (by rfl) ⟨559691, by rfl⟩ : syracuseStep 746255 = 1119383) B1119383
theorem B746299 : Blo 742328 746299 := bstep (se 1 (by rfl) ⟨559724, by rfl⟩ : syracuseStep 746299 = 1119449) B1119449
theorem B4023175 : Blo 742328 4023175 := bstep (se 1 (by rfl) ⟨3017381, by rfl⟩ : syracuseStep 4023175 = 6034763) B6034763
theorem B2515859 : Blo 742328 2515859 := bstep (se 1 (by rfl) ⟨1886894, by rfl⟩ : syracuseStep 2515859 = 3773789) B3773789
theorem B3171869 : Blo 742328 3171869 := bstep (se 3 (by rfl) ⟨594725, by rfl⟩ : syracuseStep 3171869 = 1189451) B1189451
theorem B2123293 : Blo 742328 2123293 := bstep (se 3 (by rfl) ⟨398117, by rfl⟩ : syracuseStep 2123293 = 796235) B796235
theorem B4515371 : Blo 742328 4515371 := bstep (se 1 (by rfl) ⟨3386528, by rfl⟩ : syracuseStep 4515371 = 6773057) B6773057
theorem B2451005 : Blo 742328 2451005 := bstep (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) B919127
theorem B943751 : Blo 742328 943751 := bstep (se 1 (by rfl) ⟨707813, by rfl⟩ : syracuseStep 943751 = 1415627) B1415627
theorem B2385949 : Blo 742328 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B3172553 : Blo 742328 3172553 := bstep (se 2 (by rfl) ⟨1189707, by rfl⟩ : syracuseStep 3172553 = 2379415) B2379415
theorem B2517263 : Blo 742328 2517263 := bstep (se 1 (by rfl) ⟨1887947, by rfl⟩ : syracuseStep 2517263 = 3775895) B3775895
theorem B944399 : Blo 742328 944399 := bstep (se 1 (by rfl) ⟨708299, by rfl⟩ : syracuseStep 944399 = 1416599) B1416599
theorem B5499283 : Blo 742328 5499283 := bstep (se 1 (by rfl) ⟨4124462, by rfl⟩ : syracuseStep 5499283 = 8248925) B8248925
theorem B7137821 : Blo 742328 7137821 := bstep (se 3 (by rfl) ⟨1338341, by rfl⟩ : syracuseStep 7137821 = 2676683) B2676683
theorem B2714141 : Blo 742328 2714141 := bstep (se 3 (by rfl) ⟨508901, by rfl⟩ : syracuseStep 2714141 = 1017803) B1017803
theorem B2517533 : Blo 742328 2517533 := bstep (se 3 (by rfl) ⟨472037, by rfl⟩ : syracuseStep 2517533 = 944075) B944075
theorem B10742543 : Blo 742328 10742543 := bstep (se 1 (by rfl) ⟨8056907, by rfl⟩ : syracuseStep 10742543 = 16113815) B16113815
theorem B3763097 : Blo 742328 3763097 := bstep (se 2 (by rfl) ⟨1411161, by rfl⟩ : syracuseStep 3763097 = 2822323) B2822323
theorem B2125241 : Blo 742328 2125241 := bstep (se 2 (by rfl) ⟨796965, by rfl⟩ : syracuseStep 2125241 = 1593931) B1593931
theorem B4779485 : Blo 742328 4779485 := bstep (se 3 (by rfl) ⟨896153, by rfl⟩ : syracuseStep 4779485 = 1792307) B1792307
theorem B8056385 : Blo 742328 8056385 := bstep (se 2 (by rfl) ⟨3021144, by rfl⟩ : syracuseStep 8056385 = 6042289) B6042289
theorem B4779587 : Blo 742328 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B1076923 : Blo 742328 1076923 := bstep (se 1 (by rfl) ⟨807692, by rfl⟩ : syracuseStep 1076923 = 1615385) B1615385
theorem B7171841 : Blo 742328 7171841 := bstep (se 2 (by rfl) ⟨2689440, by rfl⟩ : syracuseStep 7171841 = 5378881) B5378881
theorem B7139087 : Blo 742328 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B7171993 : Blo 742328 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B3174329 : Blo 742328 3174329 := bstep (se 2 (by rfl) ⟨1190373, by rfl⟩ : syracuseStep 3174329 = 2380747) B2380747
theorem B2682809 : Blo 742328 2682809 := bstep (se 2 (by rfl) ⟨1006053, by rfl⟩ : syracuseStep 2682809 = 2012107) B2012107
theorem B2387897 : Blo 742328 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B2388359 : Blo 742328 2388359 := bstep (se 1 (by rfl) ⟨1791269, by rfl⟩ : syracuseStep 2388359 = 3582539) B3582539
theorem B4026809 : Blo 742328 4026809 := bstep (se 2 (by rfl) ⟨1510053, by rfl⟩ : syracuseStep 4026809 = 3020107) B3020107
theorem B6025681 : Blo 742328 6025681 := bstep (se 2 (by rfl) ⟨2259630, by rfl⟩ : syracuseStep 6025681 = 4519261) B4519261
theorem B3175661 : Blo 742328 3175661 := bstep (se 3 (by rfl) ⟨595436, by rfl⟩ : syracuseStep 3175661 = 1190873) B1190873
theorem B3765689 : Blo 742328 3765689 := bstep (se 2 (by rfl) ⟨1412133, by rfl⟩ : syracuseStep 3765689 = 2824267) B2824267
theorem B3176003 : Blo 742328 3176003 := bstep (se 1 (by rfl) ⟨2382002, by rfl⟩ : syracuseStep 3176003 = 4764005) B4764005
theorem B1701577 : Blo 742328 1701577 := bstep (se 2 (by rfl) ⟨638091, by rfl⟩ : syracuseStep 1701577 = 1276183) B1276183
theorem B7239917 : Blo 742328 7239917 := bstep (se 3 (by rfl) ⟨1357484, by rfl⟩ : syracuseStep 7239917 = 2714969) B2714969
theorem B15464945 : Blo 742328 15464945 := bstep (se 2 (by rfl) ⟨5799354, by rfl⟩ : syracuseStep 15464945 = 11598709) B11598709
theorem B7240195 : Blo 742328 7240195 := bstep (se 1 (by rfl) ⟨5430146, by rfl⟩ : syracuseStep 7240195 = 10860293) B10860293
theorem B981623 : Blo 742328 981623 := bstep (se 1 (by rfl) ⟨736217, by rfl⟩ : syracuseStep 981623 = 1472435) B1472435
theorem B3766985 : Blo 742328 3766985 := bstep (se 2 (by rfl) ⟨1412619, by rfl⟩ : syracuseStep 3766985 = 2825239) B2825239
theorem B6454333 : Blo 742328 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B1670291 : Blo 742328 1670291 := bstep (se 1 (by rfl) ⟨1252718, by rfl⟩ : syracuseStep 1670291 = 2505437) B2505437
theorem B1670345 : Blo 742328 1670345 := bstep (se 2 (by rfl) ⟨626379, by rfl⟩ : syracuseStep 1670345 = 1252759) B1252759
theorem B1113515 : Blo 742328 1113515 := bstep (se 1 (by rfl) ⟨835136, by rfl⟩ : syracuseStep 1113515 = 1670273) B1670273
theorem B16317875 : Blo 742328 16317875 := bstep (se 1 (by rfl) ⟨12238406, by rfl⟩ : syracuseStep 16317875 = 24476813) B24476813
theorem B4521401 : Blo 742328 4521401 := bstep (se 2 (by rfl) ⟨1695525, by rfl⟩ : syracuseStep 4521401 = 3391051) B3391051
theorem B1113545 : Blo 742328 1113545 := bstep (se 2 (by rfl) ⟨417579, by rfl⟩ : syracuseStep 1113545 = 835159) B835159
theorem B1113659 : Blo 742328 1113659 := bstep (se 1 (by rfl) ⟨835244, by rfl⟩ : syracuseStep 1113659 = 1670489) B1670489
theorem B1113719 : Blo 742328 1113719 := bstep (se 1 (by rfl) ⟨835289, by rfl⟩ : syracuseStep 1113719 = 1670579) B1670579
theorem B1113743 : Blo 742328 1113743 := bstep (se 1 (by rfl) ⟨835307, by rfl⟩ : syracuseStep 1113743 = 1670615) B1670615
theorem B1113785 : Blo 742328 1113785 := bstep (se 2 (by rfl) ⟨417669, by rfl⟩ : syracuseStep 1113785 = 835339) B835339
theorem B1113863 : Blo 742328 1113863 := bstep (se 1 (by rfl) ⟨835397, by rfl⟩ : syracuseStep 1113863 = 1670795) B1670795
theorem B1113899 : Blo 742328 1113899 := bstep (se 1 (by rfl) ⟨835424, by rfl⟩ : syracuseStep 1113899 = 1670849) B1670849
theorem B1113929 : Blo 742328 1113929 := bstep (se 2 (by rfl) ⟨417723, by rfl⟩ : syracuseStep 1113929 = 835447) B835447
theorem B1671047 : Blo 742328 1671047 := bstep (se 1 (by rfl) ⟨1253285, by rfl⟩ : syracuseStep 1671047 = 2506571) B2506571
theorem B1114043 : Blo 742328 1114043 := bstep (se 1 (by rfl) ⟨835532, by rfl⟩ : syracuseStep 1114043 = 1671065) B1671065
theorem B12058571 : Blo 742328 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B1114103 : Blo 742328 1114103 := bstep (se 1 (by rfl) ⟨835577, by rfl⟩ : syracuseStep 1114103 = 1671155) B1671155
theorem B1114121 : Blo 742328 1114121 := bstep (se 2 (by rfl) ⟨417795, by rfl⟩ : syracuseStep 1114121 = 835591) B835591
theorem B1114151 : Blo 742328 1114151 := bstep (se 1 (by rfl) ⟨835613, by rfl⟩ : syracuseStep 1114151 = 1671227) B1671227
theorem B4292723 : Blo 742328 4292723 := bstep (se 1 (by rfl) ⟨3219542, by rfl⟩ : syracuseStep 4292723 = 6439085) B6439085
theorem B1114235 : Blo 742328 1114235 := bstep (se 1 (by rfl) ⟨835676, by rfl⟩ : syracuseStep 1114235 = 1671353) B1671353
theorem B1114361 : Blo 742328 1114361 := bstep (se 2 (by rfl) ⟨417885, by rfl⟩ : syracuseStep 1114361 = 835771) B835771
theorem B1114463 : Blo 742328 1114463 := bstep (se 1 (by rfl) ⟨835847, by rfl⟩ : syracuseStep 1114463 = 1671695) B1671695
theorem B1114475 : Blo 742328 1114475 := bstep (se 1 (by rfl) ⟨835856, by rfl⟩ : syracuseStep 1114475 = 1671713) B1671713
theorem B1409575 : Blo 742328 1409575 := bstep (se 1 (by rfl) ⟨1057181, by rfl⟩ : syracuseStep 1409575 = 2114363) B2114363
theorem B1114703 : Blo 742328 1114703 := bstep (se 1 (by rfl) ⟨836027, by rfl⟩ : syracuseStep 1114703 = 1672055) B1672055
theorem B1671803 : Blo 742328 1671803 := bstep (se 1 (by rfl) ⟨1253852, by rfl⟩ : syracuseStep 1671803 = 2507705) B2507705
theorem B1114823 : Blo 742328 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B1671929 : Blo 742328 1671929 := bstep (se 2 (by rfl) ⟨626973, by rfl⟩ : syracuseStep 1671929 = 1253947) B1253947
theorem B3769091 : Blo 742328 3769091 := bstep (se 1 (by rfl) ⟨2826818, by rfl⟩ : syracuseStep 3769091 = 5653637) B5653637
theorem B1114985 : Blo 742328 1114985 := bstep (se 2 (by rfl) ⟨418119, by rfl⟩ : syracuseStep 1114985 = 836239) B836239
theorem B6030227 : Blo 742328 6030227 := bstep (se 1 (by rfl) ⟨4522670, by rfl⟩ : syracuseStep 6030227 = 9045341) B9045341
theorem B1115063 : Blo 742328 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B1115099 : Blo 742328 1115099 := bstep (se 1 (by rfl) ⟨836324, by rfl⟩ : syracuseStep 1115099 = 1672649) B1672649
theorem B4031461 : Blo 742328 4031461 := bstep (se 4 (by rfl) ⟨377949, by rfl⟩ : syracuseStep 4031461 = 755899) B755899
theorem B1672199 : Blo 742328 1672199 := bstep (se 1 (by rfl) ⟨1254149, by rfl⟩ : syracuseStep 1672199 = 2508299) B2508299
theorem B1672271 : Blo 742328 1672271 := bstep (se 1 (by rfl) ⟨1254203, by rfl⟩ : syracuseStep 1672271 = 2508407) B2508407
theorem B2819225 : Blo 742328 2819225 := bstep (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) B2114419
theorem B10749347 : Blo 742328 10749347 := bstep (se 1 (by rfl) ⟨8062010, by rfl⟩ : syracuseStep 10749347 = 16124021) B16124021
theorem B1115567 : Blo 742328 1115567 := bstep (se 1 (by rfl) ⟨836675, by rfl⟩ : syracuseStep 1115567 = 1673351) B1673351
theorem B1672667 : Blo 742328 1672667 := bstep (se 1 (by rfl) ⟨1254500, by rfl⟩ : syracuseStep 1672667 = 2509001) B2509001
theorem B3180019 : Blo 742328 3180019 := bstep (se 1 (by rfl) ⟨2385014, by rfl⟩ : syracuseStep 3180019 = 4770029) B4770029
theorem B1115657 : Blo 742328 1115657 := bstep (se 2 (by rfl) ⟨418371, by rfl⟩ : syracuseStep 1115657 = 836743) B836743
theorem B1115687 : Blo 742328 1115687 := bstep (se 1 (by rfl) ⟨836765, by rfl⟩ : syracuseStep 1115687 = 1673531) B1673531
theorem B2819681 : Blo 742328 2819681 := bstep (se 2 (by rfl) ⟨1057380, by rfl⟩ : syracuseStep 2819681 = 2114761) B2114761
theorem B1115771 : Blo 742328 1115771 := bstep (se 1 (by rfl) ⟨836828, by rfl⟩ : syracuseStep 1115771 = 1673657) B1673657
theorem B1115897 : Blo 742328 1115897 := bstep (se 2 (by rfl) ⟨418461, by rfl⟩ : syracuseStep 1115897 = 836923) B836923
theorem B12912473 : Blo 742328 12912473 := bstep (se 2 (by rfl) ⟨4842177, by rfl⟩ : syracuseStep 12912473 = 9684355) B9684355
theorem B6031199 : Blo 742328 6031199 := bstep (se 1 (by rfl) ⟨4523399, by rfl⟩ : syracuseStep 6031199 = 9046799) B9046799
theorem B1115999 : Blo 742328 1115999 := bstep (se 1 (by rfl) ⟨836999, by rfl⟩ : syracuseStep 1115999 = 1673999) B1673999
theorem B19105631 : Blo 742328 19105631 := bstep (se 1 (by rfl) ⟨14329223, by rfl⟩ : syracuseStep 19105631 = 28658447) B28658447
theorem B1116011 : Blo 742328 1116011 := bstep (se 1 (by rfl) ⟨837008, by rfl⟩ : syracuseStep 1116011 = 1674017) B1674017
theorem B1935265 : Blo 742328 1935265 := bstep (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) B1451449
theorem B1673135 : Blo 742328 1673135 := bstep (se 1 (by rfl) ⟨1254851, by rfl⟩ : syracuseStep 1673135 = 2509703) B2509703
theorem B1116239 : Blo 742328 1116239 := bstep (se 1 (by rfl) ⟨837179, by rfl⟩ : syracuseStep 1116239 = 1674359) B1674359
theorem B2689139 : Blo 742328 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B1673387 : Blo 742328 1673387 := bstep (se 1 (by rfl) ⟨1255040, by rfl⟩ : syracuseStep 1673387 = 2510081) B2510081
theorem B1116359 : Blo 742328 1116359 := bstep (se 1 (by rfl) ⟨837269, by rfl⟩ : syracuseStep 1116359 = 1674539) B1674539
theorem B1411283 : Blo 742328 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B3770711 : Blo 742328 3770711 := bstep (se 1 (by rfl) ⟨2828033, by rfl⟩ : syracuseStep 3770711 = 5656067) B5656067
theorem B1116521 : Blo 742328 1116521 := bstep (se 2 (by rfl) ⟨418695, by rfl⟩ : syracuseStep 1116521 = 837391) B837391
theorem B1411435 : Blo 742328 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B1116599 : Blo 742328 1116599 := bstep (se 1 (by rfl) ⟨837449, by rfl⟩ : syracuseStep 1116599 = 1674899) B1674899
theorem B1116635 : Blo 742328 1116635 := bstep (se 1 (by rfl) ⟨837476, by rfl⟩ : syracuseStep 1116635 = 1674953) B1674953
theorem B1411663 : Blo 742328 1411663 := bstep (se 1 (by rfl) ⟨1058747, by rfl⟩ : syracuseStep 1411663 = 2117495) B2117495
theorem B1673927 : Blo 742328 1673927 := bstep (se 1 (by rfl) ⟨1255445, by rfl⟩ : syracuseStep 1673927 = 2510891) B2510891
theorem B3181265 : Blo 742328 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B5639057 : Blo 742328 5639057 := bstep (se 2 (by rfl) ⟨2114646, by rfl⟩ : syracuseStep 5639057 = 4229293) B4229293
theorem B1117103 : Blo 742328 1117103 := bstep (se 1 (by rfl) ⟨837827, by rfl⟩ : syracuseStep 1117103 = 1675655) B1675655
theorem B1117193 : Blo 742328 1117193 := bstep (se 2 (by rfl) ⟨418947, by rfl⟩ : syracuseStep 1117193 = 837895) B837895
theorem B2821139 : Blo 742328 2821139 := bstep (se 1 (by rfl) ⟨2115854, by rfl⟩ : syracuseStep 2821139 = 4231709) B4231709
theorem B1117223 : Blo 742328 1117223 := bstep (se 1 (by rfl) ⟨837917, by rfl⟩ : syracuseStep 1117223 = 1675835) B1675835
theorem B1117307 : Blo 742328 1117307 := bstep (se 1 (by rfl) ⟨837980, by rfl⟩ : syracuseStep 1117307 = 1675961) B1675961
theorem B1117433 : Blo 742328 1117433 := bstep (se 2 (by rfl) ⟨419037, by rfl⟩ : syracuseStep 1117433 = 838075) B838075
theorem B1117535 : Blo 742328 1117535 := bstep (se 1 (by rfl) ⟨838151, by rfl⟩ : syracuseStep 1117535 = 1676303) B1676303
theorem B1117547 : Blo 742328 1117547 := bstep (se 1 (by rfl) ⟨838160, by rfl⟩ : syracuseStep 1117547 = 1676321) B1676321
theorem B3181949 : Blo 742328 3181949 := bstep (se 3 (by rfl) ⟨596615, by rfl⟩ : syracuseStep 3181949 = 1193231) B1193231
theorem B5377499 : Blo 742328 5377499 := bstep (se 1 (by rfl) ⟨4033124, by rfl⟩ : syracuseStep 5377499 = 8066249) B8066249
theorem B1674791 : Blo 742328 1674791 := bstep (se 1 (by rfl) ⟨1256093, by rfl⟩ : syracuseStep 1674791 = 2512187) B2512187
theorem B921127 : Blo 742328 921127 := bstep (se 1 (by rfl) ⟨690845, by rfl⟩ : syracuseStep 921127 = 1381691) B1381691
theorem B1117775 : Blo 742328 1117775 := bstep (se 1 (by rfl) ⟨838331, by rfl⟩ : syracuseStep 1117775 = 1676663) B1676663
theorem B1117895 : Blo 742328 1117895 := bstep (se 1 (by rfl) ⟨838421, by rfl⟩ : syracuseStep 1117895 = 1676843) B1676843
theorem B1118057 : Blo 742328 1118057 := bstep (se 2 (by rfl) ⟨419271, by rfl⟩ : syracuseStep 1118057 = 838543) B838543
theorem B1675115 : Blo 742328 1675115 := bstep (se 1 (by rfl) ⟨1256336, by rfl⟩ : syracuseStep 1675115 = 2512673) B2512673
theorem B1675169 : Blo 742328 1675169 := bstep (se 2 (by rfl) ⟨628188, by rfl⟩ : syracuseStep 1675169 = 1256377) B1256377
theorem B1118135 : Blo 742328 1118135 := bstep (se 1 (by rfl) ⟨838601, by rfl⟩ : syracuseStep 1118135 = 1677203) B1677203
theorem B1118171 : Blo 742328 1118171 := bstep (se 1 (by rfl) ⟨838628, by rfl⟩ : syracuseStep 1118171 = 1677257) B1677257
theorem B1675511 : Blo 742328 1675511 := bstep (se 1 (by rfl) ⟨1256633, by rfl⟩ : syracuseStep 1675511 = 2513267) B2513267
theorem B1118639 : Blo 742328 1118639 := bstep (se 1 (by rfl) ⟨838979, by rfl⟩ : syracuseStep 1118639 = 1677959) B1677959
theorem B1118729 : Blo 742328 1118729 := bstep (se 2 (by rfl) ⟨419523, by rfl⟩ : syracuseStep 1118729 = 839047) B839047
theorem B1118759 : Blo 742328 1118759 := bstep (se 1 (by rfl) ⟨839069, by rfl⟩ : syracuseStep 1118759 = 1678139) B1678139
theorem B1118843 : Blo 742328 1118843 := bstep (se 1 (by rfl) ⟨839132, by rfl⟩ : syracuseStep 1118843 = 1678265) B1678265
theorem B3052171 : Blo 742328 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B2822795 : Blo 742328 2822795 := bstep (se 1 (by rfl) ⟨2117096, by rfl⟩ : syracuseStep 2822795 = 4234193) B4234193
theorem B1118969 : Blo 742328 1118969 := bstep (se 2 (by rfl) ⟨419613, by rfl⟩ : syracuseStep 1118969 = 839227) B839227
theorem B1676105 : Blo 742328 1676105 := bstep (se 2 (by rfl) ⟨628539, by rfl⟩ : syracuseStep 1676105 = 1257079) B1257079
theorem B1119071 : Blo 742328 1119071 := bstep (se 1 (by rfl) ⟨839303, by rfl⟩ : syracuseStep 1119071 = 1678607) B1678607
theorem B1119083 : Blo 742328 1119083 := bstep (se 1 (by rfl) ⟨839312, by rfl⟩ : syracuseStep 1119083 = 1678625) B1678625
theorem B2036755 : Blo 742328 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B8459315 : Blo 742328 8459315 := bstep (se 1 (by rfl) ⟨6344486, by rfl⟩ : syracuseStep 8459315 = 12688973) B12688973
theorem B1119311 : Blo 742328 1119311 := bstep (se 1 (by rfl) ⟨839483, by rfl⟩ : syracuseStep 1119311 = 1678967) B1678967
theorem B1119431 : Blo 742328 1119431 := bstep (se 1 (by rfl) ⟨839573, by rfl⟩ : syracuseStep 1119431 = 1679147) B1679147
theorem B30545099 : Blo 742328 30545099 := bstep (se 1 (by rfl) ⟨22908824, by rfl⟩ : syracuseStep 30545099 = 45817649) B45817649
theorem B5641487 : Blo 742328 5641487 := bstep (se 1 (by rfl) ⟨4231115, by rfl⟩ : syracuseStep 5641487 = 8462231) B8462231
theorem B18060691 : Blo 742328 18060691 := bstep (se 1 (by rfl) ⟨13545518, by rfl⟩ : syracuseStep 18060691 = 27091037) B27091037
theorem B1676897 : Blo 742328 1676897 := bstep (se 2 (by rfl) ⟨628836, by rfl⟩ : syracuseStep 1676897 = 1257673) B1257673
theorem B6362873 : Blo 742328 6362873 := bstep (se 2 (by rfl) ⟨2386077, by rfl⟩ : syracuseStep 6362873 = 4772155) B4772155
theorem B3774275 : Blo 742328 3774275 := bstep (se 1 (by rfl) ⟨2830706, by rfl⟩ : syracuseStep 3774275 = 5661413) B5661413
theorem B2824055 : Blo 742328 2824055 := bstep (se 1 (by rfl) ⟨2118041, by rfl⟩ : syracuseStep 2824055 = 4236083) B4236083
theorem B1677239 : Blo 742328 1677239 := bstep (se 1 (by rfl) ⟨1257929, by rfl⟩ : syracuseStep 1677239 = 2515859) B2515859
theorem B8034241 : Blo 742328 8034241 := bstep (se 2 (by rfl) ⟨3012840, by rfl⟩ : syracuseStep 8034241 = 6025681) B6025681
theorem B8067109 : Blo 742328 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B1415225 : Blo 742328 1415225 := bstep (se 2 (by rfl) ⟨530709, by rfl⟩ : syracuseStep 1415225 = 1061419) B1061419
theorem B3021275 : Blo 742328 3021275 := bstep (se 1 (by rfl) ⟨2265956, by rfl⟩ : syracuseStep 3021275 = 4531913) B4531913
theorem B1677833 : Blo 742328 1677833 := bstep (se 2 (by rfl) ⟨629187, by rfl⟩ : syracuseStep 1677833 = 1258375) B1258375
theorem B2825027 : Blo 742328 2825027 := bstep (se 1 (by rfl) ⟨2118770, by rfl⟩ : syracuseStep 2825027 = 4237541) B4237541
theorem B1678175 : Blo 742328 1678175 := bstep (se 1 (by rfl) ⟨1258631, by rfl⟩ : syracuseStep 1678175 = 2517263) B2517263
theorem B4758547 : Blo 742328 4758547 := bstep (se 1 (by rfl) ⟨3568910, by rfl⟩ : syracuseStep 4758547 = 7137821) B7137821
theorem B1809427 : Blo 742328 1809427 := bstep (se 1 (by rfl) ⟨1357070, by rfl⟩ : syracuseStep 1809427 = 2714141) B2714141
theorem B1678355 : Blo 742328 1678355 := bstep (se 1 (by rfl) ⟨1258766, by rfl⟩ : syracuseStep 1678355 = 2517533) B2517533
theorem B1678697 : Blo 742328 1678697 := bstep (se 2 (by rfl) ⟨629511, by rfl⟩ : syracuseStep 1678697 = 1259023) B1259023
theorem B1252921 : Blo 742328 1252921 := bstep (se 2 (by rfl) ⟨469845, by rfl⟩ : syracuseStep 1252921 = 939691) B939691
theorem B2268769 : Blo 742328 2268769 := bstep (se 2 (by rfl) ⟨850788, by rfl⟩ : syracuseStep 2268769 = 1701577) B1701577
theorem B1416827 : Blo 742328 1416827 := bstep (se 1 (by rfl) ⟨1062620, by rfl⟩ : syracuseStep 1416827 = 2125241) B2125241
theorem B3186323 : Blo 742328 3186323 := bstep (se 1 (by rfl) ⟨2389742, by rfl⟩ : syracuseStep 3186323 = 4779485) B4779485
theorem B1253063 : Blo 742328 1253063 := bstep (se 1 (by rfl) ⟨939797, by rfl⟩ : syracuseStep 1253063 = 1879595) B1879595
theorem B3186391 : Blo 742328 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B4759391 : Blo 742328 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B3022687 : Blo 742328 3022687 := bstep (se 1 (by rfl) ⟨2267015, by rfl⟩ : syracuseStep 3022687 = 4534031) B4534031
theorem B1253225 : Blo 742328 1253225 := bstep (se 2 (by rfl) ⟨469959, by rfl⟩ : syracuseStep 1253225 = 939919) B939919
theorem B5644403 : Blo 742328 5644403 := bstep (se 1 (by rfl) ⟨4233302, by rfl⟩ : syracuseStep 5644403 = 8466605) B8466605
theorem B12263653 : Blo 742328 12263653 := bstep (se 4 (by rfl) ⟨1149717, by rfl⟩ : syracuseStep 12263653 = 2299435) B2299435
theorem B1253623 : Blo 742328 1253623 := bstep (se 1 (by rfl) ⟨940217, by rfl⟩ : syracuseStep 1253623 = 1880435) B1880435
theorem B1253819 : Blo 742328 1253819 := bstep (se 1 (by rfl) ⟨940364, by rfl⟩ : syracuseStep 1253819 = 1880729) B1880729
theorem B2826697 : Blo 742328 2826697 := bstep (se 2 (by rfl) ⟨1060011, by rfl⟩ : syracuseStep 2826697 = 2120023) B2120023
theorem B10166809 : Blo 742328 10166809 := bstep (se 2 (by rfl) ⟨3812553, by rfl⟩ : syracuseStep 10166809 = 7625107) B7625107
theorem B3809825 : Blo 742328 3809825 := bstep (se 2 (by rfl) ⟨1428684, by rfl⟩ : syracuseStep 3809825 = 2857369) B2857369
theorem B1253927 : Blo 742328 1253927 := bstep (se 1 (by rfl) ⟨940445, by rfl⟩ : syracuseStep 1253927 = 1880891) B1880891
theorem B2827001 : Blo 742328 2827001 := bstep (se 2 (by rfl) ⟨1060125, by rfl⟩ : syracuseStep 2827001 = 2120251) B2120251
theorem B1254217 : Blo 742328 1254217 := bstep (se 2 (by rfl) ⟨470331, by rfl⟩ : syracuseStep 1254217 = 940663) B940663
theorem B3777353 : Blo 742328 3777353 := bstep (se 2 (by rfl) ⟨1416507, by rfl⟩ : syracuseStep 3777353 = 2833015) B2833015
theorem B1254251 : Blo 742328 1254251 := bstep (se 1 (by rfl) ⟨940688, by rfl⟩ : syracuseStep 1254251 = 1881377) B1881377
theorem B3023725 : Blo 742328 3023725 := bstep (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) B1133897
theorem B2827169 : Blo 742328 2827169 := bstep (se 2 (by rfl) ⟨1060188, by rfl⟩ : syracuseStep 2827169 = 2120377) B2120377
theorem B1057711 : Blo 742328 1057711 := bstep (se 1 (by rfl) ⟨793283, by rfl⟩ : syracuseStep 1057711 = 1586567) B1586567
theorem B2827183 : Blo 742328 2827183 := bstep (se 1 (by rfl) ⟨2120387, by rfl⟩ : syracuseStep 2827183 = 4240775) B4240775
theorem B4826305 : Blo 742328 4826305 := bstep (se 2 (by rfl) ⟨1809864, by rfl⟩ : syracuseStep 4826305 = 3619729) B3619729
theorem B1254649 : Blo 742328 1254649 := bstep (se 2 (by rfl) ⟨470493, by rfl⟩ : syracuseStep 1254649 = 940987) B940987
theorem B4826611 : Blo 742328 4826611 := bstep (se 1 (by rfl) ⟨3619958, by rfl⟩ : syracuseStep 4826611 = 7239917) B7239917
theorem B1254919 : Blo 742328 1254919 := bstep (se 1 (by rfl) ⟨941189, by rfl⟩ : syracuseStep 1254919 = 1882379) B1882379
theorem B1058383 : Blo 742328 1058383 := bstep (se 1 (by rfl) ⟨793787, by rfl⟩ : syracuseStep 1058383 = 1587575) B1587575
theorem B1058503 : Blo 742328 1058503 := bstep (se 1 (by rfl) ⟨793877, by rfl⟩ : syracuseStep 1058503 = 1587755) B1587755
theorem B2828141 : Blo 742328 2828141 := bstep (se 3 (by rfl) ⟨530276, by rfl⟩ : syracuseStep 2828141 = 1060553) B1060553
theorem B1255351 : Blo 742328 1255351 := bstep (se 1 (by rfl) ⟨941513, by rfl⟩ : syracuseStep 1255351 = 1883027) B1883027
theorem B1910711 : Blo 742328 1910711 := bstep (se 1 (by rfl) ⟨1433033, by rfl⟩ : syracuseStep 1910711 = 2866067) B2866067
theorem B1255547 : Blo 742328 1255547 := bstep (se 1 (by rfl) ⟨941660, by rfl⟩ : syracuseStep 1255547 = 1883321) B1883321
theorem B2828459 : Blo 742328 2828459 := bstep (se 1 (by rfl) ⟨2121344, by rfl⟩ : syracuseStep 2828459 = 4242689) B4242689
theorem B15280433 : Blo 742328 15280433 := bstep (se 2 (by rfl) ⟨5730162, by rfl⟩ : syracuseStep 15280433 = 11460325) B11460325
theorem B1255945 : Blo 742328 1255945 := bstep (se 2 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 1255945 = 941959) B941959
theorem B8039047 : Blo 742328 8039047 := bstep (se 1 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 8039047 = 12058571) B12058571
theorem B1256107 : Blo 742328 1256107 := bstep (se 1 (by rfl) ⟨942080, by rfl⟩ : syracuseStep 1256107 = 1884161) B1884161
theorem B1256411 : Blo 742328 1256411 := bstep (se 1 (by rfl) ⟨942308, by rfl⟩ : syracuseStep 1256411 = 1884617) B1884617
theorem B1256647 : Blo 742328 1256647 := bstep (se 1 (by rfl) ⟨942485, by rfl⟩ : syracuseStep 1256647 = 1884971) B1884971
theorem B1256809 : Blo 742328 1256809 := bstep (se 2 (by rfl) ⟨471303, by rfl⟩ : syracuseStep 1256809 = 942607) B942607
theorem B765535 : Blo 742328 765535 := bstep (se 1 (by rfl) ⟨574151, by rfl⟩ : syracuseStep 765535 = 1148303) B1148303
theorem B1879969 : Blo 742328 1879969 := bstep (se 2 (by rfl) ⟨704988, by rfl⟩ : syracuseStep 1879969 = 1409977) B1409977
theorem B1257403 : Blo 742328 1257403 := bstep (se 1 (by rfl) ⟨943052, by rfl⟩ : syracuseStep 1257403 = 1886105) B1886105
theorem B1257511 : Blo 742328 1257511 := bstep (se 1 (by rfl) ⟨943133, by rfl⟩ : syracuseStep 1257511 = 1886267) B1886267
theorem B8040779 : Blo 742328 8040779 := bstep (se 1 (by rfl) ⟨6030584, by rfl⟩ : syracuseStep 8040779 = 12061169) B12061169
theorem B1257835 : Blo 742328 1257835 := bstep (se 1 (by rfl) ⟨943376, by rfl⟩ : syracuseStep 1257835 = 1886753) B1886753
theorem B1192411 : Blo 742328 1192411 := bstep (se 1 (by rfl) ⟨894308, by rfl⟩ : syracuseStep 1192411 = 1788617) B1788617
theorem B1192457 : Blo 742328 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B2831057 : Blo 742328 2831057 := bstep (se 2 (by rfl) ⟨1061646, by rfl⟩ : syracuseStep 2831057 = 2123293) B2123293
theorem B1455067 : Blo 742328 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B2831375 : Blo 742328 2831375 := bstep (se 1 (by rfl) ⟨2123531, by rfl⟩ : syracuseStep 2831375 = 4247063) B4247063
theorem B1062011 : Blo 742328 1062011 := bstep (se 1 (by rfl) ⟨796508, by rfl⟩ : syracuseStep 1062011 = 1593017) B1593017
theorem B1258895 : Blo 742328 1258895 := bstep (se 1 (by rfl) ⟨944171, by rfl⟩ : syracuseStep 1258895 = 1888343) B1888343
theorem B1259131 : Blo 742328 1259131 := bstep (se 1 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 1259131 = 1888697) B1888697
theorem B5650235 : Blo 742328 5650235 := bstep (se 1 (by rfl) ⟨4237676, by rfl⟩ : syracuseStep 5650235 = 8475353) B8475353
theorem B2013103 : Blo 742328 2013103 := bstep (se 1 (by rfl) ⟨1509827, by rfl⟩ : syracuseStep 2013103 = 3019655) B3019655
theorem B1882511 : Blo 742328 1882511 := bstep (se 1 (by rfl) ⟨1411883, by rfl⟩ : syracuseStep 1882511 = 2823767) B2823767
theorem B5355929 : Blo 742328 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B1882835 : Blo 742328 1882835 := bstep (se 1 (by rfl) ⟨1412126, by rfl⟩ : syracuseStep 1882835 = 2824253) B2824253
theorem B2505545 : Blo 742328 2505545 := bstep (se 2 (by rfl) ⟨939579, by rfl⟩ : syracuseStep 2505545 = 1879159) B1879159
theorem B9550871 : Blo 742328 9550871 := bstep (se 1 (by rfl) ⟨7163153, by rfl⟩ : syracuseStep 9550871 = 14326307) B14326307
theorem B2833487 : Blo 742328 2833487 := bstep (se 1 (by rfl) ⟨2125115, by rfl⟩ : syracuseStep 2833487 = 4250231) B4250231
theorem B2014607 : Blo 742328 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B835195 : Blo 742328 835195 := bstep (se 1 (by rfl) ⟨626396, by rfl⟩ : syracuseStep 835195 = 1252793) B1252793
theorem B5881643 : Blo 742328 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B1883999 : Blo 742328 1883999 := bstep (se 1 (by rfl) ⟨1412999, by rfl⟩ : syracuseStep 1883999 = 2825999) B2825999
theorem B2506679 : Blo 742328 2506679 := bstep (se 1 (by rfl) ⟨1880009, by rfl⟩ : syracuseStep 2506679 = 3760019) B3760019
theorem B835663 : Blo 742328 835663 := bstep (se 1 (by rfl) ⟨626747, by rfl⟩ : syracuseStep 835663 = 1253495) B1253495
theorem B4768105 : Blo 742328 4768105 := bstep (se 2 (by rfl) ⟨1788039, by rfl⟩ : syracuseStep 4768105 = 3576079) B3576079
theorem B836059 : Blo 742328 836059 := bstep (se 1 (by rfl) ⟨627044, by rfl⟩ : syracuseStep 836059 = 1254089) B1254089
theorem B2507273 : Blo 742328 2507273 := bstep (se 2 (by rfl) ⟨940227, by rfl⟩ : syracuseStep 2507273 = 1880455) B1880455
theorem B2114237 : Blo 742328 2114237 := bstep (se 3 (by rfl) ⟨396419, by rfl⟩ : syracuseStep 2114237 = 792839) B792839
theorem B836527 : Blo 742328 836527 := bstep (se 1 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 836527 = 1254791) B1254791
theorem B1885103 : Blo 742328 1885103 := bstep (se 1 (by rfl) ⟨1413827, by rfl⟩ : syracuseStep 1885103 = 2827655) B2827655
theorem B4244399 : Blo 742328 4244399 := bstep (se 1 (by rfl) ⟨3183299, by rfl⟩ : syracuseStep 4244399 = 6366599) B6366599
theorem B3392513 : Blo 742328 3392513 := bstep (se 2 (by rfl) ⟨1272192, by rfl⟩ : syracuseStep 3392513 = 2544385) B2544385
theorem B2114579 : Blo 742328 2114579 := bstep (se 1 (by rfl) ⟨1585934, by rfl⟩ : syracuseStep 2114579 = 3171869) B3171869
theorem B836959 : Blo 742328 836959 := bstep (se 1 (by rfl) ⟨627719, by rfl⟩ : syracuseStep 836959 = 1255439) B1255439
theorem B2508137 : Blo 742328 2508137 := bstep (se 2 (by rfl) ⟨940551, by rfl⟩ : syracuseStep 2508137 = 1881103) B1881103
theorem B2115035 : Blo 742328 2115035 := bstep (se 1 (by rfl) ⟨1586276, by rfl⟩ : syracuseStep 2115035 = 3172553) B3172553
theorem B837319 : Blo 742328 837319 := bstep (se 1 (by rfl) ⟨627989, by rfl⟩ : syracuseStep 837319 = 1255979) B1255979
theorem B7161695 : Blo 742328 7161695 := bstep (se 1 (by rfl) ⟨5371271, by rfl⟩ : syracuseStep 7161695 = 10742543) B10742543
theorem B2541431 : Blo 742328 2541431 := bstep (se 1 (by rfl) ⟨1906073, by rfl⟩ : syracuseStep 2541431 = 3812147) B3812147
theorem B2508731 : Blo 742328 2508731 := bstep (se 1 (by rfl) ⟨1881548, by rfl⟩ : syracuseStep 2508731 = 3763097) B3763097
theorem B9029569 : Blo 742328 9029569 := bstep (se 2 (by rfl) ⟨3386088, by rfl⟩ : syracuseStep 9029569 = 6772177) B6772177
theorem B1886287 : Blo 742328 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B5654609 : Blo 742328 5654609 := bstep (se 2 (by rfl) ⟨2120478, by rfl⟩ : syracuseStep 5654609 = 4240957) B4240957
theorem B32229683 : Blo 742328 32229683 := bstep (se 1 (by rfl) ⟨24172262, by rfl⟩ : syracuseStep 32229683 = 48344525) B48344525
theorem B838183 : Blo 742328 838183 := bstep (se 1 (by rfl) ⟨628637, by rfl⟩ : syracuseStep 838183 = 1257275) B1257275
theorem B2116219 : Blo 742328 2116219 := bstep (se 1 (by rfl) ⟨1587164, by rfl⟩ : syracuseStep 2116219 = 3174329) B3174329
theorem B1788539 : Blo 742328 1788539 := bstep (se 1 (by rfl) ⟨1341404, by rfl⟩ : syracuseStep 1788539 = 2682809) B2682809
theorem B1591931 : Blo 742328 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B4770515 : Blo 742328 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B1886935 : Blo 742328 1886935 := bstep (se 1 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 1886935 = 2830403) B2830403
theorem B21449549 : Blo 742328 21449549 := bstep (se 3 (by rfl) ⟨4021790, by rfl⟩ : syracuseStep 21449549 = 8043581) B8043581
theorem B4770667 : Blo 742328 4770667 := bstep (se 1 (by rfl) ⟨3578000, by rfl⟩ : syracuseStep 4770667 = 7156001) B7156001
theorem B1592239 : Blo 742328 1592239 := bstep (se 1 (by rfl) ⟨1194179, by rfl⟩ : syracuseStep 1592239 = 2388359) B2388359
theorem B1887239 : Blo 742328 1887239 := bstep (se 1 (by rfl) ⟨1415429, by rfl⟩ : syracuseStep 1887239 = 2830859) B2830859
theorem B4246607 : Blo 742328 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B18599203 : Blo 742328 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B9653593 : Blo 742328 9653593 := bstep (se 2 (by rfl) ⟨3620097, by rfl⟩ : syracuseStep 9653593 = 7240195) B7240195
theorem B19353005 : Blo 742328 19353005 := bstep (se 3 (by rfl) ⟨3628688, by rfl⟩ : syracuseStep 19353005 = 7257377) B7257377
theorem B2117107 : Blo 742328 2117107 := bstep (se 1 (by rfl) ⟨1587830, by rfl⟩ : syracuseStep 2117107 = 3175661) B3175661
theorem B2510459 : Blo 742328 2510459 := bstep (se 1 (by rfl) ⟨1882844, by rfl⟩ : syracuseStep 2510459 = 3765689) B3765689
theorem B2117335 : Blo 742328 2117335 := bstep (se 1 (by rfl) ⟨1588001, by rfl⟩ : syracuseStep 2117335 = 3176003) B3176003
theorem B2510621 : Blo 742328 2510621 := bstep (se 3 (by rfl) ⟨470741, by rfl⟩ : syracuseStep 2510621 = 941483) B941483
theorem B16305953 : Blo 742328 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B2379593 : Blo 742328 2379593 := bstep (se 2 (by rfl) ⟨892347, by rfl⟩ : syracuseStep 2379593 = 1784695) B1784695
theorem B8605777 : Blo 742328 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B21418181 : Blo 742328 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B10309963 : Blo 742328 10309963 := bstep (se 1 (by rfl) ⟨7732472, by rfl⟩ : syracuseStep 10309963 = 15464945) B15464945
theorem B2511323 : Blo 742328 2511323 := bstep (se 1 (by rfl) ⟨1883492, by rfl⟩ : syracuseStep 2511323 = 3766985) B3766985
theorem B11457125 : Blo 742328 11457125 := bstep (se 4 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 11457125 = 2148211) B2148211
theorem B2871947 : Blo 742328 2871947 := bstep (se 1 (by rfl) ⟨2153960, by rfl⟩ : syracuseStep 2871947 = 4307921) B4307921
theorem B742343 : Blo 742328 742343 := bstep (se 1 (by rfl) ⟨556757, by rfl⟩ : syracuseStep 742343 = 1113515) B1113515
theorem B742363 : Blo 742328 742363 := bstep (se 1 (by rfl) ⟨556772, by rfl⟩ : syracuseStep 742363 = 1113545) B1113545
theorem B742439 : Blo 742328 742439 := bstep (se 1 (by rfl) ⟨556829, by rfl⟩ : syracuseStep 742439 = 1113659) B1113659
theorem B742479 : Blo 742328 742479 := bstep (se 1 (by rfl) ⟨556859, by rfl⟩ : syracuseStep 742479 = 1113719) B1113719
theorem B742495 : Blo 742328 742495 := bstep (se 1 (by rfl) ⟨556871, by rfl⟩ : syracuseStep 742495 = 1113743) B1113743
theorem B742523 : Blo 742328 742523 := bstep (se 1 (by rfl) ⟨556892, by rfl⟩ : syracuseStep 742523 = 1113785) B1113785
theorem B2512025 : Blo 742328 2512025 := bstep (se 2 (by rfl) ⟨942009, by rfl⟩ : syracuseStep 2512025 = 1884019) B1884019
theorem B742575 : Blo 742328 742575 := bstep (se 1 (by rfl) ⟨556931, by rfl⟩ : syracuseStep 742575 = 1113863) B1113863
theorem B742599 : Blo 742328 742599 := bstep (se 1 (by rfl) ⟨556949, by rfl⟩ : syracuseStep 742599 = 1113899) B1113899
theorem B742619 : Blo 742328 742619 := bstep (se 1 (by rfl) ⟨556964, by rfl⟩ : syracuseStep 742619 = 1113929) B1113929
theorem B742695 : Blo 742328 742695 := bstep (se 1 (by rfl) ⟨557021, by rfl⟩ : syracuseStep 742695 = 1114043) B1114043
theorem B742735 : Blo 742328 742735 := bstep (se 1 (by rfl) ⟨557051, by rfl⟩ : syracuseStep 742735 = 1114103) B1114103
theorem B742751 : Blo 742328 742751 := bstep (se 1 (by rfl) ⟨557063, by rfl⟩ : syracuseStep 742751 = 1114127) B1114127
theorem B742779 : Blo 742328 742779 := bstep (se 1 (by rfl) ⟨557084, by rfl⟩ : syracuseStep 742779 = 1114169) B1114169
theorem B9524627 : Blo 742328 9524627 := bstep (se 1 (by rfl) ⟨7143470, by rfl⟩ : syracuseStep 9524627 = 14286941) B14286941
theorem B742831 : Blo 742328 742831 := bstep (se 1 (by rfl) ⟨557123, by rfl⟩ : syracuseStep 742831 = 1114247) B1114247
theorem B742855 : Blo 742328 742855 := bstep (se 1 (by rfl) ⟨557141, by rfl⟩ : syracuseStep 742855 = 1114283) B1114283
theorem B742875 : Blo 742328 742875 := bstep (se 1 (by rfl) ⟨557156, by rfl⟩ : syracuseStep 742875 = 1114313) B1114313
theorem B2119193 : Blo 742328 2119193 := bstep (se 2 (by rfl) ⟨794697, by rfl⟩ : syracuseStep 2119193 = 1589395) B1589395
theorem B742951 : Blo 742328 742951 := bstep (se 1 (by rfl) ⟨557213, by rfl⟩ : syracuseStep 742951 = 1114427) B1114427
theorem B4773437 : Blo 742328 4773437 := bstep (se 3 (by rfl) ⟨895019, by rfl⟩ : syracuseStep 4773437 = 1790039) B1790039
theorem B742991 : Blo 742328 742991 := bstep (se 1 (by rfl) ⟨557243, by rfl⟩ : syracuseStep 742991 = 1114487) B1114487
theorem B743007 : Blo 742328 743007 := bstep (se 1 (by rfl) ⟨557255, by rfl⟩ : syracuseStep 743007 = 1114511) B1114511
theorem B743035 : Blo 742328 743035 := bstep (se 1 (by rfl) ⟨557276, by rfl⟩ : syracuseStep 743035 = 1114553) B1114553
theorem B743087 : Blo 742328 743087 := bstep (se 1 (by rfl) ⟨557315, by rfl⟩ : syracuseStep 743087 = 1114631) B1114631
theorem B743111 : Blo 742328 743111 := bstep (se 1 (by rfl) ⟨557333, by rfl⟩ : syracuseStep 743111 = 1114667) B1114667
theorem B743131 : Blo 742328 743131 := bstep (se 1 (by rfl) ⟨557348, by rfl⟩ : syracuseStep 743131 = 1114697) B1114697
theorem B743207 : Blo 742328 743207 := bstep (se 1 (by rfl) ⟨557405, by rfl⟩ : syracuseStep 743207 = 1114811) B1114811
theorem B743247 : Blo 742328 743247 := bstep (se 1 (by rfl) ⟨557435, by rfl⟩ : syracuseStep 743247 = 1114871) B1114871
theorem B743263 : Blo 742328 743263 := bstep (se 1 (by rfl) ⟨557447, by rfl⟩ : syracuseStep 743263 = 1114895) B1114895
theorem B743291 : Blo 742328 743291 := bstep (se 1 (by rfl) ⟨557468, by rfl⟩ : syracuseStep 743291 = 1114937) B1114937
theorem B743343 : Blo 742328 743343 := bstep (se 1 (by rfl) ⟨557507, by rfl⟩ : syracuseStep 743343 = 1115015) B1115015
theorem B743367 : Blo 742328 743367 := bstep (se 1 (by rfl) ⟨557525, by rfl⟩ : syracuseStep 743367 = 1115051) B1115051
theorem B743387 : Blo 742328 743387 := bstep (se 1 (by rfl) ⟨557540, by rfl⟩ : syracuseStep 743387 = 1115081) B1115081
theorem B1792019 : Blo 742328 1792019 := bstep (se 1 (by rfl) ⟨1344014, by rfl⟩ : syracuseStep 1792019 = 2688029) B2688029
theorem B743463 : Blo 742328 743463 := bstep (se 1 (by rfl) ⟨557597, by rfl⟩ : syracuseStep 743463 = 1115195) B1115195
theorem B743503 : Blo 742328 743503 := bstep (se 1 (by rfl) ⟨557627, by rfl⟩ : syracuseStep 743503 = 1115255) B1115255
theorem B743519 : Blo 742328 743519 := bstep (se 1 (by rfl) ⟨557639, by rfl⟩ : syracuseStep 743519 = 1115279) B1115279
theorem B743547 : Blo 742328 743547 := bstep (se 1 (by rfl) ⟨557660, by rfl⟩ : syracuseStep 743547 = 1115321) B1115321
theorem B2381977 : Blo 742328 2381977 := bstep (se 2 (by rfl) ⟨893241, by rfl⟩ : syracuseStep 2381977 = 1786483) B1786483
theorem B3758237 : Blo 742328 3758237 := bstep (se 3 (by rfl) ⟨704669, by rfl⟩ : syracuseStep 3758237 = 1409339) B1409339
theorem B2545835 : Blo 742328 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B743599 : Blo 742328 743599 := bstep (se 1 (by rfl) ⟨557699, by rfl⟩ : syracuseStep 743599 = 1115399) B1115399
theorem B743623 : Blo 742328 743623 := bstep (se 1 (by rfl) ⟨557717, by rfl⟩ : syracuseStep 743623 = 1115435) B1115435
theorem B743643 : Blo 742328 743643 := bstep (se 1 (by rfl) ⟨557732, by rfl⟩ : syracuseStep 743643 = 1115465) B1115465
theorem B743719 : Blo 742328 743719 := bstep (se 1 (by rfl) ⟨557789, by rfl⟩ : syracuseStep 743719 = 1115579) B1115579
theorem B2513213 : Blo 742328 2513213 := bstep (se 3 (by rfl) ⟨471227, by rfl⟩ : syracuseStep 2513213 = 942455) B942455
theorem B743759 : Blo 742328 743759 := bstep (se 1 (by rfl) ⟨557819, by rfl⟩ : syracuseStep 743759 = 1115639) B1115639
theorem B743775 : Blo 742328 743775 := bstep (se 1 (by rfl) ⟨557831, by rfl⟩ : syracuseStep 743775 = 1115663) B1115663
theorem B743803 : Blo 742328 743803 := bstep (se 1 (by rfl) ⟨557852, by rfl⟩ : syracuseStep 743803 = 1115705) B1115705
theorem B743855 : Blo 742328 743855 := bstep (se 1 (by rfl) ⟨557891, by rfl⟩ : syracuseStep 743855 = 1115783) B1115783
theorem B743879 : Blo 742328 743879 := bstep (se 1 (by rfl) ⟨557909, by rfl⟩ : syracuseStep 743879 = 1115819) B1115819
theorem B743899 : Blo 742328 743899 := bstep (se 1 (by rfl) ⟨557924, by rfl⟩ : syracuseStep 743899 = 1115849) B1115849
theorem B1071625 : Blo 742328 1071625 := bstep (se 2 (by rfl) ⟨401859, by rfl⟩ : syracuseStep 1071625 = 803719) B803719
theorem B5364233 : Blo 742328 5364233 := bstep (se 2 (by rfl) ⟨2011587, by rfl⟩ : syracuseStep 5364233 = 4023175) B4023175
theorem B9558557 : Blo 742328 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B743975 : Blo 742328 743975 := bstep (se 1 (by rfl) ⟨557981, by rfl⟩ : syracuseStep 743975 = 1115963) B1115963
theorem B744015 : Blo 742328 744015 := bstep (se 1 (by rfl) ⟨558011, by rfl⟩ : syracuseStep 744015 = 1116023) B1116023
theorem B744031 : Blo 742328 744031 := bstep (se 1 (by rfl) ⟨558023, by rfl⟩ : syracuseStep 744031 = 1116047) B1116047
theorem B744059 : Blo 742328 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B744111 : Blo 742328 744111 := bstep (se 1 (by rfl) ⟨558083, by rfl⟩ : syracuseStep 744111 = 1116167) B1116167
theorem B744135 : Blo 742328 744135 := bstep (se 1 (by rfl) ⟨558101, by rfl⟩ : syracuseStep 744135 = 1116203) B1116203
theorem B744155 : Blo 742328 744155 := bstep (se 1 (by rfl) ⟨558116, by rfl⟩ : syracuseStep 744155 = 1116233) B1116233
theorem B744231 : Blo 742328 744231 := bstep (se 1 (by rfl) ⟨558173, by rfl⟩ : syracuseStep 744231 = 1116347) B1116347
theorem B5659469 : Blo 742328 5659469 := bstep (se 3 (by rfl) ⟨1061150, by rfl⟩ : syracuseStep 5659469 = 2122301) B2122301
theorem B744271 : Blo 742328 744271 := bstep (se 1 (by rfl) ⟨558203, by rfl⟩ : syracuseStep 744271 = 1116407) B1116407
theorem B744287 : Blo 742328 744287 := bstep (se 1 (by rfl) ⟨558215, by rfl⟩ : syracuseStep 744287 = 1116431) B1116431
theorem B744315 : Blo 742328 744315 := bstep (se 1 (by rfl) ⟨558236, by rfl⟩ : syracuseStep 744315 = 1116473) B1116473
theorem B744367 : Blo 742328 744367 := bstep (se 1 (by rfl) ⟨558275, by rfl⟩ : syracuseStep 744367 = 1116551) B1116551
theorem B10738615 : Blo 742328 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B744391 : Blo 742328 744391 := bstep (se 1 (by rfl) ⟨558293, by rfl⟩ : syracuseStep 744391 = 1116587) B1116587
theorem B744411 : Blo 742328 744411 := bstep (se 1 (by rfl) ⟨558308, by rfl⟩ : syracuseStep 744411 = 1116617) B1116617
theorem B744487 : Blo 742328 744487 := bstep (se 1 (by rfl) ⟨558365, by rfl⟩ : syracuseStep 744487 = 1116731) B1116731
theorem B744527 : Blo 742328 744527 := bstep (se 1 (by rfl) ⟨558395, by rfl⟩ : syracuseStep 744527 = 1116791) B1116791
theorem B744543 : Blo 742328 744543 := bstep (se 1 (by rfl) ⟨558407, by rfl⟩ : syracuseStep 744543 = 1116815) B1116815
theorem B744571 : Blo 742328 744571 := bstep (se 1 (by rfl) ⟨558428, by rfl⟩ : syracuseStep 744571 = 1116857) B1116857
theorem B2514077 : Blo 742328 2514077 := bstep (se 3 (by rfl) ⟨471389, by rfl⟩ : syracuseStep 2514077 = 942779) B942779
theorem B744623 : Blo 742328 744623 := bstep (se 1 (by rfl) ⟨558467, by rfl⟩ : syracuseStep 744623 = 1116935) B1116935
theorem B744647 : Blo 742328 744647 := bstep (se 1 (by rfl) ⟨558485, by rfl⟩ : syracuseStep 744647 = 1116971) B1116971
theorem B744667 : Blo 742328 744667 := bstep (se 1 (by rfl) ⟨558500, by rfl⟩ : syracuseStep 744667 = 1117001) B1117001
theorem B12082445 : Blo 742328 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B744743 : Blo 742328 744743 := bstep (se 1 (by rfl) ⟨558557, by rfl⟩ : syracuseStep 744743 = 1117115) B1117115
theorem B744783 : Blo 742328 744783 := bstep (se 1 (by rfl) ⟨558587, by rfl⟩ : syracuseStep 744783 = 1117175) B1117175
theorem B744799 : Blo 742328 744799 := bstep (se 1 (by rfl) ⟨558599, by rfl⟩ : syracuseStep 744799 = 1117199) B1117199
theorem B744827 : Blo 742328 744827 := bstep (se 1 (by rfl) ⟨558620, by rfl⟩ : syracuseStep 744827 = 1117241) B1117241
theorem B3759533 : Blo 742328 3759533 := bstep (se 3 (by rfl) ⟨704912, by rfl⟩ : syracuseStep 3759533 = 1409825) B1409825
theorem B744879 : Blo 742328 744879 := bstep (se 1 (by rfl) ⟨558659, by rfl⟩ : syracuseStep 744879 = 1117319) B1117319
theorem B744903 : Blo 742328 744903 := bstep (se 1 (by rfl) ⟨558677, by rfl⟩ : syracuseStep 744903 = 1117355) B1117355
theorem B744923 : Blo 742328 744923 := bstep (se 1 (by rfl) ⟨558692, by rfl⟩ : syracuseStep 744923 = 1117385) B1117385
theorem B744999 : Blo 742328 744999 := bstep (se 1 (by rfl) ⟨558749, by rfl⟩ : syracuseStep 744999 = 1117499) B1117499
theorem B745039 : Blo 742328 745039 := bstep (se 1 (by rfl) ⟨558779, by rfl⟩ : syracuseStep 745039 = 1117559) B1117559
theorem B745055 : Blo 742328 745055 := bstep (se 1 (by rfl) ⟨558791, by rfl⟩ : syracuseStep 745055 = 1117583) B1117583
theorem B745083 : Blo 742328 745083 := bstep (se 1 (by rfl) ⟨558812, by rfl⟩ : syracuseStep 745083 = 1117625) B1117625
theorem B745135 : Blo 742328 745135 := bstep (se 1 (by rfl) ⟨558851, by rfl⟩ : syracuseStep 745135 = 1117703) B1117703
theorem B2514617 : Blo 742328 2514617 := bstep (se 2 (by rfl) ⟨942981, by rfl⟩ : syracuseStep 2514617 = 1885963) B1885963
theorem B745159 : Blo 742328 745159 := bstep (se 1 (by rfl) ⟨558869, by rfl⟩ : syracuseStep 745159 = 1117739) B1117739
theorem B745179 : Blo 742328 745179 := bstep (se 1 (by rfl) ⟨558884, by rfl⟩ : syracuseStep 745179 = 1117769) B1117769
theorem B745255 : Blo 742328 745255 := bstep (se 1 (by rfl) ⟨558941, by rfl⟩ : syracuseStep 745255 = 1117883) B1117883
theorem B745295 : Blo 742328 745295 := bstep (se 1 (by rfl) ⟨558971, by rfl⟩ : syracuseStep 745295 = 1117943) B1117943
theorem B745311 : Blo 742328 745311 := bstep (se 1 (by rfl) ⟨558983, by rfl⟩ : syracuseStep 745311 = 1117967) B1117967
theorem B745339 : Blo 742328 745339 := bstep (se 1 (by rfl) ⟨559004, by rfl⟩ : syracuseStep 745339 = 1118009) B1118009
theorem B745391 : Blo 742328 745391 := bstep (se 1 (by rfl) ⟨559043, by rfl⟩ : syracuseStep 745391 = 1118087) B1118087
theorem B745415 : Blo 742328 745415 := bstep (se 1 (by rfl) ⟨559061, by rfl⟩ : syracuseStep 745415 = 1118123) B1118123
theorem B745435 : Blo 742328 745435 := bstep (se 1 (by rfl) ⟨559076, by rfl⟩ : syracuseStep 745435 = 1118153) B1118153
theorem B745511 : Blo 742328 745511 := bstep (se 1 (by rfl) ⟨559133, by rfl⟩ : syracuseStep 745511 = 1118267) B1118267
theorem B2383951 : Blo 742328 2383951 := bstep (se 1 (by rfl) ⟨1787963, by rfl⟩ : syracuseStep 2383951 = 3575927) B3575927
theorem B745551 : Blo 742328 745551 := bstep (se 1 (by rfl) ⟨559163, by rfl⟩ : syracuseStep 745551 = 1118327) B1118327
theorem B745567 : Blo 742328 745567 := bstep (se 1 (by rfl) ⟨559175, by rfl⟩ : syracuseStep 745567 = 1118351) B1118351
theorem B745595 : Blo 742328 745595 := bstep (se 1 (by rfl) ⟨559196, by rfl⟩ : syracuseStep 745595 = 1118393) B1118393
theorem B745647 : Blo 742328 745647 := bstep (se 1 (by rfl) ⟨559235, by rfl⟩ : syracuseStep 745647 = 1118471) B1118471
theorem B745671 : Blo 742328 745671 := bstep (se 1 (by rfl) ⟨559253, by rfl⟩ : syracuseStep 745671 = 1118507) B1118507
theorem B745691 : Blo 742328 745691 := bstep (se 1 (by rfl) ⟨559268, by rfl⟩ : syracuseStep 745691 = 1118537) B1118537
theorem B2515211 : Blo 742328 2515211 := bstep (se 1 (by rfl) ⟨1886408, by rfl⟩ : syracuseStep 2515211 = 3772817) B3772817
theorem B745767 : Blo 742328 745767 := bstep (se 1 (by rfl) ⟨559325, by rfl⟩ : syracuseStep 745767 = 1118651) B1118651
theorem B745807 : Blo 742328 745807 := bstep (se 1 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 745807 = 1118711) B1118711
theorem B745823 : Blo 742328 745823 := bstep (se 1 (by rfl) ⟨559367, by rfl⟩ : syracuseStep 745823 = 1118735) B1118735
theorem B745851 : Blo 742328 745851 := bstep (se 1 (by rfl) ⟨559388, by rfl⟩ : syracuseStep 745851 = 1118777) B1118777
theorem B2122109 : Blo 742328 2122109 := bstep (se 3 (by rfl) ⟨397895, by rfl⟩ : syracuseStep 2122109 = 795791) B795791
theorem B942511 : Blo 742328 942511 := bstep (se 1 (by rfl) ⟨706883, by rfl⟩ : syracuseStep 942511 = 1413767) B1413767
theorem B745903 : Blo 742328 745903 := bstep (se 1 (by rfl) ⟨559427, by rfl⟩ : syracuseStep 745903 = 1118855) B1118855
theorem B745927 : Blo 742328 745927 := bstep (se 1 (by rfl) ⟨559445, by rfl⟩ : syracuseStep 745927 = 1118891) B1118891
theorem B745947 : Blo 742328 745947 := bstep (se 1 (by rfl) ⟨559460, by rfl⟩ : syracuseStep 745947 = 1118921) B1118921
theorem B9069079 : Blo 742328 9069079 := bstep (se 1 (by rfl) ⟨6801809, by rfl⟩ : syracuseStep 9069079 = 13603619) B13603619
theorem B7332377 : Blo 742328 7332377 := bstep (se 2 (by rfl) ⟨2749641, by rfl⟩ : syracuseStep 7332377 = 5499283) B5499283
theorem B2515481 : Blo 742328 2515481 := bstep (se 2 (by rfl) ⟨943305, by rfl⟩ : syracuseStep 2515481 = 1886611) B1886611
theorem B746023 : Blo 742328 746023 := bstep (se 1 (by rfl) ⟨559517, by rfl⟩ : syracuseStep 746023 = 1119035) B1119035
theorem B746063 : Blo 742328 746063 := bstep (se 1 (by rfl) ⟨559547, by rfl⟩ : syracuseStep 746063 = 1119095) B1119095
theorem B746079 : Blo 742328 746079 := bstep (se 1 (by rfl) ⟨559559, by rfl⟩ : syracuseStep 746079 = 1119119) B1119119
theorem B746107 : Blo 742328 746107 := bstep (se 1 (by rfl) ⟨559580, by rfl⟩ : syracuseStep 746107 = 1119161) B1119161
theorem B746159 : Blo 742328 746159 := bstep (se 1 (by rfl) ⟨559619, by rfl⟩ : syracuseStep 746159 = 1119239) B1119239
theorem B746183 : Blo 742328 746183 := bstep (se 1 (by rfl) ⟨559637, by rfl⟩ : syracuseStep 746183 = 1119275) B1119275
theorem B746203 : Blo 742328 746203 := bstep (se 1 (by rfl) ⟨559652, by rfl⟩ : syracuseStep 746203 = 1119305) B1119305
theorem B2679581 : Blo 742328 2679581 := bstep (se 3 (by rfl) ⟨502421, by rfl⟩ : syracuseStep 2679581 = 1004843) B1004843
theorem B746279 : Blo 742328 746279 := bstep (se 1 (by rfl) ⟨559709, by rfl⟩ : syracuseStep 746279 = 1119419) B1119419
theorem B746319 : Blo 742328 746319 := bstep (se 1 (by rfl) ⟨559739, by rfl⟩ : syracuseStep 746319 = 1119479) B1119479
theorem B2548655 : Blo 742328 2548655 := bstep (se 1 (by rfl) ⟨1911491, by rfl⟩ : syracuseStep 2548655 = 3822983) B3822983
theorem B3761153 : Blo 742328 3761153 := bstep (se 2 (by rfl) ⟨1410432, by rfl⟩ : syracuseStep 3761153 = 2820865) B2820865
theorem B1008649 : Blo 742328 1008649 := bstep (se 2 (by rfl) ⟨378243, by rfl⟩ : syracuseStep 1008649 = 756487) B756487
theorem B5661899 : Blo 742328 5661899 := bstep (se 1 (by rfl) ⟨4246424, by rfl⟩ : syracuseStep 5661899 = 8492849) B8492849
theorem B10184051 : Blo 742328 10184051 := bstep (se 1 (by rfl) ⟨7638038, by rfl⟩ : syracuseStep 10184051 = 15276077) B15276077
theorem B3827087 : Blo 742328 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B943579 : Blo 742328 943579 := bstep (se 1 (by rfl) ⟨707684, by rfl⟩ : syracuseStep 943579 = 1415369) B1415369
theorem B2516615 : Blo 742328 2516615 := bstep (se 1 (by rfl) ⟨1887461, by rfl⟩ : syracuseStep 2516615 = 3774923) B3774923
theorem B2516669 : Blo 742328 2516669 := bstep (se 3 (by rfl) ⟨471875, by rfl⟩ : syracuseStep 2516669 = 943751) B943751
theorem B3761963 : Blo 742328 3761963 := bstep (se 1 (by rfl) ⟨2821472, by rfl⟩ : syracuseStep 3761963 = 5642945) B5642945
theorem B2516831 : Blo 742328 2516831 := bstep (se 1 (by rfl) ⟨1887623, by rfl⟩ : syracuseStep 2516831 = 3775247) B3775247
theorem B2516993 : Blo 742328 2516993 := bstep (se 2 (by rfl) ⟨943872, by rfl⟩ : syracuseStep 2516993 = 1887745) B1887745
theorem B2123783 : Blo 742328 2123783 := bstep (se 1 (by rfl) ⟨1592837, by rfl⟩ : syracuseStep 2123783 = 3185675) B3185675
theorem B1435897 : Blo 742328 1435897 := bstep (se 2 (by rfl) ⟨538461, by rfl⟩ : syracuseStep 1435897 = 1076923) B1076923
theorem B9529649 : Blo 742328 9529649 := bstep (se 2 (by rfl) ⟨3573618, by rfl⟩ : syracuseStep 9529649 = 7147237) B7147237
theorem B2681369 : Blo 742328 2681369 := bstep (se 2 (by rfl) ⟨1005513, by rfl⟩ : syracuseStep 2681369 = 2011027) B2011027
theorem B9562657 : Blo 742328 9562657 := bstep (se 2 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 9562657 = 7171993) B7171993
theorem B2517803 : Blo 742328 2517803 := bstep (se 1 (by rfl) ⟨1888352, by rfl⟩ : syracuseStep 2517803 = 3776705) B3776705
theorem B2518073 : Blo 742328 2518073 := bstep (se 2 (by rfl) ⟨944277, by rfl⟩ : syracuseStep 2518073 = 1888555) B1888555
theorem B2518397 : Blo 742328 2518397 := bstep (se 3 (by rfl) ⟨472199, by rfl⟩ : syracuseStep 2518397 = 944399) B944399
theorem B2518667 : Blo 742328 2518667 := bstep (se 1 (by rfl) ⟨1889000, by rfl⟩ : syracuseStep 2518667 = 3778001) B3778001
theorem B3010247 : Blo 742328 3010247 := bstep (se 1 (by rfl) ⟨2257685, by rfl⟩ : syracuseStep 3010247 = 4515371) B4515371
theorem B1634003 : Blo 742328 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B3764231 : Blo 742328 3764231 := bstep (se 1 (by rfl) ⟨2823173, by rfl⟩ : syracuseStep 3764231 = 5646347) B5646347
theorem B2617661 : Blo 742328 2617661 := bstep (se 3 (by rfl) ⟨490811, by rfl⟩ : syracuseStep 2617661 = 981623) B981623
theorem B3764717 : Blo 742328 3764717 := bstep (se 3 (by rfl) ⟨705884, by rfl⟩ : syracuseStep 3764717 = 1411769) B1411769
theorem B1274491 : Blo 742328 1274491 := bstep (se 1 (by rfl) ⟨955868, by rfl⟩ : syracuseStep 1274491 = 1911737) B1911737
theorem B3568313 : Blo 742328 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B9532313 : Blo 742328 9532313 := bstep (se 2 (by rfl) ⟨3574617, by rfl⟩ : syracuseStep 9532313 = 7149235) B7149235
theorem B2388923 : Blo 742328 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B5370923 : Blo 742328 5370923 := bstep (se 1 (by rfl) ⟨4028192, by rfl⟩ : syracuseStep 5370923 = 8056385) B8056385
theorem B4781227 : Blo 742328 4781227 := bstep (se 1 (by rfl) ⟨3585920, by rfl⟩ : syracuseStep 4781227 = 7171841) B7171841
theorem B3765527 : Blo 742328 3765527 := bstep (se 1 (by rfl) ⟨2824145, by rfl⟩ : syracuseStep 3765527 = 5648291) B5648291
theorem B2389537 : Blo 742328 2389537 := bstep (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) B1792153
theorem B3569275 : Blo 742328 3569275 := bstep (se 1 (by rfl) ⟨2676956, by rfl⟩ : syracuseStep 3569275 = 5353913) B5353913
theorem B2684539 : Blo 742328 2684539 := bstep (se 1 (by rfl) ⟨2013404, by rfl⟩ : syracuseStep 2684539 = 4026809) B4026809
theorem B1341289 : Blo 742328 1341289 := bstep (se 2 (by rfl) ⟨502983, by rfl⟩ : syracuseStep 1341289 = 1005967) B1005967
theorem B12089249 : Blo 742328 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B1210447 : Blo 742328 1210447 := bstep (se 1 (by rfl) ⟨907835, by rfl⟩ : syracuseStep 1210447 = 1815671) B1815671
theorem B2685449 : Blo 742328 2685449 := bstep (se 2 (by rfl) ⟨1007043, by rfl⟩ : syracuseStep 2685449 = 2014087) B2014087
theorem B3767147 : Blo 742328 3767147 := bstep (se 1 (by rfl) ⟨2825360, by rfl⟩ : syracuseStep 3767147 = 5650721) B5650721
theorem B3177643 : Blo 742328 3177643 := bstep (se 1 (by rfl) ⟨2383232, by rfl⟩ : syracuseStep 3177643 = 4766465) B4766465
theorem B1670543 : Blo 742328 1670543 := bstep (se 1 (by rfl) ⟨1252907, by rfl⟩ : syracuseStep 1670543 = 2505815) B2505815
theorem B1113527 : Blo 742328 1113527 := bstep (se 1 (by rfl) ⟨835145, by rfl⟩ : syracuseStep 1113527 = 1670291) B1670291
theorem B1113563 : Blo 742328 1113563 := bstep (se 1 (by rfl) ⟨835172, by rfl⟩ : syracuseStep 1113563 = 1670345) B1670345
theorem B3767795 : Blo 742328 3767795 := bstep (se 1 (by rfl) ⟨2825846, by rfl⟩ : syracuseStep 3767795 = 5651693) B5651693
theorem B10878583 : Blo 742328 10878583 := bstep (se 1 (by rfl) ⟨8158937, by rfl⟩ : syracuseStep 10878583 = 16317875) B16317875
theorem B3014267 : Blo 742328 3014267 := bstep (se 1 (by rfl) ⟨2260700, by rfl⟩ : syracuseStep 3014267 = 4521401) B4521401
theorem B1670867 : Blo 742328 1670867 := bstep (se 1 (by rfl) ⟨1253150, by rfl⟩ : syracuseStep 1670867 = 2506301) B2506301
theorem B1114031 : Blo 742328 1114031 := bstep (se 1 (by rfl) ⟨835523, by rfl⟩ : syracuseStep 1114031 = 1671047) B1671047
theorem B1114217 : Blo 742328 1114217 := bstep (se 2 (by rfl) ⟨417831, by rfl⟩ : syracuseStep 1114217 = 835663) B835663
theorem B3178601 : Blo 742328 3178601 := bstep (se 2 (by rfl) ⟨1191975, by rfl⟩ : syracuseStep 3178601 = 2383951) B2383951
theorem B1671497 : Blo 742328 1671497 := bstep (se 2 (by rfl) ⟨626811, by rfl⟩ : syracuseStep 1671497 = 1253623) B1253623
theorem B1671515 : Blo 742328 1671515 := bstep (se 1 (by rfl) ⟨1253636, by rfl⟩ : syracuseStep 1671515 = 2507273) B2507273
theorem B6455717 : Blo 742328 6455717 := bstep (se 4 (by rfl) ⟨605223, by rfl⟩ : syracuseStep 6455717 = 1210447) B1210447
theorem B1114535 : Blo 742328 1114535 := bstep (se 1 (by rfl) ⟨835901, by rfl⟩ : syracuseStep 1114535 = 1671803) B1671803
theorem B1409491 : Blo 742328 1409491 := bstep (se 1 (by rfl) ⟨1057118, by rfl⟩ : syracuseStep 1409491 = 2114237) B2114237
theorem B6357473 : Blo 742328 6357473 := bstep (se 2 (by rfl) ⟨2384052, by rfl⟩ : syracuseStep 6357473 = 4768105) B4768105
theorem B1114619 : Blo 742328 1114619 := bstep (se 1 (by rfl) ⟨835964, by rfl⟩ : syracuseStep 1114619 = 1671929) B1671929
theorem B3768929 : Blo 742328 3768929 := bstep (se 2 (by rfl) ⟨1413348, by rfl⟩ : syracuseStep 3768929 = 2826697) B2826697
theorem B1114745 : Blo 742328 1114745 := bstep (se 2 (by rfl) ⟨418029, by rfl⟩ : syracuseStep 1114745 = 836059) B836059
theorem B2261675 : Blo 742328 2261675 := bstep (se 1 (by rfl) ⟨1696256, by rfl⟩ : syracuseStep 2261675 = 3392513) B3392513
theorem B1114799 : Blo 742328 1114799 := bstep (se 1 (by rfl) ⟨836099, by rfl⟩ : syracuseStep 1114799 = 1672199) B1672199
theorem B1409719 : Blo 742328 1409719 := bstep (se 1 (by rfl) ⟨1057289, by rfl⟩ : syracuseStep 1409719 = 2114579) B2114579
theorem B12092105 : Blo 742328 12092105 := bstep (se 2 (by rfl) ⟨4534539, by rfl⟩ : syracuseStep 12092105 = 9069079) B9069079
theorem B1114847 : Blo 742328 1114847 := bstep (se 1 (by rfl) ⟨836135, by rfl⟩ : syracuseStep 1114847 = 1672271) B1672271
theorem B1672091 : Blo 742328 1672091 := bstep (se 1 (by rfl) ⟨1254068, by rfl⟩ : syracuseStep 1672091 = 2508137) B2508137
theorem B1410023 : Blo 742328 1410023 := bstep (se 1 (by rfl) ⟨1057517, by rfl⟩ : syracuseStep 1410023 = 2115035) B2115035
theorem B1115111 : Blo 742328 1115111 := bstep (se 1 (by rfl) ⟨836333, by rfl⟩ : syracuseStep 1115111 = 1672667) B1672667
theorem B1672289 : Blo 742328 1672289 := bstep (se 2 (by rfl) ⟨627108, by rfl⟩ : syracuseStep 1672289 = 1254217) B1254217
theorem B4031633 : Blo 742328 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B65406149 : Blo 742328 65406149 := bstep (se 4 (by rfl) ⟨6131826, by rfl⟩ : syracuseStep 65406149 = 12263653) B12263653
theorem B1410281 : Blo 742328 1410281 := bstep (se 2 (by rfl) ⟨528855, by rfl⟩ : syracuseStep 1410281 = 1057711) B1057711
theorem B1115369 : Blo 742328 1115369 := bstep (se 2 (by rfl) ⟨418263, by rfl⟩ : syracuseStep 1115369 = 836527) B836527
theorem B3769577 : Blo 742328 3769577 := bstep (se 2 (by rfl) ⟨1413591, by rfl⟩ : syracuseStep 3769577 = 2827183) B2827183
theorem B1115423 : Blo 742328 1115423 := bstep (se 1 (by rfl) ⟨836567, by rfl⟩ : syracuseStep 1115423 = 1673135) B1673135
theorem B1672487 : Blo 742328 1672487 := bstep (se 1 (by rfl) ⟨1254365, by rfl⟩ : syracuseStep 1672487 = 2508731) B2508731
theorem B5375281 : Blo 742328 5375281 := bstep (se 2 (by rfl) ⟨2015730, by rfl⟩ : syracuseStep 5375281 = 4031461) B4031461
theorem B1344865 : Blo 742328 1344865 := bstep (se 2 (by rfl) ⟨504324, by rfl⟩ : syracuseStep 1344865 = 1008649) B1008649
theorem B3769739 : Blo 742328 3769739 := bstep (se 1 (by rfl) ⟨2827304, by rfl⟩ : syracuseStep 3769739 = 5654609) B5654609
theorem B1115591 : Blo 742328 1115591 := bstep (se 1 (by rfl) ⟨836693, by rfl⟩ : syracuseStep 1115591 = 1673387) B1673387
theorem B1672865 : Blo 742328 1672865 := bstep (se 2 (by rfl) ⟨627324, by rfl⟩ : syracuseStep 1672865 = 1254649) B1254649
theorem B1115945 : Blo 742328 1115945 := bstep (se 2 (by rfl) ⟨418479, by rfl⟩ : syracuseStep 1115945 = 836959) B836959
theorem B1115951 : Blo 742328 1115951 := bstep (se 1 (by rfl) ⟨836963, by rfl⟩ : syracuseStep 1115951 = 1673927) B1673927
theorem B3180343 : Blo 742328 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B1673225 : Blo 742328 1673225 := bstep (se 2 (by rfl) ⟨627459, by rfl⟩ : syracuseStep 1673225 = 1254919) B1254919
theorem B1411177 : Blo 742328 1411177 := bstep (se 2 (by rfl) ⟨529191, by rfl⟩ : syracuseStep 1411177 = 1058383) B1058383
theorem B1411337 : Blo 742328 1411337 := bstep (se 2 (by rfl) ⟨529251, by rfl⟩ : syracuseStep 1411337 = 1058503) B1058503
theorem B1116425 : Blo 742328 1116425 := bstep (se 2 (by rfl) ⟨418659, by rfl⟩ : syracuseStep 1116425 = 837319) B837319
theorem B1116527 : Blo 742328 1116527 := bstep (se 1 (by rfl) ⟨837395, by rfl⟩ : syracuseStep 1116527 = 1674791) B1674791
theorem B1673639 : Blo 742328 1673639 := bstep (se 1 (by rfl) ⟨1255229, by rfl⟩ : syracuseStep 1673639 = 2510459) B2510459
theorem B1673747 : Blo 742328 1673747 := bstep (se 1 (by rfl) ⟨1255310, by rfl⟩ : syracuseStep 1673747 = 2510621) B2510621
theorem B1116743 : Blo 742328 1116743 := bstep (se 1 (by rfl) ⟨837557, by rfl⟩ : syracuseStep 1116743 = 1675115) B1675115
theorem B1673801 : Blo 742328 1673801 := bstep (se 2 (by rfl) ⟨627675, by rfl⟩ : syracuseStep 1673801 = 1255351) B1255351
theorem B1116779 : Blo 742328 1116779 := bstep (se 1 (by rfl) ⟨837584, by rfl⟩ : syracuseStep 1116779 = 1675169) B1675169
theorem B1117007 : Blo 742328 1117007 := bstep (se 1 (by rfl) ⟨837755, by rfl⟩ : syracuseStep 1117007 = 1675511) B1675511
theorem B1674215 : Blo 742328 1674215 := bstep (se 1 (by rfl) ⟨1255661, by rfl⟩ : syracuseStep 1674215 = 2511323) B2511323
theorem B7638083 : Blo 742328 7638083 := bstep (se 1 (by rfl) ⟨5728562, by rfl⟩ : syracuseStep 7638083 = 11457125) B11457125
theorem B1117403 : Blo 742328 1117403 := bstep (se 1 (by rfl) ⟨838052, by rfl⟩ : syracuseStep 1117403 = 1676105) B1676105
theorem B1674593 : Blo 742328 1674593 := bstep (se 2 (by rfl) ⟨627972, by rfl⟩ : syracuseStep 1674593 = 1255945) B1255945
theorem B5639543 : Blo 742328 5639543 := bstep (se 1 (by rfl) ⟨4229657, by rfl⟩ : syracuseStep 5639543 = 8459315) B8459315
theorem B12750209 : Blo 742328 12750209 := bstep (se 2 (by rfl) ⟨4781328, by rfl⟩ : syracuseStep 12750209 = 9562657) B9562657
theorem B1117577 : Blo 742328 1117577 := bstep (se 2 (by rfl) ⟨419091, by rfl⟩ : syracuseStep 1117577 = 838183) B838183
theorem B1674683 : Blo 742328 1674683 := bstep (se 1 (by rfl) ⟨1256012, by rfl⟩ : syracuseStep 1674683 = 2512025) B2512025
theorem B2821625 : Blo 742328 2821625 := bstep (se 2 (by rfl) ⟨1058109, by rfl⟩ : syracuseStep 2821625 = 2116219) B2116219
theorem B10718729 : Blo 742328 10718729 := bstep (se 2 (by rfl) ⟨4019523, by rfl⟩ : syracuseStep 10718729 = 8039047) B8039047
theorem B1674809 : Blo 742328 1674809 := bstep (se 2 (by rfl) ⟨628053, by rfl⟩ : syracuseStep 1674809 = 1256107) B1256107
theorem B1412795 : Blo 742328 1412795 := bstep (se 1 (by rfl) ⟨1059596, by rfl⟩ : syracuseStep 1412795 = 2119193) B2119193
theorem B3182291 : Blo 742328 3182291 := bstep (se 1 (by rfl) ⟨2386718, by rfl⟩ : syracuseStep 3182291 = 4773437) B4773437
theorem B1117931 : Blo 742328 1117931 := bstep (se 1 (by rfl) ⟨838448, by rfl⟩ : syracuseStep 1117931 = 1676897) B1676897
theorem B6360889 : Blo 742328 6360889 := bstep (se 2 (by rfl) ⟨2385333, by rfl⟩ : syracuseStep 6360889 = 4770667) B4770667
theorem B1118159 : Blo 742328 1118159 := bstep (se 1 (by rfl) ⟨838619, by rfl⟩ : syracuseStep 1118159 = 1677239) B1677239
theorem B1675475 : Blo 742328 1675475 := bstep (se 1 (by rfl) ⟨1256606, by rfl⟩ : syracuseStep 1675475 = 2513213) B2513213
theorem B1675529 : Blo 742328 1675529 := bstep (se 2 (by rfl) ⟨628323, by rfl⟩ : syracuseStep 1675529 = 1256647) B1256647
theorem B3576155 : Blo 742328 3576155 := bstep (se 1 (by rfl) ⟨2682116, by rfl⟩ : syracuseStep 3576155 = 5364233) B5364233
theorem B1118555 : Blo 742328 1118555 := bstep (se 1 (by rfl) ⟨838916, by rfl⟩ : syracuseStep 1118555 = 1677833) B1677833
theorem B1675745 : Blo 742328 1675745 := bstep (se 2 (by rfl) ⟨628404, by rfl⟩ : syracuseStep 1675745 = 1256809) B1256809
theorem B3772979 : Blo 742328 3772979 := bstep (se 1 (by rfl) ⟨2829734, by rfl⟩ : syracuseStep 3772979 = 5659469) B5659469
theorem B1118783 : Blo 742328 1118783 := bstep (se 1 (by rfl) ⟨839087, by rfl⟩ : syracuseStep 1118783 = 1678175) B1678175
theorem B2822809 : Blo 742328 2822809 := bstep (se 2 (by rfl) ⟨1058553, by rfl⟩ : syracuseStep 2822809 = 2117107) B2117107
theorem B1118903 : Blo 742328 1118903 := bstep (se 1 (by rfl) ⟨839177, by rfl⟩ : syracuseStep 1118903 = 1678355) B1678355
theorem B1676051 : Blo 742328 1676051 := bstep (se 1 (by rfl) ⟨1257038, by rfl⟩ : syracuseStep 1676051 = 2514077) B2514077
theorem B1020713 : Blo 742328 1020713 := bstep (se 2 (by rfl) ⟨382767, by rfl⟩ : syracuseStep 1020713 = 765535) B765535
theorem B1119131 : Blo 742328 1119131 := bstep (se 1 (by rfl) ⟨839348, by rfl⟩ : syracuseStep 1119131 = 1678697) B1678697
theorem B2823113 : Blo 742328 2823113 := bstep (se 2 (by rfl) ⟨1058667, by rfl⟩ : syracuseStep 2823113 = 2117335) B2117335
theorem B1676411 : Blo 742328 1676411 := bstep (se 1 (by rfl) ⟨1257308, by rfl⟩ : syracuseStep 1676411 = 2514617) B2514617
theorem B1676537 : Blo 742328 1676537 := bstep (se 2 (by rfl) ⟨628701, by rfl⟩ : syracuseStep 1676537 = 1257403) B1257403
theorem B1676681 : Blo 742328 1676681 := bstep (se 2 (by rfl) ⟨628755, by rfl⟩ : syracuseStep 1676681 = 1257511) B1257511
theorem B11474369 : Blo 742328 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B1676807 : Blo 742328 1676807 := bstep (se 1 (by rfl) ⟨1257605, by rfl⟩ : syracuseStep 1676807 = 2515211) B2515211
theorem B1414739 : Blo 742328 1414739 := bstep (se 1 (by rfl) ⟨1061054, by rfl⟩ : syracuseStep 1414739 = 2122109) B2122109
theorem B1676987 : Blo 742328 1676987 := bstep (se 1 (by rfl) ⟨1257740, by rfl⟩ : syracuseStep 1676987 = 2515481) B2515481
theorem B6788893 : Blo 742328 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B1677113 : Blo 742328 1677113 := bstep (se 2 (by rfl) ⟨628917, by rfl⟩ : syracuseStep 1677113 = 1257835) B1257835
theorem B3774599 : Blo 742328 3774599 := bstep (se 1 (by rfl) ⟨2830949, by rfl⟩ : syracuseStep 3774599 = 5661899) B5661899
theorem B6789367 : Blo 742328 6789367 := bstep (se 1 (by rfl) ⟨5092025, by rfl⟩ : syracuseStep 6789367 = 10184051) B10184051
theorem B1677743 : Blo 742328 1677743 := bstep (se 1 (by rfl) ⟨1258307, by rfl⟩ : syracuseStep 1677743 = 2516615) B2516615
theorem B1677779 : Blo 742328 1677779 := bstep (se 1 (by rfl) ⟨1258334, by rfl⟩ : syracuseStep 1677779 = 2516669) B2516669
theorem B1677887 : Blo 742328 1677887 := bstep (se 1 (by rfl) ⟨1258415, by rfl⟩ : syracuseStep 1677887 = 2516831) B2516831
theorem B1940089 : Blo 742328 1940089 := bstep (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) B1455067
theorem B1677995 : Blo 742328 1677995 := bstep (se 1 (by rfl) ⟨1258496, by rfl⟩ : syracuseStep 1677995 = 2516993) B2516993
theorem B1415855 : Blo 742328 1415855 := bstep (se 1 (by rfl) ⟨1061891, by rfl⟩ : syracuseStep 1415855 = 2123783) B2123783
theorem B99195749 : Blo 742328 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B1678535 : Blo 742328 1678535 := bstep (se 1 (by rfl) ⟨1258901, by rfl⟩ : syracuseStep 1678535 = 2517803) B2517803
theorem B1678715 : Blo 742328 1678715 := bstep (se 1 (by rfl) ⟨1259036, by rfl⟩ : syracuseStep 1678715 = 2518073) B2518073
theorem B3186049 : Blo 742328 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B4759033 : Blo 742328 4759033 := bstep (se 2 (by rfl) ⟨1784637, by rfl⟩ : syracuseStep 4759033 = 3569275) B3569275
theorem B3579385 : Blo 742328 3579385 := bstep (se 2 (by rfl) ⟨1342269, by rfl⟩ : syracuseStep 3579385 = 2684539) B2684539
theorem B1678841 : Blo 742328 1678841 := bstep (se 2 (by rfl) ⟨629565, by rfl⟩ : syracuseStep 1678841 = 1259131) B1259131
theorem B1678931 : Blo 742328 1678931 := bstep (se 1 (by rfl) ⟨1259198, by rfl⟩ : syracuseStep 1678931 = 2518397) B2518397
theorem B1679111 : Blo 742328 1679111 := bstep (se 1 (by rfl) ⟨1259333, by rfl⟩ : syracuseStep 1679111 = 2518667) B2518667
theorem B2006831 : Blo 742328 2006831 := bstep (se 1 (by rfl) ⟨1505123, by rfl⟩ : syracuseStep 2006831 = 3010247) B3010247
theorem B1089335 : Blo 742328 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B10756145 : Blo 742328 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B1745107 : Blo 742328 1745107 := bstep (se 1 (by rfl) ⟨1308830, by rfl⟩ : syracuseStep 1745107 = 2617661) B2617661
theorem B794971 : Blo 742328 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B3580615 : Blo 742328 3580615 := bstep (se 1 (by rfl) ⟨2685461, by rfl⟩ : syracuseStep 3580615 = 5370923) B5370923
theorem B4236857 : Blo 742328 4236857 := bstep (se 2 (by rfl) ⟨1588821, by rfl⟩ : syracuseStep 4236857 = 3177643) B3177643
theorem B1255007 : Blo 742328 1255007 := bstep (se 1 (by rfl) ⟨941255, by rfl⟩ : syracuseStep 1255007 = 1882511) B1882511
theorem B8038045 : Blo 742328 8038045 := bstep (se 3 (by rfl) ⟨1507133, by rfl⟩ : syracuseStep 8038045 = 3014267) B3014267
theorem B1255223 : Blo 742328 1255223 := bstep (se 1 (by rfl) ⟨941417, by rfl⟩ : syracuseStep 1255223 = 1882835) B1882835
theorem B7153541 : Blo 742328 7153541 := bstep (se 4 (by rfl) ⟨670644, by rfl⟩ : syracuseStep 7153541 = 1341289) B1341289
theorem B6367247 : Blo 742328 6367247 := bstep (se 1 (by rfl) ⟨4775435, by rfl⟩ : syracuseStep 6367247 = 9550871) B9550871
theorem B3025025 : Blo 742328 3025025 := bstep (se 2 (by rfl) ⟨1134384, by rfl⟩ : syracuseStep 3025025 = 2268769) B2268769
theorem B1255999 : Blo 742328 1255999 := bstep (se 1 (by rfl) ⟨941999, by rfl⟩ : syracuseStep 1255999 = 1883999) B1883999
theorem B11447261 : Blo 742328 11447261 := bstep (se 3 (by rfl) ⟨2146361, by rfl⟩ : syracuseStep 11447261 = 4292723) B4292723
theorem B1256681 : Blo 742328 1256681 := bstep (se 2 (by rfl) ⟨471255, by rfl⟩ : syracuseStep 1256681 = 942511) B942511
theorem B1256735 : Blo 742328 1256735 := bstep (se 1 (by rfl) ⟨942551, by rfl⟩ : syracuseStep 1256735 = 1885103) B1885103
theorem B2829599 : Blo 742328 2829599 := bstep (se 1 (by rfl) ⟨2122199, by rfl⟩ : syracuseStep 2829599 = 4244399) B4244399
theorem B1879433 : Blo 742328 1879433 := bstep (se 2 (by rfl) ⟨704787, by rfl⟩ : syracuseStep 1879433 = 1409575) B1409575
theorem B1879483 : Blo 742328 1879483 := bstep (se 1 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 1879483 = 2819225) B2819225
theorem B1879787 : Blo 742328 1879787 := bstep (se 1 (by rfl) ⟨1409840, by rfl⟩ : syracuseStep 1879787 = 2819681) B2819681
theorem B6435073 : Blo 742328 6435073 := bstep (se 2 (by rfl) ⟨2413152, by rfl⟩ : syracuseStep 6435073 = 4826305) B4826305
theorem B9515501 : Blo 742328 9515501 := bstep (se 3 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 9515501 = 3568313) B3568313
theorem B14299699 : Blo 742328 14299699 := bstep (se 1 (by rfl) ⟨10724774, by rfl⟩ : syracuseStep 14299699 = 21449549) B21449549
theorem B1258105 : Blo 742328 1258105 := bstep (se 2 (by rfl) ⟨471789, by rfl⟩ : syracuseStep 1258105 = 943579) B943579
theorem B4240025 : Blo 742328 4240025 := bstep (se 2 (by rfl) ⟨1590009, by rfl⟩ : syracuseStep 4240025 = 3180019) B3180019
theorem B1258159 : Blo 742328 1258159 := bstep (se 1 (by rfl) ⟨943619, by rfl⟩ : syracuseStep 1258159 = 1887239) B1887239
theorem B1880759 : Blo 742328 1880759 := bstep (se 1 (by rfl) ⟨1410569, by rfl⟩ : syracuseStep 1880759 = 2821139) B2821139
theorem B2831071 : Blo 742328 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B3584999 : Blo 742328 3584999 := bstep (se 1 (by rfl) ⟨2688749, by rfl⟩ : syracuseStep 3584999 = 5377499) B5377499
theorem B1586395 : Blo 742328 1586395 := bstep (se 1 (by rfl) ⟨1189796, by rfl⟩ : syracuseStep 1586395 = 2379593) B2379593
theorem B12039425 : Blo 742328 12039425 := bstep (se 2 (by rfl) ⟨4514784, by rfl⟩ : syracuseStep 12039425 = 9029569) B9029569
theorem B2832029 : Blo 742328 2832029 := bstep (se 3 (by rfl) ⟨531005, by rfl⟩ : syracuseStep 2832029 = 1062011) B1062011
theorem B1914529 : Blo 742328 1914529 := bstep (se 2 (by rfl) ⟨717948, by rfl⟩ : syracuseStep 1914529 = 1435897) B1435897
theorem B1881863 : Blo 742328 1881863 := bstep (se 1 (by rfl) ⟨1411397, by rfl⟩ : syracuseStep 1881863 = 2822795) B2822795
theorem B1881913 : Blo 742328 1881913 := bstep (se 2 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 1881913 = 1411435) B1411435
theorem B1882217 : Blo 742328 1882217 := bstep (se 2 (by rfl) ⟨705831, by rfl⟩ : syracuseStep 1882217 = 1411663) B1411663
theorem B20363399 : Blo 742328 20363399 := bstep (se 1 (by rfl) ⟨15272549, by rfl⟩ : syracuseStep 20363399 = 30545099) B30545099
theorem B4241915 : Blo 742328 4241915 := bstep (se 1 (by rfl) ⟨3181436, by rfl⟩ : syracuseStep 4241915 = 6362873) B6362873
theorem B1882703 : Blo 742328 1882703 := bstep (se 1 (by rfl) ⟨1412027, by rfl⟩ : syracuseStep 1882703 = 2824055) B2824055
theorem B1194679 : Blo 742328 1194679 := bstep (se 1 (by rfl) ⟨896009, by rfl⟩ : syracuseStep 1194679 = 1792019) B1792019
theorem B2505491 : Blo 742328 2505491 := bstep (se 1 (by rfl) ⟨1879118, by rfl⟩ : syracuseStep 2505491 = 3758237) B3758237
theorem B2014183 : Blo 742328 2014183 := bstep (se 1 (by rfl) ⟨1510637, by rfl⟩ : syracuseStep 2014183 = 3021275) B3021275
theorem B6372371 : Blo 742328 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B1883351 : Blo 742328 1883351 := bstep (se 1 (by rfl) ⟨1412513, by rfl⟩ : syracuseStep 1883351 = 2825027) B2825027
theorem B1228169 : Blo 742328 1228169 := bstep (se 2 (by rfl) ⟨460563, by rfl⟩ : syracuseStep 1228169 = 921127) B921127
theorem B2506355 : Blo 742328 2506355 := bstep (se 1 (by rfl) ⟨1879766, by rfl⟩ : syracuseStep 2506355 = 3759533) B3759533
theorem B835375 : Blo 742328 835375 := bstep (se 1 (by rfl) ⟨626531, by rfl⟩ : syracuseStep 835375 = 1253063) B1253063
theorem B2506625 : Blo 742328 2506625 := bstep (se 2 (by rfl) ⟨939984, by rfl⟩ : syracuseStep 2506625 = 1879969) B1879969
theorem B835483 : Blo 742328 835483 := bstep (se 1 (by rfl) ⟨626612, by rfl⟩ : syracuseStep 835483 = 1253225) B1253225
theorem B10862693 : Blo 742328 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B835879 : Blo 742328 835879 := bstep (se 1 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 835879 = 1253819) B1253819
theorem B2539883 : Blo 742328 2539883 := bstep (se 1 (by rfl) ⟨1904912, by rfl⟩ : syracuseStep 2539883 = 3809825) B3809825
theorem B835951 : Blo 742328 835951 := bstep (se 1 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 835951 = 1253927) B1253927
theorem B13746617 : Blo 742328 13746617 := bstep (se 2 (by rfl) ⟨5154981, by rfl⟩ : syracuseStep 13746617 = 10309963) B10309963
theorem B1884667 : Blo 742328 1884667 := bstep (se 1 (by rfl) ⟨1413500, by rfl⟩ : syracuseStep 1884667 = 2827001) B2827001
theorem B1786387 : Blo 742328 1786387 := bstep (se 1 (by rfl) ⟨1339790, by rfl⟩ : syracuseStep 1786387 = 2679581) B2679581
theorem B836167 : Blo 742328 836167 := bstep (se 1 (by rfl) ⟨627125, by rfl⟩ : syracuseStep 836167 = 1254251) B1254251
theorem B1884779 : Blo 742328 1884779 := bstep (se 1 (by rfl) ⟨1413584, by rfl⟩ : syracuseStep 1884779 = 2827169) B2827169
theorem B1589881 : Blo 742328 1589881 := bstep (se 2 (by rfl) ⟨596205, by rfl⟩ : syracuseStep 1589881 = 1192411) B1192411
theorem B2507435 : Blo 742328 2507435 := bstep (se 1 (by rfl) ⟨1880576, by rfl⟩ : syracuseStep 2507435 = 3761153) B3761153
theorem B2507975 : Blo 742328 2507975 := bstep (se 1 (by rfl) ⟨1880981, by rfl⟩ : syracuseStep 2507975 = 3761963) B3761963
theorem B1885427 : Blo 742328 1885427 := bstep (se 1 (by rfl) ⟨1414070, by rfl⟩ : syracuseStep 1885427 = 2828141) B2828141
theorem B837031 : Blo 742328 837031 := bstep (se 1 (by rfl) ⟨627773, by rfl⟩ : syracuseStep 837031 = 1255547) B1255547
theorem B1885639 : Blo 742328 1885639 := bstep (se 1 (by rfl) ⟨1414229, by rfl⟩ : syracuseStep 1885639 = 2828459) B2828459
theorem B6374969 : Blo 742328 6374969 := bstep (se 2 (by rfl) ⟨2390613, by rfl⟩ : syracuseStep 6374969 = 4781227) B4781227
theorem B4769437 : Blo 742328 4769437 := bstep (se 3 (by rfl) ⟨894269, by rfl⟩ : syracuseStep 4769437 = 1788539) B1788539
theorem B4245149 : Blo 742328 4245149 := bstep (se 3 (by rfl) ⟨795965, by rfl⟩ : syracuseStep 4245149 = 1591931) B1591931
theorem B1787579 : Blo 742328 1787579 := bstep (se 1 (by rfl) ⟨1340684, by rfl⟩ : syracuseStep 1787579 = 2681369) B2681369
theorem B837607 : Blo 742328 837607 := bstep (se 1 (by rfl) ⟨628205, by rfl⟩ : syracuseStep 837607 = 1256411) B1256411
theorem B25741925 : Blo 742328 25741925 := bstep (se 4 (by rfl) ⟨2413305, by rfl⟩ : syracuseStep 25741925 = 4826611) B4826611
theorem B2509487 : Blo 742328 2509487 := bstep (se 1 (by rfl) ⟨1882115, by rfl⟩ : syracuseStep 2509487 = 3764231) B3764231
theorem B5360519 : Blo 742328 5360519 := bstep (se 1 (by rfl) ⟨4020389, by rfl⟩ : syracuseStep 5360519 = 8040779) B8040779
theorem B2509811 : Blo 742328 2509811 := bstep (se 1 (by rfl) ⟨1882358, by rfl⟩ : syracuseStep 2509811 = 3764717) B3764717
theorem B1887371 : Blo 742328 1887371 := bstep (se 1 (by rfl) ⟨1415528, by rfl⟩ : syracuseStep 1887371 = 2831057) B2831057
theorem B1592615 : Blo 742328 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B1887583 : Blo 742328 1887583 := bstep (se 1 (by rfl) ⟨1415687, by rfl⟩ : syracuseStep 1887583 = 2831375) B2831375
theorem B1428833 : Blo 742328 1428833 := bstep (se 2 (by rfl) ⟨535812, by rfl⟩ : syracuseStep 1428833 = 1071625) B1071625
theorem B2510351 : Blo 742328 2510351 := bstep (se 1 (by rfl) ⟨1882763, by rfl⟩ : syracuseStep 2510351 = 3765527) B3765527
theorem B839263 : Blo 742328 839263 := bstep (se 1 (by rfl) ⟨629447, by rfl⟩ : syracuseStep 839263 = 1258895) B1258895
theorem B6344729 : Blo 742328 6344729 := bstep (se 2 (by rfl) ⟨2379273, by rfl⟩ : syracuseStep 6344729 = 4758547) B4758547
theorem B2412569 : Blo 742328 2412569 := bstep (se 2 (by rfl) ⟨904713, by rfl⟩ : syracuseStep 2412569 = 1809427) B1809427
theorem B1790299 : Blo 742328 1790299 := bstep (se 1 (by rfl) ⟨1342724, by rfl⟩ : syracuseStep 1790299 = 2685449) B2685449
theorem B2511431 : Blo 742328 2511431 := bstep (se 1 (by rfl) ⟨1883573, by rfl⟩ : syracuseStep 2511431 = 3767147) B3767147
theorem B1888991 : Blo 742328 1888991 := bstep (se 1 (by rfl) ⟨1416743, by rfl⟩ : syracuseStep 1888991 = 2833487) B2833487
theorem B14504777 : Blo 742328 14504777 := bstep (se 2 (by rfl) ⟨5439291, by rfl⟩ : syracuseStep 14504777 = 10878583) B10878583
theorem B4248521 : Blo 742328 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B742351 : Blo 742328 742351 := bstep (se 1 (by rfl) ⟨556763, by rfl⟩ : syracuseStep 742351 = 1113527) B1113527
theorem B742375 : Blo 742328 742375 := bstep (se 1 (by rfl) ⟨556781, by rfl⟩ : syracuseStep 742375 = 1113563) B1113563
theorem B2511863 : Blo 742328 2511863 := bstep (se 1 (by rfl) ⟨1883897, by rfl⟩ : syracuseStep 2511863 = 3767795) B3767795
theorem B3921095 : Blo 742328 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B742687 : Blo 742328 742687 := bstep (se 1 (by rfl) ⟨557015, by rfl⟩ : syracuseStep 742687 = 1114031) B1114031
theorem B742747 : Blo 742328 742747 := bstep (se 1 (by rfl) ⟨557060, by rfl⟩ : syracuseStep 742747 = 1114121) B1114121
theorem B742767 : Blo 742328 742767 := bstep (se 1 (by rfl) ⟨557075, by rfl⟩ : syracuseStep 742767 = 1114151) B1114151
theorem B742823 : Blo 742328 742823 := bstep (se 1 (by rfl) ⟨557117, by rfl⟩ : syracuseStep 742823 = 1114235) B1114235
theorem B742907 : Blo 742328 742907 := bstep (se 1 (by rfl) ⟨557180, by rfl⟩ : syracuseStep 742907 = 1114361) B1114361
theorem B742975 : Blo 742328 742975 := bstep (se 1 (by rfl) ⟨557231, by rfl⟩ : syracuseStep 742975 = 1114463) B1114463
theorem B742983 : Blo 742328 742983 := bstep (se 1 (by rfl) ⟨557237, by rfl⟩ : syracuseStep 742983 = 1114475) B1114475
theorem B743135 : Blo 742328 743135 := bstep (se 1 (by rfl) ⟨557351, by rfl⟩ : syracuseStep 743135 = 1114703) B1114703
theorem B743215 : Blo 742328 743215 := bstep (se 1 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 743215 = 1114823) B1114823
theorem B2512727 : Blo 742328 2512727 := bstep (se 1 (by rfl) ⟨1884545, by rfl⟩ : syracuseStep 2512727 = 3769091) B3769091
theorem B743323 : Blo 742328 743323 := bstep (se 1 (by rfl) ⟨557492, by rfl⟩ : syracuseStep 743323 = 1114985) B1114985
theorem B4020151 : Blo 742328 4020151 := bstep (se 1 (by rfl) ⟨3015113, by rfl⟩ : syracuseStep 4020151 = 6030227) B6030227
theorem B743375 : Blo 742328 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B743399 : Blo 742328 743399 := bstep (se 1 (by rfl) ⟨557549, by rfl⟩ : syracuseStep 743399 = 1115099) B1115099
theorem B13555745 : Blo 742328 13555745 := bstep (se 2 (by rfl) ⟨5083404, by rfl⟩ : syracuseStep 13555745 = 10166809) B10166809
theorem B7166231 : Blo 742328 7166231 := bstep (se 1 (by rfl) ⟨5374673, by rfl⟩ : syracuseStep 7166231 = 10749347) B10749347
theorem B743711 : Blo 742328 743711 := bstep (se 1 (by rfl) ⟨557783, by rfl⟩ : syracuseStep 743711 = 1115567) B1115567
theorem B743771 : Blo 742328 743771 := bstep (se 1 (by rfl) ⟨557828, by rfl⟩ : syracuseStep 743771 = 1115657) B1115657
theorem B743791 : Blo 742328 743791 := bstep (se 1 (by rfl) ⟨557843, by rfl⟩ : syracuseStep 743791 = 1115687) B1115687
theorem B743847 : Blo 742328 743847 := bstep (se 1 (by rfl) ⟨557885, by rfl⟩ : syracuseStep 743847 = 1115771) B1115771
theorem B743931 : Blo 742328 743931 := bstep (se 1 (by rfl) ⟨557948, by rfl⟩ : syracuseStep 743931 = 1115897) B1115897
theorem B8608315 : Blo 742328 8608315 := bstep (se 1 (by rfl) ⟨6456236, by rfl⟩ : syracuseStep 8608315 = 12912473) B12912473
theorem B743999 : Blo 742328 743999 := bstep (se 1 (by rfl) ⟨557999, by rfl⟩ : syracuseStep 743999 = 1115999) B1115999
theorem B4774463 : Blo 742328 4774463 := bstep (se 1 (by rfl) ⟨3580847, by rfl⟩ : syracuseStep 4774463 = 7161695) B7161695
theorem B12737087 : Blo 742328 12737087 := bstep (se 1 (by rfl) ⟨9552815, by rfl⟩ : syracuseStep 12737087 = 19105631) B19105631
theorem B744007 : Blo 742328 744007 := bstep (se 1 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 744007 = 1116011) B1116011
theorem B1694287 : Blo 742328 1694287 := bstep (se 1 (by rfl) ⟨1270715, by rfl⟩ : syracuseStep 1694287 = 2541431) B2541431
theorem B744159 : Blo 742328 744159 := bstep (se 1 (by rfl) ⟨558119, by rfl⟩ : syracuseStep 744159 = 1116239) B1116239
theorem B19553005 : Blo 742328 19553005 := bstep (se 3 (by rfl) ⟨3666188, by rfl⟩ : syracuseStep 19553005 = 7332377) B7332377
theorem B744239 : Blo 742328 744239 := bstep (se 1 (by rfl) ⟨558179, by rfl⟩ : syracuseStep 744239 = 1116359) B1116359
theorem B21486455 : Blo 742328 21486455 := bstep (se 1 (by rfl) ⟨16114841, by rfl⟩ : syracuseStep 21486455 = 32229683) B32229683
theorem B2513807 : Blo 742328 2513807 := bstep (se 1 (by rfl) ⟨1885355, by rfl⟩ : syracuseStep 2513807 = 3770711) B3770711
theorem B744347 : Blo 742328 744347 := bstep (se 1 (by rfl) ⟨558260, by rfl⟩ : syracuseStep 744347 = 1116521) B1116521
theorem B744399 : Blo 742328 744399 := bstep (se 1 (by rfl) ⟨558299, by rfl⟩ : syracuseStep 744399 = 1116599) B1116599
theorem B744423 : Blo 742328 744423 := bstep (se 1 (by rfl) ⟨558317, by rfl⟩ : syracuseStep 744423 = 1116635) B1116635
theorem B7658525 : Blo 742328 7658525 := bstep (se 3 (by rfl) ⟨1435973, by rfl⟩ : syracuseStep 7658525 = 2871947) B2871947
theorem B2120843 : Blo 742328 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B3759371 : Blo 742328 3759371 := bstep (se 1 (by rfl) ⟨2819528, by rfl⟩ : syracuseStep 3759371 = 5639057) B5639057
theorem B744735 : Blo 742328 744735 := bstep (se 1 (by rfl) ⟨558551, by rfl⟩ : syracuseStep 744735 = 1117103) B1117103
theorem B744795 : Blo 742328 744795 := bstep (se 1 (by rfl) ⟨558596, by rfl⟩ : syracuseStep 744795 = 1117193) B1117193
theorem B744815 : Blo 742328 744815 := bstep (se 1 (by rfl) ⟨558611, by rfl⟩ : syracuseStep 744815 = 1117223) B1117223
theorem B744871 : Blo 742328 744871 := bstep (se 1 (by rfl) ⟨558653, by rfl⟩ : syracuseStep 744871 = 1117307) B1117307
theorem B744955 : Blo 742328 744955 := bstep (se 1 (by rfl) ⟨558716, by rfl⟩ : syracuseStep 744955 = 1117433) B1117433
theorem B745023 : Blo 742328 745023 := bstep (se 1 (by rfl) ⟨558767, by rfl⟩ : syracuseStep 745023 = 1117535) B1117535
theorem B745031 : Blo 742328 745031 := bstep (se 1 (by rfl) ⟨558773, by rfl⟩ : syracuseStep 745031 = 1117547) B1117547
theorem B2121299 : Blo 742328 2121299 := bstep (se 1 (by rfl) ⟨1590974, by rfl⟩ : syracuseStep 2121299 = 3181949) B3181949
theorem B12902003 : Blo 742328 12902003 := bstep (se 1 (by rfl) ⟨9676502, by rfl⟩ : syracuseStep 12902003 = 19353005) B19353005
theorem B745183 : Blo 742328 745183 := bstep (se 1 (by rfl) ⟨558887, by rfl⟩ : syracuseStep 745183 = 1117775) B1117775
theorem B745263 : Blo 742328 745263 := bstep (se 1 (by rfl) ⟨558947, by rfl⟩ : syracuseStep 745263 = 1117895) B1117895
theorem B2580353 : Blo 742328 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B745371 : Blo 742328 745371 := bstep (se 1 (by rfl) ⟨559028, by rfl⟩ : syracuseStep 745371 = 1118057) B1118057
theorem B745423 : Blo 742328 745423 := bstep (se 1 (by rfl) ⟨559067, by rfl⟩ : syracuseStep 745423 = 1118135) B1118135
theorem B745447 : Blo 742328 745447 := bstep (se 1 (by rfl) ⟨559085, by rfl⟩ : syracuseStep 745447 = 1118171) B1118171
theorem B2515049 : Blo 742328 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B14278787 : Blo 742328 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B745759 : Blo 742328 745759 := bstep (se 1 (by rfl) ⟨559319, by rfl⟩ : syracuseStep 745759 = 1118639) B1118639
theorem B745819 : Blo 742328 745819 := bstep (se 1 (by rfl) ⟨559364, by rfl⟩ : syracuseStep 745819 = 1118729) B1118729
theorem B745839 : Blo 742328 745839 := bstep (se 1 (by rfl) ⟨559379, by rfl⟩ : syracuseStep 745839 = 1118759) B1118759
theorem B745895 : Blo 742328 745895 := bstep (se 1 (by rfl) ⟨559421, by rfl⟩ : syracuseStep 745895 = 1118843) B1118843
theorem B745979 : Blo 742328 745979 := bstep (se 1 (by rfl) ⟨559484, by rfl⟩ : syracuseStep 745979 = 1118969) B1118969
theorem B746047 : Blo 742328 746047 := bstep (se 1 (by rfl) ⟨559535, by rfl⟩ : syracuseStep 746047 = 1119071) B1119071
theorem B746055 : Blo 742328 746055 := bstep (se 1 (by rfl) ⟨559541, by rfl⟩ : syracuseStep 746055 = 1119083) B1119083
theorem B746207 : Blo 742328 746207 := bstep (se 1 (by rfl) ⟨559655, by rfl⟩ : syracuseStep 746207 = 1119311) B1119311
theorem B16278245 : Blo 742328 16278245 := bstep (se 4 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 16278245 = 3052171) B3052171
theorem B746287 : Blo 742328 746287 := bstep (se 1 (by rfl) ⟨559715, by rfl⟩ : syracuseStep 746287 = 1119431) B1119431
theorem B3760991 : Blo 742328 3760991 := bstep (se 1 (by rfl) ⟨2820743, by rfl⟩ : syracuseStep 3760991 = 5641487) B5641487
theorem B6349751 : Blo 742328 6349751 := bstep (se 1 (by rfl) ⟨4762313, by rfl⟩ : syracuseStep 6349751 = 9524627) B9524627
theorem B2515913 : Blo 742328 2515913 := bstep (se 2 (by rfl) ⟨943467, by rfl⟩ : syracuseStep 2515913 = 1886935) B1886935
theorem B2516183 : Blo 742328 2516183 := bstep (se 1 (by rfl) ⟨1887137, by rfl⟩ : syracuseStep 2516183 = 3774275) B3774275
theorem B2122985 : Blo 742328 2122985 := bstep (se 2 (by rfl) ⟨796119, by rfl⟩ : syracuseStep 2122985 = 1592239) B1592239
theorem B943483 : Blo 742328 943483 := bstep (se 1 (by rfl) ⟨707612, by rfl⟩ : syracuseStep 943483 = 1415225) B1415225
theorem B12871457 : Blo 742328 12871457 := bstep (se 2 (by rfl) ⟨4826796, by rfl⟩ : syracuseStep 12871457 = 9653593) B9653593
theorem B8054963 : Blo 742328 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B16083197 : Blo 742328 16083197 := bstep (se 3 (by rfl) ⟨3015599, by rfl⟩ : syracuseStep 16083197 = 6031199) B6031199
theorem B944551 : Blo 742328 944551 := bstep (se 1 (by rfl) ⟨708413, by rfl⟩ : syracuseStep 944551 = 1416827) B1416827
theorem B2124215 : Blo 742328 2124215 := bstep (se 1 (by rfl) ⟨1593161, by rfl⟩ : syracuseStep 2124215 = 3186323) B3186323
theorem B3172927 : Blo 742328 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B3762935 : Blo 742328 3762935 := bstep (se 1 (by rfl) ⟨2822201, by rfl⟩ : syracuseStep 3762935 = 5644403) B5644403
theorem B7171037 : Blo 742328 7171037 := bstep (se 3 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 7171037 = 2689139) B2689139
theorem B2518235 : Blo 742328 2518235 := bstep (se 1 (by rfl) ⟨1888676, by rfl⟩ : syracuseStep 2518235 = 3777353) B3777353
theorem B3763421 : Blo 742328 3763421 := bstep (se 3 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 3763421 = 1411283) B1411283
theorem B1699103 : Blo 742328 1699103 := bstep (se 1 (by rfl) ⟨1274327, by rfl⟩ : syracuseStep 1699103 = 2548655) B2548655
theorem B1699321 : Blo 742328 1699321 := bstep (se 2 (by rfl) ⟨637245, by rfl⟩ : syracuseStep 1699321 = 1274491) B1274491
theorem B2551391 : Blo 742328 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B14282477 : Blo 742328 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B1273807 : Blo 742328 1273807 := bstep (se 1 (by rfl) ⟨955355, by rfl⟩ : syracuseStep 1273807 = 1910711) B1910711
theorem B6353099 : Blo 742328 6353099 := bstep (se 1 (by rfl) ⟨4764824, by rfl⟩ : syracuseStep 6353099 = 9529649) B9529649
theorem B10186955 : Blo 742328 10186955 := bstep (se 1 (by rfl) ⟨7640216, by rfl⟩ : syracuseStep 10186955 = 15280433) B15280433
theorem B24080921 : Blo 742328 24080921 := bstep (se 2 (by rfl) ⟨9030345, by rfl⟩ : syracuseStep 24080921 = 18060691) B18060691
theorem B2684137 : Blo 742328 2684137 := bstep (se 2 (by rfl) ⟨1006551, by rfl⟩ : syracuseStep 2684137 = 2013103) B2013103
theorem B10712321 : Blo 742328 10712321 := bstep (se 2 (by rfl) ⟨4017120, by rfl⟩ : syracuseStep 10712321 = 8034241) B8034241
theorem B3175969 : Blo 742328 3175969 := bstep (se 2 (by rfl) ⟨1190988, by rfl⟩ : syracuseStep 3175969 = 2381977) B2381977
theorem B173930165 : Blo 742328 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B6354875 : Blo 742328 6354875 := bstep (se 1 (by rfl) ⟨4766156, by rfl⟩ : syracuseStep 6354875 = 9532313) B9532313
theorem B3766823 : Blo 742328 3766823 := bstep (se 1 (by rfl) ⟨2825117, by rfl⟩ : syracuseStep 3766823 = 5650235) B5650235
theorem B14318153 : Blo 742328 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B8059499 : Blo 742328 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B1670363 : Blo 742328 1670363 := bstep (se 1 (by rfl) ⟨1252772, by rfl⟩ : syracuseStep 1670363 = 2505545) B2505545
theorem B1670561 : Blo 742328 1670561 := bstep (se 2 (by rfl) ⟨626460, by rfl⟩ : syracuseStep 1670561 = 1252921) B1252921
theorem B1113593 : Blo 742328 1113593 := bstep (se 2 (by rfl) ⟨417597, by rfl⟩ : syracuseStep 1113593 = 835195) B835195
theorem B1113695 : Blo 742328 1113695 := bstep (se 1 (by rfl) ⟨835271, by rfl⟩ : syracuseStep 1113695 = 1670543) B1670543
theorem B1343071 : Blo 742328 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B4030249 : Blo 742328 4030249 := bstep (se 2 (by rfl) ⟨1511343, by rfl⟩ : syracuseStep 4030249 = 3022687) B3022687
theorem B1113911 : Blo 742328 1113911 := bstep (se 1 (by rfl) ⟨835433, by rfl⟩ : syracuseStep 1113911 = 1670867) B1670867
theorem B1671119 : Blo 742328 1671119 := bstep (se 1 (by rfl) ⟨1253339, by rfl⟩ : syracuseStep 1671119 = 2506679) B2506679
theorem B7241795 : Blo 742328 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B1114331 : Blo 742328 1114331 := bstep (se 1 (by rfl) ⟨835748, by rfl⟩ : syracuseStep 1114331 = 1671497) B1671497
theorem B1114343 : Blo 742328 1114343 := bstep (se 1 (by rfl) ⟨835757, by rfl⟩ : syracuseStep 1114343 = 1671515) B1671515
theorem B1114505 : Blo 742328 1114505 := bstep (se 2 (by rfl) ⟨417939, by rfl⟩ : syracuseStep 1114505 = 835879) B835879
theorem B1671623 : Blo 742328 1671623 := bstep (se 1 (by rfl) ⟨1253717, by rfl⟩ : syracuseStep 1671623 = 2507435) B2507435
theorem B1507783 : Blo 742328 1507783 := bstep (se 1 (by rfl) ⟨1130837, by rfl⟩ : syracuseStep 1507783 = 2261675) B2261675
theorem B8061403 : Blo 742328 8061403 := bstep (se 1 (by rfl) ⟨6046052, by rfl⟩ : syracuseStep 8061403 = 12092105) B12092105
theorem B1114601 : Blo 742328 1114601 := bstep (se 2 (by rfl) ⟨417975, by rfl⟩ : syracuseStep 1114601 = 835951) B835951
theorem B1114727 : Blo 742328 1114727 := bstep (se 1 (by rfl) ⟨836045, by rfl⟩ : syracuseStep 1114727 = 1672091) B1672091
theorem B1114859 : Blo 742328 1114859 := bstep (se 1 (by rfl) ⟨836144, by rfl⟩ : syracuseStep 1114859 = 1672289) B1672289
theorem B1114889 : Blo 742328 1114889 := bstep (se 2 (by rfl) ⟨418083, by rfl⟩ : syracuseStep 1114889 = 836167) B836167
theorem B2687755 : Blo 742328 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B1671983 : Blo 742328 1671983 := bstep (se 1 (by rfl) ⟨1253987, by rfl⟩ : syracuseStep 1671983 = 2507975) B2507975
theorem B1114991 : Blo 742328 1114991 := bstep (se 1 (by rfl) ⟨836243, by rfl⟩ : syracuseStep 1114991 = 1672487) B1672487
theorem B9536413 : Blo 742328 9536413 := bstep (se 3 (by rfl) ⟨1788077, by rfl⟩ : syracuseStep 9536413 = 3576155) B3576155
theorem B9307237 : Blo 742328 9307237 := bstep (se 4 (by rfl) ⟨872553, by rfl⟩ : syracuseStep 9307237 = 1745107) B1745107
theorem B1115243 : Blo 742328 1115243 := bstep (se 1 (by rfl) ⟨836432, by rfl⟩ : syracuseStep 1115243 = 1672865) B1672865
theorem B1115483 : Blo 742328 1115483 := bstep (se 1 (by rfl) ⟨836612, by rfl⟩ : syracuseStep 1115483 = 1673225) B1673225
theorem B1115759 : Blo 742328 1115759 := bstep (se 1 (by rfl) ⟨836819, by rfl⟩ : syracuseStep 1115759 = 1673639) B1673639
theorem B1115831 : Blo 742328 1115831 := bstep (se 1 (by rfl) ⟨836873, by rfl⟩ : syracuseStep 1115831 = 1673747) B1673747
theorem B1115867 : Blo 742328 1115867 := bstep (se 1 (by rfl) ⟨836900, by rfl⟩ : syracuseStep 1115867 = 1673801) B1673801
theorem B1672991 : Blo 742328 1672991 := bstep (se 1 (by rfl) ⟨1254743, by rfl⟩ : syracuseStep 1672991 = 2509487) B2509487
theorem B1116041 : Blo 742328 1116041 := bstep (se 2 (by rfl) ⟨418515, by rfl⟩ : syracuseStep 1116041 = 837031) B837031
theorem B3573679 : Blo 742328 3573679 := bstep (se 1 (by rfl) ⟨2680259, by rfl⟩ : syracuseStep 3573679 = 5360519) B5360519
theorem B1116143 : Blo 742328 1116143 := bstep (se 1 (by rfl) ⟨837107, by rfl⟩ : syracuseStep 1116143 = 1674215) B1674215
theorem B1673207 : Blo 742328 1673207 := bstep (se 1 (by rfl) ⟨1254905, by rfl⟩ : syracuseStep 1673207 = 2509811) B2509811
theorem B6359249 : Blo 742328 6359249 := bstep (se 2 (by rfl) ⟨2384718, by rfl⟩ : syracuseStep 6359249 = 4769437) B4769437
theorem B952555 : Blo 742328 952555 := bstep (se 1 (by rfl) ⟨714416, by rfl⟩ : syracuseStep 952555 = 1428833) B1428833
theorem B1116395 : Blo 742328 1116395 := bstep (se 1 (by rfl) ⟨837296, by rfl⟩ : syracuseStep 1116395 = 1674593) B1674593
theorem B1116455 : Blo 742328 1116455 := bstep (se 1 (by rfl) ⟨837341, by rfl⟩ : syracuseStep 1116455 = 1674683) B1674683
theorem B7145819 : Blo 742328 7145819 := bstep (se 1 (by rfl) ⟨5359364, by rfl⟩ : syracuseStep 7145819 = 10718729) B10718729
theorem B1673567 : Blo 742328 1673567 := bstep (se 1 (by rfl) ⟨1255175, by rfl⟩ : syracuseStep 1673567 = 2510351) B2510351
theorem B1116539 : Blo 742328 1116539 := bstep (se 1 (by rfl) ⟨837404, by rfl⟩ : syracuseStep 1116539 = 1674809) B1674809
theorem B41388565 : Blo 742328 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B1116809 : Blo 742328 1116809 := bstep (se 2 (by rfl) ⟨418803, by rfl⟩ : syracuseStep 1116809 = 837607) B837607
theorem B4229819 : Blo 742328 4229819 := bstep (se 1 (by rfl) ⟨3172364, by rfl⟩ : syracuseStep 4229819 = 6344729) B6344729
theorem B1608379 : Blo 742328 1608379 := bstep (se 1 (by rfl) ⟨1206284, by rfl⟩ : syracuseStep 1608379 = 2412569) B2412569
theorem B1116983 : Blo 742328 1116983 := bstep (se 1 (by rfl) ⟨837737, by rfl⟩ : syracuseStep 1116983 = 1675475) B1675475
theorem B1117019 : Blo 742328 1117019 := bstep (se 1 (by rfl) ⟨837764, by rfl⟩ : syracuseStep 1117019 = 1675529) B1675529
theorem B1117163 : Blo 742328 1117163 := bstep (se 1 (by rfl) ⟨837872, by rfl⟩ : syracuseStep 1117163 = 1675745) B1675745
theorem B1674287 : Blo 742328 1674287 := bstep (se 1 (by rfl) ⟨1255715, by rfl⟩ : syracuseStep 1674287 = 2511431) B2511431
theorem B1117367 : Blo 742328 1117367 := bstep (se 1 (by rfl) ⟨838025, by rfl⟩ : syracuseStep 1117367 = 1676051) B1676051
theorem B10456253 : Blo 742328 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B9669851 : Blo 742328 9669851 := bstep (se 1 (by rfl) ⟨7252388, by rfl⟩ : syracuseStep 9669851 = 14504777) B14504777
theorem B1674575 : Blo 742328 1674575 := bstep (se 1 (by rfl) ⟨1255931, by rfl⟩ : syracuseStep 1674575 = 2511863) B2511863
theorem B1117607 : Blo 742328 1117607 := bstep (se 1 (by rfl) ⟨838205, by rfl⟩ : syracuseStep 1117607 = 1676411) B1676411
theorem B4230569 : Blo 742328 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B1674665 : Blo 742328 1674665 := bstep (se 2 (by rfl) ⟨627999, by rfl⟩ : syracuseStep 1674665 = 1255999) B1255999
theorem B1117691 : Blo 742328 1117691 := bstep (se 1 (by rfl) ⟨838268, by rfl⟩ : syracuseStep 1117691 = 1676537) B1676537
theorem B1117787 : Blo 742328 1117787 := bstep (se 1 (by rfl) ⟨838340, by rfl⟩ : syracuseStep 1117787 = 1676681) B1676681
theorem B1117871 : Blo 742328 1117871 := bstep (se 1 (by rfl) ⟨838403, by rfl⟩ : syracuseStep 1117871 = 1676807) B1676807
theorem B1117991 : Blo 742328 1117991 := bstep (se 1 (by rfl) ⟨838493, by rfl⟩ : syracuseStep 1117991 = 1676987) B1676987
theorem B1118075 : Blo 742328 1118075 := bstep (se 1 (by rfl) ⟨838556, by rfl⟩ : syracuseStep 1118075 = 1677113) B1677113
theorem B1675151 : Blo 742328 1675151 := bstep (se 1 (by rfl) ⟨1256363, by rfl⟩ : syracuseStep 1675151 = 2512727) B2512727
theorem B1118495 : Blo 742328 1118495 := bstep (se 1 (by rfl) ⟨838871, by rfl⟩ : syracuseStep 1118495 = 1677743) B1677743
theorem B1118519 : Blo 742328 1118519 := bstep (se 1 (by rfl) ⟨838889, by rfl⟩ : syracuseStep 1118519 = 1677779) B1677779
theorem B3182975 : Blo 742328 3182975 := bstep (se 1 (by rfl) ⟨2387231, by rfl⟩ : syracuseStep 3182975 = 4774463) B4774463
theorem B8491391 : Blo 742328 8491391 := bstep (se 1 (by rfl) ⟨6368543, by rfl⟩ : syracuseStep 8491391 = 12737087) B12737087
theorem B1118591 : Blo 742328 1118591 := bstep (se 1 (by rfl) ⟨838943, by rfl⟩ : syracuseStep 1118591 = 1677887) B1677887
theorem B1118663 : Blo 742328 1118663 := bstep (se 1 (by rfl) ⟨838997, by rfl⟩ : syracuseStep 1118663 = 1677995) B1677995
theorem B66130499 : Blo 742328 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B14324303 : Blo 742328 14324303 := bstep (se 1 (by rfl) ⟨10743227, by rfl⟩ : syracuseStep 14324303 = 21486455) B21486455
theorem B1675871 : Blo 742328 1675871 := bstep (se 1 (by rfl) ⟨1256903, by rfl⟩ : syracuseStep 1675871 = 2513807) B2513807
theorem B2265761 : Blo 742328 2265761 := bstep (se 2 (by rfl) ⟨849660, by rfl⟩ : syracuseStep 2265761 = 1699321) B1699321
theorem B1119017 : Blo 742328 1119017 := bstep (se 2 (by rfl) ⟨419631, by rfl⟩ : syracuseStep 1119017 = 839263) B839263
theorem B1119023 : Blo 742328 1119023 := bstep (se 1 (by rfl) ⟨839267, by rfl⟩ : syracuseStep 1119023 = 1678535) B1678535
theorem B1119143 : Blo 742328 1119143 := bstep (se 1 (by rfl) ⟨839357, by rfl⟩ : syracuseStep 1119143 = 1678715) B1678715
theorem B1119227 : Blo 742328 1119227 := bstep (se 1 (by rfl) ⟨839420, by rfl⟩ : syracuseStep 1119227 = 1678841) B1678841
theorem B1414199 : Blo 742328 1414199 := bstep (se 1 (by rfl) ⟨1060649, by rfl⟩ : syracuseStep 1414199 = 2121299) B2121299
theorem B1119287 : Blo 742328 1119287 := bstep (se 1 (by rfl) ⟨839465, by rfl⟩ : syracuseStep 1119287 = 1678931) B1678931
theorem B1119407 : Blo 742328 1119407 := bstep (se 1 (by rfl) ⟨839555, by rfl⟩ : syracuseStep 1119407 = 1679111) B1679111
theorem B1676699 : Blo 742328 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B10852163 : Blo 742328 10852163 := bstep (se 1 (by rfl) ⟨8139122, by rfl⟩ : syracuseStep 10852163 = 16278245) B16278245
theorem B4233167 : Blo 742328 4233167 := bstep (se 1 (by rfl) ⟨3174875, by rfl⟩ : syracuseStep 4233167 = 6349751) B6349751
theorem B1677275 : Blo 742328 1677275 := bstep (se 1 (by rfl) ⟨1257956, by rfl⟩ : syracuseStep 1677275 = 2515913) B2515913
theorem B1677455 : Blo 742328 1677455 := bstep (se 1 (by rfl) ⟨1258091, by rfl⟩ : syracuseStep 1677455 = 2516183) B2516183
theorem B1415323 : Blo 742328 1415323 := bstep (se 1 (by rfl) ⟨1061492, by rfl⟩ : syracuseStep 1415323 = 2122985) B2122985
theorem B1677473 : Blo 742328 1677473 := bstep (se 2 (by rfl) ⟨629052, by rfl⟩ : syracuseStep 1677473 = 1258105) B1258105
theorem B1677545 : Blo 742328 1677545 := bstep (se 2 (by rfl) ⟨629079, by rfl⟩ : syracuseStep 1677545 = 1258159) B1258159
theorem B3774761 : Blo 742328 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B2824571 : Blo 742328 2824571 := bstep (se 1 (by rfl) ⟨2118428, by rfl⟩ : syracuseStep 2824571 = 4236857) B4236857
theorem B8460773 : Blo 742328 8460773 := bstep (se 4 (by rfl) ⟨793197, by rfl⟩ : syracuseStep 8460773 = 1586395) B1586395
theorem B10722131 : Blo 742328 10722131 := bstep (se 1 (by rfl) ⟨8041598, by rfl⟩ : syracuseStep 10722131 = 16083197) B16083197
theorem B1416143 : Blo 742328 1416143 := bstep (se 1 (by rfl) ⟨1062107, by rfl⟩ : syracuseStep 1416143 = 2124215) B2124215
theorem B3578849 : Blo 742328 3578849 := bstep (se 2 (by rfl) ⟨1342068, by rfl⟩ : syracuseStep 3578849 = 2684137) B2684137
theorem B4234625 : Blo 742328 4234625 := bstep (se 2 (by rfl) ⟨1587984, by rfl⟩ : syracuseStep 4234625 = 3175969) B3175969
theorem B1678823 : Blo 742328 1678823 := bstep (se 1 (by rfl) ⟨1259117, by rfl⟩ : syracuseStep 1678823 = 2518235) B2518235
theorem B1252955 : Blo 742328 1252955 := bstep (se 1 (by rfl) ⟨939716, by rfl⟩ : syracuseStep 1252955 = 1879433) B1879433
theorem B9051857 : Blo 742328 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B1253191 : Blo 742328 1253191 := bstep (se 1 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 1253191 = 1879787) B1879787
theorem B4235399 : Blo 742328 4235399 := bstep (se 1 (by rfl) ⟨3176549, by rfl⟩ : syracuseStep 4235399 = 6353099) B6353099
theorem B6791303 : Blo 742328 6791303 := bstep (se 1 (by rfl) ⟨5093477, by rfl⟩ : syracuseStep 6791303 = 10186955) B10186955
theorem B9052489 : Blo 742328 9052489 := bstep (se 2 (by rfl) ⟨3394683, by rfl⟩ : syracuseStep 9052489 = 6789367) B6789367
theorem B10887605 : Blo 742328 10887605 := bstep (se 5 (by rfl) ⟨510356, by rfl⟩ : syracuseStep 10887605 = 1020713) B1020713
theorem B2826683 : Blo 742328 2826683 := bstep (se 1 (by rfl) ⟨2120012, by rfl⟩ : syracuseStep 2826683 = 4240025) B4240025
theorem B1253839 : Blo 742328 1253839 := bstep (se 1 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 1253839 = 1880759) B1880759
theorem B11477753 : Blo 742328 11477753 := bstep (se 2 (by rfl) ⟨4304157, by rfl⟩ : syracuseStep 11477753 = 8608315) B8608315
theorem B4530941 : Blo 742328 4530941 := bstep (se 3 (by rfl) ⟨849551, by rfl⟩ : syracuseStep 4530941 = 1699103) B1699103
theorem B42869573 : Blo 742328 42869573 := bstep (se 4 (by rfl) ⟨4019022, by rfl⟩ : syracuseStep 42869573 = 8038045) B8038045
theorem B1254575 : Blo 742328 1254575 := bstep (se 1 (by rfl) ⟨940931, by rfl⟩ : syracuseStep 1254575 = 1881863) B1881863
theorem B4236583 : Blo 742328 4236583 := bstep (se 1 (by rfl) ⟨3177437, by rfl⟩ : syracuseStep 4236583 = 6354875) B6354875
theorem B1254811 : Blo 742328 1254811 := bstep (se 1 (by rfl) ⟨941108, by rfl⟩ : syracuseStep 1254811 = 1882217) B1882217
theorem B13575599 : Blo 742328 13575599 := bstep (se 1 (by rfl) ⟨10181699, by rfl⟩ : syracuseStep 13575599 = 20363399) B20363399
theorem B2827943 : Blo 742328 2827943 := bstep (se 1 (by rfl) ⟨2120957, by rfl⟩ : syracuseStep 2827943 = 4241915) B4241915
theorem B9545435 : Blo 742328 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B1255135 : Blo 742328 1255135 := bstep (se 1 (by rfl) ⟨941351, by rfl⟩ : syracuseStep 1255135 = 1882703) B1882703
theorem B1255567 : Blo 742328 1255567 := bstep (se 1 (by rfl) ⟨941675, by rfl⟩ : syracuseStep 1255567 = 1883351) B1883351
theorem B4303811 : Blo 742328 4303811 := bstep (se 1 (by rfl) ⟨3227858, by rfl⟩ : syracuseStep 4303811 = 6455717) B6455717
theorem B4238315 : Blo 742328 4238315 := bstep (se 1 (by rfl) ⟨3178736, by rfl⟩ : syracuseStep 4238315 = 6357473) B6357473
theorem B1256519 : Blo 742328 1256519 := bstep (se 1 (by rfl) ⟨942389, by rfl⟩ : syracuseStep 1256519 = 1884779) B1884779
theorem B1059961 : Blo 742328 1059961 := bstep (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) B794971
theorem B1879321 : Blo 742328 1879321 := bstep (se 2 (by rfl) ⟨704745, by rfl⟩ : syracuseStep 1879321 = 1409491) B1409491
theorem B1256951 : Blo 742328 1256951 := bstep (se 1 (by rfl) ⟨942713, by rfl⟩ : syracuseStep 1256951 = 1885427) B1885427
theorem B1879625 : Blo 742328 1879625 := bstep (se 2 (by rfl) ⟨704859, by rfl⟩ : syracuseStep 1879625 = 1409719) B1409719
theorem B2830099 : Blo 742328 2830099 := bstep (se 1 (by rfl) ⟨2122574, by rfl⟩ : syracuseStep 2830099 = 4245149) B4245149
theorem B1191719 : Blo 742328 1191719 := bstep (se 1 (by rfl) ⟨893789, by rfl⟩ : syracuseStep 1191719 = 1787579) B1787579
theorem B1257977 : Blo 742328 1257977 := bstep (se 2 (by rfl) ⟨471741, by rfl⟩ : syracuseStep 1257977 = 943483) B943483
theorem B5092055 : Blo 742328 5092055 := bstep (se 1 (by rfl) ⟨3819041, by rfl⟩ : syracuseStep 5092055 = 7638083) B7638083
theorem B1258247 : Blo 742328 1258247 := bstep (se 1 (by rfl) ⟨943685, by rfl⟩ : syracuseStep 1258247 = 1887371) B1887371
theorem B1061743 : Blo 742328 1061743 := bstep (se 1 (by rfl) ⟨796307, by rfl⟩ : syracuseStep 1061743 = 1592615) B1592615
theorem B8500139 : Blo 742328 8500139 := bstep (se 1 (by rfl) ⟨6375104, by rfl⟩ : syracuseStep 8500139 = 12750209) B12750209
theorem B1881083 : Blo 742328 1881083 := bstep (se 1 (by rfl) ⟨1410812, by rfl⟩ : syracuseStep 1881083 = 2821625) B2821625
theorem B4240457 : Blo 742328 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B1881569 : Blo 742328 1881569 := bstep (se 2 (by rfl) ⟨705588, by rfl⟩ : syracuseStep 1881569 = 1411177) B1411177
theorem B1259327 : Blo 742328 1259327 := bstep (se 1 (by rfl) ⟨944495, by rfl⟩ : syracuseStep 1259327 = 1888991) B1888991
theorem B1259401 : Blo 742328 1259401 := bstep (se 2 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 1259401 = 944551) B944551
theorem B1882075 : Blo 742328 1882075 := bstep (se 1 (by rfl) ⟨1411556, by rfl⟩ : syracuseStep 1882075 = 2823113) B2823113
theorem B2832347 : Blo 742328 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B6371621 : Blo 742328 6371621 := bstep (se 4 (by rfl) ⟨597339, by rfl⟩ : syracuseStep 6371621 = 1194679) B1194679
theorem B7649579 : Blo 742328 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B2505977 : Blo 742328 2505977 := bstep (se 2 (by rfl) ⟨939741, by rfl⟩ : syracuseStep 2505977 = 1879483) B1879483
theorem B2506247 : Blo 742328 2506247 := bstep (se 1 (by rfl) ⟨1879685, by rfl⟩ : syracuseStep 2506247 = 3759371) B3759371
theorem B8601335 : Blo 742328 8601335 := bstep (se 1 (by rfl) ⟨6451001, by rfl⟩ : syracuseStep 8601335 = 12902003) B12902003
theorem B1720235 : Blo 742328 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B9519191 : Blo 742328 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B2507327 : Blo 742328 2507327 := bstep (se 1 (by rfl) ⟨1880495, by rfl⟩ : syracuseStep 2507327 = 3760991) B3760991
theorem B836671 : Blo 742328 836671 := bstep (se 1 (by rfl) ⟨627503, by rfl⟩ : syracuseStep 836671 = 1255007) B1255007
theorem B836815 : Blo 742328 836815 := bstep (se 1 (by rfl) ⟨627611, by rfl⟩ : syracuseStep 836815 = 1255223) B1255223
theorem B4769027 : Blo 742328 4769027 := bstep (se 1 (by rfl) ⟨3576770, by rfl⟩ : syracuseStep 4769027 = 7153541) B7153541
theorem B4244831 : Blo 742328 4244831 := bstep (se 1 (by rfl) ⟨3183623, by rfl⟩ : syracuseStep 4244831 = 6367247) B6367247
theorem B2016683 : Blo 742328 2016683 := bstep (se 1 (by rfl) ⟨1512512, by rfl⟩ : syracuseStep 2016683 = 3025025) B3025025
theorem B2508623 : Blo 742328 2508623 := bstep (se 1 (by rfl) ⟨1881467, by rfl⟩ : syracuseStep 2508623 = 3762935) B3762935
theorem B2508947 : Blo 742328 2508947 := bstep (se 1 (by rfl) ⟨1881710, by rfl⟩ : syracuseStep 2508947 = 3763421) B3763421
theorem B837787 : Blo 742328 837787 := bstep (se 1 (by rfl) ⟨628340, by rfl⟩ : syracuseStep 837787 = 1256681) B1256681
theorem B837823 : Blo 742328 837823 := bstep (se 1 (by rfl) ⟨628367, by rfl⟩ : syracuseStep 837823 = 1256735) B1256735
theorem B1886399 : Blo 742328 1886399 := bstep (se 1 (by rfl) ⟨1414799, by rfl⟩ : syracuseStep 1886399 = 2829599) B2829599
theorem B2509217 : Blo 742328 2509217 := bstep (se 2 (by rfl) ⟨940956, by rfl⟩ : syracuseStep 2509217 = 1881913) B1881913
theorem B9521651 : Blo 742328 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B5360201 : Blo 742328 5360201 := bstep (se 2 (by rfl) ⟨2010075, by rfl⟩ : syracuseStep 5360201 = 4020151) B4020151
theorem B6343667 : Blo 742328 6343667 := bstep (se 1 (by rfl) ⟨4757750, by rfl⟩ : syracuseStep 6343667 = 9515501) B9515501
theorem B5655581 : Blo 742328 5655581 := bstep (se 3 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 5655581 = 2120843) B2120843
theorem B26070673 : Blo 742328 26070673 := bstep (se 2 (by rfl) ⟨9776502, by rfl⟩ : syracuseStep 26070673 = 19553005) B19553005
theorem B1888019 : Blo 742328 1888019 := bstep (se 1 (by rfl) ⟨1416014, by rfl⟩ : syracuseStep 1888019 = 2832029) B2832029
theorem B115953443 : Blo 742328 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B2511215 : Blo 742328 2511215 := bstep (se 1 (by rfl) ⟨1883411, by rfl⟩ : syracuseStep 2511215 = 3766823) B3766823
theorem B4248065 : Blo 742328 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B6345377 : Blo 742328 6345377 := bstep (se 2 (by rfl) ⟨2379516, by rfl⟩ : syracuseStep 6345377 = 4759033) B4759033
theorem B4772513 : Blo 742328 4772513 := bstep (se 2 (by rfl) ⟨1789692, by rfl⟩ : syracuseStep 4772513 = 3579385) B3579385
theorem B4248247 : Blo 742328 4248247 := bstep (se 1 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 4248247 = 6372371) B6372371
theorem B1790761 : Blo 742328 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B2904893 : Blo 742328 2904893 := bstep (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) B1089335
theorem B742395 : Blo 742328 742395 := bstep (se 1 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 742395 = 1113593) B1113593
theorem B742463 : Blo 742328 742463 := bstep (se 1 (by rfl) ⟨556847, by rfl⟩ : syracuseStep 742463 = 1113695) B1113695
theorem B742607 : Blo 742328 742607 := bstep (se 1 (by rfl) ⟨556955, by rfl⟩ : syracuseStep 742607 = 1113911) B1113911
theorem B742811 : Blo 742328 742811 := bstep (se 1 (by rfl) ⟨557108, by rfl⟩ : syracuseStep 742811 = 1114217) B1114217
theorem B2119067 : Blo 742328 2119067 := bstep (se 1 (by rfl) ⟨1589300, by rfl⟩ : syracuseStep 2119067 = 3178601) B3178601
theorem B743023 : Blo 742328 743023 := bstep (se 1 (by rfl) ⟨557267, by rfl⟩ : syracuseStep 743023 = 1114535) B1114535
theorem B9164411 : Blo 742328 9164411 := bstep (se 1 (by rfl) ⟨6873308, by rfl⟩ : syracuseStep 9164411 = 13746617) B13746617
theorem B743079 : Blo 742328 743079 := bstep (se 1 (by rfl) ⟨557309, by rfl⟩ : syracuseStep 743079 = 1114619) B1114619
theorem B2512619 : Blo 742328 2512619 := bstep (se 1 (by rfl) ⟨1884464, by rfl⟩ : syracuseStep 2512619 = 3768929) B3768929
theorem B743163 : Blo 742328 743163 := bstep (se 1 (by rfl) ⟨557372, by rfl⟩ : syracuseStep 743163 = 1114745) B1114745
theorem B743199 : Blo 742328 743199 := bstep (se 1 (by rfl) ⟨557399, by rfl⟩ : syracuseStep 743199 = 1114799) B1114799
theorem B743231 : Blo 742328 743231 := bstep (se 1 (by rfl) ⟨557423, by rfl⟩ : syracuseStep 743231 = 1114847) B1114847
theorem B940015 : Blo 742328 940015 := bstep (se 1 (by rfl) ⟨705011, by rfl⟩ : syracuseStep 940015 = 1410023) B1410023
theorem B743407 : Blo 742328 743407 := bstep (se 1 (by rfl) ⟨557555, by rfl⟩ : syracuseStep 743407 = 1115111) B1115111
theorem B2512889 : Blo 742328 2512889 := bstep (se 2 (by rfl) ⟨942333, by rfl⟩ : syracuseStep 2512889 = 1884667) B1884667
theorem B2381849 : Blo 742328 2381849 := bstep (se 2 (by rfl) ⟨893193, by rfl⟩ : syracuseStep 2381849 = 1786387) B1786387
theorem B43604099 : Blo 742328 43604099 := bstep (se 1 (by rfl) ⟨32703074, by rfl⟩ : syracuseStep 43604099 = 65406149) B65406149
theorem B940187 : Blo 742328 940187 := bstep (se 1 (by rfl) ⟨705140, by rfl⟩ : syracuseStep 940187 = 1410281) B1410281
theorem B743579 : Blo 742328 743579 := bstep (se 1 (by rfl) ⟨557684, by rfl⟩ : syracuseStep 743579 = 1115369) B1115369
theorem B2513051 : Blo 742328 2513051 := bstep (se 1 (by rfl) ⟨1884788, by rfl⟩ : syracuseStep 2513051 = 3769577) B3769577
theorem B2119841 : Blo 742328 2119841 := bstep (se 2 (by rfl) ⟨794940, by rfl⟩ : syracuseStep 2119841 = 1589881) B1589881
theorem B743615 : Blo 742328 743615 := bstep (se 1 (by rfl) ⟨557711, by rfl⟩ : syracuseStep 743615 = 1115423) B1115423
theorem B2513159 : Blo 742328 2513159 := bstep (se 1 (by rfl) ⟨1884869, by rfl⟩ : syracuseStep 2513159 = 3769739) B3769739
theorem B4774153 : Blo 742328 4774153 := bstep (se 2 (by rfl) ⟨1790307, by rfl⟩ : syracuseStep 4774153 = 3580615) B3580615
theorem B6773021 : Blo 742328 6773021 := bstep (se 3 (by rfl) ⟨1269941, by rfl⟩ : syracuseStep 6773021 = 2539883) B2539883
theorem B743727 : Blo 742328 743727 := bstep (se 1 (by rfl) ⟨557795, by rfl⟩ : syracuseStep 743727 = 1115591) B1115591
theorem B4249979 : Blo 742328 4249979 := bstep (se 1 (by rfl) ⟨3187484, by rfl⟩ : syracuseStep 4249979 = 6374969) B6374969
theorem B743963 : Blo 742328 743963 := bstep (se 1 (by rfl) ⟨557972, by rfl⟩ : syracuseStep 743963 = 1115945) B1115945
theorem B743967 : Blo 742328 743967 := bstep (se 1 (by rfl) ⟨557975, by rfl⟩ : syracuseStep 743967 = 1115951) B1115951
theorem B940891 : Blo 742328 940891 := bstep (se 1 (by rfl) ⟨705668, by rfl⟩ : syracuseStep 940891 = 1411337) B1411337
theorem B744283 : Blo 742328 744283 := bstep (se 1 (by rfl) ⟨558212, by rfl⟩ : syracuseStep 744283 = 1116425) B1116425
theorem B744351 : Blo 742328 744351 := bstep (se 1 (by rfl) ⟨558263, by rfl⟩ : syracuseStep 744351 = 1116527) B1116527
theorem B744495 : Blo 742328 744495 := bstep (se 1 (by rfl) ⟨558371, by rfl⟩ : syracuseStep 744495 = 1116743) B1116743
theorem B7167041 : Blo 742328 7167041 := bstep (se 2 (by rfl) ⟨2687640, by rfl⟩ : syracuseStep 7167041 = 5375281) B5375281
theorem B17161283 : Blo 742328 17161283 := bstep (se 1 (by rfl) ⟨12870962, by rfl⟩ : syracuseStep 17161283 = 25741925) B25741925
theorem B744519 : Blo 742328 744519 := bstep (se 1 (by rfl) ⟨558389, by rfl⟩ : syracuseStep 744519 = 1116779) B1116779
theorem B1793153 : Blo 742328 1793153 := bstep (se 2 (by rfl) ⟨672432, by rfl⟩ : syracuseStep 1793153 = 1344865) B1344865
theorem B744671 : Blo 742328 744671 := bstep (se 1 (by rfl) ⟨558503, by rfl⟩ : syracuseStep 744671 = 1117007) B1117007
theorem B2514185 : Blo 742328 2514185 := bstep (se 2 (by rfl) ⟨942819, by rfl⟩ : syracuseStep 2514185 = 1885639) B1885639
theorem B744935 : Blo 742328 744935 := bstep (se 1 (by rfl) ⟨558701, by rfl⟩ : syracuseStep 744935 = 1117403) B1117403
theorem B3759695 : Blo 742328 3759695 := bstep (se 1 (by rfl) ⟨2819771, by rfl⟩ : syracuseStep 3759695 = 5639543) B5639543
theorem B745051 : Blo 742328 745051 := bstep (se 1 (by rfl) ⟨558788, by rfl⟩ : syracuseStep 745051 = 1117577) B1117577
theorem B941863 : Blo 742328 941863 := bstep (se 1 (by rfl) ⟨706397, by rfl⟩ : syracuseStep 941863 = 1412795) B1412795
theorem B2121527 : Blo 742328 2121527 := bstep (se 1 (by rfl) ⟨1591145, by rfl⟩ : syracuseStep 2121527 = 3182291) B3182291
theorem B745287 : Blo 742328 745287 := bstep (se 1 (by rfl) ⟨558965, by rfl⟩ : syracuseStep 745287 = 1117931) B1117931
theorem B745439 : Blo 742328 745439 := bstep (se 1 (by rfl) ⟨559079, by rfl⟩ : syracuseStep 745439 = 1118159) B1118159
theorem B745703 : Blo 742328 745703 := bstep (se 1 (by rfl) ⟨559277, by rfl⟩ : syracuseStep 745703 = 1118555) B1118555
theorem B2515319 : Blo 742328 2515319 := bstep (se 1 (by rfl) ⟨1886489, by rfl⟩ : syracuseStep 2515319 = 3772979) B3772979
theorem B745855 : Blo 742328 745855 := bstep (se 1 (by rfl) ⟨559391, by rfl⟩ : syracuseStep 745855 = 1118783) B1118783
theorem B745935 : Blo 742328 745935 := bstep (se 1 (by rfl) ⟨559451, by rfl⟩ : syracuseStep 745935 = 1118903) B1118903
theorem B746087 : Blo 742328 746087 := bstep (se 1 (by rfl) ⟨559565, by rfl⟩ : syracuseStep 746087 = 1119131) B1119131
theorem B943159 : Blo 742328 943159 := bstep (se 1 (by rfl) ⟨707369, by rfl⟩ : syracuseStep 943159 = 1414739) B1414739
theorem B9037163 : Blo 742328 9037163 := bstep (se 1 (by rfl) ⟨6777872, by rfl⟩ : syracuseStep 9037163 = 13555745) B13555745
theorem B2516399 : Blo 742328 2516399 := bstep (se 1 (by rfl) ⟨1887299, by rfl⟩ : syracuseStep 2516399 = 3774599) B3774599
theorem B4777487 : Blo 742328 4777487 := bstep (se 1 (by rfl) ⟨3583115, by rfl⟩ : syracuseStep 4777487 = 7166231) B7166231
theorem B943903 : Blo 742328 943903 := bstep (se 1 (by rfl) ⟨707927, by rfl⟩ : syracuseStep 943903 = 1415855) B1415855
theorem B2516777 : Blo 742328 2516777 := bstep (se 2 (by rfl) ⟨943791, by rfl⟩ : syracuseStep 2516777 = 1887583) B1887583
theorem B5105683 : Blo 742328 5105683 := bstep (se 1 (by rfl) ⟨3829262, by rfl⟩ : syracuseStep 5105683 = 7658525) B7658525
theorem B8481185 : Blo 742328 8481185 := bstep (se 2 (by rfl) ⟨3180444, by rfl⟩ : syracuseStep 8481185 = 6360889) B6360889
theorem B1337887 : Blo 742328 1337887 := bstep (se 1 (by rfl) ⟨1003415, by rfl⟩ : syracuseStep 1337887 = 2006831) B2006831
theorem B1698409 : Blo 742328 1698409 := bstep (se 2 (by rfl) ⟨636903, by rfl⟩ : syracuseStep 1698409 = 1273807) B1273807
theorem B7170763 : Blo 742328 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B8580097 : Blo 742328 8580097 := bstep (se 2 (by rfl) ⟨3217536, by rfl⟩ : syracuseStep 8580097 = 6435073) B6435073
theorem B2387065 : Blo 742328 2387065 := bstep (se 2 (by rfl) ⟨895149, by rfl⟩ : syracuseStep 2387065 = 1790299) B1790299
theorem B19066265 : Blo 742328 19066265 := bstep (se 2 (by rfl) ⟨7149849, by rfl⟩ : syracuseStep 19066265 = 14299699) B14299699
theorem B3763745 : Blo 742328 3763745 := bstep (se 2 (by rfl) ⟨1411404, by rfl⟩ : syracuseStep 3763745 = 2822809) B2822809
theorem B8580971 : Blo 742328 8580971 := bstep (se 1 (by rfl) ⟨6435728, by rfl⟩ : syracuseStep 8580971 = 12871457) B12871457
theorem B5369975 : Blo 742328 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B7631507 : Blo 742328 7631507 := bstep (se 1 (by rfl) ⟨5723630, by rfl⟩ : syracuseStep 7631507 = 11447261) B11447261
theorem B4780691 : Blo 742328 4780691 := bstep (se 1 (by rfl) ⟨3585518, by rfl⟩ : syracuseStep 4780691 = 7171037) B7171037
theorem B2552705 : Blo 742328 2552705 := bstep (se 2 (by rfl) ⟨957264, by rfl⟩ : syracuseStep 2552705 = 1914529) B1914529
theorem B1700927 : Blo 742328 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B16053947 : Blo 742328 16053947 := bstep (se 1 (by rfl) ⟨12040460, by rfl⟩ : syracuseStep 16053947 = 24080921) B24080921
theorem B2389999 : Blo 742328 2389999 := bstep (se 1 (by rfl) ⟨1792499, by rfl⟩ : syracuseStep 2389999 = 3584999) B3584999
theorem B2259049 : Blo 742328 2259049 := bstep (se 2 (by rfl) ⟨847143, by rfl⟩ : syracuseStep 2259049 = 1694287) B1694287
theorem B8026283 : Blo 742328 8026283 := bstep (se 1 (by rfl) ⟨6019712, by rfl⟩ : syracuseStep 8026283 = 12039425) B12039425
theorem B7141547 : Blo 742328 7141547 := bstep (se 1 (by rfl) ⟨5356160, by rfl⟩ : syracuseStep 7141547 = 10712321) B10712321
theorem B3275117 : Blo 742328 3275117 := bstep (se 3 (by rfl) ⟨614084, by rfl⟩ : syracuseStep 3275117 = 1228169) B1228169
theorem B2685577 : Blo 742328 2685577 := bstep (se 2 (by rfl) ⟨1007091, by rfl⟩ : syracuseStep 2685577 = 2014183) B2014183
theorem B5372999 : Blo 742328 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B1670327 : Blo 742328 1670327 := bstep (se 1 (by rfl) ⟨1252745, by rfl⟩ : syracuseStep 1670327 = 2505491) B2505491
theorem B1113575 : Blo 742328 1113575 := bstep (se 1 (by rfl) ⟨835181, by rfl⟩ : syracuseStep 1113575 = 1670363) B1670363
theorem B1113707 : Blo 742328 1113707 := bstep (se 1 (by rfl) ⟨835280, by rfl⟩ : syracuseStep 1113707 = 1670561) B1670561
theorem B5373665 : Blo 742328 5373665 := bstep (se 2 (by rfl) ⟨2015124, by rfl⟩ : syracuseStep 5373665 = 4030249) B4030249
theorem B1113833 : Blo 742328 1113833 := bstep (se 2 (by rfl) ⟨417687, by rfl⟩ : syracuseStep 1113833 = 835375) B835375
theorem B1670903 : Blo 742328 1670903 := bstep (se 1 (by rfl) ⟨1253177, by rfl⟩ : syracuseStep 1670903 = 2506355) B2506355
theorem B1113977 : Blo 742328 1113977 := bstep (se 2 (by rfl) ⟨417741, by rfl⟩ : syracuseStep 1113977 = 835483) B835483
theorem B1671083 : Blo 742328 1671083 := bstep (se 1 (by rfl) ⟨1253312, by rfl⟩ : syracuseStep 1671083 = 2506625) B2506625
theorem B1114079 : Blo 742328 1114079 := bstep (se 1 (by rfl) ⟨835559, by rfl⟩ : syracuseStep 1114079 = 1671119) B1671119
theorem B1114415 : Blo 742328 1114415 := bstep (se 1 (by rfl) ⟨835811, by rfl⟩ : syracuseStep 1114415 = 1671623) B1671623
theorem B1671551 : Blo 742328 1671551 := bstep (se 1 (by rfl) ⟨1253663, by rfl⟩ : syracuseStep 1671551 = 2507327) B2507327
theorem B1114655 : Blo 742328 1114655 := bstep (se 1 (by rfl) ⟨835991, by rfl⟩ : syracuseStep 1114655 = 1671983) B1671983
theorem B1671785 : Blo 742328 1671785 := bstep (se 2 (by rfl) ⟨626919, by rfl⟩ : syracuseStep 1671785 = 1253839) B1253839
theorem B10748537 : Blo 742328 10748537 := bstep (se 2 (by rfl) ⟨4030701, by rfl⟩ : syracuseStep 10748537 = 8061403) B8061403
theorem B3179351 : Blo 742328 3179351 := bstep (se 1 (by rfl) ⟨2384513, by rfl⟩ : syracuseStep 3179351 = 4769027) B4769027
theorem B1344455 : Blo 742328 1344455 := bstep (se 1 (by rfl) ⟨1008341, by rfl⟩ : syracuseStep 1344455 = 2016683) B2016683
theorem B1115327 : Blo 742328 1115327 := bstep (se 1 (by rfl) ⟨836495, by rfl⟩ : syracuseStep 1115327 = 1672991) B1672991
theorem B12715217 : Blo 742328 12715217 := bstep (se 2 (by rfl) ⟨4768206, by rfl⟩ : syracuseStep 12715217 = 9536413) B9536413
theorem B1672415 : Blo 742328 1672415 := bstep (se 1 (by rfl) ⟨1254311, by rfl⟩ : syracuseStep 1672415 = 2508623) B2508623
theorem B1115471 : Blo 742328 1115471 := bstep (se 1 (by rfl) ⟨836603, by rfl⟩ : syracuseStep 1115471 = 1673207) B1673207
theorem B1115561 : Blo 742328 1115561 := bstep (se 2 (by rfl) ⟨418335, by rfl⟩ : syracuseStep 1115561 = 836671) B836671
theorem B1672631 : Blo 742328 1672631 := bstep (se 1 (by rfl) ⟨1254473, by rfl⟩ : syracuseStep 1672631 = 2508947) B2508947
theorem B1115711 : Blo 742328 1115711 := bstep (se 1 (by rfl) ⟨836783, by rfl⟩ : syracuseStep 1115711 = 1673567) B1673567
theorem B1115753 : Blo 742328 1115753 := bstep (se 2 (by rfl) ⟨418407, by rfl⟩ : syracuseStep 1115753 = 836815) B836815
theorem B1672811 : Blo 742328 1672811 := bstep (se 1 (by rfl) ⟨1254608, by rfl⟩ : syracuseStep 1672811 = 2509217) B2509217
theorem B3573467 : Blo 742328 3573467 := bstep (se 1 (by rfl) ⟨2680100, by rfl⟩ : syracuseStep 3573467 = 5360201) B5360201
theorem B20350685 : Blo 742328 20350685 := bstep (se 3 (by rfl) ⟨3815753, by rfl⟩ : syracuseStep 20350685 = 7631507) B7631507
theorem B2819879 : Blo 742328 2819879 := bstep (se 1 (by rfl) ⟨2114909, by rfl⟩ : syracuseStep 2819879 = 4229819) B4229819
theorem B1673081 : Blo 742328 1673081 := bstep (se 2 (by rfl) ⟨627405, by rfl⟩ : syracuseStep 1673081 = 1254811) B1254811
theorem B4229111 : Blo 742328 4229111 := bstep (se 1 (by rfl) ⟨3171833, by rfl⟩ : syracuseStep 4229111 = 6343667) B6343667
theorem B3770387 : Blo 742328 3770387 := bstep (se 1 (by rfl) ⟨2827790, by rfl⟩ : syracuseStep 3770387 = 5655581) B5655581
theorem B1116191 : Blo 742328 1116191 := bstep (se 1 (by rfl) ⟨837143, by rfl⟩ : syracuseStep 1116191 = 1674287) B1674287
theorem B1116383 : Blo 742328 1116383 := bstep (se 1 (by rfl) ⟨837287, by rfl⟩ : syracuseStep 1116383 = 1674575) B1674575
theorem B2820379 : Blo 742328 2820379 := bstep (se 1 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 2820379 = 4230569) B4230569
theorem B1116443 : Blo 742328 1116443 := bstep (se 1 (by rfl) ⟨837332, by rfl⟩ : syracuseStep 1116443 = 1674665) B1674665
theorem B1673513 : Blo 742328 1673513 := bstep (se 2 (by rfl) ⟨627567, by rfl⟩ : syracuseStep 1673513 = 1255135) B1255135
theorem B77302295 : Blo 742328 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B1116767 : Blo 742328 1116767 := bstep (se 1 (by rfl) ⟨837575, by rfl⟩ : syracuseStep 1116767 = 1675151) B1675151
theorem B3771197 : Blo 742328 3771197 := bstep (se 3 (by rfl) ⟨707099, by rfl⟩ : syracuseStep 3771197 = 1414199) B1414199
theorem B1674089 : Blo 742328 1674089 := bstep (se 2 (by rfl) ⟨627783, by rfl⟩ : syracuseStep 1674089 = 1255567) B1255567
theorem B1117049 : Blo 742328 1117049 := bstep (se 2 (by rfl) ⟨418893, by rfl⟩ : syracuseStep 1117049 = 837787) B837787
theorem B1674143 : Blo 742328 1674143 := bstep (se 1 (by rfl) ⟨1255607, by rfl⟩ : syracuseStep 1674143 = 2511215) B2511215
theorem B1117097 : Blo 742328 1117097 := bstep (se 2 (by rfl) ⟨418911, by rfl⟩ : syracuseStep 1117097 = 837823) B837823
theorem B1117247 : Blo 742328 1117247 := bstep (se 1 (by rfl) ⟨837935, by rfl⟩ : syracuseStep 1117247 = 1675871) B1675871
theorem B4230251 : Blo 742328 4230251 := bstep (se 1 (by rfl) ⟨3172688, by rfl⟩ : syracuseStep 4230251 = 6345377) B6345377
theorem B3181675 : Blo 742328 3181675 := bstep (se 1 (by rfl) ⟨2386256, by rfl⟩ : syracuseStep 3181675 = 4772513) B4772513
theorem B1510507 : Blo 742328 1510507 := bstep (se 1 (by rfl) ⟨1132880, by rfl⟩ : syracuseStep 1510507 = 2265761) B2265761
theorem B1936595 : Blo 742328 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B55184753 : Blo 742328 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B2264545 : Blo 742328 2264545 := bstep (se 2 (by rfl) ⟨849204, by rfl⟩ : syracuseStep 2264545 = 1698409) B1698409
theorem B1412711 : Blo 742328 1412711 := bstep (se 1 (by rfl) ⟨1059533, by rfl⟩ : syracuseStep 1412711 = 2119067) B2119067
theorem B1117799 : Blo 742328 1117799 := bstep (se 1 (by rfl) ⟨838349, by rfl⟩ : syracuseStep 1117799 = 1676699) B1676699
theorem B1675079 : Blo 742328 1675079 := bstep (se 1 (by rfl) ⟨1256309, by rfl⟩ : syracuseStep 1675079 = 2512619) B2512619
theorem B34312085 : Blo 742328 34312085 := bstep (se 6 (by rfl) ⟨804189, by rfl⟩ : syracuseStep 34312085 = 1608379) B1608379
theorem B2822111 : Blo 742328 2822111 := bstep (se 1 (by rfl) ⟨2116583, by rfl⟩ : syracuseStep 2822111 = 4233167) B4233167
theorem B1118183 : Blo 742328 1118183 := bstep (se 1 (by rfl) ⟨838637, by rfl⟩ : syracuseStep 1118183 = 1677275) B1677275
theorem B1675259 : Blo 742328 1675259 := bstep (se 1 (by rfl) ⟨1256444, by rfl⟩ : syracuseStep 1675259 = 2512889) B2512889
theorem B11440129 : Blo 742328 11440129 := bstep (se 2 (by rfl) ⟨4290048, by rfl⟩ : syracuseStep 11440129 = 8580097) B8580097
theorem B29069399 : Blo 742328 29069399 := bstep (se 1 (by rfl) ⟨21802049, by rfl⟩ : syracuseStep 29069399 = 43604099) B43604099
theorem B1118303 : Blo 742328 1118303 := bstep (se 1 (by rfl) ⟨838727, by rfl⟩ : syracuseStep 1118303 = 1677455) B1677455
theorem B1675367 : Blo 742328 1675367 := bstep (se 1 (by rfl) ⟨1256525, by rfl⟩ : syracuseStep 1675367 = 2513051) B2513051
theorem B1413227 : Blo 742328 1413227 := bstep (se 1 (by rfl) ⟨1059920, by rfl⟩ : syracuseStep 1413227 = 2119841) B2119841
theorem B1118315 : Blo 742328 1118315 := bstep (se 1 (by rfl) ⟨838736, by rfl⟩ : syracuseStep 1118315 = 1677473) B1677473
theorem B1118363 : Blo 742328 1118363 := bstep (se 1 (by rfl) ⟨838772, by rfl⟩ : syracuseStep 1118363 = 1677545) B1677545
theorem B1413281 : Blo 742328 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B3182753 : Blo 742328 3182753 := bstep (se 2 (by rfl) ⟨1193532, by rfl⟩ : syracuseStep 3182753 = 2387065) B2387065
theorem B1675439 : Blo 742328 1675439 := bstep (se 1 (by rfl) ⟨1256579, by rfl⟩ : syracuseStep 1675439 = 2513159) B2513159
theorem B5640515 : Blo 742328 5640515 := bstep (se 1 (by rfl) ⟨4230386, by rfl⟩ : syracuseStep 5640515 = 8460773) B8460773
theorem B7148087 : Blo 742328 7148087 := bstep (se 1 (by rfl) ⟨5361065, by rfl⟩ : syracuseStep 7148087 = 10722131) B10722131
theorem B11440855 : Blo 742328 11440855 := bstep (se 1 (by rfl) ⟨8580641, by rfl⟩ : syracuseStep 11440855 = 17161283) B17161283
theorem B1676123 : Blo 742328 1676123 := bstep (se 1 (by rfl) ⟨1257092, by rfl⟩ : syracuseStep 1676123 = 2514185) B2514185
theorem B2823083 : Blo 742328 2823083 := bstep (se 1 (by rfl) ⟨2117312, by rfl⟩ : syracuseStep 2823083 = 4234625) B4234625
theorem B1119215 : Blo 742328 1119215 := bstep (se 1 (by rfl) ⟨839411, by rfl⟩ : syracuseStep 1119215 = 1678823) B1678823
theorem B3773465 : Blo 742328 3773465 := bstep (se 2 (by rfl) ⟨1415049, by rfl⟩ : syracuseStep 3773465 = 2830099) B2830099
theorem B6034571 : Blo 742328 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B1414351 : Blo 742328 1414351 := bstep (se 1 (by rfl) ⟨1060763, by rfl⟩ : syracuseStep 1414351 = 2121527) B2121527
theorem B2823599 : Blo 742328 2823599 := bstep (se 1 (by rfl) ⟨2117699, by rfl⟩ : syracuseStep 2823599 = 4235399) B4235399
theorem B4527535 : Blo 742328 4527535 := bstep (se 1 (by rfl) ⟨3395651, by rfl⟩ : syracuseStep 4527535 = 6791303) B6791303
theorem B1676879 : Blo 742328 1676879 := bstep (se 1 (by rfl) ⟨1257659, by rfl⟩ : syracuseStep 1676879 = 2515319) B2515319
theorem B3020627 : Blo 742328 3020627 := bstep (se 1 (by rfl) ⟨2265470, by rfl⟩ : syracuseStep 3020627 = 4530941) B4530941
theorem B28579715 : Blo 742328 28579715 := bstep (se 1 (by rfl) ⟨21434786, by rfl⟩ : syracuseStep 28579715 = 42869573) B42869573
theorem B9050399 : Blo 742328 9050399 := bstep (se 1 (by rfl) ⟨6787799, by rfl⟩ : syracuseStep 9050399 = 13575599) B13575599
theorem B1677599 : Blo 742328 1677599 := bstep (se 1 (by rfl) ⟨1258199, by rfl⟩ : syracuseStep 1677599 = 2516399) B2516399
theorem B3184991 : Blo 742328 3184991 := bstep (se 1 (by rfl) ⟨2388743, by rfl⟩ : syracuseStep 3184991 = 4777487) B4777487
theorem B6363623 : Blo 742328 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B1415657 : Blo 742328 1415657 := bstep (se 2 (by rfl) ⟨530871, by rfl⟩ : syracuseStep 1415657 = 1061743) B1061743
theorem B1677851 : Blo 742328 1677851 := bstep (se 1 (by rfl) ⟨1258388, by rfl⟩ : syracuseStep 1677851 = 2516777) B2516777
theorem B2825543 : Blo 742328 2825543 := bstep (se 1 (by rfl) ⟨2119157, by rfl⟩ : syracuseStep 2825543 = 4238315) B4238315
theorem B1253083 : Blo 742328 1253083 := bstep (se 1 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 1253083 = 1879625) B1879625
theorem B11476829 : Blo 742328 11476829 := bstep (se 3 (by rfl) ⟨2151905, by rfl⟩ : syracuseStep 11476829 = 4303811) B4303811
theorem B1679201 : Blo 742328 1679201 := bstep (se 2 (by rfl) ⟨629700, by rfl⟩ : syracuseStep 1679201 = 1259401) B1259401
theorem B3776381 : Blo 742328 3776381 := bstep (se 3 (by rfl) ⟨708071, by rfl⟩ : syracuseStep 3776381 = 1416143) B1416143
theorem B1253353 : Blo 742328 1253353 := bstep (se 2 (by rfl) ⟨470007, by rfl⟩ : syracuseStep 1253353 = 940015) B940015
theorem B3186665 : Blo 742328 3186665 := bstep (se 2 (by rfl) ⟨1194999, by rfl⟩ : syracuseStep 3186665 = 2389999) B2389999
theorem B3579983 : Blo 742328 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B6365537 : Blo 742328 6365537 := bstep (se 2 (by rfl) ⟨2387076, by rfl⟩ : syracuseStep 6365537 = 4774153) B4774153
theorem B3187127 : Blo 742328 3187127 := bstep (se 1 (by rfl) ⟨2390345, by rfl⟩ : syracuseStep 3187127 = 4780691) B4780691
theorem B1254055 : Blo 742328 1254055 := bstep (se 1 (by rfl) ⟨940541, by rfl⟩ : syracuseStep 1254055 = 1881083) B1881083
theorem B2826971 : Blo 742328 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B3580769 : Blo 742328 3580769 := bstep (se 2 (by rfl) ⟨1342788, by rfl⟩ : syracuseStep 3580769 = 2685577) B2685577
theorem B1254379 : Blo 742328 1254379 := bstep (se 1 (by rfl) ⟨940784, by rfl⟩ : syracuseStep 1254379 = 1881569) B1881569
theorem B1254521 : Blo 742328 1254521 := bstep (se 2 (by rfl) ⟨470445, by rfl⟩ : syracuseStep 1254521 = 940891) B940891
theorem B5350855 : Blo 742328 5350855 := bstep (se 1 (by rfl) ⟨4013141, by rfl⟩ : syracuseStep 5350855 = 8026283) B8026283
theorem B4761031 : Blo 742328 4761031 := bstep (se 1 (by rfl) ⟨3570773, by rfl⟩ : syracuseStep 4761031 = 7141547) B7141547
theorem B3581999 : Blo 742328 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B1255817 : Blo 742328 1255817 := bstep (se 2 (by rfl) ⟨470931, by rfl⟩ : syracuseStep 1255817 = 941863) B941863
theorem B3582443 : Blo 742328 3582443 := bstep (se 1 (by rfl) ⟨2686832, by rfl⟩ : syracuseStep 3582443 = 5373665) B5373665
theorem B4827863 : Blo 742328 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B12069985 : Blo 742328 12069985 := bstep (se 2 (by rfl) ⟨4526244, by rfl⟩ : syracuseStep 12069985 = 9052489) B9052489
theorem B2010377 : Blo 742328 2010377 := bstep (se 2 (by rfl) ⟨753891, by rfl⟩ : syracuseStep 2010377 = 1507783) B1507783
theorem B2829887 : Blo 742328 2829887 := bstep (se 1 (by rfl) ⟨2122415, by rfl⟩ : syracuseStep 2829887 = 4244831) B4244831
theorem B3583673 : Blo 742328 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B1257545 : Blo 742328 1257545 := bstep (se 2 (by rfl) ⟨471579, by rfl⟩ : syracuseStep 1257545 = 943159) B943159
theorem B1257599 : Blo 742328 1257599 := bstep (se 1 (by rfl) ⟨943199, by rfl⟩ : syracuseStep 1257599 = 1886399) B1886399
theorem B4239499 : Blo 742328 4239499 := bstep (se 1 (by rfl) ⟨3179624, by rfl⟩ : syracuseStep 4239499 = 6359249) B6359249
theorem B4763879 : Blo 742328 4763879 := bstep (se 1 (by rfl) ⟨3572909, by rfl⟩ : syracuseStep 4763879 = 7145819) B7145819
theorem B5648777 : Blo 742328 5648777 := bstep (se 2 (by rfl) ⟨2118291, by rfl⟩ : syracuseStep 5648777 = 4236583) B4236583
theorem B1258537 : Blo 742328 1258537 := bstep (se 2 (by rfl) ⟨471951, by rfl⟩ : syracuseStep 1258537 = 943903) B943903
theorem B1258679 : Blo 742328 1258679 := bstep (se 1 (by rfl) ⟨944009, by rfl⟩ : syracuseStep 1258679 = 1888019) B1888019
theorem B4764905 : Blo 742328 4764905 := bstep (se 2 (by rfl) ⟨1786839, by rfl⟩ : syracuseStep 4764905 = 3573679) B3573679
theorem B2832043 : Blo 742328 2832043 := bstep (se 1 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 2832043 = 4248065) B4248065
theorem B44086999 : Blo 742328 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B9549535 : Blo 742328 9549535 := bstep (se 1 (by rfl) ⟨7162151, by rfl⟩ : syracuseStep 9549535 = 14324303) B14324303
theorem B6109607 : Blo 742328 6109607 := bstep (se 1 (by rfl) ⟨4582205, by rfl⟩ : syracuseStep 6109607 = 9164411) B9164411
theorem B1587899 : Blo 742328 1587899 := bstep (se 1 (by rfl) ⟨1190924, by rfl⟩ : syracuseStep 1587899 = 2381849) B2381849
theorem B1883047 : Blo 742328 1883047 := bstep (se 1 (by rfl) ⟨1412285, by rfl⟩ : syracuseStep 1883047 = 2824571) B2824571
theorem B2833319 : Blo 742328 2833319 := bstep (se 1 (by rfl) ⟨2124989, by rfl⟩ : syracuseStep 2833319 = 4249979) B4249979
theorem B2505761 : Blo 742328 2505761 := bstep (se 2 (by rfl) ⟨939660, by rfl⟩ : syracuseStep 2505761 = 1879321) B1879321
theorem B1195435 : Blo 742328 1195435 := bstep (se 1 (by rfl) ⟨896576, by rfl⟩ : syracuseStep 1195435 = 1793153) B1793153
theorem B2506463 : Blo 742328 2506463 := bstep (se 1 (by rfl) ⟨1879847, by rfl⟩ : syracuseStep 2506463 = 3759695) B3759695
theorem B835303 : Blo 742328 835303 := bstep (se 1 (by rfl) ⟨626477, by rfl⟩ : syracuseStep 835303 = 1252955) B1252955
theorem B7258403 : Blo 742328 7258403 := bstep (se 1 (by rfl) ⟨5443802, by rfl⟩ : syracuseStep 7258403 = 10887605) B10887605
theorem B1884455 : Blo 742328 1884455 := bstep (se 1 (by rfl) ⟨1413341, by rfl⟩ : syracuseStep 1884455 = 2826683) B2826683
theorem B2507165 : Blo 742328 2507165 := bstep (se 3 (by rfl) ⟨470093, by rfl⟩ : syracuseStep 2507165 = 940187) B940187
theorem B7651835 : Blo 742328 7651835 := bstep (se 1 (by rfl) ⟨5738876, by rfl⟩ : syracuseStep 7651835 = 11477753) B11477753
theorem B836383 : Blo 742328 836383 := bstep (se 1 (by rfl) ⟨627287, by rfl⟩ : syracuseStep 836383 = 1254575) B1254575
theorem B1885295 : Blo 742328 1885295 := bstep (se 1 (by rfl) ⟨1413971, by rfl⟩ : syracuseStep 1885295 = 2827943) B2827943
theorem B5654123 : Blo 742328 5654123 := bstep (se 1 (by rfl) ⟨4240592, by rfl⟩ : syracuseStep 5654123 = 8481185) B8481185
theorem B837679 : Blo 742328 837679 := bstep (se 1 (by rfl) ⟨628259, by rfl⟩ : syracuseStep 837679 = 1256519) B1256519
theorem B837967 : Blo 742328 837967 := bstep (se 1 (by rfl) ⟨628475, by rfl⟩ : syracuseStep 837967 = 1256951) B1256951
theorem B2509163 : Blo 742328 2509163 := bstep (se 1 (by rfl) ⟨1881872, by rfl⟩ : syracuseStep 2509163 = 3763745) B3763745
theorem B5720647 : Blo 742328 5720647 := bstep (se 1 (by rfl) ⟨4290485, by rfl⟩ : syracuseStep 5720647 = 8580971) B8580971
theorem B2509433 : Blo 742328 2509433 := bstep (se 2 (by rfl) ⟨941037, by rfl⟩ : syracuseStep 2509433 = 1882075) B1882075
theorem B1887097 : Blo 742328 1887097 := bstep (se 2 (by rfl) ⟨707661, by rfl⟩ : syracuseStep 1887097 = 1415323) B1415323
theorem B838651 : Blo 742328 838651 := bstep (se 1 (by rfl) ⟨628988, by rfl⟩ : syracuseStep 838651 = 1257977) B1257977
theorem B3394703 : Blo 742328 3394703 := bstep (se 1 (by rfl) ⟨2546027, by rfl⟩ : syracuseStep 3394703 = 5092055) B5092055
theorem B838831 : Blo 742328 838831 := bstep (se 1 (by rfl) ⟨629123, by rfl⟩ : syracuseStep 838831 = 1258247) B1258247
theorem B1133951 : Blo 742328 1133951 := bstep (se 1 (by rfl) ⟨850463, by rfl⟩ : syracuseStep 1133951 = 1700927) B1700927
theorem B10702631 : Blo 742328 10702631 := bstep (se 1 (by rfl) ⟨8026973, by rfl⟩ : syracuseStep 10702631 = 16053947) B16053947
theorem B839551 : Blo 742328 839551 := bstep (se 1 (by rfl) ⟨629663, by rfl⟩ : syracuseStep 839551 = 1259327) B1259327
theorem B1888231 : Blo 742328 1888231 := bstep (se 1 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 1888231 = 2832347) B2832347
theorem B4247747 : Blo 742328 4247747 := bstep (se 1 (by rfl) ⟨3185810, by rfl⟩ : syracuseStep 4247747 = 6371621) B6371621
theorem B5099719 : Blo 742328 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B2183411 : Blo 742328 2183411 := bstep (se 1 (by rfl) ⟨1637558, by rfl⟩ : syracuseStep 2183411 = 3275117) B3275117
theorem B742383 : Blo 742328 742383 := bstep (se 1 (by rfl) ⟨556787, by rfl⟩ : syracuseStep 742383 = 1113575) B1113575
theorem B742471 : Blo 742328 742471 := bstep (se 1 (by rfl) ⟨556853, by rfl⟩ : syracuseStep 742471 = 1113707) B1113707
theorem B742555 : Blo 742328 742555 := bstep (se 1 (by rfl) ⟨556916, by rfl⟩ : syracuseStep 742555 = 1113833) B1113833
theorem B742651 : Blo 742328 742651 := bstep (se 1 (by rfl) ⟨556988, by rfl⟩ : syracuseStep 742651 = 1113977) B1113977
theorem B742719 : Blo 742328 742719 := bstep (se 1 (by rfl) ⟨557039, by rfl⟩ : syracuseStep 742719 = 1114079) B1114079
theorem B6346127 : Blo 742328 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B742887 : Blo 742328 742887 := bstep (se 1 (by rfl) ⟨557165, by rfl⟩ : syracuseStep 742887 = 1114331) B1114331
theorem B742895 : Blo 742328 742895 := bstep (se 1 (by rfl) ⟨557171, by rfl⟩ : syracuseStep 742895 = 1114343) B1114343
theorem B743003 : Blo 742328 743003 := bstep (se 1 (by rfl) ⟨557252, by rfl⟩ : syracuseStep 743003 = 1114505) B1114505
theorem B743067 : Blo 742328 743067 := bstep (se 1 (by rfl) ⟨557300, by rfl⟩ : syracuseStep 743067 = 1114601) B1114601
theorem B743151 : Blo 742328 743151 := bstep (se 1 (by rfl) ⟨557363, by rfl⟩ : syracuseStep 743151 = 1114727) B1114727
theorem B743239 : Blo 742328 743239 := bstep (se 1 (by rfl) ⟨557429, by rfl⟩ : syracuseStep 743239 = 1114859) B1114859
theorem B743259 : Blo 742328 743259 := bstep (se 1 (by rfl) ⟨557444, by rfl⟩ : syracuseStep 743259 = 1114889) B1114889
theorem B743327 : Blo 742328 743327 := bstep (se 1 (by rfl) ⟨557495, by rfl⟩ : syracuseStep 743327 = 1114991) B1114991
theorem B743495 : Blo 742328 743495 := bstep (se 1 (by rfl) ⟨557621, by rfl⟩ : syracuseStep 743495 = 1115243) B1115243
theorem B743655 : Blo 742328 743655 := bstep (se 1 (by rfl) ⟨557741, by rfl⟩ : syracuseStep 743655 = 1115483) B1115483
theorem B743839 : Blo 742328 743839 := bstep (se 1 (by rfl) ⟨557879, by rfl⟩ : syracuseStep 743839 = 1115759) B1115759
theorem B743887 : Blo 742328 743887 := bstep (se 1 (by rfl) ⟨557915, by rfl⟩ : syracuseStep 743887 = 1115831) B1115831
theorem B743911 : Blo 742328 743911 := bstep (se 1 (by rfl) ⟨557933, by rfl⟩ : syracuseStep 743911 = 1115867) B1115867
theorem B744027 : Blo 742328 744027 := bstep (se 1 (by rfl) ⟨558020, by rfl⟩ : syracuseStep 744027 = 1116041) B1116041
theorem B744095 : Blo 742328 744095 := bstep (se 1 (by rfl) ⟨558071, by rfl⟩ : syracuseStep 744095 = 1116143) B1116143
theorem B12409649 : Blo 742328 12409649 := bstep (se 2 (by rfl) ⟨4653618, by rfl⟩ : syracuseStep 12409649 = 9307237) B9307237
theorem B744263 : Blo 742328 744263 := bstep (se 1 (by rfl) ⟨558197, by rfl⟩ : syracuseStep 744263 = 1116395) B1116395
theorem B744303 : Blo 742328 744303 := bstep (se 1 (by rfl) ⟨558227, by rfl⟩ : syracuseStep 744303 = 1116455) B1116455
theorem B744359 : Blo 742328 744359 := bstep (se 1 (by rfl) ⟨558269, by rfl⟩ : syracuseStep 744359 = 1116539) B1116539
theorem B6347767 : Blo 742328 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B744539 : Blo 742328 744539 := bstep (se 1 (by rfl) ⟨558404, by rfl⟩ : syracuseStep 744539 = 1116809) B1116809
theorem B744655 : Blo 742328 744655 := bstep (se 1 (by rfl) ⟨558491, by rfl⟩ : syracuseStep 744655 = 1116983) B1116983
theorem B744679 : Blo 742328 744679 := bstep (se 1 (by rfl) ⟨558509, by rfl⟩ : syracuseStep 744679 = 1117019) B1117019
theorem B744775 : Blo 742328 744775 := bstep (se 1 (by rfl) ⟨558581, by rfl⟩ : syracuseStep 744775 = 1117163) B1117163
theorem B744911 : Blo 742328 744911 := bstep (se 1 (by rfl) ⟨558683, by rfl⟩ : syracuseStep 744911 = 1117367) B1117367
theorem B6970835 : Blo 742328 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B6446567 : Blo 742328 6446567 := bstep (se 1 (by rfl) ⟨4834925, by rfl⟩ : syracuseStep 6446567 = 9669851) B9669851
theorem B745071 : Blo 742328 745071 := bstep (se 1 (by rfl) ⟨558803, by rfl⟩ : syracuseStep 745071 = 1117607) B1117607
theorem B745127 : Blo 742328 745127 := bstep (se 1 (by rfl) ⟨558845, by rfl⟩ : syracuseStep 745127 = 1117691) B1117691
theorem B745191 : Blo 742328 745191 := bstep (se 1 (by rfl) ⟨558893, by rfl⟩ : syracuseStep 745191 = 1117787) B1117787
theorem B745247 : Blo 742328 745247 := bstep (se 1 (by rfl) ⟨558935, by rfl⟩ : syracuseStep 745247 = 1117871) B1117871
theorem B745327 : Blo 742328 745327 := bstep (se 1 (by rfl) ⟨558995, by rfl⟩ : syracuseStep 745327 = 1117991) B1117991
theorem B745383 : Blo 742328 745383 := bstep (se 1 (by rfl) ⟨559037, by rfl⟩ : syracuseStep 745383 = 1118075) B1118075
theorem B6807577 : Blo 742328 6807577 := bstep (se 2 (by rfl) ⟨2552841, by rfl⟩ : syracuseStep 6807577 = 5105683) B5105683
theorem B7135397 : Blo 742328 7135397 := bstep (se 4 (by rfl) ⟨668943, by rfl⟩ : syracuseStep 7135397 = 1337887) B1337887
theorem B745663 : Blo 742328 745663 := bstep (se 1 (by rfl) ⟨559247, by rfl⟩ : syracuseStep 745663 = 1118495) B1118495
theorem B745679 : Blo 742328 745679 := bstep (se 1 (by rfl) ⟨559259, by rfl⟩ : syracuseStep 745679 = 1118519) B1118519
theorem B2121983 : Blo 742328 2121983 := bstep (se 1 (by rfl) ⟨1591487, by rfl⟩ : syracuseStep 2121983 = 3182975) B3182975
theorem B5660927 : Blo 742328 5660927 := bstep (se 1 (by rfl) ⟨4245695, by rfl⟩ : syracuseStep 5660927 = 8491391) B8491391
theorem B745727 : Blo 742328 745727 := bstep (se 1 (by rfl) ⟨559295, by rfl⟩ : syracuseStep 745727 = 1118591) B1118591
theorem B745775 : Blo 742328 745775 := bstep (se 1 (by rfl) ⟨559331, by rfl⟩ : syracuseStep 745775 = 1118663) B1118663
theorem B1270073 : Blo 742328 1270073 := bstep (se 2 (by rfl) ⟨476277, by rfl⟩ : syracuseStep 1270073 = 952555) B952555
theorem B746011 : Blo 742328 746011 := bstep (se 1 (by rfl) ⟨559508, by rfl⟩ : syracuseStep 746011 = 1119017) B1119017
theorem B746015 : Blo 742328 746015 := bstep (se 1 (by rfl) ⟨559511, by rfl⟩ : syracuseStep 746015 = 1119023) B1119023
theorem B746095 : Blo 742328 746095 := bstep (se 1 (by rfl) ⟨559571, by rfl⟩ : syracuseStep 746095 = 1119143) B1119143
theorem B746151 : Blo 742328 746151 := bstep (se 1 (by rfl) ⟨559613, by rfl⟩ : syracuseStep 746151 = 1119227) B1119227
theorem B746191 : Blo 742328 746191 := bstep (se 1 (by rfl) ⟨559643, by rfl⟩ : syracuseStep 746191 = 1119287) B1119287
theorem B746271 : Blo 742328 746271 := bstep (se 1 (by rfl) ⟨559703, by rfl⟩ : syracuseStep 746271 = 1119407) B1119407
theorem B9561017 : Blo 742328 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B7234775 : Blo 742328 7234775 := bstep (se 1 (by rfl) ⟨5426081, by rfl⟩ : syracuseStep 7234775 = 10852163) B10852163
theorem B4515347 : Blo 742328 4515347 := bstep (se 1 (by rfl) ⟨3386510, by rfl⟩ : syracuseStep 4515347 = 6773021) B6773021
theorem B2516507 : Blo 742328 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B2385899 : Blo 742328 2385899 := bstep (se 1 (by rfl) ⟨1789424, by rfl⟩ : syracuseStep 2385899 = 3578849) B3578849
theorem B4778027 : Blo 742328 4778027 := bstep (se 1 (by rfl) ⟨3583520, by rfl⟩ : syracuseStep 4778027 = 7167041) B7167041
theorem B34760897 : Blo 742328 34760897 := bstep (se 2 (by rfl) ⟨13035336, by rfl⟩ : syracuseStep 34760897 = 26070673) B26070673
theorem B6024775 : Blo 742328 6024775 := bstep (se 1 (by rfl) ⟨4518581, by rfl⟩ : syracuseStep 6024775 = 9037163) B9037163
theorem B5664329 : Blo 742328 5664329 := bstep (se 2 (by rfl) ⟨2124123, by rfl⟩ : syracuseStep 5664329 = 4248247) B4248247
theorem B2387681 : Blo 742328 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B12710843 : Blo 742328 12710843 := bstep (se 1 (by rfl) ⟨9533132, by rfl⟩ : syracuseStep 12710843 = 19066265) B19066265
theorem B3012065 : Blo 742328 3012065 := bstep (se 2 (by rfl) ⟨1129524, by rfl⟩ : syracuseStep 3012065 = 2259049) B2259049
theorem B1701803 : Blo 742328 1701803 := bstep (se 1 (by rfl) ⟨1276352, by rfl⟩ : syracuseStep 1701803 = 2552705) B2552705
theorem B5666759 : Blo 742328 5666759 := bstep (se 1 (by rfl) ⟨4250069, by rfl⟩ : syracuseStep 5666759 = 8500139) B8500139
theorem B3177917 : Blo 742328 3177917 := bstep (se 3 (by rfl) ⟨595859, by rfl⟩ : syracuseStep 3177917 = 1191719) B1191719
theorem B1113551 : Blo 742328 1113551 := bstep (se 1 (by rfl) ⟨835163, by rfl⟩ : syracuseStep 1113551 = 1670327) B1670327
theorem B1670651 : Blo 742328 1670651 := bstep (se 1 (by rfl) ⟨1252988, by rfl⟩ : syracuseStep 1670651 = 2505977) B2505977
theorem B1670831 : Blo 742328 1670831 := bstep (se 1 (by rfl) ⟨1253123, by rfl⟩ : syracuseStep 1670831 = 2506247) B2506247
theorem B1670921 : Blo 742328 1670921 := bstep (se 2 (by rfl) ⟨626595, by rfl⟩ : syracuseStep 1670921 = 1253191) B1253191
theorem B4587293 : Blo 742328 4587293 := bstep (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) B1720235
theorem B1113935 : Blo 742328 1113935 := bstep (se 1 (by rfl) ⟨835451, by rfl⟩ : syracuseStep 1113935 = 1670903) B1670903
theorem B5734223 : Blo 742328 5734223 := bstep (se 1 (by rfl) ⟨4300667, by rfl⟩ : syracuseStep 5734223 = 8601335) B8601335
theorem B1114055 : Blo 742328 1114055 := bstep (se 1 (by rfl) ⟨835541, by rfl⟩ : syracuseStep 1114055 = 1671083) B1671083
theorem B9076769 : Blo 742328 9076769 := bstep (se 2 (by rfl) ⟨3403788, by rfl⟩ : syracuseStep 9076769 = 6807577) B6807577
theorem B1114367 : Blo 742328 1114367 := bstep (se 1 (by rfl) ⟨835775, by rfl⟩ : syracuseStep 1114367 = 1671551) B1671551
theorem B1671443 : Blo 742328 1671443 := bstep (se 1 (by rfl) ⟨1253582, by rfl⟩ : syracuseStep 1671443 = 2507165) B2507165
theorem B3768605 : Blo 742328 3768605 := bstep (se 3 (by rfl) ⟨706613, by rfl⟩ : syracuseStep 3768605 = 1413227) B1413227
theorem B1114523 : Blo 742328 1114523 := bstep (se 1 (by rfl) ⟨835892, by rfl⟩ : syracuseStep 1114523 = 1671785) B1671785
theorem B1114943 : Blo 742328 1114943 := bstep (se 1 (by rfl) ⟨836207, by rfl⟩ : syracuseStep 1114943 = 1672415) B1672415
theorem B1672073 : Blo 742328 1672073 := bstep (se 2 (by rfl) ⟨627027, by rfl⟩ : syracuseStep 1672073 = 1254055) B1254055
theorem B1115087 : Blo 742328 1115087 := bstep (se 1 (by rfl) ⟨836315, by rfl⟩ : syracuseStep 1115087 = 1672631) B1672631
theorem B1115177 : Blo 742328 1115177 := bstep (se 2 (by rfl) ⟨418191, by rfl⟩ : syracuseStep 1115177 = 836383) B836383
theorem B1115207 : Blo 742328 1115207 := bstep (se 1 (by rfl) ⟨836405, by rfl⟩ : syracuseStep 1115207 = 1672811) B1672811
theorem B3769415 : Blo 742328 3769415 := bstep (se 1 (by rfl) ⟨2827061, by rfl⟩ : syracuseStep 3769415 = 5654123) B5654123
theorem B13567123 : Blo 742328 13567123 := bstep (se 1 (by rfl) ⟨10175342, by rfl⟩ : syracuseStep 13567123 = 20350685) B20350685
theorem B1115387 : Blo 742328 1115387 := bstep (se 1 (by rfl) ⟨836540, by rfl⟩ : syracuseStep 1115387 = 1673081) B1673081
theorem B1672505 : Blo 742328 1672505 := bstep (se 2 (by rfl) ⟨627189, by rfl⟩ : syracuseStep 1672505 = 1254379) B1254379
theorem B2819407 : Blo 742328 2819407 := bstep (se 1 (by rfl) ⟨2114555, by rfl⟩ : syracuseStep 2819407 = 4229111) B4229111
theorem B1115675 : Blo 742328 1115675 := bstep (se 1 (by rfl) ⟨836756, by rfl⟩ : syracuseStep 1115675 = 1673513) B1673513
theorem B1672775 : Blo 742328 1672775 := bstep (se 1 (by rfl) ⟨1254581, by rfl⟩ : syracuseStep 1672775 = 2509163) B2509163
theorem B1672955 : Blo 742328 1672955 := bstep (se 1 (by rfl) ⟨1254716, by rfl⟩ : syracuseStep 1672955 = 2509433) B2509433
theorem B1116059 : Blo 742328 1116059 := bstep (se 1 (by rfl) ⟨837044, by rfl⟩ : syracuseStep 1116059 = 1674089) B1674089
theorem B1116095 : Blo 742328 1116095 := bstep (se 1 (by rfl) ⟨837071, by rfl⟩ : syracuseStep 1116095 = 1674143) B1674143
theorem B2820167 : Blo 742328 2820167 := bstep (se 1 (by rfl) ⟨2115125, by rfl⟩ : syracuseStep 2820167 = 4230251) B4230251
theorem B2263135 : Blo 742328 2263135 := bstep (se 1 (by rfl) ⟨1697351, by rfl⟩ : syracuseStep 2263135 = 3394703) B3394703
theorem B1116719 : Blo 742328 1116719 := bstep (se 1 (by rfl) ⟨837539, by rfl⟩ : syracuseStep 1116719 = 1675079) B1675079
theorem B22874723 : Blo 742328 22874723 := bstep (se 1 (by rfl) ⟨17156042, by rfl⟩ : syracuseStep 22874723 = 34312085) B34312085
theorem B1116839 : Blo 742328 1116839 := bstep (se 1 (by rfl) ⟨837629, by rfl⟩ : syracuseStep 1116839 = 1675259) B1675259
theorem B1116905 : Blo 742328 1116905 := bstep (se 2 (by rfl) ⟨418839, by rfl⟩ : syracuseStep 1116905 = 837679) B837679
theorem B1116911 : Blo 742328 1116911 := bstep (se 1 (by rfl) ⟨837683, by rfl⟩ : syracuseStep 1116911 = 1675367) B1675367
theorem B1116959 : Blo 742328 1116959 := bstep (se 1 (by rfl) ⟨837719, by rfl⟩ : syracuseStep 1116959 = 1675439) B1675439
theorem B1117289 : Blo 742328 1117289 := bstep (se 2 (by rfl) ⟨418983, by rfl⟩ : syracuseStep 1117289 = 837967) B837967
theorem B1117415 : Blo 742328 1117415 := bstep (se 1 (by rfl) ⟨838061, by rfl⟩ : syracuseStep 1117415 = 1676123) B1676123
theorem B4230751 : Blo 742328 4230751 := bstep (se 1 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 4230751 = 6346127) B6346127
theorem B1117919 : Blo 742328 1117919 := bstep (se 1 (by rfl) ⟨838439, by rfl⟩ : syracuseStep 1117919 = 1676879) B1676879
theorem B61017893 : Blo 742328 61017893 := bstep (se 4 (by rfl) ⟨5720427, by rfl⟩ : syracuseStep 61017893 = 11440855) B11440855
theorem B12095477 : Blo 742328 12095477 := bstep (se 5 (by rfl) ⟨566975, by rfl⟩ : syracuseStep 12095477 = 1133951) B1133951
theorem B1118201 : Blo 742328 1118201 := bstep (se 2 (by rfl) ⟨419325, by rfl⟩ : syracuseStep 1118201 = 838651) B838651
theorem B16093313 : Blo 742328 16093313 := bstep (se 2 (by rfl) ⟨6034992, by rfl⟩ : syracuseStep 16093313 = 12069985) B12069985
theorem B6033599 : Blo 742328 6033599 := bstep (se 1 (by rfl) ⟨4525199, by rfl⟩ : syracuseStep 6033599 = 9050399) B9050399
theorem B1118399 : Blo 742328 1118399 := bstep (se 1 (by rfl) ⟨838799, by rfl⟩ : syracuseStep 1118399 = 1677599) B1677599
theorem B1118441 : Blo 742328 1118441 := bstep (se 2 (by rfl) ⟨419415, by rfl⟩ : syracuseStep 1118441 = 838831) B838831
theorem B1118567 : Blo 742328 1118567 := bstep (se 1 (by rfl) ⟨838925, by rfl⟩ : syracuseStep 1118567 = 1677851) B1677851
theorem B3019393 : Blo 742328 3019393 := bstep (se 2 (by rfl) ⟨1132272, by rfl⟩ : syracuseStep 3019393 = 2264545) B2264545
theorem B8033033 : Blo 742328 8033033 := bstep (se 2 (by rfl) ⟨3012387, by rfl⟩ : syracuseStep 8033033 = 6024775) B6024775
theorem B4297711 : Blo 742328 4297711 := bstep (se 1 (by rfl) ⟨3223283, by rfl⟩ : syracuseStep 4297711 = 6446567) B6446567
theorem B1119401 : Blo 742328 1119401 := bstep (se 2 (by rfl) ⟨419775, by rfl⟩ : syracuseStep 1119401 = 839551) B839551
theorem B1119467 : Blo 742328 1119467 := bstep (se 1 (by rfl) ⟨839600, by rfl⟩ : syracuseStep 1119467 = 1679201) B1679201
theorem B4756931 : Blo 742328 4756931 := bstep (se 1 (by rfl) ⟨3567698, by rfl⟩ : syracuseStep 4756931 = 7135397) B7135397
theorem B1414655 : Blo 742328 1414655 := bstep (se 1 (by rfl) ⟨1060991, by rfl⟩ : syracuseStep 1414655 = 2121983) B2121983
theorem B3773951 : Blo 742328 3773951 := bstep (se 1 (by rfl) ⟨2830463, by rfl⟩ : syracuseStep 3773951 = 5660927) B5660927
theorem B4823183 : Blo 742328 4823183 := bstep (se 1 (by rfl) ⟨3617387, by rfl⟩ : syracuseStep 4823183 = 7234775) B7234775
theorem B1677671 : Blo 742328 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B16292285 : Blo 742328 16292285 := bstep (se 3 (by rfl) ⟨3054803, by rfl⟩ : syracuseStep 16292285 = 6109607) B6109607
theorem B3775085 : Blo 742328 3775085 := bstep (se 3 (by rfl) ⟨707828, by rfl⟩ : syracuseStep 3775085 = 1415657) B1415657
theorem B3185351 : Blo 742328 3185351 := bstep (se 1 (by rfl) ⟨2389013, by rfl⟩ : syracuseStep 3185351 = 4778027) B4778027
theorem B1678049 : Blo 742328 1678049 := bstep (se 2 (by rfl) ⟨629268, by rfl⟩ : syracuseStep 1678049 = 1258537) B1258537
theorem B23173931 : Blo 742328 23173931 := bstep (se 1 (by rfl) ⟨17380448, by rfl⟩ : syracuseStep 23173931 = 34760897) B34760897
theorem B6036713 : Blo 742328 6036713 := bstep (se 2 (by rfl) ⟨2263767, by rfl⟩ : syracuseStep 6036713 = 4527535) B4527535
theorem B3776057 : Blo 742328 3776057 := bstep (se 2 (by rfl) ⟨1416021, by rfl⟩ : syracuseStep 3776057 = 2832043) B2832043
theorem B3776219 : Blo 742328 3776219 := bstep (se 1 (by rfl) ⟨2832164, by rfl⟩ : syracuseStep 3776219 = 5664329) B5664329
theorem B2008043 : Blo 742328 2008043 := bstep (se 1 (by rfl) ⟨1506032, by rfl⟩ : syracuseStep 2008043 = 3012065) B3012065
theorem B3777839 : Blo 742328 3777839 := bstep (se 1 (by rfl) ⟨2833379, by rfl⟩ : syracuseStep 3777839 = 5666759) B5666759
theorem B8463689 : Blo 742328 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B1058599 : Blo 742328 1058599 := bstep (se 1 (by rfl) ⟨793949, by rfl⟩ : syracuseStep 1058599 = 1587899) B1587899
theorem B12232781 : Blo 742328 12232781 := bstep (se 3 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 12232781 = 4587293) B4587293
theorem B1256303 : Blo 742328 1256303 := bstep (se 1 (by rfl) ⟨942227, by rfl⟩ : syracuseStep 1256303 = 1884455) B1884455
theorem B896303 : Blo 742328 896303 := bstep (se 1 (by rfl) ⟨672227, by rfl⟩ : syracuseStep 896303 = 1344455) B1344455
theorem B1256863 : Blo 742328 1256863 := bstep (se 1 (by rfl) ⟨942647, by rfl⟩ : syracuseStep 1256863 = 1885295) B1885295
theorem B1879919 : Blo 742328 1879919 := bstep (se 1 (by rfl) ⟨1409939, by rfl⟩ : syracuseStep 1879919 = 2819879) B2819879
theorem B1291063 : Blo 742328 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B1881407 : Blo 742328 1881407 := bstep (se 1 (by rfl) ⟨1411055, by rfl⟩ : syracuseStep 1881407 = 2822111) B2822111
theorem B2831831 : Blo 742328 2831831 := bstep (se 1 (by rfl) ⟨2123873, by rfl⟩ : syracuseStep 2831831 = 4247747) B4247747
theorem B1455607 : Blo 742328 1455607 := bstep (se 1 (by rfl) ⟨1091705, by rfl⟩ : syracuseStep 1455607 = 2183411) B2183411
theorem B4765391 : Blo 742328 4765391 := bstep (se 1 (by rfl) ⟨3574043, by rfl⟩ : syracuseStep 4765391 = 7148087) B7148087
theorem B1882055 : Blo 742328 1882055 := bstep (se 1 (by rfl) ⟨1411541, by rfl⟩ : syracuseStep 1882055 = 2823083) B2823083
theorem B1882399 : Blo 742328 1882399 := bstep (se 1 (by rfl) ⟨1411799, by rfl⟩ : syracuseStep 1882399 = 2823599) B2823599
theorem B2013751 : Blo 742328 2013751 := bstep (se 1 (by rfl) ⟨1510313, by rfl⟩ : syracuseStep 2013751 = 3020627) B3020627
theorem B19053143 : Blo 742328 19053143 := bstep (se 1 (by rfl) ⟨14289857, by rfl⟩ : syracuseStep 19053143 = 28579715) B28579715
theorem B4242233 : Blo 742328 4242233 := bstep (se 2 (by rfl) ⟨1590837, by rfl⟩ : syracuseStep 4242233 = 3181675) B3181675
theorem B4242415 : Blo 742328 4242415 := bstep (se 1 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 4242415 = 6363623) B6363623
theorem B8273099 : Blo 742328 8273099 := bstep (se 1 (by rfl) ⟨6204824, by rfl⟩ : syracuseStep 8273099 = 12409649) B12409649
theorem B1883695 : Blo 742328 1883695 := bstep (se 1 (by rfl) ⟨1412771, by rfl⟩ : syracuseStep 1883695 = 2825543) B2825543
theorem B7651219 : Blo 742328 7651219 := bstep (se 1 (by rfl) ⟨5738414, by rfl⟩ : syracuseStep 7651219 = 11476829) B11476829
theorem B15253505 : Blo 742328 15253505 := bstep (se 2 (by rfl) ⟨5720064, by rfl⟩ : syracuseStep 15253505 = 11440129) B11440129
theorem B5652665 : Blo 742328 5652665 := bstep (se 2 (by rfl) ⟨2119749, by rfl⟩ : syracuseStep 5652665 = 4239499) B4239499
theorem B4243691 : Blo 742328 4243691 := bstep (se 1 (by rfl) ⟨3182768, by rfl⟩ : syracuseStep 4243691 = 6365537) B6365537
theorem B6799625 : Blo 742328 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B1884647 : Blo 742328 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B6374011 : Blo 742328 6374011 := bstep (se 1 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 6374011 = 9561017) B9561017
theorem B836347 : Blo 742328 836347 := bstep (se 1 (by rfl) ⟨627260, by rfl⟩ : syracuseStep 836347 = 1254521) B1254521
theorem B1590599 : Blo 742328 1590599 := bstep (se 1 (by rfl) ⟨1192949, by rfl⟩ : syracuseStep 1590599 = 2385899) B2385899
theorem B837211 : Blo 742328 837211 := bstep (se 1 (by rfl) ⟨627908, by rfl⟩ : syracuseStep 837211 = 1255817) B1255817
theorem B1885801 : Blo 742328 1885801 := bstep (se 2 (by rfl) ⟨707175, by rfl⟩ : syracuseStep 1885801 = 1414351) B1414351
theorem B12732713 : Blo 742328 12732713 := bstep (se 2 (by rfl) ⟨4774767, by rfl⟩ : syracuseStep 12732713 = 9549535) B9549535
theorem B1886591 : Blo 742328 1886591 := bstep (se 1 (by rfl) ⟨1414943, by rfl⟩ : syracuseStep 1886591 = 2829887) B2829887
theorem B1591787 : Blo 742328 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B838363 : Blo 742328 838363 := bstep (se 1 (by rfl) ⟨628772, by rfl⟩ : syracuseStep 838363 = 1257545) B1257545
theorem B838399 : Blo 742328 838399 := bstep (se 1 (by rfl) ⟨628799, by rfl⟩ : syracuseStep 838399 = 1257599) B1257599
theorem B8473895 : Blo 742328 8473895 := bstep (se 1 (by rfl) ⟨6355421, by rfl⟩ : syracuseStep 8473895 = 12710843) B12710843
theorem B5361005 : Blo 742328 5361005 := bstep (se 3 (by rfl) ⟨1005188, by rfl⟩ : syracuseStep 5361005 = 2010377) B2010377
theorem B839119 : Blo 742328 839119 := bstep (se 1 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 839119 = 1258679) B1258679
theorem B2510729 : Blo 742328 2510729 := bstep (se 2 (by rfl) ⟨941523, by rfl⟩ : syracuseStep 2510729 = 1883047) B1883047
theorem B1134535 : Blo 742328 1134535 := bstep (se 1 (by rfl) ⟨850901, by rfl⟩ : syracuseStep 1134535 = 1701803) B1701803
theorem B1593913 : Blo 742328 1593913 := bstep (se 2 (by rfl) ⟨597717, by rfl⟩ : syracuseStep 1593913 = 1195435) B1195435
theorem B1888879 : Blo 742328 1888879 := bstep (se 1 (by rfl) ⟨1416659, by rfl⟩ : syracuseStep 1888879 = 2833319) B2833319
theorem B2118611 : Blo 742328 2118611 := bstep (se 1 (by rfl) ⟨1588958, by rfl⟩ : syracuseStep 2118611 = 3177917) B3177917
theorem B742367 : Blo 742328 742367 := bstep (se 1 (by rfl) ⟨556775, by rfl⟩ : syracuseStep 742367 = 1113551) B1113551
theorem B742623 : Blo 742328 742623 := bstep (se 1 (by rfl) ⟨556967, by rfl⟩ : syracuseStep 742623 = 1113935) B1113935
theorem B3822815 : Blo 742328 3822815 := bstep (se 1 (by rfl) ⟨2867111, by rfl⟩ : syracuseStep 3822815 = 5734223) B5734223
theorem B742703 : Blo 742328 742703 := bstep (se 1 (by rfl) ⟨557027, by rfl⟩ : syracuseStep 742703 = 1114055) B1114055
theorem B4838935 : Blo 742328 4838935 := bstep (se 1 (by rfl) ⟨3629201, by rfl⟩ : syracuseStep 4838935 = 7258403) B7258403
theorem B742943 : Blo 742328 742943 := bstep (se 1 (by rfl) ⟨557207, by rfl⟩ : syracuseStep 742943 = 1114415) B1114415
theorem B77518397 : Blo 742328 77518397 := bstep (se 3 (by rfl) ⟨14534699, by rfl⟩ : syracuseStep 77518397 = 29069399) B29069399
theorem B5101223 : Blo 742328 5101223 := bstep (se 1 (by rfl) ⟨3825917, by rfl⟩ : syracuseStep 5101223 = 7651835) B7651835
theorem B743103 : Blo 742328 743103 := bstep (se 1 (by rfl) ⟨557327, by rfl⟩ : syracuseStep 743103 = 1114655) B1114655
theorem B7165691 : Blo 742328 7165691 := bstep (se 1 (by rfl) ⟨5374268, by rfl⟩ : syracuseStep 7165691 = 10748537) B10748537
theorem B743551 : Blo 742328 743551 := bstep (se 1 (by rfl) ⟨557663, by rfl⟩ : syracuseStep 743551 = 1115327) B1115327
theorem B8476811 : Blo 742328 8476811 := bstep (se 1 (by rfl) ⟨6357608, by rfl⟩ : syracuseStep 8476811 = 12715217) B12715217
theorem B743647 : Blo 742328 743647 := bstep (se 1 (by rfl) ⟨557735, by rfl⟩ : syracuseStep 743647 = 1115471) B1115471
theorem B743707 : Blo 742328 743707 := bstep (se 1 (by rfl) ⟨557780, by rfl⟩ : syracuseStep 743707 = 1115561) B1115561
theorem B743807 : Blo 742328 743807 := bstep (se 1 (by rfl) ⟨557855, by rfl⟩ : syracuseStep 743807 = 1115711) B1115711
theorem B743835 : Blo 742328 743835 := bstep (se 1 (by rfl) ⟨557876, by rfl⟩ : syracuseStep 743835 = 1115753) B1115753
theorem B2382311 : Blo 742328 2382311 := bstep (se 1 (by rfl) ⟨1786733, by rfl⟩ : syracuseStep 2382311 = 3573467) B3573467
theorem B2513591 : Blo 742328 2513591 := bstep (se 1 (by rfl) ⟨1885193, by rfl⟩ : syracuseStep 2513591 = 3770387) B3770387
theorem B744127 : Blo 742328 744127 := bstep (se 1 (by rfl) ⟨558095, by rfl⟩ : syracuseStep 744127 = 1116191) B1116191
theorem B744255 : Blo 742328 744255 := bstep (se 1 (by rfl) ⟨558191, by rfl⟩ : syracuseStep 744255 = 1116383) B1116383
theorem B744295 : Blo 742328 744295 := bstep (se 1 (by rfl) ⟨558221, by rfl⟩ : syracuseStep 744295 = 1116443) B1116443
theorem B51534863 : Blo 742328 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B744511 : Blo 742328 744511 := bstep (se 1 (by rfl) ⟨558383, by rfl⟩ : syracuseStep 744511 = 1116767) B1116767
theorem B2514131 : Blo 742328 2514131 := bstep (se 1 (by rfl) ⟨1885598, by rfl⟩ : syracuseStep 2514131 = 3771197) B3771197
theorem B744699 : Blo 742328 744699 := bstep (se 1 (by rfl) ⟨558524, by rfl⟩ : syracuseStep 744699 = 1117049) B1117049
theorem B7134473 : Blo 742328 7134473 := bstep (se 2 (by rfl) ⟨2675427, by rfl⟩ : syracuseStep 7134473 = 5350855) B5350855
theorem B6348041 : Blo 742328 6348041 := bstep (se 2 (by rfl) ⟨2380515, by rfl⟩ : syracuseStep 6348041 = 4761031) B4761031
theorem B744731 : Blo 742328 744731 := bstep (se 1 (by rfl) ⟨558548, by rfl⟩ : syracuseStep 744731 = 1117097) B1117097
theorem B744831 : Blo 742328 744831 := bstep (se 1 (by rfl) ⟨558623, by rfl⟩ : syracuseStep 744831 = 1117247) B1117247
theorem B8478269 : Blo 742328 8478269 := bstep (se 3 (by rfl) ⟨1589675, by rfl⟩ : syracuseStep 8478269 = 3179351) B3179351
theorem B36789835 : Blo 742328 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B941807 : Blo 742328 941807 := bstep (se 1 (by rfl) ⟨706355, by rfl⟩ : syracuseStep 941807 = 1412711) B1412711
theorem B745199 : Blo 742328 745199 := bstep (se 1 (by rfl) ⟨558899, by rfl⟩ : syracuseStep 745199 = 1117799) B1117799
theorem B745455 : Blo 742328 745455 := bstep (se 1 (by rfl) ⟨559091, by rfl⟩ : syracuseStep 745455 = 1118183) B1118183
theorem B745535 : Blo 742328 745535 := bstep (se 1 (by rfl) ⟨559151, by rfl⟩ : syracuseStep 745535 = 1118303) B1118303
theorem B745543 : Blo 742328 745543 := bstep (se 1 (by rfl) ⟨559157, by rfl⟩ : syracuseStep 745543 = 1118315) B1118315
theorem B745575 : Blo 742328 745575 := bstep (se 1 (by rfl) ⟨559181, by rfl⟩ : syracuseStep 745575 = 1118363) B1118363
theorem B942187 : Blo 742328 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B2121835 : Blo 742328 2121835 := bstep (se 1 (by rfl) ⟨1591376, by rfl⟩ : syracuseStep 2121835 = 3182753) B3182753
theorem B3760343 : Blo 742328 3760343 := bstep (se 1 (by rfl) ⟨2820257, by rfl⟩ : syracuseStep 3760343 = 5640515) B5640515
theorem B3760505 : Blo 742328 3760505 := bstep (se 2 (by rfl) ⟨1410189, by rfl⟩ : syracuseStep 3760505 = 2820379) B2820379
theorem B746143 : Blo 742328 746143 := bstep (se 1 (by rfl) ⟨559607, by rfl⟩ : syracuseStep 746143 = 1119215) B1119215
theorem B2515643 : Blo 742328 2515643 := bstep (se 1 (by rfl) ⟨1886732, by rfl⟩ : syracuseStep 2515643 = 3773465) B3773465
theorem B4023047 : Blo 742328 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B7627529 : Blo 742328 7627529 := bstep (se 2 (by rfl) ⟨2860323, by rfl⟩ : syracuseStep 7627529 = 5720647) B5720647
theorem B2516129 : Blo 742328 2516129 := bstep (se 2 (by rfl) ⟨943548, by rfl⟩ : syracuseStep 2516129 = 1887097) B1887097
theorem B2123327 : Blo 742328 2123327 := bstep (se 1 (by rfl) ⟨1592495, by rfl⟩ : syracuseStep 2123327 = 3184991) B3184991
theorem B4647223 : Blo 742328 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B2517587 : Blo 742328 2517587 := bstep (se 1 (by rfl) ⟨1888190, by rfl⟩ : syracuseStep 2517587 = 3776381) B3776381
theorem B2517641 : Blo 742328 2517641 := bstep (se 2 (by rfl) ⟨944115, by rfl⟩ : syracuseStep 2517641 = 1888231) B1888231
theorem B2124443 : Blo 742328 2124443 := bstep (se 1 (by rfl) ⟨1593332, by rfl⟩ : syracuseStep 2124443 = 3186665) B3186665
theorem B2386655 : Blo 742328 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B846715 : Blo 742328 846715 := bstep (se 1 (by rfl) ⟨635036, by rfl⟩ : syracuseStep 846715 = 1270073) B1270073
theorem B2124751 : Blo 742328 2124751 := bstep (se 1 (by rfl) ⟨1593563, by rfl⟩ : syracuseStep 2124751 = 3187127) B3187127
theorem B8056037 : Blo 742328 8056037 := bstep (se 4 (by rfl) ⟨755253, by rfl⟩ : syracuseStep 8056037 = 1510507) B1510507
theorem B2387179 : Blo 742328 2387179 := bstep (se 1 (by rfl) ⟨1790384, by rfl⟩ : syracuseStep 2387179 = 3580769) B3580769
theorem B3010231 : Blo 742328 3010231 := bstep (se 1 (by rfl) ⟨2257673, by rfl⟩ : syracuseStep 3010231 = 4515347) B4515347
theorem B2387999 : Blo 742328 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B2388295 : Blo 742328 2388295 := bstep (se 1 (by rfl) ⟨1791221, by rfl⟩ : syracuseStep 2388295 = 3582443) B3582443
theorem B12874301 : Blo 742328 12874301 := bstep (se 3 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 12874301 = 4827863) B4827863
theorem B58782665 : Blo 742328 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B2389115 : Blo 742328 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B3175919 : Blo 742328 3175919 := bstep (se 1 (by rfl) ⟨2381939, by rfl⟩ : syracuseStep 3175919 = 4763879) B4763879
theorem B3765851 : Blo 742328 3765851 := bstep (se 1 (by rfl) ⟨2824388, by rfl⟩ : syracuseStep 3765851 = 5648777) B5648777
theorem B3176603 : Blo 742328 3176603 := bstep (se 1 (by rfl) ⟨2382452, by rfl⟩ : syracuseStep 3176603 = 4764905) B4764905
theorem B1670507 : Blo 742328 1670507 := bstep (se 1 (by rfl) ⟨1252880, by rfl⟩ : syracuseStep 1670507 = 2505761) B2505761
theorem B28540349 : Blo 742328 28540349 := bstep (se 3 (by rfl) ⟨5351315, by rfl⟩ : syracuseStep 28540349 = 10702631) B10702631
theorem B1670777 : Blo 742328 1670777 := bstep (se 2 (by rfl) ⟨626541, by rfl⟩ : syracuseStep 1670777 = 1253083) B1253083
theorem B1113737 : Blo 742328 1113737 := bstep (se 2 (by rfl) ⟨417651, by rfl⟩ : syracuseStep 1113737 = 835303) B835303
theorem B1113767 : Blo 742328 1113767 := bstep (se 1 (by rfl) ⟨835325, by rfl⟩ : syracuseStep 1113767 = 1670651) B1670651
theorem B1113887 : Blo 742328 1113887 := bstep (se 1 (by rfl) ⟨835415, by rfl⟩ : syracuseStep 1113887 = 1670831) B1670831
theorem B1670975 : Blo 742328 1670975 := bstep (se 1 (by rfl) ⟨1253231, by rfl⟩ : syracuseStep 1670975 = 2506463) B2506463
theorem B1113947 : Blo 742328 1113947 := bstep (se 1 (by rfl) ⟨835460, by rfl⟩ : syracuseStep 1113947 = 1670921) B1670921
theorem B1671137 : Blo 742328 1671137 := bstep (se 2 (by rfl) ⟨626676, by rfl⟩ : syracuseStep 1671137 = 1253353) B1253353
theorem B3768443 : Blo 742328 3768443 := bstep (se 1 (by rfl) ⟨2826332, by rfl⟩ : syracuseStep 3768443 = 5652665) B5652665
theorem B1114295 : Blo 742328 1114295 := bstep (se 1 (by rfl) ⟨835721, by rfl⟩ : syracuseStep 1114295 = 1671443) B1671443
theorem B1114715 : Blo 742328 1114715 := bstep (se 1 (by rfl) ⟨836036, by rfl⟩ : syracuseStep 1114715 = 1672073) B1672073
theorem B1115003 : Blo 742328 1115003 := bstep (se 1 (by rfl) ⟨836252, by rfl⟩ : syracuseStep 1115003 = 1672505) B1672505
theorem B1115129 : Blo 742328 1115129 := bstep (se 2 (by rfl) ⟨418173, by rfl⟩ : syracuseStep 1115129 = 836347) B836347
theorem B1115183 : Blo 742328 1115183 := bstep (se 1 (by rfl) ⟨836387, by rfl⟩ : syracuseStep 1115183 = 1672775) B1672775
theorem B1115303 : Blo 742328 1115303 := bstep (se 1 (by rfl) ⟨836477, by rfl⟩ : syracuseStep 1115303 = 1672955) B1672955
theorem B18089497 : Blo 742328 18089497 := bstep (se 2 (by rfl) ⟨6783561, by rfl⟩ : syracuseStep 18089497 = 13567123) B13567123
theorem B8488475 : Blo 742328 8488475 := bstep (se 1 (by rfl) ⟨6366356, by rfl⟩ : syracuseStep 8488475 = 12732713) B12732713
theorem B1116281 : Blo 742328 1116281 := bstep (se 2 (by rfl) ⟨418605, by rfl⟩ : syracuseStep 1116281 = 837211) B837211
theorem B3574003 : Blo 742328 3574003 := bstep (se 1 (by rfl) ⟨2680502, by rfl⟩ : syracuseStep 3574003 = 5361005) B5361005
theorem B1673819 : Blo 742328 1673819 := bstep (se 1 (by rfl) ⟨1255364, by rfl⟩ : syracuseStep 1673819 = 2510729) B2510729
theorem B8063651 : Blo 742328 8063651 := bstep (se 1 (by rfl) ⟨6047738, by rfl⟩ : syracuseStep 8063651 = 12095477) B12095477
theorem B3017513 : Blo 742328 3017513 := bstep (se 2 (by rfl) ⟨1131567, by rfl⟩ : syracuseStep 3017513 = 2263135) B2263135
theorem B10194173 : Blo 742328 10194173 := bstep (se 3 (by rfl) ⟨1911407, by rfl⟩ : syracuseStep 10194173 = 3822815) B3822815
theorem B1412407 : Blo 742328 1412407 := bstep (se 1 (by rfl) ⟨1059305, by rfl⟩ : syracuseStep 1412407 = 2118611) B2118611
theorem B1117817 : Blo 742328 1117817 := bstep (se 2 (by rfl) ⟨419181, by rfl⟩ : syracuseStep 1117817 = 838363) B838363
theorem B1117865 : Blo 742328 1117865 := bstep (se 2 (by rfl) ⟨419199, by rfl⟩ : syracuseStep 1117865 = 838399) B838399
theorem B51678931 : Blo 742328 51678931 := bstep (se 1 (by rfl) ⟨38759198, by rfl⟩ : syracuseStep 51678931 = 77518397) B77518397
theorem B1118447 : Blo 742328 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B3182905 : Blo 742328 3182905 := bstep (se 2 (by rfl) ⟨1193589, by rfl⟩ : syracuseStep 3182905 = 2387179) B2387179
theorem B13603261 : Blo 742328 13603261 := bstep (se 3 (by rfl) ⟨2550611, by rfl⟩ : syracuseStep 13603261 = 5101223) B5101223
theorem B1675727 : Blo 742328 1675727 := bstep (se 1 (by rfl) ⟨1256795, by rfl⟩ : syracuseStep 1675727 = 2513591) B2513591
theorem B1118699 : Blo 742328 1118699 := bstep (se 1 (by rfl) ⟨839024, by rfl⟩ : syracuseStep 1118699 = 1678049) B1678049
theorem B1675817 : Blo 742328 1675817 := bstep (se 2 (by rfl) ⟨628431, by rfl⟩ : syracuseStep 1675817 = 1256863) B1256863
theorem B1118825 : Blo 742328 1118825 := bstep (se 2 (by rfl) ⟨419559, by rfl⟩ : syracuseStep 1118825 = 839119) B839119
theorem B5641001 : Blo 742328 5641001 := bstep (se 2 (by rfl) ⟨2115375, by rfl⟩ : syracuseStep 5641001 = 4230751) B4230751
theorem B1676087 : Blo 742328 1676087 := bstep (se 1 (by rfl) ⟨1257065, by rfl⟩ : syracuseStep 1676087 = 2514131) B2514131
theorem B4756315 : Blo 742328 4756315 := bstep (se 1 (by rfl) ⟨3567236, by rfl⟩ : syracuseStep 4756315 = 7134473) B7134473
theorem B4232027 : Blo 742328 4232027 := bstep (se 1 (by rfl) ⟨3174020, by rfl⟩ : syracuseStep 4232027 = 6348041) B6348041
theorem B1512713 : Blo 742328 1512713 := bstep (se 2 (by rfl) ⟨567267, by rfl⟩ : syracuseStep 1512713 = 1134535) B1134535
theorem B3184393 : Blo 742328 3184393 := bstep (se 2 (by rfl) ⟨1194147, by rfl⟩ : syracuseStep 3184393 = 2388295) B2388295
theorem B1677095 : Blo 742328 1677095 := bstep (se 1 (by rfl) ⟨1257821, by rfl⟩ : syracuseStep 1677095 = 2515643) B2515643
theorem B5085019 : Blo 742328 5085019 := bstep (se 1 (by rfl) ⟨3813764, by rfl⟩ : syracuseStep 5085019 = 7627529) B7627529
theorem B1677419 : Blo 742328 1677419 := bstep (se 1 (by rfl) ⟨1258064, by rfl⟩ : syracuseStep 1677419 = 2516129) B2516129
theorem B5642459 : Blo 742328 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B1415551 : Blo 742328 1415551 := bstep (se 1 (by rfl) ⟨1061663, by rfl⟩ : syracuseStep 1415551 = 2123327) B2123327
theorem B1678391 : Blo 742328 1678391 := bstep (se 1 (by rfl) ⟨1258793, by rfl⟩ : syracuseStep 1678391 = 2517587) B2517587
theorem B1678427 : Blo 742328 1678427 := bstep (se 1 (by rfl) ⟨1258820, by rfl⟩ : syracuseStep 1678427 = 2517641) B2517641
theorem B1416295 : Blo 742328 1416295 := bstep (se 1 (by rfl) ⟨1062221, by rfl⟩ : syracuseStep 1416295 = 2124443) B2124443
theorem B1940809 : Blo 742328 1940809 := bstep (se 2 (by rfl) ⟨727803, by rfl⟩ : syracuseStep 1940809 = 1455607) B1455607
theorem B1253279 : Blo 742328 1253279 := bstep (se 1 (by rfl) ⟨939959, by rfl⟩ : syracuseStep 1253279 = 1879919) B1879919
theorem B1254271 : Blo 742328 1254271 := bstep (se 1 (by rfl) ⟨940703, by rfl⟩ : syracuseStep 1254271 = 1881407) B1881407
theorem B1254703 : Blo 742328 1254703 := bstep (se 1 (by rfl) ⟨941027, by rfl⟩ : syracuseStep 1254703 = 1882055) B1882055
theorem B5645861 : Blo 742328 5645861 := bstep (se 4 (by rfl) ⟨529299, by rfl⟩ : syracuseStep 5645861 = 1058599) B1058599
theorem B2828155 : Blo 742328 2828155 := bstep (se 1 (by rfl) ⟨2121116, by rfl⟩ : syracuseStep 2828155 = 4242233) B4242233
theorem B5515399 : Blo 742328 5515399 := bstep (se 1 (by rfl) ⟨4136549, by rfl⟩ : syracuseStep 5515399 = 8273099) B8273099
theorem B10201625 : Blo 742328 10201625 := bstep (se 2 (by rfl) ⟨3825609, by rfl⟩ : syracuseStep 10201625 = 7651219) B7651219
theorem B10169003 : Blo 742328 10169003 := bstep (se 1 (by rfl) ⟨7626752, by rfl⟩ : syracuseStep 10169003 = 15253505) B15253505
theorem B6367997 : Blo 742328 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B1256249 : Blo 742328 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B2829113 : Blo 742328 2829113 := bstep (se 2 (by rfl) ⟨1060917, by rfl⟩ : syracuseStep 2829113 = 2121835) B2121835
theorem B2829127 : Blo 742328 2829127 := bstep (se 1 (by rfl) ⟨2121845, by rfl⟩ : syracuseStep 2829127 = 4243691) B4243691
theorem B4533083 : Blo 742328 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B1256431 : Blo 742328 1256431 := bstep (se 1 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 1256431 = 1884647) B1884647
theorem B8498681 : Blo 742328 8498681 := bstep (se 2 (by rfl) ⟨3187005, by rfl⟩ : syracuseStep 8498681 = 6374011) B6374011
theorem B1060399 : Blo 742328 1060399 := bstep (se 1 (by rfl) ⟨795299, by rfl⟩ : syracuseStep 1060399 = 1590599) B1590599
theorem B1880111 : Blo 742328 1880111 := bstep (se 1 (by rfl) ⟨1410083, by rfl⟩ : syracuseStep 1880111 = 2820167) B2820167
theorem B1257727 : Blo 742328 1257727 := bstep (se 1 (by rfl) ⟨943295, by rfl⟩ : syracuseStep 1257727 = 1886591) B1886591
theorem B24785189 : Blo 742328 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B1061191 : Blo 742328 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B15249815 : Blo 742328 15249815 := bstep (se 1 (by rfl) ⟨11437361, by rfl⟩ : syracuseStep 15249815 = 22874723) B22874723
theorem B10728125 : Blo 742328 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B5649263 : Blo 742328 5649263 := bstep (se 1 (by rfl) ⟨4236947, by rfl⟩ : syracuseStep 5649263 = 8473895) B8473895
theorem B40678595 : Blo 742328 40678595 := bstep (se 1 (by rfl) ⟨30508946, by rfl⟩ : syracuseStep 40678595 = 61017893) B61017893
theorem B10728875 : Blo 742328 10728875 := bstep (se 1 (by rfl) ⟨8046656, by rfl⟩ : syracuseStep 10728875 = 16093313) B16093313
theorem B6370973 : Blo 742328 6370973 := bstep (se 3 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 6370973 = 2389115) B2389115
theorem B5355355 : Blo 742328 5355355 := bstep (se 1 (by rfl) ⟨4016516, by rfl⟩ : syracuseStep 5355355 = 8033033) B8033033
theorem B1128953 : Blo 742328 1128953 := bstep (se 2 (by rfl) ⟨423357, by rfl⟩ : syracuseStep 1128953 = 846715) B846715
theorem B2833001 : Blo 742328 2833001 := bstep (se 2 (by rfl) ⟨1062375, by rfl⟩ : syracuseStep 2833001 = 2124751) B2124751
theorem B5651207 : Blo 742328 5651207 := bstep (se 1 (by rfl) ⟨4238405, by rfl⟩ : syracuseStep 5651207 = 8476811) B8476811
theorem B10861523 : Blo 742328 10861523 := bstep (se 1 (by rfl) ⟨8146142, by rfl⟩ : syracuseStep 10861523 = 16292285) B16292285
theorem B1588207 : Blo 742328 1588207 := bstep (se 1 (by rfl) ⟨1191155, by rfl⟩ : syracuseStep 1588207 = 2382311) B2382311
theorem B15449287 : Blo 742328 15449287 := bstep (se 1 (by rfl) ⟨11586965, by rfl⟩ : syracuseStep 15449287 = 23173931) B23173931
theorem B34356575 : Blo 742328 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B4013641 : Blo 742328 4013641 := bstep (se 2 (by rfl) ⟨1505115, by rfl⟩ : syracuseStep 4013641 = 3010231) B3010231
theorem B5652179 : Blo 742328 5652179 := bstep (se 1 (by rfl) ⟨4239134, by rfl⟩ : syracuseStep 5652179 = 8478269) B8478269
theorem B2506895 : Blo 742328 2506895 := bstep (se 1 (by rfl) ⟨1880171, by rfl⟩ : syracuseStep 2506895 = 3760343) B3760343
theorem B2507003 : Blo 742328 2507003 := bstep (se 1 (by rfl) ⟨1880252, by rfl⟩ : syracuseStep 2507003 = 3760505) B3760505
theorem B12861821 : Blo 742328 12861821 := bstep (se 3 (by rfl) ⟨2411591, by rfl⟩ : syracuseStep 12861821 = 4823183) B4823183
theorem B1721417 : Blo 742328 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B1591103 : Blo 742328 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B837535 : Blo 742328 837535 := bstep (se 1 (by rfl) ⟨628151, by rfl⟩ : syracuseStep 837535 = 1256303) B1256303
theorem B2509865 : Blo 742328 2509865 := bstep (se 2 (by rfl) ⟨941199, by rfl⟩ : syracuseStep 2509865 = 1882399) B1882399
theorem B21482765 : Blo 742328 21482765 := bstep (se 3 (by rfl) ⟨4028018, by rfl⟩ : syracuseStep 21482765 = 8056037) B8056037
theorem B1887887 : Blo 742328 1887887 := bstep (se 1 (by rfl) ⟨1415915, by rfl⟩ : syracuseStep 1887887 = 2831831) B2831831
theorem B2117279 : Blo 742328 2117279 := bstep (se 1 (by rfl) ⟨1587959, by rfl⟩ : syracuseStep 2117279 = 3175919) B3175919
theorem B2510567 : Blo 742328 2510567 := bstep (se 1 (by rfl) ⟨1882925, by rfl⟩ : syracuseStep 2510567 = 3765851) B3765851
theorem B5656553 : Blo 742328 5656553 := bstep (se 2 (by rfl) ⟨2121207, by rfl⟩ : syracuseStep 5656553 = 4242415) B4242415
theorem B2117735 : Blo 742328 2117735 := bstep (se 1 (by rfl) ⟨1588301, by rfl⟩ : syracuseStep 2117735 = 3176603) B3176603
theorem B12702095 : Blo 742328 12702095 := bstep (se 1 (by rfl) ⟨9526571, by rfl⟩ : syracuseStep 12702095 = 19053143) B19053143
theorem B2511485 : Blo 742328 2511485 := bstep (se 3 (by rfl) ⟨470903, by rfl⟩ : syracuseStep 2511485 = 941807) B941807
theorem B2511593 : Blo 742328 2511593 := bstep (se 2 (by rfl) ⟨941847, by rfl⟩ : syracuseStep 2511593 = 1883695) B1883695
theorem B19026899 : Blo 742328 19026899 := bstep (se 1 (by rfl) ⟨14270174, by rfl⟩ : syracuseStep 19026899 = 28540349) B28540349
theorem B742491 : Blo 742328 742491 := bstep (se 1 (by rfl) ⟨556868, by rfl⟩ : syracuseStep 742491 = 1113737) B1113737
theorem B742511 : Blo 742328 742511 := bstep (se 1 (by rfl) ⟨556883, by rfl⟩ : syracuseStep 742511 = 1113767) B1113767
theorem B742591 : Blo 742328 742591 := bstep (se 1 (by rfl) ⟨556943, by rfl⟩ : syracuseStep 742591 = 1113887) B1113887
theorem B742631 : Blo 742328 742631 := bstep (se 1 (by rfl) ⟨556973, by rfl⟩ : syracuseStep 742631 = 1113947) B1113947
theorem B6051179 : Blo 742328 6051179 := bstep (se 1 (by rfl) ⟨4538384, by rfl⟩ : syracuseStep 6051179 = 9076769) B9076769
theorem B742911 : Blo 742328 742911 := bstep (se 1 (by rfl) ⟨557183, by rfl⟩ : syracuseStep 742911 = 1114367) B1114367
theorem B2512403 : Blo 742328 2512403 := bstep (se 1 (by rfl) ⟨1884302, by rfl⟩ : syracuseStep 2512403 = 3768605) B3768605
theorem B743015 : Blo 742328 743015 := bstep (se 1 (by rfl) ⟨557261, by rfl⟩ : syracuseStep 743015 = 1114523) B1114523
theorem B743295 : Blo 742328 743295 := bstep (se 1 (by rfl) ⟨557471, by rfl⟩ : syracuseStep 743295 = 1114943) B1114943
theorem B743391 : Blo 742328 743391 := bstep (se 1 (by rfl) ⟨557543, by rfl⟩ : syracuseStep 743391 = 1115087) B1115087
theorem B743451 : Blo 742328 743451 := bstep (se 1 (by rfl) ⟨557588, by rfl⟩ : syracuseStep 743451 = 1115177) B1115177
theorem B743471 : Blo 742328 743471 := bstep (se 1 (by rfl) ⟨557603, by rfl⟩ : syracuseStep 743471 = 1115207) B1115207
theorem B2512943 : Blo 742328 2512943 := bstep (se 1 (by rfl) ⟨1884707, by rfl⟩ : syracuseStep 2512943 = 3769415) B3769415
theorem B743591 : Blo 742328 743591 := bstep (se 1 (by rfl) ⟨557693, by rfl⟩ : syracuseStep 743591 = 1115387) B1115387
theorem B743783 : Blo 742328 743783 := bstep (se 1 (by rfl) ⟨557837, by rfl⟩ : syracuseStep 743783 = 1115675) B1115675
theorem B744039 : Blo 742328 744039 := bstep (se 1 (by rfl) ⟨558029, by rfl⟩ : syracuseStep 744039 = 1116059) B1116059
theorem B744063 : Blo 742328 744063 := bstep (se 1 (by rfl) ⟨558047, by rfl⟩ : syracuseStep 744063 = 1116095) B1116095
theorem B744479 : Blo 742328 744479 := bstep (se 1 (by rfl) ⟨558359, by rfl⟩ : syracuseStep 744479 = 1116719) B1116719
theorem B3759209 : Blo 742328 3759209 := bstep (se 2 (by rfl) ⟨1409703, by rfl⟩ : syracuseStep 3759209 = 2819407) B2819407
theorem B744559 : Blo 742328 744559 := bstep (se 1 (by rfl) ⟨558419, by rfl⟩ : syracuseStep 744559 = 1116839) B1116839
theorem B744603 : Blo 742328 744603 := bstep (se 1 (by rfl) ⟨558452, by rfl⟩ : syracuseStep 744603 = 1116905) B1116905
theorem B744607 : Blo 742328 744607 := bstep (se 1 (by rfl) ⟨558455, by rfl⟩ : syracuseStep 744607 = 1116911) B1116911
theorem B744639 : Blo 742328 744639 := bstep (se 1 (by rfl) ⟨558479, by rfl⟩ : syracuseStep 744639 = 1116959) B1116959
theorem B744859 : Blo 742328 744859 := bstep (se 1 (by rfl) ⟨558644, by rfl⟩ : syracuseStep 744859 = 1117289) B1117289
theorem B2514401 : Blo 742328 2514401 := bstep (se 2 (by rfl) ⟨942900, by rfl⟩ : syracuseStep 2514401 = 1885801) B1885801
theorem B744943 : Blo 742328 744943 := bstep (se 1 (by rfl) ⟨558707, by rfl⟩ : syracuseStep 744943 = 1117415) B1117415
theorem B745279 : Blo 742328 745279 := bstep (se 1 (by rfl) ⟨558959, by rfl⟩ : syracuseStep 745279 = 1117919) B1117919
theorem B745467 : Blo 742328 745467 := bstep (se 1 (by rfl) ⟨559100, by rfl⟩ : syracuseStep 745467 = 1118201) B1118201
theorem B4022399 : Blo 742328 4022399 := bstep (se 1 (by rfl) ⟨3016799, by rfl⟩ : syracuseStep 4022399 = 6033599) B6033599
theorem B745599 : Blo 742328 745599 := bstep (se 1 (by rfl) ⟨559199, by rfl⟩ : syracuseStep 745599 = 1118399) B1118399
theorem B745627 : Blo 742328 745627 := bstep (se 1 (by rfl) ⟨559220, by rfl⟩ : syracuseStep 745627 = 1118441) B1118441
theorem B745711 : Blo 742328 745711 := bstep (se 1 (by rfl) ⟨559283, by rfl⟩ : syracuseStep 745711 = 1118567) B1118567
theorem B746267 : Blo 742328 746267 := bstep (se 1 (by rfl) ⟨559700, by rfl⟩ : syracuseStep 746267 = 1119401) B1119401
theorem B746311 : Blo 742328 746311 := bstep (se 1 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 746311 = 1119467) B1119467
theorem B3171287 : Blo 742328 3171287 := bstep (se 1 (by rfl) ⟨2378465, by rfl⟩ : syracuseStep 3171287 = 4756931) B4756931
theorem B943103 : Blo 742328 943103 := bstep (se 1 (by rfl) ⟨707327, by rfl⟩ : syracuseStep 943103 = 1414655) B1414655
theorem B2515967 : Blo 742328 2515967 := bstep (se 1 (by rfl) ⟨1886975, by rfl⟩ : syracuseStep 2515967 = 3773951) B3773951
theorem B4777127 : Blo 742328 4777127 := bstep (se 1 (by rfl) ⟨3582845, by rfl⟩ : syracuseStep 4777127 = 7165691) B7165691
theorem B2516723 : Blo 742328 2516723 := bstep (se 1 (by rfl) ⟨1887542, by rfl⟩ : syracuseStep 2516723 = 3775085) B3775085
theorem B2123567 : Blo 742328 2123567 := bstep (se 1 (by rfl) ⟨1592675, by rfl⟩ : syracuseStep 2123567 = 3185351) B3185351
theorem B4024475 : Blo 742328 4024475 := bstep (se 1 (by rfl) ⟨3018356, by rfl⟩ : syracuseStep 4024475 = 6036713) B6036713
theorem B2517371 : Blo 742328 2517371 := bstep (se 1 (by rfl) ⟨1888028, by rfl⟩ : syracuseStep 2517371 = 3776057) B3776057
theorem B2517479 : Blo 742328 2517479 := bstep (se 1 (by rfl) ⟨1888109, by rfl⟩ : syracuseStep 2517479 = 3776219) B3776219
theorem B1338695 : Blo 742328 1338695 := bstep (se 1 (by rfl) ⟨1004021, by rfl⟩ : syracuseStep 1338695 = 2008043) B2008043
theorem B2125217 : Blo 742328 2125217 := bstep (se 2 (by rfl) ⟨796956, by rfl⟩ : syracuseStep 2125217 = 1593913) B1593913
theorem B2518505 : Blo 742328 2518505 := bstep (se 2 (by rfl) ⟨944439, by rfl⟩ : syracuseStep 2518505 = 1888879) B1888879
theorem B4025857 : Blo 742328 4025857 := bstep (se 2 (by rfl) ⟨1509696, by rfl⟩ : syracuseStep 4025857 = 3019393) B3019393
theorem B2518559 : Blo 742328 2518559 := bstep (se 1 (by rfl) ⟨1888919, by rfl⟩ : syracuseStep 2518559 = 3777839) B3777839
theorem B5730281 : Blo 742328 5730281 := bstep (se 2 (by rfl) ⟨2148855, by rfl⟩ : syracuseStep 5730281 = 4297711) B4297711
theorem B8155187 : Blo 742328 8155187 := bstep (se 1 (by rfl) ⟨6116390, by rfl⟩ : syracuseStep 8155187 = 12232781) B12232781
theorem B6451913 : Blo 742328 6451913 := bstep (se 2 (by rfl) ⟨2419467, by rfl⟩ : syracuseStep 6451913 = 4838935) B4838935
theorem B8582867 : Blo 742328 8582867 := bstep (se 1 (by rfl) ⟨6437150, by rfl⟩ : syracuseStep 8582867 = 12874301) B12874301
theorem B39188443 : Blo 742328 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B2685001 : Blo 742328 2685001 := bstep (se 2 (by rfl) ⟨1006875, by rfl⟩ : syracuseStep 2685001 = 2013751) B2013751
theorem B2390141 : Blo 742328 2390141 := bstep (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) B896303
theorem B3176927 : Blo 742328 3176927 := bstep (se 1 (by rfl) ⟨2382695, by rfl⟩ : syracuseStep 3176927 = 4765391) B4765391
theorem B49053113 : Blo 742328 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B1113671 : Blo 742328 1113671 := bstep (se 1 (by rfl) ⟨835253, by rfl⟩ : syracuseStep 1113671 = 1670507) B1670507
theorem B1113851 : Blo 742328 1113851 := bstep (se 1 (by rfl) ⟨835388, by rfl⟩ : syracuseStep 1113851 = 1670777) B1670777
theorem B1113983 : Blo 742328 1113983 := bstep (se 1 (by rfl) ⟨835487, by rfl⟩ : syracuseStep 1113983 = 1670975) B1670975
theorem B1114091 : Blo 742328 1114091 := bstep (se 1 (by rfl) ⟨835568, by rfl⟩ : syracuseStep 1114091 = 1671137) B1671137
theorem B1671263 : Blo 742328 1671263 := bstep (se 1 (by rfl) ⟨1253447, by rfl⟩ : syracuseStep 1671263 = 2506895) B2506895
theorem B1671335 : Blo 742328 1671335 := bstep (se 1 (by rfl) ⟨1253501, by rfl⟩ : syracuseStep 1671335 = 2507003) B2507003
theorem B1672361 : Blo 742328 1672361 := bstep (se 2 (by rfl) ⟨627135, by rfl⟩ : syracuseStep 1672361 = 1254271) B1254271
theorem B1115879 : Blo 742328 1115879 := bstep (se 1 (by rfl) ⟨836909, by rfl⟩ : syracuseStep 1115879 = 1673819) B1673819
theorem B1672937 : Blo 742328 1672937 := bstep (se 2 (by rfl) ⟨627351, by rfl⟩ : syracuseStep 1672937 = 1254703) B1254703
theorem B5375767 : Blo 742328 5375767 := bstep (se 1 (by rfl) ⟨4031825, by rfl⟩ : syracuseStep 5375767 = 8063651) B8063651
theorem B1673243 : Blo 742328 1673243 := bstep (se 1 (by rfl) ⟨1254932, by rfl⟩ : syracuseStep 1673243 = 2509865) B2509865
theorem B24119329 : Blo 742328 24119329 := bstep (se 2 (by rfl) ⟨9044748, by rfl⟩ : syracuseStep 24119329 = 18089497) B18089497
theorem B14321843 : Blo 742328 14321843 := bstep (se 1 (by rfl) ⟨10741382, by rfl⟩ : syracuseStep 14321843 = 21482765) B21482765
theorem B1411519 : Blo 742328 1411519 := bstep (se 1 (by rfl) ⟨1058639, by rfl⟩ : syracuseStep 1411519 = 2117279) B2117279
theorem B1673711 : Blo 742328 1673711 := bstep (se 1 (by rfl) ⟨1255283, by rfl⟩ : syracuseStep 1673711 = 2510567) B2510567
theorem B3770873 : Blo 742328 3770873 := bstep (se 2 (by rfl) ⟨1414077, by rfl⟩ : syracuseStep 3770873 = 2828155) B2828155
theorem B1116713 : Blo 742328 1116713 := bstep (se 2 (by rfl) ⟨418767, by rfl⟩ : syracuseStep 1116713 = 837535) B837535
theorem B3771035 : Blo 742328 3771035 := bstep (se 1 (by rfl) ⟨2828276, by rfl⟩ : syracuseStep 3771035 = 5656553) B5656553
theorem B1411823 : Blo 742328 1411823 := bstep (se 1 (by rfl) ⟨1058867, by rfl⟩ : syracuseStep 1411823 = 2117735) B2117735
theorem B4590445 : Blo 742328 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B1117151 : Blo 742328 1117151 := bstep (se 1 (by rfl) ⟨837863, by rfl⟩ : syracuseStep 1117151 = 1675727) B1675727
theorem B1117211 : Blo 742328 1117211 := bstep (se 1 (by rfl) ⟨837908, by rfl⟩ : syracuseStep 1117211 = 1675817) B1675817
theorem B1674323 : Blo 742328 1674323 := bstep (se 1 (by rfl) ⟨1255742, by rfl⟩ : syracuseStep 1674323 = 2511485) B2511485
theorem B1674395 : Blo 742328 1674395 := bstep (se 1 (by rfl) ⟨1255796, by rfl⟩ : syracuseStep 1674395 = 2511593) B2511593
theorem B1117391 : Blo 742328 1117391 := bstep (se 1 (by rfl) ⟨838043, by rfl⟩ : syracuseStep 1117391 = 1676087) B1676087
theorem B2821351 : Blo 742328 2821351 := bstep (se 1 (by rfl) ⟨2116013, by rfl⟩ : syracuseStep 2821351 = 4232027) B4232027
theorem B12684599 : Blo 742328 12684599 := bstep (se 1 (by rfl) ⟨9513449, by rfl⟩ : syracuseStep 12684599 = 19026899) B19026899
theorem B4033901 : Blo 742328 4033901 := bstep (se 3 (by rfl) ⟨756356, by rfl⟩ : syracuseStep 4033901 = 1512713) B1512713
theorem B4034119 : Blo 742328 4034119 := bstep (se 1 (by rfl) ⟨3025589, by rfl⟩ : syracuseStep 4034119 = 6051179) B6051179
theorem B1674935 : Blo 742328 1674935 := bstep (se 1 (by rfl) ⟨1256201, by rfl⟩ : syracuseStep 1674935 = 2512403) B2512403
theorem B3772169 : Blo 742328 3772169 := bstep (se 2 (by rfl) ⟨1414563, by rfl⟩ : syracuseStep 3772169 = 2829127) B2829127
theorem B1118063 : Blo 742328 1118063 := bstep (se 1 (by rfl) ⟨838547, by rfl⟩ : syracuseStep 1118063 = 1677095) B1677095
theorem B1675241 : Blo 742328 1675241 := bstep (se 2 (by rfl) ⟨628215, by rfl⟩ : syracuseStep 1675241 = 1256431) B1256431
theorem B1675295 : Blo 742328 1675295 := bstep (se 1 (by rfl) ⟨1256471, by rfl⟩ : syracuseStep 1675295 = 2512943) B2512943
theorem B1118279 : Blo 742328 1118279 := bstep (se 1 (by rfl) ⟨838709, by rfl⟩ : syracuseStep 1118279 = 1677419) B1677419
theorem B1118927 : Blo 742328 1118927 := bstep (se 1 (by rfl) ⟨839195, by rfl⟩ : syracuseStep 1118927 = 1678391) B1678391
theorem B1118951 : Blo 742328 1118951 := bstep (se 1 (by rfl) ⟨839213, by rfl⟩ : syracuseStep 1118951 = 1678427) B1678427
theorem B1413865 : Blo 742328 1413865 := bstep (se 2 (by rfl) ⟨530199, by rfl⟩ : syracuseStep 1413865 = 1060399) B1060399
theorem B1676267 : Blo 742328 1676267 := bstep (se 1 (by rfl) ⟨1257200, by rfl⟩ : syracuseStep 1676267 = 2514401) B2514401
theorem B1676969 : Blo 742328 1676969 := bstep (se 2 (by rfl) ⟨628863, by rfl⟩ : syracuseStep 1676969 = 1257727) B1257727
theorem B1414921 : Blo 742328 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B1677311 : Blo 742328 1677311 := bstep (se 1 (by rfl) ⟨1257983, by rfl⟩ : syracuseStep 1677311 = 2515967) B2515967
theorem B3184751 : Blo 742328 3184751 := bstep (se 1 (by rfl) ⟨2388563, by rfl⟩ : syracuseStep 3184751 = 4777127) B4777127
theorem B1677815 : Blo 742328 1677815 := bstep (se 1 (by rfl) ⟨1258361, by rfl⟩ : syracuseStep 1677815 = 2516723) B2516723
theorem B1415711 : Blo 742328 1415711 := bstep (se 1 (by rfl) ⟨1061783, by rfl⟩ : syracuseStep 1415711 = 2123567) B2123567
theorem B1678247 : Blo 742328 1678247 := bstep (se 1 (by rfl) ⟨1258685, by rfl⟩ : syracuseStep 1678247 = 2517371) B2517371
theorem B1678319 : Blo 742328 1678319 := bstep (se 1 (by rfl) ⟨1258739, by rfl⟩ : syracuseStep 1678319 = 2517479) B2517479
theorem B3022055 : Blo 742328 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B892463 : Blo 742328 892463 := bstep (se 1 (by rfl) ⟨669347, by rfl⟩ : syracuseStep 892463 = 1338695) B1338695
theorem B1679003 : Blo 742328 1679003 := bstep (se 1 (by rfl) ⟨1259252, by rfl⟩ : syracuseStep 1679003 = 2518505) B2518505
theorem B1679039 : Blo 742328 1679039 := bstep (se 1 (by rfl) ⟨1259279, by rfl⟩ : syracuseStep 1679039 = 2518559) B2518559
theorem B1253407 : Blo 742328 1253407 := bstep (se 1 (by rfl) ⟨940055, by rfl⟩ : syracuseStep 1253407 = 1880111) B1880111
theorem B3580001 : Blo 742328 3580001 := bstep (se 2 (by rfl) ⟨1342500, by rfl⟩ : syracuseStep 3580001 = 2685001) B2685001
theorem B16523459 : Blo 742328 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B10166543 : Blo 742328 10166543 := bstep (se 1 (by rfl) ⟨7624907, by rfl⟩ : syracuseStep 10166543 = 15249815) B15249815
theorem B7152083 : Blo 742328 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B4301275 : Blo 742328 4301275 := bstep (se 1 (by rfl) ⟨3225956, by rfl⟩ : syracuseStep 4301275 = 6451913) B6451913
theorem B7152583 : Blo 742328 7152583 := bstep (se 1 (by rfl) ⟨5364437, by rfl⟩ : syracuseStep 7152583 = 10728875) B10728875
theorem B5351521 : Blo 742328 5351521 := bstep (se 2 (by rfl) ⟨2006820, by rfl⟩ : syracuseStep 5351521 = 4013641) B4013641
theorem B6796115 : Blo 742328 6796115 := bstep (se 1 (by rfl) ⟨5097086, by rfl⟩ : syracuseStep 6796115 = 10194173) B10194173
theorem B1258591 : Blo 742328 1258591 := bstep (se 1 (by rfl) ⟨943943, by rfl⟩ : syracuseStep 1258591 = 1887887) B1887887
theorem B7353865 : Blo 742328 7353865 := bstep (se 2 (by rfl) ⟨2757699, by rfl⟩ : syracuseStep 7353865 = 5515399) B5515399
theorem B8468063 : Blo 742328 8468063 := bstep (se 1 (by rfl) ⟨6351047, by rfl⟩ : syracuseStep 8468063 = 12702095) B12702095
theorem B4765337 : Blo 742328 4765337 := bstep (se 2 (by rfl) ⟨1787001, by rfl⟩ : syracuseStep 4765337 = 3574003) B3574003
theorem B1883209 : Blo 742328 1883209 := bstep (se 2 (by rfl) ⟨706203, by rfl⟩ : syracuseStep 1883209 = 1412407) B1412407
theorem B2506139 : Blo 742328 2506139 := bstep (se 1 (by rfl) ⟨1879604, by rfl⟩ : syracuseStep 2506139 = 3759209) B3759209
theorem B4242941 : Blo 742328 4242941 := bstep (se 3 (by rfl) ⟨795551, by rfl⟩ : syracuseStep 4242941 = 1591103) B1591103
theorem B835519 : Blo 742328 835519 := bstep (se 1 (by rfl) ⟨626639, by rfl⟩ : syracuseStep 835519 = 1253279) B1253279
theorem B4243873 : Blo 742328 4243873 := bstep (se 2 (by rfl) ⟨1591452, by rfl⟩ : syracuseStep 4243873 = 3182905) B3182905
theorem B18137681 : Blo 742328 18137681 := bstep (se 2 (by rfl) ⟨6801630, by rfl⟩ : syracuseStep 18137681 = 13603261) B13603261
theorem B2114191 : Blo 742328 2114191 := bstep (se 1 (by rfl) ⟨1585643, by rfl⟩ : syracuseStep 2114191 = 3171287) B3171287
theorem B6341753 : Blo 742328 6341753 := bstep (se 2 (by rfl) ⟨2378157, by rfl⟩ : syracuseStep 6341753 = 4756315) B4756315
theorem B6801083 : Blo 742328 6801083 := bstep (se 1 (by rfl) ⟨5100812, by rfl⟩ : syracuseStep 6801083 = 10201625) B10201625
theorem B4245331 : Blo 742328 4245331 := bstep (se 1 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 4245331 = 6367997) B6367997
theorem B837499 : Blo 742328 837499 := bstep (se 1 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 837499 = 1256249) B1256249
theorem B1886075 : Blo 742328 1886075 := bstep (se 1 (by rfl) ⟨1414556, by rfl⟩ : syracuseStep 1886075 = 2829113) B2829113
theorem B8046701 : Blo 742328 8046701 := bstep (se 3 (by rfl) ⟨1508756, by rfl⟩ : syracuseStep 8046701 = 3017513) B3017513
theorem B4245857 : Blo 742328 4245857 := bstep (se 2 (by rfl) ⟨1592196, by rfl⟩ : syracuseStep 4245857 = 3184393) B3184393
theorem B52251257 : Blo 742328 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B3820187 : Blo 742328 3820187 := bstep (se 1 (by rfl) ⟨2865140, by rfl⟩ : syracuseStep 3820187 = 5730281) B5730281
theorem B1887401 : Blo 742328 1887401 := bstep (se 2 (by rfl) ⟨707775, by rfl⟩ : syracuseStep 1887401 = 1415551) B1415551
theorem B27119063 : Blo 742328 27119063 := bstep (se 1 (by rfl) ⟨20339297, by rfl⟩ : syracuseStep 27119063 = 40678595) B40678595
theorem B4247315 : Blo 742328 4247315 := bstep (se 1 (by rfl) ⟨3185486, by rfl⟩ : syracuseStep 4247315 = 6370973) B6370973
theorem B5721911 : Blo 742328 5721911 := bstep (se 1 (by rfl) ⟨4291433, by rfl⟩ : syracuseStep 5721911 = 8582867) B8582867
theorem B2117609 : Blo 742328 2117609 := bstep (se 2 (by rfl) ⟨794103, by rfl⟩ : syracuseStep 2117609 = 1588207) B1588207
theorem B1593427 : Blo 742328 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B1888393 : Blo 742328 1888393 := bstep (se 2 (by rfl) ⟨708147, by rfl⟩ : syracuseStep 1888393 = 1416295) B1416295
theorem B20599049 : Blo 742328 20599049 := bstep (se 2 (by rfl) ⟨7724643, by rfl⟩ : syracuseStep 20599049 = 15449287) B15449287
theorem B2117951 : Blo 742328 2117951 := bstep (se 1 (by rfl) ⟨1588463, by rfl⟩ : syracuseStep 2117951 = 3176927) B3176927
theorem B1888667 : Blo 742328 1888667 := bstep (se 1 (by rfl) ⟨1416500, by rfl⟩ : syracuseStep 1888667 = 2833001) B2833001
theorem B742447 : Blo 742328 742447 := bstep (se 1 (by rfl) ⟨556835, by rfl⟩ : syracuseStep 742447 = 1113671) B1113671
theorem B742567 : Blo 742328 742567 := bstep (se 1 (by rfl) ⟨556925, by rfl⟩ : syracuseStep 742567 = 1113851) B1113851
theorem B742655 : Blo 742328 742655 := bstep (se 1 (by rfl) ⟨556991, by rfl⟩ : syracuseStep 742655 = 1113983) B1113983
theorem B742727 : Blo 742328 742727 := bstep (se 1 (by rfl) ⟨557045, by rfl⟩ : syracuseStep 742727 = 1114091) B1114091
theorem B2512295 : Blo 742328 2512295 := bstep (se 1 (by rfl) ⟨1884221, by rfl⟩ : syracuseStep 2512295 = 3768443) B3768443
theorem B742863 : Blo 742328 742863 := bstep (se 1 (by rfl) ⟨557147, by rfl⟩ : syracuseStep 742863 = 1114295) B1114295
theorem B8574547 : Blo 742328 8574547 := bstep (se 1 (by rfl) ⟨6430910, by rfl⟩ : syracuseStep 8574547 = 12861821) B12861821
theorem B743143 : Blo 742328 743143 := bstep (se 1 (by rfl) ⟨557357, by rfl⟩ : syracuseStep 743143 = 1114715) B1114715
theorem B743335 : Blo 742328 743335 := bstep (se 1 (by rfl) ⟨557501, by rfl⟩ : syracuseStep 743335 = 1115003) B1115003
theorem B743419 : Blo 742328 743419 := bstep (se 1 (by rfl) ⟨557564, by rfl⟩ : syracuseStep 743419 = 1115129) B1115129
theorem B743455 : Blo 742328 743455 := bstep (se 1 (by rfl) ⟨557591, by rfl⟩ : syracuseStep 743455 = 1115183) B1115183
theorem B743535 : Blo 742328 743535 := bstep (se 1 (by rfl) ⟨557651, by rfl⟩ : syracuseStep 743535 = 1115303) B1115303
theorem B5658983 : Blo 742328 5658983 := bstep (se 1 (by rfl) ⟨4244237, by rfl⟩ : syracuseStep 5658983 = 8488475) B8488475
theorem B744187 : Blo 742328 744187 := bstep (se 1 (by rfl) ⟨558140, by rfl⟩ : syracuseStep 744187 = 1116281) B1116281
theorem B745211 : Blo 742328 745211 := bstep (se 1 (by rfl) ⟨558908, by rfl⟩ : syracuseStep 745211 = 1117817) B1117817
theorem B745243 : Blo 742328 745243 := bstep (se 1 (by rfl) ⟨558932, by rfl⟩ : syracuseStep 745243 = 1117865) B1117865
theorem B2514941 : Blo 742328 2514941 := bstep (se 3 (by rfl) ⟨471551, by rfl⟩ : syracuseStep 2514941 = 943103) B943103
theorem B745631 : Blo 742328 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B745799 : Blo 742328 745799 := bstep (se 1 (by rfl) ⟨559349, by rfl⟩ : syracuseStep 745799 = 1118699) B1118699
theorem B745883 : Blo 742328 745883 := bstep (se 1 (by rfl) ⟨559412, by rfl⟩ : syracuseStep 745883 = 1118825) B1118825
theorem B3760667 : Blo 742328 3760667 := bstep (se 1 (by rfl) ⟨2820500, by rfl⟩ : syracuseStep 3760667 = 5641001) B5641001
theorem B3761639 : Blo 742328 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B5367809 : Blo 742328 5367809 := bstep (se 2 (by rfl) ⟨2012928, by rfl⟩ : syracuseStep 5367809 = 4025857) B4025857
theorem B68905241 : Blo 742328 68905241 := bstep (se 2 (by rfl) ⟨25839465, by rfl⟩ : syracuseStep 68905241 = 51678931) B51678931
theorem B2681599 : Blo 742328 2681599 := bstep (se 1 (by rfl) ⟨2011199, by rfl⟩ : syracuseStep 2681599 = 4022399) B4022399
theorem B3763907 : Blo 742328 3763907 := bstep (se 1 (by rfl) ⟨2822930, by rfl⟩ : syracuseStep 3763907 = 5645861) B5645861
theorem B2682983 : Blo 742328 2682983 := bstep (se 1 (by rfl) ⟨2012237, by rfl⟩ : syracuseStep 2682983 = 4024475) B4024475
theorem B6779335 : Blo 742328 6779335 := bstep (se 1 (by rfl) ⟨5084501, by rfl⟩ : syracuseStep 6779335 = 10169003) B10169003
theorem B5665787 : Blo 742328 5665787 := bstep (se 1 (by rfl) ⟨4249340, by rfl⟩ : syracuseStep 5665787 = 8498681) B8498681
theorem B7140473 : Blo 742328 7140473 := bstep (se 2 (by rfl) ⟨2677677, by rfl⟩ : syracuseStep 7140473 = 5355355) B5355355
theorem B6780025 : Blo 742328 6780025 := bstep (se 2 (by rfl) ⟨2542509, by rfl⟩ : syracuseStep 6780025 = 5085019) B5085019
theorem B5436791 : Blo 742328 5436791 := bstep (se 1 (by rfl) ⟨4077593, by rfl⟩ : syracuseStep 5436791 = 8155187) B8155187
theorem B3766175 : Blo 742328 3766175 := bstep (se 1 (by rfl) ⟨2824631, by rfl⟩ : syracuseStep 3766175 = 5649263) B5649263
theorem B5667245 : Blo 742328 5667245 := bstep (se 3 (by rfl) ⟨1062608, by rfl⟩ : syracuseStep 5667245 = 2125217) B2125217
theorem B752635 : Blo 742328 752635 := bstep (se 1 (by rfl) ⟨564476, by rfl⟩ : syracuseStep 752635 = 1128953) B1128953
theorem B2587745 : Blo 742328 2587745 := bstep (se 2 (by rfl) ⟨970404, by rfl⟩ : syracuseStep 2587745 = 1940809) B1940809
theorem B3767471 : Blo 742328 3767471 := bstep (se 1 (by rfl) ⟨2825603, by rfl⟩ : syracuseStep 3767471 = 5651207) B5651207
theorem B7241015 : Blo 742328 7241015 := bstep (se 1 (by rfl) ⟨5430761, by rfl⟩ : syracuseStep 7241015 = 10861523) B10861523
theorem B22904383 : Blo 742328 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B32702075 : Blo 742328 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B3768119 : Blo 742328 3768119 := bstep (se 1 (by rfl) ⟨2826089, by rfl⟩ : syracuseStep 3768119 = 5652179) B5652179
theorem B1671209 : Blo 742328 1671209 := bstep (se 2 (by rfl) ⟨626703, by rfl⟩ : syracuseStep 1671209 = 1253407) B1253407
theorem B1114175 : Blo 742328 1114175 := bstep (se 1 (by rfl) ⟨835631, by rfl⟩ : syracuseStep 1114175 = 1671263) B1671263
theorem B1114223 : Blo 742328 1114223 := bstep (se 1 (by rfl) ⟨835667, by rfl⟩ : syracuseStep 1114223 = 1671335) B1671335
theorem B12091787 : Blo 742328 12091787 := bstep (se 1 (by rfl) ⟨9068840, by rfl⟩ : syracuseStep 12091787 = 18137681) B18137681
theorem B5735033 : Blo 742328 5735033 := bstep (se 2 (by rfl) ⟨2150637, by rfl⟩ : syracuseStep 5735033 = 4301275) B4301275
theorem B4227835 : Blo 742328 4227835 := bstep (se 1 (by rfl) ⟨3170876, by rfl⟩ : syracuseStep 4227835 = 6341753) B6341753
theorem B1114907 : Blo 742328 1114907 := bstep (se 1 (by rfl) ⟨836180, by rfl⟩ : syracuseStep 1114907 = 1672361) B1672361
theorem B2818921 : Blo 742328 2818921 := bstep (se 2 (by rfl) ⟨1057095, by rfl⟩ : syracuseStep 2818921 = 2114191) B2114191
theorem B1115291 : Blo 742328 1115291 := bstep (se 1 (by rfl) ⟨836468, by rfl⟩ : syracuseStep 1115291 = 1672937) B1672937
theorem B9536777 : Blo 742328 9536777 := bstep (se 2 (by rfl) ⟨3576291, by rfl⟩ : syracuseStep 9536777 = 7152583) B7152583
theorem B1115495 : Blo 742328 1115495 := bstep (se 1 (by rfl) ⟨836621, by rfl⟩ : syracuseStep 1115495 = 1673243) B1673243
theorem B1115807 : Blo 742328 1115807 := bstep (se 1 (by rfl) ⟨836855, by rfl⟩ : syracuseStep 1115807 = 1673711) B1673711
theorem B34834171 : Blo 742328 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B1116215 : Blo 742328 1116215 := bstep (se 1 (by rfl) ⟨837161, by rfl⟩ : syracuseStep 1116215 = 1674323) B1674323
theorem B1116263 : Blo 742328 1116263 := bstep (se 1 (by rfl) ⟨837197, by rfl⟩ : syracuseStep 1116263 = 1674395) B1674395
theorem B8456399 : Blo 742328 8456399 := bstep (se 1 (by rfl) ⟨6342299, by rfl⟩ : syracuseStep 8456399 = 12684599) B12684599
theorem B1116623 : Blo 742328 1116623 := bstep (se 1 (by rfl) ⟨837467, by rfl⟩ : syracuseStep 1116623 = 1674935) B1674935
theorem B1116665 : Blo 742328 1116665 := bstep (se 2 (by rfl) ⟨418749, by rfl⟩ : syracuseStep 1116665 = 837499) B837499
theorem B1411739 : Blo 742328 1411739 := bstep (se 1 (by rfl) ⟨1058804, by rfl⟩ : syracuseStep 1411739 = 2117609) B2117609
theorem B1116827 : Blo 742328 1116827 := bstep (se 1 (by rfl) ⟨837620, by rfl⟩ : syracuseStep 1116827 = 1675241) B1675241
theorem B1116863 : Blo 742328 1116863 := bstep (se 1 (by rfl) ⟨837647, by rfl⟩ : syracuseStep 1116863 = 1675295) B1675295
theorem B1411967 : Blo 742328 1411967 := bstep (se 1 (by rfl) ⟨1058975, by rfl⟩ : syracuseStep 1411967 = 2117951) B2117951
theorem B1117511 : Blo 742328 1117511 := bstep (se 1 (by rfl) ⟨838133, by rfl⟩ : syracuseStep 1117511 = 1676267) B1676267
theorem B1674863 : Blo 742328 1674863 := bstep (se 1 (by rfl) ⟨1256147, by rfl⟩ : syracuseStep 1674863 = 2512295) B2512295
theorem B3575465 : Blo 742328 3575465 := bstep (se 2 (by rfl) ⟨1340799, by rfl⟩ : syracuseStep 3575465 = 2681599) B2681599
theorem B1117979 : Blo 742328 1117979 := bstep (se 1 (by rfl) ⟨838484, by rfl⟩ : syracuseStep 1117979 = 1676969) B1676969
theorem B1118207 : Blo 742328 1118207 := bstep (se 1 (by rfl) ⟨838655, by rfl⟩ : syracuseStep 1118207 = 1677311) B1677311
theorem B3772655 : Blo 742328 3772655 := bstep (se 1 (by rfl) ⟨2829491, by rfl⟩ : syracuseStep 3772655 = 5658983) B5658983
theorem B1118543 : Blo 742328 1118543 := bstep (se 1 (by rfl) ⟨838907, by rfl⟩ : syracuseStep 1118543 = 1677815) B1677815
theorem B1118831 : Blo 742328 1118831 := bstep (se 1 (by rfl) ⟨839123, by rfl⟩ : syracuseStep 1118831 = 1678247) B1678247
theorem B1118879 : Blo 742328 1118879 := bstep (se 1 (by rfl) ⟨839159, by rfl⟩ : syracuseStep 1118879 = 1678319) B1678319
theorem B5378825 : Blo 742328 5378825 := bstep (se 2 (by rfl) ⟨2017059, by rfl⟩ : syracuseStep 5378825 = 4034119) B4034119
theorem B1119335 : Blo 742328 1119335 := bstep (se 1 (by rfl) ⟨839501, by rfl⟩ : syracuseStep 1119335 = 1679003) B1679003
theorem B1119359 : Blo 742328 1119359 := bstep (se 1 (by rfl) ⟨839519, by rfl⟩ : syracuseStep 1119359 = 1679039) B1679039
theorem B1676627 : Blo 742328 1676627 := bstep (se 1 (by rfl) ⟨1257470, by rfl⟩ : syracuseStep 1676627 = 2514941) B2514941
theorem B11015639 : Blo 742328 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B1678121 : Blo 742328 1678121 := bstep (se 2 (by rfl) ⟨629295, by rfl⟩ : syracuseStep 1678121 = 1258591) B1258591
theorem B9805153 : Blo 742328 9805153 := bstep (se 2 (by rfl) ⟨3676932, by rfl⟩ : syracuseStep 9805153 = 7353865) B7353865
theorem B4530743 : Blo 742328 4530743 := bstep (se 1 (by rfl) ⟨3398057, by rfl⟩ : syracuseStep 4530743 = 6796115) B6796115
theorem B3777191 : Blo 742328 3777191 := bstep (se 1 (by rfl) ⟨2832893, by rfl⟩ : syracuseStep 3777191 = 5665787) B5665787
theorem B4760315 : Blo 742328 4760315 := bstep (se 1 (by rfl) ⟨3570236, by rfl⟩ : syracuseStep 4760315 = 7140473) B7140473
theorem B19309373 : Blo 742328 19309373 := bstep (se 3 (by rfl) ⟨3620507, by rfl⟩ : syracuseStep 19309373 = 7241015) B7241015
theorem B10757069 : Blo 742328 10757069 := bstep (se 3 (by rfl) ⟨2016950, by rfl⟩ : syracuseStep 10757069 = 4033901) B4033901
theorem B5645375 : Blo 742328 5645375 := bstep (se 1 (by rfl) ⟨4234031, by rfl⟩ : syracuseStep 5645375 = 8468063) B8468063
theorem B3778163 : Blo 742328 3778163 := bstep (se 1 (by rfl) ⟨2833622, by rfl⟩ : syracuseStep 3778163 = 5667245) B5667245
theorem B2828627 : Blo 742328 2828627 := bstep (se 1 (by rfl) ⟨2121470, by rfl⟩ : syracuseStep 2828627 = 4242941) B4242941
theorem B21801383 : Blo 742328 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B54930797 : Blo 742328 54930797 := bstep (se 3 (by rfl) ⟨10299524, by rfl⟩ : syracuseStep 54930797 = 20599049) B20599049
theorem B4534055 : Blo 742328 4534055 := bstep (se 1 (by rfl) ⟨3400541, by rfl⟩ : syracuseStep 4534055 = 6801083) B6801083
theorem B1257383 : Blo 742328 1257383 := bstep (se 1 (by rfl) ⟨943037, by rfl⟩ : syracuseStep 1257383 = 1886075) B1886075
theorem B9547895 : Blo 742328 9547895 := bstep (se 1 (by rfl) ⟨7160921, by rfl⟩ : syracuseStep 9547895 = 14321843) B14321843
theorem B2830571 : Blo 742328 2830571 := bstep (se 1 (by rfl) ⟨2122928, by rfl⟩ : syracuseStep 2830571 = 4245857) B4245857
theorem B1258267 : Blo 742328 1258267 := bstep (se 1 (by rfl) ⟨943700, by rfl⟩ : syracuseStep 1258267 = 1887401) B1887401
theorem B2831543 : Blo 742328 2831543 := bstep (se 1 (by rfl) ⟨2123657, by rfl⟩ : syracuseStep 2831543 = 4247315) B4247315
theorem B3814607 : Blo 742328 3814607 := bstep (se 1 (by rfl) ⟨2860955, by rfl⟩ : syracuseStep 3814607 = 5721911) B5721911
theorem B32159105 : Blo 742328 32159105 := bstep (se 2 (by rfl) ⟨12059664, by rfl⟩ : syracuseStep 32159105 = 24119329) B24119329
theorem B1259111 : Blo 742328 1259111 := bstep (se 1 (by rfl) ⟨944333, by rfl⟩ : syracuseStep 1259111 = 1888667) B1888667
theorem B1882025 : Blo 742328 1882025 := bstep (se 2 (by rfl) ⟨705759, by rfl⟩ : syracuseStep 1882025 = 1411519) B1411519
theorem B2014703 : Blo 742328 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B4768055 : Blo 742328 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B2507111 : Blo 742328 2507111 := bstep (se 1 (by rfl) ⟨1880333, by rfl⟩ : syracuseStep 2507111 = 3760667) B3760667
theorem B1885153 : Blo 742328 1885153 := bstep (se 2 (by rfl) ⟨706932, by rfl⟩ : syracuseStep 1885153 = 1413865) B1413865
theorem B2507759 : Blo 742328 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B1886561 : Blo 742328 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B2509271 : Blo 742328 2509271 := bstep (se 1 (by rfl) ⟨1881953, by rfl⟩ : syracuseStep 2509271 = 3763907) B3763907
theorem B1788655 : Blo 742328 1788655 := bstep (se 1 (by rfl) ⟨1341491, by rfl⟩ : syracuseStep 1788655 = 2682983) B2682983
theorem B6900653 : Blo 742328 6900653 := bstep (se 3 (by rfl) ⟨1293872, by rfl⟩ : syracuseStep 6900653 = 2587745) B2587745
theorem B3624527 : Blo 742328 3624527 := bstep (se 1 (by rfl) ⟨2718395, by rfl⟩ : syracuseStep 3624527 = 5436791) B5436791
theorem B2510783 : Blo 742328 2510783 := bstep (se 1 (by rfl) ⟨1883087, by rfl⟩ : syracuseStep 2510783 = 3766175) B3766175
theorem B1003513 : Blo 742328 1003513 := bstep (se 2 (by rfl) ⟨376317, by rfl⟩ : syracuseStep 1003513 = 752635) B752635
theorem B2510945 : Blo 742328 2510945 := bstep (se 2 (by rfl) ⟨941604, by rfl⟩ : syracuseStep 2510945 = 1883209) B1883209
theorem B2379901 : Blo 742328 2379901 := bstep (se 3 (by rfl) ⟨446231, by rfl⟩ : syracuseStep 2379901 = 892463) B892463
theorem B2511647 : Blo 742328 2511647 := bstep (se 1 (by rfl) ⟨1883735, by rfl⟩ : syracuseStep 2511647 = 3767471) B3767471
theorem B2512079 : Blo 742328 2512079 := bstep (se 1 (by rfl) ⟨1884059, by rfl⟩ : syracuseStep 2512079 = 3768119) B3768119
theorem B5658497 : Blo 742328 5658497 := bstep (se 2 (by rfl) ⟨2121936, by rfl⟩ : syracuseStep 5658497 = 4243873) B4243873
theorem B743919 : Blo 742328 743919 := bstep (se 1 (by rfl) ⟨557939, by rfl⟩ : syracuseStep 743919 = 1115879) B1115879
theorem B5364467 : Blo 742328 5364467 := bstep (se 1 (by rfl) ⟨4023350, by rfl⟩ : syracuseStep 5364467 = 8046701) B8046701
theorem B2513915 : Blo 742328 2513915 := bstep (se 1 (by rfl) ⟨1885436, by rfl⟩ : syracuseStep 2513915 = 3770873) B3770873
theorem B744475 : Blo 742328 744475 := bstep (se 1 (by rfl) ⟨558356, by rfl⟩ : syracuseStep 744475 = 1116713) B1116713
theorem B2546791 : Blo 742328 2546791 := bstep (se 1 (by rfl) ⟨1910093, by rfl⟩ : syracuseStep 2546791 = 3820187) B3820187
theorem B2514023 : Blo 742328 2514023 := bstep (se 1 (by rfl) ⟨1885517, by rfl⟩ : syracuseStep 2514023 = 3771035) B3771035
theorem B941215 : Blo 742328 941215 := bstep (se 1 (by rfl) ⟨705911, by rfl⟩ : syracuseStep 941215 = 1411823) B1411823
theorem B744767 : Blo 742328 744767 := bstep (se 1 (by rfl) ⟨558575, by rfl⟩ : syracuseStep 744767 = 1117151) B1117151
theorem B744807 : Blo 742328 744807 := bstep (se 1 (by rfl) ⟨558605, by rfl⟩ : syracuseStep 744807 = 1117211) B1117211
theorem B744927 : Blo 742328 744927 := bstep (se 1 (by rfl) ⟨558695, by rfl⟩ : syracuseStep 744927 = 1117391) B1117391
theorem B18079375 : Blo 742328 18079375 := bstep (se 1 (by rfl) ⟨13559531, by rfl⟩ : syracuseStep 18079375 = 27119063) B27119063
theorem B7167689 : Blo 742328 7167689 := bstep (se 2 (by rfl) ⟨2687883, by rfl⟩ : syracuseStep 7167689 = 5375767) B5375767
theorem B5660441 : Blo 742328 5660441 := bstep (se 2 (by rfl) ⟨2122665, by rfl⟩ : syracuseStep 5660441 = 4245331) B4245331
theorem B2514779 : Blo 742328 2514779 := bstep (se 1 (by rfl) ⟨1886084, by rfl⟩ : syracuseStep 2514779 = 3772169) B3772169
theorem B745375 : Blo 742328 745375 := bstep (se 1 (by rfl) ⟨559031, by rfl⟩ : syracuseStep 745375 = 1118063) B1118063
theorem B745519 : Blo 742328 745519 := bstep (se 1 (by rfl) ⟨559139, by rfl⟩ : syracuseStep 745519 = 1118279) B1118279
theorem B7135361 : Blo 742328 7135361 := bstep (se 2 (by rfl) ⟨2675760, by rfl⟩ : syracuseStep 7135361 = 5351521) B5351521
theorem B745951 : Blo 742328 745951 := bstep (se 1 (by rfl) ⟨559463, by rfl⟩ : syracuseStep 745951 = 1118927) B1118927
theorem B745967 : Blo 742328 745967 := bstep (se 1 (by rfl) ⟨559475, by rfl⟩ : syracuseStep 745967 = 1118951) B1118951
theorem B6120593 : Blo 742328 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B2123167 : Blo 742328 2123167 := bstep (se 1 (by rfl) ⟨1592375, by rfl⟩ : syracuseStep 2123167 = 3184751) B3184751
theorem B3761801 : Blo 742328 3761801 := bstep (se 2 (by rfl) ⟨1410675, by rfl⟩ : syracuseStep 3761801 = 2821351) B2821351
theorem B943807 : Blo 742328 943807 := bstep (se 1 (by rfl) ⟨707855, by rfl⟩ : syracuseStep 943807 = 1415711) B1415711
theorem B14314157 : Blo 742328 14314157 := bstep (se 3 (by rfl) ⟨2683904, by rfl⟩ : syracuseStep 14314157 = 5367809) B5367809
theorem B2386667 : Blo 742328 2386667 := bstep (se 1 (by rfl) ⟨1790000, by rfl⟩ : syracuseStep 2386667 = 3580001) B3580001
theorem B2124569 : Blo 742328 2124569 := bstep (se 2 (by rfl) ⟨796713, by rfl⟩ : syracuseStep 2124569 = 1593427) B1593427
theorem B6777695 : Blo 742328 6777695 := bstep (se 1 (by rfl) ⟨5083271, by rfl⟩ : syracuseStep 6777695 = 10166543) B10166543
theorem B2517857 : Blo 742328 2517857 := bstep (se 2 (by rfl) ⟨944196, by rfl⟩ : syracuseStep 2517857 = 1888393) B1888393
theorem B9039113 : Blo 742328 9039113 := bstep (se 2 (by rfl) ⟨3389667, by rfl⟩ : syracuseStep 9039113 = 6779335) B6779335
theorem B9040033 : Blo 742328 9040033 := bstep (se 2 (by rfl) ⟨3390012, by rfl⟩ : syracuseStep 9040033 = 6780025) B6780025
theorem B45936827 : Blo 742328 45936827 := bstep (se 1 (by rfl) ⟨34452620, by rfl⟩ : syracuseStep 45936827 = 68905241) B68905241
theorem B11432729 : Blo 742328 11432729 := bstep (se 2 (by rfl) ⟨4287273, by rfl⟩ : syracuseStep 11432729 = 8574547) B8574547
theorem B3176891 : Blo 742328 3176891 := bstep (se 1 (by rfl) ⟨2382668, by rfl⟩ : syracuseStep 3176891 = 4765337) B4765337
theorem B30539177 : Blo 742328 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B1670759 : Blo 742328 1670759 := bstep (se 1 (by rfl) ⟨1253069, by rfl⟩ : syracuseStep 1670759 = 2506139) B2506139
theorem B1114025 : Blo 742328 1114025 := bstep (se 2 (by rfl) ⟨417759, by rfl⟩ : syracuseStep 1114025 = 835519) B835519
theorem B1114139 : Blo 742328 1114139 := bstep (se 1 (by rfl) ⟨835604, by rfl⟩ : syracuseStep 1114139 = 1671209) B1671209
theorem B3178703 : Blo 742328 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B1671407 : Blo 742328 1671407 := bstep (se 1 (by rfl) ⟨1253555, by rfl⟩ : syracuseStep 1671407 = 2507111) B2507111
theorem B8061191 : Blo 742328 8061191 := bstep (se 1 (by rfl) ⟨6045893, by rfl⟩ : syracuseStep 8061191 = 12091787) B12091787
theorem B1671839 : Blo 742328 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B6357851 : Blo 742328 6357851 := bstep (se 1 (by rfl) ⟨4768388, by rfl⟩ : syracuseStep 6357851 = 9536777) B9536777
theorem B5637113 : Blo 742328 5637113 := bstep (se 2 (by rfl) ⟨2113917, by rfl⟩ : syracuseStep 5637113 = 4227835) B4227835
theorem B5637599 : Blo 742328 5637599 := bstep (se 1 (by rfl) ⟨4228199, by rfl⟩ : syracuseStep 5637599 = 8456399) B8456399
theorem B1672847 : Blo 742328 1672847 := bstep (se 1 (by rfl) ⟨1254635, by rfl⟩ : syracuseStep 1672847 = 2509271) B2509271
theorem B1116575 : Blo 742328 1116575 := bstep (se 1 (by rfl) ⟨837431, by rfl⟩ : syracuseStep 1116575 = 1674863) B1674863
theorem B1673855 : Blo 742328 1673855 := bstep (se 1 (by rfl) ⟨1255391, by rfl⟩ : syracuseStep 1673855 = 2510783) B2510783
theorem B1673963 : Blo 742328 1673963 := bstep (se 1 (by rfl) ⟨1255472, by rfl⟩ : syracuseStep 1673963 = 2510945) B2510945
theorem B1674431 : Blo 742328 1674431 := bstep (se 1 (by rfl) ⟨1255823, by rfl⟩ : syracuseStep 1674431 = 2511647) B2511647
theorem B1674719 : Blo 742328 1674719 := bstep (se 1 (by rfl) ⟨1256039, by rfl⟩ : syracuseStep 1674719 = 2512079) B2512079
theorem B1117751 : Blo 742328 1117751 := bstep (se 1 (by rfl) ⟨838313, by rfl⟩ : syracuseStep 1117751 = 1676627) B1676627
theorem B7343759 : Blo 742328 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B3772331 : Blo 742328 3772331 := bstep (se 1 (by rfl) ⟨2829248, by rfl⟩ : syracuseStep 3772331 = 5658497) B5658497
theorem B3576311 : Blo 742328 3576311 := bstep (se 1 (by rfl) ⟨2682233, by rfl⟩ : syracuseStep 3576311 = 5364467) B5364467
theorem B1118747 : Blo 742328 1118747 := bstep (se 1 (by rfl) ⟨839060, by rfl⟩ : syracuseStep 1118747 = 1678121) B1678121
theorem B1675943 : Blo 742328 1675943 := bstep (se 1 (by rfl) ⟨1256957, by rfl⟩ : syracuseStep 1675943 = 2513915) B2513915
theorem B1676015 : Blo 742328 1676015 := bstep (se 1 (by rfl) ⟨1257011, by rfl⟩ : syracuseStep 1676015 = 2514023) B2514023
theorem B3773627 : Blo 742328 3773627 := bstep (se 1 (by rfl) ⟨2830220, by rfl⟩ : syracuseStep 3773627 = 5660441) B5660441
theorem B1676519 : Blo 742328 1676519 := bstep (se 1 (by rfl) ⟨1257389, by rfl⟩ : syracuseStep 1676519 = 2514779) B2514779
theorem B4756907 : Blo 742328 4756907 := bstep (se 1 (by rfl) ⟨3567680, by rfl⟩ : syracuseStep 4756907 = 7135361) B7135361
theorem B3020495 : Blo 742328 3020495 := bstep (se 1 (by rfl) ⟨2265371, by rfl⟩ : syracuseStep 3020495 = 4530743) B4530743
theorem B1677689 : Blo 742328 1677689 := bstep (se 2 (by rfl) ⟨629133, by rfl⟩ : syracuseStep 1677689 = 1258267) B1258267
theorem B9542771 : Blo 742328 9542771 := bstep (se 1 (by rfl) ⟨7157078, by rfl⟩ : syracuseStep 9542771 = 14314157) B14314157
theorem B1416379 : Blo 742328 1416379 := bstep (se 1 (by rfl) ⟨1062284, by rfl⟩ : syracuseStep 1416379 = 2124569) B2124569
theorem B1678571 : Blo 742328 1678571 := bstep (se 1 (by rfl) ⟨1258928, by rfl⟩ : syracuseStep 1678571 = 2517857) B2517857
theorem B3022703 : Blo 742328 3022703 := bstep (se 1 (by rfl) ⟨2267027, by rfl⟩ : syracuseStep 3022703 = 4534055) B4534055
theorem B6365263 : Blo 742328 6365263 := bstep (se 1 (by rfl) ⟨4773947, by rfl⟩ : syracuseStep 6365263 = 9547895) B9547895
theorem B21439403 : Blo 742328 21439403 := bstep (se 1 (by rfl) ⟨16079552, by rfl⟩ : syracuseStep 21439403 = 32159105) B32159105
theorem B1254683 : Blo 742328 1254683 := bstep (se 1 (by rfl) ⟨941012, by rfl⟩ : syracuseStep 1254683 = 1882025) B1882025
theorem B1254953 : Blo 742328 1254953 := bstep (se 2 (by rfl) ⟨470607, by rfl⟩ : syracuseStep 1254953 = 941215) B941215
theorem B20359451 : Blo 742328 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B1257707 : Blo 742328 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B2830889 : Blo 742328 2830889 := bstep (se 2 (by rfl) ⟨1061583, by rfl⟩ : syracuseStep 2830889 = 2123167) B2123167
theorem B4600435 : Blo 742328 4600435 := bstep (se 1 (by rfl) ⟨3450326, by rfl⟩ : syracuseStep 4600435 = 6900653) B6900653
theorem B1258409 : Blo 742328 1258409 := bstep (se 2 (by rfl) ⟨471903, by rfl⟩ : syracuseStep 1258409 = 943807) B943807
theorem B46445561 : Blo 742328 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B3585883 : Blo 742328 3585883 := bstep (se 1 (by rfl) ⟨2689412, by rfl⟩ : syracuseStep 3585883 = 5378825) B5378825
theorem B13582885 : Blo 742328 13582885 := bstep (se 4 (by rfl) ⟨1273395, by rfl⟩ : syracuseStep 13582885 = 2546791) B2546791
theorem B4080395 : Blo 742328 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B2507867 : Blo 742328 2507867 := bstep (se 1 (by rfl) ⟨1880900, by rfl⟩ : syracuseStep 2507867 = 3761801) B3761801
theorem B1885751 : Blo 742328 1885751 := bstep (se 1 (by rfl) ⟨1414313, by rfl⟩ : syracuseStep 1885751 = 2828627) B2828627
theorem B14534255 : Blo 742328 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B1591111 : Blo 742328 1591111 := bstep (se 1 (by rfl) ⟨1193333, by rfl⟩ : syracuseStep 1591111 = 2386667) B2386667
theorem B36620531 : Blo 742328 36620531 := bstep (se 1 (by rfl) ⟨27465398, by rfl⟩ : syracuseStep 36620531 = 54930797) B54930797
theorem B838255 : Blo 742328 838255 := bstep (se 1 (by rfl) ⟨628691, by rfl⟩ : syracuseStep 838255 = 1257383) B1257383
theorem B30624551 : Blo 742328 30624551 := bstep (se 1 (by rfl) ⟨22968413, by rfl⟩ : syracuseStep 30624551 = 45936827) B45936827
theorem B1887047 : Blo 742328 1887047 := bstep (se 1 (by rfl) ⟨1415285, by rfl⟩ : syracuseStep 1887047 = 2830571) B2830571
theorem B7621819 : Blo 742328 7621819 := bstep (se 1 (by rfl) ⟨5716364, by rfl⟩ : syracuseStep 7621819 = 11432729) B11432729
theorem B1887695 : Blo 742328 1887695 := bstep (se 1 (by rfl) ⟨1415771, by rfl⟩ : syracuseStep 1887695 = 2831543) B2831543
theorem B2543071 : Blo 742328 2543071 := bstep (se 1 (by rfl) ⟨1907303, by rfl⟩ : syracuseStep 2543071 = 3814607) B3814607
theorem B839407 : Blo 742328 839407 := bstep (se 1 (by rfl) ⟨629555, by rfl⟩ : syracuseStep 839407 = 1259111) B1259111
theorem B2117927 : Blo 742328 2117927 := bstep (se 1 (by rfl) ⟨1588445, by rfl⟩ : syracuseStep 2117927 = 3176891) B3176891
theorem B24105833 : Blo 742328 24105833 := bstep (se 2 (by rfl) ⟨9039687, by rfl⟩ : syracuseStep 24105833 = 18079375) B18079375
theorem B742683 : Blo 742328 742683 := bstep (se 1 (by rfl) ⟨557012, by rfl⟩ : syracuseStep 742683 = 1114025) B1114025
theorem B742783 : Blo 742328 742783 := bstep (se 1 (by rfl) ⟨557087, by rfl⟩ : syracuseStep 742783 = 1114175) B1114175
theorem B742815 : Blo 742328 742815 := bstep (se 1 (by rfl) ⟨557111, by rfl⟩ : syracuseStep 742815 = 1114223) B1114223
theorem B3823355 : Blo 742328 3823355 := bstep (se 1 (by rfl) ⟨2867516, by rfl⟩ : syracuseStep 3823355 = 5735033) B5735033
theorem B743271 : Blo 742328 743271 := bstep (se 1 (by rfl) ⟨557453, by rfl⟩ : syracuseStep 743271 = 1114907) B1114907
theorem B743527 : Blo 742328 743527 := bstep (se 1 (by rfl) ⟨557645, by rfl⟩ : syracuseStep 743527 = 1115291) B1115291
theorem B743663 : Blo 742328 743663 := bstep (se 1 (by rfl) ⟨557747, by rfl⟩ : syracuseStep 743663 = 1115495) B1115495
theorem B743871 : Blo 742328 743871 := bstep (se 1 (by rfl) ⟨557903, by rfl⟩ : syracuseStep 743871 = 1115807) B1115807
theorem B3758561 : Blo 742328 3758561 := bstep (se 2 (by rfl) ⟨1409460, by rfl⟩ : syracuseStep 3758561 = 2818921) B2818921
theorem B2513537 : Blo 742328 2513537 := bstep (se 2 (by rfl) ⟨942576, by rfl⟩ : syracuseStep 2513537 = 1885153) B1885153
theorem B744143 : Blo 742328 744143 := bstep (se 1 (by rfl) ⟨558107, by rfl⟩ : syracuseStep 744143 = 1116215) B1116215
theorem B744175 : Blo 742328 744175 := bstep (se 1 (by rfl) ⟨558131, by rfl⟩ : syracuseStep 744175 = 1116263) B1116263
theorem B744415 : Blo 742328 744415 := bstep (se 1 (by rfl) ⟨558311, by rfl⟩ : syracuseStep 744415 = 1116623) B1116623
theorem B744443 : Blo 742328 744443 := bstep (se 1 (by rfl) ⟨558332, by rfl⟩ : syracuseStep 744443 = 1116665) B1116665
theorem B941159 : Blo 742328 941159 := bstep (se 1 (by rfl) ⟨705869, by rfl⟩ : syracuseStep 941159 = 1411739) B1411739
theorem B744551 : Blo 742328 744551 := bstep (se 1 (by rfl) ⟨558413, by rfl⟩ : syracuseStep 744551 = 1116827) B1116827
theorem B744575 : Blo 742328 744575 := bstep (se 1 (by rfl) ⟨558431, by rfl⟩ : syracuseStep 744575 = 1116863) B1116863
theorem B941311 : Blo 742328 941311 := bstep (se 1 (by rfl) ⟨705983, by rfl⟩ : syracuseStep 941311 = 1411967) B1411967
theorem B745007 : Blo 742328 745007 := bstep (se 1 (by rfl) ⟨558755, by rfl⟩ : syracuseStep 745007 = 1117511) B1117511
theorem B2416351 : Blo 742328 2416351 := bstep (se 1 (by rfl) ⟨1812263, by rfl⟩ : syracuseStep 2416351 = 3624527) B3624527
theorem B2383643 : Blo 742328 2383643 := bstep (se 1 (by rfl) ⟨1787732, by rfl⟩ : syracuseStep 2383643 = 3575465) B3575465
theorem B745319 : Blo 742328 745319 := bstep (se 1 (by rfl) ⟨558989, by rfl⟩ : syracuseStep 745319 = 1117979) B1117979
theorem B745471 : Blo 742328 745471 := bstep (se 1 (by rfl) ⟨559103, by rfl⟩ : syracuseStep 745471 = 1118207) B1118207
theorem B2515103 : Blo 742328 2515103 := bstep (se 1 (by rfl) ⟨1886327, by rfl⟩ : syracuseStep 2515103 = 3772655) B3772655
theorem B745695 : Blo 742328 745695 := bstep (se 1 (by rfl) ⟨559271, by rfl⟩ : syracuseStep 745695 = 1118543) B1118543
theorem B745887 : Blo 742328 745887 := bstep (se 1 (by rfl) ⟨559415, by rfl⟩ : syracuseStep 745887 = 1118831) B1118831
theorem B745919 : Blo 742328 745919 := bstep (se 1 (by rfl) ⟨559439, by rfl⟩ : syracuseStep 745919 = 1118879) B1118879
theorem B746223 : Blo 742328 746223 := bstep (se 1 (by rfl) ⟨559667, by rfl⟩ : syracuseStep 746223 = 1119335) B1119335
theorem B746239 : Blo 742328 746239 := bstep (se 1 (by rfl) ⟨559679, by rfl⟩ : syracuseStep 746239 = 1119359) B1119359
theorem B2384873 : Blo 742328 2384873 := bstep (se 2 (by rfl) ⟨894327, by rfl⟩ : syracuseStep 2384873 = 1788655) B1788655
theorem B4778459 : Blo 742328 4778459 := bstep (se 1 (by rfl) ⟨3583844, by rfl⟩ : syracuseStep 4778459 = 7167689) B7167689
theorem B1338017 : Blo 742328 1338017 := bstep (se 2 (by rfl) ⟨501756, by rfl⟩ : syracuseStep 1338017 = 1003513) B1003513
theorem B3173201 : Blo 742328 3173201 := bstep (se 2 (by rfl) ⟨1189950, by rfl⟩ : syracuseStep 3173201 = 2379901) B2379901
theorem B12053377 : Blo 742328 12053377 := bstep (se 2 (by rfl) ⟨4520016, by rfl⟩ : syracuseStep 12053377 = 9040033) B9040033
theorem B2518127 : Blo 742328 2518127 := bstep (se 1 (by rfl) ⟨1888595, by rfl⟩ : syracuseStep 2518127 = 3777191) B3777191
theorem B3173543 : Blo 742328 3173543 := bstep (se 1 (by rfl) ⟨2380157, by rfl⟩ : syracuseStep 3173543 = 4760315) B4760315
theorem B12872915 : Blo 742328 12872915 := bstep (se 1 (by rfl) ⟨9654686, by rfl⟩ : syracuseStep 12872915 = 19309373) B19309373
theorem B7171379 : Blo 742328 7171379 := bstep (se 1 (by rfl) ⟨5378534, by rfl⟩ : syracuseStep 7171379 = 10757069) B10757069
theorem B3763583 : Blo 742328 3763583 := bstep (se 1 (by rfl) ⟨2822687, by rfl⟩ : syracuseStep 3763583 = 5645375) B5645375
theorem B2518775 : Blo 742328 2518775 := bstep (se 1 (by rfl) ⟨1889081, by rfl⟩ : syracuseStep 2518775 = 3778163) B3778163
theorem B4518463 : Blo 742328 4518463 := bstep (se 1 (by rfl) ⟨3388847, by rfl⟩ : syracuseStep 4518463 = 6777695) B6777695
theorem B6026075 : Blo 742328 6026075 := bstep (se 1 (by rfl) ⟨4519556, by rfl⟩ : syracuseStep 6026075 = 9039113) B9039113
theorem B13073537 : Blo 742328 13073537 := bstep (se 2 (by rfl) ⟨4902576, by rfl⟩ : syracuseStep 13073537 = 9805153) B9805153
theorem B1343135 : Blo 742328 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B1113839 : Blo 742328 1113839 := bstep (se 1 (by rfl) ⟨835379, by rfl⟩ : syracuseStep 1113839 = 1670759) B1670759
theorem B8487017 : Blo 742328 8487017 := bstep (se 2 (by rfl) ⟨3182631, by rfl⟩ : syracuseStep 8487017 = 6365263) B6365263
theorem B1114271 : Blo 742328 1114271 := bstep (se 1 (by rfl) ⟨835703, by rfl⟩ : syracuseStep 1114271 = 1671407) B1671407
theorem B5374127 : Blo 742328 5374127 := bstep (se 1 (by rfl) ⟨4030595, by rfl⟩ : syracuseStep 5374127 = 8061191) B8061191
theorem B1114559 : Blo 742328 1114559 := bstep (se 1 (by rfl) ⟨835919, by rfl⟩ : syracuseStep 1114559 = 1671839) B1671839
theorem B1671911 : Blo 742328 1671911 := bstep (se 1 (by rfl) ⟨1253933, by rfl⟩ : syracuseStep 1671911 = 2507867) B2507867
theorem B1115231 : Blo 742328 1115231 := bstep (se 1 (by rfl) ⟨836423, by rfl⟩ : syracuseStep 1115231 = 1672847) B1672847
theorem B24413687 : Blo 742328 24413687 := bstep (se 1 (by rfl) ⟨18310265, by rfl⟩ : syracuseStep 24413687 = 36620531) B36620531
theorem B1115903 : Blo 742328 1115903 := bstep (se 1 (by rfl) ⟨836927, by rfl⟩ : syracuseStep 1115903 = 1673855) B1673855
theorem B1115975 : Blo 742328 1115975 := bstep (se 1 (by rfl) ⟨836981, by rfl⟩ : syracuseStep 1115975 = 1673963) B1673963
theorem B20416367 : Blo 742328 20416367 := bstep (se 1 (by rfl) ⟨15312275, by rfl⟩ : syracuseStep 20416367 = 30624551) B30624551
theorem B10881053 : Blo 742328 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B1116287 : Blo 742328 1116287 := bstep (se 1 (by rfl) ⟨837215, by rfl⟩ : syracuseStep 1116287 = 1674431) B1674431
theorem B1116479 : Blo 742328 1116479 := bstep (se 1 (by rfl) ⟨837359, by rfl⟩ : syracuseStep 1116479 = 1674719) B1674719
theorem B1117295 : Blo 742328 1117295 := bstep (se 1 (by rfl) ⟨837971, by rfl⟩ : syracuseStep 1117295 = 1675943) B1675943
theorem B1117343 : Blo 742328 1117343 := bstep (se 1 (by rfl) ⟨838007, by rfl⟩ : syracuseStep 1117343 = 1676015) B1676015
theorem B1117673 : Blo 742328 1117673 := bstep (se 2 (by rfl) ⟨419127, by rfl⟩ : syracuseStep 1117673 = 838255) B838255
theorem B1117679 : Blo 742328 1117679 := bstep (se 1 (by rfl) ⟨838259, by rfl⟩ : syracuseStep 1117679 = 1676519) B1676519
theorem B1118459 : Blo 742328 1118459 := bstep (se 1 (by rfl) ⟨838844, by rfl⟩ : syracuseStep 1118459 = 1677689) B1677689
theorem B1675691 : Blo 742328 1675691 := bstep (se 1 (by rfl) ⟨1256768, by rfl⟩ : syracuseStep 1675691 = 2513537) B2513537
theorem B6361847 : Blo 742328 6361847 := bstep (se 1 (by rfl) ⟨4771385, by rfl⟩ : syracuseStep 6361847 = 9542771) B9542771
theorem B1119047 : Blo 742328 1119047 := bstep (se 1 (by rfl) ⟨839285, by rfl⟩ : syracuseStep 1119047 = 1678571) B1678571
theorem B1119209 : Blo 742328 1119209 := bstep (se 2 (by rfl) ⟨419703, by rfl⟩ : syracuseStep 1119209 = 839407) B839407
theorem B1676735 : Blo 742328 1676735 := bstep (se 1 (by rfl) ⟨1257551, by rfl⟩ : syracuseStep 1676735 = 2515103) B2515103
theorem B14292935 : Blo 742328 14292935 := bstep (se 1 (by rfl) ⟨10719701, by rfl⟩ : syracuseStep 14292935 = 21439403) B21439403
theorem B6133913 : Blo 742328 6133913 := bstep (se 2 (by rfl) ⟨2300217, by rfl⟩ : syracuseStep 6133913 = 4600435) B4600435
theorem B13572967 : Blo 742328 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B3185639 : Blo 742328 3185639 := bstep (se 1 (by rfl) ⟨2389229, by rfl⟩ : syracuseStep 3185639 = 4778459) B4778459
theorem B1678751 : Blo 742328 1678751 := bstep (se 1 (by rfl) ⟨1259063, by rfl⟩ : syracuseStep 1678751 = 2518127) B2518127
theorem B1679183 : Blo 742328 1679183 := bstep (se 1 (by rfl) ⟨1259387, by rfl⟩ : syracuseStep 1679183 = 2518775) B2518775
theorem B1255081 : Blo 742328 1255081 := bstep (se 2 (by rfl) ⟨470655, by rfl⟩ : syracuseStep 1255081 = 941311) B941311
theorem B3221801 : Blo 742328 3221801 := bstep (se 2 (by rfl) ⟨1208175, by rfl⟩ : syracuseStep 3221801 = 2416351) B2416351
theorem B895423 : Blo 742328 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B4238567 : Blo 742328 4238567 := bstep (se 1 (by rfl) ⟨3178925, by rfl⟩ : syracuseStep 4238567 = 6357851) B6357851
theorem B5647805 : Blo 742328 5647805 := bstep (se 3 (by rfl) ⟨1058963, by rfl⟩ : syracuseStep 5647805 = 2117927) B2117927
theorem B1257167 : Blo 742328 1257167 := bstep (se 1 (by rfl) ⟨942875, by rfl⟩ : syracuseStep 1257167 = 1885751) B1885751
theorem B1258031 : Blo 742328 1258031 := bstep (se 1 (by rfl) ⟨943523, by rfl⟩ : syracuseStep 1258031 = 1887047) B1887047
theorem B1258463 : Blo 742328 1258463 := bstep (se 1 (by rfl) ⟨943847, by rfl⟩ : syracuseStep 1258463 = 1887695) B1887695
theorem B4895839 : Blo 742328 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B16070555 : Blo 742328 16070555 := bstep (se 1 (by rfl) ⟨12052916, by rfl⟩ : syracuseStep 16070555 = 24105833) B24105833
theorem B16071169 : Blo 742328 16071169 := bstep (se 2 (by rfl) ⟨6026688, by rfl⟩ : syracuseStep 16071169 = 12053377) B12053377
theorem B2505707 : Blo 742328 2505707 := bstep (se 1 (by rfl) ⟨1879280, by rfl⟩ : syracuseStep 2505707 = 3758561) B3758561
theorem B3390761 : Blo 742328 3390761 := bstep (se 2 (by rfl) ⟨1271535, by rfl⟩ : syracuseStep 3390761 = 2543071) B2543071
theorem B1589095 : Blo 742328 1589095 := bstep (se 1 (by rfl) ⟨1191821, by rfl⟩ : syracuseStep 1589095 = 2383643) B2383643
theorem B2015135 : Blo 742328 2015135 := bstep (se 1 (by rfl) ⟨1511351, by rfl⟩ : syracuseStep 2015135 = 3022703) B3022703
theorem B1589915 : Blo 742328 1589915 := bstep (se 1 (by rfl) ⟨1192436, by rfl⟩ : syracuseStep 1589915 = 2384873) B2384873
theorem B836455 : Blo 742328 836455 := bstep (se 1 (by rfl) ⟨627341, by rfl⟩ : syracuseStep 836455 = 1254683) B1254683
theorem B40649701 : Blo 742328 40649701 := bstep (se 4 (by rfl) ⟨3810909, by rfl⟩ : syracuseStep 40649701 = 7621819) B7621819
theorem B836635 : Blo 742328 836635 := bstep (se 1 (by rfl) ⟨627476, by rfl⟩ : syracuseStep 836635 = 1254953) B1254953
theorem B2115467 : Blo 742328 2115467 := bstep (se 1 (by rfl) ⟨1586600, by rfl⟩ : syracuseStep 2115467 = 3173201) B3173201
theorem B2115695 : Blo 742328 2115695 := bstep (se 1 (by rfl) ⟨1586771, by rfl⟩ : syracuseStep 2115695 = 3173543) B3173543
theorem B2509055 : Blo 742328 2509055 := bstep (se 1 (by rfl) ⟨1881791, by rfl⟩ : syracuseStep 2509055 = 3763583) B3763583
theorem B838471 : Blo 742328 838471 := bstep (se 1 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 838471 = 1257707) B1257707
theorem B2509757 : Blo 742328 2509757 := bstep (se 3 (by rfl) ⟨470579, by rfl⟩ : syracuseStep 2509757 = 941159) B941159
theorem B1887259 : Blo 742328 1887259 := bstep (se 1 (by rfl) ⟨1415444, by rfl⟩ : syracuseStep 1887259 = 2830889) B2830889
theorem B4017383 : Blo 742328 4017383 := bstep (se 1 (by rfl) ⟨3013037, by rfl⟩ : syracuseStep 4017383 = 6026075) B6026075
theorem B838939 : Blo 742328 838939 := bstep (se 1 (by rfl) ⟨629204, by rfl⟩ : syracuseStep 838939 = 1258409) B1258409
theorem B1888505 : Blo 742328 1888505 := bstep (se 2 (by rfl) ⟨708189, by rfl⟩ : syracuseStep 1888505 = 1416379) B1416379
theorem B742559 : Blo 742328 742559 := bstep (se 1 (by rfl) ⟨556919, by rfl⟩ : syracuseStep 742559 = 1113839) B1113839
theorem B742759 : Blo 742328 742759 := bstep (se 1 (by rfl) ⟨557069, by rfl⟩ : syracuseStep 742759 = 1114139) B1114139
theorem B2119135 : Blo 742328 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B3758075 : Blo 742328 3758075 := bstep (se 1 (by rfl) ⟨2818556, by rfl⟩ : syracuseStep 3758075 = 5637113) B5637113
theorem B18110513 : Blo 742328 18110513 := bstep (se 2 (by rfl) ⟨6791442, by rfl⟩ : syracuseStep 18110513 = 13582885) B13582885
theorem B3758399 : Blo 742328 3758399 := bstep (se 1 (by rfl) ⟨2818799, by rfl⟩ : syracuseStep 3758399 = 5637599) B5637599
theorem B744383 : Blo 742328 744383 := bstep (se 1 (by rfl) ⟨558287, by rfl⟩ : syracuseStep 744383 = 1116575) B1116575
theorem B745167 : Blo 742328 745167 := bstep (se 1 (by rfl) ⟨558875, by rfl⟩ : syracuseStep 745167 = 1117751) B1117751
theorem B2121481 : Blo 742328 2121481 := bstep (se 2 (by rfl) ⟨795555, by rfl⟩ : syracuseStep 2121481 = 1591111) B1591111
theorem B2514887 : Blo 742328 2514887 := bstep (se 1 (by rfl) ⟨1886165, by rfl⟩ : syracuseStep 2514887 = 3772331) B3772331
theorem B2384207 : Blo 742328 2384207 := bstep (se 1 (by rfl) ⟨1788155, by rfl⟩ : syracuseStep 2384207 = 3576311) B3576311
theorem B745831 : Blo 742328 745831 := bstep (se 1 (by rfl) ⟨559373, by rfl⟩ : syracuseStep 745831 = 1118747) B1118747
theorem B2515751 : Blo 742328 2515751 := bstep (se 1 (by rfl) ⟨1886813, by rfl⟩ : syracuseStep 2515751 = 3773627) B3773627
theorem B3171271 : Blo 742328 3171271 := bstep (se 1 (by rfl) ⟨2378453, by rfl⟩ : syracuseStep 3171271 = 4756907) B4756907
theorem B2548903 : Blo 742328 2548903 := bstep (se 1 (by rfl) ⟨1911677, by rfl⟩ : syracuseStep 2548903 = 3823355) B3823355
theorem B38758013 : Blo 742328 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B8054653 : Blo 742328 8054653 := bstep (se 3 (by rfl) ⟨1510247, by rfl⟩ : syracuseStep 8054653 = 3020495) B3020495
theorem B6024617 : Blo 742328 6024617 := bstep (se 2 (by rfl) ⟨2259231, by rfl⟩ : syracuseStep 6024617 = 4518463) B4518463
theorem B3568045 : Blo 742328 3568045 := bstep (se 3 (by rfl) ⟨669008, by rfl⟩ : syracuseStep 3568045 = 1338017) B1338017
theorem B8581943 : Blo 742328 8581943 := bstep (se 1 (by rfl) ⟨6436457, by rfl⟩ : syracuseStep 8581943 = 12872915) B12872915
theorem B4780919 : Blo 742328 4780919 := bstep (se 1 (by rfl) ⟨3585689, by rfl⟩ : syracuseStep 4780919 = 7171379) B7171379
theorem B4781177 : Blo 742328 4781177 := bstep (se 2 (by rfl) ⟨1792941, by rfl⟩ : syracuseStep 4781177 = 3585883) B3585883
theorem B30963707 : Blo 742328 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B8715691 : Blo 742328 8715691 := bstep (se 1 (by rfl) ⟨6536768, by rfl⟩ : syracuseStep 8715691 = 13073537) B13073537
theorem B1114607 : Blo 742328 1114607 := bstep (se 1 (by rfl) ⟨835955, by rfl⟩ : syracuseStep 1114607 = 1671911) B1671911
theorem B1115273 : Blo 742328 1115273 := bstep (se 2 (by rfl) ⟨418227, by rfl⟩ : syracuseStep 1115273 = 836455) B836455
theorem B1410311 : Blo 742328 1410311 := bstep (se 1 (by rfl) ⟨1057733, by rfl⟩ : syracuseStep 1410311 = 2115467) B2115467
theorem B4228361 : Blo 742328 4228361 := bstep (se 2 (by rfl) ⟨1585635, by rfl⟩ : syracuseStep 4228361 = 3171271) B3171271
theorem B54199601 : Blo 742328 54199601 := bstep (se 2 (by rfl) ⟨20324850, by rfl⟩ : syracuseStep 54199601 = 40649701) B40649701
theorem B1115513 : Blo 742328 1115513 := bstep (se 2 (by rfl) ⟨418317, by rfl⟩ : syracuseStep 1115513 = 836635) B836635
theorem B1410463 : Blo 742328 1410463 := bstep (se 1 (by rfl) ⟨1057847, by rfl⟩ : syracuseStep 1410463 = 2115695) B2115695
theorem B1672703 : Blo 742328 1672703 := bstep (se 1 (by rfl) ⟨1254527, by rfl⟩ : syracuseStep 1672703 = 2509055) B2509055
theorem B1673171 : Blo 742328 1673171 := bstep (se 1 (by rfl) ⟨1254878, by rfl⟩ : syracuseStep 1673171 = 2509757) B2509757
theorem B1673441 : Blo 742328 1673441 := bstep (se 2 (by rfl) ⟨627540, by rfl⟩ : syracuseStep 1673441 = 1255081) B1255081
theorem B1117127 : Blo 742328 1117127 := bstep (se 1 (by rfl) ⟨837845, by rfl⟩ : syracuseStep 1117127 = 1675691) B1675691
theorem B1117823 : Blo 742328 1117823 := bstep (se 1 (by rfl) ⟨838367, by rfl⟩ : syracuseStep 1117823 = 1676735) B1676735
theorem B1117961 : Blo 742328 1117961 := bstep (se 2 (by rfl) ⟨419235, by rfl⟩ : syracuseStep 1117961 = 838471) B838471
theorem B1118585 : Blo 742328 1118585 := bstep (se 2 (by rfl) ⟨419469, by rfl⟩ : syracuseStep 1118585 = 838939) B838939
theorem B1119167 : Blo 742328 1119167 := bstep (se 1 (by rfl) ⟨839375, by rfl⟩ : syracuseStep 1119167 = 1678751) B1678751
theorem B1119455 : Blo 742328 1119455 := bstep (se 1 (by rfl) ⟨839591, by rfl⟩ : syracuseStep 1119455 = 1679183) B1679183
theorem B1676591 : Blo 742328 1676591 := bstep (se 1 (by rfl) ⟨1257443, by rfl⟩ : syracuseStep 1676591 = 2514887) B2514887
theorem B1677167 : Blo 742328 1677167 := bstep (se 1 (by rfl) ⟨1257875, by rfl⟩ : syracuseStep 1677167 = 2515751) B2515751
theorem B4757393 : Blo 742328 4757393 := bstep (se 2 (by rfl) ⟨1784022, by rfl⟩ : syracuseStep 4757393 = 3568045) B3568045
theorem B6527785 : Blo 742328 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B2825513 : Blo 742328 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B2825711 : Blo 742328 2825711 := bstep (se 1 (by rfl) ⟨2119283, by rfl⟩ : syracuseStep 2825711 = 4238567) B4238567
theorem B3187279 : Blo 742328 3187279 := bstep (se 1 (by rfl) ⟨2390459, by rfl⟩ : syracuseStep 3187279 = 4780919) B4780919
theorem B3187451 : Blo 742328 3187451 := bstep (se 1 (by rfl) ⟨2390588, by rfl⟩ : syracuseStep 3187451 = 4781177) B4781177
theorem B18097289 : Blo 742328 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B2828641 : Blo 742328 2828641 := bstep (se 2 (by rfl) ⟨1060740, by rfl⟩ : syracuseStep 2828641 = 2121481) B2121481
theorem B3582751 : Blo 742328 3582751 := bstep (se 1 (by rfl) ⟨2687063, by rfl⟩ : syracuseStep 3582751 = 5374127) B5374127
theorem B13610911 : Blo 742328 13610911 := bstep (se 1 (by rfl) ⟨10208183, by rfl⟩ : syracuseStep 13610911 = 20416367) B20416367
theorem B7254035 : Blo 742328 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B4239773 : Blo 742328 4239773 := bstep (se 3 (by rfl) ⟨794957, by rfl⟩ : syracuseStep 4239773 = 1589915) B1589915
theorem B1259003 : Blo 742328 1259003 := bstep (se 1 (by rfl) ⟨944252, by rfl⟩ : syracuseStep 1259003 = 1888505) B1888505
theorem B4241231 : Blo 742328 4241231 := bstep (se 1 (by rfl) ⟨3180923, by rfl⟩ : syracuseStep 4241231 = 6361847) B6361847
theorem B1193897 : Blo 742328 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B2505383 : Blo 742328 2505383 := bstep (se 1 (by rfl) ⟨1879037, by rfl⟩ : syracuseStep 2505383 = 3758075) B3758075
theorem B2505599 : Blo 742328 2505599 := bstep (se 1 (by rfl) ⟨1879199, by rfl⟩ : syracuseStep 2505599 = 3758399) B3758399
theorem B1589471 : Blo 742328 1589471 := bstep (se 1 (by rfl) ⟨1192103, by rfl⟩ : syracuseStep 1589471 = 2384207) B2384207
theorem B25838675 : Blo 742328 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B2147867 : Blo 742328 2147867 := bstep (se 1 (by rfl) ⟨1610900, by rfl⟩ : syracuseStep 2147867 = 3221801) B3221801
theorem B4016411 : Blo 742328 4016411 := bstep (se 1 (by rfl) ⟨3012308, by rfl⟩ : syracuseStep 4016411 = 6024617) B6024617
theorem B838111 : Blo 742328 838111 := bstep (se 1 (by rfl) ⟨628583, by rfl⟩ : syracuseStep 838111 = 1257167) B1257167
theorem B838687 : Blo 742328 838687 := bstep (se 1 (by rfl) ⟨629015, by rfl⟩ : syracuseStep 838687 = 1258031) B1258031
theorem B5721295 : Blo 742328 5721295 := bstep (se 1 (by rfl) ⟨4290971, by rfl⟩ : syracuseStep 5721295 = 8581943) B8581943
theorem B838975 : Blo 742328 838975 := bstep (se 1 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 838975 = 1258463) B1258463
theorem B11620921 : Blo 742328 11620921 := bstep (se 2 (by rfl) ⟨4357845, by rfl⟩ : syracuseStep 11620921 = 8715691) B8715691
theorem B2118793 : Blo 742328 2118793 := bstep (se 2 (by rfl) ⟨794547, by rfl⟩ : syracuseStep 2118793 = 1589095) B1589095
theorem B5658011 : Blo 742328 5658011 := bstep (se 1 (by rfl) ⟨4243508, by rfl⟩ : syracuseStep 5658011 = 8487017) B8487017
theorem B742847 : Blo 742328 742847 := bstep (se 1 (by rfl) ⟨557135, by rfl⟩ : syracuseStep 742847 = 1114271) B1114271
theorem B743039 : Blo 742328 743039 := bstep (se 1 (by rfl) ⟨557279, by rfl⟩ : syracuseStep 743039 = 1114559) B1114559
theorem B743487 : Blo 742328 743487 := bstep (se 1 (by rfl) ⟨557615, by rfl⟩ : syracuseStep 743487 = 1115231) B1115231
theorem B16275791 : Blo 742328 16275791 := bstep (se 1 (by rfl) ⟨12206843, by rfl⟩ : syracuseStep 16275791 = 24413687) B24413687
theorem B743935 : Blo 742328 743935 := bstep (se 1 (by rfl) ⟨557951, by rfl⟩ : syracuseStep 743935 = 1115903) B1115903
theorem B743983 : Blo 742328 743983 := bstep (se 1 (by rfl) ⟨557987, by rfl⟩ : syracuseStep 743983 = 1115975) B1115975
theorem B744191 : Blo 742328 744191 := bstep (se 1 (by rfl) ⟨558143, by rfl⟩ : syracuseStep 744191 = 1116287) B1116287
theorem B744319 : Blo 742328 744319 := bstep (se 1 (by rfl) ⟨558239, by rfl⟩ : syracuseStep 744319 = 1116479) B1116479
theorem B3398537 : Blo 742328 3398537 := bstep (se 2 (by rfl) ⟨1274451, by rfl⟩ : syracuseStep 3398537 = 2548903) B2548903
theorem B744863 : Blo 742328 744863 := bstep (se 1 (by rfl) ⟨558647, by rfl⟩ : syracuseStep 744863 = 1117295) B1117295
theorem B744895 : Blo 742328 744895 := bstep (se 1 (by rfl) ⟨558671, by rfl⟩ : syracuseStep 744895 = 1117343) B1117343
theorem B2678255 : Blo 742328 2678255 := bstep (se 1 (by rfl) ⟨2008691, by rfl⟩ : syracuseStep 2678255 = 4017383) B4017383
theorem B745115 : Blo 742328 745115 := bstep (se 1 (by rfl) ⟨558836, by rfl⟩ : syracuseStep 745115 = 1117673) B1117673
theorem B745119 : Blo 742328 745119 := bstep (se 1 (by rfl) ⟨558839, by rfl⟩ : syracuseStep 745119 = 1117679) B1117679
theorem B10739537 : Blo 742328 10739537 := bstep (se 2 (by rfl) ⟨4027326, by rfl⟩ : syracuseStep 10739537 = 8054653) B8054653
theorem B745639 : Blo 742328 745639 := bstep (se 1 (by rfl) ⟨559229, by rfl⟩ : syracuseStep 745639 = 1118459) B1118459
theorem B746031 : Blo 742328 746031 := bstep (se 1 (by rfl) ⟨559523, by rfl⟩ : syracuseStep 746031 = 1119047) B1119047
theorem B746139 : Blo 742328 746139 := bstep (se 1 (by rfl) ⟨559604, by rfl⟩ : syracuseStep 746139 = 1119209) B1119209
theorem B9528623 : Blo 742328 9528623 := bstep (se 1 (by rfl) ⟨7146467, by rfl⟩ : syracuseStep 9528623 = 14292935) B14292935
theorem B2516345 : Blo 742328 2516345 := bstep (se 2 (by rfl) ⟨943629, by rfl⟩ : syracuseStep 2516345 = 1887259) B1887259
theorem B4089275 : Blo 742328 4089275 := bstep (se 1 (by rfl) ⟨3066956, by rfl⟩ : syracuseStep 4089275 = 6133913) B6133913
theorem B2123759 : Blo 742328 2123759 := bstep (se 1 (by rfl) ⟨1592819, by rfl⟩ : syracuseStep 2123759 = 3185639) B3185639
theorem B48294701 : Blo 742328 48294701 := bstep (se 3 (by rfl) ⟨9055256, by rfl⟩ : syracuseStep 48294701 = 18110513) B18110513
theorem B3765203 : Blo 742328 3765203 := bstep (se 1 (by rfl) ⟨2823902, by rfl⟩ : syracuseStep 3765203 = 5647805) B5647805
theorem B21428225 : Blo 742328 21428225 := bstep (se 2 (by rfl) ⟨8035584, by rfl⟩ : syracuseStep 21428225 = 16071169) B16071169
theorem B9042029 : Blo 742328 9042029 := bstep (se 3 (by rfl) ⟨1695380, by rfl⟩ : syracuseStep 9042029 = 3390761) B3390761
theorem B10713703 : Blo 742328 10713703 := bstep (se 1 (by rfl) ⟨8035277, by rfl⟩ : syracuseStep 10713703 = 16070555) B16070555
theorem B20642471 : Blo 742328 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B1670471 : Blo 742328 1670471 := bstep (se 1 (by rfl) ⟨1252853, by rfl⟩ : syracuseStep 1670471 = 2505707) B2505707
theorem B1343423 : Blo 742328 1343423 := bstep (se 1 (by rfl) ⟨1007567, by rfl⟩ : syracuseStep 1343423 = 2015135) B2015135
theorem B2818907 : Blo 742328 2818907 := bstep (se 1 (by rfl) ⟨2114180, by rfl⟩ : syracuseStep 2818907 = 4228361) B4228361
theorem B1115135 : Blo 742328 1115135 := bstep (se 1 (by rfl) ⟨836351, by rfl⟩ : syracuseStep 1115135 = 1672703) B1672703
theorem B1115447 : Blo 742328 1115447 := bstep (se 1 (by rfl) ⟨836585, by rfl⟩ : syracuseStep 1115447 = 1673171) B1673171
theorem B1115627 : Blo 742328 1115627 := bstep (se 1 (by rfl) ⟨836720, by rfl⟩ : syracuseStep 1115627 = 1673441) B1673441
theorem B3771521 : Blo 742328 3771521 := bstep (se 2 (by rfl) ⟨1414320, by rfl⟩ : syracuseStep 3771521 = 2828641) B2828641
theorem B1117481 : Blo 742328 1117481 := bstep (se 2 (by rfl) ⟨419055, by rfl⟩ : syracuseStep 1117481 = 838111) B838111
theorem B1117727 : Blo 742328 1117727 := bstep (se 1 (by rfl) ⟨838295, by rfl⟩ : syracuseStep 1117727 = 1676591) B1676591
theorem B3772007 : Blo 742328 3772007 := bstep (se 1 (by rfl) ⟨2829005, by rfl⟩ : syracuseStep 3772007 = 5658011) B5658011
theorem B1118111 : Blo 742328 1118111 := bstep (se 1 (by rfl) ⟨838583, by rfl⟩ : syracuseStep 1118111 = 1677167) B1677167
theorem B1118249 : Blo 742328 1118249 := bstep (se 2 (by rfl) ⟨419343, by rfl⟩ : syracuseStep 1118249 = 838687) B838687
theorem B10850527 : Blo 742328 10850527 := bstep (se 1 (by rfl) ⟨8137895, by rfl⟩ : syracuseStep 10850527 = 16275791) B16275791
theorem B1118633 : Blo 742328 1118633 := bstep (se 2 (by rfl) ⟨419487, by rfl⟩ : syracuseStep 1118633 = 838975) B838975
theorem B2265691 : Blo 742328 2265691 := bstep (se 1 (by rfl) ⟨1699268, by rfl⟩ : syracuseStep 2265691 = 3398537) B3398537
theorem B3183725 : Blo 742328 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B12064859 : Blo 742328 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B1677563 : Blo 742328 1677563 := bstep (se 1 (by rfl) ⟨1258172, by rfl⟩ : syracuseStep 1677563 = 2516345) B2516345
theorem B2726183 : Blo 742328 2726183 := bstep (se 1 (by rfl) ⟨2044637, by rfl⟩ : syracuseStep 2726183 = 4089275) B4089275
theorem B2825057 : Blo 742328 2825057 := bstep (se 2 (by rfl) ⟨1059396, by rfl⟩ : syracuseStep 2825057 = 2118793) B2118793
theorem B2826515 : Blo 742328 2826515 := bstep (se 1 (by rfl) ⟨2119886, by rfl⟩ : syracuseStep 2826515 = 4239773) B4239773
theorem B2827487 : Blo 742328 2827487 := bstep (se 1 (by rfl) ⟨2120615, by rfl⟩ : syracuseStep 2827487 = 4241231) B4241231
theorem B3582461 : Blo 742328 3582461 := bstep (se 3 (by rfl) ⟨671711, by rfl⟩ : syracuseStep 3582461 = 1343423) B1343423
theorem B1059647 : Blo 742328 1059647 := bstep (se 1 (by rfl) ⟨794735, by rfl⟩ : syracuseStep 1059647 = 1589471) B1589471
theorem B1880617 : Blo 742328 1880617 := bstep (se 2 (by rfl) ⟨705231, by rfl⟩ : syracuseStep 1880617 = 1410463) B1410463
theorem B1883675 : Blo 742328 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B1785503 : Blo 742328 1785503 := bstep (se 1 (by rfl) ⟨1339127, by rfl⟩ : syracuseStep 1785503 = 2678255) B2678255
theorem B1883807 : Blo 742328 1883807 := bstep (se 1 (by rfl) ⟨1412855, by rfl⟩ : syracuseStep 1883807 = 2825711) B2825711
theorem B7159691 : Blo 742328 7159691 := bstep (se 1 (by rfl) ⟨5369768, by rfl⟩ : syracuseStep 7159691 = 10739537) B10739537
theorem B32196467 : Blo 742328 32196467 := bstep (se 1 (by rfl) ⟨24147350, by rfl⟩ : syracuseStep 32196467 = 48294701) B48294701
theorem B4836023 : Blo 742328 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B2510135 : Blo 742328 2510135 := bstep (se 1 (by rfl) ⟨1882601, by rfl⟩ : syracuseStep 2510135 = 3765203) B3765203
theorem B839335 : Blo 742328 839335 := bstep (se 1 (by rfl) ⟨629501, by rfl⟩ : syracuseStep 839335 = 1259003) B1259003
theorem B8703713 : Blo 742328 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B743071 : Blo 742328 743071 := bstep (se 1 (by rfl) ⟨557303, by rfl⟩ : syracuseStep 743071 = 1114607) B1114607
theorem B17225783 : Blo 742328 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B743515 : Blo 742328 743515 := bstep (se 1 (by rfl) ⟨557636, by rfl⟩ : syracuseStep 743515 = 1115273) B1115273
theorem B4249705 : Blo 742328 4249705 := bstep (se 2 (by rfl) ⟨1593639, by rfl⟩ : syracuseStep 4249705 = 3187279) B3187279
theorem B36133067 : Blo 742328 36133067 := bstep (se 1 (by rfl) ⟨27099800, by rfl⟩ : syracuseStep 36133067 = 54199601) B54199601
theorem B743675 : Blo 742328 743675 := bstep (se 1 (by rfl) ⟨557756, by rfl⟩ : syracuseStep 743675 = 1115513) B1115513
theorem B1431911 : Blo 742328 1431911 := bstep (se 1 (by rfl) ⟨1073933, by rfl⟩ : syracuseStep 1431911 = 2147867) B2147867
theorem B2677607 : Blo 742328 2677607 := bstep (se 1 (by rfl) ⟨2008205, by rfl⟩ : syracuseStep 2677607 = 4016411) B4016411
theorem B744751 : Blo 742328 744751 := bstep (se 1 (by rfl) ⟨558563, by rfl⟩ : syracuseStep 744751 = 1117127) B1117127
theorem B745215 : Blo 742328 745215 := bstep (se 1 (by rfl) ⟨558911, by rfl⟩ : syracuseStep 745215 = 1117823) B1117823
theorem B745307 : Blo 742328 745307 := bstep (se 1 (by rfl) ⟨558980, by rfl⟩ : syracuseStep 745307 = 1117961) B1117961
theorem B745723 : Blo 742328 745723 := bstep (se 1 (by rfl) ⟨559292, by rfl⟩ : syracuseStep 745723 = 1118585) B1118585
theorem B746111 : Blo 742328 746111 := bstep (se 1 (by rfl) ⟨559583, by rfl⟩ : syracuseStep 746111 = 1119167) B1119167
theorem B3760829 : Blo 742328 3760829 := bstep (se 3 (by rfl) ⟨705155, by rfl⟩ : syracuseStep 3760829 = 1410311) B1410311
theorem B746303 : Blo 742328 746303 := bstep (se 1 (by rfl) ⟨559727, by rfl⟩ : syracuseStep 746303 = 1119455) B1119455
theorem B4777001 : Blo 742328 4777001 := bstep (se 2 (by rfl) ⟨1791375, by rfl⟩ : syracuseStep 4777001 = 3582751) B3582751
theorem B3171595 : Blo 742328 3171595 := bstep (se 1 (by rfl) ⟨2378696, by rfl⟩ : syracuseStep 3171595 = 4757393) B4757393
theorem B7628393 : Blo 742328 7628393 := bstep (se 2 (by rfl) ⟨2860647, by rfl⟩ : syracuseStep 7628393 = 5721295) B5721295
theorem B18147881 : Blo 742328 18147881 := bstep (se 2 (by rfl) ⟨6805455, by rfl⟩ : syracuseStep 18147881 = 13610911) B13610911
theorem B5663357 : Blo 742328 5663357 := bstep (se 3 (by rfl) ⟨1061879, by rfl⟩ : syracuseStep 5663357 = 2123759) B2123759
theorem B2124967 : Blo 742328 2124967 := bstep (se 1 (by rfl) ⟨1593725, by rfl⟩ : syracuseStep 2124967 = 3187451) B3187451
theorem B15494561 : Blo 742328 15494561 := bstep (se 2 (by rfl) ⟨5810460, by rfl⟩ : syracuseStep 15494561 = 11620921) B11620921
theorem B6352415 : Blo 742328 6352415 := bstep (se 1 (by rfl) ⟨4764311, by rfl⟩ : syracuseStep 6352415 = 9528623) B9528623
theorem B14284937 : Blo 742328 14284937 := bstep (se 2 (by rfl) ⟨5356851, by rfl⟩ : syracuseStep 14284937 = 10713703) B10713703
theorem B14285483 : Blo 742328 14285483 := bstep (se 1 (by rfl) ⟨10714112, by rfl⟩ : syracuseStep 14285483 = 21428225) B21428225
theorem B6028019 : Blo 742328 6028019 := bstep (se 1 (by rfl) ⟨4521014, by rfl⟩ : syracuseStep 6028019 = 9042029) B9042029
theorem B1670255 : Blo 742328 1670255 := bstep (se 1 (by rfl) ⟨1252691, by rfl⟩ : syracuseStep 1670255 = 2505383) B2505383
theorem B13761647 : Blo 742328 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B1670399 : Blo 742328 1670399 := bstep (se 1 (by rfl) ⟨1252799, by rfl⟩ : syracuseStep 1670399 = 2505599) B2505599
theorem B1113647 : Blo 742328 1113647 := bstep (se 1 (by rfl) ⟨835235, by rfl⟩ : syracuseStep 1113647 = 1670471) B1670471
theorem B21464311 : Blo 742328 21464311 := bstep (se 1 (by rfl) ⟨16098233, by rfl⟩ : syracuseStep 21464311 = 32196467) B32196467
theorem B4228793 : Blo 742328 4228793 := bstep (se 2 (by rfl) ⟨1585797, by rfl⟩ : syracuseStep 4228793 = 3171595) B3171595
theorem B1673423 : Blo 742328 1673423 := bstep (se 1 (by rfl) ⟨1255067, by rfl⟩ : syracuseStep 1673423 = 2510135) B2510135
theorem B8489933 : Blo 742328 8489933 := bstep (se 3 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 8489933 = 3183725) B3183725
theorem B24088711 : Blo 742328 24088711 := bstep (se 1 (by rfl) ⟨18066533, by rfl⟩ : syracuseStep 24088711 = 36133067) B36133067
theorem B1118375 : Blo 742328 1118375 := bstep (se 1 (by rfl) ⟨838781, by rfl⟩ : syracuseStep 1118375 = 1677563) B1677563
theorem B954607 : Blo 742328 954607 := bstep (se 1 (by rfl) ⟨715955, by rfl⟩ : syracuseStep 954607 = 1431911) B1431911
theorem B1119113 : Blo 742328 1119113 := bstep (se 2 (by rfl) ⟨419667, by rfl⟩ : syracuseStep 1119113 = 839335) B839335
theorem B3184667 : Blo 742328 3184667 := bstep (se 1 (by rfl) ⟨2388500, by rfl⟩ : syracuseStep 3184667 = 4777001) B4777001
theorem B3020921 : Blo 742328 3020921 := bstep (se 2 (by rfl) ⟨1132845, by rfl⟩ : syracuseStep 3020921 = 2265691) B2265691
theorem B5085595 : Blo 742328 5085595 := bstep (se 1 (by rfl) ⟨3814196, by rfl⟩ : syracuseStep 5085595 = 7628393) B7628393
theorem B12098587 : Blo 742328 12098587 := bstep (se 1 (by rfl) ⟨9073940, by rfl⟩ : syracuseStep 12098587 = 18147881) B18147881
theorem B3775571 : Blo 742328 3775571 := bstep (se 1 (by rfl) ⟨2831678, by rfl⟩ : syracuseStep 3775571 = 5663357) B5663357
theorem B2825725 : Blo 742328 2825725 := bstep (se 3 (by rfl) ⟨529823, by rfl⟩ : syracuseStep 2825725 = 1059647) B1059647
theorem B10329707 : Blo 742328 10329707 := bstep (se 1 (by rfl) ⟨7747280, by rfl⟩ : syracuseStep 10329707 = 15494561) B15494561
theorem B4234943 : Blo 742328 4234943 := bstep (se 1 (by rfl) ⟨3176207, by rfl⟩ : syracuseStep 4234943 = 6352415) B6352415
theorem B4761341 : Blo 742328 4761341 := bstep (se 3 (by rfl) ⟨892751, by rfl⟩ : syracuseStep 4761341 = 1785503) B1785503
theorem B23209901 : Blo 742328 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B1255783 : Blo 742328 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B1255871 : Blo 742328 1255871 := bstep (se 1 (by rfl) ⟨941903, by rfl⟩ : syracuseStep 1255871 = 1883807) B1883807
theorem B1879271 : Blo 742328 1879271 := bstep (se 1 (by rfl) ⟨1409453, by rfl⟩ : syracuseStep 1879271 = 2818907) B2818907
theorem B3224015 : Blo 742328 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B11483855 : Blo 742328 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B8043239 : Blo 742328 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B2833289 : Blo 742328 2833289 := bstep (se 2 (by rfl) ⟨1062483, by rfl⟩ : syracuseStep 2833289 = 2124967) B2124967
theorem B1883371 : Blo 742328 1883371 := bstep (se 1 (by rfl) ⟨1412528, by rfl⟩ : syracuseStep 1883371 = 2825057) B2825057
theorem B1785071 : Blo 742328 1785071 := bstep (se 1 (by rfl) ⟨1338803, by rfl⟩ : syracuseStep 1785071 = 2677607) B2677607
theorem B1884343 : Blo 742328 1884343 := bstep (se 1 (by rfl) ⟨1413257, by rfl⟩ : syracuseStep 1884343 = 2826515) B2826515
theorem B14467369 : Blo 742328 14467369 := bstep (se 2 (by rfl) ⟨5425263, by rfl⟩ : syracuseStep 14467369 = 10850527) B10850527
theorem B2507219 : Blo 742328 2507219 := bstep (se 1 (by rfl) ⟨1880414, by rfl⟩ : syracuseStep 2507219 = 3760829) B3760829
theorem B2507489 : Blo 742328 2507489 := bstep (se 2 (by rfl) ⟨940308, by rfl⟩ : syracuseStep 2507489 = 1880617) B1880617
theorem B1884991 : Blo 742328 1884991 := bstep (se 1 (by rfl) ⟨1413743, by rfl⟩ : syracuseStep 1884991 = 2827487) B2827487
theorem B9523291 : Blo 742328 9523291 := bstep (se 1 (by rfl) ⟨7142468, by rfl⟩ : syracuseStep 9523291 = 14284937) B14284937
theorem B9523655 : Blo 742328 9523655 := bstep (se 1 (by rfl) ⟨7142741, by rfl⟩ : syracuseStep 9523655 = 14285483) B14285483
theorem B4018679 : Blo 742328 4018679 := bstep (se 1 (by rfl) ⟨3014009, by rfl⟩ : syracuseStep 4018679 = 6028019) B6028019
theorem B19092509 : Blo 742328 19092509 := bstep (se 3 (by rfl) ⟨3579845, by rfl⟩ : syracuseStep 19092509 = 7159691) B7159691
theorem B742431 : Blo 742328 742431 := bstep (se 1 (by rfl) ⟨556823, by rfl⟩ : syracuseStep 742431 = 1113647) B1113647
theorem B743423 : Blo 742328 743423 := bstep (se 1 (by rfl) ⟨557567, by rfl⟩ : syracuseStep 743423 = 1115135) B1115135
theorem B743631 : Blo 742328 743631 := bstep (se 1 (by rfl) ⟨557723, by rfl⟩ : syracuseStep 743631 = 1115447) B1115447
theorem B743751 : Blo 742328 743751 := bstep (se 1 (by rfl) ⟨557813, by rfl⟩ : syracuseStep 743751 = 1115627) B1115627
theorem B2514347 : Blo 742328 2514347 := bstep (se 1 (by rfl) ⟨1885760, by rfl⟩ : syracuseStep 2514347 = 3771521) B3771521
theorem B744987 : Blo 742328 744987 := bstep (se 1 (by rfl) ⟨558740, by rfl⟩ : syracuseStep 744987 = 1117481) B1117481
theorem B745151 : Blo 742328 745151 := bstep (se 1 (by rfl) ⟨558863, by rfl⟩ : syracuseStep 745151 = 1117727) B1117727
theorem B2514671 : Blo 742328 2514671 := bstep (se 1 (by rfl) ⟨1886003, by rfl⟩ : syracuseStep 2514671 = 3772007) B3772007
theorem B745407 : Blo 742328 745407 := bstep (se 1 (by rfl) ⟨559055, by rfl⟩ : syracuseStep 745407 = 1118111) B1118111
theorem B745499 : Blo 742328 745499 := bstep (se 1 (by rfl) ⟨559124, by rfl⟩ : syracuseStep 745499 = 1118249) B1118249
theorem B745755 : Blo 742328 745755 := bstep (se 1 (by rfl) ⟨559316, by rfl⟩ : syracuseStep 745755 = 1118633) B1118633
theorem B7269821 : Blo 742328 7269821 := bstep (se 3 (by rfl) ⟨1363091, by rfl⟩ : syracuseStep 7269821 = 2726183) B2726183
theorem B2388307 : Blo 742328 2388307 := bstep (se 1 (by rfl) ⟨1791230, by rfl⟩ : syracuseStep 2388307 = 3582461) B3582461
theorem B5666273 : Blo 742328 5666273 := bstep (se 2 (by rfl) ⟨2124852, by rfl⟩ : syracuseStep 5666273 = 4249705) B4249705
theorem B1113503 : Blo 742328 1113503 := bstep (se 1 (by rfl) ⟨835127, by rfl⟩ : syracuseStep 1113503 = 1670255) B1670255
theorem B9174431 : Blo 742328 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B1113599 : Blo 742328 1113599 := bstep (se 1 (by rfl) ⟨835199, by rfl⟩ : syracuseStep 1113599 = 1670399) B1670399
theorem B1671479 : Blo 742328 1671479 := bstep (se 1 (by rfl) ⟨1253609, by rfl⟩ : syracuseStep 1671479 = 2507219) B2507219
theorem B1671659 : Blo 742328 1671659 := bstep (se 1 (by rfl) ⟨1253744, by rfl⟩ : syracuseStep 1671659 = 2507489) B2507489
theorem B2819195 : Blo 742328 2819195 := bstep (se 1 (by rfl) ⟨2114396, by rfl⟩ : syracuseStep 2819195 = 4228793) B4228793
theorem B1115615 : Blo 742328 1115615 := bstep (se 1 (by rfl) ⟨836711, by rfl⟩ : syracuseStep 1115615 = 1673423) B1673423
theorem B1674377 : Blo 742328 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B1676231 : Blo 742328 1676231 := bstep (se 1 (by rfl) ⟨1257173, by rfl⟩ : syracuseStep 1676231 = 2514347) B2514347
theorem B6886471 : Blo 742328 6886471 := bstep (se 1 (by rfl) ⟨5164853, by rfl⟩ : syracuseStep 6886471 = 10329707) B10329707
theorem B2823295 : Blo 742328 2823295 := bstep (se 1 (by rfl) ⟨2117471, by rfl⟩ : syracuseStep 2823295 = 4234943) B4234943
theorem B1676447 : Blo 742328 1676447 := bstep (se 1 (by rfl) ⟨1257335, by rfl⟩ : syracuseStep 1676447 = 2514671) B2514671
theorem B32118281 : Blo 742328 32118281 := bstep (se 2 (by rfl) ⟨12044355, by rfl⟩ : syracuseStep 32118281 = 24088711) B24088711
theorem B3184409 : Blo 742328 3184409 := bstep (se 2 (by rfl) ⟨1194153, by rfl⟩ : syracuseStep 3184409 = 2388307) B2388307
theorem B15473267 : Blo 742328 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B1252847 : Blo 742328 1252847 := bstep (se 1 (by rfl) ⟨939635, by rfl⟩ : syracuseStep 1252847 = 1879271) B1879271
theorem B3777515 : Blo 742328 3777515 := bstep (se 1 (by rfl) ⟨2833136, by rfl⟩ : syracuseStep 3777515 = 5666273) B5666273
theorem B16131449 : Blo 742328 16131449 := bstep (se 2 (by rfl) ⟨6049293, by rfl⟩ : syracuseStep 16131449 = 12098587) B12098587
theorem B1190047 : Blo 742328 1190047 := bstep (se 1 (by rfl) ⟨892535, by rfl⟩ : syracuseStep 1190047 = 1785071) B1785071
theorem B28619081 : Blo 742328 28619081 := bstep (se 2 (by rfl) ⟨10732155, by rfl⟩ : syracuseStep 28619081 = 21464311) B21464311
theorem B12728339 : Blo 742328 12728339 := bstep (se 1 (by rfl) ⟨9546254, by rfl⟩ : syracuseStep 12728339 = 19092509) B19092509
theorem B2013947 : Blo 742328 2013947 := bstep (se 1 (by rfl) ⟨1510460, by rfl⟩ : syracuseStep 2013947 = 3020921) B3020921
theorem B12697721 : Blo 742328 12697721 := bstep (se 2 (by rfl) ⟨4761645, by rfl⟩ : syracuseStep 12697721 = 9523291) B9523291
theorem B837247 : Blo 742328 837247 := bstep (se 1 (by rfl) ⟨627935, by rfl⟩ : syracuseStep 837247 = 1255871) B1255871
theorem B2149343 : Blo 742328 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B24465149 : Blo 742328 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B2511161 : Blo 742328 2511161 := bstep (se 2 (by rfl) ⟨941685, by rfl⟩ : syracuseStep 2511161 = 1883371) B1883371
theorem B7655903 : Blo 742328 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B5362159 : Blo 742328 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B1888859 : Blo 742328 1888859 := bstep (se 1 (by rfl) ⟨1416644, by rfl⟩ : syracuseStep 1888859 = 2833289) B2833289
theorem B742335 : Blo 742328 742335 := bstep (se 1 (by rfl) ⟨556751, by rfl⟩ : syracuseStep 742335 = 1113503) B1113503
theorem B742399 : Blo 742328 742399 := bstep (se 1 (by rfl) ⟨556799, by rfl⟩ : syracuseStep 742399 = 1113599) B1113599
theorem B2512457 : Blo 742328 2512457 := bstep (se 2 (by rfl) ⟨942171, by rfl⟩ : syracuseStep 2512457 = 1884343) B1884343
theorem B19289825 : Blo 742328 19289825 := bstep (se 2 (by rfl) ⟨7233684, by rfl⟩ : syracuseStep 19289825 = 14467369) B14467369
theorem B2513321 : Blo 742328 2513321 := bstep (se 2 (by rfl) ⟨942495, by rfl⟩ : syracuseStep 2513321 = 1884991) B1884991
theorem B5659955 : Blo 742328 5659955 := bstep (se 1 (by rfl) ⟨4244966, by rfl⟩ : syracuseStep 5659955 = 8489933) B8489933
theorem B27123173 : Blo 742328 27123173 := bstep (se 4 (by rfl) ⟨2542797, by rfl⟩ : syracuseStep 27123173 = 5085595) B5085595
theorem B745583 : Blo 742328 745583 := bstep (se 1 (by rfl) ⟨559187, by rfl⟩ : syracuseStep 745583 = 1118375) B1118375
theorem B6349103 : Blo 742328 6349103 := bstep (se 1 (by rfl) ⟨4761827, by rfl⟩ : syracuseStep 6349103 = 9523655) B9523655
theorem B2679119 : Blo 742328 2679119 := bstep (se 1 (by rfl) ⟨2009339, by rfl⟩ : syracuseStep 2679119 = 4018679) B4018679
theorem B746075 : Blo 742328 746075 := bstep (se 1 (by rfl) ⟨559556, by rfl⟩ : syracuseStep 746075 = 1119113) B1119113
theorem B2123111 : Blo 742328 2123111 := bstep (se 1 (by rfl) ⟨1592333, by rfl⟩ : syracuseStep 2123111 = 3184667) B3184667
theorem B2517047 : Blo 742328 2517047 := bstep (se 1 (by rfl) ⟨1887785, by rfl⟩ : syracuseStep 2517047 = 3775571) B3775571
theorem B1272809 : Blo 742328 1272809 := bstep (se 2 (by rfl) ⟨477303, by rfl⟩ : syracuseStep 1272809 = 954607) B954607
theorem B3174227 : Blo 742328 3174227 := bstep (se 1 (by rfl) ⟨2380670, by rfl⟩ : syracuseStep 3174227 = 4761341) B4761341
theorem B4846547 : Blo 742328 4846547 := bstep (se 1 (by rfl) ⟨3634910, by rfl⟩ : syracuseStep 4846547 = 7269821) B7269821
theorem B3767633 : Blo 742328 3767633 := bstep (se 2 (by rfl) ⟨1412862, by rfl⟩ : syracuseStep 3767633 = 2825725) B2825725
theorem B1114319 : Blo 742328 1114319 := bstep (se 1 (by rfl) ⟨835739, by rfl⟩ : syracuseStep 1114319 = 1671479) B1671479
theorem B1114439 : Blo 742328 1114439 := bstep (se 1 (by rfl) ⟨835829, by rfl⟩ : syracuseStep 1114439 = 1671659) B1671659
theorem B1116251 : Blo 742328 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B1116329 : Blo 742328 1116329 := bstep (se 2 (by rfl) ⟨418623, by rfl⟩ : syracuseStep 1116329 = 837247) B837247
theorem B1674107 : Blo 742328 1674107 := bstep (se 1 (by rfl) ⟨1255580, by rfl⟩ : syracuseStep 1674107 = 2511161) B2511161
theorem B1117487 : Blo 742328 1117487 := bstep (se 1 (by rfl) ⟨838115, by rfl⟩ : syracuseStep 1117487 = 1676231) B1676231
theorem B1117631 : Blo 742328 1117631 := bstep (se 1 (by rfl) ⟨838223, by rfl⟩ : syracuseStep 1117631 = 1676447) B1676447
theorem B1674971 : Blo 742328 1674971 := bstep (se 1 (by rfl) ⟨1256228, by rfl⟩ : syracuseStep 1674971 = 2512457) B2512457
theorem B1675547 : Blo 742328 1675547 := bstep (se 1 (by rfl) ⟨1256660, by rfl⟩ : syracuseStep 1675547 = 2513321) B2513321
theorem B3773303 : Blo 742328 3773303 := bstep (se 1 (by rfl) ⟨2829977, by rfl⟩ : syracuseStep 3773303 = 5659955) B5659955
theorem B4232735 : Blo 742328 4232735 := bstep (se 1 (by rfl) ⟨3174551, by rfl⟩ : syracuseStep 4232735 = 6349103) B6349103
theorem B7149545 : Blo 742328 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B1415407 : Blo 742328 1415407 := bstep (se 1 (by rfl) ⟨1061555, by rfl⟩ : syracuseStep 1415407 = 2123111) B2123111
theorem B10754299 : Blo 742328 10754299 := bstep (se 1 (by rfl) ⟨8065724, by rfl⟩ : syracuseStep 10754299 = 16131449) B16131449
theorem B1678031 : Blo 742328 1678031 := bstep (se 1 (by rfl) ⟨1258523, by rfl⟩ : syracuseStep 1678031 = 2517047) B2517047
theorem B9181961 : Blo 742328 9181961 := bstep (se 2 (by rfl) ⟨3443235, by rfl⟩ : syracuseStep 9181961 = 6886471) B6886471
theorem B19079387 : Blo 742328 19079387 := bstep (se 1 (by rfl) ⟨14309540, by rfl⟩ : syracuseStep 19079387 = 28619081) B28619081
theorem B8465147 : Blo 742328 8465147 := bstep (se 1 (by rfl) ⟨6348860, by rfl⟩ : syracuseStep 8465147 = 12697721) B12697721
theorem B1879463 : Blo 742328 1879463 := bstep (se 1 (by rfl) ⟨1409597, by rfl⟩ : syracuseStep 1879463 = 2819195) B2819195
theorem B1586729 : Blo 742328 1586729 := bstep (se 2 (by rfl) ⟨595023, by rfl⟩ : syracuseStep 1586729 = 1190047) B1190047
theorem B1259239 : Blo 742328 1259239 := bstep (se 1 (by rfl) ⟨944429, by rfl⟩ : syracuseStep 1259239 = 1888859) B1888859
theorem B21412187 : Blo 742328 21412187 := bstep (se 1 (by rfl) ⟨16059140, by rfl⟩ : syracuseStep 21412187 = 32118281) B32118281
theorem B12859883 : Blo 742328 12859883 := bstep (se 1 (by rfl) ⟨9644912, by rfl⟩ : syracuseStep 12859883 = 19289825) B19289825
theorem B835231 : Blo 742328 835231 := bstep (se 1 (by rfl) ⟨626423, by rfl⟩ : syracuseStep 835231 = 1252847) B1252847
theorem B1786079 : Blo 742328 1786079 := bstep (se 1 (by rfl) ⟨1339559, by rfl⟩ : syracuseStep 1786079 = 2679119) B2679119
theorem B2116151 : Blo 742328 2116151 := bstep (se 1 (by rfl) ⟨1587113, by rfl⟩ : syracuseStep 2116151 = 3174227) B3174227
theorem B3231031 : Blo 742328 3231031 := bstep (se 1 (by rfl) ⟨2423273, by rfl⟩ : syracuseStep 3231031 = 4846547) B4846547
theorem B2511755 : Blo 742328 2511755 := bstep (se 1 (by rfl) ⟨1883816, by rfl⟩ : syracuseStep 2511755 = 3767633) B3767633
theorem B743743 : Blo 742328 743743 := bstep (se 1 (by rfl) ⟨557807, by rfl⟩ : syracuseStep 743743 = 1115615) B1115615
theorem B1432895 : Blo 742328 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B16310099 : Blo 742328 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B5103935 : Blo 742328 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B2122939 : Blo 742328 2122939 := bstep (se 1 (by rfl) ⟨1592204, by rfl⟩ : syracuseStep 2122939 = 3184409) B3184409
theorem B10315511 : Blo 742328 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B18082115 : Blo 742328 18082115 := bstep (se 1 (by rfl) ⟨13561586, by rfl⟩ : syracuseStep 18082115 = 27123173) B27123173
theorem B2518343 : Blo 742328 2518343 := bstep (se 1 (by rfl) ⟨1888757, by rfl⟩ : syracuseStep 2518343 = 3777515) B3777515
theorem B3764393 : Blo 742328 3764393 := bstep (se 2 (by rfl) ⟨1411647, by rfl⟩ : syracuseStep 3764393 = 2823295) B2823295
theorem B848539 : Blo 742328 848539 := bstep (se 1 (by rfl) ⟨636404, by rfl⟩ : syracuseStep 848539 = 1272809) B1272809
theorem B8485559 : Blo 742328 8485559 := bstep (se 1 (by rfl) ⟨6364169, by rfl⟩ : syracuseStep 8485559 = 12728339) B12728339
theorem B1342631 : Blo 742328 1342631 := bstep (se 1 (by rfl) ⟨1006973, by rfl⟩ : syracuseStep 1342631 = 2013947) B2013947
theorem B1410767 : Blo 742328 1410767 := bstep (se 1 (by rfl) ⟨1058075, by rfl⟩ : syracuseStep 1410767 = 2116151) B2116151
theorem B1116071 : Blo 742328 1116071 := bstep (se 1 (by rfl) ⟨837053, by rfl⟩ : syracuseStep 1116071 = 1674107) B1674107
theorem B1116647 : Blo 742328 1116647 := bstep (se 1 (by rfl) ⟨837485, by rfl⟩ : syracuseStep 1116647 = 1674971) B1674971
theorem B1117031 : Blo 742328 1117031 := bstep (se 1 (by rfl) ⟨837773, by rfl⟩ : syracuseStep 1117031 = 1675547) B1675547
theorem B1674503 : Blo 742328 1674503 := bstep (se 1 (by rfl) ⟨1255877, by rfl⟩ : syracuseStep 1674503 = 2511755) B2511755
theorem B4525541 : Blo 742328 4525541 := bstep (se 4 (by rfl) ⟨424269, by rfl⟩ : syracuseStep 4525541 = 848539) B848539
theorem B2821823 : Blo 742328 2821823 := bstep (se 1 (by rfl) ⟨2116367, by rfl⟩ : syracuseStep 2821823 = 4232735) B4232735
theorem B4231277 : Blo 742328 4231277 := bstep (se 3 (by rfl) ⟨793364, by rfl⟩ : syracuseStep 4231277 = 1586729) B1586729
theorem B1118687 : Blo 742328 1118687 := bstep (se 1 (by rfl) ⟨839015, by rfl⟩ : syracuseStep 1118687 = 1678031) B1678031
theorem B12719591 : Blo 742328 12719591 := bstep (se 1 (by rfl) ⟨9539693, by rfl⟩ : syracuseStep 12719591 = 19079387) B19079387
theorem B5643431 : Blo 742328 5643431 := bstep (se 1 (by rfl) ⟨4232573, by rfl⟩ : syracuseStep 5643431 = 8465147) B8465147
theorem B1678895 : Blo 742328 1678895 := bstep (se 1 (by rfl) ⟨1259171, by rfl⟩ : syracuseStep 1678895 = 2518343) B2518343
theorem B1252975 : Blo 742328 1252975 := bstep (se 1 (by rfl) ⟨939731, by rfl⟩ : syracuseStep 1252975 = 1879463) B1879463
theorem B1678985 : Blo 742328 1678985 := bstep (se 2 (by rfl) ⟨629619, by rfl⟩ : syracuseStep 1678985 = 1259239) B1259239
theorem B895087 : Blo 742328 895087 := bstep (se 1 (by rfl) ⟨671315, by rfl⟩ : syracuseStep 895087 = 1342631) B1342631
theorem B1190719 : Blo 742328 1190719 := bstep (se 1 (by rfl) ⟨893039, by rfl⟩ : syracuseStep 1190719 = 1786079) B1786079
theorem B2830585 : Blo 742328 2830585 := bstep (se 2 (by rfl) ⟨1061469, by rfl⟩ : syracuseStep 2830585 = 2122939) B2122939
theorem B15284213 : Blo 742328 15284213 := bstep (se 5 (by rfl) ⟨716447, by rfl⟩ : syracuseStep 15284213 = 1432895) B1432895
theorem B4766363 : Blo 742328 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B4308041 : Blo 742328 4308041 := bstep (se 2 (by rfl) ⟨1615515, by rfl⟩ : syracuseStep 4308041 = 3231031) B3231031
theorem B2509595 : Blo 742328 2509595 := bstep (se 1 (by rfl) ⟨1882196, by rfl⟩ : syracuseStep 2509595 = 3764393) B3764393
theorem B1887209 : Blo 742328 1887209 := bstep (se 2 (by rfl) ⟨707703, by rfl⟩ : syracuseStep 1887209 = 1415407) B1415407
theorem B14339065 : Blo 742328 14339065 := bstep (se 2 (by rfl) ⟨5377149, by rfl⟩ : syracuseStep 14339065 = 10754299) B10754299
theorem B14274791 : Blo 742328 14274791 := bstep (se 1 (by rfl) ⟨10706093, by rfl⟩ : syracuseStep 14274791 = 21412187) B21412187
theorem B8573255 : Blo 742328 8573255 := bstep (se 1 (by rfl) ⟨6429941, by rfl⟩ : syracuseStep 8573255 = 12859883) B12859883
theorem B5657039 : Blo 742328 5657039 := bstep (se 1 (by rfl) ⟨4242779, by rfl⟩ : syracuseStep 5657039 = 8485559) B8485559
theorem B742879 : Blo 742328 742879 := bstep (se 1 (by rfl) ⟨557159, by rfl⟩ : syracuseStep 742879 = 1114319) B1114319
theorem B742959 : Blo 742328 742959 := bstep (se 1 (by rfl) ⟨557219, by rfl⟩ : syracuseStep 742959 = 1114439) B1114439
theorem B744167 : Blo 742328 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B744219 : Blo 742328 744219 := bstep (se 1 (by rfl) ⟨558164, by rfl⟩ : syracuseStep 744219 = 1116329) B1116329
theorem B744991 : Blo 742328 744991 := bstep (se 1 (by rfl) ⟨558743, by rfl⟩ : syracuseStep 744991 = 1117487) B1117487
theorem B745087 : Blo 742328 745087 := bstep (se 1 (by rfl) ⟨558815, by rfl⟩ : syracuseStep 745087 = 1117631) B1117631
theorem B2515535 : Blo 742328 2515535 := bstep (se 1 (by rfl) ⟨1886651, by rfl⟩ : syracuseStep 2515535 = 3773303) B3773303
theorem B6121307 : Blo 742328 6121307 := bstep (se 1 (by rfl) ⟨4590980, by rfl⟩ : syracuseStep 6121307 = 9181961) B9181961
theorem B10873399 : Blo 742328 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B3402623 : Blo 742328 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B6877007 : Blo 742328 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B12054743 : Blo 742328 12054743 := bstep (se 1 (by rfl) ⟨9041057, by rfl⟩ : syracuseStep 12054743 = 18082115) B18082115
theorem B1113641 : Blo 742328 1113641 := bstep (se 2 (by rfl) ⟨417615, by rfl⟩ : syracuseStep 1113641 = 835231) B835231
theorem B1673063 : Blo 742328 1673063 := bstep (se 1 (by rfl) ⟨1254797, by rfl⟩ : syracuseStep 1673063 = 2509595) B2509595
theorem B1116335 : Blo 742328 1116335 := bstep (se 1 (by rfl) ⟨837251, by rfl⟩ : syracuseStep 1116335 = 1674503) B1674503
theorem B3017027 : Blo 742328 3017027 := bstep (se 1 (by rfl) ⟨2262770, by rfl⟩ : syracuseStep 3017027 = 4525541) B4525541
theorem B2820851 : Blo 742328 2820851 := bstep (se 1 (by rfl) ⟨2115638, by rfl⟩ : syracuseStep 2820851 = 4231277) B4231277
theorem B3771359 : Blo 742328 3771359 := bstep (se 1 (by rfl) ⟨2828519, by rfl⟩ : syracuseStep 3771359 = 5657039) B5657039
theorem B1119263 : Blo 742328 1119263 := bstep (se 1 (by rfl) ⟨839447, by rfl⟩ : syracuseStep 1119263 = 1678895) B1678895
theorem B1119323 : Blo 742328 1119323 := bstep (se 1 (by rfl) ⟨839492, by rfl⟩ : syracuseStep 1119323 = 1678985) B1678985
theorem B3774113 : Blo 742328 3774113 := bstep (se 2 (by rfl) ⟨1415292, by rfl⟩ : syracuseStep 3774113 = 2830585) B2830585
theorem B1677023 : Blo 742328 1677023 := bstep (se 1 (by rfl) ⟨1257767, by rfl⟩ : syracuseStep 1677023 = 2515535) B2515535
theorem B2268415 : Blo 742328 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B8036495 : Blo 742328 8036495 := bstep (se 1 (by rfl) ⟨6027371, by rfl⟩ : syracuseStep 8036495 = 12054743) B12054743
theorem B1258139 : Blo 742328 1258139 := bstep (se 1 (by rfl) ⟨943604, by rfl⟩ : syracuseStep 1258139 = 1887209) B1887209
theorem B1881215 : Blo 742328 1881215 := bstep (se 1 (by rfl) ⟨1410911, by rfl⟩ : syracuseStep 1881215 = 2821823) B2821823
theorem B1193449 : Blo 742328 1193449 := bstep (se 2 (by rfl) ⟨447543, by rfl⟩ : syracuseStep 1193449 = 895087) B895087
theorem B9516527 : Blo 742328 9516527 := bstep (se 1 (by rfl) ⟨7137395, by rfl⟩ : syracuseStep 9516527 = 14274791) B14274791
theorem B5715503 : Blo 742328 5715503 := bstep (se 1 (by rfl) ⟨4286627, by rfl⟩ : syracuseStep 5715503 = 8573255) B8573255
theorem B14497865 : Blo 742328 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B19118753 : Blo 742328 19118753 := bstep (se 2 (by rfl) ⟨7169532, by rfl⟩ : syracuseStep 19118753 = 14339065) B14339065
theorem B4080871 : Blo 742328 4080871 := bstep (se 1 (by rfl) ⟨3060653, by rfl⟩ : syracuseStep 4080871 = 6121307) B6121307
theorem B2872027 : Blo 742328 2872027 := bstep (se 1 (by rfl) ⟨2154020, by rfl⟩ : syracuseStep 2872027 = 4308041) B4308041
theorem B742427 : Blo 742328 742427 := bstep (se 1 (by rfl) ⟨556820, by rfl⟩ : syracuseStep 742427 = 1113641) B1113641
theorem B940511 : Blo 742328 940511 := bstep (se 1 (by rfl) ⟨705383, by rfl⟩ : syracuseStep 940511 = 1410767) B1410767
theorem B744047 : Blo 742328 744047 := bstep (se 1 (by rfl) ⟨558035, by rfl⟩ : syracuseStep 744047 = 1116071) B1116071
theorem B744431 : Blo 742328 744431 := bstep (se 1 (by rfl) ⟨558323, by rfl⟩ : syracuseStep 744431 = 1116647) B1116647
theorem B744687 : Blo 742328 744687 := bstep (se 1 (by rfl) ⟨558515, by rfl⟩ : syracuseStep 744687 = 1117031) B1117031
theorem B745791 : Blo 742328 745791 := bstep (se 1 (by rfl) ⟨559343, by rfl⟩ : syracuseStep 745791 = 1118687) B1118687
theorem B8479727 : Blo 742328 8479727 := bstep (se 1 (by rfl) ⟨6359795, by rfl⟩ : syracuseStep 8479727 = 12719591) B12719591
theorem B6350501 : Blo 742328 6350501 := bstep (se 4 (by rfl) ⟨595359, by rfl⟩ : syracuseStep 6350501 = 1190719) B1190719
theorem B3762287 : Blo 742328 3762287 := bstep (se 1 (by rfl) ⟨2821715, by rfl⟩ : syracuseStep 3762287 = 5643431) B5643431
theorem B4584671 : Blo 742328 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B10189475 : Blo 742328 10189475 := bstep (se 1 (by rfl) ⟨7642106, by rfl⟩ : syracuseStep 10189475 = 15284213) B15284213
theorem B3177575 : Blo 742328 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B1670633 : Blo 742328 1670633 := bstep (se 2 (by rfl) ⟨626487, by rfl⟩ : syracuseStep 1670633 = 1252975) B1252975
theorem B1115375 : Blo 742328 1115375 := bstep (se 1 (by rfl) ⟨836531, by rfl⟩ : syracuseStep 1115375 = 1673063) B1673063
theorem B1118015 : Blo 742328 1118015 := bstep (se 1 (by rfl) ⟨838511, by rfl⟩ : syracuseStep 1118015 = 1677023) B1677023
theorem B4233667 : Blo 742328 4233667 := bstep (se 1 (by rfl) ⟨3175250, by rfl⟩ : syracuseStep 4233667 = 6350501) B6350501
theorem B21764645 : Blo 742328 21764645 := bstep (se 4 (by rfl) ⟨2040435, by rfl⟩ : syracuseStep 21764645 = 4080871) B4080871
theorem B1254143 : Blo 742328 1254143 := bstep (se 1 (by rfl) ⟨940607, by rfl⟩ : syracuseStep 1254143 = 1881215) B1881215
theorem B3056447 : Blo 742328 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B3810335 : Blo 742328 3810335 := bstep (se 1 (by rfl) ⟨2857751, by rfl⟩ : syracuseStep 3810335 = 5715503) B5715503
theorem B3024553 : Blo 742328 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B6792983 : Blo 742328 6792983 := bstep (se 1 (by rfl) ⟨5094737, by rfl⟩ : syracuseStep 6792983 = 10189475) B10189475
theorem B1880567 : Blo 742328 1880567 := bstep (se 1 (by rfl) ⟨1410425, by rfl⟩ : syracuseStep 1880567 = 2820851) B2820851
theorem B5357663 : Blo 742328 5357663 := bstep (se 1 (by rfl) ⟨4018247, by rfl⟩ : syracuseStep 5357663 = 8036495) B8036495
theorem B5653151 : Blo 742328 5653151 := bstep (se 1 (by rfl) ⟨4239863, by rfl⟩ : syracuseStep 5653151 = 8479727) B8479727
theorem B8045405 : Blo 742328 8045405 := bstep (se 3 (by rfl) ⟨1508513, by rfl⟩ : syracuseStep 8045405 = 3017027) B3017027
theorem B2508029 : Blo 742328 2508029 := bstep (se 3 (by rfl) ⟨470255, by rfl⟩ : syracuseStep 2508029 = 940511) B940511
theorem B2508191 : Blo 742328 2508191 := bstep (se 1 (by rfl) ⟨1881143, by rfl⟩ : syracuseStep 2508191 = 3762287) B3762287
theorem B1591265 : Blo 742328 1591265 := bstep (se 2 (by rfl) ⟨596724, by rfl⟩ : syracuseStep 1591265 = 1193449) B1193449
theorem B838759 : Blo 742328 838759 := bstep (se 1 (by rfl) ⟨629069, by rfl⟩ : syracuseStep 838759 = 1258139) B1258139
theorem B6344351 : Blo 742328 6344351 := bstep (se 1 (by rfl) ⟨4758263, by rfl⟩ : syracuseStep 6344351 = 9516527) B9516527
theorem B2118383 : Blo 742328 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B744223 : Blo 742328 744223 := bstep (se 1 (by rfl) ⟨558167, by rfl⟩ : syracuseStep 744223 = 1116335) B1116335
theorem B2514239 : Blo 742328 2514239 := bstep (se 1 (by rfl) ⟨1885679, by rfl⟩ : syracuseStep 2514239 = 3771359) B3771359
theorem B746175 : Blo 742328 746175 := bstep (se 1 (by rfl) ⟨559631, by rfl⟩ : syracuseStep 746175 = 1119263) B1119263
theorem B746215 : Blo 742328 746215 := bstep (se 1 (by rfl) ⟨559661, by rfl⟩ : syracuseStep 746215 = 1119323) B1119323
theorem B2516075 : Blo 742328 2516075 := bstep (se 1 (by rfl) ⟨1887056, by rfl⟩ : syracuseStep 2516075 = 3774113) B3774113
theorem B3829369 : Blo 742328 3829369 := bstep (se 2 (by rfl) ⟨1436013, by rfl⟩ : syracuseStep 3829369 = 2872027) B2872027
theorem B9665243 : Blo 742328 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B12745835 : Blo 742328 12745835 := bstep (se 1 (by rfl) ⟨9559376, by rfl⟩ : syracuseStep 12745835 = 19118753) B19118753
theorem B1113755 : Blo 742328 1113755 := bstep (se 1 (by rfl) ⟨835316, by rfl⟩ : syracuseStep 1113755 = 1670633) B1670633
theorem B3571775 : Blo 742328 3571775 := bstep (se 1 (by rfl) ⟨2678831, by rfl⟩ : syracuseStep 3571775 = 5357663) B5357663
theorem B3768767 : Blo 742328 3768767 := bstep (se 1 (by rfl) ⟨2826575, by rfl⟩ : syracuseStep 3768767 = 5653151) B5653151
theorem B1672019 : Blo 742328 1672019 := bstep (se 1 (by rfl) ⟨1254014, by rfl⟩ : syracuseStep 1672019 = 2508029) B2508029
theorem B1672127 : Blo 742328 1672127 := bstep (se 1 (by rfl) ⟨1254095, by rfl⟩ : syracuseStep 1672127 = 2508191) B2508191
theorem B4032737 : Blo 742328 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B4229567 : Blo 742328 4229567 := bstep (se 1 (by rfl) ⟨3172175, by rfl⟩ : syracuseStep 4229567 = 6344351) B6344351
theorem B10160893 : Blo 742328 10160893 := bstep (se 3 (by rfl) ⟨1905167, by rfl⟩ : syracuseStep 10160893 = 3810335) B3810335
theorem B1412255 : Blo 742328 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B1118345 : Blo 742328 1118345 := bstep (se 2 (by rfl) ⟨419379, by rfl⟩ : syracuseStep 1118345 = 838759) B838759
theorem B1676159 : Blo 742328 1676159 := bstep (se 1 (by rfl) ⟨1257119, by rfl⟩ : syracuseStep 1676159 = 2514239) B2514239
theorem B2037631 : Blo 742328 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B1677383 : Blo 742328 1677383 := bstep (se 1 (by rfl) ⟨1258037, by rfl⟩ : syracuseStep 1677383 = 2516075) B2516075
theorem B4528655 : Blo 742328 4528655 := bstep (se 1 (by rfl) ⟨3396491, by rfl⟩ : syracuseStep 4528655 = 6792983) B6792983
theorem B1253711 : Blo 742328 1253711 := bstep (se 1 (by rfl) ⟨940283, by rfl⟩ : syracuseStep 1253711 = 1880567) B1880567
theorem B5644889 : Blo 742328 5644889 := bstep (se 2 (by rfl) ⟨2116833, by rfl⟩ : syracuseStep 5644889 = 4233667) B4233667
theorem B8497223 : Blo 742328 8497223 := bstep (se 1 (by rfl) ⟨6372917, by rfl⟩ : syracuseStep 8497223 = 12745835) B12745835
theorem B4243373 : Blo 742328 4243373 := bstep (se 3 (by rfl) ⟨795632, by rfl⟩ : syracuseStep 4243373 = 1591265) B1591265
theorem B836095 : Blo 742328 836095 := bstep (se 1 (by rfl) ⟨627071, by rfl⟩ : syracuseStep 836095 = 1254143) B1254143
theorem B6443495 : Blo 742328 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B742503 : Blo 742328 742503 := bstep (se 1 (by rfl) ⟨556877, by rfl⟩ : syracuseStep 742503 = 1113755) B1113755
theorem B5363603 : Blo 742328 5363603 := bstep (se 1 (by rfl) ⟨4022702, by rfl⟩ : syracuseStep 5363603 = 8045405) B8045405
theorem B743583 : Blo 742328 743583 := bstep (se 1 (by rfl) ⟨557687, by rfl⟩ : syracuseStep 743583 = 1115375) B1115375
theorem B745343 : Blo 742328 745343 := bstep (se 1 (by rfl) ⟨559007, by rfl⟩ : syracuseStep 745343 = 1118015) B1118015
theorem B14509763 : Blo 742328 14509763 := bstep (se 1 (by rfl) ⟨10882322, by rfl⟩ : syracuseStep 14509763 = 21764645) B21764645
theorem B5105825 : Blo 742328 5105825 := bstep (se 2 (by rfl) ⟨1914684, by rfl⟩ : syracuseStep 5105825 = 3829369) B3829369
theorem B1114679 : Blo 742328 1114679 := bstep (se 1 (by rfl) ⟨836009, by rfl⟩ : syracuseStep 1114679 = 1672019) B1672019
theorem B1114751 : Blo 742328 1114751 := bstep (se 1 (by rfl) ⟨836063, by rfl⟩ : syracuseStep 1114751 = 1672127) B1672127
theorem B1114793 : Blo 742328 1114793 := bstep (se 2 (by rfl) ⟨418047, by rfl⟩ : syracuseStep 1114793 = 836095) B836095
theorem B2688491 : Blo 742328 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B2819711 : Blo 742328 2819711 := bstep (se 1 (by rfl) ⟨2114783, by rfl⟩ : syracuseStep 2819711 = 4229567) B4229567
theorem B4295663 : Blo 742328 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B1117439 : Blo 742328 1117439 := bstep (se 1 (by rfl) ⟨838079, by rfl⟩ : syracuseStep 1117439 = 1676159) B1676159
theorem B3575735 : Blo 742328 3575735 := bstep (se 1 (by rfl) ⟨2681801, by rfl⟩ : syracuseStep 3575735 = 5363603) B5363603
theorem B1118255 : Blo 742328 1118255 := bstep (se 1 (by rfl) ⟨838691, by rfl⟩ : syracuseStep 1118255 = 1677383) B1677383
theorem B3019103 : Blo 742328 3019103 := bstep (se 1 (by rfl) ⟨2264327, by rfl⟩ : syracuseStep 3019103 = 4528655) B4528655
theorem B9673175 : Blo 742328 9673175 := bstep (se 1 (by rfl) ⟨7254881, by rfl⟩ : syracuseStep 9673175 = 14509763) B14509763
theorem B2828915 : Blo 742328 2828915 := bstep (se 1 (by rfl) ⟨2121686, by rfl⟩ : syracuseStep 2828915 = 4243373) B4243373
theorem B13547857 : Blo 742328 13547857 := bstep (se 2 (by rfl) ⟨5080446, by rfl⟩ : syracuseStep 13547857 = 10160893) B10160893
theorem B835807 : Blo 742328 835807 := bstep (se 1 (by rfl) ⟨626855, by rfl⟩ : syracuseStep 835807 = 1253711) B1253711
theorem B2381183 : Blo 742328 2381183 := bstep (se 1 (by rfl) ⟨1785887, by rfl⟩ : syracuseStep 2381183 = 3571775) B3571775
theorem B2512511 : Blo 742328 2512511 := bstep (se 1 (by rfl) ⟨1884383, by rfl⟩ : syracuseStep 2512511 = 3768767) B3768767
theorem B745563 : Blo 742328 745563 := bstep (se 1 (by rfl) ⟨559172, by rfl⟩ : syracuseStep 745563 = 1118345) B1118345
theorem B3763259 : Blo 742328 3763259 := bstep (se 1 (by rfl) ⟨2822444, by rfl⟩ : syracuseStep 3763259 = 5644889) B5644889
theorem B5664815 : Blo 742328 5664815 := bstep (se 1 (by rfl) ⟨4248611, by rfl⟩ : syracuseStep 5664815 = 8497223) B8497223
theorem B3403883 : Blo 742328 3403883 := bstep (se 1 (by rfl) ⟨2552912, by rfl⟩ : syracuseStep 3403883 = 5105825) B5105825
theorem B2716841 : Blo 742328 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B3766013 : Blo 742328 3766013 := bstep (se 3 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 3766013 = 1412255) B1412255
theorem B9077021 : Blo 742328 9077021 := bstep (se 3 (by rfl) ⟨1701941, by rfl⟩ : syracuseStep 9077021 = 3403883) B3403883
theorem B1114409 : Blo 742328 1114409 := bstep (se 2 (by rfl) ⟨417903, by rfl⟩ : syracuseStep 1114409 = 835807) B835807
theorem B7244909 : Blo 742328 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B1675007 : Blo 742328 1675007 := bstep (se 1 (by rfl) ⟨1256255, by rfl⟩ : syracuseStep 1675007 = 2512511) B2512511
theorem B3776543 : Blo 742328 3776543 := bstep (se 1 (by rfl) ⟨2832407, by rfl⟩ : syracuseStep 3776543 = 5664815) B5664815
theorem B18063809 : Blo 742328 18063809 := bstep (se 2 (by rfl) ⟨6773928, by rfl⟩ : syracuseStep 18063809 = 13547857) B13547857
theorem B1879807 : Blo 742328 1879807 := bstep (se 1 (by rfl) ⟨1409855, by rfl⟩ : syracuseStep 1879807 = 2819711) B2819711
theorem B2863775 : Blo 742328 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B2012735 : Blo 742328 2012735 := bstep (se 1 (by rfl) ⟨1509551, by rfl⟩ : syracuseStep 2012735 = 3019103) B3019103
theorem B1587455 : Blo 742328 1587455 := bstep (se 1 (by rfl) ⟨1190591, by rfl⟩ : syracuseStep 1587455 = 2381183) B2381183
theorem B1885943 : Blo 742328 1885943 := bstep (se 1 (by rfl) ⟨1414457, by rfl⟩ : syracuseStep 1885943 = 2828915) B2828915
theorem B2508839 : Blo 742328 2508839 := bstep (se 1 (by rfl) ⟨1881629, by rfl⟩ : syracuseStep 2508839 = 3763259) B3763259
theorem B2510675 : Blo 742328 2510675 := bstep (se 1 (by rfl) ⟨1883006, by rfl⟩ : syracuseStep 2510675 = 3766013) B3766013
theorem B743119 : Blo 742328 743119 := bstep (se 1 (by rfl) ⟨557339, by rfl⟩ : syracuseStep 743119 = 1114679) B1114679
theorem B743167 : Blo 742328 743167 := bstep (se 1 (by rfl) ⟨557375, by rfl⟩ : syracuseStep 743167 = 1114751) B1114751
theorem B743195 : Blo 742328 743195 := bstep (se 1 (by rfl) ⟨557396, by rfl⟩ : syracuseStep 743195 = 1114793) B1114793
theorem B1792327 : Blo 742328 1792327 := bstep (se 1 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 1792327 = 2688491) B2688491
theorem B744959 : Blo 742328 744959 := bstep (se 1 (by rfl) ⟨558719, by rfl⟩ : syracuseStep 744959 = 1117439) B1117439
theorem B2383823 : Blo 742328 2383823 := bstep (se 1 (by rfl) ⟨1787867, by rfl⟩ : syracuseStep 2383823 = 3575735) B3575735
theorem B745503 : Blo 742328 745503 := bstep (se 1 (by rfl) ⟨559127, by rfl⟩ : syracuseStep 745503 = 1118255) B1118255
theorem B6448783 : Blo 742328 6448783 := bstep (se 1 (by rfl) ⟨4836587, by rfl⟩ : syracuseStep 6448783 = 9673175) B9673175
theorem B1672559 : Blo 742328 1672559 := bstep (se 1 (by rfl) ⟨1254419, by rfl⟩ : syracuseStep 1672559 = 2508839) B2508839
theorem B1116671 : Blo 742328 1116671 := bstep (se 1 (by rfl) ⟨837503, by rfl⟩ : syracuseStep 1116671 = 1675007) B1675007
theorem B1673783 : Blo 742328 1673783 := bstep (se 1 (by rfl) ⟨1255337, by rfl⟩ : syracuseStep 1673783 = 2510675) B2510675
theorem B1909183 : Blo 742328 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B1058303 : Blo 742328 1058303 := bstep (se 1 (by rfl) ⟨793727, by rfl⟩ : syracuseStep 1058303 = 1587455) B1587455
theorem B1257295 : Blo 742328 1257295 := bstep (se 1 (by rfl) ⟨942971, by rfl⟩ : syracuseStep 1257295 = 1885943) B1885943
theorem B4829939 : Blo 742328 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B8598377 : Blo 742328 8598377 := bstep (se 2 (by rfl) ⟨3224391, by rfl⟩ : syracuseStep 8598377 = 6448783) B6448783
theorem B2506409 : Blo 742328 2506409 := bstep (se 2 (by rfl) ⟨939903, by rfl⟩ : syracuseStep 2506409 = 1879807) B1879807
theorem B1589215 : Blo 742328 1589215 := bstep (se 1 (by rfl) ⟨1191911, by rfl⟩ : syracuseStep 1589215 = 2383823) B2383823
theorem B12042539 : Blo 742328 12042539 := bstep (se 1 (by rfl) ⟨9031904, by rfl⟩ : syracuseStep 12042539 = 18063809) B18063809
theorem B6051347 : Blo 742328 6051347 := bstep (se 1 (by rfl) ⟨4538510, by rfl⟩ : syracuseStep 6051347 = 9077021) B9077021
theorem B742939 : Blo 742328 742939 := bstep (se 1 (by rfl) ⟨557204, by rfl⟩ : syracuseStep 742939 = 1114409) B1114409
theorem B5367293 : Blo 742328 5367293 := bstep (se 3 (by rfl) ⟨1006367, by rfl⟩ : syracuseStep 5367293 = 2012735) B2012735
theorem B2517695 : Blo 742328 2517695 := bstep (se 1 (by rfl) ⟨1888271, by rfl⟩ : syracuseStep 2517695 = 3776543) B3776543
theorem B2389769 : Blo 742328 2389769 := bstep (se 2 (by rfl) ⟨896163, by rfl⟩ : syracuseStep 2389769 = 1792327) B1792327
theorem B8028359 : Blo 742328 8028359 := bstep (se 1 (by rfl) ⟨6021269, by rfl⟩ : syracuseStep 8028359 = 12042539) B12042539
theorem B1115039 : Blo 742328 1115039 := bstep (se 1 (by rfl) ⟨836279, by rfl⟩ : syracuseStep 1115039 = 1672559) B1672559
theorem B1115855 : Blo 742328 1115855 := bstep (se 1 (by rfl) ⟨836891, by rfl⟩ : syracuseStep 1115855 = 1673783) B1673783
theorem B4034231 : Blo 742328 4034231 := bstep (se 1 (by rfl) ⟨3025673, by rfl⟩ : syracuseStep 4034231 = 6051347) B6051347
theorem B2822141 : Blo 742328 2822141 := bstep (se 3 (by rfl) ⟨529151, by rfl⟩ : syracuseStep 2822141 = 1058303) B1058303
theorem B1676393 : Blo 742328 1676393 := bstep (se 2 (by rfl) ⟨628647, by rfl⟩ : syracuseStep 1676393 = 1257295) B1257295
theorem B3578195 : Blo 742328 3578195 := bstep (se 1 (by rfl) ⟨2683646, by rfl⟩ : syracuseStep 3578195 = 5367293) B5367293
theorem B1678463 : Blo 742328 1678463 := bstep (se 1 (by rfl) ⟨1258847, by rfl⟩ : syracuseStep 1678463 = 2517695) B2517695
theorem B3219959 : Blo 742328 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B1593179 : Blo 742328 1593179 := bstep (se 1 (by rfl) ⟨1194884, by rfl⟩ : syracuseStep 1593179 = 2389769) B2389769
theorem B2118953 : Blo 742328 2118953 := bstep (se 2 (by rfl) ⟨794607, by rfl⟩ : syracuseStep 2118953 = 1589215) B1589215
theorem B2545577 : Blo 742328 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B744447 : Blo 742328 744447 := bstep (se 1 (by rfl) ⟨558335, by rfl⟩ : syracuseStep 744447 = 1116671) B1116671
theorem B5732251 : Blo 742328 5732251 := bstep (se 1 (by rfl) ⟨4299188, by rfl⟩ : syracuseStep 5732251 = 8598377) B8598377
theorem B1670939 : Blo 742328 1670939 := bstep (se 1 (by rfl) ⟨1253204, by rfl⟩ : syracuseStep 1670939 = 2506409) B2506409
theorem B2689487 : Blo 742328 2689487 := bstep (se 1 (by rfl) ⟨2017115, by rfl⟩ : syracuseStep 2689487 = 4034231) B4034231
theorem B1117595 : Blo 742328 1117595 := bstep (se 1 (by rfl) ⟨838196, by rfl⟩ : syracuseStep 1117595 = 1676393) B1676393
theorem B1412635 : Blo 742328 1412635 := bstep (se 1 (by rfl) ⟨1059476, by rfl⟩ : syracuseStep 1412635 = 2118953) B2118953
theorem B1118975 : Blo 742328 1118975 := bstep (se 1 (by rfl) ⟨839231, by rfl⟩ : syracuseStep 1118975 = 1678463) B1678463
theorem B5352239 : Blo 742328 5352239 := bstep (se 1 (by rfl) ⟨4014179, by rfl⟩ : syracuseStep 5352239 = 8028359) B8028359
theorem B1062119 : Blo 742328 1062119 := bstep (se 1 (by rfl) ⟨796589, by rfl⟩ : syracuseStep 1062119 = 1593179) B1593179
theorem B1881427 : Blo 742328 1881427 := bstep (se 1 (by rfl) ⟨1411070, by rfl⟩ : syracuseStep 1881427 = 2822141) B2822141
theorem B2146639 : Blo 742328 2146639 := bstep (se 1 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 2146639 = 3219959) B3219959
theorem B743359 : Blo 742328 743359 := bstep (se 1 (by rfl) ⟨557519, by rfl⟩ : syracuseStep 743359 = 1115039) B1115039
theorem B743903 : Blo 742328 743903 := bstep (se 1 (by rfl) ⟨557927, by rfl⟩ : syracuseStep 743903 = 1115855) B1115855
theorem B1697051 : Blo 742328 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B2385463 : Blo 742328 2385463 := bstep (se 1 (by rfl) ⟨1789097, by rfl⟩ : syracuseStep 2385463 = 3578195) B3578195
theorem B30572005 : Blo 742328 30572005 := bstep (se 4 (by rfl) ⟨2866125, by rfl⟩ : syracuseStep 30572005 = 5732251) B5732251
theorem B1113959 : Blo 742328 1113959 := bstep (se 1 (by rfl) ⟨835469, by rfl⟩ : syracuseStep 1113959 = 1670939) B1670939
theorem B3180617 : Blo 742328 3180617 := bstep (se 2 (by rfl) ⟨1192731, by rfl⟩ : syracuseStep 3180617 = 2385463) B2385463
theorem B4525469 : Blo 742328 4525469 := bstep (se 3 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 4525469 = 1697051) B1697051
theorem B2862185 : Blo 742328 2862185 := bstep (se 2 (by rfl) ⟨1073319, by rfl⟩ : syracuseStep 2862185 = 2146639) B2146639
theorem B2832317 : Blo 742328 2832317 := bstep (se 3 (by rfl) ⟨531059, by rfl⟩ : syracuseStep 2832317 = 1062119) B1062119
theorem B1883513 : Blo 742328 1883513 := bstep (se 2 (by rfl) ⟨706317, by rfl⟩ : syracuseStep 1883513 = 1412635) B1412635
theorem B2508569 : Blo 742328 2508569 := bstep (se 2 (by rfl) ⟨940713, by rfl⟩ : syracuseStep 2508569 = 1881427) B1881427
theorem B742639 : Blo 742328 742639 := bstep (se 1 (by rfl) ⟨556979, by rfl⟩ : syracuseStep 742639 = 1113959) B1113959
theorem B1792991 : Blo 742328 1792991 := bstep (se 1 (by rfl) ⟨1344743, by rfl⟩ : syracuseStep 1792991 = 2689487) B2689487
theorem B745063 : Blo 742328 745063 := bstep (se 1 (by rfl) ⟨558797, by rfl⟩ : syracuseStep 745063 = 1117595) B1117595
theorem B745983 : Blo 742328 745983 := bstep (se 1 (by rfl) ⟨559487, by rfl⟩ : syracuseStep 745983 = 1118975) B1118975
theorem B3568159 : Blo 742328 3568159 := bstep (se 1 (by rfl) ⟨2676119, by rfl⟩ : syracuseStep 3568159 = 5352239) B5352239
theorem B40762673 : Blo 742328 40762673 := bstep (se 2 (by rfl) ⟨15286002, by rfl⟩ : syracuseStep 40762673 = 30572005) B30572005
theorem B1672379 : Blo 742328 1672379 := bstep (se 1 (by rfl) ⟨1254284, by rfl⟩ : syracuseStep 1672379 = 2508569) B2508569
theorem B3016979 : Blo 742328 3016979 := bstep (se 1 (by rfl) ⟨2262734, by rfl⟩ : syracuseStep 3016979 = 4525469) B4525469
theorem B4757545 : Blo 742328 4757545 := bstep (se 2 (by rfl) ⟨1784079, by rfl⟩ : syracuseStep 4757545 = 3568159) B3568159
theorem B27175115 : Blo 742328 27175115 := bstep (se 1 (by rfl) ⟨20381336, by rfl⟩ : syracuseStep 27175115 = 40762673) B40762673
theorem B1255675 : Blo 742328 1255675 := bstep (se 1 (by rfl) ⟨941756, by rfl⟩ : syracuseStep 1255675 = 1883513) B1883513
theorem B1195327 : Blo 742328 1195327 := bstep (se 1 (by rfl) ⟨896495, by rfl⟩ : syracuseStep 1195327 = 1792991) B1792991
theorem B1888211 : Blo 742328 1888211 := bstep (se 1 (by rfl) ⟨1416158, by rfl⟩ : syracuseStep 1888211 = 2832317) B2832317
theorem B30529973 : Blo 742328 30529973 := bstep (se 5 (by rfl) ⟨1431092, by rfl⟩ : syracuseStep 30529973 = 2862185) B2862185
theorem B2120411 : Blo 742328 2120411 := bstep (se 1 (by rfl) ⟨1590308, by rfl⟩ : syracuseStep 2120411 = 3180617) B3180617
theorem B1114919 : Blo 742328 1114919 := bstep (se 1 (by rfl) ⟨836189, by rfl⟩ : syracuseStep 1114919 = 1672379) B1672379
theorem B1674233 : Blo 742328 1674233 := bstep (se 2 (by rfl) ⟨627837, by rfl⟩ : syracuseStep 1674233 = 1255675) B1255675
theorem B20353315 : Blo 742328 20353315 := bstep (se 1 (by rfl) ⟨15264986, by rfl⟩ : syracuseStep 20353315 = 30529973) B30529973
theorem B1413607 : Blo 742328 1413607 := bstep (se 1 (by rfl) ⟨1060205, by rfl⟩ : syracuseStep 1413607 = 2120411) B2120411
theorem B2011319 : Blo 742328 2011319 := bstep (se 1 (by rfl) ⟨1508489, by rfl⟩ : syracuseStep 2011319 = 3016979) B3016979
theorem B1258807 : Blo 742328 1258807 := bstep (se 1 (by rfl) ⟨944105, by rfl⟩ : syracuseStep 1258807 = 1888211) B1888211
theorem B6343393 : Blo 742328 6343393 := bstep (se 2 (by rfl) ⟨2378772, by rfl⟩ : syracuseStep 6343393 = 4757545) B4757545
theorem B1593769 : Blo 742328 1593769 := bstep (se 2 (by rfl) ⟨597663, by rfl⟩ : syracuseStep 1593769 = 1195327) B1195327
theorem B18116743 : Blo 742328 18116743 := bstep (se 1 (by rfl) ⟨13587557, by rfl⟩ : syracuseStep 18116743 = 27175115) B27175115
theorem B1116155 : Blo 742328 1116155 := bstep (se 1 (by rfl) ⟨837116, by rfl⟩ : syracuseStep 1116155 = 1674233) B1674233
theorem B8457857 : Blo 742328 8457857 := bstep (se 2 (by rfl) ⟨3171696, by rfl⟩ : syracuseStep 8457857 = 6343393) B6343393
theorem B24155657 : Blo 742328 24155657 := bstep (se 2 (by rfl) ⟨9058371, by rfl⟩ : syracuseStep 24155657 = 18116743) B18116743
theorem B27137753 : Blo 742328 27137753 := bstep (se 2 (by rfl) ⟨10176657, by rfl⟩ : syracuseStep 27137753 = 20353315) B20353315
theorem B1678409 : Blo 742328 1678409 := bstep (se 2 (by rfl) ⟨629403, by rfl⟩ : syracuseStep 1678409 = 1258807) B1258807
theorem B1884809 : Blo 742328 1884809 := bstep (se 2 (by rfl) ⟨706803, by rfl⟩ : syracuseStep 1884809 = 1413607) B1413607
theorem B743279 : Blo 742328 743279 := bstep (se 1 (by rfl) ⟨557459, by rfl⟩ : syracuseStep 743279 = 1114919) B1114919
theorem B2125025 : Blo 742328 2125025 := bstep (se 2 (by rfl) ⟨796884, by rfl⟩ : syracuseStep 2125025 = 1593769) B1593769
theorem B1340879 : Blo 742328 1340879 := bstep (se 1 (by rfl) ⟨1005659, by rfl⟩ : syracuseStep 1340879 = 2011319) B2011319
theorem B5638571 : Blo 742328 5638571 := bstep (se 1 (by rfl) ⟨4228928, by rfl⟩ : syracuseStep 5638571 = 8457857) B8457857
theorem B18091835 : Blo 742328 18091835 := bstep (se 1 (by rfl) ⟨13568876, by rfl⟩ : syracuseStep 18091835 = 27137753) B27137753
theorem B3575677 : Blo 742328 3575677 := bstep (se 3 (by rfl) ⟨670439, by rfl⟩ : syracuseStep 3575677 = 1340879) B1340879
theorem B1118939 : Blo 742328 1118939 := bstep (se 1 (by rfl) ⟨839204, by rfl⟩ : syracuseStep 1118939 = 1678409) B1678409
theorem B1416683 : Blo 742328 1416683 := bstep (se 1 (by rfl) ⟨1062512, by rfl⟩ : syracuseStep 1416683 = 2125025) B2125025
theorem B1256539 : Blo 742328 1256539 := bstep (se 1 (by rfl) ⟨942404, by rfl⟩ : syracuseStep 1256539 = 1884809) B1884809
theorem B16103771 : Blo 742328 16103771 := bstep (se 1 (by rfl) ⟨12077828, by rfl⟩ : syracuseStep 16103771 = 24155657) B24155657
theorem B744103 : Blo 742328 744103 := bstep (se 1 (by rfl) ⟨558077, by rfl⟩ : syracuseStep 744103 = 1116155) B1116155
theorem B12061223 : Blo 742328 12061223 := bstep (se 1 (by rfl) ⟨9045917, by rfl⟩ : syracuseStep 12061223 = 18091835) B18091835
theorem B1675385 : Blo 742328 1675385 := bstep (se 2 (by rfl) ⟨628269, by rfl⟩ : syracuseStep 1675385 = 1256539) B1256539
theorem B4767569 : Blo 742328 4767569 := bstep (se 2 (by rfl) ⟨1787838, by rfl⟩ : syracuseStep 4767569 = 3575677) B3575677
theorem B10735847 : Blo 742328 10735847 := bstep (se 1 (by rfl) ⟨8051885, by rfl⟩ : syracuseStep 10735847 = 16103771) B16103771
theorem B3759047 : Blo 742328 3759047 := bstep (se 1 (by rfl) ⟨2819285, by rfl⟩ : syracuseStep 3759047 = 5638571) B5638571
theorem B745959 : Blo 742328 745959 := bstep (se 1 (by rfl) ⟨559469, by rfl⟩ : syracuseStep 745959 = 1118939) B1118939
theorem B944455 : Blo 742328 944455 := bstep (se 1 (by rfl) ⟨708341, by rfl⟩ : syracuseStep 944455 = 1416683) B1416683
theorem B1116923 : Blo 742328 1116923 := bstep (se 1 (by rfl) ⟨837692, by rfl⟩ : syracuseStep 1116923 = 1675385) B1675385
theorem B8040815 : Blo 742328 8040815 := bstep (se 1 (by rfl) ⟨6030611, by rfl⟩ : syracuseStep 8040815 = 12061223) B12061223
theorem B7157231 : Blo 742328 7157231 := bstep (se 1 (by rfl) ⟨5367923, by rfl⟩ : syracuseStep 7157231 = 10735847) B10735847
theorem B1259273 : Blo 742328 1259273 := bstep (se 2 (by rfl) ⟨472227, by rfl⟩ : syracuseStep 1259273 = 944455) B944455
theorem B2506031 : Blo 742328 2506031 := bstep (se 1 (by rfl) ⟨1879523, by rfl⟩ : syracuseStep 2506031 = 3759047) B3759047
theorem B3178379 : Blo 742328 3178379 := bstep (se 1 (by rfl) ⟨2383784, by rfl⟩ : syracuseStep 3178379 = 4767569) B4767569
theorem B5360543 : Blo 742328 5360543 := bstep (se 1 (by rfl) ⟨4020407, by rfl⟩ : syracuseStep 5360543 = 8040815) B8040815
theorem B4771487 : Blo 742328 4771487 := bstep (se 1 (by rfl) ⟨3578615, by rfl⟩ : syracuseStep 4771487 = 7157231) B7157231
theorem B839515 : Blo 742328 839515 := bstep (se 1 (by rfl) ⟨629636, by rfl⟩ : syracuseStep 839515 = 1259273) B1259273
theorem B2118919 : Blo 742328 2118919 := bstep (se 1 (by rfl) ⟨1589189, by rfl⟩ : syracuseStep 2118919 = 3178379) B3178379
theorem B744615 : Blo 742328 744615 := bstep (se 1 (by rfl) ⟨558461, by rfl⟩ : syracuseStep 744615 = 1116923) B1116923
theorem B1670687 : Blo 742328 1670687 := bstep (se 1 (by rfl) ⟨1253015, by rfl⟩ : syracuseStep 1670687 = 2506031) B2506031
theorem B3573695 : Blo 742328 3573695 := bstep (se 1 (by rfl) ⟨2680271, by rfl⟩ : syracuseStep 3573695 = 5360543) B5360543
theorem B1119353 : Blo 742328 1119353 := bstep (se 2 (by rfl) ⟨419757, by rfl⟩ : syracuseStep 1119353 = 839515) B839515
theorem B2825225 : Blo 742328 2825225 := bstep (se 2 (by rfl) ⟨1059459, by rfl⟩ : syracuseStep 2825225 = 2118919) B2118919
theorem B12723965 : Blo 742328 12723965 := bstep (se 3 (by rfl) ⟨2385743, by rfl⟩ : syracuseStep 12723965 = 4771487) B4771487
theorem B1113791 : Blo 742328 1113791 := bstep (se 1 (by rfl) ⟨835343, by rfl⟩ : syracuseStep 1113791 = 1670687) B1670687
theorem B1883483 : Blo 742328 1883483 := bstep (se 1 (by rfl) ⟨1412612, by rfl⟩ : syracuseStep 1883483 = 2825225) B2825225
theorem B742527 : Blo 742328 742527 := bstep (se 1 (by rfl) ⟨556895, by rfl⟩ : syracuseStep 742527 = 1113791) B1113791
theorem B2382463 : Blo 742328 2382463 := bstep (se 1 (by rfl) ⟨1786847, by rfl⟩ : syracuseStep 2382463 = 3573695) B3573695
theorem B746235 : Blo 742328 746235 := bstep (se 1 (by rfl) ⟨559676, by rfl⟩ : syracuseStep 746235 = 1119353) B1119353
theorem B8482643 : Blo 742328 8482643 := bstep (se 1 (by rfl) ⟨6361982, by rfl⟩ : syracuseStep 8482643 = 12723965) B12723965
theorem B1255655 : Blo 742328 1255655 := bstep (se 1 (by rfl) ⟨941741, by rfl⟩ : syracuseStep 1255655 = 1883483) B1883483
theorem B5655095 : Blo 742328 5655095 := bstep (se 1 (by rfl) ⟨4241321, by rfl⟩ : syracuseStep 5655095 = 8482643) B8482643
theorem B12706469 : Blo 742328 12706469 := bstep (se 4 (by rfl) ⟨1191231, by rfl⟩ : syracuseStep 12706469 = 2382463) B2382463
theorem B3770063 : Blo 742328 3770063 := bstep (se 1 (by rfl) ⟨2827547, by rfl⟩ : syracuseStep 3770063 = 5655095) B5655095
theorem B8470979 : Blo 742328 8470979 := bstep (se 1 (by rfl) ⟨6353234, by rfl⟩ : syracuseStep 8470979 = 12706469) B12706469
theorem B837103 : Blo 742328 837103 := bstep (se 1 (by rfl) ⟨627827, by rfl⟩ : syracuseStep 837103 = 1255655) B1255655
theorem B1116137 : Blo 742328 1116137 := bstep (se 2 (by rfl) ⟨418551, by rfl⟩ : syracuseStep 1116137 = 837103) B837103
theorem B5647319 : Blo 742328 5647319 := bstep (se 1 (by rfl) ⟨4235489, by rfl⟩ : syracuseStep 5647319 = 8470979) B8470979
theorem B2513375 : Blo 742328 2513375 := bstep (se 1 (by rfl) ⟨1885031, by rfl⟩ : syracuseStep 2513375 = 3770063) B3770063
theorem B1675583 : Blo 742328 1675583 := bstep (se 1 (by rfl) ⟨1256687, by rfl⟩ : syracuseStep 1675583 = 2513375) B2513375
theorem B744091 : Blo 742328 744091 := bstep (se 1 (by rfl) ⟨558068, by rfl⟩ : syracuseStep 744091 = 1116137) B1116137
theorem B3764879 : Blo 742328 3764879 := bstep (se 1 (by rfl) ⟨2823659, by rfl⟩ : syracuseStep 3764879 = 5647319) B5647319
theorem B1117055 : Blo 742328 1117055 := bstep (se 1 (by rfl) ⟨837791, by rfl⟩ : syracuseStep 1117055 = 1675583) B1675583
theorem B2509919 : Blo 742328 2509919 := bstep (se 1 (by rfl) ⟨1882439, by rfl⟩ : syracuseStep 2509919 = 3764879) B3764879
theorem B1673279 : Blo 742328 1673279 := bstep (se 1 (by rfl) ⟨1254959, by rfl⟩ : syracuseStep 1673279 = 2509919) B2509919
theorem B744703 : Blo 742328 744703 := bstep (se 1 (by rfl) ⟨558527, by rfl⟩ : syracuseStep 744703 = 1117055) B1117055
theorem B1115519 : Blo 742328 1115519 := bstep (se 1 (by rfl) ⟨836639, by rfl⟩ : syracuseStep 1115519 = 1673279) B1673279
theorem B743679 : Blo 742328 743679 := bstep (se 1 (by rfl) ⟨557759, by rfl⟩ : syracuseStep 743679 = 1115519) B1115519

theorem C0 (j : ℕ) (h1 : 185582 ≤ j) (h2 : j ≤ 186281) : Blo 742328 (4 * j + 3) := by
  interval_cases j
  · exact B742331
  · exact B742335
  · exact B742339
  · exact B742343
  · exact B742347
  · exact B742351
  · exact B742355
  · exact B742359
  · exact B742363
  · exact B742367
  · exact B742371
  · exact B742375
  · exact B742379
  · exact B742383
  · exact B742387
  · exact B742391
  · exact B742395
  · exact B742399
  · exact B742403
  · exact B742407
  · exact B742411
  · exact B742415
  · exact B742419
  · exact B742423
  · exact B742427
  · exact B742431
  · exact B742435
  · exact B742439
  · exact B742443
  · exact B742447
  · exact B742451
  · exact B742455
  · exact B742459
  · exact B742463
  · exact B742467
  · exact B742471
  · exact B742475
  · exact B742479
  · exact B742483
  · exact B742487
  · exact B742491
  · exact B742495
  · exact B742499
  · exact B742503
  · exact B742507
  · exact B742511
  · exact B742515
  · exact B742519
  · exact B742523
  · exact B742527
  · exact B742531
  · exact B742535
  · exact B742539
  · exact B742543
  · exact B742547
  · exact B742551
  · exact B742555
  · exact B742559
  · exact B742563
  · exact B742567
  · exact B742571
  · exact B742575
  · exact B742579
  · exact B742583
  · exact B742587
  · exact B742591
  · exact B742595
  · exact B742599
  · exact B742603
  · exact B742607
  · exact B742611
  · exact B742615
  · exact B742619
  · exact B742623
  · exact B742627
  · exact B742631
  · exact B742635
  · exact B742639
  · exact B742643
  · exact B742647
  · exact B742651
  · exact B742655
  · exact B742659
  · exact B742663
  · exact B742667
  · exact B742671
  · exact B742675
  · exact B742679
  · exact B742683
  · exact B742687
  · exact B742691
  · exact B742695
  · exact B742699
  · exact B742703
  · exact B742707
  · exact B742711
  · exact B742715
  · exact B742719
  · exact B742723
  · exact B742727
  · exact B742731
  · exact B742735
  · exact B742739
  · exact B742743
  · exact B742747
  · exact B742751
  · exact B742755
  · exact B742759
  · exact B742763
  · exact B742767
  · exact B742771
  · exact B742775
  · exact B742779
  · exact B742783
  · exact B742787
  · exact B742791
  · exact B742795
  · exact B742799
  · exact B742803
  · exact B742807
  · exact B742811
  · exact B742815
  · exact B742819
  · exact B742823
  · exact B742827
  · exact B742831
  · exact B742835
  · exact B742839
  · exact B742843
  · exact B742847
  · exact B742851
  · exact B742855
  · exact B742859
  · exact B742863
  · exact B742867
  · exact B742871
  · exact B742875
  · exact B742879
  · exact B742883
  · exact B742887
  · exact B742891
  · exact B742895
  · exact B742899
  · exact B742903
  · exact B742907
  · exact B742911
  · exact B742915
  · exact B742919
  · exact B742923
  · exact B742927
  · exact B742931
  · exact B742935
  · exact B742939
  · exact B742943
  · exact B742947
  · exact B742951
  · exact B742955
  · exact B742959
  · exact B742963
  · exact B742967
  · exact B742971
  · exact B742975
  · exact B742979
  · exact B742983
  · exact B742987
  · exact B742991
  · exact B742995
  · exact B742999
  · exact B743003
  · exact B743007
  · exact B743011
  · exact B743015
  · exact B743019
  · exact B743023
  · exact B743027
  · exact B743031
  · exact B743035
  · exact B743039
  · exact B743043
  · exact B743047
  · exact B743051
  · exact B743055
  · exact B743059
  · exact B743063
  · exact B743067
  · exact B743071
  · exact B743075
  · exact B743079
  · exact B743083
  · exact B743087
  · exact B743091
  · exact B743095
  · exact B743099
  · exact B743103
  · exact B743107
  · exact B743111
  · exact B743115
  · exact B743119
  · exact B743123
  · exact B743127
  · exact B743131
  · exact B743135
  · exact B743139
  · exact B743143
  · exact B743147
  · exact B743151
  · exact B743155
  · exact B743159
  · exact B743163
  · exact B743167
  · exact B743171
  · exact B743175
  · exact B743179
  · exact B743183
  · exact B743187
  · exact B743191
  · exact B743195
  · exact B743199
  · exact B743203
  · exact B743207
  · exact B743211
  · exact B743215
  · exact B743219
  · exact B743223
  · exact B743227
  · exact B743231
  · exact B743235
  · exact B743239
  · exact B743243
  · exact B743247
  · exact B743251
  · exact B743255
  · exact B743259
  · exact B743263
  · exact B743267
  · exact B743271
  · exact B743275
  · exact B743279
  · exact B743283
  · exact B743287
  · exact B743291
  · exact B743295
  · exact B743299
  · exact B743303
  · exact B743307
  · exact B743311
  · exact B743315
  · exact B743319
  · exact B743323
  · exact B743327
  · exact B743331
  · exact B743335
  · exact B743339
  · exact B743343
  · exact B743347
  · exact B743351
  · exact B743355
  · exact B743359
  · exact B743363
  · exact B743367
  · exact B743371
  · exact B743375
  · exact B743379
  · exact B743383
  · exact B743387
  · exact B743391
  · exact B743395
  · exact B743399
  · exact B743403
  · exact B743407
  · exact B743411
  · exact B743415
  · exact B743419
  · exact B743423
  · exact B743427
  · exact B743431
  · exact B743435
  · exact B743439
  · exact B743443
  · exact B743447
  · exact B743451
  · exact B743455
  · exact B743459
  · exact B743463
  · exact B743467
  · exact B743471
  · exact B743475
  · exact B743479
  · exact B743483
  · exact B743487
  · exact B743491
  · exact B743495
  · exact B743499
  · exact B743503
  · exact B743507
  · exact B743511
  · exact B743515
  · exact B743519
  · exact B743523
  · exact B743527
  · exact B743531
  · exact B743535
  · exact B743539
  · exact B743543
  · exact B743547
  · exact B743551
  · exact B743555
  · exact B743559
  · exact B743563
  · exact B743567
  · exact B743571
  · exact B743575
  · exact B743579
  · exact B743583
  · exact B743587
  · exact B743591
  · exact B743595
  · exact B743599
  · exact B743603
  · exact B743607
  · exact B743611
  · exact B743615
  · exact B743619
  · exact B743623
  · exact B743627
  · exact B743631
  · exact B743635
  · exact B743639
  · exact B743643
  · exact B743647
  · exact B743651
  · exact B743655
  · exact B743659
  · exact B743663
  · exact B743667
  · exact B743671
  · exact B743675
  · exact B743679
  · exact B743683
  · exact B743687
  · exact B743691
  · exact B743695
  · exact B743699
  · exact B743703
  · exact B743707
  · exact B743711
  · exact B743715
  · exact B743719
  · exact B743723
  · exact B743727
  · exact B743731
  · exact B743735
  · exact B743739
  · exact B743743
  · exact B743747
  · exact B743751
  · exact B743755
  · exact B743759
  · exact B743763
  · exact B743767
  · exact B743771
  · exact B743775
  · exact B743779
  · exact B743783
  · exact B743787
  · exact B743791
  · exact B743795
  · exact B743799
  · exact B743803
  · exact B743807
  · exact B743811
  · exact B743815
  · exact B743819
  · exact B743823
  · exact B743827
  · exact B743831
  · exact B743835
  · exact B743839
  · exact B743843
  · exact B743847
  · exact B743851
  · exact B743855
  · exact B743859
  · exact B743863
  · exact B743867
  · exact B743871
  · exact B743875
  · exact B743879
  · exact B743883
  · exact B743887
  · exact B743891
  · exact B743895
  · exact B743899
  · exact B743903
  · exact B743907
  · exact B743911
  · exact B743915
  · exact B743919
  · exact B743923
  · exact B743927
  · exact B743931
  · exact B743935
  · exact B743939
  · exact B743943
  · exact B743947
  · exact B743951
  · exact B743955
  · exact B743959
  · exact B743963
  · exact B743967
  · exact B743971
  · exact B743975
  · exact B743979
  · exact B743983
  · exact B743987
  · exact B743991
  · exact B743995
  · exact B743999
  · exact B744003
  · exact B744007
  · exact B744011
  · exact B744015
  · exact B744019
  · exact B744023
  · exact B744027
  · exact B744031
  · exact B744035
  · exact B744039
  · exact B744043
  · exact B744047
  · exact B744051
  · exact B744055
  · exact B744059
  · exact B744063
  · exact B744067
  · exact B744071
  · exact B744075
  · exact B744079
  · exact B744083
  · exact B744087
  · exact B744091
  · exact B744095
  · exact B744099
  · exact B744103
  · exact B744107
  · exact B744111
  · exact B744115
  · exact B744119
  · exact B744123
  · exact B744127
  · exact B744131
  · exact B744135
  · exact B744139
  · exact B744143
  · exact B744147
  · exact B744151
  · exact B744155
  · exact B744159
  · exact B744163
  · exact B744167
  · exact B744171
  · exact B744175
  · exact B744179
  · exact B744183
  · exact B744187
  · exact B744191
  · exact B744195
  · exact B744199
  · exact B744203
  · exact B744207
  · exact B744211
  · exact B744215
  · exact B744219
  · exact B744223
  · exact B744227
  · exact B744231
  · exact B744235
  · exact B744239
  · exact B744243
  · exact B744247
  · exact B744251
  · exact B744255
  · exact B744259
  · exact B744263
  · exact B744267
  · exact B744271
  · exact B744275
  · exact B744279
  · exact B744283
  · exact B744287
  · exact B744291
  · exact B744295
  · exact B744299
  · exact B744303
  · exact B744307
  · exact B744311
  · exact B744315
  · exact B744319
  · exact B744323
  · exact B744327
  · exact B744331
  · exact B744335
  · exact B744339
  · exact B744343
  · exact B744347
  · exact B744351
  · exact B744355
  · exact B744359
  · exact B744363
  · exact B744367
  · exact B744371
  · exact B744375
  · exact B744379
  · exact B744383
  · exact B744387
  · exact B744391
  · exact B744395
  · exact B744399
  · exact B744403
  · exact B744407
  · exact B744411
  · exact B744415
  · exact B744419
  · exact B744423
  · exact B744427
  · exact B744431
  · exact B744435
  · exact B744439
  · exact B744443
  · exact B744447
  · exact B744451
  · exact B744455
  · exact B744459
  · exact B744463
  · exact B744467
  · exact B744471
  · exact B744475
  · exact B744479
  · exact B744483
  · exact B744487
  · exact B744491
  · exact B744495
  · exact B744499
  · exact B744503
  · exact B744507
  · exact B744511
  · exact B744515
  · exact B744519
  · exact B744523
  · exact B744527
  · exact B744531
  · exact B744535
  · exact B744539
  · exact B744543
  · exact B744547
  · exact B744551
  · exact B744555
  · exact B744559
  · exact B744563
  · exact B744567
  · exact B744571
  · exact B744575
  · exact B744579
  · exact B744583
  · exact B744587
  · exact B744591
  · exact B744595
  · exact B744599
  · exact B744603
  · exact B744607
  · exact B744611
  · exact B744615
  · exact B744619
  · exact B744623
  · exact B744627
  · exact B744631
  · exact B744635
  · exact B744639
  · exact B744643
  · exact B744647
  · exact B744651
  · exact B744655
  · exact B744659
  · exact B744663
  · exact B744667
  · exact B744671
  · exact B744675
  · exact B744679
  · exact B744683
  · exact B744687
  · exact B744691
  · exact B744695
  · exact B744699
  · exact B744703
  · exact B744707
  · exact B744711
  · exact B744715
  · exact B744719
  · exact B744723
  · exact B744727
  · exact B744731
  · exact B744735
  · exact B744739
  · exact B744743
  · exact B744747
  · exact B744751
  · exact B744755
  · exact B744759
  · exact B744763
  · exact B744767
  · exact B744771
  · exact B744775
  · exact B744779
  · exact B744783
  · exact B744787
  · exact B744791
  · exact B744795
  · exact B744799
  · exact B744803
  · exact B744807
  · exact B744811
  · exact B744815
  · exact B744819
  · exact B744823
  · exact B744827
  · exact B744831
  · exact B744835
  · exact B744839
  · exact B744843
  · exact B744847
  · exact B744851
  · exact B744855
  · exact B744859
  · exact B744863
  · exact B744867
  · exact B744871
  · exact B744875
  · exact B744879
  · exact B744883
  · exact B744887
  · exact B744891
  · exact B744895
  · exact B744899
  · exact B744903
  · exact B744907
  · exact B744911
  · exact B744915
  · exact B744919
  · exact B744923
  · exact B744927
  · exact B744931
  · exact B744935
  · exact B744939
  · exact B744943
  · exact B744947
  · exact B744951
  · exact B744955
  · exact B744959
  · exact B744963
  · exact B744967
  · exact B744971
  · exact B744975
  · exact B744979
  · exact B744983
  · exact B744987
  · exact B744991
  · exact B744995
  · exact B744999
  · exact B745003
  · exact B745007
  · exact B745011
  · exact B745015
  · exact B745019
  · exact B745023
  · exact B745027
  · exact B745031
  · exact B745035
  · exact B745039
  · exact B745043
  · exact B745047
  · exact B745051
  · exact B745055
  · exact B745059
  · exact B745063
  · exact B745067
  · exact B745071
  · exact B745075
  · exact B745079
  · exact B745083
  · exact B745087
  · exact B745091
  · exact B745095
  · exact B745099
  · exact B745103
  · exact B745107
  · exact B745111
  · exact B745115
  · exact B745119
  · exact B745123
  · exact B745127

theorem C1 (j : ℕ) (h1 : 186282 ≤ j) (h2 : j ≤ 186581) : Blo 742328 (4 * j + 3) := by
  interval_cases j
  · exact B745131
  · exact B745135
  · exact B745139
  · exact B745143
  · exact B745147
  · exact B745151
  · exact B745155
  · exact B745159
  · exact B745163
  · exact B745167
  · exact B745171
  · exact B745175
  · exact B745179
  · exact B745183
  · exact B745187
  · exact B745191
  · exact B745195
  · exact B745199
  · exact B745203
  · exact B745207
  · exact B745211
  · exact B745215
  · exact B745219
  · exact B745223
  · exact B745227
  · exact B745231
  · exact B745235
  · exact B745239
  · exact B745243
  · exact B745247
  · exact B745251
  · exact B745255
  · exact B745259
  · exact B745263
  · exact B745267
  · exact B745271
  · exact B745275
  · exact B745279
  · exact B745283
  · exact B745287
  · exact B745291
  · exact B745295
  · exact B745299
  · exact B745303
  · exact B745307
  · exact B745311
  · exact B745315
  · exact B745319
  · exact B745323
  · exact B745327
  · exact B745331
  · exact B745335
  · exact B745339
  · exact B745343
  · exact B745347
  · exact B745351
  · exact B745355
  · exact B745359
  · exact B745363
  · exact B745367
  · exact B745371
  · exact B745375
  · exact B745379
  · exact B745383
  · exact B745387
  · exact B745391
  · exact B745395
  · exact B745399
  · exact B745403
  · exact B745407
  · exact B745411
  · exact B745415
  · exact B745419
  · exact B745423
  · exact B745427
  · exact B745431
  · exact B745435
  · exact B745439
  · exact B745443
  · exact B745447
  · exact B745451
  · exact B745455
  · exact B745459
  · exact B745463
  · exact B745467
  · exact B745471
  · exact B745475
  · exact B745479
  · exact B745483
  · exact B745487
  · exact B745491
  · exact B745495
  · exact B745499
  · exact B745503
  · exact B745507
  · exact B745511
  · exact B745515
  · exact B745519
  · exact B745523
  · exact B745527
  · exact B745531
  · exact B745535
  · exact B745539
  · exact B745543
  · exact B745547
  · exact B745551
  · exact B745555
  · exact B745559
  · exact B745563
  · exact B745567
  · exact B745571
  · exact B745575
  · exact B745579
  · exact B745583
  · exact B745587
  · exact B745591
  · exact B745595
  · exact B745599
  · exact B745603
  · exact B745607
  · exact B745611
  · exact B745615
  · exact B745619
  · exact B745623
  · exact B745627
  · exact B745631
  · exact B745635
  · exact B745639
  · exact B745643
  · exact B745647
  · exact B745651
  · exact B745655
  · exact B745659
  · exact B745663
  · exact B745667
  · exact B745671
  · exact B745675
  · exact B745679
  · exact B745683
  · exact B745687
  · exact B745691
  · exact B745695
  · exact B745699
  · exact B745703
  · exact B745707
  · exact B745711
  · exact B745715
  · exact B745719
  · exact B745723
  · exact B745727
  · exact B745731
  · exact B745735
  · exact B745739
  · exact B745743
  · exact B745747
  · exact B745751
  · exact B745755
  · exact B745759
  · exact B745763
  · exact B745767
  · exact B745771
  · exact B745775
  · exact B745779
  · exact B745783
  · exact B745787
  · exact B745791
  · exact B745795
  · exact B745799
  · exact B745803
  · exact B745807
  · exact B745811
  · exact B745815
  · exact B745819
  · exact B745823
  · exact B745827
  · exact B745831
  · exact B745835
  · exact B745839
  · exact B745843
  · exact B745847
  · exact B745851
  · exact B745855
  · exact B745859
  · exact B745863
  · exact B745867
  · exact B745871
  · exact B745875
  · exact B745879
  · exact B745883
  · exact B745887
  · exact B745891
  · exact B745895
  · exact B745899
  · exact B745903
  · exact B745907
  · exact B745911
  · exact B745915
  · exact B745919
  · exact B745923
  · exact B745927
  · exact B745931
  · exact B745935
  · exact B745939
  · exact B745943
  · exact B745947
  · exact B745951
  · exact B745955
  · exact B745959
  · exact B745963
  · exact B745967
  · exact B745971
  · exact B745975
  · exact B745979
  · exact B745983
  · exact B745987
  · exact B745991
  · exact B745995
  · exact B745999
  · exact B746003
  · exact B746007
  · exact B746011
  · exact B746015
  · exact B746019
  · exact B746023
  · exact B746027
  · exact B746031
  · exact B746035
  · exact B746039
  · exact B746043
  · exact B746047
  · exact B746051
  · exact B746055
  · exact B746059
  · exact B746063
  · exact B746067
  · exact B746071
  · exact B746075
  · exact B746079
  · exact B746083
  · exact B746087
  · exact B746091
  · exact B746095
  · exact B746099
  · exact B746103
  · exact B746107
  · exact B746111
  · exact B746115
  · exact B746119
  · exact B746123
  · exact B746127
  · exact B746131
  · exact B746135
  · exact B746139
  · exact B746143
  · exact B746147
  · exact B746151
  · exact B746155
  · exact B746159
  · exact B746163
  · exact B746167
  · exact B746171
  · exact B746175
  · exact B746179
  · exact B746183
  · exact B746187
  · exact B746191
  · exact B746195
  · exact B746199
  · exact B746203
  · exact B746207
  · exact B746211
  · exact B746215
  · exact B746219
  · exact B746223
  · exact B746227
  · exact B746231
  · exact B746235
  · exact B746239
  · exact B746243
  · exact B746247
  · exact B746251
  · exact B746255
  · exact B746259
  · exact B746263
  · exact B746267
  · exact B746271
  · exact B746275
  · exact B746279
  · exact B746283
  · exact B746287
  · exact B746291
  · exact B746295
  · exact B746299
  · exact B746303
  · exact B746307
  · exact B746311
  · exact B746315
  · exact B746319
  · exact B746323
  · exact B746327

theorem solution (m : ℕ) (hlo : 742328 ≤ m) (hhi : m ≤ 746328) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 185582 ≤ j := by omega
    have hj2 : j ≤ 186581 := by omega
    have hb : Blo 742328 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 186282 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
