-- Prove2me | solution 1 for syracuse_descends_range_1624511_1626511
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:13:47.27754+00:00
-- url     : https://prove2.me/submissions/c5a28257-e0b5-4b64-8c75-95187594af5e

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


theorem B2056205 : Blo 1624511 2056205 := bbase (se 3 (by rfl) ⟨385538, by rfl⟩ : syracuseStep 2056205 = 771077) (by norm_num)
theorem B2744381 : Blo 1624511 2744381 := bbase (se 3 (by rfl) ⟨514571, by rfl⟩ : syracuseStep 2744381 = 1029143) (by norm_num)
theorem B2056261 : Blo 1624511 2056261 := bbase (se 4 (by rfl) ⟨192774, by rfl⟩ : syracuseStep 2056261 = 385549) (by norm_num)
theorem B1646725 : Blo 1624511 1646725 := bbase (se 4 (by rfl) ⟨154380, by rfl⟩ : syracuseStep 1646725 = 308761) (by norm_num)
theorem B8224901 : Blo 1624511 8224901 := bbase (se 4 (by rfl) ⟨771084, by rfl⟩ : syracuseStep 8224901 = 1542169) (by norm_num)
theorem B2605205 : Blo 1624511 2605205 := bbase (se 6 (by rfl) ⟨61059, by rfl⟩ : syracuseStep 2605205 = 122119) (by norm_num)
theorem B2056357 : Blo 1624511 2056357 := bbase (se 4 (by rfl) ⟨192783, by rfl⟩ : syracuseStep 2056357 = 385567) (by norm_num)
theorem B2744509 : Blo 1624511 2744509 := bbase (se 3 (by rfl) ⟨514595, by rfl⟩ : syracuseStep 2744509 = 1029191) (by norm_num)
theorem B19767509 : Blo 1624511 19767509 := bbase (se 7 (by rfl) ⟨231650, by rfl⟩ : syracuseStep 19767509 = 463301) (by norm_num)
theorem B4112653 : Blo 1624511 4112653 := bbase (se 3 (by rfl) ⟨771122, by rfl⟩ : syracuseStep 4112653 = 1542245) (by norm_num)
theorem B2744597 : Blo 1624511 2744597 := bbase (se 6 (by rfl) ⟨64326, by rfl⟩ : syracuseStep 2744597 = 128653) (by norm_num)
theorem B2056529 : Blo 1624511 2056529 := bbase (se 2 (by rfl) ⟨771198, by rfl⟩ : syracuseStep 2056529 = 1542397) (by norm_num)
theorem B4112765 : Blo 1624511 4112765 := bbase (se 3 (by rfl) ⟨771143, by rfl⟩ : syracuseStep 4112765 = 1542287) (by norm_num)
theorem B2056585 : Blo 1624511 2056585 := bbase (se 2 (by rfl) ⟨771219, by rfl⟩ : syracuseStep 2056585 = 1542439) (by norm_num)
theorem B5489045 : Blo 1624511 5489045 := bbase (se 6 (by rfl) ⟨128649, by rfl⟩ : syracuseStep 5489045 = 257299) (by norm_num)
theorem B2744725 : Blo 1624511 2744725 := bbase (se 6 (by rfl) ⟨64329, by rfl⟩ : syracuseStep 2744725 = 128659) (by norm_num)
theorem B1647029 : Blo 1624511 1647029 := bbase (se 5 (by rfl) ⟨77204, by rfl⟩ : syracuseStep 1647029 = 154409) (by norm_num)
theorem B2056681 : Blo 1624511 2056681 := bbase (se 2 (by rfl) ⟨771255, by rfl⟩ : syracuseStep 2056681 = 1542511) (by norm_num)
theorem B2114089 : Blo 1624511 2114089 := bbase (se 2 (by rfl) ⟨792783, by rfl⟩ : syracuseStep 2114089 = 1585567) (by norm_num)
theorem B3293741 : Blo 1624511 3293741 := bbase (se 3 (by rfl) ⟨617576, by rfl⟩ : syracuseStep 3293741 = 1235153) (by norm_num)
theorem B4112957 : Blo 1624511 4112957 := bbase (se 3 (by rfl) ⟨771179, by rfl⟩ : syracuseStep 4112957 = 1542359) (by norm_num)
theorem B6431333 : Blo 1624511 6431333 := bbase (se 4 (by rfl) ⟨602937, by rfl⟩ : syracuseStep 6431333 = 1205875) (by norm_num)
theorem B2056853 : Blo 1624511 2056853 := bbase (se 6 (by rfl) ⟨48207, by rfl⟩ : syracuseStep 2056853 = 96415) (by norm_num)
theorem B2056909 : Blo 1624511 2056909 := bbase (se 3 (by rfl) ⟨385670, by rfl⟩ : syracuseStep 2056909 = 771341) (by norm_num)
theorem B5858021 : Blo 1624511 5858021 := bbase (se 4 (by rfl) ⟨549189, by rfl⟩ : syracuseStep 5858021 = 1098379) (by norm_num)
theorem B1827589 : Blo 1624511 1827589 := bbase (se 4 (by rfl) ⟨171336, by rfl⟩ : syracuseStep 1827589 = 342673) (by norm_num)
theorem B2196229 : Blo 1624511 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B6259477 : Blo 1624511 6259477 := bbase (se 6 (by rfl) ⟨146706, by rfl⟩ : syracuseStep 6259477 = 293413) (by norm_num)
theorem B1827625 : Blo 1624511 1827625 := bbase (se 2 (by rfl) ⟨685359, by rfl⟩ : syracuseStep 1827625 = 1370719) (by norm_num)
theorem B2057005 : Blo 1624511 2057005 := bbase (se 3 (by rfl) ⟨385688, by rfl⟩ : syracuseStep 2057005 = 771377) (by norm_num)
theorem B5489477 : Blo 1624511 5489477 := bbase (se 4 (by rfl) ⟨514638, by rfl⟩ : syracuseStep 5489477 = 1029277) (by norm_num)
theorem B1827661 : Blo 1624511 1827661 := bbase (se 3 (by rfl) ⟨342686, by rfl⟩ : syracuseStep 1827661 = 685373) (by norm_num)
theorem B4391765 : Blo 1624511 4391765 := bbase (se 9 (by rfl) ⟨12866, by rfl⟩ : syracuseStep 4391765 = 25733) (by norm_num)
theorem B2196325 : Blo 1624511 2196325 := bbase (se 4 (by rfl) ⟨205905, by rfl⟩ : syracuseStep 2196325 = 411811) (by norm_num)
theorem B1827697 : Blo 1624511 1827697 := bbase (se 2 (by rfl) ⟨685386, by rfl⟩ : syracuseStep 1827697 = 1370773) (by norm_num)
theorem B1827733 : Blo 1624511 1827733 := bbase (se 6 (by rfl) ⟨42837, by rfl⟩ : syracuseStep 1827733 = 85675) (by norm_num)
theorem B4113301 : Blo 1624511 4113301 := bbase (se 6 (by rfl) ⟨96405, by rfl⟩ : syracuseStep 4113301 = 192811) (by norm_num)
theorem B6939557 : Blo 1624511 6939557 := bbase (se 4 (by rfl) ⟨650583, by rfl⟩ : syracuseStep 6939557 = 1301167) (by norm_num)
theorem B4629413 : Blo 1624511 4629413 := bbase (se 4 (by rfl) ⟨434007, by rfl⟩ : syracuseStep 4629413 = 868015) (by norm_num)
theorem B1827769 : Blo 1624511 1827769 := bbase (se 2 (by rfl) ⟨685413, by rfl⟩ : syracuseStep 1827769 = 1370827) (by norm_num)
theorem B2057177 : Blo 1624511 2057177 := bbase (se 2 (by rfl) ⟨771441, by rfl⟩ : syracuseStep 2057177 = 1542883) (by norm_num)
theorem B1827805 : Blo 1624511 1827805 := bbase (se 3 (by rfl) ⟨342713, by rfl⟩ : syracuseStep 1827805 = 685427) (by norm_num)
theorem B8233973 : Blo 1624511 8233973 := bbase (se 5 (by rfl) ⟨385967, by rfl⟩ : syracuseStep 8233973 = 771935) (by norm_num)
theorem B1827841 : Blo 1624511 1827841 := bbase (se 2 (by rfl) ⟨685440, by rfl⟩ : syracuseStep 1827841 = 1370881) (by norm_num)
theorem B4113413 : Blo 1624511 4113413 := bbase (se 4 (by rfl) ⟨385632, by rfl⟩ : syracuseStep 4113413 = 771265) (by norm_num)
theorem B1647625 : Blo 1624511 1647625 := bbase (se 2 (by rfl) ⟨617859, by rfl⟩ : syracuseStep 1647625 = 1235719) (by norm_num)
theorem B2057233 : Blo 1624511 2057233 := bbase (se 2 (by rfl) ⟨771462, by rfl⟩ : syracuseStep 2057233 = 1542925) (by norm_num)
theorem B1827877 : Blo 1624511 1827877 := bbase (se 4 (by rfl) ⟨171363, by rfl⟩ : syracuseStep 1827877 = 342727) (by norm_num)
theorem B1827913 : Blo 1624511 1827913 := bbase (se 2 (by rfl) ⟨685467, by rfl⟩ : syracuseStep 1827913 = 1370935) (by norm_num)
theorem B1827949 : Blo 1624511 1827949 := bbase (se 3 (by rfl) ⟨342740, by rfl⟩ : syracuseStep 1827949 = 685481) (by norm_num)
theorem B2057329 : Blo 1624511 2057329 := bbase (se 2 (by rfl) ⟨771498, by rfl⟩ : syracuseStep 2057329 = 1542997) (by norm_num)
theorem B1827985 : Blo 1624511 1827985 := bbase (se 2 (by rfl) ⟨685494, by rfl⟩ : syracuseStep 1827985 = 1370989) (by norm_num)
theorem B1828021 : Blo 1624511 1828021 := bbase (se 5 (by rfl) ⟨85688, by rfl⟩ : syracuseStep 1828021 = 171377) (by norm_num)
theorem B2196661 : Blo 1624511 2196661 := bbase (se 5 (by rfl) ⟨102968, by rfl⟩ : syracuseStep 2196661 = 205937) (by norm_num)
theorem B4113605 : Blo 1624511 4113605 := bbase (se 4 (by rfl) ⟨385650, by rfl⟩ : syracuseStep 4113605 = 771301) (by norm_num)
theorem B15623381 : Blo 1624511 15623381 := bbase (se 7 (by rfl) ⟨183086, by rfl⟩ : syracuseStep 15623381 = 366173) (by norm_num)
theorem B1828057 : Blo 1624511 1828057 := bbase (se 2 (by rfl) ⟨685521, by rfl⟩ : syracuseStep 1828057 = 1371043) (by norm_num)
theorem B13894901 : Blo 1624511 13894901 := bbase (se 5 (by rfl) ⟨651323, by rfl⟩ : syracuseStep 13894901 = 1302647) (by norm_num)
theorem B1828093 : Blo 1624511 1828093 := bbase (se 3 (by rfl) ⟨342767, by rfl⟩ : syracuseStep 1828093 = 685535) (by norm_num)
theorem B6169877 : Blo 1624511 6169877 := bbase (se 6 (by rfl) ⟨144606, by rfl⟩ : syracuseStep 6169877 = 289213) (by norm_num)
theorem B2057501 : Blo 1624511 2057501 := bbase (se 3 (by rfl) ⟨385781, by rfl⟩ : syracuseStep 2057501 = 771563) (by norm_num)
theorem B1828129 : Blo 1624511 1828129 := bbase (se 2 (by rfl) ⟨685548, by rfl⟩ : syracuseStep 1828129 = 1371097) (by norm_num)
theorem B7808309 : Blo 1624511 7808309 := bbase (se 5 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 7808309 = 732029) (by norm_num)
theorem B2114881 : Blo 1624511 2114881 := bbase (se 2 (by rfl) ⟨793080, by rfl⟩ : syracuseStep 2114881 = 1586161) (by norm_num)
theorem B1828165 : Blo 1624511 1828165 := bbase (se 4 (by rfl) ⟨171390, by rfl⟩ : syracuseStep 1828165 = 342781) (by norm_num)
theorem B2057557 : Blo 1624511 2057557 := bbase (se 12 (by rfl) ⟨753, by rfl⟩ : syracuseStep 2057557 = 1507) (by norm_num)
theorem B1828201 : Blo 1624511 1828201 := bbase (se 2 (by rfl) ⟨685575, by rfl⟩ : syracuseStep 1828201 = 1371151) (by norm_num)
theorem B1828237 : Blo 1624511 1828237 := bbase (se 3 (by rfl) ⟨342794, by rfl⟩ : syracuseStep 1828237 = 685589) (by norm_num)
theorem B8226197 : Blo 1624511 8226197 := bbase (se 6 (by rfl) ⟨192801, by rfl⟩ : syracuseStep 8226197 = 385603) (by norm_num)
theorem B1828273 : Blo 1624511 1828273 := bbase (se 2 (by rfl) ⟨685602, by rfl⟩ : syracuseStep 1828273 = 1371205) (by norm_num)
theorem B2057653 : Blo 1624511 2057653 := bbase (se 5 (by rfl) ⟨96452, by rfl⟩ : syracuseStep 2057653 = 192905) (by norm_num)
theorem B1828309 : Blo 1624511 1828309 := bbase (se 7 (by rfl) ⟨21425, by rfl⟩ : syracuseStep 1828309 = 42851) (by norm_num)
theorem B1852913 : Blo 1624511 1852913 := bbase (se 2 (by rfl) ⟨694842, by rfl⟩ : syracuseStep 1852913 = 1389685) (by norm_num)
theorem B7808501 : Blo 1624511 7808501 := bbase (se 5 (by rfl) ⟨366023, by rfl⟩ : syracuseStep 7808501 = 732047) (by norm_num)
theorem B1828345 : Blo 1624511 1828345 := bbase (se 2 (by rfl) ⟨685629, by rfl⟩ : syracuseStep 1828345 = 1371259) (by norm_num)
theorem B1828381 : Blo 1624511 1828381 := bbase (se 3 (by rfl) ⟨342821, by rfl⟩ : syracuseStep 1828381 = 685643) (by norm_num)
theorem B4113949 : Blo 1624511 4113949 := bbase (se 3 (by rfl) ⟨771365, by rfl⟩ : syracuseStep 4113949 = 1542731) (by norm_num)
theorem B3655205 : Blo 1624511 3655205 := bbase (se 4 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 3655205 = 685351) (by norm_num)
theorem B6170165 : Blo 1624511 6170165 := bbase (se 5 (by rfl) ⟨289226, by rfl⟩ : syracuseStep 6170165 = 578453) (by norm_num)
theorem B1828417 : Blo 1624511 1828417 := bbase (se 2 (by rfl) ⟨685656, by rfl⟩ : syracuseStep 1828417 = 1371313) (by norm_num)
theorem B5858885 : Blo 1624511 5858885 := bbase (se 4 (by rfl) ⟨549270, by rfl⟩ : syracuseStep 5858885 = 1098541) (by norm_num)
theorem B4630085 : Blo 1624511 4630085 := bbase (se 4 (by rfl) ⟨434070, by rfl⟩ : syracuseStep 4630085 = 868141) (by norm_num)
theorem B2057825 : Blo 1624511 2057825 := bbase (se 2 (by rfl) ⟨771684, by rfl⟩ : syracuseStep 2057825 = 1543369) (by norm_num)
theorem B1828453 : Blo 1624511 1828453 := bbase (se 4 (by rfl) ⟨171417, by rfl⟩ : syracuseStep 1828453 = 342835) (by norm_num)
theorem B3655277 : Blo 1624511 3655277 := bbase (se 3 (by rfl) ⟨685364, by rfl⟩ : syracuseStep 3655277 = 1370729) (by norm_num)
theorem B1828489 : Blo 1624511 1828489 := bbase (se 2 (by rfl) ⟨685683, by rfl⟩ : syracuseStep 1828489 = 1371367) (by norm_num)
theorem B4114061 : Blo 1624511 4114061 := bbase (se 3 (by rfl) ⟨771386, by rfl⟩ : syracuseStep 4114061 = 1542773) (by norm_num)
theorem B2057881 : Blo 1624511 2057881 := bbase (se 2 (by rfl) ⟨771705, by rfl⟩ : syracuseStep 2057881 = 1543411) (by norm_num)
theorem B1828525 : Blo 1624511 1828525 := bbase (se 3 (by rfl) ⟨342848, by rfl⟩ : syracuseStep 1828525 = 685697) (by norm_num)
theorem B3655349 : Blo 1624511 3655349 := bbase (se 5 (by rfl) ⟨171344, by rfl⟩ : syracuseStep 3655349 = 342689) (by norm_num)
theorem B1828561 : Blo 1624511 1828561 := bbase (se 2 (by rfl) ⟨685710, by rfl⟩ : syracuseStep 1828561 = 1371421) (by norm_num)
theorem B1828597 : Blo 1624511 1828597 := bbase (se 5 (by rfl) ⟨85715, by rfl⟩ : syracuseStep 1828597 = 171431) (by norm_num)
theorem B2057977 : Blo 1624511 2057977 := bbase (se 2 (by rfl) ⟨771741, by rfl⟩ : syracuseStep 2057977 = 1543483) (by norm_num)
theorem B3655421 : Blo 1624511 3655421 := bbase (se 3 (by rfl) ⟨685391, by rfl⟩ : syracuseStep 3655421 = 1370783) (by norm_num)
theorem B1828633 : Blo 1624511 1828633 := bbase (se 2 (by rfl) ⟨685737, by rfl⟩ : syracuseStep 1828633 = 1371475) (by norm_num)
theorem B1828669 : Blo 1624511 1828669 := bbase (se 3 (by rfl) ⟨342875, by rfl⟩ : syracuseStep 1828669 = 685751) (by norm_num)
theorem B3655493 : Blo 1624511 3655493 := bbase (se 4 (by rfl) ⟨342702, by rfl⟩ : syracuseStep 3655493 = 685405) (by norm_num)
theorem B4114253 : Blo 1624511 4114253 := bbase (se 3 (by rfl) ⟨771422, by rfl⟩ : syracuseStep 4114253 = 1542845) (by norm_num)
theorem B1828705 : Blo 1624511 1828705 := bbase (se 2 (by rfl) ⟨685764, by rfl⟩ : syracuseStep 1828705 = 1371529) (by norm_num)
theorem B1828741 : Blo 1624511 1828741 := bbase (se 4 (by rfl) ⟨171444, by rfl⟩ : syracuseStep 1828741 = 342889) (by norm_num)
theorem B3655565 : Blo 1624511 3655565 := bbase (se 3 (by rfl) ⟨685418, by rfl⟩ : syracuseStep 3655565 = 1370837) (by norm_num)
theorem B2058149 : Blo 1624511 2058149 := bbase (se 4 (by rfl) ⟨192951, by rfl⟩ : syracuseStep 2058149 = 385903) (by norm_num)
theorem B1828777 : Blo 1624511 1828777 := bbase (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) (by norm_num)
theorem B1828813 : Blo 1624511 1828813 := bbase (se 3 (by rfl) ⟨342902, by rfl⟩ : syracuseStep 1828813 = 685805) (by norm_num)
theorem B3655637 : Blo 1624511 3655637 := bbase (se 7 (by rfl) ⟨42839, by rfl⟩ : syracuseStep 3655637 = 85679) (by norm_num)
theorem B2058205 : Blo 1624511 2058205 := bbase (se 3 (by rfl) ⟨385913, by rfl⟩ : syracuseStep 2058205 = 771827) (by norm_num)
theorem B1828849 : Blo 1624511 1828849 := bbase (se 2 (by rfl) ⟨685818, by rfl⟩ : syracuseStep 1828849 = 1371637) (by norm_num)
theorem B4630517 : Blo 1624511 4630517 := bbase (se 5 (by rfl) ⟨217055, by rfl⟩ : syracuseStep 4630517 = 434111) (by norm_num)
theorem B1828885 : Blo 1624511 1828885 := bbase (se 6 (by rfl) ⟨42864, by rfl⟩ : syracuseStep 1828885 = 85729) (by norm_num)
theorem B3655709 : Blo 1624511 3655709 := bbase (se 3 (by rfl) ⟨685445, by rfl⟩ : syracuseStep 3655709 = 1370891) (by norm_num)
theorem B1828921 : Blo 1624511 1828921 := bbase (se 2 (by rfl) ⟨685845, by rfl⟩ : syracuseStep 1828921 = 1371691) (by norm_num)
theorem B2058301 : Blo 1624511 2058301 := bbase (se 3 (by rfl) ⟨385931, by rfl⟩ : syracuseStep 2058301 = 771863) (by norm_num)
theorem B1853533 : Blo 1624511 1853533 := bbase (se 3 (by rfl) ⟨347537, by rfl⟩ : syracuseStep 1853533 = 695075) (by norm_num)
theorem B1828957 : Blo 1624511 1828957 := bbase (se 3 (by rfl) ⟨342929, by rfl⟩ : syracuseStep 1828957 = 685859) (by norm_num)
theorem B3655781 : Blo 1624511 3655781 := bbase (se 4 (by rfl) ⟨342729, by rfl⟩ : syracuseStep 3655781 = 685459) (by norm_num)
theorem B1828993 : Blo 1624511 1828993 := bbase (se 2 (by rfl) ⟨685872, by rfl⟩ : syracuseStep 1828993 = 1371745) (by norm_num)
theorem B5859461 : Blo 1624511 5859461 := bbase (se 4 (by rfl) ⟨549324, by rfl⟩ : syracuseStep 5859461 = 1098649) (by norm_num)
theorem B1951885 : Blo 1624511 1951885 := bbase (se 3 (by rfl) ⟨365978, by rfl⟩ : syracuseStep 1951885 = 731957) (by norm_num)
theorem B4114597 : Blo 1624511 4114597 := bbase (se 4 (by rfl) ⟨385743, by rfl⟩ : syracuseStep 4114597 = 771487) (by norm_num)
theorem B1829029 : Blo 1624511 1829029 := bbase (se 4 (by rfl) ⟨171471, by rfl⟩ : syracuseStep 1829029 = 342943) (by norm_num)
theorem B3655853 : Blo 1624511 3655853 := bbase (se 3 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 3655853 = 1370945) (by norm_num)
theorem B1829065 : Blo 1624511 1829065 := bbase (se 2 (by rfl) ⟨685899, by rfl⟩ : syracuseStep 1829065 = 1371799) (by norm_num)
theorem B2058473 : Blo 1624511 2058473 := bbase (se 2 (by rfl) ⟨771927, by rfl⟩ : syracuseStep 2058473 = 1543855) (by norm_num)
theorem B1951981 : Blo 1624511 1951981 := bbase (se 3 (by rfl) ⟨365996, by rfl⟩ : syracuseStep 1951981 = 731993) (by norm_num)
theorem B1829101 : Blo 1624511 1829101 := bbase (se 3 (by rfl) ⟨342956, by rfl⟩ : syracuseStep 1829101 = 685913) (by norm_num)
theorem B3655925 : Blo 1624511 3655925 := bbase (se 5 (by rfl) ⟨171371, by rfl⟩ : syracuseStep 3655925 = 342743) (by norm_num)
theorem B1829137 : Blo 1624511 1829137 := bbase (se 2 (by rfl) ⟨685926, by rfl⟩ : syracuseStep 1829137 = 1371853) (by norm_num)
theorem B4114709 : Blo 1624511 4114709 := bbase (se 6 (by rfl) ⟨96438, by rfl⟩ : syracuseStep 4114709 = 192877) (by norm_num)
theorem B2058529 : Blo 1624511 2058529 := bbase (se 2 (by rfl) ⟨771948, by rfl⟩ : syracuseStep 2058529 = 1543897) (by norm_num)
theorem B1829173 : Blo 1624511 1829173 := bbase (se 5 (by rfl) ⟨85742, by rfl⟩ : syracuseStep 1829173 = 171485) (by norm_num)
theorem B3655997 : Blo 1624511 3655997 := bbase (se 3 (by rfl) ⟨685499, by rfl⟩ : syracuseStep 3655997 = 1370999) (by norm_num)
theorem B1829209 : Blo 1624511 1829209 := bbase (se 2 (by rfl) ⟨685953, by rfl⟩ : syracuseStep 1829209 = 1371907) (by norm_num)
theorem B1829245 : Blo 1624511 1829245 := bbase (se 3 (by rfl) ⟨342983, by rfl⟩ : syracuseStep 1829245 = 685967) (by norm_num)
theorem B3656069 : Blo 1624511 3656069 := bbase (se 4 (by rfl) ⟨342756, by rfl⟩ : syracuseStep 3656069 = 685513) (by norm_num)
theorem B1829281 : Blo 1624511 1829281 := bbase (se 2 (by rfl) ⟨685980, by rfl⟩ : syracuseStep 1829281 = 1371961) (by norm_num)
theorem B1829317 : Blo 1624511 1829317 := bbase (se 4 (by rfl) ⟨171498, by rfl⟩ : syracuseStep 1829317 = 342997) (by norm_num)
theorem B3656141 : Blo 1624511 3656141 := bbase (se 3 (by rfl) ⟨685526, by rfl⟩ : syracuseStep 3656141 = 1371053) (by norm_num)
theorem B4114901 : Blo 1624511 4114901 := bbase (se 7 (by rfl) ⟨48221, by rfl⟩ : syracuseStep 4114901 = 96443) (by norm_num)
theorem B1829353 : Blo 1624511 1829353 := bbase (se 2 (by rfl) ⟨686007, by rfl⟩ : syracuseStep 1829353 = 1372015) (by norm_num)
theorem B5482997 : Blo 1624511 5482997 := bbase (se 5 (by rfl) ⟨257015, by rfl⟩ : syracuseStep 5482997 = 514031) (by norm_num)
theorem B1829389 : Blo 1624511 1829389 := bbase (se 3 (by rfl) ⟨343010, by rfl⟩ : syracuseStep 1829389 = 686021) (by norm_num)
theorem B3656213 : Blo 1624511 3656213 := bbase (se 6 (by rfl) ⟨85692, by rfl⟩ : syracuseStep 3656213 = 171385) (by norm_num)
theorem B1829425 : Blo 1624511 1829425 := bbase (se 2 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 1829425 = 1372069) (by norm_num)
theorem B1829461 : Blo 1624511 1829461 := bbase (se 8 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 1829461 = 21439) (by norm_num)
theorem B3656285 : Blo 1624511 3656285 := bbase (se 3 (by rfl) ⟨685553, by rfl⟩ : syracuseStep 3656285 = 1371107) (by norm_num)
theorem B1829497 : Blo 1624511 1829497 := bbase (se 2 (by rfl) ⟨686061, by rfl⟩ : syracuseStep 1829497 = 1372123) (by norm_num)
theorem B1829533 : Blo 1624511 1829533 := bbase (se 3 (by rfl) ⟨343037, by rfl⟩ : syracuseStep 1829533 = 686075) (by norm_num)
theorem B3656357 : Blo 1624511 3656357 := bbase (se 4 (by rfl) ⟨342783, by rfl⟩ : syracuseStep 3656357 = 685567) (by norm_num)
theorem B8227493 : Blo 1624511 8227493 := bbase (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) (by norm_num)
theorem B1829569 : Blo 1624511 1829569 := bbase (se 2 (by rfl) ⟨686088, by rfl⟩ : syracuseStep 1829569 = 1372177) (by norm_num)
theorem B1854149 : Blo 1624511 1854149 := bbase (se 4 (by rfl) ⟨173826, by rfl⟩ : syracuseStep 1854149 = 347653) (by norm_num)
theorem B4238021 : Blo 1624511 4238021 := bbase (se 4 (by rfl) ⟨397314, by rfl⟩ : syracuseStep 4238021 = 794629) (by norm_num)
theorem B6171349 : Blo 1624511 6171349 := bbase (se 7 (by rfl) ⟨72320, by rfl⟩ : syracuseStep 6171349 = 144641) (by norm_num)
theorem B1829605 : Blo 1624511 1829605 := bbase (se 4 (by rfl) ⟨171525, by rfl⟩ : syracuseStep 1829605 = 343051) (by norm_num)
theorem B4631269 : Blo 1624511 4631269 := bbase (se 4 (by rfl) ⟨434181, by rfl⟩ : syracuseStep 4631269 = 868363) (by norm_num)
theorem B2968301 : Blo 1624511 2968301 := bbase (se 3 (by rfl) ⟨556556, by rfl⟩ : syracuseStep 2968301 = 1113113) (by norm_num)
theorem B3656429 : Blo 1624511 3656429 := bbase (se 3 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 3656429 = 1371161) (by norm_num)
theorem B1829641 : Blo 1624511 1829641 := bbase (se 2 (by rfl) ⟨686115, by rfl⟩ : syracuseStep 1829641 = 1372231) (by norm_num)
theorem B4115245 : Blo 1624511 4115245 := bbase (se 3 (by rfl) ⟨771608, by rfl⟩ : syracuseStep 4115245 = 1543217) (by norm_num)
theorem B3296045 : Blo 1624511 3296045 := bbase (se 3 (by rfl) ⟨618008, by rfl⟩ : syracuseStep 3296045 = 1236017) (by norm_num)
theorem B1829677 : Blo 1624511 1829677 := bbase (se 3 (by rfl) ⟨343064, by rfl⟩ : syracuseStep 1829677 = 686129) (by norm_num)
theorem B3656501 : Blo 1624511 3656501 := bbase (se 5 (by rfl) ⟨171398, by rfl⟩ : syracuseStep 3656501 = 342797) (by norm_num)
theorem B1829713 : Blo 1624511 1829713 := bbase (se 2 (by rfl) ⟨686142, by rfl⟩ : syracuseStep 1829713 = 1372285) (by norm_num)
theorem B46877525 : Blo 1624511 46877525 := bbase (se 9 (by rfl) ⟨137336, by rfl⟩ : syracuseStep 46877525 = 274673) (by norm_num)
theorem B1829749 : Blo 1624511 1829749 := bbase (se 5 (by rfl) ⟨85769, by rfl⟩ : syracuseStep 1829749 = 171539) (by norm_num)
theorem B3656573 : Blo 1624511 3656573 := bbase (se 3 (by rfl) ⟨685607, by rfl⟩ : syracuseStep 3656573 = 1371215) (by norm_num)
theorem B4451221 : Blo 1624511 4451221 := bbase (se 6 (by rfl) ⟨104325, by rfl⟩ : syracuseStep 4451221 = 208651) (by norm_num)
theorem B1829785 : Blo 1624511 1829785 := bbase (se 2 (by rfl) ⟨686169, by rfl⟩ : syracuseStep 1829785 = 1372339) (by norm_num)
theorem B4115357 : Blo 1624511 4115357 := bbase (se 3 (by rfl) ⟨771629, by rfl⟩ : syracuseStep 4115357 = 1543259) (by norm_num)
theorem B5483429 : Blo 1624511 5483429 := bbase (se 4 (by rfl) ⟨514071, by rfl⟩ : syracuseStep 5483429 = 1028143) (by norm_num)
theorem B1829821 : Blo 1624511 1829821 := bbase (se 3 (by rfl) ⟨343091, by rfl⟩ : syracuseStep 1829821 = 686183) (by norm_num)
theorem B3656645 : Blo 1624511 3656645 := bbase (se 4 (by rfl) ⟨342810, by rfl⟩ : syracuseStep 3656645 = 685621) (by norm_num)
theorem B6171653 : Blo 1624511 6171653 := bbase (se 4 (by rfl) ⟨578592, by rfl⟩ : syracuseStep 6171653 = 1157185) (by norm_num)
theorem B3656717 : Blo 1624511 3656717 := bbase (se 3 (by rfl) ⟨685634, by rfl⟩ : syracuseStep 3656717 = 1371269) (by norm_num)
theorem B3705917 : Blo 1624511 3705917 := bbase (se 3 (by rfl) ⟨694859, by rfl⟩ : syracuseStep 3705917 = 1389719) (by norm_num)
theorem B3656789 : Blo 1624511 3656789 := bbase (se 8 (by rfl) ⟨21426, by rfl⟩ : syracuseStep 3656789 = 42853) (by norm_num)
theorem B4115549 : Blo 1624511 4115549 := bbase (se 3 (by rfl) ⟨771665, by rfl⟩ : syracuseStep 4115549 = 1543331) (by norm_num)
theorem B3656861 : Blo 1624511 3656861 := bbase (se 3 (by rfl) ⟨685661, by rfl⟩ : syracuseStep 3656861 = 1371323) (by norm_num)
theorem B7613621 : Blo 1624511 7613621 := bbase (se 5 (by rfl) ⟨356888, by rfl⟩ : syracuseStep 7613621 = 713777) (by norm_num)
theorem B1952957 : Blo 1624511 1952957 := bbase (se 3 (by rfl) ⟨366179, by rfl⟩ : syracuseStep 1952957 = 732359) (by norm_num)
theorem B4943045 : Blo 1624511 4943045 := bbase (se 4 (by rfl) ⟨463410, by rfl⟩ : syracuseStep 4943045 = 926821) (by norm_num)
theorem B2927821 : Blo 1624511 2927821 := bbase (se 3 (by rfl) ⟨548966, by rfl⟩ : syracuseStep 2927821 = 1097933) (by norm_num)
theorem B3656933 : Blo 1624511 3656933 := bbase (se 4 (by rfl) ⟨342837, by rfl⟩ : syracuseStep 3656933 = 685675) (by norm_num)
theorem B2927885 : Blo 1624511 2927885 := bbase (se 3 (by rfl) ⟨548978, by rfl⟩ : syracuseStep 2927885 = 1097957) (by norm_num)
theorem B3657005 : Blo 1624511 3657005 := bbase (se 3 (by rfl) ⟨685688, by rfl⟩ : syracuseStep 3657005 = 1371377) (by norm_num)
theorem B5483861 : Blo 1624511 5483861 := bbase (se 11 (by rfl) ⟨4016, by rfl⟩ : syracuseStep 5483861 = 8033) (by norm_num)
theorem B3657077 : Blo 1624511 3657077 := bbase (se 5 (by rfl) ⟨171425, by rfl⟩ : syracuseStep 3657077 = 342851) (by norm_num)
theorem B2313613 : Blo 1624511 2313613 := bbase (se 3 (by rfl) ⟨433802, by rfl⟩ : syracuseStep 2313613 = 867605) (by norm_num)
theorem B4115893 : Blo 1624511 4115893 := bbase (se 5 (by rfl) ⟨192932, by rfl⟩ : syracuseStep 4115893 = 385865) (by norm_num)
theorem B3657149 : Blo 1624511 3657149 := bbase (se 3 (by rfl) ⟨685715, by rfl⟩ : syracuseStep 3657149 = 1371431) (by norm_num)
theorem B3657221 : Blo 1624511 3657221 := bbase (se 4 (by rfl) ⟨342864, by rfl⟩ : syracuseStep 3657221 = 685729) (by norm_num)
theorem B4451861 : Blo 1624511 4451861 := bbase (se 6 (by rfl) ⟨104340, by rfl⟩ : syracuseStep 4451861 = 208681) (by norm_num)
theorem B7810597 : Blo 1624511 7810597 := bbase (se 4 (by rfl) ⟨732243, by rfl⟩ : syracuseStep 7810597 = 1464487) (by norm_num)
theorem B4394533 : Blo 1624511 4394533 := bbase (se 4 (by rfl) ⟨411987, by rfl⟩ : syracuseStep 4394533 = 823975) (by norm_num)
theorem B4116005 : Blo 1624511 4116005 := bbase (se 4 (by rfl) ⟨385875, by rfl⟩ : syracuseStep 4116005 = 771751) (by norm_num)
theorem B3657293 : Blo 1624511 3657293 := bbase (se 3 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 3657293 = 1371485) (by norm_num)
theorem B3657365 : Blo 1624511 3657365 := bbase (se 6 (by rfl) ⟨85719, by rfl⟩ : syracuseStep 3657365 = 171439) (by norm_num)
theorem B1953433 : Blo 1624511 1953433 := bbase (se 2 (by rfl) ⟨732537, by rfl⟩ : syracuseStep 1953433 = 1465075) (by norm_num)
theorem B2436773 : Blo 1624511 2436773 := bbase (se 4 (by rfl) ⟨228447, by rfl⟩ : syracuseStep 2436773 = 456895) (by norm_num)
theorem B1953461 : Blo 1624511 1953461 := bbase (se 5 (by rfl) ⟨91568, by rfl⟩ : syracuseStep 1953461 = 183137) (by norm_num)
theorem B2436797 : Blo 1624511 2436797 := bbase (se 3 (by rfl) ⟨456899, by rfl⟩ : syracuseStep 2436797 = 913799) (by norm_num)
theorem B2436821 : Blo 1624511 2436821 := bbase (se 7 (by rfl) ⟨28556, by rfl⟩ : syracuseStep 2436821 = 57113) (by norm_num)
theorem B2313949 : Blo 1624511 2313949 := bbase (se 3 (by rfl) ⟨433865, by rfl⟩ : syracuseStep 2313949 = 867731) (by norm_num)
theorem B3657437 : Blo 1624511 3657437 := bbase (se 3 (by rfl) ⟨685769, by rfl⟩ : syracuseStep 3657437 = 1371539) (by norm_num)
theorem B4116197 : Blo 1624511 4116197 := bbase (se 4 (by rfl) ⟨385893, by rfl⟩ : syracuseStep 4116197 = 771787) (by norm_num)
theorem B2436845 : Blo 1624511 2436845 := bbase (se 3 (by rfl) ⟨456908, by rfl⟩ : syracuseStep 2436845 = 913817) (by norm_num)
theorem B2436869 : Blo 1624511 2436869 := bbase (se 4 (by rfl) ⟨228456, by rfl⟩ : syracuseStep 2436869 = 456913) (by norm_num)
theorem B5484293 : Blo 1624511 5484293 := bbase (se 4 (by rfl) ⟨514152, by rfl⟩ : syracuseStep 5484293 = 1028305) (by norm_num)
theorem B9252629 : Blo 1624511 9252629 := bbase (se 6 (by rfl) ⟨216858, by rfl⟩ : syracuseStep 9252629 = 433717) (by norm_num)
theorem B2436893 : Blo 1624511 2436893 := bbase (se 3 (by rfl) ⟨456917, by rfl⟩ : syracuseStep 2436893 = 913835) (by norm_num)
theorem B3657509 : Blo 1624511 3657509 := bbase (se 4 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 3657509 = 685783) (by norm_num)
theorem B2436917 : Blo 1624511 2436917 := bbase (se 5 (by rfl) ⟨114230, by rfl⟩ : syracuseStep 2436917 = 228461) (by norm_num)
theorem B2436941 : Blo 1624511 2436941 := bbase (se 3 (by rfl) ⟨456926, by rfl⟩ : syracuseStep 2436941 = 913853) (by norm_num)
theorem B240422741 : Blo 1624511 240422741 := bbase (se 9 (by rfl) ⟨704363, by rfl⟩ : syracuseStep 240422741 = 1408727) (by norm_num)
theorem B2436965 : Blo 1624511 2436965 := bbase (se 4 (by rfl) ⟨228465, by rfl⟩ : syracuseStep 2436965 = 456931) (by norm_num)
theorem B3657581 : Blo 1624511 3657581 := bbase (se 3 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 3657581 = 1371593) (by norm_num)
theorem B3084149 : Blo 1624511 3084149 := bbase (se 5 (by rfl) ⟨144569, by rfl⟩ : syracuseStep 3084149 = 289139) (by norm_num)
theorem B1953649 : Blo 1624511 1953649 := bbase (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) (by norm_num)
theorem B2436989 : Blo 1624511 2436989 := bbase (se 3 (by rfl) ⟨456935, by rfl⟩ : syracuseStep 2436989 = 913871) (by norm_num)
theorem B2437013 : Blo 1624511 2437013 := bbase (se 6 (by rfl) ⟨57117, by rfl⟩ : syracuseStep 2437013 = 114235) (by norm_num)
theorem B9891733 : Blo 1624511 9891733 := bbase (se 6 (by rfl) ⟨231837, by rfl⟩ : syracuseStep 9891733 = 463675) (by norm_num)
theorem B2437037 : Blo 1624511 2437037 := bbase (se 3 (by rfl) ⟨456944, by rfl⟩ : syracuseStep 2437037 = 913889) (by norm_num)
theorem B2314165 : Blo 1624511 2314165 := bbase (se 5 (by rfl) ⟨108476, by rfl⟩ : syracuseStep 2314165 = 216953) (by norm_num)
theorem B8228789 : Blo 1624511 8228789 := bbase (se 5 (by rfl) ⟨385724, by rfl⟩ : syracuseStep 8228789 = 771449) (by norm_num)
theorem B3657653 : Blo 1624511 3657653 := bbase (se 5 (by rfl) ⟨171452, by rfl⟩ : syracuseStep 3657653 = 342905) (by norm_num)
theorem B2437061 : Blo 1624511 2437061 := bbase (se 4 (by rfl) ⟨228474, by rfl⟩ : syracuseStep 2437061 = 456949) (by norm_num)
theorem B2437085 : Blo 1624511 2437085 := bbase (se 3 (by rfl) ⟨456953, by rfl⟩ : syracuseStep 2437085 = 913907) (by norm_num)
theorem B1953769 : Blo 1624511 1953769 := bbase (se 2 (by rfl) ⟨732663, by rfl⟩ : syracuseStep 1953769 = 1465327) (by norm_num)
theorem B2437109 : Blo 1624511 2437109 := bbase (se 5 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 2437109 = 228479) (by norm_num)
theorem B2928629 : Blo 1624511 2928629 := bbase (se 5 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 2928629 = 274559) (by norm_num)
theorem B3657725 : Blo 1624511 3657725 := bbase (se 3 (by rfl) ⟨685823, by rfl⟩ : syracuseStep 3657725 = 1371647) (by norm_num)
theorem B3084293 : Blo 1624511 3084293 := bbase (se 4 (by rfl) ⟨289152, by rfl⟩ : syracuseStep 3084293 = 578305) (by norm_num)
theorem B2437133 : Blo 1624511 2437133 := bbase (se 3 (by rfl) ⟨456962, by rfl⟩ : syracuseStep 2437133 = 913925) (by norm_num)
theorem B2437157 : Blo 1624511 2437157 := bbase (se 4 (by rfl) ⟨228483, by rfl⟩ : syracuseStep 2437157 = 456967) (by norm_num)
theorem B2437181 : Blo 1624511 2437181 := bbase (se 3 (by rfl) ⟨456971, by rfl⟩ : syracuseStep 2437181 = 913943) (by norm_num)
theorem B4116541 : Blo 1624511 4116541 := bbase (se 3 (by rfl) ⟨771851, by rfl⟩ : syracuseStep 4116541 = 1543703) (by norm_num)
theorem B3960893 : Blo 1624511 3960893 := bbase (se 3 (by rfl) ⟨742667, by rfl⟩ : syracuseStep 3960893 = 1485335) (by norm_num)
theorem B3657797 : Blo 1624511 3657797 := bbase (se 4 (by rfl) ⟨342918, by rfl⟩ : syracuseStep 3657797 = 685837) (by norm_num)
theorem B2437205 : Blo 1624511 2437205 := bbase (se 8 (by rfl) ⟨14280, by rfl⟩ : syracuseStep 2437205 = 28561) (by norm_num)
theorem B13176917 : Blo 1624511 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B26357845 : Blo 1624511 26357845 := bbase (se 8 (by rfl) ⟨154440, by rfl⟩ : syracuseStep 26357845 = 308881) (by norm_num)
theorem B2437229 : Blo 1624511 2437229 := bbase (se 3 (by rfl) ⟨456980, by rfl⟩ : syracuseStep 2437229 = 913961) (by norm_num)
theorem B2437253 : Blo 1624511 2437253 := bbase (se 4 (by rfl) ⟨228492, by rfl⟩ : syracuseStep 2437253 = 456985) (by norm_num)
theorem B3657869 : Blo 1624511 3657869 := bbase (se 3 (by rfl) ⟨685850, by rfl⟩ : syracuseStep 3657869 = 1371701) (by norm_num)
theorem B2437277 : Blo 1624511 2437277 := bbase (se 3 (by rfl) ⟨456989, by rfl⟩ : syracuseStep 2437277 = 913979) (by norm_num)
theorem B4116653 : Blo 1624511 4116653 := bbase (se 3 (by rfl) ⟨771872, by rfl⟩ : syracuseStep 4116653 = 1543745) (by norm_num)
theorem B2437301 : Blo 1624511 2437301 := bbase (se 5 (by rfl) ⟨114248, by rfl⟩ : syracuseStep 2437301 = 228497) (by norm_num)
theorem B5484725 : Blo 1624511 5484725 := bbase (se 5 (by rfl) ⟨257096, by rfl⟩ : syracuseStep 5484725 = 514193) (by norm_num)
theorem B2437325 : Blo 1624511 2437325 := bbase (se 3 (by rfl) ⟨456998, by rfl⟩ : syracuseStep 2437325 = 913997) (by norm_num)
theorem B3518677 : Blo 1624511 3518677 := bbase (se 7 (by rfl) ⟨41234, by rfl⟩ : syracuseStep 3518677 = 82469) (by norm_num)
theorem B3657941 : Blo 1624511 3657941 := bbase (se 7 (by rfl) ⟨42866, by rfl⟩ : syracuseStep 3657941 = 85733) (by norm_num)
theorem B2437349 : Blo 1624511 2437349 := bbase (se 4 (by rfl) ⟨228501, by rfl⟩ : syracuseStep 2437349 = 457003) (by norm_num)
theorem B2437373 : Blo 1624511 2437373 := bbase (se 3 (by rfl) ⟨457007, by rfl⟩ : syracuseStep 2437373 = 914015) (by norm_num)
theorem B2437397 : Blo 1624511 2437397 := bbase (se 6 (by rfl) ⟨57126, by rfl⟩ : syracuseStep 2437397 = 114253) (by norm_num)
theorem B2928917 : Blo 1624511 2928917 := bbase (se 6 (by rfl) ⟨68646, by rfl⟩ : syracuseStep 2928917 = 137293) (by norm_num)
theorem B3658013 : Blo 1624511 3658013 := bbase (se 3 (by rfl) ⟨685877, by rfl⟩ : syracuseStep 3658013 = 1371755) (by norm_num)
theorem B3084581 : Blo 1624511 3084581 := bbase (se 4 (by rfl) ⟨289179, by rfl⟩ : syracuseStep 3084581 = 578359) (by norm_num)
theorem B2437421 : Blo 1624511 2437421 := bbase (se 3 (by rfl) ⟨457016, by rfl⟩ : syracuseStep 2437421 = 914033) (by norm_num)
theorem B2314541 : Blo 1624511 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B2437445 : Blo 1624511 2437445 := bbase (se 4 (by rfl) ⟨228510, by rfl⟩ : syracuseStep 2437445 = 457021) (by norm_num)
theorem B2437469 : Blo 1624511 2437469 := bbase (se 3 (by rfl) ⟨457025, by rfl⟩ : syracuseStep 2437469 = 914051) (by norm_num)
theorem B3658085 : Blo 1624511 3658085 := bbase (se 4 (by rfl) ⟨342945, by rfl⟩ : syracuseStep 3658085 = 685891) (by norm_num)
theorem B4116845 : Blo 1624511 4116845 := bbase (se 3 (by rfl) ⟨771908, by rfl⟩ : syracuseStep 4116845 = 1543817) (by norm_num)
theorem B2437493 : Blo 1624511 2437493 := bbase (se 5 (by rfl) ⟨114257, by rfl⟩ : syracuseStep 2437493 = 228515) (by norm_num)
theorem B2437517 : Blo 1624511 2437517 := bbase (se 3 (by rfl) ⟨457034, by rfl⟩ : syracuseStep 2437517 = 914069) (by norm_num)
theorem B2437541 : Blo 1624511 2437541 := bbase (se 4 (by rfl) ⟨228519, by rfl⟩ : syracuseStep 2437541 = 457039) (by norm_num)
theorem B3658157 : Blo 1624511 3658157 := bbase (se 3 (by rfl) ⟨685904, by rfl⟩ : syracuseStep 3658157 = 1371809) (by norm_num)
theorem B3084733 : Blo 1624511 3084733 := bbase (se 3 (by rfl) ⟨578387, by rfl⟩ : syracuseStep 3084733 = 1156775) (by norm_num)
theorem B2437565 : Blo 1624511 2437565 := bbase (se 3 (by rfl) ⟨457043, by rfl⟩ : syracuseStep 2437565 = 914087) (by norm_num)
theorem B2437589 : Blo 1624511 2437589 := bbase (se 7 (by rfl) ⟨28565, by rfl⟩ : syracuseStep 2437589 = 57131) (by norm_num)
theorem B2437613 : Blo 1624511 2437613 := bbase (se 3 (by rfl) ⟨457052, by rfl⟩ : syracuseStep 2437613 = 914105) (by norm_num)
theorem B3658229 : Blo 1624511 3658229 := bbase (se 5 (by rfl) ⟨171479, by rfl⟩ : syracuseStep 3658229 = 342959) (by norm_num)
theorem B2437637 : Blo 1624511 2437637 := bbase (se 4 (by rfl) ⟨228528, by rfl⟩ : syracuseStep 2437637 = 457057) (by norm_num)
theorem B2470429 : Blo 1624511 2470429 := bbase (se 3 (by rfl) ⟨463205, by rfl⟩ : syracuseStep 2470429 = 926411) (by norm_num)
theorem B2437661 : Blo 1624511 2437661 := bbase (se 3 (by rfl) ⟨457061, by rfl⟩ : syracuseStep 2437661 = 914123) (by norm_num)
theorem B2437685 : Blo 1624511 2437685 := bbase (se 5 (by rfl) ⟨114266, by rfl⟩ : syracuseStep 2437685 = 228533) (by norm_num)
theorem B3658301 : Blo 1624511 3658301 := bbase (se 3 (by rfl) ⟨685931, by rfl⟩ : syracuseStep 3658301 = 1371863) (by norm_num)
theorem B2437709 : Blo 1624511 2437709 := bbase (se 3 (by rfl) ⟨457070, by rfl⟩ : syracuseStep 2437709 = 914141) (by norm_num)
theorem B18526805 : Blo 1624511 18526805 := bbase (se 8 (by rfl) ⟨108555, by rfl⟩ : syracuseStep 18526805 = 217111) (by norm_num)
theorem B2437733 : Blo 1624511 2437733 := bbase (se 4 (by rfl) ⟨228537, by rfl⟩ : syracuseStep 2437733 = 457075) (by norm_num)
theorem B5485157 : Blo 1624511 5485157 := bbase (se 4 (by rfl) ⟨514233, by rfl⟩ : syracuseStep 5485157 = 1028467) (by norm_num)
theorem B2437757 : Blo 1624511 2437757 := bbase (se 3 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 2437757 = 914159) (by norm_num)
theorem B3658373 : Blo 1624511 3658373 := bbase (se 4 (by rfl) ⟨342972, by rfl⟩ : syracuseStep 3658373 = 685945) (by norm_num)
theorem B2437781 : Blo 1624511 2437781 := bbase (se 6 (by rfl) ⟨57135, by rfl⟩ : syracuseStep 2437781 = 114271) (by norm_num)
theorem B5206693 : Blo 1624511 5206693 := bbase (se 4 (by rfl) ⟨488127, by rfl⟩ : syracuseStep 5206693 = 976255) (by norm_num)
theorem B2437805 : Blo 1624511 2437805 := bbase (se 3 (by rfl) ⟨457088, by rfl⟩ : syracuseStep 2437805 = 914177) (by norm_num)
theorem B2437829 : Blo 1624511 2437829 := bbase (se 4 (by rfl) ⟨228546, by rfl⟩ : syracuseStep 2437829 = 457093) (by norm_num)
theorem B3658445 : Blo 1624511 3658445 := bbase (se 3 (by rfl) ⟨685958, by rfl⟩ : syracuseStep 3658445 = 1371917) (by norm_num)
theorem B2437853 : Blo 1624511 2437853 := bbase (se 3 (by rfl) ⟨457097, by rfl⟩ : syracuseStep 2437853 = 914195) (by norm_num)
theorem B7516901 : Blo 1624511 7516901 := bbase (se 4 (by rfl) ⟨704709, by rfl⟩ : syracuseStep 7516901 = 1409419) (by norm_num)
theorem B3085037 : Blo 1624511 3085037 := bbase (se 3 (by rfl) ⟨578444, by rfl⟩ : syracuseStep 3085037 = 1156889) (by norm_num)
theorem B2437877 : Blo 1624511 2437877 := bbase (se 5 (by rfl) ⟨114275, by rfl⟩ : syracuseStep 2437877 = 228551) (by norm_num)
theorem B2437901 : Blo 1624511 2437901 := bbase (se 3 (by rfl) ⟨457106, by rfl⟩ : syracuseStep 2437901 = 914213) (by norm_num)
theorem B3658517 : Blo 1624511 3658517 := bbase (se 6 (by rfl) ⟨85746, by rfl⟩ : syracuseStep 3658517 = 171493) (by norm_num)
theorem B2437925 : Blo 1624511 2437925 := bbase (se 4 (by rfl) ⟨228555, by rfl⟩ : syracuseStep 2437925 = 457111) (by norm_num)
theorem B2437949 : Blo 1624511 2437949 := bbase (se 3 (by rfl) ⟨457115, by rfl⟩ : syracuseStep 2437949 = 914231) (by norm_num)
theorem B2437973 : Blo 1624511 2437973 := bbase (se 9 (by rfl) ⟨7142, by rfl⟩ : syracuseStep 2437973 = 14285) (by norm_num)
theorem B3658589 : Blo 1624511 3658589 := bbase (se 3 (by rfl) ⟨685985, by rfl⟩ : syracuseStep 3658589 = 1371971) (by norm_num)
theorem B6943589 : Blo 1624511 6943589 := bbase (se 4 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 6943589 = 1301923) (by norm_num)
theorem B2437997 : Blo 1624511 2437997 := bbase (se 3 (by rfl) ⟨457124, by rfl⟩ : syracuseStep 2437997 = 914249) (by norm_num)
theorem B2438021 : Blo 1624511 2438021 := bbase (se 4 (by rfl) ⟨228564, by rfl⟩ : syracuseStep 2438021 = 457129) (by norm_num)
theorem B2438045 : Blo 1624511 2438045 := bbase (se 3 (by rfl) ⟨457133, by rfl⟩ : syracuseStep 2438045 = 914267) (by norm_num)
theorem B3658661 : Blo 1624511 3658661 := bbase (se 4 (by rfl) ⟨342999, by rfl⟩ : syracuseStep 3658661 = 685999) (by norm_num)
theorem B2438069 : Blo 1624511 2438069 := bbase (se 5 (by rfl) ⟨114284, by rfl⟩ : syracuseStep 2438069 = 228569) (by norm_num)
theorem B5952437 : Blo 1624511 5952437 := bbase (se 5 (by rfl) ⟨279020, by rfl⟩ : syracuseStep 5952437 = 558041) (by norm_num)
theorem B2438093 : Blo 1624511 2438093 := bbase (se 3 (by rfl) ⟨457142, by rfl⟩ : syracuseStep 2438093 = 914285) (by norm_num)
theorem B2085841 : Blo 1624511 2085841 := bbase (se 2 (by rfl) ⟨782190, by rfl⟩ : syracuseStep 2085841 = 1564381) (by norm_num)
theorem B3707869 : Blo 1624511 3707869 := bbase (se 3 (by rfl) ⟨695225, by rfl⟩ : syracuseStep 3707869 = 1390451) (by norm_num)
theorem B2438117 : Blo 1624511 2438117 := bbase (se 4 (by rfl) ⟨228573, by rfl⟩ : syracuseStep 2438117 = 457147) (by norm_num)
theorem B3658733 : Blo 1624511 3658733 := bbase (se 3 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 3658733 = 1372025) (by norm_num)
theorem B2438141 : Blo 1624511 2438141 := bbase (se 3 (by rfl) ⟨457151, by rfl⟩ : syracuseStep 2438141 = 914303) (by norm_num)
theorem B2470933 : Blo 1624511 2470933 := bbase (se 6 (by rfl) ⟨57912, by rfl⟩ : syracuseStep 2470933 = 115825) (by norm_num)
theorem B5485589 : Blo 1624511 5485589 := bbase (se 6 (by rfl) ⟨128568, by rfl⟩ : syracuseStep 5485589 = 257137) (by norm_num)
theorem B2438165 : Blo 1624511 2438165 := bbase (se 6 (by rfl) ⟨57144, by rfl⟩ : syracuseStep 2438165 = 114289) (by norm_num)
theorem B2438189 : Blo 1624511 2438189 := bbase (se 3 (by rfl) ⟨457160, by rfl⟩ : syracuseStep 2438189 = 914321) (by norm_num)
theorem B3658805 : Blo 1624511 3658805 := bbase (se 5 (by rfl) ⟨171506, by rfl⟩ : syracuseStep 3658805 = 343013) (by norm_num)
theorem B2438213 : Blo 1624511 2438213 := bbase (se 4 (by rfl) ⟨228582, by rfl⟩ : syracuseStep 2438213 = 457165) (by norm_num)
theorem B6173765 : Blo 1624511 6173765 := bbase (se 4 (by rfl) ⟨578790, by rfl⟩ : syracuseStep 6173765 = 1157581) (by norm_num)
theorem B2438237 : Blo 1624511 2438237 := bbase (se 3 (by rfl) ⟨457169, by rfl⟩ : syracuseStep 2438237 = 914339) (by norm_num)
theorem B2438261 : Blo 1624511 2438261 := bbase (se 5 (by rfl) ⟨114293, by rfl⟩ : syracuseStep 2438261 = 228587) (by norm_num)
theorem B3658877 : Blo 1624511 3658877 := bbase (se 3 (by rfl) ⟨686039, by rfl⟩ : syracuseStep 3658877 = 1372079) (by norm_num)
theorem B2970749 : Blo 1624511 2970749 := bbase (se 3 (by rfl) ⟨557015, by rfl⟩ : syracuseStep 2970749 = 1114031) (by norm_num)
theorem B2438285 : Blo 1624511 2438285 := bbase (se 3 (by rfl) ⟨457178, by rfl⟩ : syracuseStep 2438285 = 914357) (by norm_num)
theorem B2438309 : Blo 1624511 2438309 := bbase (se 4 (by rfl) ⟨228591, by rfl⟩ : syracuseStep 2438309 = 457183) (by norm_num)
theorem B2438333 : Blo 1624511 2438333 := bbase (se 3 (by rfl) ⟨457187, by rfl⟩ : syracuseStep 2438333 = 914375) (by norm_num)
theorem B2602181 : Blo 1624511 2602181 := bbase (se 4 (by rfl) ⟨243954, by rfl⟩ : syracuseStep 2602181 = 487909) (by norm_num)
theorem B8230085 : Blo 1624511 8230085 := bbase (se 4 (by rfl) ⟨771570, by rfl⟩ : syracuseStep 8230085 = 1543141) (by norm_num)
theorem B3658949 : Blo 1624511 3658949 := bbase (se 4 (by rfl) ⟨343026, by rfl⟩ : syracuseStep 3658949 = 686053) (by norm_num)
theorem B46855381 : Blo 1624511 46855381 := bbase (se 7 (by rfl) ⟨549086, by rfl⟩ : syracuseStep 46855381 = 1098173) (by norm_num)
theorem B2438357 : Blo 1624511 2438357 := bbase (se 7 (by rfl) ⟨28574, by rfl⟩ : syracuseStep 2438357 = 57149) (by norm_num)
theorem B2741485 : Blo 1624511 2741485 := bbase (se 3 (by rfl) ⟨514028, by rfl⟩ : syracuseStep 2741485 = 1028057) (by norm_num)
theorem B2438381 : Blo 1624511 2438381 := bbase (se 3 (by rfl) ⟨457196, by rfl⟩ : syracuseStep 2438381 = 914393) (by norm_num)
theorem B2438405 : Blo 1624511 2438405 := bbase (se 4 (by rfl) ⟨228600, by rfl⟩ : syracuseStep 2438405 = 457201) (by norm_num)
theorem B3659021 : Blo 1624511 3659021 := bbase (se 3 (by rfl) ⟨686066, by rfl⟩ : syracuseStep 3659021 = 1372133) (by norm_num)
theorem B2438429 : Blo 1624511 2438429 := bbase (se 3 (by rfl) ⟨457205, by rfl⟩ : syracuseStep 2438429 = 914411) (by norm_num)
theorem B2438453 : Blo 1624511 2438453 := bbase (se 5 (by rfl) ⟨114302, by rfl⟩ : syracuseStep 2438453 = 228605) (by norm_num)
theorem B2741573 : Blo 1624511 2741573 := bbase (se 4 (by rfl) ⟨257022, by rfl⟩ : syracuseStep 2741573 = 514045) (by norm_num)
theorem B2438477 : Blo 1624511 2438477 := bbase (se 3 (by rfl) ⟨457214, by rfl⟩ : syracuseStep 2438477 = 914429) (by norm_num)
theorem B20821333 : Blo 1624511 20821333 := bbase (se 13 (by rfl) ⟨3812, by rfl⟩ : syracuseStep 20821333 = 7625) (by norm_num)
theorem B3659093 : Blo 1624511 3659093 := bbase (se 15 (by rfl) ⟨167, by rfl⟩ : syracuseStep 3659093 = 335) (by norm_num)
theorem B2438501 : Blo 1624511 2438501 := bbase (se 4 (by rfl) ⟨228609, by rfl⟩ : syracuseStep 2438501 = 457219) (by norm_num)
theorem B6174053 : Blo 1624511 6174053 := bbase (se 4 (by rfl) ⟨578817, by rfl⟩ : syracuseStep 6174053 = 1157635) (by norm_num)
theorem B3470701 : Blo 1624511 3470701 := bbase (se 3 (by rfl) ⟨650756, by rfl⟩ : syracuseStep 3470701 = 1301513) (by norm_num)
theorem B3904885 : Blo 1624511 3904885 := bbase (se 5 (by rfl) ⟨183041, by rfl⟩ : syracuseStep 3904885 = 366083) (by norm_num)
theorem B2438525 : Blo 1624511 2438525 := bbase (se 3 (by rfl) ⟨457223, by rfl⟩ : syracuseStep 2438525 = 914447) (by norm_num)
theorem B11122069 : Blo 1624511 11122069 := bbase (se 6 (by rfl) ⟨260673, by rfl⟩ : syracuseStep 11122069 = 521347) (by norm_num)
theorem B2438549 : Blo 1624511 2438549 := bbase (se 6 (by rfl) ⟨57153, by rfl⟩ : syracuseStep 2438549 = 114307) (by norm_num)
theorem B3659165 : Blo 1624511 3659165 := bbase (se 3 (by rfl) ⟨686093, by rfl⟩ : syracuseStep 3659165 = 1372187) (by norm_num)
theorem B2602405 : Blo 1624511 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B2438573 : Blo 1624511 2438573 := bbase (se 3 (by rfl) ⟨457232, by rfl⟩ : syracuseStep 2438573 = 914465) (by norm_num)
theorem B2741701 : Blo 1624511 2741701 := bbase (se 4 (by rfl) ⟨257034, by rfl⟩ : syracuseStep 2741701 = 514069) (by norm_num)
theorem B5486021 : Blo 1624511 5486021 := bbase (se 4 (by rfl) ⟨514314, by rfl⟩ : syracuseStep 5486021 = 1028629) (by norm_num)
theorem B2438597 : Blo 1624511 2438597 := bbase (se 4 (by rfl) ⟨228618, by rfl⟩ : syracuseStep 2438597 = 457237) (by norm_num)
theorem B3085789 : Blo 1624511 3085789 := bbase (se 3 (by rfl) ⟨578585, by rfl⟩ : syracuseStep 3085789 = 1157171) (by norm_num)
theorem B2438621 : Blo 1624511 2438621 := bbase (se 3 (by rfl) ⟨457241, by rfl⟩ : syracuseStep 2438621 = 914483) (by norm_num)
theorem B3659237 : Blo 1624511 3659237 := bbase (se 4 (by rfl) ⟨343053, by rfl⟩ : syracuseStep 3659237 = 686107) (by norm_num)
theorem B2438645 : Blo 1624511 2438645 := bbase (se 5 (by rfl) ⟨114311, by rfl⟩ : syracuseStep 2438645 = 228623) (by norm_num)
theorem B2438669 : Blo 1624511 2438669 := bbase (se 3 (by rfl) ⟨457250, by rfl⟩ : syracuseStep 2438669 = 914501) (by norm_num)
theorem B3339797 : Blo 1624511 3339797 := bbase (se 6 (by rfl) ⟨78276, by rfl⟩ : syracuseStep 3339797 = 156553) (by norm_num)
theorem B2741789 : Blo 1624511 2741789 := bbase (se 3 (by rfl) ⟨514085, by rfl⟩ : syracuseStep 2741789 = 1028171) (by norm_num)
theorem B2438693 : Blo 1624511 2438693 := bbase (se 4 (by rfl) ⟨228627, by rfl⟩ : syracuseStep 2438693 = 457255) (by norm_num)
theorem B3659309 : Blo 1624511 3659309 := bbase (se 3 (by rfl) ⟨686120, by rfl⟩ : syracuseStep 3659309 = 1372241) (by norm_num)
theorem B3905077 : Blo 1624511 3905077 := bbase (se 5 (by rfl) ⟨183050, by rfl⟩ : syracuseStep 3905077 = 366101) (by norm_num)
theorem B2438717 : Blo 1624511 2438717 := bbase (se 3 (by rfl) ⟨457259, by rfl⟩ : syracuseStep 2438717 = 914519) (by norm_num)
theorem B2438741 : Blo 1624511 2438741 := bbase (se 8 (by rfl) ⟨14289, by rfl⟩ : syracuseStep 2438741 = 28579) (by norm_num)
theorem B3905117 : Blo 1624511 3905117 := bbase (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) (by norm_num)
theorem B3085933 : Blo 1624511 3085933 := bbase (se 3 (by rfl) ⟨578612, by rfl⟩ : syracuseStep 3085933 = 1157225) (by norm_num)
theorem B2438765 : Blo 1624511 2438765 := bbase (se 3 (by rfl) ⟨457268, by rfl⟩ : syracuseStep 2438765 = 914537) (by norm_num)
theorem B3659381 : Blo 1624511 3659381 := bbase (se 5 (by rfl) ⟨171533, by rfl⟩ : syracuseStep 3659381 = 343067) (by norm_num)
theorem B2438789 : Blo 1624511 2438789 := bbase (se 4 (by rfl) ⟨228636, by rfl⟩ : syracuseStep 2438789 = 457273) (by norm_num)
theorem B2741917 : Blo 1624511 2741917 := bbase (se 3 (by rfl) ⟨514109, by rfl⟩ : syracuseStep 2741917 = 1028219) (by norm_num)
theorem B2438813 : Blo 1624511 2438813 := bbase (se 3 (by rfl) ⟨457277, by rfl⟩ : syracuseStep 2438813 = 914555) (by norm_num)
theorem B2438837 : Blo 1624511 2438837 := bbase (se 5 (by rfl) ⟨114320, by rfl⟩ : syracuseStep 2438837 = 228641) (by norm_num)
theorem B2930365 : Blo 1624511 2930365 := bbase (se 3 (by rfl) ⟨549443, by rfl⟩ : syracuseStep 2930365 = 1098887) (by norm_num)
theorem B3659453 : Blo 1624511 3659453 := bbase (se 3 (by rfl) ⟨686147, by rfl⟩ : syracuseStep 3659453 = 1372295) (by norm_num)
theorem B2438861 : Blo 1624511 2438861 := bbase (se 3 (by rfl) ⟨457286, by rfl⟩ : syracuseStep 2438861 = 914573) (by norm_num)
theorem B2438885 : Blo 1624511 2438885 := bbase (se 4 (by rfl) ⟨228645, by rfl⟩ : syracuseStep 2438885 = 457291) (by norm_num)
theorem B2742005 : Blo 1624511 2742005 := bbase (se 5 (by rfl) ⟨128531, by rfl⟩ : syracuseStep 2742005 = 257063) (by norm_num)
theorem B2438909 : Blo 1624511 2438909 := bbase (se 3 (by rfl) ⟨457295, by rfl⟩ : syracuseStep 2438909 = 914591) (by norm_num)
theorem B3659525 : Blo 1624511 3659525 := bbase (se 4 (by rfl) ⟨343080, by rfl⟩ : syracuseStep 3659525 = 686161) (by norm_num)
theorem B3086093 : Blo 1624511 3086093 := bbase (se 3 (by rfl) ⟨578642, by rfl⟩ : syracuseStep 3086093 = 1157285) (by norm_num)
theorem B2438933 : Blo 1624511 2438933 := bbase (se 6 (by rfl) ⟨57162, by rfl⟩ : syracuseStep 2438933 = 114325) (by norm_num)
theorem B2438957 : Blo 1624511 2438957 := bbase (se 3 (by rfl) ⟨457304, by rfl⟩ : syracuseStep 2438957 = 914609) (by norm_num)
theorem B2438981 : Blo 1624511 2438981 := bbase (se 4 (by rfl) ⟨228654, by rfl⟩ : syracuseStep 2438981 = 457309) (by norm_num)
theorem B2930509 : Blo 1624511 2930509 := bbase (se 3 (by rfl) ⟨549470, by rfl⟩ : syracuseStep 2930509 = 1098941) (by norm_num)
theorem B3659597 : Blo 1624511 3659597 := bbase (se 3 (by rfl) ⟨686174, by rfl⟩ : syracuseStep 3659597 = 1372349) (by norm_num)
theorem B2439005 : Blo 1624511 2439005 := bbase (se 3 (by rfl) ⟨457313, by rfl⟩ : syracuseStep 2439005 = 914627) (by norm_num)
theorem B2742133 : Blo 1624511 2742133 := bbase (se 5 (by rfl) ⟨128537, by rfl⟩ : syracuseStep 2742133 = 257075) (by norm_num)
theorem B5486453 : Blo 1624511 5486453 := bbase (se 5 (by rfl) ⟨257177, by rfl⟩ : syracuseStep 5486453 = 514355) (by norm_num)
theorem B2439029 : Blo 1624511 2439029 := bbase (se 5 (by rfl) ⟨114329, by rfl⟩ : syracuseStep 2439029 = 228659) (by norm_num)
theorem B3905405 : Blo 1624511 3905405 := bbase (se 3 (by rfl) ⟨732263, by rfl⟩ : syracuseStep 3905405 = 1464527) (by norm_num)
theorem B2439053 : Blo 1624511 2439053 := bbase (se 3 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 2439053 = 914645) (by norm_num)
theorem B4626325 : Blo 1624511 4626325 := bbase (se 6 (by rfl) ⟨108429, by rfl⟩ : syracuseStep 4626325 = 216859) (by norm_num)
theorem B3086237 : Blo 1624511 3086237 := bbase (se 3 (by rfl) ⟨578669, by rfl⟩ : syracuseStep 3086237 = 1157339) (by norm_num)
theorem B2439077 : Blo 1624511 2439077 := bbase (se 4 (by rfl) ⟨228663, by rfl⟩ : syracuseStep 2439077 = 457327) (by norm_num)
theorem B9254837 : Blo 1624511 9254837 := bbase (se 5 (by rfl) ⟨433820, by rfl⟩ : syracuseStep 9254837 = 867641) (by norm_num)
theorem B2439101 : Blo 1624511 2439101 := bbase (se 3 (by rfl) ⟨457331, by rfl⟩ : syracuseStep 2439101 = 914663) (by norm_num)
theorem B2742221 : Blo 1624511 2742221 := bbase (se 3 (by rfl) ⟨514166, by rfl⟩ : syracuseStep 2742221 = 1028333) (by norm_num)
theorem B6256597 : Blo 1624511 6256597 := bbase (se 7 (by rfl) ⟨73319, by rfl⟩ : syracuseStep 6256597 = 146639) (by norm_num)
theorem B2439125 : Blo 1624511 2439125 := bbase (se 7 (by rfl) ⟨28583, by rfl⟩ : syracuseStep 2439125 = 57167) (by norm_num)
theorem B2439149 : Blo 1624511 2439149 := bbase (se 3 (by rfl) ⟨457340, by rfl⟩ : syracuseStep 2439149 = 914681) (by norm_num)
theorem B1980397 : Blo 1624511 1980397 := bbase (se 3 (by rfl) ⟨371324, by rfl⟩ : syracuseStep 1980397 = 742649) (by norm_num)
theorem B5560325 : Blo 1624511 5560325 := bbase (se 4 (by rfl) ⟨521280, by rfl⟩ : syracuseStep 5560325 = 1042561) (by norm_num)
theorem B2439173 : Blo 1624511 2439173 := bbase (se 4 (by rfl) ⟨228672, by rfl⟩ : syracuseStep 2439173 = 457345) (by norm_num)
theorem B2439197 : Blo 1624511 2439197 := bbase (se 3 (by rfl) ⟨457349, by rfl⟩ : syracuseStep 2439197 = 914699) (by norm_num)
theorem B2439221 : Blo 1624511 2439221 := bbase (se 5 (by rfl) ⟨114338, by rfl⟩ : syracuseStep 2439221 = 228677) (by norm_num)
theorem B1669177 : Blo 1624511 1669177 := bbase (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) (by norm_num)
theorem B2742349 : Blo 1624511 2742349 := bbase (se 3 (by rfl) ⟨514190, by rfl⟩ : syracuseStep 2742349 = 1028381) (by norm_num)
theorem B2439245 : Blo 1624511 2439245 := bbase (se 3 (by rfl) ⟨457358, by rfl⟩ : syracuseStep 2439245 = 914717) (by norm_num)
theorem B2439269 : Blo 1624511 2439269 := bbase (se 4 (by rfl) ⟨228681, by rfl⟩ : syracuseStep 2439269 = 457363) (by norm_num)
theorem B2439293 : Blo 1624511 2439293 := bbase (se 3 (by rfl) ⟨457367, by rfl⟩ : syracuseStep 2439293 = 914735) (by norm_num)
theorem B2439317 : Blo 1624511 2439317 := bbase (se 6 (by rfl) ⟨57171, by rfl⟩ : syracuseStep 2439317 = 114343) (by norm_num)
theorem B2742437 : Blo 1624511 2742437 := bbase (se 4 (by rfl) ⟨257103, by rfl⟩ : syracuseStep 2742437 = 514207) (by norm_num)
theorem B2472101 : Blo 1624511 2472101 := bbase (se 4 (by rfl) ⟨231759, by rfl⟩ : syracuseStep 2472101 = 463519) (by norm_num)
theorem B2439341 : Blo 1624511 2439341 := bbase (se 3 (by rfl) ⟨457376, by rfl⟩ : syracuseStep 2439341 = 914753) (by norm_num)
theorem B3086525 : Blo 1624511 3086525 := bbase (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) (by norm_num)
theorem B2439365 : Blo 1624511 2439365 := bbase (se 4 (by rfl) ⟨228690, by rfl⟩ : syracuseStep 2439365 = 457381) (by norm_num)
theorem B2439389 : Blo 1624511 2439389 := bbase (se 3 (by rfl) ⟨457385, by rfl⟩ : syracuseStep 2439389 = 914771) (by norm_num)
theorem B3471589 : Blo 1624511 3471589 := bbase (se 4 (by rfl) ⟨325461, by rfl⟩ : syracuseStep 3471589 = 650923) (by norm_num)
theorem B2439413 : Blo 1624511 2439413 := bbase (se 5 (by rfl) ⟨114347, by rfl⟩ : syracuseStep 2439413 = 228695) (by norm_num)
theorem B2439437 : Blo 1624511 2439437 := bbase (se 3 (by rfl) ⟨457394, by rfl⟩ : syracuseStep 2439437 = 914789) (by norm_num)
theorem B1734949 : Blo 1624511 1734949 := bbase (se 4 (by rfl) ⟨162651, by rfl⟩ : syracuseStep 1734949 = 325303) (by norm_num)
theorem B2742565 : Blo 1624511 2742565 := bbase (se 4 (by rfl) ⟨257115, by rfl⟩ : syracuseStep 2742565 = 514231) (by norm_num)
theorem B5486885 : Blo 1624511 5486885 := bbase (se 4 (by rfl) ⟨514395, by rfl⟩ : syracuseStep 5486885 = 1028791) (by norm_num)
theorem B2472229 : Blo 1624511 2472229 := bbase (se 4 (by rfl) ⟨231771, by rfl⟩ : syracuseStep 2472229 = 463543) (by norm_num)
theorem B2439461 : Blo 1624511 2439461 := bbase (se 4 (by rfl) ⟨228699, by rfl⟩ : syracuseStep 2439461 = 457399) (by norm_num)
theorem B13367605 : Blo 1624511 13367605 := bbase (se 5 (by rfl) ⟨626606, by rfl⟩ : syracuseStep 13367605 = 1253213) (by norm_num)
theorem B2439485 : Blo 1624511 2439485 := bbase (se 3 (by rfl) ⟨457403, by rfl⟩ : syracuseStep 2439485 = 914807) (by norm_num)
theorem B3086677 : Blo 1624511 3086677 := bbase (se 10 (by rfl) ⟨4521, by rfl⟩ : syracuseStep 3086677 = 9043) (by norm_num)
theorem B2439509 : Blo 1624511 2439509 := bbase (se 10 (by rfl) ⟨3573, by rfl⟩ : syracuseStep 2439509 = 7147) (by norm_num)
theorem B2472301 : Blo 1624511 2472301 := bbase (se 3 (by rfl) ⟨463556, by rfl⟩ : syracuseStep 2472301 = 927113) (by norm_num)
theorem B2439533 : Blo 1624511 2439533 := bbase (se 3 (by rfl) ⟨457412, by rfl⟩ : syracuseStep 2439533 = 914825) (by norm_num)
theorem B2742653 : Blo 1624511 2742653 := bbase (se 3 (by rfl) ⟨514247, by rfl⟩ : syracuseStep 2742653 = 1028495) (by norm_num)
theorem B2439557 : Blo 1624511 2439557 := bbase (se 4 (by rfl) ⟨228708, by rfl⟩ : syracuseStep 2439557 = 457417) (by norm_num)
theorem B2439581 : Blo 1624511 2439581 := bbase (se 3 (by rfl) ⟨457421, by rfl⟩ : syracuseStep 2439581 = 914843) (by norm_num)
theorem B2439605 : Blo 1624511 2439605 := bbase (se 5 (by rfl) ⟨114356, by rfl⟩ : syracuseStep 2439605 = 228713) (by norm_num)
theorem B2439629 : Blo 1624511 2439629 := bbase (se 3 (by rfl) ⟨457430, by rfl⟩ : syracuseStep 2439629 = 914861) (by norm_num)
theorem B8231381 : Blo 1624511 8231381 := bbase (se 7 (by rfl) ⟨96461, by rfl⟩ : syracuseStep 8231381 = 192923) (by norm_num)
theorem B2439653 : Blo 1624511 2439653 := bbase (se 4 (by rfl) ⟨228717, by rfl⟩ : syracuseStep 2439653 = 457435) (by norm_num)
theorem B3709421 : Blo 1624511 3709421 := bbase (se 3 (by rfl) ⟨695516, by rfl⟩ : syracuseStep 3709421 = 1391033) (by norm_num)
theorem B2742781 : Blo 1624511 2742781 := bbase (se 3 (by rfl) ⟨514271, by rfl⟩ : syracuseStep 2742781 = 1028543) (by norm_num)
theorem B2439677 : Blo 1624511 2439677 := bbase (se 3 (by rfl) ⟨457439, by rfl⟩ : syracuseStep 2439677 = 914879) (by norm_num)
theorem B6175237 : Blo 1624511 6175237 := bbase (se 4 (by rfl) ⟨578928, by rfl⟩ : syracuseStep 6175237 = 1157857) (by norm_num)
theorem B2439701 : Blo 1624511 2439701 := bbase (se 6 (by rfl) ⟨57180, by rfl⟩ : syracuseStep 2439701 = 114361) (by norm_num)
theorem B2439725 : Blo 1624511 2439725 := bbase (se 3 (by rfl) ⟨457448, by rfl⟩ : syracuseStep 2439725 = 914897) (by norm_num)
theorem B2439749 : Blo 1624511 2439749 := bbase (se 4 (by rfl) ⟨228726, by rfl⟩ : syracuseStep 2439749 = 457453) (by norm_num)
theorem B2742869 : Blo 1624511 2742869 := bbase (se 8 (by rfl) ⟨16071, by rfl⟩ : syracuseStep 2742869 = 32143) (by norm_num)
theorem B133487189 : Blo 1624511 133487189 := bbase (se 8 (by rfl) ⟨782151, by rfl⟩ : syracuseStep 133487189 = 1564303) (by norm_num)
theorem B6945365 : Blo 1624511 6945365 := bbase (se 8 (by rfl) ⟨40695, by rfl⟩ : syracuseStep 6945365 = 81391) (by norm_num)
theorem B3086981 : Blo 1624511 3086981 := bbase (se 4 (by rfl) ⟨289404, by rfl⟩ : syracuseStep 3086981 = 578809) (by norm_num)
theorem B1735381 : Blo 1624511 1735381 := bbase (se 7 (by rfl) ⟨20336, by rfl⟩ : syracuseStep 1735381 = 40673) (by norm_num)
theorem B2742997 : Blo 1624511 2742997 := bbase (se 7 (by rfl) ⟨32144, by rfl⟩ : syracuseStep 2742997 = 64289) (by norm_num)
theorem B3472085 : Blo 1624511 3472085 := bbase (se 7 (by rfl) ⟨40688, by rfl⟩ : syracuseStep 3472085 = 81377) (by norm_num)
theorem B5487317 : Blo 1624511 5487317 := bbase (se 7 (by rfl) ⟨64304, by rfl⟩ : syracuseStep 5487317 = 128609) (by norm_num)
theorem B5855989 : Blo 1624511 5855989 := bbase (se 5 (by rfl) ⟨274499, by rfl⟩ : syracuseStep 5855989 = 548999) (by norm_num)
theorem B1735453 : Blo 1624511 1735453 := bbase (se 3 (by rfl) ⟨325397, by rfl⟩ : syracuseStep 1735453 = 650795) (by norm_num)
theorem B2743085 : Blo 1624511 2743085 := bbase (se 3 (by rfl) ⟨514328, by rfl⟩ : syracuseStep 2743085 = 1028657) (by norm_num)
theorem B2603821 : Blo 1624511 2603821 := bbase (se 3 (by rfl) ⟨488216, by rfl⟩ : syracuseStep 2603821 = 976433) (by norm_num)
theorem B6175541 : Blo 1624511 6175541 := bbase (se 5 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 6175541 = 578957) (by norm_num)
theorem B31652693 : Blo 1624511 31652693 := bbase (se 9 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 31652693 = 185465) (by norm_num)
theorem B2743213 : Blo 1624511 2743213 := bbase (se 3 (by rfl) ⟨514352, by rfl⟩ : syracuseStep 2743213 = 1028705) (by norm_num)
theorem B2743301 : Blo 1624511 2743301 := bbase (se 4 (by rfl) ⟨257184, by rfl⟩ : syracuseStep 2743301 = 514369) (by norm_num)
theorem B2604077 : Blo 1624511 2604077 := bbase (se 3 (by rfl) ⟨488264, by rfl⟩ : syracuseStep 2604077 = 976529) (by norm_num)
theorem B2743429 : Blo 1624511 2743429 := bbase (se 4 (by rfl) ⟨257196, by rfl⟩ : syracuseStep 2743429 = 514393) (by norm_num)
theorem B5487749 : Blo 1624511 5487749 := bbase (se 4 (by rfl) ⟨514476, by rfl⟩ : syracuseStep 5487749 = 1028953) (by norm_num)
theorem B1735825 : Blo 1624511 1735825 := bbase (se 2 (by rfl) ⟨650934, by rfl⟩ : syracuseStep 1735825 = 1301869) (by norm_num)
theorem B2743517 : Blo 1624511 2743517 := bbase (se 3 (by rfl) ⟨514409, by rfl⟩ : syracuseStep 2743517 = 1028819) (by norm_num)
theorem B2604269 : Blo 1624511 2604269 := bbase (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) (by norm_num)
theorem B13892917 : Blo 1624511 13892917 := bbase (se 5 (by rfl) ⟨651230, by rfl⟩ : syracuseStep 13892917 = 1302461) (by norm_num)
theorem B2743645 : Blo 1624511 2743645 := bbase (se 3 (by rfl) ⟨514433, by rfl⟩ : syracuseStep 2743645 = 1028867) (by norm_num)
theorem B7814501 : Blo 1624511 7814501 := bbase (se 4 (by rfl) ⟨732609, by rfl⟩ : syracuseStep 7814501 = 1465219) (by norm_num)
theorem B4627829 : Blo 1624511 4627829 := bbase (se 5 (by rfl) ⟨216929, by rfl⟩ : syracuseStep 4627829 = 433859) (by norm_num)
theorem B3087733 : Blo 1624511 3087733 := bbase (se 5 (by rfl) ⟨144737, by rfl⟩ : syracuseStep 3087733 = 289475) (by norm_num)
theorem B2743733 : Blo 1624511 2743733 := bbase (se 5 (by rfl) ⟨128612, by rfl⟩ : syracuseStep 2743733 = 257225) (by norm_num)
theorem B5209525 : Blo 1624511 5209525 := bbase (se 5 (by rfl) ⟨244196, by rfl⟩ : syracuseStep 5209525 = 488393) (by norm_num)
theorem B5938645 : Blo 1624511 5938645 := bbase (se 7 (by rfl) ⟨69593, by rfl⟩ : syracuseStep 5938645 = 139187) (by norm_num)
theorem B2538973 : Blo 1624511 2538973 := bbase (se 3 (by rfl) ⟨476057, by rfl⟩ : syracuseStep 2538973 = 952115) (by norm_num)
theorem B6684133 : Blo 1624511 6684133 := bbase (se 4 (by rfl) ⟨626637, by rfl⟩ : syracuseStep 6684133 = 1253275) (by norm_num)
theorem B5209589 : Blo 1624511 5209589 := bbase (se 5 (by rfl) ⟨244199, by rfl⟩ : syracuseStep 5209589 = 488399) (by norm_num)
theorem B1736201 : Blo 1624511 1736201 := bbase (se 2 (by rfl) ⟨651075, by rfl⟩ : syracuseStep 1736201 = 1302151) (by norm_num)
theorem B12344885 : Blo 1624511 12344885 := bbase (se 5 (by rfl) ⟨578666, by rfl⟩ : syracuseStep 12344885 = 1157333) (by norm_num)
theorem B2743861 : Blo 1624511 2743861 := bbase (se 5 (by rfl) ⟨128618, by rfl⟩ : syracuseStep 2743861 = 257237) (by norm_num)
theorem B3472949 : Blo 1624511 3472949 := bbase (se 5 (by rfl) ⟨162794, by rfl⟩ : syracuseStep 3472949 = 325589) (by norm_num)
theorem B5488181 : Blo 1624511 5488181 := bbase (se 5 (by rfl) ⟨257258, by rfl⟩ : syracuseStep 5488181 = 514517) (by norm_num)
theorem B6946357 : Blo 1624511 6946357 := bbase (se 5 (by rfl) ⟨325610, by rfl⟩ : syracuseStep 6946357 = 651221) (by norm_num)
theorem B1736273 : Blo 1624511 1736273 := bbase (se 2 (by rfl) ⟨651102, by rfl⟩ : syracuseStep 1736273 = 1302205) (by norm_num)
theorem B2743949 : Blo 1624511 2743949 := bbase (se 3 (by rfl) ⟨514490, by rfl⟩ : syracuseStep 2743949 = 1028981) (by norm_num)
theorem B3473093 : Blo 1624511 3473093 := bbase (se 4 (by rfl) ⟨325602, by rfl⟩ : syracuseStep 3473093 = 651205) (by norm_num)
theorem B8232677 : Blo 1624511 8232677 := bbase (se 4 (by rfl) ⟨771813, by rfl⟩ : syracuseStep 8232677 = 1543627) (by norm_num)
theorem B4112117 : Blo 1624511 4112117 := bbase (se 5 (by rfl) ⟨192755, by rfl⟩ : syracuseStep 4112117 = 385511) (by norm_num)
theorem B1736461 : Blo 1624511 1736461 := bbase (se 3 (by rfl) ⟨325586, by rfl⟩ : syracuseStep 1736461 = 651173) (by norm_num)
theorem B2744077 : Blo 1624511 2744077 := bbase (se 3 (by rfl) ⟨514514, by rfl⟩ : syracuseStep 2744077 = 1029029) (by norm_num)
theorem B2056033 : Blo 1624511 2056033 := bbase (se 2 (by rfl) ⟨771012, by rfl⟩ : syracuseStep 2056033 = 1542025) (by norm_num)
theorem B2744165 : Blo 1624511 2744165 := bbase (se 4 (by rfl) ⟨257265, by rfl⟩ : syracuseStep 2744165 = 514531) (by norm_num)
theorem B7511957 : Blo 1624511 7511957 := bbase (se 6 (by rfl) ⟨176061, by rfl⟩ : syracuseStep 7511957 = 352123) (by norm_num)
theorem B4112309 : Blo 1624511 4112309 := bbase (se 5 (by rfl) ⟨192764, by rfl⟩ : syracuseStep 4112309 = 385529) (by norm_num)
theorem B1736645 : Blo 1624511 1736645 := bbase (se 4 (by rfl) ⟨162810, by rfl⟩ : syracuseStep 1736645 = 325621) (by norm_num)
theorem B12337109 : Blo 1624511 12337109 := bbase (se 7 (by rfl) ⟨144575, by rfl⟩ : syracuseStep 12337109 = 289151) (by norm_num)
theorem B2744293 : Blo 1624511 2744293 := bbase (se 4 (by rfl) ⟨257277, by rfl⟩ : syracuseStep 2744293 = 514555) (by norm_num)
theorem B5488613 : Blo 1624511 5488613 := bbase (se 4 (by rfl) ⟨514557, by rfl⟩ : syracuseStep 5488613 = 1029115) (by norm_num)
theorem B14073845 : Blo 1624511 14073845 := bbase (se 5 (by rfl) ⟨659711, by rfl⟩ : syracuseStep 14073845 = 1319423) (by norm_num)
theorem B2056195 : Blo 1624511 2056195 := bstep (se 1 (by rfl) ⟨1542146, by rfl⟩ : syracuseStep 2056195 = 3084293) B3084293
theorem B5488721 : Blo 1624511 5488721 := bstep (se 2 (by rfl) ⟨2058270, by rfl⟩ : syracuseStep 5488721 = 4116541) B4116541
theorem B2744401 : Blo 1624511 2744401 := bstep (se 2 (by rfl) ⟨1029150, by rfl⟩ : syracuseStep 2744401 = 2058301) B2058301
theorem B1736803 : Blo 1624511 1736803 := bstep (se 1 (by rfl) ⟨1302602, by rfl⟩ : syracuseStep 1736803 = 2605205) B2605205
theorem B35143793 : Blo 1624511 35143793 := bstep (se 2 (by rfl) ⟨13178922, by rfl⟩ : syracuseStep 35143793 = 26357845) B26357845
theorem B2744435 : Blo 1624511 2744435 := bstep (se 1 (by rfl) ⟨2058326, by rfl⟩ : syracuseStep 2744435 = 4116653) B4116653
theorem B2195633 : Blo 1624511 2195633 := bstep (se 2 (by rfl) ⟨823362, by rfl⟩ : syracuseStep 2195633 = 1646725) B1646725
theorem B2744563 : Blo 1624511 2744563 := bstep (se 1 (by rfl) ⟨2058422, by rfl⟩ : syracuseStep 2744563 = 4116845) B4116845
theorem B2744705 : Blo 1624511 2744705 := bstep (se 2 (by rfl) ⟨1029264, by rfl⟩ : syracuseStep 2744705 = 2058529) B2058529
theorem B2056691 : Blo 1624511 2056691 := bstep (se 1 (by rfl) ⟨1542518, by rfl⟩ : syracuseStep 2056691 = 3085037) B3085037
theorem B13181453 : Blo 1624511 13181453 := bstep (se 3 (by rfl) ⟨2471522, by rfl⟩ : syracuseStep 13181453 = 4943045) B4943045
theorem B4629059 : Blo 1624511 4629059 := bstep (se 1 (by rfl) ⟨3471794, by rfl⟩ : syracuseStep 4629059 = 6943589) B6943589
theorem B4112977 : Blo 1624511 4112977 := bstep (se 2 (by rfl) ⟨1542366, by rfl⟩ : syracuseStep 4112977 = 3084733) B3084733
theorem B5489261 : Blo 1624511 5489261 := bstep (se 3 (by rfl) ⟨1029236, by rfl⟩ : syracuseStep 5489261 = 2058473) B2058473
theorem B5489315 : Blo 1624511 5489315 := bstep (se 1 (by rfl) ⟨4116986, by rfl⟩ : syracuseStep 5489315 = 8233973) B8233973
theorem B8233649 : Blo 1624511 8233649 := bstep (se 2 (by rfl) ⟨3087618, by rfl⟩ : syracuseStep 8233649 = 6175237) B6175237
theorem B7807693 : Blo 1624511 7807693 := bstep (se 3 (by rfl) ⟨1463942, by rfl⟩ : syracuseStep 7807693 = 2927885) B2927885
theorem B3293905 : Blo 1624511 3293905 := bstep (se 2 (by rfl) ⟨1235214, by rfl⟩ : syracuseStep 3293905 = 2470429) B2470429
theorem B8225549 : Blo 1624511 8225549 := bstep (se 3 (by rfl) ⟨1542290, by rfl⟩ : syracuseStep 8225549 = 3084581) B3084581
theorem B4113251 : Blo 1624511 4113251 := bstep (se 1 (by rfl) ⟨3084938, by rfl⟩ : syracuseStep 4113251 = 6169877) B6169877
theorem B1827715 : Blo 1624511 1827715 := bstep (se 1 (by rfl) ⟨1370786, by rfl⟩ : syracuseStep 1827715 = 2741573) B2741573
theorem B7807985 : Blo 1624511 7807985 := bstep (se 2 (by rfl) ⟨2927994, by rfl⟩ : syracuseStep 7807985 = 5855989) B5855989
theorem B1827859 : Blo 1624511 1827859 := bstep (se 1 (by rfl) ⟨1370894, by rfl⟩ : syracuseStep 1827859 = 2741789) B2741789
theorem B4113443 : Blo 1624511 4113443 := bstep (se 1 (by rfl) ⟨3085082, by rfl⟩ : syracuseStep 4113443 = 6170165) B6170165
theorem B4392077 : Blo 1624511 4392077 := bstep (se 3 (by rfl) ⟨823514, by rfl⟩ : syracuseStep 4392077 = 1647029) B1647029
theorem B1828003 : Blo 1624511 1828003 := bstep (se 1 (by rfl) ⟨1371002, by rfl⟩ : syracuseStep 1828003 = 2742005) B2742005
theorem B2057395 : Blo 1624511 2057395 := bstep (se 1 (by rfl) ⟨1543046, by rfl⟩ : syracuseStep 2057395 = 3086093) B3086093
theorem B18515141 : Blo 1624511 18515141 := bstep (se 4 (by rfl) ⟨1735794, by rfl⟩ : syracuseStep 18515141 = 3471589) B3471589
theorem B2057491 : Blo 1624511 2057491 := bstep (se 1 (by rfl) ⟨1543118, by rfl⟩ : syracuseStep 2057491 = 3086237) B3086237
theorem B6169891 : Blo 1624511 6169891 := bstep (se 1 (by rfl) ⟨4627418, by rfl⟩ : syracuseStep 6169891 = 9254837) B9254837
theorem B4941101 : Blo 1624511 4941101 := bstep (se 3 (by rfl) ⟨926456, by rfl⟩ : syracuseStep 4941101 = 1852913) B1852913
theorem B1828147 : Blo 1624511 1828147 := bstep (se 1 (by rfl) ⟨1371110, by rfl⟩ : syracuseStep 1828147 = 2742221) B2742221
theorem B2196833 : Blo 1624511 2196833 := bstep (se 2 (by rfl) ⟨823812, by rfl⟩ : syracuseStep 2196833 = 1647625) B1647625
theorem B4629869 : Blo 1624511 4629869 := bstep (se 3 (by rfl) ⟨868100, by rfl⟩ : syracuseStep 4629869 = 1736201) B1736201
theorem B3294577 : Blo 1624511 3294577 := bstep (se 2 (by rfl) ⟨1235466, by rfl⟩ : syracuseStep 3294577 = 2470933) B2470933
theorem B11871629 : Blo 1624511 11871629 := bstep (se 3 (by rfl) ⟨2225930, by rfl⟩ : syracuseStep 11871629 = 4451861) B4451861
theorem B8906125 : Blo 1624511 8906125 := bstep (se 3 (by rfl) ⟨1669898, by rfl⟩ : syracuseStep 8906125 = 3339797) B3339797
theorem B1828291 : Blo 1624511 1828291 := bstep (se 1 (by rfl) ⟨1371218, by rfl⟩ : syracuseStep 1828291 = 2742437) B2742437
theorem B1648067 : Blo 1624511 1648067 := bstep (se 1 (by rfl) ⟨1236050, by rfl⟩ : syracuseStep 1648067 = 2472101) B2472101
theorem B8783309 : Blo 1624511 8783309 := bstep (se 3 (by rfl) ⟨1646870, by rfl⟩ : syracuseStep 8783309 = 3293741) B3293741
theorem B4630061 : Blo 1624511 4630061 := bstep (se 3 (by rfl) ⟨868136, by rfl⟩ : syracuseStep 4630061 = 1736273) B1736273
theorem B1828435 : Blo 1624511 1828435 := bstep (se 1 (by rfl) ⟨1371326, by rfl⟩ : syracuseStep 1828435 = 2742653) B2742653
theorem B62473841 : Blo 1624511 62473841 := bstep (se 2 (by rfl) ⟨23427690, by rfl⟩ : syracuseStep 62473841 = 46855381) B46855381
theorem B3655313 : Blo 1624511 3655313 := bstep (se 2 (by rfl) ⟨1370742, by rfl⟩ : syracuseStep 3655313 = 2741485) B2741485
theorem B3655331 : Blo 1624511 3655331 := bstep (se 1 (by rfl) ⟨2741498, by rfl⟩ : syracuseStep 3655331 = 5482997) B5482997
theorem B1828579 : Blo 1624511 1828579 := bstep (se 1 (by rfl) ⟨1371434, by rfl⟩ : syracuseStep 1828579 = 2742869) B2742869
theorem B88991459 : Blo 1624511 88991459 := bstep (se 1 (by rfl) ⟨66743594, by rfl⟩ : syracuseStep 88991459 = 133487189) B133487189
theorem B18523889 : Blo 1624511 18523889 := bstep (se 2 (by rfl) ⟨6946458, by rfl⟩ : syracuseStep 18523889 = 13892917) B13892917
theorem B2057987 : Blo 1624511 2057987 := bstep (se 1 (by rfl) ⟨1543490, by rfl⟩ : syracuseStep 2057987 = 3086981) B3086981
theorem B14829425 : Blo 1624511 14829425 := bstep (se 2 (by rfl) ⟨5561034, by rfl⟩ : syracuseStep 14829425 = 11122069) B11122069
theorem B1828723 : Blo 1624511 1828723 := bstep (se 1 (by rfl) ⟨1371542, by rfl⟩ : syracuseStep 1828723 = 2743085) B2743085
theorem B2197363 : Blo 1624511 2197363 := bstep (se 1 (by rfl) ⟨1648022, by rfl⟩ : syracuseStep 2197363 = 3296045) B3296045
theorem B9258893 : Blo 1624511 9258893 := bstep (se 3 (by rfl) ⟨1736042, by rfl⟩ : syracuseStep 9258893 = 3472085) B3472085
theorem B3655601 : Blo 1624511 3655601 := bstep (se 2 (by rfl) ⟨1370850, by rfl⟩ : syracuseStep 3655601 = 2741701) B2741701
theorem B3655619 : Blo 1624511 3655619 := bstep (se 1 (by rfl) ⟨2741714, by rfl⟩ : syracuseStep 3655619 = 5483429) B5483429
theorem B3385297 : Blo 1624511 3385297 := bstep (se 2 (by rfl) ⟨1269486, by rfl⟩ : syracuseStep 3385297 = 2538973) B2538973
theorem B4114385 : Blo 1624511 4114385 := bstep (se 2 (by rfl) ⟨1542894, by rfl⟩ : syracuseStep 4114385 = 3085789) B3085789
theorem B4114435 : Blo 1624511 4114435 := bstep (se 1 (by rfl) ⟨3085826, by rfl⟩ : syracuseStep 4114435 = 6171653) B6171653
theorem B1828867 : Blo 1624511 1828867 := bstep (se 1 (by rfl) ⟨1371650, by rfl⟩ : syracuseStep 1828867 = 2743301) B2743301
theorem B10414129 : Blo 1624511 10414129 := bstep (se 2 (by rfl) ⟨3905298, by rfl⟩ : syracuseStep 10414129 = 7810597) B7810597
theorem B5859377 : Blo 1624511 5859377 := bstep (se 2 (by rfl) ⟨2197266, by rfl⟩ : syracuseStep 5859377 = 4394533) B4394533
theorem B4114577 : Blo 1624511 4114577 := bstep (se 2 (by rfl) ⟨1542966, by rfl⟩ : syracuseStep 4114577 = 3085933) B3085933
theorem B1829011 : Blo 1624511 1829011 := bstep (se 1 (by rfl) ⟨1371758, by rfl⟩ : syracuseStep 1829011 = 2743517) B2743517
theorem B3655889 : Blo 1624511 3655889 := bstep (se 2 (by rfl) ⟨1370958, by rfl⟩ : syracuseStep 3655889 = 2741917) B2741917
theorem B3655907 : Blo 1624511 3655907 := bstep (se 1 (by rfl) ⟨2741930, by rfl⟩ : syracuseStep 3655907 = 5483861) B5483861
theorem B1829155 : Blo 1624511 1829155 := bstep (se 1 (by rfl) ⟨1371866, by rfl⟩ : syracuseStep 1829155 = 2743733) B2743733
theorem B1829299 : Blo 1624511 1829299 := bstep (se 1 (by rfl) ⟨1371974, by rfl⟩ : syracuseStep 1829299 = 2743949) B2743949
theorem B1624515 : Blo 1624511 1624515 := bstep (se 1 (by rfl) ⟨1218386, by rfl⟩ : syracuseStep 1624515 = 2436773) B2436773
theorem B1624531 : Blo 1624511 1624531 := bstep (se 1 (by rfl) ⟨1218398, by rfl⟩ : syracuseStep 1624531 = 2436797) B2436797
theorem B1624547 : Blo 1624511 1624547 := bstep (se 1 (by rfl) ⟨1218410, by rfl⟩ : syracuseStep 1624547 = 2436821) B2436821
theorem B3656177 : Blo 1624511 3656177 := bstep (se 2 (by rfl) ⟨1371066, by rfl⟩ : syracuseStep 3656177 = 2742133) B2742133
theorem B1624563 : Blo 1624511 1624563 := bstep (se 1 (by rfl) ⟨1218422, by rfl⟩ : syracuseStep 1624563 = 2436845) B2436845
theorem B1624579 : Blo 1624511 1624579 := bstep (se 1 (by rfl) ⟨1218434, by rfl⟩ : syracuseStep 1624579 = 2436869) B2436869
theorem B3656195 : Blo 1624511 3656195 := bstep (se 1 (by rfl) ⟨2742146, by rfl⟩ : syracuseStep 3656195 = 5484293) B5484293
theorem B4631053 : Blo 1624511 4631053 := bstep (se 3 (by rfl) ⟨868322, by rfl⟩ : syracuseStep 4631053 = 1736645) B1736645
theorem B1624595 : Blo 1624511 1624595 := bstep (se 1 (by rfl) ⟨1218446, by rfl⟩ : syracuseStep 1624595 = 2436893) B2436893
theorem B1624611 : Blo 1624511 1624611 := bstep (se 1 (by rfl) ⟨1218458, by rfl⟩ : syracuseStep 1624611 = 2436917) B2436917
theorem B1624627 : Blo 1624511 1624627 := bstep (se 1 (by rfl) ⟨1218470, by rfl⟩ : syracuseStep 1624627 = 2436941) B2436941
theorem B1624643 : Blo 1624511 1624643 := bstep (se 1 (by rfl) ⟨1218482, by rfl⟩ : syracuseStep 1624643 = 2436965) B2436965
theorem B1829443 : Blo 1624511 1829443 := bstep (se 1 (by rfl) ⟨1372082, by rfl⟩ : syracuseStep 1829443 = 2744165) B2744165
theorem B1624659 : Blo 1624511 1624659 := bstep (se 1 (by rfl) ⟨1218494, by rfl⟩ : syracuseStep 1624659 = 2436989) B2436989
theorem B1624675 : Blo 1624511 1624675 := bstep (se 1 (by rfl) ⟨1218506, by rfl⟩ : syracuseStep 1624675 = 2437013) B2437013
theorem B5007971 : Blo 1624511 5007971 := bstep (se 1 (by rfl) ⟨3755978, by rfl⟩ : syracuseStep 5007971 = 7511957) B7511957
theorem B8342129 : Blo 1624511 8342129 := bstep (se 2 (by rfl) ⟨3128298, by rfl⟩ : syracuseStep 8342129 = 6256597) B6256597
theorem B1624691 : Blo 1624511 1624691 := bstep (se 1 (by rfl) ⟨1218518, by rfl⟩ : syracuseStep 1624691 = 2437037) B2437037
theorem B1624707 : Blo 1624511 1624707 := bstep (se 1 (by rfl) ⟨1218530, by rfl⟩ : syracuseStep 1624707 = 2437061) B2437061
theorem B37530253 : Blo 1624511 37530253 := bstep (se 3 (by rfl) ⟨7036922, by rfl⟩ : syracuseStep 37530253 = 14073845) B14073845
theorem B2640529 : Blo 1624511 2640529 := bstep (se 2 (by rfl) ⟨990198, by rfl⟩ : syracuseStep 2640529 = 1980397) B1980397
theorem B1624723 : Blo 1624511 1624723 := bstep (se 1 (by rfl) ⟨1218542, by rfl⟩ : syracuseStep 1624723 = 2437085) B2437085
theorem B1624739 : Blo 1624511 1624739 := bstep (se 1 (by rfl) ⟨1218554, by rfl⟩ : syracuseStep 1624739 = 2437109) B2437109
theorem B1952419 : Blo 1624511 1952419 := bstep (se 1 (by rfl) ⟨1464314, by rfl⟩ : syracuseStep 1952419 = 2928629) B2928629
theorem B1624755 : Blo 1624511 1624755 := bstep (se 1 (by rfl) ⟨1218566, by rfl⟩ : syracuseStep 1624755 = 2437133) B2437133
theorem B1624771 : Blo 1624511 1624771 := bstep (se 1 (by rfl) ⟨1218578, by rfl⟩ : syracuseStep 1624771 = 2437157) B2437157
theorem B5483213 : Blo 1624511 5483213 := bstep (se 3 (by rfl) ⟨1028102, by rfl⟩ : syracuseStep 5483213 = 2056205) B2056205
theorem B1624787 : Blo 1624511 1624787 := bstep (se 1 (by rfl) ⟨1218590, by rfl⟩ : syracuseStep 1624787 = 2437181) B2437181
theorem B1829587 : Blo 1624511 1829587 := bstep (se 1 (by rfl) ⟨1372190, by rfl⟩ : syracuseStep 1829587 = 2744381) B2744381
theorem B2640595 : Blo 1624511 2640595 := bstep (se 1 (by rfl) ⟨1980446, by rfl⟩ : syracuseStep 2640595 = 3960893) B3960893
theorem B1624803 : Blo 1624511 1624803 := bstep (se 1 (by rfl) ⟨1218602, by rfl⟩ : syracuseStep 1624803 = 2437205) B2437205
theorem B8784611 : Blo 1624511 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B1624819 : Blo 1624511 1624819 := bstep (se 1 (by rfl) ⟨1218614, by rfl⟩ : syracuseStep 1624819 = 2437229) B2437229
theorem B5483267 : Blo 1624511 5483267 := bstep (se 1 (by rfl) ⟨4112450, by rfl⟩ : syracuseStep 5483267 = 8224901) B8224901
theorem B1624835 : Blo 1624511 1624835 := bstep (se 1 (by rfl) ⟨1218626, by rfl⟩ : syracuseStep 1624835 = 2437253) B2437253
theorem B3656465 : Blo 1624511 3656465 := bstep (se 2 (by rfl) ⟨1371174, by rfl⟩ : syracuseStep 3656465 = 2742349) B2742349
theorem B1624851 : Blo 1624511 1624851 := bstep (se 1 (by rfl) ⟨1218638, by rfl⟩ : syracuseStep 1624851 = 2437277) B2437277
theorem B1624867 : Blo 1624511 1624867 := bstep (se 1 (by rfl) ⟨1218650, by rfl⟩ : syracuseStep 1624867 = 2437301) B2437301
theorem B3656483 : Blo 1624511 3656483 := bstep (se 1 (by rfl) ⟨2742362, by rfl⟩ : syracuseStep 3656483 = 5484725) B5484725
theorem B1624883 : Blo 1624511 1624883 := bstep (se 1 (by rfl) ⟨1218662, by rfl⟩ : syracuseStep 1624883 = 2437325) B2437325
theorem B1624899 : Blo 1624511 1624899 := bstep (se 1 (by rfl) ⟨1218674, by rfl⟩ : syracuseStep 1624899 = 2437349) B2437349
theorem B9882445 : Blo 1624511 9882445 := bstep (se 3 (by rfl) ⟨1852958, by rfl⟩ : syracuseStep 9882445 = 3705917) B3705917
theorem B1624915 : Blo 1624511 1624915 := bstep (se 1 (by rfl) ⟨1218686, by rfl⟩ : syracuseStep 1624915 = 2437373) B2437373
theorem B1624931 : Blo 1624511 1624931 := bstep (se 1 (by rfl) ⟨1218698, by rfl⟩ : syracuseStep 1624931 = 2437397) B2437397
theorem B1829731 : Blo 1624511 1829731 := bstep (se 1 (by rfl) ⟨1372298, by rfl⟩ : syracuseStep 1829731 = 2744597) B2744597
theorem B1624947 : Blo 1624511 1624947 := bstep (se 1 (by rfl) ⟨1218710, by rfl⟩ : syracuseStep 1624947 = 2437421) B2437421
theorem B1624963 : Blo 1624511 1624963 := bstep (se 1 (by rfl) ⟨1218722, by rfl⟩ : syracuseStep 1624963 = 2437445) B2437445
theorem B11275141 : Blo 1624511 11275141 := bstep (se 4 (by rfl) ⟨1057044, by rfl⟩ : syracuseStep 11275141 = 2114089) B2114089
theorem B1624979 : Blo 1624511 1624979 := bstep (se 1 (by rfl) ⟨1218734, by rfl⟩ : syracuseStep 1624979 = 2437469) B2437469
theorem B1624995 : Blo 1624511 1624995 := bstep (se 1 (by rfl) ⟨1218746, by rfl⟩ : syracuseStep 1624995 = 2437493) B2437493
theorem B1625011 : Blo 1624511 1625011 := bstep (se 1 (by rfl) ⟨1218758, by rfl⟩ : syracuseStep 1625011 = 2437517) B2437517
theorem B1625027 : Blo 1624511 1625027 := bstep (se 1 (by rfl) ⟨1218770, by rfl⟩ : syracuseStep 1625027 = 2437541) B2437541
theorem B1625043 : Blo 1624511 1625043 := bstep (se 1 (by rfl) ⟨1218782, by rfl⟩ : syracuseStep 1625043 = 2437565) B2437565
theorem B1625059 : Blo 1624511 1625059 := bstep (se 1 (by rfl) ⟨1218794, by rfl⟩ : syracuseStep 1625059 = 2437589) B2437589
theorem B1625075 : Blo 1624511 1625075 := bstep (se 1 (by rfl) ⟨1218806, by rfl⟩ : syracuseStep 1625075 = 2437613) B2437613
theorem B1625091 : Blo 1624511 1625091 := bstep (se 1 (by rfl) ⟨1218818, by rfl⟩ : syracuseStep 1625091 = 2437637) B2437637
theorem B5483537 : Blo 1624511 5483537 := bstep (se 2 (by rfl) ⟨2056326, by rfl⟩ : syracuseStep 5483537 = 4112653) B4112653
theorem B1625107 : Blo 1624511 1625107 := bstep (se 1 (by rfl) ⟨1218830, by rfl⟩ : syracuseStep 1625107 = 2437661) B2437661
theorem B1625123 : Blo 1624511 1625123 := bstep (se 1 (by rfl) ⟨1218842, by rfl⟩ : syracuseStep 1625123 = 2437685) B2437685
theorem B3656753 : Blo 1624511 3656753 := bstep (se 2 (by rfl) ⟨1371282, by rfl⟩ : syracuseStep 3656753 = 2742565) B2742565
theorem B3296305 : Blo 1624511 3296305 := bstep (se 2 (by rfl) ⟨1236114, by rfl⟩ : syracuseStep 3296305 = 2472229) B2472229
theorem B1625139 : Blo 1624511 1625139 := bstep (se 1 (by rfl) ⟨1218854, by rfl⟩ : syracuseStep 1625139 = 2437709) B2437709
theorem B1625155 : Blo 1624511 1625155 := bstep (se 1 (by rfl) ⟨1218866, by rfl⟩ : syracuseStep 1625155 = 2437733) B2437733
theorem B3656771 : Blo 1624511 3656771 := bstep (se 1 (by rfl) ⟨2742578, by rfl⟩ : syracuseStep 3656771 = 5485157) B5485157
theorem B1625171 : Blo 1624511 1625171 := bstep (se 1 (by rfl) ⟨1218878, by rfl⟩ : syracuseStep 1625171 = 2437757) B2437757
theorem B1625187 : Blo 1624511 1625187 := bstep (se 1 (by rfl) ⟨1218890, by rfl⟩ : syracuseStep 1625187 = 2437781) B2437781
theorem B4115569 : Blo 1624511 4115569 := bstep (se 2 (by rfl) ⟨1543338, by rfl⟩ : syracuseStep 4115569 = 3086677) B3086677
theorem B1625203 : Blo 1624511 1625203 := bstep (se 1 (by rfl) ⟨1218902, by rfl⟩ : syracuseStep 1625203 = 2437805) B2437805
theorem B1625219 : Blo 1624511 1625219 := bstep (se 1 (by rfl) ⟨1218914, by rfl⟩ : syracuseStep 1625219 = 2437829) B2437829
theorem B1625235 : Blo 1624511 1625235 := bstep (se 1 (by rfl) ⟨1218926, by rfl⟩ : syracuseStep 1625235 = 2437853) B2437853
theorem B1625251 : Blo 1624511 1625251 := bstep (se 1 (by rfl) ⟨1218938, by rfl⟩ : syracuseStep 1625251 = 2437877) B2437877
theorem B1625267 : Blo 1624511 1625267 := bstep (se 1 (by rfl) ⟨1218950, by rfl⟩ : syracuseStep 1625267 = 2437901) B2437901
theorem B1625283 : Blo 1624511 1625283 := bstep (se 1 (by rfl) ⟨1218962, by rfl⟩ : syracuseStep 1625283 = 2437925) B2437925
theorem B1625299 : Blo 1624511 1625299 := bstep (se 1 (by rfl) ⟨1218974, by rfl⟩ : syracuseStep 1625299 = 2437949) B2437949
theorem B2927843 : Blo 1624511 2927843 := bstep (se 1 (by rfl) ⟨2195882, by rfl⟩ : syracuseStep 2927843 = 4391765) B4391765
theorem B1625315 : Blo 1624511 1625315 := bstep (se 1 (by rfl) ⟨1218986, by rfl⟩ : syracuseStep 1625315 = 2437973) B2437973
theorem B1625331 : Blo 1624511 1625331 := bstep (se 1 (by rfl) ⟨1218998, by rfl⟩ : syracuseStep 1625331 = 2437997) B2437997
theorem B1625347 : Blo 1624511 1625347 := bstep (se 1 (by rfl) ⟨1219010, by rfl⟩ : syracuseStep 1625347 = 2438021) B2438021
theorem B1625363 : Blo 1624511 1625363 := bstep (se 1 (by rfl) ⟨1219022, by rfl⟩ : syracuseStep 1625363 = 2438045) B2438045
theorem B1625379 : Blo 1624511 1625379 := bstep (se 1 (by rfl) ⟨1219034, by rfl⟩ : syracuseStep 1625379 = 2438069) B2438069
theorem B3968291 : Blo 1624511 3968291 := bstep (se 1 (by rfl) ⟨2976218, by rfl⟩ : syracuseStep 3968291 = 5952437) B5952437
theorem B1625395 : Blo 1624511 1625395 := bstep (se 1 (by rfl) ⟨1219046, by rfl⟩ : syracuseStep 1625395 = 2438093) B2438093
theorem B1625411 : Blo 1624511 1625411 := bstep (se 1 (by rfl) ⟨1219058, by rfl⟩ : syracuseStep 1625411 = 2438117) B2438117
theorem B3657041 : Blo 1624511 3657041 := bstep (se 2 (by rfl) ⟨1371390, by rfl⟩ : syracuseStep 3657041 = 2742781) B2742781
theorem B1625427 : Blo 1624511 1625427 := bstep (se 1 (by rfl) ⟨1219070, by rfl⟩ : syracuseStep 1625427 = 2438141) B2438141
theorem B3657059 : Blo 1624511 3657059 := bstep (se 1 (by rfl) ⟨2742794, by rfl⟩ : syracuseStep 3657059 = 5485589) B5485589
theorem B1625443 : Blo 1624511 1625443 := bstep (se 1 (by rfl) ⟨1219082, by rfl⟩ : syracuseStep 1625443 = 2438165) B2438165
theorem B1625459 : Blo 1624511 1625459 := bstep (se 1 (by rfl) ⟨1219094, by rfl⟩ : syracuseStep 1625459 = 2438189) B2438189
theorem B1625475 : Blo 1624511 1625475 := bstep (se 1 (by rfl) ⟨1219106, by rfl⟩ : syracuseStep 1625475 = 2438213) B2438213
theorem B4115843 : Blo 1624511 4115843 := bstep (se 1 (by rfl) ⟨3086882, by rfl⟩ : syracuseStep 4115843 = 6173765) B6173765
theorem B7810445 : Blo 1624511 7810445 := bstep (se 3 (by rfl) ⟨1464458, by rfl⟩ : syracuseStep 7810445 = 2928917) B2928917
theorem B1625491 : Blo 1624511 1625491 := bstep (se 1 (by rfl) ⟨1219118, by rfl⟩ : syracuseStep 1625491 = 2438237) B2438237
theorem B1625507 : Blo 1624511 1625507 := bstep (se 1 (by rfl) ⟨1219130, by rfl⟩ : syracuseStep 1625507 = 2438261) B2438261
theorem B1625523 : Blo 1624511 1625523 := bstep (se 1 (by rfl) ⟨1219142, by rfl⟩ : syracuseStep 1625523 = 2438285) B2438285
theorem B1625539 : Blo 1624511 1625539 := bstep (se 1 (by rfl) ⟨1219154, by rfl⟩ : syracuseStep 1625539 = 2438309) B2438309
theorem B6172109 : Blo 1624511 6172109 := bstep (se 3 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 6172109 = 2314541) B2314541
theorem B1625555 : Blo 1624511 1625555 := bstep (se 1 (by rfl) ⟨1219166, by rfl⟩ : syracuseStep 1625555 = 2438333) B2438333
theorem B1625571 : Blo 1624511 1625571 := bstep (se 1 (by rfl) ⟨1219178, by rfl⟩ : syracuseStep 1625571 = 2438357) B2438357
theorem B1625587 : Blo 1624511 1625587 := bstep (se 1 (by rfl) ⟨1219190, by rfl⟩ : syracuseStep 1625587 = 2438381) B2438381
theorem B1625603 : Blo 1624511 1625603 := bstep (se 1 (by rfl) ⟨1219202, by rfl⟩ : syracuseStep 1625603 = 2438405) B2438405
theorem B1625619 : Blo 1624511 1625619 := bstep (se 1 (by rfl) ⟨1219214, by rfl⟩ : syracuseStep 1625619 = 2438429) B2438429
theorem B5205539 : Blo 1624511 5205539 := bstep (se 1 (by rfl) ⟨3904154, by rfl⟩ : syracuseStep 5205539 = 7808309) B7808309
theorem B1625635 : Blo 1624511 1625635 := bstep (se 1 (by rfl) ⟨1219226, by rfl⟩ : syracuseStep 1625635 = 2438453) B2438453
theorem B5484077 : Blo 1624511 5484077 := bstep (se 3 (by rfl) ⟨1028264, by rfl⟩ : syracuseStep 5484077 = 2056529) B2056529
theorem B6942257 : Blo 1624511 6942257 := bstep (se 2 (by rfl) ⟨2603346, by rfl⟩ : syracuseStep 6942257 = 5206693) B5206693
theorem B1625651 : Blo 1624511 1625651 := bstep (se 1 (by rfl) ⟨1219238, by rfl⟩ : syracuseStep 1625651 = 2438477) B2438477
theorem B1625667 : Blo 1624511 1625667 := bstep (se 1 (by rfl) ⟨1219250, by rfl⟩ : syracuseStep 1625667 = 2438501) B2438501
theorem B4116035 : Blo 1624511 4116035 := bstep (se 1 (by rfl) ⟨3087026, by rfl⟩ : syracuseStep 4116035 = 6174053) B6174053
theorem B1625683 : Blo 1624511 1625683 := bstep (se 1 (by rfl) ⟨1219262, by rfl⟩ : syracuseStep 1625683 = 2438525) B2438525
theorem B5484131 : Blo 1624511 5484131 := bstep (se 1 (by rfl) ⟨4113098, by rfl⟩ : syracuseStep 5484131 = 8226197) B8226197
theorem B1625699 : Blo 1624511 1625699 := bstep (se 1 (by rfl) ⟨1219274, by rfl⟩ : syracuseStep 1625699 = 2438549) B2438549
theorem B2313841 : Blo 1624511 2313841 := bstep (se 2 (by rfl) ⟨867690, by rfl⟩ : syracuseStep 2313841 = 1735381) B1735381
theorem B8228465 : Blo 1624511 8228465 := bstep (se 2 (by rfl) ⟨3085674, by rfl⟩ : syracuseStep 8228465 = 6171349) B6171349
theorem B3657329 : Blo 1624511 3657329 := bstep (se 2 (by rfl) ⟨1371498, by rfl⟩ : syracuseStep 3657329 = 2742997) B2742997
theorem B1625715 : Blo 1624511 1625715 := bstep (se 1 (by rfl) ⟨1219286, by rfl⟩ : syracuseStep 1625715 = 2438573) B2438573
theorem B3657347 : Blo 1624511 3657347 := bstep (se 1 (by rfl) ⟨2743010, by rfl⟩ : syracuseStep 3657347 = 5486021) B5486021
theorem B1625731 : Blo 1624511 1625731 := bstep (se 1 (by rfl) ⟨1219298, by rfl⟩ : syracuseStep 1625731 = 2438597) B2438597
theorem B1625747 : Blo 1624511 1625747 := bstep (se 1 (by rfl) ⟨1219310, by rfl⟩ : syracuseStep 1625747 = 2438621) B2438621
theorem B1625763 : Blo 1624511 1625763 := bstep (se 1 (by rfl) ⟨1219322, by rfl⟩ : syracuseStep 1625763 = 2438645) B2438645
theorem B2436785 : Blo 1624511 2436785 := bstep (se 2 (by rfl) ⟨913794, by rfl⟩ : syracuseStep 2436785 = 1827589) B1827589
theorem B2928305 : Blo 1624511 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B1625779 : Blo 1624511 1625779 := bstep (se 1 (by rfl) ⟨1219334, by rfl⟩ : syracuseStep 1625779 = 2438669) B2438669
theorem B2436803 : Blo 1624511 2436803 := bstep (se 1 (by rfl) ⟨1827602, by rfl⟩ : syracuseStep 2436803 = 3655205) B3655205
theorem B1625795 : Blo 1624511 1625795 := bstep (se 1 (by rfl) ⟨1219346, by rfl⟩ : syracuseStep 1625795 = 2438693) B2438693
theorem B2313937 : Blo 1624511 2313937 := bstep (se 2 (by rfl) ⟨867726, by rfl⟩ : syracuseStep 2313937 = 1735453) B1735453
theorem B1625811 : Blo 1624511 1625811 := bstep (se 1 (by rfl) ⟨1219358, by rfl⟩ : syracuseStep 1625811 = 2438717) B2438717
theorem B2436833 : Blo 1624511 2436833 := bstep (se 2 (by rfl) ⟨913812, by rfl⟩ : syracuseStep 2436833 = 1827625) B1827625
theorem B1625827 : Blo 1624511 1625827 := bstep (se 1 (by rfl) ⟨1219370, by rfl⟩ : syracuseStep 1625827 = 2438741) B2438741
theorem B2436851 : Blo 1624511 2436851 := bstep (se 1 (by rfl) ⟨1827638, by rfl⟩ : syracuseStep 2436851 = 3655277) B3655277
theorem B1625843 : Blo 1624511 1625843 := bstep (se 1 (by rfl) ⟨1219382, by rfl⟩ : syracuseStep 1625843 = 2438765) B2438765
theorem B1625859 : Blo 1624511 1625859 := bstep (se 1 (by rfl) ⟨1219394, by rfl⟩ : syracuseStep 1625859 = 2438789) B2438789
theorem B2436881 : Blo 1624511 2436881 := bstep (se 2 (by rfl) ⟨913830, by rfl⟩ : syracuseStep 2436881 = 1827661) B1827661
theorem B1625875 : Blo 1624511 1625875 := bstep (se 1 (by rfl) ⟨1219406, by rfl⟩ : syracuseStep 1625875 = 2438813) B2438813
theorem B2436899 : Blo 1624511 2436899 := bstep (se 1 (by rfl) ⟨1827674, by rfl⟩ : syracuseStep 2436899 = 3655349) B3655349
theorem B1625891 : Blo 1624511 1625891 := bstep (se 1 (by rfl) ⟨1219418, by rfl⟩ : syracuseStep 1625891 = 2438837) B2438837
theorem B1625907 : Blo 1624511 1625907 := bstep (se 1 (by rfl) ⟨1219430, by rfl⟩ : syracuseStep 1625907 = 2438861) B2438861
theorem B2436929 : Blo 1624511 2436929 := bstep (se 2 (by rfl) ⟨913848, by rfl⟩ : syracuseStep 2436929 = 1827697) B1827697
theorem B1625923 : Blo 1624511 1625923 := bstep (se 1 (by rfl) ⟨1219442, by rfl⟩ : syracuseStep 1625923 = 2438885) B2438885
theorem B2436947 : Blo 1624511 2436947 := bstep (se 1 (by rfl) ⟨1827710, by rfl⟩ : syracuseStep 2436947 = 3655421) B3655421
theorem B1625939 : Blo 1624511 1625939 := bstep (se 1 (by rfl) ⟨1219454, by rfl⟩ : syracuseStep 1625939 = 2438909) B2438909
theorem B1625955 : Blo 1624511 1625955 := bstep (se 1 (by rfl) ⟨1219466, by rfl⟩ : syracuseStep 1625955 = 2438933) B2438933
theorem B5934961 : Blo 1624511 5934961 := bstep (se 2 (by rfl) ⟨2225610, by rfl⟩ : syracuseStep 5934961 = 4451221) B4451221
theorem B2436977 : Blo 1624511 2436977 := bstep (se 2 (by rfl) ⟨913866, by rfl⟩ : syracuseStep 2436977 = 1827733) B1827733
theorem B5484401 : Blo 1624511 5484401 := bstep (se 2 (by rfl) ⟨2056650, by rfl⟩ : syracuseStep 5484401 = 4113301) B4113301
theorem B1625971 : Blo 1624511 1625971 := bstep (se 1 (by rfl) ⟨1219478, by rfl⟩ : syracuseStep 1625971 = 2438957) B2438957
theorem B2436995 : Blo 1624511 2436995 := bstep (se 1 (by rfl) ⟨1827746, by rfl⟩ : syracuseStep 2436995 = 3655493) B3655493
theorem B1625987 : Blo 1624511 1625987 := bstep (se 1 (by rfl) ⟨1219490, by rfl⟩ : syracuseStep 1625987 = 2438981) B2438981
theorem B3657617 : Blo 1624511 3657617 := bstep (se 2 (by rfl) ⟨1371606, by rfl⟩ : syracuseStep 3657617 = 2743213) B2743213
theorem B1626003 : Blo 1624511 1626003 := bstep (se 1 (by rfl) ⟨1219502, by rfl⟩ : syracuseStep 1626003 = 2439005) B2439005
theorem B2437025 : Blo 1624511 2437025 := bstep (se 2 (by rfl) ⟨913884, by rfl⟩ : syracuseStep 2437025 = 1827769) B1827769
theorem B3657635 : Blo 1624511 3657635 := bstep (se 1 (by rfl) ⟨2743226, by rfl⟩ : syracuseStep 3657635 = 5486453) B5486453
theorem B1626019 : Blo 1624511 1626019 := bstep (se 1 (by rfl) ⟨1219514, by rfl⟩ : syracuseStep 1626019 = 2439029) B2439029
theorem B2437043 : Blo 1624511 2437043 := bstep (se 1 (by rfl) ⟨1827782, by rfl⟩ : syracuseStep 2437043 = 3655565) B3655565
theorem B1626035 : Blo 1624511 1626035 := bstep (se 1 (by rfl) ⟨1219526, by rfl⟩ : syracuseStep 1626035 = 2439053) B2439053
theorem B1626051 : Blo 1624511 1626051 := bstep (se 1 (by rfl) ⟨1219538, by rfl⟩ : syracuseStep 1626051 = 2439077) B2439077
theorem B2437073 : Blo 1624511 2437073 := bstep (se 2 (by rfl) ⟨913902, by rfl⟩ : syracuseStep 2437073 = 1827805) B1827805
theorem B4943825 : Blo 1624511 4943825 := bstep (se 2 (by rfl) ⟨1853934, by rfl⟩ : syracuseStep 4943825 = 3707869) B3707869
theorem B1626067 : Blo 1624511 1626067 := bstep (se 1 (by rfl) ⟨1219550, by rfl⟩ : syracuseStep 1626067 = 2439101) B2439101
theorem B2437091 : Blo 1624511 2437091 := bstep (se 1 (by rfl) ⟨1827818, by rfl⟩ : syracuseStep 2437091 = 3655637) B3655637
theorem B1626083 : Blo 1624511 1626083 := bstep (se 1 (by rfl) ⟨1219562, by rfl⟩ : syracuseStep 1626083 = 2439125) B2439125
theorem B1626099 : Blo 1624511 1626099 := bstep (se 1 (by rfl) ⟨1219574, by rfl⟩ : syracuseStep 1626099 = 2439149) B2439149
theorem B2437121 : Blo 1624511 2437121 := bstep (se 2 (by rfl) ⟨913920, by rfl⟩ : syracuseStep 2437121 = 1827841) B1827841
theorem B3706883 : Blo 1624511 3706883 := bstep (se 1 (by rfl) ⟨2780162, by rfl⟩ : syracuseStep 3706883 = 5560325) B5560325
theorem B1626115 : Blo 1624511 1626115 := bstep (se 1 (by rfl) ⟨1219586, by rfl⟩ : syracuseStep 1626115 = 2439173) B2439173
theorem B2437139 : Blo 1624511 2437139 := bstep (se 1 (by rfl) ⟨1827854, by rfl⟩ : syracuseStep 2437139 = 3655709) B3655709
theorem B1626131 : Blo 1624511 1626131 := bstep (se 1 (by rfl) ⟨1219598, by rfl⟩ : syracuseStep 1626131 = 2439197) B2439197
theorem B45117461 : Blo 1624511 45117461 := bstep (se 6 (by rfl) ⟨1057440, by rfl⟩ : syracuseStep 45117461 = 2114881) B2114881
theorem B1626147 : Blo 1624511 1626147 := bstep (se 1 (by rfl) ⟨1219610, by rfl⟩ : syracuseStep 1626147 = 2439221) B2439221
theorem B2437169 : Blo 1624511 2437169 := bstep (se 2 (by rfl) ⟨913938, by rfl⟩ : syracuseStep 2437169 = 1827877) B1827877
theorem B1626163 : Blo 1624511 1626163 := bstep (se 1 (by rfl) ⟨1219622, by rfl⟩ : syracuseStep 1626163 = 2439245) B2439245
theorem B2437187 : Blo 1624511 2437187 := bstep (se 1 (by rfl) ⟨1827890, by rfl⟩ : syracuseStep 2437187 = 3655781) B3655781
theorem B1626179 : Blo 1624511 1626179 := bstep (se 1 (by rfl) ⟨1219634, by rfl⟩ : syracuseStep 1626179 = 2439269) B2439269
theorem B9261125 : Blo 1624511 9261125 := bstep (se 4 (by rfl) ⟨868230, by rfl⟩ : syracuseStep 9261125 = 1736461) B1736461
theorem B1626195 : Blo 1624511 1626195 := bstep (se 1 (by rfl) ⟨1219646, by rfl⟩ : syracuseStep 1626195 = 2439293) B2439293
theorem B2437217 : Blo 1624511 2437217 := bstep (se 2 (by rfl) ⟨913956, by rfl⟩ : syracuseStep 2437217 = 1827913) B1827913
theorem B1626211 : Blo 1624511 1626211 := bstep (se 1 (by rfl) ⟨1219658, by rfl⟩ : syracuseStep 1626211 = 2439317) B2439317
theorem B2437235 : Blo 1624511 2437235 := bstep (se 1 (by rfl) ⟨1827926, by rfl⟩ : syracuseStep 2437235 = 3655853) B3655853
theorem B1626227 : Blo 1624511 1626227 := bstep (se 1 (by rfl) ⟨1219670, by rfl⟩ : syracuseStep 1626227 = 2439341) B2439341
theorem B1626243 : Blo 1624511 1626243 := bstep (se 1 (by rfl) ⟨1219682, by rfl⟩ : syracuseStep 1626243 = 2439365) B2439365
theorem B2437265 : Blo 1624511 2437265 := bstep (se 2 (by rfl) ⟨913974, by rfl⟩ : syracuseStep 2437265 = 1827949) B1827949
theorem B1626259 : Blo 1624511 1626259 := bstep (se 1 (by rfl) ⟨1219694, by rfl⟩ : syracuseStep 1626259 = 2439389) B2439389
theorem B2437283 : Blo 1624511 2437283 := bstep (se 1 (by rfl) ⟨1827962, by rfl⟩ : syracuseStep 2437283 = 3655925) B3655925
theorem B1626275 : Blo 1624511 1626275 := bstep (se 1 (by rfl) ⟨1219706, by rfl⟩ : syracuseStep 1626275 = 2439413) B2439413
theorem B3657905 : Blo 1624511 3657905 := bstep (se 2 (by rfl) ⟨1371714, by rfl⟩ : syracuseStep 3657905 = 2743429) B2743429
theorem B1626291 : Blo 1624511 1626291 := bstep (se 1 (by rfl) ⟨1219718, by rfl⟩ : syracuseStep 1626291 = 2439437) B2439437
theorem B2437313 : Blo 1624511 2437313 := bstep (se 2 (by rfl) ⟨913992, by rfl⟩ : syracuseStep 2437313 = 1827985) B1827985
theorem B2314433 : Blo 1624511 2314433 := bstep (se 2 (by rfl) ⟨867912, by rfl⟩ : syracuseStep 2314433 = 1735825) B1735825
theorem B3657923 : Blo 1624511 3657923 := bstep (se 1 (by rfl) ⟨2743442, by rfl⟩ : syracuseStep 3657923 = 5486885) B5486885
theorem B1626307 : Blo 1624511 1626307 := bstep (se 1 (by rfl) ⟨1219730, by rfl⟩ : syracuseStep 1626307 = 2439461) B2439461
theorem B9253061 : Blo 1624511 9253061 := bstep (se 4 (by rfl) ⟨867474, by rfl⟩ : syracuseStep 9253061 = 1734949) B1734949
theorem B2437331 : Blo 1624511 2437331 := bstep (se 1 (by rfl) ⟨1827998, by rfl⟩ : syracuseStep 2437331 = 3655997) B3655997
theorem B1626323 : Blo 1624511 1626323 := bstep (se 1 (by rfl) ⟨1219742, by rfl⟩ : syracuseStep 1626323 = 2439485) B2439485
theorem B1626339 : Blo 1624511 1626339 := bstep (se 1 (by rfl) ⟨1219754, by rfl⟩ : syracuseStep 1626339 = 2439509) B2439509
theorem B2437361 : Blo 1624511 2437361 := bstep (se 2 (by rfl) ⟨914010, by rfl⟩ : syracuseStep 2437361 = 1828021) B1828021
theorem B2928881 : Blo 1624511 2928881 := bstep (se 2 (by rfl) ⟨1098330, by rfl⟩ : syracuseStep 2928881 = 2196661) B2196661
theorem B1626355 : Blo 1624511 1626355 := bstep (se 1 (by rfl) ⟨1219766, by rfl⟩ : syracuseStep 1626355 = 2439533) B2439533
theorem B2437379 : Blo 1624511 2437379 := bstep (se 1 (by rfl) ⟨1828034, by rfl⟩ : syracuseStep 2437379 = 3656069) B3656069
theorem B1626371 : Blo 1624511 1626371 := bstep (se 1 (by rfl) ⟨1219778, by rfl⟩ : syracuseStep 1626371 = 2439557) B2439557
theorem B17150221 : Blo 1624511 17150221 := bstep (se 3 (by rfl) ⟨3215666, by rfl⟩ : syracuseStep 17150221 = 6431333) B6431333
theorem B3903761 : Blo 1624511 3903761 := bstep (se 2 (by rfl) ⟨1463910, by rfl⟩ : syracuseStep 3903761 = 2927821) B2927821
theorem B1626387 : Blo 1624511 1626387 := bstep (se 1 (by rfl) ⟨1219790, by rfl⟩ : syracuseStep 1626387 = 2439581) B2439581
theorem B2437409 : Blo 1624511 2437409 := bstep (se 2 (by rfl) ⟨914028, by rfl⟩ : syracuseStep 2437409 = 1828057) B1828057
theorem B1626403 : Blo 1624511 1626403 := bstep (se 1 (by rfl) ⟨1219802, by rfl⟩ : syracuseStep 1626403 = 2439605) B2439605
theorem B2437427 : Blo 1624511 2437427 := bstep (se 1 (by rfl) ⟨1828070, by rfl⟩ : syracuseStep 2437427 = 3656141) B3656141
theorem B1626419 : Blo 1624511 1626419 := bstep (se 1 (by rfl) ⟨1219814, by rfl⟩ : syracuseStep 1626419 = 2439629) B2439629
theorem B1626435 : Blo 1624511 1626435 := bstep (se 1 (by rfl) ⟨1219826, by rfl⟩ : syracuseStep 1626435 = 2439653) B2439653
theorem B2437457 : Blo 1624511 2437457 := bstep (se 2 (by rfl) ⟨914046, by rfl⟩ : syracuseStep 2437457 = 1828093) B1828093
theorem B1626451 : Blo 1624511 1626451 := bstep (se 1 (by rfl) ⟨1219838, by rfl⟩ : syracuseStep 1626451 = 2439677) B2439677
theorem B2437475 : Blo 1624511 2437475 := bstep (se 1 (by rfl) ⟨1828106, by rfl⟩ : syracuseStep 2437475 = 3656213) B3656213
theorem B1626467 : Blo 1624511 1626467 := bstep (se 1 (by rfl) ⟨1219850, by rfl⟩ : syracuseStep 1626467 = 2439701) B2439701
theorem B1626483 : Blo 1624511 1626483 := bstep (se 1 (by rfl) ⟨1219862, by rfl⟩ : syracuseStep 1626483 = 2439725) B2439725
theorem B2437505 : Blo 1624511 2437505 := bstep (se 2 (by rfl) ⟨914064, by rfl⟩ : syracuseStep 2437505 = 1828129) B1828129
theorem B1626499 : Blo 1624511 1626499 := bstep (se 1 (by rfl) ⟨1219874, by rfl⟩ : syracuseStep 1626499 = 2439749) B2439749
theorem B5484941 : Blo 1624511 5484941 := bstep (se 3 (by rfl) ⟨1028426, by rfl⟩ : syracuseStep 5484941 = 2056853) B2056853
theorem B2437523 : Blo 1624511 2437523 := bstep (se 1 (by rfl) ⟨1828142, by rfl⟩ : syracuseStep 2437523 = 3656285) B3656285
theorem B2437553 : Blo 1624511 2437553 := bstep (se 2 (by rfl) ⟨914082, by rfl⟩ : syracuseStep 2437553 = 1828165) B1828165
theorem B2437571 : Blo 1624511 2437571 := bstep (se 1 (by rfl) ⟨1828178, by rfl⟩ : syracuseStep 2437571 = 3656357) B3656357
theorem B5484995 : Blo 1624511 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B3658193 : Blo 1624511 3658193 := bstep (se 2 (by rfl) ⟨1371822, by rfl⟩ : syracuseStep 3658193 = 2743645) B2743645
theorem B2437601 : Blo 1624511 2437601 := bstep (se 2 (by rfl) ⟨914100, by rfl⟩ : syracuseStep 2437601 = 1828201) B1828201
theorem B3658211 : Blo 1624511 3658211 := bstep (se 1 (by rfl) ⟨2743658, by rfl⟩ : syracuseStep 3658211 = 5487317) B5487317
theorem B5206513 : Blo 1624511 5206513 := bstep (se 2 (by rfl) ⟨1952442, by rfl⟩ : syracuseStep 5206513 = 3904885) B3904885
theorem B4116977 : Blo 1624511 4116977 := bstep (se 2 (by rfl) ⟨1543866, by rfl⟩ : syracuseStep 4116977 = 3087733) B3087733
theorem B1978867 : Blo 1624511 1978867 := bstep (se 1 (by rfl) ⟨1484150, by rfl⟩ : syracuseStep 1978867 = 2968301) B2968301
theorem B2437619 : Blo 1624511 2437619 := bstep (se 1 (by rfl) ⟨1828214, by rfl⟩ : syracuseStep 2437619 = 3656429) B3656429
theorem B4944397 : Blo 1624511 4944397 := bstep (se 3 (by rfl) ⟨927074, by rfl⟩ : syracuseStep 4944397 = 1854149) B1854149
theorem B11301389 : Blo 1624511 11301389 := bstep (se 3 (by rfl) ⟨2119010, by rfl⟩ : syracuseStep 11301389 = 4238021) B4238021
theorem B3084817 : Blo 1624511 3084817 := bstep (se 2 (by rfl) ⟨1156806, by rfl⟩ : syracuseStep 3084817 = 2313613) B2313613
theorem B2437649 : Blo 1624511 2437649 := bstep (se 2 (by rfl) ⟨914118, by rfl⟩ : syracuseStep 2437649 = 1828237) B1828237
theorem B2437667 : Blo 1624511 2437667 := bstep (se 1 (by rfl) ⟨1828250, by rfl⟩ : syracuseStep 2437667 = 3656501) B3656501
theorem B4117027 : Blo 1624511 4117027 := bstep (se 1 (by rfl) ⟨3087770, by rfl⟩ : syracuseStep 4117027 = 6175541) B6175541
theorem B3469873 : Blo 1624511 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B2437697 : Blo 1624511 2437697 := bstep (se 2 (by rfl) ⟨914136, by rfl⟩ : syracuseStep 2437697 = 1828273) B1828273
theorem B13185605 : Blo 1624511 13185605 := bstep (se 4 (by rfl) ⟨1236150, by rfl⟩ : syracuseStep 13185605 = 2472301) B2472301
theorem B2437715 : Blo 1624511 2437715 := bstep (se 1 (by rfl) ⟨1828286, by rfl⟩ : syracuseStep 2437715 = 3656573) B3656573
theorem B2437745 : Blo 1624511 2437745 := bstep (se 2 (by rfl) ⟨914154, by rfl⟩ : syracuseStep 2437745 = 1828309) B1828309
theorem B7918193 : Blo 1624511 7918193 := bstep (se 2 (by rfl) ⟨2969322, by rfl⟩ : syracuseStep 7918193 = 5938645) B5938645
theorem B2437763 : Blo 1624511 2437763 := bstep (se 1 (by rfl) ⟨1828322, by rfl⟩ : syracuseStep 2437763 = 3656645) B3656645
theorem B2437793 : Blo 1624511 2437793 := bstep (se 2 (by rfl) ⟨914172, by rfl⟩ : syracuseStep 2437793 = 1828345) B1828345
theorem B2437811 : Blo 1624511 2437811 := bstep (se 1 (by rfl) ⟨1828358, by rfl⟩ : syracuseStep 2437811 = 3656717) B3656717
theorem B2437841 : Blo 1624511 2437841 := bstep (se 2 (by rfl) ⟨914190, by rfl⟩ : syracuseStep 2437841 = 1828381) B1828381
theorem B5485265 : Blo 1624511 5485265 := bstep (se 2 (by rfl) ⟨2056974, by rfl⟩ : syracuseStep 5485265 = 4113949) B4113949
theorem B2437859 : Blo 1624511 2437859 := bstep (se 1 (by rfl) ⟨1828394, by rfl⟩ : syracuseStep 2437859 = 3656789) B3656789
theorem B5206769 : Blo 1624511 5206769 := bstep (se 2 (by rfl) ⟨1952538, by rfl⟩ : syracuseStep 5206769 = 3905077) B3905077
theorem B3658481 : Blo 1624511 3658481 := bstep (se 2 (by rfl) ⟨1371930, by rfl⟩ : syracuseStep 3658481 = 2743861) B2743861
theorem B9261809 : Blo 1624511 9261809 := bstep (se 2 (by rfl) ⟨3473178, by rfl⟩ : syracuseStep 9261809 = 6946357) B6946357
theorem B2437889 : Blo 1624511 2437889 := bstep (se 2 (by rfl) ⟨914208, by rfl⟩ : syracuseStep 2437889 = 1828417) B1828417
theorem B3658499 : Blo 1624511 3658499 := bstep (se 1 (by rfl) ⟨2743874, by rfl⟩ : syracuseStep 3658499 = 5487749) B5487749
theorem B2437907 : Blo 1624511 2437907 := bstep (se 1 (by rfl) ⟨1828430, by rfl⟩ : syracuseStep 2437907 = 3656861) B3656861
theorem B5075747 : Blo 1624511 5075747 := bstep (se 1 (by rfl) ⟨3806810, by rfl⟩ : syracuseStep 5075747 = 7613621) B7613621
theorem B2437937 : Blo 1624511 2437937 := bstep (se 2 (by rfl) ⟨914226, by rfl⟩ : syracuseStep 2437937 = 1828453) B1828453
theorem B2437955 : Blo 1624511 2437955 := bstep (se 1 (by rfl) ⟨1828466, by rfl⟩ : syracuseStep 2437955 = 3656933) B3656933
theorem B2437985 : Blo 1624511 2437985 := bstep (se 2 (by rfl) ⟨914244, by rfl⟩ : syracuseStep 2437985 = 1828489) B1828489
theorem B2438003 : Blo 1624511 2438003 := bstep (se 1 (by rfl) ⟨1828502, by rfl⟩ : syracuseStep 2438003 = 3657005) B3657005
theorem B2438033 : Blo 1624511 2438033 := bstep (se 2 (by rfl) ⟨914262, by rfl⟩ : syracuseStep 2438033 = 1828525) B1828525
theorem B3085219 : Blo 1624511 3085219 := bstep (se 1 (by rfl) ⟨2313914, by rfl⟩ : syracuseStep 3085219 = 4627829) B4627829
theorem B2438051 : Blo 1624511 2438051 := bstep (se 1 (by rfl) ⟨1828538, by rfl⟩ : syracuseStep 2438051 = 3657077) B3657077
theorem B2438081 : Blo 1624511 2438081 := bstep (se 2 (by rfl) ⟨914280, by rfl⟩ : syracuseStep 2438081 = 1828561) B1828561
theorem B3085265 : Blo 1624511 3085265 := bstep (se 2 (by rfl) ⟨1156974, by rfl⟩ : syracuseStep 3085265 = 2313949) B2313949
theorem B2438099 : Blo 1624511 2438099 := bstep (se 1 (by rfl) ⟨1828574, by rfl⟩ : syracuseStep 2438099 = 3657149) B3657149
theorem B2438129 : Blo 1624511 2438129 := bstep (se 2 (by rfl) ⟨914298, by rfl⟩ : syracuseStep 2438129 = 1828597) B1828597
theorem B2438147 : Blo 1624511 2438147 := bstep (se 1 (by rfl) ⟨1828610, by rfl⟩ : syracuseStep 2438147 = 3657221) B3657221
theorem B3658769 : Blo 1624511 3658769 := bstep (se 2 (by rfl) ⟨1372038, by rfl⟩ : syracuseStep 3658769 = 2744077) B2744077
theorem B2438177 : Blo 1624511 2438177 := bstep (se 2 (by rfl) ⟨914316, by rfl⟩ : syracuseStep 2438177 = 1828633) B1828633
theorem B8229923 : Blo 1624511 8229923 := bstep (se 1 (by rfl) ⟨6172442, by rfl⟩ : syracuseStep 8229923 = 12344885) B12344885
theorem B2315299 : Blo 1624511 2315299 := bstep (se 1 (by rfl) ⟨1736474, by rfl⟩ : syracuseStep 2315299 = 3472949) B3472949
theorem B3658787 : Blo 1624511 3658787 := bstep (se 1 (by rfl) ⟨2744090, by rfl⟩ : syracuseStep 3658787 = 5488181) B5488181
theorem B2438195 : Blo 1624511 2438195 := bstep (se 1 (by rfl) ⟨1828646, by rfl⟩ : syracuseStep 2438195 = 3657293) B3657293
theorem B2438225 : Blo 1624511 2438225 := bstep (se 2 (by rfl) ⟨914334, by rfl⟩ : syracuseStep 2438225 = 1828669) B1828669
theorem B2438243 : Blo 1624511 2438243 := bstep (se 1 (by rfl) ⟨1828682, by rfl⟩ : syracuseStep 2438243 = 3657365) B3657365
theorem B2741377 : Blo 1624511 2741377 := bstep (se 2 (by rfl) ⟨1028016, by rfl⟩ : syracuseStep 2741377 = 2056033) B2056033
theorem B2438273 : Blo 1624511 2438273 := bstep (se 2 (by rfl) ⟨914352, by rfl⟩ : syracuseStep 2438273 = 1828705) B1828705
theorem B2315395 : Blo 1624511 2315395 := bstep (se 1 (by rfl) ⟨1736546, by rfl⟩ : syracuseStep 2315395 = 3473093) B3473093
theorem B2438291 : Blo 1624511 2438291 := bstep (se 1 (by rfl) ⟨1828718, by rfl⟩ : syracuseStep 2438291 = 3657437) B3657437
theorem B2741411 : Blo 1624511 2741411 := bstep (se 1 (by rfl) ⟨2056058, by rfl⟩ : syracuseStep 2741411 = 4112117) B4112117
theorem B2438321 : Blo 1624511 2438321 := bstep (se 2 (by rfl) ⟨914370, by rfl⟩ : syracuseStep 2438321 = 1828741) B1828741
theorem B2438339 : Blo 1624511 2438339 := bstep (se 1 (by rfl) ⟨1828754, by rfl⟩ : syracuseStep 2438339 = 3657509) B3657509
theorem B2438369 : Blo 1624511 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B160281827 : Blo 1624511 160281827 := bstep (se 1 (by rfl) ⟨120211370, by rfl⟩ : syracuseStep 160281827 = 240422741) B240422741
theorem B5485805 : Blo 1624511 5485805 := bstep (se 3 (by rfl) ⟨1028588, by rfl⟩ : syracuseStep 5485805 = 2057177) B2057177
theorem B3085553 : Blo 1624511 3085553 := bstep (se 2 (by rfl) ⟨1157082, by rfl⟩ : syracuseStep 3085553 = 2314165) B2314165
theorem B2438387 : Blo 1624511 2438387 := bstep (se 1 (by rfl) ⟨1828790, by rfl⟩ : syracuseStep 2438387 = 3657581) B3657581
theorem B2438417 : Blo 1624511 2438417 := bstep (se 2 (by rfl) ⟨914406, by rfl⟩ : syracuseStep 2438417 = 1828813) B1828813
theorem B2741539 : Blo 1624511 2741539 := bstep (se 1 (by rfl) ⟨2056154, by rfl⟩ : syracuseStep 2741539 = 4112309) B4112309
theorem B5485859 : Blo 1624511 5485859 := bstep (se 1 (by rfl) ⟨4114394, by rfl⟩ : syracuseStep 5485859 = 8228789) B8228789
theorem B2438435 : Blo 1624511 2438435 := bstep (se 1 (by rfl) ⟨1828826, by rfl⟩ : syracuseStep 2438435 = 3657653) B3657653
theorem B3659057 : Blo 1624511 3659057 := bstep (se 2 (by rfl) ⟨1372146, by rfl⟩ : syracuseStep 3659057 = 2744293) B2744293
theorem B2438465 : Blo 1624511 2438465 := bstep (se 2 (by rfl) ⟨914424, by rfl⟩ : syracuseStep 2438465 = 1828849) B1828849
theorem B3659075 : Blo 1624511 3659075 := bstep (se 1 (by rfl) ⟨2744306, by rfl⟩ : syracuseStep 3659075 = 5488613) B5488613
theorem B2438483 : Blo 1624511 2438483 := bstep (se 1 (by rfl) ⟨1828862, by rfl⟩ : syracuseStep 2438483 = 3657725) B3657725
theorem B2438513 : Blo 1624511 2438513 := bstep (se 2 (by rfl) ⟨914442, by rfl⟩ : syracuseStep 2438513 = 1828885) B1828885
theorem B2438531 : Blo 1624511 2438531 := bstep (se 1 (by rfl) ⟨1828898, by rfl⟩ : syracuseStep 2438531 = 3657797) B3657797
theorem B2225569 : Blo 1624511 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B2438561 : Blo 1624511 2438561 := bstep (se 2 (by rfl) ⟨914460, by rfl⟩ : syracuseStep 2438561 = 1828921) B1828921
theorem B2741681 : Blo 1624511 2741681 := bstep (se 2 (by rfl) ⟨1028130, by rfl⟩ : syracuseStep 2741681 = 2056261) B2056261
theorem B2438579 : Blo 1624511 2438579 := bstep (se 1 (by rfl) ⟨1828934, by rfl⟩ : syracuseStep 2438579 = 3657869) B3657869
theorem B2471377 : Blo 1624511 2471377 := bstep (se 2 (by rfl) ⟨926766, by rfl⟩ : syracuseStep 2471377 = 1853533) B1853533
theorem B2438609 : Blo 1624511 2438609 := bstep (se 2 (by rfl) ⟨914478, by rfl⟩ : syracuseStep 2438609 = 1828957) B1828957
theorem B13178339 : Blo 1624511 13178339 := bstep (se 1 (by rfl) ⟨9883754, by rfl⟩ : syracuseStep 13178339 = 19767509) B19767509
theorem B2438627 : Blo 1624511 2438627 := bstep (se 1 (by rfl) ⟨1828970, by rfl⟩ : syracuseStep 2438627 = 3657941) B3657941
theorem B2438657 : Blo 1624511 2438657 := bstep (se 2 (by rfl) ⟨914496, by rfl⟩ : syracuseStep 2438657 = 1828993) B1828993
theorem B2602513 : Blo 1624511 2602513 := bstep (se 2 (by rfl) ⟨975942, by rfl⟩ : syracuseStep 2602513 = 1951885) B1951885
theorem B2438675 : Blo 1624511 2438675 := bstep (se 1 (by rfl) ⟨1829006, by rfl⟩ : syracuseStep 2438675 = 3658013) B3658013
theorem B2741809 : Blo 1624511 2741809 := bstep (se 2 (by rfl) ⟨1028178, by rfl⟩ : syracuseStep 2741809 = 2056357) B2056357
theorem B5486129 : Blo 1624511 5486129 := bstep (se 2 (by rfl) ⟨2057298, by rfl⟩ : syracuseStep 5486129 = 4114597) B4114597
theorem B2438705 : Blo 1624511 2438705 := bstep (se 2 (by rfl) ⟨914514, by rfl⟩ : syracuseStep 2438705 = 1829029) B1829029
theorem B2438723 : Blo 1624511 2438723 := bstep (se 1 (by rfl) ⟨1829042, by rfl⟩ : syracuseStep 2438723 = 3658085) B3658085
theorem B3659345 : Blo 1624511 3659345 := bstep (se 2 (by rfl) ⟨1372254, by rfl⟩ : syracuseStep 3659345 = 2744509) B2744509
theorem B2741843 : Blo 1624511 2741843 := bstep (se 1 (by rfl) ⟨2056382, by rfl⟩ : syracuseStep 2741843 = 4112765) B4112765
theorem B2438753 : Blo 1624511 2438753 := bstep (se 2 (by rfl) ⟨914532, by rfl⟩ : syracuseStep 2438753 = 1829065) B1829065
theorem B3659363 : Blo 1624511 3659363 := bstep (se 1 (by rfl) ⟨2744522, by rfl⟩ : syracuseStep 3659363 = 5489045) B5489045
theorem B4691569 : Blo 1624511 4691569 := bstep (se 2 (by rfl) ⟨1759338, by rfl⟩ : syracuseStep 4691569 = 3518677) B3518677
theorem B2438771 : Blo 1624511 2438771 := bstep (se 1 (by rfl) ⟨1829078, by rfl⟩ : syracuseStep 2438771 = 3658157) B3658157
theorem B2438801 : Blo 1624511 2438801 := bstep (se 2 (by rfl) ⟨914550, by rfl⟩ : syracuseStep 2438801 = 1829101) B1829101
theorem B2438819 : Blo 1624511 2438819 := bstep (se 1 (by rfl) ⟨1829114, by rfl⟩ : syracuseStep 2438819 = 3658229) B3658229
theorem B2438849 : Blo 1624511 2438849 := bstep (se 2 (by rfl) ⟨914568, by rfl⟩ : syracuseStep 2438849 = 1829137) B1829137
theorem B2741971 : Blo 1624511 2741971 := bstep (se 1 (by rfl) ⟨2056478, by rfl⟩ : syracuseStep 2741971 = 4112957) B4112957
theorem B2438867 : Blo 1624511 2438867 := bstep (se 1 (by rfl) ⟨1829150, by rfl⟩ : syracuseStep 2438867 = 3658301) B3658301
theorem B12351203 : Blo 1624511 12351203 := bstep (se 1 (by rfl) ⟨9263402, by rfl⟩ : syracuseStep 12351203 = 18526805) B18526805
theorem B2438897 : Blo 1624511 2438897 := bstep (se 2 (by rfl) ⟨914586, by rfl⟩ : syracuseStep 2438897 = 1829173) B1829173
theorem B17823473 : Blo 1624511 17823473 := bstep (se 2 (by rfl) ⟨6683802, by rfl⟩ : syracuseStep 17823473 = 13367605) B13367605
theorem B2438915 : Blo 1624511 2438915 := bstep (se 1 (by rfl) ⟨1829186, by rfl⟩ : syracuseStep 2438915 = 3658373) B3658373
theorem B2438945 : Blo 1624511 2438945 := bstep (se 2 (by rfl) ⟨914604, by rfl⟩ : syracuseStep 2438945 = 1829209) B1829209
theorem B2438963 : Blo 1624511 2438963 := bstep (se 1 (by rfl) ⟨1829222, by rfl⟩ : syracuseStep 2438963 = 3658445) B3658445
theorem B3905347 : Blo 1624511 3905347 := bstep (se 1 (by rfl) ⟨2929010, by rfl⟩ : syracuseStep 3905347 = 5858021) B5858021
theorem B5011267 : Blo 1624511 5011267 := bstep (se 1 (by rfl) ⟨3758450, by rfl⟩ : syracuseStep 5011267 = 7516901) B7516901
theorem B5207885 : Blo 1624511 5207885 := bstep (se 3 (by rfl) ⟨976478, by rfl⟩ : syracuseStep 5207885 = 1952957) B1952957
theorem B8230733 : Blo 1624511 8230733 := bstep (se 3 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 8230733 = 3086525) B3086525
theorem B2438993 : Blo 1624511 2438993 := bstep (se 2 (by rfl) ⟨914622, by rfl⟩ : syracuseStep 2438993 = 1829245) B1829245
theorem B2742113 : Blo 1624511 2742113 := bstep (se 2 (by rfl) ⟨1028292, by rfl⟩ : syracuseStep 2742113 = 2056585) B2056585
theorem B2439011 : Blo 1624511 2439011 := bstep (se 1 (by rfl) ⟨1829258, by rfl⟩ : syracuseStep 2439011 = 3658517) B3658517
theorem B3659633 : Blo 1624511 3659633 := bstep (se 2 (by rfl) ⟨1372362, by rfl⟩ : syracuseStep 3659633 = 2744725) B2744725
theorem B2439041 : Blo 1624511 2439041 := bstep (se 2 (by rfl) ⟨914640, by rfl⟩ : syracuseStep 2439041 = 1829281) B1829281
theorem B3659651 : Blo 1624511 3659651 := bstep (se 1 (by rfl) ⟨2744738, by rfl⟩ : syracuseStep 3659651 = 5489477) B5489477
theorem B41662349 : Blo 1624511 41662349 := bstep (se 3 (by rfl) ⟨7811690, by rfl⟩ : syracuseStep 41662349 = 15623381) B15623381
theorem B2439059 : Blo 1624511 2439059 := bstep (se 1 (by rfl) ⟨1829294, by rfl⟩ : syracuseStep 2439059 = 3658589) B3658589
theorem B2439089 : Blo 1624511 2439089 := bstep (se 2 (by rfl) ⟨914658, by rfl⟩ : syracuseStep 2439089 = 1829317) B1829317
theorem B4626371 : Blo 1624511 4626371 := bstep (se 1 (by rfl) ⟨3469778, by rfl⟩ : syracuseStep 4626371 = 6939557) B6939557
theorem B3086275 : Blo 1624511 3086275 := bstep (se 1 (by rfl) ⟨2314706, by rfl⟩ : syracuseStep 3086275 = 4629413) B4629413
theorem B2439107 : Blo 1624511 2439107 := bstep (se 1 (by rfl) ⟨1829330, by rfl⟩ : syracuseStep 2439107 = 3658661) B3658661
theorem B6944717 : Blo 1624511 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B2742241 : Blo 1624511 2742241 := bstep (se 2 (by rfl) ⟨1028340, by rfl⟩ : syracuseStep 2742241 = 2056681) B2056681
theorem B2439137 : Blo 1624511 2439137 := bstep (se 2 (by rfl) ⟨914676, by rfl⟩ : syracuseStep 2439137 = 1829353) B1829353
theorem B2439155 : Blo 1624511 2439155 := bstep (se 1 (by rfl) ⟨1829366, by rfl⟩ : syracuseStep 2439155 = 3658733) B3658733
theorem B2742275 : Blo 1624511 2742275 := bstep (se 1 (by rfl) ⟨2056706, by rfl⟩ : syracuseStep 2742275 = 4113413) B4113413
theorem B2439185 : Blo 1624511 2439185 := bstep (se 2 (by rfl) ⟨914694, by rfl⟩ : syracuseStep 2439185 = 1829389) B1829389
theorem B2439203 : Blo 1624511 2439203 := bstep (se 1 (by rfl) ⟨1829402, by rfl⟩ : syracuseStep 2439203 = 3658805) B3658805
theorem B2439233 : Blo 1624511 2439233 := bstep (se 2 (by rfl) ⟨914712, by rfl⟩ : syracuseStep 2439233 = 1829425) B1829425
theorem B5486669 : Blo 1624511 5486669 := bstep (se 3 (by rfl) ⟨1028750, by rfl⟩ : syracuseStep 5486669 = 2057501) B2057501
theorem B2439251 : Blo 1624511 2439251 := bstep (se 1 (by rfl) ⟨1829438, by rfl⟩ : syracuseStep 2439251 = 3658877) B3658877
theorem B1980499 : Blo 1624511 1980499 := bstep (se 1 (by rfl) ⟨1485374, by rfl⟩ : syracuseStep 1980499 = 2970749) B2970749
theorem B2439281 : Blo 1624511 2439281 := bstep (se 2 (by rfl) ⟨914730, by rfl⟩ : syracuseStep 2439281 = 1829461) B1829461
theorem B1734787 : Blo 1624511 1734787 := bstep (se 1 (by rfl) ⟨1301090, by rfl⟩ : syracuseStep 1734787 = 2602181) B2602181
theorem B2742403 : Blo 1624511 2742403 := bstep (se 1 (by rfl) ⟨2056802, by rfl⟩ : syracuseStep 2742403 = 4113605) B4113605
theorem B5486723 : Blo 1624511 5486723 := bstep (se 1 (by rfl) ⟨4115042, by rfl⟩ : syracuseStep 5486723 = 8230085) B8230085
theorem B2439299 : Blo 1624511 2439299 := bstep (se 1 (by rfl) ⟨1829474, by rfl⟩ : syracuseStep 2439299 = 3658949) B3658949
theorem B2439329 : Blo 1624511 2439329 := bstep (se 2 (by rfl) ⟨914748, by rfl⟩ : syracuseStep 2439329 = 1829497) B1829497
theorem B9263267 : Blo 1624511 9263267 := bstep (se 1 (by rfl) ⟨6947450, by rfl⟩ : syracuseStep 9263267 = 13894901) B13894901
theorem B2439347 : Blo 1624511 2439347 := bstep (se 1 (by rfl) ⟨1829510, by rfl⟩ : syracuseStep 2439347 = 3659021) B3659021
theorem B2439377 : Blo 1624511 2439377 := bstep (se 2 (by rfl) ⟨914766, by rfl⟩ : syracuseStep 2439377 = 1829533) B1829533
theorem B2439395 : Blo 1624511 2439395 := bstep (se 1 (by rfl) ⟨1829546, by rfl⟩ : syracuseStep 2439395 = 3659093) B3659093
theorem B2439425 : Blo 1624511 2439425 := bstep (se 2 (by rfl) ⟨914784, by rfl⟩ : syracuseStep 2439425 = 1829569) B1829569
theorem B2742545 : Blo 1624511 2742545 := bstep (se 2 (by rfl) ⟨1028454, by rfl⟩ : syracuseStep 2742545 = 2056909) B2056909
theorem B2439443 : Blo 1624511 2439443 := bstep (se 1 (by rfl) ⟨1829582, by rfl⟩ : syracuseStep 2439443 = 3659165) B3659165
theorem B2439473 : Blo 1624511 2439473 := bstep (se 2 (by rfl) ⟨914802, by rfl⟩ : syracuseStep 2439473 = 1829605) B1829605
theorem B6175025 : Blo 1624511 6175025 := bstep (se 2 (by rfl) ⟨2315634, by rfl⟩ : syracuseStep 6175025 = 4631269) B4631269
theorem B2439491 : Blo 1624511 2439491 := bstep (se 1 (by rfl) ⟨1829618, by rfl⟩ : syracuseStep 2439491 = 3659237) B3659237
theorem B2439521 : Blo 1624511 2439521 := bstep (se 2 (by rfl) ⟨914820, by rfl⟩ : syracuseStep 2439521 = 1829641) B1829641
theorem B8345969 : Blo 1624511 8345969 := bstep (se 2 (by rfl) ⟨3129738, by rfl⟩ : syracuseStep 8345969 = 6259477) B6259477
theorem B2439539 : Blo 1624511 2439539 := bstep (se 1 (by rfl) ⟨1829654, by rfl⟩ : syracuseStep 2439539 = 3659309) B3659309
theorem B3905923 : Blo 1624511 3905923 := bstep (se 1 (by rfl) ⟨2929442, by rfl⟩ : syracuseStep 3905923 = 5858885) B5858885
theorem B3086723 : Blo 1624511 3086723 := bstep (se 1 (by rfl) ⟨2315042, by rfl⟩ : syracuseStep 3086723 = 4630085) B4630085
theorem B2742673 : Blo 1624511 2742673 := bstep (se 2 (by rfl) ⟨1028502, by rfl⟩ : syracuseStep 2742673 = 2057005) B2057005
theorem B3471761 : Blo 1624511 3471761 := bstep (se 2 (by rfl) ⟨1301910, by rfl⟩ : syracuseStep 3471761 = 2603821) B2603821
theorem B2603411 : Blo 1624511 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B5486993 : Blo 1624511 5486993 := bstep (se 2 (by rfl) ⟨2057622, by rfl⟩ : syracuseStep 5486993 = 4115245) B4115245
theorem B2439569 : Blo 1624511 2439569 := bstep (se 2 (by rfl) ⟨914838, by rfl⟩ : syracuseStep 2439569 = 1829677) B1829677
theorem B2439587 : Blo 1624511 2439587 := bstep (se 1 (by rfl) ⟨1829690, by rfl⟩ : syracuseStep 2439587 = 3659381) B3659381
theorem B2742707 : Blo 1624511 2742707 := bstep (se 1 (by rfl) ⟨2057030, by rfl⟩ : syracuseStep 2742707 = 4114061) B4114061
theorem B2439617 : Blo 1624511 2439617 := bstep (se 2 (by rfl) ⟨914856, by rfl⟩ : syracuseStep 2439617 = 1829713) B1829713
theorem B2439635 : Blo 1624511 2439635 := bstep (se 1 (by rfl) ⟨1829726, by rfl⟩ : syracuseStep 2439635 = 3659453) B3659453
theorem B2439665 : Blo 1624511 2439665 := bstep (se 2 (by rfl) ⟨914874, by rfl⟩ : syracuseStep 2439665 = 1829749) B1829749
theorem B2439683 : Blo 1624511 2439683 := bstep (se 1 (by rfl) ⟨1829762, by rfl⟩ : syracuseStep 2439683 = 3659525) B3659525
theorem B2439713 : Blo 1624511 2439713 := bstep (se 2 (by rfl) ⟨914892, by rfl⟩ : syracuseStep 2439713 = 1829785) B1829785
theorem B2742835 : Blo 1624511 2742835 := bstep (se 1 (by rfl) ⟨2057126, by rfl⟩ : syracuseStep 2742835 = 4114253) B4114253
theorem B2439731 : Blo 1624511 2439731 := bstep (se 1 (by rfl) ⟨1829798, by rfl⟩ : syracuseStep 2439731 = 3659597) B3659597
theorem B10410565 : Blo 1624511 10410565 := bstep (se 4 (by rfl) ⟨975990, by rfl⟩ : syracuseStep 10410565 = 1951981) B1951981
theorem B2439761 : Blo 1624511 2439761 := bstep (se 2 (by rfl) ⟨914910, by rfl⟩ : syracuseStep 2439761 = 1829821) B1829821
theorem B2603603 : Blo 1624511 2603603 := bstep (se 1 (by rfl) ⟨1952702, by rfl⟩ : syracuseStep 2603603 = 3905405) B3905405
theorem B20822669 : Blo 1624511 20822669 := bstep (se 3 (by rfl) ⟨3904250, by rfl⟩ : syracuseStep 20822669 = 7808501) B7808501
theorem B3087011 : Blo 1624511 3087011 := bstep (se 1 (by rfl) ⟨2315258, by rfl⟩ : syracuseStep 3087011 = 4630517) B4630517
theorem B2742977 : Blo 1624511 2742977 := bstep (se 2 (by rfl) ⟨1028616, by rfl⟩ : syracuseStep 2742977 = 2057233) B2057233
theorem B3906307 : Blo 1624511 3906307 := bstep (se 1 (by rfl) ⟨2929730, by rfl⟩ : syracuseStep 3906307 = 5859461) B5859461
theorem B2743105 : Blo 1624511 2743105 := bstep (se 2 (by rfl) ⟨1028664, by rfl⟩ : syracuseStep 2743105 = 2057329) B2057329
theorem B2743139 : Blo 1624511 2743139 := bstep (se 1 (by rfl) ⟨2057354, by rfl⟩ : syracuseStep 2743139 = 4114709) B4114709
theorem B18520973 : Blo 1624511 18520973 := bstep (se 3 (by rfl) ⟨3472682, by rfl⟩ : syracuseStep 18520973 = 6945365) B6945365
theorem B5487533 : Blo 1624511 5487533 := bstep (se 3 (by rfl) ⟨1028912, by rfl⟩ : syracuseStep 5487533 = 2057825) B2057825
theorem B2743267 : Blo 1624511 2743267 := bstep (se 1 (by rfl) ⟨2057450, by rfl⟩ : syracuseStep 2743267 = 4114901) B4114901
theorem B5487587 : Blo 1624511 5487587 := bstep (se 1 (by rfl) ⟨4115690, by rfl⟩ : syracuseStep 5487587 = 8231381) B8231381
theorem B2472947 : Blo 1624511 2472947 := bstep (se 1 (by rfl) ⟨1854710, by rfl⟩ : syracuseStep 2472947 = 3709421) B3709421
theorem B15629381 : Blo 1624511 15629381 := bstep (se 4 (by rfl) ⟨1465254, by rfl⟩ : syracuseStep 15629381 = 2930509) B2930509
theorem B27761777 : Blo 1624511 27761777 := bstep (se 2 (by rfl) ⟨10410666, by rfl⟩ : syracuseStep 27761777 = 20821333) B20821333
theorem B2743409 : Blo 1624511 2743409 := bstep (se 2 (by rfl) ⟨1028778, by rfl⟩ : syracuseStep 2743409 = 2057557) B2057557
theorem B5209229 : Blo 1624511 5209229 := bstep (se 3 (by rfl) ⟨976730, by rfl⟩ : syracuseStep 5209229 = 1953461) B1953461
theorem B4627601 : Blo 1624511 4627601 := bstep (se 2 (by rfl) ⟨1735350, by rfl⟩ : syracuseStep 4627601 = 3470701) B3470701
theorem B11713733 : Blo 1624511 11713733 := bstep (se 4 (by rfl) ⟨1098162, by rfl⟩ : syracuseStep 11713733 = 2196325) B2196325
theorem B21101795 : Blo 1624511 21101795 := bstep (se 1 (by rfl) ⟨15826346, by rfl⟩ : syracuseStep 21101795 = 31652693) B31652693
theorem B31251683 : Blo 1624511 31251683 := bstep (se 1 (by rfl) ⟨23438762, by rfl⟩ : syracuseStep 31251683 = 46877525) B46877525
theorem B2743537 : Blo 1624511 2743537 := bstep (se 2 (by rfl) ⟨1028826, by rfl⟩ : syracuseStep 2743537 = 2057653) B2057653
theorem B5487857 : Blo 1624511 5487857 := bstep (se 2 (by rfl) ⟨2057946, by rfl⟩ : syracuseStep 5487857 = 4115893) B4115893
theorem B6946033 : Blo 1624511 6946033 := bstep (se 2 (by rfl) ⟨2604762, by rfl⟩ : syracuseStep 6946033 = 5209525) B5209525
theorem B10419461 : Blo 1624511 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B2743571 : Blo 1624511 2743571 := bstep (se 1 (by rfl) ⟨2057678, by rfl⟩ : syracuseStep 2743571 = 4115357) B4115357
theorem B8912177 : Blo 1624511 8912177 := bstep (se 2 (by rfl) ⟨3342066, by rfl⟩ : syracuseStep 8912177 = 6684133) B6684133
theorem B1736051 : Blo 1624511 1736051 := bstep (se 1 (by rfl) ⟨1302038, by rfl⟩ : syracuseStep 1736051 = 2604077) B2604077
theorem B2743699 : Blo 1624511 2743699 := bstep (se 1 (by rfl) ⟨2057774, by rfl⟩ : syracuseStep 2743699 = 4115549) B4115549
theorem B2743841 : Blo 1624511 2743841 := bstep (se 2 (by rfl) ⟨1028940, by rfl⟩ : syracuseStep 2743841 = 2057881) B2057881
theorem B2604577 : Blo 1624511 2604577 := bstep (se 2 (by rfl) ⟨976716, by rfl⟩ : syracuseStep 2604577 = 1953433) B1953433
theorem B5209667 : Blo 1624511 5209667 := bstep (se 1 (by rfl) ⟨3907250, by rfl⟩ : syracuseStep 5209667 = 7814501) B7814501
theorem B3907153 : Blo 1624511 3907153 := bstep (se 2 (by rfl) ⟨1465182, by rfl⟩ : syracuseStep 3907153 = 2930365) B2930365
theorem B2743969 : Blo 1624511 2743969 := bstep (se 2 (by rfl) ⟨1028988, by rfl⟩ : syracuseStep 2743969 = 2057977) B2057977
theorem B3473059 : Blo 1624511 3473059 := bstep (se 1 (by rfl) ⟨2604794, by rfl⟩ : syracuseStep 3473059 = 5209589) B5209589
theorem B2744003 : Blo 1624511 2744003 := bstep (se 1 (by rfl) ⟨2058002, by rfl⟩ : syracuseStep 2744003 = 4116005) B4116005
theorem B11124485 : Blo 1624511 11124485 := bstep (se 4 (by rfl) ⟨1042920, by rfl⟩ : syracuseStep 11124485 = 2085841) B2085841
theorem B5488397 : Blo 1624511 5488397 := bstep (se 3 (by rfl) ⟨1029074, by rfl⟩ : syracuseStep 5488397 = 2058149) B2058149
theorem B2744131 : Blo 1624511 2744131 := bstep (se 1 (by rfl) ⟨2058098, by rfl⟩ : syracuseStep 2744131 = 4116197) B4116197
theorem B5488451 : Blo 1624511 5488451 := bstep (se 1 (by rfl) ⟨4116338, by rfl⟩ : syracuseStep 5488451 = 8232677) B8232677
theorem B6168419 : Blo 1624511 6168419 := bstep (se 1 (by rfl) ⟨4626314, by rfl⟩ : syracuseStep 6168419 = 9252629) B9252629
theorem B6168433 : Blo 1624511 6168433 := bstep (se 2 (by rfl) ⟨2313162, by rfl⟩ : syracuseStep 6168433 = 4626325) B4626325
theorem B13188977 : Blo 1624511 13188977 := bstep (se 2 (by rfl) ⟨4945866, by rfl⟩ : syracuseStep 13188977 = 9891733) B9891733
theorem B2056099 : Blo 1624511 2056099 := bstep (se 1 (by rfl) ⟨1542074, by rfl⟩ : syracuseStep 2056099 = 3084149) B3084149
theorem B2744273 : Blo 1624511 2744273 := bstep (se 2 (by rfl) ⟨1029102, by rfl⟩ : syracuseStep 2744273 = 2058205) B2058205
theorem B2605025 : Blo 1624511 2605025 := bstep (se 2 (by rfl) ⟨976884, by rfl⟩ : syracuseStep 2605025 = 1953769) B1953769
theorem B8224739 : Blo 1624511 8224739 := bstep (se 1 (by rfl) ⟨6168554, by rfl⟩ : syracuseStep 8224739 = 12337109) B12337109
theorem B13885505 : Blo 1624511 13885505 := bstep (se 2 (by rfl) ⟨5207064, by rfl⟩ : syracuseStep 13885505 = 10414129) B10414129
theorem B23429195 : Blo 1624511 23429195 := bstep (se 1 (by rfl) ⟨17571896, by rfl⟩ : syracuseStep 23429195 = 35143793) B35143793
theorem B6168707 : Blo 1624511 6168707 := bstep (se 1 (by rfl) ⟨4626530, by rfl⟩ : syracuseStep 6168707 = 9253061) B9253061
theorem B2744651 : Blo 1624511 2744651 := bstep (se 1 (by rfl) ⟨2058488, by rfl⟩ : syracuseStep 2744651 = 4116977) B4116977
theorem B8790403 : Blo 1624511 8790403 := bstep (se 1 (by rfl) ⟨6592802, by rfl⟩ : syracuseStep 8790403 = 13185605) B13185605
theorem B5489099 : Blo 1624511 5489099 := bstep (se 1 (by rfl) ⟨4116824, by rfl⟩ : syracuseStep 5489099 = 8233649) B8233649
theorem B3383831 : Blo 1624511 3383831 := bstep (se 1 (by rfl) ⟨2537873, by rfl⟩ : syracuseStep 3383831 = 5075747) B5075747
theorem B2056843 : Blo 1624511 2056843 := bstep (se 1 (by rfl) ⟨1542632, by rfl⟩ : syracuseStep 2056843 = 3085265) B3085265
theorem B2638489 : Blo 1624511 2638489 := bstep (se 2 (by rfl) ⟨989433, by rfl⟩ : syracuseStep 2638489 = 1978867) B1978867
theorem B4113089 : Blo 1624511 4113089 := bstep (se 2 (by rfl) ⟨1542408, by rfl⟩ : syracuseStep 4113089 = 3084817) B3084817
theorem B5489369 : Blo 1624511 5489369 := bstep (se 2 (by rfl) ⟨2058513, by rfl⟩ : syracuseStep 5489369 = 4117027) B4117027
theorem B14082821 : Blo 1624511 14082821 := bstep (se 4 (by rfl) ⟨1320264, by rfl⟩ : syracuseStep 14082821 = 2640529) B2640529
theorem B1827607 : Blo 1624511 1827607 := bstep (se 1 (by rfl) ⟨1370705, by rfl⟩ : syracuseStep 1827607 = 2741411) B2741411
theorem B3294067 : Blo 1624511 3294067 := bstep (se 1 (by rfl) ⟨2470550, by rfl⟩ : syracuseStep 3294067 = 4941101) B4941101
theorem B7914419 : Blo 1624511 7914419 := bstep (se 1 (by rfl) ⟨5935814, by rfl⟩ : syracuseStep 7914419 = 11871629) B11871629
theorem B4391873 : Blo 1624511 4391873 := bstep (se 2 (by rfl) ⟨1646952, by rfl⟩ : syracuseStep 4391873 = 3293905) B3293905
theorem B1827787 : Blo 1624511 1827787 := bstep (se 1 (by rfl) ⟨1370840, by rfl⟩ : syracuseStep 1827787 = 2741681) B2741681
theorem B4629469 : Blo 1624511 4629469 := bstep (se 3 (by rfl) ⟨868025, by rfl⟩ : syracuseStep 4629469 = 1736051) B1736051
theorem B1827895 : Blo 1624511 1827895 := bstep (se 1 (by rfl) ⟨1370921, by rfl⟩ : syracuseStep 1827895 = 2741843) B2741843
theorem B41649227 : Blo 1624511 41649227 := bstep (se 1 (by rfl) ⟨31236920, by rfl⟩ : syracuseStep 41649227 = 62473841) B62473841
theorem B59327639 : Blo 1624511 59327639 := bstep (se 1 (by rfl) ⟨44495729, by rfl⟩ : syracuseStep 59327639 = 88991459) B88991459
theorem B8234135 : Blo 1624511 8234135 := bstep (se 1 (by rfl) ⟨6175601, by rfl⟩ : syracuseStep 8234135 = 12351203) B12351203
theorem B15033521 : Blo 1624511 15033521 := bstep (se 2 (by rfl) ⟨5637570, by rfl⟩ : syracuseStep 15033521 = 11275141) B11275141
theorem B4113625 : Blo 1624511 4113625 := bstep (se 2 (by rfl) ⟨1542609, by rfl⟩ : syracuseStep 4113625 = 3085219) B3085219
theorem B1828075 : Blo 1624511 1828075 := bstep (se 1 (by rfl) ⟨1371056, by rfl⟩ : syracuseStep 1828075 = 2742113) B2742113
theorem B4629811 : Blo 1624511 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B1828183 : Blo 1624511 1828183 := bstep (se 1 (by rfl) ⟨1371137, by rfl⟩ : syracuseStep 1828183 = 2742275) B2742275
theorem B12346829 : Blo 1624511 12346829 := bstep (se 3 (by rfl) ⟨2315030, by rfl⟩ : syracuseStep 12346829 = 4630061) B4630061
theorem B3655169 : Blo 1624511 3655169 := bstep (se 2 (by rfl) ⟨1370688, by rfl⟩ : syracuseStep 3655169 = 2741377) B2741377
theorem B1828363 : Blo 1624511 1828363 := bstep (se 1 (by rfl) ⟨1371272, by rfl⟩ : syracuseStep 1828363 = 2742545) B2742545
theorem B5563979 : Blo 1624511 5563979 := bstep (se 1 (by rfl) ⟨4172984, by rfl⟩ : syracuseStep 5563979 = 8345969) B8345969
theorem B2057815 : Blo 1624511 2057815 := bstep (se 1 (by rfl) ⟨1543361, by rfl⟩ : syracuseStep 2057815 = 3086723) B3086723
theorem B13354589 : Blo 1624511 13354589 := bstep (se 3 (by rfl) ⟨2503985, by rfl⟩ : syracuseStep 13354589 = 5007971) B5007971
theorem B1828471 : Blo 1624511 1828471 := bstep (se 1 (by rfl) ⟨1371353, by rfl⟩ : syracuseStep 1828471 = 2742707) B2742707
theorem B3655385 : Blo 1624511 3655385 := bstep (se 2 (by rfl) ⟨1370769, by rfl⟩ : syracuseStep 3655385 = 2741539) B2741539
theorem B8226521 : Blo 1624511 8226521 := bstep (se 2 (by rfl) ⟨3084945, by rfl⟩ : syracuseStep 8226521 = 6169891) B6169891
theorem B1828651 : Blo 1624511 1828651 := bstep (se 1 (by rfl) ⟨1371488, by rfl⟩ : syracuseStep 1828651 = 2742977) B2742977
theorem B3655475 : Blo 1624511 3655475 := bstep (se 1 (by rfl) ⟨2741606, by rfl⟩ : syracuseStep 3655475 = 5483213) B5483213
theorem B3655511 : Blo 1624511 3655511 := bstep (se 1 (by rfl) ⟨2741633, by rfl⟩ : syracuseStep 3655511 = 5483267) B5483267
theorem B2967425 : Blo 1624511 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B1828759 : Blo 1624511 1828759 := bstep (se 1 (by rfl) ⟨1371569, by rfl⟩ : syracuseStep 1828759 = 2743139) B2743139
theorem B12347315 : Blo 1624511 12347315 := bstep (se 1 (by rfl) ⟨9260486, by rfl⟩ : syracuseStep 12347315 = 18520973) B18520973
theorem B3295169 : Blo 1624511 3295169 := bstep (se 2 (by rfl) ⟨1235688, by rfl⟩ : syracuseStep 3295169 = 2471377) B2471377
theorem B1648631 : Blo 1624511 1648631 := bstep (se 1 (by rfl) ⟨1236473, by rfl⟩ : syracuseStep 1648631 = 2472947) B2472947
theorem B3655691 : Blo 1624511 3655691 := bstep (se 1 (by rfl) ⟨2741768, by rfl⟩ : syracuseStep 3655691 = 5483537) B5483537
theorem B3655745 : Blo 1624511 3655745 := bstep (se 2 (by rfl) ⟨1370904, by rfl⟩ : syracuseStep 3655745 = 2741809) B2741809
theorem B18507851 : Blo 1624511 18507851 := bstep (se 1 (by rfl) ⟨13880888, by rfl⟩ : syracuseStep 18507851 = 27761777) B27761777
theorem B1828939 : Blo 1624511 1828939 := bstep (se 1 (by rfl) ⟨1371704, by rfl⟩ : syracuseStep 1828939 = 2743409) B2743409
theorem B7809155 : Blo 1624511 7809155 := bstep (se 1 (by rfl) ⟨5856866, by rfl⟩ : syracuseStep 7809155 = 11713733) B11713733
theorem B14067863 : Blo 1624511 14067863 := bstep (se 1 (by rfl) ⟨10550897, by rfl⟩ : syracuseStep 14067863 = 21101795) B21101795
theorem B1951895 : Blo 1624511 1951895 := bstep (se 1 (by rfl) ⟨1463921, by rfl⟩ : syracuseStep 1951895 = 2927843) B2927843
theorem B20834455 : Blo 1624511 20834455 := bstep (se 1 (by rfl) ⟨15625841, by rfl⟩ : syracuseStep 20834455 = 31251683) B31251683
theorem B1829047 : Blo 1624511 1829047 := bstep (se 1 (by rfl) ⟨1371785, by rfl⟩ : syracuseStep 1829047 = 2743571) B2743571
theorem B5941451 : Blo 1624511 5941451 := bstep (se 1 (by rfl) ⟨4456088, by rfl⟩ : syracuseStep 5941451 = 8912177) B8912177
theorem B4630745 : Blo 1624511 4630745 := bstep (se 2 (by rfl) ⟨1736529, by rfl⟩ : syracuseStep 4630745 = 3473059) B3473059
theorem B3655961 : Blo 1624511 3655961 := bstep (se 2 (by rfl) ⟨1370985, by rfl⟩ : syracuseStep 3655961 = 2741971) B2741971
theorem B4114739 : Blo 1624511 4114739 := bstep (se 1 (by rfl) ⟨3086054, by rfl⟩ : syracuseStep 4114739 = 6172109) B6172109
theorem B1829227 : Blo 1624511 1829227 := bstep (se 1 (by rfl) ⟨1371920, by rfl⟩ : syracuseStep 1829227 = 2743841) B2743841
theorem B3656051 : Blo 1624511 3656051 := bstep (se 1 (by rfl) ⟨2742038, by rfl⟩ : syracuseStep 3656051 = 5484077) B5484077
theorem B3656087 : Blo 1624511 3656087 := bstep (se 1 (by rfl) ⟨2742065, by rfl⟩ : syracuseStep 3656087 = 5484131) B5484131
theorem B1624523 : Blo 1624511 1624523 := bstep (se 1 (by rfl) ⟨1218392, by rfl⟩ : syracuseStep 1624523 = 2436785) B2436785
theorem B1952203 : Blo 1624511 1952203 := bstep (se 1 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 1952203 = 2928305) B2928305
theorem B1624535 : Blo 1624511 1624535 := bstep (se 1 (by rfl) ⟨1218401, by rfl⟩ : syracuseStep 1624535 = 2436803) B2436803
theorem B1829335 : Blo 1624511 1829335 := bstep (se 1 (by rfl) ⟨1372001, by rfl⟩ : syracuseStep 1829335 = 2744003) B2744003
theorem B1624555 : Blo 1624511 1624555 := bstep (se 1 (by rfl) ⟨1218416, by rfl⟩ : syracuseStep 1624555 = 2436833) B2436833
theorem B1624567 : Blo 1624511 1624567 := bstep (se 1 (by rfl) ⟨1218425, by rfl⟩ : syracuseStep 1624567 = 2436851) B2436851
theorem B7416323 : Blo 1624511 7416323 := bstep (se 1 (by rfl) ⟨5562242, by rfl⟩ : syracuseStep 7416323 = 11124485) B11124485
theorem B1624587 : Blo 1624511 1624587 := bstep (se 1 (by rfl) ⟨1218440, by rfl⟩ : syracuseStep 1624587 = 2436881) B2436881
theorem B1624599 : Blo 1624511 1624599 := bstep (se 1 (by rfl) ⟨1218449, by rfl⟩ : syracuseStep 1624599 = 2436899) B2436899
theorem B1624619 : Blo 1624511 1624619 := bstep (se 1 (by rfl) ⟨1218464, by rfl⟩ : syracuseStep 1624619 = 2436929) B2436929
theorem B1624631 : Blo 1624511 1624631 := bstep (se 1 (by rfl) ⟨1218473, by rfl⟩ : syracuseStep 1624631 = 2436947) B2436947
theorem B1624651 : Blo 1624511 1624651 := bstep (se 1 (by rfl) ⟨1218488, by rfl⟩ : syracuseStep 1624651 = 2436977) B2436977
theorem B3656267 : Blo 1624511 3656267 := bstep (se 1 (by rfl) ⟨2742200, by rfl⟩ : syracuseStep 3656267 = 5484401) B5484401
theorem B8792651 : Blo 1624511 8792651 := bstep (se 1 (by rfl) ⟨6594488, by rfl⟩ : syracuseStep 8792651 = 13188977) B13188977
theorem B1624663 : Blo 1624511 1624663 := bstep (se 1 (by rfl) ⟨1218497, by rfl⟩ : syracuseStep 1624663 = 2436995) B2436995
theorem B4115033 : Blo 1624511 4115033 := bstep (se 2 (by rfl) ⟨1543137, by rfl⟩ : syracuseStep 4115033 = 3086275) B3086275
theorem B1624683 : Blo 1624511 1624683 := bstep (se 1 (by rfl) ⟨1218512, by rfl⟩ : syracuseStep 1624683 = 2437025) B2437025
theorem B1624695 : Blo 1624511 1624695 := bstep (se 1 (by rfl) ⟨1218521, by rfl⟩ : syracuseStep 1624695 = 2437043) B2437043
theorem B3656321 : Blo 1624511 3656321 := bstep (se 2 (by rfl) ⟨1371120, by rfl⟩ : syracuseStep 3656321 = 2742241) B2742241
theorem B1624715 : Blo 1624511 1624715 := bstep (se 1 (by rfl) ⟨1218536, by rfl⟩ : syracuseStep 1624715 = 2437073) B2437073
theorem B3295883 : Blo 1624511 3295883 := bstep (se 1 (by rfl) ⟨2471912, by rfl⟩ : syracuseStep 3295883 = 4943825) B4943825
theorem B1829515 : Blo 1624511 1829515 := bstep (se 1 (by rfl) ⟨1372136, by rfl⟩ : syracuseStep 1829515 = 2744273) B2744273
theorem B5483159 : Blo 1624511 5483159 := bstep (se 1 (by rfl) ⟨4112369, by rfl⟩ : syracuseStep 5483159 = 8224739) B8224739
theorem B1624727 : Blo 1624511 1624727 := bstep (se 1 (by rfl) ⟨1218545, by rfl⟩ : syracuseStep 1624727 = 2437091) B2437091
theorem B1624747 : Blo 1624511 1624747 := bstep (se 1 (by rfl) ⟨1218560, by rfl⟩ : syracuseStep 1624747 = 2437121) B2437121
theorem B1624759 : Blo 1624511 1624759 := bstep (se 1 (by rfl) ⟨1218569, by rfl⟩ : syracuseStep 1624759 = 2437139) B2437139
theorem B1624779 : Blo 1624511 1624779 := bstep (se 1 (by rfl) ⟨1218584, by rfl⟩ : syracuseStep 1624779 = 2437169) B2437169
theorem B1624791 : Blo 1624511 1624791 := bstep (se 1 (by rfl) ⟨1218593, by rfl⟩ : syracuseStep 1624791 = 2437187) B2437187
theorem B1624811 : Blo 1624511 1624811 := bstep (se 1 (by rfl) ⟨1218608, by rfl⟩ : syracuseStep 1624811 = 2437217) B2437217
theorem B1624823 : Blo 1624511 1624823 := bstep (se 1 (by rfl) ⟨1218617, by rfl⟩ : syracuseStep 1624823 = 2437235) B2437235
theorem B1829623 : Blo 1624511 1829623 := bstep (se 1 (by rfl) ⟨1372217, by rfl⟩ : syracuseStep 1829623 = 2744435) B2744435
theorem B13880069 : Blo 1624511 13880069 := bstep (se 4 (by rfl) ⟨1301256, by rfl⟩ : syracuseStep 13880069 = 2602513) B2602513
theorem B1624843 : Blo 1624511 1624843 := bstep (se 1 (by rfl) ⟨1218632, by rfl⟩ : syracuseStep 1624843 = 2437265) B2437265
theorem B1624855 : Blo 1624511 1624855 := bstep (se 1 (by rfl) ⟨1218641, by rfl⟩ : syracuseStep 1624855 = 2437283) B2437283
theorem B2640665 : Blo 1624511 2640665 := bstep (se 2 (by rfl) ⟨990249, by rfl⟩ : syracuseStep 2640665 = 1980499) B1980499
theorem B1624875 : Blo 1624511 1624875 := bstep (se 1 (by rfl) ⟨1218656, by rfl⟩ : syracuseStep 1624875 = 2437313) B2437313
theorem B1624887 : Blo 1624511 1624887 := bstep (se 1 (by rfl) ⟨1218665, by rfl⟩ : syracuseStep 1624887 = 2437331) B2437331
theorem B1624907 : Blo 1624511 1624907 := bstep (se 1 (by rfl) ⟨1218680, by rfl⟩ : syracuseStep 1624907 = 2437361) B2437361
theorem B1952587 : Blo 1624511 1952587 := bstep (se 1 (by rfl) ⟨1464440, by rfl⟩ : syracuseStep 1952587 = 2928881) B2928881
theorem B1624919 : Blo 1624511 1624919 := bstep (se 1 (by rfl) ⟨1218689, by rfl⟩ : syracuseStep 1624919 = 2437379) B2437379
theorem B2313049 : Blo 1624511 2313049 := bstep (se 2 (by rfl) ⟨867393, by rfl⟩ : syracuseStep 2313049 = 1734787) B1734787
theorem B3656537 : Blo 1624511 3656537 := bstep (se 2 (by rfl) ⟨1371201, by rfl⟩ : syracuseStep 3656537 = 2742403) B2742403
theorem B1624939 : Blo 1624511 1624939 := bstep (se 1 (by rfl) ⟨1218704, by rfl⟩ : syracuseStep 1624939 = 2437409) B2437409
theorem B1624951 : Blo 1624511 1624951 := bstep (se 1 (by rfl) ⟨1218713, by rfl⟩ : syracuseStep 1624951 = 2437427) B2437427
theorem B1624971 : Blo 1624511 1624971 := bstep (se 1 (by rfl) ⟨1218728, by rfl⟩ : syracuseStep 1624971 = 2437457) B2437457
theorem B1624983 : Blo 1624511 1624983 := bstep (se 1 (by rfl) ⟨1218737, by rfl⟩ : syracuseStep 1624983 = 2437475) B2437475
theorem B1625003 : Blo 1624511 1625003 := bstep (se 1 (by rfl) ⟨1218752, by rfl⟩ : syracuseStep 1625003 = 2437505) B2437505
theorem B1829803 : Blo 1624511 1829803 := bstep (se 1 (by rfl) ⟨1372352, by rfl⟩ : syracuseStep 1829803 = 2744705) B2744705
theorem B3656627 : Blo 1624511 3656627 := bstep (se 1 (by rfl) ⟨2742470, by rfl⟩ : syracuseStep 3656627 = 5484941) B5484941
theorem B1625015 : Blo 1624511 1625015 := bstep (se 1 (by rfl) ⟨1218761, by rfl⟩ : syracuseStep 1625015 = 2437523) B2437523
theorem B1625035 : Blo 1624511 1625035 := bstep (se 1 (by rfl) ⟨1218776, by rfl⟩ : syracuseStep 1625035 = 2437553) B2437553
theorem B1625047 : Blo 1624511 1625047 := bstep (se 1 (by rfl) ⟨1218785, by rfl⟩ : syracuseStep 1625047 = 2437571) B2437571
theorem B3656663 : Blo 1624511 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B1625067 : Blo 1624511 1625067 := bstep (se 1 (by rfl) ⟨1218800, by rfl⟩ : syracuseStep 1625067 = 2437601) B2437601
theorem B1625079 : Blo 1624511 1625079 := bstep (se 1 (by rfl) ⟨1218809, by rfl⟩ : syracuseStep 1625079 = 2437619) B2437619
theorem B1625099 : Blo 1624511 1625099 := bstep (se 1 (by rfl) ⟨1218824, by rfl⟩ : syracuseStep 1625099 = 2437649) B2437649
theorem B22866961 : Blo 1624511 22866961 := bstep (se 2 (by rfl) ⟨8575110, by rfl⟩ : syracuseStep 22866961 = 17150221) B17150221
theorem B1625111 : Blo 1624511 1625111 := bstep (se 1 (by rfl) ⟨1218833, by rfl⟩ : syracuseStep 1625111 = 2437667) B2437667
theorem B1625131 : Blo 1624511 1625131 := bstep (se 1 (by rfl) ⟨1218848, by rfl⟩ : syracuseStep 1625131 = 2437697) B2437697
theorem B1625143 : Blo 1624511 1625143 := bstep (se 1 (by rfl) ⟨1218857, by rfl⟩ : syracuseStep 1625143 = 2437715) B2437715
theorem B1625163 : Blo 1624511 1625163 := bstep (se 1 (by rfl) ⟨1218872, by rfl⟩ : syracuseStep 1625163 = 2437745) B2437745
theorem B1625175 : Blo 1624511 1625175 := bstep (se 1 (by rfl) ⟨1218881, by rfl⟩ : syracuseStep 1625175 = 2437763) B2437763
theorem B1625195 : Blo 1624511 1625195 := bstep (se 1 (by rfl) ⟨1218896, by rfl⟩ : syracuseStep 1625195 = 2437793) B2437793
theorem B1625207 : Blo 1624511 1625207 := bstep (se 1 (by rfl) ⟨1218905, by rfl⟩ : syracuseStep 1625207 = 2437811) B2437811
theorem B1625227 : Blo 1624511 1625227 := bstep (se 1 (by rfl) ⟨1218920, by rfl⟩ : syracuseStep 1625227 = 2437841) B2437841
theorem B3656843 : Blo 1624511 3656843 := bstep (se 1 (by rfl) ⟨2742632, by rfl⟩ : syracuseStep 3656843 = 5485265) B5485265
theorem B1625239 : Blo 1624511 1625239 := bstep (se 1 (by rfl) ⟨1218929, by rfl⟩ : syracuseStep 1625239 = 2437859) B2437859
theorem B1625259 : Blo 1624511 1625259 := bstep (se 1 (by rfl) ⟨1218944, by rfl⟩ : syracuseStep 1625259 = 2437889) B2437889
theorem B6171821 : Blo 1624511 6171821 := bstep (se 3 (by rfl) ⟨1157216, by rfl⟩ : syracuseStep 6171821 = 2314433) B2314433
theorem B5483699 : Blo 1624511 5483699 := bstep (se 1 (by rfl) ⟨4112774, by rfl⟩ : syracuseStep 5483699 = 8225549) B8225549
theorem B1625271 : Blo 1624511 1625271 := bstep (se 1 (by rfl) ⟨1218953, by rfl⟩ : syracuseStep 1625271 = 2437907) B2437907
theorem B3656897 : Blo 1624511 3656897 := bstep (se 2 (by rfl) ⟨1371336, by rfl⟩ : syracuseStep 3656897 = 2742673) B2742673
theorem B1625291 : Blo 1624511 1625291 := bstep (se 1 (by rfl) ⟨1218968, by rfl⟩ : syracuseStep 1625291 = 2437937) B2437937
theorem B1625303 : Blo 1624511 1625303 := bstep (se 1 (by rfl) ⟨1218977, by rfl⟩ : syracuseStep 1625303 = 2437955) B2437955
theorem B1625323 : Blo 1624511 1625323 := bstep (se 1 (by rfl) ⟨1218992, by rfl⟩ : syracuseStep 1625323 = 2437985) B2437985
theorem B1625335 : Blo 1624511 1625335 := bstep (se 1 (by rfl) ⟨1219001, by rfl⟩ : syracuseStep 1625335 = 2438003) B2438003
theorem B1625355 : Blo 1624511 1625355 := bstep (se 1 (by rfl) ⟨1219016, by rfl⟩ : syracuseStep 1625355 = 2438033) B2438033
theorem B1625367 : Blo 1624511 1625367 := bstep (se 1 (by rfl) ⟨1219025, by rfl⟩ : syracuseStep 1625367 = 2438051) B2438051
theorem B1625387 : Blo 1624511 1625387 := bstep (se 1 (by rfl) ⟨1219040, by rfl⟩ : syracuseStep 1625387 = 2438081) B2438081
theorem B8228141 : Blo 1624511 8228141 := bstep (se 3 (by rfl) ⟨1542776, by rfl⟩ : syracuseStep 8228141 = 3085553) B3085553
theorem B1625399 : Blo 1624511 1625399 := bstep (se 1 (by rfl) ⟨1219049, by rfl⟩ : syracuseStep 1625399 = 2438099) B2438099
theorem B6942017 : Blo 1624511 6942017 := bstep (se 2 (by rfl) ⟨2603256, by rfl⟩ : syracuseStep 6942017 = 5206513) B5206513
theorem B5205323 : Blo 1624511 5205323 := bstep (se 1 (by rfl) ⟨3903992, by rfl⟩ : syracuseStep 5205323 = 7807985) B7807985
theorem B1625419 : Blo 1624511 1625419 := bstep (se 1 (by rfl) ⟨1219064, by rfl⟩ : syracuseStep 1625419 = 2438129) B2438129
theorem B1625431 : Blo 1624511 1625431 := bstep (se 1 (by rfl) ⟨1219073, by rfl⟩ : syracuseStep 1625431 = 2438147) B2438147
theorem B12348773 : Blo 1624511 12348773 := bstep (se 4 (by rfl) ⟨1157697, by rfl⟩ : syracuseStep 12348773 = 2315395) B2315395
theorem B1625451 : Blo 1624511 1625451 := bstep (se 1 (by rfl) ⟨1219088, by rfl⟩ : syracuseStep 1625451 = 2438177) B2438177
theorem B1625463 : Blo 1624511 1625463 := bstep (se 1 (by rfl) ⟨1219097, by rfl⟩ : syracuseStep 1625463 = 2438195) B2438195
theorem B1625483 : Blo 1624511 1625483 := bstep (se 1 (by rfl) ⟨1219112, by rfl⟩ : syracuseStep 1625483 = 2438225) B2438225
theorem B1625495 : Blo 1624511 1625495 := bstep (se 1 (by rfl) ⟨1219121, by rfl⟩ : syracuseStep 1625495 = 2438243) B2438243
theorem B3657113 : Blo 1624511 3657113 := bstep (se 2 (by rfl) ⟨1371417, by rfl⟩ : syracuseStep 3657113 = 2742835) B2742835
theorem B1625515 : Blo 1624511 1625515 := bstep (se 1 (by rfl) ⟨1219136, by rfl⟩ : syracuseStep 1625515 = 2438273) B2438273
theorem B13880753 : Blo 1624511 13880753 := bstep (se 2 (by rfl) ⟨5205282, by rfl⟩ : syracuseStep 13880753 = 10410565) B10410565
theorem B1625527 : Blo 1624511 1625527 := bstep (se 1 (by rfl) ⟨1219145, by rfl⟩ : syracuseStep 1625527 = 2438291) B2438291
theorem B5483969 : Blo 1624511 5483969 := bstep (se 2 (by rfl) ⟨2056488, by rfl⟩ : syracuseStep 5483969 = 4112977) B4112977
theorem B1625547 : Blo 1624511 1625547 := bstep (se 1 (by rfl) ⟨1219160, by rfl⟩ : syracuseStep 1625547 = 2438321) B2438321
theorem B1625559 : Blo 1624511 1625559 := bstep (se 1 (by rfl) ⟨1219169, by rfl⟩ : syracuseStep 1625559 = 2438339) B2438339
theorem B1625579 : Blo 1624511 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B3657203 : Blo 1624511 3657203 := bstep (se 1 (by rfl) ⟨2742902, by rfl⟩ : syracuseStep 3657203 = 5485805) B5485805
theorem B1625591 : Blo 1624511 1625591 := bstep (se 1 (by rfl) ⟨1219193, by rfl⟩ : syracuseStep 1625591 = 2438387) B2438387
theorem B1625611 : Blo 1624511 1625611 := bstep (se 1 (by rfl) ⟨1219208, by rfl⟩ : syracuseStep 1625611 = 2438417) B2438417
theorem B50040337 : Blo 1624511 50040337 := bstep (se 2 (by rfl) ⟨18765126, by rfl⟩ : syracuseStep 50040337 = 37530253) B37530253
theorem B3657239 : Blo 1624511 3657239 := bstep (se 1 (by rfl) ⟨2742929, by rfl⟩ : syracuseStep 3657239 = 5485859) B5485859
theorem B1625623 : Blo 1624511 1625623 := bstep (se 1 (by rfl) ⟨1219217, by rfl⟩ : syracuseStep 1625623 = 2438435) B2438435
theorem B1625643 : Blo 1624511 1625643 := bstep (se 1 (by rfl) ⟨1219232, by rfl⟩ : syracuseStep 1625643 = 2438465) B2438465
theorem B1625655 : Blo 1624511 1625655 := bstep (se 1 (by rfl) ⟨1219241, by rfl⟩ : syracuseStep 1625655 = 2438483) B2438483
theorem B1625675 : Blo 1624511 1625675 := bstep (se 1 (by rfl) ⟨1219256, by rfl⟩ : syracuseStep 1625675 = 2438513) B2438513
theorem B1625687 : Blo 1624511 1625687 := bstep (se 1 (by rfl) ⟨1219265, by rfl⟩ : syracuseStep 1625687 = 2438531) B2438531
theorem B1625707 : Blo 1624511 1625707 := bstep (se 1 (by rfl) ⟨1219280, by rfl⟩ : syracuseStep 1625707 = 2438561) B2438561
theorem B1625719 : Blo 1624511 1625719 := bstep (se 1 (by rfl) ⟨1219289, by rfl⟩ : syracuseStep 1625719 = 2438579) B2438579
theorem B1625739 : Blo 1624511 1625739 := bstep (se 1 (by rfl) ⟨1219304, by rfl⟩ : syracuseStep 1625739 = 2438609) B2438609
theorem B8785559 : Blo 1624511 8785559 := bstep (se 1 (by rfl) ⟨6589169, by rfl⟩ : syracuseStep 8785559 = 13178339) B13178339
theorem B1625751 : Blo 1624511 1625751 := bstep (se 1 (by rfl) ⟨1219313, by rfl⟩ : syracuseStep 1625751 = 2438627) B2438627
theorem B1625771 : Blo 1624511 1625771 := bstep (se 1 (by rfl) ⟨1219328, by rfl⟩ : syracuseStep 1625771 = 2438657) B2438657
theorem B23432885 : Blo 1624511 23432885 := bstep (se 5 (by rfl) ⟨1098416, by rfl⟩ : syracuseStep 23432885 = 2196833) B2196833
theorem B1625783 : Blo 1624511 1625783 := bstep (se 1 (by rfl) ⟨1219337, by rfl⟩ : syracuseStep 1625783 = 2438675) B2438675
theorem B3657419 : Blo 1624511 3657419 := bstep (se 1 (by rfl) ⟨2743064, by rfl⟩ : syracuseStep 3657419 = 5486129) B5486129
theorem B1625803 : Blo 1624511 1625803 := bstep (se 1 (by rfl) ⟨1219352, by rfl⟩ : syracuseStep 1625803 = 2438705) B2438705
theorem B1625815 : Blo 1624511 1625815 := bstep (se 1 (by rfl) ⟨1219361, by rfl⟩ : syracuseStep 1625815 = 2438723) B2438723
theorem B1625835 : Blo 1624511 1625835 := bstep (se 1 (by rfl) ⟨1219376, by rfl⟩ : syracuseStep 1625835 = 2438753) B2438753
theorem B1625847 : Blo 1624511 1625847 := bstep (se 1 (by rfl) ⟨1219385, by rfl⟩ : syracuseStep 1625847 = 2438771) B2438771
theorem B3657473 : Blo 1624511 3657473 := bstep (se 2 (by rfl) ⟨1371552, by rfl⟩ : syracuseStep 3657473 = 2743105) B2743105
theorem B12340997 : Blo 1624511 12340997 := bstep (se 4 (by rfl) ⟨1156968, by rfl⟩ : syracuseStep 12340997 = 2313937) B2313937
theorem B2436875 : Blo 1624511 2436875 := bstep (se 1 (by rfl) ⟨1827656, by rfl⟩ : syracuseStep 2436875 = 3655313) B3655313
theorem B1625867 : Blo 1624511 1625867 := bstep (se 1 (by rfl) ⟨1219400, by rfl⟩ : syracuseStep 1625867 = 2438801) B2438801
theorem B13176593 : Blo 1624511 13176593 := bstep (se 2 (by rfl) ⟨4941222, by rfl⟩ : syracuseStep 13176593 = 9882445) B9882445
theorem B2436887 : Blo 1624511 2436887 := bstep (se 1 (by rfl) ⟨1827665, by rfl⟩ : syracuseStep 2436887 = 3655331) B3655331
theorem B1625879 : Blo 1624511 1625879 := bstep (se 1 (by rfl) ⟨1219409, by rfl⟩ : syracuseStep 1625879 = 2438819) B2438819
theorem B1625899 : Blo 1624511 1625899 := bstep (se 1 (by rfl) ⟨1219424, by rfl⟩ : syracuseStep 1625899 = 2438849) B2438849
theorem B1625911 : Blo 1624511 1625911 := bstep (se 1 (by rfl) ⟨1219433, by rfl⟩ : syracuseStep 1625911 = 2438867) B2438867
theorem B1625931 : Blo 1624511 1625931 := bstep (se 1 (by rfl) ⟨1219448, by rfl⟩ : syracuseStep 1625931 = 2438897) B2438897
theorem B12349259 : Blo 1624511 12349259 := bstep (se 1 (by rfl) ⟨9261944, by rfl⟩ : syracuseStep 12349259 = 18523889) B18523889
theorem B11882315 : Blo 1624511 11882315 := bstep (se 1 (by rfl) ⟨8911736, by rfl⟩ : syracuseStep 11882315 = 17823473) B17823473
theorem B1625943 : Blo 1624511 1625943 := bstep (se 1 (by rfl) ⟨1219457, by rfl⟩ : syracuseStep 1625943 = 2438915) B2438915
theorem B2436953 : Blo 1624511 2436953 := bstep (se 2 (by rfl) ⟨913857, by rfl⟩ : syracuseStep 2436953 = 1827715) B1827715
theorem B4394845 : Blo 1624511 4394845 := bstep (se 3 (by rfl) ⟨824033, by rfl⟩ : syracuseStep 4394845 = 1648067) B1648067
theorem B1625963 : Blo 1624511 1625963 := bstep (se 1 (by rfl) ⟨1219472, by rfl⟩ : syracuseStep 1625963 = 2438945) B2438945
theorem B1625975 : Blo 1624511 1625975 := bstep (se 1 (by rfl) ⟨1219481, by rfl⟩ : syracuseStep 1625975 = 2438963) B2438963
theorem B1625995 : Blo 1624511 1625995 := bstep (se 1 (by rfl) ⟨1219496, by rfl⟩ : syracuseStep 1625995 = 2438993) B2438993
theorem B1626007 : Blo 1624511 1626007 := bstep (se 1 (by rfl) ⟨1219505, by rfl⟩ : syracuseStep 1626007 = 2439011) B2439011
theorem B1626027 : Blo 1624511 1626027 := bstep (se 1 (by rfl) ⟨1219520, by rfl⟩ : syracuseStep 1626027 = 2439041) B2439041
theorem B27774899 : Blo 1624511 27774899 := bstep (se 1 (by rfl) ⟨20831174, by rfl⟩ : syracuseStep 27774899 = 41662349) B41662349
theorem B6172595 : Blo 1624511 6172595 := bstep (se 1 (by rfl) ⟨4629446, by rfl⟩ : syracuseStep 6172595 = 9258893) B9258893
theorem B1626039 : Blo 1624511 1626039 := bstep (se 1 (by rfl) ⟨1219529, by rfl⟩ : syracuseStep 1626039 = 2439059) B2439059
theorem B2437067 : Blo 1624511 2437067 := bstep (se 1 (by rfl) ⟨1827800, by rfl⟩ : syracuseStep 2437067 = 3655601) B3655601
theorem B1626059 : Blo 1624511 1626059 := bstep (se 1 (by rfl) ⟨1219544, by rfl⟩ : syracuseStep 1626059 = 2439089) B2439089
theorem B3084247 : Blo 1624511 3084247 := bstep (se 1 (by rfl) ⟨2313185, by rfl⟩ : syracuseStep 3084247 = 4626371) B4626371
theorem B2437079 : Blo 1624511 2437079 := bstep (se 1 (by rfl) ⟨1827809, by rfl⟩ : syracuseStep 2437079 = 3655619) B3655619
theorem B3657689 : Blo 1624511 3657689 := bstep (se 2 (by rfl) ⟨1371633, by rfl⟩ : syracuseStep 3657689 = 2743267) B2743267
theorem B1626071 : Blo 1624511 1626071 := bstep (se 1 (by rfl) ⟨1219553, by rfl⟩ : syracuseStep 1626071 = 2439107) B2439107
theorem B5484509 : Blo 1624511 5484509 := bstep (se 3 (by rfl) ⟨1028345, by rfl⟩ : syracuseStep 5484509 = 2056691) B2056691
theorem B1626091 : Blo 1624511 1626091 := bstep (se 1 (by rfl) ⟨1219568, by rfl⟩ : syracuseStep 1626091 = 2439137) B2439137
theorem B1626103 : Blo 1624511 1626103 := bstep (se 1 (by rfl) ⟨1219577, by rfl⟩ : syracuseStep 1626103 = 2439155) B2439155
theorem B1626123 : Blo 1624511 1626123 := bstep (se 1 (by rfl) ⟨1219592, by rfl⟩ : syracuseStep 1626123 = 2439185) B2439185
theorem B1626135 : Blo 1624511 1626135 := bstep (se 1 (by rfl) ⟨1219601, by rfl⟩ : syracuseStep 1626135 = 2439203) B2439203
theorem B2437145 : Blo 1624511 2437145 := bstep (se 2 (by rfl) ⟨913929, by rfl⟩ : syracuseStep 2437145 = 1827859) B1827859
theorem B1626155 : Blo 1624511 1626155 := bstep (se 1 (by rfl) ⟨1219616, by rfl⟩ : syracuseStep 1626155 = 2439233) B2439233
theorem B3657779 : Blo 1624511 3657779 := bstep (se 1 (by rfl) ⟨2743334, by rfl⟩ : syracuseStep 3657779 = 5486669) B5486669
theorem B1626167 : Blo 1624511 1626167 := bstep (se 1 (by rfl) ⟨1219625, by rfl⟩ : syracuseStep 1626167 = 2439251) B2439251
theorem B4395073 : Blo 1624511 4395073 := bstep (se 2 (by rfl) ⟨1648152, by rfl⟩ : syracuseStep 4395073 = 3296305) B3296305
theorem B1626187 : Blo 1624511 1626187 := bstep (se 1 (by rfl) ⟨1219640, by rfl⟩ : syracuseStep 1626187 = 2439281) B2439281
theorem B3657815 : Blo 1624511 3657815 := bstep (se 1 (by rfl) ⟨2743361, by rfl⟩ : syracuseStep 3657815 = 5486723) B5486723
theorem B1626199 : Blo 1624511 1626199 := bstep (se 1 (by rfl) ⟨1219649, by rfl⟩ : syracuseStep 1626199 = 2439299) B2439299
theorem B1626219 : Blo 1624511 1626219 := bstep (se 1 (by rfl) ⟨1219664, by rfl⟩ : syracuseStep 1626219 = 2439329) B2439329
theorem B1626231 : Blo 1624511 1626231 := bstep (se 1 (by rfl) ⟨1219673, by rfl⟩ : syracuseStep 1626231 = 2439347) B2439347
theorem B2437259 : Blo 1624511 2437259 := bstep (se 1 (by rfl) ⟨1827944, by rfl⟩ : syracuseStep 2437259 = 3655889) B3655889
theorem B1626251 : Blo 1624511 1626251 := bstep (se 1 (by rfl) ⟨1219688, by rfl⟩ : syracuseStep 1626251 = 2439377) B2439377
theorem B2437271 : Blo 1624511 2437271 := bstep (se 1 (by rfl) ⟨1827953, by rfl⟩ : syracuseStep 2437271 = 3655907) B3655907
theorem B1626263 : Blo 1624511 1626263 := bstep (se 1 (by rfl) ⟨1219697, by rfl⟩ : syracuseStep 1626263 = 2439395) B2439395
theorem B1626283 : Blo 1624511 1626283 := bstep (se 1 (by rfl) ⟨1219712, by rfl⟩ : syracuseStep 1626283 = 2439425) B2439425
theorem B1626295 : Blo 1624511 1626295 := bstep (se 1 (by rfl) ⟨1219721, by rfl⟩ : syracuseStep 1626295 = 2439443) B2439443
theorem B1626315 : Blo 1624511 1626315 := bstep (se 1 (by rfl) ⟨1219736, by rfl⟩ : syracuseStep 1626315 = 2439473) B2439473
theorem B4116683 : Blo 1624511 4116683 := bstep (se 1 (by rfl) ⟨3087512, by rfl⟩ : syracuseStep 4116683 = 6175025) B6175025
theorem B1626327 : Blo 1624511 1626327 := bstep (se 1 (by rfl) ⟨1219745, by rfl⟩ : syracuseStep 1626327 = 2439491) B2439491
theorem B2437337 : Blo 1624511 2437337 := bstep (se 2 (by rfl) ⟨914001, by rfl⟩ : syracuseStep 2437337 = 1828003) B1828003
theorem B6942941 : Blo 1624511 6942941 := bstep (se 3 (by rfl) ⟨1301801, by rfl⟩ : syracuseStep 6942941 = 2603603) B2603603
theorem B1626347 : Blo 1624511 1626347 := bstep (se 1 (by rfl) ⟨1219760, by rfl⟩ : syracuseStep 1626347 = 2439521) B2439521
theorem B1626359 : Blo 1624511 1626359 := bstep (se 1 (by rfl) ⟨1219769, by rfl⟩ : syracuseStep 1626359 = 2439539) B2439539
theorem B2314507 : Blo 1624511 2314507 := bstep (se 1 (by rfl) ⟨1735880, by rfl⟩ : syracuseStep 2314507 = 3471761) B3471761
theorem B3657995 : Blo 1624511 3657995 := bstep (se 1 (by rfl) ⟨2743496, by rfl⟩ : syracuseStep 3657995 = 5486993) B5486993
theorem B1626379 : Blo 1624511 1626379 := bstep (se 1 (by rfl) ⟨1219784, by rfl⟩ : syracuseStep 1626379 = 2439569) B2439569
theorem B1626391 : Blo 1624511 1626391 := bstep (se 1 (by rfl) ⟨1219793, by rfl⟩ : syracuseStep 1626391 = 2439587) B2439587
theorem B1626411 : Blo 1624511 1626411 := bstep (se 1 (by rfl) ⟨1219808, by rfl⟩ : syracuseStep 1626411 = 2439617) B2439617
theorem B21115181 : Blo 1624511 21115181 := bstep (se 3 (by rfl) ⟨3959096, by rfl⟩ : syracuseStep 21115181 = 7918193) B7918193
theorem B22245677 : Blo 1624511 22245677 := bstep (se 3 (by rfl) ⟨4171064, by rfl⟩ : syracuseStep 22245677 = 8342129) B8342129
theorem B1626423 : Blo 1624511 1626423 := bstep (se 1 (by rfl) ⟨1219817, by rfl⟩ : syracuseStep 1626423 = 2439635) B2439635
theorem B3658049 : Blo 1624511 3658049 := bstep (se 2 (by rfl) ⟨1371768, by rfl⟩ : syracuseStep 3658049 = 2743537) B2743537
theorem B9261377 : Blo 1624511 9261377 := bstep (se 2 (by rfl) ⟨3473016, by rfl⟩ : syracuseStep 9261377 = 6946033) B6946033
theorem B2437451 : Blo 1624511 2437451 := bstep (se 1 (by rfl) ⟨1828088, by rfl⟩ : syracuseStep 2437451 = 3656177) B3656177
theorem B1626443 : Blo 1624511 1626443 := bstep (se 1 (by rfl) ⟨1219832, by rfl⟩ : syracuseStep 1626443 = 2439665) B2439665
theorem B2437463 : Blo 1624511 2437463 := bstep (se 1 (by rfl) ⟨1828097, by rfl⟩ : syracuseStep 2437463 = 3656195) B3656195
theorem B1626455 : Blo 1624511 1626455 := bstep (se 1 (by rfl) ⟨1219841, by rfl⟩ : syracuseStep 1626455 = 2439683) B2439683
theorem B1626475 : Blo 1624511 1626475 := bstep (se 1 (by rfl) ⟨1219856, by rfl⟩ : syracuseStep 1626475 = 2439713) B2439713
theorem B1626487 : Blo 1624511 1626487 := bstep (se 1 (by rfl) ⟨1219865, by rfl⟩ : syracuseStep 1626487 = 2439731) B2439731
theorem B1626507 : Blo 1624511 1626507 := bstep (se 1 (by rfl) ⟨1219880, by rfl⟩ : syracuseStep 1626507 = 2439761) B2439761
theorem B2437529 : Blo 1624511 2437529 := bstep (se 2 (by rfl) ⟨914073, by rfl⟩ : syracuseStep 2437529 = 1828147) B1828147
theorem B13881779 : Blo 1624511 13881779 := bstep (se 1 (by rfl) ⟨10411334, by rfl⟩ : syracuseStep 13881779 = 20822669) B20822669
theorem B2437643 : Blo 1624511 2437643 := bstep (se 1 (by rfl) ⟨1828232, by rfl⟩ : syracuseStep 2437643 = 3656465) B3656465
theorem B11874833 : Blo 1624511 11874833 := bstep (se 2 (by rfl) ⟨4453062, by rfl⟩ : syracuseStep 11874833 = 8906125) B8906125
theorem B2437655 : Blo 1624511 2437655 := bstep (se 1 (by rfl) ⟨1828241, by rfl⟩ : syracuseStep 2437655 = 3656483) B3656483
theorem B3658265 : Blo 1624511 3658265 := bstep (se 2 (by rfl) ⟨1371849, by rfl⟩ : syracuseStep 3658265 = 2743699) B2743699
theorem B2437721 : Blo 1624511 2437721 := bstep (se 2 (by rfl) ⟨914145, by rfl⟩ : syracuseStep 2437721 = 1828291) B1828291
theorem B3658355 : Blo 1624511 3658355 := bstep (se 1 (by rfl) ⟨2743766, by rfl⟩ : syracuseStep 3658355 = 5487533) B5487533
theorem B3658391 : Blo 1624511 3658391 := bstep (se 1 (by rfl) ⟨2743793, by rfl⟩ : syracuseStep 3658391 = 5487587) B5487587
theorem B2437835 : Blo 1624511 2437835 := bstep (se 1 (by rfl) ⟨1828376, by rfl⟩ : syracuseStep 2437835 = 3656753) B3656753
theorem B2437847 : Blo 1624511 2437847 := bstep (se 1 (by rfl) ⟨1828385, by rfl⟩ : syracuseStep 2437847 = 3656771) B3656771
theorem B3085067 : Blo 1624511 3085067 := bstep (se 1 (by rfl) ⟨2313800, by rfl⟩ : syracuseStep 3085067 = 4627601) B4627601
theorem B2437913 : Blo 1624511 2437913 := bstep (se 2 (by rfl) ⟨914217, by rfl⟩ : syracuseStep 2437913 = 1828435) B1828435
theorem B3085121 : Blo 1624511 3085121 := bstep (se 2 (by rfl) ⟨1156920, by rfl⟩ : syracuseStep 3085121 = 2313841) B2313841
theorem B6255425 : Blo 1624511 6255425 := bstep (se 2 (by rfl) ⟨2345784, by rfl⟩ : syracuseStep 6255425 = 4691569) B4691569
theorem B3658571 : Blo 1624511 3658571 := bstep (se 1 (by rfl) ⟨2743928, by rfl⟩ : syracuseStep 3658571 = 5487857) B5487857
theorem B3658625 : Blo 1624511 3658625 := bstep (se 2 (by rfl) ⟨1371984, by rfl⟩ : syracuseStep 3658625 = 2743969) B2743969
theorem B2438027 : Blo 1624511 2438027 := bstep (se 1 (by rfl) ⟨1828520, by rfl⟩ : syracuseStep 2438027 = 3657041) B3657041
theorem B2438039 : Blo 1624511 2438039 := bstep (se 1 (by rfl) ⟨1828529, by rfl⟩ : syracuseStep 2438039 = 3657059) B3657059
theorem B5206963 : Blo 1624511 5206963 := bstep (se 1 (by rfl) ⟨3905222, by rfl⟩ : syracuseStep 5206963 = 7810445) B7810445
theorem B2438105 : Blo 1624511 2438105 := bstep (se 2 (by rfl) ⟨914289, by rfl⟩ : syracuseStep 2438105 = 1828579) B1828579
theorem B3470359 : Blo 1624511 3470359 := bstep (se 1 (by rfl) ⟨2602769, by rfl⟩ : syracuseStep 3470359 = 5205539) B5205539
theorem B5485643 : Blo 1624511 5485643 := bstep (se 1 (by rfl) ⟨4114232, by rfl⟩ : syracuseStep 5485643 = 8228465) B8228465
theorem B2438219 : Blo 1624511 2438219 := bstep (se 1 (by rfl) ⟨1828664, by rfl⟩ : syracuseStep 2438219 = 3657329) B3657329
theorem B2438231 : Blo 1624511 2438231 := bstep (se 1 (by rfl) ⟨1828673, by rfl⟩ : syracuseStep 2438231 = 3657347) B3657347
theorem B5207129 : Blo 1624511 5207129 := bstep (se 2 (by rfl) ⟨1952673, by rfl⟩ : syracuseStep 5207129 = 3905347) B3905347
theorem B6681689 : Blo 1624511 6681689 := bstep (se 2 (by rfl) ⟨2505633, by rfl⟩ : syracuseStep 6681689 = 5011267) B5011267
theorem B3658841 : Blo 1624511 3658841 := bstep (se 2 (by rfl) ⟨1372065, by rfl⟩ : syracuseStep 3658841 = 2744131) B2744131
theorem B2438297 : Blo 1624511 2438297 := bstep (se 2 (by rfl) ⟨914361, by rfl⟩ : syracuseStep 2438297 = 1828723) B1828723
theorem B2929817 : Blo 1624511 2929817 := bstep (se 2 (by rfl) ⟨1098681, by rfl⟩ : syracuseStep 2929817 = 2197363) B2197363
theorem B3658931 : Blo 1624511 3658931 := bstep (se 1 (by rfl) ⟨2744198, by rfl⟩ : syracuseStep 3658931 = 5488397) B5488397
theorem B3658967 : Blo 1624511 3658967 := bstep (se 1 (by rfl) ⟨2744225, by rfl⟩ : syracuseStep 3658967 = 5488451) B5488451
theorem B2741465 : Blo 1624511 2741465 := bstep (se 2 (by rfl) ⟨1028049, by rfl⟩ : syracuseStep 2741465 = 2056099) B2056099
theorem B2438411 : Blo 1624511 2438411 := bstep (se 1 (by rfl) ⟨1828808, by rfl⟩ : syracuseStep 2438411 = 3657617) B3657617
theorem B2438423 : Blo 1624511 2438423 := bstep (se 1 (by rfl) ⟨1828817, by rfl⟩ : syracuseStep 2438423 = 3657635) B3657635
theorem B2471255 : Blo 1624511 2471255 := bstep (se 1 (by rfl) ⟨1853441, by rfl⟩ : syracuseStep 2471255 = 3706883) B3706883
theorem B2741593 : Blo 1624511 2741593 := bstep (se 2 (by rfl) ⟨1028097, by rfl⟩ : syracuseStep 2741593 = 2056195) B2056195
theorem B5485913 : Blo 1624511 5485913 := bstep (se 2 (by rfl) ⟨2057217, by rfl⟩ : syracuseStep 5485913 = 4114435) B4114435
theorem B2438489 : Blo 1624511 2438489 := bstep (se 2 (by rfl) ⟨914433, by rfl⟩ : syracuseStep 2438489 = 1828867) B1828867
theorem B30078307 : Blo 1624511 30078307 := bstep (se 1 (by rfl) ⟨22558730, by rfl⟩ : syracuseStep 30078307 = 45117461) B45117461
theorem B6174083 : Blo 1624511 6174083 := bstep (se 1 (by rfl) ⟨4630562, by rfl⟩ : syracuseStep 6174083 = 9261125) B9261125
theorem B3659147 : Blo 1624511 3659147 := bstep (se 1 (by rfl) ⟨2744360, by rfl⟩ : syracuseStep 3659147 = 5488721) B5488721
theorem B3659201 : Blo 1624511 3659201 := bstep (se 2 (by rfl) ⟨1372200, by rfl⟩ : syracuseStep 3659201 = 2744401) B2744401
theorem B2438603 : Blo 1624511 2438603 := bstep (se 1 (by rfl) ⟨1828952, by rfl⟩ : syracuseStep 2438603 = 3657905) B3657905
theorem B2438615 : Blo 1624511 2438615 := bstep (se 1 (by rfl) ⟨1828961, by rfl⟩ : syracuseStep 2438615 = 3657923) B3657923
theorem B2315737 : Blo 1624511 2315737 := bstep (se 2 (by rfl) ⟨868401, by rfl⟩ : syracuseStep 2315737 = 1736803) B1736803
theorem B2438681 : Blo 1624511 2438681 := bstep (se 2 (by rfl) ⟨914505, by rfl⟩ : syracuseStep 2438681 = 1829011) B1829011
theorem B2438795 : Blo 1624511 2438795 := bstep (se 1 (by rfl) ⟨1829096, by rfl⟩ : syracuseStep 2438795 = 3658193) B3658193
theorem B2438807 : Blo 1624511 2438807 := bstep (se 1 (by rfl) ⟨1829105, by rfl⟩ : syracuseStep 2438807 = 3658211) B3658211
theorem B3659417 : Blo 1624511 3659417 := bstep (se 2 (by rfl) ⟨1372281, by rfl⟩ : syracuseStep 3659417 = 2744563) B2744563
theorem B8787635 : Blo 1624511 8787635 := bstep (se 1 (by rfl) ⟨6590726, by rfl⟩ : syracuseStep 8787635 = 13181453) B13181453
theorem B7534259 : Blo 1624511 7534259 := bstep (se 1 (by rfl) ⟨5650694, by rfl⟩ : syracuseStep 7534259 = 11301389) B11301389
theorem B11712205 : Blo 1624511 11712205 := bstep (se 3 (by rfl) ⟨2196038, by rfl⟩ : syracuseStep 11712205 = 4392077) B4392077
theorem B13891277 : Blo 1624511 13891277 := bstep (se 3 (by rfl) ⟨2604614, by rfl⟩ : syracuseStep 13891277 = 5209229) B5209229
theorem B3086039 : Blo 1624511 3086039 := bstep (se 1 (by rfl) ⟨2314529, by rfl⟩ : syracuseStep 3086039 = 4629059) B4629059
theorem B2438873 : Blo 1624511 2438873 := bstep (se 2 (by rfl) ⟨914577, by rfl⟩ : syracuseStep 2438873 = 1829155) B1829155
theorem B3659507 : Blo 1624511 3659507 := bstep (se 1 (by rfl) ⟨2744630, by rfl⟩ : syracuseStep 3659507 = 5489261) B5489261
theorem B3659543 : Blo 1624511 3659543 := bstep (se 1 (by rfl) ⟨2744657, by rfl⟩ : syracuseStep 3659543 = 5489315) B5489315
theorem B5855021 : Blo 1624511 5855021 := bstep (se 3 (by rfl) ⟨1097816, by rfl⟩ : syracuseStep 5855021 = 2195633) B2195633
theorem B3471179 : Blo 1624511 3471179 := bstep (se 1 (by rfl) ⟨2603384, by rfl⟩ : syracuseStep 3471179 = 5206769) B5206769
theorem B2438987 : Blo 1624511 2438987 := bstep (se 1 (by rfl) ⟨1829240, by rfl⟩ : syracuseStep 2438987 = 3658481) B3658481
theorem B6174539 : Blo 1624511 6174539 := bstep (se 1 (by rfl) ⟨4630904, by rfl⟩ : syracuseStep 6174539 = 9261809) B9261809
theorem B2438999 : Blo 1624511 2438999 := bstep (se 1 (by rfl) ⟨1829249, by rfl⟩ : syracuseStep 2438999 = 3658499) B3658499
theorem B5207897 : Blo 1624511 5207897 := bstep (se 2 (by rfl) ⟨1952961, by rfl⟩ : syracuseStep 5207897 = 3905923) B3905923
theorem B2742167 : Blo 1624511 2742167 := bstep (se 1 (by rfl) ⟨2056625, by rfl⟩ : syracuseStep 2742167 = 4113251) B4113251
theorem B2439065 : Blo 1624511 2439065 := bstep (se 2 (by rfl) ⟨914649, by rfl⟩ : syracuseStep 2439065 = 1829299) B1829299
theorem B2439179 : Blo 1624511 2439179 := bstep (se 1 (by rfl) ⟨1829384, by rfl⟩ : syracuseStep 2439179 = 3658769) B3658769
theorem B6592529 : Blo 1624511 6592529 := bstep (se 2 (by rfl) ⟨2472198, by rfl⟩ : syracuseStep 6592529 = 4944397) B4944397
theorem B6174737 : Blo 1624511 6174737 := bstep (se 2 (by rfl) ⟨2315526, by rfl⟩ : syracuseStep 6174737 = 4631053) B4631053
theorem B2742295 : Blo 1624511 2742295 := bstep (se 1 (by rfl) ⟨2056721, by rfl⟩ : syracuseStep 2742295 = 4113443) B4113443
theorem B5486615 : Blo 1624511 5486615 := bstep (se 1 (by rfl) ⟨4114961, by rfl⟩ : syracuseStep 5486615 = 8229923) B8229923
theorem B2439191 : Blo 1624511 2439191 := bstep (se 1 (by rfl) ⟨1829393, by rfl⟩ : syracuseStep 2439191 = 3658787) B3658787
theorem B10410029 : Blo 1624511 10410029 := bstep (se 3 (by rfl) ⟨1951880, by rfl⟩ : syracuseStep 10410029 = 3903761) B3903761
theorem B4626497 : Blo 1624511 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B2439257 : Blo 1624511 2439257 := bstep (se 2 (by rfl) ⟨914721, by rfl⟩ : syracuseStep 2439257 = 1829443) B1829443
theorem B10582109 : Blo 1624511 10582109 := bstep (se 3 (by rfl) ⟨1984145, by rfl⟩ : syracuseStep 10582109 = 3968291) B3968291
theorem B12343427 : Blo 1624511 12343427 := bstep (se 1 (by rfl) ⟨9257570, by rfl⟩ : syracuseStep 12343427 = 18515141) B18515141
theorem B106854551 : Blo 1624511 106854551 := bstep (se 1 (by rfl) ⟨80140913, by rfl⟩ : syracuseStep 106854551 = 160281827) B160281827
theorem B2439371 : Blo 1624511 2439371 := bstep (se 1 (by rfl) ⟨1829528, by rfl⟩ : syracuseStep 2439371 = 3659057) B3659057
theorem B2439383 : Blo 1624511 2439383 := bstep (se 1 (by rfl) ⟨1829537, by rfl⟩ : syracuseStep 2439383 = 3659075) B3659075
theorem B2603225 : Blo 1624511 2603225 := bstep (se 2 (by rfl) ⟨976209, by rfl⟩ : syracuseStep 2603225 = 1952419) B1952419
theorem B3086579 : Blo 1624511 3086579 := bstep (se 1 (by rfl) ⟨2314934, by rfl⟩ : syracuseStep 3086579 = 4629869) B4629869
theorem B10410257 : Blo 1624511 10410257 := bstep (se 2 (by rfl) ⟨3903846, by rfl⟩ : syracuseStep 10410257 = 7807693) B7807693
theorem B2439449 : Blo 1624511 2439449 := bstep (se 2 (by rfl) ⟨914793, by rfl⟩ : syracuseStep 2439449 = 1829587) B1829587
theorem B3520793 : Blo 1624511 3520793 := bstep (se 2 (by rfl) ⟨1320297, by rfl⟩ : syracuseStep 3520793 = 2640595) B2640595
theorem B5855539 : Blo 1624511 5855539 := bstep (se 1 (by rfl) ⟨4391654, by rfl⟩ : syracuseStep 5855539 = 8783309) B8783309
theorem B5208409 : Blo 1624511 5208409 := bstep (se 2 (by rfl) ⟨1953153, by rfl⟩ : syracuseStep 5208409 = 3906307) B3906307
theorem B2439563 : Blo 1624511 2439563 := bstep (se 1 (by rfl) ⟨1829672, by rfl⟩ : syracuseStep 2439563 = 3659345) B3659345
theorem B2439575 : Blo 1624511 2439575 := bstep (se 1 (by rfl) ⟨1829681, by rfl⟩ : syracuseStep 2439575 = 3659363) B3659363
theorem B2439641 : Blo 1624511 2439641 := bstep (se 2 (by rfl) ⟨914865, by rfl⟩ : syracuseStep 2439641 = 1829731) B1829731
theorem B3471923 : Blo 1624511 3471923 := bstep (se 1 (by rfl) ⟨2603942, by rfl⟩ : syracuseStep 3471923 = 5207885) B5207885
theorem B5487155 : Blo 1624511 5487155 := bstep (se 1 (by rfl) ⟨4115366, by rfl⟩ : syracuseStep 5487155 = 8230733) B8230733
theorem B9886283 : Blo 1624511 9886283 := bstep (se 1 (by rfl) ⟨7414712, by rfl⟩ : syracuseStep 9886283 = 14829425) B14829425
theorem B2439755 : Blo 1624511 2439755 := bstep (se 1 (by rfl) ⟨1829816, by rfl⟩ : syracuseStep 2439755 = 3659633) B3659633
theorem B2439767 : Blo 1624511 2439767 := bstep (se 1 (by rfl) ⟨1829825, by rfl⟩ : syracuseStep 2439767 = 3659651) B3659651
theorem B2742923 : Blo 1624511 2742923 := bstep (se 1 (by rfl) ⟨2057192, by rfl⟩ : syracuseStep 2742923 = 4114385) B4114385
theorem B3906251 : Blo 1624511 3906251 := bstep (se 1 (by rfl) ⟨2929688, by rfl⟩ : syracuseStep 3906251 = 5859377) B5859377
theorem B3087065 : Blo 1624511 3087065 := bstep (se 2 (by rfl) ⟨1157649, by rfl⟩ : syracuseStep 3087065 = 2315299) B2315299
theorem B2743051 : Blo 1624511 2743051 := bstep (se 1 (by rfl) ⟨2057288, by rfl⟩ : syracuseStep 2743051 = 4114577) B4114577
theorem B6175511 : Blo 1624511 6175511 := bstep (se 1 (by rfl) ⟨4631633, by rfl⟩ : syracuseStep 6175511 = 9263267) B9263267
theorem B5487425 : Blo 1624511 5487425 := bstep (se 2 (by rfl) ⟨2057784, by rfl⟩ : syracuseStep 5487425 = 4115569) B4115569
theorem B2743193 : Blo 1624511 2743193 := bstep (se 2 (by rfl) ⟨1028697, by rfl⟩ : syracuseStep 2743193 = 2057395) B2057395
theorem B1735607 : Blo 1624511 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B2743321 : Blo 1624511 2743321 := bstep (se 2 (by rfl) ⟨1028745, by rfl⟩ : syracuseStep 2743321 = 2057491) B2057491
theorem B8232029 : Blo 1624511 8232029 := bstep (se 3 (by rfl) ⟨1543505, by rfl⟩ : syracuseStep 8232029 = 3087011) B3087011
theorem B5856407 : Blo 1624511 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B31653125 : Blo 1624511 31653125 := bstep (se 4 (by rfl) ⟨2967480, by rfl⟩ : syracuseStep 31653125 = 5934961) B5934961
theorem B17571077 : Blo 1624511 17571077 := bstep (se 4 (by rfl) ⟨1647288, by rfl⟩ : syracuseStep 17571077 = 3294577) B3294577
theorem B5487965 : Blo 1624511 5487965 := bstep (se 3 (by rfl) ⟨1028993, by rfl⟩ : syracuseStep 5487965 = 2057987) B2057987
theorem B3472769 : Blo 1624511 3472769 := bstep (se 2 (by rfl) ⟨1302288, by rfl⟩ : syracuseStep 3472769 = 2604577) B2604577
theorem B10419587 : Blo 1624511 10419587 := bstep (se 1 (by rfl) ⟨7814690, by rfl⟩ : syracuseStep 10419587 = 15629381) B15629381
theorem B5209537 : Blo 1624511 5209537 := bstep (se 2 (by rfl) ⟨1953576, by rfl⟩ : syracuseStep 5209537 = 3907153) B3907153
theorem B6946307 : Blo 1624511 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B2743895 : Blo 1624511 2743895 := bstep (se 1 (by rfl) ⟨2057921, by rfl⟩ : syracuseStep 2743895 = 4115843) B4115843
theorem B4628171 : Blo 1624511 4628171 := bstep (se 1 (by rfl) ⟨3471128, by rfl⟩ : syracuseStep 4628171 = 6942257) B6942257
theorem B2744023 : Blo 1624511 2744023 := bstep (se 1 (by rfl) ⟨2058017, by rfl⟩ : syracuseStep 2744023 = 4116035) B4116035
theorem B3473111 : Blo 1624511 3473111 := bstep (se 1 (by rfl) ⟨2604833, by rfl⟩ : syracuseStep 3473111 = 5209667) B5209667
theorem B8224577 : Blo 1624511 8224577 := bstep (se 2 (by rfl) ⟨3084216, by rfl⟩ : syracuseStep 8224577 = 6168433) B6168433
theorem B4112279 : Blo 1624511 4112279 := bstep (se 1 (by rfl) ⟨3084209, by rfl⟩ : syracuseStep 4112279 = 6168419) B6168419
theorem B4513729 : Blo 1624511 4513729 := bstep (se 2 (by rfl) ⟨1692648, by rfl⟩ : syracuseStep 4513729 = 3385297) B3385297
theorem B1736683 : Blo 1624511 1736683 := bstep (se 1 (by rfl) ⟨1302512, by rfl⟩ : syracuseStep 1736683 = 2605025) B2605025
theorem B9257003 : Blo 1624511 9257003 := bstep (se 1 (by rfl) ⟨6942752, by rfl⟩ : syracuseStep 9257003 = 13885505) B13885505
theorem B17580077 : Blo 1624511 17580077 := bstep (se 3 (by rfl) ⟨3296264, by rfl⟩ : syracuseStep 17580077 = 6592529) B6592529
theorem B4112471 : Blo 1624511 4112471 := bstep (se 1 (by rfl) ⟨3084353, by rfl⟩ : syracuseStep 4112471 = 6168707) B6168707
theorem B2744455 : Blo 1624511 2744455 := bstep (se 1 (by rfl) ⟨2058341, by rfl⟩ : syracuseStep 2744455 = 4116683) B4116683
theorem B4628627 : Blo 1624511 4628627 := bstep (se 1 (by rfl) ⟨3471470, by rfl⟩ : syracuseStep 4628627 = 6942941) B6942941
theorem B27779273 : Blo 1624511 27779273 := bstep (se 2 (by rfl) ⟨10417227, by rfl⟩ : syracuseStep 27779273 = 20834455) B20834455
theorem B7807385 : Blo 1624511 7807385 := bstep (se 2 (by rfl) ⟨2927769, by rfl⟩ : syracuseStep 7807385 = 5855539) B5855539
theorem B9388547 : Blo 1624511 9388547 := bstep (se 1 (by rfl) ⟨7041410, by rfl⟩ : syracuseStep 9388547 = 14082821) B14082821
theorem B15843869 : Blo 1624511 15843869 := bstep (se 3 (by rfl) ⟨2970725, by rfl⟩ : syracuseStep 15843869 = 5941451) B5941451
theorem B2056747 : Blo 1624511 2056747 := bstep (se 1 (by rfl) ⟨1542560, by rfl⟩ : syracuseStep 2056747 = 3085121) B3085121
theorem B5276279 : Blo 1624511 5276279 := bstep (se 1 (by rfl) ⟨3957209, by rfl⟩ : syracuseStep 5276279 = 7914419) B7914419
theorem B9388781 : Blo 1624511 9388781 := bstep (se 3 (by rfl) ⟨1760396, by rfl⟩ : syracuseStep 9388781 = 3520793) B3520793
theorem B39551759 : Blo 1624511 39551759 := bstep (se 1 (by rfl) ⟨29663819, by rfl⟩ : syracuseStep 39551759 = 59327639) B59327639
theorem B5489423 : Blo 1624511 5489423 := bstep (se 1 (by rfl) ⟨4117067, by rfl⟩ : syracuseStep 5489423 = 8234135) B8234135
theorem B1827643 : Blo 1624511 1827643 := bstep (se 1 (by rfl) ⟨1370732, by rfl⟩ : syracuseStep 1827643 = 2741465) B2741465
theorem B1647503 : Blo 1624511 1647503 := bstep (se 1 (by rfl) ⟨1235627, by rfl⟩ : syracuseStep 1647503 = 2471255) B2471255
theorem B5858423 : Blo 1624511 5858423 := bstep (se 1 (by rfl) ⟨4393817, by rfl⟩ : syracuseStep 5858423 = 8787635) B8787635
theorem B5022839 : Blo 1624511 5022839 := bstep (se 1 (by rfl) ⟨3767129, by rfl⟩ : syracuseStep 5022839 = 7534259) B7534259
theorem B4392089 : Blo 1624511 4392089 := bstep (se 2 (by rfl) ⟨1647033, by rfl⟩ : syracuseStep 4392089 = 3294067) B3294067
theorem B1828111 : Blo 1624511 1828111 := bstep (se 1 (by rfl) ⟨1371083, by rfl⟩ : syracuseStep 1828111 = 2742167) B2742167
theorem B2196779 : Blo 1624511 2196779 := bstep (se 1 (by rfl) ⟨1647584, by rfl⟩ : syracuseStep 2196779 = 3295169) B3295169
theorem B6940019 : Blo 1624511 6940019 := bstep (se 1 (by rfl) ⟨5205014, by rfl⟩ : syracuseStep 6940019 = 10410029) B10410029
theorem B12338567 : Blo 1624511 12338567 := bstep (se 1 (by rfl) ⟨9253925, by rfl⟩ : syracuseStep 12338567 = 18507851) B18507851
theorem B7054739 : Blo 1624511 7054739 := bstep (se 1 (by rfl) ⟨5291054, by rfl⟩ : syracuseStep 7054739 = 10582109) B10582109
theorem B9258461 : Blo 1624511 9258461 := bstep (se 3 (by rfl) ⟨1735961, by rfl⟩ : syracuseStep 9258461 = 3471923) B3471923
theorem B2057719 : Blo 1624511 2057719 := bstep (se 1 (by rfl) ⟨1543289, by rfl⟩ : syracuseStep 2057719 = 3086579) B3086579
theorem B6940171 : Blo 1624511 6940171 := bstep (se 1 (by rfl) ⟨5205128, by rfl⟩ : syracuseStep 6940171 = 10410257) B10410257
theorem B23447069 : Blo 1624511 23447069 := bstep (se 3 (by rfl) ⟨4396325, by rfl⟩ : syracuseStep 23447069 = 8792651) B8792651
theorem B35612237 : Blo 1624511 35612237 := bstep (se 3 (by rfl) ⟨6677294, by rfl⟩ : syracuseStep 35612237 = 13354589) B13354589
theorem B1828615 : Blo 1624511 1828615 := bstep (se 1 (by rfl) ⟨1371461, by rfl⟩ : syracuseStep 1828615 = 2742923) B2742923
theorem B2197255 : Blo 1624511 2197255 := bstep (se 1 (by rfl) ⟨1647941, by rfl⟩ : syracuseStep 2197255 = 3295883) B3295883
theorem B3655439 : Blo 1624511 3655439 := bstep (se 1 (by rfl) ⟨2741579, by rfl⟩ : syracuseStep 3655439 = 5483159) B5483159
theorem B3655457 : Blo 1624511 3655457 := bstep (se 2 (by rfl) ⟨1370796, by rfl⟩ : syracuseStep 3655457 = 2741593) B2741593
theorem B2058043 : Blo 1624511 2058043 := bstep (se 1 (by rfl) ⟨1543532, by rfl⟩ : syracuseStep 2058043 = 3087065) B3087065
theorem B1828795 : Blo 1624511 1828795 := bstep (se 1 (by rfl) ⟨1371596, by rfl⟩ : syracuseStep 1828795 = 2743193) B2743193
theorem B8226845 : Blo 1624511 8226845 := bstep (se 3 (by rfl) ⟨1542533, by rfl⟩ : syracuseStep 8226845 = 3085067) B3085067
theorem B4114547 : Blo 1624511 4114547 := bstep (se 1 (by rfl) ⟨3085910, by rfl⟩ : syracuseStep 4114547 = 6171821) B6171821
theorem B3655799 : Blo 1624511 3655799 := bstep (se 1 (by rfl) ⟨2741849, by rfl⟩ : syracuseStep 3655799 = 5483699) B5483699
theorem B16681133 : Blo 1624511 16681133 := bstep (se 3 (by rfl) ⟨3127712, by rfl⟩ : syracuseStep 16681133 = 6255425) B6255425
theorem B15616273 : Blo 1624511 15616273 := bstep (se 2 (by rfl) ⟨5856102, by rfl⟩ : syracuseStep 15616273 = 11712205) B11712205
theorem B3655979 : Blo 1624511 3655979 := bstep (se 1 (by rfl) ⟨2741984, by rfl⟩ : syracuseStep 3655979 = 5483969) B5483969
theorem B4630871 : Blo 1624511 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B1829263 : Blo 1624511 1829263 := bstep (se 1 (by rfl) ⟨1371947, by rfl⟩ : syracuseStep 1829263 = 2743895) B2743895
theorem B5859793 : Blo 1624511 5859793 := bstep (se 2 (by rfl) ⟨2197422, by rfl⟩ : syracuseStep 5859793 = 4394845) B4394845
theorem B8227331 : Blo 1624511 8227331 := bstep (se 1 (by rfl) ⟨6170498, by rfl⟩ : syracuseStep 8227331 = 12340997) B12340997
theorem B1624583 : Blo 1624511 1624583 := bstep (se 1 (by rfl) ⟨1218437, by rfl⟩ : syracuseStep 1624583 = 2436875) B2436875
theorem B8784395 : Blo 1624511 8784395 := bstep (se 1 (by rfl) ⟨6588296, by rfl⟩ : syracuseStep 8784395 = 13176593) B13176593
theorem B1624591 : Blo 1624511 1624591 := bstep (se 1 (by rfl) ⟨1218443, by rfl⟩ : syracuseStep 1624591 = 2436887) B2436887
theorem B5483051 : Blo 1624511 5483051 := bstep (se 1 (by rfl) ⟨4112288, by rfl⟩ : syracuseStep 5483051 = 8224577) B8224577
theorem B1624635 : Blo 1624511 1624635 := bstep (se 1 (by rfl) ⟨1218476, by rfl⟩ : syracuseStep 1624635 = 2436953) B2436953
theorem B18516599 : Blo 1624511 18516599 := bstep (se 1 (by rfl) ⟨13887449, by rfl⟩ : syracuseStep 18516599 = 27774899) B27774899
theorem B4115063 : Blo 1624511 4115063 := bstep (se 1 (by rfl) ⟨3086297, by rfl⟩ : syracuseStep 4115063 = 6172595) B6172595
theorem B1624711 : Blo 1624511 1624711 := bstep (se 1 (by rfl) ⟨1218533, by rfl⟩ : syracuseStep 1624711 = 2437067) B2437067
theorem B1624719 : Blo 1624511 1624719 := bstep (se 1 (by rfl) ⟨1218539, by rfl⟩ : syracuseStep 1624719 = 2437079) B2437079
theorem B3656339 : Blo 1624511 3656339 := bstep (se 1 (by rfl) ⟨2742254, by rfl⟩ : syracuseStep 3656339 = 5484509) B5484509
theorem B1624763 : Blo 1624511 1624763 := bstep (se 1 (by rfl) ⟨1218572, by rfl⟩ : syracuseStep 1624763 = 2437145) B2437145
theorem B3656393 : Blo 1624511 3656393 := bstep (se 2 (by rfl) ⟨1371147, by rfl⟩ : syracuseStep 3656393 = 2742295) B2742295
theorem B5860097 : Blo 1624511 5860097 := bstep (se 2 (by rfl) ⟨2197536, by rfl⟩ : syracuseStep 5860097 = 4395073) B4395073
theorem B1624839 : Blo 1624511 1624839 := bstep (se 1 (by rfl) ⟨1218629, by rfl⟩ : syracuseStep 1624839 = 2437259) B2437259
theorem B1624847 : Blo 1624511 1624847 := bstep (se 1 (by rfl) ⟨1218635, by rfl⟩ : syracuseStep 1624847 = 2437271) B2437271
theorem B1624891 : Blo 1624511 1624891 := bstep (se 1 (by rfl) ⟨1218668, by rfl⟩ : syracuseStep 1624891 = 2437337) B2437337
theorem B14076787 : Blo 1624511 14076787 := bstep (se 1 (by rfl) ⟨10557590, by rfl⟩ : syracuseStep 14076787 = 21115181) B21115181
theorem B14830451 : Blo 1624511 14830451 := bstep (se 1 (by rfl) ⟨11122838, by rfl⟩ : syracuseStep 14830451 = 22245677) B22245677
theorem B1624967 : Blo 1624511 1624967 := bstep (se 1 (by rfl) ⟨1218725, by rfl⟩ : syracuseStep 1624967 = 2437451) B2437451
theorem B1829767 : Blo 1624511 1829767 := bstep (se 1 (by rfl) ⟨1372325, by rfl⟩ : syracuseStep 1829767 = 2744651) B2744651
theorem B1624975 : Blo 1624511 1624975 := bstep (se 1 (by rfl) ⟨1218731, by rfl⟩ : syracuseStep 1624975 = 2437463) B2437463
theorem B1625019 : Blo 1624511 1625019 := bstep (se 1 (by rfl) ⟨1218764, by rfl⟩ : syracuseStep 1625019 = 2437529) B2437529
theorem B1625095 : Blo 1624511 1625095 := bstep (se 1 (by rfl) ⟨1218821, by rfl⟩ : syracuseStep 1625095 = 2437643) B2437643
theorem B7916555 : Blo 1624511 7916555 := bstep (se 1 (by rfl) ⟨5937416, by rfl⟩ : syracuseStep 7916555 = 11874833) B11874833
theorem B2255887 : Blo 1624511 2255887 := bstep (se 1 (by rfl) ⟨1691915, by rfl⟩ : syracuseStep 2255887 = 3383831) B3383831
theorem B1625103 : Blo 1624511 1625103 := bstep (se 1 (by rfl) ⟨1218827, by rfl⟩ : syracuseStep 1625103 = 2437655) B2437655
theorem B1625147 : Blo 1624511 1625147 := bstep (se 1 (by rfl) ⟨1218860, by rfl⟩ : syracuseStep 1625147 = 2437721) B2437721
theorem B5205053 : Blo 1624511 5205053 := bstep (se 3 (by rfl) ⟨975947, by rfl⟩ : syracuseStep 5205053 = 1951895) B1951895
theorem B1625223 : Blo 1624511 1625223 := bstep (se 1 (by rfl) ⟨1218917, by rfl⟩ : syracuseStep 1625223 = 2437835) B2437835
theorem B1625231 : Blo 1624511 1625231 := bstep (se 1 (by rfl) ⟨1218923, by rfl⟩ : syracuseStep 1625231 = 2437847) B2437847
theorem B1625275 : Blo 1624511 1625275 := bstep (se 1 (by rfl) ⟨1218956, by rfl⟩ : syracuseStep 1625275 = 2437913) B2437913
theorem B6941933 : Blo 1624511 6941933 := bstep (se 3 (by rfl) ⟨1301612, by rfl⟩ : syracuseStep 6941933 = 2603225) B2603225
theorem B1625351 : Blo 1624511 1625351 := bstep (se 1 (by rfl) ⟨1219013, by rfl⟩ : syracuseStep 1625351 = 2438027) B2438027
theorem B1625359 : Blo 1624511 1625359 := bstep (se 1 (by rfl) ⟨1219019, by rfl⟩ : syracuseStep 1625359 = 2438039) B2438039
theorem B2927915 : Blo 1624511 2927915 := bstep (se 1 (by rfl) ⟨2195936, by rfl⟩ : syracuseStep 2927915 = 4391873) B4391873
theorem B1625403 : Blo 1624511 1625403 := bstep (se 1 (by rfl) ⟨1219052, by rfl⟩ : syracuseStep 1625403 = 2438105) B2438105
theorem B27766151 : Blo 1624511 27766151 := bstep (se 1 (by rfl) ⟨20824613, by rfl⟩ : syracuseStep 27766151 = 41649227) B41649227
theorem B3657095 : Blo 1624511 3657095 := bstep (se 1 (by rfl) ⟨2742821, by rfl⟩ : syracuseStep 3657095 = 5485643) B5485643
theorem B1625479 : Blo 1624511 1625479 := bstep (se 1 (by rfl) ⟨1219109, by rfl⟩ : syracuseStep 1625479 = 2438219) B2438219
theorem B1625487 : Blo 1624511 1625487 := bstep (se 1 (by rfl) ⟨1219115, by rfl⟩ : syracuseStep 1625487 = 2438231) B2438231
theorem B1625531 : Blo 1624511 1625531 := bstep (se 1 (by rfl) ⟨1219148, by rfl⟩ : syracuseStep 1625531 = 2438297) B2438297
theorem B1625607 : Blo 1624511 1625607 := bstep (se 1 (by rfl) ⟨1219205, by rfl⟩ : syracuseStep 1625607 = 2438411) B2438411
theorem B1625615 : Blo 1624511 1625615 := bstep (se 1 (by rfl) ⟨1219211, by rfl⟩ : syracuseStep 1625615 = 2438423) B2438423
theorem B3517985 : Blo 1624511 3517985 := bstep (se 2 (by rfl) ⟨1319244, by rfl⟩ : syracuseStep 3517985 = 2638489) B2638489
theorem B3657275 : Blo 1624511 3657275 := bstep (se 1 (by rfl) ⟨2742956, by rfl⟩ : syracuseStep 3657275 = 5485913) B5485913
theorem B1625659 : Blo 1624511 1625659 := bstep (se 1 (by rfl) ⟨1219244, by rfl⟩ : syracuseStep 1625659 = 2438489) B2438489
theorem B4116055 : Blo 1624511 4116055 := bstep (se 1 (by rfl) ⟨3087041, by rfl⟩ : syracuseStep 4116055 = 6174083) B6174083
theorem B1625735 : Blo 1624511 1625735 := bstep (se 1 (by rfl) ⟨1219301, by rfl⟩ : syracuseStep 1625735 = 2438603) B2438603
theorem B1625743 : Blo 1624511 1625743 := bstep (se 1 (by rfl) ⟨1219307, by rfl⟩ : syracuseStep 1625743 = 2438615) B2438615
theorem B2436779 : Blo 1624511 2436779 := bstep (se 1 (by rfl) ⟨1827584, by rfl⟩ : syracuseStep 2436779 = 3655169) B3655169
theorem B3657401 : Blo 1624511 3657401 := bstep (se 2 (by rfl) ⟨1371525, by rfl⟩ : syracuseStep 3657401 = 2743051) B2743051
theorem B1625787 : Blo 1624511 1625787 := bstep (se 1 (by rfl) ⟨1219340, by rfl⟩ : syracuseStep 1625787 = 2438681) B2438681
theorem B2436809 : Blo 1624511 2436809 := bstep (se 2 (by rfl) ⟨913803, by rfl⟩ : syracuseStep 2436809 = 1827607) B1827607
theorem B1625863 : Blo 1624511 1625863 := bstep (se 1 (by rfl) ⟨1219397, by rfl⟩ : syracuseStep 1625863 = 2438795) B2438795
theorem B1625871 : Blo 1624511 1625871 := bstep (se 1 (by rfl) ⟨1219403, by rfl⟩ : syracuseStep 1625871 = 2438807) B2438807
theorem B3084065 : Blo 1624511 3084065 := bstep (se 2 (by rfl) ⟨1156524, by rfl⟩ : syracuseStep 3084065 = 2313049) B2313049
theorem B9260851 : Blo 1624511 9260851 := bstep (se 1 (by rfl) ⟨6945638, by rfl⟩ : syracuseStep 9260851 = 13891277) B13891277
theorem B2436923 : Blo 1624511 2436923 := bstep (se 1 (by rfl) ⟨1827692, by rfl⟩ : syracuseStep 2436923 = 3655385) B3655385
theorem B5484347 : Blo 1624511 5484347 := bstep (se 1 (by rfl) ⟨4113260, by rfl⟩ : syracuseStep 5484347 = 8226521) B8226521
theorem B1625915 : Blo 1624511 1625915 := bstep (se 1 (by rfl) ⟨1219436, by rfl⟩ : syracuseStep 1625915 = 2438873) B2438873
theorem B3903347 : Blo 1624511 3903347 := bstep (se 1 (by rfl) ⟨2927510, by rfl⟩ : syracuseStep 3903347 = 5855021) B5855021
theorem B2436983 : Blo 1624511 2436983 := bstep (se 1 (by rfl) ⟨1827737, by rfl⟩ : syracuseStep 2436983 = 3655475) B3655475
theorem B1625991 : Blo 1624511 1625991 := bstep (se 1 (by rfl) ⟨1219493, by rfl⟩ : syracuseStep 1625991 = 2438987) B2438987
theorem B4116359 : Blo 1624511 4116359 := bstep (se 1 (by rfl) ⟨3087269, by rfl⟩ : syracuseStep 4116359 = 6174539) B6174539
theorem B2437007 : Blo 1624511 2437007 := bstep (se 1 (by rfl) ⟨1827755, by rfl⟩ : syracuseStep 2437007 = 3655511) B3655511
theorem B1625999 : Blo 1624511 1625999 := bstep (se 1 (by rfl) ⟨1219499, by rfl⟩ : syracuseStep 1625999 = 2438999) B2438999
theorem B6942617 : Blo 1624511 6942617 := bstep (se 2 (by rfl) ⟨2603481, by rfl⟩ : syracuseStep 6942617 = 5206963) B5206963
theorem B1978283 : Blo 1624511 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B2437049 : Blo 1624511 2437049 := bstep (se 2 (by rfl) ⟨913893, by rfl⟩ : syracuseStep 2437049 = 1827787) B1827787
theorem B1626043 : Blo 1624511 1626043 := bstep (se 1 (by rfl) ⟨1219532, by rfl⟩ : syracuseStep 1626043 = 2439065) B2439065
theorem B6172625 : Blo 1624511 6172625 := bstep (se 2 (by rfl) ⟨2314734, by rfl⟩ : syracuseStep 6172625 = 4629469) B4629469
theorem B2437127 : Blo 1624511 2437127 := bstep (se 1 (by rfl) ⟨1827845, by rfl⟩ : syracuseStep 2437127 = 3655691) B3655691
theorem B1626119 : Blo 1624511 1626119 := bstep (se 1 (by rfl) ⟨1219589, by rfl⟩ : syracuseStep 1626119 = 2439179) B2439179
theorem B4116491 : Blo 1624511 4116491 := bstep (se 1 (by rfl) ⟨3087368, by rfl⟩ : syracuseStep 4116491 = 6174737) B6174737
theorem B3657743 : Blo 1624511 3657743 := bstep (se 1 (by rfl) ⟨2743307, by rfl⟩ : syracuseStep 3657743 = 5486615) B5486615
theorem B1626127 : Blo 1624511 1626127 := bstep (se 1 (by rfl) ⟨1219595, by rfl⟩ : syracuseStep 1626127 = 2439191) B2439191
theorem B3657761 : Blo 1624511 3657761 := bstep (se 2 (by rfl) ⟨1371660, by rfl⟩ : syracuseStep 3657761 = 2743321) B2743321
theorem B3084331 : Blo 1624511 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B2437163 : Blo 1624511 2437163 := bstep (se 1 (by rfl) ⟨1827872, by rfl⟩ : syracuseStep 2437163 = 3655745) B3655745
theorem B1626171 : Blo 1624511 1626171 := bstep (se 1 (by rfl) ⟨1219628, by rfl⟩ : syracuseStep 1626171 = 2439257) B2439257
theorem B2437193 : Blo 1624511 2437193 := bstep (se 2 (by rfl) ⟨913947, by rfl⟩ : syracuseStep 2437193 = 1827895) B1827895
theorem B5206103 : Blo 1624511 5206103 := bstep (se 1 (by rfl) ⟨3904577, by rfl⟩ : syracuseStep 5206103 = 7809155) B7809155
theorem B8228951 : Blo 1624511 8228951 := bstep (se 1 (by rfl) ⟨6171713, by rfl⟩ : syracuseStep 8228951 = 12343427) B12343427
theorem B1626247 : Blo 1624511 1626247 := bstep (se 1 (by rfl) ⟨1219685, by rfl⟩ : syracuseStep 1626247 = 2439371) B2439371
theorem B1626255 : Blo 1624511 1626255 := bstep (se 1 (by rfl) ⟨1219691, by rfl⟩ : syracuseStep 1626255 = 2439383) B2439383
theorem B2437307 : Blo 1624511 2437307 := bstep (se 1 (by rfl) ⟨1827980, by rfl⟩ : syracuseStep 2437307 = 3655961) B3655961
theorem B1626299 : Blo 1624511 1626299 := bstep (se 1 (by rfl) ⟨1219724, by rfl⟩ : syracuseStep 1626299 = 2439449) B2439449
theorem B2437367 : Blo 1624511 2437367 := bstep (se 1 (by rfl) ⟨1828025, by rfl⟩ : syracuseStep 2437367 = 3656051) B3656051
theorem B1626375 : Blo 1624511 1626375 := bstep (se 1 (by rfl) ⟨1219781, by rfl⟩ : syracuseStep 1626375 = 2439563) B2439563
theorem B2437391 : Blo 1624511 2437391 := bstep (se 1 (by rfl) ⟨1828043, by rfl⟩ : syracuseStep 2437391 = 3656087) B3656087
theorem B1626383 : Blo 1624511 1626383 := bstep (se 1 (by rfl) ⟨1219787, by rfl⟩ : syracuseStep 1626383 = 2439575) B2439575
theorem B5484833 : Blo 1624511 5484833 := bstep (se 2 (by rfl) ⟨2056812, by rfl⟩ : syracuseStep 5484833 = 4113625) B4113625
theorem B2437433 : Blo 1624511 2437433 := bstep (se 2 (by rfl) ⟨914037, by rfl⟩ : syracuseStep 2437433 = 1828075) B1828075
theorem B1626427 : Blo 1624511 1626427 := bstep (se 1 (by rfl) ⟨1219820, by rfl⟩ : syracuseStep 1626427 = 2439641) B2439641
theorem B4944215 : Blo 1624511 4944215 := bstep (se 1 (by rfl) ⟨3708161, by rfl⟩ : syracuseStep 4944215 = 7416323) B7416323
theorem B3658103 : Blo 1624511 3658103 := bstep (se 1 (by rfl) ⟨2743577, by rfl⟩ : syracuseStep 3658103 = 5487155) B5487155
theorem B2437511 : Blo 1624511 2437511 := bstep (se 1 (by rfl) ⟨1828133, by rfl⟩ : syracuseStep 2437511 = 3656267) B3656267
theorem B6590855 : Blo 1624511 6590855 := bstep (se 1 (by rfl) ⟨4943141, by rfl⟩ : syracuseStep 6590855 = 9886283) B9886283
theorem B1626503 : Blo 1624511 1626503 := bstep (se 1 (by rfl) ⟨1219877, by rfl⟩ : syracuseStep 1626503 = 2439755) B2439755
theorem B1626511 : Blo 1624511 1626511 := bstep (se 1 (by rfl) ⟨1219883, by rfl⟩ : syracuseStep 1626511 = 2439767) B2439767
theorem B6173081 : Blo 1624511 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B2437547 : Blo 1624511 2437547 := bstep (se 1 (by rfl) ⟨1828160, by rfl⟩ : syracuseStep 2437547 = 3656321) B3656321
theorem B2437577 : Blo 1624511 2437577 := bstep (se 2 (by rfl) ⟨914091, by rfl⟩ : syracuseStep 2437577 = 1828183) B1828183
theorem B40104409 : Blo 1624511 40104409 := bstep (se 2 (by rfl) ⟨15039153, by rfl⟩ : syracuseStep 40104409 = 30078307) B30078307
theorem B9253379 : Blo 1624511 9253379 := bstep (se 1 (by rfl) ⟨6940034, by rfl⟩ : syracuseStep 9253379 = 13880069) B13880069
theorem B4117007 : Blo 1624511 4117007 := bstep (se 1 (by rfl) ⟨3087755, by rfl⟩ : syracuseStep 4117007 = 6175511) B6175511
theorem B3658283 : Blo 1624511 3658283 := bstep (se 1 (by rfl) ⟨2743712, by rfl⟩ : syracuseStep 3658283 = 5487425) B5487425
theorem B2437691 : Blo 1624511 2437691 := bstep (se 1 (by rfl) ⟨1828268, by rfl⟩ : syracuseStep 2437691 = 3656537) B3656537
theorem B8229437 : Blo 1624511 8229437 := bstep (se 3 (by rfl) ⟨1543019, by rfl⟩ : syracuseStep 8229437 = 3086039) B3086039
theorem B2437751 : Blo 1624511 2437751 := bstep (se 1 (by rfl) ⟨1828313, by rfl⟩ : syracuseStep 2437751 = 3656627) B3656627
theorem B2437775 : Blo 1624511 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B2437817 : Blo 1624511 2437817 := bstep (se 2 (by rfl) ⟨914181, by rfl⟩ : syracuseStep 2437817 = 1828363) B1828363
theorem B66720449 : Blo 1624511 66720449 := bstep (se 2 (by rfl) ⟨25020168, by rfl⟩ : syracuseStep 66720449 = 50040337) B50040337
theorem B7041773 : Blo 1624511 7041773 := bstep (se 3 (by rfl) ⟨1320332, by rfl⟩ : syracuseStep 7041773 = 2640665) B2640665
theorem B2437895 : Blo 1624511 2437895 := bstep (se 1 (by rfl) ⟨1828421, by rfl⟩ : syracuseStep 2437895 = 3656843) B3656843
theorem B3904271 : Blo 1624511 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B2437931 : Blo 1624511 2437931 := bstep (se 1 (by rfl) ⟨1828448, by rfl⟩ : syracuseStep 2437931 = 3656897) B3656897
theorem B2437961 : Blo 1624511 2437961 := bstep (se 2 (by rfl) ⟨914235, by rfl⟩ : syracuseStep 2437961 = 1828471) B1828471
theorem B5485427 : Blo 1624511 5485427 := bstep (se 1 (by rfl) ⟨4114070, by rfl⟩ : syracuseStep 5485427 = 8228141) B8228141
theorem B3470215 : Blo 1624511 3470215 := bstep (se 1 (by rfl) ⟨2602661, by rfl⟩ : syracuseStep 3470215 = 5205323) B5205323
theorem B3658643 : Blo 1624511 3658643 := bstep (se 1 (by rfl) ⟨2743982, by rfl⟩ : syracuseStep 3658643 = 5487965) B5487965
theorem B2315179 : Blo 1624511 2315179 := bstep (se 1 (by rfl) ⟨1736384, by rfl⟩ : syracuseStep 2315179 = 3472769) B3472769
theorem B2438075 : Blo 1624511 2438075 := bstep (se 1 (by rfl) ⟨1828556, by rfl⟩ : syracuseStep 2438075 = 3657113) B3657113
theorem B3658697 : Blo 1624511 3658697 := bstep (se 2 (by rfl) ⟨1372011, by rfl⟩ : syracuseStep 3658697 = 2744023) B2744023
theorem B9253835 : Blo 1624511 9253835 := bstep (se 1 (by rfl) ⟨6940376, by rfl⟩ : syracuseStep 9253835 = 13880753) B13880753
theorem B2438135 : Blo 1624511 2438135 := bstep (se 1 (by rfl) ⟨1828601, by rfl⟩ : syracuseStep 2438135 = 3657203) B3657203
theorem B2438159 : Blo 1624511 2438159 := bstep (se 1 (by rfl) ⟨1828619, by rfl⟩ : syracuseStep 2438159 = 3657239) B3657239
theorem B2438201 : Blo 1624511 2438201 := bstep (se 2 (by rfl) ⟨914325, by rfl⟩ : syracuseStep 2438201 = 1828651) B1828651
theorem B3085447 : Blo 1624511 3085447 := bstep (se 1 (by rfl) ⟨2314085, by rfl⟩ : syracuseStep 3085447 = 4628171) B4628171
theorem B2438279 : Blo 1624511 2438279 := bstep (se 1 (by rfl) ⟨1828709, by rfl⟩ : syracuseStep 2438279 = 3657419) B3657419
theorem B2315407 : Blo 1624511 2315407 := bstep (se 1 (by rfl) ⟨1736555, by rfl⟩ : syracuseStep 2315407 = 3473111) B3473111
theorem B2438315 : Blo 1624511 2438315 := bstep (se 1 (by rfl) ⟨1828736, by rfl⟩ : syracuseStep 2438315 = 3657473) B3657473
theorem B2438345 : Blo 1624511 2438345 := bstep (se 2 (by rfl) ⟨914379, by rfl⟩ : syracuseStep 2438345 = 1828759) B1828759
theorem B9262309 : Blo 1624511 9262309 := bstep (se 4 (by rfl) ⟨868341, by rfl⟩ : syracuseStep 9262309 = 1736683) B1736683
theorem B6018305 : Blo 1624511 6018305 := bstep (se 2 (by rfl) ⟨2256864, by rfl⟩ : syracuseStep 6018305 = 4513729) B4513729
theorem B2741519 : Blo 1624511 2741519 := bstep (se 1 (by rfl) ⟨2056139, by rfl⟩ : syracuseStep 2741519 = 4112279) B4112279
theorem B2438459 : Blo 1624511 2438459 := bstep (se 1 (by rfl) ⟨1828844, by rfl⟩ : syracuseStep 2438459 = 3657689) B3657689
theorem B4396349 : Blo 1624511 4396349 := bstep (se 3 (by rfl) ⟨824315, by rfl⟩ : syracuseStep 4396349 = 1648631) B1648631
theorem B2438519 : Blo 1624511 2438519 := bstep (se 1 (by rfl) ⟨1828889, by rfl⟩ : syracuseStep 2438519 = 3657779) B3657779
theorem B15619463 : Blo 1624511 15619463 := bstep (se 1 (by rfl) ⟨11714597, by rfl⟩ : syracuseStep 15619463 = 23429195) B23429195
theorem B2438543 : Blo 1624511 2438543 := bstep (se 1 (by rfl) ⟨1828907, by rfl⟩ : syracuseStep 2438543 = 3657815) B3657815
theorem B2438585 : Blo 1624511 2438585 := bstep (se 2 (by rfl) ⟨914469, by rfl⟩ : syracuseStep 2438585 = 1828939) B1828939
theorem B2438663 : Blo 1624511 2438663 := bstep (se 1 (by rfl) ⟨1828997, by rfl⟩ : syracuseStep 2438663 = 3657995) B3657995
theorem B2438699 : Blo 1624511 2438699 := bstep (se 1 (by rfl) ⟨1829024, by rfl⟩ : syracuseStep 2438699 = 3658049) B3658049
theorem B6174251 : Blo 1624511 6174251 := bstep (se 1 (by rfl) ⟨4630688, by rfl⟩ : syracuseStep 6174251 = 9261377) B9261377
theorem B2438729 : Blo 1624511 2438729 := bstep (se 2 (by rfl) ⟨914523, by rfl⟩ : syracuseStep 2438729 = 1829047) B1829047
theorem B9254519 : Blo 1624511 9254519 := bstep (se 1 (by rfl) ⟨6940889, by rfl⟩ : syracuseStep 9254519 = 13881779) B13881779
theorem B3659399 : Blo 1624511 3659399 := bstep (se 1 (by rfl) ⟨2744549, by rfl⟩ : syracuseStep 3659399 = 5489099) B5489099
theorem B3086009 : Blo 1624511 3086009 := bstep (se 2 (by rfl) ⟨1157253, by rfl⟩ : syracuseStep 3086009 = 2314507) B2314507
theorem B2438843 : Blo 1624511 2438843 := bstep (se 1 (by rfl) ⟨1829132, by rfl⟩ : syracuseStep 2438843 = 3658265) B3658265
theorem B7812845 : Blo 1624511 7812845 := bstep (se 3 (by rfl) ⟨1464908, by rfl⟩ : syracuseStep 7812845 = 2929817) B2929817
theorem B2438903 : Blo 1624511 2438903 := bstep (se 1 (by rfl) ⟨1829177, by rfl⟩ : syracuseStep 2438903 = 3658355) B3658355
theorem B2438927 : Blo 1624511 2438927 := bstep (se 1 (by rfl) ⟨1829195, by rfl⟩ : syracuseStep 2438927 = 3658391) B3658391
theorem B6944545 : Blo 1624511 6944545 := bstep (se 2 (by rfl) ⟨2604204, by rfl⟩ : syracuseStep 6944545 = 5208409) B5208409
theorem B2742059 : Blo 1624511 2742059 := bstep (se 1 (by rfl) ⟨2056544, by rfl⟩ : syracuseStep 2742059 = 4113089) B4113089
theorem B40089389 : Blo 1624511 40089389 := bstep (se 3 (by rfl) ⟨7516760, by rfl⟩ : syracuseStep 40089389 = 15033521) B15033521
theorem B2438969 : Blo 1624511 2438969 := bstep (se 2 (by rfl) ⟨914613, by rfl⟩ : syracuseStep 2438969 = 1829227) B1829227
theorem B3659579 : Blo 1624511 3659579 := bstep (se 1 (by rfl) ⟨2744684, by rfl⟩ : syracuseStep 3659579 = 5489369) B5489369
theorem B11720537 : Blo 1624511 11720537 := bstep (se 2 (by rfl) ⟨4395201, by rfl⟩ : syracuseStep 11720537 = 8790403) B8790403
theorem B2439047 : Blo 1624511 2439047 := bstep (se 1 (by rfl) ⟨1829285, by rfl⟩ : syracuseStep 2439047 = 3658571) B3658571
theorem B2439083 : Blo 1624511 2439083 := bstep (se 1 (by rfl) ⟨1829312, by rfl⟩ : syracuseStep 2439083 = 3658625) B3658625
theorem B2602937 : Blo 1624511 2602937 := bstep (se 2 (by rfl) ⟨976101, by rfl⟩ : syracuseStep 2602937 = 1952203) B1952203
theorem B2439113 : Blo 1624511 2439113 := bstep (se 2 (by rfl) ⟨914667, by rfl⟩ : syracuseStep 2439113 = 1829335) B1829335
theorem B3471419 : Blo 1624511 3471419 := bstep (se 1 (by rfl) ⟨2603564, by rfl⟩ : syracuseStep 3471419 = 5207129) B5207129
theorem B4454459 : Blo 1624511 4454459 := bstep (se 1 (by rfl) ⟨3340844, by rfl⟩ : syracuseStep 4454459 = 6681689) B6681689
theorem B2439227 : Blo 1624511 2439227 := bstep (se 1 (by rfl) ⟨1829420, by rfl⟩ : syracuseStep 2439227 = 3658841) B3658841
theorem B2439287 : Blo 1624511 2439287 := bstep (se 1 (by rfl) ⟨1829465, by rfl⟩ : syracuseStep 2439287 = 3658931) B3658931
theorem B2439311 : Blo 1624511 2439311 := bstep (se 1 (by rfl) ⟨1829483, by rfl⟩ : syracuseStep 2439311 = 3658967) B3658967
theorem B2742457 : Blo 1624511 2742457 := bstep (se 2 (by rfl) ⟨1028421, by rfl⟩ : syracuseStep 2742457 = 2056843) B2056843
theorem B2439353 : Blo 1624511 2439353 := bstep (se 2 (by rfl) ⟨914757, by rfl⟩ : syracuseStep 2439353 = 1829515) B1829515
theorem B2439431 : Blo 1624511 2439431 := bstep (se 1 (by rfl) ⟨1829573, by rfl⟩ : syracuseStep 2439431 = 3659147) B3659147
theorem B2439467 : Blo 1624511 2439467 := bstep (se 1 (by rfl) ⟨1829600, by rfl⟩ : syracuseStep 2439467 = 3659201) B3659201
theorem B8231219 : Blo 1624511 8231219 := bstep (se 1 (by rfl) ⟨6173414, by rfl⟩ : syracuseStep 8231219 = 12346829) B12346829
theorem B2439497 : Blo 1624511 2439497 := bstep (se 2 (by rfl) ⟨914811, by rfl⟩ : syracuseStep 2439497 = 1829623) B1829623
theorem B3709319 : Blo 1624511 3709319 := bstep (se 1 (by rfl) ⟨2781989, by rfl⟩ : syracuseStep 3709319 = 5563979) B5563979
theorem B2603449 : Blo 1624511 2603449 := bstep (se 2 (by rfl) ⟨976293, by rfl⟩ : syracuseStep 2603449 = 1952587) B1952587
theorem B2439611 : Blo 1624511 2439611 := bstep (se 1 (by rfl) ⟨1829708, by rfl⟩ : syracuseStep 2439611 = 3659417) B3659417
theorem B2439671 : Blo 1624511 2439671 := bstep (se 1 (by rfl) ⟨1829753, by rfl⟩ : syracuseStep 2439671 = 3659507) B3659507
theorem B2439695 : Blo 1624511 2439695 := bstep (se 1 (by rfl) ⟨1829771, by rfl⟩ : syracuseStep 2439695 = 3659543) B3659543
theorem B2439737 : Blo 1624511 2439737 := bstep (se 2 (by rfl) ⟨914901, by rfl⟩ : syracuseStep 2439737 = 1829803) B1829803
theorem B3471931 : Blo 1624511 3471931 := bstep (se 1 (by rfl) ⟨2603948, by rfl⟩ : syracuseStep 3471931 = 5207897) B5207897
theorem B8231543 : Blo 1624511 8231543 := bstep (se 1 (by rfl) ⟨6173657, by rfl⟩ : syracuseStep 8231543 = 12347315) B12347315
theorem B30489281 : Blo 1624511 30489281 := bstep (se 2 (by rfl) ⟨11433480, by rfl⟩ : syracuseStep 30489281 = 22866961) B22866961
theorem B4627145 : Blo 1624511 4627145 := bstep (se 2 (by rfl) ⟨1735179, by rfl⟩ : syracuseStep 4627145 = 3470359) B3470359
theorem B9378575 : Blo 1624511 9378575 := bstep (se 1 (by rfl) ⟨7033931, by rfl⟩ : syracuseStep 9378575 = 14067863) B14067863
theorem B71236367 : Blo 1624511 71236367 := bstep (se 1 (by rfl) ⟨53427275, by rfl⟩ : syracuseStep 71236367 = 106854551) B106854551
theorem B3087163 : Blo 1624511 3087163 := bstep (se 1 (by rfl) ⟨2315372, by rfl⟩ : syracuseStep 3087163 = 4630745) B4630745
theorem B2743159 : Blo 1624511 2743159 := bstep (se 1 (by rfl) ⟨2057369, by rfl⟩ : syracuseStep 2743159 = 4114739) B4114739
theorem B2743355 : Blo 1624511 2743355 := bstep (se 1 (by rfl) ⟨2057516, by rfl⟩ : syracuseStep 2743355 = 4115033) B4115033
theorem B2604167 : Blo 1624511 2604167 := bstep (se 1 (by rfl) ⟨1953125, by rfl⟩ : syracuseStep 2604167 = 3906251) B3906251
theorem B6946049 : Blo 1624511 6946049 := bstep (se 2 (by rfl) ⟨2604768, by rfl⟩ : syracuseStep 6946049 = 5209537) B5209537
theorem B3087649 : Blo 1624511 3087649 := bstep (se 2 (by rfl) ⟨1157868, by rfl⟩ : syracuseStep 3087649 = 2315737) B2315737
theorem B5488019 : Blo 1624511 5488019 := bstep (se 1 (by rfl) ⟨4116014, by rfl⟩ : syracuseStep 5488019 = 8232029) B8232029
theorem B2743753 : Blo 1624511 2743753 := bstep (se 2 (by rfl) ⟨1028907, by rfl⟩ : syracuseStep 2743753 = 2057815) B2057815
theorem B21102083 : Blo 1624511 21102083 := bstep (se 1 (by rfl) ⟨15826562, by rfl⟩ : syracuseStep 21102083 = 31653125) B31653125
theorem B11714051 : Blo 1624511 11714051 := bstep (se 1 (by rfl) ⟨8785538, by rfl⟩ : syracuseStep 11714051 = 17571077) B17571077
theorem B9256477 : Blo 1624511 9256477 := bstep (se 3 (by rfl) ⟨1735589, by rfl⟩ : syracuseStep 9256477 = 3471179) B3471179
theorem B31686173 : Blo 1624511 31686173 := bstep (se 3 (by rfl) ⟨5941157, by rfl⟩ : syracuseStep 31686173 = 11882315) B11882315
theorem B4628011 : Blo 1624511 4628011 := bstep (se 1 (by rfl) ⟨3471008, by rfl⟩ : syracuseStep 4628011 = 6942017) B6942017
theorem B8232515 : Blo 1624511 8232515 := bstep (se 1 (by rfl) ⟨6174386, by rfl⟩ : syracuseStep 8232515 = 12348773) B12348773
theorem B6946391 : Blo 1624511 6946391 := bstep (se 1 (by rfl) ⟨5209793, by rfl⟩ : syracuseStep 6946391 = 10419587) B10419587
theorem B5857039 : Blo 1624511 5857039 := bstep (se 1 (by rfl) ⟨4392779, by rfl⟩ : syracuseStep 5857039 = 8785559) B8785559
theorem B15621923 : Blo 1624511 15621923 := bstep (se 1 (by rfl) ⟨11716442, by rfl⟩ : syracuseStep 15621923 = 23432885) B23432885
theorem B4628285 : Blo 1624511 4628285 := bstep (se 3 (by rfl) ⟨867803, by rfl⟩ : syracuseStep 4628285 = 1735607) B1735607
theorem B8232839 : Blo 1624511 8232839 := bstep (se 1 (by rfl) ⟨6174629, by rfl⟩ : syracuseStep 8232839 = 12349259) B12349259
theorem B4112329 : Blo 1624511 4112329 := bstep (se 2 (by rfl) ⟨1542123, by rfl⟩ : syracuseStep 4112329 = 3084247) B3084247
theorem B2744327 : Blo 1624511 2744327 := bstep (se 1 (by rfl) ⟨2058245, by rfl⟩ : syracuseStep 2744327 = 4116491) B4116491
theorem B21110813 : Blo 1624511 21110813 := bstep (se 3 (by rfl) ⟨3958277, by rfl⟩ : syracuseStep 21110813 = 7916555) B7916555
theorem B4112441 : Blo 1624511 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B6168919 : Blo 1624511 6168919 := bstep (se 1 (by rfl) ⟨4626689, by rfl⟩ : syracuseStep 6168919 = 9253379) B9253379
theorem B6259031 : Blo 1624511 6259031 := bstep (se 1 (by rfl) ⟨4694273, by rfl⟩ : syracuseStep 6259031 = 9388547) B9388547
theorem B2744671 : Blo 1624511 2744671 := bstep (se 1 (by rfl) ⟨2058503, by rfl⟩ : syracuseStep 2744671 = 4117007) B4117007
theorem B6259187 : Blo 1624511 6259187 := bstep (se 1 (by rfl) ⟨4694390, by rfl⟩ : syracuseStep 6259187 = 9388781) B9388781
theorem B6169223 : Blo 1624511 6169223 := bstep (se 1 (by rfl) ⟨4626917, by rfl⟩ : syracuseStep 6169223 = 9253835) B9253835
theorem B4629241 : Blo 1624511 4629241 := bstep (se 2 (by rfl) ⟨1735965, by rfl⟩ : syracuseStep 4629241 = 3471931) B3471931
theorem B5858077 : Blo 1624511 5858077 := bstep (se 3 (by rfl) ⟨1098389, by rfl⟩ : syracuseStep 5858077 = 2196779) B2196779
theorem B1827679 : Blo 1624511 1827679 := bstep (se 1 (by rfl) ⟨1370759, by rfl⟩ : syracuseStep 1827679 = 2741519) B2741519
theorem B8225711 : Blo 1624511 8225711 := bstep (se 1 (by rfl) ⟨6169283, by rfl⟩ : syracuseStep 8225711 = 12338567) B12338567
theorem B10412975 : Blo 1624511 10412975 := bstep (se 1 (by rfl) ⟨7809731, by rfl⟩ : syracuseStep 10412975 = 15619463) B15619463
theorem B4703159 : Blo 1624511 4703159 := bstep (se 1 (by rfl) ⟨3527369, by rfl⟩ : syracuseStep 4703159 = 7054739) B7054739
theorem B15631379 : Blo 1624511 15631379 := bstep (se 1 (by rfl) ⟨11723534, by rfl⟩ : syracuseStep 15631379 = 23447069) B23447069
theorem B6169679 : Blo 1624511 6169679 := bstep (se 1 (by rfl) ⟨4627259, by rfl⟩ : syracuseStep 6169679 = 9254519) B9254519
theorem B2057339 : Blo 1624511 2057339 := bstep (se 1 (by rfl) ⟨1543004, by rfl⟩ : syracuseStep 2057339 = 3086009) B3086009
theorem B18769049 : Blo 1624511 18769049 := bstep (se 2 (by rfl) ⟨7038393, by rfl⟩ : syracuseStep 18769049 = 14076787) B14076787
theorem B1828039 : Blo 1624511 1828039 := bstep (se 1 (by rfl) ⟨1371029, by rfl⟩ : syracuseStep 1828039 = 2742059) B2742059
theorem B3007849 : Blo 1624511 3007849 := bstep (se 2 (by rfl) ⟨1127943, by rfl⟩ : syracuseStep 3007849 = 2255887) B2255887
theorem B17573365 : Blo 1624511 17573365 := bstep (se 5 (by rfl) ⟨823751, by rfl⟩ : syracuseStep 17573365 = 1647503) B1647503
theorem B4113929 : Blo 1624511 4113929 := bstep (se 2 (by rfl) ⟨1542723, by rfl⟩ : syracuseStep 4113929 = 3085447) B3085447
theorem B3655367 : Blo 1624511 3655367 := bstep (se 1 (by rfl) ⟨2741525, by rfl⟩ : syracuseStep 3655367 = 5483051) B5483051
theorem B20326187 : Blo 1624511 20326187 := bstep (se 1 (by rfl) ⟨15244640, by rfl⟩ : syracuseStep 20326187 = 30489281) B30489281
theorem B6252383 : Blo 1624511 6252383 := bstep (se 1 (by rfl) ⟨4689287, by rfl⟩ : syracuseStep 6252383 = 9378575) B9378575
theorem B47490911 : Blo 1624511 47490911 := bstep (se 1 (by rfl) ⟨35618183, by rfl⟩ : syracuseStep 47490911 = 71236367) B71236367
theorem B12339053 : Blo 1624511 12339053 := bstep (se 3 (by rfl) ⟨2313572, by rfl⟩ : syracuseStep 12339053 = 4627145) B4627145
theorem B18778061 : Blo 1624511 18778061 := bstep (se 3 (by rfl) ⟨3520886, by rfl⟩ : syracuseStep 18778061 = 7041773) B7041773
theorem B1828903 : Blo 1624511 1828903 := bstep (se 1 (by rfl) ⟨1371677, by rfl⟩ : syracuseStep 1828903 = 2743355) B2743355
theorem B6170681 : Blo 1624511 6170681 := bstep (se 2 (by rfl) ⟨2314005, by rfl⟩ : syracuseStep 6170681 = 4628011) B4628011
theorem B4630699 : Blo 1624511 4630699 := bstep (se 1 (by rfl) ⟨3473024, by rfl⟩ : syracuseStep 4630699 = 6946049) B6946049
theorem B1951943 : Blo 1624511 1951943 := bstep (se 1 (by rfl) ⟨1463957, by rfl⟩ : syracuseStep 1951943 = 2927915) B2927915
theorem B14068055 : Blo 1624511 14068055 := bstep (se 1 (by rfl) ⟨10551041, by rfl⟩ : syracuseStep 14068055 = 21102083) B21102083
theorem B7809367 : Blo 1624511 7809367 := bstep (se 1 (by rfl) ⟨5857025, by rfl⟩ : syracuseStep 7809367 = 11714051) B11714051
theorem B7809385 : Blo 1624511 7809385 := bstep (se 2 (by rfl) ⟨2928519, by rfl⟩ : syracuseStep 7809385 = 5857039) B5857039
theorem B2345323 : Blo 1624511 2345323 := bstep (se 1 (by rfl) ⟨1758992, by rfl⟩ : syracuseStep 2345323 = 3517985) B3517985
theorem B9259393 : Blo 1624511 9259393 := bstep (se 2 (by rfl) ⟨3472272, by rfl⟩ : syracuseStep 9259393 = 6944545) B6944545
theorem B4630927 : Blo 1624511 4630927 := bstep (se 1 (by rfl) ⟨3473195, by rfl⟩ : syracuseStep 4630927 = 6946391) B6946391
theorem B12347801 : Blo 1624511 12347801 := bstep (se 2 (by rfl) ⟨4630425, by rfl⟩ : syracuseStep 12347801 = 9260851) B9260851
theorem B1624519 : Blo 1624511 1624519 := bstep (se 1 (by rfl) ⟨1218389, by rfl⟩ : syracuseStep 1624519 = 2436779) B2436779
theorem B1624539 : Blo 1624511 1624539 := bstep (se 1 (by rfl) ⟨1218404, by rfl⟩ : syracuseStep 1624539 = 2436809) B2436809
theorem B10414615 : Blo 1624511 10414615 := bstep (se 1 (by rfl) ⟨7810961, by rfl⟩ : syracuseStep 10414615 = 15621923) B15621923
theorem B1624615 : Blo 1624511 1624615 := bstep (se 1 (by rfl) ⟨1218461, by rfl⟩ : syracuseStep 1624615 = 2436923) B2436923
theorem B3656231 : Blo 1624511 3656231 := bstep (se 1 (by rfl) ⟨2742173, by rfl⟩ : syracuseStep 3656231 = 5484347) B5484347
theorem B1624655 : Blo 1624511 1624655 := bstep (se 1 (by rfl) ⟨1218491, by rfl⟩ : syracuseStep 1624655 = 2436983) B2436983
theorem B1624671 : Blo 1624511 1624671 := bstep (se 1 (by rfl) ⟨1218503, by rfl⟩ : syracuseStep 1624671 = 2437007) B2437007
theorem B5483105 : Blo 1624511 5483105 := bstep (se 2 (by rfl) ⟨2056164, by rfl⟩ : syracuseStep 5483105 = 4112329) B4112329
theorem B1624699 : Blo 1624511 1624699 := bstep (se 1 (by rfl) ⟨1218524, by rfl⟩ : syracuseStep 1624699 = 2437049) B2437049
theorem B4115083 : Blo 1624511 4115083 := bstep (se 1 (by rfl) ⟨3086312, by rfl⟩ : syracuseStep 4115083 = 6172625) B6172625
theorem B1624751 : Blo 1624511 1624751 := bstep (se 1 (by rfl) ⟨1218563, by rfl⟩ : syracuseStep 1624751 = 2437127) B2437127
theorem B64195253 : Blo 1624511 64195253 := bstep (se 5 (by rfl) ⟨3009152, by rfl⟩ : syracuseStep 64195253 = 6018305) B6018305
theorem B1624775 : Blo 1624511 1624775 := bstep (se 1 (by rfl) ⟨1218581, by rfl⟩ : syracuseStep 1624775 = 2437163) B2437163
theorem B6171335 : Blo 1624511 6171335 := bstep (se 1 (by rfl) ⟨4628501, by rfl⟩ : syracuseStep 6171335 = 9257003) B9257003
theorem B1624795 : Blo 1624511 1624795 := bstep (se 1 (by rfl) ⟨1218596, by rfl⟩ : syracuseStep 1624795 = 2437193) B2437193
theorem B1624871 : Blo 1624511 1624871 := bstep (se 1 (by rfl) ⟨1218653, by rfl⟩ : syracuseStep 1624871 = 2437307) B2437307
theorem B1624911 : Blo 1624511 1624911 := bstep (se 1 (by rfl) ⟨1218683, by rfl⟩ : syracuseStep 1624911 = 2437367) B2437367
theorem B1624927 : Blo 1624511 1624927 := bstep (se 1 (by rfl) ⟨1218695, by rfl⟩ : syracuseStep 1624927 = 2437391) B2437391
theorem B3656555 : Blo 1624511 3656555 := bstep (se 1 (by rfl) ⟨2742416, by rfl⟩ : syracuseStep 3656555 = 5484833) B5484833
theorem B1624955 : Blo 1624511 1624955 := bstep (se 1 (by rfl) ⟨1218716, by rfl⟩ : syracuseStep 1624955 = 2437433) B2437433
theorem B3296143 : Blo 1624511 3296143 := bstep (se 1 (by rfl) ⟨2472107, by rfl⟩ : syracuseStep 3296143 = 4944215) B4944215
theorem B3656609 : Blo 1624511 3656609 := bstep (se 2 (by rfl) ⟨1371228, by rfl⟩ : syracuseStep 3656609 = 2742457) B2742457
theorem B1625007 : Blo 1624511 1625007 := bstep (se 1 (by rfl) ⟨1218755, by rfl⟩ : syracuseStep 1625007 = 2437511) B2437511
theorem B4115387 : Blo 1624511 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B1625031 : Blo 1624511 1625031 := bstep (se 1 (by rfl) ⟨1218773, by rfl⟩ : syracuseStep 1625031 = 2437547) B2437547
theorem B1625051 : Blo 1624511 1625051 := bstep (se 1 (by rfl) ⟨1218788, by rfl⟩ : syracuseStep 1625051 = 2437577) B2437577
theorem B10562579 : Blo 1624511 10562579 := bstep (se 1 (by rfl) ⟨7921934, by rfl⟩ : syracuseStep 10562579 = 15843869) B15843869
theorem B1625127 : Blo 1624511 1625127 := bstep (se 1 (by rfl) ⟨1218845, by rfl⟩ : syracuseStep 1625127 = 2437691) B2437691
theorem B3517519 : Blo 1624511 3517519 := bstep (se 1 (by rfl) ⟨2638139, by rfl⟩ : syracuseStep 3517519 = 5276279) B5276279
theorem B1625167 : Blo 1624511 1625167 := bstep (se 1 (by rfl) ⟨1218875, by rfl⟩ : syracuseStep 1625167 = 2437751) B2437751
theorem B1625183 : Blo 1624511 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B1625211 : Blo 1624511 1625211 := bstep (se 1 (by rfl) ⟨1218908, by rfl⟩ : syracuseStep 1625211 = 2437817) B2437817
theorem B1625263 : Blo 1624511 1625263 := bstep (se 1 (by rfl) ⟨1218947, by rfl⟩ : syracuseStep 1625263 = 2437895) B2437895
theorem B1625287 : Blo 1624511 1625287 := bstep (se 1 (by rfl) ⟨1218965, by rfl⟩ : syracuseStep 1625287 = 2437931) B2437931
theorem B1625307 : Blo 1624511 1625307 := bstep (se 1 (by rfl) ⟨1218980, by rfl⟩ : syracuseStep 1625307 = 2437961) B2437961
theorem B3656951 : Blo 1624511 3656951 := bstep (se 1 (by rfl) ⟨2742713, by rfl⟩ : syracuseStep 3656951 = 5485427) B5485427
theorem B53472545 : Blo 1624511 53472545 := bstep (se 2 (by rfl) ⟨20052204, by rfl⟩ : syracuseStep 53472545 = 40104409) B40104409
theorem B1625383 : Blo 1624511 1625383 := bstep (se 1 (by rfl) ⟨1219037, by rfl⟩ : syracuseStep 1625383 = 2438075) B2438075
theorem B1625423 : Blo 1624511 1625423 := bstep (se 1 (by rfl) ⟨1219067, by rfl⟩ : syracuseStep 1625423 = 2438135) B2438135
theorem B1625439 : Blo 1624511 1625439 := bstep (se 1 (by rfl) ⟨1219079, by rfl⟩ : syracuseStep 1625439 = 2438159) B2438159
theorem B1625467 : Blo 1624511 1625467 := bstep (se 1 (by rfl) ⟨1219100, by rfl⟩ : syracuseStep 1625467 = 2438201) B2438201
theorem B1625519 : Blo 1624511 1625519 := bstep (se 1 (by rfl) ⟨1219139, by rfl⟩ : syracuseStep 1625519 = 2438279) B2438279
theorem B2928059 : Blo 1624511 2928059 := bstep (se 1 (by rfl) ⟨2196044, by rfl⟩ : syracuseStep 2928059 = 4392089) B4392089
theorem B1625543 : Blo 1624511 1625543 := bstep (se 1 (by rfl) ⟨1219157, by rfl⟩ : syracuseStep 1625543 = 2438315) B2438315
theorem B1625563 : Blo 1624511 1625563 := bstep (se 1 (by rfl) ⟨1219172, by rfl⟩ : syracuseStep 1625563 = 2438345) B2438345
theorem B1625639 : Blo 1624511 1625639 := bstep (se 1 (by rfl) ⟨1219229, by rfl⟩ : syracuseStep 1625639 = 2438459) B2438459
theorem B1625679 : Blo 1624511 1625679 := bstep (se 1 (by rfl) ⟨1219259, by rfl⟩ : syracuseStep 1625679 = 2438519) B2438519
theorem B1625695 : Blo 1624511 1625695 := bstep (se 1 (by rfl) ⟨1219271, by rfl⟩ : syracuseStep 1625695 = 2438543) B2438543
theorem B1625723 : Blo 1624511 1625723 := bstep (se 1 (by rfl) ⟨1219292, by rfl⟩ : syracuseStep 1625723 = 2438585) B2438585
theorem B6172307 : Blo 1624511 6172307 := bstep (se 1 (by rfl) ⟨4629230, by rfl⟩ : syracuseStep 6172307 = 9258461) B9258461
theorem B1625775 : Blo 1624511 1625775 := bstep (se 1 (by rfl) ⟨1219331, by rfl⟩ : syracuseStep 1625775 = 2438663) B2438663
theorem B17575613 : Blo 1624511 17575613 := bstep (se 3 (by rfl) ⟨3295427, by rfl⟩ : syracuseStep 17575613 = 6590855) B6590855
theorem B9891517 : Blo 1624511 9891517 := bstep (se 3 (by rfl) ⟨1854659, by rfl⟩ : syracuseStep 9891517 = 3709319) B3709319
theorem B1625799 : Blo 1624511 1625799 := bstep (se 1 (by rfl) ⟨1219349, by rfl⟩ : syracuseStep 1625799 = 2438699) B2438699
theorem B4116167 : Blo 1624511 4116167 := bstep (se 1 (by rfl) ⟨3087125, by rfl⟩ : syracuseStep 4116167 = 6174251) B6174251
theorem B1625819 : Blo 1624511 1625819 := bstep (se 1 (by rfl) ⟨1219364, by rfl⟩ : syracuseStep 1625819 = 2438729) B2438729
theorem B20819693 : Blo 1624511 20819693 := bstep (se 3 (by rfl) ⟨3903692, by rfl⟩ : syracuseStep 20819693 = 7807385) B7807385
theorem B2436857 : Blo 1624511 2436857 := bstep (se 2 (by rfl) ⟨913821, by rfl⟩ : syracuseStep 2436857 = 1827643) B1827643
theorem B4116217 : Blo 1624511 4116217 := bstep (se 2 (by rfl) ⟨1543581, by rfl⟩ : syracuseStep 4116217 = 3087163) B3087163
theorem B1625895 : Blo 1624511 1625895 := bstep (se 1 (by rfl) ⟨1219421, by rfl⟩ : syracuseStep 1625895 = 2438843) B2438843
theorem B3657545 : Blo 1624511 3657545 := bstep (se 2 (by rfl) ⟨1371579, by rfl⟩ : syracuseStep 3657545 = 2743159) B2743159
theorem B1625935 : Blo 1624511 1625935 := bstep (se 1 (by rfl) ⟨1219451, by rfl⟩ : syracuseStep 1625935 = 2438903) B2438903
theorem B2436959 : Blo 1624511 2436959 := bstep (se 1 (by rfl) ⟨1827719, by rfl⟩ : syracuseStep 2436959 = 3655439) B3655439
theorem B1625951 : Blo 1624511 1625951 := bstep (se 1 (by rfl) ⟨1219463, by rfl⟩ : syracuseStep 1625951 = 2438927) B2438927
theorem B2436971 : Blo 1624511 2436971 := bstep (se 1 (by rfl) ⟨1827728, by rfl⟩ : syracuseStep 2436971 = 3655457) B3655457
theorem B1625979 : Blo 1624511 1625979 := bstep (se 1 (by rfl) ⟨1219484, by rfl⟩ : syracuseStep 1625979 = 2438969) B2438969
theorem B1626031 : Blo 1624511 1626031 := bstep (se 1 (by rfl) ⟨1219523, by rfl⟩ : syracuseStep 1626031 = 2439047) B2439047
theorem B1626055 : Blo 1624511 1626055 := bstep (se 1 (by rfl) ⟨1219541, by rfl⟩ : syracuseStep 1626055 = 2439083) B2439083
theorem B1626075 : Blo 1624511 1626075 := bstep (se 1 (by rfl) ⟨1219556, by rfl⟩ : syracuseStep 1626075 = 2439113) B2439113
theorem B5484563 : Blo 1624511 5484563 := bstep (se 1 (by rfl) ⟨4113422, by rfl⟩ : syracuseStep 5484563 = 8226845) B8226845
theorem B2314279 : Blo 1624511 2314279 := bstep (se 1 (by rfl) ⟨1735709, by rfl⟩ : syracuseStep 2314279 = 3471419) B3471419
theorem B2969639 : Blo 1624511 2969639 := bstep (se 1 (by rfl) ⟨2227229, by rfl⟩ : syracuseStep 2969639 = 4454459) B4454459
theorem B1626151 : Blo 1624511 1626151 := bstep (se 1 (by rfl) ⟨1219613, by rfl⟩ : syracuseStep 1626151 = 2439227) B2439227
theorem B2437199 : Blo 1624511 2437199 := bstep (se 1 (by rfl) ⟨1827899, by rfl⟩ : syracuseStep 2437199 = 3655799) B3655799
theorem B1626191 : Blo 1624511 1626191 := bstep (se 1 (by rfl) ⟨1219643, by rfl⟩ : syracuseStep 1626191 = 2439287) B2439287
theorem B1626207 : Blo 1624511 1626207 := bstep (se 1 (by rfl) ⟨1219655, by rfl⟩ : syracuseStep 1626207 = 2439311) B2439311
theorem B11120755 : Blo 1624511 11120755 := bstep (se 1 (by rfl) ⟨8340566, by rfl⟩ : syracuseStep 11120755 = 16681133) B16681133
theorem B1626235 : Blo 1624511 1626235 := bstep (se 1 (by rfl) ⟨1219676, by rfl⟩ : syracuseStep 1626235 = 2439353) B2439353
theorem B1626287 : Blo 1624511 1626287 := bstep (se 1 (by rfl) ⟨1219715, by rfl⟩ : syracuseStep 1626287 = 2439431) B2439431
theorem B2437319 : Blo 1624511 2437319 := bstep (se 1 (by rfl) ⟨1827989, by rfl⟩ : syracuseStep 2437319 = 3655979) B3655979
theorem B1626311 : Blo 1624511 1626311 := bstep (se 1 (by rfl) ⟨1219733, by rfl⟩ : syracuseStep 1626311 = 2439467) B2439467
theorem B94965965 : Blo 1624511 94965965 := bstep (se 3 (by rfl) ⟨17806118, by rfl⟩ : syracuseStep 94965965 = 35612237) B35612237
theorem B1626331 : Blo 1624511 1626331 := bstep (se 1 (by rfl) ⟨1219748, by rfl⟩ : syracuseStep 1626331 = 2439497) B2439497
theorem B1626407 : Blo 1624511 1626407 := bstep (se 1 (by rfl) ⟨1219805, by rfl⟩ : syracuseStep 1626407 = 2439611) B2439611
theorem B12349745 : Blo 1624511 12349745 := bstep (se 2 (by rfl) ⟨4631154, by rfl⟩ : syracuseStep 12349745 = 9262309) B9262309
theorem B1626447 : Blo 1624511 1626447 := bstep (se 1 (by rfl) ⟨1219835, by rfl⟩ : syracuseStep 1626447 = 2439671) B2439671
theorem B5484887 : Blo 1624511 5484887 := bstep (se 1 (by rfl) ⟨4113665, by rfl⟩ : syracuseStep 5484887 = 8227331) B8227331
theorem B1626463 : Blo 1624511 1626463 := bstep (se 1 (by rfl) ⟨1219847, by rfl⟩ : syracuseStep 1626463 = 2439695) B2439695
theorem B2437481 : Blo 1624511 2437481 := bstep (se 2 (by rfl) ⟨914055, by rfl⟩ : syracuseStep 2437481 = 1828111) B1828111
theorem B1626491 : Blo 1624511 1626491 := bstep (se 1 (by rfl) ⟨1219868, by rfl⟩ : syracuseStep 1626491 = 2439737) B2439737
theorem B4116865 : Blo 1624511 4116865 := bstep (se 2 (by rfl) ⟨1543824, by rfl⟩ : syracuseStep 4116865 = 3087649) B3087649
theorem B2437559 : Blo 1624511 2437559 := bstep (se 1 (by rfl) ⟨1828169, by rfl⟩ : syracuseStep 2437559 = 3656339) B3656339
theorem B2437595 : Blo 1624511 2437595 := bstep (se 1 (by rfl) ⟨1828196, by rfl⟩ : syracuseStep 2437595 = 3656393) B3656393
theorem B3658337 : Blo 1624511 3658337 := bstep (se 2 (by rfl) ⟨1371876, by rfl⟩ : syracuseStep 3658337 = 2743753) B2743753
theorem B9253561 : Blo 1624511 9253561 := bstep (se 2 (by rfl) ⟨3470085, by rfl⟩ : syracuseStep 9253561 = 6940171) B6940171
theorem B3470035 : Blo 1624511 3470035 := bstep (se 1 (by rfl) ⟨2602526, by rfl⟩ : syracuseStep 3470035 = 5205053) B5205053
theorem B12341969 : Blo 1624511 12341969 := bstep (se 2 (by rfl) ⟨4628238, by rfl⟩ : syracuseStep 12341969 = 9256477) B9256477
theorem B18510767 : Blo 1624511 18510767 := bstep (se 1 (by rfl) ⟨13883075, by rfl⟩ : syracuseStep 18510767 = 27766151) B27766151
theorem B2438063 : Blo 1624511 2438063 := bstep (se 1 (by rfl) ⟨1828547, by rfl⟩ : syracuseStep 2438063 = 3657095) B3657095
theorem B3658679 : Blo 1624511 3658679 := bstep (se 1 (by rfl) ⟨2744009, by rfl⟩ : syracuseStep 3658679 = 5488019) B5488019
theorem B10408925 : Blo 1624511 10408925 := bstep (se 3 (by rfl) ⟨1951673, by rfl⟩ : syracuseStep 10408925 = 3903347) B3903347
theorem B2438153 : Blo 1624511 2438153 := bstep (se 2 (by rfl) ⟨914307, by rfl⟩ : syracuseStep 2438153 = 1828615) B1828615
theorem B2929673 : Blo 1624511 2929673 := bstep (se 2 (by rfl) ⟨1098627, by rfl⟩ : syracuseStep 2929673 = 2197255) B2197255
theorem B21124115 : Blo 1624511 21124115 := bstep (se 1 (by rfl) ⟨15843086, by rfl⟩ : syracuseStep 21124115 = 31686173) B31686173
theorem B2438183 : Blo 1624511 2438183 := bstep (se 1 (by rfl) ⟨1828637, by rfl⟩ : syracuseStep 2438183 = 3657275) B3657275
theorem B2438267 : Blo 1624511 2438267 := bstep (se 1 (by rfl) ⟨1828700, by rfl⟩ : syracuseStep 2438267 = 3657401) B3657401
theorem B3085523 : Blo 1624511 3085523 := bstep (se 1 (by rfl) ⟨2314142, by rfl⟩ : syracuseStep 3085523 = 4628285) B4628285
theorem B2438393 : Blo 1624511 2438393 := bstep (se 2 (by rfl) ⟨914397, by rfl⟩ : syracuseStep 2438393 = 1828795) B1828795
theorem B2438495 : Blo 1624511 2438495 := bstep (se 1 (by rfl) ⟨1828871, by rfl⟩ : syracuseStep 2438495 = 3657743) B3657743
theorem B2438507 : Blo 1624511 2438507 := bstep (se 1 (by rfl) ⟨1828880, by rfl⟩ : syracuseStep 2438507 = 3657761) B3657761
theorem B11720051 : Blo 1624511 11720051 := bstep (se 1 (by rfl) ⟨8790038, by rfl⟩ : syracuseStep 11720051 = 17580077) B17580077
theorem B2741647 : Blo 1624511 2741647 := bstep (se 1 (by rfl) ⟨2056235, by rfl⟩ : syracuseStep 2741647 = 4112471) B4112471
theorem B3470735 : Blo 1624511 3470735 := bstep (se 1 (by rfl) ⟨2603051, by rfl⟩ : syracuseStep 3470735 = 5206103) B5206103
theorem B5485967 : Blo 1624511 5485967 := bstep (se 1 (by rfl) ⟨4114475, by rfl⟩ : syracuseStep 5485967 = 8228951) B8228951
theorem B3085751 : Blo 1624511 3085751 := bstep (se 1 (by rfl) ⟨2314313, by rfl⟩ : syracuseStep 3085751 = 4628627) B4628627
theorem B18519515 : Blo 1624511 18519515 := bstep (se 1 (by rfl) ⟨13889636, by rfl⟩ : syracuseStep 18519515 = 27779273) B27779273
theorem B3659273 : Blo 1624511 3659273 := bstep (se 2 (by rfl) ⟨1372227, by rfl⟩ : syracuseStep 3659273 = 2744455) B2744455
theorem B2438735 : Blo 1624511 2438735 := bstep (se 1 (by rfl) ⟨1829051, by rfl⟩ : syracuseStep 2438735 = 3658103) B3658103
theorem B20821697 : Blo 1624511 20821697 := bstep (se 2 (by rfl) ⟨7808136, by rfl⟩ : syracuseStep 20821697 = 15616273) B15616273
theorem B2438855 : Blo 1624511 2438855 := bstep (se 1 (by rfl) ⟨1829141, by rfl⟩ : syracuseStep 2438855 = 3658283) B3658283
theorem B5486291 : Blo 1624511 5486291 := bstep (se 1 (by rfl) ⟨4114718, by rfl⟩ : syracuseStep 5486291 = 8229437) B8229437
theorem B44480299 : Blo 1624511 44480299 := bstep (se 1 (by rfl) ⟨33360224, by rfl⟩ : syracuseStep 44480299 = 66720449) B66720449
theorem B2602847 : Blo 1624511 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B26367839 : Blo 1624511 26367839 := bstep (se 1 (by rfl) ⟨19775879, by rfl⟩ : syracuseStep 26367839 = 39551759) B39551759
theorem B3659615 : Blo 1624511 3659615 := bstep (se 1 (by rfl) ⟨2744711, by rfl⟩ : syracuseStep 3659615 = 5489423) B5489423
theorem B2439017 : Blo 1624511 2439017 := bstep (se 2 (by rfl) ⟨914631, by rfl⟩ : syracuseStep 2439017 = 1829263) B1829263
theorem B3471265 : Blo 1624511 3471265 := bstep (se 2 (by rfl) ⟨1301724, by rfl⟩ : syracuseStep 3471265 = 2603449) B2603449
theorem B2439095 : Blo 1624511 2439095 := bstep (se 1 (by rfl) ⟨1829321, by rfl⟩ : syracuseStep 2439095 = 3658643) B3658643
theorem B2439131 : Blo 1624511 2439131 := bstep (se 1 (by rfl) ⟨1829348, by rfl⟩ : syracuseStep 2439131 = 3658697) B3658697
theorem B2742329 : Blo 1624511 2742329 := bstep (se 2 (by rfl) ⟨1028373, by rfl⟩ : syracuseStep 2742329 = 2056747) B2056747
theorem B3905615 : Blo 1624511 3905615 := bstep (se 1 (by rfl) ⟨2929211, by rfl⟩ : syracuseStep 3905615 = 5858423) B5858423
theorem B3348559 : Blo 1624511 3348559 := bstep (se 1 (by rfl) ⟨2511419, by rfl⟩ : syracuseStep 3348559 = 5022839) B5022839
theorem B2930899 : Blo 1624511 2930899 := bstep (se 1 (by rfl) ⟨2198174, by rfl⟩ : syracuseStep 2930899 = 4396349) B4396349
theorem B4626679 : Blo 1624511 4626679 := bstep (se 1 (by rfl) ⟨3470009, by rfl⟩ : syracuseStep 4626679 = 6940019) B6940019
theorem B2439599 : Blo 1624511 2439599 := bstep (se 1 (by rfl) ⟨1829699, by rfl⟩ : syracuseStep 2439599 = 3659399) B3659399
theorem B5208563 : Blo 1624511 5208563 := bstep (se 1 (by rfl) ⟨3906422, by rfl⟩ : syracuseStep 5208563 = 7812845) B7812845
theorem B4626953 : Blo 1624511 4626953 := bstep (se 2 (by rfl) ⟨1735107, by rfl⟩ : syracuseStep 4626953 = 3470215) B3470215
theorem B2439689 : Blo 1624511 2439689 := bstep (se 2 (by rfl) ⟨914883, by rfl⟩ : syracuseStep 2439689 = 1829767) B1829767
theorem B2439719 : Blo 1624511 2439719 := bstep (se 1 (by rfl) ⟨1829789, by rfl⟩ : syracuseStep 2439719 = 3659579) B3659579
theorem B3086905 : Blo 1624511 3086905 := bstep (se 2 (by rfl) ⟨1157589, by rfl⟩ : syracuseStep 3086905 = 2315179) B2315179
theorem B7813691 : Blo 1624511 7813691 := bstep (se 1 (by rfl) ⟨5860268, by rfl⟩ : syracuseStep 7813691 = 11720537) B11720537
theorem B1735291 : Blo 1624511 1735291 := bstep (se 1 (by rfl) ⟨1301468, by rfl⟩ : syracuseStep 1735291 = 2602937) B2602937
theorem B2743031 : Blo 1624511 2743031 := bstep (se 1 (by rfl) ⟨2057273, by rfl⟩ : syracuseStep 2743031 = 4114547) B4114547
theorem B3087209 : Blo 1624511 3087209 := bstep (se 2 (by rfl) ⟨1157703, by rfl⟩ : syracuseStep 3087209 = 2315407) B2315407
theorem B5487479 : Blo 1624511 5487479 := bstep (se 1 (by rfl) ⟨4115609, by rfl⟩ : syracuseStep 5487479 = 8231219) B8231219
theorem B3087247 : Blo 1624511 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B5856263 : Blo 1624511 5856263 := bstep (se 1 (by rfl) ⟨4392197, by rfl⟩ : syracuseStep 5856263 = 8784395) B8784395
theorem B12344399 : Blo 1624511 12344399 := bstep (se 1 (by rfl) ⟨9258299, by rfl⟩ : syracuseStep 12344399 = 18516599) B18516599
theorem B2743375 : Blo 1624511 2743375 := bstep (se 1 (by rfl) ⟨2057531, by rfl⟩ : syracuseStep 2743375 = 4115063) B4115063
theorem B5487695 : Blo 1624511 5487695 := bstep (se 1 (by rfl) ⟨4115771, by rfl⟩ : syracuseStep 5487695 = 8231543) B8231543
theorem B3906731 : Blo 1624511 3906731 := bstep (se 1 (by rfl) ⟨2930048, by rfl⟩ : syracuseStep 3906731 = 5860097) B5860097
theorem B9886967 : Blo 1624511 9886967 := bstep (se 1 (by rfl) ⟨7415225, by rfl⟩ : syracuseStep 9886967 = 14830451) B14830451
theorem B2743625 : Blo 1624511 2743625 := bstep (se 2 (by rfl) ⟨1028859, by rfl⟩ : syracuseStep 2743625 = 2057719) B2057719
theorem B1736111 : Blo 1624511 1736111 := bstep (se 1 (by rfl) ⟨1302083, by rfl⟩ : syracuseStep 1736111 = 2604167) B2604167
theorem B5488073 : Blo 1624511 5488073 := bstep (se 2 (by rfl) ⟨2058027, by rfl⟩ : syracuseStep 5488073 = 4116055) B4116055
theorem B106905037 : Blo 1624511 106905037 := bstep (se 3 (by rfl) ⟨20044694, by rfl⟩ : syracuseStep 106905037 = 40089389) B40089389
theorem B4627955 : Blo 1624511 4627955 := bstep (se 1 (by rfl) ⟨3470966, by rfl⟩ : syracuseStep 4627955 = 6941933) B6941933
theorem B5488343 : Blo 1624511 5488343 := bstep (se 1 (by rfl) ⟨4116257, by rfl⟩ : syracuseStep 5488343 = 8232515) B8232515
theorem B2744057 : Blo 1624511 2744057 := bstep (se 2 (by rfl) ⟨1029021, by rfl⟩ : syracuseStep 2744057 = 2058043) B2058043
theorem B31252229 : Blo 1624511 31252229 := bstep (se 4 (by rfl) ⟨2929896, by rfl⟩ : syracuseStep 31252229 = 5859793) B5859793
theorem B5275421 : Blo 1624511 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B2056043 : Blo 1624511 2056043 := bstep (se 1 (by rfl) ⟨1542032, by rfl⟩ : syracuseStep 2056043 = 3084065) B3084065
theorem B2744239 : Blo 1624511 2744239 := bstep (se 1 (by rfl) ⟨2058179, by rfl⟩ : syracuseStep 2744239 = 4116359) B4116359
theorem B5488559 : Blo 1624511 5488559 := bstep (se 1 (by rfl) ⟨4116419, by rfl⟩ : syracuseStep 5488559 = 8232839) B8232839
theorem B4628411 : Blo 1624511 4628411 := bstep (se 1 (by rfl) ⟨3471308, by rfl⟩ : syracuseStep 4628411 = 6942617) B6942617
theorem B14073875 : Blo 1624511 14073875 := bstep (se 1 (by rfl) ⟨10555406, by rfl⟩ : syracuseStep 14073875 = 21110813) B21110813
theorem B14827673 : Blo 1624511 14827673 := bstep (se 2 (by rfl) ⟨5560377, by rfl⟩ : syracuseStep 14827673 = 11120755) B11120755
theorem B8233163 : Blo 1624511 8233163 := bstep (se 1 (by rfl) ⟨6174872, by rfl⟩ : syracuseStep 8233163 = 12349745) B12349745
theorem B3907865 : Blo 1624511 3907865 := bstep (se 2 (by rfl) ⟨1465449, by rfl⟩ : syracuseStep 3907865 = 2930899) B2930899
theorem B6168905 : Blo 1624511 6168905 := bstep (se 2 (by rfl) ⟨2313339, by rfl⟩ : syracuseStep 6168905 = 4626679) B4626679
theorem B17858981 : Blo 1624511 17858981 := bstep (se 4 (by rfl) ⟨1674279, by rfl⟩ : syracuseStep 17858981 = 3348559) B3348559
theorem B4112815 : Blo 1624511 4112815 := bstep (se 1 (by rfl) ⟨3084611, by rfl⟩ : syracuseStep 4112815 = 6169223) B6169223
theorem B8225225 : Blo 1624511 8225225 := bstep (se 2 (by rfl) ⟨3084459, by rfl⟩ : syracuseStep 8225225 = 6168919) B6168919
theorem B10412489 : Blo 1624511 10412489 := bstep (se 2 (by rfl) ⟨3904683, by rfl⟩ : syracuseStep 10412489 = 7809367) B7809367
theorem B10412513 : Blo 1624511 10412513 := bstep (se 2 (by rfl) ⟨3904692, by rfl⟩ : syracuseStep 10412513 = 7809385) B7809385
theorem B12345857 : Blo 1624511 12345857 := bstep (se 2 (by rfl) ⟨4629696, by rfl⟩ : syracuseStep 12345857 = 9259393) B9259393
theorem B5489153 : Blo 1624511 5489153 := bstep (se 2 (by rfl) ⟨2058432, by rfl⟩ : syracuseStep 5489153 = 4116865) B4116865
theorem B6939283 : Blo 1624511 6939283 := bstep (se 1 (by rfl) ⟨5204462, by rfl⟩ : syracuseStep 6939283 = 10408925) B10408925
theorem B14082743 : Blo 1624511 14082743 := bstep (se 1 (by rfl) ⟨10562057, by rfl⟩ : syracuseStep 14082743 = 21124115) B21124115
theorem B10420919 : Blo 1624511 10420919 := bstep (se 1 (by rfl) ⟨7815689, by rfl⟩ : syracuseStep 10420919 = 15631379) B15631379
theorem B13886153 : Blo 1624511 13886153 := bstep (se 2 (by rfl) ⟨5207307, by rfl⟩ : syracuseStep 13886153 = 10414615) B10414615
theorem B4113119 : Blo 1624511 4113119 := bstep (se 1 (by rfl) ⟨3084839, by rfl⟩ : syracuseStep 4113119 = 6169679) B6169679
theorem B2057015 : Blo 1624511 2057015 := bstep (se 1 (by rfl) ⟨1542761, by rfl⟩ : syracuseStep 2057015 = 3085523) B3085523
theorem B12338081 : Blo 1624511 12338081 := bstep (se 2 (by rfl) ⟨4626780, by rfl⟩ : syracuseStep 12338081 = 9253561) B9253561
theorem B2057167 : Blo 1624511 2057167 := bstep (se 1 (by rfl) ⟨1542875, by rfl⟩ : syracuseStep 2057167 = 3085751) B3085751
theorem B12346343 : Blo 1624511 12346343 := bstep (se 1 (by rfl) ⟨9259757, by rfl⟩ : syracuseStep 12346343 = 18519515) B18519515
theorem B4629629 : Blo 1624511 4629629 := bstep (se 3 (by rfl) ⟨868055, by rfl⟩ : syracuseStep 4629629 = 1736111) B1736111
theorem B8226035 : Blo 1624511 8226035 := bstep (se 1 (by rfl) ⟨6169526, by rfl⟩ : syracuseStep 8226035 = 12339053) B12339053
theorem B12518707 : Blo 1624511 12518707 := bstep (se 1 (by rfl) ⟨9389030, by rfl⟩ : syracuseStep 12518707 = 18778061) B18778061
theorem B1828219 : Blo 1624511 1828219 := bstep (se 1 (by rfl) ⟨1371164, by rfl⟩ : syracuseStep 1828219 = 2742329) B2742329
theorem B4113787 : Blo 1624511 4113787 := bstep (se 1 (by rfl) ⟨3085340, by rfl⟩ : syracuseStep 4113787 = 6170681) B6170681
theorem B3655403 : Blo 1624511 3655403 := bstep (se 1 (by rfl) ⟨2741552, by rfl⟩ : syracuseStep 3655403 = 5483105) B5483105
theorem B42796835 : Blo 1624511 42796835 := bstep (se 1 (by rfl) ⟨32097626, by rfl⟩ : syracuseStep 42796835 = 64195253) B64195253
theorem B4114223 : Blo 1624511 4114223 := bstep (se 1 (by rfl) ⟨3085667, by rfl⟩ : syracuseStep 4114223 = 6171335) B6171335
theorem B1828687 : Blo 1624511 1828687 := bstep (se 1 (by rfl) ⟨1371515, by rfl⟩ : syracuseStep 1828687 = 2743031) B2743031
theorem B3655529 : Blo 1624511 3655529 := bstep (se 2 (by rfl) ⟨1370823, by rfl⟩ : syracuseStep 3655529 = 2741647) B2741647
theorem B2058139 : Blo 1624511 2058139 := bstep (se 1 (by rfl) ⟨1543604, by rfl⟩ : syracuseStep 2058139 = 3087209) B3087209
theorem B23431153 : Blo 1624511 23431153 := bstep (se 2 (by rfl) ⟨8786682, by rfl⟩ : syracuseStep 23431153 = 17573365) B17573365
theorem B1829083 : Blo 1624511 1829083 := bstep (se 1 (by rfl) ⟨1371812, by rfl⟩ : syracuseStep 1829083 = 2743625) B2743625
theorem B5482781 : Blo 1624511 5482781 := bstep (se 3 (by rfl) ⟨1028021, by rfl⟩ : syracuseStep 5482781 = 2056043) B2056043
theorem B1952039 : Blo 1624511 1952039 := bstep (se 1 (by rfl) ⟨1464029, by rfl⟩ : syracuseStep 1952039 = 2928059) B2928059
theorem B4114871 : Blo 1624511 4114871 := bstep (se 1 (by rfl) ⟨3086153, by rfl⟩ : syracuseStep 4114871 = 6172307) B6172307
theorem B11717075 : Blo 1624511 11717075 := bstep (se 1 (by rfl) ⟨8787806, by rfl⟩ : syracuseStep 11717075 = 17575613) B17575613
theorem B13879795 : Blo 1624511 13879795 := bstep (se 1 (by rfl) ⟨10409846, by rfl⟩ : syracuseStep 13879795 = 20819693) B20819693
theorem B1624571 : Blo 1624511 1624571 := bstep (se 1 (by rfl) ⟨1218428, by rfl⟩ : syracuseStep 1624571 = 2436857) B2436857
theorem B1829371 : Blo 1624511 1829371 := bstep (se 1 (by rfl) ⟨1372028, by rfl⟩ : syracuseStep 1829371 = 2744057) B2744057
theorem B20834819 : Blo 1624511 20834819 := bstep (se 1 (by rfl) ⟨15626114, by rfl⟩ : syracuseStep 20834819 = 31252229) B31252229
theorem B3516947 : Blo 1624511 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B1624639 : Blo 1624511 1624639 := bstep (se 1 (by rfl) ⟨1218479, by rfl⟩ : syracuseStep 1624639 = 2436959) B2436959
theorem B1624647 : Blo 1624511 1624647 := bstep (se 1 (by rfl) ⟨1218485, by rfl⟩ : syracuseStep 1624647 = 2436971) B2436971
theorem B1829551 : Blo 1624511 1829551 := bstep (se 1 (by rfl) ⟨1372163, by rfl⟩ : syracuseStep 1829551 = 2744327) B2744327
theorem B3656375 : Blo 1624511 3656375 := bstep (se 1 (by rfl) ⟨2742281, by rfl⟩ : syracuseStep 3656375 = 5484563) B5484563
theorem B1624799 : Blo 1624511 1624799 := bstep (se 1 (by rfl) ⟨1218599, by rfl⟩ : syracuseStep 1624799 = 2437199) B2437199
theorem B1624879 : Blo 1624511 1624879 := bstep (se 1 (by rfl) ⟨1218659, by rfl⟩ : syracuseStep 1624879 = 2437319) B2437319
theorem B63310643 : Blo 1624511 63310643 := bstep (se 1 (by rfl) ⟨47482982, by rfl⟩ : syracuseStep 63310643 = 94965965) B94965965
theorem B10414973 : Blo 1624511 10414973 := bstep (se 3 (by rfl) ⟨1952807, by rfl⟩ : syracuseStep 10414973 = 3905615) B3905615
theorem B3656591 : Blo 1624511 3656591 := bstep (se 1 (by rfl) ⟨2742443, by rfl⟩ : syracuseStep 3656591 = 5484887) B5484887
theorem B4172687 : Blo 1624511 4172687 := bstep (se 1 (by rfl) ⟨3129515, by rfl⟩ : syracuseStep 4172687 = 6259031) B6259031
theorem B1624987 : Blo 1624511 1624987 := bstep (se 1 (by rfl) ⟨1218740, by rfl⟩ : syracuseStep 1624987 = 2437481) B2437481
theorem B1625039 : Blo 1624511 1625039 := bstep (se 1 (by rfl) ⟨1218779, by rfl⟩ : syracuseStep 1625039 = 2437559) B2437559
theorem B1625063 : Blo 1624511 1625063 := bstep (se 1 (by rfl) ⟨1218797, by rfl⟩ : syracuseStep 1625063 = 2437595) B2437595
theorem B4172791 : Blo 1624511 4172791 := bstep (se 1 (by rfl) ⟨3129593, by rfl⟩ : syracuseStep 4172791 = 6259187) B6259187
theorem B8227979 : Blo 1624511 8227979 := bstep (se 1 (by rfl) ⟨6170984, by rfl⟩ : syracuseStep 8227979 = 12341969) B12341969
theorem B5205181 : Blo 1624511 5205181 := bstep (se 3 (by rfl) ⟨975971, by rfl⟩ : syracuseStep 5205181 = 1951943) B1951943
theorem B5483807 : Blo 1624511 5483807 := bstep (se 1 (by rfl) ⟨4112855, by rfl⟩ : syracuseStep 5483807 = 8225711) B8225711
theorem B12340511 : Blo 1624511 12340511 := bstep (se 1 (by rfl) ⟨9255383, by rfl⟩ : syracuseStep 12340511 = 18510767) B18510767
theorem B6941983 : Blo 1624511 6941983 := bstep (se 1 (by rfl) ⟨5206487, by rfl⟩ : syracuseStep 6941983 = 10412975) B10412975
theorem B1625375 : Blo 1624511 1625375 := bstep (se 1 (by rfl) ⟨1219031, by rfl⟩ : syracuseStep 1625375 = 2438063) B2438063
theorem B1625435 : Blo 1624511 1625435 := bstep (se 1 (by rfl) ⟨1219076, by rfl⟩ : syracuseStep 1625435 = 2438153) B2438153
theorem B1953115 : Blo 1624511 1953115 := bstep (se 1 (by rfl) ⟨1464836, by rfl⟩ : syracuseStep 1953115 = 2929673) B2929673
theorem B1625455 : Blo 1624511 1625455 := bstep (se 1 (by rfl) ⟨1219091, by rfl⟩ : syracuseStep 1625455 = 2438183) B2438183
theorem B4115873 : Blo 1624511 4115873 := bstep (se 2 (by rfl) ⟨1543452, by rfl⟩ : syracuseStep 4115873 = 3086905) B3086905
theorem B1625511 : Blo 1624511 1625511 := bstep (se 1 (by rfl) ⟨1219133, by rfl⟩ : syracuseStep 1625511 = 2438267) B2438267
theorem B12512699 : Blo 1624511 12512699 := bstep (se 1 (by rfl) ⟨9384524, by rfl⟩ : syracuseStep 12512699 = 18769049) B18769049
theorem B2313721 : Blo 1624511 2313721 := bstep (se 2 (by rfl) ⟨867645, by rfl⟩ : syracuseStep 2313721 = 1735291) B1735291
theorem B1625595 : Blo 1624511 1625595 := bstep (se 1 (by rfl) ⟨1219196, by rfl⟩ : syracuseStep 1625595 = 2438393) B2438393
theorem B1625663 : Blo 1624511 1625663 := bstep (se 1 (by rfl) ⟨1219247, by rfl⟩ : syracuseStep 1625663 = 2438495) B2438495
theorem B1625671 : Blo 1624511 1625671 := bstep (se 1 (by rfl) ⟨1219253, by rfl⟩ : syracuseStep 1625671 = 2438507) B2438507
theorem B3657311 : Blo 1624511 3657311 := bstep (se 1 (by rfl) ⟨2742983, by rfl⟩ : syracuseStep 3657311 = 5485967) B5485967
theorem B6172321 : Blo 1624511 6172321 := bstep (se 2 (by rfl) ⟨2314620, by rfl⟩ : syracuseStep 6172321 = 4629241) B4629241
theorem B7810769 : Blo 1624511 7810769 := bstep (se 2 (by rfl) ⟨2929038, by rfl⟩ : syracuseStep 7810769 = 5858077) B5858077
theorem B1625823 : Blo 1624511 1625823 := bstep (se 1 (by rfl) ⟨1219367, by rfl⟩ : syracuseStep 1625823 = 2438735) B2438735
theorem B2436905 : Blo 1624511 2436905 := bstep (se 2 (by rfl) ⟨913839, by rfl⟩ : syracuseStep 2436905 = 1827679) B1827679
theorem B13881131 : Blo 1624511 13881131 := bstep (se 1 (by rfl) ⟨10410848, by rfl⟩ : syracuseStep 13881131 = 20821697) B20821697
theorem B2436911 : Blo 1624511 2436911 := bstep (se 1 (by rfl) ⟨1827683, by rfl⟩ : syracuseStep 2436911 = 3655367) B3655367
theorem B1625903 : Blo 1624511 1625903 := bstep (se 1 (by rfl) ⟨1219427, by rfl⟩ : syracuseStep 1625903 = 2438855) B2438855
theorem B3657527 : Blo 1624511 3657527 := bstep (se 1 (by rfl) ⟨2743145, by rfl⟩ : syracuseStep 3657527 = 5486291) B5486291
theorem B4394857 : Blo 1624511 4394857 := bstep (se 2 (by rfl) ⟨1648071, by rfl⟩ : syracuseStep 4394857 = 3296143) B3296143
theorem B4116329 : Blo 1624511 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B1626011 : Blo 1624511 1626011 := bstep (se 1 (by rfl) ⟨1219508, by rfl⟩ : syracuseStep 1626011 = 2439017) B2439017
theorem B1626063 : Blo 1624511 1626063 := bstep (se 1 (by rfl) ⟨1219547, by rfl⟩ : syracuseStep 1626063 = 2439095) B2439095
theorem B13889501 : Blo 1624511 13889501 := bstep (se 3 (by rfl) ⟨2604281, by rfl⟩ : syracuseStep 13889501 = 5208563) B5208563
theorem B1626087 : Blo 1624511 1626087 := bstep (se 1 (by rfl) ⟨1219565, by rfl⟩ : syracuseStep 1626087 = 2439131) B2439131
theorem B4690025 : Blo 1624511 4690025 := bstep (se 2 (by rfl) ⟨1758759, by rfl⟩ : syracuseStep 4690025 = 3517519) B3517519
theorem B3657833 : Blo 1624511 3657833 := bstep (se 2 (by rfl) ⟨1371687, by rfl⟩ : syracuseStep 3657833 = 2743375) B2743375
theorem B2437385 : Blo 1624511 2437385 := bstep (se 2 (by rfl) ⟨914019, by rfl⟩ : syracuseStep 2437385 = 1828039) B1828039
theorem B1626399 : Blo 1624511 1626399 := bstep (se 1 (by rfl) ⟨1219799, by rfl⟩ : syracuseStep 1626399 = 2439599) B2439599
theorem B3084635 : Blo 1624511 3084635 := bstep (se 1 (by rfl) ⟨2313476, by rfl⟩ : syracuseStep 3084635 = 4626953) B4626953
theorem B1626459 : Blo 1624511 1626459 := bstep (se 1 (by rfl) ⟨1219844, by rfl⟩ : syracuseStep 1626459 = 2439689) B2439689
theorem B2437487 : Blo 1624511 2437487 := bstep (se 1 (by rfl) ⟨1828115, by rfl⟩ : syracuseStep 2437487 = 3656231) B3656231
theorem B1626479 : Blo 1624511 1626479 := bstep (se 1 (by rfl) ⟨1219859, by rfl⟩ : syracuseStep 1626479 = 2439719) B2439719
theorem B4010465 : Blo 1624511 4010465 := bstep (se 2 (by rfl) ⟨1503924, by rfl⟩ : syracuseStep 4010465 = 3007849) B3007849
theorem B2437703 : Blo 1624511 2437703 := bstep (se 1 (by rfl) ⟨1828277, by rfl⟩ : syracuseStep 2437703 = 3656555) B3656555
theorem B3658319 : Blo 1624511 3658319 := bstep (se 1 (by rfl) ⟨2743739, by rfl⟩ : syracuseStep 3658319 = 5487479) B5487479
theorem B2437739 : Blo 1624511 2437739 := bstep (se 1 (by rfl) ⟨1828304, by rfl⟩ : syracuseStep 2437739 = 3656609) B3656609
theorem B3904175 : Blo 1624511 3904175 := bstep (se 1 (by rfl) ⟨2928131, by rfl⟩ : syracuseStep 3904175 = 5856263) B5856263
theorem B7041719 : Blo 1624511 7041719 := bstep (se 1 (by rfl) ⟨5281289, by rfl⟩ : syracuseStep 7041719 = 10562579) B10562579
theorem B8229599 : Blo 1624511 8229599 := bstep (se 1 (by rfl) ⟨6172199, by rfl⟩ : syracuseStep 8229599 = 12344399) B12344399
theorem B3658463 : Blo 1624511 3658463 := bstep (se 1 (by rfl) ⟨2743847, by rfl⟩ : syracuseStep 3658463 = 5487695) B5487695
theorem B54203165 : Blo 1624511 54203165 := bstep (se 3 (by rfl) ⟨10163093, by rfl⟩ : syracuseStep 54203165 = 20326187) B20326187
theorem B2437967 : Blo 1624511 2437967 := bstep (se 1 (by rfl) ⟨1828475, by rfl⟩ : syracuseStep 2437967 = 3656951) B3656951
theorem B6591311 : Blo 1624511 6591311 := bstep (se 1 (by rfl) ⟨4943483, by rfl⟩ : syracuseStep 6591311 = 9886967) B9886967
theorem B35648363 : Blo 1624511 35648363 := bstep (se 1 (by rfl) ⟨26736272, by rfl⟩ : syracuseStep 35648363 = 53472545) B53472545
theorem B3658715 : Blo 1624511 3658715 := bstep (se 1 (by rfl) ⟨2744036, by rfl⟩ : syracuseStep 3658715 = 5488073) B5488073
theorem B3085303 : Blo 1624511 3085303 := bstep (se 1 (by rfl) ⟨2313977, by rfl⟩ : syracuseStep 3085303 = 4627955) B4627955
theorem B59307065 : Blo 1624511 59307065 := bstep (se 2 (by rfl) ⟨22240149, by rfl⟩ : syracuseStep 59307065 = 44480299) B44480299
theorem B3658895 : Blo 1624511 3658895 := bstep (se 1 (by rfl) ⟨2744171, by rfl⟩ : syracuseStep 3658895 = 5488343) B5488343
theorem B2438363 : Blo 1624511 2438363 := bstep (se 1 (by rfl) ⟨1828772, by rfl⟩ : syracuseStep 2438363 = 3657545) B3657545
theorem B3658985 : Blo 1624511 3658985 := bstep (se 2 (by rfl) ⟨1372119, by rfl⟩ : syracuseStep 3658985 = 2744239) B2744239
theorem B3659039 : Blo 1624511 3659039 := bstep (se 1 (by rfl) ⟨2744279, by rfl⟩ : syracuseStep 3659039 = 5488559) B5488559
theorem B3085607 : Blo 1624511 3085607 := bstep (se 1 (by rfl) ⟨2314205, by rfl⟩ : syracuseStep 3085607 = 4628411) B4628411
theorem B1979759 : Blo 1624511 1979759 := bstep (se 1 (by rfl) ⟨1484819, by rfl⟩ : syracuseStep 1979759 = 2969639) B2969639
theorem B2741627 : Blo 1624511 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B3085705 : Blo 1624511 3085705 := bstep (se 2 (by rfl) ⟨1157139, by rfl⟩ : syracuseStep 3085705 = 2314279) B2314279
theorem B2438537 : Blo 1624511 2438537 := bstep (se 2 (by rfl) ⟨914451, by rfl⟩ : syracuseStep 2438537 = 1828903) B1828903
theorem B6174265 : Blo 1624511 6174265 := bstep (se 2 (by rfl) ⟨2315349, by rfl⟩ : syracuseStep 6174265 = 4630699) B4630699
theorem B5486237 : Blo 1624511 5486237 := bstep (se 3 (by rfl) ⟨1028669, by rfl⟩ : syracuseStep 5486237 = 2057339) B2057339
theorem B2438891 : Blo 1624511 2438891 := bstep (se 1 (by rfl) ⟨1829168, by rfl⟩ : syracuseStep 2438891 = 3658337) B3658337
theorem B3659561 : Blo 1624511 3659561 := bstep (se 2 (by rfl) ⟨1372335, by rfl⟩ : syracuseStep 3659561 = 2744671) B2744671
theorem B3127097 : Blo 1624511 3127097 := bstep (se 2 (by rfl) ⟨1172661, by rfl⟩ : syracuseStep 3127097 = 2345323) B2345323
theorem B6174569 : Blo 1624511 6174569 := bstep (se 2 (by rfl) ⟨2315463, by rfl⟩ : syracuseStep 6174569 = 4630927) B4630927
theorem B3135439 : Blo 1624511 3135439 := bstep (se 1 (by rfl) ⟨2351579, by rfl⟩ : syracuseStep 3135439 = 4703159) B4703159
theorem B2439119 : Blo 1624511 2439119 := bstep (se 1 (by rfl) ⟨1829339, by rfl⟩ : syracuseStep 2439119 = 3658679) B3658679
theorem B5486777 : Blo 1624511 5486777 := bstep (se 2 (by rfl) ⟨2057541, by rfl⟩ : syracuseStep 5486777 = 4115083) B4115083
theorem B7813367 : Blo 1624511 7813367 := bstep (se 1 (by rfl) ⟨5860025, by rfl⟩ : syracuseStep 7813367 = 11720051) B11720051
theorem B4626713 : Blo 1624511 4626713 := bstep (se 2 (by rfl) ⟨1735017, by rfl⟩ : syracuseStep 4626713 = 3470035) B3470035
theorem B2742619 : Blo 1624511 2742619 := bstep (se 1 (by rfl) ⟨2056964, by rfl⟩ : syracuseStep 2742619 = 4113929) B4113929
theorem B2439515 : Blo 1624511 2439515 := bstep (se 1 (by rfl) ⟨1829636, by rfl⟩ : syracuseStep 2439515 = 3659273) B3659273
theorem B9255293 : Blo 1624511 9255293 := bstep (se 3 (by rfl) ⟨1735367, by rfl⟩ : syracuseStep 9255293 = 3470735) B3470735
theorem B4168255 : Blo 1624511 4168255 := bstep (se 1 (by rfl) ⟨3126191, by rfl⟩ : syracuseStep 4168255 = 6252383) B6252383
theorem B1735231 : Blo 1624511 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B31660607 : Blo 1624511 31660607 := bstep (se 1 (by rfl) ⟨23745455, by rfl⟩ : syracuseStep 31660607 = 47490911) B47490911
theorem B17578559 : Blo 1624511 17578559 := bstep (se 1 (by rfl) ⟨13183919, by rfl⟩ : syracuseStep 17578559 = 26367839) B26367839
theorem B2439743 : Blo 1624511 2439743 := bstep (se 1 (by rfl) ⟨1829807, by rfl⟩ : syracuseStep 2439743 = 3659615) B3659615
theorem B9378703 : Blo 1624511 9378703 := bstep (se 1 (by rfl) ⟨7034027, by rfl⟩ : syracuseStep 9378703 = 14068055) B14068055
theorem B8231867 : Blo 1624511 8231867 := bstep (se 1 (by rfl) ⟨6173900, by rfl⟩ : syracuseStep 8231867 = 12347801) B12347801
theorem B5209127 : Blo 1624511 5209127 := bstep (se 1 (by rfl) ⟨3906845, by rfl⟩ : syracuseStep 5209127 = 7813691) B7813691
theorem B142540049 : Blo 1624511 142540049 := bstep (se 2 (by rfl) ⟨53452518, by rfl⟩ : syracuseStep 142540049 = 106905037) B106905037
theorem B2743591 : Blo 1624511 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B2604487 : Blo 1624511 2604487 := bstep (se 1 (by rfl) ⟨1953365, by rfl⟩ : syracuseStep 2604487 = 3906731) B3906731
theorem B13188689 : Blo 1624511 13188689 := bstep (se 2 (by rfl) ⟨4945758, by rfl⟩ : syracuseStep 13188689 = 9891517) B9891517
theorem B5488289 : Blo 1624511 5488289 := bstep (se 2 (by rfl) ⟨2058108, by rfl⟩ : syracuseStep 5488289 = 4116217) B4116217
theorem B2744111 : Blo 1624511 2744111 := bstep (se 1 (by rfl) ⟨2058083, by rfl⟩ : syracuseStep 2744111 = 4116167) B4116167
theorem B4628353 : Blo 1624511 4628353 := bstep (se 2 (by rfl) ⟨1735632, by rfl⟩ : syracuseStep 4628353 = 3471265) B3471265
theorem B5488775 : Blo 1624511 5488775 := bstep (se 1 (by rfl) ⟨4116581, by rfl⟩ : syracuseStep 5488775 = 8233163) B8233163
theorem B4112603 : Blo 1624511 4112603 := bstep (se 1 (by rfl) ⟨3084452, by rfl⟩ : syracuseStep 4112603 = 6168905) B6168905
theorem B2056423 : Blo 1624511 2056423 := bstep (se 1 (by rfl) ⟨1542317, by rfl⟩ : syracuseStep 2056423 = 3084635) B3084635
theorem B9388495 : Blo 1624511 9388495 := bstep (se 1 (by rfl) ⟨7041371, by rfl⟩ : syracuseStep 9388495 = 14082743) B14082743
theorem B4694479 : Blo 1624511 4694479 := bstep (se 1 (by rfl) ⟨3520859, by rfl⟩ : syracuseStep 4694479 = 7041719) B7041719
theorem B6947279 : Blo 1624511 6947279 := bstep (se 1 (by rfl) ⟨5210459, by rfl⟩ : syracuseStep 6947279 = 10420919) B10420919
theorem B9257435 : Blo 1624511 9257435 := bstep (se 1 (by rfl) ⟨6943076, by rfl⟩ : syracuseStep 9257435 = 13886153) B13886153
theorem B36135443 : Blo 1624511 36135443 := bstep (se 1 (by rfl) ⟨27101582, by rfl⟩ : syracuseStep 36135443 = 54203165) B54203165
theorem B23765575 : Blo 1624511 23765575 := bstep (se 1 (by rfl) ⟨17824181, by rfl⟩ : syracuseStep 23765575 = 35648363) B35648363
theorem B8225387 : Blo 1624511 8225387 := bstep (se 1 (by rfl) ⟨6169040, by rfl⟩ : syracuseStep 8225387 = 12338081) B12338081
theorem B18506393 : Blo 1624511 18506393 := bstep (se 2 (by rfl) ⟨6939897, by rfl⟩ : syracuseStep 18506393 = 13879795) B13879795
theorem B10420973 : Blo 1624511 10420973 := bstep (se 3 (by rfl) ⟨1953932, by rfl⟩ : syracuseStep 10420973 = 3907865) B3907865
theorem B2057071 : Blo 1624511 2057071 := bstep (se 1 (by rfl) ⟨1542803, by rfl⟩ : syracuseStep 2057071 = 3085607) B3085607
theorem B1827751 : Blo 1624511 1827751 := bstep (se 1 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 1827751 = 2741627) B2741627
theorem B31245533 : Blo 1624511 31245533 := bstep (se 3 (by rfl) ⟨5858537, by rfl⟩ : syracuseStep 31245533 = 11717075) B11717075
theorem B4113737 : Blo 1624511 4113737 := bstep (se 2 (by rfl) ⟨1542651, by rfl⟩ : syracuseStep 4113737 = 3085303) B3085303
theorem B5563721 : Blo 1624511 5563721 := bstep (se 2 (by rfl) ⟨2086395, by rfl⟩ : syracuseStep 5563721 = 4172791) B4172791
theorem B3655187 : Blo 1624511 3655187 := bstep (se 1 (by rfl) ⟨2741390, by rfl⟩ : syracuseStep 3655187 = 5482781) B5482781
theorem B6940241 : Blo 1624511 6940241 := bstep (se 2 (by rfl) ⟨2602590, by rfl⟩ : syracuseStep 6940241 = 5205181) B5205181
theorem B6170195 : Blo 1624511 6170195 := bstep (se 1 (by rfl) ⟨4627646, by rfl⟩ : syracuseStep 6170195 = 9255293) B9255293
theorem B2344631 : Blo 1624511 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B4114273 : Blo 1624511 4114273 := bstep (se 2 (by rfl) ⟨1542852, by rfl⟩ : syracuseStep 4114273 = 3085705) B3085705
theorem B42207095 : Blo 1624511 42207095 := bstep (se 1 (by rfl) ⟨31655321, by rfl⟩ : syracuseStep 42207095 = 63310643) B63310643
theorem B3655871 : Blo 1624511 3655871 := bstep (se 1 (by rfl) ⟨2741903, by rfl⟩ : syracuseStep 3655871 = 5483807) B5483807
theorem B8227007 : Blo 1624511 8227007 := bstep (se 1 (by rfl) ⟨6170255, by rfl⟩ : syracuseStep 8227007 = 12340511) B12340511
theorem B8341799 : Blo 1624511 8341799 := bstep (se 1 (by rfl) ⟨6256349, by rfl⟩ : syracuseStep 8341799 = 12512699) B12512699
theorem B8792459 : Blo 1624511 8792459 := bstep (se 1 (by rfl) ⟨6594344, by rfl⟩ : syracuseStep 8792459 = 13188689) B13188689
theorem B5859809 : Blo 1624511 5859809 := bstep (se 2 (by rfl) ⟨2197428, by rfl⟩ : syracuseStep 5859809 = 4394857) B4394857
theorem B6171137 : Blo 1624511 6171137 := bstep (se 2 (by rfl) ⟨2314176, by rfl⟩ : syracuseStep 6171137 = 4628353) B4628353
theorem B1624603 : Blo 1624511 1624603 := bstep (se 1 (by rfl) ⟨1218452, by rfl⟩ : syracuseStep 1624603 = 2436905) B2436905
theorem B1624607 : Blo 1624511 1624607 := bstep (se 1 (by rfl) ⟨1218455, by rfl⟩ : syracuseStep 1624607 = 2436911) B2436911
theorem B1829407 : Blo 1624511 1829407 := bstep (se 1 (by rfl) ⟨1372055, by rfl⟩ : syracuseStep 1829407 = 2744111) B2744111
theorem B4180585 : Blo 1624511 4180585 := bstep (se 2 (by rfl) ⟨1567719, by rfl⟩ : syracuseStep 4180585 = 3135439) B3135439
theorem B9259667 : Blo 1624511 9259667 := bstep (se 1 (by rfl) ⟨6944750, by rfl⟩ : syracuseStep 9259667 = 13889501) B13889501
theorem B9382583 : Blo 1624511 9382583 := bstep (se 1 (by rfl) ⟨7036937, by rfl⟩ : syracuseStep 9382583 = 14073875) B14073875
theorem B1624923 : Blo 1624511 1624923 := bstep (se 1 (by rfl) ⟨1218692, by rfl⟩ : syracuseStep 1624923 = 2437385) B2437385
theorem B1624991 : Blo 1624511 1624991 := bstep (se 1 (by rfl) ⟨1218743, by rfl⟩ : syracuseStep 1624991 = 2437487) B2437487
theorem B11905987 : Blo 1624511 11905987 := bstep (se 1 (by rfl) ⟨8929490, by rfl⟩ : syracuseStep 11905987 = 17858981) B17858981
theorem B5483483 : Blo 1624511 5483483 := bstep (se 1 (by rfl) ⟨4112612, by rfl⟩ : syracuseStep 5483483 = 8225225) B8225225
theorem B6941659 : Blo 1624511 6941659 := bstep (se 1 (by rfl) ⟨5206244, by rfl⟩ : syracuseStep 6941659 = 10412489) B10412489
theorem B6941675 : Blo 1624511 6941675 := bstep (se 1 (by rfl) ⟨5206256, by rfl⟩ : syracuseStep 6941675 = 10412513) B10412513
theorem B1625135 : Blo 1624511 1625135 := bstep (se 1 (by rfl) ⟨1218851, by rfl⟩ : syracuseStep 1625135 = 2437703) B2437703
theorem B1625159 : Blo 1624511 1625159 := bstep (se 1 (by rfl) ⟨1218869, by rfl⟩ : syracuseStep 1625159 = 2437739) B2437739
theorem B3656825 : Blo 1624511 3656825 := bstep (se 2 (by rfl) ⟨1371309, by rfl⟩ : syracuseStep 3656825 = 2742619) B2742619
theorem B1625311 : Blo 1624511 1625311 := bstep (se 1 (by rfl) ⟨1218983, by rfl⟩ : syracuseStep 1625311 = 2437967) B2437967
theorem B4394207 : Blo 1624511 4394207 := bstep (se 1 (by rfl) ⟨3295655, by rfl⟩ : syracuseStep 4394207 = 6591311) B6591311
theorem B5483753 : Blo 1624511 5483753 := bstep (se 2 (by rfl) ⟨2056407, by rfl⟩ : syracuseStep 5483753 = 4112815) B4112815
theorem B39538043 : Blo 1624511 39538043 := bstep (se 1 (by rfl) ⟨29653532, by rfl⟩ : syracuseStep 39538043 = 59307065) B59307065
theorem B5557673 : Blo 1624511 5557673 := bstep (se 2 (by rfl) ⟨2084127, by rfl⟩ : syracuseStep 5557673 = 4168255) B4168255
theorem B2313641 : Blo 1624511 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B5205437 : Blo 1624511 5205437 := bstep (se 3 (by rfl) ⟨976019, by rfl⟩ : syracuseStep 5205437 = 1952039) B1952039
theorem B1625575 : Blo 1624511 1625575 := bstep (se 1 (by rfl) ⟨1219181, by rfl⟩ : syracuseStep 1625575 = 2438363) B2438363
theorem B5484023 : Blo 1624511 5484023 := bstep (se 1 (by rfl) ⟨4113017, by rfl⟩ : syracuseStep 5484023 = 8226035) B8226035
theorem B9252377 : Blo 1624511 9252377 := bstep (se 2 (by rfl) ⟨3469641, by rfl⟩ : syracuseStep 9252377 = 6939283) B6939283
theorem B1625691 : Blo 1624511 1625691 := bstep (se 1 (by rfl) ⟨1219268, by rfl⟩ : syracuseStep 1625691 = 2438537) B2438537
theorem B5279357 : Blo 1624511 5279357 := bstep (se 3 (by rfl) ⟨989879, by rfl⟩ : syracuseStep 5279357 = 1979759) B1979759
theorem B3657491 : Blo 1624511 3657491 := bstep (se 1 (by rfl) ⟨2743118, by rfl⟩ : syracuseStep 3657491 = 5486237) B5486237
theorem B2436935 : Blo 1624511 2436935 := bstep (se 1 (by rfl) ⟨1827701, by rfl⟩ : syracuseStep 2436935 = 3655403) B3655403
theorem B1625927 : Blo 1624511 1625927 := bstep (se 1 (by rfl) ⟨1219445, by rfl⟩ : syracuseStep 1625927 = 2438891) B2438891
theorem B12504937 : Blo 1624511 12504937 := bstep (se 2 (by rfl) ⟨4689351, by rfl⟩ : syracuseStep 12504937 = 9378703) B9378703
theorem B2437019 : Blo 1624511 2437019 := bstep (se 1 (by rfl) ⟨1827764, by rfl⟩ : syracuseStep 2437019 = 3655529) B3655529
theorem B4116379 : Blo 1624511 4116379 := bstep (se 1 (by rfl) ⟨3087284, by rfl⟩ : syracuseStep 4116379 = 6174569) B6174569
theorem B10694573 : Blo 1624511 10694573 := bstep (se 3 (by rfl) ⟨2005232, by rfl⟩ : syracuseStep 10694573 = 4010465) B4010465
theorem B1626079 : Blo 1624511 1626079 := bstep (se 1 (by rfl) ⟨1219559, by rfl⟩ : syracuseStep 1626079 = 2439119) B2439119
theorem B3657851 : Blo 1624511 3657851 := bstep (se 1 (by rfl) ⟨2743388, by rfl⟩ : syracuseStep 3657851 = 5486777) B5486777
theorem B3084475 : Blo 1624511 3084475 := bstep (se 1 (by rfl) ⟨2313356, by rfl⟩ : syracuseStep 3084475 = 4626713) B4626713
theorem B1626343 : Blo 1624511 1626343 := bstep (se 1 (by rfl) ⟨1219757, by rfl⟩ : syracuseStep 1626343 = 2439515) B2439515
theorem B13889879 : Blo 1624511 13889879 := bstep (se 1 (by rfl) ⟨10417409, by rfl⟩ : syracuseStep 13889879 = 20834819) B20834819
theorem B21107071 : Blo 1624511 21107071 := bstep (se 1 (by rfl) ⟨15830303, by rfl⟩ : syracuseStep 21107071 = 31660607) B31660607
theorem B11719039 : Blo 1624511 11719039 := bstep (se 1 (by rfl) ⟨8789279, by rfl⟩ : syracuseStep 11719039 = 17578559) B17578559
theorem B1626495 : Blo 1624511 1626495 := bstep (se 1 (by rfl) ⟨1219871, by rfl⟩ : syracuseStep 1626495 = 2439743) B2439743
theorem B3658121 : Blo 1624511 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B16691609 : Blo 1624511 16691609 := bstep (se 2 (by rfl) ⟨6259353, by rfl⟩ : syracuseStep 16691609 = 12518707) B12518707
theorem B2437583 : Blo 1624511 2437583 := bstep (se 1 (by rfl) ⟨1828187, by rfl⟩ : syracuseStep 2437583 = 3656375) B3656375
theorem B10416613 : Blo 1624511 10416613 := bstep (se 4 (by rfl) ⟨976557, by rfl⟩ : syracuseStep 10416613 = 1953115) B1953115
theorem B2437625 : Blo 1624511 2437625 := bstep (se 2 (by rfl) ⟨914109, by rfl⟩ : syracuseStep 2437625 = 1828219) B1828219
theorem B5485049 : Blo 1624511 5485049 := bstep (se 2 (by rfl) ⟨2056893, by rfl⟩ : syracuseStep 5485049 = 4113787) B4113787
theorem B6943315 : Blo 1624511 6943315 := bstep (se 1 (by rfl) ⟨5207486, by rfl⟩ : syracuseStep 6943315 = 10414973) B10414973
theorem B2437727 : Blo 1624511 2437727 := bstep (se 1 (by rfl) ⟨1828295, by rfl⟩ : syracuseStep 2437727 = 3656591) B3656591
theorem B2781791 : Blo 1624511 2781791 := bstep (se 1 (by rfl) ⟨2086343, by rfl⟩ : syracuseStep 2781791 = 4172687) B4172687
theorem B3084961 : Blo 1624511 3084961 := bstep (se 2 (by rfl) ⟨1156860, by rfl⟩ : syracuseStep 3084961 = 2313721) B2313721
theorem B5485319 : Blo 1624511 5485319 := bstep (se 1 (by rfl) ⟨4113989, by rfl⟩ : syracuseStep 5485319 = 8227979) B8227979
theorem B5485373 : Blo 1624511 5485373 := bstep (se 3 (by rfl) ⟨1028507, by rfl⟩ : syracuseStep 5485373 = 2057015) B2057015
theorem B8229761 : Blo 1624511 8229761 := bstep (se 2 (by rfl) ⟨3086160, by rfl⟩ : syracuseStep 8229761 = 6172321) B6172321
theorem B2438207 : Blo 1624511 2438207 := bstep (se 1 (by rfl) ⟨1828655, by rfl⟩ : syracuseStep 2438207 = 3657311) B3657311
theorem B2438249 : Blo 1624511 2438249 := bstep (se 2 (by rfl) ⟨914343, by rfl⟩ : syracuseStep 2438249 = 1828687) B1828687
theorem B3658859 : Blo 1624511 3658859 := bstep (se 1 (by rfl) ⟨2744144, by rfl⟩ : syracuseStep 3658859 = 5488289) B5488289
theorem B5207179 : Blo 1624511 5207179 := bstep (se 1 (by rfl) ⟨3905384, by rfl⟩ : syracuseStep 5207179 = 7810769) B7810769
theorem B9254087 : Blo 1624511 9254087 := bstep (se 1 (by rfl) ⟨6940565, by rfl⟩ : syracuseStep 9254087 = 13881131) B13881131
theorem B2438351 : Blo 1624511 2438351 := bstep (se 1 (by rfl) ⟨1828763, by rfl⟩ : syracuseStep 2438351 = 3657527) B3657527
theorem B31241537 : Blo 1624511 31241537 := bstep (se 2 (by rfl) ⟨11715576, by rfl⟩ : syracuseStep 31241537 = 23431153) B23431153
theorem B3126683 : Blo 1624511 3126683 := bstep (se 1 (by rfl) ⟨2345012, by rfl⟩ : syracuseStep 3126683 = 4690025) B4690025
theorem B2438555 : Blo 1624511 2438555 := bstep (se 1 (by rfl) ⟨1828916, by rfl⟩ : syracuseStep 2438555 = 3657833) B3657833
theorem B9885115 : Blo 1624511 9885115 := bstep (se 1 (by rfl) ⟨7413836, by rfl⟩ : syracuseStep 9885115 = 14827673) B14827673
theorem B2438777 : Blo 1624511 2438777 := bstep (se 2 (by rfl) ⟨914541, by rfl⟩ : syracuseStep 2438777 = 1829083) B1829083
theorem B8230571 : Blo 1624511 8230571 := bstep (se 1 (by rfl) ⟨6172928, by rfl⟩ : syracuseStep 8230571 = 12345857) B12345857
theorem B3659435 : Blo 1624511 3659435 := bstep (se 1 (by rfl) ⟨2744576, by rfl⟩ : syracuseStep 3659435 = 5489153) B5489153
theorem B2438879 : Blo 1624511 2438879 := bstep (se 1 (by rfl) ⟨1829159, by rfl⟩ : syracuseStep 2438879 = 3658319) B3658319
theorem B2602783 : Blo 1624511 2602783 := bstep (se 1 (by rfl) ⟨1952087, by rfl⟩ : syracuseStep 2602783 = 3904175) B3904175
theorem B2742079 : Blo 1624511 2742079 := bstep (se 1 (by rfl) ⟨2056559, by rfl⟩ : syracuseStep 2742079 = 4113119) B4113119
theorem B5486399 : Blo 1624511 5486399 := bstep (se 1 (by rfl) ⟨4114799, by rfl⟩ : syracuseStep 5486399 = 8229599) B8229599
theorem B2438975 : Blo 1624511 2438975 := bstep (se 1 (by rfl) ⟨1829231, by rfl⟩ : syracuseStep 2438975 = 3658463) B3658463
theorem B2439143 : Blo 1624511 2439143 := bstep (se 1 (by rfl) ⟨1829357, by rfl⟩ : syracuseStep 2439143 = 3658715) B3658715
theorem B8230895 : Blo 1624511 8230895 := bstep (se 1 (by rfl) ⟨6173171, by rfl⟩ : syracuseStep 8230895 = 12346343) B12346343
theorem B2439161 : Blo 1624511 2439161 := bstep (se 2 (by rfl) ⟨914685, by rfl⟩ : syracuseStep 2439161 = 1829371) B1829371
theorem B3086419 : Blo 1624511 3086419 := bstep (se 1 (by rfl) ⟨2314814, by rfl⟩ : syracuseStep 3086419 = 4629629) B4629629
theorem B2439263 : Blo 1624511 2439263 := bstep (se 1 (by rfl) ⟨1829447, by rfl⟩ : syracuseStep 2439263 = 3658895) B3658895
theorem B2439323 : Blo 1624511 2439323 := bstep (se 1 (by rfl) ⟨1829492, by rfl⟩ : syracuseStep 2439323 = 3658985) B3658985
theorem B2439359 : Blo 1624511 2439359 := bstep (se 1 (by rfl) ⟨1829519, by rfl⟩ : syracuseStep 2439359 = 3659039) B3659039
theorem B2439401 : Blo 1624511 2439401 := bstep (se 2 (by rfl) ⟨914775, by rfl⟩ : syracuseStep 2439401 = 1829551) B1829551
theorem B28531223 : Blo 1624511 28531223 := bstep (se 1 (by rfl) ⟨21398417, by rfl⟩ : syracuseStep 28531223 = 42796835) B42796835
theorem B2439707 : Blo 1624511 2439707 := bstep (se 1 (by rfl) ⟨1829780, by rfl⟩ : syracuseStep 2439707 = 3659561) B3659561
theorem B2742815 : Blo 1624511 2742815 := bstep (se 1 (by rfl) ⟨2057111, by rfl⟩ : syracuseStep 2742815 = 4114223) B4114223
theorem B2742889 : Blo 1624511 2742889 := bstep (se 2 (by rfl) ⟨1028583, by rfl⟩ : syracuseStep 2742889 = 2057167) B2057167
theorem B5208911 : Blo 1624511 5208911 := bstep (se 1 (by rfl) ⟨3906683, by rfl⟩ : syracuseStep 5208911 = 7813367) B7813367
theorem B2743247 : Blo 1624511 2743247 := bstep (se 1 (by rfl) ⟨2057435, by rfl⟩ : syracuseStep 2743247 = 4114871) B4114871
theorem B9255977 : Blo 1624511 9255977 := bstep (se 2 (by rfl) ⟨3470991, by rfl⟩ : syracuseStep 9255977 = 6941983) B6941983
theorem B3472649 : Blo 1624511 3472649 := bstep (se 2 (by rfl) ⟨1302243, by rfl⟩ : syracuseStep 3472649 = 2604487) B2604487
theorem B5487911 : Blo 1624511 5487911 := bstep (se 1 (by rfl) ⟨4115933, by rfl⟩ : syracuseStep 5487911 = 8231867) B8231867
theorem B3472751 : Blo 1624511 3472751 := bstep (se 1 (by rfl) ⟨2604563, by rfl⟩ : syracuseStep 3472751 = 5209127) B5209127
theorem B8232353 : Blo 1624511 8232353 := bstep (se 2 (by rfl) ⟨3087132, by rfl⟩ : syracuseStep 8232353 = 6174265) B6174265
theorem B8338925 : Blo 1624511 8338925 := bstep (se 3 (by rfl) ⟨1563548, by rfl⟩ : syracuseStep 8338925 = 3127097) B3127097
theorem B95026699 : Blo 1624511 95026699 := bstep (se 1 (by rfl) ⟨71270024, by rfl⟩ : syracuseStep 95026699 = 142540049) B142540049
theorem B2743915 : Blo 1624511 2743915 := bstep (se 1 (by rfl) ⟨2057936, by rfl⟩ : syracuseStep 2743915 = 4115873) B4115873
theorem B2744185 : Blo 1624511 2744185 := bstep (se 2 (by rfl) ⟨1029069, by rfl⟩ : syracuseStep 2744185 = 2058139) B2058139
theorem B2744219 : Blo 1624511 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B5861639 : Blo 1624511 5861639 := bstep (se 1 (by rfl) ⟨4396229, by rfl⟩ : syracuseStep 5861639 = 8792459) B8792459
theorem B4112633 : Blo 1624511 4112633 := bstep (se 2 (by rfl) ⟨1542237, by rfl⟩ : syracuseStep 4112633 = 3084475) B3084475
theorem B12337595 : Blo 1624511 12337595 := bstep (se 1 (by rfl) ⟨9253196, by rfl⟩ : syracuseStep 12337595 = 18506393) B18506393
theorem B6947315 : Blo 1624511 6947315 := bstep (se 1 (by rfl) ⟨5210486, by rfl⟩ : syracuseStep 6947315 = 10420973) B10420973
theorem B12517993 : Blo 1624511 12517993 := bstep (se 2 (by rfl) ⟨4694247, by rfl⟩ : syracuseStep 12517993 = 9388495) B9388495
theorem B31687433 : Blo 1624511 31687433 := bstep (se 2 (by rfl) ⟨11882787, by rfl⟩ : syracuseStep 31687433 = 23765575) B23765575
theorem B9257753 : Blo 1624511 9257753 := bstep (se 2 (by rfl) ⟨3471657, by rfl⟩ : syracuseStep 9257753 = 6943315) B6943315
theorem B6169391 : Blo 1624511 6169391 := bstep (se 1 (by rfl) ⟨4627043, by rfl⟩ : syracuseStep 6169391 = 9254087) B9254087
theorem B4113281 : Blo 1624511 4113281 := bstep (se 2 (by rfl) ⟨1542480, by rfl⟩ : syracuseStep 4113281 = 3084961) B3084961
theorem B4113463 : Blo 1624511 4113463 := bstep (se 1 (by rfl) ⟨3085097, by rfl⟩ : syracuseStep 4113463 = 6170195) B6170195
theorem B6169709 : Blo 1624511 6169709 := bstep (se 3 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 6169709 = 2313641) B2313641
theorem B4114091 : Blo 1624511 4114091 := bstep (se 1 (by rfl) ⟨3085568, by rfl⟩ : syracuseStep 4114091 = 6171137) B6171137
theorem B1828543 : Blo 1624511 1828543 := bstep (se 1 (by rfl) ⟨1371407, by rfl⟩ : syracuseStep 1828543 = 2742815) B2742815
theorem B6252349 : Blo 1624511 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B1828831 : Blo 1624511 1828831 := bstep (se 1 (by rfl) ⟨1371623, by rfl⟩ : syracuseStep 1828831 = 2743247) B2743247
theorem B3655655 : Blo 1624511 3655655 := bstep (se 1 (by rfl) ⟨2741741, by rfl⟩ : syracuseStep 3655655 = 5483483) B5483483
theorem B6170651 : Blo 1624511 6170651 := bstep (se 1 (by rfl) ⟨4627988, by rfl⟩ : syracuseStep 6170651 = 9255977) B9255977
theorem B3655835 : Blo 1624511 3655835 := bstep (se 1 (by rfl) ⟨2741876, by rfl⟩ : syracuseStep 3655835 = 5483753) B5483753
theorem B3705115 : Blo 1624511 3705115 := bstep (se 1 (by rfl) ⟨2778836, by rfl⟩ : syracuseStep 3705115 = 5557673) B5557673
theorem B3656015 : Blo 1624511 3656015 := bstep (se 1 (by rfl) ⟨2742011, by rfl⟩ : syracuseStep 3656015 = 5484023) B5484023
theorem B25037221 : Blo 1624511 25037221 := bstep (se 4 (by rfl) ⟨2347239, by rfl⟩ : syracuseStep 25037221 = 4694479) B4694479
theorem B3656105 : Blo 1624511 3656105 := bstep (se 2 (by rfl) ⟨1371039, by rfl⟩ : syracuseStep 3656105 = 2742079) B2742079
theorem B16673249 : Blo 1624511 16673249 := bstep (se 2 (by rfl) ⟨6252468, by rfl⟩ : syracuseStep 16673249 = 12504937) B12504937
theorem B1624623 : Blo 1624511 1624623 := bstep (se 1 (by rfl) ⟨1218467, by rfl⟩ : syracuseStep 1624623 = 2436935) B2436935
theorem B1624679 : Blo 1624511 1624679 := bstep (se 1 (by rfl) ⟨1218509, by rfl⟩ : syracuseStep 1624679 = 2437019) B2437019
theorem B1829479 : Blo 1624511 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B7129715 : Blo 1624511 7129715 := bstep (se 1 (by rfl) ⟨5347286, by rfl⟩ : syracuseStep 7129715 = 10694573) B10694573
theorem B506809061 : Blo 1624511 506809061 := bstep (se 4 (by rfl) ⟨47513349, by rfl⟩ : syracuseStep 506809061 = 95026699) B95026699
theorem B4115225 : Blo 1624511 4115225 := bstep (se 2 (by rfl) ⟨1543209, by rfl⟩ : syracuseStep 4115225 = 3086419) B3086419
theorem B9259919 : Blo 1624511 9259919 := bstep (se 1 (by rfl) ⟨6944939, by rfl⟩ : syracuseStep 9259919 = 13889879) B13889879
theorem B11127739 : Blo 1624511 11127739 := bstep (se 1 (by rfl) ⟨8345804, by rfl⟩ : syracuseStep 11127739 = 16691609) B16691609
theorem B1625055 : Blo 1624511 1625055 := bstep (se 1 (by rfl) ⟨1218791, by rfl⟩ : syracuseStep 1625055 = 2437583) B2437583
theorem B4631519 : Blo 1624511 4631519 := bstep (se 1 (by rfl) ⟨3473639, by rfl⟩ : syracuseStep 4631519 = 6947279) B6947279
theorem B6171623 : Blo 1624511 6171623 := bstep (se 1 (by rfl) ⟨4628717, by rfl⟩ : syracuseStep 6171623 = 9257435) B9257435
theorem B1625083 : Blo 1624511 1625083 := bstep (se 1 (by rfl) ⟨1218812, by rfl⟩ : syracuseStep 1625083 = 2437625) B2437625
theorem B3656699 : Blo 1624511 3656699 := bstep (se 1 (by rfl) ⟨2742524, by rfl⟩ : syracuseStep 3656699 = 5485049) B5485049
theorem B1625151 : Blo 1624511 1625151 := bstep (se 1 (by rfl) ⟨1218863, by rfl⟩ : syracuseStep 1625151 = 2437727) B2437727
theorem B1854527 : Blo 1624511 1854527 := bstep (se 1 (by rfl) ⟨1390895, by rfl⟩ : syracuseStep 1854527 = 2781791) B2781791
theorem B5483591 : Blo 1624511 5483591 := bstep (se 1 (by rfl) ⟨4112693, by rfl⟩ : syracuseStep 5483591 = 8225387) B8225387
theorem B28142761 : Blo 1624511 28142761 := bstep (se 2 (by rfl) ⟨10553535, by rfl⟩ : syracuseStep 28142761 = 21107071) B21107071
theorem B15625385 : Blo 1624511 15625385 := bstep (se 2 (by rfl) ⟨5859519, by rfl⟩ : syracuseStep 15625385 = 11719039) B11719039
theorem B3656879 : Blo 1624511 3656879 := bstep (se 1 (by rfl) ⟨2742659, by rfl⟩ : syracuseStep 3656879 = 5485319) B5485319
theorem B3656915 : Blo 1624511 3656915 := bstep (se 1 (by rfl) ⟨2742686, by rfl⟩ : syracuseStep 3656915 = 5485373) B5485373
theorem B11717885 : Blo 1624511 11717885 := bstep (se 3 (by rfl) ⟨2197103, by rfl⟩ : syracuseStep 11717885 = 4394207) B4394207
theorem B13888817 : Blo 1624511 13888817 := bstep (se 2 (by rfl) ⟨5208306, by rfl⟩ : syracuseStep 13888817 = 10416613) B10416613
theorem B1625471 : Blo 1624511 1625471 := bstep (se 1 (by rfl) ⟨1219103, by rfl⟩ : syracuseStep 1625471 = 2438207) B2438207
theorem B1625499 : Blo 1624511 1625499 := bstep (se 1 (by rfl) ⟨1219124, by rfl⟩ : syracuseStep 1625499 = 2438249) B2438249
theorem B22244797 : Blo 1624511 22244797 := bstep (se 3 (by rfl) ⟨4170899, by rfl⟩ : syracuseStep 22244797 = 8341799) B8341799
theorem B1625567 : Blo 1624511 1625567 := bstep (se 1 (by rfl) ⟨1219175, by rfl⟩ : syracuseStep 1625567 = 2438351) B2438351
theorem B3657185 : Blo 1624511 3657185 := bstep (se 2 (by rfl) ⟨1371444, by rfl⟩ : syracuseStep 3657185 = 2742889) B2742889
theorem B20827691 : Blo 1624511 20827691 := bstep (se 1 (by rfl) ⟨15620768, by rfl⟩ : syracuseStep 20827691 = 31241537) B31241537
theorem B2084455 : Blo 1624511 2084455 := bstep (se 1 (by rfl) ⟨1563341, by rfl⟩ : syracuseStep 2084455 = 3126683) B3126683
theorem B1625703 : Blo 1624511 1625703 := bstep (se 1 (by rfl) ⟨1219277, by rfl⟩ : syracuseStep 1625703 = 2438555) B2438555
theorem B9260669 : Blo 1624511 9260669 := bstep (se 3 (by rfl) ⟨1736375, by rfl⟩ : syracuseStep 9260669 = 3472751) B3472751
theorem B2436791 : Blo 1624511 2436791 := bstep (se 1 (by rfl) ⟨1827593, by rfl⟩ : syracuseStep 2436791 = 3655187) B3655187
theorem B1625851 : Blo 1624511 1625851 := bstep (se 1 (by rfl) ⟨1219388, by rfl⟩ : syracuseStep 1625851 = 2438777) B2438777
theorem B1625919 : Blo 1624511 1625919 := bstep (se 1 (by rfl) ⟨1219439, by rfl⟩ : syracuseStep 1625919 = 2438879) B2438879
theorem B3657599 : Blo 1624511 3657599 := bstep (se 1 (by rfl) ⟨2743199, by rfl⟩ : syracuseStep 3657599 = 5486399) B5486399
theorem B1625983 : Blo 1624511 1625983 := bstep (se 1 (by rfl) ⟨1219487, by rfl⟩ : syracuseStep 1625983 = 2438975) B2438975
theorem B2437001 : Blo 1624511 2437001 := bstep (se 2 (by rfl) ⟨913875, by rfl⟩ : syracuseStep 2437001 = 1827751) B1827751
theorem B1626095 : Blo 1624511 1626095 := bstep (se 1 (by rfl) ⟨1219571, by rfl⟩ : syracuseStep 1626095 = 2439143) B2439143
theorem B1626107 : Blo 1624511 1626107 := bstep (se 1 (by rfl) ⟨1219580, by rfl⟩ : syracuseStep 1626107 = 2439161) B2439161
theorem B1626175 : Blo 1624511 1626175 := bstep (se 1 (by rfl) ⟨1219631, by rfl⟩ : syracuseStep 1626175 = 2439263) B2439263
theorem B1626215 : Blo 1624511 1626215 := bstep (se 1 (by rfl) ⟨1219661, by rfl⟩ : syracuseStep 1626215 = 2439323) B2439323
theorem B2437247 : Blo 1624511 2437247 := bstep (se 1 (by rfl) ⟨1827935, by rfl⟩ : syracuseStep 2437247 = 3655871) B3655871
theorem B5484671 : Blo 1624511 5484671 := bstep (se 1 (by rfl) ⟨4113503, by rfl⟩ : syracuseStep 5484671 = 8227007) B8227007
theorem B1626239 : Blo 1624511 1626239 := bstep (se 1 (by rfl) ⟨1219679, by rfl⟩ : syracuseStep 1626239 = 2439359) B2439359
theorem B1626267 : Blo 1624511 1626267 := bstep (se 1 (by rfl) ⟨1219700, by rfl⟩ : syracuseStep 1626267 = 2439401) B2439401
theorem B6942905 : Blo 1624511 6942905 := bstep (se 2 (by rfl) ⟨2603589, by rfl⟩ : syracuseStep 6942905 = 5207179) B5207179
theorem B1626471 : Blo 1624511 1626471 := bstep (se 1 (by rfl) ⟨1219853, by rfl⟩ : syracuseStep 1626471 = 2439707) B2439707
theorem B6173111 : Blo 1624511 6173111 := bstep (se 1 (by rfl) ⟨4629833, by rfl⟩ : syracuseStep 6173111 = 9259667) B9259667
theorem B6255055 : Blo 1624511 6255055 := bstep (se 1 (by rfl) ⟨4691291, by rfl⟩ : syracuseStep 6255055 = 9382583) B9382583
theorem B2437883 : Blo 1624511 2437883 := bstep (se 1 (by rfl) ⟨1828412, by rfl⟩ : syracuseStep 2437883 = 3656825) B3656825
theorem B3658553 : Blo 1624511 3658553 := bstep (se 2 (by rfl) ⟨1371957, by rfl⟩ : syracuseStep 3658553 = 2743915) B2743915
theorem B2315099 : Blo 1624511 2315099 := bstep (se 1 (by rfl) ⟨1736324, by rfl⟩ : syracuseStep 2315099 = 3472649) B3472649
theorem B3658607 : Blo 1624511 3658607 := bstep (se 1 (by rfl) ⟨2743955, by rfl⟩ : syracuseStep 3658607 = 5487911) B5487911
theorem B26358695 : Blo 1624511 26358695 := bstep (se 1 (by rfl) ⟨19769021, by rfl⟩ : syracuseStep 26358695 = 39538043) B39538043
theorem B3470291 : Blo 1624511 3470291 := bstep (se 1 (by rfl) ⟨2602718, by rfl⟩ : syracuseStep 3470291 = 5205437) B5205437
theorem B5559283 : Blo 1624511 5559283 := bstep (se 1 (by rfl) ⟨4169462, by rfl⟩ : syracuseStep 5559283 = 8338925) B8338925
theorem B3470377 : Blo 1624511 3470377 := bstep (se 2 (by rfl) ⟨1301391, by rfl⟩ : syracuseStep 3470377 = 2602783) B2602783
theorem B3519571 : Blo 1624511 3519571 := bstep (se 1 (by rfl) ⟨2639678, by rfl⟩ : syracuseStep 3519571 = 5279357) B5279357
theorem B5485697 : Blo 1624511 5485697 := bstep (se 2 (by rfl) ⟨2057136, by rfl⟩ : syracuseStep 5485697 = 4114273) B4114273
theorem B3658913 : Blo 1624511 3658913 := bstep (se 2 (by rfl) ⟨1372092, by rfl⟩ : syracuseStep 3658913 = 2744185) B2744185
theorem B2438327 : Blo 1624511 2438327 := bstep (se 1 (by rfl) ⟨1828745, by rfl⟩ : syracuseStep 2438327 = 3657491) B3657491
theorem B2438567 : Blo 1624511 2438567 := bstep (se 1 (by rfl) ⟨1828925, by rfl⟩ : syracuseStep 2438567 = 3657851) B3657851
theorem B3659183 : Blo 1624511 3659183 := bstep (se 1 (by rfl) ⟨2744387, by rfl⟩ : syracuseStep 3659183 = 5488775) B5488775
theorem B2741735 : Blo 1624511 2741735 := bstep (se 1 (by rfl) ⟨2056301, by rfl⟩ : syracuseStep 2741735 = 4112603) B4112603
theorem B2438747 : Blo 1624511 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B2741897 : Blo 1624511 2741897 := bstep (se 2 (by rfl) ⟨1028211, by rfl⟩ : syracuseStep 2741897 = 2056423) B2056423
theorem B24090295 : Blo 1624511 24090295 := bstep (se 1 (by rfl) ⟨18067721, by rfl⟩ : syracuseStep 24090295 = 36135443) B36135443
theorem B5486507 : Blo 1624511 5486507 := bstep (se 1 (by rfl) ⟨4114880, by rfl⟩ : syracuseStep 5486507 = 8229761) B8229761
theorem B2439209 : Blo 1624511 2439209 := bstep (se 2 (by rfl) ⟨914703, by rfl⟩ : syracuseStep 2439209 = 1829407) B1829407
theorem B2439239 : Blo 1624511 2439239 := bstep (se 1 (by rfl) ⟨1829429, by rfl⟩ : syracuseStep 2439239 = 3658859) B3658859
theorem B356743253 : Blo 1624511 356743253 := bstep (se 8 (by rfl) ⟨2090292, by rfl⟩ : syracuseStep 356743253 = 4180585) B4180585
theorem B20830355 : Blo 1624511 20830355 := bstep (se 1 (by rfl) ⟨15622766, by rfl⟩ : syracuseStep 20830355 = 31245533) B31245533
theorem B2742491 : Blo 1624511 2742491 := bstep (se 1 (by rfl) ⟨2056868, by rfl⟩ : syracuseStep 2742491 = 4113737) B4113737
theorem B3709147 : Blo 1624511 3709147 := bstep (se 1 (by rfl) ⟨2781860, by rfl⟩ : syracuseStep 3709147 = 5563721) B5563721
theorem B4626827 : Blo 1624511 4626827 := bstep (se 1 (by rfl) ⟨3470120, by rfl⟩ : syracuseStep 4626827 = 6940241) B6940241
theorem B5487047 : Blo 1624511 5487047 := bstep (se 1 (by rfl) ⟨4115285, by rfl⟩ : syracuseStep 5487047 = 8230571) B8230571
theorem B2439623 : Blo 1624511 2439623 := bstep (se 1 (by rfl) ⟨1829717, by rfl⟩ : syracuseStep 2439623 = 3659435) B3659435
theorem B2742761 : Blo 1624511 2742761 := bstep (se 2 (by rfl) ⟨1028535, by rfl⟩ : syracuseStep 2742761 = 2057071) B2057071
theorem B28138063 : Blo 1624511 28138063 := bstep (se 1 (by rfl) ⟨21103547, by rfl⟩ : syracuseStep 28138063 = 42207095) B42207095
theorem B15874649 : Blo 1624511 15874649 := bstep (se 2 (by rfl) ⟨5952993, by rfl⟩ : syracuseStep 15874649 = 11905987) B11905987
theorem B9255545 : Blo 1624511 9255545 := bstep (se 2 (by rfl) ⟨3470829, by rfl⟩ : syracuseStep 9255545 = 6941659) B6941659
theorem B5487263 : Blo 1624511 5487263 := bstep (se 1 (by rfl) ⟨4115447, by rfl⟩ : syracuseStep 5487263 = 8230895) B8230895
theorem B3906539 : Blo 1624511 3906539 := bstep (se 1 (by rfl) ⟨2929904, by rfl⟩ : syracuseStep 3906539 = 5859809) B5859809
theorem B19020815 : Blo 1624511 19020815 := bstep (se 1 (by rfl) ⟨14265611, by rfl⟩ : syracuseStep 19020815 = 28531223) B28531223
theorem B3472607 : Blo 1624511 3472607 := bstep (se 1 (by rfl) ⟨2604455, by rfl⟩ : syracuseStep 3472607 = 5208911) B5208911
theorem B13180153 : Blo 1624511 13180153 := bstep (se 2 (by rfl) ⟨4942557, by rfl⟩ : syracuseStep 13180153 = 9885115) B9885115
theorem B4627783 : Blo 1624511 4627783 := bstep (se 1 (by rfl) ⟨3470837, by rfl⟩ : syracuseStep 4627783 = 6941675) B6941675
theorem B5488235 : Blo 1624511 5488235 := bstep (se 1 (by rfl) ⟨4116176, by rfl⟩ : syracuseStep 5488235 = 8232353) B8232353
theorem B6168251 : Blo 1624511 6168251 := bstep (se 1 (by rfl) ⟨4626188, by rfl⟩ : syracuseStep 6168251 = 9252377) B9252377
theorem B5488505 : Blo 1624511 5488505 := bstep (se 2 (by rfl) ⟨2058189, by rfl⟩ : syracuseStep 5488505 = 4116379) B4116379
theorem B4628603 : Blo 1624511 4628603 := bstep (se 1 (by rfl) ⟨3471452, by rfl⟩ : syracuseStep 4628603 = 6942905) B6942905
theorem B3907759 : Blo 1624511 3907759 := bstep (se 1 (by rfl) ⟨2930819, by rfl⟩ : syracuseStep 3907759 = 5861639) B5861639
theorem B8225063 : Blo 1624511 8225063 := bstep (se 1 (by rfl) ⟨6168797, by rfl⟩ : syracuseStep 8225063 = 12337595) B12337595
theorem B4940153 : Blo 1624511 4940153 := bstep (se 2 (by rfl) ⟨1852557, by rfl⟩ : syracuseStep 4940153 = 3705115) B3705115
theorem B4112927 : Blo 1624511 4112927 := bstep (se 1 (by rfl) ⟨3084695, by rfl⟩ : syracuseStep 4112927 = 6169391) B6169391
theorem B33382961 : Blo 1624511 33382961 := bstep (se 2 (by rfl) ⟨12518610, by rfl⟩ : syracuseStep 33382961 = 25037221) B25037221
theorem B17572463 : Blo 1624511 17572463 := bstep (se 1 (by rfl) ⟨13179347, by rfl⟩ : syracuseStep 17572463 = 26358695) B26358695
theorem B4113139 : Blo 1624511 4113139 := bstep (se 1 (by rfl) ⟨3084854, by rfl⟩ : syracuseStep 4113139 = 6169709) B6169709
theorem B1827823 : Blo 1624511 1827823 := bstep (se 1 (by rfl) ⟨1370867, by rfl⟩ : syracuseStep 1827823 = 2741735) B2741735
theorem B1827931 : Blo 1624511 1827931 := bstep (se 1 (by rfl) ⟨1370948, by rfl⟩ : syracuseStep 1827931 = 2741897) B2741897
theorem B14836985 : Blo 1624511 14836985 := bstep (se 2 (by rfl) ⟨5563869, by rfl⟩ : syracuseStep 14836985 = 11127739) B11127739
theorem B4113767 : Blo 1624511 4113767 := bstep (se 1 (by rfl) ⟨3085325, by rfl⟩ : syracuseStep 4113767 = 6170651) B6170651
theorem B13886903 : Blo 1624511 13886903 := bstep (se 1 (by rfl) ⟨10415177, by rfl⟩ : syracuseStep 13886903 = 20830355) B20830355
theorem B1828327 : Blo 1624511 1828327 := bstep (se 1 (by rfl) ⟨1371245, by rfl⟩ : syracuseStep 1828327 = 2742491) B2742491
theorem B1828507 : Blo 1624511 1828507 := bstep (se 1 (by rfl) ⟨1371380, by rfl⟩ : syracuseStep 1828507 = 2742761) B2742761
theorem B17573537 : Blo 1624511 17573537 := bstep (se 2 (by rfl) ⟨6590076, by rfl⟩ : syracuseStep 17573537 = 13180153) B13180153
theorem B6170363 : Blo 1624511 6170363 := bstep (se 1 (by rfl) ⟨4627772, by rfl⟩ : syracuseStep 6170363 = 9255545) B9255545
theorem B6170377 : Blo 1624511 6170377 := bstep (se 2 (by rfl) ⟨2313891, by rfl⟩ : syracuseStep 6170377 = 4627783) B4627783
theorem B337872707 : Blo 1624511 337872707 := bstep (se 1 (by rfl) ⟨253404530, by rfl⟩ : syracuseStep 337872707 = 506809061) B506809061
theorem B4114415 : Blo 1624511 4114415 := bstep (se 1 (by rfl) ⟨3085811, by rfl⟩ : syracuseStep 4114415 = 6171623) B6171623
theorem B3655727 : Blo 1624511 3655727 := bstep (se 1 (by rfl) ⟨2741795, by rfl⟩ : syracuseStep 3655727 = 5483591) B5483591
theorem B2779273 : Blo 1624511 2779273 := bstep (se 2 (by rfl) ⟨1042227, by rfl⟩ : syracuseStep 2779273 = 2084455) B2084455
theorem B9259211 : Blo 1624511 9259211 := bstep (se 1 (by rfl) ⟨6944408, by rfl⟩ : syracuseStep 9259211 = 13888817) B13888817
theorem B33360293 : Blo 1624511 33360293 := bstep (se 4 (by rfl) ⟨3127527, by rfl⟩ : syracuseStep 33360293 = 6255055) B6255055
theorem B1624527 : Blo 1624511 1624527 := bstep (se 1 (by rfl) ⟨1218395, by rfl⟩ : syracuseStep 1624527 = 2436791) B2436791
theorem B1624667 : Blo 1624511 1624667 := bstep (se 1 (by rfl) ⟨1218500, by rfl⟩ : syracuseStep 1624667 = 2437001) B2437001
theorem B29649509 : Blo 1624511 29649509 := bstep (se 4 (by rfl) ⟨2779641, by rfl⟩ : syracuseStep 29649509 = 5559283) B5559283
theorem B1624831 : Blo 1624511 1624831 := bstep (se 1 (by rfl) ⟨1218623, by rfl⟩ : syracuseStep 1624831 = 2437247) B2437247
theorem B3656447 : Blo 1624511 3656447 := bstep (se 1 (by rfl) ⟨2742335, by rfl⟩ : syracuseStep 3656447 = 5484671) B5484671
theorem B4115407 : Blo 1624511 4115407 := bstep (se 1 (by rfl) ⟨3086555, by rfl⟩ : syracuseStep 4115407 = 6173111) B6173111
theorem B4631543 : Blo 1624511 4631543 := bstep (se 1 (by rfl) ⟨3473657, by rfl⟩ : syracuseStep 4631543 = 6947315) B6947315
theorem B1625255 : Blo 1624511 1625255 := bstep (se 1 (by rfl) ⟨1218941, by rfl⟩ : syracuseStep 1625255 = 2437883) B2437883
theorem B6171835 : Blo 1624511 6171835 := bstep (se 1 (by rfl) ⟨4628876, by rfl⟩ : syracuseStep 6171835 = 9257753) B9257753
theorem B2313527 : Blo 1624511 2313527 := bstep (se 1 (by rfl) ⟨1735145, by rfl⟩ : syracuseStep 2313527 = 3470291) B3470291
theorem B3657131 : Blo 1624511 3657131 := bstep (se 1 (by rfl) ⟨2742848, by rfl⟩ : syracuseStep 3657131 = 5485697) B5485697
theorem B1625551 : Blo 1624511 1625551 := bstep (se 1 (by rfl) ⟨1219163, by rfl⟩ : syracuseStep 1625551 = 2438327) B2438327
theorem B16690657 : Blo 1624511 16690657 := bstep (se 2 (by rfl) ⟨6258996, by rfl⟩ : syracuseStep 16690657 = 12517993) B12517993
theorem B1625711 : Blo 1624511 1625711 := bstep (se 1 (by rfl) ⟨1219283, by rfl⟩ : syracuseStep 1625711 = 2438567) B2438567
theorem B1625831 : Blo 1624511 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B3657671 : Blo 1624511 3657671 := bstep (se 1 (by rfl) ⟨2743253, by rfl⟩ : syracuseStep 3657671 = 5486507) B5486507
theorem B2437103 : Blo 1624511 2437103 := bstep (se 1 (by rfl) ⟨1827827, by rfl⟩ : syracuseStep 2437103 = 3655655) B3655655
theorem B1626139 : Blo 1624511 1626139 := bstep (se 1 (by rfl) ⟨1219604, by rfl⟩ : syracuseStep 1626139 = 2439209) B2439209
theorem B1626159 : Blo 1624511 1626159 := bstep (se 1 (by rfl) ⟨1219619, by rfl⟩ : syracuseStep 1626159 = 2439239) B2439239
theorem B5484617 : Blo 1624511 5484617 := bstep (se 2 (by rfl) ⟨2056731, by rfl⟩ : syracuseStep 5484617 = 4113463) B4113463
theorem B2437223 : Blo 1624511 2437223 := bstep (se 1 (by rfl) ⟨1827917, by rfl⟩ : syracuseStep 2437223 = 3655835) B3655835
theorem B2437343 : Blo 1624511 2437343 := bstep (se 1 (by rfl) ⟨1828007, by rfl⟩ : syracuseStep 2437343 = 3656015) B3656015
theorem B37523681 : Blo 1624511 37523681 := bstep (se 2 (by rfl) ⟨14071380, by rfl⟩ : syracuseStep 37523681 = 28142761) B28142761
theorem B3084551 : Blo 1624511 3084551 := bstep (se 1 (by rfl) ⟨2313413, by rfl⟩ : syracuseStep 3084551 = 4626827) B4626827
theorem B2437403 : Blo 1624511 2437403 := bstep (se 1 (by rfl) ⟨1828052, by rfl⟩ : syracuseStep 2437403 = 3656105) B3656105
theorem B3658031 : Blo 1624511 3658031 := bstep (se 1 (by rfl) ⟨2743523, by rfl⟩ : syracuseStep 3658031 = 5487047) B5487047
theorem B1626415 : Blo 1624511 1626415 := bstep (se 1 (by rfl) ⟨1219811, by rfl⟩ : syracuseStep 1626415 = 2439623) B2439623
theorem B3658175 : Blo 1624511 3658175 := bstep (se 1 (by rfl) ⟨2743631, by rfl⟩ : syracuseStep 3658175 = 5487263) B5487263
theorem B29659729 : Blo 1624511 29659729 := bstep (se 2 (by rfl) ⟨11122398, by rfl⟩ : syracuseStep 29659729 = 22244797) B22244797
theorem B6173279 : Blo 1624511 6173279 := bstep (se 1 (by rfl) ⟨4629959, by rfl⟩ : syracuseStep 6173279 = 9259919) B9259919
theorem B2437799 : Blo 1624511 2437799 := bstep (se 1 (by rfl) ⟨1828349, by rfl⟩ : syracuseStep 2437799 = 3656699) B3656699
theorem B10416923 : Blo 1624511 10416923 := bstep (se 1 (by rfl) ⟨7812692, by rfl⟩ : syracuseStep 10416923 = 15625385) B15625385
theorem B2437919 : Blo 1624511 2437919 := bstep (se 1 (by rfl) ⟨1828439, by rfl⟩ : syracuseStep 2437919 = 3656879) B3656879
theorem B2437943 : Blo 1624511 2437943 := bstep (se 1 (by rfl) ⟨1828457, by rfl⟩ : syracuseStep 2437943 = 3656915) B3656915
theorem B2315071 : Blo 1624511 2315071 := bstep (se 1 (by rfl) ⟨1736303, by rfl⟩ : syracuseStep 2315071 = 3472607) B3472607
theorem B7811923 : Blo 1624511 7811923 := bstep (se 1 (by rfl) ⟨5858942, by rfl⟩ : syracuseStep 7811923 = 11717885) B11717885
theorem B6173597 : Blo 1624511 6173597 := bstep (se 3 (by rfl) ⟨1157549, by rfl⟩ : syracuseStep 6173597 = 2315099) B2315099
theorem B2438057 : Blo 1624511 2438057 := bstep (se 2 (by rfl) ⟨914271, by rfl⟩ : syracuseStep 2438057 = 1828543) B1828543
theorem B2438123 : Blo 1624511 2438123 := bstep (se 1 (by rfl) ⟨1828592, by rfl⟩ : syracuseStep 2438123 = 3657185) B3657185
theorem B3658823 : Blo 1624511 3658823 := bstep (se 1 (by rfl) ⟨2744117, by rfl⟩ : syracuseStep 3658823 = 5488235) B5488235
theorem B8336465 : Blo 1624511 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B6173779 : Blo 1624511 6173779 := bstep (se 1 (by rfl) ⟨4630334, by rfl⟩ : syracuseStep 6173779 = 9260669) B9260669
theorem B3659003 : Blo 1624511 3659003 := bstep (se 1 (by rfl) ⟨2744252, by rfl⟩ : syracuseStep 3659003 = 5488505) B5488505
theorem B12350717 : Blo 1624511 12350717 := bstep (se 3 (by rfl) ⟨2315759, by rfl⟩ : syracuseStep 12350717 = 4631519) B4631519
theorem B2438399 : Blo 1624511 2438399 := bstep (se 1 (by rfl) ⟨1828799, by rfl⟩ : syracuseStep 2438399 = 3657599) B3657599
theorem B2438441 : Blo 1624511 2438441 := bstep (se 2 (by rfl) ⟨914415, by rfl⟩ : syracuseStep 2438441 = 1828831) B1828831
theorem B2741755 : Blo 1624511 2741755 := bstep (se 1 (by rfl) ⟨2056316, by rfl⟩ : syracuseStep 2741755 = 4112633) B4112633
theorem B4945529 : Blo 1624511 4945529 := bstep (se 2 (by rfl) ⟨1854573, by rfl⟩ : syracuseStep 4945529 = 3709147) B3709147
theorem B21124955 : Blo 1624511 21124955 := bstep (se 1 (by rfl) ⟨15843716, by rfl⟩ : syracuseStep 21124955 = 31687433) B31687433
theorem B2439035 : Blo 1624511 2439035 := bstep (se 1 (by rfl) ⟨1829276, by rfl⟩ : syracuseStep 2439035 = 3658553) B3658553
theorem B2439071 : Blo 1624511 2439071 := bstep (se 1 (by rfl) ⟨1829303, by rfl⟩ : syracuseStep 2439071 = 3658607) B3658607
theorem B2742187 : Blo 1624511 2742187 := bstep (se 1 (by rfl) ⟨2056640, by rfl⟩ : syracuseStep 2742187 = 4113281) B4113281
theorem B19781621 : Blo 1624511 19781621 := bstep (se 5 (by rfl) ⟨927263, by rfl⟩ : syracuseStep 19781621 = 1854527) B1854527
theorem B37517417 : Blo 1624511 37517417 := bstep (se 2 (by rfl) ⟨14069031, by rfl⟩ : syracuseStep 37517417 = 28138063) B28138063
theorem B2439275 : Blo 1624511 2439275 := bstep (se 1 (by rfl) ⟨1829456, by rfl⟩ : syracuseStep 2439275 = 3658913) B3658913
theorem B2439305 : Blo 1624511 2439305 := bstep (se 2 (by rfl) ⟨914739, by rfl⟩ : syracuseStep 2439305 = 1829479) B1829479
theorem B2439455 : Blo 1624511 2439455 := bstep (se 1 (by rfl) ⟨1829591, by rfl⟩ : syracuseStep 2439455 = 3659183) B3659183
theorem B2742727 : Blo 1624511 2742727 := bstep (se 1 (by rfl) ⟨2057045, by rfl⟩ : syracuseStep 2742727 = 4114091) B4114091
theorem B4627169 : Blo 1624511 4627169 := bstep (se 2 (by rfl) ⟨1735188, by rfl⟩ : syracuseStep 4627169 = 3470377) B3470377
theorem B237828835 : Blo 1624511 237828835 := bstep (se 1 (by rfl) ⟨178371626, by rfl⟩ : syracuseStep 237828835 = 356743253) B356743253
theorem B4692761 : Blo 1624511 4692761 := bstep (se 2 (by rfl) ⟨1759785, by rfl⟩ : syracuseStep 4692761 = 3519571) B3519571
theorem B19012573 : Blo 1624511 19012573 := bstep (se 3 (by rfl) ⟨3564857, by rfl⟩ : syracuseStep 19012573 = 7129715) B7129715
theorem B11115499 : Blo 1624511 11115499 := bstep (se 1 (by rfl) ⟨8336624, by rfl⟩ : syracuseStep 11115499 = 16673249) B16673249
theorem B10583099 : Blo 1624511 10583099 := bstep (se 1 (by rfl) ⟨7937324, by rfl⟩ : syracuseStep 10583099 = 15874649) B15874649
theorem B2743483 : Blo 1624511 2743483 := bstep (se 1 (by rfl) ⟨2057612, by rfl⟩ : syracuseStep 2743483 = 4115225) B4115225
theorem B2604359 : Blo 1624511 2604359 := bstep (se 1 (by rfl) ⟨1953269, by rfl⟩ : syracuseStep 2604359 = 3906539) B3906539
theorem B12680543 : Blo 1624511 12680543 := bstep (se 1 (by rfl) ⟨9510407, by rfl⟩ : syracuseStep 12680543 = 19020815) B19020815
theorem B32120393 : Blo 1624511 32120393 := bstep (se 2 (by rfl) ⟨12045147, by rfl⟩ : syracuseStep 32120393 = 24090295) B24090295
theorem B13885127 : Blo 1624511 13885127 := bstep (se 1 (by rfl) ⟨10413845, by rfl⟩ : syracuseStep 13885127 = 20827691) B20827691
theorem B4112167 : Blo 1624511 4112167 := bstep (se 1 (by rfl) ⟨3084125, by rfl⟩ : syracuseStep 4112167 = 6168251) B6168251
theorem B2056367 : Blo 1624511 2056367 := bstep (se 1 (by rfl) ⟨1542275, by rfl⟩ : syracuseStep 2056367 = 3084551) B3084551
theorem B5210345 : Blo 1624511 5210345 := bstep (se 2 (by rfl) ⟨1953879, by rfl⟩ : syracuseStep 5210345 = 3907759) B3907759
theorem B3293435 : Blo 1624511 3293435 := bstep (se 1 (by rfl) ⟨2470076, by rfl⟩ : syracuseStep 3293435 = 4940153) B4940153
theorem B11714975 : Blo 1624511 11714975 := bstep (se 1 (by rfl) ⟨8786231, by rfl⟩ : syracuseStep 11714975 = 17572463) B17572463
theorem B6169405 : Blo 1624511 6169405 := bstep (se 3 (by rfl) ⟨1156763, by rfl⟩ : syracuseStep 6169405 = 2313527) B2313527
theorem B8233811 : Blo 1624511 8233811 := bstep (se 1 (by rfl) ⟨6175358, by rfl⟩ : syracuseStep 8233811 = 12350717) B12350717
theorem B9257935 : Blo 1624511 9257935 := bstep (se 1 (by rfl) ⟨6943451, by rfl⟩ : syracuseStep 9257935 = 13886903) B13886903
theorem B317105113 : Blo 1624511 317105113 := bstep (se 2 (by rfl) ⟨118914417, by rfl⟩ : syracuseStep 317105113 = 237828835) B237828835
theorem B11715691 : Blo 1624511 11715691 := bstep (se 1 (by rfl) ⟨8786768, by rfl⟩ : syracuseStep 11715691 = 17573537) B17573537
theorem B4113575 : Blo 1624511 4113575 := bstep (se 1 (by rfl) ⟨3085181, by rfl⟩ : syracuseStep 4113575 = 6170363) B6170363
theorem B225248471 : Blo 1624511 225248471 := bstep (se 1 (by rfl) ⟨168936353, by rfl⟩ : syracuseStep 225248471 = 337872707) B337872707
theorem B14083303 : Blo 1624511 14083303 := bstep (se 1 (by rfl) ⟨10562477, by rfl⟩ : syracuseStep 14083303 = 21124955) B21124955
theorem B14820665 : Blo 1624511 14820665 := bstep (se 2 (by rfl) ⟨5557749, by rfl⟩ : syracuseStep 14820665 = 11115499) B11115499
theorem B25011611 : Blo 1624511 25011611 := bstep (se 1 (by rfl) ⟨18758708, by rfl⟩ : syracuseStep 25011611 = 37517417) B37517417
theorem B3655673 : Blo 1624511 3655673 := bstep (se 2 (by rfl) ⟨1370877, by rfl⟩ : syracuseStep 3655673 = 2741755) B2741755
theorem B7055399 : Blo 1624511 7055399 := bstep (se 1 (by rfl) ⟨5291549, by rfl⟩ : syracuseStep 7055399 = 10583099) B10583099
theorem B8227169 : Blo 1624511 8227169 := bstep (se 2 (by rfl) ⟨3085188, by rfl⟩ : syracuseStep 8227169 = 6170377) B6170377
theorem B5482889 : Blo 1624511 5482889 := bstep (se 2 (by rfl) ⟨2056083, by rfl⟩ : syracuseStep 5482889 = 4112167) B4112167
theorem B3656249 : Blo 1624511 3656249 := bstep (se 2 (by rfl) ⟨1371093, by rfl⟩ : syracuseStep 3656249 = 2742187) B2742187
theorem B1624735 : Blo 1624511 1624735 := bstep (se 1 (by rfl) ⟨1218551, by rfl⟩ : syracuseStep 1624735 = 2437103) B2437103
theorem B3656411 : Blo 1624511 3656411 := bstep (se 1 (by rfl) ⟨2742308, by rfl⟩ : syracuseStep 3656411 = 5484617) B5484617
theorem B1624815 : Blo 1624511 1624815 := bstep (se 1 (by rfl) ⟨1218611, by rfl⟩ : syracuseStep 1624815 = 2437223) B2437223
theorem B1624895 : Blo 1624511 1624895 := bstep (se 1 (by rfl) ⟨1218671, by rfl⟩ : syracuseStep 1624895 = 2437343) B2437343
theorem B3705697 : Blo 1624511 3705697 := bstep (se 2 (by rfl) ⟨1389636, by rfl⟩ : syracuseStep 3705697 = 2779273) B2779273
theorem B1624935 : Blo 1624511 1624935 := bstep (se 1 (by rfl) ⟨1218701, by rfl⟩ : syracuseStep 1624935 = 2437403) B2437403
theorem B5483375 : Blo 1624511 5483375 := bstep (se 1 (by rfl) ⟨4112531, by rfl⟩ : syracuseStep 5483375 = 8225063) B8225063
theorem B4115519 : Blo 1624511 4115519 := bstep (se 1 (by rfl) ⟨3086639, by rfl⟩ : syracuseStep 4115519 = 6173279) B6173279
theorem B1625199 : Blo 1624511 1625199 := bstep (se 1 (by rfl) ⟨1218899, by rfl⟩ : syracuseStep 1625199 = 2437799) B2437799
theorem B1625279 : Blo 1624511 1625279 := bstep (se 1 (by rfl) ⟨1218959, by rfl⟩ : syracuseStep 1625279 = 2437919) B2437919
theorem B1625295 : Blo 1624511 1625295 := bstep (se 1 (by rfl) ⟨1218971, by rfl⟩ : syracuseStep 1625295 = 2437943) B2437943
theorem B3656969 : Blo 1624511 3656969 := bstep (se 2 (by rfl) ⟨1371363, by rfl⟩ : syracuseStep 3656969 = 2742727) B2742727
theorem B4115731 : Blo 1624511 4115731 := bstep (se 1 (by rfl) ⟨3086798, by rfl⟩ : syracuseStep 4115731 = 6173597) B6173597
theorem B1625371 : Blo 1624511 1625371 := bstep (se 1 (by rfl) ⟨1219028, by rfl⟩ : syracuseStep 1625371 = 2438057) B2438057
theorem B1625415 : Blo 1624511 1625415 := bstep (se 1 (by rfl) ⟨1219061, by rfl⟩ : syracuseStep 1625415 = 2438123) B2438123
theorem B5557643 : Blo 1624511 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B342617525 : Blo 1624511 342617525 := bstep (se 5 (by rfl) ⟨16060196, by rfl⟩ : syracuseStep 342617525 = 32120393) B32120393
theorem B39546305 : Blo 1624511 39546305 := bstep (se 2 (by rfl) ⟨14829864, by rfl⟩ : syracuseStep 39546305 = 29659729) B29659729
theorem B9891323 : Blo 1624511 9891323 := bstep (se 1 (by rfl) ⟨7418492, by rfl⟩ : syracuseStep 9891323 = 14836985) B14836985
theorem B1625599 : Blo 1624511 1625599 := bstep (se 1 (by rfl) ⟨1219199, by rfl⟩ : syracuseStep 1625599 = 2438399) B2438399
theorem B1625627 : Blo 1624511 1625627 := bstep (se 1 (by rfl) ⟨1219220, by rfl⟩ : syracuseStep 1625627 = 2438441) B2438441
theorem B5484185 : Blo 1624511 5484185 := bstep (se 2 (by rfl) ⟨2056569, by rfl⟩ : syracuseStep 5484185 = 4113139) B4113139
theorem B3297019 : Blo 1624511 3297019 := bstep (se 1 (by rfl) ⟨2472764, by rfl⟩ : syracuseStep 3297019 = 4945529) B4945529
theorem B88960781 : Blo 1624511 88960781 := bstep (se 3 (by rfl) ⟨16680146, by rfl⟩ : syracuseStep 88960781 = 33360293) B33360293
theorem B10415897 : Blo 1624511 10415897 := bstep (se 2 (by rfl) ⟨3905961, by rfl⟩ : syracuseStep 10415897 = 7811923) B7811923
theorem B1626023 : Blo 1624511 1626023 := bstep (se 1 (by rfl) ⟨1219517, by rfl⟩ : syracuseStep 1626023 = 2439035) B2439035
theorem B1626047 : Blo 1624511 1626047 := bstep (se 1 (by rfl) ⟨1219535, by rfl⟩ : syracuseStep 1626047 = 2439071) B2439071
theorem B25350097 : Blo 1624511 25350097 := bstep (se 2 (by rfl) ⟨9506286, by rfl⟩ : syracuseStep 25350097 = 19012573) B19012573
theorem B2437097 : Blo 1624511 2437097 := bstep (se 2 (by rfl) ⟨913911, by rfl⟩ : syracuseStep 2437097 = 1827823) B1827823
theorem B2437151 : Blo 1624511 2437151 := bstep (se 1 (by rfl) ⟨1827863, by rfl⟩ : syracuseStep 2437151 = 3655727) B3655727
theorem B1626183 : Blo 1624511 1626183 := bstep (se 1 (by rfl) ⟨1219637, by rfl⟩ : syracuseStep 1626183 = 2439275) B2439275
theorem B1626203 : Blo 1624511 1626203 := bstep (se 1 (by rfl) ⟨1219652, by rfl⟩ : syracuseStep 1626203 = 2439305) B2439305
theorem B2437241 : Blo 1624511 2437241 := bstep (se 2 (by rfl) ⟨913965, by rfl⟩ : syracuseStep 2437241 = 1827931) B1827931
theorem B6172807 : Blo 1624511 6172807 := bstep (se 1 (by rfl) ⟨4629605, by rfl⟩ : syracuseStep 6172807 = 9259211) B9259211
theorem B1626303 : Blo 1624511 1626303 := bstep (se 1 (by rfl) ⟨1219727, by rfl⟩ : syracuseStep 1626303 = 2439455) B2439455
theorem B8229113 : Blo 1624511 8229113 := bstep (se 2 (by rfl) ⟨3085917, by rfl⟩ : syracuseStep 8229113 = 6171835) B6171835
theorem B3657977 : Blo 1624511 3657977 := bstep (se 2 (by rfl) ⟨1371741, by rfl⟩ : syracuseStep 3657977 = 2743483) B2743483
theorem B3084779 : Blo 1624511 3084779 := bstep (se 1 (by rfl) ⟨2313584, by rfl⟩ : syracuseStep 3084779 = 4627169) B4627169
theorem B2437631 : Blo 1624511 2437631 := bstep (se 1 (by rfl) ⟨1828223, by rfl⟩ : syracuseStep 2437631 = 3656447) B3656447
theorem B22254209 : Blo 1624511 22254209 := bstep (se 2 (by rfl) ⟨8345328, by rfl⟩ : syracuseStep 22254209 = 16690657) B16690657
theorem B2437769 : Blo 1624511 2437769 := bstep (se 2 (by rfl) ⟨914163, by rfl⟩ : syracuseStep 2437769 = 1828327) B1828327
theorem B2438009 : Blo 1624511 2438009 := bstep (se 2 (by rfl) ⟨914253, by rfl⟩ : syracuseStep 2438009 = 1828507) B1828507
theorem B2438087 : Blo 1624511 2438087 := bstep (se 1 (by rfl) ⟨1828565, by rfl⟩ : syracuseStep 2438087 = 3657131) B3657131
theorem B2438447 : Blo 1624511 2438447 := bstep (se 1 (by rfl) ⟨1828835, by rfl⟩ : syracuseStep 2438447 = 3657671) B3657671
theorem B25015787 : Blo 1624511 25015787 := bstep (se 1 (by rfl) ⟨18761840, by rfl⟩ : syracuseStep 25015787 = 37523681) B37523681
theorem B2438687 : Blo 1624511 2438687 := bstep (se 1 (by rfl) ⟨1829015, by rfl⟩ : syracuseStep 2438687 = 3658031) B3658031
theorem B2438783 : Blo 1624511 2438783 := bstep (se 1 (by rfl) ⟨1829087, by rfl⟩ : syracuseStep 2438783 = 3658175) B3658175
theorem B12342941 : Blo 1624511 12342941 := bstep (se 3 (by rfl) ⟨2314301, by rfl⟩ : syracuseStep 12342941 = 4628603) B4628603
theorem B2741951 : Blo 1624511 2741951 := bstep (se 1 (by rfl) ⟨2056463, by rfl⟩ : syracuseStep 2741951 = 4112927) B4112927
theorem B22255307 : Blo 1624511 22255307 := bstep (se 1 (by rfl) ⟨16691480, by rfl⟩ : syracuseStep 22255307 = 33382961) B33382961
theorem B6944615 : Blo 1624511 6944615 := bstep (se 1 (by rfl) ⟨5208461, by rfl⟩ : syracuseStep 6944615 = 10416923) B10416923
theorem B2439215 : Blo 1624511 2439215 := bstep (se 1 (by rfl) ⟨1829411, by rfl⟩ : syracuseStep 2439215 = 3658823) B3658823
theorem B2439335 : Blo 1624511 2439335 := bstep (se 1 (by rfl) ⟨1829501, by rfl⟩ : syracuseStep 2439335 = 3659003) B3659003
theorem B2742511 : Blo 1624511 2742511 := bstep (se 1 (by rfl) ⟨2056883, by rfl⟩ : syracuseStep 2742511 = 4113767) B4113767
theorem B3086761 : Blo 1624511 3086761 := bstep (se 2 (by rfl) ⟨1157535, by rfl⟩ : syracuseStep 3086761 = 2315071) B2315071
theorem B5487209 : Blo 1624511 5487209 := bstep (se 2 (by rfl) ⟨2057703, by rfl⟩ : syracuseStep 5487209 = 4115407) B4115407
theorem B2742943 : Blo 1624511 2742943 := bstep (se 1 (by rfl) ⟨2057207, by rfl⟩ : syracuseStep 2742943 = 4114415) B4114415
theorem B13187747 : Blo 1624511 13187747 := bstep (se 1 (by rfl) ⟨9890810, by rfl⟩ : syracuseStep 13187747 = 19781621) B19781621
theorem B8231705 : Blo 1624511 8231705 := bstep (se 2 (by rfl) ⟨3086889, by rfl⟩ : syracuseStep 8231705 = 6173779) B6173779
theorem B19766339 : Blo 1624511 19766339 := bstep (se 1 (by rfl) ⟨14824754, by rfl⟩ : syracuseStep 19766339 = 29649509) B29649509
theorem B3128507 : Blo 1624511 3128507 := bstep (se 1 (by rfl) ⟨2346380, by rfl⟩ : syracuseStep 3128507 = 4692761) B4692761
theorem B3087695 : Blo 1624511 3087695 := bstep (se 1 (by rfl) ⟨2315771, by rfl⟩ : syracuseStep 3087695 = 4631543) B4631543
theorem B1736239 : Blo 1624511 1736239 := bstep (se 1 (by rfl) ⟨1302179, by rfl⟩ : syracuseStep 1736239 = 2604359) B2604359
theorem B8453695 : Blo 1624511 8453695 := bstep (se 1 (by rfl) ⟨6340271, by rfl⟩ : syracuseStep 8453695 = 12680543) B12680543
theorem B9256751 : Blo 1624511 9256751 := bstep (se 1 (by rfl) ⟨6942563, by rfl⟩ : syracuseStep 9256751 = 13885127) B13885127
theorem B2195623 : Blo 1624511 2195623 := bstep (se 1 (by rfl) ⟨1646717, by rfl⟩ : syracuseStep 2195623 = 3293435) B3293435
theorem B2056519 : Blo 1624511 2056519 := bstep (se 1 (by rfl) ⟨1542389, by rfl⟩ : syracuseStep 2056519 = 3084779) B3084779
theorem B14836139 : Blo 1624511 14836139 := bstep (se 1 (by rfl) ⟨11127104, by rfl⟩ : syracuseStep 14836139 = 22254209) B22254209
theorem B5489207 : Blo 1624511 5489207 := bstep (se 1 (by rfl) ⟨4116905, by rfl⟩ : syracuseStep 5489207 = 8233811) B8233811
theorem B13894253 : Blo 1624511 13894253 := bstep (se 3 (by rfl) ⟨2605172, by rfl⟩ : syracuseStep 13894253 = 5210345) B5210345
theorem B8225873 : Blo 1624511 8225873 := bstep (se 2 (by rfl) ⟨3084702, by rfl⟩ : syracuseStep 8225873 = 6169405) B6169405
theorem B1827967 : Blo 1624511 1827967 := bstep (se 1 (by rfl) ⟨1370975, by rfl⟩ : syracuseStep 1827967 = 2741951) B2741951
theorem B4940929 : Blo 1624511 4940929 := bstep (se 2 (by rfl) ⟨1852848, by rfl⟩ : syracuseStep 4940929 = 3705697) B3705697
theorem B14836871 : Blo 1624511 14836871 := bstep (se 1 (by rfl) ⟨11127653, by rfl⟩ : syracuseStep 14836871 = 22255307) B22255307
theorem B4629743 : Blo 1624511 4629743 := bstep (se 1 (by rfl) ⟨3472307, by rfl⟩ : syracuseStep 4629743 = 6944615) B6944615
theorem B422806817 : Blo 1624511 422806817 := bstep (se 2 (by rfl) ⟨158552556, by rfl⟩ : syracuseStep 422806817 = 317105113) B317105113
theorem B4703599 : Blo 1624511 4703599 := bstep (se 1 (by rfl) ⟨3527699, by rfl⟩ : syracuseStep 4703599 = 7055399) B7055399
theorem B3655259 : Blo 1624511 3655259 := bstep (se 1 (by rfl) ⟨2741444, by rfl⟩ : syracuseStep 3655259 = 5482889) B5482889
theorem B18777737 : Blo 1624511 18777737 := bstep (se 2 (by rfl) ⟨7041651, by rfl⟩ : syracuseStep 18777737 = 14083303) B14083303
theorem B8791831 : Blo 1624511 8791831 := bstep (se 1 (by rfl) ⟨6593873, by rfl⟩ : syracuseStep 8791831 = 13187747) B13187747
theorem B3655583 : Blo 1624511 3655583 := bstep (se 1 (by rfl) ⟨2741687, by rfl⟩ : syracuseStep 3655583 = 5483375) B5483375
theorem B2058463 : Blo 1624511 2058463 := bstep (se 1 (by rfl) ⟨1543847, by rfl⟩ : syracuseStep 2058463 = 3087695) B3087695
theorem B3705095 : Blo 1624511 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B228411683 : Blo 1624511 228411683 := bstep (se 1 (by rfl) ⟨171308762, by rfl⟩ : syracuseStep 228411683 = 342617525) B342617525
theorem B26364203 : Blo 1624511 26364203 := bstep (se 1 (by rfl) ⟨19773152, by rfl⟩ : syracuseStep 26364203 = 39546305) B39546305
theorem B3656123 : Blo 1624511 3656123 := bstep (se 1 (by rfl) ⟨2742092, by rfl⟩ : syracuseStep 3656123 = 5484185) B5484185
theorem B6171167 : Blo 1624511 6171167 := bstep (se 1 (by rfl) ⟨4628375, by rfl⟩ : syracuseStep 6171167 = 9256751) B9256751
theorem B1624731 : Blo 1624511 1624731 := bstep (se 1 (by rfl) ⟨1218548, by rfl⟩ : syracuseStep 1624731 = 2437097) B2437097
theorem B1624767 : Blo 1624511 1624767 := bstep (se 1 (by rfl) ⟨1218575, by rfl⟩ : syracuseStep 1624767 = 2437151) B2437151
theorem B1624827 : Blo 1624511 1624827 := bstep (se 1 (by rfl) ⟨1218620, by rfl⟩ : syracuseStep 1624827 = 2437241) B2437241
theorem B7809983 : Blo 1624511 7809983 := bstep (se 1 (by rfl) ⟨5857487, by rfl⟩ : syracuseStep 7809983 = 11714975) B11714975
theorem B3656681 : Blo 1624511 3656681 := bstep (se 2 (by rfl) ⟨1371255, by rfl⟩ : syracuseStep 3656681 = 2742511) B2742511
theorem B1625087 : Blo 1624511 1625087 := bstep (se 1 (by rfl) ⟨1218815, by rfl⟩ : syracuseStep 1625087 = 2437631) B2437631
theorem B1625179 : Blo 1624511 1625179 := bstep (se 1 (by rfl) ⟨1218884, by rfl⟩ : syracuseStep 1625179 = 2437769) B2437769
theorem B5483645 : Blo 1624511 5483645 := bstep (se 3 (by rfl) ⟨1028183, by rfl⟩ : syracuseStep 5483645 = 2056367) B2056367
theorem B4115681 : Blo 1624511 4115681 := bstep (se 2 (by rfl) ⟨1543380, by rfl⟩ : syracuseStep 4115681 = 3086761) B3086761
theorem B1625339 : Blo 1624511 1625339 := bstep (se 1 (by rfl) ⟨1219004, by rfl⟩ : syracuseStep 1625339 = 2438009) B2438009
theorem B1625391 : Blo 1624511 1625391 := bstep (se 1 (by rfl) ⟨1219043, by rfl⟩ : syracuseStep 1625391 = 2438087) B2438087
theorem B39521773 : Blo 1624511 39521773 := bstep (se 3 (by rfl) ⟨7410332, by rfl⟩ : syracuseStep 39521773 = 14820665) B14820665
theorem B1625631 : Blo 1624511 1625631 := bstep (se 1 (by rfl) ⟨1219223, by rfl⟩ : syracuseStep 1625631 = 2438447) B2438447
theorem B3657257 : Blo 1624511 3657257 := bstep (se 2 (by rfl) ⟨1371471, by rfl⟩ : syracuseStep 3657257 = 2742943) B2742943
theorem B16674407 : Blo 1624511 16674407 := bstep (se 1 (by rfl) ⟨12505805, by rfl⟩ : syracuseStep 16674407 = 25011611) B25011611
theorem B1625791 : Blo 1624511 1625791 := bstep (se 1 (by rfl) ⟨1219343, by rfl⟩ : syracuseStep 1625791 = 2438687) B2438687
theorem B1625855 : Blo 1624511 1625855 := bstep (se 1 (by rfl) ⟨1219391, by rfl⟩ : syracuseStep 1625855 = 2438783) B2438783
theorem B8228627 : Blo 1624511 8228627 := bstep (se 1 (by rfl) ⟨6171470, by rfl⟩ : syracuseStep 8228627 = 12342941) B12342941
theorem B2437115 : Blo 1624511 2437115 := bstep (se 1 (by rfl) ⟨1827836, by rfl⟩ : syracuseStep 2437115 = 3655673) B3655673
theorem B1626143 : Blo 1624511 1626143 := bstep (se 1 (by rfl) ⟨1219607, by rfl⟩ : syracuseStep 1626143 = 2439215) B2439215
theorem B1626223 : Blo 1624511 1626223 := bstep (se 1 (by rfl) ⟨1219667, by rfl⟩ : syracuseStep 1626223 = 2439335) B2439335
theorem B5484779 : Blo 1624511 5484779 := bstep (se 1 (by rfl) ⟨4113584, by rfl⟩ : syracuseStep 5484779 = 8227169) B8227169
theorem B2437499 : Blo 1624511 2437499 := bstep (se 1 (by rfl) ⟨1828124, by rfl⟩ : syracuseStep 2437499 = 3656249) B3656249
theorem B3658139 : Blo 1624511 3658139 := bstep (se 1 (by rfl) ⟨2743604, by rfl⟩ : syracuseStep 3658139 = 5487209) B5487209
theorem B2437607 : Blo 1624511 2437607 := bstep (se 1 (by rfl) ⟨1828205, by rfl⟩ : syracuseStep 2437607 = 3656411) B3656411
theorem B13177559 : Blo 1624511 13177559 := bstep (se 1 (by rfl) ⟨9883169, by rfl⟩ : syracuseStep 13177559 = 19766339) B19766339
theorem B2314985 : Blo 1624511 2314985 := bstep (se 2 (by rfl) ⟨868119, by rfl⟩ : syracuseStep 2314985 = 1736239) B1736239
theorem B2085671 : Blo 1624511 2085671 := bstep (se 1 (by rfl) ⟨1564253, by rfl⟩ : syracuseStep 2085671 = 3128507) B3128507
theorem B2437979 : Blo 1624511 2437979 := bstep (se 1 (by rfl) ⟨1828484, by rfl⟩ : syracuseStep 2437979 = 3656969) B3656969
theorem B4396025 : Blo 1624511 4396025 := bstep (se 2 (by rfl) ⟨1648509, by rfl⟩ : syracuseStep 4396025 = 3297019) B3297019
theorem B59307187 : Blo 1624511 59307187 := bstep (se 1 (by rfl) ⟨44480390, by rfl⟩ : syracuseStep 59307187 = 88960781) B88960781
theorem B6943931 : Blo 1624511 6943931 := bstep (se 1 (by rfl) ⟨5207948, by rfl⟩ : syracuseStep 6943931 = 10415897) B10415897
theorem B5486075 : Blo 1624511 5486075 := bstep (se 1 (by rfl) ⟨4114556, by rfl⟩ : syracuseStep 5486075 = 8229113) B8229113
theorem B2438651 : Blo 1624511 2438651 := bstep (se 1 (by rfl) ⟨1828988, by rfl⟩ : syracuseStep 2438651 = 3657977) B3657977
theorem B8230409 : Blo 1624511 8230409 := bstep (se 2 (by rfl) ⟨3086403, by rfl⟩ : syracuseStep 8230409 = 6172807) B6172807
theorem B2742383 : Blo 1624511 2742383 := bstep (se 1 (by rfl) ⟨2056787, by rfl⟩ : syracuseStep 2742383 = 4113575) B4113575
theorem B150165647 : Blo 1624511 150165647 := bstep (se 1 (by rfl) ⟨112624235, by rfl⟩ : syracuseStep 150165647 = 225248471) B225248471
theorem B16677191 : Blo 1624511 16677191 := bstep (se 1 (by rfl) ⟨12507893, by rfl⟩ : syracuseStep 16677191 = 25015787) B25015787
theorem B12343913 : Blo 1624511 12343913 := bstep (se 2 (by rfl) ⟨4628967, by rfl⟩ : syracuseStep 12343913 = 9257935) B9257935
theorem B15620921 : Blo 1624511 15620921 := bstep (se 2 (by rfl) ⟨5857845, by rfl⟩ : syracuseStep 15620921 = 11715691) B11715691
theorem B5487641 : Blo 1624511 5487641 := bstep (se 2 (by rfl) ⟨2057865, by rfl⟩ : syracuseStep 5487641 = 4115731) B4115731
theorem B5487803 : Blo 1624511 5487803 := bstep (se 1 (by rfl) ⟨4115852, by rfl⟩ : syracuseStep 5487803 = 8231705) B8231705
theorem B2743679 : Blo 1624511 2743679 := bstep (se 1 (by rfl) ⟨2057759, by rfl⟩ : syracuseStep 2743679 = 4115519) B4115519
theorem B11271593 : Blo 1624511 11271593 := bstep (se 2 (by rfl) ⟨4226847, by rfl⟩ : syracuseStep 11271593 = 8453695) B8453695
theorem B6594215 : Blo 1624511 6594215 := bstep (se 1 (by rfl) ⟨4945661, by rfl⟩ : syracuseStep 6594215 = 9891323) B9891323
theorem B33800129 : Blo 1624511 33800129 := bstep (se 2 (by rfl) ⟨12675048, by rfl⟩ : syracuseStep 33800129 = 25350097) B25350097
theorem B2744617 : Blo 1624511 2744617 := bstep (se 2 (by rfl) ⟨1029231, by rfl⟩ : syracuseStep 2744617 = 2058463) B2058463
theorem B4629287 : Blo 1624511 4629287 := bstep (se 1 (by rfl) ⟨3471965, by rfl⟩ : syracuseStep 4629287 = 6943931) B6943931
theorem B281871211 : Blo 1624511 281871211 := bstep (se 1 (by rfl) ⟨211403408, by rfl⟩ : syracuseStep 281871211 = 422806817) B422806817
theorem B12518491 : Blo 1624511 12518491 := bstep (se 1 (by rfl) ⟨9388868, by rfl⟩ : syracuseStep 12518491 = 18777737) B18777737
theorem B30057581 : Blo 1624511 30057581 := bstep (se 3 (by rfl) ⟨5635796, by rfl⟩ : syracuseStep 30057581 = 11271593) B11271593
theorem B1828255 : Blo 1624511 1828255 := bstep (se 1 (by rfl) ⟨1371191, by rfl⟩ : syracuseStep 1828255 = 2742383) B2742383
theorem B6587905 : Blo 1624511 6587905 := bstep (se 2 (by rfl) ⟨2470464, by rfl⟩ : syracuseStep 6587905 = 4940929) B4940929
theorem B152274455 : Blo 1624511 152274455 := bstep (se 1 (by rfl) ⟨114205841, by rfl⟩ : syracuseStep 152274455 = 228411683) B228411683
theorem B4114111 : Blo 1624511 4114111 := bstep (se 1 (by rfl) ⟨3085583, by rfl⟩ : syracuseStep 4114111 = 6171167) B6171167
theorem B10413947 : Blo 1624511 10413947 := bstep (se 1 (by rfl) ⟨7810460, by rfl⟩ : syracuseStep 10413947 = 15620921) B15620921
theorem B25085861 : Blo 1624511 25085861 := bstep (se 4 (by rfl) ⟨2351799, by rfl⟩ : syracuseStep 25085861 = 4703599) B4703599
theorem B3655763 : Blo 1624511 3655763 := bstep (se 1 (by rfl) ⟨2741822, by rfl⟩ : syracuseStep 3655763 = 5483645) B5483645
theorem B1829119 : Blo 1624511 1829119 := bstep (se 1 (by rfl) ⟨1371839, by rfl⟩ : syracuseStep 1829119 = 2743679) B2743679
theorem B1624743 : Blo 1624511 1624743 := bstep (se 1 (by rfl) ⟨1218557, by rfl⟩ : syracuseStep 1624743 = 2437115) B2437115
theorem B3656519 : Blo 1624511 3656519 := bstep (se 1 (by rfl) ⟨2742389, by rfl⟩ : syracuseStep 3656519 = 5484779) B5484779
theorem B2927497 : Blo 1624511 2927497 := bstep (se 2 (by rfl) ⟨1097811, by rfl⟩ : syracuseStep 2927497 = 2195623) B2195623
theorem B1624999 : Blo 1624511 1624999 := bstep (se 1 (by rfl) ⟨1218749, by rfl⟩ : syracuseStep 1624999 = 2437499) B2437499
theorem B9890759 : Blo 1624511 9890759 := bstep (se 1 (by rfl) ⟨7418069, by rfl⟩ : syracuseStep 9890759 = 14836139) B14836139
theorem B1625071 : Blo 1624511 1625071 := bstep (se 1 (by rfl) ⟨1218803, by rfl⟩ : syracuseStep 1625071 = 2437607) B2437607
theorem B8785039 : Blo 1624511 8785039 := bstep (se 1 (by rfl) ⟨6588779, by rfl⟩ : syracuseStep 8785039 = 13177559) B13177559
theorem B1625319 : Blo 1624511 1625319 := bstep (se 1 (by rfl) ⟨1218989, by rfl⟩ : syracuseStep 1625319 = 2437979) B2437979
theorem B5483915 : Blo 1624511 5483915 := bstep (se 1 (by rfl) ⟨4112936, by rfl⟩ : syracuseStep 5483915 = 8225873) B8225873
theorem B9891247 : Blo 1624511 9891247 := bstep (se 1 (by rfl) ⟨7418435, by rfl⟩ : syracuseStep 9891247 = 14836871) B14836871
theorem B3657383 : Blo 1624511 3657383 := bstep (se 1 (by rfl) ⟨2743037, by rfl⟩ : syracuseStep 3657383 = 5486075) B5486075
theorem B1625767 : Blo 1624511 1625767 := bstep (se 1 (by rfl) ⟨1219325, by rfl⟩ : syracuseStep 1625767 = 2438651) B2438651
theorem B2436839 : Blo 1624511 2436839 := bstep (se 1 (by rfl) ⟨1827629, by rfl⟩ : syracuseStep 2436839 = 3655259) B3655259
theorem B2437055 : Blo 1624511 2437055 := bstep (se 1 (by rfl) ⟨1827791, by rfl⟩ : syracuseStep 2437055 = 3655583) B3655583
theorem B100110431 : Blo 1624511 100110431 := bstep (se 1 (by rfl) ⟨75082823, by rfl⟩ : syracuseStep 100110431 = 150165647) B150165647
theorem B2437289 : Blo 1624511 2437289 := bstep (se 2 (by rfl) ⟨913983, by rfl⟩ : syracuseStep 2437289 = 1827967) B1827967
theorem B2470063 : Blo 1624511 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B17576135 : Blo 1624511 17576135 := bstep (se 1 (by rfl) ⟨13182101, by rfl⟩ : syracuseStep 17576135 = 26364203) B26364203
theorem B2437415 : Blo 1624511 2437415 := bstep (se 1 (by rfl) ⟨1828061, by rfl⟩ : syracuseStep 2437415 = 3656123) B3656123
theorem B8229275 : Blo 1624511 8229275 := bstep (se 1 (by rfl) ⟨6171956, by rfl⟩ : syracuseStep 8229275 = 12343913) B12343913
theorem B17584573 : Blo 1624511 17584573 := bstep (se 3 (by rfl) ⟨3297107, by rfl⟩ : syracuseStep 17584573 = 6594215) B6594215
theorem B6173293 : Blo 1624511 6173293 := bstep (se 3 (by rfl) ⟨1157492, by rfl⟩ : syracuseStep 6173293 = 2314985) B2314985
theorem B5206655 : Blo 1624511 5206655 := bstep (se 1 (by rfl) ⟨3904991, by rfl⟩ : syracuseStep 5206655 = 7809983) B7809983
theorem B52695697 : Blo 1624511 52695697 := bstep (se 2 (by rfl) ⟨19760886, by rfl⟩ : syracuseStep 52695697 = 39521773) B39521773
theorem B2437787 : Blo 1624511 2437787 := bstep (se 1 (by rfl) ⟨1828340, by rfl⟩ : syracuseStep 2437787 = 3656681) B3656681
theorem B3658427 : Blo 1624511 3658427 := bstep (se 1 (by rfl) ⟨2743820, by rfl⟩ : syracuseStep 3658427 = 5487641) B5487641
theorem B3658535 : Blo 1624511 3658535 := bstep (se 1 (by rfl) ⟨2743901, by rfl⟩ : syracuseStep 3658535 = 5487803) B5487803
theorem B2438171 : Blo 1624511 2438171 := bstep (se 1 (by rfl) ⟨1828628, by rfl⟩ : syracuseStep 2438171 = 3657257) B3657257
theorem B5485751 : Blo 1624511 5485751 := bstep (se 1 (by rfl) ⟨4114313, by rfl⟩ : syracuseStep 5485751 = 8228627) B8228627
theorem B22533419 : Blo 1624511 22533419 := bstep (se 1 (by rfl) ⟨16900064, by rfl⟩ : syracuseStep 22533419 = 33800129) B33800129
theorem B2438759 : Blo 1624511 2438759 := bstep (se 1 (by rfl) ⟨1829069, by rfl⟩ : syracuseStep 2438759 = 3658139) B3658139
theorem B3659471 : Blo 1624511 3659471 := bstep (se 1 (by rfl) ⟨2744603, by rfl⟩ : syracuseStep 3659471 = 5489207) B5489207
theorem B9262835 : Blo 1624511 9262835 := bstep (se 1 (by rfl) ⟨6947126, by rfl⟩ : syracuseStep 9262835 = 13894253) B13894253
theorem B2742025 : Blo 1624511 2742025 := bstep (se 2 (by rfl) ⟨1028259, by rfl⟩ : syracuseStep 2742025 = 2056519) B2056519
theorem B2930683 : Blo 1624511 2930683 := bstep (se 1 (by rfl) ⟨2198012, by rfl⟩ : syracuseStep 2930683 = 4396025) B4396025
theorem B3086495 : Blo 1624511 3086495 := bstep (se 1 (by rfl) ⟨2314871, by rfl⟩ : syracuseStep 3086495 = 4629743) B4629743
theorem B44472509 : Blo 1624511 44472509 := bstep (se 3 (by rfl) ⟨8338595, by rfl⟩ : syracuseStep 44472509 = 16677191) B16677191
theorem B5486939 : Blo 1624511 5486939 := bstep (se 1 (by rfl) ⟨4115204, by rfl⟩ : syracuseStep 5486939 = 8230409) B8230409
theorem B79076249 : Blo 1624511 79076249 := bstep (se 2 (by rfl) ⟨29653593, by rfl⟩ : syracuseStep 79076249 = 59307187) B59307187
theorem B5561789 : Blo 1624511 5561789 := bstep (se 3 (by rfl) ⟨1042835, by rfl⟩ : syracuseStep 5561789 = 2085671) B2085671
theorem B2743787 : Blo 1624511 2743787 := bstep (se 1 (by rfl) ⟨2057840, by rfl⟩ : syracuseStep 2743787 = 4115681) B4115681
theorem B11722441 : Blo 1624511 11722441 := bstep (se 2 (by rfl) ⟨4395915, by rfl⟩ : syracuseStep 11722441 = 8791831) B8791831
theorem B11116271 : Blo 1624511 11116271 := bstep (se 1 (by rfl) ⟨8337203, by rfl⟩ : syracuseStep 11116271 = 16674407) B16674407
theorem B66740287 : Blo 1624511 66740287 := bstep (se 1 (by rfl) ⟨50055215, by rfl⟩ : syracuseStep 66740287 = 100110431) B100110431
theorem B3293417 : Blo 1624511 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B23446097 : Blo 1624511 23446097 := bstep (se 2 (by rfl) ⟨8792286, by rfl⟩ : syracuseStep 23446097 = 17584573) B17584573
theorem B101516303 : Blo 1624511 101516303 := bstep (se 1 (by rfl) ⟨76137227, by rfl⟩ : syracuseStep 101516303 = 152274455) B152274455
theorem B2057663 : Blo 1624511 2057663 := bstep (se 1 (by rfl) ⟨1543247, by rfl⟩ : syracuseStep 2057663 = 3086495) B3086495
theorem B29648339 : Blo 1624511 29648339 := bstep (se 1 (by rfl) ⟨22236254, by rfl⟩ : syracuseStep 29648339 = 44472509) B44472509
theorem B52717499 : Blo 1624511 52717499 := bstep (se 1 (by rfl) ⟨39538124, by rfl⟩ : syracuseStep 52717499 = 79076249) B79076249
theorem B8783873 : Blo 1624511 8783873 := bstep (se 2 (by rfl) ⟨3293952, by rfl⟩ : syracuseStep 8783873 = 6587905) B6587905
theorem B3655943 : Blo 1624511 3655943 := bstep (se 1 (by rfl) ⟨2741957, by rfl⟩ : syracuseStep 3655943 = 5483915) B5483915
theorem B1829191 : Blo 1624511 1829191 := bstep (se 1 (by rfl) ⟨1371893, by rfl⟩ : syracuseStep 1829191 = 2743787) B2743787
theorem B3656033 : Blo 1624511 3656033 := bstep (se 2 (by rfl) ⟨1371012, by rfl⟩ : syracuseStep 3656033 = 2742025) B2742025
theorem B1624559 : Blo 1624511 1624559 := bstep (se 1 (by rfl) ⟨1218419, by rfl⟩ : syracuseStep 1624559 = 2436839) B2436839
theorem B1624703 : Blo 1624511 1624703 := bstep (se 1 (by rfl) ⟨1218527, by rfl⟩ : syracuseStep 1624703 = 2437055) B2437055
theorem B1624859 : Blo 1624511 1624859 := bstep (se 1 (by rfl) ⟨1218644, by rfl⟩ : syracuseStep 1624859 = 2437289) B2437289
theorem B11717423 : Blo 1624511 11717423 := bstep (se 1 (by rfl) ⟨8788067, by rfl⟩ : syracuseStep 11717423 = 17576135) B17576135
theorem B1624943 : Blo 1624511 1624943 := bstep (se 1 (by rfl) ⟨1218707, by rfl⟩ : syracuseStep 1624943 = 2437415) B2437415
theorem B80153549 : Blo 1624511 80153549 := bstep (se 3 (by rfl) ⟨15028790, by rfl⟩ : syracuseStep 80153549 = 30057581) B30057581
theorem B1625191 : Blo 1624511 1625191 := bstep (se 1 (by rfl) ⟨1218893, by rfl⟩ : syracuseStep 1625191 = 2437787) B2437787
theorem B1625447 : Blo 1624511 1625447 := bstep (se 1 (by rfl) ⟨1219085, by rfl⟩ : syracuseStep 1625447 = 2438171) B2438171
theorem B3657167 : Blo 1624511 3657167 := bstep (se 1 (by rfl) ⟨2742875, by rfl⟩ : syracuseStep 3657167 = 5485751) B5485751
theorem B1625839 : Blo 1624511 1625839 := bstep (se 1 (by rfl) ⟨1219379, by rfl⟩ : syracuseStep 1625839 = 2438759) B2438759
theorem B375828281 : Blo 1624511 375828281 := bstep (se 2 (by rfl) ⟨140935605, by rfl⟩ : syracuseStep 375828281 = 281871211) B281871211
theorem B14831437 : Blo 1624511 14831437 := bstep (se 3 (by rfl) ⟨2780894, by rfl⟩ : syracuseStep 14831437 = 5561789) B5561789
theorem B3903329 : Blo 1624511 3903329 := bstep (se 2 (by rfl) ⟨1463748, by rfl⟩ : syracuseStep 3903329 = 2927497) B2927497
theorem B16723907 : Blo 1624511 16723907 := bstep (se 1 (by rfl) ⟨12542930, by rfl⟩ : syracuseStep 16723907 = 25085861) B25085861
theorem B2437175 : Blo 1624511 2437175 := bstep (se 1 (by rfl) ⟨1827881, by rfl⟩ : syracuseStep 2437175 = 3655763) B3655763
theorem B16691321 : Blo 1624511 16691321 := bstep (se 2 (by rfl) ⟨6259245, by rfl⟩ : syracuseStep 16691321 = 12518491) B12518491
theorem B3657959 : Blo 1624511 3657959 := bstep (se 1 (by rfl) ⟨2743469, by rfl⟩ : syracuseStep 3657959 = 5486939) B5486939
theorem B2437673 : Blo 1624511 2437673 := bstep (se 2 (by rfl) ⟨914127, by rfl⟩ : syracuseStep 2437673 = 1828255) B1828255
theorem B2437679 : Blo 1624511 2437679 := bstep (se 1 (by rfl) ⟨1828259, by rfl⟩ : syracuseStep 2437679 = 3656519) B3656519
theorem B5485481 : Blo 1624511 5485481 := bstep (se 2 (by rfl) ⟨2057055, by rfl⟩ : syracuseStep 5485481 = 4114111) B4114111
theorem B2438255 : Blo 1624511 2438255 := bstep (se 1 (by rfl) ⟨1828691, by rfl⟩ : syracuseStep 2438255 = 3657383) B3657383
theorem B7410847 : Blo 1624511 7410847 := bstep (se 1 (by rfl) ⟨5558135, by rfl⟩ : syracuseStep 7410847 = 11116271) B11116271
theorem B26375357 : Blo 1624511 26375357 := bstep (se 3 (by rfl) ⟨4945379, by rfl⟩ : syracuseStep 26375357 = 9890759) B9890759
theorem B5486183 : Blo 1624511 5486183 := bstep (se 1 (by rfl) ⟨4114637, by rfl⟩ : syracuseStep 5486183 = 8229275) B8229275
theorem B2438825 : Blo 1624511 2438825 := bstep (se 2 (by rfl) ⟨914559, by rfl⟩ : syracuseStep 2438825 = 1829119) B1829119
theorem B3659489 : Blo 1624511 3659489 := bstep (se 2 (by rfl) ⟨1372308, by rfl⟩ : syracuseStep 3659489 = 2744617) B2744617
theorem B3471103 : Blo 1624511 3471103 := bstep (se 1 (by rfl) ⟨2603327, by rfl⟩ : syracuseStep 3471103 = 5206655) B5206655
theorem B2438951 : Blo 1624511 2438951 := bstep (se 1 (by rfl) ⟨1829213, by rfl⟩ : syracuseStep 2438951 = 3658427) B3658427
theorem B3086191 : Blo 1624511 3086191 := bstep (se 1 (by rfl) ⟨2314643, by rfl⟩ : syracuseStep 3086191 = 4629287) B4629287
theorem B2439023 : Blo 1624511 2439023 := bstep (se 1 (by rfl) ⟨1829267, by rfl⟩ : syracuseStep 2439023 = 3658535) B3658535
theorem B8231057 : Blo 1624511 8231057 := bstep (se 2 (by rfl) ⟨3086646, by rfl⟩ : syracuseStep 8231057 = 6173293) B6173293
theorem B70260929 : Blo 1624511 70260929 := bstep (se 2 (by rfl) ⟨26347848, by rfl⟩ : syracuseStep 70260929 = 52695697) B52695697
theorem B15022279 : Blo 1624511 15022279 := bstep (se 1 (by rfl) ⟨11266709, by rfl⟩ : syracuseStep 15022279 = 22533419) B22533419
theorem B2439647 : Blo 1624511 2439647 := bstep (se 1 (by rfl) ⟨1829735, by rfl⟩ : syracuseStep 2439647 = 3659471) B3659471
theorem B6175223 : Blo 1624511 6175223 := bstep (se 1 (by rfl) ⟨4631417, by rfl⟩ : syracuseStep 6175223 = 9262835) B9262835
theorem B11713385 : Blo 1624511 11713385 := bstep (se 2 (by rfl) ⟨4392519, by rfl⟩ : syracuseStep 11713385 = 8785039) B8785039
theorem B3907577 : Blo 1624511 3907577 := bstep (se 2 (by rfl) ⟨1465341, by rfl⟩ : syracuseStep 3907577 = 2930683) B2930683
theorem B13188329 : Blo 1624511 13188329 := bstep (se 2 (by rfl) ⟨4945623, by rfl⟩ : syracuseStep 13188329 = 9891247) B9891247
theorem B15629921 : Blo 1624511 15629921 := bstep (se 2 (by rfl) ⟨5861220, by rfl⟩ : syracuseStep 15629921 = 11722441) B11722441
theorem B27770525 : Blo 1624511 27770525 := bstep (se 3 (by rfl) ⟨5206973, by rfl⟩ : syracuseStep 27770525 = 10413947) B10413947
theorem B15630731 : Blo 1624511 15630731 := bstep (se 1 (by rfl) ⟨11723048, by rfl⟩ : syracuseStep 15630731 = 23446097) B23446097
theorem B8782445 : Blo 1624511 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B80118821 : Blo 1624511 80118821 := bstep (se 4 (by rfl) ⟨7511139, by rfl⟩ : syracuseStep 80118821 = 15022279) B15022279
theorem B35144999 : Blo 1624511 35144999 := bstep (se 1 (by rfl) ⟨26358749, by rfl⟩ : syracuseStep 35144999 = 52717499) B52717499
theorem B9881129 : Blo 1624511 9881129 := bstep (se 2 (by rfl) ⟨3705423, by rfl⟩ : syracuseStep 9881129 = 7410847) B7410847
theorem B7808923 : Blo 1624511 7808923 := bstep (se 1 (by rfl) ⟨5856692, by rfl⟩ : syracuseStep 7808923 = 11713385) B11713385
theorem B8792219 : Blo 1624511 8792219 := bstep (se 1 (by rfl) ⟨6594164, by rfl⟩ : syracuseStep 8792219 = 13188329) B13188329
theorem B4114921 : Blo 1624511 4114921 := bstep (se 2 (by rfl) ⟨1543095, by rfl⟩ : syracuseStep 4114921 = 3086191) B3086191
theorem B1624783 : Blo 1624511 1624783 := bstep (se 1 (by rfl) ⟨1218587, by rfl⟩ : syracuseStep 1624783 = 2437175) B2437175
theorem B11127547 : Blo 1624511 11127547 := bstep (se 1 (by rfl) ⟨8345660, by rfl⟩ : syracuseStep 11127547 = 16691321) B16691321
theorem B1625115 : Blo 1624511 1625115 := bstep (se 1 (by rfl) ⟨1218836, by rfl⟩ : syracuseStep 1625115 = 2437673) B2437673
theorem B1625119 : Blo 1624511 1625119 := bstep (se 1 (by rfl) ⟨1218839, by rfl⟩ : syracuseStep 1625119 = 2437679) B2437679
theorem B3656987 : Blo 1624511 3656987 := bstep (se 1 (by rfl) ⟨2742740, by rfl⟩ : syracuseStep 3656987 = 5485481) B5485481
theorem B67677535 : Blo 1624511 67677535 := bstep (se 1 (by rfl) ⟨50758151, by rfl⟩ : syracuseStep 67677535 = 101516303) B101516303
theorem B1625503 : Blo 1624511 1625503 := bstep (se 1 (by rfl) ⟨1219127, by rfl⟩ : syracuseStep 1625503 = 2438255) B2438255
theorem B17583571 : Blo 1624511 17583571 := bstep (se 1 (by rfl) ⟨13187678, by rfl⟩ : syracuseStep 17583571 = 26375357) B26375357
theorem B3657455 : Blo 1624511 3657455 := bstep (se 1 (by rfl) ⟨2743091, by rfl⟩ : syracuseStep 3657455 = 5486183) B5486183
theorem B1625883 : Blo 1624511 1625883 := bstep (se 1 (by rfl) ⟨1219412, by rfl⟩ : syracuseStep 1625883 = 2438825) B2438825
theorem B1625967 : Blo 1624511 1625967 := bstep (se 1 (by rfl) ⟨1219475, by rfl⟩ : syracuseStep 1625967 = 2438951) B2438951
theorem B1626015 : Blo 1624511 1626015 := bstep (se 1 (by rfl) ⟨1219511, by rfl⟩ : syracuseStep 1626015 = 2439023) B2439023
theorem B2437295 : Blo 1624511 2437295 := bstep (se 1 (by rfl) ⟨1827971, by rfl⟩ : syracuseStep 2437295 = 3655943) B3655943
theorem B2437355 : Blo 1624511 2437355 := bstep (se 1 (by rfl) ⟨1828016, by rfl⟩ : syracuseStep 2437355 = 3656033) B3656033
theorem B1626431 : Blo 1624511 1626431 := bstep (se 1 (by rfl) ⟨1219823, by rfl⟩ : syracuseStep 1626431 = 2439647) B2439647
theorem B4116815 : Blo 1624511 4116815 := bstep (se 1 (by rfl) ⟨3087611, by rfl⟩ : syracuseStep 4116815 = 6175223) B6175223
theorem B7811615 : Blo 1624511 7811615 := bstep (se 1 (by rfl) ⟨5858711, by rfl⟩ : syracuseStep 7811615 = 11717423) B11717423
theorem B2438111 : Blo 1624511 2438111 := bstep (se 1 (by rfl) ⟨1828583, by rfl⟩ : syracuseStep 2438111 = 3657167) B3657167
theorem B2602219 : Blo 1624511 2602219 := bstep (se 1 (by rfl) ⟨1951664, by rfl⟩ : syracuseStep 2602219 = 3903329) B3903329
theorem B88987049 : Blo 1624511 88987049 := bstep (se 2 (by rfl) ⟨33370143, by rfl⟩ : syracuseStep 88987049 = 66740287) B66740287
theorem B2438639 : Blo 1624511 2438639 := bstep (se 1 (by rfl) ⟨1828979, by rfl⟩ : syracuseStep 2438639 = 3657959) B3657959
theorem B2438921 : Blo 1624511 2438921 := bstep (se 2 (by rfl) ⟨914595, by rfl⟩ : syracuseStep 2438921 = 1829191) B1829191
theorem B19765559 : Blo 1624511 19765559 := bstep (se 1 (by rfl) ⟨14824169, by rfl⟩ : syracuseStep 19765559 = 29648339) B29648339
theorem B2439659 : Blo 1624511 2439659 := bstep (se 1 (by rfl) ⟨1829744, by rfl⟩ : syracuseStep 2439659 = 3659489) B3659489
theorem B5487101 : Blo 1624511 5487101 := bstep (se 3 (by rfl) ⟨1028831, by rfl⟩ : syracuseStep 5487101 = 2057663) B2057663
theorem B5855915 : Blo 1624511 5855915 := bstep (se 1 (by rfl) ⟨4391936, by rfl⟩ : syracuseStep 5855915 = 8783873) B8783873
theorem B5487371 : Blo 1624511 5487371 := bstep (se 1 (by rfl) ⟨4115528, by rfl⟩ : syracuseStep 5487371 = 8231057) B8231057
theorem B46840619 : Blo 1624511 46840619 := bstep (se 1 (by rfl) ⟨35130464, by rfl⟩ : syracuseStep 46840619 = 70260929) B70260929
theorem B53435699 : Blo 1624511 53435699 := bstep (se 1 (by rfl) ⟨40076774, by rfl⟩ : syracuseStep 53435699 = 80153549) B80153549
theorem B4628137 : Blo 1624511 4628137 := bstep (se 2 (by rfl) ⟨1735551, by rfl⟩ : syracuseStep 4628137 = 3471103) B3471103
theorem B10419947 : Blo 1624511 10419947 := bstep (se 1 (by rfl) ⟨7814960, by rfl⟩ : syracuseStep 10419947 = 15629921) B15629921
theorem B19775249 : Blo 1624511 19775249 := bstep (se 2 (by rfl) ⟨7415718, by rfl⟩ : syracuseStep 19775249 = 14831437) B14831437
theorem B18513683 : Blo 1624511 18513683 := bstep (se 1 (by rfl) ⟨13885262, by rfl⟩ : syracuseStep 18513683 = 27770525) B27770525
theorem B250552187 : Blo 1624511 250552187 := bstep (se 1 (by rfl) ⟨187914140, by rfl⟩ : syracuseStep 250552187 = 375828281) B375828281
theorem B11149271 : Blo 1624511 11149271 := bstep (se 1 (by rfl) ⟨8361953, by rfl⟩ : syracuseStep 11149271 = 16723907) B16723907
theorem B2605051 : Blo 1624511 2605051 := bstep (se 1 (by rfl) ⟨1953788, by rfl⟩ : syracuseStep 2605051 = 3907577) B3907577
theorem B2744543 : Blo 1624511 2744543 := bstep (se 1 (by rfl) ⟨2058407, by rfl⟩ : syracuseStep 2744543 = 4116815) B4116815
theorem B10420487 : Blo 1624511 10420487 := bstep (se 1 (by rfl) ⟨7815365, by rfl⟩ : syracuseStep 10420487 = 15630731) B15630731
theorem B53412547 : Blo 1624511 53412547 := bstep (se 1 (by rfl) ⟨40059410, by rfl⟩ : syracuseStep 53412547 = 80118821) B80118821
theorem B52708157 : Blo 1624511 52708157 := bstep (se 3 (by rfl) ⟨9882779, by rfl⟩ : syracuseStep 52708157 = 19765559) B19765559
theorem B23429999 : Blo 1624511 23429999 := bstep (se 1 (by rfl) ⟨17572499, by rfl⟩ : syracuseStep 23429999 = 35144999) B35144999
theorem B14836729 : Blo 1624511 14836729 := bstep (se 2 (by rfl) ⟨5563773, by rfl⟩ : syracuseStep 14836729 = 11127547) B11127547
theorem B6587419 : Blo 1624511 6587419 := bstep (se 1 (by rfl) ⟨4940564, by rfl⟩ : syracuseStep 6587419 = 9881129) B9881129
theorem B15615773 : Blo 1624511 15615773 := bstep (se 3 (by rfl) ⟨2927957, by rfl⟩ : syracuseStep 15615773 = 5855915) B5855915
theorem B90236713 : Blo 1624511 90236713 := bstep (se 2 (by rfl) ⟨33838767, by rfl⟩ : syracuseStep 90236713 = 67677535) B67677535
theorem B6170849 : Blo 1624511 6170849 := bstep (se 2 (by rfl) ⟨2314068, by rfl⟩ : syracuseStep 6170849 = 4628137) B4628137
theorem B13183499 : Blo 1624511 13183499 := bstep (se 1 (by rfl) ⟨9887624, by rfl⟩ : syracuseStep 13183499 = 19775249) B19775249
theorem B7432847 : Blo 1624511 7432847 := bstep (se 1 (by rfl) ⟨5574635, by rfl⟩ : syracuseStep 7432847 = 11149271) B11149271
theorem B1624863 : Blo 1624511 1624863 := bstep (se 1 (by rfl) ⟨1218647, by rfl⟩ : syracuseStep 1624863 = 2437295) B2437295
theorem B1624903 : Blo 1624511 1624903 := bstep (se 1 (by rfl) ⟨1218677, by rfl⟩ : syracuseStep 1624903 = 2437355) B2437355
theorem B1625407 : Blo 1624511 1625407 := bstep (se 1 (by rfl) ⟨1219055, by rfl⟩ : syracuseStep 1625407 = 2438111) B2438111
theorem B1625759 : Blo 1624511 1625759 := bstep (se 1 (by rfl) ⟨1219319, by rfl⟩ : syracuseStep 1625759 = 2438639) B2438639
theorem B1625947 : Blo 1624511 1625947 := bstep (se 1 (by rfl) ⟨1219460, by rfl⟩ : syracuseStep 1625947 = 2438921) B2438921
theorem B5861479 : Blo 1624511 5861479 := bstep (se 1 (by rfl) ⟨4396109, by rfl⟩ : syracuseStep 5861479 = 8792219) B8792219
theorem B3469625 : Blo 1624511 3469625 := bstep (se 2 (by rfl) ⟨1301109, by rfl⟩ : syracuseStep 3469625 = 2602219) B2602219
theorem B1626439 : Blo 1624511 1626439 := bstep (se 1 (by rfl) ⟨1219829, by rfl⟩ : syracuseStep 1626439 = 2439659) B2439659
theorem B3658067 : Blo 1624511 3658067 := bstep (se 1 (by rfl) ⟨2743550, by rfl⟩ : syracuseStep 3658067 = 5487101) B5487101
theorem B3658247 : Blo 1624511 3658247 := bstep (se 1 (by rfl) ⟨2743685, by rfl⟩ : syracuseStep 3658247 = 5487371) B5487371
theorem B2437991 : Blo 1624511 2437991 := bstep (se 1 (by rfl) ⟨1828493, by rfl⟩ : syracuseStep 2437991 = 3656987) B3656987
theorem B35623799 : Blo 1624511 35623799 := bstep (se 1 (by rfl) ⟨26717849, by rfl⟩ : syracuseStep 35623799 = 53435699) B53435699
theorem B2438303 : Blo 1624511 2438303 := bstep (se 1 (by rfl) ⟨1828727, by rfl⟩ : syracuseStep 2438303 = 3657455) B3657455
theorem B12342455 : Blo 1624511 12342455 := bstep (se 1 (by rfl) ⟨9256841, by rfl⟩ : syracuseStep 12342455 = 18513683) B18513683
theorem B5207743 : Blo 1624511 5207743 := bstep (se 1 (by rfl) ⟨3905807, by rfl⟩ : syracuseStep 5207743 = 7811615) B7811615
theorem B5486561 : Blo 1624511 5486561 := bstep (se 2 (by rfl) ⟨2057460, by rfl⟩ : syracuseStep 5486561 = 4114921) B4114921
theorem B59324699 : Blo 1624511 59324699 := bstep (se 1 (by rfl) ⟨44493524, by rfl⟩ : syracuseStep 59324699 = 88987049) B88987049
theorem B23419853 : Blo 1624511 23419853 := bstep (se 3 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 23419853 = 8782445) B8782445
theorem B31227079 : Blo 1624511 31227079 := bstep (se 1 (by rfl) ⟨23420309, by rfl⟩ : syracuseStep 31227079 = 46840619) B46840619
theorem B23444761 : Blo 1624511 23444761 := bstep (se 2 (by rfl) ⟨8791785, by rfl⟩ : syracuseStep 23444761 = 17583571) B17583571
theorem B6946631 : Blo 1624511 6946631 := bstep (se 1 (by rfl) ⟨5209973, by rfl⟩ : syracuseStep 6946631 = 10419947) B10419947
theorem B10411897 : Blo 1624511 10411897 := bstep (se 2 (by rfl) ⟨3904461, by rfl⟩ : syracuseStep 10411897 = 7808923) B7808923
theorem B167034791 : Blo 1624511 167034791 := bstep (se 1 (by rfl) ⟨125276093, by rfl⟩ : syracuseStep 167034791 = 250552187) B250552187
theorem B3473401 : Blo 1624511 3473401 := bstep (se 2 (by rfl) ⟨1302525, by rfl⟩ : syracuseStep 3473401 = 2605051) B2605051
theorem B7815305 : Blo 1624511 7815305 := bstep (se 2 (by rfl) ⟨2930739, by rfl⟩ : syracuseStep 7815305 = 5861479) B5861479
theorem B6946991 : Blo 1624511 6946991 := bstep (se 1 (by rfl) ⟨5210243, by rfl⟩ : syracuseStep 6946991 = 10420487) B10420487
theorem B23749199 : Blo 1624511 23749199 := bstep (se 1 (by rfl) ⟨17811899, by rfl⟩ : syracuseStep 23749199 = 35623799) B35623799
theorem B8783225 : Blo 1624511 8783225 := bstep (se 2 (by rfl) ⟨3293709, by rfl⟩ : syracuseStep 8783225 = 6587419) B6587419
theorem B4113899 : Blo 1624511 4113899 := bstep (se 1 (by rfl) ⟨3085424, by rfl⟩ : syracuseStep 4113899 = 6170849) B6170849
theorem B4631087 : Blo 1624511 4631087 := bstep (se 1 (by rfl) ⟨3473315, by rfl⟩ : syracuseStep 4631087 = 6946631) B6946631
theorem B111356527 : Blo 1624511 111356527 := bstep (se 1 (by rfl) ⟨83517395, by rfl⟩ : syracuseStep 111356527 = 167034791) B167034791
theorem B4631201 : Blo 1624511 4631201 := bstep (se 2 (by rfl) ⟨1736700, by rfl⟩ : syracuseStep 4631201 = 3473401) B3473401
theorem B1829695 : Blo 1624511 1829695 := bstep (se 1 (by rfl) ⟨1372271, by rfl⟩ : syracuseStep 1829695 = 2744543) B2744543
theorem B2313083 : Blo 1624511 2313083 := bstep (se 1 (by rfl) ⟨1734812, by rfl⟩ : syracuseStep 2313083 = 3469625) B3469625
theorem B35138771 : Blo 1624511 35138771 := bstep (se 1 (by rfl) ⟨26354078, by rfl⟩ : syracuseStep 35138771 = 52708157) B52708157
theorem B1625327 : Blo 1624511 1625327 := bstep (se 1 (by rfl) ⟨1218995, by rfl⟩ : syracuseStep 1625327 = 2437991) B2437991
theorem B1625535 : Blo 1624511 1625535 := bstep (se 1 (by rfl) ⟨1219151, by rfl⟩ : syracuseStep 1625535 = 2438303) B2438303
theorem B8228303 : Blo 1624511 8228303 := bstep (se 1 (by rfl) ⟨6171227, by rfl⟩ : syracuseStep 8228303 = 12342455) B12342455
theorem B71216729 : Blo 1624511 71216729 := bstep (se 2 (by rfl) ⟨26706273, by rfl⟩ : syracuseStep 71216729 = 53412547) B53412547
theorem B3657707 : Blo 1624511 3657707 := bstep (se 1 (by rfl) ⟨2743280, by rfl⟩ : syracuseStep 3657707 = 5486561) B5486561
theorem B41636105 : Blo 1624511 41636105 := bstep (se 2 (by rfl) ⟨15613539, by rfl⟩ : syracuseStep 41636105 = 31227079) B31227079
theorem B6943657 : Blo 1624511 6943657 := bstep (se 2 (by rfl) ⟨2603871, by rfl⟩ : syracuseStep 6943657 = 5207743) B5207743
theorem B13882529 : Blo 1624511 13882529 := bstep (se 2 (by rfl) ⟨5205948, by rfl⟩ : syracuseStep 13882529 = 10411897) B10411897
theorem B2438711 : Blo 1624511 2438711 := bstep (se 1 (by rfl) ⟨1829033, by rfl⟩ : syracuseStep 2438711 = 3658067) B3658067
theorem B2438831 : Blo 1624511 2438831 := bstep (se 1 (by rfl) ⟨1829123, by rfl⟩ : syracuseStep 2438831 = 3658247) B3658247
theorem B15619999 : Blo 1624511 15619999 := bstep (se 1 (by rfl) ⟨11714999, by rfl⟩ : syracuseStep 15619999 = 23429999) B23429999
theorem B10410515 : Blo 1624511 10410515 := bstep (se 1 (by rfl) ⟨7807886, by rfl⟩ : syracuseStep 10410515 = 15615773) B15615773
theorem B19782305 : Blo 1624511 19782305 := bstep (se 2 (by rfl) ⟨7418364, by rfl⟩ : syracuseStep 19782305 = 14836729) B14836729
theorem B39549799 : Blo 1624511 39549799 := bstep (se 1 (by rfl) ⟨29662349, by rfl⟩ : syracuseStep 39549799 = 59324699) B59324699
theorem B8788999 : Blo 1624511 8788999 := bstep (se 1 (by rfl) ⟨6591749, by rfl⟩ : syracuseStep 8788999 = 13183499) B13183499
theorem B31259681 : Blo 1624511 31259681 := bstep (se 2 (by rfl) ⟨11722380, by rfl⟩ : syracuseStep 31259681 = 23444761) B23444761
theorem B4955231 : Blo 1624511 4955231 := bstep (se 1 (by rfl) ⟨3716423, by rfl⟩ : syracuseStep 4955231 = 7432847) B7432847
theorem B15613235 : Blo 1624511 15613235 := bstep (se 1 (by rfl) ⟨11709926, by rfl⟩ : syracuseStep 15613235 = 23419853) B23419853
theorem B120315617 : Blo 1624511 120315617 := bstep (se 2 (by rfl) ⟨45118356, by rfl⟩ : syracuseStep 120315617 = 90236713) B90236713
theorem B13213949 : Blo 1624511 13213949 := bstep (se 3 (by rfl) ⟨2477615, by rfl⟩ : syracuseStep 13213949 = 4955231) B4955231
theorem B20840813 : Blo 1624511 20840813 := bstep (se 3 (by rfl) ⟨3907652, by rfl⟩ : syracuseStep 20840813 = 7815305) B7815305
theorem B52733065 : Blo 1624511 52733065 := bstep (se 2 (by rfl) ⟨19774899, by rfl⟩ : syracuseStep 52733065 = 39549799) B39549799
theorem B9258209 : Blo 1624511 9258209 := bstep (se 2 (by rfl) ⟨3471828, by rfl⟩ : syracuseStep 9258209 = 6943657) B6943657
theorem B6940343 : Blo 1624511 6940343 := bstep (se 1 (by rfl) ⟨5205257, by rfl⟩ : syracuseStep 6940343 = 10410515) B10410515
theorem B80210411 : Blo 1624511 80210411 := bstep (se 1 (by rfl) ⟨60157808, by rfl⟩ : syracuseStep 80210411 = 120315617) B120315617
theorem B20826665 : Blo 1624511 20826665 := bstep (se 2 (by rfl) ⟨7809999, by rfl⟩ : syracuseStep 20826665 = 15619999) B15619999
theorem B4631327 : Blo 1624511 4631327 := bstep (se 1 (by rfl) ⟨3473495, by rfl⟩ : syracuseStep 4631327 = 6946991) B6946991
theorem B27757403 : Blo 1624511 27757403 := bstep (se 1 (by rfl) ⟨20818052, by rfl⟩ : syracuseStep 27757403 = 41636105) B41636105
theorem B148475369 : Blo 1624511 148475369 := bstep (se 2 (by rfl) ⟨55678263, by rfl⟩ : syracuseStep 148475369 = 111356527) B111356527
theorem B1625807 : Blo 1624511 1625807 := bstep (se 1 (by rfl) ⟨1219355, by rfl⟩ : syracuseStep 1625807 = 2438711) B2438711
theorem B1625887 : Blo 1624511 1625887 := bstep (se 1 (by rfl) ⟨1219415, by rfl⟩ : syracuseStep 1625887 = 2438831) B2438831
theorem B11718665 : Blo 1624511 11718665 := bstep (se 2 (by rfl) ⟨4394499, by rfl⟩ : syracuseStep 11718665 = 8788999) B8788999
theorem B23425847 : Blo 1624511 23425847 := bstep (se 1 (by rfl) ⟨17569385, by rfl⟩ : syracuseStep 23425847 = 35138771) B35138771
theorem B10408823 : Blo 1624511 10408823 := bstep (se 1 (by rfl) ⟨7806617, by rfl⟩ : syracuseStep 10408823 = 15613235) B15613235
theorem B5485535 : Blo 1624511 5485535 := bstep (se 1 (by rfl) ⟨4114151, by rfl⟩ : syracuseStep 5485535 = 8228303) B8228303
theorem B47477819 : Blo 1624511 47477819 := bstep (se 1 (by rfl) ⟨35608364, by rfl⟩ : syracuseStep 47477819 = 71216729) B71216729
theorem B2438471 : Blo 1624511 2438471 := bstep (se 1 (by rfl) ⟨1828853, by rfl⟩ : syracuseStep 2438471 = 3657707) B3657707
theorem B15832799 : Blo 1624511 15832799 := bstep (se 1 (by rfl) ⟨11874599, by rfl⟩ : syracuseStep 15832799 = 23749199) B23749199
theorem B9255019 : Blo 1624511 9255019 := bstep (se 1 (by rfl) ⟨6941264, by rfl⟩ : syracuseStep 9255019 = 13882529) B13882529
theorem B5855483 : Blo 1624511 5855483 := bstep (se 1 (by rfl) ⟨4391612, by rfl⟩ : syracuseStep 5855483 = 8783225) B8783225
theorem B2742599 : Blo 1624511 2742599 := bstep (se 1 (by rfl) ⟨2056949, by rfl⟩ : syracuseStep 2742599 = 4113899) B4113899
theorem B2439593 : Blo 1624511 2439593 := bstep (se 2 (by rfl) ⟨914847, by rfl⟩ : syracuseStep 2439593 = 1829695) B1829695
theorem B3087391 : Blo 1624511 3087391 := bstep (se 1 (by rfl) ⟨2315543, by rfl⟩ : syracuseStep 3087391 = 4631087) B4631087
theorem B3087467 : Blo 1624511 3087467 := bstep (se 1 (by rfl) ⟨2315600, by rfl⟩ : syracuseStep 3087467 = 4631201) B4631201
theorem B13188203 : Blo 1624511 13188203 := bstep (se 1 (by rfl) ⟨9891152, by rfl⟩ : syracuseStep 13188203 = 19782305) B19782305
theorem B20839787 : Blo 1624511 20839787 := bstep (se 1 (by rfl) ⟨15629840, by rfl⟩ : syracuseStep 20839787 = 31259681) B31259681
theorem B6168221 : Blo 1624511 6168221 := bstep (se 3 (by rfl) ⟨1156541, by rfl⟩ : syracuseStep 6168221 = 2313083) B2313083
theorem B13893875 : Blo 1624511 13893875 := bstep (se 1 (by rfl) ⟨10420406, by rfl⟩ : syracuseStep 13893875 = 20840813) B20840813
theorem B6939215 : Blo 1624511 6939215 := bstep (se 1 (by rfl) ⟨5204411, by rfl⟩ : syracuseStep 6939215 = 10408823) B10408823
theorem B1828399 : Blo 1624511 1828399 := bstep (se 1 (by rfl) ⟨1371299, by rfl⟩ : syracuseStep 1828399 = 2742599) B2742599
theorem B2058311 : Blo 1624511 2058311 := bstep (se 1 (by rfl) ⟨1543733, by rfl⟩ : syracuseStep 2058311 = 3087467) B3087467
theorem B8792135 : Blo 1624511 8792135 := bstep (se 1 (by rfl) ⟨6594101, by rfl⟩ : syracuseStep 8792135 = 13188203) B13188203
theorem B12340025 : Blo 1624511 12340025 := bstep (se 2 (by rfl) ⟨4627509, by rfl⟩ : syracuseStep 12340025 = 9255019) B9255019
theorem B15617231 : Blo 1624511 15617231 := bstep (se 1 (by rfl) ⟨11712923, by rfl⟩ : syracuseStep 15617231 = 23425847) B23425847
theorem B3657023 : Blo 1624511 3657023 := bstep (se 1 (by rfl) ⟨2742767, by rfl⟩ : syracuseStep 3657023 = 5485535) B5485535
theorem B35237197 : Blo 1624511 35237197 := bstep (se 3 (by rfl) ⟨6606974, by rfl⟩ : syracuseStep 35237197 = 13213949) B13213949
theorem B6172139 : Blo 1624511 6172139 := bstep (se 1 (by rfl) ⟨4629104, by rfl⟩ : syracuseStep 6172139 = 9258209) B9258209
theorem B1625647 : Blo 1624511 1625647 := bstep (se 1 (by rfl) ⟨1219235, by rfl⟩ : syracuseStep 1625647 = 2438471) B2438471
theorem B10555199 : Blo 1624511 10555199 := bstep (se 1 (by rfl) ⟨7916399, by rfl⟩ : syracuseStep 10555199 = 15832799) B15832799
theorem B4116521 : Blo 1624511 4116521 := bstep (se 2 (by rfl) ⟨1543695, by rfl⟩ : syracuseStep 4116521 = 3087391) B3087391
theorem B3903655 : Blo 1624511 3903655 := bstep (se 1 (by rfl) ⟨2927741, by rfl⟩ : syracuseStep 3903655 = 5855483) B5855483
theorem B1626395 : Blo 1624511 1626395 := bstep (se 1 (by rfl) ⟨1219796, by rfl⟩ : syracuseStep 1626395 = 2439593) B2439593
theorem B53473607 : Blo 1624511 53473607 := bstep (se 1 (by rfl) ⟨40105205, by rfl⟩ : syracuseStep 53473607 = 80210411) B80210411
theorem B7812443 : Blo 1624511 7812443 := bstep (se 1 (by rfl) ⟨5859332, by rfl⟩ : syracuseStep 7812443 = 11718665) B11718665
theorem B31651879 : Blo 1624511 31651879 := bstep (se 1 (by rfl) ⟨23738909, by rfl⟩ : syracuseStep 31651879 = 47477819) B47477819
theorem B4626895 : Blo 1624511 4626895 := bstep (se 1 (by rfl) ⟨3470171, by rfl⟩ : syracuseStep 4626895 = 6940343) B6940343
theorem B70310753 : Blo 1624511 70310753 := bstep (se 2 (by rfl) ⟨26366532, by rfl⟩ : syracuseStep 70310753 = 52733065) B52733065
theorem B13884443 : Blo 1624511 13884443 := bstep (se 1 (by rfl) ⟨10413332, by rfl⟩ : syracuseStep 13884443 = 20826665) B20826665
theorem B3087551 : Blo 1624511 3087551 := bstep (se 1 (by rfl) ⟨2315663, by rfl⟩ : syracuseStep 3087551 = 4631327) B4631327
theorem B18504935 : Blo 1624511 18504935 := bstep (se 1 (by rfl) ⟨13878701, by rfl⟩ : syracuseStep 18504935 = 27757403) B27757403
theorem B13893191 : Blo 1624511 13893191 := bstep (se 1 (by rfl) ⟨10419893, by rfl⟩ : syracuseStep 13893191 = 20839787) B20839787
theorem B98983579 : Blo 1624511 98983579 := bstep (se 1 (by rfl) ⟨74237684, by rfl⟩ : syracuseStep 98983579 = 148475369) B148475369
theorem B4112147 : Blo 1624511 4112147 := bstep (se 1 (by rfl) ⟨3084110, by rfl⟩ : syracuseStep 4112147 = 6168221) B6168221
theorem B2744347 : Blo 1624511 2744347 := bstep (se 1 (by rfl) ⟨2058260, by rfl⟩ : syracuseStep 2744347 = 4116521) B4116521
theorem B5488829 : Blo 1624511 5488829 := bstep (se 3 (by rfl) ⟨1029155, by rfl⟩ : syracuseStep 5488829 = 2058311) B2058311
theorem B6169193 : Blo 1624511 6169193 := bstep (se 2 (by rfl) ⟨2313447, by rfl⟩ : syracuseStep 6169193 = 4626895) B4626895
theorem B46982929 : Blo 1624511 46982929 := bstep (se 2 (by rfl) ⟨17618598, by rfl⟩ : syracuseStep 46982929 = 35237197) B35237197
theorem B8226683 : Blo 1624511 8226683 := bstep (se 1 (by rfl) ⟨6170012, by rfl⟩ : syracuseStep 8226683 = 12340025) B12340025
theorem B2058367 : Blo 1624511 2058367 := bstep (se 1 (by rfl) ⟨1543775, by rfl⟩ : syracuseStep 2058367 = 3087551) B3087551
theorem B4114759 : Blo 1624511 4114759 := bstep (se 1 (by rfl) ⟨3086069, by rfl⟩ : syracuseStep 4114759 = 6172139) B6172139
theorem B5204873 : Blo 1624511 5204873 := bstep (se 2 (by rfl) ⟨1951827, by rfl⟩ : syracuseStep 5204873 = 3903655) B3903655
theorem B5861423 : Blo 1624511 5861423 := bstep (se 1 (by rfl) ⟨4396067, by rfl⟩ : syracuseStep 5861423 = 8792135) B8792135
theorem B2437865 : Blo 1624511 2437865 := bstep (se 2 (by rfl) ⟨914199, by rfl⟩ : syracuseStep 2437865 = 1828399) B1828399
theorem B131978105 : Blo 1624511 131978105 := bstep (se 2 (by rfl) ⟨49491789, by rfl⟩ : syracuseStep 131978105 = 98983579) B98983579
theorem B2438015 : Blo 1624511 2438015 := bstep (se 1 (by rfl) ⟨1828511, by rfl⟩ : syracuseStep 2438015 = 3657023) B3657023
theorem B9262127 : Blo 1624511 9262127 := bstep (se 1 (by rfl) ⟨6946595, by rfl⟩ : syracuseStep 9262127 = 13893191) B13893191
theorem B2741431 : Blo 1624511 2741431 := bstep (se 1 (by rfl) ⟨2056073, by rfl⟩ : syracuseStep 2741431 = 4112147) B4112147
theorem B42202505 : Blo 1624511 42202505 := bstep (se 2 (by rfl) ⟨15825939, by rfl⟩ : syracuseStep 42202505 = 31651879) B31651879
theorem B9262583 : Blo 1624511 9262583 := bstep (se 1 (by rfl) ⟨6946937, by rfl⟩ : syracuseStep 9262583 = 13893875) B13893875
theorem B35649071 : Blo 1624511 35649071 := bstep (se 1 (by rfl) ⟨26736803, by rfl⟩ : syracuseStep 35649071 = 53473607) B53473607
theorem B4626143 : Blo 1624511 4626143 := bstep (se 1 (by rfl) ⟨3469607, by rfl⟩ : syracuseStep 4626143 = 6939215) B6939215
theorem B5208295 : Blo 1624511 5208295 := bstep (se 1 (by rfl) ⟨3906221, by rfl⟩ : syracuseStep 5208295 = 7812443) B7812443
theorem B46873835 : Blo 1624511 46873835 := bstep (se 1 (by rfl) ⟨35155376, by rfl⟩ : syracuseStep 46873835 = 70310753) B70310753
theorem B9256295 : Blo 1624511 9256295 := bstep (se 1 (by rfl) ⟨6942221, by rfl⟩ : syracuseStep 9256295 = 13884443) B13884443
theorem B10411487 : Blo 1624511 10411487 := bstep (se 1 (by rfl) ⟨7808615, by rfl⟩ : syracuseStep 10411487 = 15617231) B15617231
theorem B12336623 : Blo 1624511 12336623 := bstep (se 1 (by rfl) ⟨9252467, by rfl⟩ : syracuseStep 12336623 = 18504935) B18504935
theorem B7036799 : Blo 1624511 7036799 := bstep (se 1 (by rfl) ⟨5277599, by rfl⟩ : syracuseStep 7036799 = 10555199) B10555199
theorem B3907615 : Blo 1624511 3907615 := bstep (se 1 (by rfl) ⟨2930711, by rfl⟩ : syracuseStep 3907615 = 5861423) B5861423
theorem B2744489 : Blo 1624511 2744489 := bstep (se 2 (by rfl) ⟨1029183, by rfl⟩ : syracuseStep 2744489 = 2058367) B2058367
theorem B4112795 : Blo 1624511 4112795 := bstep (se 1 (by rfl) ⟨3084596, by rfl⟩ : syracuseStep 4112795 = 6169193) B6169193
theorem B23766047 : Blo 1624511 23766047 := bstep (se 1 (by rfl) ⟨17824535, by rfl⟩ : syracuseStep 23766047 = 35649071) B35649071
theorem B3655241 : Blo 1624511 3655241 := bstep (se 2 (by rfl) ⟨1370715, by rfl⟩ : syracuseStep 3655241 = 2741431) B2741431
theorem B6170863 : Blo 1624511 6170863 := bstep (se 1 (by rfl) ⟨4628147, by rfl⟩ : syracuseStep 6170863 = 9256295) B9256295
theorem B6940991 : Blo 1624511 6940991 := bstep (se 1 (by rfl) ⟨5205743, by rfl⟩ : syracuseStep 6940991 = 10411487) B10411487
theorem B1625243 : Blo 1624511 1625243 := bstep (se 1 (by rfl) ⟨1218932, by rfl⟩ : syracuseStep 1625243 = 2437865) B2437865
theorem B87985403 : Blo 1624511 87985403 := bstep (se 1 (by rfl) ⟨65989052, by rfl⟩ : syracuseStep 87985403 = 131978105) B131978105
theorem B1625343 : Blo 1624511 1625343 := bstep (se 1 (by rfl) ⟨1219007, by rfl⟩ : syracuseStep 1625343 = 2438015) B2438015
theorem B3084095 : Blo 1624511 3084095 := bstep (se 1 (by rfl) ⟨2313071, by rfl⟩ : syracuseStep 3084095 = 4626143) B4626143
theorem B5484455 : Blo 1624511 5484455 := bstep (se 1 (by rfl) ⟨4113341, by rfl⟩ : syracuseStep 5484455 = 8226683) B8226683
theorem B3469915 : Blo 1624511 3469915 := bstep (se 1 (by rfl) ⟨2602436, by rfl⟩ : syracuseStep 3469915 = 5204873) B5204873
theorem B31249223 : Blo 1624511 31249223 := bstep (se 1 (by rfl) ⟨23436917, by rfl⟩ : syracuseStep 31249223 = 46873835) B46873835
theorem B18764797 : Blo 1624511 18764797 := bstep (se 3 (by rfl) ⟨3518399, by rfl⟩ : syracuseStep 18764797 = 7036799) B7036799
theorem B3659129 : Blo 1624511 3659129 := bstep (se 2 (by rfl) ⟨1372173, by rfl⟩ : syracuseStep 3659129 = 2744347) B2744347
theorem B3659219 : Blo 1624511 3659219 := bstep (se 1 (by rfl) ⟨2744414, by rfl⟩ : syracuseStep 3659219 = 5488829) B5488829
theorem B6944393 : Blo 1624511 6944393 := bstep (se 2 (by rfl) ⟨2604147, by rfl⟩ : syracuseStep 6944393 = 5208295) B5208295
theorem B5486345 : Blo 1624511 5486345 := bstep (se 2 (by rfl) ⟨2057379, by rfl⟩ : syracuseStep 5486345 = 4114759) B4114759
theorem B6174751 : Blo 1624511 6174751 := bstep (se 1 (by rfl) ⟨4631063, by rfl⟩ : syracuseStep 6174751 = 9262127) B9262127
theorem B6175055 : Blo 1624511 6175055 := bstep (se 1 (by rfl) ⟨4631291, by rfl⟩ : syracuseStep 6175055 = 9262583) B9262583
theorem B112540013 : Blo 1624511 112540013 := bstep (se 3 (by rfl) ⟨21101252, by rfl⟩ : syracuseStep 112540013 = 42202505) B42202505
theorem B8224415 : Blo 1624511 8224415 := bstep (se 1 (by rfl) ⟨6168311, by rfl⟩ : syracuseStep 8224415 = 12336623) B12336623
theorem B62643905 : Blo 1624511 62643905 := bstep (se 2 (by rfl) ⟨23491464, by rfl⟩ : syracuseStep 62643905 = 46982929) B46982929
theorem B8233001 : Blo 1624511 8233001 := bstep (se 2 (by rfl) ⟨3087375, by rfl⟩ : syracuseStep 8233001 = 6174751) B6174751
theorem B5210153 : Blo 1624511 5210153 := bstep (se 2 (by rfl) ⟨1953807, by rfl⟩ : syracuseStep 5210153 = 3907615) B3907615
theorem B20832815 : Blo 1624511 20832815 := bstep (se 1 (by rfl) ⟨15624611, by rfl⟩ : syracuseStep 20832815 = 31249223) B31249223
theorem B15844031 : Blo 1624511 15844031 := bstep (se 1 (by rfl) ⟨11883023, by rfl⟩ : syracuseStep 15844031 = 23766047) B23766047
theorem B4629595 : Blo 1624511 4629595 := bstep (se 1 (by rfl) ⟨3472196, by rfl⟩ : syracuseStep 4629595 = 6944393) B6944393
theorem B25019729 : Blo 1624511 25019729 := bstep (se 2 (by rfl) ⟨9382398, by rfl⟩ : syracuseStep 25019729 = 18764797) B18764797
theorem B58656935 : Blo 1624511 58656935 := bstep (se 1 (by rfl) ⟨43992701, by rfl⟩ : syracuseStep 58656935 = 87985403) B87985403
theorem B5482943 : Blo 1624511 5482943 := bstep (se 1 (by rfl) ⟨4112207, by rfl⟩ : syracuseStep 5482943 = 8224415) B8224415
theorem B3656303 : Blo 1624511 3656303 := bstep (se 1 (by rfl) ⟨2742227, by rfl⟩ : syracuseStep 3656303 = 5484455) B5484455
theorem B1829659 : Blo 1624511 1829659 := bstep (se 1 (by rfl) ⟨1372244, by rfl⟩ : syracuseStep 1829659 = 2744489) B2744489
theorem B8227817 : Blo 1624511 8227817 := bstep (se 2 (by rfl) ⟨3085431, by rfl⟩ : syracuseStep 8227817 = 6170863) B6170863
theorem B18509309 : Blo 1624511 18509309 := bstep (se 3 (by rfl) ⟨3470495, by rfl⟩ : syracuseStep 18509309 = 6940991) B6940991
theorem B2436827 : Blo 1624511 2436827 := bstep (se 1 (by rfl) ⟨1827620, by rfl⟩ : syracuseStep 2436827 = 3655241) B3655241
theorem B3657563 : Blo 1624511 3657563 := bstep (se 1 (by rfl) ⟨2743172, by rfl⟩ : syracuseStep 3657563 = 5486345) B5486345
theorem B4116703 : Blo 1624511 4116703 := bstep (se 1 (by rfl) ⟨3087527, by rfl⟩ : syracuseStep 4116703 = 6175055) B6175055
theorem B75026675 : Blo 1624511 75026675 := bstep (se 1 (by rfl) ⟨56270006, by rfl⟩ : syracuseStep 75026675 = 112540013) B112540013
theorem B2741863 : Blo 1624511 2741863 := bstep (se 1 (by rfl) ⟨2056397, by rfl⟩ : syracuseStep 2741863 = 4112795) B4112795
theorem B4626553 : Blo 1624511 4626553 := bstep (se 2 (by rfl) ⟨1734957, by rfl⟩ : syracuseStep 4626553 = 3469915) B3469915
theorem B2439419 : Blo 1624511 2439419 := bstep (se 1 (by rfl) ⟨1829564, by rfl⟩ : syracuseStep 2439419 = 3659129) B3659129
theorem B2439479 : Blo 1624511 2439479 := bstep (se 1 (by rfl) ⟨1829609, by rfl⟩ : syracuseStep 2439479 = 3659219) B3659219
theorem B8224253 : Blo 1624511 8224253 := bstep (se 3 (by rfl) ⟨1542047, by rfl⟩ : syracuseStep 8224253 = 3084095) B3084095
theorem B41762603 : Blo 1624511 41762603 := bstep (se 1 (by rfl) ⟨31321952, by rfl⟩ : syracuseStep 41762603 = 62643905) B62643905
theorem B5488667 : Blo 1624511 5488667 := bstep (se 1 (by rfl) ⟨4116500, by rfl⟩ : syracuseStep 5488667 = 8233001) B8233001
theorem B3473435 : Blo 1624511 3473435 := bstep (se 1 (by rfl) ⟨2605076, by rfl⟩ : syracuseStep 3473435 = 5210153) B5210153
theorem B6168737 : Blo 1624511 6168737 := bstep (se 2 (by rfl) ⟨2313276, by rfl⟩ : syracuseStep 6168737 = 4626553) B4626553
theorem B5488937 : Blo 1624511 5488937 := bstep (se 2 (by rfl) ⟨2058351, by rfl⟩ : syracuseStep 5488937 = 4116703) B4116703
theorem B16679819 : Blo 1624511 16679819 := bstep (se 1 (by rfl) ⟨12509864, by rfl⟩ : syracuseStep 16679819 = 25019729) B25019729
theorem B3655295 : Blo 1624511 3655295 := bstep (se 1 (by rfl) ⟨2741471, by rfl⟩ : syracuseStep 3655295 = 5482943) B5482943
theorem B3655817 : Blo 1624511 3655817 := bstep (se 2 (by rfl) ⟨1370931, by rfl⟩ : syracuseStep 3655817 = 2741863) B2741863
theorem B5482835 : Blo 1624511 5482835 := bstep (se 1 (by rfl) ⟨4112126, by rfl⟩ : syracuseStep 5482835 = 8224253) B8224253
theorem B12339539 : Blo 1624511 12339539 := bstep (se 1 (by rfl) ⟨9254654, by rfl⟩ : syracuseStep 12339539 = 18509309) B18509309
theorem B1624551 : Blo 1624511 1624551 := bstep (se 1 (by rfl) ⟨1218413, by rfl⟩ : syracuseStep 1624551 = 2436827) B2436827
theorem B13888543 : Blo 1624511 13888543 := bstep (se 1 (by rfl) ⟨10416407, by rfl⟩ : syracuseStep 13888543 = 20832815) B20832815
theorem B10562687 : Blo 1624511 10562687 := bstep (se 1 (by rfl) ⟨7922015, by rfl⟩ : syracuseStep 10562687 = 15844031) B15844031
theorem B39104623 : Blo 1624511 39104623 := bstep (se 1 (by rfl) ⟨29328467, by rfl⟩ : syracuseStep 39104623 = 58656935) B58656935
theorem B6172793 : Blo 1624511 6172793 := bstep (se 2 (by rfl) ⟨2314797, by rfl⟩ : syracuseStep 6172793 = 4629595) B4629595
theorem B1626279 : Blo 1624511 1626279 := bstep (se 1 (by rfl) ⟨1219709, by rfl⟩ : syracuseStep 1626279 = 2439419) B2439419
theorem B1626319 : Blo 1624511 1626319 := bstep (se 1 (by rfl) ⟨1219739, by rfl⟩ : syracuseStep 1626319 = 2439479) B2439479
theorem B2437535 : Blo 1624511 2437535 := bstep (se 1 (by rfl) ⟨1828151, by rfl⟩ : syracuseStep 2437535 = 3656303) B3656303
theorem B5485211 : Blo 1624511 5485211 := bstep (se 1 (by rfl) ⟨4113908, by rfl⟩ : syracuseStep 5485211 = 8227817) B8227817
theorem B27841735 : Blo 1624511 27841735 := bstep (se 1 (by rfl) ⟨20881301, by rfl⟩ : syracuseStep 27841735 = 41762603) B41762603
theorem B2438375 : Blo 1624511 2438375 := bstep (se 1 (by rfl) ⟨1828781, by rfl⟩ : syracuseStep 2438375 = 3657563) B3657563
theorem B50017783 : Blo 1624511 50017783 := bstep (se 1 (by rfl) ⟨37513337, by rfl⟩ : syracuseStep 50017783 = 75026675) B75026675
theorem B2439545 : Blo 1624511 2439545 := bstep (se 2 (by rfl) ⟨914829, by rfl⟩ : syracuseStep 2439545 = 1829659) B1829659
theorem B4112491 : Blo 1624511 4112491 := bstep (se 1 (by rfl) ⟨3084368, by rfl⟩ : syracuseStep 4112491 = 6168737) B6168737
theorem B3655223 : Blo 1624511 3655223 := bstep (se 1 (by rfl) ⟨2741417, by rfl⟩ : syracuseStep 3655223 = 5482835) B5482835
theorem B8226359 : Blo 1624511 8226359 := bstep (se 1 (by rfl) ⟨6169769, by rfl⟩ : syracuseStep 8226359 = 12339539) B12339539
theorem B4115195 : Blo 1624511 4115195 := bstep (se 1 (by rfl) ⟨3086396, by rfl⟩ : syracuseStep 4115195 = 6172793) B6172793
theorem B1625023 : Blo 1624511 1625023 := bstep (se 1 (by rfl) ⟨1218767, by rfl⟩ : syracuseStep 1625023 = 2437535) B2437535
theorem B3656807 : Blo 1624511 3656807 := bstep (se 1 (by rfl) ⟨2742605, by rfl⟩ : syracuseStep 3656807 = 5485211) B5485211
theorem B11119879 : Blo 1624511 11119879 := bstep (se 1 (by rfl) ⟨8339909, by rfl⟩ : syracuseStep 11119879 = 16679819) B16679819
theorem B1625583 : Blo 1624511 1625583 := bstep (se 1 (by rfl) ⟨1219187, by rfl⟩ : syracuseStep 1625583 = 2438375) B2438375
theorem B2436863 : Blo 1624511 2436863 := bstep (se 1 (by rfl) ⟨1827647, by rfl⟩ : syracuseStep 2436863 = 3655295) B3655295
theorem B18518057 : Blo 1624511 18518057 := bstep (se 2 (by rfl) ⟨6944271, by rfl⟩ : syracuseStep 18518057 = 13888543) B13888543
theorem B2437211 : Blo 1624511 2437211 := bstep (se 1 (by rfl) ⟨1827908, by rfl⟩ : syracuseStep 2437211 = 3655817) B3655817
theorem B1626363 : Blo 1624511 1626363 := bstep (se 1 (by rfl) ⟨1219772, by rfl⟩ : syracuseStep 1626363 = 2439545) B2439545
theorem B37122313 : Blo 1624511 37122313 := bstep (se 2 (by rfl) ⟨13920867, by rfl⟩ : syracuseStep 37122313 = 27841735) B27841735
theorem B7041791 : Blo 1624511 7041791 := bstep (se 1 (by rfl) ⟨5281343, by rfl⟩ : syracuseStep 7041791 = 10562687) B10562687
theorem B3659111 : Blo 1624511 3659111 := bstep (se 1 (by rfl) ⟨2744333, by rfl⟩ : syracuseStep 3659111 = 5488667) B5488667
theorem B2315623 : Blo 1624511 2315623 := bstep (se 1 (by rfl) ⟨1736717, by rfl⟩ : syracuseStep 2315623 = 3473435) B3473435
theorem B52139497 : Blo 1624511 52139497 := bstep (se 2 (by rfl) ⟨19552311, by rfl⟩ : syracuseStep 52139497 = 39104623) B39104623
theorem B3659291 : Blo 1624511 3659291 := bstep (se 1 (by rfl) ⟨2744468, by rfl⟩ : syracuseStep 3659291 = 5488937) B5488937
theorem B66690377 : Blo 1624511 66690377 := bstep (se 2 (by rfl) ⟨25008891, by rfl⟩ : syracuseStep 66690377 = 50017783) B50017783
theorem B12345371 : Blo 1624511 12345371 := bstep (se 1 (by rfl) ⟨9259028, by rfl⟩ : syracuseStep 12345371 = 18518057) B18518057
theorem B49496417 : Blo 1624511 49496417 := bstep (se 2 (by rfl) ⟨18561156, by rfl⟩ : syracuseStep 49496417 = 37122313) B37122313
theorem B4694527 : Blo 1624511 4694527 := bstep (se 1 (by rfl) ⟨3520895, by rfl⟩ : syracuseStep 4694527 = 7041791) B7041791
theorem B69519329 : Blo 1624511 69519329 := bstep (se 2 (by rfl) ⟨26069748, by rfl⟩ : syracuseStep 69519329 = 52139497) B52139497
theorem B44460251 : Blo 1624511 44460251 := bstep (se 1 (by rfl) ⟨33345188, by rfl⟩ : syracuseStep 44460251 = 66690377) B66690377
theorem B1624575 : Blo 1624511 1624575 := bstep (se 1 (by rfl) ⟨1218431, by rfl⟩ : syracuseStep 1624575 = 2436863) B2436863
theorem B1624807 : Blo 1624511 1624807 := bstep (se 1 (by rfl) ⟨1218605, by rfl⟩ : syracuseStep 1624807 = 2437211) B2437211
theorem B5483321 : Blo 1624511 5483321 := bstep (se 2 (by rfl) ⟨2056245, by rfl⟩ : syracuseStep 5483321 = 4112491) B4112491
theorem B2436815 : Blo 1624511 2436815 := bstep (se 1 (by rfl) ⟨1827611, by rfl⟩ : syracuseStep 2436815 = 3655223) B3655223
theorem B5484239 : Blo 1624511 5484239 := bstep (se 1 (by rfl) ⟨4113179, by rfl⟩ : syracuseStep 5484239 = 8226359) B8226359
theorem B2437871 : Blo 1624511 2437871 := bstep (se 1 (by rfl) ⟨1828403, by rfl⟩ : syracuseStep 2437871 = 3656807) B3656807
theorem B2439407 : Blo 1624511 2439407 := bstep (se 1 (by rfl) ⟨1829555, by rfl⟩ : syracuseStep 2439407 = 3659111) B3659111
theorem B2439527 : Blo 1624511 2439527 := bstep (se 1 (by rfl) ⟨1829645, by rfl⟩ : syracuseStep 2439527 = 3659291) B3659291
theorem B14826505 : Blo 1624511 14826505 := bstep (se 2 (by rfl) ⟨5559939, by rfl⟩ : syracuseStep 14826505 = 11119879) B11119879
theorem B3087497 : Blo 1624511 3087497 := bstep (se 2 (by rfl) ⟨1157811, by rfl⟩ : syracuseStep 3087497 = 2315623) B2315623
theorem B2743463 : Blo 1624511 2743463 := bstep (se 1 (by rfl) ⟨2057597, by rfl⟩ : syracuseStep 2743463 = 4115195) B4115195
theorem B32997611 : Blo 1624511 32997611 := bstep (se 1 (by rfl) ⟨24748208, by rfl⟩ : syracuseStep 32997611 = 49496417) B49496417
theorem B8233325 : Blo 1624511 8233325 := bstep (se 3 (by rfl) ⟨1543748, by rfl⟩ : syracuseStep 8233325 = 3087497) B3087497
theorem B6259369 : Blo 1624511 6259369 := bstep (se 2 (by rfl) ⟨2347263, by rfl⟩ : syracuseStep 6259369 = 4694527) B4694527
theorem B19768673 : Blo 1624511 19768673 := bstep (se 2 (by rfl) ⟨7413252, by rfl⟩ : syracuseStep 19768673 = 14826505) B14826505
theorem B29640167 : Blo 1624511 29640167 := bstep (se 1 (by rfl) ⟨22230125, by rfl⟩ : syracuseStep 29640167 = 44460251) B44460251
theorem B3655547 : Blo 1624511 3655547 := bstep (se 1 (by rfl) ⟨2741660, by rfl⟩ : syracuseStep 3655547 = 5483321) B5483321
theorem B1828975 : Blo 1624511 1828975 := bstep (se 1 (by rfl) ⟨1371731, by rfl⟩ : syracuseStep 1828975 = 2743463) B2743463
theorem B1624543 : Blo 1624511 1624543 := bstep (se 1 (by rfl) ⟨1218407, by rfl⟩ : syracuseStep 1624543 = 2436815) B2436815
theorem B3656159 : Blo 1624511 3656159 := bstep (se 1 (by rfl) ⟨2742119, by rfl⟩ : syracuseStep 3656159 = 5484239) B5484239
theorem B1625247 : Blo 1624511 1625247 := bstep (se 1 (by rfl) ⟨1218935, by rfl⟩ : syracuseStep 1625247 = 2437871) B2437871
theorem B46346219 : Blo 1624511 46346219 := bstep (se 1 (by rfl) ⟨34759664, by rfl⟩ : syracuseStep 46346219 = 69519329) B69519329
theorem B1626271 : Blo 1624511 1626271 := bstep (se 1 (by rfl) ⟨1219703, by rfl⟩ : syracuseStep 1626271 = 2439407) B2439407
theorem B1626351 : Blo 1624511 1626351 := bstep (se 1 (by rfl) ⟨1219763, by rfl⟩ : syracuseStep 1626351 = 2439527) B2439527
theorem B8230247 : Blo 1624511 8230247 := bstep (se 1 (by rfl) ⟨6172685, by rfl⟩ : syracuseStep 8230247 = 12345371) B12345371
theorem B5488883 : Blo 1624511 5488883 := bstep (se 1 (by rfl) ⟨4116662, by rfl⟩ : syracuseStep 5488883 = 8233325) B8233325
theorem B19760111 : Blo 1624511 19760111 := bstep (se 1 (by rfl) ⟨14820083, by rfl⟩ : syracuseStep 19760111 = 29640167) B29640167
theorem B21998407 : Blo 1624511 21998407 := bstep (se 1 (by rfl) ⟨16498805, by rfl⟩ : syracuseStep 21998407 = 32997611) B32997611
theorem B2437031 : Blo 1624511 2437031 := bstep (se 1 (by rfl) ⟨1827773, by rfl⟩ : syracuseStep 2437031 = 3655547) B3655547
theorem B2437439 : Blo 1624511 2437439 := bstep (se 1 (by rfl) ⟨1828079, by rfl⟩ : syracuseStep 2437439 = 3656159) B3656159
theorem B30897479 : Blo 1624511 30897479 := bstep (se 1 (by rfl) ⟨23173109, by rfl⟩ : syracuseStep 30897479 = 46346219) B46346219
theorem B2438633 : Blo 1624511 2438633 := bstep (se 2 (by rfl) ⟨914487, by rfl⟩ : syracuseStep 2438633 = 1828975) B1828975
theorem B8345825 : Blo 1624511 8345825 := bstep (se 2 (by rfl) ⟨3129684, by rfl⟩ : syracuseStep 8345825 = 6259369) B6259369
theorem B13179115 : Blo 1624511 13179115 := bstep (se 1 (by rfl) ⟨9884336, by rfl⟩ : syracuseStep 13179115 = 19768673) B19768673
theorem B5486831 : Blo 1624511 5486831 := bstep (se 1 (by rfl) ⟨4115123, by rfl⟩ : syracuseStep 5486831 = 8230247) B8230247
theorem B17572153 : Blo 1624511 17572153 := bstep (se 2 (by rfl) ⟨6589557, by rfl⟩ : syracuseStep 17572153 = 13179115) B13179115
theorem B13173407 : Blo 1624511 13173407 := bstep (se 1 (by rfl) ⟨9880055, by rfl⟩ : syracuseStep 13173407 = 19760111) B19760111
theorem B5563883 : Blo 1624511 5563883 := bstep (se 1 (by rfl) ⟨4172912, by rfl⟩ : syracuseStep 5563883 = 8345825) B8345825
theorem B1624687 : Blo 1624511 1624687 := bstep (se 1 (by rfl) ⟨1218515, by rfl⟩ : syracuseStep 1624687 = 2437031) B2437031
theorem B1624959 : Blo 1624511 1624959 := bstep (se 1 (by rfl) ⟨1218719, by rfl⟩ : syracuseStep 1624959 = 2437439) B2437439
theorem B20598319 : Blo 1624511 20598319 := bstep (se 1 (by rfl) ⟨15448739, by rfl⟩ : syracuseStep 20598319 = 30897479) B30897479
theorem B1625755 : Blo 1624511 1625755 := bstep (se 1 (by rfl) ⟨1219316, by rfl⟩ : syracuseStep 1625755 = 2438633) B2438633
theorem B29331209 : Blo 1624511 29331209 := bstep (se 2 (by rfl) ⟨10999203, by rfl⟩ : syracuseStep 29331209 = 21998407) B21998407
theorem B3657887 : Blo 1624511 3657887 := bstep (se 1 (by rfl) ⟨2743415, by rfl⟩ : syracuseStep 3657887 = 5486831) B5486831
theorem B3659255 : Blo 1624511 3659255 := bstep (se 1 (by rfl) ⟨2744441, by rfl⟩ : syracuseStep 3659255 = 5488883) B5488883
theorem B23429537 : Blo 1624511 23429537 := bstep (se 2 (by rfl) ⟨8786076, by rfl⟩ : syracuseStep 23429537 = 17572153) B17572153
theorem B8782271 : Blo 1624511 8782271 := bstep (se 1 (by rfl) ⟨6586703, by rfl⟩ : syracuseStep 8782271 = 13173407) B13173407
theorem B109857701 : Blo 1624511 109857701 := bstep (se 4 (by rfl) ⟨10299159, by rfl⟩ : syracuseStep 109857701 = 20598319) B20598319
theorem B2438591 : Blo 1624511 2438591 := bstep (se 1 (by rfl) ⟨1828943, by rfl⟩ : syracuseStep 2438591 = 3657887) B3657887
theorem B3709255 : Blo 1624511 3709255 := bstep (se 1 (by rfl) ⟨2781941, by rfl⟩ : syracuseStep 3709255 = 5563883) B5563883
theorem B2439503 : Blo 1624511 2439503 := bstep (se 1 (by rfl) ⟨1829627, by rfl⟩ : syracuseStep 2439503 = 3659255) B3659255
theorem B19554139 : Blo 1624511 19554139 := bstep (se 1 (by rfl) ⟨14665604, by rfl⟩ : syracuseStep 19554139 = 29331209) B29331209
theorem B73238467 : Blo 1624511 73238467 := bstep (se 1 (by rfl) ⟨54928850, by rfl⟩ : syracuseStep 73238467 = 109857701) B109857701
theorem B1625727 : Blo 1624511 1625727 := bstep (se 1 (by rfl) ⟨1219295, by rfl⟩ : syracuseStep 1625727 = 2438591) B2438591
theorem B1626335 : Blo 1624511 1626335 := bstep (se 1 (by rfl) ⟨1219751, by rfl⟩ : syracuseStep 1626335 = 2439503) B2439503
theorem B104288741 : Blo 1624511 104288741 := bstep (se 4 (by rfl) ⟨9777069, by rfl⟩ : syracuseStep 104288741 = 19554139) B19554139
theorem B15619691 : Blo 1624511 15619691 := bstep (se 1 (by rfl) ⟨11714768, by rfl⟩ : syracuseStep 15619691 = 23429537) B23429537
theorem B5854847 : Blo 1624511 5854847 := bstep (se 1 (by rfl) ⟨4391135, by rfl⟩ : syracuseStep 5854847 = 8782271) B8782271
theorem B4945673 : Blo 1624511 4945673 := bstep (se 2 (by rfl) ⟨1854627, by rfl⟩ : syracuseStep 4945673 = 3709255) B3709255
theorem B69525827 : Blo 1624511 69525827 := bstep (se 1 (by rfl) ⟨52144370, by rfl⟩ : syracuseStep 69525827 = 104288741) B104288741
theorem B10413127 : Blo 1624511 10413127 := bstep (se 1 (by rfl) ⟨7809845, by rfl⟩ : syracuseStep 10413127 = 15619691) B15619691
theorem B97651289 : Blo 1624511 97651289 := bstep (se 2 (by rfl) ⟨36619233, by rfl⟩ : syracuseStep 97651289 = 73238467) B73238467
theorem B3297115 : Blo 1624511 3297115 := bstep (se 1 (by rfl) ⟨2472836, by rfl⟩ : syracuseStep 3297115 = 4945673) B4945673
theorem B15612925 : Blo 1624511 15612925 := bstep (se 3 (by rfl) ⟨2927423, by rfl⟩ : syracuseStep 15612925 = 5854847) B5854847
theorem B46350551 : Blo 1624511 46350551 := bstep (se 1 (by rfl) ⟨34762913, by rfl⟩ : syracuseStep 46350551 = 69525827) B69525827
theorem B20817233 : Blo 1624511 20817233 := bstep (se 2 (by rfl) ⟨7806462, by rfl⟩ : syracuseStep 20817233 = 15612925) B15612925
theorem B260403437 : Blo 1624511 260403437 := bstep (se 3 (by rfl) ⟨48825644, by rfl⟩ : syracuseStep 260403437 = 97651289) B97651289
theorem B4396153 : Blo 1624511 4396153 := bstep (se 2 (by rfl) ⟨1648557, by rfl⟩ : syracuseStep 4396153 = 3297115) B3297115
theorem B13884169 : Blo 1624511 13884169 := bstep (se 2 (by rfl) ⟨5206563, by rfl⟩ : syracuseStep 13884169 = 10413127) B10413127
theorem B30900367 : Blo 1624511 30900367 := bstep (se 1 (by rfl) ⟨23175275, by rfl⟩ : syracuseStep 30900367 = 46350551) B46350551
theorem B13878155 : Blo 1624511 13878155 := bstep (se 1 (by rfl) ⟨10408616, by rfl⟩ : syracuseStep 13878155 = 20817233) B20817233
theorem B5861537 : Blo 1624511 5861537 := bstep (se 2 (by rfl) ⟨2198076, by rfl⟩ : syracuseStep 5861537 = 4396153) B4396153
theorem B173602291 : Blo 1624511 173602291 := bstep (se 1 (by rfl) ⟨130201718, by rfl⟩ : syracuseStep 173602291 = 260403437) B260403437
theorem B18512225 : Blo 1624511 18512225 := bstep (se 2 (by rfl) ⟨6942084, by rfl⟩ : syracuseStep 18512225 = 13884169) B13884169
theorem B3907691 : Blo 1624511 3907691 := bstep (se 1 (by rfl) ⟨2930768, by rfl⟩ : syracuseStep 3907691 = 5861537) B5861537
theorem B41200489 : Blo 1624511 41200489 := bstep (se 2 (by rfl) ⟨15450183, by rfl⟩ : syracuseStep 41200489 = 30900367) B30900367
theorem B9252103 : Blo 1624511 9252103 := bstep (se 1 (by rfl) ⟨6939077, by rfl⟩ : syracuseStep 9252103 = 13878155) B13878155
theorem B12341483 : Blo 1624511 12341483 := bstep (se 1 (by rfl) ⟨9256112, by rfl⟩ : syracuseStep 12341483 = 18512225) B18512225
theorem B231469721 : Blo 1624511 231469721 := bstep (se 2 (by rfl) ⟨86801145, by rfl⟩ : syracuseStep 231469721 = 173602291) B173602291
theorem B2605127 : Blo 1624511 2605127 := bstep (se 1 (by rfl) ⟨1953845, by rfl⟩ : syracuseStep 2605127 = 3907691) B3907691
theorem B154313147 : Blo 1624511 154313147 := bstep (se 1 (by rfl) ⟨115734860, by rfl⟩ : syracuseStep 154313147 = 231469721) B231469721
theorem B8227655 : Blo 1624511 8227655 := bstep (se 1 (by rfl) ⟨6170741, by rfl⟩ : syracuseStep 8227655 = 12341483) B12341483
theorem B54933985 : Blo 1624511 54933985 := bstep (se 2 (by rfl) ⟨20600244, by rfl⟩ : syracuseStep 54933985 = 41200489) B41200489
theorem B12336137 : Blo 1624511 12336137 := bstep (se 2 (by rfl) ⟨4626051, by rfl⟩ : syracuseStep 12336137 = 9252103) B9252103
theorem B102875431 : Blo 1624511 102875431 := bstep (se 1 (by rfl) ⟨77156573, by rfl⟩ : syracuseStep 102875431 = 154313147) B154313147
theorem B73245313 : Blo 1624511 73245313 := bstep (se 2 (by rfl) ⟨27466992, by rfl⟩ : syracuseStep 73245313 = 54933985) B54933985
theorem B27788021 : Blo 1624511 27788021 := bstep (se 5 (by rfl) ⟨1302563, by rfl⟩ : syracuseStep 27788021 = 2605127) B2605127
theorem B5485103 : Blo 1624511 5485103 := bstep (se 1 (by rfl) ⟨4113827, by rfl⟩ : syracuseStep 5485103 = 8227655) B8227655
theorem B8224091 : Blo 1624511 8224091 := bstep (se 1 (by rfl) ⟨6168068, by rfl⟩ : syracuseStep 8224091 = 12336137) B12336137
theorem B137167241 : Blo 1624511 137167241 := bstep (se 2 (by rfl) ⟨51437715, by rfl⟩ : syracuseStep 137167241 = 102875431) B102875431
theorem B5482727 : Blo 1624511 5482727 := bstep (se 1 (by rfl) ⟨4112045, by rfl⟩ : syracuseStep 5482727 = 8224091) B8224091
theorem B3656735 : Blo 1624511 3656735 := bstep (se 1 (by rfl) ⟨2742551, by rfl⟩ : syracuseStep 3656735 = 5485103) B5485103
theorem B18525347 : Blo 1624511 18525347 := bstep (se 1 (by rfl) ⟨13894010, by rfl⟩ : syracuseStep 18525347 = 27788021) B27788021
theorem B97660417 : Blo 1624511 97660417 := bstep (se 2 (by rfl) ⟨36622656, by rfl⟩ : syracuseStep 97660417 = 73245313) B73245313
theorem B3655151 : Blo 1624511 3655151 := bstep (se 1 (by rfl) ⟨2741363, by rfl⟩ : syracuseStep 3655151 = 5482727) B5482727
theorem B130213889 : Blo 1624511 130213889 := bstep (se 2 (by rfl) ⟨48830208, by rfl⟩ : syracuseStep 130213889 = 97660417) B97660417
theorem B2437823 : Blo 1624511 2437823 := bstep (se 1 (by rfl) ⟨1828367, by rfl⟩ : syracuseStep 2437823 = 3656735) B3656735
theorem B12350231 : Blo 1624511 12350231 := bstep (se 1 (by rfl) ⟨9262673, by rfl⟩ : syracuseStep 12350231 = 18525347) B18525347
theorem B365779309 : Blo 1624511 365779309 := bstep (se 3 (by rfl) ⟨68583620, by rfl⟩ : syracuseStep 365779309 = 137167241) B137167241
theorem B8233487 : Blo 1624511 8233487 := bstep (se 1 (by rfl) ⟨6175115, by rfl⟩ : syracuseStep 8233487 = 12350231) B12350231
theorem B1625215 : Blo 1624511 1625215 := bstep (se 1 (by rfl) ⟨1218911, by rfl⟩ : syracuseStep 1625215 = 2437823) B2437823
theorem B487705745 : Blo 1624511 487705745 := bstep (se 2 (by rfl) ⟨182889654, by rfl⟩ : syracuseStep 487705745 = 365779309) B365779309
theorem B2436767 : Blo 1624511 2436767 := bstep (se 1 (by rfl) ⟨1827575, by rfl⟩ : syracuseStep 2436767 = 3655151) B3655151
theorem B86809259 : Blo 1624511 86809259 := bstep (se 1 (by rfl) ⟨65106944, by rfl⟩ : syracuseStep 86809259 = 130213889) B130213889
theorem B5488991 : Blo 1624511 5488991 := bstep (se 1 (by rfl) ⟨4116743, by rfl⟩ : syracuseStep 5488991 = 8233487) B8233487
theorem B1624511 : Blo 1624511 1624511 := bstep (se 1 (by rfl) ⟨1218383, by rfl⟩ : syracuseStep 1624511 = 2436767) B2436767
theorem B57872839 : Blo 1624511 57872839 := bstep (se 1 (by rfl) ⟨43404629, by rfl⟩ : syracuseStep 57872839 = 86809259) B86809259
theorem B325137163 : Blo 1624511 325137163 := bstep (se 1 (by rfl) ⟨243852872, by rfl⟩ : syracuseStep 325137163 = 487705745) B487705745
theorem B77163785 : Blo 1624511 77163785 := bstep (se 2 (by rfl) ⟨28936419, by rfl⟩ : syracuseStep 77163785 = 57872839) B57872839
theorem B433516217 : Blo 1624511 433516217 := bstep (se 2 (by rfl) ⟨162568581, by rfl⟩ : syracuseStep 433516217 = 325137163) B325137163
theorem B3659327 : Blo 1624511 3659327 := bstep (se 1 (by rfl) ⟨2744495, by rfl⟩ : syracuseStep 3659327 = 5488991) B5488991
theorem B4624172981 : Blo 1624511 4624172981 := bstep (se 5 (by rfl) ⟨216758108, by rfl⟩ : syracuseStep 4624172981 = 433516217) B433516217
theorem B51442523 : Blo 1624511 51442523 := bstep (se 1 (by rfl) ⟨38581892, by rfl⟩ : syracuseStep 51442523 = 77163785) B77163785
theorem B2439551 : Blo 1624511 2439551 := bstep (se 1 (by rfl) ⟨1829663, by rfl⟩ : syracuseStep 2439551 = 3659327) B3659327
theorem B3082781987 : Blo 1624511 3082781987 := bstep (se 1 (by rfl) ⟨2312086490, by rfl⟩ : syracuseStep 3082781987 = 4624172981) B4624172981
theorem B34295015 : Blo 1624511 34295015 := bstep (se 1 (by rfl) ⟨25721261, by rfl⟩ : syracuseStep 34295015 = 51442523) B51442523
theorem B1626367 : Blo 1624511 1626367 := bstep (se 1 (by rfl) ⟨1219775, by rfl⟩ : syracuseStep 1626367 = 2439551) B2439551
theorem B2055187991 : Blo 1624511 2055187991 := bstep (se 1 (by rfl) ⟨1541390993, by rfl⟩ : syracuseStep 2055187991 = 3082781987) B3082781987
theorem B22863343 : Blo 1624511 22863343 := bstep (se 1 (by rfl) ⟨17147507, by rfl⟩ : syracuseStep 22863343 = 34295015) B34295015
theorem B30484457 : Blo 1624511 30484457 := bstep (se 2 (by rfl) ⟨11431671, by rfl⟩ : syracuseStep 30484457 = 22863343) B22863343
theorem B1370125327 : Blo 1624511 1370125327 := bstep (se 1 (by rfl) ⟨1027593995, by rfl⟩ : syracuseStep 1370125327 = 2055187991) B2055187991
theorem B1826833769 : Blo 1624511 1826833769 := bstep (se 2 (by rfl) ⟨685062663, by rfl⟩ : syracuseStep 1826833769 = 1370125327) B1370125327
theorem B20322971 : Blo 1624511 20322971 := bstep (se 1 (by rfl) ⟨15242228, by rfl⟩ : syracuseStep 20322971 = 30484457) B30484457
theorem B1217889179 : Blo 1624511 1217889179 := bstep (se 1 (by rfl) ⟨913416884, by rfl⟩ : syracuseStep 1217889179 = 1826833769) B1826833769
theorem B13548647 : Blo 1624511 13548647 := bstep (se 1 (by rfl) ⟨10161485, by rfl⟩ : syracuseStep 13548647 = 20322971) B20322971
theorem B811926119 : Blo 1624511 811926119 := bstep (se 1 (by rfl) ⟨608944589, by rfl⟩ : syracuseStep 811926119 = 1217889179) B1217889179
theorem B36129725 : Blo 1624511 36129725 := bstep (se 3 (by rfl) ⟨6774323, by rfl⟩ : syracuseStep 36129725 = 13548647) B13548647
theorem B24086483 : Blo 1624511 24086483 := bstep (se 1 (by rfl) ⟨18064862, by rfl⟩ : syracuseStep 24086483 = 36129725) B36129725
theorem B541284079 : Blo 1624511 541284079 := bstep (se 1 (by rfl) ⟨405963059, by rfl⟩ : syracuseStep 541284079 = 811926119) B811926119
theorem B16057655 : Blo 1624511 16057655 := bstep (se 1 (by rfl) ⟨12043241, by rfl⟩ : syracuseStep 16057655 = 24086483) B24086483
theorem B721712105 : Blo 1624511 721712105 := bstep (se 2 (by rfl) ⟨270642039, by rfl⟩ : syracuseStep 721712105 = 541284079) B541284079
theorem B481141403 : Blo 1624511 481141403 := bstep (se 1 (by rfl) ⟨360856052, by rfl⟩ : syracuseStep 481141403 = 721712105) B721712105
theorem B10705103 : Blo 1624511 10705103 := bstep (se 1 (by rfl) ⟨8028827, by rfl⟩ : syracuseStep 10705103 = 16057655) B16057655
theorem B320760935 : Blo 1624511 320760935 := bstep (se 1 (by rfl) ⟨240570701, by rfl⟩ : syracuseStep 320760935 = 481141403) B481141403
theorem B114187765 : Blo 1624511 114187765 := bstep (se 5 (by rfl) ⟨5352551, by rfl⟩ : syracuseStep 114187765 = 10705103) B10705103
theorem B152250353 : Blo 1624511 152250353 := bstep (se 2 (by rfl) ⟨57093882, by rfl⟩ : syracuseStep 152250353 = 114187765) B114187765
theorem B213840623 : Blo 1624511 213840623 := bstep (se 1 (by rfl) ⟨160380467, by rfl⟩ : syracuseStep 213840623 = 320760935) B320760935
theorem B101500235 : Blo 1624511 101500235 := bstep (se 1 (by rfl) ⟨76125176, by rfl⟩ : syracuseStep 101500235 = 152250353) B152250353
theorem B142560415 : Blo 1624511 142560415 := bstep (se 1 (by rfl) ⟨106920311, by rfl⟩ : syracuseStep 142560415 = 213840623) B213840623
theorem B67666823 : Blo 1624511 67666823 := bstep (se 1 (by rfl) ⟨50750117, by rfl⟩ : syracuseStep 67666823 = 101500235) B101500235
theorem B190080553 : Blo 1624511 190080553 := bstep (se 2 (by rfl) ⟨71280207, by rfl⟩ : syracuseStep 190080553 = 142560415) B142560415
theorem B253440737 : Blo 1624511 253440737 := bstep (se 2 (by rfl) ⟨95040276, by rfl⟩ : syracuseStep 253440737 = 190080553) B190080553
theorem B45111215 : Blo 1624511 45111215 := bstep (se 1 (by rfl) ⟨33833411, by rfl⟩ : syracuseStep 45111215 = 67666823) B67666823
theorem B168960491 : Blo 1624511 168960491 := bstep (se 1 (by rfl) ⟨126720368, by rfl⟩ : syracuseStep 168960491 = 253440737) B253440737
theorem B120296573 : Blo 1624511 120296573 := bstep (se 3 (by rfl) ⟨22555607, by rfl⟩ : syracuseStep 120296573 = 45111215) B45111215
theorem B112640327 : Blo 1624511 112640327 := bstep (se 1 (by rfl) ⟨84480245, by rfl⟩ : syracuseStep 112640327 = 168960491) B168960491
theorem B80197715 : Blo 1624511 80197715 := bstep (se 1 (by rfl) ⟨60148286, by rfl⟩ : syracuseStep 80197715 = 120296573) B120296573
theorem B53465143 : Blo 1624511 53465143 := bstep (se 1 (by rfl) ⟨40098857, by rfl⟩ : syracuseStep 53465143 = 80197715) B80197715
theorem B75093551 : Blo 1624511 75093551 := bstep (se 1 (by rfl) ⟨56320163, by rfl⟩ : syracuseStep 75093551 = 112640327) B112640327
theorem B71286857 : Blo 1624511 71286857 := bstep (se 2 (by rfl) ⟨26732571, by rfl⟩ : syracuseStep 71286857 = 53465143) B53465143
theorem B50062367 : Blo 1624511 50062367 := bstep (se 1 (by rfl) ⟨37546775, by rfl⟩ : syracuseStep 50062367 = 75093551) B75093551
theorem B33374911 : Blo 1624511 33374911 := bstep (se 1 (by rfl) ⟨25031183, by rfl⟩ : syracuseStep 33374911 = 50062367) B50062367
theorem B47524571 : Blo 1624511 47524571 := bstep (se 1 (by rfl) ⟨35643428, by rfl⟩ : syracuseStep 47524571 = 71286857) B71286857
theorem B44499881 : Blo 1624511 44499881 := bstep (se 2 (by rfl) ⟨16687455, by rfl⟩ : syracuseStep 44499881 = 33374911) B33374911
theorem B31683047 : Blo 1624511 31683047 := bstep (se 1 (by rfl) ⟨23762285, by rfl⟩ : syracuseStep 31683047 = 47524571) B47524571
theorem B29666587 : Blo 1624511 29666587 := bstep (se 1 (by rfl) ⟨22249940, by rfl⟩ : syracuseStep 29666587 = 44499881) B44499881
theorem B84488125 : Blo 1624511 84488125 := bstep (se 3 (by rfl) ⟨15841523, by rfl⟩ : syracuseStep 84488125 = 31683047) B31683047
theorem B112650833 : Blo 1624511 112650833 := bstep (se 2 (by rfl) ⟨42244062, by rfl⟩ : syracuseStep 112650833 = 84488125) B84488125
theorem B39555449 : Blo 1624511 39555449 := bstep (se 2 (by rfl) ⟨14833293, by rfl⟩ : syracuseStep 39555449 = 29666587) B29666587
theorem B26370299 : Blo 1624511 26370299 := bstep (se 1 (by rfl) ⟨19777724, by rfl⟩ : syracuseStep 26370299 = 39555449) B39555449
theorem B75100555 : Blo 1624511 75100555 := bstep (se 1 (by rfl) ⟨56325416, by rfl⟩ : syracuseStep 75100555 = 112650833) B112650833
theorem B70320797 : Blo 1624511 70320797 := bstep (se 3 (by rfl) ⟨13185149, by rfl⟩ : syracuseStep 70320797 = 26370299) B26370299
theorem B100134073 : Blo 1624511 100134073 := bstep (se 2 (by rfl) ⟨37550277, by rfl⟩ : syracuseStep 100134073 = 75100555) B75100555
theorem B46880531 : Blo 1624511 46880531 := bstep (se 1 (by rfl) ⟨35160398, by rfl⟩ : syracuseStep 46880531 = 70320797) B70320797
theorem B133512097 : Blo 1624511 133512097 := bstep (se 2 (by rfl) ⟨50067036, by rfl⟩ : syracuseStep 133512097 = 100134073) B100134073
theorem B31253687 : Blo 1624511 31253687 := bstep (se 1 (by rfl) ⟨23440265, by rfl⟩ : syracuseStep 31253687 = 46880531) B46880531
theorem B178016129 : Blo 1624511 178016129 := bstep (se 2 (by rfl) ⟨66756048, by rfl⟩ : syracuseStep 178016129 = 133512097) B133512097
theorem B20835791 : Blo 1624511 20835791 := bstep (se 1 (by rfl) ⟨15626843, by rfl⟩ : syracuseStep 20835791 = 31253687) B31253687
theorem B118677419 : Blo 1624511 118677419 := bstep (se 1 (by rfl) ⟨89008064, by rfl⟩ : syracuseStep 118677419 = 178016129) B178016129
theorem B13890527 : Blo 1624511 13890527 := bstep (se 1 (by rfl) ⟨10417895, by rfl⟩ : syracuseStep 13890527 = 20835791) B20835791
theorem B79118279 : Blo 1624511 79118279 := bstep (se 1 (by rfl) ⟨59338709, by rfl⟩ : syracuseStep 79118279 = 118677419) B118677419
theorem B9260351 : Blo 1624511 9260351 := bstep (se 1 (by rfl) ⟨6945263, by rfl⟩ : syracuseStep 9260351 = 13890527) B13890527
theorem B52745519 : Blo 1624511 52745519 := bstep (se 1 (by rfl) ⟨39559139, by rfl⟩ : syracuseStep 52745519 = 79118279) B79118279
theorem B6173567 : Blo 1624511 6173567 := bstep (se 1 (by rfl) ⟨4630175, by rfl⟩ : syracuseStep 6173567 = 9260351) B9260351
theorem B140654717 : Blo 1624511 140654717 := bstep (se 3 (by rfl) ⟨26372759, by rfl⟩ : syracuseStep 140654717 = 52745519) B52745519
theorem B4115711 : Blo 1624511 4115711 := bstep (se 1 (by rfl) ⟨3086783, by rfl⟩ : syracuseStep 4115711 = 6173567) B6173567
theorem B93769811 : Blo 1624511 93769811 := bstep (se 1 (by rfl) ⟨70327358, by rfl⟩ : syracuseStep 93769811 = 140654717) B140654717
theorem B62513207 : Blo 1624511 62513207 := bstep (se 1 (by rfl) ⟨46884905, by rfl⟩ : syracuseStep 62513207 = 93769811) B93769811
theorem B2743807 : Blo 1624511 2743807 := bstep (se 1 (by rfl) ⟨2057855, by rfl⟩ : syracuseStep 2743807 = 4115711) B4115711
theorem B41675471 : Blo 1624511 41675471 := bstep (se 1 (by rfl) ⟨31256603, by rfl⟩ : syracuseStep 41675471 = 62513207) B62513207
theorem B3658409 : Blo 1624511 3658409 := bstep (se 2 (by rfl) ⟨1371903, by rfl⟩ : syracuseStep 3658409 = 2743807) B2743807
theorem B27783647 : Blo 1624511 27783647 := bstep (se 1 (by rfl) ⟨20837735, by rfl⟩ : syracuseStep 27783647 = 41675471) B41675471
theorem B2438939 : Blo 1624511 2438939 := bstep (se 1 (by rfl) ⟨1829204, by rfl⟩ : syracuseStep 2438939 = 3658409) B3658409
theorem B18522431 : Blo 1624511 18522431 := bstep (se 1 (by rfl) ⟨13891823, by rfl⟩ : syracuseStep 18522431 = 27783647) B27783647
theorem B1625959 : Blo 1624511 1625959 := bstep (se 1 (by rfl) ⟨1219469, by rfl⟩ : syracuseStep 1625959 = 2438939) B2438939
theorem B12348287 : Blo 1624511 12348287 := bstep (se 1 (by rfl) ⟨9261215, by rfl⟩ : syracuseStep 12348287 = 18522431) B18522431
theorem B8232191 : Blo 1624511 8232191 := bstep (se 1 (by rfl) ⟨6174143, by rfl⟩ : syracuseStep 8232191 = 12348287) B12348287
theorem B5488127 : Blo 1624511 5488127 := bstep (se 1 (by rfl) ⟨4116095, by rfl⟩ : syracuseStep 5488127 = 8232191) B8232191
theorem B3658751 : Blo 1624511 3658751 := bstep (se 1 (by rfl) ⟨2744063, by rfl⟩ : syracuseStep 3658751 = 5488127) B5488127
theorem B2439167 : Blo 1624511 2439167 := bstep (se 1 (by rfl) ⟨1829375, by rfl⟩ : syracuseStep 2439167 = 3658751) B3658751
theorem B1626111 : Blo 1624511 1626111 := bstep (se 1 (by rfl) ⟨1219583, by rfl⟩ : syracuseStep 1626111 = 2439167) B2439167

theorem C0 (j : ℕ) (h1 : 406127 ≤ j) (h2 : j ≤ 406627) : Blo 1624511 (4 * j + 3) := by
  interval_cases j
  · exact B1624511
  · exact B1624515
  · exact B1624519
  · exact B1624523
  · exact B1624527
  · exact B1624531
  · exact B1624535
  · exact B1624539
  · exact B1624543
  · exact B1624547
  · exact B1624551
  · exact B1624555
  · exact B1624559
  · exact B1624563
  · exact B1624567
  · exact B1624571
  · exact B1624575
  · exact B1624579
  · exact B1624583
  · exact B1624587
  · exact B1624591
  · exact B1624595
  · exact B1624599
  · exact B1624603
  · exact B1624607
  · exact B1624611
  · exact B1624615
  · exact B1624619
  · exact B1624623
  · exact B1624627
  · exact B1624631
  · exact B1624635
  · exact B1624639
  · exact B1624643
  · exact B1624647
  · exact B1624651
  · exact B1624655
  · exact B1624659
  · exact B1624663
  · exact B1624667
  · exact B1624671
  · exact B1624675
  · exact B1624679
  · exact B1624683
  · exact B1624687
  · exact B1624691
  · exact B1624695
  · exact B1624699
  · exact B1624703
  · exact B1624707
  · exact B1624711
  · exact B1624715
  · exact B1624719
  · exact B1624723
  · exact B1624727
  · exact B1624731
  · exact B1624735
  · exact B1624739
  · exact B1624743
  · exact B1624747
  · exact B1624751
  · exact B1624755
  · exact B1624759
  · exact B1624763
  · exact B1624767
  · exact B1624771
  · exact B1624775
  · exact B1624779
  · exact B1624783
  · exact B1624787
  · exact B1624791
  · exact B1624795
  · exact B1624799
  · exact B1624803
  · exact B1624807
  · exact B1624811
  · exact B1624815
  · exact B1624819
  · exact B1624823
  · exact B1624827
  · exact B1624831
  · exact B1624835
  · exact B1624839
  · exact B1624843
  · exact B1624847
  · exact B1624851
  · exact B1624855
  · exact B1624859
  · exact B1624863
  · exact B1624867
  · exact B1624871
  · exact B1624875
  · exact B1624879
  · exact B1624883
  · exact B1624887
  · exact B1624891
  · exact B1624895
  · exact B1624899
  · exact B1624903
  · exact B1624907
  · exact B1624911
  · exact B1624915
  · exact B1624919
  · exact B1624923
  · exact B1624927
  · exact B1624931
  · exact B1624935
  · exact B1624939
  · exact B1624943
  · exact B1624947
  · exact B1624951
  · exact B1624955
  · exact B1624959
  · exact B1624963
  · exact B1624967
  · exact B1624971
  · exact B1624975
  · exact B1624979
  · exact B1624983
  · exact B1624987
  · exact B1624991
  · exact B1624995
  · exact B1624999
  · exact B1625003
  · exact B1625007
  · exact B1625011
  · exact B1625015
  · exact B1625019
  · exact B1625023
  · exact B1625027
  · exact B1625031
  · exact B1625035
  · exact B1625039
  · exact B1625043
  · exact B1625047
  · exact B1625051
  · exact B1625055
  · exact B1625059
  · exact B1625063
  · exact B1625067
  · exact B1625071
  · exact B1625075
  · exact B1625079
  · exact B1625083
  · exact B1625087
  · exact B1625091
  · exact B1625095
  · exact B1625099
  · exact B1625103
  · exact B1625107
  · exact B1625111
  · exact B1625115
  · exact B1625119
  · exact B1625123
  · exact B1625127
  · exact B1625131
  · exact B1625135
  · exact B1625139
  · exact B1625143
  · exact B1625147
  · exact B1625151
  · exact B1625155
  · exact B1625159
  · exact B1625163
  · exact B1625167
  · exact B1625171
  · exact B1625175
  · exact B1625179
  · exact B1625183
  · exact B1625187
  · exact B1625191
  · exact B1625195
  · exact B1625199
  · exact B1625203
  · exact B1625207
  · exact B1625211
  · exact B1625215
  · exact B1625219
  · exact B1625223
  · exact B1625227
  · exact B1625231
  · exact B1625235
  · exact B1625239
  · exact B1625243
  · exact B1625247
  · exact B1625251
  · exact B1625255
  · exact B1625259
  · exact B1625263
  · exact B1625267
  · exact B1625271
  · exact B1625275
  · exact B1625279
  · exact B1625283
  · exact B1625287
  · exact B1625291
  · exact B1625295
  · exact B1625299
  · exact B1625303
  · exact B1625307
  · exact B1625311
  · exact B1625315
  · exact B1625319
  · exact B1625323
  · exact B1625327
  · exact B1625331
  · exact B1625335
  · exact B1625339
  · exact B1625343
  · exact B1625347
  · exact B1625351
  · exact B1625355
  · exact B1625359
  · exact B1625363
  · exact B1625367
  · exact B1625371
  · exact B1625375
  · exact B1625379
  · exact B1625383
  · exact B1625387
  · exact B1625391
  · exact B1625395
  · exact B1625399
  · exact B1625403
  · exact B1625407
  · exact B1625411
  · exact B1625415
  · exact B1625419
  · exact B1625423
  · exact B1625427
  · exact B1625431
  · exact B1625435
  · exact B1625439
  · exact B1625443
  · exact B1625447
  · exact B1625451
  · exact B1625455
  · exact B1625459
  · exact B1625463
  · exact B1625467
  · exact B1625471
  · exact B1625475
  · exact B1625479
  · exact B1625483
  · exact B1625487
  · exact B1625491
  · exact B1625495
  · exact B1625499
  · exact B1625503
  · exact B1625507
  · exact B1625511
  · exact B1625515
  · exact B1625519
  · exact B1625523
  · exact B1625527
  · exact B1625531
  · exact B1625535
  · exact B1625539
  · exact B1625543
  · exact B1625547
  · exact B1625551
  · exact B1625555
  · exact B1625559
  · exact B1625563
  · exact B1625567
  · exact B1625571
  · exact B1625575
  · exact B1625579
  · exact B1625583
  · exact B1625587
  · exact B1625591
  · exact B1625595
  · exact B1625599
  · exact B1625603
  · exact B1625607
  · exact B1625611
  · exact B1625615
  · exact B1625619
  · exact B1625623
  · exact B1625627
  · exact B1625631
  · exact B1625635
  · exact B1625639
  · exact B1625643
  · exact B1625647
  · exact B1625651
  · exact B1625655
  · exact B1625659
  · exact B1625663
  · exact B1625667
  · exact B1625671
  · exact B1625675
  · exact B1625679
  · exact B1625683
  · exact B1625687
  · exact B1625691
  · exact B1625695
  · exact B1625699
  · exact B1625703
  · exact B1625707
  · exact B1625711
  · exact B1625715
  · exact B1625719
  · exact B1625723
  · exact B1625727
  · exact B1625731
  · exact B1625735
  · exact B1625739
  · exact B1625743
  · exact B1625747
  · exact B1625751
  · exact B1625755
  · exact B1625759
  · exact B1625763
  · exact B1625767
  · exact B1625771
  · exact B1625775
  · exact B1625779
  · exact B1625783
  · exact B1625787
  · exact B1625791
  · exact B1625795
  · exact B1625799
  · exact B1625803
  · exact B1625807
  · exact B1625811
  · exact B1625815
  · exact B1625819
  · exact B1625823
  · exact B1625827
  · exact B1625831
  · exact B1625835
  · exact B1625839
  · exact B1625843
  · exact B1625847
  · exact B1625851
  · exact B1625855
  · exact B1625859
  · exact B1625863
  · exact B1625867
  · exact B1625871
  · exact B1625875
  · exact B1625879
  · exact B1625883
  · exact B1625887
  · exact B1625891
  · exact B1625895
  · exact B1625899
  · exact B1625903
  · exact B1625907
  · exact B1625911
  · exact B1625915
  · exact B1625919
  · exact B1625923
  · exact B1625927
  · exact B1625931
  · exact B1625935
  · exact B1625939
  · exact B1625943
  · exact B1625947
  · exact B1625951
  · exact B1625955
  · exact B1625959
  · exact B1625963
  · exact B1625967
  · exact B1625971
  · exact B1625975
  · exact B1625979
  · exact B1625983
  · exact B1625987
  · exact B1625991
  · exact B1625995
  · exact B1625999
  · exact B1626003
  · exact B1626007
  · exact B1626011
  · exact B1626015
  · exact B1626019
  · exact B1626023
  · exact B1626027
  · exact B1626031
  · exact B1626035
  · exact B1626039
  · exact B1626043
  · exact B1626047
  · exact B1626051
  · exact B1626055
  · exact B1626059
  · exact B1626063
  · exact B1626067
  · exact B1626071
  · exact B1626075
  · exact B1626079
  · exact B1626083
  · exact B1626087
  · exact B1626091
  · exact B1626095
  · exact B1626099
  · exact B1626103
  · exact B1626107
  · exact B1626111
  · exact B1626115
  · exact B1626119
  · exact B1626123
  · exact B1626127
  · exact B1626131
  · exact B1626135
  · exact B1626139
  · exact B1626143
  · exact B1626147
  · exact B1626151
  · exact B1626155
  · exact B1626159
  · exact B1626163
  · exact B1626167
  · exact B1626171
  · exact B1626175
  · exact B1626179
  · exact B1626183
  · exact B1626187
  · exact B1626191
  · exact B1626195
  · exact B1626199
  · exact B1626203
  · exact B1626207
  · exact B1626211
  · exact B1626215
  · exact B1626219
  · exact B1626223
  · exact B1626227
  · exact B1626231
  · exact B1626235
  · exact B1626239
  · exact B1626243
  · exact B1626247
  · exact B1626251
  · exact B1626255
  · exact B1626259
  · exact B1626263
  · exact B1626267
  · exact B1626271
  · exact B1626275
  · exact B1626279
  · exact B1626283
  · exact B1626287
  · exact B1626291
  · exact B1626295
  · exact B1626299
  · exact B1626303
  · exact B1626307
  · exact B1626311
  · exact B1626315
  · exact B1626319
  · exact B1626323
  · exact B1626327
  · exact B1626331
  · exact B1626335
  · exact B1626339
  · exact B1626343
  · exact B1626347
  · exact B1626351
  · exact B1626355
  · exact B1626359
  · exact B1626363
  · exact B1626367
  · exact B1626371
  · exact B1626375
  · exact B1626379
  · exact B1626383
  · exact B1626387
  · exact B1626391
  · exact B1626395
  · exact B1626399
  · exact B1626403
  · exact B1626407
  · exact B1626411
  · exact B1626415
  · exact B1626419
  · exact B1626423
  · exact B1626427
  · exact B1626431
  · exact B1626435
  · exact B1626439
  · exact B1626443
  · exact B1626447
  · exact B1626451
  · exact B1626455
  · exact B1626459
  · exact B1626463
  · exact B1626467
  · exact B1626471
  · exact B1626475
  · exact B1626479
  · exact B1626483
  · exact B1626487
  · exact B1626491
  · exact B1626495
  · exact B1626499
  · exact B1626503
  · exact B1626507
  · exact B1626511

theorem solution (m : ℕ) (hlo : 1624511 ≤ m) (hhi : m ≤ 1626511) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 406127 ≤ j := by omega
    have hj2 : j ≤ 406627 := by omega
    have hb : Blo 1624511 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
