-- Prove2me | solution 1 for syracuse_descends_range_1128631_1132631
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:43.51172+00:00
-- url     : https://prove2.me/submissions/db9ca8a3-e15c-4d07-b0f1-8f295bfe5c29

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


theorem B1146893 : Blo 1128631 1146893 := bbase (se 3 (by rfl) ⟨215042, by rfl⟩ : syracuseStep 1146893 = 430085) (by norm_num)
theorem B4358213 : Blo 1128631 4358213 := bbase (se 4 (by rfl) ⟨408582, by rfl⟩ : syracuseStep 4358213 = 817165) (by norm_num)
theorem B1147117 : Blo 1128631 1147117 := bbase (se 3 (by rfl) ⟨215084, by rfl⟩ : syracuseStep 1147117 = 430169) (by norm_num)
theorem B1147429 : Blo 1128631 1147429 := bbase (se 4 (by rfl) ⟨107571, by rfl⟩ : syracuseStep 1147429 = 215143) (by norm_num)
theorem B1147477 : Blo 1128631 1147477 := bbase (se 8 (by rfl) ⟨6723, by rfl⟩ : syracuseStep 1147477 = 13447) (by norm_num)
theorem B4293445 : Blo 1128631 4293445 := bbase (se 4 (by rfl) ⟨402510, by rfl⟩ : syracuseStep 4293445 = 805021) (by norm_num)
theorem B3441653 : Blo 1128631 3441653 := bbase (se 5 (by rfl) ⟨161327, by rfl⟩ : syracuseStep 3441653 = 322655) (by norm_num)
theorem B4293749 : Blo 1128631 4293749 := bbase (se 5 (by rfl) ⟨201269, by rfl⟩ : syracuseStep 4293749 = 402539) (by norm_num)
theorem B3867797 : Blo 1128631 3867797 := bbase (se 6 (by rfl) ⟨90651, by rfl⟩ : syracuseStep 3867797 = 181303) (by norm_num)
theorem B2720965 : Blo 1128631 2720965 := bbase (se 4 (by rfl) ⟨255090, by rfl⟩ : syracuseStep 2720965 = 510181) (by norm_num)
theorem B1607149 : Blo 1128631 1607149 := bbase (se 3 (by rfl) ⟨301340, by rfl⟩ : syracuseStep 1607149 = 602681) (by norm_num)
theorem B1607941 : Blo 1128631 1607941 := bbase (se 4 (by rfl) ⟨150744, by rfl⟩ : syracuseStep 1607941 = 301489) (by norm_num)
theorem B2034013 : Blo 1128631 2034013 := bbase (se 3 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 2034013 = 762755) (by norm_num)
theorem B2034077 : Blo 1128631 2034077 := bbase (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) (by norm_num)
theorem B1608277 : Blo 1128631 1608277 := bbase (se 8 (by rfl) ⟨9423, by rfl⟩ : syracuseStep 1608277 = 18847) (by norm_num)
theorem B1608493 : Blo 1128631 1608493 := bbase (se 3 (by rfl) ⟨301592, by rfl⟩ : syracuseStep 1608493 = 603185) (by norm_num)
theorem B1608869 : Blo 1128631 1608869 := bbase (se 4 (by rfl) ⟨150831, by rfl⟩ : syracuseStep 1608869 = 301663) (by norm_num)
theorem B4295861 : Blo 1128631 4295861 := bbase (se 5 (by rfl) ⟨201368, by rfl⟩ : syracuseStep 4295861 = 402737) (by norm_num)
theorem B1936805 : Blo 1128631 1936805 := bbase (se 4 (by rfl) ⟨181575, by rfl⟩ : syracuseStep 1936805 = 363151) (by norm_num)
theorem B4132309 : Blo 1128631 4132309 := bbase (se 7 (by rfl) ⟨48425, by rfl⟩ : syracuseStep 4132309 = 96851) (by norm_num)
theorem B4296149 : Blo 1128631 4296149 := bbase (se 7 (by rfl) ⟨50345, by rfl⟩ : syracuseStep 4296149 = 100691) (by norm_num)
theorem B12881429 : Blo 1128631 12881429 := bbase (se 6 (by rfl) ⟨301908, by rfl⟩ : syracuseStep 12881429 = 603817) (by norm_num)
theorem B3214981 : Blo 1128631 3214981 := bbase (se 4 (by rfl) ⟨301404, by rfl⟩ : syracuseStep 3214981 = 602809) (by norm_num)
theorem B2035397 : Blo 1128631 2035397 := bbase (se 4 (by rfl) ⟨190818, by rfl⟩ : syracuseStep 2035397 = 381637) (by norm_num)
theorem B8589077 : Blo 1128631 8589077 := bbase (se 6 (by rfl) ⟨201306, by rfl⟩ : syracuseStep 8589077 = 402613) (by norm_num)
theorem B1904573 : Blo 1128631 1904573 := bbase (se 3 (by rfl) ⟨357107, by rfl⟩ : syracuseStep 1904573 = 714215) (by norm_num)
theorem B1904701 : Blo 1128631 1904701 := bbase (se 3 (by rfl) ⟨357131, by rfl⟩ : syracuseStep 1904701 = 714263) (by norm_num)
theorem B1904789 : Blo 1128631 1904789 := bbase (se 6 (by rfl) ⟨44643, by rfl⟩ : syracuseStep 1904789 = 89287) (by norm_num)
theorem B1904917 : Blo 1128631 1904917 := bbase (se 6 (by rfl) ⟨44646, by rfl⟩ : syracuseStep 1904917 = 89293) (by norm_num)
theorem B23892245 : Blo 1128631 23892245 := bbase (se 6 (by rfl) ⟨559974, by rfl⟩ : syracuseStep 23892245 = 1119949) (by norm_num)
theorem B1905005 : Blo 1128631 1905005 := bbase (se 3 (by rfl) ⟨357188, by rfl⟩ : syracuseStep 1905005 = 714377) (by norm_num)
theorem B1905133 : Blo 1128631 1905133 := bbase (se 3 (by rfl) ⟨357212, by rfl⟩ : syracuseStep 1905133 = 714425) (by norm_num)
theorem B1610293 : Blo 1128631 1610293 := bbase (se 5 (by rfl) ⟨75482, by rfl⟩ : syracuseStep 1610293 = 150965) (by norm_num)
theorem B1905221 : Blo 1128631 1905221 := bbase (se 4 (by rfl) ⟨178614, by rfl⟩ : syracuseStep 1905221 = 357229) (by norm_num)
theorem B7246421 : Blo 1128631 7246421 := bbase (se 8 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 7246421 = 84919) (by norm_num)
theorem B4297333 : Blo 1128631 4297333 := bbase (se 5 (by rfl) ⟨201437, by rfl⟩ : syracuseStep 4297333 = 402875) (by norm_num)
theorem B8163989 : Blo 1128631 8163989 := bbase (se 6 (by rfl) ⟨191343, by rfl⟩ : syracuseStep 8163989 = 382687) (by norm_num)
theorem B1905349 : Blo 1128631 1905349 := bbase (se 4 (by rfl) ⟨178626, by rfl⟩ : syracuseStep 1905349 = 357253) (by norm_num)
theorem B1905437 : Blo 1128631 1905437 := bbase (se 3 (by rfl) ⟨357269, by rfl⟩ : syracuseStep 1905437 = 714539) (by norm_num)
theorem B1905565 : Blo 1128631 1905565 := bbase (se 3 (by rfl) ⟨357293, by rfl⟩ : syracuseStep 1905565 = 714587) (by norm_num)
theorem B4821925 : Blo 1128631 4821925 := bbase (se 4 (by rfl) ⟨452055, by rfl⟩ : syracuseStep 4821925 = 904111) (by norm_num)
theorem B4297637 : Blo 1128631 4297637 := bbase (se 4 (by rfl) ⟨402903, by rfl⟩ : syracuseStep 4297637 = 805807) (by norm_num)
theorem B2036701 : Blo 1128631 2036701 := bbase (se 3 (by rfl) ⟨381881, by rfl⟩ : syracuseStep 2036701 = 763763) (by norm_num)
theorem B1905653 : Blo 1128631 1905653 := bbase (se 5 (by rfl) ⟨89327, by rfl⟩ : syracuseStep 1905653 = 178655) (by norm_num)
theorem B3216485 : Blo 1128631 3216485 := bbase (se 4 (by rfl) ⟨301545, by rfl⟩ : syracuseStep 3216485 = 603091) (by norm_num)
theorem B1905781 : Blo 1128631 1905781 := bbase (se 5 (by rfl) ⟨89333, by rfl⟩ : syracuseStep 1905781 = 178667) (by norm_num)
theorem B1610885 : Blo 1128631 1610885 := bbase (se 4 (by rfl) ⟨151020, by rfl⟩ : syracuseStep 1610885 = 302041) (by norm_num)
theorem B1905869 : Blo 1128631 1905869 := bbase (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) (by norm_num)
theorem B1610965 : Blo 1128631 1610965 := bbase (se 7 (by rfl) ⟨18878, by rfl⟩ : syracuseStep 1610965 = 37757) (by norm_num)
theorem B6427957 : Blo 1128631 6427957 := bbase (se 5 (by rfl) ⟨301310, by rfl⟩ : syracuseStep 6427957 = 602621) (by norm_num)
theorem B8262965 : Blo 1128631 8262965 := bbase (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) (by norm_num)
theorem B1905997 : Blo 1128631 1905997 := bbase (se 3 (by rfl) ⟨357374, by rfl⟩ : syracuseStep 1905997 = 714749) (by norm_num)
theorem B1611085 : Blo 1128631 1611085 := bbase (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) (by norm_num)
theorem B1906085 : Blo 1128631 1906085 := bbase (se 4 (by rfl) ⟨178695, by rfl⟩ : syracuseStep 1906085 = 357391) (by norm_num)
theorem B1611181 : Blo 1128631 1611181 := bbase (se 3 (by rfl) ⟨302096, by rfl⟩ : syracuseStep 1611181 = 604193) (by norm_num)
theorem B9180661 : Blo 1128631 9180661 := bbase (se 5 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 9180661 = 860687) (by norm_num)
theorem B1906213 : Blo 1128631 1906213 := bbase (se 4 (by rfl) ⟨178707, by rfl⟩ : syracuseStep 1906213 = 357415) (by norm_num)
theorem B1906301 : Blo 1128631 1906301 := bbase (se 3 (by rfl) ⟨357431, by rfl⟩ : syracuseStep 1906301 = 714863) (by norm_num)
theorem B10327733 : Blo 1128631 10327733 := bbase (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) (by norm_num)
theorem B1906429 : Blo 1128631 1906429 := bbase (se 3 (by rfl) ⟨357455, by rfl⟩ : syracuseStep 1906429 = 714911) (by norm_num)
theorem B1906517 : Blo 1128631 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B2791277 : Blo 1128631 2791277 := bbase (se 3 (by rfl) ⟨523364, by rfl⟩ : syracuseStep 2791277 = 1046729) (by norm_num)
theorem B1611677 : Blo 1128631 1611677 := bbase (se 3 (by rfl) ⟨302189, by rfl⟩ : syracuseStep 1611677 = 604379) (by norm_num)
theorem B1906645 : Blo 1128631 1906645 := bbase (se 7 (by rfl) ⟨22343, by rfl⟩ : syracuseStep 1906645 = 44687) (by norm_num)
theorem B5150693 : Blo 1128631 5150693 := bbase (se 4 (by rfl) ⟨482877, by rfl⟩ : syracuseStep 5150693 = 965755) (by norm_num)
theorem B2856941 : Blo 1128631 2856941 := bbase (se 3 (by rfl) ⟨535676, by rfl⟩ : syracuseStep 2856941 = 1071353) (by norm_num)
theorem B1906733 : Blo 1128631 1906733 := bbase (se 3 (by rfl) ⟨357512, by rfl⟩ : syracuseStep 1906733 = 715025) (by norm_num)
theorem B1808453 : Blo 1128631 1808453 := bbase (se 4 (by rfl) ⟨169542, by rfl⟩ : syracuseStep 1808453 = 339085) (by norm_num)
theorem B5150789 : Blo 1128631 5150789 := bbase (se 4 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 5150789 = 965773) (by norm_num)
theorem B2857133 : Blo 1128631 2857133 := bbase (se 3 (by rfl) ⟨535712, by rfl⟩ : syracuseStep 2857133 = 1071425) (by norm_num)
theorem B1906861 : Blo 1128631 1906861 := bbase (se 3 (by rfl) ⟨357536, by rfl⟩ : syracuseStep 1906861 = 715073) (by norm_num)
theorem B2037941 : Blo 1128631 2037941 := bbase (se 5 (by rfl) ⟨95528, by rfl⟩ : syracuseStep 2037941 = 191057) (by norm_num)
theorem B7936213 : Blo 1128631 7936213 := bbase (se 7 (by rfl) ⟨93002, by rfl⟩ : syracuseStep 7936213 = 186005) (by norm_num)
theorem B1906949 : Blo 1128631 1906949 := bbase (se 4 (by rfl) ⟨178776, by rfl⟩ : syracuseStep 1906949 = 357553) (by norm_num)
theorem B8690005 : Blo 1128631 8690005 := bbase (se 10 (by rfl) ⟨12729, by rfl⟩ : syracuseStep 8690005 = 25459) (by norm_num)
theorem B1907077 : Blo 1128631 1907077 := bbase (se 4 (by rfl) ⟨178788, by rfl⟩ : syracuseStep 1907077 = 357577) (by norm_num)
theorem B1612229 : Blo 1128631 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B1907165 : Blo 1128631 1907165 := bbase (se 3 (by rfl) ⟨357593, by rfl⟩ : syracuseStep 1907165 = 715187) (by norm_num)
theorem B2857477 : Blo 1128631 2857477 := bbase (se 4 (by rfl) ⟨267888, by rfl⟩ : syracuseStep 2857477 = 535777) (by norm_num)
theorem B1907293 : Blo 1128631 1907293 := bbase (se 3 (by rfl) ⟨357617, by rfl⟩ : syracuseStep 1907293 = 715235) (by norm_num)
theorem B2857589 : Blo 1128631 2857589 := bbase (se 5 (by rfl) ⟨133949, by rfl⟩ : syracuseStep 2857589 = 267899) (by norm_num)
theorem B3054229 : Blo 1128631 3054229 := bbase (se 6 (by rfl) ⟨71583, by rfl⟩ : syracuseStep 3054229 = 143167) (by norm_num)
theorem B3218069 : Blo 1128631 3218069 := bbase (se 6 (by rfl) ⟨75423, by rfl⟩ : syracuseStep 3218069 = 150847) (by norm_num)
theorem B1907381 : Blo 1128631 1907381 := bbase (se 5 (by rfl) ⟨89408, by rfl⟩ : syracuseStep 1907381 = 178817) (by norm_num)
theorem B2857781 : Blo 1128631 2857781 := bbase (se 5 (by rfl) ⟨133958, by rfl⟩ : syracuseStep 2857781 = 267917) (by norm_num)
theorem B1907509 : Blo 1128631 1907509 := bbase (se 5 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 1907509 = 178829) (by norm_num)
theorem B1907597 : Blo 1128631 1907597 := bbase (se 3 (by rfl) ⟨357674, by rfl⟩ : syracuseStep 1907597 = 715349) (by norm_num)
theorem B4299749 : Blo 1128631 4299749 := bbase (se 4 (by rfl) ⟨403101, by rfl⟩ : syracuseStep 4299749 = 806203) (by norm_num)
theorem B1907725 : Blo 1128631 1907725 := bbase (se 3 (by rfl) ⟨357698, by rfl⟩ : syracuseStep 1907725 = 715397) (by norm_num)
theorem B1907813 : Blo 1128631 1907813 := bbase (se 4 (by rfl) ⟨178857, by rfl⟩ : syracuseStep 1907813 = 357715) (by norm_num)
theorem B2858125 : Blo 1128631 2858125 := bbase (se 3 (by rfl) ⟨535898, by rfl⟩ : syracuseStep 2858125 = 1071797) (by norm_num)
theorem B1907941 : Blo 1128631 1907941 := bbase (se 4 (by rfl) ⟨178869, by rfl⟩ : syracuseStep 1907941 = 357739) (by norm_num)
theorem B6429941 : Blo 1128631 6429941 := bbase (se 5 (by rfl) ⟨301403, by rfl⟩ : syracuseStep 6429941 = 602807) (by norm_num)
theorem B2858237 : Blo 1128631 2858237 := bbase (se 3 (by rfl) ⟨535919, by rfl⟩ : syracuseStep 2858237 = 1071839) (by norm_num)
theorem B4300037 : Blo 1128631 4300037 := bbase (se 4 (by rfl) ⟨403128, by rfl⟩ : syracuseStep 4300037 = 806257) (by norm_num)
theorem B3218741 : Blo 1128631 3218741 := bbase (se 5 (by rfl) ⟨150878, by rfl⟩ : syracuseStep 3218741 = 301757) (by norm_num)
theorem B2235701 : Blo 1128631 2235701 := bbase (se 5 (by rfl) ⟨104798, by rfl⟩ : syracuseStep 2235701 = 209597) (by norm_num)
theorem B1908029 : Blo 1128631 1908029 := bbase (se 3 (by rfl) ⟨357755, by rfl⟩ : syracuseStep 1908029 = 715511) (by norm_num)
theorem B9182645 : Blo 1128631 9182645 := bbase (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) (by norm_num)
theorem B2858429 : Blo 1128631 2858429 := bbase (se 3 (by rfl) ⟨535955, by rfl⟩ : syracuseStep 2858429 = 1071911) (by norm_num)
theorem B1908157 : Blo 1128631 1908157 := bbase (se 3 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 1908157 = 715559) (by norm_num)
theorem B47095253 : Blo 1128631 47095253 := bbase (se 7 (by rfl) ⟨551897, by rfl⟩ : syracuseStep 47095253 = 1103795) (by norm_num)
theorem B1908245 : Blo 1128631 1908245 := bbase (se 6 (by rfl) ⟨44724, by rfl⟩ : syracuseStep 1908245 = 89449) (by norm_num)
theorem B1809965 : Blo 1128631 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B1908373 : Blo 1128631 1908373 := bbase (se 6 (by rfl) ⟨44727, by rfl⟩ : syracuseStep 1908373 = 89455) (by norm_num)
theorem B3219173 : Blo 1128631 3219173 := bbase (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) (by norm_num)
theorem B1908461 : Blo 1128631 1908461 := bbase (se 3 (by rfl) ⟨357836, by rfl⟩ : syracuseStep 1908461 = 715673) (by norm_num)
theorem B2858773 : Blo 1128631 2858773 := bbase (se 6 (by rfl) ⟨67002, by rfl⟩ : syracuseStep 2858773 = 134005) (by norm_num)
theorem B1548077 : Blo 1128631 1548077 := bbase (se 3 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 1548077 = 580529) (by norm_num)
theorem B4824917 : Blo 1128631 4824917 := bbase (se 9 (by rfl) ⟨14135, by rfl⟩ : syracuseStep 4824917 = 28271) (by norm_num)
theorem B1908589 : Blo 1128631 1908589 := bbase (se 3 (by rfl) ⟨357860, by rfl⟩ : syracuseStep 1908589 = 715721) (by norm_num)
theorem B2858885 : Blo 1128631 2858885 := bbase (se 4 (by rfl) ⟨268020, by rfl⟩ : syracuseStep 2858885 = 536041) (by norm_num)
theorem B1908677 : Blo 1128631 1908677 := bbase (se 4 (by rfl) ⟨178938, by rfl⟩ : syracuseStep 1908677 = 357877) (by norm_num)
theorem B1810421 : Blo 1128631 1810421 := bbase (se 5 (by rfl) ⟨84863, by rfl⟩ : syracuseStep 1810421 = 169727) (by norm_num)
theorem B9674741 : Blo 1128631 9674741 := bbase (se 5 (by rfl) ⟨453503, by rfl⟩ : syracuseStep 9674741 = 907007) (by norm_num)
theorem B2859077 : Blo 1128631 2859077 := bbase (se 4 (by rfl) ⟨268038, by rfl⟩ : syracuseStep 2859077 = 536077) (by norm_num)
theorem B1908805 : Blo 1128631 1908805 := bbase (se 4 (by rfl) ⟨178950, by rfl⟩ : syracuseStep 1908805 = 357901) (by norm_num)
theorem B2039917 : Blo 1128631 2039917 := bbase (se 3 (by rfl) ⟨382484, by rfl⟩ : syracuseStep 2039917 = 764969) (by norm_num)
theorem B3809429 : Blo 1128631 3809429 := bbase (se 6 (by rfl) ⟨89283, by rfl⟩ : syracuseStep 3809429 = 178567) (by norm_num)
theorem B1908893 : Blo 1128631 1908893 := bbase (se 3 (by rfl) ⟨357917, by rfl⟩ : syracuseStep 1908893 = 715835) (by norm_num)
theorem B1909021 : Blo 1128631 1909021 := bbase (se 3 (by rfl) ⟨357941, by rfl⟩ : syracuseStep 1909021 = 715883) (by norm_num)
theorem B1909109 : Blo 1128631 1909109 := bbase (se 5 (by rfl) ⟨89489, by rfl⟩ : syracuseStep 1909109 = 178979) (by norm_num)
theorem B2859421 : Blo 1128631 2859421 := bbase (se 3 (by rfl) ⟨536141, by rfl⟩ : syracuseStep 2859421 = 1072283) (by norm_num)
theorem B4071845 : Blo 1128631 4071845 := bbase (se 4 (by rfl) ⟨381735, by rfl⟩ : syracuseStep 4071845 = 763471) (by norm_num)
theorem B3056069 : Blo 1128631 3056069 := bbase (se 4 (by rfl) ⟨286506, by rfl⟩ : syracuseStep 3056069 = 573013) (by norm_num)
theorem B3219925 : Blo 1128631 3219925 := bbase (se 7 (by rfl) ⟨37733, by rfl⟩ : syracuseStep 3219925 = 75467) (by norm_num)
theorem B1909237 : Blo 1128631 1909237 := bbase (se 5 (by rfl) ⟨89495, by rfl⟩ : syracuseStep 1909237 = 178991) (by norm_num)
theorem B2859533 : Blo 1128631 2859533 := bbase (se 3 (by rfl) ⟨536162, by rfl⟩ : syracuseStep 2859533 = 1072325) (by norm_num)
theorem B4071989 : Blo 1128631 4071989 := bbase (se 5 (by rfl) ⟨190874, by rfl⟩ : syracuseStep 4071989 = 381749) (by norm_num)
theorem B3809861 : Blo 1128631 3809861 := bbase (se 4 (by rfl) ⟨357174, by rfl⟩ : syracuseStep 3809861 = 714349) (by norm_num)
theorem B1909325 : Blo 1128631 1909325 := bbase (se 3 (by rfl) ⟨357998, by rfl⟩ : syracuseStep 1909325 = 715997) (by norm_num)
theorem B1548893 : Blo 1128631 1548893 := bbase (se 3 (by rfl) ⟨290417, by rfl⟩ : syracuseStep 1548893 = 580835) (by norm_num)
theorem B5808773 : Blo 1128631 5808773 := bbase (se 4 (by rfl) ⟨544572, by rfl⟩ : syracuseStep 5808773 = 1089145) (by norm_num)
theorem B2859725 : Blo 1128631 2859725 := bbase (se 3 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 2859725 = 1072397) (by norm_num)
theorem B1909453 : Blo 1128631 1909453 := bbase (se 3 (by rfl) ⟨358022, by rfl⟩ : syracuseStep 1909453 = 716045) (by norm_num)
theorem B1909541 : Blo 1128631 1909541 := bbase (se 4 (by rfl) ⟨179019, by rfl⟩ : syracuseStep 1909541 = 358039) (by norm_num)
theorem B4825925 : Blo 1128631 4825925 := bbase (se 4 (by rfl) ⟨452430, by rfl⟩ : syracuseStep 4825925 = 904861) (by norm_num)
theorem B2040709 : Blo 1128631 2040709 := bbase (se 4 (by rfl) ⟨191316, by rfl⟩ : syracuseStep 2040709 = 382633) (by norm_num)
theorem B1909669 : Blo 1128631 1909669 := bbase (se 4 (by rfl) ⟨179031, by rfl⟩ : syracuseStep 1909669 = 358063) (by norm_num)
theorem B1811413 : Blo 1128631 1811413 := bbase (se 7 (by rfl) ⟨21227, by rfl⟩ : syracuseStep 1811413 = 42455) (by norm_num)
theorem B3810293 : Blo 1128631 3810293 := bbase (se 5 (by rfl) ⟨178607, by rfl⟩ : syracuseStep 3810293 = 357215) (by norm_num)
theorem B1909757 : Blo 1128631 1909757 := bbase (se 3 (by rfl) ⟨358079, by rfl⟩ : syracuseStep 1909757 = 716159) (by norm_num)
theorem B2860069 : Blo 1128631 2860069 := bbase (se 4 (by rfl) ⟨268131, by rfl⟩ : syracuseStep 2860069 = 536263) (by norm_num)
theorem B1909885 : Blo 1128631 1909885 := bbase (se 3 (by rfl) ⟨358103, by rfl⟩ : syracuseStep 1909885 = 716207) (by norm_num)
theorem B2860181 : Blo 1128631 2860181 := bbase (se 6 (by rfl) ⟨67035, by rfl⟩ : syracuseStep 2860181 = 134071) (by norm_num)
theorem B2041013 : Blo 1128631 2041013 := bbase (se 5 (by rfl) ⟨95672, by rfl⟩ : syracuseStep 2041013 = 191345) (by norm_num)
theorem B1909973 : Blo 1128631 1909973 := bbase (se 7 (by rfl) ⟨22382, by rfl⟩ : syracuseStep 1909973 = 44765) (by norm_num)
theorem B2172149 : Blo 1128631 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B2860373 : Blo 1128631 2860373 := bbase (se 12 (by rfl) ⟨1047, by rfl⟩ : syracuseStep 2860373 = 2095) (by norm_num)
theorem B1910101 : Blo 1128631 1910101 := bbase (se 12 (by rfl) ⟨699, by rfl⟩ : syracuseStep 1910101 = 1399) (by norm_num)
theorem B6432149 : Blo 1128631 6432149 := bbase (se 6 (by rfl) ⟨150753, by rfl⟩ : syracuseStep 6432149 = 301507) (by norm_num)
theorem B3810725 : Blo 1128631 3810725 := bbase (se 4 (by rfl) ⟨357255, by rfl⟩ : syracuseStep 3810725 = 714511) (by norm_num)
theorem B1910189 : Blo 1128631 1910189 := bbase (se 3 (by rfl) ⟨358160, by rfl⟩ : syracuseStep 1910189 = 716321) (by norm_num)
theorem B1910317 : Blo 1128631 1910317 := bbase (se 3 (by rfl) ⟨358184, by rfl⟩ : syracuseStep 1910317 = 716369) (by norm_num)
theorem B1812061 : Blo 1128631 1812061 := bbase (se 3 (by rfl) ⟨339761, by rfl⟩ : syracuseStep 1812061 = 679523) (by norm_num)
theorem B1910405 : Blo 1128631 1910405 := bbase (se 4 (by rfl) ⟨179100, by rfl⟩ : syracuseStep 1910405 = 358201) (by norm_num)
theorem B3057301 : Blo 1128631 3057301 := bbase (se 6 (by rfl) ⟨71655, by rfl⟩ : syracuseStep 3057301 = 143311) (by norm_num)
theorem B2860717 : Blo 1128631 2860717 := bbase (se 3 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 2860717 = 1072769) (by norm_num)
theorem B2827997 : Blo 1128631 2827997 := bbase (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) (by norm_num)
theorem B1910533 : Blo 1128631 1910533 := bbase (se 4 (by rfl) ⟨179112, by rfl⟩ : syracuseStep 1910533 = 358225) (by norm_num)
theorem B2860829 : Blo 1128631 2860829 := bbase (se 3 (by rfl) ⟨536405, by rfl⟩ : syracuseStep 2860829 = 1072811) (by norm_num)
theorem B3811157 : Blo 1128631 3811157 := bbase (se 9 (by rfl) ⟨11165, by rfl⟩ : syracuseStep 3811157 = 22331) (by norm_num)
theorem B1910621 : Blo 1128631 1910621 := bbase (se 3 (by rfl) ⟨358241, by rfl⟩ : syracuseStep 1910621 = 716483) (by norm_num)
theorem B10856405 : Blo 1128631 10856405 := bbase (se 7 (by rfl) ⟨127223, by rfl⟩ : syracuseStep 10856405 = 254447) (by norm_num)
theorem B2861021 : Blo 1128631 2861021 := bbase (se 3 (by rfl) ⟨536441, by rfl⟩ : syracuseStep 2861021 = 1072883) (by norm_num)
theorem B1910749 : Blo 1128631 1910749 := bbase (se 3 (by rfl) ⟨358265, by rfl⟩ : syracuseStep 1910749 = 716531) (by norm_num)
theorem B1910837 : Blo 1128631 1910837 := bbase (se 5 (by rfl) ⟨89570, by rfl⟩ : syracuseStep 1910837 = 179141) (by norm_num)
theorem B1910965 : Blo 1128631 1910965 := bbase (se 5 (by rfl) ⟨89576, by rfl⟩ : syracuseStep 1910965 = 179153) (by norm_num)
theorem B7252213 : Blo 1128631 7252213 := bbase (se 5 (by rfl) ⟨339947, by rfl⟩ : syracuseStep 7252213 = 679895) (by norm_num)
theorem B3811589 : Blo 1128631 3811589 := bbase (se 4 (by rfl) ⟨357336, by rfl⟩ : syracuseStep 3811589 = 714673) (by norm_num)
theorem B1911053 : Blo 1128631 1911053 := bbase (se 3 (by rfl) ⟨358322, by rfl⟩ : syracuseStep 1911053 = 716645) (by norm_num)
theorem B2861365 : Blo 1128631 2861365 := bbase (se 5 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 2861365 = 268253) (by norm_num)
theorem B3058037 : Blo 1128631 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B1911181 : Blo 1128631 1911181 := bbase (se 3 (by rfl) ⟨358346, by rfl⟩ : syracuseStep 1911181 = 716693) (by norm_num)
theorem B2206109 : Blo 1128631 2206109 := bbase (se 3 (by rfl) ⟨413645, by rfl⟩ : syracuseStep 2206109 = 827291) (by norm_num)
theorem B1288613 : Blo 1128631 1288613 := bbase (se 4 (by rfl) ⟨120807, by rfl⟩ : syracuseStep 1288613 = 241615) (by norm_num)
theorem B2861477 : Blo 1128631 2861477 := bbase (se 4 (by rfl) ⟨268263, by rfl⟩ : syracuseStep 2861477 = 536527) (by norm_num)
theorem B1911269 : Blo 1128631 1911269 := bbase (se 4 (by rfl) ⟨179181, by rfl⟩ : syracuseStep 1911269 = 358363) (by norm_num)
theorem B1812989 : Blo 1128631 1812989 := bbase (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) (by norm_num)
theorem B4827701 : Blo 1128631 4827701 := bbase (se 5 (by rfl) ⟨226298, by rfl⟩ : syracuseStep 4827701 = 452597) (by norm_num)
theorem B2861669 : Blo 1128631 2861669 := bbase (se 4 (by rfl) ⟨268281, by rfl⟩ : syracuseStep 2861669 = 536563) (by norm_num)
theorem B3812021 : Blo 1128631 3812021 := bbase (se 5 (by rfl) ⟨178688, by rfl⟩ : syracuseStep 3812021 = 357377) (by norm_num)
theorem B1452749 : Blo 1128631 1452749 := bbase (se 3 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 1452749 = 544781) (by norm_num)
theorem B3058469 : Blo 1128631 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B2862013 : Blo 1128631 2862013 := bbase (se 3 (by rfl) ⟨536627, by rfl⟩ : syracuseStep 2862013 = 1073255) (by norm_num)
theorem B1813445 : Blo 1128631 1813445 := bbase (se 4 (by rfl) ⟨170010, by rfl⟩ : syracuseStep 1813445 = 340021) (by norm_num)
theorem B1289197 : Blo 1128631 1289197 := bbase (se 3 (by rfl) ⟨241724, by rfl⟩ : syracuseStep 1289197 = 483449) (by norm_num)
theorem B2173981 : Blo 1128631 2173981 := bbase (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) (by norm_num)
theorem B2862125 : Blo 1128631 2862125 := bbase (se 3 (by rfl) ⟨536648, by rfl⟩ : syracuseStep 2862125 = 1073297) (by norm_num)
theorem B3812453 : Blo 1128631 3812453 := bbase (se 4 (by rfl) ⟨357417, by rfl⟩ : syracuseStep 3812453 = 714835) (by norm_num)
theorem B3058805 : Blo 1128631 3058805 := bbase (se 5 (by rfl) ⟨143381, by rfl⟩ : syracuseStep 3058805 = 286763) (by norm_num)
theorem B3058901 : Blo 1128631 3058901 := bbase (se 7 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 3058901 = 71693) (by norm_num)
theorem B2862317 : Blo 1128631 2862317 := bbase (se 3 (by rfl) ⟨536684, by rfl⟩ : syracuseStep 2862317 = 1073369) (by norm_num)
theorem B3222773 : Blo 1128631 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B1289525 : Blo 1128631 1289525 := bbase (se 5 (by rfl) ⟨60446, by rfl⟩ : syracuseStep 1289525 = 120893) (by norm_num)
theorem B8596853 : Blo 1128631 8596853 := bbase (se 5 (by rfl) ⟨402977, by rfl⟩ : syracuseStep 8596853 = 805955) (by norm_num)
theorem B3812885 : Blo 1128631 3812885 := bbase (se 6 (by rfl) ⟨89364, by rfl⟩ : syracuseStep 3812885 = 178729) (by norm_num)
theorem B2862661 : Blo 1128631 2862661 := bbase (se 4 (by rfl) ⟨268374, by rfl⟩ : syracuseStep 2862661 = 536749) (by norm_num)
theorem B2862773 : Blo 1128631 2862773 := bbase (se 5 (by rfl) ⟨134192, by rfl⟩ : syracuseStep 2862773 = 268385) (by norm_num)
theorem B2862965 : Blo 1128631 2862965 := bbase (se 5 (by rfl) ⟨134201, by rfl⟩ : syracuseStep 2862965 = 268403) (by norm_num)
theorem B3813317 : Blo 1128631 3813317 := bbase (se 4 (by rfl) ⟨357498, by rfl⟩ : syracuseStep 3813317 = 714997) (by norm_num)
theorem B9646037 : Blo 1128631 9646037 := bbase (se 7 (by rfl) ⟨113039, by rfl⟩ : syracuseStep 9646037 = 226079) (by norm_num)
theorem B2896013 : Blo 1128631 2896013 := bbase (se 3 (by rfl) ⟨543002, by rfl⟩ : syracuseStep 2896013 = 1086005) (by norm_num)
theorem B2863309 : Blo 1128631 2863309 := bbase (se 3 (by rfl) ⟨536870, by rfl⟩ : syracuseStep 2863309 = 1073741) (by norm_num)
theorem B2863421 : Blo 1128631 2863421 := bbase (se 3 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 2863421 = 1073783) (by norm_num)
theorem B3813749 : Blo 1128631 3813749 := bbase (se 5 (by rfl) ⟨178769, by rfl⟩ : syracuseStep 3813749 = 357539) (by norm_num)
theorem B3223957 : Blo 1128631 3223957 := bbase (se 6 (by rfl) ⟨75561, by rfl⟩ : syracuseStep 3223957 = 151123) (by norm_num)
theorem B1290685 : Blo 1128631 1290685 := bbase (se 3 (by rfl) ⟨242003, by rfl⟩ : syracuseStep 1290685 = 484007) (by norm_num)
theorem B2863613 : Blo 1128631 2863613 := bbase (se 3 (by rfl) ⟨536927, by rfl⟩ : syracuseStep 2863613 = 1073855) (by norm_num)
theorem B3224117 : Blo 1128631 3224117 := bbase (se 5 (by rfl) ⟨151130, by rfl⟩ : syracuseStep 3224117 = 302261) (by norm_num)
theorem B5714549 : Blo 1128631 5714549 := bbase (se 5 (by rfl) ⟨267869, by rfl⟩ : syracuseStep 5714549 = 535739) (by norm_num)
theorem B6206165 : Blo 1128631 6206165 := bbase (se 7 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 6206165 = 145457) (by norm_num)
theorem B2142949 : Blo 1128631 2142949 := bbase (se 4 (by rfl) ⟨200901, by rfl⟩ : syracuseStep 2142949 = 401803) (by norm_num)
theorem B3814181 : Blo 1128631 3814181 := bbase (se 4 (by rfl) ⟨357579, by rfl⟩ : syracuseStep 3814181 = 715159) (by norm_num)
theorem B3224357 : Blo 1128631 3224357 := bbase (se 4 (by rfl) ⟨302283, by rfl⟩ : syracuseStep 3224357 = 604567) (by norm_num)
theorem B2863957 : Blo 1128631 2863957 := bbase (se 9 (by rfl) ⟨8390, by rfl⟩ : syracuseStep 2863957 = 16781) (by norm_num)
theorem B2143093 : Blo 1128631 2143093 := bbase (se 5 (by rfl) ⟨100457, by rfl⟩ : syracuseStep 2143093 = 200915) (by norm_num)
theorem B1291177 : Blo 1128631 1291177 := bbase (se 2 (by rfl) ⟨484191, by rfl⟩ : syracuseStep 1291177 = 968383) (by norm_num)
theorem B2864069 : Blo 1128631 2864069 := bbase (se 4 (by rfl) ⟨268506, by rfl⟩ : syracuseStep 2864069 = 537013) (by norm_num)
theorem B3224549 : Blo 1128631 3224549 := bbase (se 4 (by rfl) ⟨302301, by rfl⟩ : syracuseStep 3224549 = 604603) (by norm_num)
theorem B2143253 : Blo 1128631 2143253 := bbase (se 6 (by rfl) ⟨50232, by rfl⟩ : syracuseStep 2143253 = 100465) (by norm_num)
theorem B2864261 : Blo 1128631 2864261 := bbase (se 4 (by rfl) ⟨268524, by rfl⟩ : syracuseStep 2864261 = 537049) (by norm_num)
theorem B2143397 : Blo 1128631 2143397 := bbase (se 4 (by rfl) ⟨200943, by rfl⟩ : syracuseStep 2143397 = 401887) (by norm_num)
theorem B3814613 : Blo 1128631 3814613 := bbase (se 7 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 3814613 = 89405) (by norm_num)
theorem B1357085 : Blo 1128631 1357085 := bbase (se 3 (by rfl) ⟨254453, by rfl⟩ : syracuseStep 1357085 = 508907) (by norm_num)
theorem B11744597 : Blo 1128631 11744597 := bbase (se 13 (by rfl) ⟨2150, by rfl⟩ : syracuseStep 11744597 = 4301) (by norm_num)
theorem B2143685 : Blo 1128631 2143685 := bbase (se 4 (by rfl) ⟨200970, by rfl⟩ : syracuseStep 2143685 = 401941) (by norm_num)
theorem B2864605 : Blo 1128631 2864605 := bbase (se 3 (by rfl) ⟨537113, by rfl⟩ : syracuseStep 2864605 = 1074227) (by norm_num)
theorem B3618341 : Blo 1128631 3618341 := bbase (se 4 (by rfl) ⟨339219, by rfl⟩ : syracuseStep 3618341 = 678439) (by norm_num)
theorem B2864717 : Blo 1128631 2864717 := bbase (se 3 (by rfl) ⟨537134, by rfl⟩ : syracuseStep 2864717 = 1074269) (by norm_num)
theorem B1357393 : Blo 1128631 1357393 := bbase (se 2 (by rfl) ⟨509022, by rfl⟩ : syracuseStep 1357393 = 1018045) (by norm_num)
theorem B2143837 : Blo 1128631 2143837 := bbase (se 3 (by rfl) ⟨401969, by rfl⟩ : syracuseStep 2143837 = 803939) (by norm_num)
theorem B3815045 : Blo 1128631 3815045 := bbase (se 4 (by rfl) ⟨357660, by rfl⟩ : syracuseStep 3815045 = 715321) (by norm_num)
theorem B1357493 : Blo 1128631 1357493 := bbase (se 5 (by rfl) ⟨63632, by rfl⟩ : syracuseStep 1357493 = 127265) (by norm_num)
theorem B2864909 : Blo 1128631 2864909 := bbase (se 3 (by rfl) ⟨537170, by rfl⟩ : syracuseStep 2864909 = 1074341) (by norm_num)
theorem B3094325 : Blo 1128631 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B5715845 : Blo 1128631 5715845 := bbase (se 4 (by rfl) ⟨535860, by rfl⟩ : syracuseStep 5715845 = 1071721) (by norm_num)
theorem B2144141 : Blo 1128631 2144141 := bbase (se 3 (by rfl) ⟨402026, by rfl⟩ : syracuseStep 2144141 = 804053) (by norm_num)
theorem B1718261 : Blo 1128631 1718261 := bbase (se 5 (by rfl) ⟨80543, by rfl⟩ : syracuseStep 1718261 = 161087) (by norm_num)
theorem B3815477 : Blo 1128631 3815477 := bbase (se 5 (by rfl) ⟨178850, by rfl⟩ : syracuseStep 3815477 = 357701) (by norm_num)
theorem B1357897 : Blo 1128631 1357897 := bbase (se 2 (by rfl) ⟨509211, by rfl⟩ : syracuseStep 1357897 = 1018423) (by norm_num)
theorem B2865253 : Blo 1128631 2865253 := bbase (se 4 (by rfl) ⟨268617, by rfl⟩ : syracuseStep 2865253 = 537235) (by norm_num)
theorem B2865365 : Blo 1128631 2865365 := bbase (se 7 (by rfl) ⟨33578, by rfl⟩ : syracuseStep 2865365 = 67157) (by norm_num)
theorem B2865557 : Blo 1128631 2865557 := bbase (se 6 (by rfl) ⟨67161, by rfl⟩ : syracuseStep 2865557 = 134323) (by norm_num)
theorem B1358281 : Blo 1128631 1358281 := bbase (se 2 (by rfl) ⟨509355, by rfl⟩ : syracuseStep 1358281 = 1018711) (by norm_num)
theorem B3815909 : Blo 1128631 3815909 := bbase (se 4 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 3815909 = 715483) (by norm_num)
theorem B2144893 : Blo 1128631 2144893 := bbase (se 3 (by rfl) ⟨402167, by rfl⟩ : syracuseStep 2144893 = 804335) (by norm_num)
theorem B4831973 : Blo 1128631 4831973 := bbase (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) (by norm_num)
theorem B2865901 : Blo 1128631 2865901 := bbase (se 3 (by rfl) ⟨537356, by rfl⟩ : syracuseStep 2865901 = 1074713) (by norm_num)
theorem B2145037 : Blo 1128631 2145037 := bbase (se 3 (by rfl) ⟨402194, by rfl⟩ : syracuseStep 2145037 = 804389) (by norm_num)
theorem B2866013 : Blo 1128631 2866013 := bbase (se 3 (by rfl) ⟨537377, by rfl⟩ : syracuseStep 2866013 = 1074755) (by norm_num)
theorem B3816341 : Blo 1128631 3816341 := bbase (se 6 (by rfl) ⟨89445, by rfl⟩ : syracuseStep 3816341 = 178891) (by norm_num)
theorem B2145197 : Blo 1128631 2145197 := bbase (se 3 (by rfl) ⟨402224, by rfl⟩ : syracuseStep 2145197 = 804449) (by norm_num)
theorem B1489949 : Blo 1128631 1489949 := bbase (se 3 (by rfl) ⟨279365, by rfl⟩ : syracuseStep 1489949 = 558731) (by norm_num)
theorem B2866205 : Blo 1128631 2866205 := bbase (se 3 (by rfl) ⟨537413, by rfl⟩ : syracuseStep 2866205 = 1074827) (by norm_num)
theorem B2145341 : Blo 1128631 2145341 := bbase (se 3 (by rfl) ⟨402251, by rfl⟩ : syracuseStep 2145341 = 804503) (by norm_num)
theorem B5717141 : Blo 1128631 5717141 := bbase (se 6 (by rfl) ⟨133995, by rfl⟩ : syracuseStep 5717141 = 267991) (by norm_num)
theorem B1359137 : Blo 1128631 1359137 := bbase (se 2 (by rfl) ⟨509676, by rfl⟩ : syracuseStep 1359137 = 1019353) (by norm_num)
theorem B8142133 : Blo 1128631 8142133 := bbase (se 5 (by rfl) ⟨381662, by rfl⟩ : syracuseStep 8142133 = 763325) (by norm_num)
theorem B3816773 : Blo 1128631 3816773 := bbase (se 4 (by rfl) ⟨357822, by rfl⟩ : syracuseStep 3816773 = 715645) (by norm_num)
theorem B2145629 : Blo 1128631 2145629 := bbase (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) (by norm_num)
theorem B2866549 : Blo 1128631 2866549 := bbase (se 5 (by rfl) ⟨134369, by rfl⟩ : syracuseStep 2866549 = 268739) (by norm_num)
theorem B2866661 : Blo 1128631 2866661 := bbase (se 4 (by rfl) ⟨268749, by rfl⟩ : syracuseStep 2866661 = 537499) (by norm_num)
theorem B2145781 : Blo 1128631 2145781 := bbase (se 5 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 2145781 = 201167) (by norm_num)
theorem B1359445 : Blo 1128631 1359445 := bbase (se 8 (by rfl) ⟨7965, by rfl⟩ : syracuseStep 1359445 = 15931) (by norm_num)
theorem B2866853 : Blo 1128631 2866853 := bbase (se 4 (by rfl) ⟨268767, by rfl⟩ : syracuseStep 2866853 = 537535) (by norm_num)
theorem B3620533 : Blo 1128631 3620533 := bbase (se 5 (by rfl) ⟨169712, by rfl⟩ : syracuseStep 3620533 = 339425) (by norm_num)
theorem B3817205 : Blo 1128631 3817205 := bbase (se 5 (by rfl) ⟨178931, by rfl⟩ : syracuseStep 3817205 = 357863) (by norm_num)
theorem B2899709 : Blo 1128631 2899709 := bbase (se 3 (by rfl) ⟨543695, by rfl⟩ : syracuseStep 2899709 = 1087391) (by norm_num)
theorem B2146085 : Blo 1128631 2146085 := bbase (se 4 (by rfl) ⟨201195, by rfl⟩ : syracuseStep 2146085 = 402391) (by norm_num)
theorem B1359661 : Blo 1128631 1359661 := bbase (se 3 (by rfl) ⟨254936, by rfl⟩ : syracuseStep 1359661 = 509873) (by norm_num)
theorem B10305397 : Blo 1128631 10305397 := bbase (se 5 (by rfl) ⟨483065, by rfl⟩ : syracuseStep 10305397 = 966131) (by norm_num)
theorem B2539421 : Blo 1128631 2539421 := bbase (se 3 (by rfl) ⟨476141, by rfl⟩ : syracuseStep 2539421 = 952283) (by norm_num)
theorem B2539493 : Blo 1128631 2539493 := bbase (se 4 (by rfl) ⟨238077, by rfl⟩ : syracuseStep 2539493 = 476155) (by norm_num)
theorem B2539565 : Blo 1128631 2539565 := bbase (se 3 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 2539565 = 952337) (by norm_num)
theorem B2539637 : Blo 1128631 2539637 := bbase (se 5 (by rfl) ⟨119045, by rfl⟩ : syracuseStep 2539637 = 238091) (by norm_num)
theorem B3817637 : Blo 1128631 3817637 := bbase (se 4 (by rfl) ⟨357903, by rfl⟩ : syracuseStep 3817637 = 715807) (by norm_num)
theorem B2539709 : Blo 1128631 2539709 := bbase (se 3 (by rfl) ⟨476195, by rfl⟩ : syracuseStep 2539709 = 952391) (by norm_num)
theorem B4079861 : Blo 1128631 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B2539781 : Blo 1128631 2539781 := bbase (se 4 (by rfl) ⟨238104, by rfl⟩ : syracuseStep 2539781 = 476209) (by norm_num)
theorem B2539853 : Blo 1128631 2539853 := bbase (se 3 (by rfl) ⟨476222, by rfl⟩ : syracuseStep 2539853 = 952445) (by norm_num)
theorem B1360261 : Blo 1128631 1360261 := bbase (se 4 (by rfl) ⟨127524, by rfl⟩ : syracuseStep 1360261 = 255049) (by norm_num)
theorem B2539925 : Blo 1128631 2539925 := bbase (se 6 (by rfl) ⟨59529, by rfl⟩ : syracuseStep 2539925 = 119059) (by norm_num)
theorem B5718437 : Blo 1128631 5718437 := bbase (se 4 (by rfl) ⟨536103, by rfl⟩ : syracuseStep 5718437 = 1072207) (by norm_num)
theorem B4833749 : Blo 1128631 4833749 := bbase (se 7 (by rfl) ⟨56645, by rfl⟩ : syracuseStep 4833749 = 113291) (by norm_num)
theorem B2539997 : Blo 1128631 2539997 := bbase (se 3 (by rfl) ⟨476249, by rfl⟩ : syracuseStep 2539997 = 952499) (by norm_num)
theorem B3621365 : Blo 1128631 3621365 := bbase (se 5 (by rfl) ⟨169751, by rfl⟩ : syracuseStep 3621365 = 339503) (by norm_num)
theorem B2146837 : Blo 1128631 2146837 := bbase (se 6 (by rfl) ⟨50316, by rfl⟩ : syracuseStep 2146837 = 100633) (by norm_num)
theorem B2540069 : Blo 1128631 2540069 := bbase (se 4 (by rfl) ⟨238131, by rfl⟩ : syracuseStep 2540069 = 476263) (by norm_num)
theorem B5423669 : Blo 1128631 5423669 := bbase (se 5 (by rfl) ⟨254234, by rfl⟩ : syracuseStep 5423669 = 508469) (by norm_num)
theorem B3818069 : Blo 1128631 3818069 := bbase (se 8 (by rfl) ⟨22371, by rfl⟩ : syracuseStep 3818069 = 44743) (by norm_num)
theorem B2900573 : Blo 1128631 2900573 := bbase (se 3 (by rfl) ⟨543857, by rfl⟩ : syracuseStep 2900573 = 1087715) (by norm_num)
theorem B2540141 : Blo 1128631 2540141 := bbase (se 3 (by rfl) ⟨476276, by rfl⟩ : syracuseStep 2540141 = 952553) (by norm_num)
theorem B9159317 : Blo 1128631 9159317 := bbase (se 6 (by rfl) ⟨214671, by rfl⟩ : syracuseStep 9159317 = 429343) (by norm_num)
theorem B2146981 : Blo 1128631 2146981 := bbase (se 4 (by rfl) ⟨201279, by rfl⟩ : syracuseStep 2146981 = 402559) (by norm_num)
theorem B2540213 : Blo 1128631 2540213 := bbase (se 5 (by rfl) ⟨119072, by rfl⟩ : syracuseStep 2540213 = 238145) (by norm_num)
theorem B1721021 : Blo 1128631 1721021 := bbase (se 3 (by rfl) ⟨322691, by rfl⟩ : syracuseStep 1721021 = 645383) (by norm_num)
theorem B4833989 : Blo 1128631 4833989 := bbase (se 4 (by rfl) ⟨453186, by rfl⟩ : syracuseStep 4833989 = 906373) (by norm_num)
theorem B2540285 : Blo 1128631 2540285 := bbase (se 3 (by rfl) ⟨476303, by rfl⟩ : syracuseStep 2540285 = 952607) (by norm_num)
theorem B2540357 : Blo 1128631 2540357 := bbase (se 4 (by rfl) ⟨238158, by rfl⟩ : syracuseStep 2540357 = 476317) (by norm_num)
theorem B2147141 : Blo 1128631 2147141 := bbase (se 4 (by rfl) ⟨201294, by rfl⟩ : syracuseStep 2147141 = 402589) (by norm_num)
theorem B11027285 : Blo 1128631 11027285 := bbase (se 9 (by rfl) ⟨32306, by rfl⟩ : syracuseStep 11027285 = 64613) (by norm_num)
theorem B2540429 : Blo 1128631 2540429 := bbase (se 3 (by rfl) ⟨476330, by rfl⟩ : syracuseStep 2540429 = 952661) (by norm_num)
theorem B2540501 : Blo 1128631 2540501 := bbase (se 7 (by rfl) ⟨29771, by rfl⟩ : syracuseStep 2540501 = 59543) (by norm_num)
theorem B2147285 : Blo 1128631 2147285 := bbase (se 7 (by rfl) ⟨25163, by rfl⟩ : syracuseStep 2147285 = 50327) (by norm_num)
theorem B3818501 : Blo 1128631 3818501 := bbase (se 4 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 3818501 = 715969) (by norm_num)
theorem B2540573 : Blo 1128631 2540573 := bbase (se 3 (by rfl) ⟨476357, by rfl⟩ : syracuseStep 2540573 = 952715) (by norm_num)
theorem B2540645 : Blo 1128631 2540645 := bbase (se 4 (by rfl) ⟨238185, by rfl⟩ : syracuseStep 2540645 = 476371) (by norm_num)
theorem B2540717 : Blo 1128631 2540717 := bbase (se 3 (by rfl) ⟨476384, by rfl⟩ : syracuseStep 2540717 = 952769) (by norm_num)
theorem B2540789 : Blo 1128631 2540789 := bbase (se 5 (by rfl) ⟨119099, by rfl⟩ : syracuseStep 2540789 = 238199) (by norm_num)
theorem B2147573 : Blo 1128631 2147573 := bbase (se 5 (by rfl) ⟨100667, by rfl⟩ : syracuseStep 2147573 = 201335) (by norm_num)
theorem B2540861 : Blo 1128631 2540861 := bbase (se 3 (by rfl) ⟨476411, by rfl⟩ : syracuseStep 2540861 = 952823) (by norm_num)
theorem B2901341 : Blo 1128631 2901341 := bbase (se 3 (by rfl) ⟨544001, by rfl⟩ : syracuseStep 2901341 = 1088003) (by norm_num)
theorem B2540933 : Blo 1128631 2540933 := bbase (se 4 (by rfl) ⟨238212, by rfl⟩ : syracuseStep 2540933 = 476425) (by norm_num)
theorem B2147725 : Blo 1128631 2147725 := bbase (se 3 (by rfl) ⟨402698, by rfl⟩ : syracuseStep 2147725 = 805397) (by norm_num)
theorem B5162405 : Blo 1128631 5162405 := bbase (se 4 (by rfl) ⟨483975, by rfl⟩ : syracuseStep 5162405 = 967951) (by norm_num)
theorem B3818933 : Blo 1128631 3818933 := bbase (se 5 (by rfl) ⟨179012, by rfl⟩ : syracuseStep 3818933 = 358025) (by norm_num)
theorem B2541005 : Blo 1128631 2541005 := bbase (se 3 (by rfl) ⟨476438, by rfl⟩ : syracuseStep 2541005 = 952877) (by norm_num)
theorem B2541077 : Blo 1128631 2541077 := bbase (se 6 (by rfl) ⟨59556, by rfl⟩ : syracuseStep 2541077 = 119113) (by norm_num)
theorem B2541149 : Blo 1128631 2541149 := bbase (se 3 (by rfl) ⟨476465, by rfl⟩ : syracuseStep 2541149 = 952931) (by norm_num)
theorem B2541221 : Blo 1128631 2541221 := bbase (se 4 (by rfl) ⟨238239, by rfl⟩ : syracuseStep 2541221 = 476479) (by norm_num)
theorem B1525429 : Blo 1128631 1525429 := bbase (se 5 (by rfl) ⟨71504, by rfl⟩ : syracuseStep 1525429 = 143009) (by norm_num)
theorem B5719733 : Blo 1128631 5719733 := bbase (se 5 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 5719733 = 536225) (by norm_num)
theorem B2148029 : Blo 1128631 2148029 := bbase (se 3 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 2148029 = 805511) (by norm_num)
theorem B2541293 : Blo 1128631 2541293 := bbase (se 3 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 2541293 = 952985) (by norm_num)
theorem B2541365 : Blo 1128631 2541365 := bbase (se 5 (by rfl) ⟨119126, by rfl⟩ : syracuseStep 2541365 = 238253) (by norm_num)
theorem B3819365 : Blo 1128631 3819365 := bbase (se 4 (by rfl) ⟨358065, by rfl⟩ : syracuseStep 3819365 = 716131) (by norm_num)
theorem B2574197 : Blo 1128631 2574197 := bbase (se 5 (by rfl) ⟨120665, by rfl⟩ : syracuseStep 2574197 = 241331) (by norm_num)
theorem B2541437 : Blo 1128631 2541437 := bbase (se 3 (by rfl) ⟨476519, by rfl⟩ : syracuseStep 2541437 = 953039) (by norm_num)
theorem B1525645 : Blo 1128631 1525645 := bbase (se 3 (by rfl) ⟨286058, by rfl⟩ : syracuseStep 1525645 = 572117) (by norm_num)
theorem B2541509 : Blo 1128631 2541509 := bbase (se 4 (by rfl) ⟨238266, by rfl⟩ : syracuseStep 2541509 = 476533) (by norm_num)
theorem B2541581 : Blo 1128631 2541581 := bbase (se 3 (by rfl) ⟨476546, by rfl⟩ : syracuseStep 2541581 = 953093) (by norm_num)
theorem B2541653 : Blo 1128631 2541653 := bbase (se 8 (by rfl) ⟨14892, by rfl⟩ : syracuseStep 2541653 = 29785) (by norm_num)
theorem B2541725 : Blo 1128631 2541725 := bbase (se 3 (by rfl) ⟨476573, by rfl⟩ : syracuseStep 2541725 = 953147) (by norm_num)
theorem B2541797 : Blo 1128631 2541797 := bbase (se 4 (by rfl) ⟨238293, by rfl⟩ : syracuseStep 2541797 = 476587) (by norm_num)
theorem B3819797 : Blo 1128631 3819797 := bbase (se 6 (by rfl) ⟨89526, by rfl⟩ : syracuseStep 3819797 = 179053) (by norm_num)
theorem B1526045 : Blo 1128631 1526045 := bbase (se 3 (by rfl) ⟨286133, by rfl⟩ : syracuseStep 1526045 = 572267) (by norm_num)
theorem B2541869 : Blo 1128631 2541869 := bbase (se 3 (by rfl) ⟨476600, by rfl⟩ : syracuseStep 2541869 = 953201) (by norm_num)
theorem B1526077 : Blo 1128631 1526077 := bbase (se 3 (by rfl) ⟨286139, by rfl⟩ : syracuseStep 1526077 = 572279) (by norm_num)
theorem B3623237 : Blo 1128631 3623237 := bbase (se 4 (by rfl) ⟨339678, by rfl⟩ : syracuseStep 3623237 = 679357) (by norm_num)
theorem B2541941 : Blo 1128631 2541941 := bbase (se 5 (by rfl) ⟨119153, by rfl⟩ : syracuseStep 2541941 = 238307) (by norm_num)
theorem B2148781 : Blo 1128631 2148781 := bbase (se 3 (by rfl) ⟨402896, by rfl⟩ : syracuseStep 2148781 = 805793) (by norm_num)
theorem B2542013 : Blo 1128631 2542013 := bbase (se 3 (by rfl) ⟨476627, by rfl⟩ : syracuseStep 2542013 = 953255) (by norm_num)
theorem B2542085 : Blo 1128631 2542085 := bbase (se 4 (by rfl) ⟨238320, by rfl⟩ : syracuseStep 2542085 = 476641) (by norm_num)
theorem B2148925 : Blo 1128631 2148925 := bbase (se 3 (by rfl) ⟨402923, by rfl⟩ : syracuseStep 2148925 = 805847) (by norm_num)
theorem B2542157 : Blo 1128631 2542157 := bbase (se 3 (by rfl) ⟨476654, by rfl⟩ : syracuseStep 2542157 = 953309) (by norm_num)
theorem B2411117 : Blo 1128631 2411117 := bbase (se 3 (by rfl) ⟨452084, by rfl⟩ : syracuseStep 2411117 = 904169) (by norm_num)
theorem B2542229 : Blo 1128631 2542229 := bbase (se 6 (by rfl) ⟨59583, by rfl⟩ : syracuseStep 2542229 = 119167) (by norm_num)
theorem B3820229 : Blo 1128631 3820229 := bbase (se 4 (by rfl) ⟨358146, by rfl⟩ : syracuseStep 3820229 = 716293) (by norm_num)
theorem B2542301 : Blo 1128631 2542301 := bbase (se 3 (by rfl) ⟨476681, by rfl⟩ : syracuseStep 2542301 = 953363) (by norm_num)
theorem B2149085 : Blo 1128631 2149085 := bbase (se 3 (by rfl) ⟨402953, by rfl⟩ : syracuseStep 2149085 = 805907) (by norm_num)
theorem B2575109 : Blo 1128631 2575109 := bbase (se 4 (by rfl) ⟨241416, by rfl⟩ : syracuseStep 2575109 = 482833) (by norm_num)
theorem B2542373 : Blo 1128631 2542373 := bbase (se 4 (by rfl) ⟨238347, by rfl⟩ : syracuseStep 2542373 = 476695) (by norm_num)
theorem B9161525 : Blo 1128631 9161525 := bbase (se 5 (by rfl) ⟨429446, by rfl⟩ : syracuseStep 9161525 = 858893) (by norm_num)
theorem B2411365 : Blo 1128631 2411365 := bbase (se 4 (by rfl) ⟨226065, by rfl⟩ : syracuseStep 2411365 = 452131) (by norm_num)
theorem B2542445 : Blo 1128631 2542445 := bbase (se 3 (by rfl) ⟨476708, by rfl⟩ : syracuseStep 2542445 = 953417) (by norm_num)
theorem B2149229 : Blo 1128631 2149229 := bbase (se 3 (by rfl) ⟨402980, by rfl⟩ : syracuseStep 2149229 = 805961) (by norm_num)
theorem B2542517 : Blo 1128631 2542517 := bbase (se 5 (by rfl) ⟨119180, by rfl⟩ : syracuseStep 2542517 = 238361) (by norm_num)
theorem B4836277 : Blo 1128631 4836277 := bbase (se 5 (by rfl) ⟨226700, by rfl⟩ : syracuseStep 4836277 = 453401) (by norm_num)
theorem B5721029 : Blo 1128631 5721029 := bbase (se 4 (by rfl) ⟨536346, by rfl⟩ : syracuseStep 5721029 = 1072693) (by norm_num)
theorem B1428445 : Blo 1128631 1428445 := bbase (se 3 (by rfl) ⟨267833, by rfl⟩ : syracuseStep 1428445 = 535667) (by norm_num)
theorem B2542589 : Blo 1128631 2542589 := bbase (se 3 (by rfl) ⟨476735, by rfl⟩ : syracuseStep 2542589 = 953471) (by norm_num)
theorem B6442037 : Blo 1128631 6442037 := bbase (se 5 (by rfl) ⟨301970, by rfl⟩ : syracuseStep 6442037 = 603941) (by norm_num)
theorem B2542661 : Blo 1128631 2542661 := bbase (se 4 (by rfl) ⟨238374, by rfl⟩ : syracuseStep 2542661 = 476749) (by norm_num)
theorem B3820661 : Blo 1128631 3820661 := bbase (se 5 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 3820661 = 358187) (by norm_num)
theorem B1428617 : Blo 1128631 1428617 := bbase (se 2 (by rfl) ⟨535731, by rfl⟩ : syracuseStep 1428617 = 1071463) (by norm_num)
theorem B2542733 : Blo 1128631 2542733 := bbase (se 3 (by rfl) ⟨476762, by rfl⟩ : syracuseStep 2542733 = 953525) (by norm_num)
theorem B2149517 : Blo 1128631 2149517 := bbase (se 3 (by rfl) ⟨403034, by rfl⟩ : syracuseStep 2149517 = 806069) (by norm_num)
theorem B19319957 : Blo 1128631 19319957 := bbase (se 6 (by rfl) ⟨452811, by rfl⟩ : syracuseStep 19319957 = 905623) (by norm_num)
theorem B5426357 : Blo 1128631 5426357 := bbase (se 5 (by rfl) ⟨254360, by rfl⟩ : syracuseStep 5426357 = 508721) (by norm_num)
theorem B1428673 : Blo 1128631 1428673 := bbase (se 2 (by rfl) ⟨535752, by rfl⟩ : syracuseStep 1428673 = 1071505) (by norm_num)
theorem B2542805 : Blo 1128631 2542805 := bbase (se 7 (by rfl) ⟨29798, by rfl⟩ : syracuseStep 2542805 = 59597) (by norm_num)
theorem B2542877 : Blo 1128631 2542877 := bbase (se 3 (by rfl) ⟨476789, by rfl⟩ : syracuseStep 2542877 = 953579) (by norm_num)
theorem B1428769 : Blo 1128631 1428769 := bbase (se 2 (by rfl) ⟨535788, by rfl⟩ : syracuseStep 1428769 = 1071577) (by norm_num)
theorem B2149669 : Blo 1128631 2149669 := bbase (se 4 (by rfl) ⟨201531, by rfl⟩ : syracuseStep 2149669 = 403063) (by norm_num)
theorem B2411869 : Blo 1128631 2411869 := bbase (se 3 (by rfl) ⟨452225, by rfl⟩ : syracuseStep 2411869 = 904451) (by norm_num)
theorem B2542949 : Blo 1128631 2542949 := bbase (se 4 (by rfl) ⟨238401, by rfl⟩ : syracuseStep 2542949 = 476803) (by norm_num)
theorem B2543021 : Blo 1128631 2543021 := bbase (se 3 (by rfl) ⟨476816, by rfl⟩ : syracuseStep 2543021 = 953633) (by norm_num)
theorem B1428941 : Blo 1128631 1428941 := bbase (se 3 (by rfl) ⟨267926, by rfl⟩ : syracuseStep 1428941 = 535853) (by norm_num)
theorem B2543093 : Blo 1128631 2543093 := bbase (se 5 (by rfl) ⟨119207, by rfl⟩ : syracuseStep 2543093 = 238415) (by norm_num)
theorem B1428997 : Blo 1128631 1428997 := bbase (se 4 (by rfl) ⟨133968, by rfl⟩ : syracuseStep 1428997 = 267937) (by norm_num)
theorem B3821093 : Blo 1128631 3821093 := bbase (se 4 (by rfl) ⟨358227, by rfl⟩ : syracuseStep 3821093 = 716455) (by norm_num)
theorem B5164597 : Blo 1128631 5164597 := bbase (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) (by norm_num)
theorem B2543165 : Blo 1128631 2543165 := bbase (se 3 (by rfl) ⟨476843, by rfl⟩ : syracuseStep 2543165 = 953687) (by norm_num)
theorem B2149973 : Blo 1128631 2149973 := bbase (se 8 (by rfl) ⟨12597, by rfl⟩ : syracuseStep 2149973 = 25195) (by norm_num)
theorem B1429093 : Blo 1128631 1429093 := bbase (se 4 (by rfl) ⟨133977, by rfl⟩ : syracuseStep 1429093 = 267955) (by norm_num)
theorem B2543237 : Blo 1128631 2543237 := bbase (se 4 (by rfl) ⟨238428, by rfl⟩ : syracuseStep 2543237 = 476857) (by norm_num)
theorem B4181701 : Blo 1128631 4181701 := bbase (se 4 (by rfl) ⟨392034, by rfl⟩ : syracuseStep 4181701 = 784069) (by norm_num)
theorem B2543309 : Blo 1128631 2543309 := bbase (se 3 (by rfl) ⟨476870, by rfl⟩ : syracuseStep 2543309 = 953741) (by norm_num)
theorem B1429265 : Blo 1128631 1429265 := bbase (se 2 (by rfl) ⟨535974, by rfl⟩ : syracuseStep 1429265 = 1071949) (by norm_num)
theorem B2543381 : Blo 1128631 2543381 := bbase (se 6 (by rfl) ⟨59610, by rfl⟩ : syracuseStep 2543381 = 119221) (by norm_num)
theorem B1429321 : Blo 1128631 1429321 := bbase (se 2 (by rfl) ⟨535995, by rfl⟩ : syracuseStep 1429321 = 1071991) (by norm_num)
theorem B2543453 : Blo 1128631 2543453 := bbase (se 3 (by rfl) ⟨476897, by rfl⟩ : syracuseStep 2543453 = 953795) (by norm_num)
theorem B2543525 : Blo 1128631 2543525 := bbase (se 4 (by rfl) ⟨238455, by rfl⟩ : syracuseStep 2543525 = 476911) (by norm_num)
theorem B1429417 : Blo 1128631 1429417 := bbase (se 2 (by rfl) ⟨536031, by rfl⟩ : syracuseStep 1429417 = 1072063) (by norm_num)
theorem B3821525 : Blo 1128631 3821525 := bbase (se 7 (by rfl) ⟨44783, by rfl⟩ : syracuseStep 3821525 = 89567) (by norm_num)
theorem B2543597 : Blo 1128631 2543597 := bbase (se 3 (by rfl) ⟨476924, by rfl⟩ : syracuseStep 2543597 = 953849) (by norm_num)
theorem B2543669 : Blo 1128631 2543669 := bbase (se 5 (by rfl) ⟨119234, by rfl⟩ : syracuseStep 2543669 = 238469) (by norm_num)
theorem B1429589 : Blo 1128631 1429589 := bbase (se 8 (by rfl) ⟨8376, by rfl⟩ : syracuseStep 1429589 = 16753) (by norm_num)
theorem B2543741 : Blo 1128631 2543741 := bbase (se 3 (by rfl) ⟨476951, by rfl⟩ : syracuseStep 2543741 = 953903) (by norm_num)
theorem B1429645 : Blo 1128631 1429645 := bbase (se 3 (by rfl) ⟨268058, by rfl⟩ : syracuseStep 1429645 = 536117) (by norm_num)
theorem B2543813 : Blo 1128631 2543813 := bbase (se 4 (by rfl) ⟨238482, by rfl⟩ : syracuseStep 2543813 = 476965) (by norm_num)
theorem B14110933 : Blo 1128631 14110933 := bbase (se 7 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 14110933 = 330725) (by norm_num)
theorem B2412757 : Blo 1128631 2412757 := bbase (se 7 (by rfl) ⟨28274, by rfl⟩ : syracuseStep 2412757 = 56549) (by norm_num)
theorem B5722325 : Blo 1128631 5722325 := bbase (se 7 (by rfl) ⟨67058, by rfl⟩ : syracuseStep 5722325 = 134117) (by norm_num)
theorem B1429741 : Blo 1128631 1429741 := bbase (se 3 (by rfl) ⟨268076, by rfl⟩ : syracuseStep 1429741 = 536153) (by norm_num)
theorem B2543885 : Blo 1128631 2543885 := bbase (se 3 (by rfl) ⟨476978, by rfl⟩ : syracuseStep 2543885 = 953957) (by norm_num)
theorem B4641077 : Blo 1128631 4641077 := bbase (se 5 (by rfl) ⟨217550, by rfl⟩ : syracuseStep 4641077 = 435101) (by norm_num)
theorem B2543957 : Blo 1128631 2543957 := bbase (se 10 (by rfl) ⟨3726, by rfl⟩ : syracuseStep 2543957 = 7453) (by norm_num)
theorem B3821957 : Blo 1128631 3821957 := bbase (se 4 (by rfl) ⟨358308, by rfl⟩ : syracuseStep 3821957 = 716617) (by norm_num)
theorem B4837765 : Blo 1128631 4837765 := bbase (se 4 (by rfl) ⟨453540, by rfl⟩ : syracuseStep 4837765 = 907081) (by norm_num)
theorem B4837781 : Blo 1128631 4837781 := bbase (se 6 (by rfl) ⟨113385, by rfl⟩ : syracuseStep 4837781 = 226771) (by norm_num)
theorem B1429913 : Blo 1128631 1429913 := bbase (se 2 (by rfl) ⟨536217, by rfl⟩ : syracuseStep 1429913 = 1072435) (by norm_num)
theorem B2544029 : Blo 1128631 2544029 := bbase (se 3 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 2544029 = 954011) (by norm_num)
theorem B1429969 : Blo 1128631 1429969 := bbase (se 2 (by rfl) ⟨536238, by rfl⟩ : syracuseStep 1429969 = 1072477) (by norm_num)
theorem B2544101 : Blo 1128631 2544101 := bbase (se 4 (by rfl) ⟨238509, by rfl⟩ : syracuseStep 2544101 = 477019) (by norm_num)
theorem B2544173 : Blo 1128631 2544173 := bbase (se 3 (by rfl) ⟨477032, by rfl⟩ : syracuseStep 2544173 = 954065) (by norm_num)
theorem B1430065 : Blo 1128631 1430065 := bbase (se 2 (by rfl) ⟨536274, by rfl⟩ : syracuseStep 1430065 = 1072549) (by norm_num)
theorem B8573525 : Blo 1128631 8573525 := bbase (se 8 (by rfl) ⟨50235, by rfl⟩ : syracuseStep 8573525 = 100471) (by norm_num)
theorem B2544245 : Blo 1128631 2544245 := bbase (se 5 (by rfl) ⟨119261, by rfl⟩ : syracuseStep 2544245 = 238523) (by norm_num)
theorem B2544317 : Blo 1128631 2544317 := bbase (se 3 (by rfl) ⟨477059, by rfl⟩ : syracuseStep 2544317 = 954119) (by norm_num)
theorem B2413253 : Blo 1128631 2413253 := bbase (se 4 (by rfl) ⟨226242, by rfl⟩ : syracuseStep 2413253 = 452485) (by norm_num)
theorem B1430237 : Blo 1128631 1430237 := bbase (se 3 (by rfl) ⟨268169, by rfl⟩ : syracuseStep 1430237 = 536339) (by norm_num)
theorem B10867445 : Blo 1128631 10867445 := bbase (se 5 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 10867445 = 1018823) (by norm_num)
theorem B2544389 : Blo 1128631 2544389 := bbase (se 4 (by rfl) ⟨238536, by rfl⟩ : syracuseStep 2544389 = 477073) (by norm_num)
theorem B1430293 : Blo 1128631 1430293 := bbase (se 6 (by rfl) ⟨33522, by rfl⟩ : syracuseStep 1430293 = 67045) (by norm_num)
theorem B3822389 : Blo 1128631 3822389 := bbase (se 5 (by rfl) ⟨179174, by rfl⟩ : syracuseStep 3822389 = 358349) (by norm_num)
theorem B2544461 : Blo 1128631 2544461 := bbase (se 3 (by rfl) ⟨477086, by rfl⟩ : syracuseStep 2544461 = 954173) (by norm_num)
theorem B1430389 : Blo 1128631 1430389 := bbase (se 5 (by rfl) ⟨67049, by rfl⟩ : syracuseStep 1430389 = 134099) (by norm_num)
theorem B2511749 : Blo 1128631 2511749 := bbase (se 4 (by rfl) ⟨235476, by rfl⟩ : syracuseStep 2511749 = 470953) (by norm_num)
theorem B2544533 : Blo 1128631 2544533 := bbase (se 6 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 2544533 = 119275) (by norm_num)
theorem B2544605 : Blo 1128631 2544605 := bbase (se 3 (by rfl) ⟨477113, by rfl⟩ : syracuseStep 2544605 = 954227) (by norm_num)
theorem B3626005 : Blo 1128631 3626005 := bbase (se 6 (by rfl) ⟨84984, by rfl⟩ : syracuseStep 3626005 = 169969) (by norm_num)
theorem B1430561 : Blo 1128631 1430561 := bbase (se 2 (by rfl) ⟨536460, by rfl⟩ : syracuseStep 1430561 = 1072921) (by norm_num)
theorem B2544677 : Blo 1128631 2544677 := bbase (se 4 (by rfl) ⟨238563, by rfl⟩ : syracuseStep 2544677 = 477127) (by norm_num)
theorem B1430617 : Blo 1128631 1430617 := bbase (se 2 (by rfl) ⟨536481, by rfl⟩ : syracuseStep 1430617 = 1072963) (by norm_num)
theorem B2544749 : Blo 1128631 2544749 := bbase (se 3 (by rfl) ⟨477140, by rfl⟩ : syracuseStep 2544749 = 954281) (by norm_num)
theorem B2544821 : Blo 1128631 2544821 := bbase (se 5 (by rfl) ⟨119288, by rfl⟩ : syracuseStep 2544821 = 238577) (by norm_num)
theorem B1430713 : Blo 1128631 1430713 := bbase (se 2 (by rfl) ⟨536517, by rfl⟩ : syracuseStep 1430713 = 1073035) (by norm_num)
theorem B2544893 : Blo 1128631 2544893 := bbase (se 3 (by rfl) ⟨477167, by rfl⟩ : syracuseStep 2544893 = 954335) (by norm_num)
theorem B1692965 : Blo 1128631 1692965 := bbase (se 4 (by rfl) ⟨158715, by rfl⟩ : syracuseStep 1692965 = 317431) (by norm_num)
theorem B1692989 : Blo 1128631 1692989 := bbase (se 3 (by rfl) ⟨317435, by rfl⟩ : syracuseStep 1692989 = 634871) (by norm_num)
theorem B2544965 : Blo 1128631 2544965 := bbase (se 4 (by rfl) ⟨238590, by rfl⟩ : syracuseStep 2544965 = 477181) (by norm_num)
theorem B1693013 : Blo 1128631 1693013 := bbase (se 15 (by rfl) ⟨77, by rfl⟩ : syracuseStep 1693013 = 155) (by norm_num)
theorem B1430885 : Blo 1128631 1430885 := bbase (se 4 (by rfl) ⟨134145, by rfl⟩ : syracuseStep 1430885 = 268291) (by norm_num)
theorem B1693037 : Blo 1128631 1693037 := bbase (se 3 (by rfl) ⟨317444, by rfl⟩ : syracuseStep 1693037 = 634889) (by norm_num)
theorem B7853429 : Blo 1128631 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B1693061 : Blo 1128631 1693061 := bbase (se 4 (by rfl) ⟨158724, by rfl⟩ : syracuseStep 1693061 = 317449) (by norm_num)
theorem B2446733 : Blo 1128631 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B2545037 : Blo 1128631 2545037 := bbase (se 3 (by rfl) ⟨477194, by rfl⟩ : syracuseStep 2545037 = 954389) (by norm_num)
theorem B1693085 : Blo 1128631 1693085 := bbase (se 3 (by rfl) ⟨317453, by rfl⟩ : syracuseStep 1693085 = 634907) (by norm_num)
theorem B1430941 : Blo 1128631 1430941 := bbase (se 3 (by rfl) ⟨268301, by rfl⟩ : syracuseStep 1430941 = 536603) (by norm_num)
theorem B1693109 : Blo 1128631 1693109 := bbase (se 5 (by rfl) ⟨79364, by rfl⟩ : syracuseStep 1693109 = 158729) (by norm_num)
theorem B1693133 : Blo 1128631 1693133 := bbase (se 3 (by rfl) ⟨317462, by rfl⟩ : syracuseStep 1693133 = 634925) (by norm_num)
theorem B2545109 : Blo 1128631 2545109 := bbase (se 7 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 2545109 = 59651) (by norm_num)
theorem B1693157 : Blo 1128631 1693157 := bbase (se 4 (by rfl) ⟨158733, by rfl⟩ : syracuseStep 1693157 = 317467) (by norm_num)
theorem B5723621 : Blo 1128631 5723621 := bbase (se 4 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 5723621 = 1073179) (by norm_num)
theorem B1693181 : Blo 1128631 1693181 := bbase (se 3 (by rfl) ⟨317471, by rfl⟩ : syracuseStep 1693181 = 634943) (by norm_num)
theorem B1431037 : Blo 1128631 1431037 := bbase (se 3 (by rfl) ⟨268319, by rfl⟩ : syracuseStep 1431037 = 536639) (by norm_num)
theorem B1693205 : Blo 1128631 1693205 := bbase (se 6 (by rfl) ⟨39684, by rfl⟩ : syracuseStep 1693205 = 79369) (by norm_num)
theorem B2545181 : Blo 1128631 2545181 := bbase (se 3 (by rfl) ⟨477221, by rfl⟩ : syracuseStep 2545181 = 954443) (by norm_num)
theorem B1693229 : Blo 1128631 1693229 := bbase (se 3 (by rfl) ⟨317480, by rfl⟩ : syracuseStep 1693229 = 634961) (by norm_num)
theorem B2414141 : Blo 1128631 2414141 := bbase (se 3 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 2414141 = 905303) (by norm_num)
theorem B4576837 : Blo 1128631 4576837 := bbase (se 4 (by rfl) ⟨429078, by rfl⟩ : syracuseStep 4576837 = 858157) (by norm_num)
theorem B1693253 : Blo 1128631 1693253 := bbase (se 4 (by rfl) ⟨158742, by rfl⟩ : syracuseStep 1693253 = 317485) (by norm_num)
theorem B1693277 : Blo 1128631 1693277 := bbase (se 3 (by rfl) ⟨317489, by rfl⟩ : syracuseStep 1693277 = 634979) (by norm_num)
theorem B2545253 : Blo 1128631 2545253 := bbase (se 4 (by rfl) ⟨238617, by rfl⟩ : syracuseStep 2545253 = 477235) (by norm_num)
theorem B1693301 : Blo 1128631 1693301 := bbase (se 5 (by rfl) ⟨79373, by rfl⟩ : syracuseStep 1693301 = 158747) (by norm_num)
theorem B1693325 : Blo 1128631 1693325 := bbase (se 3 (by rfl) ⟨317498, by rfl⟩ : syracuseStep 1693325 = 634997) (by norm_num)
theorem B1693349 : Blo 1128631 1693349 := bbase (se 4 (by rfl) ⟨158751, by rfl⟩ : syracuseStep 1693349 = 317503) (by norm_num)
theorem B1431209 : Blo 1128631 1431209 := bbase (se 2 (by rfl) ⟨536703, by rfl⟩ : syracuseStep 1431209 = 1073407) (by norm_num)
theorem B2545325 : Blo 1128631 2545325 := bbase (se 3 (by rfl) ⟨477248, by rfl⟩ : syracuseStep 2545325 = 954497) (by norm_num)
theorem B7722677 : Blo 1128631 7722677 := bbase (se 5 (by rfl) ⟨362000, by rfl⟩ : syracuseStep 7722677 = 724001) (by norm_num)
theorem B2414261 : Blo 1128631 2414261 := bbase (se 5 (by rfl) ⟨113168, by rfl⟩ : syracuseStep 2414261 = 226337) (by norm_num)
theorem B1693373 : Blo 1128631 1693373 := bbase (se 3 (by rfl) ⟨317507, by rfl⟩ : syracuseStep 1693373 = 635015) (by norm_num)
theorem B1693397 : Blo 1128631 1693397 := bbase (se 7 (by rfl) ⟨19844, by rfl⟩ : syracuseStep 1693397 = 39689) (by norm_num)
theorem B1431265 : Blo 1128631 1431265 := bbase (se 2 (by rfl) ⟨536724, by rfl⟩ : syracuseStep 1431265 = 1073449) (by norm_num)
theorem B1693421 : Blo 1128631 1693421 := bbase (se 3 (by rfl) ⟨317516, by rfl⟩ : syracuseStep 1693421 = 635033) (by norm_num)
theorem B2545397 : Blo 1128631 2545397 := bbase (se 5 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 2545397 = 238631) (by norm_num)
theorem B1693445 : Blo 1128631 1693445 := bbase (se 4 (by rfl) ⟨158760, by rfl⟩ : syracuseStep 1693445 = 317521) (by norm_num)
theorem B1693469 : Blo 1128631 1693469 := bbase (se 3 (by rfl) ⟨317525, by rfl⟩ : syracuseStep 1693469 = 635051) (by norm_num)
theorem B1693493 : Blo 1128631 1693493 := bbase (se 5 (by rfl) ⟨79382, by rfl⟩ : syracuseStep 1693493 = 158765) (by norm_num)
theorem B2545469 : Blo 1128631 2545469 := bbase (se 3 (by rfl) ⟨477275, by rfl⟩ : syracuseStep 2545469 = 954551) (by norm_num)
theorem B1431361 : Blo 1128631 1431361 := bbase (se 2 (by rfl) ⟨536760, by rfl⟩ : syracuseStep 1431361 = 1073521) (by norm_num)
theorem B1693517 : Blo 1128631 1693517 := bbase (se 3 (by rfl) ⟨317534, by rfl⟩ : syracuseStep 1693517 = 635069) (by norm_num)
theorem B1693541 : Blo 1128631 1693541 := bbase (se 4 (by rfl) ⟨158769, by rfl⟩ : syracuseStep 1693541 = 317539) (by norm_num)
theorem B1693565 : Blo 1128631 1693565 := bbase (se 3 (by rfl) ⟨317543, by rfl⟩ : syracuseStep 1693565 = 635087) (by norm_num)
theorem B2545541 : Blo 1128631 2545541 := bbase (se 4 (by rfl) ⟨238644, by rfl⟩ : syracuseStep 2545541 = 477289) (by norm_num)
theorem B1693589 : Blo 1128631 1693589 := bbase (se 6 (by rfl) ⟨39693, by rfl⟩ : syracuseStep 1693589 = 79387) (by norm_num)
theorem B1693613 : Blo 1128631 1693613 := bbase (se 3 (by rfl) ⟨317552, by rfl⟩ : syracuseStep 1693613 = 635105) (by norm_num)
theorem B1693637 : Blo 1128631 1693637 := bbase (se 4 (by rfl) ⟨158778, by rfl⟩ : syracuseStep 1693637 = 317557) (by norm_num)
theorem B2545613 : Blo 1128631 2545613 := bbase (se 3 (by rfl) ⟨477302, by rfl⟩ : syracuseStep 2545613 = 954605) (by norm_num)
theorem B1693661 : Blo 1128631 1693661 := bbase (se 3 (by rfl) ⟨317561, by rfl⟩ : syracuseStep 1693661 = 635123) (by norm_num)
theorem B1431533 : Blo 1128631 1431533 := bbase (se 3 (by rfl) ⟨268412, by rfl⟩ : syracuseStep 1431533 = 536825) (by norm_num)
theorem B1693685 : Blo 1128631 1693685 := bbase (se 5 (by rfl) ⟨79391, by rfl⟩ : syracuseStep 1693685 = 158783) (by norm_num)
theorem B1693709 : Blo 1128631 1693709 := bbase (se 3 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 1693709 = 635141) (by norm_num)
theorem B21714965 : Blo 1128631 21714965 := bbase (se 6 (by rfl) ⟨508944, by rfl⟩ : syracuseStep 21714965 = 1017889) (by norm_num)
theorem B2545685 : Blo 1128631 2545685 := bbase (se 6 (by rfl) ⟨59664, by rfl⟩ : syracuseStep 2545685 = 119329) (by norm_num)
theorem B1693733 : Blo 1128631 1693733 := bbase (se 4 (by rfl) ⟨158787, by rfl⟩ : syracuseStep 1693733 = 317575) (by norm_num)
theorem B1431589 : Blo 1128631 1431589 := bbase (se 4 (by rfl) ⟨134211, by rfl⟩ : syracuseStep 1431589 = 268423) (by norm_num)
theorem B1693757 : Blo 1128631 1693757 := bbase (se 3 (by rfl) ⟨317579, by rfl⟩ : syracuseStep 1693757 = 635159) (by norm_num)
theorem B1693781 : Blo 1128631 1693781 := bbase (se 8 (by rfl) ⟨9924, by rfl⟩ : syracuseStep 1693781 = 19849) (by norm_num)
theorem B2545757 : Blo 1128631 2545757 := bbase (se 3 (by rfl) ⟨477329, by rfl⟩ : syracuseStep 2545757 = 954659) (by norm_num)
theorem B3922021 : Blo 1128631 3922021 := bbase (se 4 (by rfl) ⟨367689, by rfl⟩ : syracuseStep 3922021 = 735379) (by norm_num)
theorem B1693805 : Blo 1128631 1693805 := bbase (se 3 (by rfl) ⟨317588, by rfl⟩ : syracuseStep 1693805 = 635177) (by norm_num)
theorem B1693829 : Blo 1128631 1693829 := bbase (se 4 (by rfl) ⟨158796, by rfl⟩ : syracuseStep 1693829 = 317593) (by norm_num)
theorem B1431685 : Blo 1128631 1431685 := bbase (se 4 (by rfl) ⟨134220, by rfl⟩ : syracuseStep 1431685 = 268441) (by norm_num)
theorem B1693853 : Blo 1128631 1693853 := bbase (se 3 (by rfl) ⟨317597, by rfl⟩ : syracuseStep 1693853 = 635195) (by norm_num)
theorem B2545829 : Blo 1128631 2545829 := bbase (se 4 (by rfl) ⟨238671, by rfl⟩ : syracuseStep 2545829 = 477343) (by norm_num)
theorem B1693877 : Blo 1128631 1693877 := bbase (se 5 (by rfl) ⟨79400, by rfl⟩ : syracuseStep 1693877 = 158801) (by norm_num)
theorem B1693901 : Blo 1128631 1693901 := bbase (se 3 (by rfl) ⟨317606, by rfl⟩ : syracuseStep 1693901 = 635213) (by norm_num)
theorem B1693925 : Blo 1128631 1693925 := bbase (se 4 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 1693925 = 317611) (by norm_num)
theorem B2545901 : Blo 1128631 2545901 := bbase (se 3 (by rfl) ⟨477356, by rfl⟩ : syracuseStep 2545901 = 954713) (by norm_num)
theorem B1693949 : Blo 1128631 1693949 := bbase (se 3 (by rfl) ⟨317615, by rfl⟩ : syracuseStep 1693949 = 635231) (by norm_num)
theorem B1693973 : Blo 1128631 1693973 := bbase (se 6 (by rfl) ⟨39702, by rfl⟩ : syracuseStep 1693973 = 79405) (by norm_num)
theorem B1693997 : Blo 1128631 1693997 := bbase (se 3 (by rfl) ⟨317624, by rfl⟩ : syracuseStep 1693997 = 635249) (by norm_num)
theorem B2414893 : Blo 1128631 2414893 := bbase (se 3 (by rfl) ⟨452792, by rfl⟩ : syracuseStep 2414893 = 905585) (by norm_num)
theorem B1431857 : Blo 1128631 1431857 := bbase (se 2 (by rfl) ⟨536946, by rfl⟩ : syracuseStep 1431857 = 1073893) (by norm_num)
theorem B2545973 : Blo 1128631 2545973 := bbase (se 5 (by rfl) ⟨119342, by rfl⟩ : syracuseStep 2545973 = 238685) (by norm_num)
theorem B1694021 : Blo 1128631 1694021 := bbase (se 4 (by rfl) ⟨158814, by rfl⟩ : syracuseStep 1694021 = 317629) (by norm_num)
theorem B1530181 : Blo 1128631 1530181 := bbase (se 4 (by rfl) ⟨143454, by rfl⟩ : syracuseStep 1530181 = 286909) (by norm_num)
theorem B1694045 : Blo 1128631 1694045 := bbase (se 3 (by rfl) ⟨317633, by rfl⟩ : syracuseStep 1694045 = 635267) (by norm_num)
theorem B1431913 : Blo 1128631 1431913 := bbase (se 2 (by rfl) ⟨536967, by rfl⟩ : syracuseStep 1431913 = 1073935) (by norm_num)
theorem B1694069 : Blo 1128631 1694069 := bbase (se 5 (by rfl) ⟨79409, by rfl⟩ : syracuseStep 1694069 = 158819) (by norm_num)
theorem B2546045 : Blo 1128631 2546045 := bbase (se 3 (by rfl) ⟨477383, by rfl⟩ : syracuseStep 2546045 = 954767) (by norm_num)
theorem B1694093 : Blo 1128631 1694093 := bbase (se 3 (by rfl) ⟨317642, by rfl⟩ : syracuseStep 1694093 = 635285) (by norm_num)
theorem B1694117 : Blo 1128631 1694117 := bbase (se 4 (by rfl) ⟨158823, by rfl⟩ : syracuseStep 1694117 = 317647) (by norm_num)
theorem B1694141 : Blo 1128631 1694141 := bbase (se 3 (by rfl) ⟨317651, by rfl⟩ : syracuseStep 1694141 = 635303) (by norm_num)
theorem B2546117 : Blo 1128631 2546117 := bbase (se 4 (by rfl) ⟨238698, by rfl⟩ : syracuseStep 2546117 = 477397) (by norm_num)
theorem B1432009 : Blo 1128631 1432009 := bbase (se 2 (by rfl) ⟨537003, by rfl⟩ : syracuseStep 1432009 = 1074007) (by norm_num)
theorem B1694165 : Blo 1128631 1694165 := bbase (se 7 (by rfl) ⟨19853, by rfl⟩ : syracuseStep 1694165 = 39707) (by norm_num)
theorem B1694189 : Blo 1128631 1694189 := bbase (se 3 (by rfl) ⟨317660, by rfl⟩ : syracuseStep 1694189 = 635321) (by norm_num)
theorem B1694213 : Blo 1128631 1694213 := bbase (se 4 (by rfl) ⟨158832, by rfl⟩ : syracuseStep 1694213 = 317665) (by norm_num)
theorem B2546189 : Blo 1128631 2546189 := bbase (se 3 (by rfl) ⟨477410, by rfl⟩ : syracuseStep 2546189 = 954821) (by norm_num)
theorem B1694237 : Blo 1128631 1694237 := bbase (se 3 (by rfl) ⟨317669, by rfl⟩ : syracuseStep 1694237 = 635339) (by norm_num)
theorem B1694261 : Blo 1128631 1694261 := bbase (se 5 (by rfl) ⟨79418, by rfl⟩ : syracuseStep 1694261 = 158837) (by norm_num)
theorem B1694285 : Blo 1128631 1694285 := bbase (se 3 (by rfl) ⟨317678, by rfl⟩ : syracuseStep 1694285 = 635357) (by norm_num)
theorem B2546261 : Blo 1128631 2546261 := bbase (se 8 (by rfl) ⟨14919, by rfl⟩ : syracuseStep 2546261 = 29839) (by norm_num)
theorem B1694309 : Blo 1128631 1694309 := bbase (se 4 (by rfl) ⟨158841, by rfl⟩ : syracuseStep 1694309 = 317683) (by norm_num)
theorem B1432181 : Blo 1128631 1432181 := bbase (se 5 (by rfl) ⟨67133, by rfl⟩ : syracuseStep 1432181 = 134267) (by norm_num)
theorem B1694333 : Blo 1128631 1694333 := bbase (se 3 (by rfl) ⟨317687, by rfl⟩ : syracuseStep 1694333 = 635375) (by norm_num)
theorem B1694357 : Blo 1128631 1694357 := bbase (se 6 (by rfl) ⟨39711, by rfl⟩ : syracuseStep 1694357 = 79423) (by norm_num)
theorem B2546333 : Blo 1128631 2546333 := bbase (se 3 (by rfl) ⟨477437, by rfl⟩ : syracuseStep 2546333 = 954875) (by norm_num)
theorem B1694381 : Blo 1128631 1694381 := bbase (se 3 (by rfl) ⟨317696, by rfl⟩ : syracuseStep 1694381 = 635393) (by norm_num)
theorem B1432237 : Blo 1128631 1432237 := bbase (se 3 (by rfl) ⟨268544, by rfl⟩ : syracuseStep 1432237 = 537089) (by norm_num)
theorem B1694405 : Blo 1128631 1694405 := bbase (se 4 (by rfl) ⟨158850, by rfl⟩ : syracuseStep 1694405 = 317701) (by norm_num)
theorem B1694429 : Blo 1128631 1694429 := bbase (se 3 (by rfl) ⟨317705, by rfl⟩ : syracuseStep 1694429 = 635411) (by norm_num)
theorem B2546405 : Blo 1128631 2546405 := bbase (se 4 (by rfl) ⟨238725, by rfl⟩ : syracuseStep 2546405 = 477451) (by norm_num)
theorem B1694453 : Blo 1128631 1694453 := bbase (se 5 (by rfl) ⟨79427, by rfl⟩ : syracuseStep 1694453 = 158855) (by norm_num)
theorem B5724917 : Blo 1128631 5724917 := bbase (se 5 (by rfl) ⟨268355, by rfl⟩ : syracuseStep 5724917 = 536711) (by norm_num)
theorem B1694477 : Blo 1128631 1694477 := bbase (se 3 (by rfl) ⟨317714, by rfl⟩ : syracuseStep 1694477 = 635429) (by norm_num)
theorem B1432333 : Blo 1128631 1432333 := bbase (se 3 (by rfl) ⟨268562, by rfl⟩ : syracuseStep 1432333 = 537125) (by norm_num)
theorem B1694501 : Blo 1128631 1694501 := bbase (se 4 (by rfl) ⟨158859, by rfl⟩ : syracuseStep 1694501 = 317719) (by norm_num)
theorem B2546477 : Blo 1128631 2546477 := bbase (se 3 (by rfl) ⟨477464, by rfl⟩ : syracuseStep 2546477 = 954929) (by norm_num)
theorem B1694525 : Blo 1128631 1694525 := bbase (se 3 (by rfl) ⟨317723, by rfl⟩ : syracuseStep 1694525 = 635447) (by norm_num)
theorem B1694549 : Blo 1128631 1694549 := bbase (se 9 (by rfl) ⟨4964, by rfl⟩ : syracuseStep 1694549 = 9929) (by norm_num)
theorem B1694573 : Blo 1128631 1694573 := bbase (se 3 (by rfl) ⟨317732, by rfl⟩ : syracuseStep 1694573 = 635465) (by norm_num)
theorem B2546549 : Blo 1128631 2546549 := bbase (se 5 (by rfl) ⟨119369, by rfl⟩ : syracuseStep 2546549 = 238739) (by norm_num)
theorem B1694597 : Blo 1128631 1694597 := bbase (se 4 (by rfl) ⟨158868, by rfl⟩ : syracuseStep 1694597 = 317737) (by norm_num)
theorem B1694621 : Blo 1128631 1694621 := bbase (se 3 (by rfl) ⟨317741, by rfl⟩ : syracuseStep 1694621 = 635483) (by norm_num)
theorem B1694645 : Blo 1128631 1694645 := bbase (se 5 (by rfl) ⟨79436, by rfl⟩ : syracuseStep 1694645 = 158873) (by norm_num)
theorem B1432505 : Blo 1128631 1432505 := bbase (se 2 (by rfl) ⟨537189, by rfl⟩ : syracuseStep 1432505 = 1074379) (by norm_num)
theorem B2546621 : Blo 1128631 2546621 := bbase (se 3 (by rfl) ⟨477491, by rfl⟩ : syracuseStep 2546621 = 954983) (by norm_num)
theorem B1694669 : Blo 1128631 1694669 := bbase (se 3 (by rfl) ⟨317750, by rfl⟩ : syracuseStep 1694669 = 635501) (by norm_num)
theorem B1694693 : Blo 1128631 1694693 := bbase (se 4 (by rfl) ⟨158877, by rfl⟩ : syracuseStep 1694693 = 317755) (by norm_num)
theorem B1432561 : Blo 1128631 1432561 := bbase (se 2 (by rfl) ⟨537210, by rfl⟩ : syracuseStep 1432561 = 1074421) (by norm_num)
theorem B1694717 : Blo 1128631 1694717 := bbase (se 3 (by rfl) ⟨317759, by rfl⟩ : syracuseStep 1694717 = 635519) (by norm_num)
theorem B2546693 : Blo 1128631 2546693 := bbase (se 4 (by rfl) ⟨238752, by rfl⟩ : syracuseStep 2546693 = 477505) (by norm_num)
theorem B1694741 : Blo 1128631 1694741 := bbase (se 6 (by rfl) ⟨39720, by rfl⟩ : syracuseStep 1694741 = 79441) (by norm_num)
theorem B1694765 : Blo 1128631 1694765 := bbase (se 3 (by rfl) ⟨317768, by rfl⟩ : syracuseStep 1694765 = 635537) (by norm_num)
theorem B9428021 : Blo 1128631 9428021 := bbase (se 5 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 9428021 = 883877) (by norm_num)
theorem B1694789 : Blo 1128631 1694789 := bbase (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) (by norm_num)
theorem B2546765 : Blo 1128631 2546765 := bbase (se 3 (by rfl) ⟨477518, by rfl⟩ : syracuseStep 2546765 = 955037) (by norm_num)
theorem B1432657 : Blo 1128631 1432657 := bbase (se 2 (by rfl) ⟨537246, by rfl⟩ : syracuseStep 1432657 = 1074493) (by norm_num)
theorem B1694813 : Blo 1128631 1694813 := bbase (se 3 (by rfl) ⟨317777, by rfl⟩ : syracuseStep 1694813 = 635555) (by norm_num)
theorem B1694837 : Blo 1128631 1694837 := bbase (se 5 (by rfl) ⟨79445, by rfl⟩ : syracuseStep 1694837 = 158891) (by norm_num)
theorem B1694861 : Blo 1128631 1694861 := bbase (se 3 (by rfl) ⟨317786, by rfl⟩ : syracuseStep 1694861 = 635573) (by norm_num)
theorem B2546837 : Blo 1128631 2546837 := bbase (se 6 (by rfl) ⟨59691, by rfl⟩ : syracuseStep 2546837 = 119383) (by norm_num)
theorem B1694885 : Blo 1128631 1694885 := bbase (se 4 (by rfl) ⟨158895, by rfl⟩ : syracuseStep 1694885 = 317791) (by norm_num)
theorem B2415781 : Blo 1128631 2415781 := bbase (se 4 (by rfl) ⟨226479, by rfl⟩ : syracuseStep 2415781 = 452959) (by norm_num)
theorem B1694909 : Blo 1128631 1694909 := bbase (se 3 (by rfl) ⟨317795, by rfl⟩ : syracuseStep 1694909 = 635591) (by norm_num)
theorem B1694933 : Blo 1128631 1694933 := bbase (se 7 (by rfl) ⟨19862, by rfl⟩ : syracuseStep 1694933 = 39725) (by norm_num)
theorem B2546909 : Blo 1128631 2546909 := bbase (se 3 (by rfl) ⟨477545, by rfl⟩ : syracuseStep 2546909 = 955091) (by norm_num)
theorem B1694957 : Blo 1128631 1694957 := bbase (se 3 (by rfl) ⟨317804, by rfl⟩ : syracuseStep 1694957 = 635609) (by norm_num)
theorem B1432829 : Blo 1128631 1432829 := bbase (se 3 (by rfl) ⟨268655, by rfl⟩ : syracuseStep 1432829 = 537311) (by norm_num)
theorem B1694981 : Blo 1128631 1694981 := bbase (se 4 (by rfl) ⟨158904, by rfl⟩ : syracuseStep 1694981 = 317809) (by norm_num)
theorem B1695005 : Blo 1128631 1695005 := bbase (se 3 (by rfl) ⟨317813, by rfl⟩ : syracuseStep 1695005 = 635627) (by norm_num)
theorem B2415901 : Blo 1128631 2415901 := bbase (se 3 (by rfl) ⟨452981, by rfl⟩ : syracuseStep 2415901 = 905963) (by norm_num)
theorem B2546981 : Blo 1128631 2546981 := bbase (se 4 (by rfl) ⟨238779, by rfl⟩ : syracuseStep 2546981 = 477559) (by norm_num)
theorem B1695029 : Blo 1128631 1695029 := bbase (se 5 (by rfl) ⟨79454, by rfl⟩ : syracuseStep 1695029 = 158909) (by norm_num)
theorem B1432885 : Blo 1128631 1432885 := bbase (se 5 (by rfl) ⟨67166, by rfl⟩ : syracuseStep 1432885 = 134333) (by norm_num)
theorem B1695053 : Blo 1128631 1695053 := bbase (se 3 (by rfl) ⟨317822, by rfl⟩ : syracuseStep 1695053 = 635645) (by norm_num)
theorem B41278805 : Blo 1128631 41278805 := bbase (se 11 (by rfl) ⟨30233, by rfl⟩ : syracuseStep 41278805 = 60467) (by norm_num)
theorem B1695077 : Blo 1128631 1695077 := bbase (se 4 (by rfl) ⟨158913, by rfl⟩ : syracuseStep 1695077 = 317827) (by norm_num)
theorem B2547053 : Blo 1128631 2547053 := bbase (se 3 (by rfl) ⟨477572, by rfl⟩ : syracuseStep 2547053 = 955145) (by norm_num)
theorem B1695101 : Blo 1128631 1695101 := bbase (se 3 (by rfl) ⟨317831, by rfl⟩ : syracuseStep 1695101 = 635663) (by norm_num)
theorem B2579845 : Blo 1128631 2579845 := bbase (se 4 (by rfl) ⟨241860, by rfl⟩ : syracuseStep 2579845 = 483721) (by norm_num)
theorem B1695125 : Blo 1128631 1695125 := bbase (se 6 (by rfl) ⟨39729, by rfl⟩ : syracuseStep 1695125 = 79459) (by norm_num)
theorem B1432981 : Blo 1128631 1432981 := bbase (se 6 (by rfl) ⟨33585, by rfl⟩ : syracuseStep 1432981 = 67171) (by norm_num)
theorem B1695149 : Blo 1128631 1695149 := bbase (se 3 (by rfl) ⟨317840, by rfl⟩ : syracuseStep 1695149 = 635681) (by norm_num)
theorem B2547125 : Blo 1128631 2547125 := bbase (se 5 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 2547125 = 238793) (by norm_num)
theorem B1695173 : Blo 1128631 1695173 := bbase (se 4 (by rfl) ⟨158922, by rfl⟩ : syracuseStep 1695173 = 317845) (by norm_num)
theorem B1695197 : Blo 1128631 1695197 := bbase (se 3 (by rfl) ⟨317849, by rfl⟩ : syracuseStep 1695197 = 635699) (by norm_num)
theorem B1695221 : Blo 1128631 1695221 := bbase (se 5 (by rfl) ⟨79463, by rfl⟩ : syracuseStep 1695221 = 158927) (by norm_num)
theorem B2547197 : Blo 1128631 2547197 := bbase (se 3 (by rfl) ⟨477599, by rfl⟩ : syracuseStep 2547197 = 955199) (by norm_num)
theorem B1695245 : Blo 1128631 1695245 := bbase (se 3 (by rfl) ⟨317858, by rfl⟩ : syracuseStep 1695245 = 635717) (by norm_num)
theorem B2416157 : Blo 1128631 2416157 := bbase (se 3 (by rfl) ⟨453029, by rfl⟩ : syracuseStep 2416157 = 906059) (by norm_num)
theorem B1695269 : Blo 1128631 1695269 := bbase (se 4 (by rfl) ⟨158931, by rfl⟩ : syracuseStep 1695269 = 317863) (by norm_num)
theorem B1695293 : Blo 1128631 1695293 := bbase (se 3 (by rfl) ⟨317867, by rfl⟩ : syracuseStep 1695293 = 635735) (by norm_num)
theorem B1433153 : Blo 1128631 1433153 := bbase (se 2 (by rfl) ⟨537432, by rfl⟩ : syracuseStep 1433153 = 1074865) (by norm_num)
theorem B2547269 : Blo 1128631 2547269 := bbase (se 4 (by rfl) ⟨238806, by rfl⟩ : syracuseStep 2547269 = 477613) (by norm_num)
theorem B1695317 : Blo 1128631 1695317 := bbase (se 8 (by rfl) ⟨9933, by rfl⟩ : syracuseStep 1695317 = 19867) (by norm_num)
theorem B1695341 : Blo 1128631 1695341 := bbase (se 3 (by rfl) ⟨317876, by rfl⟩ : syracuseStep 1695341 = 635753) (by norm_num)
theorem B1433209 : Blo 1128631 1433209 := bbase (se 2 (by rfl) ⟨537453, by rfl⟩ : syracuseStep 1433209 = 1074907) (by norm_num)
theorem B1695365 : Blo 1128631 1695365 := bbase (se 4 (by rfl) ⟨158940, by rfl⟩ : syracuseStep 1695365 = 317881) (by norm_num)
theorem B2547341 : Blo 1128631 2547341 := bbase (se 3 (by rfl) ⟨477626, by rfl⟩ : syracuseStep 2547341 = 955253) (by norm_num)
theorem B1695389 : Blo 1128631 1695389 := bbase (se 3 (by rfl) ⟨317885, by rfl⟩ : syracuseStep 1695389 = 635771) (by norm_num)
theorem B1695413 : Blo 1128631 1695413 := bbase (se 5 (by rfl) ⟨79472, by rfl⟩ : syracuseStep 1695413 = 158945) (by norm_num)
theorem B1695437 : Blo 1128631 1695437 := bbase (se 3 (by rfl) ⟨317894, by rfl⟩ : syracuseStep 1695437 = 635789) (by norm_num)
theorem B2547413 : Blo 1128631 2547413 := bbase (se 7 (by rfl) ⟨29852, by rfl⟩ : syracuseStep 2547413 = 59705) (by norm_num)
theorem B1433305 : Blo 1128631 1433305 := bbase (se 2 (by rfl) ⟨537489, by rfl⟩ : syracuseStep 1433305 = 1074979) (by norm_num)
theorem B1695461 : Blo 1128631 1695461 := bbase (se 4 (by rfl) ⟨158949, by rfl⟩ : syracuseStep 1695461 = 317899) (by norm_num)
theorem B1695485 : Blo 1128631 1695485 := bbase (se 3 (by rfl) ⟨317903, by rfl⟩ : syracuseStep 1695485 = 635807) (by norm_num)
theorem B1695509 : Blo 1128631 1695509 := bbase (se 6 (by rfl) ⟨39738, by rfl⟩ : syracuseStep 1695509 = 79477) (by norm_num)
theorem B2547485 : Blo 1128631 2547485 := bbase (se 3 (by rfl) ⟨477653, by rfl⟩ : syracuseStep 2547485 = 955307) (by norm_num)
theorem B1695533 : Blo 1128631 1695533 := bbase (se 3 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 1695533 = 635825) (by norm_num)
theorem B1695557 : Blo 1128631 1695557 := bbase (se 4 (by rfl) ⟨158958, by rfl⟩ : syracuseStep 1695557 = 317917) (by norm_num)
theorem B3923797 : Blo 1128631 3923797 := bbase (se 9 (by rfl) ⟨11495, by rfl⟩ : syracuseStep 3923797 = 22991) (by norm_num)
theorem B1695581 : Blo 1128631 1695581 := bbase (se 3 (by rfl) ⟨317921, by rfl⟩ : syracuseStep 1695581 = 635843) (by norm_num)
theorem B2547557 : Blo 1128631 2547557 := bbase (se 4 (by rfl) ⟨238833, by rfl⟩ : syracuseStep 2547557 = 477667) (by norm_num)
theorem B1695605 : Blo 1128631 1695605 := bbase (se 5 (by rfl) ⟨79481, by rfl⟩ : syracuseStep 1695605 = 158963) (by norm_num)
theorem B1433477 : Blo 1128631 1433477 := bbase (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) (by norm_num)
theorem B1695629 : Blo 1128631 1695629 := bbase (se 3 (by rfl) ⟨317930, by rfl⟩ : syracuseStep 1695629 = 635861) (by norm_num)
theorem B1695653 : Blo 1128631 1695653 := bbase (se 4 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 1695653 = 317935) (by norm_num)
theorem B2547629 : Blo 1128631 2547629 := bbase (se 3 (by rfl) ⟨477680, by rfl⟩ : syracuseStep 2547629 = 955361) (by norm_num)
theorem B1695677 : Blo 1128631 1695677 := bbase (se 3 (by rfl) ⟨317939, by rfl⟩ : syracuseStep 1695677 = 635879) (by norm_num)
theorem B1695701 : Blo 1128631 1695701 := bbase (se 7 (by rfl) ⟨19871, by rfl⟩ : syracuseStep 1695701 = 39743) (by norm_num)
theorem B1269733 : Blo 1128631 1269733 := bbase (se 4 (by rfl) ⟨119037, by rfl⟩ : syracuseStep 1269733 = 238075) (by norm_num)
theorem B1695725 : Blo 1128631 1695725 := bbase (se 3 (by rfl) ⟨317948, by rfl⟩ : syracuseStep 1695725 = 635897) (by norm_num)
theorem B2547701 : Blo 1128631 2547701 := bbase (se 5 (by rfl) ⟨119423, by rfl⟩ : syracuseStep 2547701 = 238847) (by norm_num)
theorem B1695749 : Blo 1128631 1695749 := bbase (se 4 (by rfl) ⟨158976, by rfl⟩ : syracuseStep 1695749 = 317953) (by norm_num)
theorem B5726213 : Blo 1128631 5726213 := bbase (se 4 (by rfl) ⟨536832, by rfl⟩ : syracuseStep 5726213 = 1073665) (by norm_num)
theorem B1269769 : Blo 1128631 1269769 := bbase (se 2 (by rfl) ⟨476163, by rfl⟩ : syracuseStep 1269769 = 952327) (by norm_num)
theorem B1695773 : Blo 1128631 1695773 := bbase (se 3 (by rfl) ⟨317957, by rfl⟩ : syracuseStep 1695773 = 635915) (by norm_num)
theorem B1269805 : Blo 1128631 1269805 := bbase (se 3 (by rfl) ⟨238088, by rfl⟩ : syracuseStep 1269805 = 476177) (by norm_num)
theorem B1695797 : Blo 1128631 1695797 := bbase (se 5 (by rfl) ⟨79490, by rfl⟩ : syracuseStep 1695797 = 158981) (by norm_num)
theorem B2547773 : Blo 1128631 2547773 := bbase (se 3 (by rfl) ⟨477707, by rfl⟩ : syracuseStep 2547773 = 955415) (by norm_num)
theorem B1695821 : Blo 1128631 1695821 := bbase (se 3 (by rfl) ⟨317966, by rfl⟩ : syracuseStep 1695821 = 635933) (by norm_num)
theorem B1269841 : Blo 1128631 1269841 := bbase (se 2 (by rfl) ⟨476190, by rfl⟩ : syracuseStep 1269841 = 952381) (by norm_num)
theorem B1695845 : Blo 1128631 1695845 := bbase (se 4 (by rfl) ⟨158985, by rfl⟩ : syracuseStep 1695845 = 317971) (by norm_num)
theorem B1269877 : Blo 1128631 1269877 := bbase (se 5 (by rfl) ⟨59525, by rfl⟩ : syracuseStep 1269877 = 119051) (by norm_num)
theorem B1695869 : Blo 1128631 1695869 := bbase (se 3 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 1695869 = 635951) (by norm_num)
theorem B2547845 : Blo 1128631 2547845 := bbase (se 4 (by rfl) ⟨238860, by rfl⟩ : syracuseStep 2547845 = 477721) (by norm_num)
theorem B1695893 : Blo 1128631 1695893 := bbase (se 6 (by rfl) ⟨39747, by rfl⟩ : syracuseStep 1695893 = 79495) (by norm_num)
theorem B1269913 : Blo 1128631 1269913 := bbase (se 2 (by rfl) ⟨476217, by rfl⟩ : syracuseStep 1269913 = 952435) (by norm_num)
theorem B1695917 : Blo 1128631 1695917 := bbase (se 3 (by rfl) ⟨317984, by rfl⟩ : syracuseStep 1695917 = 635969) (by norm_num)
theorem B1269949 : Blo 1128631 1269949 := bbase (se 3 (by rfl) ⟨238115, by rfl⟩ : syracuseStep 1269949 = 476231) (by norm_num)
theorem B1695941 : Blo 1128631 1695941 := bbase (se 4 (by rfl) ⟨158994, by rfl⟩ : syracuseStep 1695941 = 317989) (by norm_num)
theorem B2547917 : Blo 1128631 2547917 := bbase (se 3 (by rfl) ⟨477734, by rfl⟩ : syracuseStep 2547917 = 955469) (by norm_num)
theorem B1695965 : Blo 1128631 1695965 := bbase (se 3 (by rfl) ⟨317993, by rfl⟩ : syracuseStep 1695965 = 635987) (by norm_num)
theorem B1269985 : Blo 1128631 1269985 := bbase (se 2 (by rfl) ⟨476244, by rfl⟩ : syracuseStep 1269985 = 952489) (by norm_num)
theorem B1695989 : Blo 1128631 1695989 := bbase (se 5 (by rfl) ⟨79499, by rfl⟩ : syracuseStep 1695989 = 158999) (by norm_num)
theorem B1270021 : Blo 1128631 1270021 := bbase (se 4 (by rfl) ⟨119064, by rfl⟩ : syracuseStep 1270021 = 238129) (by norm_num)
theorem B1696013 : Blo 1128631 1696013 := bbase (se 3 (by rfl) ⟨318002, by rfl⟩ : syracuseStep 1696013 = 636005) (by norm_num)
theorem B2547989 : Blo 1128631 2547989 := bbase (se 6 (by rfl) ⟨59718, by rfl⟩ : syracuseStep 2547989 = 119437) (by norm_num)
theorem B1696037 : Blo 1128631 1696037 := bbase (se 4 (by rfl) ⟨159003, by rfl⟩ : syracuseStep 1696037 = 318007) (by norm_num)
theorem B1270057 : Blo 1128631 1270057 := bbase (se 2 (by rfl) ⟨476271, by rfl⟩ : syracuseStep 1270057 = 952543) (by norm_num)
theorem B1696061 : Blo 1128631 1696061 := bbase (se 3 (by rfl) ⟨318011, by rfl⟩ : syracuseStep 1696061 = 636023) (by norm_num)
theorem B1270093 : Blo 1128631 1270093 := bbase (se 3 (by rfl) ⟨238142, by rfl⟩ : syracuseStep 1270093 = 476285) (by norm_num)
theorem B4350293 : Blo 1128631 4350293 := bbase (se 10 (by rfl) ⟨6372, by rfl⟩ : syracuseStep 4350293 = 12745) (by norm_num)
theorem B1696085 : Blo 1128631 1696085 := bbase (se 10 (by rfl) ⟨2484, by rfl⟩ : syracuseStep 1696085 = 4969) (by norm_num)
theorem B2548061 : Blo 1128631 2548061 := bbase (se 3 (by rfl) ⟨477761, by rfl⟩ : syracuseStep 2548061 = 955523) (by norm_num)
theorem B1696109 : Blo 1128631 1696109 := bbase (se 3 (by rfl) ⟨318020, by rfl⟩ : syracuseStep 1696109 = 636041) (by norm_num)
theorem B1270129 : Blo 1128631 1270129 := bbase (se 2 (by rfl) ⟨476298, by rfl⟩ : syracuseStep 1270129 = 952597) (by norm_num)
theorem B1696133 : Blo 1128631 1696133 := bbase (se 4 (by rfl) ⟨159012, by rfl⟩ : syracuseStep 1696133 = 318025) (by norm_num)
theorem B1270165 : Blo 1128631 1270165 := bbase (se 6 (by rfl) ⟨29769, by rfl⟩ : syracuseStep 1270165 = 59539) (by norm_num)
theorem B2417045 : Blo 1128631 2417045 := bbase (se 6 (by rfl) ⟨56649, by rfl⟩ : syracuseStep 2417045 = 113299) (by norm_num)
theorem B1696157 : Blo 1128631 1696157 := bbase (se 3 (by rfl) ⟨318029, by rfl⟩ : syracuseStep 1696157 = 636059) (by norm_num)
theorem B2548133 : Blo 1128631 2548133 := bbase (se 4 (by rfl) ⟨238887, by rfl⟩ : syracuseStep 2548133 = 477775) (by norm_num)
theorem B1696181 : Blo 1128631 1696181 := bbase (se 5 (by rfl) ⟨79508, by rfl⟩ : syracuseStep 1696181 = 159017) (by norm_num)
theorem B1270201 : Blo 1128631 1270201 := bbase (se 2 (by rfl) ⟨476325, by rfl⟩ : syracuseStep 1270201 = 952651) (by norm_num)
theorem B1696205 : Blo 1128631 1696205 := bbase (se 3 (by rfl) ⟨318038, by rfl⟩ : syracuseStep 1696205 = 636077) (by norm_num)
theorem B1270237 : Blo 1128631 1270237 := bbase (se 3 (by rfl) ⟨238169, by rfl⟩ : syracuseStep 1270237 = 476339) (by norm_num)
theorem B1696229 : Blo 1128631 1696229 := bbase (se 4 (by rfl) ⟨159021, by rfl⟩ : syracuseStep 1696229 = 318043) (by norm_num)
theorem B2548205 : Blo 1128631 2548205 := bbase (se 3 (by rfl) ⟨477788, by rfl⟩ : syracuseStep 2548205 = 955577) (by norm_num)
theorem B1696253 : Blo 1128631 1696253 := bbase (se 3 (by rfl) ⟨318047, by rfl⟩ : syracuseStep 1696253 = 636095) (by norm_num)
theorem B1270273 : Blo 1128631 1270273 := bbase (se 2 (by rfl) ⟨476352, by rfl⟩ : syracuseStep 1270273 = 952705) (by norm_num)
theorem B1696277 : Blo 1128631 1696277 := bbase (se 6 (by rfl) ⟨39756, by rfl⟩ : syracuseStep 1696277 = 79513) (by norm_num)
theorem B2581021 : Blo 1128631 2581021 := bbase (se 3 (by rfl) ⟨483941, by rfl⟩ : syracuseStep 2581021 = 967883) (by norm_num)
theorem B1270309 : Blo 1128631 1270309 := bbase (se 4 (by rfl) ⟨119091, by rfl⟩ : syracuseStep 1270309 = 238183) (by norm_num)
theorem B1696301 : Blo 1128631 1696301 := bbase (se 3 (by rfl) ⟨318056, by rfl⟩ : syracuseStep 1696301 = 636113) (by norm_num)
theorem B2548277 : Blo 1128631 2548277 := bbase (se 5 (by rfl) ⟨119450, by rfl⟩ : syracuseStep 2548277 = 238901) (by norm_num)
theorem B1696325 : Blo 1128631 1696325 := bbase (se 4 (by rfl) ⟨159030, by rfl⟩ : syracuseStep 1696325 = 318061) (by norm_num)
theorem B1270345 : Blo 1128631 1270345 := bbase (se 2 (by rfl) ⟨476379, by rfl⟩ : syracuseStep 1270345 = 952759) (by norm_num)
theorem B1696349 : Blo 1128631 1696349 := bbase (se 3 (by rfl) ⟨318065, by rfl⟩ : syracuseStep 1696349 = 636131) (by norm_num)
theorem B1270381 : Blo 1128631 1270381 := bbase (se 3 (by rfl) ⟨238196, by rfl⟩ : syracuseStep 1270381 = 476393) (by norm_num)
theorem B1696373 : Blo 1128631 1696373 := bbase (se 5 (by rfl) ⟨79517, by rfl⟩ : syracuseStep 1696373 = 159035) (by norm_num)
theorem B2548349 : Blo 1128631 2548349 := bbase (se 3 (by rfl) ⟨477815, by rfl⟩ : syracuseStep 2548349 = 955631) (by norm_num)
theorem B2417285 : Blo 1128631 2417285 := bbase (se 4 (by rfl) ⟨226620, by rfl⟩ : syracuseStep 2417285 = 453241) (by norm_num)
theorem B1696397 : Blo 1128631 1696397 := bbase (se 3 (by rfl) ⟨318074, by rfl⟩ : syracuseStep 1696397 = 636149) (by norm_num)
theorem B1270417 : Blo 1128631 1270417 := bbase (se 2 (by rfl) ⟨476406, by rfl⟩ : syracuseStep 1270417 = 952813) (by norm_num)
theorem B1696421 : Blo 1128631 1696421 := bbase (se 4 (by rfl) ⟨159039, by rfl⟩ : syracuseStep 1696421 = 318079) (by norm_num)
theorem B1270453 : Blo 1128631 1270453 := bbase (se 5 (by rfl) ⟨59552, by rfl⟩ : syracuseStep 1270453 = 119105) (by norm_num)
theorem B1696445 : Blo 1128631 1696445 := bbase (se 3 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 1696445 = 636167) (by norm_num)
theorem B2548421 : Blo 1128631 2548421 := bbase (se 4 (by rfl) ⟨238914, by rfl⟩ : syracuseStep 2548421 = 477829) (by norm_num)
theorem B1696469 : Blo 1128631 1696469 := bbase (se 7 (by rfl) ⟨19880, by rfl⟩ : syracuseStep 1696469 = 39761) (by norm_num)
theorem B1270489 : Blo 1128631 1270489 := bbase (se 2 (by rfl) ⟨476433, by rfl⟩ : syracuseStep 1270489 = 952867) (by norm_num)
theorem B1696493 : Blo 1128631 1696493 := bbase (se 3 (by rfl) ⟨318092, by rfl⟩ : syracuseStep 1696493 = 636185) (by norm_num)
theorem B1270525 : Blo 1128631 1270525 := bbase (se 3 (by rfl) ⟨238223, by rfl⟩ : syracuseStep 1270525 = 476447) (by norm_num)
theorem B2712325 : Blo 1128631 2712325 := bbase (se 4 (by rfl) ⟨254280, by rfl⟩ : syracuseStep 2712325 = 508561) (by norm_num)
theorem B1696517 : Blo 1128631 1696517 := bbase (se 4 (by rfl) ⟨159048, by rfl⟩ : syracuseStep 1696517 = 318097) (by norm_num)
theorem B1696541 : Blo 1128631 1696541 := bbase (se 3 (by rfl) ⟨318101, by rfl⟩ : syracuseStep 1696541 = 636203) (by norm_num)
theorem B1270561 : Blo 1128631 1270561 := bbase (se 2 (by rfl) ⟨476460, by rfl⟩ : syracuseStep 1270561 = 952921) (by norm_num)
theorem B1696565 : Blo 1128631 1696565 := bbase (se 5 (by rfl) ⟨79526, by rfl⟩ : syracuseStep 1696565 = 159053) (by norm_num)
theorem B1270597 : Blo 1128631 1270597 := bbase (se 4 (by rfl) ⟨119118, by rfl⟩ : syracuseStep 1270597 = 238237) (by norm_num)
theorem B1696589 : Blo 1128631 1696589 := bbase (se 3 (by rfl) ⟨318110, by rfl⟩ : syracuseStep 1696589 = 636221) (by norm_num)
theorem B23192405 : Blo 1128631 23192405 := bbase (se 9 (by rfl) ⟨67946, by rfl⟩ : syracuseStep 23192405 = 135893) (by norm_num)
theorem B1696613 : Blo 1128631 1696613 := bbase (se 4 (by rfl) ⟨159057, by rfl⟩ : syracuseStep 1696613 = 318115) (by norm_num)
theorem B1270633 : Blo 1128631 1270633 := bbase (se 2 (by rfl) ⟨476487, by rfl⟩ : syracuseStep 1270633 = 952975) (by norm_num)
theorem B1696637 : Blo 1128631 1696637 := bbase (se 3 (by rfl) ⟨318119, by rfl⟩ : syracuseStep 1696637 = 636239) (by norm_num)
theorem B1270669 : Blo 1128631 1270669 := bbase (se 3 (by rfl) ⟨238250, by rfl⟩ : syracuseStep 1270669 = 476501) (by norm_num)
theorem B1696661 : Blo 1128631 1696661 := bbase (se 6 (by rfl) ⟨39765, by rfl⟩ : syracuseStep 1696661 = 79531) (by norm_num)
theorem B1696685 : Blo 1128631 1696685 := bbase (se 3 (by rfl) ⟨318128, by rfl⟩ : syracuseStep 1696685 = 636257) (by norm_num)
theorem B1270705 : Blo 1128631 1270705 := bbase (se 2 (by rfl) ⟨476514, by rfl⟩ : syracuseStep 1270705 = 953029) (by norm_num)
theorem B1696709 : Blo 1128631 1696709 := bbase (se 4 (by rfl) ⟨159066, by rfl⟩ : syracuseStep 1696709 = 318133) (by norm_num)
theorem B1270741 : Blo 1128631 1270741 := bbase (se 7 (by rfl) ⟨14891, by rfl⟩ : syracuseStep 1270741 = 29783) (by norm_num)
theorem B1696733 : Blo 1128631 1696733 := bbase (se 3 (by rfl) ⟨318137, by rfl⟩ : syracuseStep 1696733 = 636275) (by norm_num)
theorem B1696757 : Blo 1128631 1696757 := bbase (se 5 (by rfl) ⟨79535, by rfl⟩ : syracuseStep 1696757 = 159071) (by norm_num)
theorem B1270777 : Blo 1128631 1270777 := bbase (se 2 (by rfl) ⟨476541, by rfl⟩ : syracuseStep 1270777 = 953083) (by norm_num)
theorem B1696781 : Blo 1128631 1696781 := bbase (se 3 (by rfl) ⟨318146, by rfl⟩ : syracuseStep 1696781 = 636293) (by norm_num)
theorem B1270813 : Blo 1128631 1270813 := bbase (se 3 (by rfl) ⟨238277, by rfl⟩ : syracuseStep 1270813 = 476555) (by norm_num)
theorem B1205285 : Blo 1128631 1205285 := bbase (se 4 (by rfl) ⟨112995, by rfl⟩ : syracuseStep 1205285 = 225991) (by norm_num)
theorem B1696805 : Blo 1128631 1696805 := bbase (se 4 (by rfl) ⟨159075, by rfl⟩ : syracuseStep 1696805 = 318151) (by norm_num)
theorem B1696829 : Blo 1128631 1696829 := bbase (se 3 (by rfl) ⟨318155, by rfl⟩ : syracuseStep 1696829 = 636311) (by norm_num)
theorem B1270849 : Blo 1128631 1270849 := bbase (se 2 (by rfl) ⟨476568, by rfl⟩ : syracuseStep 1270849 = 953137) (by norm_num)
theorem B1696853 : Blo 1128631 1696853 := bbase (se 8 (by rfl) ⟨9942, by rfl⟩ : syracuseStep 1696853 = 19885) (by norm_num)
theorem B1270885 : Blo 1128631 1270885 := bbase (se 4 (by rfl) ⟨119145, by rfl⟩ : syracuseStep 1270885 = 238291) (by norm_num)
theorem B1696877 : Blo 1128631 1696877 := bbase (se 3 (by rfl) ⟨318164, by rfl⟩ : syracuseStep 1696877 = 636329) (by norm_num)
theorem B2417789 : Blo 1128631 2417789 := bbase (se 3 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 2417789 = 906671) (by norm_num)
theorem B1696901 : Blo 1128631 1696901 := bbase (se 4 (by rfl) ⟨159084, by rfl⟩ : syracuseStep 1696901 = 318169) (by norm_num)
theorem B2417797 : Blo 1128631 2417797 := bbase (se 4 (by rfl) ⟨226668, by rfl⟩ : syracuseStep 2417797 = 453337) (by norm_num)
theorem B1270921 : Blo 1128631 1270921 := bbase (se 2 (by rfl) ⟨476595, by rfl⟩ : syracuseStep 1270921 = 953191) (by norm_num)
theorem B1696925 : Blo 1128631 1696925 := bbase (se 3 (by rfl) ⟨318173, by rfl⟩ : syracuseStep 1696925 = 636347) (by norm_num)
theorem B1270957 : Blo 1128631 1270957 := bbase (se 3 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 1270957 = 476609) (by norm_num)
theorem B1696949 : Blo 1128631 1696949 := bbase (se 5 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 1696949 = 159089) (by norm_num)
theorem B1696973 : Blo 1128631 1696973 := bbase (se 3 (by rfl) ⟨318182, by rfl⟩ : syracuseStep 1696973 = 636365) (by norm_num)
theorem B1270993 : Blo 1128631 1270993 := bbase (se 2 (by rfl) ⟨476622, by rfl⟩ : syracuseStep 1270993 = 953245) (by norm_num)
theorem B4285669 : Blo 1128631 4285669 := bbase (se 4 (by rfl) ⟨401781, by rfl⟩ : syracuseStep 4285669 = 803563) (by norm_num)
theorem B1696997 : Blo 1128631 1696997 := bbase (se 4 (by rfl) ⟨159093, by rfl⟩ : syracuseStep 1696997 = 318187) (by norm_num)
theorem B1271029 : Blo 1128631 1271029 := bbase (se 5 (by rfl) ⟨59579, by rfl⟩ : syracuseStep 1271029 = 119159) (by norm_num)
theorem B1697021 : Blo 1128631 1697021 := bbase (se 3 (by rfl) ⟨318191, by rfl⟩ : syracuseStep 1697021 = 636383) (by norm_num)
theorem B5727509 : Blo 1128631 5727509 := bbase (se 6 (by rfl) ⟨134238, by rfl⟩ : syracuseStep 5727509 = 268477) (by norm_num)
theorem B1697045 : Blo 1128631 1697045 := bbase (se 6 (by rfl) ⟨39774, by rfl⟩ : syracuseStep 1697045 = 79549) (by norm_num)
theorem B1271065 : Blo 1128631 1271065 := bbase (se 2 (by rfl) ⟨476649, by rfl⟩ : syracuseStep 1271065 = 953299) (by norm_num)
theorem B1205533 : Blo 1128631 1205533 := bbase (se 3 (by rfl) ⟨226037, by rfl⟩ : syracuseStep 1205533 = 452075) (by norm_num)
theorem B1697069 : Blo 1128631 1697069 := bbase (se 3 (by rfl) ⟨318200, by rfl⟩ : syracuseStep 1697069 = 636401) (by norm_num)
theorem B1271101 : Blo 1128631 1271101 := bbase (se 3 (by rfl) ⟨238331, by rfl⟩ : syracuseStep 1271101 = 476663) (by norm_num)
theorem B5432645 : Blo 1128631 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B1697093 : Blo 1128631 1697093 := bbase (se 4 (by rfl) ⟨159102, by rfl⟩ : syracuseStep 1697093 = 318205) (by norm_num)
theorem B1697117 : Blo 1128631 1697117 := bbase (se 3 (by rfl) ⟨318209, by rfl⟩ : syracuseStep 1697117 = 636419) (by norm_num)
theorem B1271137 : Blo 1128631 1271137 := bbase (se 2 (by rfl) ⟨476676, by rfl⟩ : syracuseStep 1271137 = 953353) (by norm_num)
theorem B1697141 : Blo 1128631 1697141 := bbase (se 5 (by rfl) ⟨79553, by rfl⟩ : syracuseStep 1697141 = 159107) (by norm_num)
theorem B1271173 : Blo 1128631 1271173 := bbase (se 4 (by rfl) ⟨119172, by rfl⟩ : syracuseStep 1271173 = 238345) (by norm_num)
theorem B1697165 : Blo 1128631 1697165 := bbase (se 3 (by rfl) ⟨318218, by rfl⟩ : syracuseStep 1697165 = 636437) (by norm_num)
theorem B5432741 : Blo 1128631 5432741 := bbase (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) (by norm_num)
theorem B1697189 : Blo 1128631 1697189 := bbase (se 4 (by rfl) ⟨159111, by rfl⟩ : syracuseStep 1697189 = 318223) (by norm_num)
theorem B1271209 : Blo 1128631 1271209 := bbase (se 2 (by rfl) ⟨476703, by rfl⟩ : syracuseStep 1271209 = 953407) (by norm_num)
theorem B10872245 : Blo 1128631 10872245 := bbase (se 5 (by rfl) ⟨509636, by rfl⟩ : syracuseStep 10872245 = 1019273) (by norm_num)
theorem B1697213 : Blo 1128631 1697213 := bbase (se 3 (by rfl) ⟨318227, by rfl⟩ : syracuseStep 1697213 = 636455) (by norm_num)
theorem B1271245 : Blo 1128631 1271245 := bbase (se 3 (by rfl) ⟨238358, by rfl⟩ : syracuseStep 1271245 = 476717) (by norm_num)
theorem B1697237 : Blo 1128631 1697237 := bbase (se 7 (by rfl) ⟨19889, by rfl⟩ : syracuseStep 1697237 = 39779) (by norm_num)
theorem B1697261 : Blo 1128631 1697261 := bbase (se 3 (by rfl) ⟨318236, by rfl⟩ : syracuseStep 1697261 = 636473) (by norm_num)
theorem B1271281 : Blo 1128631 1271281 := bbase (se 2 (by rfl) ⟨476730, by rfl⟩ : syracuseStep 1271281 = 953461) (by norm_num)
theorem B2942453 : Blo 1128631 2942453 := bbase (se 5 (by rfl) ⟨137927, by rfl⟩ : syracuseStep 2942453 = 275855) (by norm_num)
theorem B1697285 : Blo 1128631 1697285 := bbase (se 4 (by rfl) ⟨159120, by rfl⟩ : syracuseStep 1697285 = 318241) (by norm_num)
theorem B4285973 : Blo 1128631 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B1271317 : Blo 1128631 1271317 := bbase (se 6 (by rfl) ⟨29796, by rfl⟩ : syracuseStep 1271317 = 59593) (by norm_num)
theorem B1697309 : Blo 1128631 1697309 := bbase (se 3 (by rfl) ⟨318245, by rfl⟩ : syracuseStep 1697309 = 636491) (by norm_num)
theorem B1697333 : Blo 1128631 1697333 := bbase (se 5 (by rfl) ⟨79562, by rfl⟩ : syracuseStep 1697333 = 159125) (by norm_num)
theorem B1271353 : Blo 1128631 1271353 := bbase (se 2 (by rfl) ⟨476757, by rfl⟩ : syracuseStep 1271353 = 953515) (by norm_num)
theorem B1631821 : Blo 1128631 1631821 := bbase (se 3 (by rfl) ⟨305966, by rfl⟩ : syracuseStep 1631821 = 611933) (by norm_num)
theorem B1697357 : Blo 1128631 1697357 := bbase (se 3 (by rfl) ⟨318254, by rfl⟩ : syracuseStep 1697357 = 636509) (by norm_num)
theorem B1271389 : Blo 1128631 1271389 := bbase (se 3 (by rfl) ⟨238385, by rfl⟩ : syracuseStep 1271389 = 476771) (by norm_num)
theorem B1697381 : Blo 1128631 1697381 := bbase (se 4 (by rfl) ⟨159129, by rfl⟩ : syracuseStep 1697381 = 318259) (by norm_num)
theorem B1697405 : Blo 1128631 1697405 := bbase (se 3 (by rfl) ⟨318263, by rfl⟩ : syracuseStep 1697405 = 636527) (by norm_num)
theorem B1271425 : Blo 1128631 1271425 := bbase (se 2 (by rfl) ⟨476784, by rfl⟩ : syracuseStep 1271425 = 953569) (by norm_num)
theorem B1697429 : Blo 1128631 1697429 := bbase (se 6 (by rfl) ⟨39783, by rfl⟩ : syracuseStep 1697429 = 79567) (by norm_num)
theorem B1271461 : Blo 1128631 1271461 := bbase (se 4 (by rfl) ⟨119199, by rfl⟩ : syracuseStep 1271461 = 238399) (by norm_num)
theorem B1697453 : Blo 1128631 1697453 := bbase (se 3 (by rfl) ⟨318272, by rfl⟩ : syracuseStep 1697453 = 636545) (by norm_num)
theorem B2582189 : Blo 1128631 2582189 := bbase (se 3 (by rfl) ⟨484160, by rfl⟩ : syracuseStep 2582189 = 968321) (by norm_num)
theorem B1697477 : Blo 1128631 1697477 := bbase (se 4 (by rfl) ⟨159138, by rfl⟩ : syracuseStep 1697477 = 318277) (by norm_num)
theorem B1271497 : Blo 1128631 1271497 := bbase (se 2 (by rfl) ⟨476811, by rfl⟩ : syracuseStep 1271497 = 953623) (by norm_num)
theorem B1205977 : Blo 1128631 1205977 := bbase (se 2 (by rfl) ⟨452241, by rfl⟩ : syracuseStep 1205977 = 904483) (by norm_num)
theorem B1697501 : Blo 1128631 1697501 := bbase (se 3 (by rfl) ⟨318281, by rfl⟩ : syracuseStep 1697501 = 636563) (by norm_num)
theorem B1271533 : Blo 1128631 1271533 := bbase (se 3 (by rfl) ⟨238412, by rfl⟩ : syracuseStep 1271533 = 476825) (by norm_num)
theorem B2713333 : Blo 1128631 2713333 := bbase (se 5 (by rfl) ⟨127187, by rfl⟩ : syracuseStep 2713333 = 254375) (by norm_num)
theorem B1697525 : Blo 1128631 1697525 := bbase (se 5 (by rfl) ⟨79571, by rfl⟩ : syracuseStep 1697525 = 159143) (by norm_num)
theorem B1697549 : Blo 1128631 1697549 := bbase (se 3 (by rfl) ⟨318290, by rfl⟩ : syracuseStep 1697549 = 636581) (by norm_num)
theorem B1271569 : Blo 1128631 1271569 := bbase (se 2 (by rfl) ⟨476838, by rfl⟩ : syracuseStep 1271569 = 953677) (by norm_num)
theorem B1206037 : Blo 1128631 1206037 := bbase (se 6 (by rfl) ⟨28266, by rfl⟩ : syracuseStep 1206037 = 56533) (by norm_num)
theorem B4351781 : Blo 1128631 4351781 := bbase (se 4 (by rfl) ⟨407979, by rfl⟩ : syracuseStep 4351781 = 815959) (by norm_num)
theorem B1697573 : Blo 1128631 1697573 := bbase (se 4 (by rfl) ⟨159147, by rfl⟩ : syracuseStep 1697573 = 318295) (by norm_num)
theorem B1271605 : Blo 1128631 1271605 := bbase (se 5 (by rfl) ⟨59606, by rfl⟩ : syracuseStep 1271605 = 119213) (by norm_num)
theorem B1697597 : Blo 1128631 1697597 := bbase (se 3 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 1697597 = 636599) (by norm_num)
theorem B2713429 : Blo 1128631 2713429 := bbase (se 9 (by rfl) ⟨7949, by rfl⟩ : syracuseStep 2713429 = 15899) (by norm_num)
theorem B1697621 : Blo 1128631 1697621 := bbase (se 9 (by rfl) ⟨4973, by rfl⟩ : syracuseStep 1697621 = 9947) (by norm_num)
theorem B1271641 : Blo 1128631 1271641 := bbase (se 2 (by rfl) ⟨476865, by rfl⟩ : syracuseStep 1271641 = 953731) (by norm_num)
theorem B1697645 : Blo 1128631 1697645 := bbase (se 3 (by rfl) ⟨318308, by rfl⟩ : syracuseStep 1697645 = 636617) (by norm_num)
theorem B1271677 : Blo 1128631 1271677 := bbase (se 3 (by rfl) ⟨238439, by rfl⟩ : syracuseStep 1271677 = 476879) (by norm_num)
theorem B1697669 : Blo 1128631 1697669 := bbase (se 4 (by rfl) ⟨159156, by rfl⟩ : syracuseStep 1697669 = 318313) (by norm_num)
theorem B1697693 : Blo 1128631 1697693 := bbase (se 3 (by rfl) ⟨318317, by rfl⟩ : syracuseStep 1697693 = 636635) (by norm_num)
theorem B1271713 : Blo 1128631 1271713 := bbase (se 2 (by rfl) ⟨476892, by rfl⟩ : syracuseStep 1271713 = 953785) (by norm_num)
theorem B1697717 : Blo 1128631 1697717 := bbase (se 5 (by rfl) ⟨79580, by rfl⟩ : syracuseStep 1697717 = 159161) (by norm_num)
theorem B1271749 : Blo 1128631 1271749 := bbase (se 4 (by rfl) ⟨119226, by rfl⟩ : syracuseStep 1271749 = 238453) (by norm_num)
theorem B1697741 : Blo 1128631 1697741 := bbase (se 3 (by rfl) ⟨318326, by rfl⟩ : syracuseStep 1697741 = 636653) (by norm_num)
theorem B1697765 : Blo 1128631 1697765 := bbase (se 4 (by rfl) ⟨159165, by rfl⟩ : syracuseStep 1697765 = 318331) (by norm_num)
theorem B1271785 : Blo 1128631 1271785 := bbase (se 2 (by rfl) ⟨476919, by rfl⟩ : syracuseStep 1271785 = 953839) (by norm_num)
theorem B1697789 : Blo 1128631 1697789 := bbase (se 3 (by rfl) ⟨318335, by rfl⟩ : syracuseStep 1697789 = 636671) (by norm_num)
theorem B1271821 : Blo 1128631 1271821 := bbase (se 3 (by rfl) ⟨238466, by rfl⟩ : syracuseStep 1271821 = 476933) (by norm_num)
theorem B1697813 : Blo 1128631 1697813 := bbase (se 6 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 1697813 = 79585) (by norm_num)
theorem B1697837 : Blo 1128631 1697837 := bbase (se 3 (by rfl) ⟨318344, by rfl⟩ : syracuseStep 1697837 = 636689) (by norm_num)
theorem B1271857 : Blo 1128631 1271857 := bbase (se 2 (by rfl) ⟨476946, by rfl⟩ : syracuseStep 1271857 = 953893) (by norm_num)
theorem B1697861 : Blo 1128631 1697861 := bbase (se 4 (by rfl) ⟨159174, by rfl⟩ : syracuseStep 1697861 = 318349) (by norm_num)
theorem B1960013 : Blo 1128631 1960013 := bbase (se 3 (by rfl) ⟨367502, by rfl⟩ : syracuseStep 1960013 = 735005) (by norm_num)
theorem B1206353 : Blo 1128631 1206353 := bbase (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) (by norm_num)
theorem B1271893 : Blo 1128631 1271893 := bbase (se 8 (by rfl) ⟨7452, by rfl⟩ : syracuseStep 1271893 = 14905) (by norm_num)
theorem B1697885 : Blo 1128631 1697885 := bbase (se 3 (by rfl) ⟨318353, by rfl⟩ : syracuseStep 1697885 = 636707) (by norm_num)
theorem B1697909 : Blo 1128631 1697909 := bbase (se 5 (by rfl) ⟨79589, by rfl⟩ : syracuseStep 1697909 = 159179) (by norm_num)
theorem B1271929 : Blo 1128631 1271929 := bbase (se 2 (by rfl) ⟨476973, by rfl⟩ : syracuseStep 1271929 = 953947) (by norm_num)
theorem B1697933 : Blo 1128631 1697933 := bbase (se 3 (by rfl) ⟨318362, by rfl⟩ : syracuseStep 1697933 = 636725) (by norm_num)
theorem B1271965 : Blo 1128631 1271965 := bbase (se 3 (by rfl) ⟨238493, by rfl⟩ : syracuseStep 1271965 = 476987) (by norm_num)
theorem B1697957 : Blo 1128631 1697957 := bbase (se 4 (by rfl) ⟨159183, by rfl⟩ : syracuseStep 1697957 = 318367) (by norm_num)
theorem B1697981 : Blo 1128631 1697981 := bbase (se 3 (by rfl) ⟨318371, by rfl⟩ : syracuseStep 1697981 = 636743) (by norm_num)
theorem B1272001 : Blo 1128631 1272001 := bbase (se 2 (by rfl) ⟨477000, by rfl⟩ : syracuseStep 1272001 = 954001) (by norm_num)
theorem B1698005 : Blo 1128631 1698005 := bbase (se 7 (by rfl) ⟨19898, by rfl⟩ : syracuseStep 1698005 = 39797) (by norm_num)
theorem B1272037 : Blo 1128631 1272037 := bbase (se 4 (by rfl) ⟨119253, by rfl⟩ : syracuseStep 1272037 = 238507) (by norm_num)
theorem B1698029 : Blo 1128631 1698029 := bbase (se 3 (by rfl) ⟨318380, by rfl⟩ : syracuseStep 1698029 = 636761) (by norm_num)
theorem B2418925 : Blo 1128631 2418925 := bbase (se 3 (by rfl) ⟨453548, by rfl⟩ : syracuseStep 2418925 = 907097) (by norm_num)
theorem B1698053 : Blo 1128631 1698053 := bbase (se 4 (by rfl) ⟨159192, by rfl⟩ : syracuseStep 1698053 = 318385) (by norm_num)
theorem B1272073 : Blo 1128631 1272073 := bbase (se 2 (by rfl) ⟨477027, by rfl⟩ : syracuseStep 1272073 = 954055) (by norm_num)
theorem B1698077 : Blo 1128631 1698077 := bbase (se 3 (by rfl) ⟨318389, by rfl⟩ : syracuseStep 1698077 = 636779) (by norm_num)
theorem B1272109 : Blo 1128631 1272109 := bbase (se 3 (by rfl) ⟨238520, by rfl⟩ : syracuseStep 1272109 = 477041) (by norm_num)
theorem B1698101 : Blo 1128631 1698101 := bbase (se 5 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 1698101 = 159197) (by norm_num)
theorem B1698125 : Blo 1128631 1698125 := bbase (se 3 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 1698125 = 636797) (by norm_num)
theorem B1272145 : Blo 1128631 1272145 := bbase (se 2 (by rfl) ⟨477054, by rfl⟩ : syracuseStep 1272145 = 954109) (by norm_num)
theorem B2713949 : Blo 1128631 2713949 := bbase (se 3 (by rfl) ⟨508865, by rfl⟩ : syracuseStep 2713949 = 1017731) (by norm_num)
theorem B1698149 : Blo 1128631 1698149 := bbase (se 4 (by rfl) ⟨159201, by rfl⟩ : syracuseStep 1698149 = 318403) (by norm_num)
theorem B1272181 : Blo 1128631 1272181 := bbase (se 5 (by rfl) ⟨59633, by rfl⟩ : syracuseStep 1272181 = 119267) (by norm_num)
theorem B1698173 : Blo 1128631 1698173 := bbase (se 3 (by rfl) ⟨318407, by rfl⟩ : syracuseStep 1698173 = 636815) (by norm_num)
theorem B1698197 : Blo 1128631 1698197 := bbase (se 6 (by rfl) ⟨39801, by rfl⟩ : syracuseStep 1698197 = 79603) (by norm_num)
theorem B1272217 : Blo 1128631 1272217 := bbase (se 2 (by rfl) ⟨477081, by rfl⟩ : syracuseStep 1272217 = 954163) (by norm_num)
theorem B1698221 : Blo 1128631 1698221 := bbase (se 3 (by rfl) ⟨318416, by rfl⟩ : syracuseStep 1698221 = 636833) (by norm_num)
theorem B1272253 : Blo 1128631 1272253 := bbase (se 3 (by rfl) ⟨238547, by rfl⟩ : syracuseStep 1272253 = 477095) (by norm_num)
theorem B1698245 : Blo 1128631 1698245 := bbase (se 4 (by rfl) ⟨159210, by rfl⟩ : syracuseStep 1698245 = 318421) (by norm_num)
theorem B1698269 : Blo 1128631 1698269 := bbase (se 3 (by rfl) ⟨318425, by rfl⟩ : syracuseStep 1698269 = 636851) (by norm_num)
theorem B1272289 : Blo 1128631 1272289 := bbase (se 2 (by rfl) ⟨477108, by rfl⟩ : syracuseStep 1272289 = 954217) (by norm_num)
theorem B1698293 : Blo 1128631 1698293 := bbase (se 5 (by rfl) ⟨79607, by rfl⟩ : syracuseStep 1698293 = 159215) (by norm_num)
theorem B1272325 : Blo 1128631 1272325 := bbase (se 4 (by rfl) ⟨119280, by rfl⟩ : syracuseStep 1272325 = 238561) (by norm_num)
theorem B1206797 : Blo 1128631 1206797 := bbase (se 3 (by rfl) ⟨226274, by rfl⟩ : syracuseStep 1206797 = 452549) (by norm_num)
theorem B1698317 : Blo 1128631 1698317 := bbase (se 3 (by rfl) ⟨318434, by rfl⟩ : syracuseStep 1698317 = 636869) (by norm_num)
theorem B5728805 : Blo 1128631 5728805 := bbase (se 4 (by rfl) ⟨537075, by rfl⟩ : syracuseStep 5728805 = 1074151) (by norm_num)
theorem B1698341 : Blo 1128631 1698341 := bbase (se 4 (by rfl) ⟨159219, by rfl⟩ : syracuseStep 1698341 = 318439) (by norm_num)
theorem B1272361 : Blo 1128631 1272361 := bbase (se 2 (by rfl) ⟨477135, by rfl⟩ : syracuseStep 1272361 = 954271) (by norm_num)
theorem B1698365 : Blo 1128631 1698365 := bbase (se 3 (by rfl) ⟨318443, by rfl⟩ : syracuseStep 1698365 = 636887) (by norm_num)
theorem B1206857 : Blo 1128631 1206857 := bbase (se 2 (by rfl) ⟨452571, by rfl⟩ : syracuseStep 1206857 = 905143) (by norm_num)
theorem B1272397 : Blo 1128631 1272397 := bbase (se 3 (by rfl) ⟨238574, by rfl⟩ : syracuseStep 1272397 = 477149) (by norm_num)
theorem B1698389 : Blo 1128631 1698389 := bbase (se 8 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 1698389 = 19903) (by norm_num)
theorem B1698413 : Blo 1128631 1698413 := bbase (se 3 (by rfl) ⟨318452, by rfl⟩ : syracuseStep 1698413 = 636905) (by norm_num)
theorem B1272433 : Blo 1128631 1272433 := bbase (se 2 (by rfl) ⟨477162, by rfl⟩ : syracuseStep 1272433 = 954325) (by norm_num)
theorem B1698437 : Blo 1128631 1698437 := bbase (se 4 (by rfl) ⟨159228, by rfl⟩ : syracuseStep 1698437 = 318457) (by norm_num)
theorem B1272469 : Blo 1128631 1272469 := bbase (se 6 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 1272469 = 59647) (by norm_num)
theorem B1698461 : Blo 1128631 1698461 := bbase (se 3 (by rfl) ⟨318461, by rfl⟩ : syracuseStep 1698461 = 636923) (by norm_num)
theorem B1862317 : Blo 1128631 1862317 := bbase (se 3 (by rfl) ⟨349184, by rfl⟩ : syracuseStep 1862317 = 698369) (by norm_num)
theorem B1698485 : Blo 1128631 1698485 := bbase (se 5 (by rfl) ⟨79616, by rfl⟩ : syracuseStep 1698485 = 159233) (by norm_num)
theorem B1272505 : Blo 1128631 1272505 := bbase (se 2 (by rfl) ⟨477189, by rfl⟩ : syracuseStep 1272505 = 954379) (by norm_num)
theorem B1206985 : Blo 1128631 1206985 := bbase (se 2 (by rfl) ⟨452619, by rfl⟩ : syracuseStep 1206985 = 905239) (by norm_num)
theorem B1698509 : Blo 1128631 1698509 := bbase (se 3 (by rfl) ⟨318470, by rfl⟩ : syracuseStep 1698509 = 636941) (by norm_num)
theorem B1272541 : Blo 1128631 1272541 := bbase (se 3 (by rfl) ⟨238601, by rfl⟩ : syracuseStep 1272541 = 477203) (by norm_num)
theorem B1698533 : Blo 1128631 1698533 := bbase (se 4 (by rfl) ⟨159237, by rfl⟩ : syracuseStep 1698533 = 318475) (by norm_num)
theorem B1698557 : Blo 1128631 1698557 := bbase (se 3 (by rfl) ⟨318479, by rfl⟩ : syracuseStep 1698557 = 636959) (by norm_num)
theorem B1272577 : Blo 1128631 1272577 := bbase (se 2 (by rfl) ⟨477216, by rfl⟩ : syracuseStep 1272577 = 954433) (by norm_num)
theorem B7236373 : Blo 1128631 7236373 := bbase (se 6 (by rfl) ⟨169602, by rfl⟩ : syracuseStep 7236373 = 339205) (by norm_num)
theorem B1698581 : Blo 1128631 1698581 := bbase (se 6 (by rfl) ⟨39810, by rfl⟩ : syracuseStep 1698581 = 79621) (by norm_num)
theorem B1272613 : Blo 1128631 1272613 := bbase (se 4 (by rfl) ⟨119307, by rfl⟩ : syracuseStep 1272613 = 238615) (by norm_num)
theorem B1698605 : Blo 1128631 1698605 := bbase (se 3 (by rfl) ⟨318488, by rfl⟩ : syracuseStep 1698605 = 636977) (by norm_num)
theorem B1698629 : Blo 1128631 1698629 := bbase (se 4 (by rfl) ⟨159246, by rfl⟩ : syracuseStep 1698629 = 318493) (by norm_num)
theorem B1272649 : Blo 1128631 1272649 := bbase (se 2 (by rfl) ⟨477243, by rfl⟩ : syracuseStep 1272649 = 954487) (by norm_num)
theorem B2321237 : Blo 1128631 2321237 := bbase (se 9 (by rfl) ⟨6800, by rfl⟩ : syracuseStep 2321237 = 13601) (by norm_num)
theorem B1698653 : Blo 1128631 1698653 := bbase (se 3 (by rfl) ⟨318497, by rfl⟩ : syracuseStep 1698653 = 636995) (by norm_num)
theorem B2714477 : Blo 1128631 2714477 := bbase (se 3 (by rfl) ⟨508964, by rfl⟩ : syracuseStep 2714477 = 1017929) (by norm_num)
theorem B1272685 : Blo 1128631 1272685 := bbase (se 3 (by rfl) ⟨238628, by rfl⟩ : syracuseStep 1272685 = 477257) (by norm_num)
theorem B1698677 : Blo 1128631 1698677 := bbase (se 5 (by rfl) ⟨79625, by rfl⟩ : syracuseStep 1698677 = 159251) (by norm_num)
theorem B1698701 : Blo 1128631 1698701 := bbase (se 3 (by rfl) ⟨318506, by rfl⟩ : syracuseStep 1698701 = 637013) (by norm_num)
theorem B1272721 : Blo 1128631 1272721 := bbase (se 2 (by rfl) ⟨477270, by rfl⟩ : syracuseStep 1272721 = 954541) (by norm_num)
theorem B1698725 : Blo 1128631 1698725 := bbase (se 4 (by rfl) ⟨159255, by rfl⟩ : syracuseStep 1698725 = 318511) (by norm_num)
theorem B1272757 : Blo 1128631 1272757 := bbase (se 5 (by rfl) ⟨59660, by rfl⟩ : syracuseStep 1272757 = 119321) (by norm_num)
theorem B6450101 : Blo 1128631 6450101 := bbase (se 5 (by rfl) ⟨302348, by rfl⟩ : syracuseStep 6450101 = 604697) (by norm_num)
theorem B1698749 : Blo 1128631 1698749 := bbase (se 3 (by rfl) ⟨318515, by rfl⟩ : syracuseStep 1698749 = 637031) (by norm_num)
theorem B1698773 : Blo 1128631 1698773 := bbase (se 7 (by rfl) ⟨19907, by rfl⟩ : syracuseStep 1698773 = 39815) (by norm_num)
theorem B1272793 : Blo 1128631 1272793 := bbase (se 2 (by rfl) ⟨477297, by rfl⟩ : syracuseStep 1272793 = 954595) (by norm_num)
theorem B1698797 : Blo 1128631 1698797 := bbase (se 3 (by rfl) ⟨318524, by rfl⟩ : syracuseStep 1698797 = 637049) (by norm_num)
theorem B1272829 : Blo 1128631 1272829 := bbase (se 3 (by rfl) ⟨238655, by rfl⟩ : syracuseStep 1272829 = 477311) (by norm_num)
theorem B1698821 : Blo 1128631 1698821 := bbase (se 4 (by rfl) ⟨159264, by rfl⟩ : syracuseStep 1698821 = 318529) (by norm_num)
theorem B1698845 : Blo 1128631 1698845 := bbase (se 3 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 1698845 = 637067) (by norm_num)
theorem B1272865 : Blo 1128631 1272865 := bbase (se 2 (by rfl) ⟨477324, by rfl⟩ : syracuseStep 1272865 = 954649) (by norm_num)
theorem B1698869 : Blo 1128631 1698869 := bbase (se 5 (by rfl) ⟨79634, by rfl⟩ : syracuseStep 1698869 = 159269) (by norm_num)
theorem B1272901 : Blo 1128631 1272901 := bbase (se 4 (by rfl) ⟨119334, by rfl⟩ : syracuseStep 1272901 = 238669) (by norm_num)
theorem B1698893 : Blo 1128631 1698893 := bbase (se 3 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 1698893 = 637085) (by norm_num)
theorem B2714717 : Blo 1128631 2714717 := bbase (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) (by norm_num)
theorem B1698917 : Blo 1128631 1698917 := bbase (se 4 (by rfl) ⟨159273, by rfl⟩ : syracuseStep 1698917 = 318547) (by norm_num)
theorem B1272937 : Blo 1128631 1272937 := bbase (se 2 (by rfl) ⟨477351, by rfl⟩ : syracuseStep 1272937 = 954703) (by norm_num)
theorem B1698941 : Blo 1128631 1698941 := bbase (se 3 (by rfl) ⟨318551, by rfl⟩ : syracuseStep 1698941 = 637103) (by norm_num)
theorem B1207429 : Blo 1128631 1207429 := bbase (se 4 (by rfl) ⟨113196, by rfl⟩ : syracuseStep 1207429 = 226393) (by norm_num)
theorem B1272973 : Blo 1128631 1272973 := bbase (se 3 (by rfl) ⟨238682, by rfl⟩ : syracuseStep 1272973 = 477365) (by norm_num)
theorem B1273009 : Blo 1128631 1273009 := bbase (se 2 (by rfl) ⟨477378, by rfl⟩ : syracuseStep 1273009 = 954757) (by norm_num)
theorem B1273045 : Blo 1128631 1273045 := bbase (se 7 (by rfl) ⟨14918, by rfl⟩ : syracuseStep 1273045 = 29837) (by norm_num)
theorem B1273081 : Blo 1128631 1273081 := bbase (se 2 (by rfl) ⟨477405, by rfl⟩ : syracuseStep 1273081 = 954811) (by norm_num)
theorem B1207549 : Blo 1128631 1207549 := bbase (se 3 (by rfl) ⟨226415, by rfl⟩ : syracuseStep 1207549 = 452831) (by norm_num)
theorem B1273117 : Blo 1128631 1273117 := bbase (se 3 (by rfl) ⟨238709, by rfl⟩ : syracuseStep 1273117 = 477419) (by norm_num)
theorem B5434661 : Blo 1128631 5434661 := bbase (se 4 (by rfl) ⟨509499, by rfl⟩ : syracuseStep 5434661 = 1018999) (by norm_num)
theorem B1273153 : Blo 1128631 1273153 := bbase (se 2 (by rfl) ⟨477432, by rfl⟩ : syracuseStep 1273153 = 954865) (by norm_num)
theorem B1273189 : Blo 1128631 1273189 := bbase (se 4 (by rfl) ⟨119361, by rfl⟩ : syracuseStep 1273189 = 238723) (by norm_num)
theorem B1273225 : Blo 1128631 1273225 := bbase (se 2 (by rfl) ⟨477459, by rfl⟩ : syracuseStep 1273225 = 954919) (by norm_num)
theorem B1273261 : Blo 1128631 1273261 := bbase (se 3 (by rfl) ⟨238736, by rfl⟩ : syracuseStep 1273261 = 477473) (by norm_num)
theorem B1273297 : Blo 1128631 1273297 := bbase (se 2 (by rfl) ⟨477486, by rfl⟩ : syracuseStep 1273297 = 954973) (by norm_num)
theorem B1633765 : Blo 1128631 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B1273333 : Blo 1128631 1273333 := bbase (se 5 (by rfl) ⟨59687, by rfl⟩ : syracuseStep 1273333 = 119375) (by norm_num)
theorem B1207801 : Blo 1128631 1207801 := bbase (se 2 (by rfl) ⟨452925, by rfl⟩ : syracuseStep 1207801 = 905851) (by norm_num)
theorem B2289149 : Blo 1128631 2289149 := bbase (se 3 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 2289149 = 858431) (by norm_num)
theorem B1207805 : Blo 1128631 1207805 := bbase (se 3 (by rfl) ⟨226463, by rfl⟩ : syracuseStep 1207805 = 452927) (by norm_num)
theorem B1273369 : Blo 1128631 1273369 := bbase (se 2 (by rfl) ⟨477513, by rfl⟩ : syracuseStep 1273369 = 955027) (by norm_num)
theorem B1273405 : Blo 1128631 1273405 := bbase (se 3 (by rfl) ⟨238763, by rfl⟩ : syracuseStep 1273405 = 477527) (by norm_num)
theorem B4288085 : Blo 1128631 4288085 := bbase (se 8 (by rfl) ⟨25125, by rfl⟩ : syracuseStep 4288085 = 50251) (by norm_num)
theorem B1273441 : Blo 1128631 1273441 := bbase (se 2 (by rfl) ⟨477540, by rfl⟩ : syracuseStep 1273441 = 955081) (by norm_num)
theorem B3862117 : Blo 1128631 3862117 := bbase (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) (by norm_num)
theorem B1273477 : Blo 1128631 1273477 := bbase (se 4 (by rfl) ⟨119388, by rfl⟩ : syracuseStep 1273477 = 238777) (by norm_num)
theorem B1273513 : Blo 1128631 1273513 := bbase (se 2 (by rfl) ⟨477567, by rfl⟩ : syracuseStep 1273513 = 955135) (by norm_num)
theorem B1273549 : Blo 1128631 1273549 := bbase (se 3 (by rfl) ⟨238790, by rfl⟩ : syracuseStep 1273549 = 477581) (by norm_num)
theorem B1273585 : Blo 1128631 1273585 := bbase (se 2 (by rfl) ⟨477594, by rfl⟩ : syracuseStep 1273585 = 955189) (by norm_num)
theorem B1306381 : Blo 1128631 1306381 := bbase (se 3 (by rfl) ⟨244946, by rfl⟩ : syracuseStep 1306381 = 489893) (by norm_num)
theorem B1273621 : Blo 1128631 1273621 := bbase (se 6 (by rfl) ⟨29850, by rfl⟩ : syracuseStep 1273621 = 59701) (by norm_num)
theorem B5730101 : Blo 1128631 5730101 := bbase (se 5 (by rfl) ⟨268598, by rfl⟩ : syracuseStep 5730101 = 537197) (by norm_num)
theorem B1273657 : Blo 1128631 1273657 := bbase (se 2 (by rfl) ⟨477621, by rfl⟩ : syracuseStep 1273657 = 955243) (by norm_num)
theorem B1306453 : Blo 1128631 1306453 := bbase (se 9 (by rfl) ⟨3827, by rfl⟩ : syracuseStep 1306453 = 7655) (by norm_num)
theorem B1273693 : Blo 1128631 1273693 := bbase (se 3 (by rfl) ⟨238817, by rfl⟩ : syracuseStep 1273693 = 477635) (by norm_num)
theorem B4288373 : Blo 1128631 4288373 := bbase (se 5 (by rfl) ⟨201017, by rfl⟩ : syracuseStep 4288373 = 402035) (by norm_num)
theorem B1273729 : Blo 1128631 1273729 := bbase (se 2 (by rfl) ⟨477648, by rfl⟩ : syracuseStep 1273729 = 955297) (by norm_num)
theorem B1273765 : Blo 1128631 1273765 := bbase (se 4 (by rfl) ⟨119415, by rfl⟩ : syracuseStep 1273765 = 238831) (by norm_num)
theorem B1273801 : Blo 1128631 1273801 := bbase (se 2 (by rfl) ⟨477675, by rfl⟩ : syracuseStep 1273801 = 955351) (by norm_num)
theorem B1273837 : Blo 1128631 1273837 := bbase (se 3 (by rfl) ⟨238844, by rfl⟩ : syracuseStep 1273837 = 477689) (by norm_num)
theorem B1273873 : Blo 1128631 1273873 := bbase (se 2 (by rfl) ⟨477702, by rfl⟩ : syracuseStep 1273873 = 955405) (by norm_num)
theorem B2289701 : Blo 1128631 2289701 := bbase (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) (by norm_num)
theorem B1208369 : Blo 1128631 1208369 := bbase (se 2 (by rfl) ⟨453138, by rfl⟩ : syracuseStep 1208369 = 906277) (by norm_num)
theorem B1273909 : Blo 1128631 1273909 := bbase (se 5 (by rfl) ⟨59714, by rfl⟩ : syracuseStep 1273909 = 119429) (by norm_num)
theorem B1634365 : Blo 1128631 1634365 := bbase (se 3 (by rfl) ⟨306443, by rfl⟩ : syracuseStep 1634365 = 612887) (by norm_num)
theorem B1273945 : Blo 1128631 1273945 := bbase (se 2 (by rfl) ⟨477729, by rfl⟩ : syracuseStep 1273945 = 955459) (by norm_num)
theorem B1273981 : Blo 1128631 1273981 := bbase (se 3 (by rfl) ⟨238871, by rfl⟩ : syracuseStep 1273981 = 477743) (by norm_num)
theorem B1274017 : Blo 1128631 1274017 := bbase (se 2 (by rfl) ⟨477756, by rfl⟩ : syracuseStep 1274017 = 955513) (by norm_num)
theorem B8581301 : Blo 1128631 8581301 := bbase (se 5 (by rfl) ⟨402248, by rfl⟩ : syracuseStep 8581301 = 804497) (by norm_num)
theorem B1274053 : Blo 1128631 1274053 := bbase (se 4 (by rfl) ⟨119442, by rfl⟩ : syracuseStep 1274053 = 238885) (by norm_num)
theorem B1274089 : Blo 1128631 1274089 := bbase (se 2 (by rfl) ⟨477783, by rfl⟩ : syracuseStep 1274089 = 955567) (by norm_num)
theorem B1208557 : Blo 1128631 1208557 := bbase (se 3 (by rfl) ⟨226604, by rfl⟩ : syracuseStep 1208557 = 453209) (by norm_num)
theorem B1274125 : Blo 1128631 1274125 := bbase (se 3 (by rfl) ⟨238898, by rfl⟩ : syracuseStep 1274125 = 477797) (by norm_num)
theorem B1274161 : Blo 1128631 1274161 := bbase (se 2 (by rfl) ⟨477810, by rfl⟩ : syracuseStep 1274161 = 955621) (by norm_num)
theorem B1274197 : Blo 1128631 1274197 := bbase (se 10 (by rfl) ⟨1866, by rfl⟩ : syracuseStep 1274197 = 3733) (by norm_num)
theorem B2290277 : Blo 1128631 2290277 := bbase (se 4 (by rfl) ⟨214713, by rfl⟩ : syracuseStep 2290277 = 429427) (by norm_num)
theorem B5436085 : Blo 1128631 5436085 := bbase (se 5 (by rfl) ⟨254816, by rfl⟩ : syracuseStep 5436085 = 509633) (by norm_num)
theorem B2716429 : Blo 1128631 2716429 := bbase (se 3 (by rfl) ⟨509330, by rfl⟩ : syracuseStep 2716429 = 1018661) (by norm_num)
theorem B24474581 : Blo 1128631 24474581 := bbase (se 7 (by rfl) ⟨286811, by rfl⟩ : syracuseStep 24474581 = 573623) (by norm_num)
theorem B4289557 : Blo 1128631 4289557 := bbase (se 6 (by rfl) ⟨100536, by rfl⟩ : syracuseStep 4289557 = 201073) (by norm_num)
theorem B1209377 : Blo 1128631 1209377 := bbase (se 2 (by rfl) ⟨453516, by rfl⟩ : syracuseStep 1209377 = 907033) (by norm_num)
theorem B5731397 : Blo 1128631 5731397 := bbase (se 4 (by rfl) ⟨537318, by rfl⟩ : syracuseStep 5731397 = 1074637) (by norm_num)
theorem B1176869 : Blo 1128631 1176869 := bbase (se 4 (by rfl) ⟨110331, by rfl⟩ : syracuseStep 1176869 = 220663) (by norm_num)
theorem B4289861 : Blo 1128631 4289861 := bbase (se 4 (by rfl) ⟨402174, by rfl⟩ : syracuseStep 4289861 = 804349) (by norm_num)
theorem B123958613 : Blo 1128631 123958613 := bbase (se 13 (by rfl) ⟨22697, by rfl⟩ : syracuseStep 123958613 = 45395) (by norm_num)
theorem B3437957 : Blo 1128631 3437957 := bbase (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) (by norm_num)
theorem B1144477 : Blo 1128631 1144477 := bbase (se 3 (by rfl) ⟨214589, by rfl⟩ : syracuseStep 1144477 = 429179) (by norm_num)
theorem B2291581 : Blo 1128631 2291581 := bbase (se 3 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 2291581 = 859343) (by norm_num)
theorem B1931381 : Blo 1128631 1931381 := bbase (se 5 (by rfl) ⟨90533, by rfl⟩ : syracuseStep 1931381 = 181067) (by norm_num)
theorem B1177745 : Blo 1128631 1177745 := bbase (se 2 (by rfl) ⟨441654, by rfl⟩ : syracuseStep 1177745 = 883309) (by norm_num)
theorem B6715541 : Blo 1128631 6715541 := bbase (se 6 (by rfl) ⟨157395, by rfl⟩ : syracuseStep 6715541 = 314791) (by norm_num)
theorem B2717869 : Blo 1128631 2717869 := bbase (se 3 (by rfl) ⟨509600, by rfl⟩ : syracuseStep 2717869 = 1019201) (by norm_num)
theorem B13760725 : Blo 1128631 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B1145053 : Blo 1128631 1145053 := bbase (se 3 (by rfl) ⟨214697, by rfl⟩ : syracuseStep 1145053 = 429395) (by norm_num)
theorem B5732693 : Blo 1128631 5732693 := bbase (se 10 (by rfl) ⟨8397, by rfl⟩ : syracuseStep 5732693 = 16795) (by norm_num)
theorem B2292181 : Blo 1128631 2292181 := bbase (se 7 (by rfl) ⟨26861, by rfl⟩ : syracuseStep 2292181 = 53723) (by norm_num)
theorem B7240373 : Blo 1128631 7240373 := bbase (se 5 (by rfl) ⟨339392, by rfl⟩ : syracuseStep 7240373 = 678785) (by norm_num)
theorem B15497941 : Blo 1128631 15497941 := bbase (se 7 (by rfl) ⟨181616, by rfl⟩ : syracuseStep 15497941 = 363233) (by norm_num)
theorem B2718485 : Blo 1128631 2718485 := bbase (se 6 (by rfl) ⟨63714, by rfl⟩ : syracuseStep 2718485 = 127429) (by norm_num)
theorem B1145689 : Blo 1128631 1145689 := bbase (se 2 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 1145689 = 859267) (by norm_num)
theorem B1833877 : Blo 1128631 1833877 := bbase (se 6 (by rfl) ⟨42981, by rfl⟩ : syracuseStep 1833877 = 85963) (by norm_num)
theorem B2718677 : Blo 1128631 2718677 := bbase (se 7 (by rfl) ⟨31859, by rfl⟩ : syracuseStep 2718677 = 63719) (by norm_num)
theorem B1932317 : Blo 1128631 1932317 := bbase (se 3 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 1932317 = 724619) (by norm_num)
theorem B1145917 : Blo 1128631 1145917 := bbase (se 3 (by rfl) ⟨214859, by rfl⟩ : syracuseStep 1145917 = 429719) (by norm_num)
theorem B2718965 : Blo 1128631 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B4291973 : Blo 1128631 4291973 := bbase (se 4 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 4291973 = 804745) (by norm_num)
theorem B2293397 : Blo 1128631 2293397 := bbase (se 6 (by rfl) ⟨53751, by rfl⟩ : syracuseStep 2293397 = 107503) (by norm_num)
theorem B4292261 : Blo 1128631 4292261 := bbase (se 4 (by rfl) ⟨402399, by rfl⟩ : syracuseStep 4292261 = 804799) (by norm_num)
theorem B1146533 : Blo 1128631 1146533 := bbase (se 4 (by rfl) ⟨107487, by rfl⟩ : syracuseStep 1146533 = 214975) (by norm_num)
theorem B3440485 : Blo 1128631 3440485 := bbase (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) (by norm_num)
theorem B1146793 : Blo 1128631 1146793 := bbase (se 2 (by rfl) ⟨430047, by rfl⟩ : syracuseStep 1146793 = 860095) (by norm_num)
theorem B2719889 : Blo 1128631 2719889 := bstep (se 2 (by rfl) ⟨1019958, by rfl⟩ : syracuseStep 2719889 = 2039917) B2039917
theorem B2719907 : Blo 1128631 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B20611381 : Blo 1128631 20611381 := bstep (se 5 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 20611381 = 1932317) B1932317
theorem B15892789 : Blo 1128631 15892789 := bstep (se 5 (by rfl) ⟨744974, by rfl⟩ : syracuseStep 15892789 = 1489949) B1489949
theorem B1933715 : Blo 1128631 1933715 := bstep (se 1 (by rfl) ⟨1450286, by rfl⟩ : syracuseStep 1933715 = 2900573) B2900573
theorem B4293233 : Blo 1128631 4293233 := bstep (se 2 (by rfl) ⟨1609962, by rfl⟩ : syracuseStep 4293233 = 3219925) B3219925
theorem B2294435 : Blo 1128631 2294435 := bstep (se 1 (by rfl) ⟨1720826, by rfl⟩ : syracuseStep 2294435 = 3441653) B3441653
theorem B3441361 : Blo 1128631 3441361 := bstep (se 2 (by rfl) ⟨1290510, by rfl⟩ : syracuseStep 3441361 = 2581021) B2581021
theorem B1934227 : Blo 1128631 1934227 := bstep (se 1 (by rfl) ⟨1450670, by rfl⟩ : syracuseStep 1934227 = 2901341) B2901341
theorem B2720945 : Blo 1128631 2720945 := bstep (se 2 (by rfl) ⟨1020354, by rfl⟩ : syracuseStep 2720945 = 2040709) B2040709
theorem B4130381 : Blo 1128631 4130381 := bstep (se 3 (by rfl) ⟨774446, by rfl⟩ : syracuseStep 4130381 = 1548893) B1548893
theorem B1607377 : Blo 1128631 1607377 := bstep (se 2 (by rfl) ⟨602766, by rfl⟩ : syracuseStep 1607377 = 1205533) B1205533
theorem B1607411 : Blo 1128631 1607411 := bstep (se 1 (by rfl) ⟨1205558, by rfl⟩ : syracuseStep 1607411 = 2411117) B2411117
theorem B4589389 : Blo 1128631 4589389 := bstep (se 3 (by rfl) ⟨860510, by rfl⟩ : syracuseStep 4589389 = 1721021) B1721021
theorem B4294691 : Blo 1128631 4294691 := bstep (se 1 (by rfl) ⟨3221018, by rfl⟩ : syracuseStep 4294691 = 6442037) B6442037
theorem B12879971 : Blo 1128631 12879971 := bstep (se 1 (by rfl) ⟨9659978, by rfl⟩ : syracuseStep 12879971 = 19319957) B19319957
theorem B2033905 : Blo 1128631 2033905 := bstep (se 2 (by rfl) ⟨762714, by rfl⟩ : syracuseStep 2033905 = 1525429) B1525429
theorem B1607969 : Blo 1128631 1607969 := bstep (se 2 (by rfl) ⟨602988, by rfl⟩ : syracuseStep 1607969 = 1205977) B1205977
theorem B8587619 : Blo 1128631 8587619 := bstep (se 1 (by rfl) ⟨6440714, by rfl⟩ : syracuseStep 8587619 = 12881429) B12881429
theorem B1608049 : Blo 1128631 1608049 := bstep (se 2 (by rfl) ⟨603018, by rfl⟩ : syracuseStep 1608049 = 1206037) B1206037
theorem B12224965 : Blo 1128631 12224965 := bstep (se 4 (by rfl) ⟨1146090, by rfl⟩ : syracuseStep 12224965 = 2292181) B2292181
theorem B2034193 : Blo 1128631 2034193 := bstep (se 2 (by rfl) ⟨762822, by rfl⟩ : syracuseStep 2034193 = 1525645) B1525645
theorem B3214093 : Blo 1128631 3214093 := bstep (se 3 (by rfl) ⟨602642, by rfl⟩ : syracuseStep 3214093 = 1205285) B1205285
theorem B15928163 : Blo 1128631 15928163 := bstep (se 1 (by rfl) ⟨11946122, by rfl⟩ : syracuseStep 15928163 = 23892245) B23892245
theorem B9669617 : Blo 1128631 9669617 := bstep (se 2 (by rfl) ⟨3626106, by rfl⟩ : syracuseStep 9669617 = 7252213) B7252213
theorem B4295693 : Blo 1128631 4295693 := bstep (se 3 (by rfl) ⟨805442, by rfl⟩ : syracuseStep 4295693 = 1610885) B1610885
theorem B2034769 : Blo 1128631 2034769 := bstep (se 2 (by rfl) ⟨763038, by rfl⟩ : syracuseStep 2034769 = 1526077) B1526077
theorem B5442659 : Blo 1128631 5442659 := bstep (se 1 (by rfl) ⟨4081994, by rfl⟩ : syracuseStep 5442659 = 8163989) B8163989
theorem B1608835 : Blo 1128631 1608835 := bstep (se 1 (by rfl) ⟨1206626, by rfl⟩ : syracuseStep 1608835 = 2413253) B2413253
theorem B7244963 : Blo 1128631 7244963 := bstep (se 1 (by rfl) ⟨5433722, by rfl⟩ : syracuseStep 7244963 = 10867445) B10867445
theorem B1674499 : Blo 1128631 1674499 := bstep (se 1 (by rfl) ⟨1255874, by rfl⟩ : syracuseStep 1674499 = 2511749) B2511749
theorem B16289221 : Blo 1128631 16289221 := bstep (se 4 (by rfl) ⟨1527114, by rfl⟩ : syracuseStep 16289221 = 3054229) B3054229
theorem B5508643 : Blo 1128631 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B1609313 : Blo 1128631 1609313 := bstep (se 2 (by rfl) ⟨603492, by rfl⟩ : syracuseStep 1609313 = 1206985) B1206985
theorem B6524621 : Blo 1128631 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B1609427 : Blo 1128631 1609427 := bstep (se 1 (by rfl) ⟨1207070, by rfl⟩ : syracuseStep 1609427 = 2414141) B2414141
theorem B5148451 : Blo 1128631 5148451 := bstep (se 1 (by rfl) ⟨3861338, by rfl⟩ : syracuseStep 5148451 = 7722677) B7722677
theorem B1609507 : Blo 1128631 1609507 := bstep (se 1 (by rfl) ⟨1207130, by rfl⟩ : syracuseStep 1609507 = 2414261) B2414261
theorem B6885155 : Blo 1128631 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B3215153 : Blo 1128631 3215153 := bstep (se 2 (by rfl) ⟨1205682, by rfl⟩ : syracuseStep 3215153 = 2411365) B2411365
theorem B1904593 : Blo 1128631 1904593 := bstep (se 2 (by rfl) ⟨714222, by rfl⟩ : syracuseStep 1904593 = 1428445) B1428445
theorem B1904627 : Blo 1128631 1904627 := bstep (se 1 (by rfl) ⟨1428470, by rfl⟩ : syracuseStep 1904627 = 2856941) B2856941
theorem B1904755 : Blo 1128631 1904755 := bstep (se 1 (by rfl) ⟨1428566, by rfl⟩ : syracuseStep 1904755 = 2857133) B2857133
theorem B1904897 : Blo 1128631 1904897 := bstep (se 2 (by rfl) ⟨714336, by rfl⟩ : syracuseStep 1904897 = 1428673) B1428673
theorem B1610065 : Blo 1128631 1610065 := bstep (se 2 (by rfl) ⟨603774, by rfl⟩ : syracuseStep 1610065 = 1207549) B1207549
theorem B1905025 : Blo 1128631 1905025 := bstep (se 2 (by rfl) ⟨714384, by rfl⟩ : syracuseStep 1905025 = 1428769) B1428769
theorem B1905059 : Blo 1128631 1905059 := bstep (se 1 (by rfl) ⟨1428794, by rfl⟩ : syracuseStep 1905059 = 2857589) B2857589
theorem B3215825 : Blo 1128631 3215825 := bstep (se 2 (by rfl) ⟨1205934, by rfl⟩ : syracuseStep 3215825 = 2411869) B2411869
theorem B1905187 : Blo 1128631 1905187 := bstep (se 1 (by rfl) ⟨1428890, by rfl⟩ : syracuseStep 1905187 = 2857781) B2857781
theorem B5509745 : Blo 1128631 5509745 := bstep (se 2 (by rfl) ⟨2066154, by rfl⟩ : syracuseStep 5509745 = 4132309) B4132309
theorem B1905329 : Blo 1128631 1905329 := bstep (se 2 (by rfl) ⟨714498, by rfl⟩ : syracuseStep 1905329 = 1428997) B1428997
theorem B6886129 : Blo 1128631 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B5149489 : Blo 1128631 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B1905457 : Blo 1128631 1905457 := bstep (se 2 (by rfl) ⟨714546, by rfl⟩ : syracuseStep 1905457 = 1429093) B1429093
theorem B1905491 : Blo 1128631 1905491 := bstep (se 1 (by rfl) ⟨1429118, by rfl⟩ : syracuseStep 1905491 = 2858237) B2858237
theorem B5575601 : Blo 1128631 5575601 := bstep (se 2 (by rfl) ⟨2090850, by rfl⟩ : syracuseStep 5575601 = 4181701) B4181701
theorem B1905619 : Blo 1128631 1905619 := bstep (se 1 (by rfl) ⟨1429214, by rfl⟩ : syracuseStep 1905619 = 2858429) B2858429
theorem B31396835 : Blo 1128631 31396835 := bstep (se 1 (by rfl) ⟨23547626, by rfl⟩ : syracuseStep 31396835 = 47095253) B47095253
theorem B1741841 : Blo 1128631 1741841 := bstep (se 2 (by rfl) ⟨653190, by rfl⟩ : syracuseStep 1741841 = 1306381) B1306381
theorem B1610771 : Blo 1128631 1610771 := bstep (se 1 (by rfl) ⟨1208078, by rfl⟩ : syracuseStep 1610771 = 2416157) B2416157
theorem B4297805 : Blo 1128631 4297805 := bstep (se 3 (by rfl) ⟨805838, by rfl⟩ : syracuseStep 4297805 = 1611677) B1611677
theorem B1905761 : Blo 1128631 1905761 := bstep (se 2 (by rfl) ⟨714660, by rfl⟩ : syracuseStep 1905761 = 1429321) B1429321
theorem B1741937 : Blo 1128631 1741937 := bstep (se 2 (by rfl) ⟨653226, by rfl⟩ : syracuseStep 1741937 = 1306453) B1306453
theorem B1905889 : Blo 1128631 1905889 := bstep (se 2 (by rfl) ⟨714708, by rfl⟩ : syracuseStep 1905889 = 1429417) B1429417
theorem B3216611 : Blo 1128631 3216611 := bstep (se 1 (by rfl) ⟨2412458, by rfl⟩ : syracuseStep 3216611 = 4824917) B4824917
theorem B1905923 : Blo 1128631 1905923 := bstep (se 1 (by rfl) ⟨1429442, by rfl⟩ : syracuseStep 1905923 = 2858885) B2858885
theorem B1906051 : Blo 1128631 1906051 := bstep (se 1 (by rfl) ⟨1429538, by rfl⟩ : syracuseStep 1906051 = 2859077) B2859077
theorem B4822541 : Blo 1128631 4822541 := bstep (se 3 (by rfl) ⟨904226, by rfl⟩ : syracuseStep 4822541 = 1808453) B1808453
theorem B1906193 : Blo 1128631 1906193 := bstep (se 2 (by rfl) ⟨714822, by rfl⟩ : syracuseStep 1906193 = 1429645) B1429645
theorem B3216941 : Blo 1128631 3216941 := bstep (se 3 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 3216941 = 1206353) B1206353
theorem B18814577 : Blo 1128631 18814577 := bstep (se 2 (by rfl) ⟨7055466, by rfl⟩ : syracuseStep 18814577 = 14110933) B14110933
theorem B3217009 : Blo 1128631 3217009 := bstep (se 2 (by rfl) ⟨1206378, by rfl⟩ : syracuseStep 3217009 = 2412757) B2412757
theorem B2037379 : Blo 1128631 2037379 := bstep (se 1 (by rfl) ⟨1528034, by rfl⟩ : syracuseStep 2037379 = 3056069) B3056069
theorem B1906321 : Blo 1128631 1906321 := bstep (se 2 (by rfl) ⟨714870, by rfl⟩ : syracuseStep 1906321 = 1429741) B1429741
theorem B1611409 : Blo 1128631 1611409 := bstep (se 2 (by rfl) ⟨604278, by rfl⟩ : syracuseStep 1611409 = 1208557) B1208557
theorem B1906355 : Blo 1128631 1906355 := bstep (se 1 (by rfl) ⟨1429766, by rfl⟩ : syracuseStep 1906355 = 2859533) B2859533
theorem B1611523 : Blo 1128631 1611523 := bstep (se 1 (by rfl) ⟨1208642, by rfl⟩ : syracuseStep 1611523 = 2417285) B2417285
theorem B1906483 : Blo 1128631 1906483 := bstep (se 1 (by rfl) ⟨1429862, by rfl⟩ : syracuseStep 1906483 = 2859725) B2859725
theorem B4298609 : Blo 1128631 4298609 := bstep (se 2 (by rfl) ⟨1611978, by rfl⟩ : syracuseStep 4298609 = 3223957) B3223957
theorem B3217283 : Blo 1128631 3217283 := bstep (se 1 (by rfl) ⟨2412962, by rfl⟩ : syracuseStep 3217283 = 4825925) B4825925
theorem B1906625 : Blo 1128631 1906625 := bstep (se 2 (by rfl) ⟨714984, by rfl⟩ : syracuseStep 1906625 = 1429969) B1429969
theorem B1906753 : Blo 1128631 1906753 := bstep (se 2 (by rfl) ⟨715032, by rfl⟩ : syracuseStep 1906753 = 1430065) B1430065
theorem B4069453 : Blo 1128631 4069453 := bstep (se 3 (by rfl) ⟨763022, by rfl⟩ : syracuseStep 4069453 = 1526045) B1526045
theorem B1906787 : Blo 1128631 1906787 := bstep (se 1 (by rfl) ⟨1430090, by rfl⟩ : syracuseStep 1906787 = 2860181) B2860181
theorem B1448099 : Blo 1128631 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B1906915 : Blo 1128631 1906915 := bstep (se 1 (by rfl) ⟨1430186, by rfl⟩ : syracuseStep 1906915 = 2860373) B2860373
theorem B7248113 : Blo 1128631 7248113 := bstep (se 2 (by rfl) ⟨2718042, by rfl⟩ : syracuseStep 7248113 = 5436085) B5436085
theorem B7248163 : Blo 1128631 7248163 := bstep (se 1 (by rfl) ⟨5436122, by rfl⟩ : syracuseStep 7248163 = 10872245) B10872245
theorem B2857265 : Blo 1128631 2857265 := bstep (se 2 (by rfl) ⟨1071474, by rfl⟩ : syracuseStep 2857265 = 2142949) B2142949
theorem B2857315 : Blo 1128631 2857315 := bstep (se 1 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 2857315 = 4285973) B4285973
theorem B1907057 : Blo 1128631 1907057 := bstep (se 2 (by rfl) ⟨715146, by rfl⟩ : syracuseStep 1907057 = 1430293) B1430293
theorem B2857457 : Blo 1128631 2857457 := bstep (se 2 (by rfl) ⟨1071546, by rfl⟩ : syracuseStep 2857457 = 2143093) B2143093
theorem B1907185 : Blo 1128631 1907185 := bstep (se 2 (by rfl) ⟨715194, by rfl⟩ : syracuseStep 1907185 = 1430389) B1430389
theorem B4299277 : Blo 1128631 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B1907219 : Blo 1128631 1907219 := bstep (se 1 (by rfl) ⟨1430414, by rfl⟩ : syracuseStep 1907219 = 2860829) B2860829
theorem B6429233 : Blo 1128631 6429233 := bstep (se 2 (by rfl) ⟨2410962, by rfl⟩ : syracuseStep 6429233 = 4821925) B4821925
theorem B1907347 : Blo 1128631 1907347 := bstep (se 1 (by rfl) ⟨1430510, by rfl⟩ : syracuseStep 1907347 = 2861021) B2861021
theorem B3218125 : Blo 1128631 3218125 := bstep (se 3 (by rfl) ⟨603398, by rfl⟩ : syracuseStep 3218125 = 1206797) B1206797
theorem B1907489 : Blo 1128631 1907489 := bstep (se 2 (by rfl) ⟨715308, by rfl⟩ : syracuseStep 1907489 = 1430617) B1430617
theorem B3218285 : Blo 1128631 3218285 := bstep (se 3 (by rfl) ⟨603428, by rfl⟩ : syracuseStep 3218285 = 1206857) B1206857
theorem B1809299 : Blo 1128631 1809299 := bstep (se 1 (by rfl) ⟨1356974, by rfl⟩ : syracuseStep 1809299 = 2713949) B2713949
theorem B1907617 : Blo 1128631 1907617 := bstep (se 2 (by rfl) ⟨715356, by rfl⟩ : syracuseStep 1907617 = 1430713) B1430713
theorem B2038691 : Blo 1128631 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B1907651 : Blo 1128631 1907651 := bstep (se 1 (by rfl) ⟨1430738, by rfl⟩ : syracuseStep 1907651 = 2861477) B2861477
theorem B3218467 : Blo 1128631 3218467 := bstep (se 1 (by rfl) ⟨2413850, by rfl⟩ : syracuseStep 3218467 = 4827701) B4827701
theorem B1907779 : Blo 1128631 1907779 := bstep (se 1 (by rfl) ⟨1430834, by rfl⟩ : syracuseStep 1907779 = 2861669) B2861669
theorem B2038979 : Blo 1128631 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B3873997 : Blo 1128631 3873997 := bstep (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) B1452749
theorem B1907921 : Blo 1128631 1907921 := bstep (se 2 (by rfl) ⟨715470, by rfl⟩ : syracuseStep 1907921 = 1430941) B1430941
theorem B1547491 : Blo 1128631 1547491 := bstep (se 1 (by rfl) ⟨1160618, by rfl⟩ : syracuseStep 1547491 = 2321237) B2321237
theorem B4300067 : Blo 1128631 4300067 := bstep (se 1 (by rfl) ⟨3225050, by rfl⟩ : syracuseStep 4300067 = 6450101) B6450101
theorem B1908049 : Blo 1128631 1908049 := bstep (se 2 (by rfl) ⟨715518, by rfl⟩ : syracuseStep 1908049 = 1431037) B1431037
theorem B1908083 : Blo 1128631 1908083 := bstep (se 1 (by rfl) ⟨1431062, by rfl⟩ : syracuseStep 1908083 = 2862125) B2862125
theorem B1809811 : Blo 1128631 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B2039203 : Blo 1128631 2039203 := bstep (se 1 (by rfl) ⟨1529402, by rfl⟩ : syracuseStep 2039203 = 3058805) B3058805
theorem B6102449 : Blo 1128631 6102449 := bstep (se 2 (by rfl) ⟨2288418, by rfl⟩ : syracuseStep 6102449 = 4576837) B4576837
theorem B1809857 : Blo 1128631 1809857 := bstep (se 2 (by rfl) ⟨678696, by rfl⟩ : syracuseStep 1809857 = 1357393) B1357393
theorem B2858449 : Blo 1128631 2858449 := bstep (se 2 (by rfl) ⟨1071918, by rfl⟩ : syracuseStep 2858449 = 2143837) B2143837
theorem B2039267 : Blo 1128631 2039267 := bstep (se 1 (by rfl) ⟨1529450, by rfl⟩ : syracuseStep 2039267 = 3058901) B3058901
theorem B1908211 : Blo 1128631 1908211 := bstep (se 1 (by rfl) ⟨1431158, by rfl⟩ : syracuseStep 1908211 = 2862317) B2862317
theorem B8592965 : Blo 1128631 8592965 := bstep (se 4 (by rfl) ⟨805590, by rfl⟩ : syracuseStep 8592965 = 1611181) B1611181
theorem B1908353 : Blo 1128631 1908353 := bstep (se 2 (by rfl) ⟨715632, by rfl⟩ : syracuseStep 1908353 = 1431265) B1431265
theorem B2858723 : Blo 1128631 2858723 := bstep (se 1 (by rfl) ⟨2144042, by rfl⟩ : syracuseStep 2858723 = 4288085) B4288085
theorem B1908481 : Blo 1128631 1908481 := bstep (se 2 (by rfl) ⟨715680, by rfl⟩ : syracuseStep 1908481 = 1431361) B1431361
theorem B1908515 : Blo 1128631 1908515 := bstep (se 1 (by rfl) ⟨1431386, by rfl⟩ : syracuseStep 1908515 = 2862773) B2862773
theorem B3055441 : Blo 1128631 3055441 := bstep (se 2 (by rfl) ⟨1145790, by rfl⟩ : syracuseStep 3055441 = 2291581) B2291581
theorem B1908643 : Blo 1128631 1908643 := bstep (se 1 (by rfl) ⟨1431482, by rfl⟩ : syracuseStep 1908643 = 2862965) B2862965
theorem B2858915 : Blo 1128631 2858915 := bstep (se 1 (by rfl) ⟨2144186, by rfl⟩ : syracuseStep 2858915 = 4288373) B4288373
theorem B6430691 : Blo 1128631 6430691 := bstep (se 1 (by rfl) ⟨4823018, by rfl⟩ : syracuseStep 6430691 = 9646037) B9646037
theorem B1908785 : Blo 1128631 1908785 := bstep (se 2 (by rfl) ⟨715794, by rfl⟩ : syracuseStep 1908785 = 1431589) B1431589
theorem B1810529 : Blo 1128631 1810529 := bstep (se 2 (by rfl) ⟨678948, by rfl⟩ : syracuseStep 1810529 = 1357897) B1357897
theorem B1908913 : Blo 1128631 1908913 := bstep (se 2 (by rfl) ⟨715842, by rfl⟩ : syracuseStep 1908913 = 1431685) B1431685
theorem B1908947 : Blo 1128631 1908947 := bstep (se 1 (by rfl) ⟨1431710, by rfl⟩ : syracuseStep 1908947 = 2863421) B2863421
theorem B1909075 : Blo 1128631 1909075 := bstep (se 1 (by rfl) ⟨1431806, by rfl⟩ : syracuseStep 1909075 = 2863613) B2863613
theorem B3809645 : Blo 1128631 3809645 := bstep (se 3 (by rfl) ⟨714308, by rfl⟩ : syracuseStep 3809645 = 1428617) B1428617
theorem B3219857 : Blo 1128631 3219857 := bstep (se 2 (by rfl) ⟨1207446, by rfl⟩ : syracuseStep 3219857 = 2414893) B2414893
theorem B3809699 : Blo 1128631 3809699 := bstep (se 1 (by rfl) ⟨2857274, by rfl⟩ : syracuseStep 3809699 = 5714549) B5714549
theorem B2040241 : Blo 1128631 2040241 := bstep (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) B1530181
theorem B1909217 : Blo 1128631 1909217 := bstep (se 2 (by rfl) ⟨715956, by rfl⟩ : syracuseStep 1909217 = 1431913) B1431913
theorem B4137443 : Blo 1128631 4137443 := bstep (se 1 (by rfl) ⟨3103082, by rfl⟩ : syracuseStep 4137443 = 6206165) B6206165
theorem B1811041 : Blo 1128631 1811041 := bstep (se 2 (by rfl) ⟨679140, by rfl⟩ : syracuseStep 1811041 = 1358281) B1358281
theorem B1909345 : Blo 1128631 1909345 := bstep (se 2 (by rfl) ⟨716004, by rfl⟩ : syracuseStep 1909345 = 1432009) B1432009
theorem B1909379 : Blo 1128631 1909379 := bstep (se 1 (by rfl) ⟨1432034, by rfl⟩ : syracuseStep 1909379 = 2864069) B2864069
theorem B7250573 : Blo 1128631 7250573 := bstep (se 3 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 7250573 = 2718965) B2718965
theorem B3809969 : Blo 1128631 3809969 := bstep (se 2 (by rfl) ⟨1428738, by rfl⟩ : syracuseStep 3809969 = 2857477) B2857477
theorem B1909507 : Blo 1128631 1909507 := bstep (se 1 (by rfl) ⟨1432130, by rfl⟩ : syracuseStep 1909507 = 2864261) B2864261
theorem B14492429 : Blo 1128631 14492429 := bstep (se 3 (by rfl) ⟨2717330, by rfl⟩ : syracuseStep 14492429 = 5434661) B5434661
theorem B2859857 : Blo 1128631 2859857 := bstep (se 2 (by rfl) ⟨1072446, by rfl⟩ : syracuseStep 2859857 = 2144893) B2144893
theorem B2859907 : Blo 1128631 2859907 := bstep (se 1 (by rfl) ⟨2144930, by rfl⟩ : syracuseStep 2859907 = 4289861) B4289861
theorem B1909649 : Blo 1128631 1909649 := bstep (se 2 (by rfl) ⟨716118, by rfl⟩ : syracuseStep 1909649 = 1432237) B1432237
theorem B2860049 : Blo 1128631 2860049 := bstep (se 2 (by rfl) ⟨1072518, by rfl⟩ : syracuseStep 2860049 = 2145037) B2145037
theorem B1909777 : Blo 1128631 1909777 := bstep (se 2 (by rfl) ⟨716166, by rfl⟩ : syracuseStep 1909777 = 1432333) B1432333
theorem B1909811 : Blo 1128631 1909811 := bstep (se 1 (by rfl) ⟨1432358, by rfl⟩ : syracuseStep 1909811 = 2864717) B2864717
theorem B1909939 : Blo 1128631 1909939 := bstep (se 1 (by rfl) ⟨1432454, by rfl⟩ : syracuseStep 1909939 = 2864909) B2864909
theorem B3810509 : Blo 1128631 3810509 := bstep (se 3 (by rfl) ⟨714470, by rfl⟩ : syracuseStep 3810509 = 1428941) B1428941
theorem B3810563 : Blo 1128631 3810563 := bstep (se 1 (by rfl) ⟨2857922, by rfl⟩ : syracuseStep 3810563 = 5715845) B5715845
theorem B1910081 : Blo 1128631 1910081 := bstep (se 2 (by rfl) ⟨716280, by rfl⟩ : syracuseStep 1910081 = 1432561) B1432561
theorem B3220813 : Blo 1128631 3220813 := bstep (se 3 (by rfl) ⟨603902, by rfl⟩ : syracuseStep 3220813 = 1207805) B1207805
theorem B1287587 : Blo 1128631 1287587 := bstep (se 1 (by rfl) ⟨965690, by rfl⟩ : syracuseStep 1287587 = 1931381) B1931381
theorem B1910209 : Blo 1128631 1910209 := bstep (se 2 (by rfl) ⟨716328, by rfl⟩ : syracuseStep 1910209 = 1432657) B1432657
theorem B4826573 : Blo 1128631 4826573 := bstep (se 3 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 4826573 = 1809965) B1809965
theorem B1910243 : Blo 1128631 1910243 := bstep (se 1 (by rfl) ⟨1432682, by rfl⟩ : syracuseStep 1910243 = 2865365) B2865365
theorem B3810833 : Blo 1128631 3810833 := bstep (se 2 (by rfl) ⟨1429062, by rfl⟩ : syracuseStep 3810833 = 2858125) B2858125
theorem B3221041 : Blo 1128631 3221041 := bstep (se 2 (by rfl) ⟨1207890, by rfl⟩ : syracuseStep 3221041 = 2415781) B2415781
theorem B1910371 : Blo 1128631 1910371 := bstep (se 1 (by rfl) ⟨1432778, by rfl⟩ : syracuseStep 1910371 = 2865557) B2865557
theorem B3221201 : Blo 1128631 3221201 := bstep (se 2 (by rfl) ⟨1207950, by rfl⟩ : syracuseStep 3221201 = 2415901) B2415901
theorem B10856177 : Blo 1128631 10856177 := bstep (se 2 (by rfl) ⟨4071066, by rfl⟩ : syracuseStep 10856177 = 8142133) B8142133
theorem B1910513 : Blo 1128631 1910513 := bstep (se 2 (by rfl) ⟨716442, by rfl⟩ : syracuseStep 1910513 = 1432885) B1432885
theorem B3057421 : Blo 1128631 3057421 := bstep (se 3 (by rfl) ⟨573266, by rfl⟩ : syracuseStep 3057421 = 1146533) B1146533
theorem B4826915 : Blo 1128631 4826915 := bstep (se 1 (by rfl) ⟨3620186, by rfl⟩ : syracuseStep 4826915 = 7240373) B7240373
theorem B3221315 : Blo 1128631 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B1812323 : Blo 1128631 1812323 := bstep (se 1 (by rfl) ⟨1359242, by rfl⟩ : syracuseStep 1812323 = 2718485) B2718485
theorem B1910641 : Blo 1128631 1910641 := bstep (se 2 (by rfl) ⟨716490, by rfl⟩ : syracuseStep 1910641 = 1432981) B1432981
theorem B1910675 : Blo 1128631 1910675 := bstep (se 1 (by rfl) ⟨1433006, by rfl⟩ : syracuseStep 1910675 = 2866013) B2866013
theorem B1812451 : Blo 1128631 1812451 := bstep (se 1 (by rfl) ⟨1359338, by rfl⟩ : syracuseStep 1812451 = 2718677) B2718677
theorem B2861041 : Blo 1128631 2861041 := bstep (se 2 (by rfl) ⟨1072890, by rfl⟩ : syracuseStep 2861041 = 2145781) B2145781
theorem B1910803 : Blo 1128631 1910803 := bstep (se 1 (by rfl) ⟨1433102, by rfl⟩ : syracuseStep 1910803 = 2866205) B2866205
theorem B3811373 : Blo 1128631 3811373 := bstep (se 3 (by rfl) ⟨714632, by rfl⟩ : syracuseStep 3811373 = 1429265) B1429265
theorem B3811427 : Blo 1128631 3811427 := bstep (se 1 (by rfl) ⟨2858570, by rfl⟩ : syracuseStep 3811427 = 5717141) B5717141
theorem B1812593 : Blo 1128631 1812593 := bstep (se 2 (by rfl) ⟨679722, by rfl⟩ : syracuseStep 1812593 = 1359445) B1359445
theorem B1910945 : Blo 1128631 1910945 := bstep (se 2 (by rfl) ⟨716604, by rfl⟩ : syracuseStep 1910945 = 1433209) B1433209
theorem B4827377 : Blo 1128631 4827377 := bstep (se 2 (by rfl) ⟨1810266, by rfl⟩ : syracuseStep 4827377 = 3620533) B3620533
theorem B2861315 : Blo 1128631 2861315 := bstep (se 1 (by rfl) ⟨2145986, by rfl⟩ : syracuseStep 2861315 = 4291973) B4291973
theorem B1911073 : Blo 1128631 1911073 := bstep (se 2 (by rfl) ⟨716652, by rfl⟩ : syracuseStep 1911073 = 1433305) B1433305
theorem B1911107 : Blo 1128631 1911107 := bstep (se 1 (by rfl) ⟨1433330, by rfl⟩ : syracuseStep 1911107 = 2866661) B2866661
theorem B3811697 : Blo 1128631 3811697 := bstep (se 2 (by rfl) ⟨1429386, by rfl⟩ : syracuseStep 3811697 = 2858773) B2858773
theorem B1812881 : Blo 1128631 1812881 := bstep (se 2 (by rfl) ⟨679830, by rfl⟩ : syracuseStep 1812881 = 1359661) B1359661
theorem B2861507 : Blo 1128631 2861507 := bstep (se 1 (by rfl) ⟨2146130, by rfl⟩ : syracuseStep 2861507 = 4292261) B4292261
theorem B1911235 : Blo 1128631 1911235 := bstep (se 1 (by rfl) ⟨1433426, by rfl⟩ : syracuseStep 1911235 = 2866853) B2866853
theorem B13740529 : Blo 1128631 13740529 := bstep (se 2 (by rfl) ⟨5152698, by rfl⟩ : syracuseStep 13740529 = 10305397) B10305397
theorem B3058381 : Blo 1128631 3058381 := bstep (se 3 (by rfl) ⟨573446, by rfl⟩ : syracuseStep 3058381 = 1146893) B1146893
theorem B3222317 : Blo 1128631 3222317 := bstep (se 3 (by rfl) ⟨604184, by rfl⟩ : syracuseStep 3222317 = 1208369) B1208369
theorem B3812237 : Blo 1128631 3812237 := bstep (se 3 (by rfl) ⟨714794, by rfl⟩ : syracuseStep 3812237 = 1429589) B1429589
theorem B3812291 : Blo 1128631 3812291 := bstep (se 1 (by rfl) ⟨2859218, by rfl⟩ : syracuseStep 3812291 = 5718437) B5718437
theorem B3222499 : Blo 1128631 3222499 := bstep (se 1 (by rfl) ⟨2416874, by rfl⟩ : syracuseStep 3222499 = 4833749) B4833749
theorem B3615779 : Blo 1128631 3615779 := bstep (se 1 (by rfl) ⟨2711834, by rfl⟩ : syracuseStep 3615779 = 5423669) B5423669
theorem B6106211 : Blo 1128631 6106211 := bstep (se 1 (by rfl) ⟨4579658, by rfl⟩ : syracuseStep 6106211 = 9159317) B9159317
theorem B3222659 : Blo 1128631 3222659 := bstep (se 1 (by rfl) ⟨2416994, by rfl⟩ : syracuseStep 3222659 = 4833989) B4833989
theorem B1813681 : Blo 1128631 1813681 := bstep (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) B1360261
theorem B3812561 : Blo 1128631 3812561 := bstep (se 2 (by rfl) ⟨1429710, by rfl⟩ : syracuseStep 3812561 = 2859421) B2859421
theorem B7351523 : Blo 1128631 7351523 := bstep (se 1 (by rfl) ⟨5513642, by rfl⟩ : syracuseStep 7351523 = 11027285) B11027285
theorem B2862449 : Blo 1128631 2862449 := bstep (se 2 (by rfl) ⟨1073418, by rfl⟩ : syracuseStep 2862449 = 2146837) B2146837
theorem B2862499 : Blo 1128631 2862499 := bstep (se 1 (by rfl) ⟨2146874, by rfl⟩ : syracuseStep 2862499 = 4293749) B4293749
theorem B2862641 : Blo 1128631 2862641 := bstep (se 2 (by rfl) ⟨1073490, by rfl⟩ : syracuseStep 2862641 = 2146981) B2146981
theorem B3616433 : Blo 1128631 3616433 := bstep (se 2 (by rfl) ⟨1356162, by rfl⟩ : syracuseStep 3616433 = 2712325) B2712325
theorem B3813101 : Blo 1128631 3813101 := bstep (se 3 (by rfl) ⟨714956, by rfl⟩ : syracuseStep 3813101 = 1429913) B1429913
theorem B3813155 : Blo 1128631 3813155 := bstep (se 1 (by rfl) ⟨2859866, by rfl⟩ : syracuseStep 3813155 = 5719733) B5719733
theorem B1716131 : Blo 1128631 1716131 := bstep (se 1 (by rfl) ⟨1287098, by rfl⟩ : syracuseStep 1716131 = 2574197) B2574197
theorem B3813425 : Blo 1128631 3813425 := bstep (se 2 (by rfl) ⟨1430034, by rfl⟩ : syracuseStep 3813425 = 2860069) B2860069
theorem B10858637 : Blo 1128631 10858637 := bstep (se 3 (by rfl) ⟨2035994, by rfl⟩ : syracuseStep 10858637 = 4071989) B4071989
theorem B3223729 : Blo 1128631 3223729 := bstep (se 2 (by rfl) ⟨1208898, by rfl⟩ : syracuseStep 3223729 = 2417797) B2417797
theorem B5714225 : Blo 1128631 5714225 := bstep (se 2 (by rfl) ⟨2142834, by rfl⟩ : syracuseStep 5714225 = 4285669) B4285669
theorem B2863633 : Blo 1128631 2863633 := bstep (se 2 (by rfl) ⟨1073862, by rfl⟩ : syracuseStep 2863633 = 2147725) B2147725
theorem B6107683 : Blo 1128631 6107683 := bstep (se 1 (by rfl) ⟨4580762, by rfl⟩ : syracuseStep 6107683 = 9161525) B9161525
theorem B3813965 : Blo 1128631 3813965 := bstep (se 3 (by rfl) ⟨715118, by rfl⟩ : syracuseStep 3813965 = 1430237) B1430237
theorem B3814019 : Blo 1128631 3814019 := bstep (se 1 (by rfl) ⟨2860514, by rfl⟩ : syracuseStep 3814019 = 5721029) B5721029
theorem B2142865 : Blo 1128631 2142865 := bstep (se 2 (by rfl) ⟨803574, by rfl⟩ : syracuseStep 2142865 = 1607149) B1607149
theorem B2175761 : Blo 1128631 2175761 := bstep (se 2 (by rfl) ⟨815910, by rfl⟩ : syracuseStep 2175761 = 1631821) B1631821
theorem B2863907 : Blo 1128631 2863907 := bstep (se 1 (by rfl) ⟨2147930, by rfl⟩ : syracuseStep 2863907 = 4295861) B4295861
theorem B4076401 : Blo 1128631 4076401 := bstep (se 2 (by rfl) ⟨1528650, by rfl⟩ : syracuseStep 4076401 = 3057301) B3057301
theorem B3814289 : Blo 1128631 3814289 := bstep (se 2 (by rfl) ⟨1430358, by rfl⟩ : syracuseStep 3814289 = 2860717) B2860717
theorem B2864099 : Blo 1128631 2864099 := bstep (se 1 (by rfl) ⟨2148074, by rfl⟩ : syracuseStep 2864099 = 4296149) B4296149
theorem B3617777 : Blo 1128631 3617777 := bstep (se 2 (by rfl) ⟨1356666, by rfl⟩ : syracuseStep 3617777 = 2713333) B2713333
theorem B1356931 : Blo 1128631 1356931 := bstep (se 1 (by rfl) ⟨1017698, by rfl⟩ : syracuseStep 1356931 = 2035397) B2035397
theorem B8598797 : Blo 1128631 8598797 := bstep (se 3 (by rfl) ⟨1612274, by rfl⟩ : syracuseStep 8598797 = 3224549) B3224549
theorem B3814829 : Blo 1128631 3814829 := bstep (se 3 (by rfl) ⟨715280, by rfl⟩ : syracuseStep 3814829 = 1430561) B1430561
theorem B3225005 : Blo 1128631 3225005 := bstep (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) B1209377
theorem B3814883 : Blo 1128631 3814883 := bstep (se 1 (by rfl) ⟨2861162, by rfl⟩ : syracuseStep 3814883 = 5722325) B5722325
theorem B3094051 : Blo 1128631 3094051 := bstep (se 1 (by rfl) ⟨2320538, by rfl⟩ : syracuseStep 3094051 = 4641077) B4641077
theorem B3225187 : Blo 1128631 3225187 := bstep (se 1 (by rfl) ⟨2418890, by rfl⟩ : syracuseStep 3225187 = 4837781) B4837781
theorem B3225233 : Blo 1128631 3225233 := bstep (se 2 (by rfl) ⟨1209462, by rfl⟩ : syracuseStep 3225233 = 2418925) B2418925
theorem B2143921 : Blo 1128631 2143921 := bstep (se 2 (by rfl) ⟨803970, by rfl⟩ : syracuseStep 2143921 = 1607941) B1607941
theorem B5715683 : Blo 1128631 5715683 := bstep (se 1 (by rfl) ⟨4286762, by rfl⟩ : syracuseStep 5715683 = 8573525) B8573525
theorem B4830947 : Blo 1128631 4830947 := bstep (se 1 (by rfl) ⟨3623210, by rfl⟩ : syracuseStep 4830947 = 7246421) B7246421
theorem B3815153 : Blo 1128631 3815153 := bstep (se 2 (by rfl) ⟨1430682, by rfl⟩ : syracuseStep 3815153 = 2861365) B2861365
theorem B2865041 : Blo 1128631 2865041 := bstep (se 2 (by rfl) ⟨1074390, by rfl⟩ : syracuseStep 2865041 = 2148781) B2148781
theorem B2865091 : Blo 1128631 2865091 := bstep (se 1 (by rfl) ⟨2148818, by rfl⟩ : syracuseStep 2865091 = 4297637) B4297637
theorem B2144323 : Blo 1128631 2144323 := bstep (se 1 (by rfl) ⟨1608242, by rfl⟩ : syracuseStep 2144323 = 3216485) B3216485
theorem B3618893 : Blo 1128631 3618893 := bstep (se 3 (by rfl) ⟨678542, by rfl⟩ : syracuseStep 3618893 = 1357085) B1357085
theorem B2865233 : Blo 1128631 2865233 := bstep (se 2 (by rfl) ⟨1074462, by rfl⟩ : syracuseStep 2865233 = 2148925) B2148925
theorem B2144369 : Blo 1128631 2144369 := bstep (se 2 (by rfl) ⟨804138, by rfl⟩ : syracuseStep 2144369 = 1608277) B1608277
theorem B1128643 : Blo 1128631 1128643 := bstep (se 1 (by rfl) ⟨846482, by rfl⟩ : syracuseStep 1128643 = 1692965) B1692965
theorem B1128659 : Blo 1128631 1128659 := bstep (se 1 (by rfl) ⟨846494, by rfl⟩ : syracuseStep 1128659 = 1692989) B1692989
theorem B1128675 : Blo 1128631 1128675 := bstep (se 1 (by rfl) ⟨846506, by rfl⟩ : syracuseStep 1128675 = 1693013) B1693013
theorem B1128691 : Blo 1128631 1128691 := bstep (se 1 (by rfl) ⟨846518, by rfl⟩ : syracuseStep 1128691 = 1693037) B1693037
theorem B1128707 : Blo 1128631 1128707 := bstep (se 1 (by rfl) ⟨846530, by rfl⟩ : syracuseStep 1128707 = 1693061) B1693061
theorem B3815693 : Blo 1128631 3815693 := bstep (se 3 (by rfl) ⟨715442, by rfl⟩ : syracuseStep 3815693 = 1430885) B1430885
theorem B1128723 : Blo 1128631 1128723 := bstep (se 1 (by rfl) ⟨846542, by rfl⟩ : syracuseStep 1128723 = 1693085) B1693085
theorem B1128739 : Blo 1128631 1128739 := bstep (se 1 (by rfl) ⟨846554, by rfl⟩ : syracuseStep 1128739 = 1693109) B1693109
theorem B1128755 : Blo 1128631 1128755 := bstep (se 1 (by rfl) ⟨846566, by rfl⟩ : syracuseStep 1128755 = 1693133) B1693133
theorem B1128771 : Blo 1128631 1128771 := bstep (se 1 (by rfl) ⟨846578, by rfl⟩ : syracuseStep 1128771 = 1693157) B1693157
theorem B3815747 : Blo 1128631 3815747 := bstep (se 1 (by rfl) ⟨2861810, by rfl⟩ : syracuseStep 3815747 = 5723621) B5723621
theorem B1128787 : Blo 1128631 1128787 := bstep (se 1 (by rfl) ⟨846590, by rfl⟩ : syracuseStep 1128787 = 1693181) B1693181
theorem B1128803 : Blo 1128631 1128803 := bstep (se 1 (by rfl) ⟨846602, by rfl⟩ : syracuseStep 1128803 = 1693205) B1693205
theorem B9648497 : Blo 1128631 9648497 := bstep (se 2 (by rfl) ⟨3618186, by rfl⟩ : syracuseStep 9648497 = 7236373) B7236373
theorem B1128819 : Blo 1128631 1128819 := bstep (se 1 (by rfl) ⟨846614, by rfl⟩ : syracuseStep 1128819 = 1693229) B1693229
theorem B1128835 : Blo 1128631 1128835 := bstep (se 1 (by rfl) ⟨846626, by rfl⟩ : syracuseStep 1128835 = 1693253) B1693253
theorem B2144657 : Blo 1128631 2144657 := bstep (se 2 (by rfl) ⟨804246, by rfl⟩ : syracuseStep 2144657 = 1608493) B1608493
theorem B1128851 : Blo 1128631 1128851 := bstep (se 1 (by rfl) ⟨846638, by rfl⟩ : syracuseStep 1128851 = 1693277) B1693277
theorem B1128867 : Blo 1128631 1128867 := bstep (se 1 (by rfl) ⟨846650, by rfl⟩ : syracuseStep 1128867 = 1693301) B1693301
theorem B1128883 : Blo 1128631 1128883 := bstep (se 1 (by rfl) ⟨846662, by rfl⟩ : syracuseStep 1128883 = 1693325) B1693325
theorem B1128899 : Blo 1128631 1128899 := bstep (se 1 (by rfl) ⟨846674, by rfl⟩ : syracuseStep 1128899 = 1693349) B1693349
theorem B1128915 : Blo 1128631 1128915 := bstep (se 1 (by rfl) ⟨846686, by rfl⟩ : syracuseStep 1128915 = 1693373) B1693373
theorem B1128931 : Blo 1128631 1128931 := bstep (se 1 (by rfl) ⟨846698, by rfl⟩ : syracuseStep 1128931 = 1693397) B1693397
theorem B1128947 : Blo 1128631 1128947 := bstep (se 1 (by rfl) ⟨846710, by rfl⟩ : syracuseStep 1128947 = 1693421) B1693421
theorem B1128963 : Blo 1128631 1128963 := bstep (se 1 (by rfl) ⟨846722, by rfl⟩ : syracuseStep 1128963 = 1693445) B1693445
theorem B5716493 : Blo 1128631 5716493 := bstep (se 3 (by rfl) ⟨1071842, by rfl⟩ : syracuseStep 5716493 = 2143685) B2143685
theorem B1128979 : Blo 1128631 1128979 := bstep (se 1 (by rfl) ⟨846734, by rfl⟩ : syracuseStep 1128979 = 1693469) B1693469
theorem B1128995 : Blo 1128631 1128995 := bstep (se 1 (by rfl) ⟨846746, by rfl⟩ : syracuseStep 1128995 = 1693493) B1693493
theorem B1129011 : Blo 1128631 1129011 := bstep (se 1 (by rfl) ⟨846758, by rfl⟩ : syracuseStep 1129011 = 1693517) B1693517
theorem B1129027 : Blo 1128631 1129027 := bstep (se 1 (by rfl) ⟨846770, by rfl⟩ : syracuseStep 1129027 = 1693541) B1693541
theorem B3816017 : Blo 1128631 3816017 := bstep (se 2 (by rfl) ⟨1431006, by rfl⟩ : syracuseStep 3816017 = 2862013) B2862013
theorem B1129043 : Blo 1128631 1129043 := bstep (se 1 (by rfl) ⟨846782, by rfl⟩ : syracuseStep 1129043 = 1693565) B1693565
theorem B1129059 : Blo 1128631 1129059 := bstep (se 1 (by rfl) ⟨846794, by rfl⟩ : syracuseStep 1129059 = 1693589) B1693589
theorem B1129075 : Blo 1128631 1129075 := bstep (se 1 (by rfl) ⟨846806, by rfl⟩ : syracuseStep 1129075 = 1693613) B1693613
theorem B1129091 : Blo 1128631 1129091 := bstep (se 1 (by rfl) ⟨846818, by rfl⟩ : syracuseStep 1129091 = 1693637) B1693637
theorem B1718929 : Blo 1128631 1718929 := bstep (se 2 (by rfl) ⟨644598, by rfl⟩ : syracuseStep 1718929 = 1289197) B1289197
theorem B1129107 : Blo 1128631 1129107 := bstep (se 1 (by rfl) ⟨846830, by rfl⟩ : syracuseStep 1129107 = 1693661) B1693661
theorem B1129123 : Blo 1128631 1129123 := bstep (se 1 (by rfl) ⟨846842, by rfl⟩ : syracuseStep 1129123 = 1693685) B1693685
theorem B1129139 : Blo 1128631 1129139 := bstep (se 1 (by rfl) ⟨846854, by rfl⟩ : syracuseStep 1129139 = 1693709) B1693709
theorem B1129155 : Blo 1128631 1129155 := bstep (se 1 (by rfl) ⟨846866, by rfl⟩ : syracuseStep 1129155 = 1693733) B1693733
theorem B2898641 : Blo 1128631 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1129171 : Blo 1128631 1129171 := bstep (se 1 (by rfl) ⟨846878, by rfl⟩ : syracuseStep 1129171 = 1693757) B1693757
theorem B1129187 : Blo 1128631 1129187 := bstep (se 1 (by rfl) ⟨846890, by rfl⟩ : syracuseStep 1129187 = 1693781) B1693781
theorem B1129203 : Blo 1128631 1129203 := bstep (se 1 (by rfl) ⟨846902, by rfl⟩ : syracuseStep 1129203 = 1693805) B1693805
theorem B1129219 : Blo 1128631 1129219 := bstep (se 1 (by rfl) ⟨846914, by rfl⟩ : syracuseStep 1129219 = 1693829) B1693829
theorem B1129235 : Blo 1128631 1129235 := bstep (se 1 (by rfl) ⟨846926, by rfl⟩ : syracuseStep 1129235 = 1693853) B1693853
theorem B1129251 : Blo 1128631 1129251 := bstep (se 1 (by rfl) ⟨846938, by rfl⟩ : syracuseStep 1129251 = 1693877) B1693877
theorem B1358627 : Blo 1128631 1358627 := bstep (se 1 (by rfl) ⟨1018970, by rfl⟩ : syracuseStep 1358627 = 2037941) B2037941
theorem B1129267 : Blo 1128631 1129267 := bstep (se 1 (by rfl) ⟨846950, by rfl⟩ : syracuseStep 1129267 = 1693901) B1693901
theorem B1129283 : Blo 1128631 1129283 := bstep (se 1 (by rfl) ⟨846962, by rfl⟩ : syracuseStep 1129283 = 1693925) B1693925
theorem B1129299 : Blo 1128631 1129299 := bstep (se 1 (by rfl) ⟨846974, by rfl⟩ : syracuseStep 1129299 = 1693949) B1693949
theorem B1129315 : Blo 1128631 1129315 := bstep (se 1 (by rfl) ⟨846986, by rfl⟩ : syracuseStep 1129315 = 1693973) B1693973
theorem B1129331 : Blo 1128631 1129331 := bstep (se 1 (by rfl) ⟨846998, by rfl⟩ : syracuseStep 1129331 = 1693997) B1693997
theorem B1129347 : Blo 1128631 1129347 := bstep (se 1 (by rfl) ⟨847010, by rfl⟩ : syracuseStep 1129347 = 1694021) B1694021
theorem B1129363 : Blo 1128631 1129363 := bstep (se 1 (by rfl) ⟨847022, by rfl⟩ : syracuseStep 1129363 = 1694045) B1694045
theorem B1129379 : Blo 1128631 1129379 := bstep (se 1 (by rfl) ⟨847034, by rfl⟩ : syracuseStep 1129379 = 1694069) B1694069
theorem B1129395 : Blo 1128631 1129395 := bstep (se 1 (by rfl) ⟨847046, by rfl⟩ : syracuseStep 1129395 = 1694093) B1694093
theorem B1129411 : Blo 1128631 1129411 := bstep (se 1 (by rfl) ⟨847058, by rfl⟩ : syracuseStep 1129411 = 1694117) B1694117
theorem B1129427 : Blo 1128631 1129427 := bstep (se 1 (by rfl) ⟨847070, by rfl⟩ : syracuseStep 1129427 = 1694141) B1694141
theorem B1129443 : Blo 1128631 1129443 := bstep (se 1 (by rfl) ⟨847082, by rfl⟩ : syracuseStep 1129443 = 1694165) B1694165
theorem B1129459 : Blo 1128631 1129459 := bstep (se 1 (by rfl) ⟨847094, by rfl⟩ : syracuseStep 1129459 = 1694189) B1694189
theorem B1129475 : Blo 1128631 1129475 := bstep (se 1 (by rfl) ⟨847106, by rfl⟩ : syracuseStep 1129475 = 1694213) B1694213
theorem B1129491 : Blo 1128631 1129491 := bstep (se 1 (by rfl) ⟨847118, by rfl⟩ : syracuseStep 1129491 = 1694237) B1694237
theorem B1129507 : Blo 1128631 1129507 := bstep (se 1 (by rfl) ⟨847130, by rfl⟩ : syracuseStep 1129507 = 1694261) B1694261
theorem B2866225 : Blo 1128631 2866225 := bstep (se 2 (by rfl) ⟨1074834, by rfl⟩ : syracuseStep 2866225 = 2149669) B2149669
theorem B1129523 : Blo 1128631 1129523 := bstep (se 1 (by rfl) ⟨847142, by rfl⟩ : syracuseStep 1129523 = 1694285) B1694285
theorem B55065653 : Blo 1128631 55065653 := bstep (se 5 (by rfl) ⟨2581202, by rfl⟩ : syracuseStep 55065653 = 5162405) B5162405
theorem B1129539 : Blo 1128631 1129539 := bstep (se 1 (by rfl) ⟨847154, by rfl⟩ : syracuseStep 1129539 = 1694309) B1694309
theorem B1129555 : Blo 1128631 1129555 := bstep (se 1 (by rfl) ⟨847166, by rfl⟩ : syracuseStep 1129555 = 1694333) B1694333
theorem B1129571 : Blo 1128631 1129571 := bstep (se 1 (by rfl) ⟨847178, by rfl⟩ : syracuseStep 1129571 = 1694357) B1694357
theorem B2145379 : Blo 1128631 2145379 := bstep (se 1 (by rfl) ⟨1609034, by rfl⟩ : syracuseStep 2145379 = 3218069) B3218069
theorem B3816557 : Blo 1128631 3816557 := bstep (se 3 (by rfl) ⟨715604, by rfl⟩ : syracuseStep 3816557 = 1431209) B1431209
theorem B1129587 : Blo 1128631 1129587 := bstep (se 1 (by rfl) ⟨847190, by rfl⟩ : syracuseStep 1129587 = 1694381) B1694381
theorem B1129603 : Blo 1128631 1129603 := bstep (se 1 (by rfl) ⟨847202, by rfl⟩ : syracuseStep 1129603 = 1694405) B1694405
theorem B3619981 : Blo 1128631 3619981 := bstep (se 3 (by rfl) ⟨678746, by rfl⟩ : syracuseStep 3619981 = 1357493) B1357493
theorem B1129619 : Blo 1128631 1129619 := bstep (se 1 (by rfl) ⟨847214, by rfl⟩ : syracuseStep 1129619 = 1694429) B1694429
theorem B1129635 : Blo 1128631 1129635 := bstep (se 1 (by rfl) ⟨847226, by rfl⟩ : syracuseStep 1129635 = 1694453) B1694453
theorem B3816611 : Blo 1128631 3816611 := bstep (se 1 (by rfl) ⟨2862458, by rfl⟩ : syracuseStep 3816611 = 5724917) B5724917
theorem B1129651 : Blo 1128631 1129651 := bstep (se 1 (by rfl) ⟨847238, by rfl⟩ : syracuseStep 1129651 = 1694477) B1694477
theorem B1129667 : Blo 1128631 1129667 := bstep (se 1 (by rfl) ⟨847250, by rfl⟩ : syracuseStep 1129667 = 1694501) B1694501
theorem B1129683 : Blo 1128631 1129683 := bstep (se 1 (by rfl) ⟨847262, by rfl⟩ : syracuseStep 1129683 = 1694525) B1694525
theorem B1129699 : Blo 1128631 1129699 := bstep (se 1 (by rfl) ⟨847274, by rfl⟩ : syracuseStep 1129699 = 1694549) B1694549
theorem B1129715 : Blo 1128631 1129715 := bstep (se 1 (by rfl) ⟨847286, by rfl⟩ : syracuseStep 1129715 = 1694573) B1694573
theorem B1129731 : Blo 1128631 1129731 := bstep (se 1 (by rfl) ⟨847298, by rfl⟩ : syracuseStep 1129731 = 1694597) B1694597
theorem B1129747 : Blo 1128631 1129747 := bstep (se 1 (by rfl) ⟨847310, by rfl⟩ : syracuseStep 1129747 = 1694621) B1694621
theorem B1129763 : Blo 1128631 1129763 := bstep (se 1 (by rfl) ⟨847322, by rfl⟩ : syracuseStep 1129763 = 1694645) B1694645
theorem B2178353 : Blo 1128631 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B1129779 : Blo 1128631 1129779 := bstep (se 1 (by rfl) ⟨847334, by rfl⟩ : syracuseStep 1129779 = 1694669) B1694669
theorem B1129795 : Blo 1128631 1129795 := bstep (se 1 (by rfl) ⟨847346, by rfl⟩ : syracuseStep 1129795 = 1694693) B1694693
theorem B2866499 : Blo 1128631 2866499 := bstep (se 1 (by rfl) ⟨2149874, by rfl⟩ : syracuseStep 2866499 = 4299749) B4299749
theorem B1129811 : Blo 1128631 1129811 := bstep (se 1 (by rfl) ⟨847358, by rfl⟩ : syracuseStep 1129811 = 1694717) B1694717
theorem B1129827 : Blo 1128631 1129827 := bstep (se 1 (by rfl) ⟨847370, by rfl⟩ : syracuseStep 1129827 = 1694741) B1694741
theorem B1129843 : Blo 1128631 1129843 := bstep (se 1 (by rfl) ⟨847382, by rfl⟩ : syracuseStep 1129843 = 1694765) B1694765
theorem B1129859 : Blo 1128631 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B1129875 : Blo 1128631 1129875 := bstep (se 1 (by rfl) ⟨847406, by rfl⟩ : syracuseStep 1129875 = 1694813) B1694813
theorem B1129891 : Blo 1128631 1129891 := bstep (se 1 (by rfl) ⟨847418, by rfl⟩ : syracuseStep 1129891 = 1694837) B1694837
theorem B3816881 : Blo 1128631 3816881 := bstep (se 2 (by rfl) ⟨1431330, by rfl⟩ : syracuseStep 3816881 = 2862661) B2862661
theorem B1129907 : Blo 1128631 1129907 := bstep (se 1 (by rfl) ⟨847430, by rfl⟩ : syracuseStep 1129907 = 1694861) B1694861
theorem B1129923 : Blo 1128631 1129923 := bstep (se 1 (by rfl) ⟨847442, by rfl⟩ : syracuseStep 1129923 = 1694885) B1694885
theorem B1129939 : Blo 1128631 1129939 := bstep (se 1 (by rfl) ⟨847454, by rfl⟩ : syracuseStep 1129939 = 1694909) B1694909
theorem B1129955 : Blo 1128631 1129955 := bstep (se 1 (by rfl) ⟨847466, by rfl⟩ : syracuseStep 1129955 = 1694933) B1694933
theorem B1129971 : Blo 1128631 1129971 := bstep (se 1 (by rfl) ⟨847478, by rfl⟩ : syracuseStep 1129971 = 1694957) B1694957
theorem B1129987 : Blo 1128631 1129987 := bstep (se 1 (by rfl) ⟨847490, by rfl⟩ : syracuseStep 1129987 = 1694981) B1694981
theorem B2866691 : Blo 1128631 2866691 := bstep (se 1 (by rfl) ⟨2150018, by rfl⟩ : syracuseStep 2866691 = 4300037) B4300037
theorem B1130003 : Blo 1128631 1130003 := bstep (se 1 (by rfl) ⟨847502, by rfl⟩ : syracuseStep 1130003 = 1695005) B1695005
theorem B1130019 : Blo 1128631 1130019 := bstep (se 1 (by rfl) ⟨847514, by rfl⟩ : syracuseStep 1130019 = 1695029) B1695029
theorem B2145827 : Blo 1128631 2145827 := bstep (se 1 (by rfl) ⟨1609370, by rfl⟩ : syracuseStep 2145827 = 3218741) B3218741
theorem B1130035 : Blo 1128631 1130035 := bstep (se 1 (by rfl) ⟨847526, by rfl⟩ : syracuseStep 1130035 = 1695053) B1695053
theorem B1130051 : Blo 1128631 1130051 := bstep (se 1 (by rfl) ⟨847538, by rfl⟩ : syracuseStep 1130051 = 1695077) B1695077
theorem B1130067 : Blo 1128631 1130067 := bstep (se 1 (by rfl) ⟨847550, by rfl⟩ : syracuseStep 1130067 = 1695101) B1695101
theorem B1130083 : Blo 1128631 1130083 := bstep (se 1 (by rfl) ⟨847562, by rfl⟩ : syracuseStep 1130083 = 1695125) B1695125
theorem B1130099 : Blo 1128631 1130099 := bstep (se 1 (by rfl) ⟨847574, by rfl⟩ : syracuseStep 1130099 = 1695149) B1695149
theorem B1130115 : Blo 1128631 1130115 := bstep (se 1 (by rfl) ⟨847586, by rfl⟩ : syracuseStep 1130115 = 1695173) B1695173
theorem B1130131 : Blo 1128631 1130131 := bstep (se 1 (by rfl) ⟨847598, by rfl⟩ : syracuseStep 1130131 = 1695197) B1695197
theorem B1130147 : Blo 1128631 1130147 := bstep (se 1 (by rfl) ⟨847610, by rfl⟩ : syracuseStep 1130147 = 1695221) B1695221
theorem B1130163 : Blo 1128631 1130163 := bstep (se 1 (by rfl) ⟨847622, by rfl⟩ : syracuseStep 1130163 = 1695245) B1695245
theorem B1130179 : Blo 1128631 1130179 := bstep (se 1 (by rfl) ⟨847634, by rfl⟩ : syracuseStep 1130179 = 1695269) B1695269
theorem B1130195 : Blo 1128631 1130195 := bstep (se 1 (by rfl) ⟨847646, by rfl⟩ : syracuseStep 1130195 = 1695293) B1695293
theorem B1130211 : Blo 1128631 1130211 := bstep (se 1 (by rfl) ⟨847658, by rfl⟩ : syracuseStep 1130211 = 1695317) B1695317
theorem B1130227 : Blo 1128631 1130227 := bstep (se 1 (by rfl) ⟨847670, by rfl⟩ : syracuseStep 1130227 = 1695341) B1695341
theorem B1130243 : Blo 1128631 1130243 := bstep (se 1 (by rfl) ⟨847682, by rfl⟩ : syracuseStep 1130243 = 1695365) B1695365
theorem B1130259 : Blo 1128631 1130259 := bstep (se 1 (by rfl) ⟨847694, by rfl⟩ : syracuseStep 1130259 = 1695389) B1695389
theorem B1130275 : Blo 1128631 1130275 := bstep (se 1 (by rfl) ⟨847706, by rfl⟩ : syracuseStep 1130275 = 1695413) B1695413
theorem B1130291 : Blo 1128631 1130291 := bstep (se 1 (by rfl) ⟨847718, by rfl⟩ : syracuseStep 1130291 = 1695437) B1695437
theorem B1130307 : Blo 1128631 1130307 := bstep (se 1 (by rfl) ⟨847730, by rfl⟩ : syracuseStep 1130307 = 1695461) B1695461
theorem B2146115 : Blo 1128631 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B1130323 : Blo 1128631 1130323 := bstep (se 1 (by rfl) ⟨847742, by rfl⟩ : syracuseStep 1130323 = 1695485) B1695485
theorem B1130339 : Blo 1128631 1130339 := bstep (se 1 (by rfl) ⟨847754, by rfl⟩ : syracuseStep 1130339 = 1695509) B1695509
theorem B1130355 : Blo 1128631 1130355 := bstep (se 1 (by rfl) ⟨847766, by rfl⟩ : syracuseStep 1130355 = 1695533) B1695533
theorem B1130371 : Blo 1128631 1130371 := bstep (se 1 (by rfl) ⟨847778, by rfl⟩ : syracuseStep 1130371 = 1695557) B1695557
theorem B1130387 : Blo 1128631 1130387 := bstep (se 1 (by rfl) ⟨847790, by rfl⟩ : syracuseStep 1130387 = 1695581) B1695581
theorem B1130403 : Blo 1128631 1130403 := bstep (se 1 (by rfl) ⟨847802, by rfl⟩ : syracuseStep 1130403 = 1695605) B1695605
theorem B1130419 : Blo 1128631 1130419 := bstep (se 1 (by rfl) ⟨847814, by rfl⟩ : syracuseStep 1130419 = 1695629) B1695629
theorem B1130435 : Blo 1128631 1130435 := bstep (se 1 (by rfl) ⟨847826, by rfl⟩ : syracuseStep 1130435 = 1695653) B1695653
theorem B3817421 : Blo 1128631 3817421 := bstep (se 3 (by rfl) ⟨715766, by rfl⟩ : syracuseStep 3817421 = 1431533) B1431533
theorem B1130451 : Blo 1128631 1130451 := bstep (se 1 (by rfl) ⟨847838, by rfl⟩ : syracuseStep 1130451 = 1695677) B1695677
theorem B1130467 : Blo 1128631 1130467 := bstep (se 1 (by rfl) ⟨847850, by rfl⟩ : syracuseStep 1130467 = 1695701) B1695701
theorem B1130483 : Blo 1128631 1130483 := bstep (se 1 (by rfl) ⟨847862, by rfl⟩ : syracuseStep 1130483 = 1695725) B1695725
theorem B1130499 : Blo 1128631 1130499 := bstep (se 1 (by rfl) ⟨847874, by rfl⟩ : syracuseStep 1130499 = 1695749) B1695749
theorem B3817475 : Blo 1128631 3817475 := bstep (se 1 (by rfl) ⟨2863106, by rfl⟩ : syracuseStep 3817475 = 5726213) B5726213
theorem B1130515 : Blo 1128631 1130515 := bstep (se 1 (by rfl) ⟨847886, by rfl⟩ : syracuseStep 1130515 = 1695773) B1695773
theorem B1130531 : Blo 1128631 1130531 := bstep (se 1 (by rfl) ⟨847898, by rfl⟩ : syracuseStep 1130531 = 1695797) B1695797
theorem B1130547 : Blo 1128631 1130547 := bstep (se 1 (by rfl) ⟨847910, by rfl⟩ : syracuseStep 1130547 = 1695821) B1695821
theorem B1130563 : Blo 1128631 1130563 := bstep (se 1 (by rfl) ⟨847922, by rfl⟩ : syracuseStep 1130563 = 1695845) B1695845
theorem B2539601 : Blo 1128631 2539601 := bstep (se 2 (by rfl) ⟨952350, by rfl⟩ : syracuseStep 2539601 = 1904701) B1904701
theorem B2179153 : Blo 1128631 2179153 := bstep (se 2 (by rfl) ⟨817182, by rfl⟩ : syracuseStep 2179153 = 1634365) B1634365
theorem B1130579 : Blo 1128631 1130579 := bstep (se 1 (by rfl) ⟨847934, by rfl⟩ : syracuseStep 1130579 = 1695869) B1695869
theorem B2539619 : Blo 1128631 2539619 := bstep (se 1 (by rfl) ⟨1904714, by rfl⟩ : syracuseStep 2539619 = 3809429) B3809429
theorem B1130595 : Blo 1128631 1130595 := bstep (se 1 (by rfl) ⟨847946, by rfl⟩ : syracuseStep 1130595 = 1695893) B1695893
theorem B1130611 : Blo 1128631 1130611 := bstep (se 1 (by rfl) ⟨847958, by rfl⟩ : syracuseStep 1130611 = 1695917) B1695917
theorem B1130627 : Blo 1128631 1130627 := bstep (se 1 (by rfl) ⟨847970, by rfl⟩ : syracuseStep 1130627 = 1695941) B1695941
theorem B1130643 : Blo 1128631 1130643 := bstep (se 1 (by rfl) ⟨847982, by rfl⟩ : syracuseStep 1130643 = 1695965) B1695965
theorem B1130659 : Blo 1128631 1130659 := bstep (se 1 (by rfl) ⟨847994, by rfl⟩ : syracuseStep 1130659 = 1695989) B1695989
theorem B1130675 : Blo 1128631 1130675 := bstep (se 1 (by rfl) ⟨848006, by rfl⟩ : syracuseStep 1130675 = 1696013) B1696013
theorem B1130691 : Blo 1128631 1130691 := bstep (se 1 (by rfl) ⟨848018, by rfl⟩ : syracuseStep 1130691 = 1696037) B1696037
theorem B1130707 : Blo 1128631 1130707 := bstep (se 1 (by rfl) ⟨848030, by rfl⟩ : syracuseStep 1130707 = 1696061) B1696061
theorem B2900195 : Blo 1128631 2900195 := bstep (se 1 (by rfl) ⟨2175146, by rfl⟩ : syracuseStep 2900195 = 4350293) B4350293
theorem B1130723 : Blo 1128631 1130723 := bstep (se 1 (by rfl) ⟨848042, by rfl⟩ : syracuseStep 1130723 = 1696085) B1696085
theorem B1130739 : Blo 1128631 1130739 := bstep (se 1 (by rfl) ⟨848054, by rfl⟩ : syracuseStep 1130739 = 1696109) B1696109
theorem B1130755 : Blo 1128631 1130755 := bstep (se 1 (by rfl) ⟨848066, by rfl⟩ : syracuseStep 1130755 = 1696133) B1696133
theorem B3817745 : Blo 1128631 3817745 := bstep (se 2 (by rfl) ⟨1431654, by rfl⟩ : syracuseStep 3817745 = 2863309) B2863309
theorem B1130771 : Blo 1128631 1130771 := bstep (se 1 (by rfl) ⟨848078, by rfl⟩ : syracuseStep 1130771 = 1696157) B1696157
theorem B1130787 : Blo 1128631 1130787 := bstep (se 1 (by rfl) ⟨848090, by rfl⟩ : syracuseStep 1130787 = 1696181) B1696181
theorem B1130803 : Blo 1128631 1130803 := bstep (se 1 (by rfl) ⟨848102, by rfl⟩ : syracuseStep 1130803 = 1696205) B1696205
theorem B1130819 : Blo 1128631 1130819 := bstep (se 1 (by rfl) ⟨848114, by rfl⟩ : syracuseStep 1130819 = 1696229) B1696229
theorem B6111557 : Blo 1128631 6111557 := bstep (se 4 (by rfl) ⟨572958, by rfl⟩ : syracuseStep 6111557 = 1145917) B1145917
theorem B1130835 : Blo 1128631 1130835 := bstep (se 1 (by rfl) ⟨848126, by rfl⟩ : syracuseStep 1130835 = 1696253) B1696253
theorem B1130851 : Blo 1128631 1130851 := bstep (se 1 (by rfl) ⟨848138, by rfl⟩ : syracuseStep 1130851 = 1696277) B1696277
theorem B2539889 : Blo 1128631 2539889 := bstep (se 2 (by rfl) ⟨952458, by rfl⟩ : syracuseStep 2539889 = 1904917) B1904917
theorem B1130867 : Blo 1128631 1130867 := bstep (se 1 (by rfl) ⟨848150, by rfl⟩ : syracuseStep 1130867 = 1696301) B1696301
theorem B2539907 : Blo 1128631 2539907 := bstep (se 1 (by rfl) ⟨1904930, by rfl⟩ : syracuseStep 2539907 = 3809861) B3809861
theorem B1130883 : Blo 1128631 1130883 := bstep (se 1 (by rfl) ⟨848162, by rfl⟩ : syracuseStep 1130883 = 1696325) B1696325
theorem B1130899 : Blo 1128631 1130899 := bstep (se 1 (by rfl) ⟨848174, by rfl⟩ : syracuseStep 1130899 = 1696349) B1696349
theorem B1130915 : Blo 1128631 1130915 := bstep (se 1 (by rfl) ⟨848186, by rfl⟩ : syracuseStep 1130915 = 1696373) B1696373
theorem B1130931 : Blo 1128631 1130931 := bstep (se 1 (by rfl) ⟨848198, by rfl⟩ : syracuseStep 1130931 = 1696397) B1696397
theorem B1130947 : Blo 1128631 1130947 := bstep (se 1 (by rfl) ⟨848210, by rfl⟩ : syracuseStep 1130947 = 1696421) B1696421
theorem B1130963 : Blo 1128631 1130963 := bstep (se 1 (by rfl) ⟨848222, by rfl⟩ : syracuseStep 1130963 = 1696445) B1696445
theorem B1130979 : Blo 1128631 1130979 := bstep (se 1 (by rfl) ⟨848234, by rfl⟩ : syracuseStep 1130979 = 1696469) B1696469
theorem B1130995 : Blo 1128631 1130995 := bstep (se 1 (by rfl) ⟨848246, by rfl⟩ : syracuseStep 1130995 = 1696493) B1696493
theorem B1131011 : Blo 1128631 1131011 := bstep (se 1 (by rfl) ⟨848258, by rfl⟩ : syracuseStep 1131011 = 1696517) B1696517
theorem B1131027 : Blo 1128631 1131027 := bstep (se 1 (by rfl) ⟨848270, by rfl⟩ : syracuseStep 1131027 = 1696541) B1696541
theorem B1131043 : Blo 1128631 1131043 := bstep (se 1 (by rfl) ⟨848282, by rfl⟩ : syracuseStep 1131043 = 1696565) B1696565
theorem B1131059 : Blo 1128631 1131059 := bstep (se 1 (by rfl) ⟨848294, by rfl⟩ : syracuseStep 1131059 = 1696589) B1696589
theorem B1131075 : Blo 1128631 1131075 := bstep (se 1 (by rfl) ⟨848306, by rfl⟩ : syracuseStep 1131075 = 1696613) B1696613
theorem B1720913 : Blo 1128631 1720913 := bstep (se 2 (by rfl) ⟨645342, by rfl⟩ : syracuseStep 1720913 = 1290685) B1290685
theorem B1131091 : Blo 1128631 1131091 := bstep (se 1 (by rfl) ⟨848318, by rfl⟩ : syracuseStep 1131091 = 1696637) B1696637
theorem B1131107 : Blo 1128631 1131107 := bstep (se 1 (by rfl) ⟨848330, by rfl⟩ : syracuseStep 1131107 = 1696661) B1696661
theorem B1131123 : Blo 1128631 1131123 := bstep (se 1 (by rfl) ⟨848342, by rfl⟩ : syracuseStep 1131123 = 1696685) B1696685
theorem B1131139 : Blo 1128631 1131139 := bstep (se 1 (by rfl) ⟨848354, by rfl⟩ : syracuseStep 1131139 = 1696709) B1696709
theorem B2540177 : Blo 1128631 2540177 := bstep (se 2 (by rfl) ⟨952566, by rfl⟩ : syracuseStep 2540177 = 1905133) B1905133
theorem B1131155 : Blo 1128631 1131155 := bstep (se 1 (by rfl) ⟨848366, by rfl⟩ : syracuseStep 1131155 = 1696733) B1696733
theorem B2540195 : Blo 1128631 2540195 := bstep (se 1 (by rfl) ⟨1905146, by rfl⟩ : syracuseStep 2540195 = 3810293) B3810293
theorem B1131171 : Blo 1128631 1131171 := bstep (se 1 (by rfl) ⟨848378, by rfl⟩ : syracuseStep 1131171 = 1696757) B1696757
theorem B1131187 : Blo 1128631 1131187 := bstep (se 1 (by rfl) ⟨848390, by rfl⟩ : syracuseStep 1131187 = 1696781) B1696781
theorem B1131203 : Blo 1128631 1131203 := bstep (se 1 (by rfl) ⟨848402, by rfl⟩ : syracuseStep 1131203 = 1696805) B1696805
theorem B6439621 : Blo 1128631 6439621 := bstep (se 4 (by rfl) ⟨603714, by rfl⟩ : syracuseStep 6439621 = 1207429) B1207429
theorem B1131219 : Blo 1128631 1131219 := bstep (se 1 (by rfl) ⟨848414, by rfl⟩ : syracuseStep 1131219 = 1696829) B1696829
theorem B1131235 : Blo 1128631 1131235 := bstep (se 1 (by rfl) ⟨848426, by rfl⟩ : syracuseStep 1131235 = 1696853) B1696853
theorem B2147057 : Blo 1128631 2147057 := bstep (se 2 (by rfl) ⟨805146, by rfl⟩ : syracuseStep 2147057 = 1610293) B1610293
theorem B1131251 : Blo 1128631 1131251 := bstep (se 1 (by rfl) ⟨848438, by rfl⟩ : syracuseStep 1131251 = 1696877) B1696877
theorem B1131267 : Blo 1128631 1131267 := bstep (se 1 (by rfl) ⟨848450, by rfl⟩ : syracuseStep 1131267 = 1696901) B1696901
theorem B1131283 : Blo 1128631 1131283 := bstep (se 1 (by rfl) ⟨848462, by rfl⟩ : syracuseStep 1131283 = 1696925) B1696925
theorem B1131299 : Blo 1128631 1131299 := bstep (se 1 (by rfl) ⟨848474, by rfl⟩ : syracuseStep 1131299 = 1696949) B1696949
theorem B1360675 : Blo 1128631 1360675 := bstep (se 1 (by rfl) ⟨1020506, by rfl⟩ : syracuseStep 1360675 = 2041013) B2041013
theorem B3818285 : Blo 1128631 3818285 := bstep (se 3 (by rfl) ⟨715928, by rfl⟩ : syracuseStep 3818285 = 1431857) B1431857
theorem B1131315 : Blo 1128631 1131315 := bstep (se 1 (by rfl) ⟨848486, by rfl⟩ : syracuseStep 1131315 = 1696973) B1696973
theorem B1131331 : Blo 1128631 1131331 := bstep (se 1 (by rfl) ⟨848498, by rfl⟩ : syracuseStep 1131331 = 1696997) B1696997
theorem B1131347 : Blo 1128631 1131347 := bstep (se 1 (by rfl) ⟨848510, by rfl⟩ : syracuseStep 1131347 = 1697021) B1697021
theorem B3818339 : Blo 1128631 3818339 := bstep (se 1 (by rfl) ⟨2863754, by rfl⟩ : syracuseStep 3818339 = 5727509) B5727509
theorem B1131363 : Blo 1128631 1131363 := bstep (se 1 (by rfl) ⟨848522, by rfl⟩ : syracuseStep 1131363 = 1697045) B1697045
theorem B1131379 : Blo 1128631 1131379 := bstep (se 1 (by rfl) ⟨848534, by rfl⟩ : syracuseStep 1131379 = 1697069) B1697069
theorem B3621763 : Blo 1128631 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B1131395 : Blo 1128631 1131395 := bstep (se 1 (by rfl) ⟨848546, by rfl⟩ : syracuseStep 1131395 = 1697093) B1697093
theorem B1131411 : Blo 1128631 1131411 := bstep (se 1 (by rfl) ⟨848558, by rfl⟩ : syracuseStep 1131411 = 1697117) B1697117
theorem B1131427 : Blo 1128631 1131427 := bstep (se 1 (by rfl) ⟨848570, by rfl⟩ : syracuseStep 1131427 = 1697141) B1697141
theorem B2540465 : Blo 1128631 2540465 := bstep (se 2 (by rfl) ⟨952674, by rfl⟩ : syracuseStep 2540465 = 1905349) B1905349
theorem B1131443 : Blo 1128631 1131443 := bstep (se 1 (by rfl) ⟨848582, by rfl⟩ : syracuseStep 1131443 = 1697165) B1697165
theorem B2540483 : Blo 1128631 2540483 := bstep (se 1 (by rfl) ⟨1905362, by rfl⟩ : syracuseStep 2540483 = 3810725) B3810725
theorem B3621827 : Blo 1128631 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B1131459 : Blo 1128631 1131459 := bstep (se 1 (by rfl) ⟨848594, by rfl⟩ : syracuseStep 1131459 = 1697189) B1697189
theorem B1131475 : Blo 1128631 1131475 := bstep (se 1 (by rfl) ⟨848606, by rfl⟩ : syracuseStep 1131475 = 1697213) B1697213
theorem B1131491 : Blo 1128631 1131491 := bstep (se 1 (by rfl) ⟨848618, by rfl⟩ : syracuseStep 1131491 = 1697237) B1697237
theorem B1131507 : Blo 1128631 1131507 := bstep (se 1 (by rfl) ⟨848630, by rfl⟩ : syracuseStep 1131507 = 1697261) B1697261
theorem B1131523 : Blo 1128631 1131523 := bstep (se 1 (by rfl) ⟨848642, by rfl⟩ : syracuseStep 1131523 = 1697285) B1697285
theorem B3621905 : Blo 1128631 3621905 := bstep (se 2 (by rfl) ⟨1358214, by rfl⟩ : syracuseStep 3621905 = 2716429) B2716429
theorem B1131539 : Blo 1128631 1131539 := bstep (se 1 (by rfl) ⟨848654, by rfl⟩ : syracuseStep 1131539 = 1697309) B1697309
theorem B1131555 : Blo 1128631 1131555 := bstep (se 1 (by rfl) ⟨848666, by rfl⟩ : syracuseStep 1131555 = 1697333) B1697333
theorem B1131571 : Blo 1128631 1131571 := bstep (se 1 (by rfl) ⟨848678, by rfl⟩ : syracuseStep 1131571 = 1697357) B1697357
theorem B1131587 : Blo 1128631 1131587 := bstep (se 1 (by rfl) ⟨848690, by rfl⟩ : syracuseStep 1131587 = 1697381) B1697381
theorem B5424205 : Blo 1128631 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B1131603 : Blo 1128631 1131603 := bstep (se 1 (by rfl) ⟨848702, by rfl⟩ : syracuseStep 1131603 = 1697405) B1697405
theorem B1131619 : Blo 1128631 1131619 := bstep (se 1 (by rfl) ⟨848714, by rfl⟩ : syracuseStep 1131619 = 1697429) B1697429
theorem B3818609 : Blo 1128631 3818609 := bstep (se 2 (by rfl) ⟨1431978, by rfl⟩ : syracuseStep 3818609 = 2863957) B2863957
theorem B1131635 : Blo 1128631 1131635 := bstep (se 1 (by rfl) ⟨848726, by rfl⟩ : syracuseStep 1131635 = 1697453) B1697453
theorem B1721459 : Blo 1128631 1721459 := bstep (se 1 (by rfl) ⟨1291094, by rfl⟩ : syracuseStep 1721459 = 2582189) B2582189
theorem B1131651 : Blo 1128631 1131651 := bstep (se 1 (by rfl) ⟨848738, by rfl⟩ : syracuseStep 1131651 = 1697477) B1697477
theorem B1885331 : Blo 1128631 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B1131667 : Blo 1128631 1131667 := bstep (se 1 (by rfl) ⟨848750, by rfl⟩ : syracuseStep 1131667 = 1697501) B1697501
theorem B1131683 : Blo 1128631 1131683 := bstep (se 1 (by rfl) ⟨848762, by rfl⟩ : syracuseStep 1131683 = 1697525) B1697525
theorem B1131699 : Blo 1128631 1131699 := bstep (se 1 (by rfl) ⟨848774, by rfl⟩ : syracuseStep 1131699 = 1697549) B1697549
theorem B2901187 : Blo 1128631 2901187 := bstep (se 1 (by rfl) ⟨2175890, by rfl⟩ : syracuseStep 2901187 = 4351781) B4351781
theorem B1131715 : Blo 1128631 1131715 := bstep (se 1 (by rfl) ⟨848786, by rfl⟩ : syracuseStep 1131715 = 1697573) B1697573
theorem B2540753 : Blo 1128631 2540753 := bstep (se 2 (by rfl) ⟨952782, by rfl⟩ : syracuseStep 2540753 = 1905565) B1905565
theorem B1131731 : Blo 1128631 1131731 := bstep (se 1 (by rfl) ⟨848798, by rfl⟩ : syracuseStep 1131731 = 1697597) B1697597
theorem B1721569 : Blo 1128631 1721569 := bstep (se 2 (by rfl) ⟨645588, by rfl⟩ : syracuseStep 1721569 = 1291177) B1291177
theorem B2540771 : Blo 1128631 2540771 := bstep (se 1 (by rfl) ⟨1905578, by rfl⟩ : syracuseStep 2540771 = 3811157) B3811157
theorem B1131747 : Blo 1128631 1131747 := bstep (se 1 (by rfl) ⟨848810, by rfl⟩ : syracuseStep 1131747 = 1697621) B1697621
theorem B1131763 : Blo 1128631 1131763 := bstep (se 1 (by rfl) ⟨848822, by rfl⟩ : syracuseStep 1131763 = 1697645) B1697645
theorem B1131779 : Blo 1128631 1131779 := bstep (se 1 (by rfl) ⟨848834, by rfl⟩ : syracuseStep 1131779 = 1697669) B1697669
theorem B1131795 : Blo 1128631 1131795 := bstep (se 1 (by rfl) ⟨848846, by rfl⟩ : syracuseStep 1131795 = 1697693) B1697693
theorem B1131811 : Blo 1128631 1131811 := bstep (se 1 (by rfl) ⟨848858, by rfl⟩ : syracuseStep 1131811 = 1697717) B1697717
theorem B1131827 : Blo 1128631 1131827 := bstep (se 1 (by rfl) ⟨848870, by rfl⟩ : syracuseStep 1131827 = 1697741) B1697741
theorem B1131843 : Blo 1128631 1131843 := bstep (se 1 (by rfl) ⟨848882, by rfl⟩ : syracuseStep 1131843 = 1697765) B1697765
theorem B4834637 : Blo 1128631 4834637 := bstep (se 3 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 4834637 = 1812989) B1812989
theorem B1131859 : Blo 1128631 1131859 := bstep (se 1 (by rfl) ⟨848894, by rfl⟩ : syracuseStep 1131859 = 1697789) B1697789
theorem B1131875 : Blo 1128631 1131875 := bstep (se 1 (by rfl) ⟨848906, by rfl⟩ : syracuseStep 1131875 = 1697813) B1697813
theorem B5719409 : Blo 1128631 5719409 := bstep (se 2 (by rfl) ⟨2144778, by rfl⟩ : syracuseStep 5719409 = 4289557) B4289557
theorem B4834673 : Blo 1128631 4834673 := bstep (se 2 (by rfl) ⟨1813002, by rfl⟩ : syracuseStep 4834673 = 3626005) B3626005
theorem B1131891 : Blo 1128631 1131891 := bstep (se 1 (by rfl) ⟨848918, by rfl⟩ : syracuseStep 1131891 = 1697837) B1697837
theorem B1131907 : Blo 1128631 1131907 := bstep (se 1 (by rfl) ⟨848930, by rfl⟩ : syracuseStep 1131907 = 1697861) B1697861
theorem B1131923 : Blo 1128631 1131923 := bstep (se 1 (by rfl) ⟨848942, by rfl⟩ : syracuseStep 1131923 = 1697885) B1697885
theorem B1131939 : Blo 1128631 1131939 := bstep (se 1 (by rfl) ⟨848954, by rfl⟩ : syracuseStep 1131939 = 1697909) B1697909
theorem B1131955 : Blo 1128631 1131955 := bstep (se 1 (by rfl) ⟨848966, by rfl⟩ : syracuseStep 1131955 = 1697933) B1697933
theorem B1131971 : Blo 1128631 1131971 := bstep (se 1 (by rfl) ⟨848978, by rfl⟩ : syracuseStep 1131971 = 1697957) B1697957
theorem B1131987 : Blo 1128631 1131987 := bstep (se 1 (by rfl) ⟨848990, by rfl⟩ : syracuseStep 1131987 = 1697981) B1697981
theorem B1132003 : Blo 1128631 1132003 := bstep (se 1 (by rfl) ⟨849002, by rfl⟩ : syracuseStep 1132003 = 1698005) B1698005
theorem B2541041 : Blo 1128631 2541041 := bstep (se 2 (by rfl) ⟨952890, by rfl⟩ : syracuseStep 2541041 = 1905781) B1905781
theorem B1132019 : Blo 1128631 1132019 := bstep (se 1 (by rfl) ⟨849014, by rfl⟩ : syracuseStep 1132019 = 1698029) B1698029
theorem B2541059 : Blo 1128631 2541059 := bstep (se 1 (by rfl) ⟨1905794, by rfl⟩ : syracuseStep 2541059 = 3811589) B3811589
theorem B1132035 : Blo 1128631 1132035 := bstep (se 1 (by rfl) ⟨849026, by rfl⟩ : syracuseStep 1132035 = 1698053) B1698053
theorem B1132051 : Blo 1128631 1132051 := bstep (se 1 (by rfl) ⟨849038, by rfl⟩ : syracuseStep 1132051 = 1698077) B1698077
theorem B1132067 : Blo 1128631 1132067 := bstep (se 1 (by rfl) ⟨849050, by rfl⟩ : syracuseStep 1132067 = 1698101) B1698101
theorem B1132083 : Blo 1128631 1132083 := bstep (se 1 (by rfl) ⟨849062, by rfl⟩ : syracuseStep 1132083 = 1698125) B1698125
theorem B1132099 : Blo 1128631 1132099 := bstep (se 1 (by rfl) ⟨849074, by rfl⟩ : syracuseStep 1132099 = 1698149) B1698149
theorem B1132115 : Blo 1128631 1132115 := bstep (se 1 (by rfl) ⟨849086, by rfl⟩ : syracuseStep 1132115 = 1698173) B1698173
theorem B1132131 : Blo 1128631 1132131 := bstep (se 1 (by rfl) ⟨849098, by rfl⟩ : syracuseStep 1132131 = 1698197) B1698197
theorem B2147953 : Blo 1128631 2147953 := bstep (se 2 (by rfl) ⟨805482, by rfl⟩ : syracuseStep 2147953 = 1610965) B1610965
theorem B1132147 : Blo 1128631 1132147 := bstep (se 1 (by rfl) ⟨849110, by rfl⟩ : syracuseStep 1132147 = 1698221) B1698221
theorem B1132163 : Blo 1128631 1132163 := bstep (se 1 (by rfl) ⟨849122, by rfl⟩ : syracuseStep 1132163 = 1698245) B1698245
theorem B3819149 : Blo 1128631 3819149 := bstep (se 3 (by rfl) ⟨716090, by rfl⟩ : syracuseStep 3819149 = 1432181) B1432181
theorem B1132179 : Blo 1128631 1132179 := bstep (se 1 (by rfl) ⟨849134, by rfl⟩ : syracuseStep 1132179 = 1698269) B1698269
theorem B1132195 : Blo 1128631 1132195 := bstep (se 1 (by rfl) ⟨849146, by rfl⟩ : syracuseStep 1132195 = 1698293) B1698293
theorem B1132211 : Blo 1128631 1132211 := bstep (se 1 (by rfl) ⟨849158, by rfl⟩ : syracuseStep 1132211 = 1698317) B1698317
theorem B3819203 : Blo 1128631 3819203 := bstep (se 1 (by rfl) ⟨2864402, by rfl⟩ : syracuseStep 3819203 = 5728805) B5728805
theorem B1132227 : Blo 1128631 1132227 := bstep (se 1 (by rfl) ⟨849170, by rfl⟩ : syracuseStep 1132227 = 1698341) B1698341
theorem B1132243 : Blo 1128631 1132243 := bstep (se 1 (by rfl) ⟨849182, by rfl⟩ : syracuseStep 1132243 = 1698365) B1698365
theorem B1132259 : Blo 1128631 1132259 := bstep (se 1 (by rfl) ⟨849194, by rfl⟩ : syracuseStep 1132259 = 1698389) B1698389
theorem B8570609 : Blo 1128631 8570609 := bstep (se 2 (by rfl) ⟨3213978, by rfl⟩ : syracuseStep 8570609 = 6427957) B6427957
theorem B1132275 : Blo 1128631 1132275 := bstep (se 1 (by rfl) ⟨849206, by rfl⟩ : syracuseStep 1132275 = 1698413) B1698413
theorem B1132291 : Blo 1128631 1132291 := bstep (se 1 (by rfl) ⟨849218, by rfl⟩ : syracuseStep 1132291 = 1698437) B1698437
theorem B2541329 : Blo 1128631 2541329 := bstep (se 2 (by rfl) ⟨952998, by rfl⟩ : syracuseStep 2541329 = 1905997) B1905997
theorem B2148113 : Blo 1128631 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B1132307 : Blo 1128631 1132307 := bstep (se 1 (by rfl) ⟨849230, by rfl⟩ : syracuseStep 1132307 = 1698461) B1698461
theorem B2541347 : Blo 1128631 2541347 := bstep (se 1 (by rfl) ⟨1906010, by rfl⟩ : syracuseStep 2541347 = 3812021) B3812021
theorem B1132323 : Blo 1128631 1132323 := bstep (se 1 (by rfl) ⟨849242, by rfl⟩ : syracuseStep 1132323 = 1698485) B1698485
theorem B1132339 : Blo 1128631 1132339 := bstep (se 1 (by rfl) ⟨849254, by rfl⟩ : syracuseStep 1132339 = 1698509) B1698509
theorem B1132355 : Blo 1128631 1132355 := bstep (se 1 (by rfl) ⟨849266, by rfl⟩ : syracuseStep 1132355 = 1698533) B1698533
theorem B1132371 : Blo 1128631 1132371 := bstep (se 1 (by rfl) ⟨849278, by rfl⟩ : syracuseStep 1132371 = 1698557) B1698557
theorem B1132387 : Blo 1128631 1132387 := bstep (se 1 (by rfl) ⟨849290, by rfl⟩ : syracuseStep 1132387 = 1698581) B1698581
theorem B1132403 : Blo 1128631 1132403 := bstep (se 1 (by rfl) ⟨849302, by rfl⟩ : syracuseStep 1132403 = 1698605) B1698605
theorem B1132419 : Blo 1128631 1132419 := bstep (se 1 (by rfl) ⟨849314, by rfl⟩ : syracuseStep 1132419 = 1698629) B1698629
theorem B1132435 : Blo 1128631 1132435 := bstep (se 1 (by rfl) ⟨849326, by rfl⟩ : syracuseStep 1132435 = 1698653) B1698653
theorem B1132451 : Blo 1128631 1132451 := bstep (se 1 (by rfl) ⟨849338, by rfl⟩ : syracuseStep 1132451 = 1698677) B1698677
theorem B1132467 : Blo 1128631 1132467 := bstep (se 1 (by rfl) ⟨849350, by rfl⟩ : syracuseStep 1132467 = 1698701) B1698701
theorem B1132483 : Blo 1128631 1132483 := bstep (se 1 (by rfl) ⟨849362, by rfl⟩ : syracuseStep 1132483 = 1698725) B1698725
theorem B3819473 : Blo 1128631 3819473 := bstep (se 2 (by rfl) ⟨1432302, by rfl⟩ : syracuseStep 3819473 = 2864605) B2864605
theorem B1132499 : Blo 1128631 1132499 := bstep (se 1 (by rfl) ⟨849374, by rfl⟩ : syracuseStep 1132499 = 1698749) B1698749
theorem B1132515 : Blo 1128631 1132515 := bstep (se 1 (by rfl) ⟨849386, by rfl⟩ : syracuseStep 1132515 = 1698773) B1698773
theorem B12240881 : Blo 1128631 12240881 := bstep (se 2 (by rfl) ⟨4590330, by rfl⟩ : syracuseStep 12240881 = 9180661) B9180661
theorem B1132531 : Blo 1128631 1132531 := bstep (se 1 (by rfl) ⟨849398, by rfl⟩ : syracuseStep 1132531 = 1698797) B1698797
theorem B1132547 : Blo 1128631 1132547 := bstep (se 1 (by rfl) ⟨849410, by rfl⟩ : syracuseStep 1132547 = 1698821) B1698821
theorem B6866957 : Blo 1128631 6866957 := bstep (se 3 (by rfl) ⟨1287554, by rfl⟩ : syracuseStep 6866957 = 2575109) B2575109
theorem B1132563 : Blo 1128631 1132563 := bstep (se 1 (by rfl) ⟨849422, by rfl⟩ : syracuseStep 1132563 = 1698845) B1698845
theorem B1132579 : Blo 1128631 1132579 := bstep (se 1 (by rfl) ⟨849434, by rfl⟩ : syracuseStep 1132579 = 1698869) B1698869
theorem B2541617 : Blo 1128631 2541617 := bstep (se 2 (by rfl) ⟨953106, by rfl⟩ : syracuseStep 2541617 = 1906213) B1906213
theorem B1132595 : Blo 1128631 1132595 := bstep (se 1 (by rfl) ⟨849446, by rfl⟩ : syracuseStep 1132595 = 1698893) B1698893
theorem B2541635 : Blo 1128631 2541635 := bstep (se 1 (by rfl) ⟨1906226, by rfl⟩ : syracuseStep 2541635 = 3812453) B3812453
theorem B1132611 : Blo 1128631 1132611 := bstep (se 1 (by rfl) ⟨849458, by rfl⟩ : syracuseStep 1132611 = 1698917) B1698917
theorem B1132627 : Blo 1128631 1132627 := bstep (se 1 (by rfl) ⟨849470, by rfl⟩ : syracuseStep 1132627 = 1698941) B1698941
theorem B2148515 : Blo 1128631 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B1525969 : Blo 1128631 1525969 := bstep (se 2 (by rfl) ⟨572238, by rfl⟩ : syracuseStep 1525969 = 1144477) B1144477
theorem B2541905 : Blo 1128631 2541905 := bstep (se 2 (by rfl) ⟨953214, by rfl⟩ : syracuseStep 2541905 = 1906429) B1906429
theorem B1526099 : Blo 1128631 1526099 := bstep (se 1 (by rfl) ⟨1144574, by rfl⟩ : syracuseStep 1526099 = 2289149) B2289149
theorem B2541923 : Blo 1128631 2541923 := bstep (se 1 (by rfl) ⟨1906442, by rfl⟩ : syracuseStep 2541923 = 3812885) B3812885
theorem B3820013 : Blo 1128631 3820013 := bstep (se 3 (by rfl) ⟨716252, by rfl⟩ : syracuseStep 3820013 = 1432505) B1432505
theorem B3820067 : Blo 1128631 3820067 := bstep (se 1 (by rfl) ⟨2865050, by rfl⟩ : syracuseStep 3820067 = 5730101) B5730101
theorem B2542193 : Blo 1128631 2542193 := bstep (se 2 (by rfl) ⟨953322, by rfl⟩ : syracuseStep 2542193 = 1906645) B1906645
theorem B2542211 : Blo 1128631 2542211 := bstep (se 1 (by rfl) ⟨1906658, by rfl⟩ : syracuseStep 2542211 = 3813317) B3813317
theorem B6441605 : Blo 1128631 6441605 := bstep (se 4 (by rfl) ⟨603900, by rfl⟩ : syracuseStep 6441605 = 1207801) B1207801
theorem B1526467 : Blo 1128631 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B5720867 : Blo 1128631 5720867 := bstep (se 1 (by rfl) ⟨4290650, by rfl⟩ : syracuseStep 5720867 = 8581301) B8581301
theorem B5229361 : Blo 1128631 5229361 := bstep (se 2 (by rfl) ⟨1961010, by rfl⟩ : syracuseStep 5229361 = 3922021) B3922021
theorem B3820337 : Blo 1128631 3820337 := bstep (se 2 (by rfl) ⟨1432626, by rfl⟩ : syracuseStep 3820337 = 2865253) B2865253
theorem B2542481 : Blo 1128631 2542481 := bstep (se 2 (by rfl) ⟨953430, by rfl⟩ : syracuseStep 2542481 = 1906861) B1906861
theorem B3623825 : Blo 1128631 3623825 := bstep (se 2 (by rfl) ⟨1358934, by rfl⟩ : syracuseStep 3623825 = 2717869) B2717869
theorem B2542499 : Blo 1128631 2542499 := bstep (se 1 (by rfl) ⟨1906874, by rfl⟩ : syracuseStep 2542499 = 3813749) B3813749
theorem B1526737 : Blo 1128631 1526737 := bstep (se 2 (by rfl) ⟨572526, by rfl⟩ : syracuseStep 1526737 = 1145053) B1145053
theorem B2149411 : Blo 1128631 2149411 := bstep (se 1 (by rfl) ⟨1612058, by rfl⟩ : syracuseStep 2149411 = 3224117) B3224117
theorem B1526851 : Blo 1128631 1526851 := bstep (se 1 (by rfl) ⟨1145138, by rfl⟩ : syracuseStep 1526851 = 2290277) B2290277
theorem B11586673 : Blo 1128631 11586673 := bstep (se 2 (by rfl) ⟨4345002, by rfl⟩ : syracuseStep 11586673 = 8690005) B8690005
theorem B14470285 : Blo 1128631 14470285 := bstep (se 3 (by rfl) ⟨2713178, by rfl⟩ : syracuseStep 14470285 = 5426357) B5426357
theorem B2542769 : Blo 1128631 2542769 := bstep (se 2 (by rfl) ⟨953538, by rfl⟩ : syracuseStep 2542769 = 1907077) B1907077
theorem B2542787 : Blo 1128631 2542787 := bstep (se 1 (by rfl) ⟨1907090, by rfl⟩ : syracuseStep 2542787 = 3814181) B3814181
theorem B2149571 : Blo 1128631 2149571 := bstep (se 1 (by rfl) ⟨1612178, by rfl⟩ : syracuseStep 2149571 = 3224357) B3224357
theorem B3820877 : Blo 1128631 3820877 := bstep (se 3 (by rfl) ⟨716414, by rfl⟩ : syracuseStep 3820877 = 1432829) B1432829
theorem B1428835 : Blo 1128631 1428835 := bstep (se 1 (by rfl) ⟨1071626, by rfl⟩ : syracuseStep 1428835 = 2143253) B2143253
theorem B3820931 : Blo 1128631 3820931 := bstep (se 1 (by rfl) ⟨2865698, by rfl⟩ : syracuseStep 3820931 = 5731397) B5731397
theorem B3624365 : Blo 1128631 3624365 := bstep (se 3 (by rfl) ⟨679568, by rfl⟩ : syracuseStep 3624365 = 1359137) B1359137
theorem B1428931 : Blo 1128631 1428931 := bstep (se 1 (by rfl) ⟨1071698, by rfl⟩ : syracuseStep 1428931 = 2143397) B2143397
theorem B2543057 : Blo 1128631 2543057 := bstep (se 2 (by rfl) ⟨953646, by rfl⟩ : syracuseStep 2543057 = 1907293) B1907293
theorem B2543075 : Blo 1128631 2543075 := bstep (se 1 (by rfl) ⟨1907306, by rfl⟩ : syracuseStep 2543075 = 3814613) B3814613
theorem B5721677 : Blo 1128631 5721677 := bstep (se 3 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 5721677 = 2145629) B2145629
theorem B20663921 : Blo 1128631 20663921 := bstep (se 2 (by rfl) ⟨7748970, by rfl⟩ : syracuseStep 20663921 = 15497941) B15497941
theorem B3821201 : Blo 1128631 3821201 := bstep (se 2 (by rfl) ⟨1432950, by rfl⟩ : syracuseStep 3821201 = 2865901) B2865901
theorem B2412227 : Blo 1128631 2412227 := bstep (se 1 (by rfl) ⟨1809170, by rfl⟩ : syracuseStep 2412227 = 3618341) B3618341
theorem B2543345 : Blo 1128631 2543345 := bstep (se 2 (by rfl) ⟨953754, by rfl⟩ : syracuseStep 2543345 = 1907509) B1907509
theorem B2543363 : Blo 1128631 2543363 := bstep (se 1 (by rfl) ⟨1907522, by rfl⟩ : syracuseStep 2543363 = 3815045) B3815045
theorem B5164813 : Blo 1128631 5164813 := bstep (se 3 (by rfl) ⟨968402, by rfl⟩ : syracuseStep 5164813 = 1936805) B1936805
theorem B2445169 : Blo 1128631 2445169 := bstep (se 2 (by rfl) ⟨916938, by rfl⟩ : syracuseStep 2445169 = 1833877) B1833877
theorem B1429427 : Blo 1128631 1429427 := bstep (se 1 (by rfl) ⟨1072070, by rfl⟩ : syracuseStep 1429427 = 2144141) B2144141
theorem B2543633 : Blo 1128631 2543633 := bstep (se 2 (by rfl) ⟨953862, by rfl⟩ : syracuseStep 2543633 = 1907725) B1907725
theorem B2543651 : Blo 1128631 2543651 := bstep (se 1 (by rfl) ⟨1907738, by rfl⟩ : syracuseStep 2543651 = 3815477) B3815477
theorem B4477027 : Blo 1128631 4477027 := bstep (se 1 (by rfl) ⟨3357770, by rfl⟩ : syracuseStep 4477027 = 6715541) B6715541
theorem B3821741 : Blo 1128631 3821741 := bstep (se 3 (by rfl) ⟨716576, by rfl⟩ : syracuseStep 3821741 = 1433153) B1433153
theorem B3821795 : Blo 1128631 3821795 := bstep (se 1 (by rfl) ⟨2866346, by rfl⟩ : syracuseStep 3821795 = 5732693) B5732693
theorem B2543921 : Blo 1128631 2543921 := bstep (se 2 (by rfl) ⟨953970, by rfl⟩ : syracuseStep 2543921 = 1907941) B1907941
theorem B2543939 : Blo 1128631 2543939 := bstep (se 1 (by rfl) ⟨1907954, by rfl⟩ : syracuseStep 2543939 = 3815909) B3815909
theorem B14471621 : Blo 1128631 14471621 := bstep (se 4 (by rfl) ⟨1356714, by rfl⟩ : syracuseStep 14471621 = 2713429) B2713429
theorem B3822065 : Blo 1128631 3822065 := bstep (se 2 (by rfl) ⟨1433274, by rfl⟩ : syracuseStep 3822065 = 2866549) B2866549
theorem B2544209 : Blo 1128631 2544209 := bstep (se 2 (by rfl) ⟨954078, by rfl⟩ : syracuseStep 2544209 = 1908157) B1908157
theorem B2544227 : Blo 1128631 2544227 := bstep (se 1 (by rfl) ⟨1908170, by rfl⟩ : syracuseStep 2544227 = 3816341) B3816341
theorem B1430131 : Blo 1128631 1430131 := bstep (se 1 (by rfl) ⟨1072598, by rfl⟩ : syracuseStep 1430131 = 2145197) B2145197
theorem B1430227 : Blo 1128631 1430227 := bstep (se 1 (by rfl) ⟨1072670, by rfl⟩ : syracuseStep 1430227 = 2145341) B2145341
theorem B2544497 : Blo 1128631 2544497 := bstep (se 2 (by rfl) ⟨954186, by rfl⟩ : syracuseStep 2544497 = 1908373) B1908373
theorem B2544515 : Blo 1128631 2544515 := bstep (se 1 (by rfl) ⟨1908386, by rfl⟩ : syracuseStep 2544515 = 3816773) B3816773
theorem B3822605 : Blo 1128631 3822605 := bstep (se 3 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 3822605 = 1433477) B1433477
theorem B1528931 : Blo 1128631 1528931 := bstep (se 1 (by rfl) ⟨1146698, by rfl⟩ : syracuseStep 1528931 = 2293397) B2293397
theorem B5231729 : Blo 1128631 5231729 := bstep (se 2 (by rfl) ⟨1961898, by rfl⟩ : syracuseStep 5231729 = 3923797) B3923797
theorem B2544785 : Blo 1128631 2544785 := bstep (se 2 (by rfl) ⟨954294, by rfl⟩ : syracuseStep 2544785 = 1908589) B1908589
theorem B2544803 : Blo 1128631 2544803 := bstep (se 1 (by rfl) ⟨1908602, by rfl⟩ : syracuseStep 2544803 = 3817205) B3817205
theorem B1430723 : Blo 1128631 1430723 := bstep (se 1 (by rfl) ⟨1073042, by rfl⟩ : syracuseStep 1430723 = 2146085) B2146085
theorem B1529057 : Blo 1128631 1529057 := bstep (se 2 (by rfl) ⟨573396, by rfl⟩ : syracuseStep 1529057 = 1146793) B1146793
theorem B1692947 : Blo 1128631 1692947 := bstep (se 1 (by rfl) ⟨1269710, by rfl⟩ : syracuseStep 1692947 = 2539421) B2539421
theorem B1692977 : Blo 1128631 1692977 := bstep (se 2 (by rfl) ⟨634866, by rfl⟩ : syracuseStep 1692977 = 1269733) B1269733
theorem B1692995 : Blo 1128631 1692995 := bstep (se 1 (by rfl) ⟨1269746, by rfl⟩ : syracuseStep 1692995 = 2539493) B2539493
theorem B1693025 : Blo 1128631 1693025 := bstep (se 2 (by rfl) ⟨634884, by rfl⟩ : syracuseStep 1693025 = 1269769) B1269769
theorem B1693043 : Blo 1128631 1693043 := bstep (se 1 (by rfl) ⟨1269782, by rfl⟩ : syracuseStep 1693043 = 2539565) B2539565
theorem B2905475 : Blo 1128631 2905475 := bstep (se 1 (by rfl) ⟨2179106, by rfl⟩ : syracuseStep 2905475 = 4358213) B4358213
theorem B1693073 : Blo 1128631 1693073 := bstep (se 2 (by rfl) ⟨634902, by rfl⟩ : syracuseStep 1693073 = 1269805) B1269805
theorem B1693091 : Blo 1128631 1693091 := bstep (se 1 (by rfl) ⟨1269818, by rfl⟩ : syracuseStep 1693091 = 2539637) B2539637
theorem B2545073 : Blo 1128631 2545073 := bstep (se 2 (by rfl) ⟨954402, by rfl⟩ : syracuseStep 2545073 = 1908805) B1908805
theorem B1693121 : Blo 1128631 1693121 := bstep (se 2 (by rfl) ⟨634920, by rfl⟩ : syracuseStep 1693121 = 1269841) B1269841
theorem B2545091 : Blo 1128631 2545091 := bstep (se 1 (by rfl) ⟨1908818, by rfl⟩ : syracuseStep 2545091 = 3817637) B3817637
theorem B1693139 : Blo 1128631 1693139 := bstep (se 1 (by rfl) ⟨1269854, by rfl⟩ : syracuseStep 1693139 = 2539709) B2539709
theorem B1693169 : Blo 1128631 1693169 := bstep (se 2 (by rfl) ⟨634938, by rfl⟩ : syracuseStep 1693169 = 1269877) B1269877
theorem B1693187 : Blo 1128631 1693187 := bstep (se 1 (by rfl) ⟨1269890, by rfl⟩ : syracuseStep 1693187 = 2539781) B2539781
theorem B1693217 : Blo 1128631 1693217 := bstep (se 2 (by rfl) ⟨634956, by rfl⟩ : syracuseStep 1693217 = 1269913) B1269913
theorem B1693235 : Blo 1128631 1693235 := bstep (se 1 (by rfl) ⟨1269926, by rfl⟩ : syracuseStep 1693235 = 2539853) B2539853
theorem B1693265 : Blo 1128631 1693265 := bstep (se 2 (by rfl) ⟨634974, by rfl⟩ : syracuseStep 1693265 = 1269949) B1269949
theorem B1693283 : Blo 1128631 1693283 := bstep (se 1 (by rfl) ⟨1269962, by rfl⟩ : syracuseStep 1693283 = 2539925) B2539925
theorem B1693313 : Blo 1128631 1693313 := bstep (se 2 (by rfl) ⟨634992, by rfl⟩ : syracuseStep 1693313 = 1269985) B1269985
theorem B1529489 : Blo 1128631 1529489 := bstep (se 2 (by rfl) ⟨573558, by rfl⟩ : syracuseStep 1529489 = 1147117) B1147117
theorem B1693331 : Blo 1128631 1693331 := bstep (se 1 (by rfl) ⟨1269998, by rfl⟩ : syracuseStep 1693331 = 2539997) B2539997
theorem B2414243 : Blo 1128631 2414243 := bstep (se 1 (by rfl) ⟨1810682, by rfl⟩ : syracuseStep 2414243 = 3621365) B3621365
theorem B1693361 : Blo 1128631 1693361 := bstep (se 2 (by rfl) ⟨635010, by rfl⟩ : syracuseStep 1693361 = 1270021) B1270021
theorem B1693379 : Blo 1128631 1693379 := bstep (se 1 (by rfl) ⟨1270034, by rfl⟩ : syracuseStep 1693379 = 2540069) B2540069
theorem B7722701 : Blo 1128631 7722701 := bstep (se 3 (by rfl) ⟨1448006, by rfl⟩ : syracuseStep 7722701 = 2896013) B2896013
theorem B2545361 : Blo 1128631 2545361 := bstep (se 2 (by rfl) ⟨954510, by rfl⟩ : syracuseStep 2545361 = 1909021) B1909021
theorem B1693409 : Blo 1128631 1693409 := bstep (se 2 (by rfl) ⟨635028, by rfl⟩ : syracuseStep 1693409 = 1270057) B1270057
theorem B2545379 : Blo 1128631 2545379 := bstep (se 1 (by rfl) ⟨1909034, by rfl⟩ : syracuseStep 2545379 = 3818069) B3818069
theorem B1693427 : Blo 1128631 1693427 := bstep (se 1 (by rfl) ⟨1270070, by rfl⟩ : syracuseStep 1693427 = 2540141) B2540141
theorem B1693457 : Blo 1128631 1693457 := bstep (se 2 (by rfl) ⟨635046, by rfl⟩ : syracuseStep 1693457 = 1270093) B1270093
theorem B1693475 : Blo 1128631 1693475 := bstep (se 1 (by rfl) ⟨1270106, by rfl⟩ : syracuseStep 1693475 = 2540213) B2540213
theorem B1693505 : Blo 1128631 1693505 := bstep (se 2 (by rfl) ⟨635064, by rfl⟩ : syracuseStep 1693505 = 1270129) B1270129
theorem B1693523 : Blo 1128631 1693523 := bstep (se 1 (by rfl) ⟨1270142, by rfl⟩ : syracuseStep 1693523 = 2540285) B2540285
theorem B1693553 : Blo 1128631 1693553 := bstep (se 2 (by rfl) ⟨635082, by rfl⟩ : syracuseStep 1693553 = 1270165) B1270165
theorem B1693571 : Blo 1128631 1693571 := bstep (se 1 (by rfl) ⟨1270178, by rfl⟩ : syracuseStep 1693571 = 2540357) B2540357
theorem B1431427 : Blo 1128631 1431427 := bstep (se 1 (by rfl) ⟨1073570, by rfl⟩ : syracuseStep 1431427 = 2147141) B2147141
theorem B1693601 : Blo 1128631 1693601 := bstep (se 2 (by rfl) ⟨635100, by rfl⟩ : syracuseStep 1693601 = 1270201) B1270201
theorem B1693619 : Blo 1128631 1693619 := bstep (se 1 (by rfl) ⟨1270214, by rfl⟩ : syracuseStep 1693619 = 2540429) B2540429
theorem B1693649 : Blo 1128631 1693649 := bstep (se 2 (by rfl) ⟨635118, by rfl⟩ : syracuseStep 1693649 = 1270237) B1270237
theorem B1693667 : Blo 1128631 1693667 := bstep (se 1 (by rfl) ⟨1270250, by rfl⟩ : syracuseStep 1693667 = 2540501) B2540501
theorem B1431523 : Blo 1128631 1431523 := bstep (se 1 (by rfl) ⟨1073642, by rfl⟩ : syracuseStep 1431523 = 2147285) B2147285
theorem B2545649 : Blo 1128631 2545649 := bstep (se 2 (by rfl) ⟨954618, by rfl⟩ : syracuseStep 2545649 = 1909237) B1909237
theorem B1693697 : Blo 1128631 1693697 := bstep (se 2 (by rfl) ⟨635136, by rfl⟩ : syracuseStep 1693697 = 1270273) B1270273
theorem B2545667 : Blo 1128631 2545667 := bstep (se 1 (by rfl) ⟨1909250, by rfl⟩ : syracuseStep 2545667 = 3818501) B3818501
theorem B1693715 : Blo 1128631 1693715 := bstep (se 1 (by rfl) ⟨1270286, by rfl⟩ : syracuseStep 1693715 = 2540573) B2540573
theorem B1693745 : Blo 1128631 1693745 := bstep (se 2 (by rfl) ⟨635154, by rfl⟩ : syracuseStep 1693745 = 1270309) B1270309
theorem B1693763 : Blo 1128631 1693763 := bstep (se 1 (by rfl) ⟨1270322, by rfl⟩ : syracuseStep 1693763 = 2540645) B2540645
theorem B1693793 : Blo 1128631 1693793 := bstep (se 2 (by rfl) ⟨635172, by rfl⟩ : syracuseStep 1693793 = 1270345) B1270345
theorem B1529969 : Blo 1128631 1529969 := bstep (se 2 (by rfl) ⟨573738, by rfl⟩ : syracuseStep 1529969 = 1147477) B1147477
theorem B1693811 : Blo 1128631 1693811 := bstep (se 1 (by rfl) ⟨1270358, by rfl⟩ : syracuseStep 1693811 = 2540717) B2540717
theorem B1693841 : Blo 1128631 1693841 := bstep (se 2 (by rfl) ⟨635190, by rfl⟩ : syracuseStep 1693841 = 1270381) B1270381
theorem B1693859 : Blo 1128631 1693859 := bstep (se 1 (by rfl) ⟨1270394, by rfl⟩ : syracuseStep 1693859 = 2540789) B2540789
theorem B1693889 : Blo 1128631 1693889 := bstep (se 2 (by rfl) ⟨635208, by rfl⟩ : syracuseStep 1693889 = 1270417) B1270417
theorem B1693907 : Blo 1128631 1693907 := bstep (se 1 (by rfl) ⟨1270430, by rfl⟩ : syracuseStep 1693907 = 2540861) B2540861
theorem B1693937 : Blo 1128631 1693937 := bstep (se 2 (by rfl) ⟨635226, by rfl⟩ : syracuseStep 1693937 = 1270453) B1270453
theorem B1693955 : Blo 1128631 1693955 := bstep (se 1 (by rfl) ⟨1270466, by rfl⟩ : syracuseStep 1693955 = 2540933) B2540933
theorem B2545937 : Blo 1128631 2545937 := bstep (se 2 (by rfl) ⟨954726, by rfl⟩ : syracuseStep 2545937 = 1909453) B1909453
theorem B1693985 : Blo 1128631 1693985 := bstep (se 2 (by rfl) ⟨635244, by rfl⟩ : syracuseStep 1693985 = 1270489) B1270489
theorem B2545955 : Blo 1128631 2545955 := bstep (se 1 (by rfl) ⟨1909466, by rfl⟩ : syracuseStep 2545955 = 3818933) B3818933
theorem B1694003 : Blo 1128631 1694003 := bstep (se 1 (by rfl) ⟨1270502, by rfl⟩ : syracuseStep 1694003 = 2541005) B2541005
theorem B1694033 : Blo 1128631 1694033 := bstep (se 2 (by rfl) ⟨635262, by rfl⟩ : syracuseStep 1694033 = 1270525) B1270525
theorem B1694051 : Blo 1128631 1694051 := bstep (se 1 (by rfl) ⟨1270538, by rfl⟩ : syracuseStep 1694051 = 2541077) B2541077
theorem B1694081 : Blo 1128631 1694081 := bstep (se 2 (by rfl) ⟨635280, by rfl⟩ : syracuseStep 1694081 = 1270561) B1270561
theorem B6445453 : Blo 1128631 6445453 := bstep (se 3 (by rfl) ⟨1208522, by rfl⟩ : syracuseStep 6445453 = 2417045) B2417045
theorem B1694099 : Blo 1128631 1694099 := bstep (se 1 (by rfl) ⟨1270574, by rfl⟩ : syracuseStep 1694099 = 2541149) B2541149
theorem B1694129 : Blo 1128631 1694129 := bstep (se 2 (by rfl) ⟨635298, by rfl⟩ : syracuseStep 1694129 = 1270597) B1270597
theorem B5724593 : Blo 1128631 5724593 := bstep (se 2 (by rfl) ⟨2146722, by rfl⟩ : syracuseStep 5724593 = 4293445) B4293445
theorem B1694147 : Blo 1128631 1694147 := bstep (se 1 (by rfl) ⟨1270610, by rfl⟩ : syracuseStep 1694147 = 2541221) B2541221
theorem B1432019 : Blo 1128631 1432019 := bstep (se 1 (by rfl) ⟨1074014, by rfl⟩ : syracuseStep 1432019 = 2148029) B2148029
theorem B1694177 : Blo 1128631 1694177 := bstep (se 2 (by rfl) ⟨635316, by rfl⟩ : syracuseStep 1694177 = 1270633) B1270633
theorem B1694195 : Blo 1128631 1694195 := bstep (se 1 (by rfl) ⟨1270646, by rfl⟩ : syracuseStep 1694195 = 2541293) B2541293
theorem B1694225 : Blo 1128631 1694225 := bstep (se 2 (by rfl) ⟨635334, by rfl⟩ : syracuseStep 1694225 = 1270669) B1270669
theorem B1694243 : Blo 1128631 1694243 := bstep (se 1 (by rfl) ⟨1270682, by rfl⟩ : syracuseStep 1694243 = 2541365) B2541365
theorem B2546225 : Blo 1128631 2546225 := bstep (se 2 (by rfl) ⟨954834, by rfl⟩ : syracuseStep 2546225 = 1909669) B1909669
theorem B1694273 : Blo 1128631 1694273 := bstep (se 2 (by rfl) ⟨635352, by rfl⟩ : syracuseStep 1694273 = 1270705) B1270705
theorem B2546243 : Blo 1128631 2546243 := bstep (se 1 (by rfl) ⟨1909682, by rfl⟩ : syracuseStep 2546243 = 3819365) B3819365
theorem B1694291 : Blo 1128631 1694291 := bstep (se 1 (by rfl) ⟨1270718, by rfl⟩ : syracuseStep 1694291 = 2541437) B2541437
theorem B1694321 : Blo 1128631 1694321 := bstep (se 2 (by rfl) ⟨635370, by rfl⟩ : syracuseStep 1694321 = 1270741) B1270741
theorem B1694339 : Blo 1128631 1694339 := bstep (se 1 (by rfl) ⟨1270754, by rfl⟩ : syracuseStep 1694339 = 2541509) B2541509
theorem B1694369 : Blo 1128631 1694369 := bstep (se 2 (by rfl) ⟨635388, by rfl⟩ : syracuseStep 1694369 = 1270777) B1270777
theorem B1694387 : Blo 1128631 1694387 := bstep (se 1 (by rfl) ⟨1270790, by rfl⟩ : syracuseStep 1694387 = 2541581) B2541581
theorem B1694417 : Blo 1128631 1694417 := bstep (se 2 (by rfl) ⟨635406, by rfl⟩ : syracuseStep 1694417 = 1270813) B1270813
theorem B1694435 : Blo 1128631 1694435 := bstep (se 1 (by rfl) ⟨1270826, by rfl⟩ : syracuseStep 1694435 = 2541653) B2541653
theorem B1694465 : Blo 1128631 1694465 := bstep (se 2 (by rfl) ⟨635424, by rfl⟩ : syracuseStep 1694465 = 1270849) B1270849
theorem B1694483 : Blo 1128631 1694483 := bstep (se 1 (by rfl) ⟨1270862, by rfl⟩ : syracuseStep 1694483 = 2541725) B2541725
theorem B1694513 : Blo 1128631 1694513 := bstep (se 2 (by rfl) ⟨635442, by rfl⟩ : syracuseStep 1694513 = 1270885) B1270885
theorem B1694531 : Blo 1128631 1694531 := bstep (se 1 (by rfl) ⟨1270898, by rfl⟩ : syracuseStep 1694531 = 2541797) B2541797
theorem B2546513 : Blo 1128631 2546513 := bstep (se 2 (by rfl) ⟨954942, by rfl⟩ : syracuseStep 2546513 = 1909885) B1909885
theorem B1694561 : Blo 1128631 1694561 := bstep (se 2 (by rfl) ⟨635460, by rfl⟩ : syracuseStep 1694561 = 1270921) B1270921
theorem B2546531 : Blo 1128631 2546531 := bstep (se 1 (by rfl) ⟨1909898, by rfl⟩ : syracuseStep 2546531 = 3819797) B3819797
theorem B1694579 : Blo 1128631 1694579 := bstep (se 1 (by rfl) ⟨1270934, by rfl⟩ : syracuseStep 1694579 = 2541869) B2541869
theorem B2415491 : Blo 1128631 2415491 := bstep (se 1 (by rfl) ⟨1811618, by rfl⟩ : syracuseStep 2415491 = 3623237) B3623237
theorem B1694609 : Blo 1128631 1694609 := bstep (se 2 (by rfl) ⟨635478, by rfl⟩ : syracuseStep 1694609 = 1270957) B1270957
theorem B1694627 : Blo 1128631 1694627 := bstep (se 1 (by rfl) ⟨1270970, by rfl⟩ : syracuseStep 1694627 = 2541941) B2541941
theorem B3627953 : Blo 1128631 3627953 := bstep (se 2 (by rfl) ⟨1360482, by rfl⟩ : syracuseStep 3627953 = 2720965) B2720965
theorem B1694657 : Blo 1128631 1694657 := bstep (se 2 (by rfl) ⟨635496, by rfl⟩ : syracuseStep 1694657 = 1270993) B1270993
theorem B1694675 : Blo 1128631 1694675 := bstep (se 1 (by rfl) ⟨1271006, by rfl⟩ : syracuseStep 1694675 = 2542013) B2542013
theorem B1694705 : Blo 1128631 1694705 := bstep (se 2 (by rfl) ⟨635514, by rfl⟩ : syracuseStep 1694705 = 1271029) B1271029
theorem B1694723 : Blo 1128631 1694723 := bstep (se 1 (by rfl) ⟨1271042, by rfl⟩ : syracuseStep 1694723 = 2542085) B2542085
theorem B15490061 : Blo 1128631 15490061 := bstep (se 3 (by rfl) ⟨2904386, by rfl⟩ : syracuseStep 15490061 = 5808773) B5808773
theorem B1694753 : Blo 1128631 1694753 := bstep (se 2 (by rfl) ⟨635532, by rfl⟩ : syracuseStep 1694753 = 1271065) B1271065
theorem B1694771 : Blo 1128631 1694771 := bstep (se 1 (by rfl) ⟨1271078, by rfl⟩ : syracuseStep 1694771 = 2542157) B2542157
theorem B1694801 : Blo 1128631 1694801 := bstep (se 2 (by rfl) ⟨635550, by rfl⟩ : syracuseStep 1694801 = 1271101) B1271101
theorem B1694819 : Blo 1128631 1694819 := bstep (se 1 (by rfl) ⟨1271114, by rfl⟩ : syracuseStep 1694819 = 2542229) B2542229
theorem B2546801 : Blo 1128631 2546801 := bstep (se 2 (by rfl) ⟨955050, by rfl⟩ : syracuseStep 2546801 = 1910101) B1910101
theorem B1694849 : Blo 1128631 1694849 := bstep (se 2 (by rfl) ⟨635568, by rfl⟩ : syracuseStep 1694849 = 1271137) B1271137
theorem B2546819 : Blo 1128631 2546819 := bstep (se 1 (by rfl) ⟨1910114, by rfl⟩ : syracuseStep 2546819 = 3820229) B3820229
theorem B1694867 : Blo 1128631 1694867 := bstep (se 1 (by rfl) ⟨1271150, by rfl⟩ : syracuseStep 1694867 = 2542301) B2542301
theorem B1432723 : Blo 1128631 1432723 := bstep (se 1 (by rfl) ⟨1074542, by rfl⟩ : syracuseStep 1432723 = 2149085) B2149085
theorem B1694897 : Blo 1128631 1694897 := bstep (se 2 (by rfl) ⟨635586, by rfl⟩ : syracuseStep 1694897 = 1271173) B1271173
theorem B1694915 : Blo 1128631 1694915 := bstep (se 1 (by rfl) ⟨1271186, by rfl⟩ : syracuseStep 1694915 = 2542373) B2542373
theorem B1694945 : Blo 1128631 1694945 := bstep (se 2 (by rfl) ⟨635604, by rfl⟩ : syracuseStep 1694945 = 1271209) B1271209
theorem B1694963 : Blo 1128631 1694963 := bstep (se 1 (by rfl) ⟨1271222, by rfl⟩ : syracuseStep 1694963 = 2542445) B2542445
theorem B1432819 : Blo 1128631 1432819 := bstep (se 1 (by rfl) ⟨1074614, by rfl⟩ : syracuseStep 1432819 = 2149229) B2149229
theorem B1694993 : Blo 1128631 1694993 := bstep (se 2 (by rfl) ⟨635622, by rfl⟩ : syracuseStep 1694993 = 1271245) B1271245
theorem B1695011 : Blo 1128631 1695011 := bstep (se 1 (by rfl) ⟨1271258, by rfl⟩ : syracuseStep 1695011 = 2542517) B2542517
theorem B1695041 : Blo 1128631 1695041 := bstep (se 2 (by rfl) ⟨635640, by rfl⟩ : syracuseStep 1695041 = 1271281) B1271281
theorem B1695059 : Blo 1128631 1695059 := bstep (se 1 (by rfl) ⟨1271294, by rfl⟩ : syracuseStep 1695059 = 2542589) B2542589
theorem B1695089 : Blo 1128631 1695089 := bstep (se 2 (by rfl) ⟨635658, by rfl⟩ : syracuseStep 1695089 = 1271317) B1271317
theorem B1695107 : Blo 1128631 1695107 := bstep (se 1 (by rfl) ⟨1271330, by rfl⟩ : syracuseStep 1695107 = 2542661) B2542661
theorem B2547089 : Blo 1128631 2547089 := bstep (se 2 (by rfl) ⟨955158, by rfl⟩ : syracuseStep 2547089 = 1910317) B1910317
theorem B1695137 : Blo 1128631 1695137 := bstep (se 2 (by rfl) ⟨635676, by rfl⟩ : syracuseStep 1695137 = 1271353) B1271353
theorem B2547107 : Blo 1128631 2547107 := bstep (se 1 (by rfl) ⟨1910330, by rfl⟩ : syracuseStep 2547107 = 3820661) B3820661
theorem B1695155 : Blo 1128631 1695155 := bstep (se 1 (by rfl) ⟨1271366, by rfl⟩ : syracuseStep 1695155 = 2542733) B2542733
theorem B1695185 : Blo 1128631 1695185 := bstep (se 2 (by rfl) ⟨635694, by rfl⟩ : syracuseStep 1695185 = 1271389) B1271389
theorem B2416081 : Blo 1128631 2416081 := bstep (se 2 (by rfl) ⟨906030, by rfl⟩ : syracuseStep 2416081 = 1812061) B1812061
theorem B1695203 : Blo 1128631 1695203 := bstep (se 1 (by rfl) ⟨1271402, by rfl⟩ : syracuseStep 1695203 = 2542805) B2542805
theorem B1695233 : Blo 1128631 1695233 := bstep (se 2 (by rfl) ⟨635712, by rfl⟩ : syracuseStep 1695233 = 1271425) B1271425
theorem B1695251 : Blo 1128631 1695251 := bstep (se 1 (by rfl) ⟨1271438, by rfl⟩ : syracuseStep 1695251 = 2542877) B2542877
theorem B1695281 : Blo 1128631 1695281 := bstep (se 2 (by rfl) ⟨635730, by rfl⟩ : syracuseStep 1695281 = 1271461) B1271461
theorem B1695299 : Blo 1128631 1695299 := bstep (se 1 (by rfl) ⟨1271474, by rfl⟩ : syracuseStep 1695299 = 2542949) B2542949
theorem B1695329 : Blo 1128631 1695329 := bstep (se 2 (by rfl) ⟨635748, by rfl⟩ : syracuseStep 1695329 = 1271497) B1271497
theorem B1695347 : Blo 1128631 1695347 := bstep (se 1 (by rfl) ⟨1271510, by rfl⟩ : syracuseStep 1695347 = 2543021) B2543021
theorem B1695377 : Blo 1128631 1695377 := bstep (se 2 (by rfl) ⟨635766, by rfl⟩ : syracuseStep 1695377 = 1271533) B1271533
theorem B1695395 : Blo 1128631 1695395 := bstep (se 1 (by rfl) ⟨1271546, by rfl⟩ : syracuseStep 1695395 = 2543093) B2543093
theorem B2547377 : Blo 1128631 2547377 := bstep (se 2 (by rfl) ⟨955266, by rfl⟩ : syracuseStep 2547377 = 1910533) B1910533
theorem B1695425 : Blo 1128631 1695425 := bstep (se 2 (by rfl) ⟨635784, by rfl⟩ : syracuseStep 1695425 = 1271569) B1271569
theorem B2547395 : Blo 1128631 2547395 := bstep (se 1 (by rfl) ⟨1910546, by rfl⟩ : syracuseStep 2547395 = 3821093) B3821093
theorem B1695443 : Blo 1128631 1695443 := bstep (se 1 (by rfl) ⟨1271582, by rfl⟩ : syracuseStep 1695443 = 2543165) B2543165
theorem B1433315 : Blo 1128631 1433315 := bstep (se 1 (by rfl) ⟨1074986, by rfl⟩ : syracuseStep 1433315 = 2149973) B2149973
theorem B1695473 : Blo 1128631 1695473 := bstep (se 2 (by rfl) ⟨635802, by rfl⟩ : syracuseStep 1695473 = 1271605) B1271605
theorem B1695491 : Blo 1128631 1695491 := bstep (se 1 (by rfl) ⟨1271618, by rfl⟩ : syracuseStep 1695491 = 2543237) B2543237
theorem B1695521 : Blo 1128631 1695521 := bstep (se 2 (by rfl) ⟨635820, by rfl⟩ : syracuseStep 1695521 = 1271641) B1271641
theorem B1695539 : Blo 1128631 1695539 := bstep (se 1 (by rfl) ⟨1271654, by rfl⟩ : syracuseStep 1695539 = 2543309) B2543309
theorem B1695569 : Blo 1128631 1695569 := bstep (se 2 (by rfl) ⟨635838, by rfl⟩ : syracuseStep 1695569 = 1271677) B1271677
theorem B1695587 : Blo 1128631 1695587 := bstep (se 1 (by rfl) ⟨1271690, by rfl⟩ : syracuseStep 1695587 = 2543381) B2543381
theorem B5726051 : Blo 1128631 5726051 := bstep (se 1 (by rfl) ⟨4294538, by rfl⟩ : syracuseStep 5726051 = 8589077) B8589077
theorem B1695617 : Blo 1128631 1695617 := bstep (se 2 (by rfl) ⟨635856, by rfl⟩ : syracuseStep 1695617 = 1271713) B1271713
theorem B1695635 : Blo 1128631 1695635 := bstep (se 1 (by rfl) ⟨1271726, by rfl⟩ : syracuseStep 1695635 = 2543453) B2543453
theorem B1695665 : Blo 1128631 1695665 := bstep (se 2 (by rfl) ⟨635874, by rfl⟩ : syracuseStep 1695665 = 1271749) B1271749
theorem B1695683 : Blo 1128631 1695683 := bstep (se 1 (by rfl) ⟨1271762, by rfl⟩ : syracuseStep 1695683 = 2543525) B2543525
theorem B2547665 : Blo 1128631 2547665 := bstep (se 2 (by rfl) ⟨955374, by rfl⟩ : syracuseStep 2547665 = 1910749) B1910749
theorem B1269715 : Blo 1128631 1269715 := bstep (se 1 (by rfl) ⟨952286, by rfl⟩ : syracuseStep 1269715 = 1904573) B1904573
theorem B1695713 : Blo 1128631 1695713 := bstep (se 2 (by rfl) ⟨635892, by rfl⟩ : syracuseStep 1695713 = 1271785) B1271785
theorem B2547683 : Blo 1128631 2547683 := bstep (se 1 (by rfl) ⟨1910762, by rfl⟩ : syracuseStep 2547683 = 3821525) B3821525
theorem B1695731 : Blo 1128631 1695731 := bstep (se 1 (by rfl) ⟨1271798, by rfl⟩ : syracuseStep 1695731 = 2543597) B2543597
theorem B1695761 : Blo 1128631 1695761 := bstep (se 2 (by rfl) ⟨635910, by rfl⟩ : syracuseStep 1695761 = 1271821) B1271821
theorem B1695779 : Blo 1128631 1695779 := bstep (se 1 (by rfl) ⟨1271834, by rfl⟩ : syracuseStep 1695779 = 2543669) B2543669
theorem B1695809 : Blo 1128631 1695809 := bstep (se 2 (by rfl) ⟨635928, by rfl⟩ : syracuseStep 1695809 = 1271857) B1271857
theorem B1695827 : Blo 1128631 1695827 := bstep (se 1 (by rfl) ⟨1271870, by rfl⟩ : syracuseStep 1695827 = 2543741) B2543741
theorem B1269859 : Blo 1128631 1269859 := bstep (se 1 (by rfl) ⟨952394, by rfl⟩ : syracuseStep 1269859 = 1904789) B1904789
theorem B1695857 : Blo 1128631 1695857 := bstep (se 2 (by rfl) ⟨635946, by rfl⟩ : syracuseStep 1695857 = 1271893) B1271893
theorem B1695875 : Blo 1128631 1695875 := bstep (se 1 (by rfl) ⟨1271906, by rfl⟩ : syracuseStep 1695875 = 2543813) B2543813
theorem B1695905 : Blo 1128631 1695905 := bstep (se 2 (by rfl) ⟨635964, by rfl⟩ : syracuseStep 1695905 = 1271929) B1271929
theorem B1695923 : Blo 1128631 1695923 := bstep (se 1 (by rfl) ⟨1271942, by rfl⟩ : syracuseStep 1695923 = 2543885) B2543885
theorem B6119621 : Blo 1128631 6119621 := bstep (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) B1147429
theorem B1695953 : Blo 1128631 1695953 := bstep (se 2 (by rfl) ⟨635982, by rfl⟩ : syracuseStep 1695953 = 1271965) B1271965
theorem B1695971 : Blo 1128631 1695971 := bstep (se 1 (by rfl) ⟨1271978, by rfl⟩ : syracuseStep 1695971 = 2543957) B2543957
theorem B2547953 : Blo 1128631 2547953 := bstep (se 2 (by rfl) ⟨955482, by rfl⟩ : syracuseStep 2547953 = 1910965) B1910965
theorem B1270003 : Blo 1128631 1270003 := bstep (se 1 (by rfl) ⟨952502, by rfl⟩ : syracuseStep 1270003 = 1905005) B1905005
theorem B1696001 : Blo 1128631 1696001 := bstep (se 2 (by rfl) ⟨636000, by rfl⟩ : syracuseStep 1696001 = 1272001) B1272001
theorem B2547971 : Blo 1128631 2547971 := bstep (se 1 (by rfl) ⟨1910978, by rfl⟩ : syracuseStep 2547971 = 3821957) B3821957
theorem B1696019 : Blo 1128631 1696019 := bstep (se 1 (by rfl) ⟨1272014, by rfl⟩ : syracuseStep 1696019 = 2544029) B2544029
theorem B1696049 : Blo 1128631 1696049 := bstep (se 2 (by rfl) ⟨636018, by rfl⟩ : syracuseStep 1696049 = 1272037) B1272037
theorem B1696067 : Blo 1128631 1696067 := bstep (se 1 (by rfl) ⟨1272050, by rfl⟩ : syracuseStep 1696067 = 2544101) B2544101
theorem B6447437 : Blo 1128631 6447437 := bstep (se 3 (by rfl) ⟨1208894, by rfl⟩ : syracuseStep 6447437 = 2417789) B2417789
theorem B1696097 : Blo 1128631 1696097 := bstep (se 2 (by rfl) ⟨636036, by rfl⟩ : syracuseStep 1696097 = 1272073) B1272073
theorem B1696115 : Blo 1128631 1696115 := bstep (se 1 (by rfl) ⟨1272086, by rfl⟩ : syracuseStep 1696115 = 2544173) B2544173
theorem B1270147 : Blo 1128631 1270147 := bstep (se 1 (by rfl) ⟨952610, by rfl⟩ : syracuseStep 1270147 = 1905221) B1905221
theorem B10314125 : Blo 1128631 10314125 := bstep (se 3 (by rfl) ⟨1933898, by rfl⟩ : syracuseStep 10314125 = 3867797) B3867797
theorem B1696145 : Blo 1128631 1696145 := bstep (se 2 (by rfl) ⟨636054, by rfl⟩ : syracuseStep 1696145 = 1272109) B1272109
theorem B1696163 : Blo 1128631 1696163 := bstep (se 1 (by rfl) ⟨1272122, by rfl⟩ : syracuseStep 1696163 = 2544245) B2544245
theorem B1696193 : Blo 1128631 1696193 := bstep (se 2 (by rfl) ⟨636072, by rfl⟩ : syracuseStep 1696193 = 1272145) B1272145
theorem B2712017 : Blo 1128631 2712017 := bstep (se 2 (by rfl) ⟨1017006, by rfl⟩ : syracuseStep 2712017 = 2034013) B2034013
theorem B1696211 : Blo 1128631 1696211 := bstep (se 1 (by rfl) ⟨1272158, by rfl⟩ : syracuseStep 1696211 = 2544317) B2544317
theorem B1696241 : Blo 1128631 1696241 := bstep (se 2 (by rfl) ⟨636090, by rfl⟩ : syracuseStep 1696241 = 1272181) B1272181
theorem B1696259 : Blo 1128631 1696259 := bstep (se 1 (by rfl) ⟨1272194, by rfl⟩ : syracuseStep 1696259 = 2544389) B2544389
theorem B2548241 : Blo 1128631 2548241 := bstep (se 2 (by rfl) ⟨955590, by rfl⟩ : syracuseStep 2548241 = 1911181) B1911181
theorem B1270291 : Blo 1128631 1270291 := bstep (se 1 (by rfl) ⟨952718, by rfl⟩ : syracuseStep 1270291 = 1905437) B1905437
theorem B1696289 : Blo 1128631 1696289 := bstep (se 2 (by rfl) ⟨636108, by rfl⟩ : syracuseStep 1696289 = 1272217) B1272217
theorem B2548259 : Blo 1128631 2548259 := bstep (se 1 (by rfl) ⟨1911194, by rfl⟩ : syracuseStep 2548259 = 3822389) B3822389
theorem B1696307 : Blo 1128631 1696307 := bstep (se 1 (by rfl) ⟨1272230, by rfl⟩ : syracuseStep 1696307 = 2544461) B2544461
theorem B13754933 : Blo 1128631 13754933 := bstep (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) B1289525
theorem B1696337 : Blo 1128631 1696337 := bstep (se 2 (by rfl) ⟨636126, by rfl⟩ : syracuseStep 1696337 = 1272253) B1272253
theorem B1696355 : Blo 1128631 1696355 := bstep (se 1 (by rfl) ⟨1272266, by rfl⟩ : syracuseStep 1696355 = 2544533) B2544533
theorem B1696385 : Blo 1128631 1696385 := bstep (se 2 (by rfl) ⟨636144, by rfl⟩ : syracuseStep 1696385 = 1272289) B1272289
theorem B5726861 : Blo 1128631 5726861 := bstep (se 3 (by rfl) ⟨1073786, by rfl⟩ : syracuseStep 5726861 = 2147573) B2147573
theorem B1696403 : Blo 1128631 1696403 := bstep (se 1 (by rfl) ⟨1272302, by rfl⟩ : syracuseStep 1696403 = 2544605) B2544605
theorem B1270435 : Blo 1128631 1270435 := bstep (se 1 (by rfl) ⟨952826, by rfl⟩ : syracuseStep 1270435 = 1905653) B1905653
theorem B1696433 : Blo 1128631 1696433 := bstep (se 2 (by rfl) ⟨636162, by rfl⟩ : syracuseStep 1696433 = 1272325) B1272325
theorem B1696451 : Blo 1128631 1696451 := bstep (se 1 (by rfl) ⟨1272338, by rfl⟩ : syracuseStep 1696451 = 2544677) B2544677
theorem B1696481 : Blo 1128631 1696481 := bstep (se 2 (by rfl) ⟨636180, by rfl⟩ : syracuseStep 1696481 = 1272361) B1272361
theorem B1696499 : Blo 1128631 1696499 := bstep (se 1 (by rfl) ⟨1272374, by rfl⟩ : syracuseStep 1696499 = 2544749) B2544749
theorem B3138317 : Blo 1128631 3138317 := bstep (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) B1176869
theorem B1696529 : Blo 1128631 1696529 := bstep (se 2 (by rfl) ⟨636198, by rfl⟩ : syracuseStep 1696529 = 1272397) B1272397
theorem B1696547 : Blo 1128631 1696547 := bstep (se 1 (by rfl) ⟨1272410, by rfl⟩ : syracuseStep 1696547 = 2544821) B2544821
theorem B1270579 : Blo 1128631 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B1696577 : Blo 1128631 1696577 := bstep (se 2 (by rfl) ⟨636216, by rfl⟩ : syracuseStep 1696577 = 1272433) B1272433
theorem B1696595 : Blo 1128631 1696595 := bstep (se 1 (by rfl) ⟨1272446, by rfl⟩ : syracuseStep 1696595 = 2544893) B2544893
theorem B1696625 : Blo 1128631 1696625 := bstep (se 2 (by rfl) ⟨636234, by rfl⟩ : syracuseStep 1696625 = 1272469) B1272469
theorem B1696643 : Blo 1128631 1696643 := bstep (se 1 (by rfl) ⟨1272482, by rfl⟩ : syracuseStep 1696643 = 2544965) B2544965
theorem B1696673 : Blo 1128631 1696673 := bstep (se 2 (by rfl) ⟨636252, by rfl⟩ : syracuseStep 1696673 = 1272505) B1272505
theorem B5235619 : Blo 1128631 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1696691 : Blo 1128631 1696691 := bstep (se 1 (by rfl) ⟨1272518, by rfl⟩ : syracuseStep 1696691 = 2545037) B2545037
theorem B1270723 : Blo 1128631 1270723 := bstep (se 1 (by rfl) ⟨953042, by rfl⟩ : syracuseStep 1270723 = 1906085) B1906085
theorem B1696721 : Blo 1128631 1696721 := bstep (se 2 (by rfl) ⟨636270, by rfl⟩ : syracuseStep 1696721 = 1272541) B1272541
theorem B1696739 : Blo 1128631 1696739 := bstep (se 1 (by rfl) ⟨1272554, by rfl⟩ : syracuseStep 1696739 = 2545109) B2545109
theorem B1696769 : Blo 1128631 1696769 := bstep (se 2 (by rfl) ⟨636288, by rfl⟩ : syracuseStep 1696769 = 1272577) B1272577
theorem B1696787 : Blo 1128631 1696787 := bstep (se 1 (by rfl) ⟨1272590, by rfl⟩ : syracuseStep 1696787 = 2545181) B2545181
theorem B1696817 : Blo 1128631 1696817 := bstep (se 2 (by rfl) ⟨636306, by rfl⟩ : syracuseStep 1696817 = 1272613) B1272613
theorem B1696835 : Blo 1128631 1696835 := bstep (se 1 (by rfl) ⟨1272626, by rfl⟩ : syracuseStep 1696835 = 2545253) B2545253
theorem B1270867 : Blo 1128631 1270867 := bstep (se 1 (by rfl) ⟨953150, by rfl⟩ : syracuseStep 1270867 = 1906301) B1906301
theorem B158917717 : Blo 1128631 158917717 := bstep (se 8 (by rfl) ⟨931158, by rfl⟩ : syracuseStep 158917717 = 1862317) B1862317
theorem B1696865 : Blo 1128631 1696865 := bstep (se 2 (by rfl) ⟨636324, by rfl⟩ : syracuseStep 1696865 = 1272649) B1272649
theorem B1696883 : Blo 1128631 1696883 := bstep (se 1 (by rfl) ⟨1272662, by rfl⟩ : syracuseStep 1696883 = 2545325) B2545325
theorem B1696913 : Blo 1128631 1696913 := bstep (se 2 (by rfl) ⟨636342, by rfl⟩ : syracuseStep 1696913 = 1272685) B1272685
theorem B1696931 : Blo 1128631 1696931 := bstep (se 1 (by rfl) ⟨1272698, by rfl⟩ : syracuseStep 1696931 = 2545397) B2545397
theorem B1696961 : Blo 1128631 1696961 := bstep (se 2 (by rfl) ⟨636360, by rfl⟩ : syracuseStep 1696961 = 1272721) B1272721
theorem B1696979 : Blo 1128631 1696979 := bstep (se 1 (by rfl) ⟨1272734, by rfl⟩ : syracuseStep 1696979 = 2545469) B2545469
theorem B1271011 : Blo 1128631 1271011 := bstep (se 1 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 1271011 = 1906517) B1906517
theorem B1697009 : Blo 1128631 1697009 := bstep (se 2 (by rfl) ⟨636378, by rfl⟩ : syracuseStep 1697009 = 1272757) B1272757
theorem B6448369 : Blo 1128631 6448369 := bstep (se 2 (by rfl) ⟨2418138, by rfl⟩ : syracuseStep 6448369 = 4836277) B4836277
theorem B1860851 : Blo 1128631 1860851 := bstep (se 1 (by rfl) ⟨1395638, by rfl⟩ : syracuseStep 1860851 = 2791277) B2791277
theorem B1697027 : Blo 1128631 1697027 := bstep (se 1 (by rfl) ⟨1272770, by rfl⟩ : syracuseStep 1697027 = 2545541) B2545541
theorem B1697057 : Blo 1128631 1697057 := bstep (se 2 (by rfl) ⟨636396, by rfl⟩ : syracuseStep 1697057 = 1272793) B1272793
theorem B1697075 : Blo 1128631 1697075 := bstep (se 1 (by rfl) ⟨1272806, by rfl⟩ : syracuseStep 1697075 = 2545613) B2545613
theorem B3433795 : Blo 1128631 3433795 := bstep (se 1 (by rfl) ⟨2575346, by rfl⟩ : syracuseStep 3433795 = 5150693) B5150693
theorem B1697105 : Blo 1128631 1697105 := bstep (se 2 (by rfl) ⟨636414, by rfl⟩ : syracuseStep 1697105 = 1272829) B1272829
theorem B14476643 : Blo 1128631 14476643 := bstep (se 1 (by rfl) ⟨10857482, by rfl⟩ : syracuseStep 14476643 = 21714965) B21714965
theorem B1697123 : Blo 1128631 1697123 := bstep (se 1 (by rfl) ⟨1272842, by rfl⟩ : syracuseStep 1697123 = 2545685) B2545685
theorem B1271155 : Blo 1128631 1271155 := bstep (se 1 (by rfl) ⟨953366, by rfl⟩ : syracuseStep 1271155 = 1906733) B1906733
theorem B1697153 : Blo 1128631 1697153 := bstep (se 2 (by rfl) ⟨636432, by rfl⟩ : syracuseStep 1697153 = 1272865) B1272865
theorem B3433859 : Blo 1128631 3433859 := bstep (se 1 (by rfl) ⟨2575394, by rfl⟩ : syracuseStep 3433859 = 5150789) B5150789
theorem B1697171 : Blo 1128631 1697171 := bstep (se 1 (by rfl) ⟨1272878, by rfl⟩ : syracuseStep 1697171 = 2545757) B2545757
theorem B1697201 : Blo 1128631 1697201 := bstep (se 2 (by rfl) ⟨636450, by rfl⟩ : syracuseStep 1697201 = 1272901) B1272901
theorem B1697219 : Blo 1128631 1697219 := bstep (se 1 (by rfl) ⟨1272914, by rfl⟩ : syracuseStep 1697219 = 2545829) B2545829
theorem B1697249 : Blo 1128631 1697249 := bstep (se 2 (by rfl) ⟨636468, by rfl⟩ : syracuseStep 1697249 = 1272937) B1272937
theorem B1697267 : Blo 1128631 1697267 := bstep (se 1 (by rfl) ⟨1272950, by rfl⟩ : syracuseStep 1697267 = 2545901) B2545901
theorem B1271299 : Blo 1128631 1271299 := bstep (se 1 (by rfl) ⟨953474, by rfl⟩ : syracuseStep 1271299 = 1906949) B1906949
theorem B1697297 : Blo 1128631 1697297 := bstep (se 2 (by rfl) ⟨636486, by rfl⟩ : syracuseStep 1697297 = 1272973) B1272973
theorem B1697315 : Blo 1128631 1697315 := bstep (se 1 (by rfl) ⟨1272986, by rfl⟩ : syracuseStep 1697315 = 2545973) B2545973
theorem B1697345 : Blo 1128631 1697345 := bstep (se 2 (by rfl) ⟨636504, by rfl⟩ : syracuseStep 1697345 = 1273009) B1273009
theorem B1697363 : Blo 1128631 1697363 := bstep (se 1 (by rfl) ⟨1273022, by rfl⟩ : syracuseStep 1697363 = 2546045) B2546045
theorem B1697393 : Blo 1128631 1697393 := bstep (se 2 (by rfl) ⟨636522, by rfl⟩ : syracuseStep 1697393 = 1273045) B1273045
theorem B1697411 : Blo 1128631 1697411 := bstep (se 1 (by rfl) ⟨1273058, by rfl⟩ : syracuseStep 1697411 = 2546117) B2546117
theorem B1271443 : Blo 1128631 1271443 := bstep (se 1 (by rfl) ⟨953582, by rfl⟩ : syracuseStep 1271443 = 1907165) B1907165
theorem B1697441 : Blo 1128631 1697441 := bstep (se 2 (by rfl) ⟨636540, by rfl⟩ : syracuseStep 1697441 = 1273081) B1273081
theorem B1697459 : Blo 1128631 1697459 := bstep (se 1 (by rfl) ⟨1273094, by rfl⟩ : syracuseStep 1697459 = 2546189) B2546189
theorem B1697489 : Blo 1128631 1697489 := bstep (se 2 (by rfl) ⟨636558, by rfl⟩ : syracuseStep 1697489 = 1273117) B1273117
theorem B1697507 : Blo 1128631 1697507 := bstep (se 1 (by rfl) ⟨1273130, by rfl⟩ : syracuseStep 1697507 = 2546261) B2546261
theorem B1697537 : Blo 1128631 1697537 := bstep (se 2 (by rfl) ⟨636576, by rfl⟩ : syracuseStep 1697537 = 1273153) B1273153
theorem B1697555 : Blo 1128631 1697555 := bstep (se 1 (by rfl) ⟨1273166, by rfl⟩ : syracuseStep 1697555 = 2546333) B2546333
theorem B1271587 : Blo 1128631 1271587 := bstep (se 1 (by rfl) ⟨953690, by rfl⟩ : syracuseStep 1271587 = 1907381) B1907381
theorem B1697585 : Blo 1128631 1697585 := bstep (se 2 (by rfl) ⟨636594, by rfl⟩ : syracuseStep 1697585 = 1273189) B1273189
theorem B1697603 : Blo 1128631 1697603 := bstep (se 1 (by rfl) ⟨1273202, by rfl⟩ : syracuseStep 1697603 = 2546405) B2546405
theorem B1697633 : Blo 1128631 1697633 := bstep (se 2 (by rfl) ⟨636612, by rfl⟩ : syracuseStep 1697633 = 1273225) B1273225
theorem B1697651 : Blo 1128631 1697651 := bstep (se 1 (by rfl) ⟨1273238, by rfl⟩ : syracuseStep 1697651 = 2546477) B2546477
theorem B1697681 : Blo 1128631 1697681 := bstep (se 2 (by rfl) ⟨636630, by rfl⟩ : syracuseStep 1697681 = 1273261) B1273261
theorem B1697699 : Blo 1128631 1697699 := bstep (se 1 (by rfl) ⟨1273274, by rfl⟩ : syracuseStep 1697699 = 2546549) B2546549
theorem B1271731 : Blo 1128631 1271731 := bstep (se 1 (by rfl) ⟨953798, by rfl⟩ : syracuseStep 1271731 = 1907597) B1907597
theorem B1697729 : Blo 1128631 1697729 := bstep (se 2 (by rfl) ⟨636648, by rfl⟩ : syracuseStep 1697729 = 1273297) B1273297
theorem B1697747 : Blo 1128631 1697747 := bstep (se 1 (by rfl) ⟨1273310, by rfl⟩ : syracuseStep 1697747 = 2546621) B2546621
theorem B1697777 : Blo 1128631 1697777 := bstep (se 2 (by rfl) ⟨636666, by rfl⟩ : syracuseStep 1697777 = 1273333) B1273333
theorem B1697795 : Blo 1128631 1697795 := bstep (se 1 (by rfl) ⟨1273346, by rfl⟩ : syracuseStep 1697795 = 2546693) B2546693
theorem B1697825 : Blo 1128631 1697825 := bstep (se 2 (by rfl) ⟨636684, by rfl⟩ : syracuseStep 1697825 = 1273369) B1273369
theorem B6285347 : Blo 1128631 6285347 := bstep (se 1 (by rfl) ⟨4714010, by rfl⟩ : syracuseStep 6285347 = 9428021) B9428021
theorem B1697843 : Blo 1128631 1697843 := bstep (se 1 (by rfl) ⟨1273382, by rfl⟩ : syracuseStep 1697843 = 2546765) B2546765
theorem B1271875 : Blo 1128631 1271875 := bstep (se 1 (by rfl) ⟨953906, by rfl⟩ : syracuseStep 1271875 = 1907813) B1907813
theorem B1697873 : Blo 1128631 1697873 := bstep (se 2 (by rfl) ⟨636702, by rfl⟩ : syracuseStep 1697873 = 1273405) B1273405
theorem B1697891 : Blo 1128631 1697891 := bstep (se 1 (by rfl) ⟨1273418, by rfl⟩ : syracuseStep 1697891 = 2546837) B2546837
theorem B1697921 : Blo 1128631 1697921 := bstep (se 2 (by rfl) ⟨636720, by rfl⟩ : syracuseStep 1697921 = 1273441) B1273441
theorem B1697939 : Blo 1128631 1697939 := bstep (se 1 (by rfl) ⟨1273454, by rfl⟩ : syracuseStep 1697939 = 2546909) B2546909
theorem B4286627 : Blo 1128631 4286627 := bstep (se 1 (by rfl) ⟨3214970, by rfl⟩ : syracuseStep 4286627 = 6429941) B6429941
theorem B4286641 : Blo 1128631 4286641 := bstep (se 2 (by rfl) ⟨1607490, by rfl⟩ : syracuseStep 4286641 = 3214981) B3214981
theorem B1697969 : Blo 1128631 1697969 := bstep (se 2 (by rfl) ⟨636738, by rfl⟩ : syracuseStep 1697969 = 1273477) B1273477
theorem B1697987 : Blo 1128631 1697987 := bstep (se 1 (by rfl) ⟨1273490, by rfl⟩ : syracuseStep 1697987 = 2546981) B2546981
theorem B1272019 : Blo 1128631 1272019 := bstep (se 1 (by rfl) ⟨954014, by rfl⟩ : syracuseStep 1272019 = 1908029) B1908029
theorem B1698017 : Blo 1128631 1698017 := bstep (se 2 (by rfl) ⟨636756, by rfl⟩ : syracuseStep 1698017 = 1273513) B1273513
theorem B27519203 : Blo 1128631 27519203 := bstep (se 1 (by rfl) ⟨20639402, by rfl⟩ : syracuseStep 27519203 = 41278805) B41278805
theorem B1698035 : Blo 1128631 1698035 := bstep (se 1 (by rfl) ⟨1273526, by rfl⟩ : syracuseStep 1698035 = 2547053) B2547053
theorem B1698065 : Blo 1128631 1698065 := bstep (se 2 (by rfl) ⟨636774, by rfl⟩ : syracuseStep 1698065 = 1273549) B1273549
theorem B1698083 : Blo 1128631 1698083 := bstep (se 1 (by rfl) ⟨1273562, by rfl⟩ : syracuseStep 1698083 = 2547125) B2547125
theorem B6121763 : Blo 1128631 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B1698113 : Blo 1128631 1698113 := bstep (se 2 (by rfl) ⟨636792, by rfl⟩ : syracuseStep 1698113 = 1273585) B1273585
theorem B1698131 : Blo 1128631 1698131 := bstep (se 1 (by rfl) ⟨1273598, by rfl⟩ : syracuseStep 1698131 = 2547197) B2547197
theorem B1272163 : Blo 1128631 1272163 := bstep (se 1 (by rfl) ⟨954122, by rfl⟩ : syracuseStep 1272163 = 1908245) B1908245
theorem B1698161 : Blo 1128631 1698161 := bstep (se 2 (by rfl) ⟨636810, by rfl⟩ : syracuseStep 1698161 = 1273621) B1273621
theorem B1698179 : Blo 1128631 1698179 := bstep (se 1 (by rfl) ⟨1273634, by rfl⟩ : syracuseStep 1698179 = 2547269) B2547269
theorem B1698209 : Blo 1128631 1698209 := bstep (se 2 (by rfl) ⟨636828, by rfl⟩ : syracuseStep 1698209 = 1273657) B1273657
theorem B1698227 : Blo 1128631 1698227 := bstep (se 1 (by rfl) ⟨1273670, by rfl⟩ : syracuseStep 1698227 = 2547341) B2547341
theorem B9660869 : Blo 1128631 9660869 := bstep (se 4 (by rfl) ⟨905706, by rfl⟩ : syracuseStep 9660869 = 1811413) B1811413
theorem B1698257 : Blo 1128631 1698257 := bstep (se 2 (by rfl) ⟨636846, by rfl⟩ : syracuseStep 1698257 = 1273693) B1273693
theorem B1698275 : Blo 1128631 1698275 := bstep (se 1 (by rfl) ⟨1273706, by rfl⟩ : syracuseStep 1698275 = 2547413) B2547413
theorem B1272307 : Blo 1128631 1272307 := bstep (se 1 (by rfl) ⟨954230, by rfl⟩ : syracuseStep 1272307 = 1908461) B1908461
theorem B1698305 : Blo 1128631 1698305 := bstep (se 2 (by rfl) ⟨636864, by rfl⟩ : syracuseStep 1698305 = 1273729) B1273729
theorem B1698323 : Blo 1128631 1698323 := bstep (se 1 (by rfl) ⟨1273742, by rfl⟩ : syracuseStep 1698323 = 2547485) B2547485
theorem B1698353 : Blo 1128631 1698353 := bstep (se 2 (by rfl) ⟨636882, by rfl⟩ : syracuseStep 1698353 = 1273765) B1273765
theorem B1698371 : Blo 1128631 1698371 := bstep (se 1 (by rfl) ⟨1273778, by rfl⟩ : syracuseStep 1698371 = 2547557) B2547557
theorem B1698401 : Blo 1128631 1698401 := bstep (se 2 (by rfl) ⟨636900, by rfl⟩ : syracuseStep 1698401 = 1273801) B1273801
theorem B1698419 : Blo 1128631 1698419 := bstep (se 1 (by rfl) ⟨1273814, by rfl⟩ : syracuseStep 1698419 = 2547629) B2547629
theorem B1272451 : Blo 1128631 1272451 := bstep (se 1 (by rfl) ⟨954338, by rfl⟩ : syracuseStep 1272451 = 1908677) B1908677
theorem B1698449 : Blo 1128631 1698449 := bstep (se 2 (by rfl) ⟨636918, by rfl⟩ : syracuseStep 1698449 = 1273837) B1273837
theorem B1206947 : Blo 1128631 1206947 := bstep (se 1 (by rfl) ⟨905210, by rfl⟩ : syracuseStep 1206947 = 1810421) B1810421
theorem B1698467 : Blo 1128631 1698467 := bstep (se 1 (by rfl) ⟨1273850, by rfl⟩ : syracuseStep 1698467 = 2547701) B2547701
theorem B6449827 : Blo 1128631 6449827 := bstep (se 1 (by rfl) ⟨4837370, by rfl⟩ : syracuseStep 6449827 = 9674741) B9674741
theorem B1698497 : Blo 1128631 1698497 := bstep (se 2 (by rfl) ⟨636936, by rfl⟩ : syracuseStep 1698497 = 1273873) B1273873
theorem B1698515 : Blo 1128631 1698515 := bstep (se 1 (by rfl) ⟨1273886, by rfl⟩ : syracuseStep 1698515 = 2547773) B2547773
theorem B1698545 : Blo 1128631 1698545 := bstep (se 2 (by rfl) ⟨636954, by rfl⟩ : syracuseStep 1698545 = 1273909) B1273909
theorem B1698563 : Blo 1128631 1698563 := bstep (se 1 (by rfl) ⟨1273922, by rfl⟩ : syracuseStep 1698563 = 2547845) B2547845
theorem B1272595 : Blo 1128631 1272595 := bstep (se 1 (by rfl) ⟨954446, by rfl⟩ : syracuseStep 1272595 = 1908893) B1908893
theorem B1698593 : Blo 1128631 1698593 := bstep (se 2 (by rfl) ⟨636972, by rfl⟩ : syracuseStep 1698593 = 1273945) B1273945
theorem B1698611 : Blo 1128631 1698611 := bstep (se 1 (by rfl) ⟨1273958, by rfl⟩ : syracuseStep 1698611 = 2547917) B2547917
theorem B1698641 : Blo 1128631 1698641 := bstep (se 2 (by rfl) ⟨636990, by rfl⟩ : syracuseStep 1698641 = 1273981) B1273981
theorem B1698659 : Blo 1128631 1698659 := bstep (se 1 (by rfl) ⟨1273994, by rfl⟩ : syracuseStep 1698659 = 2547989) B2547989
theorem B1698689 : Blo 1128631 1698689 := bstep (se 2 (by rfl) ⟨637008, by rfl⟩ : syracuseStep 1698689 = 1274017) B1274017
theorem B1698707 : Blo 1128631 1698707 := bstep (se 1 (by rfl) ⟨1274030, by rfl⟩ : syracuseStep 1698707 = 2548061) B2548061
theorem B1272739 : Blo 1128631 1272739 := bstep (se 1 (by rfl) ⟨954554, by rfl⟩ : syracuseStep 1272739 = 1909109) B1909109
theorem B1698737 : Blo 1128631 1698737 := bstep (se 2 (by rfl) ⟨637026, by rfl⟩ : syracuseStep 1698737 = 1274053) B1274053
theorem B2714563 : Blo 1128631 2714563 := bstep (se 1 (by rfl) ⟨2035922, by rfl⟩ : syracuseStep 2714563 = 4071845) B4071845
theorem B1698755 : Blo 1128631 1698755 := bstep (se 1 (by rfl) ⟨1274066, by rfl⟩ : syracuseStep 1698755 = 2548133) B2548133
theorem B1698785 : Blo 1128631 1698785 := bstep (se 2 (by rfl) ⟨637044, by rfl⟩ : syracuseStep 1698785 = 1274089) B1274089
theorem B1698803 : Blo 1128631 1698803 := bstep (se 1 (by rfl) ⟨1274102, by rfl⟩ : syracuseStep 1698803 = 2548205) B2548205
theorem B1698833 : Blo 1128631 1698833 := bstep (se 2 (by rfl) ⟨637062, by rfl⟩ : syracuseStep 1698833 = 1274125) B1274125
theorem B1698851 : Blo 1128631 1698851 := bstep (se 1 (by rfl) ⟨1274138, by rfl⟩ : syracuseStep 1698851 = 2548277) B2548277
theorem B3140653 : Blo 1128631 3140653 := bstep (se 3 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 3140653 = 1177745) B1177745
theorem B1272883 : Blo 1128631 1272883 := bstep (se 1 (by rfl) ⟨954662, by rfl⟩ : syracuseStep 1272883 = 1909325) B1909325
theorem B1698881 : Blo 1128631 1698881 := bstep (se 2 (by rfl) ⟨637080, by rfl⟩ : syracuseStep 1698881 = 1274161) B1274161
theorem B1698899 : Blo 1128631 1698899 := bstep (se 1 (by rfl) ⟨1274174, by rfl⟩ : syracuseStep 1698899 = 2548349) B2548349
theorem B1698929 : Blo 1128631 1698929 := bstep (se 2 (by rfl) ⟨637098, by rfl⟩ : syracuseStep 1698929 = 1274197) B1274197
theorem B1698947 : Blo 1128631 1698947 := bstep (se 1 (by rfl) ⟨1274210, by rfl⟩ : syracuseStep 1698947 = 2548421) B2548421
theorem B6450353 : Blo 1128631 6450353 := bstep (se 2 (by rfl) ⟨2418882, by rfl⟩ : syracuseStep 6450353 = 4837765) B4837765
theorem B1273027 : Blo 1128631 1273027 := bstep (se 1 (by rfl) ⟨954770, by rfl⟩ : syracuseStep 1273027 = 1909541) B1909541
theorem B15461603 : Blo 1128631 15461603 := bstep (se 1 (by rfl) ⟨11596202, by rfl⟩ : syracuseStep 15461603 = 23192405) B23192405
theorem B1273171 : Blo 1128631 1273171 := bstep (se 1 (by rfl) ⟨954878, by rfl⟩ : syracuseStep 1273171 = 1909757) B1909757
theorem B1273315 : Blo 1128631 1273315 := bstep (se 1 (by rfl) ⟨954986, by rfl⟩ : syracuseStep 1273315 = 1909973) B1909973
theorem B5729777 : Blo 1128631 5729777 := bstep (se 2 (by rfl) ⟨2148666, by rfl⟩ : syracuseStep 5729777 = 4297333) B4297333
theorem B4288099 : Blo 1128631 4288099 := bstep (se 1 (by rfl) ⟨3216074, by rfl⟩ : syracuseStep 4288099 = 6432149) B6432149
theorem B1273459 : Blo 1128631 1273459 := bstep (se 1 (by rfl) ⟨955094, by rfl⟩ : syracuseStep 1273459 = 1910189) B1910189
theorem B1961635 : Blo 1128631 1961635 := bstep (se 1 (by rfl) ⟨1471226, by rfl⟩ : syracuseStep 1961635 = 2942453) B2942453
theorem B1273603 : Blo 1128631 1273603 := bstep (se 1 (by rfl) ⟨955202, by rfl⟩ : syracuseStep 1273603 = 1910405) B1910405
theorem B3436301 : Blo 1128631 3436301 := bstep (se 3 (by rfl) ⟨644306, by rfl⟩ : syracuseStep 3436301 = 1288613) B1288613
theorem B1273747 : Blo 1128631 1273747 := bstep (se 1 (by rfl) ⟨955310, by rfl⟩ : syracuseStep 1273747 = 1910621) B1910621
theorem B2715601 : Blo 1128631 2715601 := bstep (se 2 (by rfl) ⟨1018350, by rfl⟩ : syracuseStep 2715601 = 2036701) B2036701
theorem B7237603 : Blo 1128631 7237603 := bstep (se 1 (by rfl) ⟨5428202, by rfl⟩ : syracuseStep 7237603 = 10856405) B10856405
theorem B1273891 : Blo 1128631 1273891 := bstep (se 1 (by rfl) ⟨955418, by rfl⟩ : syracuseStep 1273891 = 1910837) B1910837
theorem B1306675 : Blo 1128631 1306675 := bstep (se 1 (by rfl) ⟨980006, by rfl⟩ : syracuseStep 1306675 = 1960013) B1960013
theorem B1274035 : Blo 1128631 1274035 := bstep (se 1 (by rfl) ⟨955526, by rfl⟩ : syracuseStep 1274035 = 1911053) B1911053
theorem B1470739 : Blo 1128631 1470739 := bstep (se 1 (by rfl) ⟨1103054, by rfl⟩ : syracuseStep 1470739 = 2206109) B2206109
theorem B1274179 : Blo 1128631 1274179 := bstep (se 1 (by rfl) ⟨955634, by rfl⟩ : syracuseStep 1274179 = 1911269) B1911269
theorem B24441365 : Blo 1128631 24441365 := bstep (se 6 (by rfl) ⟨572844, by rfl⟩ : syracuseStep 24441365 = 1145689) B1145689
theorem B1208963 : Blo 1128631 1208963 := bstep (se 1 (by rfl) ⟨906722, by rfl⟩ : syracuseStep 1208963 = 1813445) B1813445
theorem B5731235 : Blo 1128631 5731235 := bstep (se 1 (by rfl) ⟨4298426, by rfl⟩ : syracuseStep 5731235 = 8596853) B8596853
theorem B7238605 : Blo 1128631 7238605 := bstep (se 3 (by rfl) ⟨1357238, by rfl⟩ : syracuseStep 7238605 = 2714477) B2714477
theorem B10581617 : Blo 1128631 10581617 := bstep (se 2 (by rfl) ⟨3968106, by rfl⟩ : syracuseStep 10581617 = 7936213) B7936213
theorem B18347633 : Blo 1128631 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B5732045 : Blo 1128631 5732045 := bstep (se 3 (by rfl) ⟨1074758, by rfl⟩ : syracuseStep 5732045 = 2149517) B2149517
theorem B4290317 : Blo 1128631 4290317 := bstep (se 3 (by rfl) ⟨804434, by rfl⟩ : syracuseStep 4290317 = 1608869) B1608869
theorem B16512821 : Blo 1128631 16512821 := bstep (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) B1548077
theorem B16316387 : Blo 1128631 16316387 := bstep (se 1 (by rfl) ⟨12237290, by rfl⟩ : syracuseStep 16316387 = 24474581) B24474581
theorem B5961869 : Blo 1128631 5961869 := bstep (se 3 (by rfl) ⟨1117850, by rfl⟩ : syracuseStep 5961869 = 2235701) B2235701
theorem B7829731 : Blo 1128631 7829731 := bstep (se 1 (by rfl) ⟨5872298, by rfl⟩ : syracuseStep 7829731 = 11744597) B11744597
theorem B82639075 : Blo 1128631 82639075 := bstep (se 1 (by rfl) ⟨61979306, by rfl⟩ : syracuseStep 82639075 = 123958613) B123958613
theorem B2291971 : Blo 1128631 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B2062883 : Blo 1128631 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B1145507 : Blo 1128631 1145507 := bstep (se 1 (by rfl) ⟨859130, by rfl⟩ : syracuseStep 1145507 = 1718261) B1718261
theorem B3439793 : Blo 1128631 3439793 := bstep (se 2 (by rfl) ⟨1289922, by rfl⟩ : syracuseStep 3439793 = 2579845) B2579845
theorem B4587313 : Blo 1128631 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B1933139 : Blo 1128631 1933139 := bstep (se 1 (by rfl) ⟨1449854, by rfl⟩ : syracuseStep 1933139 = 2899709) B2899709
theorem B1933463 : Blo 1128631 1933463 := bstep (se 1 (by rfl) ⟨1450097, by rfl⟩ : syracuseStep 1933463 = 2900195) B2900195
theorem B2720321 : Blo 1128631 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B8586161 : Blo 1128631 8586161 := bstep (se 2 (by rfl) ⟨3219810, by rfl⟩ : syracuseStep 8586161 = 6439621) B6439621
theorem B4588481 : Blo 1128631 4588481 := bstep (se 2 (by rfl) ⟨1720680, by rfl⟩ : syracuseStep 4588481 = 3441361) B3441361
theorem B2753587 : Blo 1128631 2753587 := bstep (se 1 (by rfl) ⟨2065190, by rfl⟩ : syracuseStep 2753587 = 4130381) B4130381
theorem B18580661 : Blo 1128631 18580661 := bstep (se 5 (by rfl) ⟨870968, by rfl⟩ : syracuseStep 18580661 = 1741937) B1741937
theorem B6980825 : Blo 1128631 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B8160587 : Blo 1128631 8160587 := bstep (se 1 (by rfl) ⟨6120440, by rfl⟩ : syracuseStep 8160587 = 12240881) B12240881
theorem B8586647 : Blo 1128631 8586647 := bstep (se 1 (by rfl) ⟨6439985, by rfl⟩ : syracuseStep 8586647 = 12879971) B12879971
theorem B4589101 : Blo 1128631 4589101 := bstep (se 3 (by rfl) ⟨860456, by rfl⟩ : syracuseStep 4589101 = 1720913) B1720913
theorem B3868249 : Blo 1128631 3868249 := bstep (se 2 (by rfl) ⟨1450593, by rfl⟩ : syracuseStep 3868249 = 2901187) B2901187
theorem B2295425 : Blo 1128631 2295425 := bstep (se 2 (by rfl) ⟨860784, by rfl⟩ : syracuseStep 2295425 = 1721569) B1721569
theorem B4294403 : Blo 1128631 4294403 := bstep (se 1 (by rfl) ⟨3220802, by rfl⟩ : syracuseStep 4294403 = 6441605) B6441605
theorem B4294417 : Blo 1128631 4294417 := bstep (se 2 (by rfl) ⟨1610406, by rfl⟩ : syracuseStep 4294417 = 3220813) B3220813
theorem B10618775 : Blo 1128631 10618775 := bstep (se 1 (by rfl) ⟨7964081, by rfl⟩ : syracuseStep 10618775 = 15928163) B15928163
theorem B5802029 : Blo 1128631 5802029 := bstep (se 3 (by rfl) ⟨1087880, by rfl⟩ : syracuseStep 5802029 = 2175761) B2175761
theorem B4294721 : Blo 1128631 4294721 := bstep (se 2 (by rfl) ⟨1610520, by rfl⟩ : syracuseStep 4294721 = 3221041) B3221041
theorem B4590103 : Blo 1128631 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B4295389 : Blo 1128631 4295389 := bstep (se 3 (by rfl) ⟨805385, by rfl⟩ : syracuseStep 4295389 = 1610771) B1610771
theorem B4590557 : Blo 1128631 4590557 := bstep (se 3 (by rfl) ⟨860729, by rfl⟩ : syracuseStep 4590557 = 1721459) B1721459
theorem B3673163 : Blo 1128631 3673163 := bstep (se 1 (by rfl) ⟨2754872, by rfl⟩ : syracuseStep 3673163 = 5509745) B5509745
theorem B18320705 : Blo 1128631 18320705 := bstep (se 2 (by rfl) ⟨6870264, by rfl⟩ : syracuseStep 18320705 = 13740529) B13740529
theorem B2035289 : Blo 1128631 2035289 := bstep (se 2 (by rfl) ⟨763233, by rfl⟩ : syracuseStep 2035289 = 1526467) B1526467
theorem B3215027 : Blo 1128631 3215027 := bstep (se 1 (by rfl) ⟨2411270, by rfl⟩ : syracuseStep 3215027 = 4822541) B4822541
theorem B5148467 : Blo 1128631 5148467 := bstep (se 1 (by rfl) ⟨3861350, by rfl⟩ : syracuseStep 5148467 = 7722701) B7722701
theorem B2035649 : Blo 1128631 2035649 := bstep (se 2 (by rfl) ⟨763368, by rfl⟩ : syracuseStep 2035649 = 1526737) B1526737
theorem B4296665 : Blo 1128631 4296665 := bstep (se 2 (by rfl) ⟨1611249, by rfl⟩ : syracuseStep 4296665 = 3222499) B3222499
theorem B2035801 : Blo 1128631 2035801 := bstep (se 2 (by rfl) ⟨763425, by rfl⟩ : syracuseStep 2035801 = 1526851) B1526851
theorem B1904843 : Blo 1128631 1904843 := bstep (se 1 (by rfl) ⟨1428632, by rfl⟩ : syracuseStep 1904843 = 2857265) B2857265
theorem B50172205 : Blo 1128631 50172205 := bstep (se 3 (by rfl) ⟨9407288, by rfl⟩ : syracuseStep 50172205 = 18814577) B18814577
theorem B1904971 : Blo 1128631 1904971 := bstep (se 1 (by rfl) ⟨1428728, by rfl⟩ : syracuseStep 1904971 = 2857457) B2857457
theorem B2232665 : Blo 1128631 2232665 := bstep (se 2 (by rfl) ⟨837249, by rfl⟩ : syracuseStep 2232665 = 1674499) B1674499
theorem B1905113 : Blo 1128631 1905113 := bstep (se 2 (by rfl) ⟨714417, by rfl⟩ : syracuseStep 1905113 = 1428835) B1428835
theorem B1610327 : Blo 1128631 1610327 := bstep (se 1 (by rfl) ⟨1207745, by rfl⟩ : syracuseStep 1610327 = 2415491) B2415491
theorem B1905241 : Blo 1128631 1905241 := bstep (se 2 (by rfl) ⟨714465, by rfl⟩ : syracuseStep 1905241 = 1428931) B1428931
theorem B10326707 : Blo 1128631 10326707 := bstep (se 1 (by rfl) ⟨7745030, by rfl⟩ : syracuseStep 10326707 = 15490061) B15490061
theorem B7344857 : Blo 1128631 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B4068299 : Blo 1128631 4068299 := bstep (se 1 (by rfl) ⟨3051224, by rfl⟩ : syracuseStep 4068299 = 6102449) B6102449
theorem B1905815 : Blo 1128631 1905815 := bstep (se 1 (by rfl) ⟨1429361, by rfl⟩ : syracuseStep 1905815 = 2858723) B2858723
theorem B1905943 : Blo 1128631 1905943 := bstep (se 1 (by rfl) ⟨1429457, by rfl⟩ : syracuseStep 1905943 = 2858915) B2858915
theorem B5969369 : Blo 1128631 5969369 := bstep (se 2 (by rfl) ⟨2238513, by rfl⟩ : syracuseStep 5969369 = 4477027) B4477027
theorem B4298291 : Blo 1128631 4298291 := bstep (se 1 (by rfl) ⟨3223718, by rfl⟩ : syracuseStep 4298291 = 6447437) B6447437
theorem B4298305 : Blo 1128631 4298305 := bstep (se 2 (by rfl) ⟨1611864, by rfl⟩ : syracuseStep 4298305 = 3223729) B3223729
theorem B1808011 : Blo 1128631 1808011 := bstep (se 1 (by rfl) ⟨1356008, by rfl⟩ : syracuseStep 1808011 = 2712017) B2712017
theorem B2758295 : Blo 1128631 2758295 := bstep (se 1 (by rfl) ⟨2068721, by rfl⟩ : syracuseStep 2758295 = 4137443) B4137443
theorem B1906571 : Blo 1128631 1906571 := bstep (se 1 (by rfl) ⟨1429928, by rfl⟩ : syracuseStep 1906571 = 2859857) B2859857
theorem B1906699 : Blo 1128631 1906699 := bstep (se 1 (by rfl) ⟨1430024, by rfl⟩ : syracuseStep 1906699 = 2860049) B2860049
theorem B1906841 : Blo 1128631 1906841 := bstep (se 2 (by rfl) ⟨715065, by rfl⟩ : syracuseStep 1906841 = 1430131) B1430131
theorem B2857153 : Blo 1128631 2857153 := bstep (se 2 (by rfl) ⟨1071432, by rfl⟩ : syracuseStep 2857153 = 2142865) B2142865
theorem B4069597 : Blo 1128631 4069597 := bstep (se 3 (by rfl) ⟨763049, by rfl⟩ : syracuseStep 4069597 = 1526099) B1526099
theorem B9672965 : Blo 1128631 9672965 := bstep (se 4 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 9672965 = 1813681) B1813681
theorem B1906969 : Blo 1128631 1906969 := bstep (se 2 (by rfl) ⟨715113, by rfl⟩ : syracuseStep 1906969 = 1430227) B1430227
theorem B3217715 : Blo 1128631 3217715 := bstep (se 1 (by rfl) ⟨2413286, by rfl⟩ : syracuseStep 3217715 = 4826573) B4826573
theorem B9181505 : Blo 1128631 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B3217943 : Blo 1128631 3217943 := bstep (se 1 (by rfl) ⟨2413457, by rfl⟩ : syracuseStep 3217943 = 4826915) B4826915
theorem B2857751 : Blo 1128631 2857751 := bstep (se 1 (by rfl) ⟨2143313, by rfl⟩ : syracuseStep 2857751 = 4286627) B4286627
theorem B3218251 : Blo 1128631 3218251 := bstep (se 1 (by rfl) ⟨2413688, by rfl⟩ : syracuseStep 3218251 = 4827377) B4827377
theorem B1907543 : Blo 1128631 1907543 := bstep (se 1 (by rfl) ⟨1430657, by rfl⟩ : syracuseStep 1907543 = 2861315) B2861315
theorem B1907671 : Blo 1128631 1907671 := bstep (se 1 (by rfl) ⟨1430753, by rfl⟩ : syracuseStep 1907671 = 2861507) B2861507
theorem B3054685 : Blo 1128631 3054685 := bstep (se 3 (by rfl) ⟨572753, by rfl⟩ : syracuseStep 3054685 = 1145507) B1145507
theorem B3218525 : Blo 1128631 3218525 := bstep (se 3 (by rfl) ⟨603473, by rfl⟩ : syracuseStep 3218525 = 1206947) B1206947
theorem B4070807 : Blo 1128631 4070807 := bstep (se 1 (by rfl) ⟨3053105, by rfl⟩ : syracuseStep 4070807 = 6106211) B6106211
theorem B4300235 : Blo 1128631 4300235 := bstep (se 1 (by rfl) ⟨3225176, by rfl⟩ : syracuseStep 4300235 = 6450353) B6450353
theorem B4300249 : Blo 1128631 4300249 := bstep (se 2 (by rfl) ⟨1612593, by rfl⟩ : syracuseStep 4300249 = 3225187) B3225187
theorem B2858561 : Blo 1128631 2858561 := bstep (se 2 (by rfl) ⟨1071960, by rfl⟩ : syracuseStep 2858561 = 2143921) B2143921
theorem B1908299 : Blo 1128631 1908299 := bstep (se 1 (by rfl) ⟨1431224, by rfl⟩ : syracuseStep 1908299 = 2862449) B2862449
theorem B1908427 : Blo 1128631 1908427 := bstep (se 1 (by rfl) ⟨1431320, by rfl⟩ : syracuseStep 1908427 = 2862641) B2862641
theorem B1908569 : Blo 1128631 1908569 := bstep (se 2 (by rfl) ⟨715713, by rfl⟩ : syracuseStep 1908569 = 1431427) B1431427
theorem B1908697 : Blo 1128631 1908697 := bstep (se 2 (by rfl) ⟨715761, by rfl⟩ : syracuseStep 1908697 = 1431523) B1431523
theorem B2859097 : Blo 1128631 2859097 := bstep (se 2 (by rfl) ⟨1072161, by rfl⟩ : syracuseStep 2859097 = 2144323) B2144323
theorem B3809483 : Blo 1128631 3809483 := bstep (se 1 (by rfl) ⟨2857112, by rfl⟩ : syracuseStep 3809483 = 5714225) B5714225
theorem B3055961 : Blo 1128631 3055961 := bstep (se 2 (by rfl) ⟨1145985, by rfl⟩ : syracuseStep 3055961 = 2291971) B2291971
theorem B16294243 : Blo 1128631 16294243 := bstep (se 1 (by rfl) ⟨12220682, by rfl⟩ : syracuseStep 16294243 = 24441365) B24441365
theorem B3809753 : Blo 1128631 3809753 := bstep (se 2 (by rfl) ⟨1428657, by rfl⟩ : syracuseStep 3809753 = 2857315) B2857315
theorem B8593937 : Blo 1128631 8593937 := bstep (se 2 (by rfl) ⟨3222726, by rfl⟩ : syracuseStep 8593937 = 6445453) B6445453
theorem B1909271 : Blo 1128631 1909271 := bstep (se 1 (by rfl) ⟨1431953, by rfl⟩ : syracuseStep 1909271 = 2863907) B2863907
theorem B1909399 : Blo 1128631 1909399 := bstep (se 1 (by rfl) ⟨1432049, by rfl⟩ : syracuseStep 1909399 = 2864099) B2864099
theorem B5808941 : Blo 1128631 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B7054411 : Blo 1128631 7054411 := bstep (se 1 (by rfl) ⟨5290808, by rfl⟩ : syracuseStep 7054411 = 10581617) B10581617
theorem B12231755 : Blo 1128631 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B3810455 : Blo 1128631 3810455 := bstep (se 1 (by rfl) ⟨2857841, by rfl⟩ : syracuseStep 3810455 = 5715683) B5715683
theorem B3220631 : Blo 1128631 3220631 := bstep (se 1 (by rfl) ⟨2415473, by rfl⟩ : syracuseStep 3220631 = 4830947) B4830947
theorem B2860211 : Blo 1128631 2860211 := bstep (se 1 (by rfl) ⟨2145158, by rfl⟩ : syracuseStep 2860211 = 4290317) B4290317
theorem B1910027 : Blo 1128631 1910027 := bstep (se 1 (by rfl) ⟨1432520, by rfl⟩ : syracuseStep 1910027 = 2865041) B2865041
theorem B1910155 : Blo 1128631 1910155 := bstep (se 1 (by rfl) ⟨1432616, by rfl⟩ : syracuseStep 1910155 = 2865233) B2865233
theorem B3974579 : Blo 1128631 3974579 := bstep (se 1 (by rfl) ⟨2980934, by rfl⟩ : syracuseStep 3974579 = 5961869) B5961869
theorem B2860505 : Blo 1128631 2860505 := bstep (se 2 (by rfl) ⟨1072689, by rfl⟩ : syracuseStep 2860505 = 2145379) B2145379
theorem B4826641 : Blo 1128631 4826641 := bstep (se 2 (by rfl) ⟨1809990, by rfl⟩ : syracuseStep 4826641 = 3619981) B3619981
theorem B1910297 : Blo 1128631 1910297 := bstep (se 2 (by rfl) ⟨716361, by rfl⟩ : syracuseStep 1910297 = 1432723) B1432723
theorem B6432331 : Blo 1128631 6432331 := bstep (se 1 (by rfl) ⟨4824248, by rfl⟩ : syracuseStep 6432331 = 9648497) B9648497
theorem B1910425 : Blo 1128631 1910425 := bstep (se 2 (by rfl) ⟨716409, by rfl⟩ : syracuseStep 1910425 = 1432819) B1432819
theorem B3810995 : Blo 1128631 3810995 := bstep (se 1 (by rfl) ⟨2858246, by rfl⟩ : syracuseStep 3810995 = 5716493) B5716493
theorem B6432605 : Blo 1128631 6432605 := bstep (se 3 (by rfl) ⟨1206113, by rfl⟩ : syracuseStep 6432605 = 2412227) B2412227
theorem B3811265 : Blo 1128631 3811265 := bstep (se 2 (by rfl) ⟨1429224, by rfl⟩ : syracuseStep 3811265 = 2858449) B2858449
theorem B3221441 : Blo 1128631 3221441 := bstep (se 2 (by rfl) ⟨1208040, by rfl⟩ : syracuseStep 3221441 = 2416081) B2416081
theorem B36710435 : Blo 1128631 36710435 := bstep (se 1 (by rfl) ⟨27532826, by rfl⟩ : syracuseStep 36710435 = 55065653) B55065653
theorem B1910999 : Blo 1128631 1910999 := bstep (se 1 (by rfl) ⟨1433249, by rfl⟩ : syracuseStep 1910999 = 2866499) B2866499
theorem B1911127 : Blo 1128631 1911127 := bstep (se 1 (by rfl) ⟨1433345, by rfl⟩ : syracuseStep 1911127 = 2866691) B2866691
theorem B4073921 : Blo 1128631 4073921 := bstep (se 2 (by rfl) ⟨1527720, by rfl⟩ : syracuseStep 4073921 = 3055441) B3055441
theorem B3811805 : Blo 1128631 3811805 := bstep (se 3 (by rfl) ⟨714713, by rfl⟩ : syracuseStep 3811805 = 1429427) B1429427
theorem B1288759 : Blo 1128631 1288759 := bstep (se 1 (by rfl) ⟨966569, by rfl⟩ : syracuseStep 1288759 = 1933139) B1933139
theorem B1813259 : Blo 1128631 1813259 := bstep (se 1 (by rfl) ⟨1359944, by rfl⟩ : syracuseStep 1813259 = 2719889) B2719889
theorem B1813271 : Blo 1128631 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B4074371 : Blo 1128631 4074371 := bstep (se 1 (by rfl) ⟨3055778, by rfl⟩ : syracuseStep 4074371 = 6111557) B6111557
theorem B1289143 : Blo 1128631 1289143 := bstep (se 1 (by rfl) ⟨966857, by rfl⟩ : syracuseStep 1289143 = 1933715) B1933715
theorem B2862155 : Blo 1128631 2862155 := bstep (se 1 (by rfl) ⟨2146616, by rfl⟩ : syracuseStep 2862155 = 4293233) B4293233
theorem B1256887 : Blo 1128631 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B1813963 : Blo 1128631 1813963 := bstep (se 1 (by rfl) ⟨1360472, by rfl⟩ : syracuseStep 1813963 = 2720945) B2720945
theorem B3223091 : Blo 1128631 3223091 := bstep (se 1 (by rfl) ⟨2417318, by rfl⟩ : syracuseStep 3223091 = 4834637) B4834637
theorem B3812939 : Blo 1128631 3812939 := bstep (se 1 (by rfl) ⟨2859704, by rfl⟩ : syracuseStep 3812939 = 5719409) B5719409
theorem B3223115 : Blo 1128631 3223115 := bstep (se 1 (by rfl) ⟨2417336, by rfl⟩ : syracuseStep 3223115 = 4834673) B4834673
theorem B1814233 : Blo 1128631 1814233 := bstep (se 2 (by rfl) ⟨680337, by rfl⟩ : syracuseStep 1814233 = 1360675) B1360675
theorem B8138501 : Blo 1128631 8138501 := bstep (se 4 (by rfl) ⟨762984, by rfl⟩ : syracuseStep 8138501 = 1525969) B1525969
theorem B5713739 : Blo 1128631 5713739 := bstep (se 1 (by rfl) ⟨4285304, by rfl⟩ : syracuseStep 5713739 = 8570609) B8570609
theorem B3813209 : Blo 1128631 3813209 := bstep (se 2 (by rfl) ⟨1429953, by rfl⟩ : syracuseStep 3813209 = 2859907) B2859907
theorem B4829017 : Blo 1128631 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B2863127 : Blo 1128631 2863127 := bstep (se 1 (by rfl) ⟨2147345, by rfl⟩ : syracuseStep 2863127 = 4294691) B4294691
theorem B8597825 : Blo 1128631 8597825 := bstep (se 2 (by rfl) ⟨3224184, by rfl⟩ : syracuseStep 8597825 = 6448369) B6448369
theorem B3223901 : Blo 1128631 3223901 := bstep (se 3 (by rfl) ⟨604481, by rfl⟩ : syracuseStep 3223901 = 1208963) B1208963
theorem B15446389 : Blo 1128631 15446389 := bstep (se 5 (by rfl) ⟨724049, by rfl⟩ : syracuseStep 15446389 = 1448099) B1448099
theorem B3813911 : Blo 1128631 3813911 := bstep (se 1 (by rfl) ⟨2860433, by rfl⟩ : syracuseStep 3813911 = 5720867) B5720867
theorem B2863795 : Blo 1128631 2863795 := bstep (se 1 (by rfl) ⟨2147846, by rfl⟩ : syracuseStep 2863795 = 4295693) B4295693
theorem B4829975 : Blo 1128631 4829975 := bstep (se 1 (by rfl) ⟨3622481, by rfl⟩ : syracuseStep 4829975 = 7244963) B7244963
theorem B2863937 : Blo 1128631 2863937 := bstep (se 2 (by rfl) ⟨1073976, by rfl⟩ : syracuseStep 2863937 = 2147953) B2147953
theorem B2143169 : Blo 1128631 2143169 := bstep (se 2 (by rfl) ⟨803688, by rfl⟩ : syracuseStep 2143169 = 1607377) B1607377
theorem B4076561 : Blo 1128631 4076561 := bstep (se 2 (by rfl) ⟨1528710, by rfl⟩ : syracuseStep 4076561 = 3057421) B3057421
theorem B3814451 : Blo 1128631 3814451 := bstep (se 1 (by rfl) ⟨2860838, by rfl⟩ : syracuseStep 3814451 = 5721677) B5721677
theorem B2143435 : Blo 1128631 2143435 := bstep (se 1 (by rfl) ⟨1607576, by rfl⟩ : syracuseStep 2143435 = 3215153) B3215153
theorem B3814721 : Blo 1128631 3814721 := bstep (se 2 (by rfl) ⟨1430520, by rfl⟩ : syracuseStep 3814721 = 2861041) B2861041
theorem B5715521 : Blo 1128631 5715521 := bstep (se 2 (by rfl) ⟨2143320, by rfl⟩ : syracuseStep 5715521 = 4286641) B4286641
theorem B4077149 : Blo 1128631 4077149 := bstep (se 3 (by rfl) ⟨764465, by rfl⟩ : syracuseStep 4077149 = 1528931) B1528931
theorem B9647747 : Blo 1128631 9647747 := bstep (se 1 (by rfl) ⟨7235810, by rfl⟩ : syracuseStep 9647747 = 14471621) B14471621
theorem B2143883 : Blo 1128631 2143883 := bstep (se 1 (by rfl) ⟨1607912, by rfl⟩ : syracuseStep 2143883 = 3215825) B3215825
theorem B2144065 : Blo 1128631 2144065 := bstep (se 2 (by rfl) ⟨804024, by rfl⟩ : syracuseStep 2144065 = 1608049) B1608049
theorem B3815261 : Blo 1128631 3815261 := bstep (se 3 (by rfl) ⟨715361, by rfl⟩ : syracuseStep 3815261 = 1430723) B1430723
theorem B4077485 : Blo 1128631 4077485 := bstep (se 3 (by rfl) ⟨764528, by rfl⟩ : syracuseStep 4077485 = 1529057) B1529057
theorem B16299953 : Blo 1128631 16299953 := bstep (se 2 (by rfl) ⟨6112482, by rfl⟩ : syracuseStep 16299953 = 12224965) B12224965
theorem B4962269 : Blo 1128631 4962269 := bstep (se 3 (by rfl) ⟨930425, by rfl⟩ : syracuseStep 4962269 = 1860851) B1860851
theorem B1161227 : Blo 1128631 1161227 := bstep (se 1 (by rfl) ⟨870920, by rfl⟩ : syracuseStep 1161227 = 1741841) B1741841
theorem B2865203 : Blo 1128631 2865203 := bstep (se 1 (by rfl) ⟨2148902, by rfl⟩ : syracuseStep 2865203 = 4297805) B4297805
theorem B2144407 : Blo 1128631 2144407 := bstep (se 1 (by rfl) ⟨1608305, by rfl⟩ : syracuseStep 2144407 = 3216611) B3216611
theorem B1128631 : Blo 1128631 1128631 := bstep (se 1 (by rfl) ⟨846473, by rfl⟩ : syracuseStep 1128631 = 1692947) B1692947
theorem B1128651 : Blo 1128631 1128651 := bstep (se 1 (by rfl) ⟨846488, by rfl⟩ : syracuseStep 1128651 = 1692977) B1692977
theorem B1128663 : Blo 1128631 1128663 := bstep (se 1 (by rfl) ⟨846497, by rfl⟩ : syracuseStep 1128663 = 1692995) B1692995
theorem B8599769 : Blo 1128631 8599769 := bstep (se 2 (by rfl) ⟨3224913, by rfl⟩ : syracuseStep 8599769 = 6449827) B6449827
theorem B1128683 : Blo 1128631 1128683 := bstep (se 1 (by rfl) ⟨846512, by rfl⟩ : syracuseStep 1128683 = 1693025) B1693025
theorem B1128695 : Blo 1128631 1128695 := bstep (se 1 (by rfl) ⟨846521, by rfl⟩ : syracuseStep 1128695 = 1693043) B1693043
theorem B1128715 : Blo 1128631 1128715 := bstep (se 1 (by rfl) ⟨846536, by rfl⟩ : syracuseStep 1128715 = 1693073) B1693073
theorem B1128727 : Blo 1128631 1128727 := bstep (se 1 (by rfl) ⟨846545, by rfl⟩ : syracuseStep 1128727 = 1693091) B1693091
theorem B1128747 : Blo 1128631 1128747 := bstep (se 1 (by rfl) ⟨846560, by rfl⟩ : syracuseStep 1128747 = 1693121) B1693121
theorem B1128759 : Blo 1128631 1128759 := bstep (se 1 (by rfl) ⟨846569, by rfl⟩ : syracuseStep 1128759 = 1693139) B1693139
theorem B1128779 : Blo 1128631 1128779 := bstep (se 1 (by rfl) ⟨846584, by rfl⟩ : syracuseStep 1128779 = 1693169) B1693169
theorem B1128791 : Blo 1128631 1128791 := bstep (se 1 (by rfl) ⟨846593, by rfl⟩ : syracuseStep 1128791 = 1693187) B1693187
theorem B1128811 : Blo 1128631 1128811 := bstep (se 1 (by rfl) ⟨846608, by rfl⟩ : syracuseStep 1128811 = 1693217) B1693217
theorem B2144627 : Blo 1128631 2144627 := bstep (se 1 (by rfl) ⟨1608470, by rfl⟩ : syracuseStep 2144627 = 3216941) B3216941
theorem B1128823 : Blo 1128631 1128823 := bstep (se 1 (by rfl) ⟨846617, by rfl⟩ : syracuseStep 1128823 = 1693235) B1693235
theorem B1128843 : Blo 1128631 1128843 := bstep (se 1 (by rfl) ⟨846632, by rfl⟩ : syracuseStep 1128843 = 1693265) B1693265
theorem B1128855 : Blo 1128631 1128855 := bstep (se 1 (by rfl) ⟨846641, by rfl⟩ : syracuseStep 1128855 = 1693283) B1693283
theorem B1128875 : Blo 1128631 1128875 := bstep (se 1 (by rfl) ⟨846656, by rfl⟩ : syracuseStep 1128875 = 1693313) B1693313
theorem B1128887 : Blo 1128631 1128887 := bstep (se 1 (by rfl) ⟨846665, by rfl⟩ : syracuseStep 1128887 = 1693331) B1693331
theorem B1128907 : Blo 1128631 1128907 := bstep (se 1 (by rfl) ⟨846680, by rfl⟩ : syracuseStep 1128907 = 1693361) B1693361
theorem B1128919 : Blo 1128631 1128919 := bstep (se 1 (by rfl) ⟨846689, by rfl⟩ : syracuseStep 1128919 = 1693379) B1693379
theorem B1128939 : Blo 1128631 1128939 := bstep (se 1 (by rfl) ⟨846704, by rfl⟩ : syracuseStep 1128939 = 1693409) B1693409
theorem B1128951 : Blo 1128631 1128951 := bstep (se 1 (by rfl) ⟨846713, by rfl⟩ : syracuseStep 1128951 = 1693427) B1693427
theorem B1128971 : Blo 1128631 1128971 := bstep (se 1 (by rfl) ⟨846728, by rfl⟩ : syracuseStep 1128971 = 1693457) B1693457
theorem B1128983 : Blo 1128631 1128983 := bstep (se 1 (by rfl) ⟨846737, by rfl⟩ : syracuseStep 1128983 = 1693475) B1693475
theorem B1129003 : Blo 1128631 1129003 := bstep (se 1 (by rfl) ⟨846752, by rfl⟩ : syracuseStep 1129003 = 1693505) B1693505
theorem B1129015 : Blo 1128631 1129015 := bstep (se 1 (by rfl) ⟨846761, by rfl⟩ : syracuseStep 1129015 = 1693523) B1693523
theorem B1129035 : Blo 1128631 1129035 := bstep (se 1 (by rfl) ⟨846776, by rfl⟩ : syracuseStep 1129035 = 1693553) B1693553
theorem B2865739 : Blo 1128631 2865739 := bstep (se 1 (by rfl) ⟨2149304, by rfl⟩ : syracuseStep 2865739 = 4298609) B4298609
theorem B1129047 : Blo 1128631 1129047 := bstep (se 1 (by rfl) ⟨846785, by rfl⟩ : syracuseStep 1129047 = 1693571) B1693571
theorem B2144855 : Blo 1128631 2144855 := bstep (se 1 (by rfl) ⟨1608641, by rfl⟩ : syracuseStep 2144855 = 3217283) B3217283
theorem B3619417 : Blo 1128631 3619417 := bstep (se 2 (by rfl) ⟨1357281, by rfl⟩ : syracuseStep 3619417 = 2714563) B2714563
theorem B1129067 : Blo 1128631 1129067 := bstep (se 1 (by rfl) ⟨846800, by rfl⟩ : syracuseStep 1129067 = 1693601) B1693601
theorem B1129079 : Blo 1128631 1129079 := bstep (se 1 (by rfl) ⟨846809, by rfl⟩ : syracuseStep 1129079 = 1693619) B1693619
theorem B1129099 : Blo 1128631 1129099 := bstep (se 1 (by rfl) ⟨846824, by rfl⟩ : syracuseStep 1129099 = 1693649) B1693649
theorem B1129111 : Blo 1128631 1129111 := bstep (se 1 (by rfl) ⟨846833, by rfl⟩ : syracuseStep 1129111 = 1693667) B1693667
theorem B1129131 : Blo 1128631 1129131 := bstep (se 1 (by rfl) ⟨846848, by rfl⟩ : syracuseStep 1129131 = 1693697) B1693697
theorem B1129143 : Blo 1128631 1129143 := bstep (se 1 (by rfl) ⟨846857, by rfl⟩ : syracuseStep 1129143 = 1693715) B1693715
theorem B1129163 : Blo 1128631 1129163 := bstep (se 1 (by rfl) ⟨846872, by rfl⟩ : syracuseStep 1129163 = 1693745) B1693745
theorem B1129175 : Blo 1128631 1129175 := bstep (se 1 (by rfl) ⟨846881, by rfl⟩ : syracuseStep 1129175 = 1693763) B1693763
theorem B2865881 : Blo 1128631 2865881 := bstep (se 2 (by rfl) ⟨1074705, by rfl⟩ : syracuseStep 2865881 = 2149411) B2149411
theorem B1129195 : Blo 1128631 1129195 := bstep (se 1 (by rfl) ⟨846896, by rfl⟩ : syracuseStep 1129195 = 1693793) B1693793
theorem B1129207 : Blo 1128631 1129207 := bstep (se 1 (by rfl) ⟨846905, by rfl⟩ : syracuseStep 1129207 = 1693811) B1693811
theorem B1129227 : Blo 1128631 1129227 := bstep (se 1 (by rfl) ⟨846920, by rfl⟩ : syracuseStep 1129227 = 1693841) B1693841
theorem B1129239 : Blo 1128631 1129239 := bstep (se 1 (by rfl) ⟨846929, by rfl⟩ : syracuseStep 1129239 = 1693859) B1693859
theorem B1129259 : Blo 1128631 1129259 := bstep (se 1 (by rfl) ⟨846944, by rfl⟩ : syracuseStep 1129259 = 1693889) B1693889
theorem B1129271 : Blo 1128631 1129271 := bstep (se 1 (by rfl) ⟨846953, by rfl⟩ : syracuseStep 1129271 = 1693907) B1693907
theorem B15448897 : Blo 1128631 15448897 := bstep (se 2 (by rfl) ⟨5793336, by rfl⟩ : syracuseStep 15448897 = 11586673) B11586673
theorem B1129291 : Blo 1128631 1129291 := bstep (se 1 (by rfl) ⟨846968, by rfl⟩ : syracuseStep 1129291 = 1693937) B1693937
theorem B4832075 : Blo 1128631 4832075 := bstep (se 1 (by rfl) ⟨3624056, by rfl⟩ : syracuseStep 4832075 = 7248113) B7248113
theorem B1129303 : Blo 1128631 1129303 := bstep (se 1 (by rfl) ⟨846977, by rfl⟩ : syracuseStep 1129303 = 1693955) B1693955
theorem B2145113 : Blo 1128631 2145113 := bstep (se 2 (by rfl) ⟨804417, by rfl⟩ : syracuseStep 2145113 = 1608835) B1608835
theorem B1129323 : Blo 1128631 1129323 := bstep (se 1 (by rfl) ⟨846992, by rfl⟩ : syracuseStep 1129323 = 1693985) B1693985
theorem B1129335 : Blo 1128631 1129335 := bstep (se 1 (by rfl) ⟨847001, by rfl⟩ : syracuseStep 1129335 = 1694003) B1694003
theorem B1129355 : Blo 1128631 1129355 := bstep (se 1 (by rfl) ⟨847016, by rfl⟩ : syracuseStep 1129355 = 1694033) B1694033
theorem B1129367 : Blo 1128631 1129367 := bstep (se 1 (by rfl) ⟨847025, by rfl⟩ : syracuseStep 1129367 = 1694051) B1694051
theorem B1129387 : Blo 1128631 1129387 := bstep (se 1 (by rfl) ⟨847040, by rfl⟩ : syracuseStep 1129387 = 1694081) B1694081
theorem B1129399 : Blo 1128631 1129399 := bstep (se 1 (by rfl) ⟨847049, by rfl⟩ : syracuseStep 1129399 = 1694099) B1694099
theorem B1129419 : Blo 1128631 1129419 := bstep (se 1 (by rfl) ⟨847064, by rfl⟩ : syracuseStep 1129419 = 1694129) B1694129
theorem B3816395 : Blo 1128631 3816395 := bstep (se 1 (by rfl) ⟨2862296, by rfl⟩ : syracuseStep 3816395 = 5724593) B5724593
theorem B1129431 : Blo 1128631 1129431 := bstep (se 1 (by rfl) ⟨847073, by rfl⟩ : syracuseStep 1129431 = 1694147) B1694147
theorem B1129451 : Blo 1128631 1129451 := bstep (se 1 (by rfl) ⟨847088, by rfl⟩ : syracuseStep 1129451 = 1694177) B1694177
theorem B1129463 : Blo 1128631 1129463 := bstep (se 1 (by rfl) ⟨847097, by rfl⟩ : syracuseStep 1129463 = 1694195) B1694195
theorem B1129483 : Blo 1128631 1129483 := bstep (se 1 (by rfl) ⟨847112, by rfl⟩ : syracuseStep 1129483 = 1694225) B1694225
theorem B1129495 : Blo 1128631 1129495 := bstep (se 1 (by rfl) ⟨847121, by rfl⟩ : syracuseStep 1129495 = 1694243) B1694243
theorem B1129515 : Blo 1128631 1129515 := bstep (se 1 (by rfl) ⟨847136, by rfl⟩ : syracuseStep 1129515 = 1694273) B1694273
theorem B4078637 : Blo 1128631 4078637 := bstep (se 3 (by rfl) ⟨764744, by rfl⟩ : syracuseStep 4078637 = 1529489) B1529489
theorem B1129527 : Blo 1128631 1129527 := bstep (se 1 (by rfl) ⟨847145, by rfl⟩ : syracuseStep 1129527 = 1694291) B1694291
theorem B1129547 : Blo 1128631 1129547 := bstep (se 1 (by rfl) ⟨847160, by rfl⟩ : syracuseStep 1129547 = 1694321) B1694321
theorem B1129559 : Blo 1128631 1129559 := bstep (se 1 (by rfl) ⟨847169, by rfl⟩ : syracuseStep 1129559 = 1694339) B1694339
theorem B6437981 : Blo 1128631 6437981 := bstep (se 3 (by rfl) ⟨1207121, by rfl⟩ : syracuseStep 6437981 = 2414243) B2414243
theorem B1129579 : Blo 1128631 1129579 := bstep (se 1 (by rfl) ⟨847184, by rfl⟩ : syracuseStep 1129579 = 1694369) B1694369
theorem B1129591 : Blo 1128631 1129591 := bstep (se 1 (by rfl) ⟨847193, by rfl⟩ : syracuseStep 1129591 = 1694387) B1694387
theorem B1129611 : Blo 1128631 1129611 := bstep (se 1 (by rfl) ⟨847208, by rfl⟩ : syracuseStep 1129611 = 1694417) B1694417
theorem B1129623 : Blo 1128631 1129623 := bstep (se 1 (by rfl) ⟨847217, by rfl⟩ : syracuseStep 1129623 = 1694435) B1694435
theorem B1129643 : Blo 1128631 1129643 := bstep (se 1 (by rfl) ⟨847232, by rfl⟩ : syracuseStep 1129643 = 1694465) B1694465
theorem B1129655 : Blo 1128631 1129655 := bstep (se 1 (by rfl) ⟨847241, by rfl⟩ : syracuseStep 1129655 = 1694483) B1694483
theorem B1129675 : Blo 1128631 1129675 := bstep (se 1 (by rfl) ⟨847256, by rfl⟩ : syracuseStep 1129675 = 1694513) B1694513
theorem B1129687 : Blo 1128631 1129687 := bstep (se 1 (by rfl) ⟨847265, by rfl⟩ : syracuseStep 1129687 = 1694531) B1694531
theorem B3816665 : Blo 1128631 3816665 := bstep (se 2 (by rfl) ⟨1431249, by rfl⟩ : syracuseStep 3816665 = 2862499) B2862499
theorem B1129707 : Blo 1128631 1129707 := bstep (se 1 (by rfl) ⟨847280, by rfl⟩ : syracuseStep 1129707 = 1694561) B1694561
theorem B2145523 : Blo 1128631 2145523 := bstep (se 1 (by rfl) ⟨1609142, by rfl⟩ : syracuseStep 2145523 = 3218285) B3218285
theorem B1129719 : Blo 1128631 1129719 := bstep (se 1 (by rfl) ⟨847289, by rfl⟩ : syracuseStep 1129719 = 1694579) B1694579
theorem B1129739 : Blo 1128631 1129739 := bstep (se 1 (by rfl) ⟨847304, by rfl⟩ : syracuseStep 1129739 = 1694609) B1694609
theorem B1359127 : Blo 1128631 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B1129751 : Blo 1128631 1129751 := bstep (se 1 (by rfl) ⟨847313, by rfl⟩ : syracuseStep 1129751 = 1694627) B1694627
theorem B1129771 : Blo 1128631 1129771 := bstep (se 1 (by rfl) ⟨847328, by rfl⟩ : syracuseStep 1129771 = 1694657) B1694657
theorem B1129783 : Blo 1128631 1129783 := bstep (se 1 (by rfl) ⟨847337, by rfl⟩ : syracuseStep 1129783 = 1694675) B1694675
theorem B1129803 : Blo 1128631 1129803 := bstep (se 1 (by rfl) ⟨847352, by rfl⟩ : syracuseStep 1129803 = 1694705) B1694705
theorem B1129815 : Blo 1128631 1129815 := bstep (se 1 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 1129815 = 1694723) B1694723
theorem B1129835 : Blo 1128631 1129835 := bstep (se 1 (by rfl) ⟨847376, by rfl⟩ : syracuseStep 1129835 = 1694753) B1694753
theorem B1129847 : Blo 1128631 1129847 := bstep (se 1 (by rfl) ⟨847385, by rfl⟩ : syracuseStep 1129847 = 1694771) B1694771
theorem B1129867 : Blo 1128631 1129867 := bstep (se 1 (by rfl) ⟨847400, by rfl⟩ : syracuseStep 1129867 = 1694801) B1694801
theorem B1129879 : Blo 1128631 1129879 := bstep (se 1 (by rfl) ⟨847409, by rfl⟩ : syracuseStep 1129879 = 1694819) B1694819
theorem B1129899 : Blo 1128631 1129899 := bstep (se 1 (by rfl) ⟨847424, by rfl⟩ : syracuseStep 1129899 = 1694849) B1694849
theorem B1129911 : Blo 1128631 1129911 := bstep (se 1 (by rfl) ⟨847433, by rfl⟩ : syracuseStep 1129911 = 1694867) B1694867
theorem B1129931 : Blo 1128631 1129931 := bstep (se 1 (by rfl) ⟨847448, by rfl⟩ : syracuseStep 1129931 = 1694897) B1694897
theorem B1129943 : Blo 1128631 1129943 := bstep (se 1 (by rfl) ⟨847457, by rfl⟩ : syracuseStep 1129943 = 1694915) B1694915
theorem B5717465 : Blo 1128631 5717465 := bstep (se 2 (by rfl) ⟨2144049, by rfl⟩ : syracuseStep 5717465 = 4288099) B4288099
theorem B1129963 : Blo 1128631 1129963 := bstep (se 1 (by rfl) ⟨847472, by rfl⟩ : syracuseStep 1129963 = 1694945) B1694945
theorem B1129975 : Blo 1128631 1129975 := bstep (se 1 (by rfl) ⟨847481, by rfl⟩ : syracuseStep 1129975 = 1694963) B1694963
theorem B1129995 : Blo 1128631 1129995 := bstep (se 1 (by rfl) ⟨847496, by rfl⟩ : syracuseStep 1129995 = 1694993) B1694993
theorem B1130007 : Blo 1128631 1130007 := bstep (se 1 (by rfl) ⟨847505, by rfl⟩ : syracuseStep 1130007 = 1695011) B1695011
theorem B2866711 : Blo 1128631 2866711 := bstep (se 1 (by rfl) ⟨2150033, by rfl⟩ : syracuseStep 2866711 = 4300067) B4300067
theorem B1130027 : Blo 1128631 1130027 := bstep (se 1 (by rfl) ⟨847520, by rfl⟩ : syracuseStep 1130027 = 1695041) B1695041
theorem B1130039 : Blo 1128631 1130039 := bstep (se 1 (by rfl) ⟨847529, by rfl⟩ : syracuseStep 1130039 = 1695059) B1695059
theorem B1130059 : Blo 1128631 1130059 := bstep (se 1 (by rfl) ⟨847544, by rfl⟩ : syracuseStep 1130059 = 1695089) B1695089
theorem B1130071 : Blo 1128631 1130071 := bstep (se 1 (by rfl) ⟨847553, by rfl⟩ : syracuseStep 1130071 = 1695107) B1695107
theorem B1130091 : Blo 1128631 1130091 := bstep (se 1 (by rfl) ⟨847568, by rfl⟩ : syracuseStep 1130091 = 1695137) B1695137
theorem B1130103 : Blo 1128631 1130103 := bstep (se 1 (by rfl) ⟨847577, by rfl⟩ : syracuseStep 1130103 = 1695155) B1695155
theorem B1130123 : Blo 1128631 1130123 := bstep (se 1 (by rfl) ⟨847592, by rfl⟩ : syracuseStep 1130123 = 1695185) B1695185
theorem B1130135 : Blo 1128631 1130135 := bstep (se 1 (by rfl) ⟨847601, by rfl⟩ : syracuseStep 1130135 = 1695203) B1695203
theorem B1359511 : Blo 1128631 1359511 := bstep (se 1 (by rfl) ⟨1019633, by rfl⟩ : syracuseStep 1359511 = 2039267) B2039267
theorem B1130155 : Blo 1128631 1130155 := bstep (se 1 (by rfl) ⟨847616, by rfl⟩ : syracuseStep 1130155 = 1695233) B1695233
theorem B1130167 : Blo 1128631 1130167 := bstep (se 1 (by rfl) ⟨847625, by rfl⟩ : syracuseStep 1130167 = 1695251) B1695251
theorem B1130187 : Blo 1128631 1130187 := bstep (se 1 (by rfl) ⟨847640, by rfl⟩ : syracuseStep 1130187 = 1695281) B1695281
theorem B1130199 : Blo 1128631 1130199 := bstep (se 1 (by rfl) ⟨847649, by rfl⟩ : syracuseStep 1130199 = 1695299) B1695299
theorem B6864601 : Blo 1128631 6864601 := bstep (se 2 (by rfl) ⟨2574225, by rfl⟩ : syracuseStep 6864601 = 5148451) B5148451
theorem B2146009 : Blo 1128631 2146009 := bstep (se 2 (by rfl) ⟨804753, by rfl⟩ : syracuseStep 2146009 = 1609507) B1609507
theorem B1130219 : Blo 1128631 1130219 := bstep (se 1 (by rfl) ⟨847664, by rfl⟩ : syracuseStep 1130219 = 1695329) B1695329
theorem B1130231 : Blo 1128631 1130231 := bstep (se 1 (by rfl) ⟨847673, by rfl⟩ : syracuseStep 1130231 = 1695347) B1695347
theorem B1130251 : Blo 1128631 1130251 := bstep (se 1 (by rfl) ⟨847688, by rfl⟩ : syracuseStep 1130251 = 1695377) B1695377
theorem B1130263 : Blo 1128631 1130263 := bstep (se 1 (by rfl) ⟨847697, by rfl⟩ : syracuseStep 1130263 = 1695395) B1695395
theorem B1130283 : Blo 1128631 1130283 := bstep (se 1 (by rfl) ⟨847712, by rfl⟩ : syracuseStep 1130283 = 1695425) B1695425
theorem B1130295 : Blo 1128631 1130295 := bstep (se 1 (by rfl) ⟨847721, by rfl⟩ : syracuseStep 1130295 = 1695443) B1695443
theorem B3260225 : Blo 1128631 3260225 := bstep (se 2 (by rfl) ⟨1222584, by rfl⟩ : syracuseStep 3260225 = 2445169) B2445169
theorem B1130315 : Blo 1128631 1130315 := bstep (se 1 (by rfl) ⟨847736, by rfl⟩ : syracuseStep 1130315 = 1695473) B1695473
theorem B1130327 : Blo 1128631 1130327 := bstep (se 1 (by rfl) ⟨847745, by rfl⟩ : syracuseStep 1130327 = 1695491) B1695491
theorem B1130347 : Blo 1128631 1130347 := bstep (se 1 (by rfl) ⟨847760, by rfl⟩ : syracuseStep 1130347 = 1695521) B1695521
theorem B1130359 : Blo 1128631 1130359 := bstep (se 1 (by rfl) ⟨847769, by rfl⟩ : syracuseStep 1130359 = 1695539) B1695539
theorem B1130379 : Blo 1128631 1130379 := bstep (se 1 (by rfl) ⟨847784, by rfl⟩ : syracuseStep 1130379 = 1695569) B1695569
theorem B1130391 : Blo 1128631 1130391 := bstep (se 1 (by rfl) ⟨847793, by rfl⟩ : syracuseStep 1130391 = 1695587) B1695587
theorem B3817367 : Blo 1128631 3817367 := bstep (se 1 (by rfl) ⟨2863025, by rfl⟩ : syracuseStep 3817367 = 5726051) B5726051
theorem B1130411 : Blo 1128631 1130411 := bstep (se 1 (by rfl) ⟨847808, by rfl⟩ : syracuseStep 1130411 = 1695617) B1695617
theorem B1130423 : Blo 1128631 1130423 := bstep (se 1 (by rfl) ⟨847817, by rfl⟩ : syracuseStep 1130423 = 1695635) B1695635
theorem B2539457 : Blo 1128631 2539457 := bstep (se 2 (by rfl) ⟨952296, by rfl⟩ : syracuseStep 2539457 = 1904593) B1904593
theorem B3620801 : Blo 1128631 3620801 := bstep (se 2 (by rfl) ⟨1357800, by rfl⟩ : syracuseStep 3620801 = 2715601) B2715601
theorem B1130443 : Blo 1128631 1130443 := bstep (se 1 (by rfl) ⟨847832, by rfl⟩ : syracuseStep 1130443 = 1695665) B1695665
theorem B1130455 : Blo 1128631 1130455 := bstep (se 1 (by rfl) ⟨847841, by rfl⟩ : syracuseStep 1130455 = 1695683) B1695683
theorem B9650137 : Blo 1128631 9650137 := bstep (se 2 (by rfl) ⟨3618801, by rfl⟩ : syracuseStep 9650137 = 7237603) B7237603
theorem B1130475 : Blo 1128631 1130475 := bstep (se 1 (by rfl) ⟨847856, by rfl⟩ : syracuseStep 1130475 = 1695713) B1695713
theorem B1130487 : Blo 1128631 1130487 := bstep (se 1 (by rfl) ⟨847865, by rfl⟩ : syracuseStep 1130487 = 1695731) B1695731
theorem B1130507 : Blo 1128631 1130507 := bstep (se 1 (by rfl) ⟨847880, by rfl⟩ : syracuseStep 1130507 = 1695761) B1695761
theorem B1130519 : Blo 1128631 1130519 := bstep (se 1 (by rfl) ⟨847889, by rfl⟩ : syracuseStep 1130519 = 1695779) B1695779
theorem B1130539 : Blo 1128631 1130539 := bstep (se 1 (by rfl) ⟨847904, by rfl⟩ : syracuseStep 1130539 = 1695809) B1695809
theorem B1130551 : Blo 1128631 1130551 := bstep (se 1 (by rfl) ⟨847913, by rfl⟩ : syracuseStep 1130551 = 1695827) B1695827
theorem B1130571 : Blo 1128631 1130571 := bstep (se 1 (by rfl) ⟨847928, by rfl⟩ : syracuseStep 1130571 = 1695857) B1695857
theorem B1130583 : Blo 1128631 1130583 := bstep (se 1 (by rfl) ⟨847937, by rfl⟩ : syracuseStep 1130583 = 1695875) B1695875
theorem B1130603 : Blo 1128631 1130603 := bstep (se 1 (by rfl) ⟨847952, by rfl⟩ : syracuseStep 1130603 = 1695905) B1695905
theorem B1130615 : Blo 1128631 1130615 := bstep (se 1 (by rfl) ⟨847961, by rfl⟩ : syracuseStep 1130615 = 1695923) B1695923
theorem B4079747 : Blo 1128631 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B1130635 : Blo 1128631 1130635 := bstep (se 1 (by rfl) ⟨847976, by rfl⟩ : syracuseStep 1130635 = 1695953) B1695953
theorem B1130647 : Blo 1128631 1130647 := bstep (se 1 (by rfl) ⟨847985, by rfl⟩ : syracuseStep 1130647 = 1695971) B1695971
theorem B2539673 : Blo 1128631 2539673 := bstep (se 2 (by rfl) ⟨952377, by rfl⟩ : syracuseStep 2539673 = 1904755) B1904755
theorem B1130667 : Blo 1128631 1130667 := bstep (se 1 (by rfl) ⟨848000, by rfl⟩ : syracuseStep 1130667 = 1696001) B1696001
theorem B1130679 : Blo 1128631 1130679 := bstep (se 1 (by rfl) ⟨848009, by rfl⟩ : syracuseStep 1130679 = 1696019) B1696019
theorem B1130699 : Blo 1128631 1130699 := bstep (se 1 (by rfl) ⟨848024, by rfl⟩ : syracuseStep 1130699 = 1696049) B1696049
theorem B1130711 : Blo 1128631 1130711 := bstep (se 1 (by rfl) ⟨848033, by rfl⟩ : syracuseStep 1130711 = 1696067) B1696067
theorem B1130731 : Blo 1128631 1130731 := bstep (se 1 (by rfl) ⟨848048, by rfl⟩ : syracuseStep 1130731 = 1696097) B1696097
theorem B2539763 : Blo 1128631 2539763 := bstep (se 1 (by rfl) ⟨1904822, by rfl⟩ : syracuseStep 2539763 = 3809645) B3809645
theorem B1130743 : Blo 1128631 1130743 := bstep (se 1 (by rfl) ⟨848057, by rfl⟩ : syracuseStep 1130743 = 1696115) B1696115
theorem B2146571 : Blo 1128631 2146571 := bstep (se 1 (by rfl) ⟨1609928, by rfl⟩ : syracuseStep 2146571 = 3219857) B3219857
theorem B1130763 : Blo 1128631 1130763 := bstep (se 1 (by rfl) ⟨848072, by rfl⟩ : syracuseStep 1130763 = 1696145) B1696145
theorem B2539799 : Blo 1128631 2539799 := bstep (se 1 (by rfl) ⟨1904849, by rfl⟩ : syracuseStep 2539799 = 3809699) B3809699
theorem B1130775 : Blo 1128631 1130775 := bstep (se 1 (by rfl) ⟨848081, by rfl⟩ : syracuseStep 1130775 = 1696163) B1696163
theorem B1130795 : Blo 1128631 1130795 := bstep (se 1 (by rfl) ⟨848096, by rfl⟩ : syracuseStep 1130795 = 1696193) B1696193
theorem B4079917 : Blo 1128631 4079917 := bstep (se 3 (by rfl) ⟨764984, by rfl⟩ : syracuseStep 4079917 = 1529969) B1529969
theorem B1130807 : Blo 1128631 1130807 := bstep (se 1 (by rfl) ⟨848105, by rfl⟩ : syracuseStep 1130807 = 1696211) B1696211
theorem B1130827 : Blo 1128631 1130827 := bstep (se 1 (by rfl) ⟨848120, by rfl⟩ : syracuseStep 1130827 = 1696241) B1696241
theorem B1130839 : Blo 1128631 1130839 := bstep (se 1 (by rfl) ⟨848129, by rfl⟩ : syracuseStep 1130839 = 1696259) B1696259
theorem B1130859 : Blo 1128631 1130859 := bstep (se 1 (by rfl) ⟨848144, by rfl⟩ : syracuseStep 1130859 = 1696289) B1696289
theorem B1130871 : Blo 1128631 1130871 := bstep (se 1 (by rfl) ⟨848153, by rfl⟩ : syracuseStep 1130871 = 1696307) B1696307
theorem B1130891 : Blo 1128631 1130891 := bstep (se 1 (by rfl) ⟨848168, by rfl⟩ : syracuseStep 1130891 = 1696337) B1696337
theorem B1130903 : Blo 1128631 1130903 := bstep (se 1 (by rfl) ⟨848177, by rfl⟩ : syracuseStep 1130903 = 1696355) B1696355
theorem B1130923 : Blo 1128631 1130923 := bstep (se 1 (by rfl) ⟨848192, by rfl⟩ : syracuseStep 1130923 = 1696385) B1696385
theorem B3817907 : Blo 1128631 3817907 := bstep (se 1 (by rfl) ⟨2863430, by rfl⟩ : syracuseStep 3817907 = 5726861) B5726861
theorem B4833715 : Blo 1128631 4833715 := bstep (se 1 (by rfl) ⟨3625286, by rfl⟩ : syracuseStep 4833715 = 7250573) B7250573
theorem B1130935 : Blo 1128631 1130935 := bstep (se 1 (by rfl) ⟨848201, by rfl⟩ : syracuseStep 1130935 = 1696403) B1696403
theorem B2146753 : Blo 1128631 2146753 := bstep (se 2 (by rfl) ⟨805032, by rfl⟩ : syracuseStep 2146753 = 1610065) B1610065
theorem B847561157 : Blo 1128631 847561157 := bstep (se 4 (by rfl) ⟨79458858, by rfl⟩ : syracuseStep 847561157 = 158917717) B158917717
theorem B2539979 : Blo 1128631 2539979 := bstep (se 1 (by rfl) ⟨1904984, by rfl⟩ : syracuseStep 2539979 = 3809969) B3809969
theorem B1130955 : Blo 1128631 1130955 := bstep (se 1 (by rfl) ⟨848216, by rfl⟩ : syracuseStep 1130955 = 1696433) B1696433
theorem B1130967 : Blo 1128631 1130967 := bstep (se 1 (by rfl) ⟨848225, by rfl⟩ : syracuseStep 1130967 = 1696451) B1696451
theorem B1130987 : Blo 1128631 1130987 := bstep (se 1 (by rfl) ⟨848240, by rfl⟩ : syracuseStep 1130987 = 1696481) B1696481
theorem B1130999 : Blo 1128631 1130999 := bstep (se 1 (by rfl) ⟨848249, by rfl⟩ : syracuseStep 1130999 = 1696499) B1696499
theorem B2540033 : Blo 1128631 2540033 := bstep (se 2 (by rfl) ⟨952512, by rfl⟩ : syracuseStep 2540033 = 1905025) B1905025
theorem B1131019 : Blo 1128631 1131019 := bstep (se 1 (by rfl) ⟨848264, by rfl⟩ : syracuseStep 1131019 = 1696529) B1696529
theorem B1131031 : Blo 1128631 1131031 := bstep (se 1 (by rfl) ⟨848273, by rfl⟩ : syracuseStep 1131031 = 1696547) B1696547
theorem B1131051 : Blo 1128631 1131051 := bstep (se 1 (by rfl) ⟨848288, by rfl⟩ : syracuseStep 1131051 = 1696577) B1696577
theorem B1131063 : Blo 1128631 1131063 := bstep (se 1 (by rfl) ⟨848297, by rfl⟩ : syracuseStep 1131063 = 1696595) B1696595
theorem B1131083 : Blo 1128631 1131083 := bstep (se 1 (by rfl) ⟨848312, by rfl⟩ : syracuseStep 1131083 = 1696625) B1696625
theorem B1131095 : Blo 1128631 1131095 := bstep (se 1 (by rfl) ⟨848321, by rfl⟩ : syracuseStep 1131095 = 1696643) B1696643
theorem B1131115 : Blo 1128631 1131115 := bstep (se 1 (by rfl) ⟨848336, by rfl⟩ : syracuseStep 1131115 = 1696673) B1696673
theorem B1131127 : Blo 1128631 1131127 := bstep (se 1 (by rfl) ⟨848345, by rfl⟩ : syracuseStep 1131127 = 1696691) B1696691
theorem B1131147 : Blo 1128631 1131147 := bstep (se 1 (by rfl) ⟨848360, by rfl⟩ : syracuseStep 1131147 = 1696721) B1696721
theorem B1131159 : Blo 1128631 1131159 := bstep (se 1 (by rfl) ⟨848369, by rfl⟩ : syracuseStep 1131159 = 1696739) B1696739
theorem B1131179 : Blo 1128631 1131179 := bstep (se 1 (by rfl) ⟨848384, by rfl⟩ : syracuseStep 1131179 = 1696769) B1696769
theorem B1131191 : Blo 1128631 1131191 := bstep (se 1 (by rfl) ⟨848393, by rfl⟩ : syracuseStep 1131191 = 1696787) B1696787
theorem B3818177 : Blo 1128631 3818177 := bstep (se 2 (by rfl) ⟨1431816, by rfl⟩ : syracuseStep 3818177 = 2863633) B2863633
theorem B1131211 : Blo 1128631 1131211 := bstep (se 1 (by rfl) ⟨848408, by rfl⟩ : syracuseStep 1131211 = 1696817) B1696817
theorem B1131223 : Blo 1128631 1131223 := bstep (se 1 (by rfl) ⟨848417, by rfl⟩ : syracuseStep 1131223 = 1696835) B1696835
theorem B2540249 : Blo 1128631 2540249 := bstep (se 2 (by rfl) ⟨952593, by rfl⟩ : syracuseStep 2540249 = 1905187) B1905187
theorem B8143577 : Blo 1128631 8143577 := bstep (se 2 (by rfl) ⟨3053841, by rfl⟩ : syracuseStep 8143577 = 6107683) B6107683
theorem B1131243 : Blo 1128631 1131243 := bstep (se 1 (by rfl) ⟨848432, by rfl⟩ : syracuseStep 1131243 = 1696865) B1696865
theorem B1131255 : Blo 1128631 1131255 := bstep (se 1 (by rfl) ⟨848441, by rfl⟩ : syracuseStep 1131255 = 1696883) B1696883
theorem B1131275 : Blo 1128631 1131275 := bstep (se 1 (by rfl) ⟨848456, by rfl⟩ : syracuseStep 1131275 = 1696913) B1696913
theorem B1131287 : Blo 1128631 1131287 := bstep (se 1 (by rfl) ⟨848465, by rfl⟩ : syracuseStep 1131287 = 1696931) B1696931
theorem B1131307 : Blo 1128631 1131307 := bstep (se 1 (by rfl) ⟨848480, by rfl⟩ : syracuseStep 1131307 = 1696961) B1696961
theorem B2540339 : Blo 1128631 2540339 := bstep (se 1 (by rfl) ⟨1905254, by rfl⟩ : syracuseStep 2540339 = 3810509) B3810509
theorem B1131319 : Blo 1128631 1131319 := bstep (se 1 (by rfl) ⟨848489, by rfl⟩ : syracuseStep 1131319 = 1696979) B1696979
theorem B1131339 : Blo 1128631 1131339 := bstep (se 1 (by rfl) ⟨848504, by rfl⟩ : syracuseStep 1131339 = 1697009) B1697009
theorem B2540375 : Blo 1128631 2540375 := bstep (se 1 (by rfl) ⟨1905281, by rfl⟩ : syracuseStep 2540375 = 3810563) B3810563
theorem B1131351 : Blo 1128631 1131351 := bstep (se 1 (by rfl) ⟨848513, by rfl⟩ : syracuseStep 1131351 = 1697027) B1697027
theorem B1131371 : Blo 1128631 1131371 := bstep (se 1 (by rfl) ⟨848528, by rfl⟩ : syracuseStep 1131371 = 1697057) B1697057
theorem B1131383 : Blo 1128631 1131383 := bstep (se 1 (by rfl) ⟨848537, by rfl⟩ : syracuseStep 1131383 = 1697075) B1697075
theorem B1131403 : Blo 1128631 1131403 := bstep (se 1 (by rfl) ⟨848552, by rfl⟩ : syracuseStep 1131403 = 1697105) B1697105
theorem B9651095 : Blo 1128631 9651095 := bstep (se 1 (by rfl) ⟨7238321, by rfl⟩ : syracuseStep 9651095 = 14476643) B14476643
theorem B1131415 : Blo 1128631 1131415 := bstep (se 1 (by rfl) ⟨848561, by rfl⟩ : syracuseStep 1131415 = 1697123) B1697123
theorem B1131435 : Blo 1128631 1131435 := bstep (se 1 (by rfl) ⟨848576, by rfl⟩ : syracuseStep 1131435 = 1697153) B1697153
theorem B1131447 : Blo 1128631 1131447 := bstep (se 1 (by rfl) ⟨848585, by rfl⟩ : syracuseStep 1131447 = 1697171) B1697171
theorem B1131467 : Blo 1128631 1131467 := bstep (se 1 (by rfl) ⟨848600, by rfl⟩ : syracuseStep 1131467 = 1697201) B1697201
theorem B1131479 : Blo 1128631 1131479 := bstep (se 1 (by rfl) ⟨848609, by rfl⟩ : syracuseStep 1131479 = 1697219) B1697219
theorem B1131499 : Blo 1128631 1131499 := bstep (se 1 (by rfl) ⟨848624, by rfl⟩ : syracuseStep 1131499 = 1697249) B1697249
theorem B1131511 : Blo 1128631 1131511 := bstep (se 1 (by rfl) ⟨848633, by rfl⟩ : syracuseStep 1131511 = 1697267) B1697267
theorem B2540555 : Blo 1128631 2540555 := bstep (se 1 (by rfl) ⟨1905416, by rfl⟩ : syracuseStep 2540555 = 3810833) B3810833
theorem B1131531 : Blo 1128631 1131531 := bstep (se 1 (by rfl) ⟨848648, by rfl⟩ : syracuseStep 1131531 = 1697297) B1697297
theorem B1131543 : Blo 1128631 1131543 := bstep (se 1 (by rfl) ⟨848657, by rfl⟩ : syracuseStep 1131543 = 1697315) B1697315
theorem B1131563 : Blo 1128631 1131563 := bstep (se 1 (by rfl) ⟨848672, by rfl⟩ : syracuseStep 1131563 = 1697345) B1697345
theorem B4834349 : Blo 1128631 4834349 := bstep (se 3 (by rfl) ⟨906440, by rfl⟩ : syracuseStep 4834349 = 1812881) B1812881
theorem B5719085 : Blo 1128631 5719085 := bstep (se 3 (by rfl) ⟨1072328, by rfl⟩ : syracuseStep 5719085 = 2144657) B2144657
theorem B1131575 : Blo 1128631 1131575 := bstep (se 1 (by rfl) ⟨848681, by rfl⟩ : syracuseStep 1131575 = 1697363) B1697363
theorem B6865985 : Blo 1128631 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B2540609 : Blo 1128631 2540609 := bstep (se 2 (by rfl) ⟨952728, by rfl⟩ : syracuseStep 2540609 = 1905457) B1905457
theorem B1131595 : Blo 1128631 1131595 := bstep (se 1 (by rfl) ⟨848696, by rfl⟩ : syracuseStep 1131595 = 1697393) B1697393
theorem B1131607 : Blo 1128631 1131607 := bstep (se 1 (by rfl) ⟨848705, by rfl⟩ : syracuseStep 1131607 = 1697411) B1697411
theorem B1131627 : Blo 1128631 1131627 := bstep (se 1 (by rfl) ⟨848720, by rfl⟩ : syracuseStep 1131627 = 1697441) B1697441
theorem B1131639 : Blo 1128631 1131639 := bstep (se 1 (by rfl) ⟨848729, by rfl⟩ : syracuseStep 1131639 = 1697459) B1697459
theorem B2147467 : Blo 1128631 2147467 := bstep (se 1 (by rfl) ⟨1610600, by rfl⟩ : syracuseStep 2147467 = 3221201) B3221201
theorem B1131659 : Blo 1128631 1131659 := bstep (se 1 (by rfl) ⟨848744, by rfl⟩ : syracuseStep 1131659 = 1697489) B1697489
theorem B1131671 : Blo 1128631 1131671 := bstep (se 1 (by rfl) ⟨848753, by rfl⟩ : syracuseStep 1131671 = 1697507) B1697507
theorem B1131691 : Blo 1128631 1131691 := bstep (se 1 (by rfl) ⟨848768, by rfl⟩ : syracuseStep 1131691 = 1697537) B1697537
theorem B1131703 : Blo 1128631 1131703 := bstep (se 1 (by rfl) ⟨848777, by rfl⟩ : syracuseStep 1131703 = 1697555) B1697555
theorem B1131723 : Blo 1128631 1131723 := bstep (se 1 (by rfl) ⟨848792, by rfl⟩ : syracuseStep 1131723 = 1697585) B1697585
theorem B2147543 : Blo 1128631 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B1131735 : Blo 1128631 1131735 := bstep (se 1 (by rfl) ⟨848801, by rfl⟩ : syracuseStep 1131735 = 1697603) B1697603
theorem B3818717 : Blo 1128631 3818717 := bstep (se 3 (by rfl) ⟨716009, by rfl⟩ : syracuseStep 3818717 = 1432019) B1432019
theorem B1131755 : Blo 1128631 1131755 := bstep (se 1 (by rfl) ⟨848816, by rfl⟩ : syracuseStep 1131755 = 1697633) B1697633
theorem B1131767 : Blo 1128631 1131767 := bstep (se 1 (by rfl) ⟨848825, by rfl⟩ : syracuseStep 1131767 = 1697651) B1697651
theorem B1131787 : Blo 1128631 1131787 := bstep (se 1 (by rfl) ⟨848840, by rfl⟩ : syracuseStep 1131787 = 1697681) B1697681
theorem B9651473 : Blo 1128631 9651473 := bstep (se 2 (by rfl) ⟨3619302, by rfl⟩ : syracuseStep 9651473 = 7238605) B7238605
theorem B1131799 : Blo 1128631 1131799 := bstep (se 1 (by rfl) ⟨848849, by rfl⟩ : syracuseStep 1131799 = 1697699) B1697699
theorem B2540825 : Blo 1128631 2540825 := bstep (se 2 (by rfl) ⟨952809, by rfl⟩ : syracuseStep 2540825 = 1905619) B1905619
theorem B1131819 : Blo 1128631 1131819 := bstep (se 1 (by rfl) ⟨848864, by rfl⟩ : syracuseStep 1131819 = 1697729) B1697729
theorem B1131831 : Blo 1128631 1131831 := bstep (se 1 (by rfl) ⟨848873, by rfl⟩ : syracuseStep 1131831 = 1697747) B1697747
theorem B1131851 : Blo 1128631 1131851 := bstep (se 1 (by rfl) ⟨848888, by rfl⟩ : syracuseStep 1131851 = 1697777) B1697777
theorem B1131863 : Blo 1128631 1131863 := bstep (se 1 (by rfl) ⟨848897, by rfl⟩ : syracuseStep 1131863 = 1697795) B1697795
theorem B1131883 : Blo 1128631 1131883 := bstep (se 1 (by rfl) ⟨848912, by rfl⟩ : syracuseStep 1131883 = 1697825) B1697825
theorem B2540915 : Blo 1128631 2540915 := bstep (se 1 (by rfl) ⟨1905686, by rfl⟩ : syracuseStep 2540915 = 3811373) B3811373
theorem B1131895 : Blo 1128631 1131895 := bstep (se 1 (by rfl) ⟨848921, by rfl⟩ : syracuseStep 1131895 = 1697843) B1697843
theorem B1131915 : Blo 1128631 1131915 := bstep (se 1 (by rfl) ⟨848936, by rfl⟩ : syracuseStep 1131915 = 1697873) B1697873
theorem B2540951 : Blo 1128631 2540951 := bstep (se 1 (by rfl) ⟨1905713, by rfl⟩ : syracuseStep 2540951 = 3811427) B3811427
theorem B1131927 : Blo 1128631 1131927 := bstep (se 1 (by rfl) ⟨848945, by rfl⟩ : syracuseStep 1131927 = 1697891) B1697891
theorem B1131947 : Blo 1128631 1131947 := bstep (se 1 (by rfl) ⟨848960, by rfl⟩ : syracuseStep 1131947 = 1697921) B1697921
theorem B1131959 : Blo 1128631 1131959 := bstep (se 1 (by rfl) ⟨848969, by rfl⟩ : syracuseStep 1131959 = 1697939) B1697939
theorem B1131979 : Blo 1128631 1131979 := bstep (se 1 (by rfl) ⟨848984, by rfl⟩ : syracuseStep 1131979 = 1697969) B1697969
theorem B1131991 : Blo 1128631 1131991 := bstep (se 1 (by rfl) ⟨848993, by rfl⟩ : syracuseStep 1131991 = 1697987) B1697987
theorem B1132011 : Blo 1128631 1132011 := bstep (se 1 (by rfl) ⟨849008, by rfl⟩ : syracuseStep 1132011 = 1698017) B1698017
theorem B1132023 : Blo 1128631 1132023 := bstep (se 1 (by rfl) ⟨849017, by rfl⟩ : syracuseStep 1132023 = 1698035) B1698035
theorem B1132043 : Blo 1128631 1132043 := bstep (se 1 (by rfl) ⟨849032, by rfl⟩ : syracuseStep 1132043 = 1698065) B1698065
theorem B1132055 : Blo 1128631 1132055 := bstep (se 1 (by rfl) ⟨849041, by rfl⟩ : syracuseStep 1132055 = 1698083) B1698083
theorem B4081175 : Blo 1128631 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B1132075 : Blo 1128631 1132075 := bstep (se 1 (by rfl) ⟨849056, by rfl⟩ : syracuseStep 1132075 = 1698113) B1698113
theorem B1132087 : Blo 1128631 1132087 := bstep (se 1 (by rfl) ⟨849065, by rfl⟩ : syracuseStep 1132087 = 1698131) B1698131
theorem B2541131 : Blo 1128631 2541131 := bstep (se 1 (by rfl) ⟨1905848, by rfl⟩ : syracuseStep 2541131 = 3811697) B3811697
theorem B1132107 : Blo 1128631 1132107 := bstep (se 1 (by rfl) ⟨849080, by rfl⟩ : syracuseStep 1132107 = 1698161) B1698161
theorem B1132119 : Blo 1128631 1132119 := bstep (se 1 (by rfl) ⟨849089, by rfl⟩ : syracuseStep 1132119 = 1698179) B1698179
theorem B1132139 : Blo 1128631 1132139 := bstep (se 1 (by rfl) ⟨849104, by rfl⟩ : syracuseStep 1132139 = 1698209) B1698209
theorem B1132151 : Blo 1128631 1132151 := bstep (se 1 (by rfl) ⟨849113, by rfl⟩ : syracuseStep 1132151 = 1698227) B1698227
theorem B2541185 : Blo 1128631 2541185 := bstep (se 2 (by rfl) ⟨952944, by rfl⟩ : syracuseStep 2541185 = 1905889) B1905889
theorem B6440579 : Blo 1128631 6440579 := bstep (se 1 (by rfl) ⟨4830434, by rfl⟩ : syracuseStep 6440579 = 9660869) B9660869
theorem B1132171 : Blo 1128631 1132171 := bstep (se 1 (by rfl) ⟨849128, by rfl⟩ : syracuseStep 1132171 = 1698257) B1698257
theorem B1132183 : Blo 1128631 1132183 := bstep (se 1 (by rfl) ⟨849137, by rfl⟩ : syracuseStep 1132183 = 1698275) B1698275
theorem B1132203 : Blo 1128631 1132203 := bstep (se 1 (by rfl) ⟨849152, by rfl⟩ : syracuseStep 1132203 = 1698305) B1698305
theorem B1132215 : Blo 1128631 1132215 := bstep (se 1 (by rfl) ⟨849161, by rfl⟩ : syracuseStep 1132215 = 1698323) B1698323
theorem B1132235 : Blo 1128631 1132235 := bstep (se 1 (by rfl) ⟨849176, by rfl⟩ : syracuseStep 1132235 = 1698353) B1698353
theorem B1132247 : Blo 1128631 1132247 := bstep (se 1 (by rfl) ⟨849185, by rfl⟩ : syracuseStep 1132247 = 1698371) B1698371
theorem B1132267 : Blo 1128631 1132267 := bstep (se 1 (by rfl) ⟨849200, by rfl⟩ : syracuseStep 1132267 = 1698401) B1698401
theorem B1132279 : Blo 1128631 1132279 := bstep (se 1 (by rfl) ⟨849209, by rfl⟩ : syracuseStep 1132279 = 1698419) B1698419
theorem B1132299 : Blo 1128631 1132299 := bstep (se 1 (by rfl) ⟨849224, by rfl⟩ : syracuseStep 1132299 = 1698449) B1698449
theorem B1132311 : Blo 1128631 1132311 := bstep (se 1 (by rfl) ⟨849233, by rfl⟩ : syracuseStep 1132311 = 1698467) B1698467
theorem B1132331 : Blo 1128631 1132331 := bstep (se 1 (by rfl) ⟨849248, by rfl⟩ : syracuseStep 1132331 = 1698497) B1698497
theorem B1132343 : Blo 1128631 1132343 := bstep (se 1 (by rfl) ⟨849257, by rfl⟩ : syracuseStep 1132343 = 1698515) B1698515
theorem B1132363 : Blo 1128631 1132363 := bstep (se 1 (by rfl) ⟨849272, by rfl⟩ : syracuseStep 1132363 = 1698545) B1698545
theorem B1132375 : Blo 1128631 1132375 := bstep (se 1 (by rfl) ⟨849281, by rfl⟩ : syracuseStep 1132375 = 1698563) B1698563
theorem B2541401 : Blo 1128631 2541401 := bstep (se 2 (by rfl) ⟨953025, by rfl⟩ : syracuseStep 2541401 = 1906051) B1906051
theorem B1132395 : Blo 1128631 1132395 := bstep (se 1 (by rfl) ⟨849296, by rfl⟩ : syracuseStep 1132395 = 1698593) B1698593
theorem B2148211 : Blo 1128631 2148211 := bstep (se 1 (by rfl) ⟨1611158, by rfl⟩ : syracuseStep 2148211 = 3222317) B3222317
theorem B1132407 : Blo 1128631 1132407 := bstep (se 1 (by rfl) ⟨849305, by rfl⟩ : syracuseStep 1132407 = 1698611) B1698611
theorem B1132427 : Blo 1128631 1132427 := bstep (se 1 (by rfl) ⟨849320, by rfl⟩ : syracuseStep 1132427 = 1698641) B1698641
theorem B1132439 : Blo 1128631 1132439 := bstep (se 1 (by rfl) ⟨849329, by rfl⟩ : syracuseStep 1132439 = 1698659) B1698659
theorem B1132459 : Blo 1128631 1132459 := bstep (se 1 (by rfl) ⟨849344, by rfl⟩ : syracuseStep 1132459 = 1698689) B1698689
theorem B2541491 : Blo 1128631 2541491 := bstep (se 1 (by rfl) ⟨1906118, by rfl⟩ : syracuseStep 2541491 = 3812237) B3812237
theorem B1132471 : Blo 1128631 1132471 := bstep (se 1 (by rfl) ⟨849353, by rfl⟩ : syracuseStep 1132471 = 1698707) B1698707
theorem B1132491 : Blo 1128631 1132491 := bstep (se 1 (by rfl) ⟨849368, by rfl⟩ : syracuseStep 1132491 = 1698737) B1698737
theorem B2541527 : Blo 1128631 2541527 := bstep (se 1 (by rfl) ⟨1906145, by rfl⟩ : syracuseStep 2541527 = 3812291) B3812291
theorem B1132503 : Blo 1128631 1132503 := bstep (se 1 (by rfl) ⟨849377, by rfl⟩ : syracuseStep 1132503 = 1698755) B1698755
theorem B1132523 : Blo 1128631 1132523 := bstep (se 1 (by rfl) ⟨849392, by rfl⟩ : syracuseStep 1132523 = 1698785) B1698785
theorem B1132535 : Blo 1128631 1132535 := bstep (se 1 (by rfl) ⟨849401, by rfl⟩ : syracuseStep 1132535 = 1698803) B1698803
theorem B1132555 : Blo 1128631 1132555 := bstep (se 1 (by rfl) ⟨849416, by rfl⟩ : syracuseStep 1132555 = 1698833) B1698833
theorem B2410519 : Blo 1128631 2410519 := bstep (se 1 (by rfl) ⟨1807889, by rfl⟩ : syracuseStep 2410519 = 3615779) B3615779
theorem B1132567 : Blo 1128631 1132567 := bstep (se 1 (by rfl) ⟨849425, by rfl⟩ : syracuseStep 1132567 = 1698851) B1698851
theorem B1132587 : Blo 1128631 1132587 := bstep (se 1 (by rfl) ⟨849440, by rfl⟩ : syracuseStep 1132587 = 1698881) B1698881
theorem B1132599 : Blo 1128631 1132599 := bstep (se 1 (by rfl) ⟨849449, by rfl⟩ : syracuseStep 1132599 = 1698899) B1698899
theorem B1132619 : Blo 1128631 1132619 := bstep (se 1 (by rfl) ⟨849464, by rfl⟩ : syracuseStep 1132619 = 1698929) B1698929
theorem B2148439 : Blo 1128631 2148439 := bstep (se 1 (by rfl) ⟨1611329, by rfl⟩ : syracuseStep 2148439 = 3222659) B3222659
theorem B1132631 : Blo 1128631 1132631 := bstep (se 1 (by rfl) ⟨849473, by rfl⟩ : syracuseStep 1132631 = 1698947) B1698947
theorem B3623005 : Blo 1128631 3623005 := bstep (se 3 (by rfl) ⟨679313, by rfl⟩ : syracuseStep 3623005 = 1358627) B1358627
theorem B2541707 : Blo 1128631 2541707 := bstep (se 1 (by rfl) ⟨1906280, by rfl⟩ : syracuseStep 2541707 = 3812561) B3812561
theorem B10307735 : Blo 1128631 10307735 := bstep (se 1 (by rfl) ⟨7730801, by rfl⟩ : syracuseStep 10307735 = 15461603) B15461603
theorem B4901015 : Blo 1128631 4901015 := bstep (se 1 (by rfl) ⟨3675761, by rfl⟩ : syracuseStep 4901015 = 7351523) B7351523
theorem B2541761 : Blo 1128631 2541761 := bstep (se 2 (by rfl) ⟨953160, by rfl⟩ : syracuseStep 2541761 = 1906321) B1906321
theorem B2148545 : Blo 1128631 2148545 := bstep (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) B1611409
theorem B3819851 : Blo 1128631 3819851 := bstep (se 1 (by rfl) ⟨2864888, by rfl⟩ : syracuseStep 3819851 = 5729777) B5729777
theorem B2148697 : Blo 1128631 2148697 := bstep (se 2 (by rfl) ⟨805761, by rfl⟩ : syracuseStep 2148697 = 1611523) B1611523
theorem B2541977 : Blo 1128631 2541977 := bstep (se 2 (by rfl) ⟨953241, by rfl⟩ : syracuseStep 2541977 = 1906483) B1906483
theorem B2410955 : Blo 1128631 2410955 := bstep (se 1 (by rfl) ⟨1808216, by rfl⟩ : syracuseStep 2410955 = 3616433) B3616433
theorem B2542067 : Blo 1128631 2542067 := bstep (se 1 (by rfl) ⟨1906550, by rfl⟩ : syracuseStep 2542067 = 3813101) B3813101
theorem B2542103 : Blo 1128631 2542103 := bstep (se 1 (by rfl) ⟨1906577, by rfl⟩ : syracuseStep 2542103 = 3813155) B3813155
theorem B3820121 : Blo 1128631 3820121 := bstep (se 2 (by rfl) ⟨1432545, by rfl⟩ : syracuseStep 3820121 = 2865091) B2865091
theorem B2542283 : Blo 1128631 2542283 := bstep (se 1 (by rfl) ⟨1906712, by rfl⟩ : syracuseStep 2542283 = 3813425) B3813425
theorem B2542337 : Blo 1128631 2542337 := bstep (se 2 (by rfl) ⟨953376, by rfl⟩ : syracuseStep 2542337 = 1906753) B1906753
theorem B5425937 : Blo 1128631 5425937 := bstep (se 2 (by rfl) ⟨2034726, by rfl⟩ : syracuseStep 5425937 = 4069453) B4069453
theorem B10439641 : Blo 1128631 10439641 := bstep (se 2 (by rfl) ⟨3914865, by rfl⟩ : syracuseStep 10439641 = 7829731) B7829731
theorem B2542553 : Blo 1128631 2542553 := bstep (se 2 (by rfl) ⟨953457, by rfl⟩ : syracuseStep 2542553 = 1906915) B1906915
theorem B110185433 : Blo 1128631 110185433 := bstep (se 2 (by rfl) ⟨41319537, by rfl⟩ : syracuseStep 110185433 = 82639075) B82639075
theorem B2542643 : Blo 1128631 2542643 := bstep (se 1 (by rfl) ⟨1906982, by rfl⟩ : syracuseStep 2542643 = 3813965) B3813965
theorem B2542679 : Blo 1128631 2542679 := bstep (se 1 (by rfl) ⟨1907009, by rfl⟩ : syracuseStep 2542679 = 3814019) B3814019
theorem B2542859 : Blo 1128631 2542859 := bstep (se 1 (by rfl) ⟨1907144, by rfl⟩ : syracuseStep 2542859 = 3814289) B3814289
theorem B3820823 : Blo 1128631 3820823 := bstep (se 1 (by rfl) ⟨2865617, by rfl⟩ : syracuseStep 3820823 = 5731235) B5731235
theorem B2542913 : Blo 1128631 2542913 := bstep (se 2 (by rfl) ⟨953592, by rfl⟩ : syracuseStep 2542913 = 1907185) B1907185
theorem B2411851 : Blo 1128631 2411851 := bstep (se 1 (by rfl) ⟨1808888, by rfl⟩ : syracuseStep 2411851 = 3617777) B3617777
theorem B2543129 : Blo 1128631 2543129 := bstep (se 2 (by rfl) ⟨953673, by rfl⟩ : syracuseStep 2543129 = 1907347) B1907347
theorem B2543219 : Blo 1128631 2543219 := bstep (se 1 (by rfl) ⟨1907414, by rfl⟩ : syracuseStep 2543219 = 3814829) B3814829
theorem B2150003 : Blo 1128631 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B2543255 : Blo 1128631 2543255 := bstep (se 1 (by rfl) ⟨1907441, by rfl⟩ : syracuseStep 2543255 = 3814883) B3814883
theorem B2150155 : Blo 1128631 2150155 := bstep (se 1 (by rfl) ⟨1612616, by rfl⟩ : syracuseStep 2150155 = 3225233) B3225233
theorem B3821363 : Blo 1128631 3821363 := bstep (se 1 (by rfl) ⟨2866022, by rfl⟩ : syracuseStep 3821363 = 5732045) B5732045
theorem B2543435 : Blo 1128631 2543435 := bstep (se 1 (by rfl) ⟨1907576, by rfl⟩ : syracuseStep 2543435 = 3815153) B3815153
theorem B2543489 : Blo 1128631 2543489 := bstep (se 2 (by rfl) ⟨953808, by rfl⟩ : syracuseStep 2543489 = 1907617) B1907617
theorem B2412595 : Blo 1128631 2412595 := bstep (se 1 (by rfl) ⟨1809446, by rfl⟩ : syracuseStep 2412595 = 3618893) B3618893
theorem B3821633 : Blo 1128631 3821633 := bstep (se 2 (by rfl) ⟨1433112, by rfl⟩ : syracuseStep 3821633 = 2866225) B2866225
theorem B27545669 : Blo 1128631 27545669 := bstep (se 4 (by rfl) ⟨2582406, by rfl⟩ : syracuseStep 27545669 = 5164813) B5164813
theorem B1429579 : Blo 1128631 1429579 := bstep (se 1 (by rfl) ⟨1072184, by rfl⟩ : syracuseStep 1429579 = 2144369) B2144369
theorem B2543705 : Blo 1128631 2543705 := bstep (se 2 (by rfl) ⟨953889, by rfl⟩ : syracuseStep 2543705 = 1907779) B1907779
theorem B2543795 : Blo 1128631 2543795 := bstep (se 1 (by rfl) ⟨1907846, by rfl⟩ : syracuseStep 2543795 = 3815693) B3815693
theorem B2543831 : Blo 1128631 2543831 := bstep (se 1 (by rfl) ⟨1907873, by rfl⟩ : syracuseStep 2543831 = 3815747) B3815747
theorem B5165329 : Blo 1128631 5165329 := bstep (se 2 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 5165329 = 3873997) B3873997
theorem B55103789 : Blo 1128631 55103789 := bstep (se 3 (by rfl) ⟨10331960, by rfl⟩ : syracuseStep 55103789 = 20663921) B20663921
theorem B2544011 : Blo 1128631 2544011 := bstep (se 1 (by rfl) ⟨1908008, by rfl⟩ : syracuseStep 2544011 = 3816017) B3816017
theorem B2544065 : Blo 1128631 2544065 := bstep (se 2 (by rfl) ⟨954024, by rfl⟩ : syracuseStep 2544065 = 1908049) B1908049
theorem B2413081 : Blo 1128631 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B3822173 : Blo 1128631 3822173 := bstep (se 3 (by rfl) ⟨716657, by rfl⟩ : syracuseStep 3822173 = 1433315) B1433315
theorem B2544281 : Blo 1128631 2544281 := bstep (se 2 (by rfl) ⟨954105, by rfl⟩ : syracuseStep 2544281 = 1908211) B1908211
theorem B9163469 : Blo 1128631 9163469 := bstep (se 3 (by rfl) ⟨1718150, by rfl⟩ : syracuseStep 9163469 = 3436301) B3436301
theorem B2544371 : Blo 1128631 2544371 := bstep (se 1 (by rfl) ⟨1908278, by rfl⟩ : syracuseStep 2544371 = 3816557) B3816557
theorem B2544407 : Blo 1128631 2544407 := bstep (se 1 (by rfl) ⟨1908305, by rfl⟩ : syracuseStep 2544407 = 3816611) B3816611
theorem B5722973 : Blo 1128631 5722973 := bstep (se 3 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 5722973 = 2146115) B2146115
theorem B2544587 : Blo 1128631 2544587 := bstep (se 1 (by rfl) ⟨1908440, by rfl⟩ : syracuseStep 2544587 = 3816881) B3816881
theorem B2544641 : Blo 1128631 2544641 := bstep (se 2 (by rfl) ⟨954240, by rfl⟩ : syracuseStep 2544641 = 1908481) B1908481
theorem B1430551 : Blo 1128631 1430551 := bstep (se 1 (by rfl) ⟨1072913, by rfl⟩ : syracuseStep 1430551 = 2145827) B2145827
theorem B6116417 : Blo 1128631 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B4576349 : Blo 1128631 4576349 := bstep (se 3 (by rfl) ⟨858065, by rfl⟩ : syracuseStep 4576349 = 1716131) B1716131
theorem B2544857 : Blo 1128631 2544857 := bstep (se 2 (by rfl) ⟨954321, by rfl⟩ : syracuseStep 2544857 = 1908643) B1908643
theorem B1692953 : Blo 1128631 1692953 := bstep (se 2 (by rfl) ⟨634857, by rfl⟩ : syracuseStep 1692953 = 1269715) B1269715
theorem B2544947 : Blo 1128631 2544947 := bstep (se 1 (by rfl) ⟨1908710, by rfl⟩ : syracuseStep 2544947 = 3817421) B3817421
theorem B2544983 : Blo 1128631 2544983 := bstep (se 1 (by rfl) ⟨1908737, by rfl⟩ : syracuseStep 2544983 = 3817475) B3817475
theorem B1693067 : Blo 1128631 1693067 := bstep (se 1 (by rfl) ⟨1269800, by rfl⟩ : syracuseStep 1693067 = 2539601) B2539601
theorem B1693079 : Blo 1128631 1693079 := bstep (se 1 (by rfl) ⟨1269809, by rfl⟩ : syracuseStep 1693079 = 2539619) B2539619
theorem B2905537 : Blo 1128631 2905537 := bstep (se 2 (by rfl) ⟨1089576, by rfl⟩ : syracuseStep 2905537 = 2179153) B2179153
theorem B1693145 : Blo 1128631 1693145 := bstep (se 2 (by rfl) ⟨634929, by rfl⟩ : syracuseStep 1693145 = 1269859) B1269859
theorem B2545163 : Blo 1128631 2545163 := bstep (se 1 (by rfl) ⟨1908872, by rfl⟩ : syracuseStep 2545163 = 3817745) B3817745
theorem B2545217 : Blo 1128631 2545217 := bstep (se 2 (by rfl) ⟨954456, by rfl⟩ : syracuseStep 2545217 = 1908913) B1908913
theorem B1693259 : Blo 1128631 1693259 := bstep (se 1 (by rfl) ⟨1269944, by rfl⟩ : syracuseStep 1693259 = 2539889) B2539889
theorem B1693271 : Blo 1128631 1693271 := bstep (se 1 (by rfl) ⟨1269953, by rfl⟩ : syracuseStep 1693271 = 2539907) B2539907
theorem B6968933 : Blo 1128631 6968933 := bstep (se 4 (by rfl) ⟨653337, by rfl⟩ : syracuseStep 6968933 = 1306675) B1306675
theorem B1693337 : Blo 1128631 1693337 := bstep (se 2 (by rfl) ⟨635001, by rfl⟩ : syracuseStep 1693337 = 1270003) B1270003
theorem B27481841 : Blo 1128631 27481841 := bstep (se 2 (by rfl) ⟨10305690, by rfl⟩ : syracuseStep 27481841 = 20611381) B20611381
theorem B21190385 : Blo 1128631 21190385 := bstep (se 2 (by rfl) ⟨7946394, by rfl⟩ : syracuseStep 21190385 = 15892789) B15892789
theorem B1693451 : Blo 1128631 1693451 := bstep (se 1 (by rfl) ⟨1270088, by rfl⟩ : syracuseStep 1693451 = 2540177) B2540177
theorem B1693463 : Blo 1128631 1693463 := bstep (se 1 (by rfl) ⟨1270097, by rfl⟩ : syracuseStep 1693463 = 2540195) B2540195
theorem B1529623 : Blo 1128631 1529623 := bstep (se 1 (by rfl) ⟨1147217, by rfl⟩ : syracuseStep 1529623 = 2294435) B2294435
theorem B2545433 : Blo 1128631 2545433 := bstep (se 2 (by rfl) ⟨954537, by rfl⟩ : syracuseStep 2545433 = 1909075) B1909075
theorem B1431371 : Blo 1128631 1431371 := bstep (se 1 (by rfl) ⟨1073528, by rfl⟩ : syracuseStep 1431371 = 2147057) B2147057
theorem B1693529 : Blo 1128631 1693529 := bstep (se 2 (by rfl) ⟨635073, by rfl⟩ : syracuseStep 1693529 = 1270147) B1270147
theorem B2545523 : Blo 1128631 2545523 := bstep (se 1 (by rfl) ⟨1909142, by rfl⟩ : syracuseStep 2545523 = 3818285) B3818285
theorem B2545559 : Blo 1128631 2545559 := bstep (se 1 (by rfl) ⟨1909169, by rfl⟩ : syracuseStep 2545559 = 3818339) B3818339
theorem B1693643 : Blo 1128631 1693643 := bstep (se 1 (by rfl) ⟨1270232, by rfl⟩ : syracuseStep 1693643 = 2540465) B2540465
theorem B1693655 : Blo 1128631 1693655 := bstep (se 1 (by rfl) ⟨1270241, by rfl⟩ : syracuseStep 1693655 = 2540483) B2540483
theorem B2414551 : Blo 1128631 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B2414603 : Blo 1128631 2414603 := bstep (se 1 (by rfl) ⟨1810952, by rfl⟩ : syracuseStep 2414603 = 3621905) B3621905
theorem B1693721 : Blo 1128631 1693721 := bstep (se 2 (by rfl) ⟨635145, by rfl⟩ : syracuseStep 1693721 = 1270291) B1270291
theorem B2545739 : Blo 1128631 2545739 := bstep (se 1 (by rfl) ⟨1909304, by rfl⟩ : syracuseStep 2545739 = 3818609) B3818609
theorem B2545793 : Blo 1128631 2545793 := bstep (se 2 (by rfl) ⟨954672, by rfl⟩ : syracuseStep 2545793 = 1909345) B1909345
theorem B1693835 : Blo 1128631 1693835 := bstep (se 1 (by rfl) ⟨1270376, by rfl⟩ : syracuseStep 1693835 = 2540753) B2540753
theorem B1693847 : Blo 1128631 1693847 := bstep (se 1 (by rfl) ⟨1270385, by rfl⟩ : syracuseStep 1693847 = 2540771) B2540771
theorem B1693913 : Blo 1128631 1693913 := bstep (se 2 (by rfl) ⟨635217, by rfl⟩ : syracuseStep 1693913 = 1270435) B1270435
theorem B1694027 : Blo 1128631 1694027 := bstep (se 1 (by rfl) ⟨1270520, by rfl⟩ : syracuseStep 1694027 = 2541041) B2541041
theorem B1694039 : Blo 1128631 1694039 := bstep (se 1 (by rfl) ⟨1270529, by rfl⟩ : syracuseStep 1694039 = 2541059) B2541059
theorem B2546009 : Blo 1128631 2546009 := bstep (se 2 (by rfl) ⟨954753, by rfl⟩ : syracuseStep 2546009 = 1909507) B1909507
theorem B1694105 : Blo 1128631 1694105 := bstep (se 2 (by rfl) ⟨635289, by rfl⟩ : syracuseStep 1694105 = 1270579) B1270579
theorem B2546099 : Blo 1128631 2546099 := bstep (se 1 (by rfl) ⟨1909574, by rfl⟩ : syracuseStep 2546099 = 3819149) B3819149
theorem B2546135 : Blo 1128631 2546135 := bstep (se 1 (by rfl) ⟨1909601, by rfl⟩ : syracuseStep 2546135 = 3819203) B3819203
theorem B1694219 : Blo 1128631 1694219 := bstep (se 1 (by rfl) ⟨1270664, by rfl⟩ : syracuseStep 1694219 = 2541329) B2541329
theorem B1432075 : Blo 1128631 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B1694231 : Blo 1128631 1694231 := bstep (se 1 (by rfl) ⟨1270673, by rfl⟩ : syracuseStep 1694231 = 2541347) B2541347
theorem B2578969 : Blo 1128631 2578969 := bstep (se 2 (by rfl) ⟨967113, by rfl⟩ : syracuseStep 2578969 = 1934227) B1934227
theorem B1694297 : Blo 1128631 1694297 := bstep (se 2 (by rfl) ⟨635361, by rfl⟩ : syracuseStep 1694297 = 1270723) B1270723
theorem B2546315 : Blo 1128631 2546315 := bstep (se 1 (by rfl) ⟨1909736, by rfl⟩ : syracuseStep 2546315 = 3819473) B3819473
theorem B4577971 : Blo 1128631 4577971 := bstep (se 1 (by rfl) ⟨3433478, by rfl⟩ : syracuseStep 4577971 = 6866957) B6866957
theorem B2546369 : Blo 1128631 2546369 := bstep (se 2 (by rfl) ⟨954888, by rfl⟩ : syracuseStep 2546369 = 1909777) B1909777
theorem B1694411 : Blo 1128631 1694411 := bstep (se 1 (by rfl) ⟨1270808, by rfl⟩ : syracuseStep 1694411 = 2541617) B2541617
theorem B1694423 : Blo 1128631 1694423 := bstep (se 1 (by rfl) ⟨1270817, by rfl⟩ : syracuseStep 1694423 = 2541635) B2541635
theorem B7232273 : Blo 1128631 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B1432343 : Blo 1128631 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1694489 : Blo 1128631 1694489 := bstep (se 2 (by rfl) ⟨635433, by rfl⟩ : syracuseStep 1694489 = 1270867) B1270867
theorem B1694603 : Blo 1128631 1694603 := bstep (se 1 (by rfl) ⟨1270952, by rfl⟩ : syracuseStep 1694603 = 2541905) B2541905
theorem B1694615 : Blo 1128631 1694615 := bstep (se 1 (by rfl) ⟨1270961, by rfl⟩ : syracuseStep 1694615 = 2541923) B2541923
theorem B5725079 : Blo 1128631 5725079 := bstep (se 1 (by rfl) ⟨4293809, by rfl⟩ : syracuseStep 5725079 = 8587619) B8587619
theorem B2546585 : Blo 1128631 2546585 := bstep (se 2 (by rfl) ⟨954969, by rfl⟩ : syracuseStep 2546585 = 1909939) B1909939
theorem B1694681 : Blo 1128631 1694681 := bstep (se 2 (by rfl) ⟨635505, by rfl⟩ : syracuseStep 1694681 = 1271011) B1271011
theorem B2546675 : Blo 1128631 2546675 := bstep (se 1 (by rfl) ⟨1910006, by rfl⟩ : syracuseStep 2546675 = 3820013) B3820013
theorem B2546711 : Blo 1128631 2546711 := bstep (se 1 (by rfl) ⟨1910033, by rfl⟩ : syracuseStep 2546711 = 3820067) B3820067
theorem B1694795 : Blo 1128631 1694795 := bstep (se 1 (by rfl) ⟨1271096, by rfl⟩ : syracuseStep 1694795 = 2542193) B2542193
theorem B1694807 : Blo 1128631 1694807 := bstep (se 1 (by rfl) ⟨1271105, by rfl⟩ : syracuseStep 1694807 = 2542211) B2542211
theorem B1694873 : Blo 1128631 1694873 := bstep (se 2 (by rfl) ⟨635577, by rfl⟩ : syracuseStep 1694873 = 1271155) B1271155
theorem B2546891 : Blo 1128631 2546891 := bstep (se 1 (by rfl) ⟨1910168, by rfl⟩ : syracuseStep 2546891 = 3820337) B3820337
theorem B2546945 : Blo 1128631 2546945 := bstep (se 2 (by rfl) ⟨955104, by rfl⟩ : syracuseStep 2546945 = 1910209) B1910209
theorem B1694987 : Blo 1128631 1694987 := bstep (se 1 (by rfl) ⟨1271240, by rfl⟩ : syracuseStep 1694987 = 2542481) B2542481
theorem B1694999 : Blo 1128631 1694999 := bstep (se 1 (by rfl) ⟨1271249, by rfl⟩ : syracuseStep 1694999 = 2542499) B2542499
theorem B6446411 : Blo 1128631 6446411 := bstep (se 1 (by rfl) ⟨4834808, by rfl⟩ : syracuseStep 6446411 = 9669617) B9669617
theorem B1695065 : Blo 1128631 1695065 := bstep (se 2 (by rfl) ⟨635649, by rfl⟩ : syracuseStep 1695065 = 1271299) B1271299
theorem B3628439 : Blo 1128631 3628439 := bstep (se 1 (by rfl) ⟨2721329, by rfl⟩ : syracuseStep 3628439 = 5442659) B5442659
theorem B1695179 : Blo 1128631 1695179 := bstep (se 1 (by rfl) ⟨1271384, by rfl⟩ : syracuseStep 1695179 = 2542769) B2542769
theorem B1695191 : Blo 1128631 1695191 := bstep (se 1 (by rfl) ⟨1271393, by rfl⟩ : syracuseStep 1695191 = 2542787) B2542787
theorem B1433047 : Blo 1128631 1433047 := bstep (se 1 (by rfl) ⟨1074785, by rfl⟩ : syracuseStep 1433047 = 2149571) B2149571
theorem B2547161 : Blo 1128631 2547161 := bstep (se 2 (by rfl) ⟨955185, by rfl⟩ : syracuseStep 2547161 = 1910371) B1910371
theorem B1695257 : Blo 1128631 1695257 := bstep (se 2 (by rfl) ⟨635721, by rfl⟩ : syracuseStep 1695257 = 1271443) B1271443
theorem B2547251 : Blo 1128631 2547251 := bstep (se 1 (by rfl) ⟨1910438, by rfl⟩ : syracuseStep 2547251 = 3820877) B3820877
theorem B2547287 : Blo 1128631 2547287 := bstep (se 1 (by rfl) ⟨1910465, by rfl⟩ : syracuseStep 2547287 = 3820931) B3820931
theorem B2416243 : Blo 1128631 2416243 := bstep (se 1 (by rfl) ⟨1812182, by rfl⟩ : syracuseStep 2416243 = 3624365) B3624365
theorem B1695371 : Blo 1128631 1695371 := bstep (se 1 (by rfl) ⟨1271528, by rfl⟩ : syracuseStep 1695371 = 2543057) B2543057
theorem B1695383 : Blo 1128631 1695383 := bstep (se 1 (by rfl) ⟨1271537, by rfl⟩ : syracuseStep 1695383 = 2543075) B2543075
theorem B1695449 : Blo 1128631 1695449 := bstep (se 2 (by rfl) ⟨635793, by rfl⟩ : syracuseStep 1695449 = 1271587) B1271587
theorem B2547467 : Blo 1128631 2547467 := bstep (se 1 (by rfl) ⟨1910600, by rfl⟩ : syracuseStep 2547467 = 3821201) B3821201
theorem B6119185 : Blo 1128631 6119185 := bstep (se 2 (by rfl) ⟨2294694, by rfl⟩ : syracuseStep 6119185 = 4589389) B4589389
theorem B14868269 : Blo 1128631 14868269 := bstep (se 3 (by rfl) ⟨2787800, by rfl⟩ : syracuseStep 14868269 = 5575601) B5575601
theorem B4349747 : Blo 1128631 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B2547521 : Blo 1128631 2547521 := bstep (se 2 (by rfl) ⟨955320, by rfl⟩ : syracuseStep 2547521 = 1910641) B1910641
theorem B1695563 : Blo 1128631 1695563 := bstep (se 1 (by rfl) ⟨1271672, by rfl⟩ : syracuseStep 1695563 = 2543345) B2543345
theorem B1695575 : Blo 1128631 1695575 := bstep (se 1 (by rfl) ⟨1271681, by rfl⟩ : syracuseStep 1695575 = 2543363) B2543363
theorem B1695641 : Blo 1128631 1695641 := bstep (se 2 (by rfl) ⟨635865, by rfl⟩ : syracuseStep 1695641 = 1271731) B1271731
theorem B2416601 : Blo 1128631 2416601 := bstep (se 2 (by rfl) ⟨906225, by rfl⟩ : syracuseStep 2416601 = 1812451) B1812451
theorem B1269751 : Blo 1128631 1269751 := bstep (se 1 (by rfl) ⟨952313, by rfl⟩ : syracuseStep 1269751 = 1904627) B1904627
theorem B1695755 : Blo 1128631 1695755 := bstep (se 1 (by rfl) ⟨1271816, by rfl⟩ : syracuseStep 1695755 = 2543633) B2543633
theorem B1695767 : Blo 1128631 1695767 := bstep (se 1 (by rfl) ⟨1271825, by rfl⟩ : syracuseStep 1695767 = 2543651) B2543651
theorem B2547737 : Blo 1128631 2547737 := bstep (se 2 (by rfl) ⟨955401, by rfl⟩ : syracuseStep 2547737 = 1910803) B1910803
theorem B1695833 : Blo 1128631 1695833 := bstep (se 2 (by rfl) ⟨635937, by rfl⟩ : syracuseStep 1695833 = 1271875) B1271875
theorem B2547827 : Blo 1128631 2547827 := bstep (se 1 (by rfl) ⟨1910870, by rfl⟩ : syracuseStep 2547827 = 3821741) B3821741
theorem B2547863 : Blo 1128631 2547863 := bstep (se 1 (by rfl) ⟨1910897, by rfl⟩ : syracuseStep 2547863 = 3821795) B3821795
theorem B1269931 : Blo 1128631 1269931 := bstep (se 1 (by rfl) ⟨952448, by rfl⟩ : syracuseStep 1269931 = 1904897) B1904897
theorem B1695947 : Blo 1128631 1695947 := bstep (se 1 (by rfl) ⟨1271960, by rfl⟩ : syracuseStep 1695947 = 2543921) B2543921
theorem B1695959 : Blo 1128631 1695959 := bstep (se 1 (by rfl) ⟨1271969, by rfl⟩ : syracuseStep 1695959 = 2543939) B2543939
theorem B1270039 : Blo 1128631 1270039 := bstep (se 1 (by rfl) ⟨952529, by rfl⟩ : syracuseStep 1270039 = 1905059) B1905059
theorem B1696025 : Blo 1128631 1696025 := bstep (se 2 (by rfl) ⟨636009, by rfl⟩ : syracuseStep 1696025 = 1272019) B1272019
theorem B13951277 : Blo 1128631 13951277 := bstep (se 3 (by rfl) ⟨2615864, by rfl⟩ : syracuseStep 13951277 = 5231729) B5231729
theorem B2711873 : Blo 1128631 2711873 := bstep (se 2 (by rfl) ⟨1016952, by rfl⟩ : syracuseStep 2711873 = 2033905) B2033905
theorem B2548043 : Blo 1128631 2548043 := bstep (se 1 (by rfl) ⟨1911032, by rfl⟩ : syracuseStep 2548043 = 3822065) B3822065
theorem B2548097 : Blo 1128631 2548097 := bstep (se 2 (by rfl) ⟨955536, by rfl⟩ : syracuseStep 2548097 = 1911073) B1911073
theorem B1696139 : Blo 1128631 1696139 := bstep (se 1 (by rfl) ⟨1272104, by rfl⟩ : syracuseStep 1696139 = 2544209) B2544209
theorem B1696151 : Blo 1128631 1696151 := bstep (se 1 (by rfl) ⟨1272113, by rfl⟩ : syracuseStep 1696151 = 2544227) B2544227
theorem B1270219 : Blo 1128631 1270219 := bstep (se 1 (by rfl) ⟨952664, by rfl⟩ : syracuseStep 1270219 = 1905329) B1905329
theorem B1696217 : Blo 1128631 1696217 := bstep (se 2 (by rfl) ⟨636081, by rfl⟩ : syracuseStep 1696217 = 1272163) B1272163
theorem B9658885 : Blo 1128631 9658885 := bstep (se 4 (by rfl) ⟨905520, by rfl⟩ : syracuseStep 9658885 = 1811041) B1811041
theorem B1270327 : Blo 1128631 1270327 := bstep (se 1 (by rfl) ⟨952745, by rfl⟩ : syracuseStep 1270327 = 1905491) B1905491
theorem B1696331 : Blo 1128631 1696331 := bstep (se 1 (by rfl) ⟨1272248, by rfl⟩ : syracuseStep 1696331 = 2544497) B2544497
theorem B1696343 : Blo 1128631 1696343 := bstep (se 1 (by rfl) ⟨1272257, by rfl⟩ : syracuseStep 1696343 = 2544515) B2544515
theorem B2548313 : Blo 1128631 2548313 := bstep (se 2 (by rfl) ⟨955617, by rfl⟩ : syracuseStep 2548313 = 1911235) B1911235
theorem B20931223 : Blo 1128631 20931223 := bstep (se 1 (by rfl) ⟨15698417, by rfl⟩ : syracuseStep 20931223 = 31396835) B31396835
theorem B1696409 : Blo 1128631 1696409 := bstep (se 2 (by rfl) ⟨636153, by rfl⟩ : syracuseStep 1696409 = 1272307) B1272307
theorem B2548403 : Blo 1128631 2548403 := bstep (se 1 (by rfl) ⟨1911302, by rfl⟩ : syracuseStep 2548403 = 3822605) B3822605
theorem B2712257 : Blo 1128631 2712257 := bstep (se 2 (by rfl) ⟨1017096, by rfl⟩ : syracuseStep 2712257 = 2034193) B2034193
theorem B1270507 : Blo 1128631 1270507 := bstep (se 1 (by rfl) ⟨952880, by rfl⟩ : syracuseStep 1270507 = 1905761) B1905761
theorem B1696523 : Blo 1128631 1696523 := bstep (se 1 (by rfl) ⟨1272392, by rfl⟩ : syracuseStep 1696523 = 2544785) B2544785
theorem B1696535 : Blo 1128631 1696535 := bstep (se 1 (by rfl) ⟨1272401, by rfl⟩ : syracuseStep 1696535 = 2544803) B2544803
theorem B1270615 : Blo 1128631 1270615 := bstep (se 1 (by rfl) ⟨952961, by rfl⟩ : syracuseStep 1270615 = 1905923) B1905923
theorem B1696601 : Blo 1128631 1696601 := bstep (se 2 (by rfl) ⟨636225, by rfl⟩ : syracuseStep 1696601 = 1272451) B1272451
theorem B1696715 : Blo 1128631 1696715 := bstep (se 1 (by rfl) ⟨1272536, by rfl⟩ : syracuseStep 1696715 = 2545073) B2545073
theorem B1696727 : Blo 1128631 1696727 := bstep (se 1 (by rfl) ⟨1272545, by rfl⟩ : syracuseStep 1696727 = 2545091) B2545091
theorem B1270795 : Blo 1128631 1270795 := bstep (se 1 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 1270795 = 1906193) B1906193
theorem B4285457 : Blo 1128631 4285457 := bstep (se 2 (by rfl) ⟨1607046, by rfl⟩ : syracuseStep 4285457 = 3214093) B3214093
theorem B1696793 : Blo 1128631 1696793 := bstep (se 2 (by rfl) ⟨636297, by rfl⟩ : syracuseStep 1696793 = 1272595) B1272595
theorem B6972481 : Blo 1128631 6972481 := bstep (se 2 (by rfl) ⟨2614680, by rfl⟩ : syracuseStep 6972481 = 5229361) B5229361
theorem B16311365 : Blo 1128631 16311365 := bstep (se 4 (by rfl) ⟨1529190, by rfl⟩ : syracuseStep 16311365 = 3058381) B3058381
theorem B3433565 : Blo 1128631 3433565 := bstep (se 3 (by rfl) ⟨643793, by rfl⟩ : syracuseStep 3433565 = 1287587) B1287587
theorem B1270903 : Blo 1128631 1270903 := bstep (se 1 (by rfl) ⟨953177, by rfl⟩ : syracuseStep 1270903 = 1906355) B1906355
theorem B1696907 : Blo 1128631 1696907 := bstep (se 1 (by rfl) ⟨1272680, by rfl⟩ : syracuseStep 1696907 = 2545361) B2545361
theorem B1696919 : Blo 1128631 1696919 := bstep (se 1 (by rfl) ⟨1272689, by rfl⟩ : syracuseStep 1696919 = 2545379) B2545379
theorem B1696985 : Blo 1128631 1696985 := bstep (se 2 (by rfl) ⟨636369, by rfl⟩ : syracuseStep 1696985 = 1272739) B1272739
theorem B1271083 : Blo 1128631 1271083 := bstep (se 1 (by rfl) ⟨953312, by rfl⟩ : syracuseStep 1271083 = 1906625) B1906625
theorem B1697099 : Blo 1128631 1697099 := bstep (se 1 (by rfl) ⟨1272824, by rfl⟩ : syracuseStep 1697099 = 2545649) B2545649
theorem B1697111 : Blo 1128631 1697111 := bstep (se 1 (by rfl) ⟨1272833, by rfl⟩ : syracuseStep 1697111 = 2545667) B2545667
theorem B30991733 : Blo 1128631 30991733 := bstep (se 5 (by rfl) ⟨1452737, by rfl⟩ : syracuseStep 30991733 = 2905475) B2905475
theorem B4187537 : Blo 1128631 4187537 := bstep (se 2 (by rfl) ⟨1570326, by rfl⟩ : syracuseStep 4187537 = 3140653) B3140653
theorem B1271191 : Blo 1128631 1271191 := bstep (se 1 (by rfl) ⟨953393, by rfl⟩ : syracuseStep 1271191 = 1906787) B1906787
theorem B1697177 : Blo 1128631 1697177 := bstep (se 2 (by rfl) ⟨636441, by rfl⟩ : syracuseStep 1697177 = 1272883) B1272883
theorem B2713025 : Blo 1128631 2713025 := bstep (se 2 (by rfl) ⟨1017384, by rfl⟩ : syracuseStep 2713025 = 2034769) B2034769
theorem B1697291 : Blo 1128631 1697291 := bstep (se 1 (by rfl) ⟨1272968, by rfl⟩ : syracuseStep 1697291 = 2545937) B2545937
theorem B19293713 : Blo 1128631 19293713 := bstep (se 2 (by rfl) ⟨7235142, by rfl⟩ : syracuseStep 19293713 = 14470285) B14470285
theorem B1697303 : Blo 1128631 1697303 := bstep (se 1 (by rfl) ⟨1272977, by rfl⟩ : syracuseStep 1697303 = 2545955) B2545955
theorem B1271371 : Blo 1128631 1271371 := bstep (se 1 (by rfl) ⟨953528, by rfl⟩ : syracuseStep 1271371 = 1907057) B1907057
theorem B1697369 : Blo 1128631 1697369 := bstep (se 2 (by rfl) ⟨636513, by rfl⟩ : syracuseStep 1697369 = 1273027) B1273027
theorem B1271479 : Blo 1128631 1271479 := bstep (se 1 (by rfl) ⟨953609, by rfl⟩ : syracuseStep 1271479 = 1907219) B1907219
theorem B4286155 : Blo 1128631 4286155 := bstep (se 1 (by rfl) ⟨3214616, by rfl⟩ : syracuseStep 4286155 = 6429233) B6429233
theorem B1697483 : Blo 1128631 1697483 := bstep (se 1 (by rfl) ⟨1273112, by rfl⟩ : syracuseStep 1697483 = 2546225) B2546225
theorem B1697495 : Blo 1128631 1697495 := bstep (se 1 (by rfl) ⟨1273121, by rfl⟩ : syracuseStep 1697495 = 2546243) B2546243
theorem B1697561 : Blo 1128631 1697561 := bstep (se 2 (by rfl) ⟨636585, by rfl⟩ : syracuseStep 1697561 = 1273171) B1273171
theorem B1271659 : Blo 1128631 1271659 := bstep (se 1 (by rfl) ⟨953744, by rfl⟩ : syracuseStep 1271659 = 1907489) B1907489
theorem B1697675 : Blo 1128631 1697675 := bstep (se 1 (by rfl) ⟨1273256, by rfl⟩ : syracuseStep 1697675 = 2546513) B2546513
theorem B1697687 : Blo 1128631 1697687 := bstep (se 1 (by rfl) ⟨1273265, by rfl⟩ : syracuseStep 1697687 = 2546531) B2546531
theorem B21718961 : Blo 1128631 21718961 := bstep (se 2 (by rfl) ⟨8144610, by rfl⟩ : syracuseStep 21718961 = 16289221) B16289221
theorem B1206199 : Blo 1128631 1206199 := bstep (se 1 (by rfl) ⟨904649, by rfl⟩ : syracuseStep 1206199 = 1809299) B1809299
theorem B2418635 : Blo 1128631 2418635 := bstep (se 1 (by rfl) ⟨1813976, by rfl⟩ : syracuseStep 2418635 = 3627953) B3627953
theorem B1271767 : Blo 1128631 1271767 := bstep (se 1 (by rfl) ⟨953825, by rfl⟩ : syracuseStep 1271767 = 1907651) B1907651
theorem B1697753 : Blo 1128631 1697753 := bstep (se 2 (by rfl) ⟨636657, by rfl⟩ : syracuseStep 1697753 = 1273315) B1273315
theorem B4286429 : Blo 1128631 4286429 := bstep (se 3 (by rfl) ⟨803705, by rfl⟩ : syracuseStep 4286429 = 1607411) B1607411
theorem B1697867 : Blo 1128631 1697867 := bstep (se 1 (by rfl) ⟨1273400, by rfl⟩ : syracuseStep 1697867 = 2546801) B2546801
theorem B1697879 : Blo 1128631 1697879 := bstep (se 1 (by rfl) ⟨1273409, by rfl⟩ : syracuseStep 1697879 = 2546819) B2546819
theorem B1271947 : Blo 1128631 1271947 := bstep (se 1 (by rfl) ⟨953960, by rfl⟩ : syracuseStep 1271947 = 1907921) B1907921
theorem B1697945 : Blo 1128631 1697945 := bstep (se 2 (by rfl) ⟨636729, by rfl⟩ : syracuseStep 1697945 = 1273459) B1273459
theorem B2615513 : Blo 1128631 2615513 := bstep (se 2 (by rfl) ⟨980817, by rfl⟩ : syracuseStep 2615513 = 1961635) B1961635
theorem B1272055 : Blo 1128631 1272055 := bstep (se 1 (by rfl) ⟨954041, by rfl⟩ : syracuseStep 1272055 = 1908083) B1908083
theorem B1698059 : Blo 1128631 1698059 := bstep (se 1 (by rfl) ⟨1273544, by rfl⟩ : syracuseStep 1698059 = 2547089) B2547089
theorem B1698071 : Blo 1128631 1698071 := bstep (se 1 (by rfl) ⟨1273553, by rfl⟩ : syracuseStep 1698071 = 2547107) B2547107
theorem B1206571 : Blo 1128631 1206571 := bstep (se 1 (by rfl) ⟨904928, by rfl⟩ : syracuseStep 1206571 = 1809857) B1809857
theorem B1698137 : Blo 1128631 1698137 := bstep (se 2 (by rfl) ⟨636801, by rfl⟩ : syracuseStep 1698137 = 1273603) B1273603
theorem B5728643 : Blo 1128631 5728643 := bstep (se 1 (by rfl) ⟨4296482, by rfl⟩ : syracuseStep 5728643 = 8592965) B8592965
theorem B1272235 : Blo 1128631 1272235 := bstep (se 1 (by rfl) ⟨954176, by rfl⟩ : syracuseStep 1272235 = 1908353) B1908353
theorem B1698251 : Blo 1128631 1698251 := bstep (se 1 (by rfl) ⟨1273688, by rfl⟩ : syracuseStep 1698251 = 2547377) B2547377
theorem B1698263 : Blo 1128631 1698263 := bstep (se 1 (by rfl) ⟨1273697, by rfl⟩ : syracuseStep 1698263 = 2547395) B2547395
theorem B1272343 : Blo 1128631 1272343 := bstep (se 1 (by rfl) ⟨954257, by rfl⟩ : syracuseStep 1272343 = 1908515) B1908515
theorem B1698329 : Blo 1128631 1698329 := bstep (se 2 (by rfl) ⟨636873, by rfl⟩ : syracuseStep 1698329 = 1273747) B1273747
theorem B1698443 : Blo 1128631 1698443 := bstep (se 1 (by rfl) ⟨1273832, by rfl⟩ : syracuseStep 1698443 = 2547665) B2547665
theorem B4287127 : Blo 1128631 4287127 := bstep (se 1 (by rfl) ⟨3215345, by rfl⟩ : syracuseStep 4287127 = 6430691) B6430691
theorem B1698455 : Blo 1128631 1698455 := bstep (se 1 (by rfl) ⟨1273841, by rfl⟩ : syracuseStep 1698455 = 2547683) B2547683
theorem B1272523 : Blo 1128631 1272523 := bstep (se 1 (by rfl) ⟨954392, by rfl⟩ : syracuseStep 1272523 = 1908785) B1908785
theorem B1698521 : Blo 1128631 1698521 := bstep (se 2 (by rfl) ⟨636945, by rfl⟩ : syracuseStep 1698521 = 1273891) B1273891
theorem B1207019 : Blo 1128631 1207019 := bstep (se 1 (by rfl) ⟨905264, by rfl⟩ : syracuseStep 1207019 = 1810529) B1810529
theorem B1272631 : Blo 1128631 1272631 := bstep (se 1 (by rfl) ⟨954473, by rfl⟩ : syracuseStep 1272631 = 1908947) B1908947
theorem B1698635 : Blo 1128631 1698635 := bstep (se 1 (by rfl) ⟨1273976, by rfl⟩ : syracuseStep 1698635 = 2547953) B2547953
theorem B1698647 : Blo 1128631 1698647 := bstep (se 1 (by rfl) ⟨1273985, by rfl⟩ : syracuseStep 1698647 = 2547971) B2547971
theorem B1698713 : Blo 1128631 1698713 := bstep (se 2 (by rfl) ⟨637017, by rfl⟩ : syracuseStep 1698713 = 1274035) B1274035
theorem B6876083 : Blo 1128631 6876083 := bstep (se 1 (by rfl) ⟨5157062, by rfl⟩ : syracuseStep 6876083 = 10314125) B10314125
theorem B1272811 : Blo 1128631 1272811 := bstep (se 1 (by rfl) ⟨954608, by rfl⟩ : syracuseStep 1272811 = 1909217) B1909217
theorem B1698827 : Blo 1128631 1698827 := bstep (se 1 (by rfl) ⟨1274120, by rfl⟩ : syracuseStep 1698827 = 2548241) B2548241
theorem B1698839 : Blo 1128631 1698839 := bstep (se 1 (by rfl) ⟨1274129, by rfl⟩ : syracuseStep 1698839 = 2548259) B2548259
theorem B1960985 : Blo 1128631 1960985 := bstep (se 2 (by rfl) ⟨735369, by rfl⟩ : syracuseStep 1960985 = 1470739) B1470739
theorem B9169955 : Blo 1128631 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B1272919 : Blo 1128631 1272919 := bstep (se 1 (by rfl) ⟨954689, by rfl⟩ : syracuseStep 1272919 = 1909379) B1909379
theorem B1698905 : Blo 1128631 1698905 := bstep (se 2 (by rfl) ⟨637089, by rfl⟩ : syracuseStep 1698905 = 1274179) B1274179
theorem B2092211 : Blo 1128631 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B9661619 : Blo 1128631 9661619 := bstep (se 1 (by rfl) ⟨7246214, by rfl⟩ : syracuseStep 9661619 = 14492429) B14492429
theorem B1273099 : Blo 1128631 1273099 := bstep (se 1 (by rfl) ⟨954824, by rfl⟩ : syracuseStep 1273099 = 1909649) B1909649
theorem B7236965 : Blo 1128631 7236965 := bstep (se 4 (by rfl) ⟨678465, by rfl⟩ : syracuseStep 7236965 = 1356931) B1356931
theorem B1273207 : Blo 1128631 1273207 := bstep (se 1 (by rfl) ⟨954905, by rfl⟩ : syracuseStep 1273207 = 1909811) B1909811
theorem B4287917 : Blo 1128631 4287917 := bstep (se 3 (by rfl) ⟨803984, by rfl⟩ : syracuseStep 4287917 = 1607969) B1607969
theorem B1273387 : Blo 1128631 1273387 := bstep (se 1 (by rfl) ⟨955040, by rfl⟩ : syracuseStep 1273387 = 1910081) B1910081
theorem B2289239 : Blo 1128631 2289239 := bstep (se 1 (by rfl) ⟨1716929, by rfl⟩ : syracuseStep 2289239 = 3433859) B3433859
theorem B1273495 : Blo 1128631 1273495 := bstep (se 1 (by rfl) ⟨955121, by rfl⟩ : syracuseStep 1273495 = 1910243) B1910243
theorem B5435201 : Blo 1128631 5435201 := bstep (se 2 (by rfl) ⟨2038200, by rfl⟩ : syracuseStep 5435201 = 4076401) B4076401
theorem B7237451 : Blo 1128631 7237451 := bstep (se 1 (by rfl) ⟨5428088, by rfl⟩ : syracuseStep 7237451 = 10856177) B10856177
theorem B1273675 : Blo 1128631 1273675 := bstep (se 1 (by rfl) ⟨955256, by rfl⟩ : syracuseStep 1273675 = 1910513) B1910513
theorem B1208215 : Blo 1128631 1208215 := bstep (se 1 (by rfl) ⟨906161, by rfl⟩ : syracuseStep 1208215 = 1812323) B1812323
theorem B1273783 : Blo 1128631 1273783 := bstep (se 1 (by rfl) ⟨955337, by rfl⟩ : syracuseStep 1273783 = 1910675) B1910675
theorem B4190231 : Blo 1128631 4190231 := bstep (se 1 (by rfl) ⟨3142673, by rfl⟩ : syracuseStep 4190231 = 6285347) B6285347
theorem B1208395 : Blo 1128631 1208395 := bstep (se 1 (by rfl) ⟨906296, by rfl⟩ : syracuseStep 1208395 = 1812593) B1812593
theorem B1273963 : Blo 1128631 1273963 := bstep (se 1 (by rfl) ⟨955472, by rfl⟩ : syracuseStep 1273963 = 1910945) B1910945
theorem B18346135 : Blo 1128631 18346135 := bstep (se 1 (by rfl) ⟨13759601, by rfl⟩ : syracuseStep 18346135 = 27519203) B27519203
theorem B1274071 : Blo 1128631 1274071 := bstep (se 1 (by rfl) ⟨955553, by rfl⟩ : syracuseStep 1274071 = 1911107) B1911107
theorem B18313573 : Blo 1128631 18313573 := bstep (se 4 (by rfl) ⟨1716897, by rfl⟩ : syracuseStep 18313573 = 3433795) B3433795
theorem B4125401 : Blo 1128631 4125401 := bstep (se 2 (by rfl) ⟨1547025, by rfl⟩ : syracuseStep 4125401 = 3094051) B3094051
theorem B4289345 : Blo 1128631 4289345 := bstep (se 2 (by rfl) ⟨1608504, by rfl⟩ : syracuseStep 4289345 = 3217009) B3217009
theorem B2716505 : Blo 1128631 2716505 := bstep (se 2 (by rfl) ⟨1018689, by rfl⟩ : syracuseStep 2716505 = 2037379) B2037379
theorem B9663533 : Blo 1128631 9663533 := bstep (se 3 (by rfl) ⟨1811912, by rfl⟩ : syracuseStep 9663533 = 3623825) B3623825
theorem B7239091 : Blo 1128631 7239091 := bstep (se 1 (by rfl) ⟨5429318, by rfl⟩ : syracuseStep 7239091 = 10858637) B10858637
theorem B9664217 : Blo 1128631 9664217 := bstep (se 2 (by rfl) ⟨3624081, by rfl⟩ : syracuseStep 9664217 = 7248163) B7248163
theorem B5437277 : Blo 1128631 5437277 := bstep (se 3 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 5437277 = 2038979) B2038979
theorem B5732369 : Blo 1128631 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B5732531 : Blo 1128631 5732531 := bstep (se 1 (by rfl) ⟨4299398, by rfl⟩ : syracuseStep 5732531 = 8598797) B8598797
theorem B2291905 : Blo 1128631 2291905 := bstep (se 2 (by rfl) ⟨859464, by rfl⟩ : syracuseStep 2291905 = 1718929) B1718929
theorem B4290833 : Blo 1128631 4290833 := bstep (se 2 (by rfl) ⟨1609062, by rfl⟩ : syracuseStep 4290833 = 3218125) B3218125
theorem B11008547 : Blo 1128631 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B10877591 : Blo 1128631 10877591 := bstep (se 1 (by rfl) ⟨8158193, by rfl⟩ : syracuseStep 10877591 = 16316387) B16316387
theorem B4291289 : Blo 1128631 4291289 := bstep (se 2 (by rfl) ⟨1609233, by rfl⟩ : syracuseStep 4291289 = 3218467) B3218467
theorem B4291501 : Blo 1128631 4291501 := bstep (se 3 (by rfl) ⟨804656, by rfl⟩ : syracuseStep 4291501 = 1609313) B1609313
theorem B2063321 : Blo 1128631 2063321 := bstep (se 2 (by rfl) ⟨773745, by rfl⟩ : syracuseStep 2063321 = 1547491) B1547491
theorem B1375255 : Blo 1128631 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B1932427 : Blo 1128631 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B2718937 : Blo 1128631 2718937 := bstep (se 2 (by rfl) ⟨1019601, by rfl⟩ : syracuseStep 2718937 = 2039203) B2039203
theorem B4291805 : Blo 1128631 4291805 := bstep (se 3 (by rfl) ⟨804713, by rfl⟩ : syracuseStep 4291805 = 1609427) B1609427
theorem B2293195 : Blo 1128631 2293195 := bstep (se 1 (by rfl) ⟨1719896, by rfl⟩ : syracuseStep 2293195 = 3439793) B3439793
theorem B2719831 : Blo 1128631 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B5439889 : Blo 1128631 5439889 := bstep (se 2 (by rfl) ⟨2039958, by rfl⟩ : syracuseStep 5439889 = 4079917) B4079917
theorem B21725657 : Blo 1128631 21725657 := bstep (se 2 (by rfl) ⟨8147121, by rfl⟩ : syracuseStep 21725657 = 16294243) B16294243
theorem B12878513 : Blo 1128631 12878513 := bstep (se 2 (by rfl) ⟨4829442, by rfl⟩ : syracuseStep 12878513 = 9658885) B9658885
theorem B12387107 : Blo 1128631 12387107 := bstep (se 1 (by rfl) ⟨9290330, by rfl⟩ : syracuseStep 12387107 = 18580661) B18580661
theorem B4653883 : Blo 1128631 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B5440391 : Blo 1128631 5440391 := bstep (se 1 (by rfl) ⟨4080293, by rfl⟩ : syracuseStep 5440391 = 8160587) B8160587
theorem B12223493 : Blo 1128631 12223493 := bstep (se 4 (by rfl) ⟨1145952, by rfl⟩ : syracuseStep 12223493 = 2291905) B2291905
theorem B2720783 : Blo 1128631 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B4293719 : Blo 1128631 4293719 := bstep (se 1 (by rfl) ⟨3220289, by rfl⟩ : syracuseStep 4293719 = 6440579) B6440579
theorem B7079183 : Blo 1128631 7079183 := bstep (se 1 (by rfl) ⟨5309387, by rfl⟩ : syracuseStep 7079183 = 10618775) B10618775
theorem B3868019 : Blo 1128631 3868019 := bstep (se 1 (by rfl) ⟨2901014, by rfl⟩ : syracuseStep 3868019 = 5802029) B5802029
theorem B3671449 : Blo 1128631 3671449 := bstep (se 2 (by rfl) ⟨1376793, by rfl⟩ : syracuseStep 3671449 = 2753587) B2753587
theorem B9405881 : Blo 1128631 9405881 := bstep (se 2 (by rfl) ⟨3527205, by rfl⟩ : syracuseStep 9405881 = 7054411) B7054411
theorem B4294205 : Blo 1128631 4294205 := bstep (se 3 (by rfl) ⟨805163, by rfl⟩ : syracuseStep 4294205 = 1610327) B1610327
theorem B1607303 : Blo 1128631 1607303 := bstep (se 1 (by rfl) ⟨1205477, by rfl⟩ : syracuseStep 1607303 = 2410955) B2410955
theorem B1608265 : Blo 1128631 1608265 := bstep (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) B1206199
theorem B3214025 : Blo 1128631 3214025 := bstep (se 2 (by rfl) ⟨1205259, by rfl⟩ : syracuseStep 3214025 = 2410519) B2410519
theorem B36735859 : Blo 1128631 36735859 := bstep (se 1 (by rfl) ⟨27551894, by rfl⟩ : syracuseStep 36735859 = 55103789) B55103789
theorem B1608761 : Blo 1128631 1608761 := bstep (se 2 (by rfl) ⟨603285, by rfl⟩ : syracuseStep 1608761 = 1206571) B1206571
theorem B6884471 : Blo 1128631 6884471 := bstep (se 1 (by rfl) ⟨5163353, by rfl⟩ : syracuseStep 6884471 = 10326707) B10326707
theorem B1838863 : Blo 1128631 1838863 := bstep (se 1 (by rfl) ⟨1379147, by rfl⟩ : syracuseStep 1838863 = 2758295) B2758295
theorem B18321227 : Blo 1128631 18321227 := bstep (se 1 (by rfl) ⟨13740920, by rfl⟩ : syracuseStep 18321227 = 27481841) B27481841
theorem B14126923 : Blo 1128631 14126923 := bstep (se 1 (by rfl) ⟨10595192, by rfl⟩ : syracuseStep 14126923 = 21190385) B21190385
theorem B1609735 : Blo 1128631 1609735 := bstep (se 1 (by rfl) ⟨1207301, by rfl⟩ : syracuseStep 1609735 = 2414603) B2414603
theorem B3215801 : Blo 1128631 3215801 := bstep (se 2 (by rfl) ⟨1205925, by rfl⟩ : syracuseStep 3215801 = 2411851) B2411851
theorem B4821515 : Blo 1128631 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B1905167 : Blo 1128631 1905167 := bstep (se 1 (by rfl) ⟨1428875, by rfl⟩ : syracuseStep 1905167 = 2857751) B2857751
theorem B4297607 : Blo 1128631 4297607 := bstep (se 1 (by rfl) ⟨3223205, by rfl⟩ : syracuseStep 4297607 = 6446411) B6446411
theorem B1905707 : Blo 1128631 1905707 := bstep (se 1 (by rfl) ⟨1429280, by rfl⟩ : syracuseStep 1905707 = 2858561) B2858561
theorem B3216793 : Blo 1128631 3216793 := bstep (se 2 (by rfl) ⟨1206297, by rfl⟩ : syracuseStep 3216793 = 2412595) B2412595
theorem B1906105 : Blo 1128631 1906105 := bstep (se 2 (by rfl) ⟨714789, by rfl⟩ : syracuseStep 1906105 = 1429579) B1429579
theorem B1611193 : Blo 1128631 1611193 := bstep (se 2 (by rfl) ⟨604197, by rfl⟩ : syracuseStep 1611193 = 1208395) B1208395
theorem B1807915 : Blo 1128631 1807915 := bstep (se 1 (by rfl) ⟨1355936, by rfl⟩ : syracuseStep 1807915 = 2711873) B2711873
theorem B2037307 : Blo 1128631 2037307 := bstep (se 1 (by rfl) ⟨1527980, by rfl⟩ : syracuseStep 2037307 = 3055961) B3055961
theorem B6887105 : Blo 1128631 6887105 := bstep (se 2 (by rfl) ⟨2582664, by rfl⟩ : syracuseStep 6887105 = 5165329) B5165329
theorem B1808171 : Blo 1128631 1808171 := bstep (se 1 (by rfl) ⟨1356128, by rfl⟩ : syracuseStep 1808171 = 2712257) B2712257
theorem B24418097 : Blo 1128631 24418097 := bstep (se 2 (by rfl) ⟨9156786, by rfl⟩ : syracuseStep 24418097 = 18313573) B18313573
theorem B3872627 : Blo 1128631 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B2856971 : Blo 1128631 2856971 := bstep (se 1 (by rfl) ⟨2142728, by rfl⟩ : syracuseStep 2856971 = 4285457) B4285457
theorem B1906807 : Blo 1128631 1906807 := bstep (se 1 (by rfl) ⟨1430105, by rfl⟩ : syracuseStep 1906807 = 2860211) B2860211
theorem B2791691 : Blo 1128631 2791691 := bstep (se 1 (by rfl) ⟨2093768, by rfl⟩ : syracuseStep 2791691 = 4187537) B4187537
theorem B1907003 : Blo 1128631 1907003 := bstep (se 1 (by rfl) ⟨1430252, by rfl⟩ : syracuseStep 1907003 = 2860505) B2860505
theorem B1612423 : Blo 1128631 1612423 := bstep (se 1 (by rfl) ⟨1209317, by rfl⟩ : syracuseStep 1612423 = 2418635) B2418635
theorem B2857619 : Blo 1128631 2857619 := bstep (se 1 (by rfl) ⟨2143214, by rfl⟩ : syracuseStep 2857619 = 4286429) B4286429
theorem B1907401 : Blo 1128631 1907401 := bstep (se 2 (by rfl) ⟨715275, by rfl⟩ : syracuseStep 1907401 = 1430551) B1430551
theorem B2857913 : Blo 1128631 2857913 := bstep (se 2 (by rfl) ⟨1071717, by rfl⟩ : syracuseStep 2857913 = 2143435) B2143435
theorem B3874049 : Blo 1128631 3874049 := bstep (se 2 (by rfl) ⟨1452768, by rfl⟩ : syracuseStep 3874049 = 2905537) B2905537
theorem B3218717 : Blo 1128631 3218717 := bstep (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) B1207019
theorem B1908103 : Blo 1128631 1908103 := bstep (se 1 (by rfl) ⟨1431077, by rfl⟩ : syracuseStep 1908103 = 2862155) B2862155
theorem B4824643 : Blo 1128631 4824643 := bstep (se 1 (by rfl) ⟨3618482, by rfl⟩ : syracuseStep 4824643 = 7236965) B7236965
theorem B2858611 : Blo 1128631 2858611 := bstep (se 1 (by rfl) ⟨2143958, by rfl⟩ : syracuseStep 2858611 = 4287917) B4287917
theorem B2858753 : Blo 1128631 2858753 := bstep (se 2 (by rfl) ⟨1072032, by rfl⟩ : syracuseStep 2858753 = 2144065) B2144065
theorem B3809159 : Blo 1128631 3809159 := bstep (se 1 (by rfl) ⟨2856869, by rfl⟩ : syracuseStep 3809159 = 5713739) B5713739
theorem B4824967 : Blo 1128631 4824967 := bstep (se 1 (by rfl) ⟨3618725, by rfl⟩ : syracuseStep 4824967 = 7237451) B7237451
theorem B3219401 : Blo 1128631 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B1908751 : Blo 1128631 1908751 := bstep (se 1 (by rfl) ⟨1431563, by rfl⟩ : syracuseStep 1908751 = 2863127) B2863127
theorem B2793487 : Blo 1128631 2793487 := bstep (se 1 (by rfl) ⟨2095115, by rfl⟩ : syracuseStep 2793487 = 4190231) B4190231
theorem B2859209 : Blo 1128631 2859209 := bstep (se 2 (by rfl) ⟨1072203, by rfl⟩ : syracuseStep 2859209 = 2144407) B2144407
theorem B3809537 : Blo 1128631 3809537 := bstep (se 2 (by rfl) ⟨1428576, by rfl⟩ : syracuseStep 3809537 = 2857153) B2857153
theorem B3219983 : Blo 1128631 3219983 := bstep (se 1 (by rfl) ⟨2414987, by rfl⟩ : syracuseStep 3219983 = 4829975) B4829975
theorem B2859563 : Blo 1128631 2859563 := bstep (se 1 (by rfl) ⟨2144672, by rfl⟩ : syracuseStep 2859563 = 4289345) B4289345
theorem B1909291 : Blo 1128631 1909291 := bstep (se 1 (by rfl) ⟨1431968, by rfl⟩ : syracuseStep 1909291 = 2863937) B2863937
theorem B1811003 : Blo 1128631 1811003 := bstep (se 1 (by rfl) ⟨1358252, by rfl⟩ : syracuseStep 1811003 = 2716505) B2716505
theorem B1909433 : Blo 1128631 1909433 := bstep (se 2 (by rfl) ⟨716037, by rfl⟩ : syracuseStep 1909433 = 1432075) B1432075
theorem B9642725 : Blo 1128631 9642725 := bstep (se 4 (by rfl) ⟨904005, by rfl⟩ : syracuseStep 9642725 = 1808011) B1808011
theorem B4825889 : Blo 1128631 4825889 := bstep (se 2 (by rfl) ⟨1809708, by rfl⟩ : syracuseStep 4825889 = 3619417) B3619417
theorem B7250725 : Blo 1128631 7250725 := bstep (se 4 (by rfl) ⟨679755, by rfl⟩ : syracuseStep 7250725 = 1359511) B1359511
theorem B6103961 : Blo 1128631 6103961 := bstep (se 2 (by rfl) ⟨2288985, by rfl⟩ : syracuseStep 6103961 = 4577971) B4577971
theorem B3810347 : Blo 1128631 3810347 := bstep (se 1 (by rfl) ⟨2857760, by rfl⟩ : syracuseStep 3810347 = 5715521) B5715521
theorem B6431831 : Blo 1128631 6431831 := bstep (se 1 (by rfl) ⟨4823873, by rfl⟩ : syracuseStep 6431831 = 9647747) B9647747
theorem B1910135 : Blo 1128631 1910135 := bstep (se 1 (by rfl) ⟨1432601, by rfl⟩ : syracuseStep 1910135 = 2865203) B2865203
theorem B4072913 : Blo 1128631 4072913 := bstep (se 2 (by rfl) ⟨1527342, by rfl⟩ : syracuseStep 4072913 = 3054685) B3054685
theorem B8594909 : Blo 1128631 8594909 := bstep (se 3 (by rfl) ⟨1611545, by rfl⟩ : syracuseStep 8594909 = 3223091) B3223091
theorem B2860555 : Blo 1128631 2860555 := bstep (se 1 (by rfl) ⟨2145416, by rfl⟩ : syracuseStep 2860555 = 4290833) B4290833
theorem B2860697 : Blo 1128631 2860697 := bstep (se 2 (by rfl) ⟨1072761, by rfl⟩ : syracuseStep 2860697 = 2145523) B2145523
theorem B1812169 : Blo 1128631 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B7251727 : Blo 1128631 7251727 := bstep (se 1 (by rfl) ⟨5438795, by rfl⟩ : syracuseStep 7251727 = 10877591) B10877591
theorem B2860859 : Blo 1128631 2860859 := bstep (se 1 (by rfl) ⟨2145644, by rfl⟩ : syracuseStep 2860859 = 4291289) B4291289
theorem B1910587 : Blo 1128631 1910587 := bstep (se 1 (by rfl) ⟨1432940, by rfl⟩ : syracuseStep 1910587 = 2865881) B2865881
theorem B3221383 : Blo 1128631 3221383 := bstep (se 1 (by rfl) ⟨2416037, by rfl⟩ : syracuseStep 3221383 = 4832075) B4832075
theorem B3057593 : Blo 1128631 3057593 := bstep (se 2 (by rfl) ⟨1146597, by rfl⟩ : syracuseStep 3057593 = 2293195) B2293195
theorem B1910729 : Blo 1128631 1910729 := bstep (se 2 (by rfl) ⟨716523, by rfl⟩ : syracuseStep 1910729 = 1433047) B1433047
theorem B2861203 : Blo 1128631 2861203 := bstep (se 1 (by rfl) ⟨2145902, by rfl⟩ : syracuseStep 2861203 = 4291805) B4291805
theorem B3221657 : Blo 1128631 3221657 := bstep (se 2 (by rfl) ⟨1208121, by rfl⟩ : syracuseStep 3221657 = 2416243) B2416243
theorem B9152801 : Blo 1128631 9152801 := bstep (se 2 (by rfl) ⟨3432300, by rfl⟩ : syracuseStep 9152801 = 6864601) B6864601
theorem B2861345 : Blo 1128631 2861345 := bstep (se 2 (by rfl) ⟨1073004, by rfl⟩ : syracuseStep 2861345 = 2146009) B2146009
theorem B3811643 : Blo 1128631 3811643 := bstep (se 1 (by rfl) ⟨2858732, by rfl⟩ : syracuseStep 3811643 = 5717465) B5717465
theorem B2173483 : Blo 1128631 2173483 := bstep (se 1 (by rfl) ⟨1630112, by rfl⟩ : syracuseStep 2173483 = 3260225) B3260225
theorem B1288975 : Blo 1128631 1288975 := bstep (se 1 (by rfl) ⟨966731, by rfl⟩ : syracuseStep 1288975 = 1933463) B1933463
theorem B3812129 : Blo 1128631 3812129 := bstep (se 2 (by rfl) ⟨1429548, by rfl⟩ : syracuseStep 3812129 = 2859097) B2859097
theorem B1813547 : Blo 1128631 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B2862337 : Blo 1128631 2862337 := bstep (se 2 (by rfl) ⟨1073376, by rfl⟩ : syracuseStep 2862337 = 2146753) B2146753
theorem B6434063 : Blo 1128631 6434063 := bstep (se 1 (by rfl) ⟨4825547, by rfl⟩ : syracuseStep 6434063 = 9651095) B9651095
theorem B3058987 : Blo 1128631 3058987 := bstep (se 1 (by rfl) ⟨2294240, by rfl⟩ : syracuseStep 3058987 = 4588481) B4588481
theorem B3812723 : Blo 1128631 3812723 := bstep (se 1 (by rfl) ⟨2859542, by rfl⟩ : syracuseStep 3812723 = 5719085) B5719085
theorem B3222899 : Blo 1128631 3222899 := bstep (se 1 (by rfl) ⟨2417174, by rfl⟩ : syracuseStep 3222899 = 4834349) B4834349
theorem B6434315 : Blo 1128631 6434315 := bstep (se 1 (by rfl) ⟨4825736, by rfl⟩ : syracuseStep 6434315 = 9651473) B9651473
theorem B2862935 : Blo 1128631 2862935 := bstep (se 1 (by rfl) ⟨2147201, by rfl⟩ : syracuseStep 2862935 = 4294403) B4294403
theorem B2863147 : Blo 1128631 2863147 := bstep (se 1 (by rfl) ⟨2147360, by rfl⟩ : syracuseStep 2863147 = 4294721) B4294721
theorem B2863289 : Blo 1128631 2863289 := bstep (se 2 (by rfl) ⟨1073733, by rfl⟩ : syracuseStep 2863289 = 2147467) B2147467
theorem B3617291 : Blo 1128631 3617291 := bstep (se 1 (by rfl) ⟨2712968, by rfl⟩ : syracuseStep 3617291 = 5425937) B5425937
theorem B3060371 : Blo 1128631 3060371 := bstep (se 1 (by rfl) ⟨2295278, by rfl⟩ : syracuseStep 3060371 = 4590557) B4590557
theorem B6435521 : Blo 1128631 6435521 := bstep (se 2 (by rfl) ⟨2413320, by rfl⟩ : syracuseStep 6435521 = 4826641) B4826641
theorem B5157665 : Blo 1128631 5157665 := bstep (se 2 (by rfl) ⟨1934124, by rfl⟩ : syracuseStep 5157665 = 3868249) B3868249
theorem B27898805 : Blo 1128631 27898805 := bstep (se 5 (by rfl) ⟨1307756, by rfl⟩ : syracuseStep 27898805 = 2615513) B2615513
theorem B5714873 : Blo 1128631 5714873 := bstep (se 2 (by rfl) ⟨2143077, by rfl⟩ : syracuseStep 5714873 = 4286155) B4286155
theorem B1356859 : Blo 1128631 1356859 := bstep (se 1 (by rfl) ⟨1017644, by rfl⟩ : syracuseStep 1356859 = 2035289) B2035289
theorem B2143351 : Blo 1128631 2143351 := bstep (se 1 (by rfl) ⟨1607513, by rfl⟩ : syracuseStep 2143351 = 3215027) B3215027
theorem B2864281 : Blo 1128631 2864281 := bstep (se 2 (by rfl) ⟨1074105, by rfl⟩ : syracuseStep 2864281 = 2148211) B2148211
theorem B2864443 : Blo 1128631 2864443 := bstep (se 1 (by rfl) ⟨2148332, by rfl⟩ : syracuseStep 2864443 = 4296665) B4296665
theorem B18363779 : Blo 1128631 18363779 := bstep (se 1 (by rfl) ⟨13772834, by rfl⟩ : syracuseStep 18363779 = 27545669) B27545669
theorem B2864585 : Blo 1128631 2864585 := bstep (se 2 (by rfl) ⟨1074219, by rfl⟩ : syracuseStep 2864585 = 2148439) B2148439
theorem B4830673 : Blo 1128631 4830673 := bstep (se 2 (by rfl) ⟨1811502, by rfl⟩ : syracuseStep 4830673 = 3623005) B3623005
theorem B1488443 : Blo 1128631 1488443 := bstep (se 1 (by rfl) ⟨1116332, by rfl⟩ : syracuseStep 1488443 = 2232665) B2232665
theorem B12203597 : Blo 1128631 12203597 := bstep (se 3 (by rfl) ⟨2288174, by rfl⟩ : syracuseStep 12203597 = 4576349) B4576349
theorem B2864929 : Blo 1128631 2864929 := bstep (se 2 (by rfl) ⟨1074348, by rfl⟩ : syracuseStep 2864929 = 2148697) B2148697
theorem B6108979 : Blo 1128631 6108979 := bstep (se 1 (by rfl) ⟨4581734, by rfl⟩ : syracuseStep 6108979 = 9163469) B9163469
theorem B4896571 : Blo 1128631 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B3815315 : Blo 1128631 3815315 := bstep (se 1 (by rfl) ⟨2861486, by rfl⟩ : syracuseStep 3815315 = 5722973) B5722973
theorem B4077611 : Blo 1128631 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B1718345 : Blo 1128631 1718345 := bstep (se 2 (by rfl) ⟨644379, by rfl⟩ : syracuseStep 1718345 = 1288759) B1288759
theorem B1128635 : Blo 1128631 1128635 := bstep (se 1 (by rfl) ⟨846476, by rfl⟩ : syracuseStep 1128635 = 1692953) B1692953
theorem B5716169 : Blo 1128631 5716169 := bstep (se 2 (by rfl) ⟨2143563, by rfl⟩ : syracuseStep 5716169 = 4287127) B4287127
theorem B1128711 : Blo 1128631 1128711 := bstep (se 1 (by rfl) ⟨846533, by rfl⟩ : syracuseStep 1128711 = 1693067) B1693067
theorem B1128719 : Blo 1128631 1128719 := bstep (se 1 (by rfl) ⟨846539, by rfl⟩ : syracuseStep 1128719 = 1693079) B1693079
theorem B1128763 : Blo 1128631 1128763 := bstep (se 1 (by rfl) ⟨846572, by rfl⟩ : syracuseStep 1128763 = 1693145) B1693145
theorem B3979579 : Blo 1128631 3979579 := bstep (se 1 (by rfl) ⟨2984684, by rfl⟩ : syracuseStep 3979579 = 5969369) B5969369
theorem B2865527 : Blo 1128631 2865527 := bstep (se 1 (by rfl) ⟨2149145, by rfl⟩ : syracuseStep 2865527 = 4298291) B4298291
theorem B1128839 : Blo 1128631 1128839 := bstep (se 1 (by rfl) ⟨846629, by rfl⟩ : syracuseStep 1128839 = 1693259) B1693259
theorem B1128847 : Blo 1128631 1128847 := bstep (se 1 (by rfl) ⟨846635, by rfl⟩ : syracuseStep 1128847 = 1693271) B1693271
theorem B1128891 : Blo 1128631 1128891 := bstep (se 1 (by rfl) ⟨846668, by rfl⟩ : syracuseStep 1128891 = 1693337) B1693337
theorem B1128967 : Blo 1128631 1128967 := bstep (se 1 (by rfl) ⟨846725, by rfl⟩ : syracuseStep 1128967 = 1693451) B1693451
theorem B1128975 : Blo 1128631 1128975 := bstep (se 1 (by rfl) ⟨846731, by rfl⟩ : syracuseStep 1128975 = 1693463) B1693463
theorem B1129019 : Blo 1128631 1129019 := bstep (se 1 (by rfl) ⟨846764, by rfl⟩ : syracuseStep 1129019 = 1693529) B1693529
theorem B1718857 : Blo 1128631 1718857 := bstep (se 2 (by rfl) ⟨644571, by rfl⟩ : syracuseStep 1718857 = 1289143) B1289143
theorem B1129095 : Blo 1128631 1129095 := bstep (se 1 (by rfl) ⟨846821, by rfl⟩ : syracuseStep 1129095 = 1693643) B1693643
theorem B1129103 : Blo 1128631 1129103 := bstep (se 1 (by rfl) ⟨846827, by rfl⟩ : syracuseStep 1129103 = 1693655) B1693655
theorem B1129147 : Blo 1128631 1129147 := bstep (se 1 (by rfl) ⟨846860, by rfl⟩ : syracuseStep 1129147 = 1693721) B1693721
theorem B1129223 : Blo 1128631 1129223 := bstep (se 1 (by rfl) ⟨846917, by rfl⟩ : syracuseStep 1129223 = 1693835) B1693835
theorem B1129231 : Blo 1128631 1129231 := bstep (se 1 (by rfl) ⟨846923, by rfl⟩ : syracuseStep 1129231 = 1693847) B1693847
theorem B1129275 : Blo 1128631 1129275 := bstep (se 1 (by rfl) ⟨846956, by rfl⟩ : syracuseStep 1129275 = 1693913) B1693913
theorem B2145143 : Blo 1128631 2145143 := bstep (se 1 (by rfl) ⟨1608857, by rfl⟩ : syracuseStep 2145143 = 3217715) B3217715
theorem B1129351 : Blo 1128631 1129351 := bstep (se 1 (by rfl) ⟨847013, by rfl⟩ : syracuseStep 1129351 = 1694027) B1694027
theorem B1129359 : Blo 1128631 1129359 := bstep (se 1 (by rfl) ⟨847019, by rfl⟩ : syracuseStep 1129359 = 1694039) B1694039
theorem B1129403 : Blo 1128631 1129403 := bstep (se 1 (by rfl) ⟨847052, by rfl⟩ : syracuseStep 1129403 = 1694105) B1694105
theorem B82394117 : Blo 1128631 82394117 := bstep (se 4 (by rfl) ⟨7724448, by rfl⟩ : syracuseStep 82394117 = 15448897) B15448897
theorem B1129479 : Blo 1128631 1129479 := bstep (se 1 (by rfl) ⟨847109, by rfl⟩ : syracuseStep 1129479 = 1694219) B1694219
theorem B1129487 : Blo 1128631 1129487 := bstep (se 1 (by rfl) ⟨847115, by rfl⟩ : syracuseStep 1129487 = 1694231) B1694231
theorem B2145295 : Blo 1128631 2145295 := bstep (se 1 (by rfl) ⟨1608971, by rfl⟩ : syracuseStep 2145295 = 3217943) B3217943
theorem B1129531 : Blo 1128631 1129531 := bstep (se 1 (by rfl) ⟨847148, by rfl⟩ : syracuseStep 1129531 = 1694297) B1694297
theorem B1129607 : Blo 1128631 1129607 := bstep (se 1 (by rfl) ⟨847205, by rfl⟩ : syracuseStep 1129607 = 1694411) B1694411
theorem B1129615 : Blo 1128631 1129615 := bstep (se 1 (by rfl) ⟨847211, by rfl⟩ : syracuseStep 1129615 = 1694423) B1694423
theorem B1129659 : Blo 1128631 1129659 := bstep (se 1 (by rfl) ⟨847244, by rfl⟩ : syracuseStep 1129659 = 1694489) B1694489
theorem B1129735 : Blo 1128631 1129735 := bstep (se 1 (by rfl) ⟨847301, by rfl⟩ : syracuseStep 1129735 = 1694603) B1694603
theorem B1129743 : Blo 1128631 1129743 := bstep (se 1 (by rfl) ⟨847307, by rfl⟩ : syracuseStep 1129743 = 1694615) B1694615
theorem B3816719 : Blo 1128631 3816719 := bstep (se 1 (by rfl) ⟨2862539, by rfl⟩ : syracuseStep 3816719 = 5725079) B5725079
theorem B1129787 : Blo 1128631 1129787 := bstep (se 1 (by rfl) ⟨847340, by rfl⟩ : syracuseStep 1129787 = 1694681) B1694681
theorem B1129863 : Blo 1128631 1129863 := bstep (se 1 (by rfl) ⟨847397, by rfl⟩ : syracuseStep 1129863 = 1694795) B1694795
theorem B1129871 : Blo 1128631 1129871 := bstep (se 1 (by rfl) ⟨847403, by rfl⟩ : syracuseStep 1129871 = 1694807) B1694807
theorem B2145683 : Blo 1128631 2145683 := bstep (se 1 (by rfl) ⟨1609262, by rfl⟩ : syracuseStep 2145683 = 3218525) B3218525
theorem B1129915 : Blo 1128631 1129915 := bstep (se 1 (by rfl) ⟨847436, by rfl⟩ : syracuseStep 1129915 = 1694873) B1694873
theorem B1129991 : Blo 1128631 1129991 := bstep (se 1 (by rfl) ⟨847493, by rfl⟩ : syracuseStep 1129991 = 1694987) B1694987
theorem B1129999 : Blo 1128631 1129999 := bstep (se 1 (by rfl) ⟨847499, by rfl⟩ : syracuseStep 1129999 = 1694999) B1694999
theorem B3816989 : Blo 1128631 3816989 := bstep (se 3 (by rfl) ⟨715685, by rfl⟩ : syracuseStep 3816989 = 1431371) B1431371
theorem B1130043 : Blo 1128631 1130043 := bstep (se 1 (by rfl) ⟨847532, by rfl⟩ : syracuseStep 1130043 = 1695065) B1695065
theorem B1130119 : Blo 1128631 1130119 := bstep (se 1 (by rfl) ⟨847589, by rfl⟩ : syracuseStep 1130119 = 1695179) B1695179
theorem B2866823 : Blo 1128631 2866823 := bstep (se 1 (by rfl) ⟨2150117, by rfl⟩ : syracuseStep 2866823 = 4300235) B4300235
theorem B1130127 : Blo 1128631 1130127 := bstep (se 1 (by rfl) ⟨847595, by rfl⟩ : syracuseStep 1130127 = 1695191) B1695191
theorem B2866873 : Blo 1128631 2866873 := bstep (se 2 (by rfl) ⟨1075077, by rfl⟩ : syracuseStep 2866873 = 2150155) B2150155
theorem B1130171 : Blo 1128631 1130171 := bstep (se 1 (by rfl) ⟨847628, by rfl⟩ : syracuseStep 1130171 = 1695257) B1695257
theorem B1130247 : Blo 1128631 1130247 := bstep (se 1 (by rfl) ⟨847685, by rfl⟩ : syracuseStep 1130247 = 1695371) B1695371
theorem B1130255 : Blo 1128631 1130255 := bstep (se 1 (by rfl) ⟨847691, by rfl⟩ : syracuseStep 1130255 = 1695383) B1695383
theorem B6438689 : Blo 1128631 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B1130299 : Blo 1128631 1130299 := bstep (se 1 (by rfl) ⟨847724, by rfl⟩ : syracuseStep 1130299 = 1695449) B1695449
theorem B9912179 : Blo 1128631 9912179 := bstep (se 1 (by rfl) ⟨7434134, by rfl⟩ : syracuseStep 9912179 = 14868269) B14868269
theorem B1130375 : Blo 1128631 1130375 := bstep (se 1 (by rfl) ⟨847781, by rfl⟩ : syracuseStep 1130375 = 1695563) B1695563
theorem B1130383 : Blo 1128631 1130383 := bstep (se 1 (by rfl) ⟨847787, by rfl⟩ : syracuseStep 1130383 = 1695575) B1695575
theorem B1130427 : Blo 1128631 1130427 := bstep (se 1 (by rfl) ⟨847820, by rfl⟩ : syracuseStep 1130427 = 1695641) B1695641
theorem B1130503 : Blo 1128631 1130503 := bstep (se 1 (by rfl) ⟨847877, by rfl⟩ : syracuseStep 1130503 = 1695755) B1695755
theorem B1130511 : Blo 1128631 1130511 := bstep (se 1 (by rfl) ⟨847883, by rfl⟩ : syracuseStep 1130511 = 1695767) B1695767
theorem B3096605 : Blo 1128631 3096605 := bstep (se 3 (by rfl) ⟨580613, by rfl⟩ : syracuseStep 3096605 = 1161227) B1161227
theorem B1130555 : Blo 1128631 1130555 := bstep (se 1 (by rfl) ⟨847916, by rfl⟩ : syracuseStep 1130555 = 1695833) B1695833
theorem B2539655 : Blo 1128631 2539655 := bstep (se 1 (by rfl) ⟨1904741, by rfl⟩ : syracuseStep 2539655 = 3809483) B3809483
theorem B1130631 : Blo 1128631 1130631 := bstep (se 1 (by rfl) ⟨847973, by rfl⟩ : syracuseStep 1130631 = 1695947) B1695947
theorem B1130639 : Blo 1128631 1130639 := bstep (se 1 (by rfl) ⟨847979, by rfl⟩ : syracuseStep 1130639 = 1695959) B1695959
theorem B1130683 : Blo 1128631 1130683 := bstep (se 1 (by rfl) ⟨848012, by rfl⟩ : syracuseStep 1130683 = 1696025) B1696025
theorem B24461513 : Blo 1128631 24461513 := bstep (se 2 (by rfl) ⟨9173067, by rfl⟩ : syracuseStep 24461513 = 18346135) B18346135
theorem B1130759 : Blo 1128631 1130759 := bstep (se 1 (by rfl) ⟨848069, by rfl⟩ : syracuseStep 1130759 = 1696139) B1696139
theorem B1130767 : Blo 1128631 1130767 := bstep (se 1 (by rfl) ⟨848075, by rfl⟩ : syracuseStep 1130767 = 1696151) B1696151
theorem B2539835 : Blo 1128631 2539835 := bstep (se 1 (by rfl) ⟨1904876, by rfl⟩ : syracuseStep 2539835 = 3809753) B3809753
theorem B1130811 : Blo 1128631 1130811 := bstep (se 1 (by rfl) ⟨848108, by rfl⟩ : syracuseStep 1130811 = 1696217) B1696217
theorem B1130887 : Blo 1128631 1130887 := bstep (se 1 (by rfl) ⟨848165, by rfl⟩ : syracuseStep 1130887 = 1696331) B1696331
theorem B1130895 : Blo 1128631 1130895 := bstep (se 1 (by rfl) ⟨848171, by rfl⟩ : syracuseStep 1130895 = 1696343) B1696343
theorem B66896273 : Blo 1128631 66896273 := bstep (se 2 (by rfl) ⟨25086102, by rfl⟩ : syracuseStep 66896273 = 50172205) B50172205
theorem B2539961 : Blo 1128631 2539961 := bstep (se 2 (by rfl) ⟨952485, by rfl⟩ : syracuseStep 2539961 = 1904971) B1904971
theorem B1130939 : Blo 1128631 1130939 := bstep (se 1 (by rfl) ⟨848204, by rfl⟩ : syracuseStep 1130939 = 1696409) B1696409
theorem B20595185 : Blo 1128631 20595185 := bstep (se 2 (by rfl) ⟨7723194, by rfl⟩ : syracuseStep 20595185 = 15446389) B15446389
theorem B1131015 : Blo 1128631 1131015 := bstep (se 1 (by rfl) ⟨848261, by rfl⟩ : syracuseStep 1131015 = 1696523) B1696523
theorem B1131023 : Blo 1128631 1131023 := bstep (se 1 (by rfl) ⟨848267, by rfl⟩ : syracuseStep 1131023 = 1696535) B1696535
theorem B1131067 : Blo 1128631 1131067 := bstep (se 1 (by rfl) ⟨848300, by rfl⟩ : syracuseStep 1131067 = 1696601) B1696601
theorem B1131143 : Blo 1128631 1131143 := bstep (se 1 (by rfl) ⟨848357, by rfl⟩ : syracuseStep 1131143 = 1696715) B1696715
theorem B1131151 : Blo 1128631 1131151 := bstep (se 1 (by rfl) ⟨848363, by rfl⟩ : syracuseStep 1131151 = 1696727) B1696727
theorem B1131195 : Blo 1128631 1131195 := bstep (se 1 (by rfl) ⟨848396, by rfl⟩ : syracuseStep 1131195 = 1696793) B1696793
theorem B1131271 : Blo 1128631 1131271 := bstep (se 1 (by rfl) ⟨848453, by rfl⟩ : syracuseStep 1131271 = 1696907) B1696907
theorem B2540303 : Blo 1128631 2540303 := bstep (se 1 (by rfl) ⟨1905227, by rfl⟩ : syracuseStep 2540303 = 3810455) B3810455
theorem B2147087 : Blo 1128631 2147087 := bstep (se 1 (by rfl) ⟨1610315, by rfl⟩ : syracuseStep 2147087 = 3220631) B3220631
theorem B1131279 : Blo 1128631 1131279 := bstep (se 1 (by rfl) ⟨848459, by rfl⟩ : syracuseStep 1131279 = 1696919) B1696919
theorem B2540321 : Blo 1128631 2540321 := bstep (se 2 (by rfl) ⟨952620, by rfl⟩ : syracuseStep 2540321 = 1905241) B1905241
theorem B1131323 : Blo 1128631 1131323 := bstep (se 1 (by rfl) ⟨848492, by rfl⟩ : syracuseStep 1131323 = 1696985) B1696985
theorem B1131399 : Blo 1128631 1131399 := bstep (se 1 (by rfl) ⟨848549, by rfl⟩ : syracuseStep 1131399 = 1697099) B1697099
theorem B1131407 : Blo 1128631 1131407 := bstep (se 1 (by rfl) ⟨848555, by rfl⟩ : syracuseStep 1131407 = 1697111) B1697111
theorem B3818393 : Blo 1128631 3818393 := bstep (se 2 (by rfl) ⟨1431897, by rfl⟩ : syracuseStep 3818393 = 2863795) B2863795
theorem B20661155 : Blo 1128631 20661155 := bstep (se 1 (by rfl) ⟨15495866, by rfl⟩ : syracuseStep 20661155 = 30991733) B30991733
theorem B1131451 : Blo 1128631 1131451 := bstep (se 1 (by rfl) ⟨848588, by rfl⟩ : syracuseStep 1131451 = 1697177) B1697177
theorem B1131527 : Blo 1128631 1131527 := bstep (se 1 (by rfl) ⟨848645, by rfl⟩ : syracuseStep 1131527 = 1697291) B1697291
theorem B12862475 : Blo 1128631 12862475 := bstep (se 1 (by rfl) ⟨9646856, by rfl⟩ : syracuseStep 12862475 = 19293713) B19293713
theorem B1131535 : Blo 1128631 1131535 := bstep (se 1 (by rfl) ⟨848651, by rfl⟩ : syracuseStep 1131535 = 1697303) B1697303
theorem B1131579 : Blo 1128631 1131579 := bstep (se 1 (by rfl) ⟨848684, by rfl⟩ : syracuseStep 1131579 = 1697369) B1697369
theorem B2540663 : Blo 1128631 2540663 := bstep (se 1 (by rfl) ⟨1905497, by rfl⟩ : syracuseStep 2540663 = 3810995) B3810995
theorem B1131655 : Blo 1128631 1131655 := bstep (se 1 (by rfl) ⟨848741, by rfl⟩ : syracuseStep 1131655 = 1697483) B1697483
theorem B1131663 : Blo 1128631 1131663 := bstep (se 1 (by rfl) ⟨848747, by rfl⟩ : syracuseStep 1131663 = 1697495) B1697495
theorem B1131707 : Blo 1128631 1131707 := bstep (se 1 (by rfl) ⟨848780, by rfl⟩ : syracuseStep 1131707 = 1697561) B1697561
theorem B1131783 : Blo 1128631 1131783 := bstep (se 1 (by rfl) ⟨848837, by rfl⟩ : syracuseStep 1131783 = 1697675) B1697675
theorem B1131791 : Blo 1128631 1131791 := bstep (se 1 (by rfl) ⟨848843, by rfl⟩ : syracuseStep 1131791 = 1697687) B1697687
theorem B2540843 : Blo 1128631 2540843 := bstep (se 1 (by rfl) ⟨1905632, by rfl⟩ : syracuseStep 2540843 = 3811265) B3811265
theorem B2147627 : Blo 1128631 2147627 := bstep (se 1 (by rfl) ⟨1610720, by rfl⟩ : syracuseStep 2147627 = 3221441) B3221441
theorem B1131835 : Blo 1128631 1131835 := bstep (se 1 (by rfl) ⟨848876, by rfl⟩ : syracuseStep 1131835 = 1697753) B1697753
theorem B1131911 : Blo 1128631 1131911 := bstep (se 1 (by rfl) ⟨848933, by rfl⟩ : syracuseStep 1131911 = 1697867) B1697867
theorem B1131919 : Blo 1128631 1131919 := bstep (se 1 (by rfl) ⟨848939, by rfl⟩ : syracuseStep 1131919 = 1697879) B1697879
theorem B1131963 : Blo 1128631 1131963 := bstep (se 1 (by rfl) ⟨848972, by rfl⟩ : syracuseStep 1131963 = 1697945) B1697945
theorem B1132039 : Blo 1128631 1132039 := bstep (se 1 (by rfl) ⟨849029, by rfl⟩ : syracuseStep 1132039 = 1698059) B1698059
theorem B1132047 : Blo 1128631 1132047 := bstep (se 1 (by rfl) ⟨849035, by rfl⟩ : syracuseStep 1132047 = 1698071) B1698071
theorem B1132091 : Blo 1128631 1132091 := bstep (se 1 (by rfl) ⟨849068, by rfl⟩ : syracuseStep 1132091 = 1698137) B1698137
theorem B3819095 : Blo 1128631 3819095 := bstep (se 1 (by rfl) ⟨2864321, by rfl⟩ : syracuseStep 3819095 = 5728643) B5728643
theorem B1132167 : Blo 1128631 1132167 := bstep (se 1 (by rfl) ⟨849125, by rfl⟩ : syracuseStep 1132167 = 1698251) B1698251
theorem B1132175 : Blo 1128631 1132175 := bstep (se 1 (by rfl) ⟨849131, by rfl⟩ : syracuseStep 1132175 = 1698263) B1698263
theorem B2541203 : Blo 1128631 2541203 := bstep (se 1 (by rfl) ⟨1905902, by rfl⟩ : syracuseStep 2541203 = 3811805) B3811805
theorem B1132219 : Blo 1128631 1132219 := bstep (se 1 (by rfl) ⟨849164, by rfl⟩ : syracuseStep 1132219 = 1698329) B1698329
theorem B2541257 : Blo 1128631 2541257 := bstep (se 2 (by rfl) ⟨952971, by rfl⟩ : syracuseStep 2541257 = 1905943) B1905943
theorem B1132295 : Blo 1128631 1132295 := bstep (se 1 (by rfl) ⟨849221, by rfl⟩ : syracuseStep 1132295 = 1698443) B1698443
theorem B1132303 : Blo 1128631 1132303 := bstep (se 1 (by rfl) ⟨849227, by rfl⟩ : syracuseStep 1132303 = 1698455) B1698455
theorem B1132347 : Blo 1128631 1132347 := bstep (se 1 (by rfl) ⟨849260, by rfl⟩ : syracuseStep 1132347 = 1698521) B1698521
theorem B1132423 : Blo 1128631 1132423 := bstep (se 1 (by rfl) ⟨849317, by rfl⟩ : syracuseStep 1132423 = 1698635) B1698635
theorem B1132431 : Blo 1128631 1132431 := bstep (se 1 (by rfl) ⟨849323, by rfl⟩ : syracuseStep 1132431 = 1698647) B1698647
theorem B9652121 : Blo 1128631 9652121 := bstep (se 2 (by rfl) ⟨3619545, by rfl⟩ : syracuseStep 9652121 = 7239091) B7239091
theorem B1132475 : Blo 1128631 1132475 := bstep (se 1 (by rfl) ⟨849356, by rfl⟩ : syracuseStep 1132475 = 1698713) B1698713
theorem B1132551 : Blo 1128631 1132551 := bstep (se 1 (by rfl) ⟨849413, by rfl⟩ : syracuseStep 1132551 = 1698827) B1698827
theorem B1132559 : Blo 1128631 1132559 := bstep (se 1 (by rfl) ⟨849419, by rfl⟩ : syracuseStep 1132559 = 1698839) B1698839
theorem B6113303 : Blo 1128631 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B1132603 : Blo 1128631 1132603 := bstep (se 1 (by rfl) ⟨849452, by rfl⟩ : syracuseStep 1132603 = 1698905) B1698905
theorem B3819581 : Blo 1128631 3819581 := bstep (se 3 (by rfl) ⟨716171, by rfl⟩ : syracuseStep 3819581 = 1432343) B1432343
theorem B4835389 : Blo 1128631 4835389 := bstep (se 3 (by rfl) ⟨906635, by rfl⟩ : syracuseStep 4835389 = 1813271) B1813271
theorem B1394807 : Blo 1128631 1394807 := bstep (se 1 (by rfl) ⟨1046105, by rfl⟩ : syracuseStep 1394807 = 2092211) B2092211
theorem B6441079 : Blo 1128631 6441079 := bstep (se 1 (by rfl) ⟨4830809, by rfl⟩ : syracuseStep 6441079 = 9661619) B9661619
theorem B6703397 : Blo 1128631 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B2541959 : Blo 1128631 2541959 := bstep (se 1 (by rfl) ⟨1906469, by rfl⟩ : syracuseStep 2541959 = 3812939) B3812939
theorem B2148743 : Blo 1128631 2148743 := bstep (se 1 (by rfl) ⟨1611557, by rfl⟩ : syracuseStep 2148743 = 3223115) B3223115
theorem B1526159 : Blo 1128631 1526159 := bstep (se 1 (by rfl) ⟨1144619, by rfl⟩ : syracuseStep 1526159 = 2289239) B2289239
theorem B5425667 : Blo 1128631 5425667 := bstep (se 1 (by rfl) ⟨4069250, by rfl⟩ : syracuseStep 5425667 = 8138501) B8138501
theorem B3623467 : Blo 1128631 3623467 := bstep (se 1 (by rfl) ⟨2717600, by rfl⟩ : syracuseStep 3623467 = 5435201) B5435201
theorem B2542139 : Blo 1128631 2542139 := bstep (se 1 (by rfl) ⟨1906604, by rfl⟩ : syracuseStep 2542139 = 3813209) B3813209
theorem B2542265 : Blo 1128631 2542265 := bstep (se 2 (by rfl) ⟨953349, by rfl⟩ : syracuseStep 2542265 = 1906699) B1906699
theorem B2149267 : Blo 1128631 2149267 := bstep (se 1 (by rfl) ⟨1611950, by rfl⟩ : syracuseStep 2149267 = 3223901) B3223901
theorem B5426129 : Blo 1128631 5426129 := bstep (se 2 (by rfl) ⟨2034798, by rfl⟩ : syracuseStep 5426129 = 4069597) B4069597
theorem B2542607 : Blo 1128631 2542607 := bstep (se 1 (by rfl) ⟨1906955, by rfl⟩ : syracuseStep 2542607 = 3813911) B3813911
theorem B2542625 : Blo 1128631 2542625 := bstep (se 2 (by rfl) ⟨953484, by rfl⟩ : syracuseStep 2542625 = 1906969) B1906969
theorem B1428779 : Blo 1128631 1428779 := bstep (se 1 (by rfl) ⟨1071584, by rfl⟩ : syracuseStep 1428779 = 2143169) B2143169
theorem B6442355 : Blo 1128631 6442355 := bstep (se 1 (by rfl) ⟨4831766, by rfl⟩ : syracuseStep 6442355 = 9663533) B9663533
theorem B2542967 : Blo 1128631 2542967 := bstep (se 1 (by rfl) ⟨1907225, by rfl⟩ : syracuseStep 2542967 = 3814451) B3814451
theorem B3820985 : Blo 1128631 3820985 := bstep (se 2 (by rfl) ⟨1432869, by rfl⟩ : syracuseStep 3820985 = 2865739) B2865739
theorem B2543147 : Blo 1128631 2543147 := bstep (se 1 (by rfl) ⟨1907360, by rfl⟩ : syracuseStep 2543147 = 3814721) B3814721
theorem B1429255 : Blo 1128631 1429255 := bstep (se 1 (by rfl) ⟨1071941, by rfl⟩ : syracuseStep 1429255 = 2143883) B2143883
theorem B6442811 : Blo 1128631 6442811 := bstep (se 1 (by rfl) ⟨4832108, by rfl⟩ : syracuseStep 6442811 = 9664217) B9664217
theorem B5722001 : Blo 1128631 5722001 := bstep (se 2 (by rfl) ⟨2145750, by rfl⟩ : syracuseStep 5722001 = 4291501) B4291501
theorem B2543507 : Blo 1128631 2543507 := bstep (se 1 (by rfl) ⟨1907630, by rfl⟩ : syracuseStep 2543507 = 3815261) B3815261
theorem B3624851 : Blo 1128631 3624851 := bstep (se 1 (by rfl) ⟨2718638, by rfl⟩ : syracuseStep 3624851 = 5437277) B5437277
theorem B2543561 : Blo 1128631 2543561 := bstep (se 2 (by rfl) ⟨953835, by rfl⟩ : syracuseStep 2543561 = 1907671) B1907671
theorem B10866635 : Blo 1128631 10866635 := bstep (se 1 (by rfl) ⟨8149976, by rfl⟩ : syracuseStep 10866635 = 16299953) B16299953
theorem B3821579 : Blo 1128631 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B3821687 : Blo 1128631 3821687 := bstep (se 1 (by rfl) ⟨2866265, by rfl⟩ : syracuseStep 3821687 = 5732531) B5732531
theorem B2576569 : Blo 1128631 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B1429751 : Blo 1128631 1429751 := bstep (se 1 (by rfl) ⟨1072313, by rfl⟩ : syracuseStep 1429751 = 2144627) B2144627
theorem B3625249 : Blo 1128631 3625249 := bstep (se 2 (by rfl) ⟨1359468, by rfl⟩ : syracuseStep 3625249 = 2718937) B2718937
theorem B1429903 : Blo 1128631 1429903 := bstep (se 1 (by rfl) ⟨1072427, by rfl⟩ : syracuseStep 1429903 = 2144855) B2144855
theorem B1430075 : Blo 1128631 1430075 := bstep (se 1 (by rfl) ⟨1072556, by rfl⟩ : syracuseStep 1430075 = 2145113) B2145113
theorem B2544263 : Blo 1128631 2544263 := bstep (se 1 (by rfl) ⟨1908197, by rfl⟩ : syracuseStep 2544263 = 3816395) B3816395
theorem B3822281 : Blo 1128631 3822281 := bstep (se 2 (by rfl) ⟨1433355, by rfl⟩ : syracuseStep 3822281 = 2866711) B2866711
theorem B6443813 : Blo 1128631 6443813 := bstep (se 4 (by rfl) ⟨604107, by rfl⟩ : syracuseStep 6443813 = 1208215) B1208215
theorem B2544443 : Blo 1128631 2544443 := bstep (se 1 (by rfl) ⟨1908332, by rfl⟩ : syracuseStep 2544443 = 3816665) B3816665
theorem B2544569 : Blo 1128631 2544569 := bstep (se 2 (by rfl) ⟨954213, by rfl⟩ : syracuseStep 2544569 = 1908427) B1908427
theorem B5428397 : Blo 1128631 5428397 := bstep (se 3 (by rfl) ⟨1017824, by rfl⟩ : syracuseStep 5428397 = 2035649) B2035649
theorem B9655469 : Blo 1128631 9655469 := bstep (se 3 (by rfl) ⟨1810400, by rfl⟩ : syracuseStep 9655469 = 3620801) B3620801
theorem B6444269 : Blo 1128631 6444269 := bstep (se 3 (by rfl) ⟨1208300, by rfl⟩ : syracuseStep 6444269 = 2416601) B2416601
theorem B2544911 : Blo 1128631 2544911 := bstep (se 1 (by rfl) ⟨1908683, by rfl⟩ : syracuseStep 2544911 = 3817367) B3817367
theorem B12866849 : Blo 1128631 12866849 := bstep (se 2 (by rfl) ⟨4825068, by rfl⟩ : syracuseStep 12866849 = 9650137) B9650137
theorem B2544929 : Blo 1128631 2544929 := bstep (se 2 (by rfl) ⟨954348, by rfl⟩ : syracuseStep 2544929 = 1908697) B1908697
theorem B1692971 : Blo 1128631 1692971 := bstep (se 1 (by rfl) ⟨1269728, by rfl⟩ : syracuseStep 1692971 = 2539457) B2539457
theorem B1693001 : Blo 1128631 1693001 := bstep (se 2 (by rfl) ⟨634875, by rfl⟩ : syracuseStep 1693001 = 1269751) B1269751
theorem B1693115 : Blo 1128631 1693115 := bstep (se 1 (by rfl) ⟨1269836, by rfl⟩ : syracuseStep 1693115 = 2539673) B2539673
theorem B1693175 : Blo 1128631 1693175 := bstep (se 1 (by rfl) ⟨1269881, by rfl⟩ : syracuseStep 1693175 = 2539763) B2539763
theorem B1431047 : Blo 1128631 1431047 := bstep (se 1 (by rfl) ⟨1073285, by rfl⟩ : syracuseStep 1431047 = 2146571) B2146571
theorem B1693199 : Blo 1128631 1693199 := bstep (se 1 (by rfl) ⟨1269899, by rfl⟩ : syracuseStep 1693199 = 2539799) B2539799
theorem B1693241 : Blo 1128631 1693241 := bstep (se 2 (by rfl) ⟨634965, by rfl⟩ : syracuseStep 1693241 = 1269931) B1269931
theorem B2545271 : Blo 1128631 2545271 := bstep (se 1 (by rfl) ⟨1908953, by rfl⟩ : syracuseStep 2545271 = 3817907) B3817907
theorem B565040771 : Blo 1128631 565040771 := bstep (se 1 (by rfl) ⟨423780578, by rfl⟩ : syracuseStep 565040771 = 847561157) B847561157
theorem B1693319 : Blo 1128631 1693319 := bstep (se 1 (by rfl) ⟨1269989, by rfl⟩ : syracuseStep 1693319 = 2539979) B2539979
theorem B1693355 : Blo 1128631 1693355 := bstep (se 1 (by rfl) ⟨1270016, by rfl⟩ : syracuseStep 1693355 = 2540033) B2540033
theorem B1693385 : Blo 1128631 1693385 := bstep (se 2 (by rfl) ⟨635019, by rfl⟩ : syracuseStep 1693385 = 1270039) B1270039
theorem B2545451 : Blo 1128631 2545451 := bstep (se 1 (by rfl) ⟨1909088, by rfl⟩ : syracuseStep 2545451 = 3818177) B3818177
theorem B1693499 : Blo 1128631 1693499 := bstep (se 1 (by rfl) ⟨1270124, by rfl⟩ : syracuseStep 1693499 = 2540249) B2540249
theorem B5429051 : Blo 1128631 5429051 := bstep (se 1 (by rfl) ⟨4071788, by rfl⟩ : syracuseStep 5429051 = 8143577) B8143577
theorem B1693559 : Blo 1128631 1693559 := bstep (se 1 (by rfl) ⟨1270169, by rfl⟩ : syracuseStep 1693559 = 2540339) B2540339
theorem B1693583 : Blo 1128631 1693583 := bstep (se 1 (by rfl) ⟨1270187, by rfl⟩ : syracuseStep 1693583 = 2540375) B2540375
theorem B6444953 : Blo 1128631 6444953 := bstep (se 2 (by rfl) ⟨2416857, by rfl⟩ : syracuseStep 6444953 = 4833715) B4833715
theorem B1693625 : Blo 1128631 1693625 := bstep (se 2 (by rfl) ⟨635109, by rfl⟩ : syracuseStep 1693625 = 1270219) B1270219
theorem B5724107 : Blo 1128631 5724107 := bstep (se 1 (by rfl) ⟨4293080, by rfl⟩ : syracuseStep 5724107 = 8586161) B8586161
theorem B1693703 : Blo 1128631 1693703 := bstep (se 1 (by rfl) ⟨1270277, by rfl⟩ : syracuseStep 1693703 = 2540555) B2540555
theorem B4577323 : Blo 1128631 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B1693739 : Blo 1128631 1693739 := bstep (se 1 (by rfl) ⟨1270304, by rfl⟩ : syracuseStep 1693739 = 2540609) B2540609
theorem B1693769 : Blo 1128631 1693769 := bstep (se 2 (by rfl) ⟨635163, by rfl⟩ : syracuseStep 1693769 = 1270327) B1270327
theorem B1431695 : Blo 1128631 1431695 := bstep (se 1 (by rfl) ⟨1073771, by rfl⟩ : syracuseStep 1431695 = 2147543) B2147543
theorem B2545811 : Blo 1128631 2545811 := bstep (se 1 (by rfl) ⟨1909358, by rfl⟩ : syracuseStep 2545811 = 3818717) B3818717
theorem B1693883 : Blo 1128631 1693883 := bstep (se 1 (by rfl) ⟨1270412, by rfl⟩ : syracuseStep 1693883 = 2540825) B2540825
theorem B2545865 : Blo 1128631 2545865 := bstep (se 2 (by rfl) ⟨954699, by rfl⟩ : syracuseStep 2545865 = 1909399) B1909399
theorem B27908297 : Blo 1128631 27908297 := bstep (se 2 (by rfl) ⟨10465611, by rfl⟩ : syracuseStep 27908297 = 20931223) B20931223
theorem B1693943 : Blo 1128631 1693943 := bstep (se 1 (by rfl) ⟨1270457, by rfl⟩ : syracuseStep 1693943 = 2540915) B2540915
theorem B1693967 : Blo 1128631 1693967 := bstep (se 1 (by rfl) ⟨1270475, by rfl⟩ : syracuseStep 1693967 = 2540951) B2540951
theorem B5724431 : Blo 1128631 5724431 := bstep (se 1 (by rfl) ⟨4293323, by rfl⟩ : syracuseStep 5724431 = 8586647) B8586647
theorem B1694009 : Blo 1128631 1694009 := bstep (se 2 (by rfl) ⟨635253, by rfl⟩ : syracuseStep 1694009 = 1270507) B1270507
theorem B1694087 : Blo 1128631 1694087 := bstep (se 1 (by rfl) ⟨1270565, by rfl⟩ : syracuseStep 1694087 = 2541131) B2541131
theorem B1694123 : Blo 1128631 1694123 := bstep (se 1 (by rfl) ⟨1270592, by rfl⟩ : syracuseStep 1694123 = 2541185) B2541185
theorem B1694153 : Blo 1128631 1694153 := bstep (se 2 (by rfl) ⟨635307, by rfl⟩ : syracuseStep 1694153 = 1270615) B1270615
theorem B1694267 : Blo 1128631 1694267 := bstep (se 1 (by rfl) ⟨1270700, by rfl⟩ : syracuseStep 1694267 = 2541401) B2541401
theorem B1694327 : Blo 1128631 1694327 := bstep (se 1 (by rfl) ⟨1270745, by rfl⟩ : syracuseStep 1694327 = 2541491) B2541491
theorem B1694351 : Blo 1128631 1694351 := bstep (se 1 (by rfl) ⟨1270763, by rfl⟩ : syracuseStep 1694351 = 2541527) B2541527
theorem B1694393 : Blo 1128631 1694393 := bstep (se 2 (by rfl) ⟨635397, by rfl⟩ : syracuseStep 1694393 = 1270795) B1270795
theorem B9296641 : Blo 1128631 9296641 := bstep (se 2 (by rfl) ⟨3486240, by rfl⟩ : syracuseStep 9296641 = 6972481) B6972481
theorem B1694471 : Blo 1128631 1694471 := bstep (se 1 (by rfl) ⟨1270853, by rfl⟩ : syracuseStep 1694471 = 2541707) B2541707
theorem B6871823 : Blo 1128631 6871823 := bstep (se 1 (by rfl) ⟨5153867, by rfl⟩ : syracuseStep 6871823 = 10307735) B10307735
theorem B3267343 : Blo 1128631 3267343 := bstep (se 1 (by rfl) ⟨2450507, by rfl⟩ : syracuseStep 3267343 = 4901015) B4901015
theorem B1694507 : Blo 1128631 1694507 := bstep (se 1 (by rfl) ⟨1270880, by rfl⟩ : syracuseStep 1694507 = 2541761) B2541761
theorem B1694537 : Blo 1128631 1694537 := bstep (se 2 (by rfl) ⟨635451, by rfl⟩ : syracuseStep 1694537 = 1270903) B1270903
theorem B2546567 : Blo 1128631 2546567 := bstep (se 1 (by rfl) ⟨1909925, by rfl⟩ : syracuseStep 2546567 = 3819851) B3819851
theorem B1694651 : Blo 1128631 1694651 := bstep (se 1 (by rfl) ⟨1270988, by rfl⟩ : syracuseStep 1694651 = 2541977) B2541977
theorem B1694711 : Blo 1128631 1694711 := bstep (se 1 (by rfl) ⟨1271033, by rfl⟩ : syracuseStep 1694711 = 2542067) B2542067
theorem B1694735 : Blo 1128631 1694735 := bstep (se 1 (by rfl) ⟨1271051, by rfl⟩ : syracuseStep 1694735 = 2542103) B2542103
theorem B1694777 : Blo 1128631 1694777 := bstep (se 2 (by rfl) ⟨635541, by rfl⟩ : syracuseStep 1694777 = 1271083) B1271083
theorem B2546747 : Blo 1128631 2546747 := bstep (se 1 (by rfl) ⟨1910060, by rfl⟩ : syracuseStep 2546747 = 3820121) B3820121
theorem B1694855 : Blo 1128631 1694855 := bstep (se 1 (by rfl) ⟨1271141, by rfl⟩ : syracuseStep 1694855 = 2542283) B2542283
theorem B1694891 : Blo 1128631 1694891 := bstep (se 1 (by rfl) ⟨1271168, by rfl⟩ : syracuseStep 1694891 = 2542337) B2542337
theorem B2546873 : Blo 1128631 2546873 := bstep (se 2 (by rfl) ⟨955077, by rfl⟩ : syracuseStep 2546873 = 1910155) B1910155
theorem B1694921 : Blo 1128631 1694921 := bstep (se 2 (by rfl) ⟨635595, by rfl⟩ : syracuseStep 1694921 = 1271191) B1271191
theorem B1695035 : Blo 1128631 1695035 := bstep (se 1 (by rfl) ⟨1271276, by rfl⟩ : syracuseStep 1695035 = 2542553) B2542553
theorem B73456955 : Blo 1128631 73456955 := bstep (se 1 (by rfl) ⟨55092716, by rfl⟩ : syracuseStep 73456955 = 110185433) B110185433
theorem B1695095 : Blo 1128631 1695095 := bstep (se 1 (by rfl) ⟨1271321, by rfl⟩ : syracuseStep 1695095 = 2542643) B2542643
theorem B2448775 : Blo 1128631 2448775 := bstep (se 1 (by rfl) ⟨1836581, by rfl⟩ : syracuseStep 2448775 = 3673163) B3673163
theorem B1695119 : Blo 1128631 1695119 := bstep (se 1 (by rfl) ⟨1271339, by rfl⟩ : syracuseStep 1695119 = 2542679) B2542679
theorem B8576441 : Blo 1128631 8576441 := bstep (se 2 (by rfl) ⟨3216165, by rfl⟩ : syracuseStep 8576441 = 6432331) B6432331
theorem B1695161 : Blo 1128631 1695161 := bstep (se 2 (by rfl) ⟨635685, by rfl⟩ : syracuseStep 1695161 = 1271371) B1271371
theorem B1695239 : Blo 1128631 1695239 := bstep (se 1 (by rfl) ⟨1271429, by rfl⟩ : syracuseStep 1695239 = 2542859) B2542859
theorem B2547215 : Blo 1128631 2547215 := bstep (se 1 (by rfl) ⟨1910411, by rfl⟩ : syracuseStep 2547215 = 3820823) B3820823
theorem B2547233 : Blo 1128631 2547233 := bstep (se 2 (by rfl) ⟨955212, by rfl⟩ : syracuseStep 2547233 = 1910425) B1910425
theorem B12213803 : Blo 1128631 12213803 := bstep (se 1 (by rfl) ⟨9160352, by rfl⟩ : syracuseStep 12213803 = 18320705) B18320705
theorem B1695275 : Blo 1128631 1695275 := bstep (se 1 (by rfl) ⟨1271456, by rfl⟩ : syracuseStep 1695275 = 2542913) B2542913
theorem B1695305 : Blo 1128631 1695305 := bstep (se 2 (by rfl) ⟨635739, by rfl⟩ : syracuseStep 1695305 = 1271479) B1271479
theorem B1695419 : Blo 1128631 1695419 := bstep (se 1 (by rfl) ⟨1271564, by rfl⟩ : syracuseStep 1695419 = 2543129) B2543129
theorem B5725889 : Blo 1128631 5725889 := bstep (se 2 (by rfl) ⟨2147208, by rfl⟩ : syracuseStep 5725889 = 4294417) B4294417
theorem B1695479 : Blo 1128631 1695479 := bstep (se 1 (by rfl) ⟨1271609, by rfl⟩ : syracuseStep 1695479 = 2543219) B2543219
theorem B1695503 : Blo 1128631 1695503 := bstep (se 1 (by rfl) ⟨1271627, by rfl⟩ : syracuseStep 1695503 = 2543255) B2543255
theorem B1695545 : Blo 1128631 1695545 := bstep (se 2 (by rfl) ⟨635829, by rfl⟩ : syracuseStep 1695545 = 1271659) B1271659
theorem B3432311 : Blo 1128631 3432311 := bstep (se 1 (by rfl) ⟨2574233, by rfl⟩ : syracuseStep 3432311 = 5148467) B5148467
theorem B2547575 : Blo 1128631 2547575 := bstep (se 1 (by rfl) ⟨1910681, by rfl⟩ : syracuseStep 2547575 = 3821363) B3821363
theorem B1695623 : Blo 1128631 1695623 := bstep (se 1 (by rfl) ⟨1271717, by rfl⟩ : syracuseStep 1695623 = 2543435) B2543435
theorem B1695659 : Blo 1128631 1695659 := bstep (se 1 (by rfl) ⟨1271744, by rfl⟩ : syracuseStep 1695659 = 2543489) B2543489
theorem B1695689 : Blo 1128631 1695689 := bstep (se 2 (by rfl) ⟨635883, by rfl⟩ : syracuseStep 1695689 = 1271767) B1271767
theorem B2547755 : Blo 1128631 2547755 := bstep (se 1 (by rfl) ⟨1910816, by rfl⟩ : syracuseStep 2547755 = 3821633) B3821633
theorem B1695803 : Blo 1128631 1695803 := bstep (se 1 (by rfl) ⟨1271852, by rfl⟩ : syracuseStep 1695803 = 2543705) B2543705
theorem B1695863 : Blo 1128631 1695863 := bstep (se 1 (by rfl) ⟨1271897, by rfl⟩ : syracuseStep 1695863 = 2543795) B2543795
theorem B12869765 : Blo 1128631 12869765 := bstep (se 4 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 12869765 = 2413081) B2413081
theorem B1269895 : Blo 1128631 1269895 := bstep (se 1 (by rfl) ⟨952421, by rfl⟩ : syracuseStep 1269895 = 1904843) B1904843
theorem B1695887 : Blo 1128631 1695887 := bstep (se 1 (by rfl) ⟨1271915, by rfl⟩ : syracuseStep 1695887 = 2543831) B2543831
theorem B1695929 : Blo 1128631 1695929 := bstep (se 2 (by rfl) ⟨635973, by rfl⟩ : syracuseStep 1695929 = 1271947) B1271947
theorem B1696007 : Blo 1128631 1696007 := bstep (se 1 (by rfl) ⟨1272005, by rfl⟩ : syracuseStep 1696007 = 2544011) B2544011
theorem B1696043 : Blo 1128631 1696043 := bstep (se 1 (by rfl) ⟨1272032, by rfl⟩ : syracuseStep 1696043 = 2544065) B2544065
theorem B1270075 : Blo 1128631 1270075 := bstep (se 1 (by rfl) ⟨952556, by rfl⟩ : syracuseStep 1270075 = 1905113) B1905113
theorem B1696073 : Blo 1128631 1696073 := bstep (se 2 (by rfl) ⟨636027, by rfl⟩ : syracuseStep 1696073 = 1272055) B1272055
theorem B2548115 : Blo 1128631 2548115 := bstep (se 1 (by rfl) ⟨1911086, by rfl⟩ : syracuseStep 2548115 = 3822173) B3822173
theorem B1696187 : Blo 1128631 1696187 := bstep (se 1 (by rfl) ⟨1272140, by rfl⟩ : syracuseStep 1696187 = 2544281) B2544281
theorem B2548169 : Blo 1128631 2548169 := bstep (se 2 (by rfl) ⟨955563, by rfl⟩ : syracuseStep 2548169 = 1911127) B1911127
theorem B1696247 : Blo 1128631 1696247 := bstep (se 1 (by rfl) ⟨1272185, by rfl⟩ : syracuseStep 1696247 = 2544371) B2544371
theorem B1696271 : Blo 1128631 1696271 := bstep (se 1 (by rfl) ⟨1272203, by rfl⟩ : syracuseStep 1696271 = 2544407) B2544407
theorem B1696313 : Blo 1128631 1696313 := bstep (se 2 (by rfl) ⟨636117, by rfl⟩ : syracuseStep 1696313 = 1272235) B1272235
theorem B2712199 : Blo 1128631 2712199 := bstep (se 1 (by rfl) ⟨2034149, by rfl⟩ : syracuseStep 2712199 = 4068299) B4068299
theorem B1696391 : Blo 1128631 1696391 := bstep (se 1 (by rfl) ⟨1272293, by rfl⟩ : syracuseStep 1696391 = 2544587) B2544587
theorem B1696427 : Blo 1128631 1696427 := bstep (se 1 (by rfl) ⟨1272320, by rfl⟩ : syracuseStep 1696427 = 2544641) B2544641
theorem B1696457 : Blo 1128631 1696457 := bstep (se 2 (by rfl) ⟨636171, by rfl⟩ : syracuseStep 1696457 = 1272343) B1272343
theorem B6120137 : Blo 1128631 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B1270543 : Blo 1128631 1270543 := bstep (se 1 (by rfl) ⟨952907, by rfl⟩ : syracuseStep 1270543 = 1905815) B1905815
theorem B1696571 : Blo 1128631 1696571 := bstep (se 1 (by rfl) ⟨1272428, by rfl⟩ : syracuseStep 1696571 = 2544857) B2544857
theorem B1696631 : Blo 1128631 1696631 := bstep (se 1 (by rfl) ⟨1272473, by rfl⟩ : syracuseStep 1696631 = 2544947) B2544947
theorem B1696655 : Blo 1128631 1696655 := bstep (se 1 (by rfl) ⟨1272491, by rfl⟩ : syracuseStep 1696655 = 2544983) B2544983
theorem B1696697 : Blo 1128631 1696697 := bstep (se 2 (by rfl) ⟨636261, by rfl⟩ : syracuseStep 1696697 = 1272523) B1272523
theorem B5727185 : Blo 1128631 5727185 := bstep (se 2 (by rfl) ⟨2147694, by rfl⟩ : syracuseStep 5727185 = 4295389) B4295389
theorem B1696775 : Blo 1128631 1696775 := bstep (se 1 (by rfl) ⟨1272581, by rfl⟩ : syracuseStep 1696775 = 2545163) B2545163
theorem B1696811 : Blo 1128631 1696811 := bstep (se 1 (by rfl) ⟨1272608, by rfl⟩ : syracuseStep 1696811 = 2545217) B2545217
theorem B4645955 : Blo 1128631 4645955 := bstep (se 1 (by rfl) ⟨3484466, by rfl⟩ : syracuseStep 4645955 = 6968933) B6968933
theorem B1696841 : Blo 1128631 1696841 := bstep (se 2 (by rfl) ⟨636315, by rfl⟩ : syracuseStep 1696841 = 1272631) B1272631
theorem B7234733 : Blo 1128631 7234733 := bstep (se 3 (by rfl) ⟨1356512, by rfl⟩ : syracuseStep 7234733 = 2713025) B2713025
theorem B1696955 : Blo 1128631 1696955 := bstep (se 1 (by rfl) ⟨1272716, by rfl⟩ : syracuseStep 1696955 = 2545433) B2545433
theorem B1697015 : Blo 1128631 1697015 := bstep (se 1 (by rfl) ⟨1272761, by rfl⟩ : syracuseStep 1697015 = 2545523) B2545523
theorem B1271047 : Blo 1128631 1271047 := bstep (se 1 (by rfl) ⟨953285, by rfl⟩ : syracuseStep 1271047 = 1906571) B1906571
theorem B1697039 : Blo 1128631 1697039 := bstep (se 1 (by rfl) ⟨1272779, by rfl⟩ : syracuseStep 1697039 = 2545559) B2545559
theorem B13919521 : Blo 1128631 13919521 := bstep (se 2 (by rfl) ⟨5219820, by rfl⟩ : syracuseStep 13919521 = 10439641) B10439641
theorem B1697081 : Blo 1128631 1697081 := bstep (se 2 (by rfl) ⟨636405, by rfl⟩ : syracuseStep 1697081 = 1272811) B1272811
theorem B1697159 : Blo 1128631 1697159 := bstep (se 1 (by rfl) ⟨1272869, by rfl⟩ : syracuseStep 1697159 = 2545739) B2545739
theorem B1697195 : Blo 1128631 1697195 := bstep (se 1 (by rfl) ⟨1272896, by rfl⟩ : syracuseStep 1697195 = 2545793) B2545793
theorem B1271227 : Blo 1128631 1271227 := bstep (se 1 (by rfl) ⟨953420, by rfl⟩ : syracuseStep 1271227 = 1906841) B1906841
theorem B1697225 : Blo 1128631 1697225 := bstep (se 2 (by rfl) ⟨636459, by rfl⟩ : syracuseStep 1697225 = 1272919) B1272919
theorem B6448643 : Blo 1128631 6448643 := bstep (se 1 (by rfl) ⟨4836482, by rfl⟩ : syracuseStep 6448643 = 9672965) B9672965
theorem B6121003 : Blo 1128631 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B1697339 : Blo 1128631 1697339 := bstep (se 1 (by rfl) ⟨1273004, by rfl⟩ : syracuseStep 1697339 = 2546009) B2546009
theorem B10872397 : Blo 1128631 10872397 := bstep (se 3 (by rfl) ⟨2038574, by rfl⟩ : syracuseStep 10872397 = 4077149) B4077149
theorem B1697399 : Blo 1128631 1697399 := bstep (se 1 (by rfl) ⟨1273049, by rfl⟩ : syracuseStep 1697399 = 2546099) B2546099
theorem B1697423 : Blo 1128631 1697423 := bstep (se 1 (by rfl) ⟨1273067, by rfl⟩ : syracuseStep 1697423 = 2546135) B2546135
theorem B6121133 : Blo 1128631 6121133 := bstep (se 3 (by rfl) ⟨1147712, by rfl⟩ : syracuseStep 6121133 = 2295425) B2295425
theorem B1697465 : Blo 1128631 1697465 := bstep (se 2 (by rfl) ⟨636549, by rfl⟩ : syracuseStep 1697465 = 1273099) B1273099
theorem B1697543 : Blo 1128631 1697543 := bstep (se 1 (by rfl) ⟨1273157, by rfl⟩ : syracuseStep 1697543 = 2546315) B2546315
theorem B1697579 : Blo 1128631 1697579 := bstep (se 1 (by rfl) ⟨1273184, by rfl⟩ : syracuseStep 1697579 = 2546369) B2546369
theorem B1697609 : Blo 1128631 1697609 := bstep (se 2 (by rfl) ⟨636603, by rfl⟩ : syracuseStep 1697609 = 1273207) B1273207
theorem B1271695 : Blo 1128631 1271695 := bstep (se 1 (by rfl) ⟨953771, by rfl⟩ : syracuseStep 1271695 = 1907543) B1907543
theorem B2418617 : Blo 1128631 2418617 := bstep (se 2 (by rfl) ⟨906981, by rfl⟩ : syracuseStep 2418617 = 1813963) B1813963
theorem B1697723 : Blo 1128631 1697723 := bstep (se 1 (by rfl) ⟨1273292, by rfl⟩ : syracuseStep 1697723 = 2546585) B2546585
theorem B1697783 : Blo 1128631 1697783 := bstep (se 1 (by rfl) ⟨1273337, by rfl⟩ : syracuseStep 1697783 = 2546675) B2546675
theorem B1697807 : Blo 1128631 1697807 := bstep (se 1 (by rfl) ⟨1273355, by rfl⟩ : syracuseStep 1697807 = 2546711) B2546711
theorem B1697849 : Blo 1128631 1697849 := bstep (se 2 (by rfl) ⟨636693, by rfl⟩ : syracuseStep 1697849 = 1273387) B1273387
theorem B1697927 : Blo 1128631 1697927 := bstep (se 1 (by rfl) ⟨1273445, by rfl⟩ : syracuseStep 1697927 = 2546891) B2546891
theorem B1697963 : Blo 1128631 1697963 := bstep (se 1 (by rfl) ⟨1273472, by rfl⟩ : syracuseStep 1697963 = 2546945) B2546945
theorem B1697993 : Blo 1128631 1697993 := bstep (se 2 (by rfl) ⟨636747, by rfl⟩ : syracuseStep 1697993 = 1273495) B1273495
theorem B2713871 : Blo 1128631 2713871 := bstep (se 1 (by rfl) ⟨2035403, by rfl⟩ : syracuseStep 2713871 = 4070807) B4070807
theorem B2418959 : Blo 1128631 2418959 := bstep (se 1 (by rfl) ⟨1814219, by rfl⟩ : syracuseStep 2418959 = 3628439) B3628439
theorem B2418977 : Blo 1128631 2418977 := bstep (se 2 (by rfl) ⟨907116, by rfl⟩ : syracuseStep 2418977 = 1814233) B1814233
theorem B1698107 : Blo 1128631 1698107 := bstep (se 1 (by rfl) ⟨1273580, by rfl⟩ : syracuseStep 1698107 = 2547161) B2547161
theorem B1698167 : Blo 1128631 1698167 := bstep (se 1 (by rfl) ⟨1273625, by rfl⟩ : syracuseStep 1698167 = 2547251) B2547251
theorem B1272199 : Blo 1128631 1272199 := bstep (se 1 (by rfl) ⟨954149, by rfl⟩ : syracuseStep 1272199 = 1908299) B1908299
theorem B1698191 : Blo 1128631 1698191 := bstep (se 1 (by rfl) ⟨1273643, by rfl⟩ : syracuseStep 1698191 = 2547287) B2547287
theorem B1698233 : Blo 1128631 1698233 := bstep (se 2 (by rfl) ⟨636837, by rfl⟩ : syracuseStep 1698233 = 1273675) B1273675
theorem B1698311 : Blo 1128631 1698311 := bstep (se 1 (by rfl) ⟨1273733, by rfl⟩ : syracuseStep 1698311 = 2547467) B2547467
theorem B1698347 : Blo 1128631 1698347 := bstep (se 1 (by rfl) ⟨1273760, by rfl⟩ : syracuseStep 1698347 = 2547521) B2547521
theorem B1272379 : Blo 1128631 1272379 := bstep (se 1 (by rfl) ⟨954284, by rfl⟩ : syracuseStep 1272379 = 1908569) B1908569
theorem B1698377 : Blo 1128631 1698377 := bstep (se 2 (by rfl) ⟨636891, by rfl⟩ : syracuseStep 1698377 = 1273783) B1273783
theorem B13232717 : Blo 1128631 13232717 := bstep (se 3 (by rfl) ⟨2481134, by rfl⟩ : syracuseStep 13232717 = 4962269) B4962269
theorem B1698491 : Blo 1128631 1698491 := bstep (se 1 (by rfl) ⟨1273868, by rfl⟩ : syracuseStep 1698491 = 2547737) B2547737
theorem B1698551 : Blo 1128631 1698551 := bstep (se 1 (by rfl) ⟨1273913, by rfl⟩ : syracuseStep 1698551 = 2547827) B2547827
theorem B1698575 : Blo 1128631 1698575 := bstep (se 1 (by rfl) ⟨1273931, by rfl⟩ : syracuseStep 1698575 = 2547863) B2547863
theorem B2714401 : Blo 1128631 2714401 := bstep (se 2 (by rfl) ⟨1017900, by rfl⟩ : syracuseStep 2714401 = 2035801) B2035801
theorem B1698617 : Blo 1128631 1698617 := bstep (se 2 (by rfl) ⟨636981, by rfl⟩ : syracuseStep 1698617 = 1273963) B1273963
theorem B9300851 : Blo 1128631 9300851 := bstep (se 1 (by rfl) ⟨6975638, by rfl⟩ : syracuseStep 9300851 = 13951277) B13951277
theorem B1698695 : Blo 1128631 1698695 := bstep (se 1 (by rfl) ⟨1274021, by rfl⟩ : syracuseStep 1698695 = 2548043) B2548043
theorem B1698731 : Blo 1128631 1698731 := bstep (se 1 (by rfl) ⟨1274048, by rfl⟩ : syracuseStep 1698731 = 2548097) B2548097
theorem B1698761 : Blo 1128631 1698761 := bstep (se 2 (by rfl) ⟨637035, by rfl⟩ : syracuseStep 1698761 = 1274071) B1274071
theorem B5729291 : Blo 1128631 5729291 := bstep (se 1 (by rfl) ⟨4296968, by rfl⟩ : syracuseStep 5729291 = 8593937) B8593937
theorem B1272847 : Blo 1128631 1272847 := bstep (se 1 (by rfl) ⟨954635, by rfl⟩ : syracuseStep 1272847 = 1909271) B1909271
theorem B1698875 : Blo 1128631 1698875 := bstep (se 1 (by rfl) ⟨1274156, by rfl⟩ : syracuseStep 1698875 = 2548313) B2548313
theorem B1698935 : Blo 1128631 1698935 := bstep (se 1 (by rfl) ⟨1274201, by rfl⟩ : syracuseStep 1698935 = 2548403) B2548403
theorem B5729453 : Blo 1128631 5729453 := bstep (se 3 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 5729453 = 2148545) B2148545
theorem B10874243 : Blo 1128631 10874243 := bstep (se 1 (by rfl) ⟨8155682, by rfl⟩ : syracuseStep 10874243 = 16311365) B16311365
theorem B8154503 : Blo 1128631 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B2289043 : Blo 1128631 2289043 := bstep (se 1 (by rfl) ⟨1716782, by rfl⟩ : syracuseStep 2289043 = 3433565) B3433565
theorem B1273351 : Blo 1128631 1273351 := bstep (se 1 (by rfl) ⟨955013, by rfl⟩ : syracuseStep 1273351 = 1910027) B1910027
theorem B2649719 : Blo 1128631 2649719 := bstep (se 1 (by rfl) ⟨1987289, by rfl⟩ : syracuseStep 2649719 = 3974579) B3974579
theorem B1273531 : Blo 1128631 1273531 := bstep (se 1 (by rfl) ⟨955148, by rfl⟩ : syracuseStep 1273531 = 1910297) B1910297
theorem B4288403 : Blo 1128631 4288403 := bstep (se 1 (by rfl) ⟨3216302, by rfl⟩ : syracuseStep 4288403 = 6432605) B6432605
theorem B14479307 : Blo 1128631 14479307 := bstep (se 1 (by rfl) ⟨10859480, by rfl⟩ : syracuseStep 14479307 = 21718961) B21718961
theorem B24473623 : Blo 1128631 24473623 := bstep (se 1 (by rfl) ⟨18355217, by rfl⟩ : syracuseStep 24473623 = 36710435) B36710435
theorem B1273999 : Blo 1128631 1273999 := bstep (se 1 (by rfl) ⟨955499, by rfl⟩ : syracuseStep 1273999 = 1910999) B1910999
theorem B2715947 : Blo 1128631 2715947 := bstep (se 1 (by rfl) ⟨2036960, by rfl⟩ : syracuseStep 2715947 = 4073921) B4073921
theorem B1208839 : Blo 1128631 1208839 := bstep (se 1 (by rfl) ⟨906629, by rfl⟩ : syracuseStep 1208839 = 1813259) B1813259
theorem B2716247 : Blo 1128631 2716247 := bstep (se 1 (by rfl) ⟨2037185, by rfl⟩ : syracuseStep 2716247 = 4074371) B4074371
theorem B4584055 : Blo 1128631 4584055 := bstep (se 1 (by rfl) ⟨3438041, by rfl⟩ : syracuseStep 4584055 = 6876083) B6876083
theorem B1307323 : Blo 1128631 1307323 := bstep (se 1 (by rfl) ⟨980492, by rfl⟩ : syracuseStep 1307323 = 1960985) B1960985
theorem B5731073 : Blo 1128631 5731073 := bstep (se 2 (by rfl) ⟨2149152, by rfl⟩ : syracuseStep 5731073 = 4298305) B4298305
theorem B5731883 : Blo 1128631 5731883 := bstep (se 1 (by rfl) ⟨4298912, by rfl⟩ : syracuseStep 5731883 = 8597825) B8597825
theorem B24475205 : Blo 1128631 24475205 := bstep (se 4 (by rfl) ⟨2294550, by rfl⟩ : syracuseStep 24475205 = 4589101) B4589101
theorem B2750267 : Blo 1128631 2750267 := bstep (se 1 (by rfl) ⟨2062700, by rfl⟩ : syracuseStep 2750267 = 4125401) B4125401
theorem B2717707 : Blo 1128631 2717707 := bstep (se 1 (by rfl) ⟨2038280, by rfl⟩ : syracuseStep 2717707 = 4076561) B4076561
theorem B3438625 : Blo 1128631 3438625 := bstep (se 2 (by rfl) ⟨1289484, by rfl⟩ : syracuseStep 3438625 = 2578969) B2578969
theorem B4291001 : Blo 1128631 4291001 := bstep (se 2 (by rfl) ⟨1609125, by rfl⟩ : syracuseStep 4291001 = 3218251) B3218251
theorem B2718323 : Blo 1128631 2718323 := bstep (se 1 (by rfl) ⟨2038742, by rfl⟩ : syracuseStep 2718323 = 4077485) B4077485
theorem B1833673 : Blo 1128631 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B8157989 : Blo 1128631 8157989 := bstep (se 4 (by rfl) ⟨764811, by rfl⟩ : syracuseStep 8157989 = 1529623) B1529623
theorem B5733179 : Blo 1128631 5733179 := bstep (se 1 (by rfl) ⟨4299884, by rfl⟩ : syracuseStep 5733179 = 8599769) B8599769
theorem B5733341 : Blo 1128631 5733341 := bstep (se 3 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 5733341 = 2150003) B2150003
theorem B7339031 : Blo 1128631 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B5733665 : Blo 1128631 5733665 := bstep (se 2 (by rfl) ⟨2150124, by rfl⟩ : syracuseStep 5733665 = 4300249) B4300249
theorem B1375547 : Blo 1128631 1375547 := bstep (se 1 (by rfl) ⟨1031660, by rfl⟩ : syracuseStep 1375547 = 2063321) B2063321
theorem B2719091 : Blo 1128631 2719091 := bstep (se 1 (by rfl) ⟨2039318, by rfl⟩ : syracuseStep 2719091 = 4078637) B4078637
theorem B4291987 : Blo 1128631 4291987 := bstep (se 1 (by rfl) ⟨3218990, by rfl⟩ : syracuseStep 4291987 = 6437981) B6437981
theorem B11599325 : Blo 1128631 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B8158913 : Blo 1128631 8158913 := bstep (se 2 (by rfl) ⟨3059592, by rfl⟩ : syracuseStep 8158913 = 6119185) B6119185
theorem B2064403 : Blo 1128631 2064403 := bstep (se 1 (by rfl) ⟨1548302, by rfl⟩ : syracuseStep 2064403 = 3096605) B3096605
theorem B44597515 : Blo 1128631 44597515 := bstep (se 1 (by rfl) ⟨33448136, by rfl⟩ : syracuseStep 44597515 = 66896273) B66896273
theorem B14483771 : Blo 1128631 14483771 := bstep (se 1 (by rfl) ⟨10862828, by rfl⟩ : syracuseStep 14483771 = 21725657) B21725657
theorem B13730123 : Blo 1128631 13730123 := bstep (se 1 (by rfl) ⟨10297592, by rfl⟩ : syracuseStep 13730123 = 20595185) B20595185
theorem B8585675 : Blo 1128631 8585675 := bstep (se 1 (by rfl) ⟨6439256, by rfl⟩ : syracuseStep 8585675 = 12878513) B12878513
theorem B8258071 : Blo 1128631 8258071 := bstep (se 1 (by rfl) ⟨6193553, by rfl⟩ : syracuseStep 8258071 = 12387107) B12387107
theorem B4719455 : Blo 1128631 4719455 := bstep (se 1 (by rfl) ⟨3539591, by rfl⟩ : syracuseStep 4719455 = 7079183) B7079183
theorem B9667633 : Blo 1128631 9667633 := bstep (se 2 (by rfl) ⟨3625362, by rfl⟩ : syracuseStep 9667633 = 7250725) B7250725
theorem B16320365 : Blo 1128631 16320365 := bstep (se 3 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 16320365 = 6120137) B6120137
theorem B8161337 : Blo 1128631 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B4294903 : Blo 1128631 4294903 := bstep (se 1 (by rfl) ⟨3221177, by rfl⟩ : syracuseStep 4294903 = 6442355) B6442355
theorem B9668969 : Blo 1128631 9668969 := bstep (se 2 (by rfl) ⟨3625863, by rfl⟩ : syracuseStep 9668969 = 7251727) B7251727
theorem B4295177 : Blo 1128631 4295177 := bstep (se 2 (by rfl) ⟨1610691, by rfl⟩ : syracuseStep 4295177 = 3221383) B3221383
theorem B4295207 : Blo 1128631 4295207 := bstep (se 1 (by rfl) ⟨3221405, by rfl⟩ : syracuseStep 4295207 = 6442811) B6442811
theorem B7244423 : Blo 1128631 7244423 := bstep (se 1 (by rfl) ⟨5433317, by rfl⟩ : syracuseStep 7244423 = 10866635) B10866635
theorem B8588105 : Blo 1128631 8588105 := bstep (se 2 (by rfl) ⟨3220539, by rfl⟩ : syracuseStep 8588105 = 6441079) B6441079
theorem B12389213 : Blo 1128631 12389213 := bstep (se 3 (by rfl) ⟨2322977, by rfl⟩ : syracuseStep 12389213 = 4645955) B4645955
theorem B3214343 : Blo 1128631 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B4295875 : Blo 1128631 4295875 := bstep (se 1 (by rfl) ⟨3221906, by rfl⟩ : syracuseStep 4295875 = 6443813) B6443813
theorem B4296179 : Blo 1128631 4296179 := bstep (se 1 (by rfl) ⟨3222134, by rfl⟩ : syracuseStep 4296179 = 6444269) B6444269
theorem B4591403 : Blo 1128631 4591403 := bstep (se 1 (by rfl) ⟨3443552, by rfl⟩ : syracuseStep 4591403 = 6887105) B6887105
theorem B4296635 : Blo 1128631 4296635 := bstep (se 1 (by rfl) ⟨3222476, by rfl⟩ : syracuseStep 4296635 = 6444953) B6444953
theorem B1904647 : Blo 1128631 1904647 := bstep (se 1 (by rfl) ⟨1428485, by rfl⟩ : syracuseStep 1904647 = 2856971) B2856971
theorem B3969181 : Blo 1128631 3969181 := bstep (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) B1488443
theorem B1905079 : Blo 1128631 1905079 := bstep (se 1 (by rfl) ⟨1428809, by rfl⟩ : syracuseStep 1905079 = 2857619) B2857619
theorem B1905275 : Blo 1128631 1905275 := bstep (se 1 (by rfl) ⟨1428956, by rfl⟩ : syracuseStep 1905275 = 2857913) B2857913
theorem B1905673 : Blo 1128631 1905673 := bstep (se 2 (by rfl) ⟨714627, by rfl⟩ : syracuseStep 1905673 = 1429255) B1429255
theorem B1905835 : Blo 1128631 1905835 := bstep (se 1 (by rfl) ⟨1429376, by rfl⟩ : syracuseStep 1905835 = 2858753) B2858753
theorem B1906139 : Blo 1128631 1906139 := bstep (se 1 (by rfl) ⟨1429604, by rfl⟩ : syracuseStep 1906139 = 2859209) B2859209
theorem B1906375 : Blo 1128631 1906375 := bstep (se 1 (by rfl) ⟨1429781, by rfl⟩ : syracuseStep 1906375 = 2859563) B2859563
theorem B6428483 : Blo 1128631 6428483 := bstep (se 1 (by rfl) ⟨4821362, by rfl⟩ : syracuseStep 6428483 = 9642725) B9642725
theorem B1906537 : Blo 1128631 1906537 := bstep (se 2 (by rfl) ⟨714951, by rfl⟩ : syracuseStep 1906537 = 1429903) B1429903
theorem B3217259 : Blo 1128631 3217259 := bstep (se 1 (by rfl) ⟨2412944, by rfl⟩ : syracuseStep 3217259 = 4825889) B4825889
theorem B4069307 : Blo 1128631 4069307 := bstep (se 1 (by rfl) ⟨3051980, by rfl⟩ : syracuseStep 4069307 = 6103961) B6103961
theorem B1611785 : Blo 1128631 1611785 := bstep (se 2 (by rfl) ⟨604419, by rfl⟩ : syracuseStep 1611785 = 1208839) B1208839
theorem B4823155 : Blo 1128631 4823155 := bstep (se 1 (by rfl) ⟨3617366, by rfl⟩ : syracuseStep 4823155 = 7234733) B7234733
theorem B4299095 : Blo 1128631 4299095 := bstep (se 1 (by rfl) ⟨3224321, by rfl⟩ : syracuseStep 4299095 = 6448643) B6448643
theorem B4069757 : Blo 1128631 4069757 := bstep (se 3 (by rfl) ⟨763079, by rfl⟩ : syracuseStep 4069757 = 1526159) B1526159
theorem B1907131 : Blo 1128631 1907131 := bstep (se 1 (by rfl) ⟨1430348, by rfl⟩ : syracuseStep 1907131 = 2860697) B2860697
theorem B1907239 : Blo 1128631 1907239 := bstep (se 1 (by rfl) ⟨1430429, by rfl⟩ : syracuseStep 1907239 = 2860859) B2860859
theorem B1809145 : Blo 1128631 1809145 := bstep (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) B1356859
theorem B2857801 : Blo 1128631 2857801 := bstep (se 2 (by rfl) ⟨1071675, by rfl⟩ : syracuseStep 2857801 = 2143351) B2143351
theorem B1612639 : Blo 1128631 1612639 := bstep (se 1 (by rfl) ⟨1209479, by rfl⟩ : syracuseStep 1612639 = 2418959) B2418959
theorem B6101867 : Blo 1128631 6101867 := bstep (se 1 (by rfl) ⟨4576400, by rfl⟩ : syracuseStep 6101867 = 9152801) B9152801
theorem B1907563 : Blo 1128631 1907563 := bstep (se 1 (by rfl) ⟨1430672, by rfl⟩ : syracuseStep 1907563 = 2861345) B2861345
theorem B1612651 : Blo 1128631 1612651 := bstep (se 1 (by rfl) ⟨1209488, by rfl⟩ : syracuseStep 1612651 = 2418977) B2418977
theorem B8821811 : Blo 1128631 8821811 := bstep (se 1 (by rfl) ⟨6616358, by rfl⟩ : syracuseStep 8821811 = 13232717) B13232717
theorem B6200567 : Blo 1128631 6200567 := bstep (se 1 (by rfl) ⟨4650425, by rfl⟩ : syracuseStep 6200567 = 9300851) B9300851
theorem B7249495 : Blo 1128631 7249495 := bstep (se 1 (by rfl) ⟨5437121, by rfl⟩ : syracuseStep 7249495 = 10874243) B10874243
theorem B6528761 : Blo 1128631 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B1908623 : Blo 1128631 1908623 := bstep (se 1 (by rfl) ⟨1431467, by rfl⟩ : syracuseStep 1908623 = 2862935) B2862935
theorem B2858935 : Blo 1128631 2858935 := bstep (se 1 (by rfl) ⟨2144201, by rfl⟩ : syracuseStep 2858935 = 4288403) B4288403
theorem B6103097 : Blo 1128631 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B1908859 : Blo 1128631 1908859 := bstep (se 1 (by rfl) ⟨1431644, by rfl⟩ : syracuseStep 1908859 = 2863289) B2863289
theorem B1810631 : Blo 1128631 1810631 := bstep (se 1 (by rfl) ⟨1357973, by rfl⟩ : syracuseStep 1810631 = 2715947) B2715947
theorem B18358589 : Blo 1128631 18358589 := bstep (se 3 (by rfl) ⟨3442235, by rfl⟩ : syracuseStep 18358589 = 6884471) B6884471
theorem B1810831 : Blo 1128631 1810831 := bstep (se 1 (by rfl) ⟨1358123, by rfl⟩ : syracuseStep 1810831 = 2716247) B2716247
theorem B2040247 : Blo 1128631 2040247 := bstep (se 1 (by rfl) ⟨1530185, by rfl⟩ : syracuseStep 2040247 = 3060371) B3060371
theorem B3809915 : Blo 1128631 3809915 := bstep (se 1 (by rfl) ⟨2857436, by rfl⟩ : syracuseStep 3809915 = 5714873) B5714873
theorem B3810077 : Blo 1128631 3810077 := bstep (se 3 (by rfl) ⟨714389, by rfl⟩ : syracuseStep 3810077 = 1428779) B1428779
theorem B1909723 : Blo 1128631 1909723 := bstep (se 1 (by rfl) ⟨1432292, by rfl⟩ : syracuseStep 1909723 = 2864585) B2864585
theorem B12395521 : Blo 1128631 12395521 := bstep (se 2 (by rfl) ⟨4648320, by rfl⟩ : syracuseStep 12395521 = 9296641) B9296641
theorem B8135731 : Blo 1128631 8135731 := bstep (se 1 (by rfl) ⟨6101798, by rfl⟩ : syracuseStep 8135731 = 12203597) B12203597
theorem B2860393 : Blo 1128631 2860393 := bstep (se 2 (by rfl) ⟨1072647, by rfl⟩ : syracuseStep 2860393 = 2145295) B2145295
theorem B3810779 : Blo 1128631 3810779 := bstep (se 1 (by rfl) ⟨2858084, by rfl⟩ : syracuseStep 3810779 = 5716169) B5716169
theorem B1910351 : Blo 1128631 1910351 := bstep (se 1 (by rfl) ⟨1432763, by rfl⟩ : syracuseStep 1910351 = 2865527) B2865527
theorem B2860667 : Blo 1128631 2860667 := bstep (se 1 (by rfl) ⟨2145500, by rfl⟩ : syracuseStep 2860667 = 4291001) B4291001
theorem B1812215 : Blo 1128631 1812215 := bstep (se 1 (by rfl) ⟨1359161, by rfl⟩ : syracuseStep 1812215 = 2718323) B2718323
theorem B54929411 : Blo 1128631 54929411 := bstep (se 1 (by rfl) ⟨41197058, by rfl⟩ : syracuseStep 54929411 = 82394117) B82394117
theorem B4892687 : Blo 1128631 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B6432857 : Blo 1128631 6432857 := bstep (se 2 (by rfl) ⟨2412321, by rfl⟩ : syracuseStep 6432857 = 4824643) B4824643
theorem B3811481 : Blo 1128631 3811481 := bstep (se 2 (by rfl) ⟨1429305, by rfl⟩ : syracuseStep 3811481 = 2858611) B2858611
theorem B1812727 : Blo 1128631 1812727 := bstep (se 1 (by rfl) ⟨1359545, by rfl⟩ : syracuseStep 1812727 = 2719091) B2719091
theorem B1911215 : Blo 1128631 1911215 := bstep (se 1 (by rfl) ⟨1433411, by rfl⟩ : syracuseStep 1911215 = 2866823) B2866823
theorem B6433289 : Blo 1128631 6433289 := bstep (se 2 (by rfl) ⟨2412483, by rfl⟩ : syracuseStep 6433289 = 4824967) B4824967
theorem B13774103 : Blo 1128631 13774103 := bstep (se 1 (by rfl) ⟨10330577, by rfl⟩ : syracuseStep 13774103 = 20661155) B20661155
theorem B3812669 : Blo 1128631 3812669 := bstep (se 3 (by rfl) ⟨714875, by rfl⟩ : syracuseStep 3812669 = 1429751) B1429751
theorem B1813855 : Blo 1128631 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B2862479 : Blo 1128631 2862479 := bstep (se 1 (by rfl) ⟨2146859, by rfl⟩ : syracuseStep 2862479 = 4293719) B4293719
theorem B3616265 : Blo 1128631 3616265 := bstep (se 2 (by rfl) ⟨1356099, by rfl⟩ : syracuseStep 3616265 = 2712199) B2712199
theorem B6270587 : Blo 1128631 6270587 := bstep (se 1 (by rfl) ⟨4702940, by rfl⟩ : syracuseStep 6270587 = 9405881) B9405881
theorem B2862803 : Blo 1128631 2862803 := bstep (se 1 (by rfl) ⟨2147102, by rfl⟩ : syracuseStep 2862803 = 4294205) B4294205
theorem B6205177 : Blo 1128631 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B6434747 : Blo 1128631 6434747 := bstep (se 1 (by rfl) ⟨4826060, by rfl⟩ : syracuseStep 6434747 = 9652121) B9652121
theorem B4075535 : Blo 1128631 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B3813533 : Blo 1128631 3813533 := bstep (se 3 (by rfl) ⟨715037, by rfl⟩ : syracuseStep 3813533 = 1430075) B1430075
theorem B4829341 : Blo 1128631 4829341 := bstep (se 3 (by rfl) ⟨905501, by rfl⟩ : syracuseStep 4829341 = 1811003) B1811003
theorem B4468931 : Blo 1128631 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B3617111 : Blo 1128631 3617111 := bstep (se 1 (by rfl) ⟨2712833, by rfl⟩ : syracuseStep 3617111 = 5425667) B5425667
theorem B18559361 : Blo 1128631 18559361 := bstep (se 2 (by rfl) ⟨6959760, by rfl⟩ : syracuseStep 18559361 = 13919521) B13919521
theorem B2142683 : Blo 1128631 2142683 := bstep (se 1 (by rfl) ⟨1607012, by rfl⟩ : syracuseStep 2142683 = 3214025) B3214025
theorem B3617419 : Blo 1128631 3617419 := bstep (se 1 (by rfl) ⟨2713064, by rfl⟩ : syracuseStep 3617419 = 5426129) B5426129
theorem B3814073 : Blo 1128631 3814073 := bstep (se 2 (by rfl) ⟨1430277, by rfl⟩ : syracuseStep 3814073 = 2860555) B2860555
theorem B29012741 : Blo 1128631 29012741 := bstep (se 4 (by rfl) ⟨2719944, by rfl⟩ : syracuseStep 29012741 = 5439889) B5439889
theorem B14496529 : Blo 1128631 14496529 := bstep (se 2 (by rfl) ⟨5436198, by rfl⟩ : syracuseStep 14496529 = 10872397) B10872397
theorem B3814667 : Blo 1128631 3814667 := bstep (se 1 (by rfl) ⟨2861000, by rfl⟩ : syracuseStep 3814667 = 5722001) B5722001
theorem B3814937 : Blo 1128631 3814937 := bstep (se 2 (by rfl) ⟨1430601, by rfl⟩ : syracuseStep 3814937 = 2861203) B2861203
theorem B2865071 : Blo 1128631 2865071 := bstep (se 1 (by rfl) ⟨2148803, by rfl⟩ : syracuseStep 2865071 = 4297607) B4297607
theorem B2897977 : Blo 1128631 2897977 := bstep (se 2 (by rfl) ⟨1086741, by rfl⟩ : syracuseStep 2897977 = 2173483) B2173483
theorem B4831289 : Blo 1128631 4831289 := bstep (se 2 (by rfl) ⟨1811733, by rfl⟩ : syracuseStep 4831289 = 3623467) B3623467
theorem B3618931 : Blo 1128631 3618931 := bstep (se 1 (by rfl) ⟨2714198, by rfl⟩ : syracuseStep 3618931 = 5428397) B5428397
theorem B6436979 : Blo 1128631 6436979 := bstep (se 1 (by rfl) ⟨4827734, by rfl⟩ : syracuseStep 6436979 = 9655469) B9655469
theorem B1128647 : Blo 1128631 1128647 := bstep (se 1 (by rfl) ⟨846485, by rfl⟩ : syracuseStep 1128647 = 1692971) B1692971
theorem B1128667 : Blo 1128631 1128667 := bstep (se 1 (by rfl) ⟨846500, by rfl⟩ : syracuseStep 1128667 = 1693001) B1693001
theorem B1128743 : Blo 1128631 1128743 := bstep (se 1 (by rfl) ⟨846557, by rfl⟩ : syracuseStep 1128743 = 1693115) B1693115
theorem B1128783 : Blo 1128631 1128783 := bstep (se 1 (by rfl) ⟨846587, by rfl⟩ : syracuseStep 1128783 = 1693175) B1693175
theorem B1128799 : Blo 1128631 1128799 := bstep (se 1 (by rfl) ⟨846599, by rfl⟩ : syracuseStep 1128799 = 1693199) B1693199
theorem B1718633 : Blo 1128631 1718633 := bstep (se 2 (by rfl) ⟨644487, by rfl⟩ : syracuseStep 1718633 = 1288975) B1288975
theorem B1128827 : Blo 1128631 1128827 := bstep (se 1 (by rfl) ⟨846620, by rfl⟩ : syracuseStep 1128827 = 1693241) B1693241
theorem B3619201 : Blo 1128631 3619201 := bstep (se 2 (by rfl) ⟨1357200, by rfl⟩ : syracuseStep 3619201 = 2714401) B2714401
theorem B1128879 : Blo 1128631 1128879 := bstep (se 1 (by rfl) ⟨846659, by rfl⟩ : syracuseStep 1128879 = 1693319) B1693319
theorem B1128903 : Blo 1128631 1128903 := bstep (se 1 (by rfl) ⟨846677, by rfl⟩ : syracuseStep 1128903 = 1693355) B1693355
theorem B1128923 : Blo 1128631 1128923 := bstep (se 1 (by rfl) ⟨846692, by rfl⟩ : syracuseStep 1128923 = 1693385) B1693385
theorem B2865689 : Blo 1128631 2865689 := bstep (se 2 (by rfl) ⟨1074633, by rfl⟩ : syracuseStep 2865689 = 2149267) B2149267
theorem B1128999 : Blo 1128631 1128999 := bstep (se 1 (by rfl) ⟨846749, by rfl⟩ : syracuseStep 1128999 = 1693499) B1693499
theorem B3619367 : Blo 1128631 3619367 := bstep (se 1 (by rfl) ⟨2714525, by rfl⟩ : syracuseStep 3619367 = 5429051) B5429051
theorem B1129039 : Blo 1128631 1129039 := bstep (se 1 (by rfl) ⟨846779, by rfl⟩ : syracuseStep 1129039 = 1693559) B1693559
theorem B1129055 : Blo 1128631 1129055 := bstep (se 1 (by rfl) ⟨846791, by rfl⟩ : syracuseStep 1129055 = 1693583) B1693583
theorem B1129083 : Blo 1128631 1129083 := bstep (se 1 (by rfl) ⟨846812, by rfl⟩ : syracuseStep 1129083 = 1693625) B1693625
theorem B3816071 : Blo 1128631 3816071 := bstep (se 1 (by rfl) ⟨2862053, by rfl⟩ : syracuseStep 3816071 = 5724107) B5724107
theorem B1129135 : Blo 1128631 1129135 := bstep (se 1 (by rfl) ⟨846851, by rfl⟩ : syracuseStep 1129135 = 1693703) B1693703
theorem B3816125 : Blo 1128631 3816125 := bstep (se 3 (by rfl) ⟨715523, by rfl⟩ : syracuseStep 3816125 = 1431047) B1431047
theorem B1129159 : Blo 1128631 1129159 := bstep (se 1 (by rfl) ⟨846869, by rfl⟩ : syracuseStep 1129159 = 1693739) B1693739
theorem B1129179 : Blo 1128631 1129179 := bstep (se 1 (by rfl) ⟨846884, by rfl⟩ : syracuseStep 1129179 = 1693769) B1693769
theorem B1129255 : Blo 1128631 1129255 := bstep (se 1 (by rfl) ⟨846941, by rfl⟩ : syracuseStep 1129255 = 1693883) B1693883
theorem B1129295 : Blo 1128631 1129295 := bstep (se 1 (by rfl) ⟨846971, by rfl⟩ : syracuseStep 1129295 = 1693943) B1693943
theorem B1129311 : Blo 1128631 1129311 := bstep (se 1 (by rfl) ⟨846983, by rfl⟩ : syracuseStep 1129311 = 1693967) B1693967
theorem B3816287 : Blo 1128631 3816287 := bstep (se 1 (by rfl) ⟨2862215, by rfl⟩ : syracuseStep 3816287 = 5724431) B5724431
theorem B1129339 : Blo 1128631 1129339 := bstep (se 1 (by rfl) ⟨847004, by rfl⟩ : syracuseStep 1129339 = 1694009) B1694009
theorem B1129391 : Blo 1128631 1129391 := bstep (se 1 (by rfl) ⟨847043, by rfl⟩ : syracuseStep 1129391 = 1694087) B1694087
theorem B1129415 : Blo 1128631 1129415 := bstep (se 1 (by rfl) ⟨847061, by rfl⟩ : syracuseStep 1129415 = 1694123) B1694123
theorem B1129435 : Blo 1128631 1129435 := bstep (se 1 (by rfl) ⟨847076, by rfl⟩ : syracuseStep 1129435 = 1694153) B1694153
theorem B3816449 : Blo 1128631 3816449 := bstep (se 2 (by rfl) ⟨1431168, by rfl⟩ : syracuseStep 3816449 = 2862337) B2862337
theorem B1129511 : Blo 1128631 1129511 := bstep (se 1 (by rfl) ⟨847133, by rfl⟩ : syracuseStep 1129511 = 1694267) B1694267
theorem B4078649 : Blo 1128631 4078649 := bstep (se 2 (by rfl) ⟨1529493, by rfl⟩ : syracuseStep 4078649 = 3058987) B3058987
theorem B1129551 : Blo 1128631 1129551 := bstep (se 1 (by rfl) ⟨847163, by rfl⟩ : syracuseStep 1129551 = 1694327) B1694327
theorem B1129567 : Blo 1128631 1129567 := bstep (se 1 (by rfl) ⟨847175, by rfl⟩ : syracuseStep 1129567 = 1694351) B1694351
theorem B1129595 : Blo 1128631 1129595 := bstep (se 1 (by rfl) ⟨847196, by rfl⟩ : syracuseStep 1129595 = 1694393) B1694393
theorem B1129647 : Blo 1128631 1129647 := bstep (se 1 (by rfl) ⟨847235, by rfl⟩ : syracuseStep 1129647 = 1694471) B1694471
theorem B1129671 : Blo 1128631 1129671 := bstep (se 1 (by rfl) ⟨847253, by rfl⟩ : syracuseStep 1129671 = 1694507) B1694507
theorem B1129691 : Blo 1128631 1129691 := bstep (se 1 (by rfl) ⟨847268, by rfl⟩ : syracuseStep 1129691 = 1694537) B1694537
theorem B1129767 : Blo 1128631 1129767 := bstep (se 1 (by rfl) ⟨847325, by rfl⟩ : syracuseStep 1129767 = 1694651) B1694651
theorem B1129807 : Blo 1128631 1129807 := bstep (se 1 (by rfl) ⟨847355, by rfl⟩ : syracuseStep 1129807 = 1694711) B1694711
theorem B1129823 : Blo 1128631 1129823 := bstep (se 1 (by rfl) ⟨847367, by rfl⟩ : syracuseStep 1129823 = 1694735) B1694735
theorem B1129851 : Blo 1128631 1129851 := bstep (se 1 (by rfl) ⟨847388, by rfl⟩ : syracuseStep 1129851 = 1694777) B1694777
theorem B1129903 : Blo 1128631 1129903 := bstep (se 1 (by rfl) ⟨847427, by rfl⟩ : syracuseStep 1129903 = 1694855) B1694855
theorem B1129927 : Blo 1128631 1129927 := bstep (se 1 (by rfl) ⟨847445, by rfl⟩ : syracuseStep 1129927 = 1694891) B1694891
theorem B1129947 : Blo 1128631 1129947 := bstep (se 1 (by rfl) ⟨847460, by rfl⟩ : syracuseStep 1129947 = 1694921) B1694921
theorem B1130023 : Blo 1128631 1130023 := bstep (se 1 (by rfl) ⟨847517, by rfl⟩ : syracuseStep 1130023 = 1695035) B1695035
theorem B48971303 : Blo 1128631 48971303 := bstep (se 1 (by rfl) ⟨36728477, by rfl⟩ : syracuseStep 48971303 = 73456955) B73456955
theorem B1130063 : Blo 1128631 1130063 := bstep (se 1 (by rfl) ⟨847547, by rfl⟩ : syracuseStep 1130063 = 1695095) B1695095
theorem B1130079 : Blo 1128631 1130079 := bstep (se 1 (by rfl) ⟨847559, by rfl⟩ : syracuseStep 1130079 = 1695119) B1695119
theorem B5717627 : Blo 1128631 5717627 := bstep (se 1 (by rfl) ⟨4288220, by rfl⟩ : syracuseStep 5717627 = 8576441) B8576441
theorem B1130107 : Blo 1128631 1130107 := bstep (se 1 (by rfl) ⟨847580, by rfl⟩ : syracuseStep 1130107 = 1695161) B1695161
theorem B1130159 : Blo 1128631 1130159 := bstep (se 1 (by rfl) ⟨847619, by rfl⟩ : syracuseStep 1130159 = 1695239) B1695239
theorem B8142535 : Blo 1128631 8142535 := bstep (se 1 (by rfl) ⟨6106901, by rfl⟩ : syracuseStep 8142535 = 12213803) B12213803
theorem B1130183 : Blo 1128631 1130183 := bstep (se 1 (by rfl) ⟨847637, by rfl⟩ : syracuseStep 1130183 = 1695275) B1695275
theorem B1130203 : Blo 1128631 1130203 := bstep (se 1 (by rfl) ⟨847652, by rfl⟩ : syracuseStep 1130203 = 1695305) B1695305
theorem B1130279 : Blo 1128631 1130279 := bstep (se 1 (by rfl) ⟨847709, by rfl⟩ : syracuseStep 1130279 = 1695419) B1695419
theorem B3817259 : Blo 1128631 3817259 := bstep (se 1 (by rfl) ⟨2862944, by rfl⟩ : syracuseStep 3817259 = 5725889) B5725889
theorem B1130319 : Blo 1128631 1130319 := bstep (se 1 (by rfl) ⟨847739, by rfl⟩ : syracuseStep 1130319 = 1695479) B1695479
theorem B1130335 : Blo 1128631 1130335 := bstep (se 1 (by rfl) ⟨847751, by rfl⟩ : syracuseStep 1130335 = 1695503) B1695503
theorem B1130363 : Blo 1128631 1130363 := bstep (se 1 (by rfl) ⟨847772, by rfl⟩ : syracuseStep 1130363 = 1695545) B1695545
theorem B2539439 : Blo 1128631 2539439 := bstep (se 1 (by rfl) ⟨1904579, by rfl⟩ : syracuseStep 2539439 = 3809159) B3809159
theorem B1130415 : Blo 1128631 1130415 := bstep (se 1 (by rfl) ⟨847811, by rfl⟩ : syracuseStep 1130415 = 1695623) B1695623
theorem B1130439 : Blo 1128631 1130439 := bstep (se 1 (by rfl) ⟨847829, by rfl⟩ : syracuseStep 1130439 = 1695659) B1695659
theorem B1130459 : Blo 1128631 1130459 := bstep (se 1 (by rfl) ⟨847844, by rfl⟩ : syracuseStep 1130459 = 1695689) B1695689
theorem B2146267 : Blo 1128631 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B2146313 : Blo 1128631 2146313 := bstep (se 2 (by rfl) ⟨804867, by rfl⟩ : syracuseStep 2146313 = 1609735) B1609735
theorem B1130535 : Blo 1128631 1130535 := bstep (se 1 (by rfl) ⟨847901, by rfl⟩ : syracuseStep 1130535 = 1695803) B1695803
theorem B3817529 : Blo 1128631 3817529 := bstep (se 2 (by rfl) ⟨1431573, by rfl⟩ : syracuseStep 3817529 = 2863147) B2863147
theorem B1130575 : Blo 1128631 1130575 := bstep (se 1 (by rfl) ⟨847931, by rfl⟩ : syracuseStep 1130575 = 1695863) B1695863
theorem B1130591 : Blo 1128631 1130591 := bstep (se 1 (by rfl) ⟨847943, by rfl⟩ : syracuseStep 1130591 = 1695887) B1695887
theorem B1130619 : Blo 1128631 1130619 := bstep (se 1 (by rfl) ⟨847964, by rfl⟩ : syracuseStep 1130619 = 1695929) B1695929
theorem B2539691 : Blo 1128631 2539691 := bstep (se 1 (by rfl) ⟨1904768, by rfl⟩ : syracuseStep 2539691 = 3809537) B3809537
theorem B1130671 : Blo 1128631 1130671 := bstep (se 1 (by rfl) ⟨848003, by rfl⟩ : syracuseStep 1130671 = 1696007) B1696007
theorem B1130695 : Blo 1128631 1130695 := bstep (se 1 (by rfl) ⟨848021, by rfl⟩ : syracuseStep 1130695 = 1696043) B1696043
theorem B1130715 : Blo 1128631 1130715 := bstep (se 1 (by rfl) ⟨848036, by rfl⟩ : syracuseStep 1130715 = 1696073) B1696073
theorem B1130791 : Blo 1128631 1130791 := bstep (se 1 (by rfl) ⟨848093, by rfl⟩ : syracuseStep 1130791 = 1696187) B1696187
theorem B3719485 : Blo 1128631 3719485 := bstep (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) B1394807
theorem B1130831 : Blo 1128631 1130831 := bstep (se 1 (by rfl) ⟨848123, by rfl⟩ : syracuseStep 1130831 = 1696247) B1696247
theorem B2146655 : Blo 1128631 2146655 := bstep (se 1 (by rfl) ⟨1609991, by rfl⟩ : syracuseStep 2146655 = 3219983) B3219983
theorem B1130847 : Blo 1128631 1130847 := bstep (se 1 (by rfl) ⟨848135, by rfl⟩ : syracuseStep 1130847 = 1696271) B1696271
theorem B1130875 : Blo 1128631 1130875 := bstep (se 1 (by rfl) ⟨848156, by rfl⟩ : syracuseStep 1130875 = 1696313) B1696313
theorem B3817853 : Blo 1128631 3817853 := bstep (se 3 (by rfl) ⟨715847, by rfl⟩ : syracuseStep 3817853 = 1431695) B1431695
theorem B4833665 : Blo 1128631 4833665 := bstep (se 2 (by rfl) ⟨1812624, by rfl⟩ : syracuseStep 4833665 = 3625249) B3625249
theorem B1130927 : Blo 1128631 1130927 := bstep (se 1 (by rfl) ⟨848195, by rfl⟩ : syracuseStep 1130927 = 1696391) B1696391
theorem B1130951 : Blo 1128631 1130951 := bstep (se 1 (by rfl) ⟨848213, by rfl⟩ : syracuseStep 1130951 = 1696427) B1696427
theorem B1130971 : Blo 1128631 1130971 := bstep (se 1 (by rfl) ⟨848228, by rfl⟩ : syracuseStep 1130971 = 1696457) B1696457
theorem B1131047 : Blo 1128631 1131047 := bstep (se 1 (by rfl) ⟨848285, by rfl⟩ : syracuseStep 1131047 = 1696571) B1696571
theorem B1131087 : Blo 1128631 1131087 := bstep (se 1 (by rfl) ⟨848315, by rfl⟩ : syracuseStep 1131087 = 1696631) B1696631
theorem B1131103 : Blo 1128631 1131103 := bstep (se 1 (by rfl) ⟨848327, by rfl⟩ : syracuseStep 1131103 = 1696655) B1696655
theorem B1131131 : Blo 1128631 1131131 := bstep (se 1 (by rfl) ⟨848348, by rfl⟩ : syracuseStep 1131131 = 1696697) B1696697
theorem B3818123 : Blo 1128631 3818123 := bstep (se 1 (by rfl) ⟨2863592, by rfl⟩ : syracuseStep 3818123 = 5727185) B5727185
theorem B1131183 : Blo 1128631 1131183 := bstep (se 1 (by rfl) ⟨848387, by rfl⟩ : syracuseStep 1131183 = 1696775) B1696775
theorem B2540231 : Blo 1128631 2540231 := bstep (se 1 (by rfl) ⟨1905173, by rfl⟩ : syracuseStep 2540231 = 3810347) B3810347
theorem B1131207 : Blo 1128631 1131207 := bstep (se 1 (by rfl) ⟨848405, by rfl⟩ : syracuseStep 1131207 = 1696811) B1696811
theorem B1131227 : Blo 1128631 1131227 := bstep (se 1 (by rfl) ⟨848420, by rfl⟩ : syracuseStep 1131227 = 1696841) B1696841
theorem B1131303 : Blo 1128631 1131303 := bstep (se 1 (by rfl) ⟨848477, by rfl⟩ : syracuseStep 1131303 = 1696955) B1696955
theorem B6112073 : Blo 1128631 6112073 := bstep (se 2 (by rfl) ⟨2292027, by rfl⟩ : syracuseStep 6112073 = 4584055) B4584055
theorem B1131343 : Blo 1128631 1131343 := bstep (se 1 (by rfl) ⟨848507, by rfl⟩ : syracuseStep 1131343 = 1697015) B1697015
theorem B1131359 : Blo 1128631 1131359 := bstep (se 1 (by rfl) ⟨848519, by rfl⟩ : syracuseStep 1131359 = 1697039) B1697039
theorem B1131387 : Blo 1128631 1131387 := bstep (se 1 (by rfl) ⟨848540, by rfl⟩ : syracuseStep 1131387 = 1697081) B1697081
theorem B1131439 : Blo 1128631 1131439 := bstep (se 1 (by rfl) ⟨848579, by rfl⟩ : syracuseStep 1131439 = 1697159) B1697159
theorem B1131463 : Blo 1128631 1131463 := bstep (se 1 (by rfl) ⟨848597, by rfl⟩ : syracuseStep 1131463 = 1697195) B1697195
theorem B1131483 : Blo 1128631 1131483 := bstep (se 1 (by rfl) ⟨848612, by rfl⟩ : syracuseStep 1131483 = 1697225) B1697225
theorem B1131559 : Blo 1128631 1131559 := bstep (se 1 (by rfl) ⟨848669, by rfl⟩ : syracuseStep 1131559 = 1697339) B1697339
theorem B1131599 : Blo 1128631 1131599 := bstep (se 1 (by rfl) ⟨848699, by rfl⟩ : syracuseStep 1131599 = 1697399) B1697399
theorem B1131615 : Blo 1128631 1131615 := bstep (se 1 (by rfl) ⟨848711, by rfl⟩ : syracuseStep 1131615 = 1697423) B1697423
theorem B4080755 : Blo 1128631 4080755 := bstep (se 1 (by rfl) ⟨3060566, by rfl⟩ : syracuseStep 4080755 = 6121133) B6121133
theorem B1131643 : Blo 1128631 1131643 := bstep (se 1 (by rfl) ⟨848732, by rfl⟩ : syracuseStep 1131643 = 1697465) B1697465
theorem B1131695 : Blo 1128631 1131695 := bstep (se 1 (by rfl) ⟨848771, by rfl⟩ : syracuseStep 1131695 = 1697543) B1697543
theorem B1131719 : Blo 1128631 1131719 := bstep (se 1 (by rfl) ⟨848789, by rfl⟩ : syracuseStep 1131719 = 1697579) B1697579
theorem B1131739 : Blo 1128631 1131739 := bstep (se 1 (by rfl) ⟨848804, by rfl⟩ : syracuseStep 1131739 = 1697609) B1697609
theorem B1131815 : Blo 1128631 1131815 := bstep (se 1 (by rfl) ⟨848861, by rfl⟩ : syracuseStep 1131815 = 1697723) B1697723
theorem B1131855 : Blo 1128631 1131855 := bstep (se 1 (by rfl) ⟨848891, by rfl⟩ : syracuseStep 1131855 = 1697783) B1697783
theorem B1131871 : Blo 1128631 1131871 := bstep (se 1 (by rfl) ⟨848903, by rfl⟩ : syracuseStep 1131871 = 1697807) B1697807
theorem B1131899 : Blo 1128631 1131899 := bstep (se 1 (by rfl) ⟨848924, by rfl⟩ : syracuseStep 1131899 = 1697849) B1697849
theorem B1131951 : Blo 1128631 1131951 := bstep (se 1 (by rfl) ⟨848963, by rfl⟩ : syracuseStep 1131951 = 1697927) B1697927
theorem B2147771 : Blo 1128631 2147771 := bstep (se 1 (by rfl) ⟨1610828, by rfl⟩ : syracuseStep 2147771 = 3221657) B3221657
theorem B1131975 : Blo 1128631 1131975 := bstep (se 1 (by rfl) ⟨848981, by rfl⟩ : syracuseStep 1131975 = 1697963) B1697963
theorem B1131995 : Blo 1128631 1131995 := bstep (se 1 (by rfl) ⟨848996, by rfl⟩ : syracuseStep 1131995 = 1697993) B1697993
theorem B3819041 : Blo 1128631 3819041 := bstep (se 2 (by rfl) ⟨1432140, by rfl⟩ : syracuseStep 3819041 = 2864281) B2864281
theorem B2541095 : Blo 1128631 2541095 := bstep (se 1 (by rfl) ⟨1905821, by rfl⟩ : syracuseStep 2541095 = 3811643) B3811643
theorem B1132071 : Blo 1128631 1132071 := bstep (se 1 (by rfl) ⟨849053, by rfl⟩ : syracuseStep 1132071 = 1698107) B1698107
theorem B1132111 : Blo 1128631 1132111 := bstep (se 1 (by rfl) ⟨849083, by rfl⟩ : syracuseStep 1132111 = 1698167) B1698167
theorem B1132127 : Blo 1128631 1132127 := bstep (se 1 (by rfl) ⟨849095, by rfl⟩ : syracuseStep 1132127 = 1698191) B1698191
theorem B1132155 : Blo 1128631 1132155 := bstep (se 1 (by rfl) ⟨849116, by rfl⟩ : syracuseStep 1132155 = 1698233) B1698233
theorem B1132207 : Blo 1128631 1132207 := bstep (se 1 (by rfl) ⟨849155, by rfl⟩ : syracuseStep 1132207 = 1698311) B1698311
theorem B1132231 : Blo 1128631 1132231 := bstep (se 1 (by rfl) ⟨849173, by rfl⟩ : syracuseStep 1132231 = 1698347) B1698347
theorem B1132251 : Blo 1128631 1132251 := bstep (se 1 (by rfl) ⟨849188, by rfl⟩ : syracuseStep 1132251 = 1698377) B1698377
theorem B3819257 : Blo 1128631 3819257 := bstep (se 2 (by rfl) ⟨1432221, by rfl⟩ : syracuseStep 3819257 = 2864443) B2864443
theorem B1132327 : Blo 1128631 1132327 := bstep (se 1 (by rfl) ⟨849245, by rfl⟩ : syracuseStep 1132327 = 1698491) B1698491
theorem B1132367 : Blo 1128631 1132367 := bstep (se 1 (by rfl) ⟨849275, by rfl⟩ : syracuseStep 1132367 = 1698551) B1698551
theorem B1132383 : Blo 1128631 1132383 := bstep (se 1 (by rfl) ⟨849287, by rfl⟩ : syracuseStep 1132383 = 1698575) B1698575
theorem B2541419 : Blo 1128631 2541419 := bstep (se 1 (by rfl) ⟨1906064, by rfl⟩ : syracuseStep 2541419 = 3812129) B3812129
theorem B1132411 : Blo 1128631 1132411 := bstep (se 1 (by rfl) ⟨849308, by rfl⟩ : syracuseStep 1132411 = 1698617) B1698617
theorem B2541473 : Blo 1128631 2541473 := bstep (se 2 (by rfl) ⟨953052, by rfl⟩ : syracuseStep 2541473 = 1906105) B1906105
theorem B2148257 : Blo 1128631 2148257 := bstep (se 2 (by rfl) ⟨805596, by rfl⟩ : syracuseStep 2148257 = 1611193) B1611193
theorem B1132463 : Blo 1128631 1132463 := bstep (se 1 (by rfl) ⟨849347, by rfl⟩ : syracuseStep 1132463 = 1698695) B1698695
theorem B6440897 : Blo 1128631 6440897 := bstep (se 2 (by rfl) ⟨2415336, by rfl⟩ : syracuseStep 6440897 = 4830673) B4830673
theorem B1132487 : Blo 1128631 1132487 := bstep (se 1 (by rfl) ⟨849365, by rfl⟩ : syracuseStep 1132487 = 1698731) B1698731
theorem B1132507 : Blo 1128631 1132507 := bstep (se 1 (by rfl) ⟨849380, by rfl⟩ : syracuseStep 1132507 = 1698761) B1698761
theorem B3819527 : Blo 1128631 3819527 := bstep (se 1 (by rfl) ⟨2864645, by rfl⟩ : syracuseStep 3819527 = 5729291) B5729291
theorem B13060133 : Blo 1128631 13060133 := bstep (se 4 (by rfl) ⟨1224387, by rfl⟩ : syracuseStep 13060133 = 2448775) B2448775
theorem B1132583 : Blo 1128631 1132583 := bstep (se 1 (by rfl) ⟨849437, by rfl⟩ : syracuseStep 1132583 = 1698875) B1698875
theorem B2410553 : Blo 1128631 2410553 := bstep (se 2 (by rfl) ⟨903957, by rfl⟩ : syracuseStep 2410553 = 1807915) B1807915
theorem B1132623 : Blo 1128631 1132623 := bstep (se 1 (by rfl) ⟨849467, by rfl⟩ : syracuseStep 1132623 = 1698935) B1698935
theorem B12208229 : Blo 1128631 12208229 := bstep (se 4 (by rfl) ⟨1144521, by rfl⟩ : syracuseStep 12208229 = 2289043) B2289043
theorem B3819635 : Blo 1128631 3819635 := bstep (se 1 (by rfl) ⟨2864726, by rfl⟩ : syracuseStep 3819635 = 5729453) B5729453
theorem B19581061 : Blo 1128631 19581061 := bstep (se 4 (by rfl) ⟨1835724, by rfl⟩ : syracuseStep 19581061 = 3671449) B3671449
theorem B2541815 : Blo 1128631 2541815 := bstep (se 1 (by rfl) ⟨1906361, by rfl⟩ : syracuseStep 2541815 = 3812723) B3812723
theorem B2148599 : Blo 1128631 2148599 := bstep (se 1 (by rfl) ⟨1611449, by rfl⟩ : syracuseStep 2148599 = 3222899) B3222899
theorem B5720381 : Blo 1128631 5720381 := bstep (se 3 (by rfl) ⟨1072571, by rfl⟩ : syracuseStep 5720381 = 2145143) B2145143
theorem B3819905 : Blo 1128631 3819905 := bstep (se 2 (by rfl) ⟨1432464, by rfl⟩ : syracuseStep 3819905 = 2864929) B2864929
theorem B8145305 : Blo 1128631 8145305 := bstep (se 2 (by rfl) ⟨3054489, by rfl⟩ : syracuseStep 8145305 = 6108979) B6108979
theorem B9652871 : Blo 1128631 9652871 := bstep (se 1 (by rfl) ⟨7239653, by rfl⟩ : syracuseStep 9652871 = 14479307) B14479307
theorem B3623609 : Blo 1128631 3623609 := bstep (se 2 (by rfl) ⟨1358853, by rfl⟩ : syracuseStep 3623609 = 2717707) B2717707
theorem B4836125 : Blo 1128631 4836125 := bstep (se 3 (by rfl) ⟨906773, by rfl⟩ : syracuseStep 4836125 = 1813547) B1813547
theorem B2542409 : Blo 1128631 2542409 := bstep (se 2 (by rfl) ⟨953403, by rfl⟩ : syracuseStep 2542409 = 1906807) B1906807
theorem B2411527 : Blo 1128631 2411527 := bstep (se 1 (by rfl) ⟨1808645, by rfl⟩ : syracuseStep 2411527 = 3617291) B3617291
theorem B3820715 : Blo 1128631 3820715 := bstep (se 1 (by rfl) ⟨2865536, by rfl⟩ : syracuseStep 3820715 = 5731073) B5731073
theorem B18599203 : Blo 1128631 18599203 := bstep (se 1 (by rfl) ⟨13949402, by rfl⟩ : syracuseStep 18599203 = 27898805) B27898805
theorem B2149897 : Blo 1128631 2149897 := bstep (se 2 (by rfl) ⟨806211, by rfl⟩ : syracuseStep 2149897 = 1612423) B1612423
theorem B12242519 : Blo 1128631 12242519 := bstep (se 1 (by rfl) ⟨9181889, by rfl⟩ : syracuseStep 12242519 = 18363779) B18363779
theorem B2444897 : Blo 1128631 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B2543201 : Blo 1128631 2543201 := bstep (se 2 (by rfl) ⟨953700, by rfl⟩ : syracuseStep 2543201 = 1907401) B1907401
theorem B3821255 : Blo 1128631 3821255 := bstep (se 1 (by rfl) ⟨2865941, by rfl⟩ : syracuseStep 3821255 = 5731883) B5731883
theorem B2543543 : Blo 1128631 2543543 := bstep (se 1 (by rfl) ⟨1907657, by rfl⟩ : syracuseStep 2543543 = 3815315) B3815315
theorem B7065917 : Blo 1128631 7065917 := bstep (se 3 (by rfl) ⟨1324859, by rfl⟩ : syracuseStep 7065917 = 2649719) B2649719
theorem B2544137 : Blo 1128631 2544137 := bstep (se 2 (by rfl) ⟨954051, by rfl⟩ : syracuseStep 2544137 = 1908103) B1908103
theorem B5722649 : Blo 1128631 5722649 := bstep (se 2 (by rfl) ⟨2145993, by rfl⟩ : syracuseStep 5722649 = 4291987) B4291987
theorem B3822119 : Blo 1128631 3822119 := bstep (se 1 (by rfl) ⟨2866589, by rfl⟩ : syracuseStep 3822119 = 5733179) B5733179
theorem B3822227 : Blo 1128631 3822227 := bstep (se 1 (by rfl) ⟨2866670, by rfl⟩ : syracuseStep 3822227 = 5733341) B5733341
theorem B2544479 : Blo 1128631 2544479 := bstep (se 1 (by rfl) ⟨1908359, by rfl⟩ : syracuseStep 2544479 = 3816719) B3816719
theorem B3822443 : Blo 1128631 3822443 := bstep (se 1 (by rfl) ⟨2866832, by rfl⟩ : syracuseStep 3822443 = 5733665) B5733665
theorem B3822497 : Blo 1128631 3822497 := bstep (se 2 (by rfl) ⟨1433436, by rfl⟩ : syracuseStep 3822497 = 2866873) B2866873
theorem B1430455 : Blo 1128631 1430455 := bstep (se 1 (by rfl) ⟨1072841, by rfl⟩ : syracuseStep 1430455 = 2145683) B2145683
theorem B26432477 : Blo 1128631 26432477 := bstep (se 3 (by rfl) ⟨4956089, by rfl⟩ : syracuseStep 26432477 = 9912179) B9912179
theorem B2544659 : Blo 1128631 2544659 := bstep (se 1 (by rfl) ⟨1908494, by rfl⟩ : syracuseStep 2544659 = 3816989) B3816989
theorem B2545001 : Blo 1128631 2545001 := bstep (se 2 (by rfl) ⟨954375, by rfl⟩ : syracuseStep 2545001 = 1908751) B1908751
theorem B3724649 : Blo 1128631 3724649 := bstep (se 2 (by rfl) ⟨1396743, by rfl⟩ : syracuseStep 3724649 = 2793487) B2793487
theorem B1693103 : Blo 1128631 1693103 := bstep (se 1 (by rfl) ⟨1269827, by rfl⟩ : syracuseStep 1693103 = 2539655) B2539655
theorem B3626441 : Blo 1128631 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B16307675 : Blo 1128631 16307675 := bstep (se 1 (by rfl) ⟨12230756, by rfl⟩ : syracuseStep 16307675 = 24461513) B24461513
theorem B1693193 : Blo 1128631 1693193 := bstep (se 2 (by rfl) ⟨634947, by rfl⟩ : syracuseStep 1693193 = 1269895) B1269895
theorem B1693223 : Blo 1128631 1693223 := bstep (se 1 (by rfl) ⟨1269917, by rfl⟩ : syracuseStep 1693223 = 2539835) B2539835
theorem B1693307 : Blo 1128631 1693307 := bstep (se 1 (by rfl) ⟨1269980, by rfl⟩ : syracuseStep 1693307 = 2539961) B2539961
theorem B1693433 : Blo 1128631 1693433 := bstep (se 2 (by rfl) ⟨635037, by rfl⟩ : syracuseStep 1693433 = 1270075) B1270075
theorem B1693535 : Blo 1128631 1693535 := bstep (se 1 (by rfl) ⟨1270151, by rfl⟩ : syracuseStep 1693535 = 2540303) B2540303
theorem B1693547 : Blo 1128631 1693547 := bstep (se 1 (by rfl) ⟨1270160, by rfl⟩ : syracuseStep 1693547 = 2540321) B2540321
theorem B3626927 : Blo 1128631 3626927 := bstep (se 1 (by rfl) ⟨2720195, by rfl⟩ : syracuseStep 3626927 = 5440391) B5440391
theorem B2545595 : Blo 1128631 2545595 := bstep (se 1 (by rfl) ⟨1909196, by rfl⟩ : syracuseStep 2545595 = 3818393) B3818393
theorem B8148995 : Blo 1128631 8148995 := bstep (se 1 (by rfl) ⟨6111746, by rfl⟩ : syracuseStep 8148995 = 12223493) B12223493
theorem B8574983 : Blo 1128631 8574983 := bstep (se 1 (by rfl) ⟨6431237, by rfl⟩ : syracuseStep 8574983 = 12862475) B12862475
theorem B2545721 : Blo 1128631 2545721 := bstep (se 2 (by rfl) ⟨954645, by rfl⟩ : syracuseStep 2545721 = 1909291) B1909291
theorem B1693775 : Blo 1128631 1693775 := bstep (se 1 (by rfl) ⟨1270331, by rfl⟩ : syracuseStep 1693775 = 2540663) B2540663
theorem B1693895 : Blo 1128631 1693895 := bstep (se 1 (by rfl) ⟨1270421, by rfl⟩ : syracuseStep 1693895 = 2540843) B2540843
theorem B1431751 : Blo 1128631 1431751 := bstep (se 1 (by rfl) ⟨1073813, by rfl⟩ : syracuseStep 1431751 = 2147627) B2147627
theorem B2578679 : Blo 1128631 2578679 := bstep (se 1 (by rfl) ⟨1934009, by rfl⟩ : syracuseStep 2578679 = 3868019) B3868019
theorem B1694057 : Blo 1128631 1694057 := bstep (se 2 (by rfl) ⟨635271, by rfl⟩ : syracuseStep 1694057 = 1270543) B1270543
theorem B2546063 : Blo 1128631 2546063 := bstep (se 1 (by rfl) ⟨1909547, by rfl⟩ : syracuseStep 2546063 = 3819095) B3819095
theorem B1694135 : Blo 1128631 1694135 := bstep (se 1 (by rfl) ⟨1270601, by rfl⟩ : syracuseStep 1694135 = 2541203) B2541203
theorem B1694171 : Blo 1128631 1694171 := bstep (se 1 (by rfl) ⟨1270628, by rfl⟩ : syracuseStep 1694171 = 2541257) B2541257
theorem B8575469 : Blo 1128631 8575469 := bstep (se 3 (by rfl) ⟨1607900, by rfl⟩ : syracuseStep 8575469 = 3215801) B3215801
theorem B2546387 : Blo 1128631 2546387 := bstep (se 1 (by rfl) ⟨1909790, by rfl⟩ : syracuseStep 2546387 = 3819581) B3819581
theorem B1694639 : Blo 1128631 1694639 := bstep (se 1 (by rfl) ⟨1270979, by rfl⟩ : syracuseStep 1694639 = 2541959) B2541959
theorem B1432495 : Blo 1128631 1432495 := bstep (se 1 (by rfl) ⟨1074371, by rfl⟩ : syracuseStep 1432495 = 2148743) B2148743
theorem B1694729 : Blo 1128631 1694729 := bstep (se 2 (by rfl) ⟨635523, by rfl⟩ : syracuseStep 1694729 = 1271047) B1271047
theorem B1694759 : Blo 1128631 1694759 := bstep (se 1 (by rfl) ⟨1271069, by rfl⟩ : syracuseStep 1694759 = 2542139) B2542139
theorem B1694843 : Blo 1128631 1694843 := bstep (se 1 (by rfl) ⟨1271132, by rfl⟩ : syracuseStep 1694843 = 2542265) B2542265
theorem B1694969 : Blo 1128631 1694969 := bstep (se 2 (by rfl) ⟨635613, by rfl⟩ : syracuseStep 1694969 = 1271227) B1271227
theorem B1695071 : Blo 1128631 1695071 := bstep (se 1 (by rfl) ⟨1271303, by rfl⟩ : syracuseStep 1695071 = 2542607) B2542607
theorem B1695083 : Blo 1128631 1695083 := bstep (se 1 (by rfl) ⟨1271312, by rfl⟩ : syracuseStep 1695083 = 2542625) B2542625
theorem B5725565 : Blo 1128631 5725565 := bstep (se 3 (by rfl) ⟨1073543, by rfl⟩ : syracuseStep 5725565 = 2147087) B2147087
theorem B1695311 : Blo 1128631 1695311 := bstep (se 1 (by rfl) ⟨1271483, by rfl⟩ : syracuseStep 1695311 = 2542967) B2542967
theorem B2416225 : Blo 1128631 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B2547323 : Blo 1128631 2547323 := bstep (se 1 (by rfl) ⟨1910492, by rfl⟩ : syracuseStep 2547323 = 3820985) B3820985
theorem B1695431 : Blo 1128631 1695431 := bstep (se 1 (by rfl) ⟨1271573, by rfl⟩ : syracuseStep 1695431 = 2543147) B2543147
theorem B2547449 : Blo 1128631 2547449 := bstep (se 2 (by rfl) ⟨955293, by rfl⟩ : syracuseStep 2547449 = 1910587) B1910587
theorem B1695593 : Blo 1128631 1695593 := bstep (se 2 (by rfl) ⟨635847, by rfl⟩ : syracuseStep 1695593 = 1271695) B1271695
theorem B12214151 : Blo 1128631 12214151 := bstep (se 1 (by rfl) ⟨9160613, by rfl⟩ : syracuseStep 12214151 = 18321227) B18321227
theorem B1695671 : Blo 1128631 1695671 := bstep (se 1 (by rfl) ⟨1271753, by rfl⟩ : syracuseStep 1695671 = 2543507) B2543507
theorem B2416567 : Blo 1128631 2416567 := bstep (se 1 (by rfl) ⟨1812425, by rfl⟩ : syracuseStep 2416567 = 3624851) B3624851
theorem B1695707 : Blo 1128631 1695707 := bstep (se 1 (by rfl) ⟨1271780, by rfl⟩ : syracuseStep 1695707 = 2543561) B2543561
theorem B2547719 : Blo 1128631 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B2547791 : Blo 1128631 2547791 := bstep (se 1 (by rfl) ⟨1910843, by rfl⟩ : syracuseStep 2547791 = 3821687) B3821687
theorem B6447185 : Blo 1128631 6447185 := bstep (se 2 (by rfl) ⟨2417694, by rfl⟩ : syracuseStep 6447185 = 4835389) B4835389
theorem B1270111 : Blo 1128631 1270111 := bstep (se 1 (by rfl) ⟨952583, by rfl⟩ : syracuseStep 1270111 = 1905167) B1905167
theorem B8577413 : Blo 1128631 8577413 := bstep (se 4 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 8577413 = 1608265) B1608265
theorem B1696175 : Blo 1128631 1696175 := bstep (se 1 (by rfl) ⟨1272131, by rfl⟩ : syracuseStep 1696175 = 2544263) B2544263
theorem B2548187 : Blo 1128631 2548187 := bstep (se 1 (by rfl) ⟨1911140, by rfl⟩ : syracuseStep 2548187 = 3822281) B3822281
theorem B1696265 : Blo 1128631 1696265 := bstep (se 2 (by rfl) ⟨636099, by rfl⟩ : syracuseStep 1696265 = 1272199) B1272199
theorem B1696295 : Blo 1128631 1696295 := bstep (se 1 (by rfl) ⟨1272221, by rfl⟩ : syracuseStep 1696295 = 2544443) B2544443
theorem B1696379 : Blo 1128631 1696379 := bstep (se 1 (by rfl) ⟨1272284, by rfl⟩ : syracuseStep 1696379 = 2544569) B2544569
theorem B1270471 : Blo 1128631 1270471 := bstep (se 1 (by rfl) ⟨952853, by rfl⟩ : syracuseStep 1270471 = 1905707) B1905707
theorem B1696505 : Blo 1128631 1696505 := bstep (se 2 (by rfl) ⟨636189, by rfl⟩ : syracuseStep 1696505 = 1272379) B1272379
theorem B1696607 : Blo 1128631 1696607 := bstep (se 1 (by rfl) ⟨1272455, by rfl⟩ : syracuseStep 1696607 = 2544911) B2544911
theorem B8577899 : Blo 1128631 8577899 := bstep (se 1 (by rfl) ⟨6433424, by rfl⟩ : syracuseStep 8577899 = 12866849) B12866849
theorem B1696619 : Blo 1128631 1696619 := bstep (se 1 (by rfl) ⟨1272464, by rfl⟩ : syracuseStep 1696619 = 2544929) B2544929
theorem B6972389 : Blo 1128631 6972389 := bstep (se 4 (by rfl) ⟨653661, by rfl⟩ : syracuseStep 6972389 = 1307323) B1307323
theorem B1696847 : Blo 1128631 1696847 := bstep (se 1 (by rfl) ⟨1272635, by rfl⟩ : syracuseStep 1696847 = 2545271) B2545271
theorem B376693847 : Blo 1128631 376693847 := bstep (se 1 (by rfl) ⟨282520385, by rfl⟩ : syracuseStep 376693847 = 565040771) B565040771
theorem B48981145 : Blo 1128631 48981145 := bstep (se 2 (by rfl) ⟨18367929, by rfl⟩ : syracuseStep 48981145 = 36735859) B36735859
theorem B1205447 : Blo 1128631 1205447 := bstep (se 1 (by rfl) ⟨904085, by rfl⟩ : syracuseStep 1205447 = 1808171) B1808171
theorem B1696967 : Blo 1128631 1696967 := bstep (se 1 (by rfl) ⟨1272725, by rfl⟩ : syracuseStep 1696967 = 2545451) B2545451
theorem B16278731 : Blo 1128631 16278731 := bstep (se 1 (by rfl) ⟨12209048, by rfl⟩ : syracuseStep 16278731 = 24418097) B24418097
theorem B2581751 : Blo 1128631 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B1697129 : Blo 1128631 1697129 := bstep (se 2 (by rfl) ⟨636423, by rfl⟩ : syracuseStep 1697129 = 1272847) B1272847
theorem B17425829 : Blo 1128631 17425829 := bstep (se 4 (by rfl) ⟨1633671, by rfl⟩ : syracuseStep 17425829 = 3267343) B3267343
theorem B1697207 : Blo 1128631 1697207 := bstep (se 1 (by rfl) ⟨1272905, by rfl⟩ : syracuseStep 1697207 = 2545811) B2545811
theorem B1697243 : Blo 1128631 1697243 := bstep (se 1 (by rfl) ⟨1272932, by rfl⟩ : syracuseStep 1697243 = 2545865) B2545865
theorem B18605531 : Blo 1128631 18605531 := bstep (se 1 (by rfl) ⟨13954148, by rfl⟩ : syracuseStep 18605531 = 27908297) B27908297
theorem B1861127 : Blo 1128631 1861127 := bstep (se 1 (by rfl) ⟨1395845, by rfl⟩ : syracuseStep 1861127 = 2791691) B2791691
theorem B1271335 : Blo 1128631 1271335 := bstep (se 1 (by rfl) ⟨953501, by rfl⟩ : syracuseStep 1271335 = 1907003) B1907003
theorem B4286141 : Blo 1128631 4286141 := bstep (se 3 (by rfl) ⟨803651, by rfl⟩ : syracuseStep 4286141 = 1607303) B1607303
theorem B4581215 : Blo 1128631 4581215 := bstep (se 1 (by rfl) ⟨3435911, by rfl⟩ : syracuseStep 4581215 = 6871823) B6871823
theorem B1697711 : Blo 1128631 1697711 := bstep (se 1 (by rfl) ⟨1273283, by rfl⟩ : syracuseStep 1697711 = 2546567) B2546567
theorem B1697801 : Blo 1128631 1697801 := bstep (se 2 (by rfl) ⟨636675, by rfl⟩ : syracuseStep 1697801 = 1273351) B1273351
theorem B1697831 : Blo 1128631 1697831 := bstep (se 1 (by rfl) ⟨1273373, by rfl⟩ : syracuseStep 1697831 = 2546747) B2546747
theorem B1697915 : Blo 1128631 1697915 := bstep (se 1 (by rfl) ⟨1273436, by rfl⟩ : syracuseStep 1697915 = 2546873) B2546873
theorem B2582699 : Blo 1128631 2582699 := bstep (se 1 (by rfl) ⟨1937024, by rfl⟩ : syracuseStep 2582699 = 3874049) B3874049
theorem B1698041 : Blo 1128631 1698041 := bstep (se 2 (by rfl) ⟨636765, by rfl⟩ : syracuseStep 1698041 = 1273531) B1273531
theorem B1698143 : Blo 1128631 1698143 := bstep (se 1 (by rfl) ⟨1273607, by rfl⟩ : syracuseStep 1698143 = 2547215) B2547215
theorem B2451817 : Blo 1128631 2451817 := bstep (se 2 (by rfl) ⟨919431, by rfl⟩ : syracuseStep 2451817 = 1838863) B1838863
theorem B1698155 : Blo 1128631 1698155 := bstep (se 1 (by rfl) ⟨1273616, by rfl⟩ : syracuseStep 1698155 = 2547233) B2547233
theorem B18835897 : Blo 1128631 18835897 := bstep (se 2 (by rfl) ⟨7063461, by rfl⟩ : syracuseStep 18835897 = 14126923) B14126923
theorem B8153581 : Blo 1128631 8153581 := bstep (se 3 (by rfl) ⟨1528796, by rfl⟩ : syracuseStep 8153581 = 3057593) B3057593
theorem B6449645 : Blo 1128631 6449645 := bstep (se 3 (by rfl) ⟨1209308, by rfl⟩ : syracuseStep 6449645 = 2418617) B2418617
theorem B2288207 : Blo 1128631 2288207 := bstep (se 1 (by rfl) ⟨1716155, by rfl⟩ : syracuseStep 2288207 = 3432311) B3432311
theorem B1698383 : Blo 1128631 1698383 := bstep (se 1 (by rfl) ⟨1273787, by rfl⟩ : syracuseStep 1698383 = 2547575) B2547575
theorem B1698503 : Blo 1128631 1698503 := bstep (se 1 (by rfl) ⟨1273877, by rfl⟩ : syracuseStep 1698503 = 2547755) B2547755
theorem B32631497 : Blo 1128631 32631497 := bstep (se 2 (by rfl) ⟨12236811, by rfl⟩ : syracuseStep 32631497 = 24473623) B24473623
theorem B8579843 : Blo 1128631 8579843 := bstep (se 1 (by rfl) ⟨6434882, by rfl⟩ : syracuseStep 8579843 = 12869765) B12869765
theorem B1698665 : Blo 1128631 1698665 := bstep (se 2 (by rfl) ⟨636999, by rfl⟩ : syracuseStep 1698665 = 1273999) B1273999
theorem B4582253 : Blo 1128631 4582253 := bstep (se 3 (by rfl) ⟨859172, by rfl⟩ : syracuseStep 4582253 = 1718345) B1718345
theorem B3435425 : Blo 1128631 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B1698743 : Blo 1128631 1698743 := bstep (se 1 (by rfl) ⟨1274057, by rfl⟩ : syracuseStep 1698743 = 2548115) B2548115
theorem B1698779 : Blo 1128631 1698779 := bstep (se 1 (by rfl) ⟨1274084, by rfl⟩ : syracuseStep 1698779 = 2548169) B2548169
theorem B1272955 : Blo 1128631 1272955 := bstep (se 1 (by rfl) ⟨954716, by rfl⟩ : syracuseStep 1272955 = 1909433) B1909433
theorem B7236989 : Blo 1128631 7236989 := bstep (se 3 (by rfl) ⟨1356935, by rfl⟩ : syracuseStep 7236989 = 2713871) B2713871
theorem B4287887 : Blo 1128631 4287887 := bstep (se 1 (by rfl) ⟨3215915, by rfl⟩ : syracuseStep 4287887 = 6431831) B6431831
theorem B1273423 : Blo 1128631 1273423 := bstep (se 1 (by rfl) ⟨955067, by rfl⟩ : syracuseStep 1273423 = 1910135) B1910135
theorem B2715275 : Blo 1128631 2715275 := bstep (se 1 (by rfl) ⟨2036456, by rfl⟩ : syracuseStep 2715275 = 4072913) B4072913
theorem B5729939 : Blo 1128631 5729939 := bstep (se 1 (by rfl) ⟨4297454, by rfl⟩ : syracuseStep 5729939 = 8594909) B8594909
theorem B1273819 : Blo 1128631 1273819 := bstep (se 1 (by rfl) ⟨955364, by rfl⟩ : syracuseStep 1273819 = 1910729) B1910729
theorem B4289057 : Blo 1128631 4289057 := bstep (se 2 (by rfl) ⟨1608396, by rfl⟩ : syracuseStep 4289057 = 3216793) B3216793
theorem B2716409 : Blo 1128631 2716409 := bstep (se 2 (by rfl) ⟨1018653, by rfl⟩ : syracuseStep 2716409 = 2037307) B2037307
theorem B4289375 : Blo 1128631 4289375 := bstep (se 1 (by rfl) ⟨3217031, by rfl⟩ : syracuseStep 4289375 = 6434063) B6434063
theorem B5436335 : Blo 1128631 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B4289543 : Blo 1128631 4289543 := bstep (se 1 (by rfl) ⟨3217157, by rfl⟩ : syracuseStep 4289543 = 6434315) B6434315
theorem B4584833 : Blo 1128631 4584833 := bstep (se 2 (by rfl) ⟨1719312, by rfl⟩ : syracuseStep 4584833 = 3438625) B3438625
theorem B4290029 : Blo 1128631 4290029 := bstep (se 3 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 4290029 = 1608761) B1608761
theorem B5306105 : Blo 1128631 5306105 := bstep (se 2 (by rfl) ⟨1989789, by rfl⟩ : syracuseStep 5306105 = 3979579) B3979579
theorem B4290347 : Blo 1128631 4290347 := bstep (se 1 (by rfl) ⟨3217760, by rfl⟩ : syracuseStep 4290347 = 6435521) B6435521
theorem B3438443 : Blo 1128631 3438443 := bstep (se 1 (by rfl) ⟨2578832, by rfl⟩ : syracuseStep 3438443 = 5157665) B5157665
theorem B8583245 : Blo 1128631 8583245 := bstep (se 3 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 8583245 = 3218717) B3218717
theorem B2291809 : Blo 1128631 2291809 := bstep (se 2 (by rfl) ⟨859428, by rfl⟩ : syracuseStep 2291809 = 1718857) B1718857
theorem B3668125 : Blo 1128631 3668125 := bstep (se 3 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 3668125 = 1375547) B1375547
theorem B16316803 : Blo 1128631 16316803 := bstep (se 1 (by rfl) ⟨12237602, by rfl⟩ : syracuseStep 16316803 = 24475205) B24475205
theorem B1833511 : Blo 1128631 1833511 := bstep (se 1 (by rfl) ⟨1375133, by rfl⟩ : syracuseStep 1833511 = 2750267) B2750267
theorem B2718407 : Blo 1128631 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B5438659 : Blo 1128631 5438659 := bstep (se 1 (by rfl) ⟨4078994, by rfl⟩ : syracuseStep 5438659 = 8157989) B8157989
theorem B7732883 : Blo 1128631 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B5439275 : Blo 1128631 5439275 := bstep (se 1 (by rfl) ⟨4079456, by rfl⟩ : syracuseStep 5439275 = 8158913) B8158913
theorem B4292459 : Blo 1128631 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B2752537 : Blo 1128631 2752537 := bstep (se 2 (by rfl) ⟨1032201, by rfl⟩ : syracuseStep 2752537 = 2064403) B2064403
theorem B3146303 : Blo 1128631 3146303 := bstep (se 1 (by rfl) ⟨2359727, by rfl⟩ : syracuseStep 3146303 = 4719455) B4719455
theorem B11010761 : Blo 1128631 11010761 := bstep (se 2 (by rfl) ⟨4129035, by rfl⟩ : syracuseStep 11010761 = 8258071) B8258071
theorem B2720503 : Blo 1128631 2720503 := bstep (se 1 (by rfl) ⟨2040377, by rfl⟩ : syracuseStep 2720503 = 4080755) B4080755
theorem B21168965 : Blo 1128631 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B48956237 : Blo 1128631 48956237 := bstep (se 3 (by rfl) ⟨9179294, by rfl⟩ : syracuseStep 48956237 = 18358589) B18358589
theorem B10880243 : Blo 1128631 10880243 := bstep (se 1 (by rfl) ⟨8160182, by rfl⟩ : syracuseStep 10880243 = 16320365) B16320365
theorem B4293931 : Blo 1128631 4293931 := bstep (se 1 (by rfl) ⟨3220448, by rfl⟩ : syracuseStep 4293931 = 6440897) B6440897
theorem B1607035 : Blo 1128631 1607035 := bstep (se 1 (by rfl) ⟨1205276, by rfl⟩ : syracuseStep 1607035 = 2410553) B2410553
theorem B5440891 : Blo 1128631 5440891 := bstep (se 1 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 5440891 = 8161337) B8161337
theorem B10847641 : Blo 1128631 10847641 := bstep (se 2 (by rfl) ⟨4067865, by rfl⟩ : syracuseStep 10847641 = 8135731) B8135731
theorem B65308193 : Blo 1128631 65308193 := bstep (se 2 (by rfl) ⟨24490572, by rfl⟩ : syracuseStep 65308193 = 48981145) B48981145
theorem B10881317 : Blo 1128631 10881317 := bstep (se 4 (by rfl) ⟨1020123, by rfl⟩ : syracuseStep 10881317 = 2040247) B2040247
theorem B8161679 : Blo 1128631 8161679 := bstep (se 1 (by rfl) ⟨6121259, by rfl⟩ : syracuseStep 8161679 = 12242519) B12242519
theorem B6884669 : Blo 1128631 6884669 := bstep (se 3 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 6884669 = 2581751) B2581751
theorem B3215369 : Blo 1128631 3215369 := bstep (se 2 (by rfl) ⟨1205763, by rfl⟩ : syracuseStep 3215369 = 2411527) B2411527
theorem B4067911 : Blo 1128631 4067911 := bstep (se 1 (by rfl) ⟨3050933, by rfl⟩ : syracuseStep 4067911 = 6101867) B6101867
theorem B4133711 : Blo 1128631 4133711 := bstep (se 1 (by rfl) ⟨3100283, by rfl⟩ : syracuseStep 4133711 = 6200567) B6200567
theorem B4298093 : Blo 1128631 4298093 := bstep (se 3 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 4298093 = 1611785) B1611785
theorem B4068731 : Blo 1128631 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B4298123 : Blo 1128631 4298123 := bstep (se 1 (by rfl) ⟨3223592, by rfl⟩ : syracuseStep 4298123 = 6447185) B6447185
theorem B6887197 : Blo 1128631 6887197 := bstep (se 3 (by rfl) ⟨1291349, by rfl⟩ : syracuseStep 6887197 = 2582699) B2582699
theorem B10852487 : Blo 1128631 10852487 := bstep (se 1 (by rfl) ⟨8139365, by rfl⟩ : syracuseStep 10852487 = 16278731) B16278731
theorem B4823225 : Blo 1128631 4823225 := bstep (se 2 (by rfl) ⟨1808709, by rfl⟩ : syracuseStep 4823225 = 3617419) B3617419
theorem B1907111 : Blo 1128631 1907111 := bstep (se 1 (by rfl) ⟨1430333, by rfl⟩ : syracuseStep 1907111 = 2860667) B2860667
theorem B2857427 : Blo 1128631 2857427 := bstep (se 1 (by rfl) ⟨2143070, by rfl⟩ : syracuseStep 2857427 = 4286141) B4286141
theorem B3054143 : Blo 1128631 3054143 := bstep (se 1 (by rfl) ⟨2290607, by rfl⟩ : syracuseStep 3054143 = 4581215) B4581215
theorem B1907273 : Blo 1128631 1907273 := bstep (se 2 (by rfl) ⟨715227, by rfl⟩ : syracuseStep 1907273 = 1430455) B1430455
theorem B99195749 : Blo 1128631 99195749 := bstep (se 4 (by rfl) ⟨9299601, by rfl⟩ : syracuseStep 99195749 = 18599203) B18599203
theorem B6101885 : Blo 1128631 6101885 := bstep (se 3 (by rfl) ⟨1144103, by rfl⟩ : syracuseStep 6101885 = 2288207) B2288207
theorem B4299763 : Blo 1128631 4299763 := bstep (se 1 (by rfl) ⟨3224822, by rfl⟩ : syracuseStep 4299763 = 6449645) B6449645
theorem B7249085 : Blo 1128631 7249085 := bstep (se 3 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 7249085 = 2718407) B2718407
theorem B3054835 : Blo 1128631 3054835 := bstep (se 1 (by rfl) ⟨2291126, by rfl⟩ : syracuseStep 3054835 = 4582253) B4582253
theorem B9182735 : Blo 1128631 9182735 := bstep (se 1 (by rfl) ⟨6887051, by rfl⟩ : syracuseStep 9182735 = 13774103) B13774103
theorem B33037901 : Blo 1128631 33037901 := bstep (se 3 (by rfl) ⟨6194606, by rfl⟩ : syracuseStep 33037901 = 12389213) B12389213
theorem B4824659 : Blo 1128631 4824659 := bstep (se 1 (by rfl) ⟨3618494, by rfl⟩ : syracuseStep 4824659 = 7236989) B7236989
theorem B2858591 : Blo 1128631 2858591 := bstep (se 1 (by rfl) ⟨2143943, by rfl⟩ : syracuseStep 2858591 = 4287887) B4287887
theorem B1908319 : Blo 1128631 1908319 := bstep (se 1 (by rfl) ⟨1431239, by rfl⟩ : syracuseStep 1908319 = 2862479) B2862479
theorem B1810183 : Blo 1128631 1810183 := bstep (se 1 (by rfl) ⟨1357637, by rfl⟩ : syracuseStep 1810183 = 2715275) B2715275
theorem B1908535 : Blo 1128631 1908535 := bstep (se 1 (by rfl) ⟨1431401, by rfl⟩ : syracuseStep 1908535 = 2862803) B2862803
theorem B3055745 : Blo 1128631 3055745 := bstep (se 2 (by rfl) ⟨1145904, by rfl⟩ : syracuseStep 3055745 = 2291809) B2291809
theorem B6430873 : Blo 1128631 6430873 := bstep (se 2 (by rfl) ⟨2411577, by rfl⟩ : syracuseStep 6430873 = 4823155) B4823155
theorem B4825241 : Blo 1128631 4825241 := bstep (se 2 (by rfl) ⟨1809465, by rfl⟩ : syracuseStep 4825241 = 3618931) B3618931
theorem B4890833 : Blo 1128631 4890833 := bstep (se 2 (by rfl) ⟨1834062, by rfl⟩ : syracuseStep 4890833 = 3668125) B3668125
theorem B1909001 : Blo 1128631 1909001 := bstep (se 2 (by rfl) ⟨715875, by rfl⟩ : syracuseStep 1909001 = 1431751) B1431751
theorem B2859371 : Blo 1128631 2859371 := bstep (se 1 (by rfl) ⟨2144528, by rfl⟩ : syracuseStep 2859371 = 4289057) B4289057
theorem B1810939 : Blo 1128631 1810939 := bstep (se 1 (by rfl) ⟨1358204, by rfl⟩ : syracuseStep 1810939 = 2716409) B2716409
theorem B4825601 : Blo 1128631 4825601 := bstep (se 2 (by rfl) ⟨1809600, by rfl⟩ : syracuseStep 4825601 = 3619201) B3619201
theorem B19341827 : Blo 1128631 19341827 := bstep (se 1 (by rfl) ⟨14506370, by rfl⟩ : syracuseStep 19341827 = 29012741) B29012741
theorem B2859583 : Blo 1128631 2859583 := bstep (se 1 (by rfl) ⟨2144687, by rfl⟩ : syracuseStep 2859583 = 4289375) B4289375
theorem B2859695 : Blo 1128631 2859695 := bstep (se 1 (by rfl) ⟨2144771, by rfl⟩ : syracuseStep 2859695 = 4289543) B4289543
theorem B3056555 : Blo 1128631 3056555 := bstep (se 1 (by rfl) ⟨2292416, by rfl⟩ : syracuseStep 3056555 = 4584833) B4584833
theorem B2860019 : Blo 1128631 2860019 := bstep (se 1 (by rfl) ⟨2145014, by rfl⟩ : syracuseStep 2860019 = 4290029) B4290029
theorem B3810401 : Blo 1128631 3810401 := bstep (se 2 (by rfl) ⟨1428900, by rfl⟩ : syracuseStep 3810401 = 2857801) B2857801
theorem B2860231 : Blo 1128631 2860231 := bstep (se 1 (by rfl) ⟨2145173, by rfl⟩ : syracuseStep 2860231 = 4290347) B4290347
theorem B1909993 : Blo 1128631 1909993 := bstep (se 2 (by rfl) ⟨716247, by rfl⟩ : syracuseStep 1909993 = 1432495) B1432495
theorem B1910047 : Blo 1128631 1910047 := bstep (se 1 (by rfl) ⟨1432535, by rfl⟩ : syracuseStep 1910047 = 2865071) B2865071
theorem B9643373 : Blo 1128631 9643373 := bstep (se 3 (by rfl) ⟨1808132, by rfl⟩ : syracuseStep 9643373 = 3616265) B3616265
theorem B3220859 : Blo 1128631 3220859 := bstep (se 1 (by rfl) ⟨2415644, by rfl⟩ : syracuseStep 3220859 = 4831289) B4831289
theorem B7251545 : Blo 1128631 7251545 := bstep (se 2 (by rfl) ⟨2719329, by rfl⟩ : syracuseStep 7251545 = 5438659) B5438659
theorem B1910459 : Blo 1128631 1910459 := bstep (se 1 (by rfl) ⟨1432844, by rfl⟩ : syracuseStep 1910459 = 2865689) B2865689
theorem B3221633 : Blo 1128631 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B10856713 : Blo 1128631 10856713 := bstep (se 2 (by rfl) ⟨4071267, by rfl⟩ : syracuseStep 10856713 = 8142535) B8142535
theorem B32647535 : Blo 1128631 32647535 := bstep (se 1 (by rfl) ⟨24485651, by rfl⟩ : syracuseStep 32647535 = 48971303) B48971303
theorem B3811751 : Blo 1128631 3811751 := bstep (se 1 (by rfl) ⟨2858813, by rfl⟩ : syracuseStep 3811751 = 5717627) B5717627
theorem B5155255 : Blo 1128631 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B2861639 : Blo 1128631 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B3811913 : Blo 1128631 3811913 := bstep (se 2 (by rfl) ⟨1429467, by rfl⟩ : syracuseStep 3811913 = 2858935) B2858935
theorem B3222089 : Blo 1128631 3222089 := bstep (se 2 (by rfl) ⟨1208283, by rfl⟩ : syracuseStep 3222089 = 2416567) B2416567
theorem B2861689 : Blo 1128631 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B9153415 : Blo 1128631 9153415 := bstep (se 1 (by rfl) ⟨6865061, by rfl⟩ : syracuseStep 9153415 = 13730123) B13730123
theorem B3222443 : Blo 1128631 3222443 := bstep (se 1 (by rfl) ⟨2416832, by rfl⟩ : syracuseStep 3222443 = 4833665) B4833665
theorem B4959313 : Blo 1128631 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B4828349 : Blo 1128631 4828349 := bstep (se 3 (by rfl) ⟨905315, by rfl⟩ : syracuseStep 4828349 = 1810631) B1810631
theorem B4074715 : Blo 1128631 4074715 := bstep (se 1 (by rfl) ⟨3056036, by rfl⟩ : syracuseStep 4074715 = 6112073) B6112073
theorem B16527361 : Blo 1128631 16527361 := bstep (se 2 (by rfl) ⟨6197760, by rfl⟩ : syracuseStep 16527361 = 12395521) B12395521
theorem B12890177 : Blo 1128631 12890177 := bstep (se 2 (by rfl) ⟨4833816, by rfl⟩ : syracuseStep 12890177 = 9667633) B9667633
theorem B8138819 : Blo 1128631 8138819 := bstep (se 1 (by rfl) ⟨6104114, by rfl⟩ : syracuseStep 8138819 = 12208229) B12208229
theorem B3813587 : Blo 1128631 3813587 := bstep (se 1 (by rfl) ⟨2860190, by rfl⟩ : syracuseStep 3813587 = 5720381) B5720381
theorem B2863451 : Blo 1128631 2863451 := bstep (se 1 (by rfl) ⟨2147588, by rfl⟩ : syracuseStep 2863451 = 4295177) B4295177
theorem B2863471 : Blo 1128631 2863471 := bstep (se 1 (by rfl) ⟨2147603, by rfl⟩ : syracuseStep 2863471 = 4295207) B4295207
theorem B6435247 : Blo 1128631 6435247 := bstep (se 1 (by rfl) ⟨4826435, by rfl⟩ : syracuseStep 6435247 = 9652871) B9652871
theorem B4829615 : Blo 1128631 4829615 := bstep (se 1 (by rfl) ⟨3622211, by rfl⟩ : syracuseStep 4829615 = 7244423) B7244423
theorem B3813857 : Blo 1128631 3813857 := bstep (se 2 (by rfl) ⟨1430196, by rfl⟩ : syracuseStep 3813857 = 2860393) B2860393
theorem B3224083 : Blo 1128631 3224083 := bstep (se 1 (by rfl) ⟨2418062, by rfl⟩ : syracuseStep 3224083 = 4836125) B4836125
theorem B12858101 : Blo 1128631 12858101 := bstep (se 5 (by rfl) ⟨602723, by rfl⟩ : syracuseStep 12858101 = 1205447) B1205447
theorem B2864119 : Blo 1128631 2864119 := bstep (se 1 (by rfl) ⟨2148089, by rfl⟩ : syracuseStep 2864119 = 4296179) B4296179
theorem B14496893 : Blo 1128631 14496893 := bstep (se 3 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 14496893 = 5436335) B5436335
theorem B3060935 : Blo 1128631 3060935 := bstep (se 1 (by rfl) ⟨2295701, by rfl⟩ : syracuseStep 3060935 = 4591403) B4591403
theorem B2864423 : Blo 1128631 2864423 := bstep (se 1 (by rfl) ⟨2148317, by rfl⟩ : syracuseStep 2864423 = 4296635) B4296635
theorem B3815099 : Blo 1128631 3815099 := bstep (se 1 (by rfl) ⟨2861324, by rfl⟩ : syracuseStep 3815099 = 5722649) B5722649
theorem B25114529 : Blo 1128631 25114529 := bstep (se 2 (by rfl) ⟨9417948, by rfl⟩ : syracuseStep 25114529 = 18835897) B18835897
theorem B1128735 : Blo 1128631 1128735 := bstep (se 1 (by rfl) ⟨846551, by rfl⟩ : syracuseStep 1128735 = 1693103) B1693103
theorem B1128795 : Blo 1128631 1128795 := bstep (se 1 (by rfl) ⟨846596, by rfl⟩ : syracuseStep 1128795 = 1693193) B1693193
theorem B1128815 : Blo 1128631 1128815 := bstep (se 1 (by rfl) ⟨846611, by rfl⟩ : syracuseStep 1128815 = 1693223) B1693223
theorem B1128871 : Blo 1128631 1128871 := bstep (se 1 (by rfl) ⟨846653, by rfl⟩ : syracuseStep 1128871 = 1693307) B1693307
theorem B1128955 : Blo 1128631 1128955 := bstep (se 1 (by rfl) ⟨846716, by rfl⟩ : syracuseStep 1128955 = 1693433) B1693433
theorem B1129023 : Blo 1128631 1129023 := bstep (se 1 (by rfl) ⟨846767, by rfl⟩ : syracuseStep 1129023 = 1693535) B1693535
theorem B1129031 : Blo 1128631 1129031 := bstep (se 1 (by rfl) ⟨846773, by rfl⟩ : syracuseStep 1129031 = 1693547) B1693547
theorem B5716655 : Blo 1128631 5716655 := bstep (se 1 (by rfl) ⟨4287491, by rfl⟩ : syracuseStep 5716655 = 8574983) B8574983
theorem B1129183 : Blo 1128631 1129183 := bstep (se 1 (by rfl) ⟨846887, by rfl⟩ : syracuseStep 1129183 = 1693775) B1693775
theorem B1129263 : Blo 1128631 1129263 := bstep (se 1 (by rfl) ⟨846947, by rfl⟩ : syracuseStep 1129263 = 1693895) B1693895
theorem B1719119 : Blo 1128631 1719119 := bstep (se 1 (by rfl) ⟨1289339, by rfl⟩ : syracuseStep 1719119 = 2578679) B2578679
theorem B2866063 : Blo 1128631 2866063 := bstep (se 1 (by rfl) ⟨2149547, by rfl⟩ : syracuseStep 2866063 = 4299095) B4299095
theorem B1129371 : Blo 1128631 1129371 := bstep (se 1 (by rfl) ⟨847028, by rfl⟩ : syracuseStep 1129371 = 1694057) B1694057
theorem B1129423 : Blo 1128631 1129423 := bstep (se 1 (by rfl) ⟨847067, by rfl⟩ : syracuseStep 1129423 = 1694135) B1694135
theorem B1129447 : Blo 1128631 1129447 := bstep (se 1 (by rfl) ⟨847085, by rfl⟩ : syracuseStep 1129447 = 1694171) B1694171
theorem B5716979 : Blo 1128631 5716979 := bstep (se 1 (by rfl) ⟨4287734, by rfl⟩ : syracuseStep 5716979 = 8575469) B8575469
theorem B8600741 : Blo 1128631 8600741 := bstep (se 4 (by rfl) ⟨806319, by rfl⟩ : syracuseStep 8600741 = 1612639) B1612639
theorem B1129759 : Blo 1128631 1129759 := bstep (se 1 (by rfl) ⟨847319, by rfl⟩ : syracuseStep 1129759 = 1694639) B1694639
theorem B1129819 : Blo 1128631 1129819 := bstep (se 1 (by rfl) ⟨847364, by rfl⟩ : syracuseStep 1129819 = 1694729) B1694729
theorem B2866529 : Blo 1128631 2866529 := bstep (se 2 (by rfl) ⟨1074948, by rfl⟩ : syracuseStep 2866529 = 2149897) B2149897
theorem B1129839 : Blo 1128631 1129839 := bstep (se 1 (by rfl) ⟨847379, by rfl⟩ : syracuseStep 1129839 = 1694759) B1694759
theorem B1129895 : Blo 1128631 1129895 := bstep (se 1 (by rfl) ⟨847421, by rfl⟩ : syracuseStep 1129895 = 1694843) B1694843
theorem B1129979 : Blo 1128631 1129979 := bstep (se 1 (by rfl) ⟨847484, by rfl⟩ : syracuseStep 1129979 = 1694969) B1694969
theorem B1130047 : Blo 1128631 1130047 := bstep (se 1 (by rfl) ⟨847535, by rfl⟩ : syracuseStep 1130047 = 1695071) B1695071
theorem B1130055 : Blo 1128631 1130055 := bstep (se 1 (by rfl) ⟨847541, by rfl⟩ : syracuseStep 1130055 = 1695083) B1695083
theorem B3817043 : Blo 1128631 3817043 := bstep (se 1 (by rfl) ⟨2862782, by rfl⟩ : syracuseStep 3817043 = 5725565) B5725565
theorem B1130207 : Blo 1128631 1130207 := bstep (se 1 (by rfl) ⟨847655, by rfl⟩ : syracuseStep 1130207 = 1695311) B1695311
theorem B1130287 : Blo 1128631 1130287 := bstep (se 1 (by rfl) ⟨847715, by rfl⟩ : syracuseStep 1130287 = 1695431) B1695431
theorem B1130395 : Blo 1128631 1130395 := bstep (se 1 (by rfl) ⟨847796, by rfl⟩ : syracuseStep 1130395 = 1695593) B1695593
theorem B8142767 : Blo 1128631 8142767 := bstep (se 1 (by rfl) ⟨6107075, by rfl⟩ : syracuseStep 8142767 = 12214151) B12214151
theorem B1130447 : Blo 1128631 1130447 := bstep (se 1 (by rfl) ⟨847835, by rfl⟩ : syracuseStep 1130447 = 1695671) B1695671
theorem B1130471 : Blo 1128631 1130471 := bstep (se 1 (by rfl) ⟨847853, by rfl⟩ : syracuseStep 1130471 = 1695707) B1695707
theorem B2539529 : Blo 1128631 2539529 := bstep (se 2 (by rfl) ⟨952323, by rfl⟩ : syracuseStep 2539529 = 1904647) B1904647
theorem B6439121 : Blo 1128631 6439121 := bstep (se 2 (by rfl) ⟨2414670, by rfl⟩ : syracuseStep 6439121 = 4829341) B4829341
theorem B5718275 : Blo 1128631 5718275 := bstep (se 1 (by rfl) ⟨4288706, by rfl⟩ : syracuseStep 5718275 = 8577413) B8577413
theorem B1130783 : Blo 1128631 1130783 := bstep (se 1 (by rfl) ⟨848087, by rfl⟩ : syracuseStep 1130783 = 1696175) B1696175
theorem B1130843 : Blo 1128631 1130843 := bstep (se 1 (by rfl) ⟨848132, by rfl⟩ : syracuseStep 1130843 = 1696265) B1696265
theorem B1130863 : Blo 1128631 1130863 := bstep (se 1 (by rfl) ⟨848147, by rfl⟩ : syracuseStep 1130863 = 1696295) B1696295
theorem B2539943 : Blo 1128631 2539943 := bstep (se 1 (by rfl) ⟨1904957, by rfl⟩ : syracuseStep 2539943 = 3809915) B3809915
theorem B1130919 : Blo 1128631 1130919 := bstep (se 1 (by rfl) ⟨848189, by rfl⟩ : syracuseStep 1130919 = 1696379) B1696379
theorem B1131003 : Blo 1128631 1131003 := bstep (se 1 (by rfl) ⟨848252, by rfl⟩ : syracuseStep 1131003 = 1696505) B1696505
theorem B2540051 : Blo 1128631 2540051 := bstep (se 1 (by rfl) ⟨1905038, by rfl⟩ : syracuseStep 2540051 = 3810077) B3810077
theorem B1131071 : Blo 1128631 1131071 := bstep (se 1 (by rfl) ⟨848303, by rfl⟩ : syracuseStep 1131071 = 1696607) B1696607
theorem B5718599 : Blo 1128631 5718599 := bstep (se 1 (by rfl) ⟨4288949, by rfl⟩ : syracuseStep 5718599 = 8577899) B8577899
theorem B1131079 : Blo 1128631 1131079 := bstep (se 1 (by rfl) ⟨848309, by rfl⟩ : syracuseStep 1131079 = 1696619) B1696619
theorem B2540105 : Blo 1128631 2540105 := bstep (se 2 (by rfl) ⟨952539, by rfl⟩ : syracuseStep 2540105 = 1905079) B1905079
theorem B1131231 : Blo 1128631 1131231 := bstep (se 1 (by rfl) ⟨848423, by rfl⟩ : syracuseStep 1131231 = 1696847) B1696847
theorem B1131311 : Blo 1128631 1131311 := bstep (se 1 (by rfl) ⟨848483, by rfl⟩ : syracuseStep 1131311 = 1696967) B1696967
theorem B1131419 : Blo 1128631 1131419 := bstep (se 1 (by rfl) ⟨848564, by rfl⟩ : syracuseStep 1131419 = 1697129) B1697129
theorem B11617219 : Blo 1128631 11617219 := bstep (se 1 (by rfl) ⟨8712914, by rfl⟩ : syracuseStep 11617219 = 17425829) B17425829
theorem B1131471 : Blo 1128631 1131471 := bstep (se 1 (by rfl) ⟨848603, by rfl⟩ : syracuseStep 1131471 = 1697207) B1697207
theorem B2540519 : Blo 1128631 2540519 := bstep (se 1 (by rfl) ⟨1905389, by rfl⟩ : syracuseStep 2540519 = 3810779) B3810779
theorem B1131495 : Blo 1128631 1131495 := bstep (se 1 (by rfl) ⟨848621, by rfl⟩ : syracuseStep 1131495 = 1697243) B1697243
theorem B12403687 : Blo 1128631 12403687 := bstep (se 1 (by rfl) ⟨9302765, by rfl⟩ : syracuseStep 12403687 = 18605531) B18605531
theorem B1131807 : Blo 1128631 1131807 := bstep (se 1 (by rfl) ⟨848855, by rfl⟩ : syracuseStep 1131807 = 1697711) B1697711
theorem B36619607 : Blo 1128631 36619607 := bstep (se 1 (by rfl) ⟨27464705, by rfl⟩ : syracuseStep 36619607 = 54929411) B54929411
theorem B1131867 : Blo 1128631 1131867 := bstep (se 1 (by rfl) ⟨848900, by rfl⟩ : syracuseStep 1131867 = 1697801) B1697801
theorem B3261791 : Blo 1128631 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B2540897 : Blo 1128631 2540897 := bstep (se 2 (by rfl) ⟨952836, by rfl⟩ : syracuseStep 2540897 = 1905673) B1905673
theorem B1131887 : Blo 1128631 1131887 := bstep (se 1 (by rfl) ⟨848915, by rfl⟩ : syracuseStep 1131887 = 1697831) B1697831
theorem B1131943 : Blo 1128631 1131943 := bstep (se 1 (by rfl) ⟨848957, by rfl⟩ : syracuseStep 1131943 = 1697915) B1697915
theorem B2540987 : Blo 1128631 2540987 := bstep (se 1 (by rfl) ⟨1905740, by rfl⟩ : syracuseStep 2540987 = 3811481) B3811481
theorem B1132027 : Blo 1128631 1132027 := bstep (se 1 (by rfl) ⟨849020, by rfl⟩ : syracuseStep 1132027 = 1698041) B1698041
theorem B2541113 : Blo 1128631 2541113 := bstep (se 2 (by rfl) ⟨952917, by rfl⟩ : syracuseStep 2541113 = 1905835) B1905835
theorem B1132095 : Blo 1128631 1132095 := bstep (se 1 (by rfl) ⟨849071, by rfl⟩ : syracuseStep 1132095 = 1698143) B1698143
theorem B1132103 : Blo 1128631 1132103 := bstep (se 1 (by rfl) ⟨849077, by rfl⟩ : syracuseStep 1132103 = 1698155) B1698155
theorem B1132255 : Blo 1128631 1132255 := bstep (se 1 (by rfl) ⟨849191, by rfl⟩ : syracuseStep 1132255 = 1698383) B1698383
theorem B1132335 : Blo 1128631 1132335 := bstep (se 1 (by rfl) ⟨849251, by rfl⟩ : syracuseStep 1132335 = 1698503) B1698503
theorem B5719895 : Blo 1128631 5719895 := bstep (se 1 (by rfl) ⟨4289921, by rfl⟩ : syracuseStep 5719895 = 8579843) B8579843
theorem B1132443 : Blo 1128631 1132443 := bstep (se 1 (by rfl) ⟨849332, by rfl⟩ : syracuseStep 1132443 = 1698665) B1698665
theorem B1132495 : Blo 1128631 1132495 := bstep (se 1 (by rfl) ⟨849371, by rfl⟩ : syracuseStep 1132495 = 1698743) B1698743
theorem B1132519 : Blo 1128631 1132519 := bstep (se 1 (by rfl) ⟨849389, by rfl⟩ : syracuseStep 1132519 = 1698779) B1698779
theorem B2541779 : Blo 1128631 2541779 := bstep (se 1 (by rfl) ⟨1906334, by rfl⟩ : syracuseStep 2541779 = 3812669) B3812669
theorem B2541833 : Blo 1128631 2541833 := bstep (se 2 (by rfl) ⟨953187, by rfl⟩ : syracuseStep 2541833 = 1906375) B1906375
theorem B4180391 : Blo 1128631 4180391 := bstep (se 1 (by rfl) ⟨3135293, by rfl⟩ : syracuseStep 4180391 = 6270587) B6270587
theorem B3819959 : Blo 1128631 3819959 := bstep (se 1 (by rfl) ⟨2864969, by rfl⟩ : syracuseStep 3819959 = 5729939) B5729939
theorem B2542049 : Blo 1128631 2542049 := bstep (se 2 (by rfl) ⟨953268, by rfl⟩ : syracuseStep 2542049 = 1906537) B1906537
theorem B8571581 : Blo 1128631 8571581 := bstep (se 3 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 8571581 = 3214343) B3214343
theorem B2542355 : Blo 1128631 2542355 := bstep (se 1 (by rfl) ⟨1906766, by rfl⟩ : syracuseStep 2542355 = 3813533) B3813533
theorem B2411407 : Blo 1128631 2411407 := bstep (se 1 (by rfl) ⟨1808555, by rfl⟩ : syracuseStep 2411407 = 3617111) B3617111
theorem B12372907 : Blo 1128631 12372907 := bstep (se 1 (by rfl) ⟨9279680, by rfl⟩ : syracuseStep 12372907 = 18559361) B18559361
theorem B1428455 : Blo 1128631 1428455 := bstep (se 1 (by rfl) ⟨1071341, by rfl⟩ : syracuseStep 1428455 = 2142683) B2142683
theorem B2542715 : Blo 1128631 2542715 := bstep (se 1 (by rfl) ⟨1907036, by rfl⟩ : syracuseStep 2542715 = 3814073) B3814073
theorem B2542841 : Blo 1128631 2542841 := bstep (se 2 (by rfl) ⟨953565, by rfl⟩ : syracuseStep 2542841 = 1907131) B1907131
theorem B2444681 : Blo 1128631 2444681 := bstep (se 2 (by rfl) ⟨916755, by rfl⟩ : syracuseStep 2444681 = 1833511) B1833511
theorem B2542985 : Blo 1128631 2542985 := bstep (se 2 (by rfl) ⟨953619, by rfl⟩ : syracuseStep 2542985 = 1907239) B1907239
theorem B2543111 : Blo 1128631 2543111 := bstep (se 1 (by rfl) ⟨1907333, by rfl⟩ : syracuseStep 2543111 = 3814667) B3814667
theorem B2412193 : Blo 1128631 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B2543291 : Blo 1128631 2543291 := bstep (se 1 (by rfl) ⟨1907468, by rfl⟩ : syracuseStep 2543291 = 3814937) B3814937
theorem B2543417 : Blo 1128631 2543417 := bstep (se 2 (by rfl) ⟨953781, by rfl⟩ : syracuseStep 2543417 = 1907563) B1907563
theorem B2150201 : Blo 1128631 2150201 := bstep (se 2 (by rfl) ⟨806325, by rfl⟩ : syracuseStep 2150201 = 1612651) B1612651
theorem B5722163 : Blo 1128631 5722163 := bstep (se 1 (by rfl) ⟨4291622, by rfl⟩ : syracuseStep 5722163 = 8583245) B8583245
theorem B2412911 : Blo 1128631 2412911 := bstep (se 1 (by rfl) ⟨1809683, by rfl⟩ : syracuseStep 2412911 = 3619367) B3619367
theorem B2544047 : Blo 1128631 2544047 := bstep (se 1 (by rfl) ⟨1908035, by rfl⟩ : syracuseStep 2544047 = 3816071) B3816071
theorem B2544083 : Blo 1128631 2544083 := bstep (se 1 (by rfl) ⟨1908062, by rfl⟩ : syracuseStep 2544083 = 3816125) B3816125
theorem B2544191 : Blo 1128631 2544191 := bstep (se 1 (by rfl) ⟨1908143, by rfl⟩ : syracuseStep 2544191 = 3816287) B3816287
theorem B2544299 : Blo 1128631 2544299 := bstep (se 1 (by rfl) ⟨1908224, by rfl⟩ : syracuseStep 2544299 = 3816449) B3816449
theorem B2544839 : Blo 1128631 2544839 := bstep (se 1 (by rfl) ⟨1908629, by rfl⟩ : syracuseStep 2544839 = 3817259) B3817259
theorem B3626183 : Blo 1128631 3626183 := bstep (se 1 (by rfl) ⟨2719637, by rfl⟩ : syracuseStep 3626183 = 5439275) B5439275
theorem B1692959 : Blo 1128631 1692959 := bstep (se 1 (by rfl) ⟨1269719, by rfl⟩ : syracuseStep 1692959 = 2539439) B2539439
theorem B1430875 : Blo 1128631 1430875 := bstep (se 1 (by rfl) ⟨1073156, by rfl⟩ : syracuseStep 1430875 = 2146313) B2146313
theorem B2545019 : Blo 1128631 2545019 := bstep (se 1 (by rfl) ⟨1908764, by rfl⟩ : syracuseStep 2545019 = 3817529) B3817529
theorem B10868093 : Blo 1128631 10868093 := bstep (se 3 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 10868093 = 4075535) B4075535
theorem B1693127 : Blo 1128631 1693127 := bstep (se 1 (by rfl) ⟨1269845, by rfl⟩ : syracuseStep 1693127 = 2539691) B2539691
theorem B2545145 : Blo 1128631 2545145 := bstep (se 2 (by rfl) ⟨954429, by rfl⟩ : syracuseStep 2545145 = 1908859) B1908859
theorem B9655847 : Blo 1128631 9655847 := bstep (se 1 (by rfl) ⟨7241885, by rfl⟩ : syracuseStep 9655847 = 14483771) B14483771
theorem B1431103 : Blo 1128631 1431103 := bstep (se 1 (by rfl) ⟨1073327, by rfl⟩ : syracuseStep 1431103 = 2146655) B2146655
theorem B2545235 : Blo 1128631 2545235 := bstep (se 1 (by rfl) ⟨1908926, by rfl⟩ : syracuseStep 2545235 = 3817853) B3817853
theorem B5723783 : Blo 1128631 5723783 := bstep (se 1 (by rfl) ⟨4292837, by rfl⟩ : syracuseStep 5723783 = 8585675) B8585675
theorem B59463353 : Blo 1128631 59463353 := bstep (se 2 (by rfl) ⟨22298757, by rfl⟩ : syracuseStep 59463353 = 44597515) B44597515
theorem B2545415 : Blo 1128631 2545415 := bstep (se 1 (by rfl) ⟨1909061, by rfl⟩ : syracuseStep 2545415 = 3818123) B3818123
theorem B1693481 : Blo 1128631 1693481 := bstep (se 2 (by rfl) ⟨635055, by rfl⟩ : syracuseStep 1693481 = 1270111) B1270111
theorem B1693487 : Blo 1128631 1693487 := bstep (se 1 (by rfl) ⟨1270115, by rfl⟩ : syracuseStep 1693487 = 2540231) B2540231
theorem B2414441 : Blo 1128631 2414441 := bstep (se 2 (by rfl) ⟨905415, by rfl⟩ : syracuseStep 2414441 = 1810831) B1810831
theorem B1693961 : Blo 1128631 1693961 := bstep (se 2 (by rfl) ⟨635235, by rfl⟩ : syracuseStep 1693961 = 1270471) B1270471
theorem B1431847 : Blo 1128631 1431847 := bstep (se 1 (by rfl) ⟨1073885, by rfl⟩ : syracuseStep 1431847 = 2147771) B2147771
theorem B2546027 : Blo 1128631 2546027 := bstep (se 1 (by rfl) ⟨1909520, by rfl⟩ : syracuseStep 2546027 = 3819041) B3819041
theorem B1694063 : Blo 1128631 1694063 := bstep (se 1 (by rfl) ⟨1270547, by rfl⟩ : syracuseStep 1694063 = 2541095) B2541095
theorem B2546171 : Blo 1128631 2546171 := bstep (se 1 (by rfl) ⟨1909628, by rfl⟩ : syracuseStep 2546171 = 3819257) B3819257
theorem B1694279 : Blo 1128631 1694279 := bstep (se 1 (by rfl) ⟨1270709, by rfl⟩ : syracuseStep 1694279 = 2541419) B2541419
theorem B1694315 : Blo 1128631 1694315 := bstep (se 1 (by rfl) ⟨1270736, by rfl⟩ : syracuseStep 1694315 = 2541473) B2541473
theorem B1432171 : Blo 1128631 1432171 := bstep (se 1 (by rfl) ⟨1074128, by rfl⟩ : syracuseStep 1432171 = 2148257) B2148257
theorem B2546297 : Blo 1128631 2546297 := bstep (se 2 (by rfl) ⟨954861, by rfl⟩ : syracuseStep 2546297 = 1909723) B1909723
theorem B2546351 : Blo 1128631 2546351 := bstep (se 1 (by rfl) ⟨1909763, by rfl⟩ : syracuseStep 2546351 = 3819527) B3819527
theorem B8706755 : Blo 1128631 8706755 := bstep (se 1 (by rfl) ⟨6530066, by rfl⟩ : syracuseStep 8706755 = 13060133) B13060133
theorem B2546423 : Blo 1128631 2546423 := bstep (se 1 (by rfl) ⟨1909817, by rfl⟩ : syracuseStep 2546423 = 3819635) B3819635
theorem B1694543 : Blo 1128631 1694543 := bstep (se 1 (by rfl) ⟨1270907, by rfl⟩ : syracuseStep 1694543 = 2541815) B2541815
theorem B1432399 : Blo 1128631 1432399 := bstep (se 1 (by rfl) ⟨1074299, by rfl⟩ : syracuseStep 1432399 = 2148599) B2148599
theorem B6445979 : Blo 1128631 6445979 := bstep (se 1 (by rfl) ⟨4834484, by rfl⟩ : syracuseStep 6445979 = 9668969) B9668969
theorem B2546603 : Blo 1128631 2546603 := bstep (se 1 (by rfl) ⟨1909952, by rfl⟩ : syracuseStep 2546603 = 3819905) B3819905
theorem B5430203 : Blo 1128631 5430203 := bstep (se 1 (by rfl) ⟨4072652, by rfl⟩ : syracuseStep 5430203 = 8145305) B8145305
theorem B2415739 : Blo 1128631 2415739 := bstep (se 1 (by rfl) ⟨1811804, by rfl⟩ : syracuseStep 2415739 = 3623609) B3623609
theorem B1694939 : Blo 1128631 1694939 := bstep (se 1 (by rfl) ⟨1271204, by rfl⟩ : syracuseStep 1694939 = 2542409) B2542409
theorem B5725403 : Blo 1128631 5725403 := bstep (se 1 (by rfl) ⟨4294052, by rfl⟩ : syracuseStep 5725403 = 8588105) B8588105
theorem B1695113 : Blo 1128631 1695113 := bstep (se 2 (by rfl) ⟨635667, by rfl⟩ : syracuseStep 1695113 = 1271335) B1271335
theorem B2547143 : Blo 1128631 2547143 := bstep (se 1 (by rfl) ⟨1910357, by rfl⟩ : syracuseStep 2547143 = 3820715) B3820715
theorem B1629931 : Blo 1128631 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B1695467 : Blo 1128631 1695467 := bstep (se 1 (by rfl) ⟨1271600, by rfl⟩ : syracuseStep 1695467 = 2543201) B2543201
theorem B2547503 : Blo 1128631 2547503 := bstep (se 1 (by rfl) ⟨1910627, by rfl⟩ : syracuseStep 2547503 = 3821255) B3821255
theorem B1695695 : Blo 1128631 1695695 := bstep (se 1 (by rfl) ⟨1271771, by rfl⟩ : syracuseStep 1695695 = 2543543) B2543543
theorem B26108081 : Blo 1128631 26108081 := bstep (se 2 (by rfl) ⟨9790530, by rfl⟩ : syracuseStep 26108081 = 19581061) B19581061
theorem B4710611 : Blo 1128631 4710611 := bstep (se 1 (by rfl) ⟨3532958, by rfl⟩ : syracuseStep 4710611 = 7065917) B7065917
theorem B5726537 : Blo 1128631 5726537 := bstep (se 2 (by rfl) ⟨2147451, by rfl⟩ : syracuseStep 5726537 = 4294903) B4294903
theorem B2416969 : Blo 1128631 2416969 := bstep (se 2 (by rfl) ⟨906363, by rfl⟩ : syracuseStep 2416969 = 1812727) B1812727
theorem B1696091 : Blo 1128631 1696091 := bstep (se 1 (by rfl) ⟨1272068, by rfl⟩ : syracuseStep 1696091 = 2544137) B2544137
theorem B2548079 : Blo 1128631 2548079 := bstep (se 1 (by rfl) ⟨1911059, by rfl⟩ : syracuseStep 2548079 = 3822119) B3822119
theorem B1270183 : Blo 1128631 1270183 := bstep (se 1 (by rfl) ⟨952637, by rfl⟩ : syracuseStep 1270183 = 1905275) B1905275
theorem B2548151 : Blo 1128631 2548151 := bstep (se 1 (by rfl) ⟨1911113, by rfl⟩ : syracuseStep 2548151 = 3822227) B3822227
theorem B3269089 : Blo 1128631 3269089 := bstep (se 2 (by rfl) ⟨1225908, by rfl⟩ : syracuseStep 3269089 = 2451817) B2451817
theorem B1696319 : Blo 1128631 1696319 := bstep (se 1 (by rfl) ⟨1272239, by rfl⟩ : syracuseStep 1696319 = 2544479) B2544479
theorem B2548295 : Blo 1128631 2548295 := bstep (se 1 (by rfl) ⟨1911221, by rfl⟩ : syracuseStep 2548295 = 3822443) B3822443
theorem B2548331 : Blo 1128631 2548331 := bstep (se 1 (by rfl) ⟨1911248, by rfl⟩ : syracuseStep 2548331 = 3822497) B3822497
theorem B10871441 : Blo 1128631 10871441 := bstep (se 2 (by rfl) ⟨4076790, by rfl⟩ : syracuseStep 10871441 = 8153581) B8153581
theorem B17621651 : Blo 1128631 17621651 := bstep (se 1 (by rfl) ⟨13216238, by rfl⟩ : syracuseStep 17621651 = 26432477) B26432477
theorem B1696439 : Blo 1128631 1696439 := bstep (se 1 (by rfl) ⟨1272329, by rfl⟩ : syracuseStep 1696439 = 2544659) B2544659
theorem B1696667 : Blo 1128631 1696667 := bstep (se 1 (by rfl) ⟨1272500, by rfl⟩ : syracuseStep 1696667 = 2545001) B2545001
theorem B2483099 : Blo 1128631 2483099 := bstep (se 1 (by rfl) ⟨1862324, by rfl⟩ : syracuseStep 2483099 = 3724649) B3724649
theorem B2417627 : Blo 1128631 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B1270759 : Blo 1128631 1270759 := bstep (se 1 (by rfl) ⟨953069, by rfl⟩ : syracuseStep 1270759 = 1906139) B1906139
theorem B10871783 : Blo 1128631 10871783 := bstep (se 1 (by rfl) ⟨8153837, by rfl⟩ : syracuseStep 10871783 = 16307675) B16307675
theorem B4285655 : Blo 1128631 4285655 := bstep (se 1 (by rfl) ⟨3214241, by rfl⟩ : syracuseStep 4285655 = 6428483) B6428483
theorem B2417951 : Blo 1128631 2417951 := bstep (se 1 (by rfl) ⟨1813463, by rfl⟩ : syracuseStep 2417951 = 3626927) B3626927
theorem B2712871 : Blo 1128631 2712871 := bstep (se 1 (by rfl) ⟨2034653, by rfl⟩ : syracuseStep 2712871 = 4069307) B4069307
theorem B1697063 : Blo 1128631 1697063 := bstep (se 1 (by rfl) ⟨1272797, by rfl⟩ : syracuseStep 1697063 = 2545595) B2545595
theorem B5432663 : Blo 1128631 5432663 := bstep (se 1 (by rfl) ⟨4074497, by rfl⟩ : syracuseStep 5432663 = 8148995) B8148995
theorem B1697147 : Blo 1128631 1697147 := bstep (se 1 (by rfl) ⟨1272860, by rfl⟩ : syracuseStep 1697147 = 2545721) B2545721
theorem B1697273 : Blo 1128631 1697273 := bstep (se 2 (by rfl) ⟨636477, by rfl⟩ : syracuseStep 1697273 = 1272955) B1272955
theorem B2713171 : Blo 1128631 2713171 := bstep (se 1 (by rfl) ⟨2034878, by rfl⟩ : syracuseStep 2713171 = 4069757) B4069757
theorem B5727833 : Blo 1128631 5727833 := bstep (se 2 (by rfl) ⟨2147937, by rfl⟩ : syracuseStep 5727833 = 4295875) B4295875
theorem B1697375 : Blo 1128631 1697375 := bstep (se 1 (by rfl) ⟨1273031, by rfl⟩ : syracuseStep 1697375 = 2546063) B2546063
theorem B2418473 : Blo 1128631 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B1697591 : Blo 1128631 1697591 := bstep (se 1 (by rfl) ⟨1273193, by rfl⟩ : syracuseStep 1697591 = 2546387) B2546387
theorem B14149613 : Blo 1128631 14149613 := bstep (se 3 (by rfl) ⟨2653052, by rfl⟩ : syracuseStep 14149613 = 5306105) B5306105
theorem B1697897 : Blo 1128631 1697897 := bstep (se 2 (by rfl) ⟨636711, by rfl⟩ : syracuseStep 1697897 = 1273423) B1273423
theorem B8579357 : Blo 1128631 8579357 := bstep (se 3 (by rfl) ⟨1608629, by rfl⟩ : syracuseStep 8579357 = 3217259) B3217259
theorem B1698215 : Blo 1128631 1698215 := bstep (se 1 (by rfl) ⟨1273661, by rfl⟩ : syracuseStep 1698215 = 2547323) B2547323
theorem B4352507 : Blo 1128631 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B1698299 : Blo 1128631 1698299 := bstep (se 1 (by rfl) ⟨1273724, by rfl⟩ : syracuseStep 1698299 = 2547449) B2547449
theorem B1272415 : Blo 1128631 1272415 := bstep (se 1 (by rfl) ⟨954311, by rfl⟩ : syracuseStep 1272415 = 1908623) B1908623
theorem B1698425 : Blo 1128631 1698425 := bstep (se 2 (by rfl) ⟨636909, by rfl⟩ : syracuseStep 1698425 = 1273819) B1273819
theorem B1698479 : Blo 1128631 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B1698527 : Blo 1128631 1698527 := bstep (se 1 (by rfl) ⟨1273895, by rfl⟩ : syracuseStep 1698527 = 2547791) B2547791
theorem B1698791 : Blo 1128631 1698791 := bstep (se 1 (by rfl) ⟨1274093, by rfl⟩ : syracuseStep 1698791 = 2548187) B2548187
theorem B4648259 : Blo 1128631 4648259 := bstep (se 1 (by rfl) ⟨3486194, by rfl⟩ : syracuseStep 4648259 = 6972389) B6972389
theorem B251129231 : Blo 1128631 251129231 := bstep (se 1 (by rfl) ⟨188346923, by rfl⟩ : syracuseStep 251129231 = 376693847) B376693847
theorem B1240751 : Blo 1128631 1240751 := bstep (se 1 (by rfl) ⟨930563, by rfl⟩ : syracuseStep 1240751 = 1861127) B1861127
theorem B19328705 : Blo 1128631 19328705 := bstep (se 2 (by rfl) ⟨7248264, by rfl⟩ : syracuseStep 19328705 = 14496529) B14496529
theorem B1273567 : Blo 1128631 1273567 := bstep (se 1 (by rfl) ⟨955175, by rfl⟩ : syracuseStep 1273567 = 1910351) B1910351
theorem B1208143 : Blo 1128631 1208143 := bstep (se 1 (by rfl) ⟨906107, by rfl⟩ : syracuseStep 1208143 = 1812215) B1812215
theorem B4288571 : Blo 1128631 4288571 := bstep (se 1 (by rfl) ⟨3216428, by rfl⟩ : syracuseStep 4288571 = 6432857) B6432857
theorem B1274143 : Blo 1128631 1274143 := bstep (se 1 (by rfl) ⟨955607, by rfl⟩ : syracuseStep 1274143 = 1911215) B1911215
theorem B4288859 : Blo 1128631 4288859 := bstep (se 1 (by rfl) ⟨3216644, by rfl⟩ : syracuseStep 4288859 = 6433289) B6433289
theorem B21754331 : Blo 1128631 21754331 := bstep (se 1 (by rfl) ⟨16315748, by rfl⟩ : syracuseStep 21754331 = 32631497) B32631497
theorem B2290283 : Blo 1128631 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B4289831 : Blo 1128631 4289831 := bstep (se 1 (by rfl) ⟨3217373, by rfl⟩ : syracuseStep 4289831 = 6434747) B6434747
theorem B3863969 : Blo 1128631 3863969 := bstep (se 2 (by rfl) ⟨1448988, by rfl⟩ : syracuseStep 3863969 = 2897977) B2897977
theorem B2979287 : Blo 1128631 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B23524829 : Blo 1128631 23524829 := bstep (se 3 (by rfl) ⟨4410905, by rfl⟩ : syracuseStep 23524829 = 8821811) B8821811
theorem B21755737 : Blo 1128631 21755737 := bstep (se 2 (by rfl) ⟨8158401, by rfl⟩ : syracuseStep 21755737 = 16316803) B16316803
theorem B2292295 : Blo 1128631 2292295 := bstep (se 1 (by rfl) ⟨1719221, by rfl⟩ : syracuseStep 2292295 = 3438443) B3438443
theorem B33094277 : Blo 1128631 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B4291319 : Blo 1128631 4291319 := bstep (se 1 (by rfl) ⟨3218489, by rfl⟩ : syracuseStep 4291319 = 6436979) B6436979
theorem B1145755 : Blo 1128631 1145755 := bstep (se 1 (by rfl) ⟨859316, by rfl⟩ : syracuseStep 1145755 = 1718633) B1718633
theorem B2719099 : Blo 1128631 2719099 := bstep (se 1 (by rfl) ⟨2039324, by rfl⟩ : syracuseStep 2719099 = 4078649) B4078649
theorem B9665993 : Blo 1128631 9665993 := bstep (se 2 (by rfl) ⟨3624747, by rfl⟩ : syracuseStep 9665993 = 7249495) B7249495
theorem B3670049 : Blo 1128631 3670049 := bstep (se 2 (by rfl) ⟨1376268, by rfl⟩ : syracuseStep 3670049 = 2752537) B2752537
theorem B4292747 : Blo 1128631 4292747 := bstep (se 1 (by rfl) ⟨3219560, by rfl⟩ : syracuseStep 4292747 = 6439121) B6439121
theorem B2097535 : Blo 1128631 2097535 := bstep (se 1 (by rfl) ⟨1573151, by rfl⟩ : syracuseStep 2097535 = 3146303) B3146303
theorem B7340507 : Blo 1128631 7340507 := bstep (se 1 (by rfl) ⟨5505380, by rfl⟩ : syracuseStep 7340507 = 11010761) B11010761
theorem B32637491 : Blo 1128631 32637491 := bstep (se 1 (by rfl) ⟨24478118, by rfl⟩ : syracuseStep 32637491 = 48956237) B48956237
theorem B24413071 : Blo 1128631 24413071 := bstep (se 1 (by rfl) ⟨18309803, by rfl⟩ : syracuseStep 24413071 = 36619607) B36619607
theorem B4589779 : Blo 1128631 4589779 := bstep (se 1 (by rfl) ⟨3442334, by rfl⟩ : syracuseStep 4589779 = 6884669) B6884669
theorem B17435141 : Blo 1128631 17435141 := bstep (se 4 (by rfl) ⟨1634544, by rfl⟩ : syracuseStep 17435141 = 3269089) B3269089
theorem B1608607 : Blo 1128631 1608607 := bstep (se 1 (by rfl) ⟨1206455, by rfl⟩ : syracuseStep 1608607 = 2412911) B2412911
theorem B7245395 : Blo 1128631 7245395 := bstep (se 1 (by rfl) ⟨5434046, by rfl⟩ : syracuseStep 7245395 = 10868093) B10868093
theorem B10849949 : Blo 1128631 10849949 := bstep (se 3 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 10849949 = 4068731) B4068731
theorem B3215209 : Blo 1128631 3215209 := bstep (se 2 (by rfl) ⟨1205703, by rfl⟩ : syracuseStep 3215209 = 2411407) B2411407
theorem B1609627 : Blo 1128631 1609627 := bstep (se 1 (by rfl) ⟨1207220, by rfl⟩ : syracuseStep 1609627 = 2414441) B2414441
theorem B3215483 : Blo 1128631 3215483 := bstep (se 1 (by rfl) ⟨2411612, by rfl⟩ : syracuseStep 3215483 = 4823225) B4823225
theorem B19337453 : Blo 1128631 19337453 := bstep (se 3 (by rfl) ⟨3625772, by rfl⟩ : syracuseStep 19337453 = 7251545) B7251545
theorem B1904951 : Blo 1128631 1904951 := bstep (se 1 (by rfl) ⟨1428713, by rfl⟩ : syracuseStep 1904951 = 2857427) B2857427
theorem B5804503 : Blo 1128631 5804503 := bstep (se 1 (by rfl) ⟨4353377, by rfl⟩ : syracuseStep 5804503 = 8706755) B8706755
theorem B158568941 : Blo 1128631 158568941 := bstep (se 3 (by rfl) ⟨29731676, by rfl⟩ : syracuseStep 158568941 = 59463353) B59463353
theorem B66130499 : Blo 1128631 66130499 := bstep (se 1 (by rfl) ⟨49597874, by rfl⟩ : syracuseStep 66130499 = 99195749) B99195749
theorem B4067923 : Blo 1128631 4067923 := bstep (se 1 (by rfl) ⟨3050942, by rfl⟩ : syracuseStep 4067923 = 6101885) B6101885
theorem B4297319 : Blo 1128631 4297319 := bstep (se 1 (by rfl) ⟨3222989, by rfl⟩ : syracuseStep 4297319 = 6445979) B6445979
theorem B3216257 : Blo 1128631 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B22025267 : Blo 1128631 22025267 := bstep (se 1 (by rfl) ⟨16518950, by rfl⟩ : syracuseStep 22025267 = 33037901) B33037901
theorem B3216439 : Blo 1128631 3216439 := bstep (se 1 (by rfl) ⟨2412329, by rfl⟩ : syracuseStep 3216439 = 4824659) B4824659
theorem B1905727 : Blo 1128631 1905727 := bstep (se 1 (by rfl) ⟨1429295, by rfl⟩ : syracuseStep 1905727 = 2858591) B2858591
theorem B1610857 : Blo 1128631 1610857 := bstep (se 2 (by rfl) ⟨604071, by rfl⟩ : syracuseStep 1610857 = 1208143) B1208143
theorem B2037163 : Blo 1128631 2037163 := bstep (se 1 (by rfl) ⟨1527872, by rfl⟩ : syracuseStep 2037163 = 3055745) B3055745
theorem B3216827 : Blo 1128631 3216827 := bstep (se 1 (by rfl) ⟨2412620, by rfl⟩ : syracuseStep 3216827 = 4825241) B4825241
theorem B17405387 : Blo 1128631 17405387 := bstep (se 1 (by rfl) ⟨13054040, by rfl⟩ : syracuseStep 17405387 = 26108081) B26108081
theorem B1906247 : Blo 1128631 1906247 := bstep (se 1 (by rfl) ⟨1429685, by rfl⟩ : syracuseStep 1906247 = 2859371) B2859371
theorem B3217067 : Blo 1128631 3217067 := bstep (se 1 (by rfl) ⟨2412800, by rfl⟩ : syracuseStep 3217067 = 4825601) B4825601
theorem B8591021 : Blo 1128631 8591021 := bstep (se 3 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 8591021 = 3221633) B3221633
theorem B26449669 : Blo 1128631 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B7247627 : Blo 1128631 7247627 := bstep (se 1 (by rfl) ⟨5435720, by rfl⟩ : syracuseStep 7247627 = 10871441) B10871441
theorem B1906463 : Blo 1128631 1906463 := bstep (se 1 (by rfl) ⟨1429847, by rfl⟩ : syracuseStep 1906463 = 2859695) B2859695
theorem B1611751 : Blo 1128631 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B7247855 : Blo 1128631 7247855 := bstep (se 1 (by rfl) ⟨5435891, by rfl⟩ : syracuseStep 7247855 = 10871783) B10871783
theorem B1906679 : Blo 1128631 1906679 := bstep (se 1 (by rfl) ⟨1430009, by rfl⟩ : syracuseStep 1906679 = 2860019) B2860019
theorem B4298777 : Blo 1128631 4298777 := bstep (se 2 (by rfl) ⟨1612041, by rfl⟩ : syracuseStep 4298777 = 3224083) B3224083
theorem B2857103 : Blo 1128631 2857103 := bstep (se 1 (by rfl) ⟨2142827, by rfl⟩ : syracuseStep 2857103 = 4285655) B4285655
theorem B6428915 : Blo 1128631 6428915 := bstep (se 1 (by rfl) ⟨4821686, by rfl⟩ : syracuseStep 6428915 = 9643373) B9643373
theorem B21764477 : Blo 1128631 21764477 := bstep (se 3 (by rfl) ⟨4080839, by rfl⟩ : syracuseStep 21764477 = 8161679) B8161679
theorem B1612315 : Blo 1128631 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B21765023 : Blo 1128631 21765023 := bstep (se 1 (by rfl) ⟨16323767, by rfl⟩ : syracuseStep 21765023 = 32647535) B32647535
theorem B178363349 : Blo 1128631 178363349 := bstep (se 7 (by rfl) ⟨2090195, by rfl⟩ : syracuseStep 178363349 = 4180391) B4180391
theorem B1907759 : Blo 1128631 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B1907833 : Blo 1128631 1907833 := bstep (se 2 (by rfl) ⟨715437, by rfl⟩ : syracuseStep 1907833 = 1430875) B1430875
theorem B1908137 : Blo 1128631 1908137 := bstep (se 2 (by rfl) ⟨715551, by rfl⟩ : syracuseStep 1908137 = 1431103) B1431103
theorem B167419487 : Blo 1128631 167419487 := bstep (se 1 (by rfl) ⟨125564615, by rfl⟩ : syracuseStep 167419487 = 251129231) B251129231
theorem B9182929 : Blo 1128631 9182929 := bstep (se 2 (by rfl) ⟨3443598, by rfl⟩ : syracuseStep 9182929 = 6887197) B6887197
theorem B29007649 : Blo 1128631 29007649 := bstep (se 2 (by rfl) ⟨10877868, by rfl⟩ : syracuseStep 29007649 = 21755737) B21755737
theorem B12885803 : Blo 1128631 12885803 := bstep (se 1 (by rfl) ⟨9664352, by rfl⟩ : syracuseStep 12885803 = 19328705) B19328705
theorem B3809213 : Blo 1128631 3809213 := bstep (se 3 (by rfl) ⟨714227, by rfl⟩ : syracuseStep 3809213 = 1428455) B1428455
theorem B2859047 : Blo 1128631 2859047 := bstep (se 1 (by rfl) ⟨2144285, by rfl⟩ : syracuseStep 2859047 = 4288571) B4288571
theorem B8593451 : Blo 1128631 8593451 := bstep (se 1 (by rfl) ⟨6445088, by rfl⟩ : syracuseStep 8593451 = 12890177) B12890177
theorem B2859239 : Blo 1128631 2859239 := bstep (se 1 (by rfl) ⟨2144429, by rfl⟩ : syracuseStep 2859239 = 4288859) B4288859
theorem B1908967 : Blo 1128631 1908967 := bstep (se 1 (by rfl) ⟨1431725, by rfl⟩ : syracuseStep 1908967 = 2863451) B2863451
theorem B3219743 : Blo 1128631 3219743 := bstep (se 1 (by rfl) ⟨2414807, by rfl⟩ : syracuseStep 3219743 = 4829615) B4829615
theorem B1909129 : Blo 1128631 1909129 := bstep (se 2 (by rfl) ⟨715923, by rfl⟩ : syracuseStep 1909129 = 1431847) B1431847
theorem B3056393 : Blo 1128631 3056393 := bstep (se 2 (by rfl) ⟨1146147, by rfl⟩ : syracuseStep 3056393 = 2292295) B2292295
theorem B2040623 : Blo 1128631 2040623 := bstep (se 1 (by rfl) ⟨1530467, by rfl⟩ : syracuseStep 2040623 = 3060935) B3060935
theorem B1909561 : Blo 1128631 1909561 := bstep (se 2 (by rfl) ⟨716085, by rfl⟩ : syracuseStep 1909561 = 1432171) B1432171
theorem B2859887 : Blo 1128631 2859887 := bstep (se 1 (by rfl) ⟨2144915, by rfl⟩ : syracuseStep 2859887 = 4289831) B4289831
theorem B1909615 : Blo 1128631 1909615 := bstep (se 1 (by rfl) ⟨1432211, by rfl⟩ : syracuseStep 1909615 = 2864423) B2864423
theorem B1909865 : Blo 1128631 1909865 := bstep (se 2 (by rfl) ⟨716199, by rfl⟩ : syracuseStep 1909865 = 1432399) B1432399
theorem B3220985 : Blo 1128631 3220985 := bstep (se 2 (by rfl) ⟨1207869, by rfl⟩ : syracuseStep 3220985 = 2415739) B2415739
theorem B4073113 : Blo 1128631 4073113 := bstep (se 2 (by rfl) ⟨1527417, by rfl⟩ : syracuseStep 4073113 = 3054835) B3054835
theorem B22062851 : Blo 1128631 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B3811103 : Blo 1128631 3811103 := bstep (se 1 (by rfl) ⟨2858327, by rfl⟩ : syracuseStep 3811103 = 5716655) B5716655
theorem B2860879 : Blo 1128631 2860879 := bstep (se 1 (by rfl) ⟨2145659, by rfl⟩ : syracuseStep 2860879 = 4291319) B4291319
theorem B3811319 : Blo 1128631 3811319 := bstep (se 1 (by rfl) ⟨2858489, by rfl⟩ : syracuseStep 3811319 = 5716979) B5716979
theorem B1911019 : Blo 1128631 1911019 := bstep (se 1 (by rfl) ⟨1433264, by rfl⟩ : syracuseStep 1911019 = 2866529) B2866529
theorem B2173241 : Blo 1128631 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B3812183 : Blo 1128631 3812183 := bstep (se 1 (by rfl) ⟨2859137, by rfl⟩ : syracuseStep 3812183 = 5718275) B5718275
theorem B3812399 : Blo 1128631 3812399 := bstep (se 1 (by rfl) ⟨2859299, by rfl⟩ : syracuseStep 3812399 = 5718599) B5718599
theorem B3222625 : Blo 1128631 3222625 := bstep (se 2 (by rfl) ⟨1208484, by rfl⟩ : syracuseStep 3222625 = 2416969) B2416969
theorem B3812777 : Blo 1128631 3812777 := bstep (se 2 (by rfl) ⟨1429791, by rfl⟩ : syracuseStep 3812777 = 2859583) B2859583
theorem B7253495 : Blo 1128631 7253495 := bstep (se 1 (by rfl) ⟨5440121, by rfl⟩ : syracuseStep 7253495 = 10880243) B10880243
theorem B3813263 : Blo 1128631 3813263 := bstep (se 1 (by rfl) ⟨2859947, by rfl⟩ : syracuseStep 3813263 = 5719895) B5719895
theorem B7254211 : Blo 1128631 7254211 := bstep (se 1 (by rfl) ⟨5440658, by rfl⟩ : syracuseStep 7254211 = 10881317) B10881317
theorem B3813641 : Blo 1128631 3813641 := bstep (se 2 (by rfl) ⟨1430115, by rfl⟩ : syracuseStep 3813641 = 2860231) B2860231
theorem B5714387 : Blo 1128631 5714387 := bstep (se 1 (by rfl) ⟨4285790, by rfl⟩ : syracuseStep 5714387 = 8571581) B8571581
theorem B2142713 : Blo 1128631 2142713 := bstep (se 2 (by rfl) ⟨803517, by rfl⟩ : syracuseStep 2142713 = 1607035) B1607035
theorem B7254521 : Blo 1128631 7254521 := bstep (se 2 (by rfl) ⟨2720445, by rfl⟩ : syracuseStep 7254521 = 5440891) B5440891
theorem B14463521 : Blo 1128631 14463521 := bstep (se 2 (by rfl) ⟨5423820, by rfl⟩ : syracuseStep 14463521 = 10847641) B10847641
theorem B3617561 : Blo 1128631 3617561 := bstep (se 2 (by rfl) ⟨1356585, by rfl⟩ : syracuseStep 3617561 = 2713171) B2713171
theorem B11023229 : Blo 1128631 11023229 := bstep (se 3 (by rfl) ⟨2066855, by rfl⟩ : syracuseStep 11023229 = 4133711) B4133711
theorem B2143579 : Blo 1128631 2143579 := bstep (se 1 (by rfl) ⟨1607684, by rfl⟩ : syracuseStep 2143579 = 3215369) B3215369
theorem B3814775 : Blo 1128631 3814775 := bstep (se 1 (by rfl) ⟨2861081, by rfl⟩ : syracuseStep 3814775 = 5722163) B5722163
theorem B3815585 : Blo 1128631 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B1128639 : Blo 1128631 1128639 := bstep (se 1 (by rfl) ⟨846479, by rfl⟩ : syracuseStep 1128639 = 1692959) B1692959
theorem B2865395 : Blo 1128631 2865395 := bstep (se 1 (by rfl) ⟨2149046, by rfl⟩ : syracuseStep 2865395 = 4298093) B4298093
theorem B8698109 : Blo 1128631 8698109 := bstep (se 3 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 8698109 = 3261791) B3261791
theorem B2865415 : Blo 1128631 2865415 := bstep (se 1 (by rfl) ⟨2149061, by rfl⟩ : syracuseStep 2865415 = 4298123) B4298123
theorem B1128751 : Blo 1128631 1128751 := bstep (se 1 (by rfl) ⟨846563, by rfl⟩ : syracuseStep 1128751 = 1693127) B1693127
theorem B6437231 : Blo 1128631 6437231 := bstep (se 1 (by rfl) ⟨4827923, by rfl⟩ : syracuseStep 6437231 = 9655847) B9655847
theorem B3815855 : Blo 1128631 3815855 := bstep (se 1 (by rfl) ⟨2861891, by rfl⟩ : syracuseStep 3815855 = 5723783) B5723783
theorem B12204553 : Blo 1128631 12204553 := bstep (se 2 (by rfl) ⟨4576707, by rfl⟩ : syracuseStep 12204553 = 9153415) B9153415
theorem B1128987 : Blo 1128631 1128987 := bstep (se 1 (by rfl) ⟨846740, by rfl⟩ : syracuseStep 1128987 = 1693481) B1693481
theorem B1128991 : Blo 1128631 1128991 := bstep (se 1 (by rfl) ⟨846743, by rfl⟩ : syracuseStep 1128991 = 1693487) B1693487
theorem B16497209 : Blo 1128631 16497209 := bstep (se 2 (by rfl) ⟨6186453, by rfl⟩ : syracuseStep 16497209 = 12372907) B12372907
theorem B1129307 : Blo 1128631 1129307 := bstep (se 1 (by rfl) ⟨846980, by rfl⟩ : syracuseStep 1129307 = 1693961) B1693961
theorem B1129375 : Blo 1128631 1129375 := bstep (se 1 (by rfl) ⟨847031, by rfl⟩ : syracuseStep 1129375 = 1694063) B1694063
theorem B1129519 : Blo 1128631 1129519 := bstep (se 1 (by rfl) ⟨847139, by rfl⟩ : syracuseStep 1129519 = 1694279) B1694279
theorem B1129543 : Blo 1128631 1129543 := bstep (se 1 (by rfl) ⟨847157, by rfl⟩ : syracuseStep 1129543 = 1694315) B1694315
theorem B1129695 : Blo 1128631 1129695 := bstep (se 1 (by rfl) ⟨847271, by rfl⟩ : syracuseStep 1129695 = 1694543) B1694543
theorem B3620135 : Blo 1128631 3620135 := bstep (se 1 (by rfl) ⟨2715101, by rfl⟩ : syracuseStep 3620135 = 5430203) B5430203
theorem B4832723 : Blo 1128631 4832723 := bstep (se 1 (by rfl) ⟨3624542, by rfl⟩ : syracuseStep 4832723 = 7249085) B7249085
theorem B1129959 : Blo 1128631 1129959 := bstep (se 1 (by rfl) ⟨847469, by rfl⟩ : syracuseStep 1129959 = 1694939) B1694939
theorem B3816935 : Blo 1128631 3816935 := bstep (se 1 (by rfl) ⟨2862701, by rfl⟩ : syracuseStep 3816935 = 5725403) B5725403
theorem B1130075 : Blo 1128631 1130075 := bstep (se 1 (by rfl) ⟨847556, by rfl⟩ : syracuseStep 1130075 = 1695113) B1695113
theorem B1130311 : Blo 1128631 1130311 := bstep (se 1 (by rfl) ⟨847733, by rfl⟩ : syracuseStep 1130311 = 1695467) B1695467
theorem B1130463 : Blo 1128631 1130463 := bstep (se 1 (by rfl) ⟨847847, by rfl⟩ : syracuseStep 1130463 = 1695695) B1695695
theorem B22036481 : Blo 1128631 22036481 := bstep (se 2 (by rfl) ⟨8263680, by rfl⟩ : syracuseStep 22036481 = 16527361) B16527361
theorem B3260555 : Blo 1128631 3260555 := bstep (se 1 (by rfl) ⟨2445416, by rfl⟩ : syracuseStep 3260555 = 4890833) B4890833
theorem B3817691 : Blo 1128631 3817691 := bstep (se 1 (by rfl) ⟨2863268, by rfl⟩ : syracuseStep 3817691 = 5726537) B5726537
theorem B1130727 : Blo 1128631 1130727 := bstep (se 1 (by rfl) ⟨848045, by rfl⟩ : syracuseStep 1130727 = 1696091) B1696091
theorem B12894551 : Blo 1128631 12894551 := bstep (se 1 (by rfl) ⟨9670913, by rfl⟩ : syracuseStep 12894551 = 19341827) B19341827
theorem B1130879 : Blo 1128631 1130879 := bstep (se 1 (by rfl) ⟨848159, by rfl⟩ : syracuseStep 1130879 = 1696319) B1696319
theorem B11747767 : Blo 1128631 11747767 := bstep (se 1 (by rfl) ⟨8810825, by rfl⟩ : syracuseStep 11747767 = 17621651) B17621651
theorem B1130959 : Blo 1128631 1130959 := bstep (se 1 (by rfl) ⟨848219, by rfl⟩ : syracuseStep 1130959 = 1696439) B1696439
theorem B3817961 : Blo 1128631 3817961 := bstep (se 2 (by rfl) ⟨1431735, by rfl⟩ : syracuseStep 3817961 = 2863471) B2863471
theorem B1131111 : Blo 1128631 1131111 := bstep (se 1 (by rfl) ⟨848333, by rfl⟩ : syracuseStep 1131111 = 1696667) B1696667
theorem B1655399 : Blo 1128631 1655399 := bstep (se 1 (by rfl) ⟨1241549, by rfl⟩ : syracuseStep 1655399 = 2483099) B2483099
theorem B2540267 : Blo 1128631 2540267 := bstep (se 1 (by rfl) ⟨1905200, by rfl⟩ : syracuseStep 2540267 = 3810401) B3810401
theorem B5423881 : Blo 1128631 5423881 := bstep (se 2 (by rfl) ⟨2033955, by rfl⟩ : syracuseStep 5423881 = 4067911) B4067911
theorem B1131375 : Blo 1128631 1131375 := bstep (se 1 (by rfl) ⟨848531, by rfl⟩ : syracuseStep 1131375 = 1697063) B1697063
theorem B3621775 : Blo 1128631 3621775 := bstep (se 1 (by rfl) ⟨2716331, by rfl⟩ : syracuseStep 3621775 = 5432663) B5432663
theorem B2147239 : Blo 1128631 2147239 := bstep (se 1 (by rfl) ⟨1610429, by rfl⟩ : syracuseStep 2147239 = 3220859) B3220859
theorem B1131431 : Blo 1128631 1131431 := bstep (se 1 (by rfl) ⟨848573, by rfl⟩ : syracuseStep 1131431 = 1697147) B1697147
theorem B1131515 : Blo 1128631 1131515 := bstep (se 1 (by rfl) ⟨848636, by rfl⟩ : syracuseStep 1131515 = 1697273) B1697273
theorem B3818555 : Blo 1128631 3818555 := bstep (se 1 (by rfl) ⟨2863916, by rfl⟩ : syracuseStep 3818555 = 5727833) B5727833
theorem B1131583 : Blo 1128631 1131583 := bstep (se 1 (by rfl) ⟨848687, by rfl⟩ : syracuseStep 1131583 = 1697375) B1697375
theorem B1131727 : Blo 1128631 1131727 := bstep (se 1 (by rfl) ⟨848795, by rfl⟩ : syracuseStep 1131727 = 1697591) B1697591
theorem B3818825 : Blo 1128631 3818825 := bstep (se 2 (by rfl) ⟨1432059, by rfl⟩ : syracuseStep 3818825 = 2864119) B2864119
theorem B1131931 : Blo 1128631 1131931 := bstep (se 1 (by rfl) ⟨848948, by rfl⟩ : syracuseStep 1131931 = 1697897) B1697897
theorem B8144381 : Blo 1128631 8144381 := bstep (se 3 (by rfl) ⟨1527071, by rfl⟩ : syracuseStep 8144381 = 3054143) B3054143
theorem B5719571 : Blo 1128631 5719571 := bstep (se 1 (by rfl) ⟨4289678, by rfl⟩ : syracuseStep 5719571 = 8579357) B8579357
theorem B14468645 : Blo 1128631 14468645 := bstep (se 4 (by rfl) ⟨1356435, by rfl⟩ : syracuseStep 14468645 = 2712871) B2712871
theorem B2541167 : Blo 1128631 2541167 := bstep (se 1 (by rfl) ⟨1905875, by rfl⟩ : syracuseStep 2541167 = 3811751) B3811751
theorem B1132143 : Blo 1128631 1132143 := bstep (se 1 (by rfl) ⟨849107, by rfl⟩ : syracuseStep 1132143 = 1698215) B1698215
theorem B2901671 : Blo 1128631 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B1132199 : Blo 1128631 1132199 := bstep (se 1 (by rfl) ⟨849149, by rfl⟩ : syracuseStep 1132199 = 1698299) B1698299
theorem B2541275 : Blo 1128631 2541275 := bstep (se 1 (by rfl) ⟨1905956, by rfl⟩ : syracuseStep 2541275 = 3811913) B3811913
theorem B2148059 : Blo 1128631 2148059 := bstep (se 1 (by rfl) ⟨1611044, by rfl⟩ : syracuseStep 2148059 = 3222089) B3222089
theorem B1132283 : Blo 1128631 1132283 := bstep (se 1 (by rfl) ⟨849212, by rfl⟩ : syracuseStep 1132283 = 1698425) B1698425
theorem B1132319 : Blo 1128631 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B1132351 : Blo 1128631 1132351 := bstep (se 1 (by rfl) ⟨849263, by rfl⟩ : syracuseStep 1132351 = 1698527) B1698527
theorem B2148295 : Blo 1128631 2148295 := bstep (se 1 (by rfl) ⟨1611221, by rfl⟩ : syracuseStep 2148295 = 3222443) B3222443
theorem B14501861 : Blo 1128631 14501861 := bstep (se 4 (by rfl) ⟨1359549, by rfl⟩ : syracuseStep 14501861 = 2719099) B2719099
theorem B1132527 : Blo 1128631 1132527 := bstep (se 1 (by rfl) ⟨849395, by rfl⟩ : syracuseStep 1132527 = 1698791) B1698791
theorem B3098839 : Blo 1128631 3098839 := bstep (se 1 (by rfl) ⟨2324129, by rfl⟩ : syracuseStep 3098839 = 4648259) B4648259
theorem B5425879 : Blo 1128631 5425879 := bstep (se 1 (by rfl) ⟨4069409, by rfl⟩ : syracuseStep 5425879 = 8138819) B8138819
theorem B2542391 : Blo 1128631 2542391 := bstep (se 1 (by rfl) ⟨1906793, by rfl⟩ : syracuseStep 2542391 = 3813587) B3813587
theorem B14502887 : Blo 1128631 14502887 := bstep (se 1 (by rfl) ⟨10877165, by rfl⟩ : syracuseStep 14502887 = 21754331) B21754331
theorem B2542571 : Blo 1128631 2542571 := bstep (se 1 (by rfl) ⟨1906928, by rfl⟩ : syracuseStep 2542571 = 3813857) B3813857
theorem B1526855 : Blo 1128631 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B8572067 : Blo 1128631 8572067 := bstep (se 1 (by rfl) ⟨6429050, by rfl⟩ : syracuseStep 8572067 = 12858101) B12858101
theorem B2575979 : Blo 1128631 2575979 := bstep (se 1 (by rfl) ⟨1931984, by rfl⟩ : syracuseStep 2575979 = 3863969) B3863969
theorem B1986191 : Blo 1128631 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B15683219 : Blo 1128631 15683219 := bstep (se 1 (by rfl) ⟨11762414, by rfl⟩ : syracuseStep 15683219 = 23524829) B23524829
theorem B2543399 : Blo 1128631 2543399 := bstep (se 1 (by rfl) ⟨1907549, by rfl⟩ : syracuseStep 2543399 = 3815099) B3815099
theorem B3821417 : Blo 1128631 3821417 := bstep (se 2 (by rfl) ⟨1433031, by rfl⟩ : syracuseStep 3821417 = 2866063) B2866063
theorem B1527673 : Blo 1128631 1527673 := bstep (se 2 (by rfl) ⟨572877, by rfl⟩ : syracuseStep 1527673 = 1145755) B1145755
theorem B2544425 : Blo 1128631 2544425 := bstep (se 2 (by rfl) ⟨954159, by rfl⟩ : syracuseStep 2544425 = 1908319) B1908319
theorem B6443995 : Blo 1128631 6443995 := bstep (se 1 (by rfl) ⟨4832996, by rfl⟩ : syracuseStep 6443995 = 9665993) B9665993
theorem B2413577 : Blo 1128631 2413577 := bstep (se 2 (by rfl) ⟨905091, by rfl⟩ : syracuseStep 2413577 = 1810183) B1810183
theorem B2544695 : Blo 1128631 2544695 := bstep (se 1 (by rfl) ⟨1908521, by rfl⟩ : syracuseStep 2544695 = 3817043) B3817043
theorem B2544713 : Blo 1128631 2544713 := bstep (se 2 (by rfl) ⟨954267, by rfl⟩ : syracuseStep 2544713 = 1908535) B1908535
theorem B5428511 : Blo 1128631 5428511 := bstep (se 1 (by rfl) ⟨4071383, by rfl⟩ : syracuseStep 5428511 = 8142767) B8142767
theorem B1693019 : Blo 1128631 1693019 := bstep (se 1 (by rfl) ⟨1269764, by rfl⟩ : syracuseStep 1693019 = 2539529) B2539529
theorem B8574497 : Blo 1128631 8574497 := bstep (se 2 (by rfl) ⟨3215436, by rfl⟩ : syracuseStep 8574497 = 6430873) B6430873
theorem B1693295 : Blo 1128631 1693295 := bstep (se 1 (by rfl) ⟨1269971, by rfl⟩ : syracuseStep 1693295 = 2539943) B2539943
theorem B1693367 : Blo 1128631 1693367 := bstep (se 1 (by rfl) ⟨1270025, by rfl⟩ : syracuseStep 1693367 = 2540051) B2540051
theorem B1693403 : Blo 1128631 1693403 := bstep (se 1 (by rfl) ⟨1270052, by rfl⟩ : syracuseStep 1693403 = 2540105) B2540105
theorem B14112643 : Blo 1128631 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B1693577 : Blo 1128631 1693577 := bstep (se 2 (by rfl) ⟨635091, by rfl⟩ : syracuseStep 1693577 = 1270183) B1270183
theorem B1693679 : Blo 1128631 1693679 := bstep (se 1 (by rfl) ⟨1270259, by rfl⟩ : syracuseStep 1693679 = 2540519) B2540519
theorem B2414585 : Blo 1128631 2414585 := bstep (se 2 (by rfl) ⟨905469, by rfl⟩ : syracuseStep 2414585 = 1810939) B1810939
theorem B1693931 : Blo 1128631 1693931 := bstep (se 1 (by rfl) ⟨1270448, by rfl⟩ : syracuseStep 1693931 = 2540897) B2540897
theorem B1693991 : Blo 1128631 1693991 := bstep (se 1 (by rfl) ⟨1270493, by rfl⟩ : syracuseStep 1693991 = 2540987) B2540987
theorem B3627337 : Blo 1128631 3627337 := bstep (se 2 (by rfl) ⟨1360251, by rfl⟩ : syracuseStep 3627337 = 2720503) B2720503
theorem B43538795 : Blo 1128631 43538795 := bstep (se 1 (by rfl) ⟨32654096, by rfl⟩ : syracuseStep 43538795 = 65308193) B65308193
theorem B1694075 : Blo 1128631 1694075 := bstep (se 1 (by rfl) ⟨1270556, by rfl⟩ : syracuseStep 1694075 = 2541113) B2541113
theorem B15489625 : Blo 1128631 15489625 := bstep (se 2 (by rfl) ⟨5808609, by rfl⟩ : syracuseStep 15489625 = 11617219) B11617219
theorem B1694345 : Blo 1128631 1694345 := bstep (se 2 (by rfl) ⟨635379, by rfl⟩ : syracuseStep 1694345 = 1270759) B1270759
theorem B16538249 : Blo 1128631 16538249 := bstep (se 2 (by rfl) ⟨6201843, by rfl⟩ : syracuseStep 16538249 = 12403687) B12403687
theorem B1694519 : Blo 1128631 1694519 := bstep (se 1 (by rfl) ⟨1270889, by rfl⟩ : syracuseStep 1694519 = 2541779) B2541779
theorem B1694555 : Blo 1128631 1694555 := bstep (se 1 (by rfl) ⟨1270916, by rfl⟩ : syracuseStep 1694555 = 2541833) B2541833
theorem B2546639 : Blo 1128631 2546639 := bstep (se 1 (by rfl) ⟨1909979, by rfl⟩ : syracuseStep 2546639 = 3819959) B3819959
theorem B2546657 : Blo 1128631 2546657 := bstep (se 2 (by rfl) ⟨954996, by rfl⟩ : syracuseStep 2546657 = 1909993) B1909993
theorem B1694699 : Blo 1128631 1694699 := bstep (se 1 (by rfl) ⟨1271024, by rfl⟩ : syracuseStep 1694699 = 2542049) B2542049
theorem B2546729 : Blo 1128631 2546729 := bstep (se 2 (by rfl) ⟨955023, by rfl⟩ : syracuseStep 2546729 = 1910047) B1910047
theorem B5725241 : Blo 1128631 5725241 := bstep (se 2 (by rfl) ⟨2146965, by rfl⟩ : syracuseStep 5725241 = 4293931) B4293931
theorem B1694903 : Blo 1128631 1694903 := bstep (se 1 (by rfl) ⟨1271177, by rfl⟩ : syracuseStep 1694903 = 2542355) B2542355
theorem B1695143 : Blo 1128631 1695143 := bstep (se 1 (by rfl) ⟨1271357, by rfl⟩ : syracuseStep 1695143 = 2542715) B2542715
theorem B1695227 : Blo 1128631 1695227 := bstep (se 1 (by rfl) ⟨1271420, by rfl⟩ : syracuseStep 1695227 = 2542841) B2542841
theorem B1695323 : Blo 1128631 1695323 := bstep (se 1 (by rfl) ⟨1271492, by rfl⟩ : syracuseStep 1695323 = 2542985) B2542985
theorem B1695407 : Blo 1128631 1695407 := bstep (se 1 (by rfl) ⟨1271555, by rfl⟩ : syracuseStep 1695407 = 2543111) B2543111
theorem B8150813 : Blo 1128631 8150813 := bstep (se 3 (by rfl) ⟨1528277, by rfl⟩ : syracuseStep 8150813 = 3056555) B3056555
theorem B1695527 : Blo 1128631 1695527 := bstep (se 1 (by rfl) ⟨1271645, by rfl⟩ : syracuseStep 1695527 = 2543291) B2543291
theorem B1695611 : Blo 1128631 1695611 := bstep (se 1 (by rfl) ⟨1271708, by rfl⟩ : syracuseStep 1695611 = 2543417) B2543417
theorem B1433467 : Blo 1128631 1433467 := bstep (se 1 (by rfl) ⟨1075100, by rfl⟩ : syracuseStep 1433467 = 2150201) B2150201
theorem B1696031 : Blo 1128631 1696031 := bstep (se 1 (by rfl) ⟨1272023, by rfl⟩ : syracuseStep 1696031 = 2544047) B2544047
theorem B1696055 : Blo 1128631 1696055 := bstep (se 1 (by rfl) ⟨1272041, by rfl⟩ : syracuseStep 1696055 = 2544083) B2544083
theorem B14475617 : Blo 1128631 14475617 := bstep (se 2 (by rfl) ⟨5428356, by rfl⟩ : syracuseStep 14475617 = 10856713) B10856713
theorem B1696127 : Blo 1128631 1696127 := bstep (se 1 (by rfl) ⟨1272095, by rfl⟩ : syracuseStep 1696127 = 2544191) B2544191
theorem B1696199 : Blo 1128631 1696199 := bstep (se 1 (by rfl) ⟨1272149, by rfl⟩ : syracuseStep 1696199 = 2544299) B2544299
theorem B6873673 : Blo 1128631 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B6447869 : Blo 1128631 6447869 := bstep (se 3 (by rfl) ⟨1208975, by rfl⟩ : syracuseStep 6447869 = 2417951) B2417951
theorem B1696553 : Blo 1128631 1696553 := bstep (se 2 (by rfl) ⟨636207, by rfl⟩ : syracuseStep 1696553 = 1272415) B1272415
theorem B1696559 : Blo 1128631 1696559 := bstep (se 1 (by rfl) ⟨1272419, by rfl⟩ : syracuseStep 1696559 = 2544839) B2544839
theorem B2417455 : Blo 1128631 2417455 := bstep (se 1 (by rfl) ⟨1813091, by rfl⟩ : syracuseStep 2417455 = 3626183) B3626183
theorem B1696679 : Blo 1128631 1696679 := bstep (se 1 (by rfl) ⟨1272509, by rfl⟩ : syracuseStep 1696679 = 2545019) B2545019
theorem B1696763 : Blo 1128631 1696763 := bstep (se 1 (by rfl) ⟨1272572, by rfl⟩ : syracuseStep 1696763 = 2545145) B2545145
theorem B1696823 : Blo 1128631 1696823 := bstep (se 1 (by rfl) ⟨1272617, by rfl⟩ : syracuseStep 1696823 = 2545235) B2545235
theorem B1696943 : Blo 1128631 1696943 := bstep (se 1 (by rfl) ⟨1272707, by rfl⟩ : syracuseStep 1696943 = 2545415) B2545415
theorem B7234991 : Blo 1128631 7234991 := bstep (se 1 (by rfl) ⟨5426243, by rfl⟩ : syracuseStep 7234991 = 10852487) B10852487
theorem B1697351 : Blo 1128631 1697351 := bstep (se 1 (by rfl) ⟨1273013, by rfl⟩ : syracuseStep 1697351 = 2546027) B2546027
theorem B1271407 : Blo 1128631 1271407 := bstep (se 1 (by rfl) ⟨953555, by rfl⟩ : syracuseStep 1271407 = 1907111) B1907111
theorem B5432953 : Blo 1128631 5432953 := bstep (se 2 (by rfl) ⟨2037357, by rfl⟩ : syracuseStep 5432953 = 4074715) B4074715
theorem B1697447 : Blo 1128631 1697447 := bstep (se 1 (by rfl) ⟨1273085, by rfl⟩ : syracuseStep 1697447 = 2546171) B2546171
theorem B1271515 : Blo 1128631 1271515 := bstep (se 1 (by rfl) ⟨953636, by rfl⟩ : syracuseStep 1271515 = 1907273) B1907273
theorem B1697531 : Blo 1128631 1697531 := bstep (se 1 (by rfl) ⟨1273148, by rfl⟩ : syracuseStep 1697531 = 2546297) B2546297
theorem B1697567 : Blo 1128631 1697567 := bstep (se 1 (by rfl) ⟨1273175, by rfl⟩ : syracuseStep 1697567 = 2546351) B2546351
theorem B1697615 : Blo 1128631 1697615 := bstep (se 1 (by rfl) ⟨1273211, by rfl⟩ : syracuseStep 1697615 = 2546423) B2546423
theorem B1697735 : Blo 1128631 1697735 := bstep (se 1 (by rfl) ⟨1273301, by rfl⟩ : syracuseStep 1697735 = 2546603) B2546603
theorem B1698089 : Blo 1128631 1698089 := bstep (se 2 (by rfl) ⟨636783, by rfl⟩ : syracuseStep 1698089 = 1273567) B1273567
theorem B1698095 : Blo 1128631 1698095 := bstep (se 1 (by rfl) ⟨1273571, by rfl⟩ : syracuseStep 1698095 = 2547143) B2547143
theorem B6121823 : Blo 1128631 6121823 := bstep (se 1 (by rfl) ⟨4591367, by rfl⟩ : syracuseStep 6121823 = 9182735) B9182735
theorem B1698335 : Blo 1128631 1698335 := bstep (se 1 (by rfl) ⟨1273751, by rfl⟩ : syracuseStep 1698335 = 2547503) B2547503
theorem B3140407 : Blo 1128631 3140407 := bstep (se 1 (by rfl) ⟨2355305, by rfl⟩ : syracuseStep 3140407 = 4710611) B4710611
theorem B1272667 : Blo 1128631 1272667 := bstep (se 1 (by rfl) ⟨954500, by rfl⟩ : syracuseStep 1272667 = 1909001) B1909001
theorem B1698719 : Blo 1128631 1698719 := bstep (se 1 (by rfl) ⟨1274039, by rfl⟩ : syracuseStep 1698719 = 2548079) B2548079
theorem B1698767 : Blo 1128631 1698767 := bstep (se 1 (by rfl) ⟨1274075, by rfl⟩ : syracuseStep 1698767 = 2548151) B2548151
theorem B1698857 : Blo 1128631 1698857 := bstep (se 2 (by rfl) ⟨637071, by rfl⟩ : syracuseStep 1698857 = 1274143) B1274143
theorem B1698863 : Blo 1128631 1698863 := bstep (se 1 (by rfl) ⟨1274147, by rfl⟩ : syracuseStep 1698863 = 2548295) B2548295
theorem B1698887 : Blo 1128631 1698887 := bstep (se 1 (by rfl) ⟨1274165, by rfl⟩ : syracuseStep 1698887 = 2548331) B2548331
theorem B8580329 : Blo 1128631 8580329 := bstep (se 2 (by rfl) ⟨3217623, by rfl⟩ : syracuseStep 8580329 = 6435247) B6435247
theorem B1273639 : Blo 1128631 1273639 := bstep (se 1 (by rfl) ⟨955229, by rfl⟩ : syracuseStep 1273639 = 1910459) B1910459
theorem B9433075 : Blo 1128631 9433075 := bstep (se 1 (by rfl) ⟨7074806, by rfl⟩ : syracuseStep 9433075 = 14149613) B14149613
theorem B12875597 : Blo 1128631 12875597 := bstep (se 3 (by rfl) ⟨2414174, by rfl⟩ : syracuseStep 12875597 = 4828349) B4828349
theorem B9664595 : Blo 1128631 9664595 := bstep (se 1 (by rfl) ⟨7248446, by rfl⟩ : syracuseStep 9664595 = 14496893) B14496893
theorem B6519149 : Blo 1128631 6519149 := bstep (se 3 (by rfl) ⟨1222340, by rfl⟩ : syracuseStep 6519149 = 2444681) B2444681
theorem B16743019 : Blo 1128631 16743019 := bstep (se 1 (by rfl) ⟨12557264, by rfl⟩ : syracuseStep 16743019 = 25114529) B25114529
theorem B5733017 : Blo 1128631 5733017 := bstep (se 2 (by rfl) ⟨2149881, by rfl⟩ : syracuseStep 5733017 = 4299763) B4299763
theorem B3308669 : Blo 1128631 3308669 := bstep (se 3 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 3308669 = 1240751) B1240751
theorem B1146079 : Blo 1128631 1146079 := bstep (se 1 (by rfl) ⟨859559, by rfl⟩ : syracuseStep 1146079 = 1719119) B1719119
theorem B5733827 : Blo 1128631 5733827 := bstep (se 1 (by rfl) ⟨4300370, by rfl⟩ : syracuseStep 5733827 = 8600741) B8600741
theorem B21758327 : Blo 1128631 21758327 := bstep (se 1 (by rfl) ⟨16318745, by rfl⟩ : syracuseStep 21758327 = 32637491) B32637491
theorem B15663689 : Blo 1128631 15663689 := bstep (se 2 (by rfl) ⟨5873883, by rfl⟩ : syracuseStep 15663689 = 11747767) B11747767
theorem B16286453 : Blo 1128631 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B1934447 : Blo 1128631 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B9667907 : Blo 1128631 9667907 := bstep (se 1 (by rfl) ⟨7250930, by rfl⟩ : syracuseStep 9667907 = 14501861) B14501861
theorem B9668591 : Blo 1128631 9668591 := bstep (se 1 (by rfl) ⟨7251443, by rfl⟩ : syracuseStep 9668591 = 14502887) B14502887
theorem B7243937 : Blo 1128631 7243937 := bstep (se 2 (by rfl) ⟨2716476, by rfl⟩ : syracuseStep 7243937 = 5432953) B5432953
theorem B10455479 : Blo 1128631 10455479 := bstep (se 1 (by rfl) ⟨7841609, by rfl⟩ : syracuseStep 10455479 = 15683219) B15683219
theorem B4131785 : Blo 1128631 4131785 := bstep (se 2 (by rfl) ⟨1549419, by rfl⟩ : syracuseStep 4131785 = 3098839) B3098839
theorem B105712627 : Blo 1128631 105712627 := bstep (se 1 (by rfl) ⟨79284470, by rfl⟩ : syracuseStep 105712627 = 158568941) B158568941
theorem B14683511 : Blo 1128631 14683511 := bstep (se 1 (by rfl) ⟨11012633, by rfl⟩ : syracuseStep 14683511 = 22025267) B22025267
theorem B11603591 : Blo 1128631 11603591 := bstep (se 1 (by rfl) ⟨8702693, by rfl⟩ : syracuseStep 11603591 = 17405387) B17405387
theorem B1609723 : Blo 1128631 1609723 := bstep (se 1 (by rfl) ⟨1207292, by rfl⟩ : syracuseStep 1609723 = 2414585) B2414585
theorem B1904735 : Blo 1128631 1904735 := bstep (se 1 (by rfl) ⟨1428551, by rfl⟩ : syracuseStep 1904735 = 2857103) B2857103
theorem B4296833 : Blo 1128631 4296833 := bstep (se 2 (by rfl) ⟨1611312, by rfl⟩ : syracuseStep 4296833 = 3222625) B3222625
theorem B111612991 : Blo 1128631 111612991 := bstep (se 1 (by rfl) ⟨83709743, by rfl⟩ : syracuseStep 111612991 = 167419487) B167419487
theorem B2036897 : Blo 1128631 2036897 := bstep (se 2 (by rfl) ⟨763836, by rfl⟩ : syracuseStep 2036897 = 1527673) B1527673
theorem B8590535 : Blo 1128631 8590535 := bstep (se 1 (by rfl) ⟨6442901, by rfl⟩ : syracuseStep 8590535 = 12885803) B12885803
theorem B1906031 : Blo 1128631 1906031 := bstep (se 1 (by rfl) ⟨1429523, by rfl⟩ : syracuseStep 1906031 = 2859047) B2859047
theorem B1906159 : Blo 1128631 1906159 := bstep (se 1 (by rfl) ⟨1429619, by rfl⟩ : syracuseStep 1906159 = 2859239) B2859239
theorem B9672281 : Blo 1128631 9672281 := bstep (se 2 (by rfl) ⟨3627105, by rfl⟩ : syracuseStep 9672281 = 7254211) B7254211
theorem B4298579 : Blo 1128631 4298579 := bstep (se 1 (by rfl) ⟨3223934, by rfl⟩ : syracuseStep 4298579 = 6447869) B6447869
theorem B1906591 : Blo 1128631 1906591 := bstep (se 1 (by rfl) ⟨1429943, by rfl⟩ : syracuseStep 1906591 = 2859887) B2859887
theorem B16324861 : Blo 1128631 16324861 := bstep (se 3 (by rfl) ⟨3060911, by rfl⟩ : syracuseStep 16324861 = 6121823) B6121823
theorem B4823327 : Blo 1128631 4823327 := bstep (se 1 (by rfl) ⟨3617495, by rfl⟩ : syracuseStep 4823327 = 7234991) B7234991
theorem B8591993 : Blo 1128631 8591993 := bstep (se 2 (by rfl) ⟨3221997, by rfl⟩ : syracuseStep 8591993 = 6443995) B6443995
theorem B2858105 : Blo 1128631 2858105 := bstep (se 2 (by rfl) ⟨1071789, by rfl⟩ : syracuseStep 2858105 = 2143579) B2143579
theorem B35266225 : Blo 1128631 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B18816857 : Blo 1128631 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B3809591 : Blo 1128631 3809591 := bstep (se 1 (by rfl) ⟨2857193, by rfl⟩ : syracuseStep 3809591 = 5714387) B5714387
theorem B9642347 : Blo 1128631 9642347 := bstep (se 1 (by rfl) ⟨7231760, by rfl⟩ : syracuseStep 9642347 = 14463521) B14463521
theorem B7348819 : Blo 1128631 7348819 := bstep (se 1 (by rfl) ⟨5511614, by rfl⟩ : syracuseStep 7348819 = 11023229) B11023229
theorem B20652833 : Blo 1128631 20652833 := bstep (se 2 (by rfl) ⟨7744812, by rfl⟩ : syracuseStep 20652833 = 15489625) B15489625
theorem B22324025 : Blo 1128631 22324025 := bstep (se 2 (by rfl) ⟨8371509, by rfl⟩ : syracuseStep 22324025 = 16743019) B16743019
theorem B12887261 : Blo 1128631 12887261 := bstep (se 3 (by rfl) ⟨2416361, by rfl⟩ : syracuseStep 12887261 = 4832723) B4832723
theorem B1910263 : Blo 1128631 1910263 := bstep (se 1 (by rfl) ⟨1432697, by rfl⟩ : syracuseStep 1910263 = 2865395) B2865395
theorem B2205779 : Blo 1128631 2205779 := bstep (se 1 (by rfl) ⟨1654334, by rfl⟩ : syracuseStep 2205779 = 3308669) B3308669
theorem B38676865 : Blo 1128631 38676865 := bstep (se 2 (by rfl) ⟨14503824, by rfl⟩ : syracuseStep 38676865 = 29007649) B29007649
theorem B1911289 : Blo 1128631 1911289 := bstep (se 2 (by rfl) ⟨716733, by rfl⟩ : syracuseStep 1911289 = 1433467) B1433467
theorem B14690987 : Blo 1128631 14690987 := bstep (se 1 (by rfl) ⟨11018240, by rfl⟩ : syracuseStep 14690987 = 22036481) B22036481
theorem B2173703 : Blo 1128631 2173703 := bstep (se 1 (by rfl) ⟨1630277, by rfl⟩ : syracuseStep 2173703 = 3260555) B3260555
theorem B2861831 : Blo 1128631 2861831 := bstep (se 1 (by rfl) ⟨2146373, by rfl⟩ : syracuseStep 2861831 = 4292747) B4292747
theorem B8596367 : Blo 1128631 8596367 := bstep (se 1 (by rfl) ⟨6447275, by rfl⟩ : syracuseStep 8596367 = 12894551) B12894551
theorem B4893671 : Blo 1128631 4893671 := bstep (se 1 (by rfl) ⟨3670253, by rfl⟩ : syracuseStep 4893671 = 7340507) B7340507
theorem B2796713 : Blo 1128631 2796713 := bstep (se 2 (by rfl) ⟨1048767, by rfl⟩ : syracuseStep 2796713 = 2097535) B2097535
theorem B3813047 : Blo 1128631 3813047 := bstep (se 1 (by rfl) ⟨2859785, by rfl⟩ : syracuseStep 3813047 = 5719571) B5719571
theorem B9645763 : Blo 1128631 9645763 := bstep (se 1 (by rfl) ⟨7234322, by rfl⟩ : syracuseStep 9645763 = 14468645) B14468645
theorem B32550761 : Blo 1128631 32550761 := bstep (se 2 (by rfl) ⟨12206535, by rfl⟩ : syracuseStep 32550761 = 24413071) B24413071
theorem B4829033 : Blo 1128631 4829033 := bstep (se 2 (by rfl) ⟨1810887, by rfl⟩ : syracuseStep 4829033 = 3621775) B3621775
theorem B2862985 : Blo 1128631 2862985 := bstep (se 2 (by rfl) ⟨1073619, by rfl⟩ : syracuseStep 2862985 = 2147239) B2147239
theorem B5713901 : Blo 1128631 5713901 := bstep (se 3 (by rfl) ⟨1071356, by rfl⟩ : syracuseStep 5713901 = 2142713) B2142713
theorem B5714711 : Blo 1128631 5714711 := bstep (se 1 (by rfl) ⟨4286033, by rfl⟩ : syracuseStep 5714711 = 8572067) B8572067
theorem B4830263 : Blo 1128631 4830263 := bstep (se 1 (by rfl) ⟨3622697, by rfl⟩ : syracuseStep 4830263 = 7245395) B7245395
theorem B1717319 : Blo 1128631 1717319 := bstep (se 1 (by rfl) ⟨1287989, by rfl⟩ : syracuseStep 1717319 = 2575979) B2575979
theorem B1324127 : Blo 1128631 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B3814505 : Blo 1128631 3814505 := bstep (se 2 (by rfl) ⟨1430439, by rfl⟩ : syracuseStep 3814505 = 2860879) B2860879
theorem B2864393 : Blo 1128631 2864393 := bstep (se 2 (by rfl) ⟨1074147, by rfl⟩ : syracuseStep 2864393 = 2148295) B2148295
theorem B6436205 : Blo 1128631 6436205 := bstep (se 3 (by rfl) ⟨1206788, by rfl⟩ : syracuseStep 6436205 = 2413577) B2413577
theorem B2143655 : Blo 1128631 2143655 := bstep (se 1 (by rfl) ⟨1607741, by rfl⟩ : syracuseStep 2143655 = 3215483) B3215483
theorem B12891635 : Blo 1128631 12891635 := bstep (se 1 (by rfl) ⟨9668726, by rfl⟩ : syracuseStep 12891635 = 19337453) B19337453
theorem B44086999 : Blo 1128631 44086999 := bstep (se 1 (by rfl) ⟨33065249, by rfl⟩ : syracuseStep 44086999 = 66130499) B66130499
theorem B2864879 : Blo 1128631 2864879 := bstep (se 1 (by rfl) ⟨2148659, by rfl⟩ : syracuseStep 2864879 = 4297319) B4297319
theorem B2144171 : Blo 1128631 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B3619007 : Blo 1128631 3619007 := bstep (se 1 (by rfl) ⟨2714255, by rfl⟩ : syracuseStep 3619007 = 5428511) B5428511
theorem B1128679 : Blo 1128631 1128679 := bstep (se 1 (by rfl) ⟨846509, by rfl⟩ : syracuseStep 1128679 = 1693019) B1693019
theorem B2144551 : Blo 1128631 2144551 := bstep (se 1 (by rfl) ⟨1608413, by rfl⟩ : syracuseStep 2144551 = 3216827) B3216827
theorem B5716331 : Blo 1128631 5716331 := bstep (se 1 (by rfl) ⟨4287248, by rfl⟩ : syracuseStep 5716331 = 8574497) B8574497
theorem B1128863 : Blo 1128631 1128863 := bstep (se 1 (by rfl) ⟨846647, by rfl⟩ : syracuseStep 1128863 = 1693295) B1693295
theorem B2144711 : Blo 1128631 2144711 := bstep (se 1 (by rfl) ⟨1608533, by rfl⟩ : syracuseStep 2144711 = 3217067) B3217067
theorem B1128911 : Blo 1128631 1128911 := bstep (se 1 (by rfl) ⟨846683, by rfl⟩ : syracuseStep 1128911 = 1693367) B1693367
theorem B1128935 : Blo 1128631 1128935 := bstep (se 1 (by rfl) ⟨846701, by rfl⟩ : syracuseStep 1128935 = 1693403) B1693403
theorem B4831751 : Blo 1128631 4831751 := bstep (se 1 (by rfl) ⟨3623813, by rfl⟩ : syracuseStep 4831751 = 7247627) B7247627
theorem B2144809 : Blo 1128631 2144809 := bstep (se 2 (by rfl) ⟨804303, by rfl⟩ : syracuseStep 2144809 = 1608607) B1608607
theorem B1129051 : Blo 1128631 1129051 := bstep (se 1 (by rfl) ⟨846788, by rfl⟩ : syracuseStep 1129051 = 1693577) B1693577
theorem B1129119 : Blo 1128631 1129119 := bstep (se 1 (by rfl) ⟨846839, by rfl⟩ : syracuseStep 1129119 = 1693679) B1693679
theorem B4831903 : Blo 1128631 4831903 := bstep (se 1 (by rfl) ⟨3623927, by rfl⟩ : syracuseStep 4831903 = 7247855) B7247855
theorem B2865851 : Blo 1128631 2865851 := bstep (se 1 (by rfl) ⟨2149388, by rfl⟩ : syracuseStep 2865851 = 4298777) B4298777
theorem B1129287 : Blo 1128631 1129287 := bstep (se 1 (by rfl) ⟨846965, by rfl⟩ : syracuseStep 1129287 = 1693931) B1693931
theorem B1129327 : Blo 1128631 1129327 := bstep (se 1 (by rfl) ⟨846995, by rfl⟩ : syracuseStep 1129327 = 1693991) B1693991
theorem B12893093 : Blo 1128631 12893093 := bstep (se 4 (by rfl) ⟨1208727, by rfl⟩ : syracuseStep 12893093 = 2417455) B2417455
theorem B1129383 : Blo 1128631 1129383 := bstep (se 1 (by rfl) ⟨847037, by rfl⟩ : syracuseStep 1129383 = 1694075) B1694075
theorem B11025499 : Blo 1128631 11025499 := bstep (se 1 (by rfl) ⟨8269124, by rfl⟩ : syracuseStep 11025499 = 16538249) B16538249
theorem B1129563 : Blo 1128631 1129563 := bstep (se 1 (by rfl) ⟨847172, by rfl⟩ : syracuseStep 1129563 = 1694345) B1694345
theorem B1129679 : Blo 1128631 1129679 := bstep (se 1 (by rfl) ⟨847259, by rfl⟩ : syracuseStep 1129679 = 1694519) B1694519
theorem B1129703 : Blo 1128631 1129703 := bstep (se 1 (by rfl) ⟨847277, by rfl⟩ : syracuseStep 1129703 = 1694555) B1694555
theorem B1129799 : Blo 1128631 1129799 := bstep (se 1 (by rfl) ⟨847349, by rfl⟩ : syracuseStep 1129799 = 1694699) B1694699
theorem B3816827 : Blo 1128631 3816827 := bstep (se 1 (by rfl) ⟨2862620, by rfl⟩ : syracuseStep 3816827 = 5725241) B5725241
theorem B1129935 : Blo 1128631 1129935 := bstep (se 1 (by rfl) ⟨847451, by rfl⟩ : syracuseStep 1129935 = 1694903) B1694903
theorem B1130095 : Blo 1128631 1130095 := bstep (se 1 (by rfl) ⟨847571, by rfl⟩ : syracuseStep 1130095 = 1695143) B1695143
theorem B1130151 : Blo 1128631 1130151 := bstep (se 1 (by rfl) ⟨847613, by rfl⟩ : syracuseStep 1130151 = 1695227) B1695227
theorem B1130215 : Blo 1128631 1130215 := bstep (se 1 (by rfl) ⟨847661, by rfl⟩ : syracuseStep 1130215 = 1695323) B1695323
theorem B1130271 : Blo 1128631 1130271 := bstep (se 1 (by rfl) ⟨847703, by rfl⟩ : syracuseStep 1130271 = 1695407) B1695407
theorem B1130351 : Blo 1128631 1130351 := bstep (se 1 (by rfl) ⟨847763, by rfl⟩ : syracuseStep 1130351 = 1695527) B1695527
theorem B2146169 : Blo 1128631 2146169 := bstep (se 2 (by rfl) ⟨804813, by rfl⟩ : syracuseStep 2146169 = 1609627) B1609627
theorem B1130407 : Blo 1128631 1130407 := bstep (se 1 (by rfl) ⟨847805, by rfl⟩ : syracuseStep 1130407 = 1695611) B1695611
theorem B2539475 : Blo 1128631 2539475 := bstep (se 1 (by rfl) ⟨1904606, by rfl⟩ : syracuseStep 2539475 = 3809213) B3809213
theorem B2146495 : Blo 1128631 2146495 := bstep (se 1 (by rfl) ⟨1609871, by rfl⟩ : syracuseStep 2146495 = 3219743) B3219743
theorem B1130687 : Blo 1128631 1130687 := bstep (se 1 (by rfl) ⟨848015, by rfl⟩ : syracuseStep 1130687 = 1696031) B1696031
theorem B1130703 : Blo 1128631 1130703 := bstep (se 1 (by rfl) ⟨848027, by rfl⟩ : syracuseStep 1130703 = 1696055) B1696055
theorem B9650411 : Blo 1128631 9650411 := bstep (se 1 (by rfl) ⟨7237808, by rfl⟩ : syracuseStep 9650411 = 14475617) B14475617
theorem B1130751 : Blo 1128631 1130751 := bstep (se 1 (by rfl) ⟨848063, by rfl⟩ : syracuseStep 1130751 = 1696127) B1696127
theorem B1130799 : Blo 1128631 1130799 := bstep (se 1 (by rfl) ⟨848099, by rfl⟩ : syracuseStep 1130799 = 1696199) B1696199
theorem B1131035 : Blo 1128631 1131035 := bstep (se 1 (by rfl) ⟨848276, by rfl⟩ : syracuseStep 1131035 = 1696553) B1696553
theorem B1131039 : Blo 1128631 1131039 := bstep (se 1 (by rfl) ⟨848279, by rfl⟩ : syracuseStep 1131039 = 1696559) B1696559
theorem B1360415 : Blo 1128631 1360415 := bstep (se 1 (by rfl) ⟨1020311, by rfl⟩ : syracuseStep 1360415 = 2040623) B2040623
theorem B1131119 : Blo 1128631 1131119 := bstep (se 1 (by rfl) ⟨848339, by rfl⟩ : syracuseStep 1131119 = 1696679) B1696679
theorem B1131175 : Blo 1128631 1131175 := bstep (se 1 (by rfl) ⟨848381, by rfl⟩ : syracuseStep 1131175 = 1696763) B1696763
theorem B1131215 : Blo 1128631 1131215 := bstep (se 1 (by rfl) ⟨848411, by rfl⟩ : syracuseStep 1131215 = 1696823) B1696823
theorem B5423897 : Blo 1128631 5423897 := bstep (se 2 (by rfl) ⟨2033961, by rfl⟩ : syracuseStep 5423897 = 4067923) B4067923
theorem B1131295 : Blo 1128631 1131295 := bstep (se 1 (by rfl) ⟨848471, by rfl⟩ : syracuseStep 1131295 = 1696943) B1696943
theorem B2147323 : Blo 1128631 2147323 := bstep (se 1 (by rfl) ⟨1610492, by rfl⟩ : syracuseStep 2147323 = 3220985) B3220985
theorem B1131567 : Blo 1128631 1131567 := bstep (se 1 (by rfl) ⟨848675, by rfl⟩ : syracuseStep 1131567 = 1697351) B1697351
theorem B1131631 : Blo 1128631 1131631 := bstep (se 1 (by rfl) ⟨848723, by rfl⟩ : syracuseStep 1131631 = 1697447) B1697447
theorem B6112421 : Blo 1128631 6112421 := bstep (se 4 (by rfl) ⟨573039, by rfl⟩ : syracuseStep 6112421 = 1146079) B1146079
theorem B1131687 : Blo 1128631 1131687 := bstep (se 1 (by rfl) ⟨848765, by rfl⟩ : syracuseStep 1131687 = 1697531) B1697531
theorem B2540735 : Blo 1128631 2540735 := bstep (se 1 (by rfl) ⟨1905551, by rfl⟩ : syracuseStep 2540735 = 3811103) B3811103
theorem B1131711 : Blo 1128631 1131711 := bstep (se 1 (by rfl) ⟨848783, by rfl⟩ : syracuseStep 1131711 = 1697567) B1697567
theorem B1131743 : Blo 1128631 1131743 := bstep (se 1 (by rfl) ⟨848807, by rfl⟩ : syracuseStep 1131743 = 1697615) B1697615
theorem B1131823 : Blo 1128631 1131823 := bstep (se 1 (by rfl) ⟨848867, by rfl⟩ : syracuseStep 1131823 = 1697735) B1697735
theorem B2540879 : Blo 1128631 2540879 := bstep (se 1 (by rfl) ⟨1905659, by rfl⟩ : syracuseStep 2540879 = 3811319) B3811319
theorem B2540969 : Blo 1128631 2540969 := bstep (se 2 (by rfl) ⟨952863, by rfl⟩ : syracuseStep 2540969 = 1905727) B1905727
theorem B2147809 : Blo 1128631 2147809 := bstep (se 2 (by rfl) ⟨805428, by rfl⟩ : syracuseStep 2147809 = 1610857) B1610857
theorem B1132059 : Blo 1128631 1132059 := bstep (se 1 (by rfl) ⟨849044, by rfl⟩ : syracuseStep 1132059 = 1698089) B1698089
theorem B1132063 : Blo 1128631 1132063 := bstep (se 1 (by rfl) ⟨849047, by rfl⟩ : syracuseStep 1132063 = 1698095) B1698095
theorem B1132223 : Blo 1128631 1132223 := bstep (se 1 (by rfl) ⟨849167, by rfl⟩ : syracuseStep 1132223 = 1698335) B1698335
theorem B2541455 : Blo 1128631 2541455 := bstep (se 1 (by rfl) ⟨1906091, by rfl⟩ : syracuseStep 2541455 = 3812183) B3812183
theorem B1132479 : Blo 1128631 1132479 := bstep (se 1 (by rfl) ⟨849359, by rfl⟩ : syracuseStep 1132479 = 1698719) B1698719
theorem B1132511 : Blo 1128631 1132511 := bstep (se 1 (by rfl) ⟨849383, by rfl⟩ : syracuseStep 1132511 = 1698767) B1698767
theorem B1132571 : Blo 1128631 1132571 := bstep (se 1 (by rfl) ⟨849428, by rfl⟩ : syracuseStep 1132571 = 1698857) B1698857
theorem B2541599 : Blo 1128631 2541599 := bstep (se 1 (by rfl) ⟨1906199, by rfl⟩ : syracuseStep 2541599 = 3812399) B3812399
theorem B1132575 : Blo 1128631 1132575 := bstep (se 1 (by rfl) ⟨849431, by rfl⟩ : syracuseStep 1132575 = 1698863) B1698863
theorem B1132591 : Blo 1128631 1132591 := bstep (se 1 (by rfl) ⟨849443, by rfl⟩ : syracuseStep 1132591 = 1698887) B1698887
theorem B5720219 : Blo 1128631 5720219 := bstep (se 1 (by rfl) ⟨4290164, by rfl⟩ : syracuseStep 5720219 = 8580329) B8580329
theorem B2541851 : Blo 1128631 2541851 := bstep (se 1 (by rfl) ⟨1906388, by rfl⟩ : syracuseStep 2541851 = 3812777) B3812777
theorem B4835663 : Blo 1128631 4835663 := bstep (se 1 (by rfl) ⟨3626747, by rfl⟩ : syracuseStep 4835663 = 7253495) B7253495
theorem B2542175 : Blo 1128631 2542175 := bstep (se 1 (by rfl) ⟨1906631, by rfl⟩ : syracuseStep 2542175 = 3813263) B3813263
theorem B2149001 : Blo 1128631 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B2542427 : Blo 1128631 2542427 := bstep (se 1 (by rfl) ⟨1906820, by rfl⟩ : syracuseStep 2542427 = 3813641) B3813641
theorem B4836347 : Blo 1128631 4836347 := bstep (se 1 (by rfl) ⟨3627260, by rfl⟩ : syracuseStep 4836347 = 7254521) B7254521
theorem B3820553 : Blo 1128631 3820553 := bstep (se 2 (by rfl) ⟨1432707, by rfl⟩ : syracuseStep 3820553 = 2865415) B2865415
theorem B4836449 : Blo 1128631 4836449 := bstep (se 2 (by rfl) ⟨1813668, by rfl⟩ : syracuseStep 4836449 = 3627337) B3627337
theorem B2411707 : Blo 1128631 2411707 := bstep (se 1 (by rfl) ⟨1808780, by rfl⟩ : syracuseStep 2411707 = 3617561) B3617561
theorem B16272737 : Blo 1128631 16272737 := bstep (se 2 (by rfl) ⟨6102276, by rfl⟩ : syracuseStep 16272737 = 12204553) B12204553
theorem B2149753 : Blo 1128631 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B2543183 : Blo 1128631 2543183 := bstep (se 1 (by rfl) ⟨1907387, by rfl⟩ : syracuseStep 2543183 = 3814775) B3814775
theorem B6443063 : Blo 1128631 6443063 := bstep (se 1 (by rfl) ⟨4832297, by rfl⟩ : syracuseStep 6443063 = 9664595) B9664595
theorem B2543723 : Blo 1128631 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B2543777 : Blo 1128631 2543777 := bstep (se 2 (by rfl) ⟨953916, by rfl⟩ : syracuseStep 2543777 = 1907833) B1907833
theorem B4346099 : Blo 1128631 4346099 := bstep (se 1 (by rfl) ⟨3259574, by rfl⟩ : syracuseStep 4346099 = 6519149) B6519149
theorem B2543903 : Blo 1128631 2543903 := bstep (se 1 (by rfl) ⟨1907927, by rfl⟩ : syracuseStep 2543903 = 3815855) B3815855
theorem B10998139 : Blo 1128631 10998139 := bstep (se 1 (by rfl) ⟨8248604, by rfl⟩ : syracuseStep 10998139 = 16497209) B16497209
theorem B3822011 : Blo 1128631 3822011 := bstep (se 1 (by rfl) ⟨2866508, by rfl⟩ : syracuseStep 3822011 = 5733017) B5733017
theorem B2413423 : Blo 1128631 2413423 := bstep (se 1 (by rfl) ⟨1810067, by rfl⟩ : syracuseStep 2413423 = 3620135) B3620135
theorem B12243905 : Blo 1128631 12243905 := bstep (se 2 (by rfl) ⟨4591464, by rfl⟩ : syracuseStep 12243905 = 9182929) B9182929
theorem B3822551 : Blo 1128631 3822551 := bstep (se 1 (by rfl) ⟨2866913, by rfl⟩ : syracuseStep 3822551 = 5733827) B5733827
theorem B2544623 : Blo 1128631 2544623 := bstep (se 1 (by rfl) ⟨1908467, by rfl⟩ : syracuseStep 2544623 = 3816935) B3816935
theorem B2446699 : Blo 1128631 2446699 := bstep (se 1 (by rfl) ⟨1835024, by rfl⟩ : syracuseStep 2446699 = 3670049) B3670049
theorem B2545127 : Blo 1128631 2545127 := bstep (se 1 (by rfl) ⟨1908845, by rfl⟩ : syracuseStep 2545127 = 3817691) B3817691
theorem B2545289 : Blo 1128631 2545289 := bstep (se 2 (by rfl) ⟨954483, by rfl⟩ : syracuseStep 2545289 = 1908967) B1908967
theorem B2545307 : Blo 1128631 2545307 := bstep (se 1 (by rfl) ⟨1908980, by rfl⟩ : syracuseStep 2545307 = 3817961) B3817961
theorem B1693511 : Blo 1128631 1693511 := bstep (se 1 (by rfl) ⟨1270133, by rfl⟩ : syracuseStep 1693511 = 2540267) B2540267
theorem B2545505 : Blo 1128631 2545505 := bstep (se 2 (by rfl) ⟨954564, by rfl⟩ : syracuseStep 2545505 = 1909129) B1909129
theorem B2545703 : Blo 1128631 2545703 := bstep (se 1 (by rfl) ⟨1909277, by rfl⟩ : syracuseStep 2545703 = 3818555) B3818555
theorem B9164897 : Blo 1128631 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B2545883 : Blo 1128631 2545883 := bstep (se 1 (by rfl) ⟨1909412, by rfl⟩ : syracuseStep 2545883 = 3818825) B3818825
theorem B5429587 : Blo 1128631 5429587 := bstep (se 1 (by rfl) ⟨4072190, by rfl⟩ : syracuseStep 5429587 = 8144381) B8144381
theorem B7231841 : Blo 1128631 7231841 := bstep (se 2 (by rfl) ⟨2711940, by rfl⟩ : syracuseStep 7231841 = 5423881) B5423881
theorem B1694111 : Blo 1128631 1694111 := bstep (se 1 (by rfl) ⟨1270583, by rfl⟩ : syracuseStep 1694111 = 2541167) B2541167
theorem B2546081 : Blo 1128631 2546081 := bstep (se 2 (by rfl) ⟨954780, by rfl⟩ : syracuseStep 2546081 = 1909561) B1909561
theorem B1694183 : Blo 1128631 1694183 := bstep (se 1 (by rfl) ⟨1270637, by rfl⟩ : syracuseStep 1694183 = 2541275) B2541275
theorem B2546153 : Blo 1128631 2546153 := bstep (se 2 (by rfl) ⟨954807, by rfl⟩ : syracuseStep 2546153 = 1909615) B1909615
theorem B4414397 : Blo 1128631 4414397 := bstep (se 3 (by rfl) ⟨827699, by rfl⟩ : syracuseStep 4414397 = 1655399) B1655399
theorem B11623427 : Blo 1128631 11623427 := bstep (se 1 (by rfl) ⟨8717570, by rfl⟩ : syracuseStep 11623427 = 17435141) B17435141
theorem B1694927 : Blo 1128631 1694927 := bstep (se 1 (by rfl) ⟨1271195, by rfl⟩ : syracuseStep 1694927 = 2542391) B2542391
theorem B1695047 : Blo 1128631 1695047 := bstep (se 1 (by rfl) ⟨1271285, by rfl⟩ : syracuseStep 1695047 = 2542571) B2542571
theorem B8150381 : Blo 1128631 8150381 := bstep (se 3 (by rfl) ⟨1528196, by rfl⟩ : syracuseStep 8150381 = 3056393) B3056393
theorem B1695209 : Blo 1128631 1695209 := bstep (se 2 (by rfl) ⟨635703, by rfl⟩ : syracuseStep 1695209 = 1271407) B1271407
theorem B5430817 : Blo 1128631 5430817 := bstep (se 2 (by rfl) ⟨2036556, by rfl⟩ : syracuseStep 5430817 = 4073113) B4073113
theorem B1695353 : Blo 1128631 1695353 := bstep (se 2 (by rfl) ⟨635757, by rfl⟩ : syracuseStep 1695353 = 1271515) B1271515
theorem B7233299 : Blo 1128631 7233299 := bstep (se 1 (by rfl) ⟨5424974, by rfl⟩ : syracuseStep 7233299 = 10849949) B10849949
theorem B1695599 : Blo 1128631 1695599 := bstep (se 1 (by rfl) ⟨1271699, by rfl⟩ : syracuseStep 1695599 = 2543399) B2543399
theorem B2547611 : Blo 1128631 2547611 := bstep (se 1 (by rfl) ⟨1910708, by rfl⟩ : syracuseStep 2547611 = 3821417) B3821417
theorem B1269967 : Blo 1128631 1269967 := bstep (se 1 (by rfl) ⟨952475, by rfl⟩ : syracuseStep 1269967 = 1904951) B1904951
theorem B6119705 : Blo 1128631 6119705 := bstep (se 2 (by rfl) ⟨2294889, by rfl⟩ : syracuseStep 6119705 = 4589779) B4589779
theorem B2548025 : Blo 1128631 2548025 := bstep (se 2 (by rfl) ⟨955509, by rfl⟩ : syracuseStep 2548025 = 1911019) B1911019
theorem B1696283 : Blo 1128631 1696283 := bstep (se 1 (by rfl) ⟨1272212, by rfl⟩ : syracuseStep 1696283 = 2544425) B2544425
theorem B1696463 : Blo 1128631 1696463 := bstep (se 1 (by rfl) ⟨1272347, by rfl⟩ : syracuseStep 1696463 = 2544695) B2544695
theorem B1696475 : Blo 1128631 1696475 := bstep (se 1 (by rfl) ⟨1272356, by rfl⟩ : syracuseStep 1696475 = 2544713) B2544713
theorem B7234505 : Blo 1128631 7234505 := bstep (se 2 (by rfl) ⟨2712939, by rfl⟩ : syracuseStep 7234505 = 5425879) B5425879
theorem B1270831 : Blo 1128631 1270831 := bstep (se 1 (by rfl) ⟨953123, by rfl⟩ : syracuseStep 1270831 = 1906247) B1906247
theorem B4187209 : Blo 1128631 4187209 := bstep (se 2 (by rfl) ⟨1570203, by rfl⟩ : syracuseStep 4187209 = 3140407) B3140407
theorem B5727347 : Blo 1128631 5727347 := bstep (se 1 (by rfl) ⟨4295510, by rfl⟩ : syracuseStep 5727347 = 8591021) B8591021
theorem B1696889 : Blo 1128631 1696889 := bstep (se 2 (by rfl) ⟨636333, by rfl⟩ : syracuseStep 1696889 = 1272667) B1272667
theorem B1270975 : Blo 1128631 1270975 := bstep (se 1 (by rfl) ⟨953231, by rfl⟩ : syracuseStep 1270975 = 1906463) B1906463
theorem B1271119 : Blo 1128631 1271119 := bstep (se 1 (by rfl) ⟨953339, by rfl⟩ : syracuseStep 1271119 = 1906679) B1906679
theorem B4285943 : Blo 1128631 4285943 := bstep (se 1 (by rfl) ⟨3214457, by rfl⟩ : syracuseStep 4285943 = 6428915) B6428915
theorem B29025863 : Blo 1128631 29025863 := bstep (se 1 (by rfl) ⟨21769397, by rfl⟩ : syracuseStep 29025863 = 43538795) B43538795
theorem B14509651 : Blo 1128631 14509651 := bstep (se 1 (by rfl) ⟨10882238, by rfl⟩ : syracuseStep 14509651 = 21764477) B21764477
theorem B5728157 : Blo 1128631 5728157 := bstep (se 3 (by rfl) ⟨1074029, by rfl⟩ : syracuseStep 5728157 = 2148059) B2148059
theorem B14510015 : Blo 1128631 14510015 := bstep (se 1 (by rfl) ⟨10882511, by rfl⟩ : syracuseStep 14510015 = 21765023) B21765023
theorem B1697759 : Blo 1128631 1697759 := bstep (se 1 (by rfl) ⟨1273319, by rfl⟩ : syracuseStep 1697759 = 2546639) B2546639
theorem B118908899 : Blo 1128631 118908899 := bstep (se 1 (by rfl) ⟨89181674, by rfl⟩ : syracuseStep 118908899 = 178363349) B178363349
theorem B1697771 : Blo 1128631 1697771 := bstep (se 1 (by rfl) ⟨1273328, by rfl⟩ : syracuseStep 1697771 = 2546657) B2546657
theorem B1697819 : Blo 1128631 1697819 := bstep (se 1 (by rfl) ⟨1273364, by rfl⟩ : syracuseStep 1697819 = 2546729) B2546729
theorem B1271839 : Blo 1128631 1271839 := bstep (se 1 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 1271839 = 1907759) B1907759
theorem B1272091 : Blo 1128631 1272091 := bstep (se 1 (by rfl) ⟨954068, by rfl⟩ : syracuseStep 1272091 = 1908137) B1908137
theorem B1698185 : Blo 1128631 1698185 := bstep (se 2 (by rfl) ⟨636819, by rfl⟩ : syracuseStep 1698185 = 1273639) B1273639
theorem B4286945 : Blo 1128631 4286945 := bstep (se 2 (by rfl) ⟨1607604, by rfl⟩ : syracuseStep 4286945 = 3215209) B3215209
theorem B5433875 : Blo 1128631 5433875 := bstep (se 1 (by rfl) ⟨4075406, by rfl⟩ : syracuseStep 5433875 = 8150813) B8150813
theorem B12577433 : Blo 1128631 12577433 := bstep (se 2 (by rfl) ⟨4716537, by rfl⟩ : syracuseStep 12577433 = 9433075) B9433075
theorem B5728967 : Blo 1128631 5728967 := bstep (se 1 (by rfl) ⟨4296725, by rfl⟩ : syracuseStep 5728967 = 8593451) B8593451
theorem B23194957 : Blo 1128631 23194957 := bstep (se 3 (by rfl) ⟨4349054, by rfl⟩ : syracuseStep 23194957 = 8698109) B8698109
theorem B1273243 : Blo 1128631 1273243 := bstep (se 1 (by rfl) ⟨954932, by rfl⟩ : syracuseStep 1273243 = 1909865) B1909865
theorem B5795309 : Blo 1128631 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B14708567 : Blo 1128631 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B4288585 : Blo 1128631 4288585 := bstep (se 2 (by rfl) ⟨1608219, by rfl⟩ : syracuseStep 4288585 = 3216439) B3216439
theorem B2716217 : Blo 1128631 2716217 := bstep (se 2 (by rfl) ⟨1018581, by rfl⟩ : syracuseStep 2716217 = 2037163) B2037163
theorem B8583731 : Blo 1128631 8583731 := bstep (se 1 (by rfl) ⟨6437798, by rfl⟩ : syracuseStep 8583731 = 12875597) B12875597
theorem B4291487 : Blo 1128631 4291487 := bstep (se 1 (by rfl) ⟨3218615, by rfl⟩ : syracuseStep 4291487 = 6437231) B6437231
theorem B123829397 : Blo 1128631 123829397 := bstep (se 6 (by rfl) ⟨2902251, by rfl⟩ : syracuseStep 123829397 = 5804503) B5804503
theorem B9798425 : Blo 1128631 9798425 := bstep (se 2 (by rfl) ⟨3674409, by rfl⟩ : syracuseStep 9798425 = 7348819) B7348819
theorem B2754523 : Blo 1128631 2754523 := bstep (se 1 (by rfl) ⟨2065892, by rfl⟩ : syracuseStep 2754523 = 4131785) B4131785
theorem B10848491 : Blo 1128631 10848491 := bstep (se 1 (by rfl) ⟨8136368, by rfl⟩ : syracuseStep 10848491 = 16272737) B16272737
theorem B7735727 : Blo 1128631 7735727 := bstep (se 1 (by rfl) ⟨5801795, by rfl⟩ : syracuseStep 7735727 = 11603591) B11603591
theorem B4295375 : Blo 1128631 4295375 := bstep (se 1 (by rfl) ⟨3221531, by rfl⟩ : syracuseStep 4295375 = 6443063) B6443063
theorem B8162603 : Blo 1128631 8162603 := bstep (se 1 (by rfl) ⟨6121952, by rfl⟩ : syracuseStep 8162603 = 12243905) B12243905
theorem B3215551 : Blo 1128631 3215551 := bstep (se 1 (by rfl) ⟨2411663, by rfl⟩ : syracuseStep 3215551 = 4823327) B4823327
theorem B4821227 : Blo 1128631 4821227 := bstep (se 1 (by rfl) ⟨3615920, by rfl⟩ : syracuseStep 4821227 = 7231841) B7231841
theorem B3215609 : Blo 1128631 3215609 := bstep (se 2 (by rfl) ⟨1205853, by rfl⟩ : syracuseStep 3215609 = 2411707) B2411707
theorem B1905403 : Blo 1128631 1905403 := bstep (se 1 (by rfl) ⟨1429052, by rfl⟩ : syracuseStep 1905403 = 2858105) B2858105
theorem B4822199 : Blo 1128631 4822199 := bstep (se 1 (by rfl) ⟨3616649, by rfl⟩ : syracuseStep 4822199 = 7233299) B7233299
theorem B6428231 : Blo 1128631 6428231 := bstep (se 1 (by rfl) ⟨4821173, by rfl⟩ : syracuseStep 6428231 = 9642347) B9642347
theorem B13768555 : Blo 1128631 13768555 := bstep (se 1 (by rfl) ⟨10326416, by rfl⟩ : syracuseStep 13768555 = 20652833) B20652833
theorem B4823003 : Blo 1128631 4823003 := bstep (se 1 (by rfl) ⟨3617252, by rfl⟩ : syracuseStep 4823003 = 7234505) B7234505
theorem B8591507 : Blo 1128631 8591507 := bstep (se 1 (by rfl) ⟨6443630, by rfl⟩ : syracuseStep 8591507 = 12887261) B12887261
theorem B2857295 : Blo 1128631 2857295 := bstep (se 1 (by rfl) ⟨2142971, by rfl⟩ : syracuseStep 2857295 = 4285943) B4285943
theorem B3217897 : Blo 1128631 3217897 := bstep (se 2 (by rfl) ⟨1206711, by rfl⟩ : syracuseStep 3217897 = 2413423) B2413423
theorem B9673343 : Blo 1128631 9673343 := bstep (se 1 (by rfl) ⟨7255007, by rfl⟩ : syracuseStep 9673343 = 14510015) B14510015
theorem B79272599 : Blo 1128631 79272599 := bstep (se 1 (by rfl) ⟨59454449, by rfl⟩ : syracuseStep 79272599 = 118908899) B118908899
theorem B134159285 : Blo 1128631 134159285 := bstep (se 5 (by rfl) ⟨6288716, by rfl⟩ : syracuseStep 134159285 = 12577433) B12577433
theorem B2857963 : Blo 1128631 2857963 := bstep (se 1 (by rfl) ⟨2143472, by rfl⟩ : syracuseStep 2857963 = 4286945) B4286945
theorem B1907887 : Blo 1128631 1907887 := bstep (se 1 (by rfl) ⟨1430915, by rfl⟩ : syracuseStep 1907887 = 2861831) B2861831
theorem B11771725 : Blo 1128631 11771725 := bstep (se 3 (by rfl) ⟨2207198, by rfl⟩ : syracuseStep 11771725 = 4414397) B4414397
theorem B9805711 : Blo 1128631 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B21700507 : Blo 1128631 21700507 := bstep (se 1 (by rfl) ⟨16275380, by rfl⟩ : syracuseStep 21700507 = 32550761) B32550761
theorem B3219355 : Blo 1128631 3219355 := bstep (se 1 (by rfl) ⟨2414516, by rfl⟩ : syracuseStep 3219355 = 4829033) B4829033
theorem B3809267 : Blo 1128631 3809267 := bstep (se 1 (by rfl) ⟨2856950, by rfl⟩ : syracuseStep 3809267 = 5713901) B5713901
theorem B21766481 : Blo 1128631 21766481 := bstep (se 2 (by rfl) ⟨8162430, by rfl⟩ : syracuseStep 21766481 = 16324861) B16324861
theorem B1810811 : Blo 1128631 1810811 := bstep (se 1 (by rfl) ⟨1358108, by rfl⟩ : syracuseStep 1810811 = 2716217) B2716217
theorem B2859401 : Blo 1128631 2859401 := bstep (se 2 (by rfl) ⟨1072275, by rfl⟩ : syracuseStep 2859401 = 2144551) B2144551
theorem B3809807 : Blo 1128631 3809807 := bstep (se 1 (by rfl) ⟨2857355, by rfl⟩ : syracuseStep 3809807 = 5714711) B5714711
theorem B3220175 : Blo 1128631 3220175 := bstep (se 1 (by rfl) ⟨2415131, by rfl⟩ : syracuseStep 3220175 = 4830263) B4830263
theorem B2859745 : Blo 1128631 2859745 := bstep (se 2 (by rfl) ⟨1072404, by rfl⟩ : syracuseStep 2859745 = 2144809) B2144809
theorem B1909595 : Blo 1128631 1909595 := bstep (se 1 (by rfl) ⟨1432196, by rfl⟩ : syracuseStep 1909595 = 2864393) B2864393
theorem B8594423 : Blo 1128631 8594423 := bstep (se 1 (by rfl) ⟨6445817, by rfl⟩ : syracuseStep 8594423 = 12891635) B12891635
theorem B1909919 : Blo 1128631 1909919 := bstep (se 1 (by rfl) ⟨1432439, by rfl⟩ : syracuseStep 1909919 = 2864879) B2864879
theorem B3810887 : Blo 1128631 3810887 := bstep (se 1 (by rfl) ⟨2858165, by rfl⟩ : syracuseStep 3810887 = 5716331) B5716331
theorem B3221167 : Blo 1128631 3221167 := bstep (se 1 (by rfl) ⟨2415875, by rfl⟩ : syracuseStep 3221167 = 4831751) B4831751
theorem B1910567 : Blo 1128631 1910567 := bstep (se 1 (by rfl) ⟨1432925, by rfl⟩ : syracuseStep 1910567 = 2865851) B2865851
theorem B2860991 : Blo 1128631 2860991 := bstep (se 1 (by rfl) ⟨2145743, by rfl⟩ : syracuseStep 2860991 = 4291487) B4291487
theorem B8595395 : Blo 1128631 8595395 := bstep (se 1 (by rfl) ⟨6446546, by rfl⟩ : syracuseStep 8595395 = 12893093) B12893093
theorem B82552931 : Blo 1128631 82552931 := bstep (se 1 (by rfl) ⟨61914698, by rfl⟩ : syracuseStep 82552931 = 123829397) B123829397
theorem B6433607 : Blo 1128631 6433607 := bstep (se 1 (by rfl) ⟨4825205, by rfl⟩ : syracuseStep 6433607 = 9650411) B9650411
theorem B2861993 : Blo 1128631 2861993 := bstep (se 2 (by rfl) ⟨1073247, by rfl⟩ : syracuseStep 2861993 = 2146495) B2146495
theorem B10857635 : Blo 1128631 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B3615931 : Blo 1128631 3615931 := bstep (se 1 (by rfl) ⟨2711948, by rfl⟩ : syracuseStep 3615931 = 5423897) B5423897
theorem B4074947 : Blo 1128631 4074947 := bstep (se 1 (by rfl) ⟨3056210, by rfl⟩ : syracuseStep 4074947 = 6112421) B6112421
theorem B2863097 : Blo 1128631 2863097 := bstep (se 2 (by rfl) ⟨1073661, by rfl⟩ : syracuseStep 2863097 = 2147323) B2147323
theorem B5582945 : Blo 1128631 5582945 := bstep (se 2 (by rfl) ⟨2093604, by rfl⟩ : syracuseStep 5582945 = 4187209) B4187209
theorem B3813479 : Blo 1128631 3813479 := bstep (se 1 (by rfl) ⟨2860109, by rfl⟩ : syracuseStep 3813479 = 5720219) B5720219
theorem B4829291 : Blo 1128631 4829291 := bstep (se 1 (by rfl) ⟨3621968, by rfl⟩ : syracuseStep 4829291 = 7243937) B7243937
theorem B3223775 : Blo 1128631 3223775 := bstep (se 1 (by rfl) ⟨2417831, by rfl⟩ : syracuseStep 3223775 = 4835663) B4835663
theorem B2863745 : Blo 1128631 2863745 := bstep (se 2 (by rfl) ⟨1073904, by rfl⟩ : syracuseStep 2863745 = 2147809) B2147809
theorem B3224231 : Blo 1128631 3224231 := bstep (se 1 (by rfl) ⟨2418173, by rfl⟩ : syracuseStep 3224231 = 4836347) B4836347
theorem B3224299 : Blo 1128631 3224299 := bstep (se 1 (by rfl) ⟨2418224, by rfl⟩ : syracuseStep 3224299 = 4836449) B4836449
theorem B19346201 : Blo 1128631 19346201 := bstep (se 2 (by rfl) ⟨7254825, by rfl⟩ : syracuseStep 19346201 = 14509651) B14509651
theorem B2864555 : Blo 1128631 2864555 := bstep (se 1 (by rfl) ⟨2148416, by rfl⟩ : syracuseStep 2864555 = 4296833) B4296833
theorem B2897399 : Blo 1128631 2897399 := bstep (se 1 (by rfl) ⟨2173049, by rfl⟩ : syracuseStep 2897399 = 4346099) B4346099
theorem B5158525 : Blo 1128631 5158525 := bstep (se 3 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 5158525 = 1934447) B1934447
theorem B1357931 : Blo 1128631 1357931 := bstep (se 1 (by rfl) ⟨1018448, by rfl⟩ : syracuseStep 1357931 = 2036897) B2036897
theorem B1129007 : Blo 1128631 1129007 := bstep (se 1 (by rfl) ⟨846755, by rfl⟩ : syracuseStep 1129007 = 1693511) B1693511
theorem B2865719 : Blo 1128631 2865719 := bstep (se 1 (by rfl) ⟨2149289, by rfl⟩ : syracuseStep 2865719 = 4298579) B4298579
theorem B140950169 : Blo 1128631 140950169 := bstep (se 2 (by rfl) ⟨52856313, by rfl⟩ : syracuseStep 140950169 = 105712627) B105712627
theorem B6109931 : Blo 1128631 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B1129407 : Blo 1128631 1129407 := bstep (se 1 (by rfl) ⟨847055, by rfl⟩ : syracuseStep 1129407 = 1694111) B1694111
theorem B1129455 : Blo 1128631 1129455 := bstep (se 1 (by rfl) ⟨847091, by rfl⟩ : syracuseStep 1129455 = 1694183) B1694183
theorem B2866337 : Blo 1128631 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B7748951 : Blo 1128631 7748951 := bstep (se 1 (by rfl) ⟨5811713, by rfl⟩ : syracuseStep 7748951 = 11623427) B11623427
theorem B1129951 : Blo 1128631 1129951 := bstep (se 1 (by rfl) ⟨847463, by rfl⟩ : syracuseStep 1129951 = 1694927) B1694927
theorem B1130031 : Blo 1128631 1130031 := bstep (se 1 (by rfl) ⟨847523, by rfl⟩ : syracuseStep 1130031 = 1695047) B1695047
theorem B12861017 : Blo 1128631 12861017 := bstep (se 2 (by rfl) ⟨4822881, by rfl⟩ : syracuseStep 12861017 = 9645763) B9645763
theorem B1130139 : Blo 1128631 1130139 := bstep (se 1 (by rfl) ⟨847604, by rfl⟩ : syracuseStep 1130139 = 1695209) B1695209
theorem B1130235 : Blo 1128631 1130235 := bstep (se 1 (by rfl) ⟨847676, by rfl⟩ : syracuseStep 1130235 = 1695353) B1695353
theorem B5717789 : Blo 1128631 5717789 := bstep (se 3 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 5717789 = 2144171) B2144171
theorem B3817313 : Blo 1128631 3817313 := bstep (se 2 (by rfl) ⟨1431492, by rfl⟩ : syracuseStep 3817313 = 2862985) B2862985
theorem B1130399 : Blo 1128631 1130399 := bstep (se 1 (by rfl) ⟨847799, by rfl⟩ : syracuseStep 1130399 = 1695599) B1695599
theorem B5718113 : Blo 1128631 5718113 := bstep (se 2 (by rfl) ⟨2144292, by rfl⟩ : syracuseStep 5718113 = 4288585) B4288585
theorem B4079803 : Blo 1128631 4079803 := bstep (se 1 (by rfl) ⟨3059852, by rfl⟩ : syracuseStep 4079803 = 6119705) B6119705
theorem B2539727 : Blo 1128631 2539727 := bstep (se 1 (by rfl) ⟨1904795, by rfl⟩ : syracuseStep 2539727 = 3809591) B3809591
theorem B5882077 : Blo 1128631 5882077 := bstep (se 3 (by rfl) ⟨1102889, by rfl⟩ : syracuseStep 5882077 = 2205779) B2205779
theorem B1130855 : Blo 1128631 1130855 := bstep (se 1 (by rfl) ⟨848141, by rfl⟩ : syracuseStep 1130855 = 1696283) B1696283
theorem B1130975 : Blo 1128631 1130975 := bstep (se 1 (by rfl) ⟨848231, by rfl⟩ : syracuseStep 1130975 = 1696463) B1696463
theorem B1130983 : Blo 1128631 1130983 := bstep (se 1 (by rfl) ⟨848237, by rfl⟩ : syracuseStep 1130983 = 1696475) B1696475
theorem B14664185 : Blo 1128631 14664185 := bstep (se 2 (by rfl) ⟨5499069, by rfl⟩ : syracuseStep 14664185 = 10998139) B10998139
theorem B3818231 : Blo 1128631 3818231 := bstep (se 1 (by rfl) ⟨2863673, by rfl⟩ : syracuseStep 3818231 = 5727347) B5727347
theorem B1131259 : Blo 1128631 1131259 := bstep (se 1 (by rfl) ⟨848444, by rfl⟩ : syracuseStep 1131259 = 1696889) B1696889
theorem B19350575 : Blo 1128631 19350575 := bstep (se 1 (by rfl) ⟨14512931, by rfl⟩ : syracuseStep 19350575 = 29025863) B29025863
theorem B3818771 : Blo 1128631 3818771 := bstep (se 1 (by rfl) ⟨2864078, by rfl⟩ : syracuseStep 3818771 = 5728157) B5728157
theorem B1131839 : Blo 1128631 1131839 := bstep (se 1 (by rfl) ⟨848879, by rfl⟩ : syracuseStep 1131839 = 1697759) B1697759
theorem B1131847 : Blo 1128631 1131847 := bstep (se 1 (by rfl) ⟨848885, by rfl⟩ : syracuseStep 1131847 = 1697771) B1697771
theorem B1131879 : Blo 1128631 1131879 := bstep (se 1 (by rfl) ⟨848909, by rfl⟩ : syracuseStep 1131879 = 1697819) B1697819
theorem B148817321 : Blo 1128631 148817321 := bstep (se 2 (by rfl) ⟨55806495, by rfl⟩ : syracuseStep 148817321 = 111612991) B111612991
theorem B1132123 : Blo 1128631 1132123 := bstep (se 1 (by rfl) ⟨849092, by rfl⟩ : syracuseStep 1132123 = 1698185) B1698185
theorem B3622583 : Blo 1128631 3622583 := bstep (se 1 (by rfl) ⟨2716937, by rfl⟩ : syracuseStep 3622583 = 5433875) B5433875
theorem B3819311 : Blo 1128631 3819311 := bstep (se 1 (by rfl) ⟨2864483, by rfl⟩ : syracuseStep 3819311 = 5728967) B5728967
theorem B3262265 : Blo 1128631 3262265 := bstep (se 2 (by rfl) ⟨1223349, by rfl⟩ : syracuseStep 3262265 = 2446699) B2446699
theorem B2541545 : Blo 1128631 2541545 := bstep (se 2 (by rfl) ⟨953079, by rfl⟩ : syracuseStep 2541545 = 1906159) B1906159
theorem B3262447 : Blo 1128631 3262447 := bstep (se 1 (by rfl) ⟨2446835, by rfl⟩ : syracuseStep 3262447 = 4893671) B4893671
theorem B2542031 : Blo 1128631 2542031 := bstep (se 1 (by rfl) ⟨1906523, by rfl⟩ : syracuseStep 2542031 = 3813047) B3813047
theorem B2542121 : Blo 1128631 2542121 := bstep (se 2 (by rfl) ⟨953295, by rfl⟩ : syracuseStep 2542121 = 1906591) B1906591
theorem B2543003 : Blo 1128631 2543003 := bstep (se 1 (by rfl) ⟨1907252, by rfl⟩ : syracuseStep 2543003 = 3814505) B3814505
theorem B6442537 : Blo 1128631 6442537 := bstep (se 2 (by rfl) ⟨2415951, by rfl⟩ : syracuseStep 6442537 = 4831903) B4831903
theorem B1429103 : Blo 1128631 1429103 := bstep (se 1 (by rfl) ⟨1071827, by rfl⟩ : syracuseStep 1429103 = 2143655) B2143655
theorem B14700665 : Blo 1128631 14700665 := bstep (se 2 (by rfl) ⟨5512749, by rfl⟩ : syracuseStep 14700665 = 11025499) B11025499
theorem B2412671 : Blo 1128631 2412671 := bstep (se 1 (by rfl) ⟨1809503, by rfl⟩ : syracuseStep 2412671 = 3619007) B3619007
theorem B1429807 : Blo 1128631 1429807 := bstep (se 1 (by rfl) ⟨1072355, by rfl⟩ : syracuseStep 1429807 = 2144711) B2144711
theorem B5722487 : Blo 1128631 5722487 := bstep (se 1 (by rfl) ⟨4291865, by rfl⟩ : syracuseStep 5722487 = 8583731) B8583731
theorem B2544551 : Blo 1128631 2544551 := bstep (se 1 (by rfl) ⟨1908413, by rfl⟩ : syracuseStep 2544551 = 3816827) B3816827
theorem B1430779 : Blo 1128631 1430779 := bstep (se 1 (by rfl) ⟨1073084, by rfl⟩ : syracuseStep 1430779 = 2146169) B2146169
theorem B1692983 : Blo 1128631 1692983 := bstep (se 1 (by rfl) ⟨1269737, by rfl⟩ : syracuseStep 1692983 = 2539475) B2539475
theorem B14505551 : Blo 1128631 14505551 := bstep (se 1 (by rfl) ⟨10879163, by rfl⟩ : syracuseStep 14505551 = 21758327) B21758327
theorem B1693289 : Blo 1128631 1693289 := bstep (se 2 (by rfl) ⟨634983, by rfl⟩ : syracuseStep 1693289 = 1269967) B1269967
theorem B10442459 : Blo 1128631 10442459 := bstep (se 1 (by rfl) ⟨7831844, by rfl⟩ : syracuseStep 10442459 = 15663689) B15663689
theorem B1693823 : Blo 1128631 1693823 := bstep (se 1 (by rfl) ⟨1270367, by rfl⟩ : syracuseStep 1693823 = 2540735) B2540735
theorem B6445271 : Blo 1128631 6445271 := bstep (se 1 (by rfl) ⟨4833953, by rfl⟩ : syracuseStep 6445271 = 9667907) B9667907
theorem B1693919 : Blo 1128631 1693919 := bstep (se 1 (by rfl) ⟨1270439, by rfl⟩ : syracuseStep 1693919 = 2540879) B2540879
theorem B1693979 : Blo 1128631 1693979 := bstep (se 1 (by rfl) ⟨1270484, by rfl⟩ : syracuseStep 1693979 = 2540969) B2540969
theorem B1694303 : Blo 1128631 1694303 := bstep (se 1 (by rfl) ⟨1270727, by rfl⟩ : syracuseStep 1694303 = 2541455) B2541455
theorem B6445727 : Blo 1128631 6445727 := bstep (se 1 (by rfl) ⟨4834295, by rfl⟩ : syracuseStep 6445727 = 9668591) B9668591
theorem B1694399 : Blo 1128631 1694399 := bstep (se 1 (by rfl) ⟨1270799, by rfl⟩ : syracuseStep 1694399 = 2541599) B2541599
theorem B1694441 : Blo 1128631 1694441 := bstep (se 2 (by rfl) ⟨635415, by rfl⟩ : syracuseStep 1694441 = 1270831) B1270831
theorem B3627773 : Blo 1128631 3627773 := bstep (se 3 (by rfl) ⟨680207, by rfl⟩ : syracuseStep 3627773 = 1360415) B1360415
theorem B1694567 : Blo 1128631 1694567 := bstep (se 1 (by rfl) ⟨1270925, by rfl⟩ : syracuseStep 1694567 = 2541851) B2541851
theorem B1694633 : Blo 1128631 1694633 := bstep (se 2 (by rfl) ⟨635487, by rfl⟩ : syracuseStep 1694633 = 1270975) B1270975
theorem B6970319 : Blo 1128631 6970319 := bstep (se 1 (by rfl) ⟨5227739, by rfl⟩ : syracuseStep 6970319 = 10455479) B10455479
theorem B1694783 : Blo 1128631 1694783 := bstep (se 1 (by rfl) ⟨1271087, by rfl⟩ : syracuseStep 1694783 = 2542175) B2542175
theorem B1432667 : Blo 1128631 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B1694825 : Blo 1128631 1694825 := bstep (se 2 (by rfl) ⟨635559, by rfl⟩ : syracuseStep 1694825 = 1271119) B1271119
theorem B1694951 : Blo 1128631 1694951 := bstep (se 1 (by rfl) ⟨1271213, by rfl⟩ : syracuseStep 1694951 = 2542427) B2542427
theorem B2547017 : Blo 1128631 2547017 := bstep (se 2 (by rfl) ⟨955131, by rfl⟩ : syracuseStep 2547017 = 1910263) B1910263
theorem B2547035 : Blo 1128631 2547035 := bstep (se 1 (by rfl) ⟨1910276, by rfl⟩ : syracuseStep 2547035 = 3820553) B3820553
theorem B59530733 : Blo 1128631 59530733 := bstep (se 3 (by rfl) ⟨11162012, by rfl⟩ : syracuseStep 59530733 = 22324025) B22324025
theorem B9789007 : Blo 1128631 9789007 := bstep (se 1 (by rfl) ⟨7341755, by rfl⟩ : syracuseStep 9789007 = 14683511) B14683511
theorem B1695455 : Blo 1128631 1695455 := bstep (se 1 (by rfl) ⟨1271591, by rfl⟩ : syracuseStep 1695455 = 2543183) B2543183
theorem B1695785 : Blo 1128631 1695785 := bstep (se 2 (by rfl) ⟨635919, by rfl⟩ : syracuseStep 1695785 = 1271839) B1271839
theorem B1269823 : Blo 1128631 1269823 := bstep (se 1 (by rfl) ⟨952367, by rfl⟩ : syracuseStep 1269823 = 1904735) B1904735
theorem B1695815 : Blo 1128631 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B1695851 : Blo 1128631 1695851 := bstep (se 1 (by rfl) ⟨1271888, by rfl⟩ : syracuseStep 1695851 = 2543777) B2543777
theorem B4579517 : Blo 1128631 4579517 := bstep (se 3 (by rfl) ⟨858659, by rfl⟩ : syracuseStep 4579517 = 1717319) B1717319
theorem B1695935 : Blo 1128631 1695935 := bstep (se 1 (by rfl) ⟨1271951, by rfl⟩ : syracuseStep 1695935 = 2543903) B2543903
theorem B3531005 : Blo 1128631 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B2548007 : Blo 1128631 2548007 := bstep (se 1 (by rfl) ⟨1911005, by rfl⟩ : syracuseStep 2548007 = 3822011) B3822011
theorem B1696121 : Blo 1128631 1696121 := bstep (se 2 (by rfl) ⟨636045, by rfl⟩ : syracuseStep 1696121 = 1272091) B1272091
theorem B51569153 : Blo 1128631 51569153 := bstep (se 2 (by rfl) ⟨19338432, by rfl⟩ : syracuseStep 51569153 = 38676865) B38676865
theorem B2548367 : Blo 1128631 2548367 := bstep (se 1 (by rfl) ⟨1911275, by rfl⟩ : syracuseStep 2548367 = 3822551) B3822551
theorem B1696415 : Blo 1128631 1696415 := bstep (se 1 (by rfl) ⟨1272311, by rfl⟩ : syracuseStep 1696415 = 2544623) B2544623
theorem B2548385 : Blo 1128631 2548385 := bstep (se 2 (by rfl) ⟨955644, by rfl⟩ : syracuseStep 2548385 = 1911289) B1911289
theorem B5727023 : Blo 1128631 5727023 := bstep (se 1 (by rfl) ⟨4295267, by rfl⟩ : syracuseStep 5727023 = 8590535) B8590535
theorem B1270687 : Blo 1128631 1270687 := bstep (se 1 (by rfl) ⟨953015, by rfl⟩ : syracuseStep 1270687 = 1906031) B1906031
theorem B1696751 : Blo 1128631 1696751 := bstep (se 1 (by rfl) ⟨1272563, by rfl⟩ : syracuseStep 1696751 = 2545127) B2545127
theorem B6448187 : Blo 1128631 6448187 := bstep (se 1 (by rfl) ⟨4836140, by rfl⟩ : syracuseStep 6448187 = 9672281) B9672281
theorem B1696859 : Blo 1128631 1696859 := bstep (se 1 (by rfl) ⟨1272644, by rfl⟩ : syracuseStep 1696859 = 2545289) B2545289
theorem B1696871 : Blo 1128631 1696871 := bstep (se 1 (by rfl) ⟨1272653, by rfl⟩ : syracuseStep 1696871 = 2545307) B2545307
theorem B1697003 : Blo 1128631 1697003 := bstep (se 1 (by rfl) ⟨1272752, by rfl⟩ : syracuseStep 1697003 = 2545505) B2545505
theorem B1697135 : Blo 1128631 1697135 := bstep (se 1 (by rfl) ⟨1272851, by rfl⟩ : syracuseStep 1697135 = 2545703) B2545703
theorem B1697255 : Blo 1128631 1697255 := bstep (se 1 (by rfl) ⟨1272941, by rfl⟩ : syracuseStep 1697255 = 2545883) B2545883
theorem B1697387 : Blo 1128631 1697387 := bstep (se 1 (by rfl) ⟨1273040, by rfl⟩ : syracuseStep 1697387 = 2546081) B2546081
theorem B1697435 : Blo 1128631 1697435 := bstep (se 1 (by rfl) ⟨1273076, by rfl⟩ : syracuseStep 1697435 = 2546153) B2546153
theorem B5727995 : Blo 1128631 5727995 := bstep (se 1 (by rfl) ⟨4295996, by rfl⟩ : syracuseStep 5727995 = 8591993) B8591993
theorem B30926609 : Blo 1128631 30926609 := bstep (se 2 (by rfl) ⟨11597478, by rfl⟩ : syracuseStep 30926609 = 23194957) B23194957
theorem B1697657 : Blo 1128631 1697657 := bstep (se 2 (by rfl) ⟨636621, by rfl⟩ : syracuseStep 1697657 = 1273243) B1273243
theorem B5433587 : Blo 1128631 5433587 := bstep (se 1 (by rfl) ⟨4075190, by rfl⟩ : syracuseStep 5433587 = 8150381) B8150381
theorem B12544571 : Blo 1128631 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B1698407 : Blo 1128631 1698407 := bstep (se 1 (by rfl) ⟨1273805, by rfl⟩ : syracuseStep 1698407 = 2547611) B2547611
theorem B1698683 : Blo 1128631 1698683 := bstep (se 1 (by rfl) ⟨1274012, by rfl⟩ : syracuseStep 1698683 = 2548025) B2548025
theorem B9793991 : Blo 1128631 9793991 := bstep (se 1 (by rfl) ⟨7345493, by rfl⟩ : syracuseStep 9793991 = 14690987) B14690987
theorem B5730911 : Blo 1128631 5730911 := bstep (se 1 (by rfl) ⟨4298183, by rfl⟩ : syracuseStep 5730911 = 8596367) B8596367
theorem B5796541 : Blo 1128631 5796541 := bstep (se 3 (by rfl) ⟨1086851, by rfl⟩ : syracuseStep 5796541 = 2173703) B2173703
theorem B1864475 : Blo 1128631 1864475 := bstep (se 1 (by rfl) ⟨1398356, by rfl⟩ : syracuseStep 1864475 = 2796713) B2796713
theorem B58782665 : Blo 1128631 58782665 := bstep (se 2 (by rfl) ⟨22043499, by rfl⟩ : syracuseStep 58782665 = 44086999) B44086999
theorem B3863539 : Blo 1128631 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B7239449 : Blo 1128631 7239449 := bstep (se 2 (by rfl) ⟨2714793, by rfl⟩ : syracuseStep 7239449 = 5429587) B5429587
theorem B4290803 : Blo 1128631 4290803 := bstep (se 1 (by rfl) ⟨3218102, by rfl⟩ : syracuseStep 4290803 = 6436205) B6436205
theorem B7241089 : Blo 1128631 7241089 := bstep (se 2 (by rfl) ⟨2715408, by rfl⟩ : syracuseStep 7241089 = 5430817) B5430817
theorem B47021633 : Blo 1128631 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B8585189 : Blo 1128631 8585189 := bstep (se 4 (by rfl) ⟨804861, by rfl⟩ : syracuseStep 8585189 = 1609723) B1609723
theorem B5439737 : Blo 1128631 5439737 := bstep (se 2 (by rfl) ⟨2039901, by rfl⟩ : syracuseStep 5439737 = 4079803) B4079803
theorem B26117309 : Blo 1128631 26117309 := bstep (se 3 (by rfl) ⟨4896995, by rfl⟩ : syracuseStep 26117309 = 9793991) B9793991
theorem B8587133 : Blo 1128631 8587133 := bstep (se 3 (by rfl) ⟨1610087, by rfl⟩ : syracuseStep 8587133 = 3220175) B3220175
theorem B5441735 : Blo 1128631 5441735 := bstep (se 1 (by rfl) ⟨4081301, by rfl⟩ : syracuseStep 5441735 = 8162603) B8162603
theorem B4294889 : Blo 1128631 4294889 := bstep (se 2 (by rfl) ⟨1610583, by rfl⟩ : syracuseStep 4294889 = 3221167) B3221167
theorem B3672697 : Blo 1128631 3672697 := bstep (se 2 (by rfl) ⟨1377261, by rfl⟩ : syracuseStep 3672697 = 2754523) B2754523
theorem B9800443 : Blo 1128631 9800443 := bstep (se 1 (by rfl) ⟨7350332, by rfl⟩ : syracuseStep 9800443 = 14700665) B14700665
theorem B3214151 : Blo 1128631 3214151 := bstep (se 1 (by rfl) ⟨2410613, by rfl⟩ : syracuseStep 3214151 = 4821227) B4821227
theorem B3214799 : Blo 1128631 3214799 := bstep (se 1 (by rfl) ⟨2411099, by rfl⟩ : syracuseStep 3214799 = 4822199) B4822199
theorem B9670367 : Blo 1128631 9670367 := bstep (se 1 (by rfl) ⟨7252775, by rfl⟩ : syracuseStep 9670367 = 14505551) B14505551
theorem B3215335 : Blo 1128631 3215335 := bstep (se 1 (by rfl) ⟨2411501, by rfl⟩ : syracuseStep 3215335 = 4823003) B4823003
theorem B4296847 : Blo 1128631 4296847 := bstep (se 1 (by rfl) ⟨3222635, by rfl⟩ : syracuseStep 4296847 = 6445271) B6445271
theorem B1904863 : Blo 1128631 1904863 := bstep (se 1 (by rfl) ⟨1428647, by rfl⟩ : syracuseStep 1904863 = 2857295) B2857295
theorem B4297151 : Blo 1128631 4297151 := bstep (se 1 (by rfl) ⟨3222863, by rfl⟩ : syracuseStep 4297151 = 6445727) B6445727
theorem B8590049 : Blo 1128631 8590049 := bstep (se 2 (by rfl) ⟨3221268, by rfl⟩ : syracuseStep 8590049 = 6442537) B6442537
theorem B39687155 : Blo 1128631 39687155 := bstep (se 1 (by rfl) ⟨29765366, by rfl⟩ : syracuseStep 39687155 = 59530733) B59530733
theorem B3053011 : Blo 1128631 3053011 := bstep (se 1 (by rfl) ⟨2289758, by rfl⟩ : syracuseStep 3053011 = 4579517) B4579517
theorem B1906267 : Blo 1128631 1906267 := bstep (se 1 (by rfl) ⟨1429700, by rfl⟩ : syracuseStep 1906267 = 2859401) B2859401
theorem B34379435 : Blo 1128631 34379435 := bstep (se 1 (by rfl) ⟨25784576, by rfl⟩ : syracuseStep 34379435 = 51569153) B51569153
theorem B1906409 : Blo 1128631 1906409 := bstep (se 2 (by rfl) ⟨714903, by rfl⟩ : syracuseStep 1906409 = 1429807) B1429807
theorem B4298791 : Blo 1128631 4298791 := bstep (se 1 (by rfl) ⟨3224093, by rfl⟩ : syracuseStep 4298791 = 6448187) B6448187
theorem B4299065 : Blo 1128631 4299065 := bstep (se 2 (by rfl) ⟨1612149, by rfl⟩ : syracuseStep 4299065 = 3224299) B3224299
theorem B20617739 : Blo 1128631 20617739 := bstep (se 1 (by rfl) ⟨15463304, by rfl⟩ : syracuseStep 20617739 = 30926609) B30926609
theorem B1907327 : Blo 1128631 1907327 := bstep (se 1 (by rfl) ⟨1430495, by rfl⟩ : syracuseStep 1907327 = 2860991) B2860991
theorem B5151385 : Blo 1128631 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B1907705 : Blo 1128631 1907705 := bstep (se 2 (by rfl) ⟨715389, by rfl⟩ : syracuseStep 1907705 = 1430779) B1430779
theorem B8363047 : Blo 1128631 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B211393597 : Blo 1128631 211393597 := bstep (se 3 (by rfl) ⟨39636299, by rfl⟩ : syracuseStep 211393597 = 79272599) B79272599
theorem B1907995 : Blo 1128631 1907995 := bstep (se 1 (by rfl) ⟨1430996, by rfl⟩ : syracuseStep 1907995 = 2861993) B2861993
theorem B16293149 : Blo 1128631 16293149 := bstep (se 3 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 16293149 = 6109931) B6109931
theorem B18358073 : Blo 1128631 18358073 := bstep (se 2 (by rfl) ⟨6884277, by rfl⟩ : syracuseStep 18358073 = 13768555) B13768555
theorem B1908731 : Blo 1128631 1908731 := bstep (se 1 (by rfl) ⟨1431548, by rfl⟩ : syracuseStep 1908731 = 2863097) B2863097
theorem B3219527 : Blo 1128631 3219527 := bstep (se 1 (by rfl) ⟨2414645, by rfl⟩ : syracuseStep 3219527 = 4829291) B4829291
theorem B1909163 : Blo 1128631 1909163 := bstep (se 1 (by rfl) ⟨1431872, by rfl⟩ : syracuseStep 1909163 = 2863745) B2863745
theorem B1909703 : Blo 1128631 1909703 := bstep (se 1 (by rfl) ⟨1432277, by rfl⟩ : syracuseStep 1909703 = 2864555) B2864555
theorem B4826299 : Blo 1128631 4826299 := bstep (se 1 (by rfl) ⟨3619724, by rfl⟩ : syracuseStep 4826299 = 7239449) B7239449
theorem B3810617 : Blo 1128631 3810617 := bstep (se 2 (by rfl) ⟨1428981, by rfl⟩ : syracuseStep 3810617 = 2857963) B2857963
theorem B2860535 : Blo 1128631 2860535 := bstep (se 1 (by rfl) ⟨2145401, by rfl⟩ : syracuseStep 2860535 = 4290803) B4290803
theorem B3810941 : Blo 1128631 3810941 := bstep (se 3 (by rfl) ⟨714551, by rfl⟩ : syracuseStep 3810941 = 1429103) B1429103
theorem B1910479 : Blo 1128631 1910479 := bstep (se 1 (by rfl) ⟨1432859, by rfl⟩ : syracuseStep 1910479 = 2865719) B2865719
theorem B13052009 : Blo 1128631 13052009 := bstep (se 2 (by rfl) ⟨4894503, by rfl⟩ : syracuseStep 13052009 = 9789007) B9789007
theorem B1910891 : Blo 1128631 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B3811859 : Blo 1128631 3811859 := bstep (se 1 (by rfl) ⟨2858894, by rfl⟩ : syracuseStep 3811859 = 5717789) B5717789
theorem B3812075 : Blo 1128631 3812075 := bstep (se 1 (by rfl) ⟨2859056, by rfl⟩ : syracuseStep 3812075 = 5718113) B5718113
theorem B9776123 : Blo 1128631 9776123 := bstep (se 1 (by rfl) ⟨7332092, by rfl⟩ : syracuseStep 9776123 = 14664185) B14664185
theorem B6433789 : Blo 1128631 6433789 := bstep (se 3 (by rfl) ⟨1206335, by rfl⟩ : syracuseStep 6433789 = 2412671) B2412671
theorem B6532283 : Blo 1128631 6532283 := bstep (se 1 (by rfl) ⟨4899212, by rfl⟩ : syracuseStep 6532283 = 9798425) B9798425
theorem B3812993 : Blo 1128631 3812993 := bstep (se 2 (by rfl) ⟨1429872, by rfl⟩ : syracuseStep 3812993 = 2859745) B2859745
theorem B31371077 : Blo 1128631 31371077 := bstep (se 4 (by rfl) ⟨2941038, by rfl⟩ : syracuseStep 31371077 = 5882077) B5882077
theorem B2174843 : Blo 1128631 2174843 := bstep (se 1 (by rfl) ⟨1631132, by rfl⟩ : syracuseStep 2174843 = 3262265) B3262265
theorem B5157151 : Blo 1128631 5157151 := bstep (se 1 (by rfl) ⟨3867863, by rfl⟩ : syracuseStep 5157151 = 7735727) B7735727
theorem B2863583 : Blo 1128631 2863583 := bstep (se 1 (by rfl) ⟨2147687, by rfl⟩ : syracuseStep 2863583 = 4295375) B4295375
theorem B2143739 : Blo 1128631 2143739 := bstep (se 1 (by rfl) ⟨1607804, by rfl⟩ : syracuseStep 2143739 = 3215609) B3215609
theorem B3814991 : Blo 1128631 3814991 := bstep (se 1 (by rfl) ⟨2861243, by rfl⟩ : syracuseStep 3814991 = 5722487) B5722487
theorem B1128655 : Blo 1128631 1128655 := bstep (se 1 (by rfl) ⟨846491, by rfl⟩ : syracuseStep 1128655 = 1692983) B1692983
theorem B30914885 : Blo 1128631 30914885 := bstep (se 4 (by rfl) ⟨2898270, by rfl⟩ : syracuseStep 30914885 = 5796541) B5796541
theorem B1128859 : Blo 1128631 1128859 := bstep (se 1 (by rfl) ⟨846644, by rfl⟩ : syracuseStep 1128859 = 1693289) B1693289
theorem B6961639 : Blo 1128631 6961639 := bstep (se 1 (by rfl) ⟨5221229, by rfl⟩ : syracuseStep 6961639 = 10442459) B10442459
theorem B1129215 : Blo 1128631 1129215 := bstep (se 1 (by rfl) ⟨846911, by rfl⟩ : syracuseStep 1129215 = 1693823) B1693823
theorem B1129279 : Blo 1128631 1129279 := bstep (se 1 (by rfl) ⟨846959, by rfl⟩ : syracuseStep 1129279 = 1693919) B1693919
theorem B1129319 : Blo 1128631 1129319 := bstep (se 1 (by rfl) ⟨846989, by rfl⟩ : syracuseStep 1129319 = 1693979) B1693979
theorem B1129535 : Blo 1128631 1129535 := bstep (se 1 (by rfl) ⟨847151, by rfl⟩ : syracuseStep 1129535 = 1694303) B1694303
theorem B1129599 : Blo 1128631 1129599 := bstep (se 1 (by rfl) ⟨847199, by rfl⟩ : syracuseStep 1129599 = 1694399) B1694399
theorem B1129627 : Blo 1128631 1129627 := bstep (se 1 (by rfl) ⟨847220, by rfl⟩ : syracuseStep 1129627 = 1694441) B1694441
theorem B1129711 : Blo 1128631 1129711 := bstep (se 1 (by rfl) ⟨847283, by rfl⟩ : syracuseStep 1129711 = 1694567) B1694567
theorem B1129755 : Blo 1128631 1129755 := bstep (se 1 (by rfl) ⟨847316, by rfl⟩ : syracuseStep 1129755 = 1694633) B1694633
theorem B1129855 : Blo 1128631 1129855 := bstep (se 1 (by rfl) ⟨847391, by rfl⟩ : syracuseStep 1129855 = 1694783) B1694783
theorem B1129883 : Blo 1128631 1129883 := bstep (se 1 (by rfl) ⟨847412, by rfl⟩ : syracuseStep 1129883 = 1694825) B1694825
theorem B1129967 : Blo 1128631 1129967 := bstep (se 1 (by rfl) ⟨847475, by rfl⟩ : syracuseStep 1129967 = 1694951) B1694951
theorem B1130303 : Blo 1128631 1130303 := bstep (se 1 (by rfl) ⟨847727, by rfl⟩ : syracuseStep 1130303 = 1695455) B1695455
theorem B2539511 : Blo 1128631 2539511 := bstep (se 1 (by rfl) ⟨1904633, by rfl⟩ : syracuseStep 2539511 = 3809267) B3809267
theorem B1130523 : Blo 1128631 1130523 := bstep (se 1 (by rfl) ⟨847892, by rfl⟩ : syracuseStep 1130523 = 1695785) B1695785
theorem B1130543 : Blo 1128631 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B1130567 : Blo 1128631 1130567 := bstep (se 1 (by rfl) ⟨847925, by rfl⟩ : syracuseStep 1130567 = 1695851) B1695851
theorem B1130623 : Blo 1128631 1130623 := bstep (se 1 (by rfl) ⟨847967, by rfl⟩ : syracuseStep 1130623 = 1695935) B1695935
theorem B1130747 : Blo 1128631 1130747 := bstep (se 1 (by rfl) ⟨848060, by rfl⟩ : syracuseStep 1130747 = 1696121) B1696121
theorem B3621149 : Blo 1128631 3621149 := bstep (se 3 (by rfl) ⟨678965, by rfl⟩ : syracuseStep 3621149 = 1357931) B1357931
theorem B2539871 : Blo 1128631 2539871 := bstep (se 1 (by rfl) ⟨1904903, by rfl⟩ : syracuseStep 2539871 = 3809807) B3809807
theorem B1130943 : Blo 1128631 1130943 := bstep (se 1 (by rfl) ⟨848207, by rfl⟩ : syracuseStep 1130943 = 1696415) B1696415
theorem B3818015 : Blo 1128631 3818015 := bstep (se 1 (by rfl) ⟨2863511, by rfl⟩ : syracuseStep 3818015 = 5727023) B5727023
theorem B1131167 : Blo 1128631 1131167 := bstep (se 1 (by rfl) ⟨848375, by rfl⟩ : syracuseStep 1131167 = 1696751) B1696751
theorem B1131239 : Blo 1128631 1131239 := bstep (se 1 (by rfl) ⟨848429, by rfl⟩ : syracuseStep 1131239 = 1696859) B1696859
theorem B1131247 : Blo 1128631 1131247 := bstep (se 1 (by rfl) ⟨848435, by rfl⟩ : syracuseStep 1131247 = 1696871) B1696871
theorem B1131335 : Blo 1128631 1131335 := bstep (se 1 (by rfl) ⟨848501, by rfl⟩ : syracuseStep 1131335 = 1697003) B1697003
theorem B1131423 : Blo 1128631 1131423 := bstep (se 1 (by rfl) ⟨848567, by rfl⟩ : syracuseStep 1131423 = 1697135) B1697135
theorem B19284965 : Blo 1128631 19284965 := bstep (se 4 (by rfl) ⟨1807965, by rfl⟩ : syracuseStep 19284965 = 3615931) B3615931
theorem B1131503 : Blo 1128631 1131503 := bstep (se 1 (by rfl) ⟨848627, by rfl⟩ : syracuseStep 1131503 = 1697255) B1697255
theorem B2540537 : Blo 1128631 2540537 := bstep (se 2 (by rfl) ⟨952701, by rfl⟩ : syracuseStep 2540537 = 1905403) B1905403
theorem B2540591 : Blo 1128631 2540591 := bstep (se 1 (by rfl) ⟨1905443, by rfl⟩ : syracuseStep 2540591 = 3810887) B3810887
theorem B1131591 : Blo 1128631 1131591 := bstep (se 1 (by rfl) ⟨848693, by rfl⟩ : syracuseStep 1131591 = 1697387) B1697387
theorem B1131623 : Blo 1128631 1131623 := bstep (se 1 (by rfl) ⟨848717, by rfl⟩ : syracuseStep 1131623 = 1697435) B1697435
theorem B3818663 : Blo 1128631 3818663 := bstep (se 1 (by rfl) ⟨2863997, by rfl⟩ : syracuseStep 3818663 = 5727995) B5727995
theorem B1131771 : Blo 1128631 1131771 := bstep (se 1 (by rfl) ⟨848828, by rfl⟩ : syracuseStep 1131771 = 1697657) B1697657
theorem B55035287 : Blo 1128631 55035287 := bstep (se 1 (by rfl) ⟨41276465, by rfl⟩ : syracuseStep 55035287 = 82552931) B82552931
theorem B3622391 : Blo 1128631 3622391 := bstep (se 1 (by rfl) ⟨2716793, by rfl⟩ : syracuseStep 3622391 = 5433587) B5433587
theorem B1132271 : Blo 1128631 1132271 := bstep (se 1 (by rfl) ⟨849203, by rfl⟩ : syracuseStep 1132271 = 1698407) B1698407
theorem B1132455 : Blo 1128631 1132455 := bstep (se 1 (by rfl) ⟨849341, by rfl⟩ : syracuseStep 1132455 = 1698683) B1698683
theorem B3721963 : Blo 1128631 3721963 := bstep (se 1 (by rfl) ⟨2791472, by rfl⟩ : syracuseStep 3721963 = 5582945) B5582945
theorem B2542319 : Blo 1128631 2542319 := bstep (se 1 (by rfl) ⟨1906739, by rfl⟩ : syracuseStep 2542319 = 3813479) B3813479
theorem B2149183 : Blo 1128631 2149183 := bstep (se 1 (by rfl) ⟨1611887, by rfl⟩ : syracuseStep 2149183 = 3223775) B3223775
theorem B3820445 : Blo 1128631 3820445 := bstep (se 3 (by rfl) ⟨716333, by rfl⟩ : syracuseStep 3820445 = 1432667) B1432667
theorem B3820607 : Blo 1128631 3820607 := bstep (se 1 (by rfl) ⟨2865455, by rfl⟩ : syracuseStep 3820607 = 5730911) B5730911
theorem B2149487 : Blo 1128631 2149487 := bstep (se 1 (by rfl) ⟨1612115, by rfl⟩ : syracuseStep 2149487 = 3224231) B3224231
theorem B12897467 : Blo 1128631 12897467 := bstep (se 1 (by rfl) ⟨9673100, by rfl⟩ : syracuseStep 12897467 = 19346201) B19346201
theorem B20663869 : Blo 1128631 20663869 := bstep (se 3 (by rfl) ⟨3874475, by rfl⟩ : syracuseStep 20663869 = 7748951) B7748951
theorem B2543849 : Blo 1128631 2543849 := bstep (se 2 (by rfl) ⟨953943, by rfl⟩ : syracuseStep 2543849 = 1907887) B1907887
theorem B93966779 : Blo 1128631 93966779 := bstep (se 1 (by rfl) ⟨70475084, by rfl⟩ : syracuseStep 93966779 = 140950169) B140950169
theorem B9654785 : Blo 1128631 9654785 := bstep (se 2 (by rfl) ⟨3620544, by rfl⟩ : syracuseStep 9654785 = 7241089) B7241089
theorem B31347755 : Blo 1128631 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B8574011 : Blo 1128631 8574011 := bstep (se 1 (by rfl) ⟨6430508, by rfl⟩ : syracuseStep 8574011 = 12861017) B12861017
theorem B2544875 : Blo 1128631 2544875 := bstep (se 1 (by rfl) ⟨1908656, by rfl⟩ : syracuseStep 2544875 = 3817313) B3817313
theorem B5723459 : Blo 1128631 5723459 := bstep (se 1 (by rfl) ⟨4292594, by rfl⟩ : syracuseStep 5723459 = 8585189) B8585189
theorem B1693097 : Blo 1128631 1693097 := bstep (se 2 (by rfl) ⟨634911, by rfl⟩ : syracuseStep 1693097 = 1269823) B1269823
theorem B1693151 : Blo 1128631 1693151 := bstep (se 1 (by rfl) ⟨1269863, by rfl⟩ : syracuseStep 1693151 = 2539727) B2539727
theorem B2545487 : Blo 1128631 2545487 := bstep (se 1 (by rfl) ⟨1909115, by rfl⟩ : syracuseStep 2545487 = 3818231) B3818231
theorem B12900383 : Blo 1128631 12900383 := bstep (se 1 (by rfl) ⟨9675287, by rfl⟩ : syracuseStep 12900383 = 19350575) B19350575
theorem B2545847 : Blo 1128631 2545847 := bstep (se 1 (by rfl) ⟨1909385, by rfl⟩ : syracuseStep 2545847 = 3818771) B3818771
theorem B99211547 : Blo 1128631 99211547 := bstep (se 1 (by rfl) ⟨74408660, by rfl⟩ : syracuseStep 99211547 = 148817321) B148817321
theorem B2546207 : Blo 1128631 2546207 := bstep (se 1 (by rfl) ⟨1909655, by rfl⟩ : syracuseStep 2546207 = 3819311) B3819311
theorem B1694249 : Blo 1128631 1694249 := bstep (se 2 (by rfl) ⟨635343, by rfl⟩ : syracuseStep 1694249 = 1270687) B1270687
theorem B1694363 : Blo 1128631 1694363 := bstep (se 1 (by rfl) ⟨1270772, by rfl⟩ : syracuseStep 1694363 = 2541545) B2541545
theorem B7232327 : Blo 1128631 7232327 := bstep (se 1 (by rfl) ⟨5424245, by rfl⟩ : syracuseStep 7232327 = 10848491) B10848491
theorem B1694687 : Blo 1128631 1694687 := bstep (se 1 (by rfl) ⟨1271015, by rfl⟩ : syracuseStep 1694687 = 2542031) B2542031
theorem B1694747 : Blo 1128631 1694747 := bstep (se 1 (by rfl) ⟨1271060, by rfl⟩ : syracuseStep 1694747 = 2542121) B2542121
theorem B1695335 : Blo 1128631 1695335 := bstep (se 1 (by rfl) ⟨1271501, by rfl⟩ : syracuseStep 1695335 = 2543003) B2543003
theorem B1696367 : Blo 1128631 1696367 := bstep (se 1 (by rfl) ⟨1272275, by rfl⟩ : syracuseStep 1696367 = 2544551) B2544551
theorem B4285487 : Blo 1128631 4285487 := bstep (se 1 (by rfl) ⟨3214115, by rfl⟩ : syracuseStep 4285487 = 6428231) B6428231
theorem B5727671 : Blo 1128631 5727671 := bstep (se 1 (by rfl) ⟨4295753, by rfl⟩ : syracuseStep 5727671 = 8591507) B8591507
theorem B6448895 : Blo 1128631 6448895 := bstep (se 1 (by rfl) ⟨4836671, by rfl⟩ : syracuseStep 6448895 = 9673343) B9673343
theorem B9660221 : Blo 1128631 9660221 := bstep (se 3 (by rfl) ⟨1811291, by rfl⟩ : syracuseStep 9660221 = 3622583) B3622583
theorem B2418515 : Blo 1128631 2418515 := bstep (se 1 (by rfl) ⟨1813886, by rfl⟩ : syracuseStep 2418515 = 3627773) B3627773
theorem B4646879 : Blo 1128631 4646879 := bstep (se 1 (by rfl) ⟨3485159, by rfl⟩ : syracuseStep 4646879 = 6970319) B6970319
theorem B1698011 : Blo 1128631 1698011 := bstep (se 1 (by rfl) ⟨1273508, by rfl⟩ : syracuseStep 1698011 = 2547017) B2547017
theorem B1698023 : Blo 1128631 1698023 := bstep (se 1 (by rfl) ⟨1273517, by rfl⟩ : syracuseStep 1698023 = 2547035) B2547035
theorem B2354003 : Blo 1128631 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B1698671 : Blo 1128631 1698671 := bstep (se 1 (by rfl) ⟨1274003, by rfl⟩ : syracuseStep 1698671 = 2548007) B2548007
theorem B14510987 : Blo 1128631 14510987 := bstep (se 1 (by rfl) ⟨10883240, by rfl⟩ : syracuseStep 14510987 = 21766481) B21766481
theorem B1207207 : Blo 1128631 1207207 := bstep (se 1 (by rfl) ⟨905405, by rfl⟩ : syracuseStep 1207207 = 1810811) B1810811
theorem B4287401 : Blo 1128631 4287401 := bstep (se 2 (by rfl) ⟨1607775, by rfl⟩ : syracuseStep 4287401 = 3215551) B3215551
theorem B1698911 : Blo 1128631 1698911 := bstep (se 1 (by rfl) ⟨1274183, by rfl⟩ : syracuseStep 1698911 = 2548367) B2548367
theorem B1698923 : Blo 1128631 1698923 := bstep (se 1 (by rfl) ⟨1274192, by rfl⟩ : syracuseStep 1698923 = 2548385) B2548385
theorem B1273063 : Blo 1128631 1273063 := bstep (se 1 (by rfl) ⟨954797, by rfl⟩ : syracuseStep 1273063 = 1909595) B1909595
theorem B5729615 : Blo 1128631 5729615 := bstep (se 1 (by rfl) ⟨4297211, by rfl⟩ : syracuseStep 5729615 = 8594423) B8594423
theorem B1273279 : Blo 1128631 1273279 := bstep (se 1 (by rfl) ⟨954959, by rfl⟩ : syracuseStep 1273279 = 1909919) B1909919
theorem B1273711 : Blo 1128631 1273711 := bstep (se 1 (by rfl) ⟨955283, by rfl⟩ : syracuseStep 1273711 = 1910567) B1910567
theorem B5730263 : Blo 1128631 5730263 := bstep (se 1 (by rfl) ⟨4297697, by rfl⟩ : syracuseStep 5730263 = 8595395) B8595395
theorem B4289071 : Blo 1128631 4289071 := bstep (se 1 (by rfl) ⟨3216803, by rfl⟩ : syracuseStep 4289071 = 6433607) B6433607
theorem B7238423 : Blo 1128631 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B6878033 : Blo 1128631 6878033 := bstep (se 2 (by rfl) ⟨2579262, by rfl⟩ : syracuseStep 6878033 = 5158525) B5158525
theorem B2716631 : Blo 1128631 2716631 := bstep (se 1 (by rfl) ⟨2037473, by rfl⟩ : syracuseStep 2716631 = 4074947) B4074947
theorem B357758093 : Blo 1128631 357758093 := bstep (se 3 (by rfl) ⟨67079642, by rfl⟩ : syracuseStep 357758093 = 134159285) B134159285
theorem B1242983 : Blo 1128631 1242983 := bstep (se 1 (by rfl) ⟨932237, by rfl⟩ : syracuseStep 1242983 = 1864475) B1864475
theorem B39188443 : Blo 1128631 39188443 := bstep (se 1 (by rfl) ⟨29391332, by rfl⟩ : syracuseStep 39188443 = 58782665) B58782665
theorem B4290529 : Blo 1128631 4290529 := bstep (se 2 (by rfl) ⟨1608948, by rfl⟩ : syracuseStep 4290529 = 3217897) B3217897
theorem B1931599 : Blo 1128631 1931599 := bstep (se 1 (by rfl) ⟨1448699, by rfl⟩ : syracuseStep 1931599 = 2897399) B2897399
theorem B15695633 : Blo 1128631 15695633 := bstep (se 2 (by rfl) ⟨5885862, by rfl⟩ : syracuseStep 15695633 = 11771725) B11771725
theorem B13074281 : Blo 1128631 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B28934009 : Blo 1128631 28934009 := bstep (se 2 (by rfl) ⟨10850253, by rfl⟩ : syracuseStep 28934009 = 21700507) B21700507
theorem B4292473 : Blo 1128631 4292473 := bstep (se 2 (by rfl) ⟨1609677, by rfl⟩ : syracuseStep 4292473 = 3219355) B3219355
theorem B17399717 : Blo 1128631 17399717 := bstep (se 4 (by rfl) ⟨1631223, by rfl⟩ : syracuseStep 17399717 = 3262447) B3262447
theorem B19302461 : Blo 1128631 19302461 := bstep (se 3 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 19302461 = 7238423) B7238423
theorem B4821551 : Blo 1128631 4821551 := bstep (se 1 (by rfl) ⟨3616163, by rfl⟩ : syracuseStep 4821551 = 7232327) B7232327
theorem B3314621 : Blo 1128631 3314621 := bstep (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) B1242983
theorem B2856991 : Blo 1128631 2856991 := bstep (se 1 (by rfl) ⟨2142743, by rfl⟩ : syracuseStep 2856991 = 4285487) B4285487
theorem B1907023 : Blo 1128631 1907023 := bstep (se 1 (by rfl) ⟨1430267, by rfl⟩ : syracuseStep 1907023 = 2860535) B2860535
theorem B4299263 : Blo 1128631 4299263 := bstep (se 1 (by rfl) ⟨3224447, by rfl⟩ : syracuseStep 4299263 = 6448895) B6448895
theorem B1612343 : Blo 1128631 1612343 := bstep (se 1 (by rfl) ⟨1209257, by rfl⟩ : syracuseStep 1612343 = 2418515) B2418515
theorem B9673991 : Blo 1128631 9673991 := bstep (se 1 (by rfl) ⟨7255493, by rfl⟩ : syracuseStep 9673991 = 14510987) B14510987
theorem B4070681 : Blo 1128631 4070681 := bstep (se 2 (by rfl) ⟨1526505, by rfl⟩ : syracuseStep 4070681 = 3053011) B3053011
theorem B2858267 : Blo 1128631 2858267 := bstep (se 1 (by rfl) ⟨2143700, by rfl⟩ : syracuseStep 2858267 = 4287401) B4287401
theorem B20914051 : Blo 1128631 20914051 := bstep (se 1 (by rfl) ⟨15685538, by rfl⟩ : syracuseStep 20914051 = 31371077) B31371077
theorem B1449895 : Blo 1128631 1449895 := bstep (se 1 (by rfl) ⟨1087421, by rfl⟩ : syracuseStep 1449895 = 2174843) B2174843
theorem B1909055 : Blo 1128631 1909055 := bstep (se 1 (by rfl) ⟨1431791, by rfl⟩ : syracuseStep 1909055 = 2863583) B2863583
theorem B9282185 : Blo 1128631 9282185 := bstep (se 2 (by rfl) ⟨3480819, by rfl⟩ : syracuseStep 9282185 = 6961639) B6961639
theorem B1811087 : Blo 1128631 1811087 := bstep (se 1 (by rfl) ⟨1358315, by rfl⟩ : syracuseStep 1811087 = 2716631) B2716631
theorem B25109365 : Blo 1128631 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B11150729 : Blo 1128631 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B10463755 : Blo 1128631 10463755 := bstep (se 1 (by rfl) ⟨7847816, by rfl⟩ : syracuseStep 10463755 = 15695633) B15695633
theorem B12856643 : Blo 1128631 12856643 := bstep (se 1 (by rfl) ⟨9642482, by rfl⟩ : syracuseStep 12856643 = 19284965) B19284965
theorem B17411539 : Blo 1128631 17411539 := bstep (se 1 (by rfl) ⟨13058654, by rfl⟩ : syracuseStep 17411539 = 26117309) B26117309
theorem B2863259 : Blo 1128631 2863259 := bstep (se 1 (by rfl) ⟨2147444, by rfl⟩ : syracuseStep 2863259 = 4294889) B4294889
theorem B27504805 : Blo 1128631 27504805 := bstep (se 4 (by rfl) ⟨2578575, by rfl⟩ : syracuseStep 27504805 = 5157151) B5157151
theorem B6435065 : Blo 1128631 6435065 := bstep (se 2 (by rfl) ⟨2413149, by rfl⟩ : syracuseStep 6435065 = 4826299) B4826299
theorem B2142767 : Blo 1128631 2142767 := bstep (se 1 (by rfl) ⟨1607075, by rfl⟩ : syracuseStep 2142767 = 3214151) B3214151
theorem B8598311 : Blo 1128631 8598311 := bstep (se 1 (by rfl) ⟨6448733, by rfl⟩ : syracuseStep 8598311 = 12897467) B12897467
theorem B2143199 : Blo 1128631 2143199 := bstep (se 1 (by rfl) ⟨1607399, by rfl⟩ : syracuseStep 2143199 = 3214799) B3214799
theorem B2864767 : Blo 1128631 2864767 := bstep (se 1 (by rfl) ⟨2148575, by rfl⟩ : syracuseStep 2864767 = 4297151) B4297151
theorem B6436523 : Blo 1128631 6436523 := bstep (se 1 (by rfl) ⟨4827392, by rfl⟩ : syracuseStep 6436523 = 9654785) B9654785
theorem B954021581 : Blo 1128631 954021581 := bstep (se 3 (by rfl) ⟨178879046, by rfl⟩ : syracuseStep 954021581 = 357758093) B357758093
theorem B26458103 : Blo 1128631 26458103 := bstep (se 1 (by rfl) ⟨19843577, by rfl⟩ : syracuseStep 26458103 = 39687155) B39687155
theorem B5716007 : Blo 1128631 5716007 := bstep (se 1 (by rfl) ⟨4287005, by rfl⟩ : syracuseStep 5716007 = 8574011) B8574011
theorem B4896929 : Blo 1128631 4896929 := bstep (se 2 (by rfl) ⟨1836348, by rfl⟩ : syracuseStep 4896929 = 3672697) B3672697
theorem B3815639 : Blo 1128631 3815639 := bstep (se 1 (by rfl) ⟨2861729, by rfl⟩ : syracuseStep 3815639 = 5723459) B5723459
theorem B1128731 : Blo 1128631 1128731 := bstep (se 1 (by rfl) ⟨846548, by rfl⟩ : syracuseStep 1128731 = 1693097) B1693097
theorem B4962617 : Blo 1128631 4962617 := bstep (se 2 (by rfl) ⟨1860981, by rfl⟩ : syracuseStep 4962617 = 3721963) B3721963
theorem B1128767 : Blo 1128631 1128767 := bstep (se 1 (by rfl) ⟨846575, by rfl⟩ : syracuseStep 1128767 = 1693151) B1693151
theorem B2865577 : Blo 1128631 2865577 := bstep (se 2 (by rfl) ⟨1074591, by rfl⟩ : syracuseStep 2865577 = 2149183) B2149183
theorem B8600255 : Blo 1128631 8600255 := bstep (se 1 (by rfl) ⟨6450191, by rfl⟩ : syracuseStep 8600255 = 12900383) B12900383
theorem B66141031 : Blo 1128631 66141031 := bstep (se 1 (by rfl) ⟨49605773, by rfl⟩ : syracuseStep 66141031 = 99211547) B99211547
theorem B2866043 : Blo 1128631 2866043 := bstep (se 1 (by rfl) ⟨2149532, by rfl⟩ : syracuseStep 2866043 = 4299065) B4299065
theorem B13745159 : Blo 1128631 13745159 := bstep (se 1 (by rfl) ⟨10308869, by rfl⟩ : syracuseStep 13745159 = 20617739) B20617739
theorem B1129499 : Blo 1128631 1129499 := bstep (se 1 (by rfl) ⟨847124, by rfl⟩ : syracuseStep 1129499 = 1694249) B1694249
theorem B1129575 : Blo 1128631 1129575 := bstep (se 1 (by rfl) ⟨847181, by rfl⟩ : syracuseStep 1129575 = 1694363) B1694363
theorem B1129791 : Blo 1128631 1129791 := bstep (se 1 (by rfl) ⟨847343, by rfl⟩ : syracuseStep 1129791 = 1694687) B1694687
theorem B1129831 : Blo 1128631 1129831 := bstep (se 1 (by rfl) ⟨847373, by rfl⟩ : syracuseStep 1129831 = 1694747) B1694747
theorem B10862099 : Blo 1128631 10862099 := bstep (se 1 (by rfl) ⟨8146574, by rfl⟩ : syracuseStep 10862099 = 16293149) B16293149
theorem B6438437 : Blo 1128631 6438437 := bstep (se 4 (by rfl) ⟨603603, by rfl⟩ : syracuseStep 6438437 = 1207207) B1207207
theorem B1130223 : Blo 1128631 1130223 := bstep (se 1 (by rfl) ⟨847667, by rfl⟩ : syracuseStep 1130223 = 1695335) B1695335
theorem B12238715 : Blo 1128631 12238715 := bstep (se 1 (by rfl) ⟨9179036, by rfl⟩ : syracuseStep 12238715 = 18358073) B18358073
theorem B2146351 : Blo 1128631 2146351 := bstep (se 1 (by rfl) ⟨1609763, by rfl⟩ : syracuseStep 2146351 = 3219527) B3219527
theorem B2539817 : Blo 1128631 2539817 := bstep (se 2 (by rfl) ⟨952431, by rfl⟩ : syracuseStep 2539817 = 1904863) B1904863
theorem B1130911 : Blo 1128631 1130911 := bstep (se 1 (by rfl) ⟨848183, by rfl⟩ : syracuseStep 1130911 = 1696367) B1696367
theorem B5718761 : Blo 1128631 5718761 := bstep (se 2 (by rfl) ⟨2144535, by rfl⟩ : syracuseStep 5718761 = 4289071) B4289071
theorem B2540411 : Blo 1128631 2540411 := bstep (se 1 (by rfl) ⟨1905308, by rfl⟩ : syracuseStep 2540411 = 3810617) B3810617
theorem B3818447 : Blo 1128631 3818447 := bstep (se 1 (by rfl) ⟨2863835, by rfl⟩ : syracuseStep 3818447 = 5727671) B5727671
theorem B2540627 : Blo 1128631 2540627 := bstep (se 1 (by rfl) ⟨1905470, by rfl⟩ : syracuseStep 2540627 = 3810941) B3810941
theorem B6440147 : Blo 1128631 6440147 := bstep (se 1 (by rfl) ⟨4830110, by rfl⟩ : syracuseStep 6440147 = 9660221) B9660221
theorem B3097919 : Blo 1128631 3097919 := bstep (se 1 (by rfl) ⟨2323439, by rfl⟩ : syracuseStep 3097919 = 4646879) B4646879
theorem B8701339 : Blo 1128631 8701339 := bstep (se 1 (by rfl) ⟨6526004, by rfl⟩ : syracuseStep 8701339 = 13052009) B13052009
theorem B1132007 : Blo 1128631 1132007 := bstep (se 1 (by rfl) ⟨849005, by rfl⟩ : syracuseStep 1132007 = 1698011) B1698011
theorem B1132015 : Blo 1128631 1132015 := bstep (se 1 (by rfl) ⟨849011, by rfl⟩ : syracuseStep 1132015 = 1698023) B1698023
theorem B2541239 : Blo 1128631 2541239 := bstep (se 1 (by rfl) ⟨1905929, by rfl⟩ : syracuseStep 2541239 = 3811859) B3811859
theorem B2541383 : Blo 1128631 2541383 := bstep (se 1 (by rfl) ⟨1906037, by rfl⟩ : syracuseStep 2541383 = 3812075) B3812075
theorem B1132447 : Blo 1128631 1132447 := bstep (se 1 (by rfl) ⟨849335, by rfl⟩ : syracuseStep 1132447 = 1698671) B1698671
theorem B1132607 : Blo 1128631 1132607 := bstep (se 1 (by rfl) ⟨849455, by rfl⟩ : syracuseStep 1132607 = 1698911) B1698911
theorem B1132615 : Blo 1128631 1132615 := bstep (se 1 (by rfl) ⟨849461, by rfl⟩ : syracuseStep 1132615 = 1698923) B1698923
theorem B2541689 : Blo 1128631 2541689 := bstep (se 2 (by rfl) ⟨953133, by rfl⟩ : syracuseStep 2541689 = 1906267) B1906267
theorem B3819743 : Blo 1128631 3819743 := bstep (se 1 (by rfl) ⟨2864807, by rfl⟩ : syracuseStep 3819743 = 5729615) B5729615
theorem B2541995 : Blo 1128631 2541995 := bstep (se 1 (by rfl) ⟨1906496, by rfl⟩ : syracuseStep 2541995 = 3812993) B3812993
theorem B52251257 : Blo 1128631 52251257 := bstep (se 2 (by rfl) ⟨19594221, by rfl⟩ : syracuseStep 52251257 = 39188443) B39188443
theorem B5720705 : Blo 1128631 5720705 := bstep (se 2 (by rfl) ⟨2145264, by rfl⟩ : syracuseStep 5720705 = 4290529) B4290529
theorem B3820175 : Blo 1128631 3820175 := bstep (se 1 (by rfl) ⟨2865131, by rfl⟩ : syracuseStep 3820175 = 5730263) B5730263
theorem B2575465 : Blo 1128631 2575465 := bstep (se 2 (by rfl) ⟨965799, by rfl⟩ : syracuseStep 2575465 = 1931599) B1931599
theorem B17419421 : Blo 1128631 17419421 := bstep (se 3 (by rfl) ⟨3266141, by rfl⟩ : syracuseStep 17419421 = 6532283) B6532283
theorem B6868513 : Blo 1128631 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B1429159 : Blo 1128631 1429159 := bstep (se 1 (by rfl) ⟨1071869, by rfl⟩ : syracuseStep 1429159 = 2143739) B2143739
theorem B2543327 : Blo 1128631 2543327 := bstep (se 1 (by rfl) ⟨1907495, by rfl⟩ : syracuseStep 2543327 = 3814991) B3814991
theorem B281858129 : Blo 1128631 281858129 := bstep (se 2 (by rfl) ⟨105696798, by rfl⟩ : syracuseStep 281858129 = 211393597) B211393597
theorem B2543993 : Blo 1128631 2543993 := bstep (se 2 (by rfl) ⟨953997, by rfl⟩ : syracuseStep 2543993 = 1907995) B1907995
theorem B5723297 : Blo 1128631 5723297 := bstep (se 2 (by rfl) ⟨2146236, by rfl⟩ : syracuseStep 5723297 = 4292473) B4292473
theorem B19289339 : Blo 1128631 19289339 := bstep (se 1 (by rfl) ⟨14467004, by rfl⟩ : syracuseStep 19289339 = 28934009) B28934009
theorem B1693007 : Blo 1128631 1693007 := bstep (se 1 (by rfl) ⟨1269755, by rfl⟩ : syracuseStep 1693007 = 2539511) B2539511
theorem B3626491 : Blo 1128631 3626491 := bstep (se 1 (by rfl) ⟨2719868, by rfl⟩ : syracuseStep 3626491 = 5439737) B5439737
theorem B2414099 : Blo 1128631 2414099 := bstep (se 1 (by rfl) ⟨1810574, by rfl⟩ : syracuseStep 2414099 = 3621149) B3621149
theorem B1693247 : Blo 1128631 1693247 := bstep (se 1 (by rfl) ⟨1269935, by rfl⟩ : syracuseStep 1693247 = 2539871) B2539871
theorem B2545343 : Blo 1128631 2545343 := bstep (se 1 (by rfl) ⟨1909007, by rfl⟩ : syracuseStep 2545343 = 3818015) B3818015
theorem B1693691 : Blo 1128631 1693691 := bstep (se 1 (by rfl) ⟨1270268, by rfl⟩ : syracuseStep 1693691 = 2540537) B2540537
theorem B1693727 : Blo 1128631 1693727 := bstep (se 1 (by rfl) ⟨1270295, by rfl⟩ : syracuseStep 1693727 = 2540591) B2540591
theorem B2545775 : Blo 1128631 2545775 := bstep (se 1 (by rfl) ⟨1909331, by rfl⟩ : syracuseStep 2545775 = 3818663) B3818663
theorem B36690191 : Blo 1128631 36690191 := bstep (se 1 (by rfl) ⟨27517643, by rfl⟩ : syracuseStep 36690191 = 55035287) B55035287
theorem B2414927 : Blo 1128631 2414927 := bstep (se 1 (by rfl) ⟨1811195, by rfl⟩ : syracuseStep 2414927 = 3622391) B3622391
theorem B5724755 : Blo 1128631 5724755 := bstep (se 1 (by rfl) ⟨4293566, by rfl⟩ : syracuseStep 5724755 = 8587133) B8587133
theorem B3627823 : Blo 1128631 3627823 := bstep (se 1 (by rfl) ⟨2720867, by rfl⟩ : syracuseStep 3627823 = 5441735) B5441735
theorem B1694879 : Blo 1128631 1694879 := bstep (se 1 (by rfl) ⟨1271159, by rfl⟩ : syracuseStep 1694879 = 2542319) B2542319
theorem B2546963 : Blo 1128631 2546963 := bstep (se 1 (by rfl) ⟨1910222, by rfl⟩ : syracuseStep 2546963 = 3820445) B3820445
theorem B2547071 : Blo 1128631 2547071 := bstep (se 1 (by rfl) ⟨1910303, by rfl⟩ : syracuseStep 2547071 = 3820607) B3820607
theorem B1432991 : Blo 1128631 1432991 := bstep (se 1 (by rfl) ⟨1074743, by rfl⟩ : syracuseStep 1432991 = 2149487) B2149487
theorem B2547305 : Blo 1128631 2547305 := bstep (se 2 (by rfl) ⟨955239, by rfl⟩ : syracuseStep 2547305 = 1910479) B1910479
theorem B6446911 : Blo 1128631 6446911 := bstep (se 1 (by rfl) ⟨4835183, by rfl⟩ : syracuseStep 6446911 = 9670367) B9670367
theorem B1695899 : Blo 1128631 1695899 := bstep (se 1 (by rfl) ⟨1271924, by rfl⟩ : syracuseStep 1695899 = 2543849) B2543849
theorem B62644519 : Blo 1128631 62644519 := bstep (se 1 (by rfl) ⟨46983389, by rfl⟩ : syracuseStep 62644519 = 93966779) B93966779
theorem B5726699 : Blo 1128631 5726699 := bstep (se 1 (by rfl) ⟨4295024, by rfl⟩ : syracuseStep 5726699 = 8590049) B8590049
theorem B20898503 : Blo 1128631 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B1696583 : Blo 1128631 1696583 := bstep (se 1 (by rfl) ⟨1272437, by rfl⟩ : syracuseStep 1696583 = 2544875) B2544875
theorem B13067257 : Blo 1128631 13067257 := bstep (se 2 (by rfl) ⟨4900221, by rfl⟩ : syracuseStep 13067257 = 9800443) B9800443
theorem B1270939 : Blo 1128631 1270939 := bstep (se 1 (by rfl) ⟨953204, by rfl⟩ : syracuseStep 1270939 = 1906409) B1906409
theorem B1696991 : Blo 1128631 1696991 := bstep (se 1 (by rfl) ⟨1272743, by rfl⟩ : syracuseStep 1696991 = 2545487) B2545487
theorem B8578385 : Blo 1128631 8578385 := bstep (se 2 (by rfl) ⟨3216894, by rfl⟩ : syracuseStep 8578385 = 6433789) B6433789
theorem B1697231 : Blo 1128631 1697231 := bstep (se 1 (by rfl) ⟨1272923, by rfl⟩ : syracuseStep 1697231 = 2545847) B2545847
theorem B1697417 : Blo 1128631 1697417 := bstep (se 2 (by rfl) ⟨636531, by rfl⟩ : syracuseStep 1697417 = 1273063) B1273063
theorem B1697471 : Blo 1128631 1697471 := bstep (se 1 (by rfl) ⟨1273103, by rfl⟩ : syracuseStep 1697471 = 2546207) B2546207
theorem B1271551 : Blo 1128631 1271551 := bstep (se 1 (by rfl) ⟨953663, by rfl⟩ : syracuseStep 1271551 = 1907327) B1907327
theorem B91678493 : Blo 1128631 91678493 := bstep (se 3 (by rfl) ⟨17189717, by rfl⟩ : syracuseStep 91678493 = 34379435) B34379435
theorem B1697705 : Blo 1128631 1697705 := bstep (se 2 (by rfl) ⟨636639, by rfl⟩ : syracuseStep 1697705 = 1273279) B1273279
theorem B1271803 : Blo 1128631 1271803 := bstep (se 1 (by rfl) ⟨953852, by rfl⟩ : syracuseStep 1271803 = 1907705) B1907705
theorem B27551825 : Blo 1128631 27551825 := bstep (se 2 (by rfl) ⟨10331934, by rfl⟩ : syracuseStep 27551825 = 20663869) B20663869
theorem B1698281 : Blo 1128631 1698281 := bstep (se 2 (by rfl) ⟨636855, by rfl⟩ : syracuseStep 1698281 = 1273711) B1273711
theorem B4287113 : Blo 1128631 4287113 := bstep (se 2 (by rfl) ⟨1607667, by rfl⟩ : syracuseStep 4287113 = 3215335) B3215335
theorem B1272487 : Blo 1128631 1272487 := bstep (se 1 (by rfl) ⟨954365, by rfl⟩ : syracuseStep 1272487 = 1908731) B1908731
theorem B5729129 : Blo 1128631 5729129 := bstep (se 2 (by rfl) ⟨2148423, by rfl⟩ : syracuseStep 5729129 = 4296847) B4296847
theorem B1272775 : Blo 1128631 1272775 := bstep (se 1 (by rfl) ⟨954581, by rfl⟩ : syracuseStep 1272775 = 1909163) B1909163
theorem B1273135 : Blo 1128631 1273135 := bstep (se 1 (by rfl) ⟨954851, by rfl⟩ : syracuseStep 1273135 = 1909703) B1909703
theorem B1273927 : Blo 1128631 1273927 := bstep (se 1 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 1273927 = 1910891) B1910891
theorem B6517415 : Blo 1128631 6517415 := bstep (se 1 (by rfl) ⟨4888061, by rfl⟩ : syracuseStep 6517415 = 9776123) B9776123
theorem B5731721 : Blo 1128631 5731721 := bstep (se 2 (by rfl) ⟨2149395, by rfl⟩ : syracuseStep 5731721 = 4298791) B4298791
theorem B4585355 : Blo 1128631 4585355 := bstep (se 1 (by rfl) ⟨3439016, by rfl⟩ : syracuseStep 4585355 = 6878033) B6878033
theorem B20609923 : Blo 1128631 20609923 := bstep (se 1 (by rfl) ⟨15457442, by rfl⟩ : syracuseStep 20609923 = 30914885) B30914885
theorem B8716187 : Blo 1128631 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B11599811 : Blo 1128631 11599811 := bstep (se 1 (by rfl) ⟨8699858, by rfl⟩ : syracuseStep 11599811 = 17399717) B17399717
theorem B83526025 : Blo 1128631 83526025 := bstep (se 2 (by rfl) ⟨31322259, by rfl⟩ : syracuseStep 83526025 = 62644519) B62644519
theorem B4293431 : Blo 1128631 4293431 := bstep (se 1 (by rfl) ⟨3220073, by rfl⟩ : syracuseStep 4293431 = 6440147) B6440147
theorem B2065279 : Blo 1128631 2065279 := bstep (se 1 (by rfl) ⟨1548959, by rfl⟩ : syracuseStep 2065279 = 3097919) B3097919
theorem B34834171 : Blo 1128631 34834171 := bstep (se 1 (by rfl) ⟨26125628, by rfl⟩ : syracuseStep 34834171 = 52251257) B52251257
theorem B11601785 : Blo 1128631 11601785 := bstep (se 2 (by rfl) ⟨4350669, by rfl⟩ : syracuseStep 11601785 = 8701339) B8701339
theorem B3214367 : Blo 1128631 3214367 := bstep (se 1 (by rfl) ⟨2410775, by rfl⟩ : syracuseStep 3214367 = 4821551) B4821551
theorem B1609399 : Blo 1128631 1609399 := bstep (se 1 (by rfl) ⟨1207049, by rfl⟩ : syracuseStep 1609399 = 2414099) B2414099
theorem B1609951 : Blo 1128631 1609951 := bstep (se 1 (by rfl) ⟨1207463, by rfl⟩ : syracuseStep 1609951 = 2414927) B2414927
theorem B1905511 : Blo 1128631 1905511 := bstep (se 1 (by rfl) ⟨1429133, by rfl⟩ : syracuseStep 1905511 = 2858267) B2858267
theorem B1905545 : Blo 1128631 1905545 := bstep (se 2 (by rfl) ⟨714579, by rfl⟩ : syracuseStep 1905545 = 1429159) B1429159
theorem B36673073 : Blo 1128631 36673073 := bstep (se 2 (by rfl) ⟨13752402, by rfl⟩ : syracuseStep 36673073 = 27504805) B27504805
theorem B13932335 : Blo 1128631 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B13735813 : Blo 1128631 13735813 := bstep (se 4 (by rfl) ⟨1287732, by rfl⟩ : syracuseStep 13735813 = 2575465) B2575465
theorem B4299581 : Blo 1128631 4299581 := bstep (se 3 (by rfl) ⟨806171, by rfl⟩ : syracuseStep 4299581 = 1612343) B1612343
theorem B2858075 : Blo 1128631 2858075 := bstep (se 1 (by rfl) ⟨2143556, by rfl⟩ : syracuseStep 2858075 = 4287113) B4287113
theorem B3809321 : Blo 1128631 3809321 := bstep (se 2 (by rfl) ⟨1428495, by rfl⟩ : syracuseStep 3809321 = 2856991) B2856991
theorem B1908839 : Blo 1128631 1908839 := bstep (se 1 (by rfl) ⟨1431629, by rfl⟩ : syracuseStep 1908839 = 2863259) B2863259
theorem B88188041 : Blo 1128631 88188041 := bstep (se 2 (by rfl) ⟨33070515, by rfl⟩ : syracuseStep 88188041 = 66141031) B66141031
theorem B3056903 : Blo 1128631 3056903 := bstep (se 1 (by rfl) ⟨2292677, by rfl⟩ : syracuseStep 3056903 = 4585355) B4585355
theorem B17638735 : Blo 1128631 17638735 := bstep (se 1 (by rfl) ⟨13229051, by rfl⟩ : syracuseStep 17638735 = 26458103) B26458103
theorem B3810671 : Blo 1128631 3810671 := bstep (se 1 (by rfl) ⟨2858003, by rfl⟩ : syracuseStep 3810671 = 5716007) B5716007
theorem B1910695 : Blo 1128631 1910695 := bstep (se 1 (by rfl) ⟨1433021, by rfl⟩ : syracuseStep 1910695 = 2866043) B2866043
theorem B8595881 : Blo 1128631 8595881 := bstep (se 2 (by rfl) ⟨3223455, by rfl⟩ : syracuseStep 8595881 = 6446911) B6446911
theorem B5810791 : Blo 1128631 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B2861801 : Blo 1128631 2861801 := bstep (se 2 (by rfl) ⟨1073175, by rfl⟩ : syracuseStep 2861801 = 2146351) B2146351
theorem B3812507 : Blo 1128631 3812507 := bstep (se 1 (by rfl) ⟨2859380, by rfl⟩ : syracuseStep 3812507 = 5718761) B5718761
theorem B3813803 : Blo 1128631 3813803 := bstep (se 1 (by rfl) ⟨2860352, by rfl⟩ : syracuseStep 3813803 = 5720705) B5720705
theorem B5715197 : Blo 1128631 5715197 := bstep (se 3 (by rfl) ⟨1071599, by rfl⟩ : syracuseStep 5715197 = 2143199) B2143199
theorem B187905419 : Blo 1128631 187905419 := bstep (se 1 (by rfl) ⟨140929064, by rfl⟩ : syracuseStep 187905419 = 281858129) B281858129
theorem B2209747 : Blo 1128631 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B3815531 : Blo 1128631 3815531 := bstep (se 1 (by rfl) ⟨2861648, by rfl⟩ : syracuseStep 3815531 = 5723297) B5723297
theorem B12859559 : Blo 1128631 12859559 := bstep (se 1 (by rfl) ⟨9644669, by rfl⟩ : syracuseStep 12859559 = 19289339) B19289339
theorem B1128671 : Blo 1128631 1128671 := bstep (se 1 (by rfl) ⟨846503, by rfl⟩ : syracuseStep 1128671 = 1693007) B1693007
theorem B1128831 : Blo 1128631 1128831 := bstep (se 1 (by rfl) ⟨846623, by rfl⟩ : syracuseStep 1128831 = 1693247) B1693247
theorem B1129127 : Blo 1128631 1129127 := bstep (se 1 (by rfl) ⟨846845, by rfl⟩ : syracuseStep 1129127 = 1693691) B1693691
theorem B1129151 : Blo 1128631 1129151 := bstep (se 1 (by rfl) ⟨846863, by rfl⟩ : syracuseStep 1129151 = 1693727) B1693727
theorem B24460127 : Blo 1128631 24460127 := bstep (se 1 (by rfl) ⟨18345095, by rfl⟩ : syracuseStep 24460127 = 36690191) B36690191
theorem B2866175 : Blo 1128631 2866175 := bstep (se 1 (by rfl) ⟨2149631, by rfl⟩ : syracuseStep 2866175 = 4299263) B4299263
theorem B3816503 : Blo 1128631 3816503 := bstep (se 1 (by rfl) ⟨2862377, by rfl⟩ : syracuseStep 3816503 = 5724755) B5724755
theorem B23215385 : Blo 1128631 23215385 := bstep (se 2 (by rfl) ⟨8705769, by rfl⟩ : syracuseStep 23215385 = 17411539) B17411539
theorem B9158017 : Blo 1128631 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B1129919 : Blo 1128631 1129919 := bstep (se 1 (by rfl) ⟨847439, by rfl⟩ : syracuseStep 1129919 = 1694879) B1694879
theorem B1130599 : Blo 1128631 1130599 := bstep (se 1 (by rfl) ⟨847949, by rfl⟩ : syracuseStep 1130599 = 1695899) B1695899
theorem B3817799 : Blo 1128631 3817799 := bstep (se 1 (by rfl) ⟨2863349, by rfl⟩ : syracuseStep 3817799 = 5726699) B5726699
theorem B1131055 : Blo 1128631 1131055 := bstep (se 1 (by rfl) ⟨848291, by rfl⟩ : syracuseStep 1131055 = 1696583) B1696583
theorem B1131327 : Blo 1128631 1131327 := bstep (se 1 (by rfl) ⟨848495, by rfl⟩ : syracuseStep 1131327 = 1696991) B1696991
theorem B5718923 : Blo 1128631 5718923 := bstep (se 1 (by rfl) ⟨4289192, by rfl⟩ : syracuseStep 5718923 = 8578385) B8578385
theorem B1131487 : Blo 1128631 1131487 := bstep (se 1 (by rfl) ⟨848615, by rfl⟩ : syracuseStep 1131487 = 1697231) B1697231
theorem B1131611 : Blo 1128631 1131611 := bstep (se 1 (by rfl) ⟨848708, by rfl⟩ : syracuseStep 1131611 = 1697417) B1697417
theorem B1131647 : Blo 1128631 1131647 := bstep (se 1 (by rfl) ⟨848735, by rfl⟩ : syracuseStep 1131647 = 1697471) B1697471
theorem B1131803 : Blo 1128631 1131803 := bstep (se 1 (by rfl) ⟨848852, by rfl⟩ : syracuseStep 1131803 = 1697705) B1697705
theorem B18367883 : Blo 1128631 18367883 := bstep (se 1 (by rfl) ⟨13775912, by rfl⟩ : syracuseStep 18367883 = 27551825) B27551825
theorem B1132187 : Blo 1128631 1132187 := bstep (se 1 (by rfl) ⟨849140, by rfl⟩ : syracuseStep 1132187 = 1698281) B1698281
theorem B3819419 : Blo 1128631 3819419 := bstep (se 1 (by rfl) ⟨2864564, by rfl⟩ : syracuseStep 3819419 = 5729129) B5729129
theorem B4835321 : Blo 1128631 4835321 := bstep (se 2 (by rfl) ⟨1813245, by rfl⟩ : syracuseStep 4835321 = 3626491) B3626491
theorem B3819689 : Blo 1128631 3819689 := bstep (se 2 (by rfl) ⟨1432383, by rfl⟩ : syracuseStep 3819689 = 2864767) B2864767
theorem B8571095 : Blo 1128631 8571095 := bstep (se 1 (by rfl) ⟨6428321, by rfl⟩ : syracuseStep 8571095 = 12856643) B12856643
theorem B1428511 : Blo 1128631 1428511 := bstep (se 1 (by rfl) ⟨1071383, by rfl⟩ : syracuseStep 1428511 = 2142767) B2142767
theorem B46451789 : Blo 1128631 46451789 := bstep (se 3 (by rfl) ⟨8709710, by rfl⟩ : syracuseStep 46451789 = 17419421) B17419421
theorem B2542697 : Blo 1128631 2542697 := bstep (se 2 (by rfl) ⟨953511, by rfl⟩ : syracuseStep 2542697 = 1907023) B1907023
theorem B4344943 : Blo 1128631 4344943 := bstep (se 1 (by rfl) ⟨3258707, by rfl⟩ : syracuseStep 4344943 = 6517415) B6517415
theorem B3820769 : Blo 1128631 3820769 := bstep (se 2 (by rfl) ⟨1432788, by rfl⟩ : syracuseStep 3820769 = 2865577) B2865577
theorem B3821147 : Blo 1128631 3821147 := bstep (se 1 (by rfl) ⟨2865860, by rfl⟩ : syracuseStep 3821147 = 5731721) B5731721
theorem B4837097 : Blo 1128631 4837097 := bstep (se 2 (by rfl) ⟨1813911, by rfl⟩ : syracuseStep 4837097 = 3627823) B3627823
theorem B3821309 : Blo 1128631 3821309 := bstep (se 3 (by rfl) ⟨716495, by rfl⟩ : syracuseStep 3821309 = 1432991) B1432991
theorem B636014387 : Blo 1128631 636014387 := bstep (se 1 (by rfl) ⟨477010790, by rfl⟩ : syracuseStep 636014387 = 954021581) B954021581
theorem B27479897 : Blo 1128631 27479897 := bstep (se 2 (by rfl) ⟨10304961, by rfl⟩ : syracuseStep 27479897 = 20609923) B20609923
theorem B3264619 : Blo 1128631 3264619 := bstep (se 1 (by rfl) ⟨2448464, by rfl⟩ : syracuseStep 3264619 = 4896929) B4896929
theorem B2543759 : Blo 1128631 2543759 := bstep (se 1 (by rfl) ⟨1907819, by rfl⟩ : syracuseStep 2543759 = 3815639) B3815639
theorem B9163439 : Blo 1128631 9163439 := bstep (se 1 (by rfl) ⟨6872579, by rfl⟩ : syracuseStep 9163439 = 13745159) B13745159
theorem B1693211 : Blo 1128631 1693211 := bstep (se 1 (by rfl) ⟨1269908, by rfl⟩ : syracuseStep 1693211 = 2539817) B2539817
theorem B1693607 : Blo 1128631 1693607 := bstep (se 1 (by rfl) ⟨1270205, by rfl⟩ : syracuseStep 1693607 = 2540411) B2540411
theorem B2545631 : Blo 1128631 2545631 := bstep (se 1 (by rfl) ⟨1909223, by rfl⟩ : syracuseStep 2545631 = 3818447) B3818447
theorem B1693751 : Blo 1128631 1693751 := bstep (se 1 (by rfl) ⟨1270313, by rfl⟩ : syracuseStep 1693751 = 2540627) B2540627
theorem B1694159 : Blo 1128631 1694159 := bstep (se 1 (by rfl) ⟨1270619, by rfl⟩ : syracuseStep 1694159 = 2541239) B2541239
theorem B33479153 : Blo 1128631 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B1694255 : Blo 1128631 1694255 := bstep (se 1 (by rfl) ⟨1270691, by rfl⟩ : syracuseStep 1694255 = 2541383) B2541383
theorem B17423009 : Blo 1128631 17423009 := bstep (se 2 (by rfl) ⟨6533628, by rfl⟩ : syracuseStep 17423009 = 13067257) B13067257
theorem B12868307 : Blo 1128631 12868307 := bstep (se 1 (by rfl) ⟨9651230, by rfl⟩ : syracuseStep 12868307 = 19302461) B19302461
theorem B1694459 : Blo 1128631 1694459 := bstep (se 1 (by rfl) ⟨1270844, by rfl⟩ : syracuseStep 1694459 = 2541689) B2541689
theorem B2546495 : Blo 1128631 2546495 := bstep (se 1 (by rfl) ⟨1909871, by rfl⟩ : syracuseStep 2546495 = 3819743) B3819743
theorem B1694585 : Blo 1128631 1694585 := bstep (se 2 (by rfl) ⟨635469, by rfl⟩ : syracuseStep 1694585 = 1270939) B1270939
theorem B1694663 : Blo 1128631 1694663 := bstep (se 1 (by rfl) ⟨1270997, by rfl⟩ : syracuseStep 1694663 = 2541995) B2541995
theorem B2546783 : Blo 1128631 2546783 := bstep (se 1 (by rfl) ⟨1910087, by rfl⟩ : syracuseStep 2546783 = 3820175) B3820175
theorem B1695401 : Blo 1128631 1695401 := bstep (se 2 (by rfl) ⟨635775, by rfl⟩ : syracuseStep 1695401 = 1271551) B1271551
theorem B1695551 : Blo 1128631 1695551 := bstep (se 1 (by rfl) ⟨1271663, by rfl⟩ : syracuseStep 1695551 = 2543327) B2543327
theorem B1695737 : Blo 1128631 1695737 := bstep (se 2 (by rfl) ⟨635901, by rfl⟩ : syracuseStep 1695737 = 1271803) B1271803
theorem B1695995 : Blo 1128631 1695995 := bstep (se 1 (by rfl) ⟨1271996, by rfl⟩ : syracuseStep 1695995 = 2543993) B2543993
theorem B13951673 : Blo 1128631 13951673 := bstep (se 2 (by rfl) ⟨5231877, by rfl⟩ : syracuseStep 13951673 = 10463755) B10463755
theorem B1696649 : Blo 1128631 1696649 := bstep (se 2 (by rfl) ⟨636243, by rfl⟩ : syracuseStep 1696649 = 1272487) B1272487
theorem B1696895 : Blo 1128631 1696895 := bstep (se 1 (by rfl) ⟨1272671, by rfl⟩ : syracuseStep 1696895 = 2545343) B2545343
theorem B1697033 : Blo 1128631 1697033 := bstep (se 2 (by rfl) ⟨636387, by rfl⟩ : syracuseStep 1697033 = 1272775) B1272775
theorem B1697183 : Blo 1128631 1697183 := bstep (se 1 (by rfl) ⟨1272887, by rfl⟩ : syracuseStep 1697183 = 2545775) B2545775
theorem B1697513 : Blo 1128631 1697513 := bstep (se 2 (by rfl) ⟨636567, by rfl⟩ : syracuseStep 1697513 = 1273135) B1273135
theorem B244475981 : Blo 1128631 244475981 := bstep (se 3 (by rfl) ⟨45839246, by rfl⟩ : syracuseStep 244475981 = 91678493) B91678493
theorem B6449327 : Blo 1128631 6449327 := bstep (se 1 (by rfl) ⟨4836995, by rfl⟩ : syracuseStep 6449327 = 9673991) B9673991
theorem B1697975 : Blo 1128631 1697975 := bstep (se 1 (by rfl) ⟨1273481, by rfl⟩ : syracuseStep 1697975 = 2546963) B2546963
theorem B2713787 : Blo 1128631 2713787 := bstep (se 1 (by rfl) ⟨2035340, by rfl⟩ : syracuseStep 2713787 = 4070681) B4070681
theorem B1698047 : Blo 1128631 1698047 := bstep (se 1 (by rfl) ⟨1273535, by rfl⟩ : syracuseStep 1698047 = 2547071) B2547071
theorem B1698203 : Blo 1128631 1698203 := bstep (se 1 (by rfl) ⟨1273652, by rfl⟩ : syracuseStep 1698203 = 2547305) B2547305
theorem B1698569 : Blo 1128631 1698569 := bstep (se 2 (by rfl) ⟨636963, by rfl⟩ : syracuseStep 1698569 = 1273927) B1273927
theorem B1272703 : Blo 1128631 1272703 := bstep (se 1 (by rfl) ⟨954527, by rfl⟩ : syracuseStep 1272703 = 1909055) B1909055
theorem B6188123 : Blo 1128631 6188123 := bstep (se 1 (by rfl) ⟨4641092, by rfl⟩ : syracuseStep 6188123 = 9282185) B9282185
theorem B1207391 : Blo 1128631 1207391 := bstep (se 1 (by rfl) ⟨905543, by rfl⟩ : syracuseStep 1207391 = 1811087) B1811087
theorem B7433819 : Blo 1128631 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B4290043 : Blo 1128631 4290043 := bstep (se 1 (by rfl) ⟨3217532, by rfl⟩ : syracuseStep 4290043 = 6435065) B6435065
theorem B5732207 : Blo 1128631 5732207 := bstep (se 1 (by rfl) ⟨4299155, by rfl⟩ : syracuseStep 5732207 = 8598311) B8598311
theorem B4291015 : Blo 1128631 4291015 := bstep (se 1 (by rfl) ⟨3218261, by rfl⟩ : syracuseStep 4291015 = 6436523) B6436523
theorem B3308411 : Blo 1128631 3308411 := bstep (se 1 (by rfl) ⟨2481308, by rfl⟩ : syracuseStep 3308411 = 4962617) B4962617
theorem B5733503 : Blo 1128631 5733503 := bstep (se 1 (by rfl) ⟨4300127, by rfl⟩ : syracuseStep 5733503 = 8600255) B8600255
theorem B7241399 : Blo 1128631 7241399 := bstep (se 1 (by rfl) ⟨5431049, by rfl⟩ : syracuseStep 7241399 = 10862099) B10862099
theorem B4292291 : Blo 1128631 4292291 := bstep (se 1 (by rfl) ⟨3219218, by rfl⟩ : syracuseStep 4292291 = 6438437) B6438437
theorem B27885401 : Blo 1128631 27885401 := bstep (se 2 (by rfl) ⟨10457025, by rfl⟩ : syracuseStep 27885401 = 20914051) B20914051
theorem B1933193 : Blo 1128631 1933193 := bstep (se 2 (by rfl) ⟨724947, by rfl⟩ : syracuseStep 1933193 = 1449895) B1449895
theorem B8159143 : Blo 1128631 8159143 := bstep (se 1 (by rfl) ⟨6119357, by rfl⟩ : syracuseStep 8159143 = 12238715) B12238715
theorem B7733207 : Blo 1128631 7733207 := bstep (se 1 (by rfl) ⟨5799905, by rfl⟩ : syracuseStep 7733207 = 11599811) B11599811
theorem B2753705 : Blo 1128631 2753705 := bstep (se 2 (by rfl) ⟨1032639, by rfl⟩ : syracuseStep 2753705 = 2065279) B2065279
theorem B7734523 : Blo 1128631 7734523 := bstep (se 1 (by rfl) ⟨5800892, by rfl⟩ : syracuseStep 7734523 = 11601785) B11601785
theorem B30967859 : Blo 1128631 30967859 := bstep (se 1 (by rfl) ⟨23225894, by rfl⟩ : syracuseStep 30967859 = 46451789) B46451789
theorem B18319931 : Blo 1128631 18319931 := bstep (se 1 (by rfl) ⟨13739948, by rfl⟩ : syracuseStep 18319931 = 27479897) B27479897
theorem B24448715 : Blo 1128631 24448715 := bstep (se 1 (by rfl) ⟨18336536, by rfl⟩ : syracuseStep 24448715 = 36673073) B36673073
theorem B1904681 : Blo 1128631 1904681 := bstep (se 2 (by rfl) ⟨714255, by rfl⟩ : syracuseStep 1904681 = 1428511) B1428511
theorem B22319435 : Blo 1128631 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B1905383 : Blo 1128631 1905383 := bstep (se 1 (by rfl) ⟨1429037, by rfl⟩ : syracuseStep 1905383 = 2858075) B2858075
theorem B2037935 : Blo 1128631 2037935 := bstep (se 1 (by rfl) ⟨1528451, by rfl⟩ : syracuseStep 2037935 = 3056903) B3056903
theorem B4299551 : Blo 1128631 4299551 := bstep (se 1 (by rfl) ⟨3224663, by rfl⟩ : syracuseStep 4299551 = 6449327) B6449327
theorem B1809191 : Blo 1128631 1809191 := bstep (se 1 (by rfl) ⟨1356893, by rfl⟩ : syracuseStep 1809191 = 2713787) B2713787
theorem B1907867 : Blo 1128631 1907867 := bstep (se 1 (by rfl) ⟨1430900, by rfl⟩ : syracuseStep 1907867 = 2861801) B2861801
theorem B4955879 : Blo 1128631 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B3219709 : Blo 1128631 3219709 := bstep (se 3 (by rfl) ⟨603695, by rfl⟩ : syracuseStep 3219709 = 1207391) B1207391
theorem B3810131 : Blo 1128631 3810131 := bstep (se 1 (by rfl) ⟨2857598, by rfl⟩ : syracuseStep 3810131 = 5715197) B5715197
theorem B2205607 : Blo 1128631 2205607 := bstep (se 1 (by rfl) ⟨1654205, by rfl⟩ : syracuseStep 2205607 = 3308411) B3308411
theorem B1910783 : Blo 1128631 1910783 := bstep (se 1 (by rfl) ⟨1433087, by rfl⟩ : syracuseStep 1910783 = 2866175) B2866175
theorem B15476923 : Blo 1128631 15476923 := bstep (se 1 (by rfl) ⟨11607692, by rfl⟩ : syracuseStep 15476923 = 23215385) B23215385
theorem B5155181 : Blo 1128631 5155181 := bstep (se 3 (by rfl) ⟨966596, by rfl⟩ : syracuseStep 5155181 = 1933193) B1933193
theorem B4827599 : Blo 1128631 4827599 := bstep (se 1 (by rfl) ⟨3620699, by rfl⟩ : syracuseStep 4827599 = 7241399) B7241399
theorem B2861527 : Blo 1128631 2861527 := bstep (se 1 (by rfl) ⟨2146145, by rfl⟩ : syracuseStep 2861527 = 4292291) B4292291
theorem B18590267 : Blo 1128631 18590267 := bstep (se 1 (by rfl) ⟨13942700, by rfl⟩ : syracuseStep 18590267 = 27885401) B27885401
theorem B5155471 : Blo 1128631 5155471 := bstep (se 1 (by rfl) ⟨3866603, by rfl⟩ : syracuseStep 5155471 = 7733207) B7733207
theorem B2862287 : Blo 1128631 2862287 := bstep (se 1 (by rfl) ⟨2146715, by rfl⟩ : syracuseStep 2862287 = 4293431) B4293431
theorem B3812615 : Blo 1128631 3812615 := bstep (se 1 (by rfl) ⟨2859461, by rfl⟩ : syracuseStep 3812615 = 5718923) B5718923
theorem B3223547 : Blo 1128631 3223547 := bstep (se 1 (by rfl) ⟨2417660, by rfl⟩ : syracuseStep 3223547 = 4835321) B4835321
theorem B5714063 : Blo 1128631 5714063 := bstep (se 1 (by rfl) ⟨4285547, by rfl⟩ : syracuseStep 5714063 = 8571095) B8571095
theorem B2142911 : Blo 1128631 2142911 := bstep (se 1 (by rfl) ⟨1607183, by rfl⟩ : syracuseStep 2142911 = 3214367) B3214367
theorem B46445561 : Blo 1128631 46445561 := bstep (se 2 (by rfl) ⟨17417085, by rfl⟩ : syracuseStep 46445561 = 34834171) B34834171
theorem B6108959 : Blo 1128631 6108959 := bstep (se 1 (by rfl) ⟨4581719, by rfl⟩ : syracuseStep 6108959 = 9163439) B9163439
theorem B7747721 : Blo 1128631 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B1128807 : Blo 1128631 1128807 := bstep (se 1 (by rfl) ⟨846605, by rfl⟩ : syracuseStep 1128807 = 1693211) B1693211
theorem B1129071 : Blo 1128631 1129071 := bstep (se 1 (by rfl) ⟨846803, by rfl⟩ : syracuseStep 1129071 = 1693607) B1693607
theorem B1129167 : Blo 1128631 1129167 := bstep (se 1 (by rfl) ⟨846875, by rfl⟩ : syracuseStep 1129167 = 1693751) B1693751
theorem B1129439 : Blo 1128631 1129439 := bstep (se 1 (by rfl) ⟨847079, by rfl⟩ : syracuseStep 1129439 = 1694159) B1694159
theorem B1129503 : Blo 1128631 1129503 := bstep (se 1 (by rfl) ⟨847127, by rfl⟩ : syracuseStep 1129503 = 1694255) B1694255
theorem B11615339 : Blo 1128631 11615339 := bstep (se 1 (by rfl) ⟨8711504, by rfl⟩ : syracuseStep 11615339 = 17423009) B17423009
theorem B1129639 : Blo 1128631 1129639 := bstep (se 1 (by rfl) ⟨847229, by rfl⟩ : syracuseStep 1129639 = 1694459) B1694459
theorem B2866387 : Blo 1128631 2866387 := bstep (se 1 (by rfl) ⟨2149790, by rfl⟩ : syracuseStep 2866387 = 4299581) B4299581
theorem B1129723 : Blo 1128631 1129723 := bstep (se 1 (by rfl) ⟨847292, by rfl⟩ : syracuseStep 1129723 = 1694585) B1694585
theorem B1129775 : Blo 1128631 1129775 := bstep (se 1 (by rfl) ⟨847331, by rfl⟩ : syracuseStep 1129775 = 1694663) B1694663
theorem B2145865 : Blo 1128631 2145865 := bstep (se 2 (by rfl) ⟨804699, by rfl⟩ : syracuseStep 2145865 = 1609399) B1609399
theorem B1130267 : Blo 1128631 1130267 := bstep (se 1 (by rfl) ⟨847700, by rfl⟩ : syracuseStep 1130267 = 1695401) B1695401
theorem B1130367 : Blo 1128631 1130367 := bstep (se 1 (by rfl) ⟨847775, by rfl⟩ : syracuseStep 1130367 = 1695551) B1695551
theorem B1130491 : Blo 1128631 1130491 := bstep (se 1 (by rfl) ⟨847868, by rfl⟩ : syracuseStep 1130491 = 1695737) B1695737
theorem B2539547 : Blo 1128631 2539547 := bstep (se 1 (by rfl) ⟨1904660, by rfl⟩ : syracuseStep 2539547 = 3809321) B3809321
theorem B1130663 : Blo 1128631 1130663 := bstep (se 1 (by rfl) ⟨847997, by rfl⟩ : syracuseStep 1130663 = 1695995) B1695995
theorem B2146601 : Blo 1128631 2146601 := bstep (se 2 (by rfl) ⟨804975, by rfl⟩ : syracuseStep 2146601 = 1609951) B1609951
theorem B1131099 : Blo 1128631 1131099 := bstep (se 1 (by rfl) ⟨848324, by rfl⟩ : syracuseStep 1131099 = 1696649) B1696649
theorem B1131263 : Blo 1128631 1131263 := bstep (se 1 (by rfl) ⟨848447, by rfl⟩ : syracuseStep 1131263 = 1696895) B1696895
theorem B1131355 : Blo 1128631 1131355 := bstep (se 1 (by rfl) ⟨848516, by rfl⟩ : syracuseStep 1131355 = 1697033) B1697033
theorem B2540447 : Blo 1128631 2540447 := bstep (se 1 (by rfl) ⟨1905335, by rfl⟩ : syracuseStep 2540447 = 3810671) B3810671
theorem B1131455 : Blo 1128631 1131455 := bstep (se 1 (by rfl) ⟨848591, by rfl⟩ : syracuseStep 1131455 = 1697183) B1697183
theorem B2540681 : Blo 1128631 2540681 := bstep (se 2 (by rfl) ⟨952755, by rfl⟩ : syracuseStep 2540681 = 1905511) B1905511
theorem B1131675 : Blo 1128631 1131675 := bstep (se 1 (by rfl) ⟨848756, by rfl⟩ : syracuseStep 1131675 = 1697513) B1697513
theorem B1131983 : Blo 1128631 1131983 := bstep (se 1 (by rfl) ⟨848987, by rfl⟩ : syracuseStep 1131983 = 1697975) B1697975
theorem B1132031 : Blo 1128631 1132031 := bstep (se 1 (by rfl) ⟨849023, by rfl⟩ : syracuseStep 1132031 = 1698047) B1698047
theorem B188565077 : Blo 1128631 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B1132135 : Blo 1128631 1132135 := bstep (se 1 (by rfl) ⟨849101, by rfl⟩ : syracuseStep 1132135 = 1698203) B1698203
theorem B1132379 : Blo 1128631 1132379 := bstep (se 1 (by rfl) ⟨849284, by rfl⟩ : syracuseStep 1132379 = 1698569) B1698569
theorem B5720057 : Blo 1128631 5720057 := bstep (se 2 (by rfl) ⟨2145021, by rfl⟩ : syracuseStep 5720057 = 4290043) B4290043
theorem B2541671 : Blo 1128631 2541671 := bstep (se 1 (by rfl) ⟨1906253, by rfl⟩ : syracuseStep 2541671 = 3812507) B3812507
theorem B2542535 : Blo 1128631 2542535 := bstep (se 1 (by rfl) ⟨1906901, by rfl⟩ : syracuseStep 2542535 = 3813803) B3813803
theorem B5721353 : Blo 1128631 5721353 := bstep (se 2 (by rfl) ⟨2145507, by rfl⟩ : syracuseStep 5721353 = 4291015) B4291015
theorem B3821471 : Blo 1128631 3821471 := bstep (se 1 (by rfl) ⟨2866103, by rfl⟩ : syracuseStep 3821471 = 5732207) B5732207
theorem B2543687 : Blo 1128631 2543687 := bstep (se 1 (by rfl) ⟨1907765, by rfl⟩ : syracuseStep 2543687 = 3815531) B3815531
theorem B8573039 : Blo 1128631 8573039 := bstep (se 1 (by rfl) ⟨6429779, by rfl⟩ : syracuseStep 8573039 = 12859559) B12859559
theorem B12210689 : Blo 1128631 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B16306751 : Blo 1128631 16306751 := bstep (se 1 (by rfl) ⟨12230063, by rfl⟩ : syracuseStep 16306751 = 24460127) B24460127
theorem B12898925 : Blo 1128631 12898925 := bstep (se 3 (by rfl) ⟨2418548, by rfl⟩ : syracuseStep 12898925 = 4837097) B4837097
theorem B2544335 : Blo 1128631 2544335 := bstep (se 1 (by rfl) ⟨1908251, by rfl⟩ : syracuseStep 2544335 = 3816503) B3816503
theorem B3822335 : Blo 1128631 3822335 := bstep (se 1 (by rfl) ⟨2866751, by rfl⟩ : syracuseStep 3822335 = 5733503) B5733503
theorem B2545199 : Blo 1128631 2545199 := bstep (se 1 (by rfl) ⟨1908899, by rfl⟩ : syracuseStep 2545199 = 3817799) B3817799
theorem B111368033 : Blo 1128631 111368033 := bstep (se 2 (by rfl) ⟨41763012, by rfl⟩ : syracuseStep 111368033 = 83526025) B83526025
theorem B12245255 : Blo 1128631 12245255 := bstep (se 1 (by rfl) ⟨9183941, by rfl⟩ : syracuseStep 12245255 = 18367883) B18367883
theorem B2546279 : Blo 1128631 2546279 := bstep (se 1 (by rfl) ⟨1909709, by rfl⟩ : syracuseStep 2546279 = 3819419) B3819419
theorem B2546459 : Blo 1128631 2546459 := bstep (se 1 (by rfl) ⟨1909844, by rfl⟩ : syracuseStep 2546459 = 3819689) B3819689
theorem B23518313 : Blo 1128631 23518313 := bstep (se 2 (by rfl) ⟨8819367, by rfl⟩ : syracuseStep 23518313 = 17638735) B17638735
theorem B1695131 : Blo 1128631 1695131 := bstep (se 1 (by rfl) ⟨1271348, by rfl⟩ : syracuseStep 1695131 = 2542697) B2542697
theorem B2547179 : Blo 1128631 2547179 := bstep (se 1 (by rfl) ⟨1910384, by rfl⟩ : syracuseStep 2547179 = 3820769) B3820769
theorem B2547431 : Blo 1128631 2547431 := bstep (se 1 (by rfl) ⟨1910573, by rfl⟩ : syracuseStep 2547431 = 3821147) B3821147
theorem B2547539 : Blo 1128631 2547539 := bstep (se 1 (by rfl) ⟨1910654, by rfl⟩ : syracuseStep 2547539 = 3821309) B3821309
theorem B2547593 : Blo 1128631 2547593 := bstep (se 2 (by rfl) ⟨955347, by rfl⟩ : syracuseStep 2547593 = 1910695) B1910695
theorem B1695839 : Blo 1128631 1695839 := bstep (se 1 (by rfl) ⟨1271879, by rfl⟩ : syracuseStep 1695839 = 2543759) B2543759
theorem B235168109 : Blo 1128631 235168109 := bstep (se 3 (by rfl) ⟨44094020, by rfl⟩ : syracuseStep 235168109 = 88188041) B88188041
theorem B1270363 : Blo 1128631 1270363 := bstep (se 1 (by rfl) ⟨952772, by rfl⟩ : syracuseStep 1270363 = 1905545) B1905545
theorem B1696937 : Blo 1128631 1696937 := bstep (se 2 (by rfl) ⟨636351, by rfl⟩ : syracuseStep 1696937 = 1272703) B1272703
theorem B1697087 : Blo 1128631 1697087 := bstep (se 1 (by rfl) ⟨1272815, by rfl⟩ : syracuseStep 1697087 = 2545631) B2545631
theorem B5793257 : Blo 1128631 5793257 := bstep (se 2 (by rfl) ⟨2172471, by rfl⟩ : syracuseStep 5793257 = 4344943) B4344943
theorem B8578871 : Blo 1128631 8578871 := bstep (se 1 (by rfl) ⟨6434153, by rfl⟩ : syracuseStep 8578871 = 12868307) B12868307
theorem B1697663 : Blo 1128631 1697663 := bstep (se 1 (by rfl) ⟨1273247, by rfl⟩ : syracuseStep 1697663 = 2546495) B2546495
theorem B1697855 : Blo 1128631 1697855 := bstep (se 1 (by rfl) ⟨1273391, by rfl⟩ : syracuseStep 1697855 = 2546783) B2546783
theorem B37152893 : Blo 1128631 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B1272559 : Blo 1128631 1272559 := bstep (se 1 (by rfl) ⟨954419, by rfl⟩ : syracuseStep 1272559 = 1908839) B1908839
theorem B4352825 : Blo 1128631 4352825 := bstep (se 2 (by rfl) ⟨1632309, by rfl⟩ : syracuseStep 4352825 = 3264619) B3264619
theorem B9301115 : Blo 1128631 9301115 := bstep (se 1 (by rfl) ⟨6975836, by rfl⟩ : syracuseStep 9301115 = 13951673) B13951673
theorem B162983987 : Blo 1128631 162983987 := bstep (se 1 (by rfl) ⟨122237990, by rfl⟩ : syracuseStep 162983987 = 244475981) B244475981
theorem B5730587 : Blo 1128631 5730587 := bstep (se 1 (by rfl) ⟨4297940, by rfl⟩ : syracuseStep 5730587 = 8595881) B8595881
theorem B4125415 : Blo 1128631 4125415 := bstep (se 1 (by rfl) ⟨3094061, by rfl⟩ : syracuseStep 4125415 = 6188123) B6188123
theorem B18314417 : Blo 1128631 18314417 := bstep (se 2 (by rfl) ⟨6867906, by rfl⟩ : syracuseStep 18314417 = 13735813) B13735813
theorem B125270279 : Blo 1128631 125270279 := bstep (se 1 (by rfl) ⟨93952709, by rfl⟩ : syracuseStep 125270279 = 187905419) B187905419
theorem B1696038365 : Blo 1128631 1696038365 := bstep (se 3 (by rfl) ⟨318007193, by rfl⟩ : syracuseStep 1696038365 = 636014387) B636014387
theorem B10878857 : Blo 1128631 10878857 := bstep (se 2 (by rfl) ⟨4079571, by rfl⟩ : syracuseStep 10878857 = 8159143) B8159143
theorem B4292945 : Blo 1128631 4292945 := bstep (se 2 (by rfl) ⟨1609854, by rfl⟩ : syracuseStep 4292945 = 3219709) B3219709
theorem B1835803 : Blo 1128631 1835803 := bstep (se 1 (by rfl) ⟨1376852, by rfl⟩ : syracuseStep 1835803 = 2753705) B2753705
theorem B20645239 : Blo 1128631 20645239 := bstep (se 1 (by rfl) ⟨15483929, by rfl⟩ : syracuseStep 20645239 = 30967859) B30967859
theorem B14879623 : Blo 1128631 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B27495845 : Blo 1128631 27495845 := bstep (se 4 (by rfl) ⟨2577735, by rfl⟩ : syracuseStep 27495845 = 5155471) B5155471
theorem B8163503 : Blo 1128631 8163503 := bstep (se 1 (by rfl) ⟨6122627, by rfl⟩ : syracuseStep 8163503 = 12245255) B12245255
theorem B3218399 : Blo 1128631 3218399 := bstep (se 1 (by rfl) ⟨2413799, by rfl⟩ : syracuseStep 3218399 = 4827599) B4827599
theorem B1908191 : Blo 1128631 1908191 := bstep (se 1 (by rfl) ⟨1431143, by rfl⟩ : syracuseStep 1908191 = 2862287) B2862287
theorem B11607533 : Blo 1128631 11607533 := bstep (se 3 (by rfl) ⟨2176412, by rfl⟩ : syracuseStep 11607533 = 4352825) B4352825
theorem B3809375 : Blo 1128631 3809375 := bstep (se 1 (by rfl) ⟨2857031, by rfl⟩ : syracuseStep 3809375 = 5714063) B5714063
theorem B4072639 : Blo 1128631 4072639 := bstep (se 1 (by rfl) ⟨3054479, by rfl⟩ : syracuseStep 4072639 = 6108959) B6108959
theorem B7743559 : Blo 1128631 7743559 := bstep (se 1 (by rfl) ⟨5807669, by rfl⟩ : syracuseStep 7743559 = 11615339) B11615339
theorem B2861153 : Blo 1128631 2861153 := bstep (se 2 (by rfl) ⟨1072932, by rfl⟩ : syracuseStep 2861153 = 2145865) B2145865
theorem B7252571 : Blo 1128631 7252571 := bstep (se 1 (by rfl) ⟨5439428, by rfl⟩ : syracuseStep 7252571 = 10878857) B10878857
theorem B125710051 : Blo 1128631 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B3813371 : Blo 1128631 3813371 := bstep (se 1 (by rfl) ⟨2860028, by rfl⟩ : syracuseStep 3813371 = 5720057) B5720057
theorem B3814235 : Blo 1128631 3814235 := bstep (se 1 (by rfl) ⟨2860676, by rfl⟩ : syracuseStep 3814235 = 5721353) B5721353
theorem B16299143 : Blo 1128631 16299143 := bstep (se 1 (by rfl) ⟨12224357, by rfl⟩ : syracuseStep 16299143 = 24448715) B24448715
theorem B5715359 : Blo 1128631 5715359 := bstep (se 1 (by rfl) ⟨4286519, by rfl⟩ : syracuseStep 5715359 = 8573039) B8573039
theorem B8140459 : Blo 1128631 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B8599283 : Blo 1128631 8599283 := bstep (se 1 (by rfl) ⟨6449462, by rfl⟩ : syracuseStep 8599283 = 12898925) B12898925
theorem B3815369 : Blo 1128631 3815369 := bstep (se 2 (by rfl) ⟨1430763, by rfl⟩ : syracuseStep 3815369 = 2861527) B2861527
theorem B1358623 : Blo 1128631 1358623 := bstep (se 1 (by rfl) ⟨1018967, by rfl⟩ : syracuseStep 1358623 = 2037935) B2037935
theorem B2866367 : Blo 1128631 2866367 := bstep (se 1 (by rfl) ⟨2149775, by rfl⟩ : syracuseStep 2866367 = 4299551) B4299551
theorem B15678875 : Blo 1128631 15678875 := bstep (se 1 (by rfl) ⟨11759156, by rfl⟩ : syracuseStep 15678875 = 23518313) B23518313
theorem B1130087 : Blo 1128631 1130087 := bstep (se 1 (by rfl) ⟨847565, by rfl⟩ : syracuseStep 1130087 = 1695131) B1695131
theorem B1130559 : Blo 1128631 1130559 := bstep (se 1 (by rfl) ⟨847919, by rfl⟩ : syracuseStep 1130559 = 1695839) B1695839
theorem B156778739 : Blo 1128631 156778739 := bstep (se 1 (by rfl) ⟨117584054, by rfl⟩ : syracuseStep 156778739 = 235168109) B235168109
theorem B2540087 : Blo 1128631 2540087 := bstep (se 1 (by rfl) ⟨1905065, by rfl⟩ : syracuseStep 2540087 = 3810131) B3810131
theorem B1131291 : Blo 1128631 1131291 := bstep (se 1 (by rfl) ⟨848468, by rfl⟩ : syracuseStep 1131291 = 1696937) B1696937
theorem B1131391 : Blo 1128631 1131391 := bstep (se 1 (by rfl) ⟨848543, by rfl⟩ : syracuseStep 1131391 = 1697087) B1697087
theorem B5719247 : Blo 1128631 5719247 := bstep (se 1 (by rfl) ⟨4289435, by rfl⟩ : syracuseStep 5719247 = 8578871) B8578871
theorem B1131775 : Blo 1128631 1131775 := bstep (se 1 (by rfl) ⟨848831, by rfl⟩ : syracuseStep 1131775 = 1697663) B1697663
theorem B1131903 : Blo 1128631 1131903 := bstep (se 1 (by rfl) ⟨848927, by rfl⟩ : syracuseStep 1131903 = 1697855) B1697855
theorem B2541743 : Blo 1128631 2541743 := bstep (se 1 (by rfl) ⟨1906307, by rfl⟩ : syracuseStep 2541743 = 3812615) B3812615
theorem B2149031 : Blo 1128631 2149031 := bstep (se 1 (by rfl) ⟨1611773, by rfl⟩ : syracuseStep 2149031 = 3223547) B3223547
theorem B3820391 : Blo 1128631 3820391 := bstep (se 1 (by rfl) ⟨2865293, by rfl⟩ : syracuseStep 3820391 = 5730587) B5730587
theorem B1428607 : Blo 1128631 1428607 := bstep (se 1 (by rfl) ⟨1071455, by rfl⟩ : syracuseStep 1428607 = 2142911) B2142911
theorem B12209611 : Blo 1128631 12209611 := bstep (se 1 (by rfl) ⟨9157208, by rfl⟩ : syracuseStep 12209611 = 18314417) B18314417
theorem B5165147 : Blo 1128631 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B83513519 : Blo 1128631 83513519 := bstep (se 1 (by rfl) ⟨62635139, by rfl⟩ : syracuseStep 83513519 = 125270279) B125270279
theorem B3821849 : Blo 1128631 3821849 := bstep (se 2 (by rfl) ⟨1433193, by rfl⟩ : syracuseStep 3821849 = 2866387) B2866387
theorem B1693031 : Blo 1128631 1693031 := bstep (se 1 (by rfl) ⟨1269773, by rfl⟩ : syracuseStep 1693031 = 2539547) B2539547
theorem B1693631 : Blo 1128631 1693631 := bstep (se 1 (by rfl) ⟨1270223, by rfl⟩ : syracuseStep 1693631 = 2540447) B2540447
theorem B1693787 : Blo 1128631 1693787 := bstep (se 1 (by rfl) ⟨1270340, by rfl⟩ : syracuseStep 1693787 = 2540681) B2540681
theorem B5724269 : Blo 1128631 5724269 := bstep (se 3 (by rfl) ⟨1073300, by rfl⟩ : syracuseStep 5724269 = 2146601) B2146601
theorem B1693817 : Blo 1128631 1693817 := bstep (se 2 (by rfl) ⟨635181, by rfl⟩ : syracuseStep 1693817 = 1270363) B1270363
theorem B1694447 : Blo 1128631 1694447 := bstep (se 1 (by rfl) ⟨1270835, by rfl⟩ : syracuseStep 1694447 = 2541671) B2541671
theorem B10312697 : Blo 1128631 10312697 := bstep (se 2 (by rfl) ⟨3867261, by rfl⟩ : syracuseStep 10312697 = 7734523) B7734523
theorem B12213287 : Blo 1128631 12213287 := bstep (se 1 (by rfl) ⟨9159965, by rfl⟩ : syracuseStep 12213287 = 18319931) B18319931
theorem B1695023 : Blo 1128631 1695023 := bstep (se 1 (by rfl) ⟨1271267, by rfl⟩ : syracuseStep 1695023 = 2542535) B2542535
theorem B2940809 : Blo 1128631 2940809 := bstep (se 2 (by rfl) ⟨1102803, by rfl⟩ : syracuseStep 2940809 = 2205607) B2205607
theorem B2547647 : Blo 1128631 2547647 := bstep (se 1 (by rfl) ⟨1910735, by rfl⟩ : syracuseStep 2547647 = 3821471) B3821471
theorem B1269787 : Blo 1128631 1269787 := bstep (se 1 (by rfl) ⟨952340, by rfl⟩ : syracuseStep 1269787 = 1904681) B1904681
theorem B1695791 : Blo 1128631 1695791 := bstep (se 1 (by rfl) ⟨1271843, by rfl⟩ : syracuseStep 1695791 = 2543687) B2543687
theorem B20635897 : Blo 1128631 20635897 := bstep (se 2 (by rfl) ⟨7738461, by rfl⟩ : syracuseStep 20635897 = 15476923) B15476923
theorem B10871167 : Blo 1128631 10871167 := bstep (se 1 (by rfl) ⟨8153375, by rfl⟩ : syracuseStep 10871167 = 16306751) B16306751
theorem B1696223 : Blo 1128631 1696223 := bstep (se 1 (by rfl) ⟨1272167, by rfl⟩ : syracuseStep 1696223 = 2544335) B2544335
theorem B1270255 : Blo 1128631 1270255 := bstep (se 1 (by rfl) ⟨952691, by rfl⟩ : syracuseStep 1270255 = 1905383) B1905383
theorem B2548223 : Blo 1128631 2548223 := bstep (se 1 (by rfl) ⟨1911167, by rfl⟩ : syracuseStep 2548223 = 3822335) B3822335
theorem B1696745 : Blo 1128631 1696745 := bstep (se 2 (by rfl) ⟨636279, by rfl⟩ : syracuseStep 1696745 = 1272559) B1272559
theorem B1696799 : Blo 1128631 1696799 := bstep (se 1 (by rfl) ⟨1272599, by rfl⟩ : syracuseStep 1696799 = 2545199) B2545199
theorem B74245355 : Blo 1128631 74245355 := bstep (se 1 (by rfl) ⟨55684016, by rfl⟩ : syracuseStep 74245355 = 111368033) B111368033
theorem B1697519 : Blo 1128631 1697519 := bstep (se 1 (by rfl) ⟨1273139, by rfl⟩ : syracuseStep 1697519 = 2546279) B2546279
theorem B1697639 : Blo 1128631 1697639 := bstep (se 1 (by rfl) ⟨1273229, by rfl⟩ : syracuseStep 1697639 = 2546459) B2546459
theorem B1206127 : Blo 1128631 1206127 := bstep (se 1 (by rfl) ⟨904595, by rfl⟩ : syracuseStep 1206127 = 1809191) B1809191
theorem B1271911 : Blo 1128631 1271911 := bstep (se 1 (by rfl) ⟨953933, by rfl⟩ : syracuseStep 1271911 = 1907867) B1907867
theorem B1698119 : Blo 1128631 1698119 := bstep (se 1 (by rfl) ⟨1273589, by rfl⟩ : syracuseStep 1698119 = 2547179) B2547179
theorem B3303919 : Blo 1128631 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B1698287 : Blo 1128631 1698287 := bstep (se 1 (by rfl) ⟨1273715, by rfl⟩ : syracuseStep 1698287 = 2547431) B2547431
theorem B1698359 : Blo 1128631 1698359 := bstep (se 1 (by rfl) ⟨1273769, by rfl⟩ : syracuseStep 1698359 = 2547539) B2547539
theorem B1698395 : Blo 1128631 1698395 := bstep (se 1 (by rfl) ⟨1273796, by rfl⟩ : syracuseStep 1698395 = 2547593) B2547593
theorem B5500553 : Blo 1128631 5500553 := bstep (se 2 (by rfl) ⟨2062707, by rfl⟩ : syracuseStep 5500553 = 4125415) B4125415
theorem B3862171 : Blo 1128631 3862171 := bstep (se 1 (by rfl) ⟨2896628, by rfl⟩ : syracuseStep 3862171 = 5793257) B5793257
theorem B1273855 : Blo 1128631 1273855 := bstep (se 1 (by rfl) ⟨955391, by rfl⟩ : syracuseStep 1273855 = 1910783) B1910783
theorem B24768595 : Blo 1128631 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B49574045 : Blo 1128631 49574045 := bstep (se 3 (by rfl) ⟨9295133, by rfl⟩ : syracuseStep 49574045 = 18590267) B18590267
theorem B3436787 : Blo 1128631 3436787 := bstep (se 1 (by rfl) ⟨2577590, by rfl⟩ : syracuseStep 3436787 = 5155181) B5155181
theorem B108655991 : Blo 1128631 108655991 := bstep (se 1 (by rfl) ⟨81491993, by rfl⟩ : syracuseStep 108655991 = 162983987) B162983987
theorem B24802973 : Blo 1128631 24802973 := bstep (se 3 (by rfl) ⟨4650557, by rfl⟩ : syracuseStep 24802973 = 9301115) B9301115
theorem B30963707 : Blo 1128631 30963707 := bstep (se 1 (by rfl) ⟨23222780, by rfl⟩ : syracuseStep 30963707 = 46445561) B46445561
theorem B1130692243 : Blo 1128631 1130692243 := bstep (se 1 (by rfl) ⟨848019182, by rfl⟩ : syracuseStep 1130692243 = 1696038365) B1696038365
theorem B27526985 : Blo 1128631 27526985 := bstep (se 2 (by rfl) ⟨10322619, by rfl⟩ : syracuseStep 27526985 = 20645239) B20645239
theorem B1608169 : Blo 1128631 1608169 := bstep (se 2 (by rfl) ⟨603063, by rfl⟩ : syracuseStep 1608169 = 1206127) B1206127
theorem B10324745 : Blo 1128631 10324745 := bstep (se 2 (by rfl) ⟨3871779, by rfl⟩ : syracuseStep 10324745 = 7743559) B7743559
theorem B55675679 : Blo 1128631 55675679 := bstep (se 1 (by rfl) ⟨41756759, by rfl⟩ : syracuseStep 55675679 = 83513519) B83513519
theorem B5442335 : Blo 1128631 5442335 := bstep (se 1 (by rfl) ⟨4081751, by rfl⟩ : syracuseStep 5442335 = 8163503) B8163503
theorem B1904809 : Blo 1128631 1904809 := bstep (se 2 (by rfl) ⟨714303, by rfl⟩ : syracuseStep 1904809 = 1428607) B1428607
theorem B167613401 : Blo 1128631 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B7738355 : Blo 1128631 7738355 := bstep (se 1 (by rfl) ⟨5803766, by rfl⟩ : syracuseStep 7738355 = 11607533) B11607533
theorem B1907435 : Blo 1128631 1907435 := bstep (se 1 (by rfl) ⟨1430576, by rfl⟩ : syracuseStep 1907435 = 2861153) B2861153
theorem B10853945 : Blo 1128631 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B3810239 : Blo 1128631 3810239 := bstep (se 1 (by rfl) ⟨2857679, by rfl⟩ : syracuseStep 3810239 = 5715359) B5715359
theorem B1811497 : Blo 1128631 1811497 := bstep (se 2 (by rfl) ⟨679311, by rfl⟩ : syracuseStep 1811497 = 1358623) B1358623
theorem B31368629 : Blo 1128631 31368629 := bstep (se 5 (by rfl) ⟨1470404, by rfl⟩ : syracuseStep 31368629 = 2940809) B2940809
theorem B1910911 : Blo 1128631 1910911 := bstep (se 1 (by rfl) ⟨1433183, by rfl⟩ : syracuseStep 1910911 = 2866367) B2866367
theorem B2861963 : Blo 1128631 2861963 := bstep (se 1 (by rfl) ⟨2146472, by rfl⟩ : syracuseStep 2861963 = 4292945) B4292945
theorem B13773725 : Blo 1128631 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B132197453 : Blo 1128631 132197453 := bstep (se 3 (by rfl) ⟨24787022, by rfl⟩ : syracuseStep 132197453 = 49574045) B49574045
theorem B132099173 : Blo 1128631 132099173 := bstep (se 4 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 132099173 = 24768595) B24768595
theorem B14494889 : Blo 1128631 14494889 := bstep (se 2 (by rfl) ⟨5435583, by rfl⟩ : syracuseStep 14494889 = 10871167) B10871167
theorem B3812831 : Blo 1128631 3812831 := bstep (se 1 (by rfl) ⟨2859623, by rfl⟩ : syracuseStep 3812831 = 5719247) B5719247
theorem B18330563 : Blo 1128631 18330563 := bstep (se 1 (by rfl) ⟨13747922, by rfl⟩ : syracuseStep 18330563 = 27495845) B27495845
theorem B1128687 : Blo 1128631 1128687 := bstep (se 1 (by rfl) ⟨846515, by rfl⟩ : syracuseStep 1128687 = 1693031) B1693031
theorem B19839497 : Blo 1128631 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B1129087 : Blo 1128631 1129087 := bstep (se 1 (by rfl) ⟨846815, by rfl⟩ : syracuseStep 1129087 = 1693631) B1693631
theorem B1129191 : Blo 1128631 1129191 := bstep (se 1 (by rfl) ⟨846893, by rfl⟩ : syracuseStep 1129191 = 1693787) B1693787
theorem B3816179 : Blo 1128631 3816179 := bstep (se 1 (by rfl) ⟨2862134, by rfl⟩ : syracuseStep 3816179 = 5724269) B5724269
theorem B1129211 : Blo 1128631 1129211 := bstep (se 1 (by rfl) ⟨846908, by rfl⟩ : syracuseStep 1129211 = 1693817) B1693817
theorem B1129631 : Blo 1128631 1129631 := bstep (se 1 (by rfl) ⟨847223, by rfl⟩ : syracuseStep 1129631 = 1694447) B1694447
theorem B2145599 : Blo 1128631 2145599 := bstep (se 1 (by rfl) ⟨1609199, by rfl⟩ : syracuseStep 2145599 = 3218399) B3218399
theorem B8142191 : Blo 1128631 8142191 := bstep (se 1 (by rfl) ⟨6106643, by rfl⟩ : syracuseStep 8142191 = 12213287) B12213287
theorem B1130015 : Blo 1128631 1130015 := bstep (se 1 (by rfl) ⟨847511, by rfl⟩ : syracuseStep 1130015 = 1695023) B1695023
theorem B1130527 : Blo 1128631 1130527 := bstep (se 1 (by rfl) ⟨847895, by rfl⟩ : syracuseStep 1130527 = 1695791) B1695791
theorem B2539583 : Blo 1128631 2539583 := bstep (se 1 (by rfl) ⟨1904687, by rfl⟩ : syracuseStep 2539583 = 3809375) B3809375
theorem B1130815 : Blo 1128631 1130815 := bstep (se 1 (by rfl) ⟨848111, by rfl⟩ : syracuseStep 1130815 = 1696223) B1696223
theorem B1131163 : Blo 1128631 1131163 := bstep (se 1 (by rfl) ⟨848372, by rfl⟩ : syracuseStep 1131163 = 1696745) B1696745
theorem B1131199 : Blo 1128631 1131199 := bstep (se 1 (by rfl) ⟨848399, by rfl⟩ : syracuseStep 1131199 = 1696799) B1696799
theorem B49496903 : Blo 1128631 49496903 := bstep (se 1 (by rfl) ⟨37122677, by rfl⟩ : syracuseStep 49496903 = 74245355) B74245355
theorem B1131679 : Blo 1128631 1131679 := bstep (se 1 (by rfl) ⟨848759, by rfl⟩ : syracuseStep 1131679 = 1697519) B1697519
theorem B1131759 : Blo 1128631 1131759 := bstep (se 1 (by rfl) ⟨848819, by rfl⟩ : syracuseStep 1131759 = 1697639) B1697639
theorem B1132079 : Blo 1128631 1132079 := bstep (se 1 (by rfl) ⟨849059, by rfl⟩ : syracuseStep 1132079 = 1698119) B1698119
theorem B1132191 : Blo 1128631 1132191 := bstep (se 1 (by rfl) ⟨849143, by rfl⟩ : syracuseStep 1132191 = 1698287) B1698287
theorem B1132239 : Blo 1128631 1132239 := bstep (se 1 (by rfl) ⟨849179, by rfl⟩ : syracuseStep 1132239 = 1698359) B1698359
theorem B4835047 : Blo 1128631 4835047 := bstep (se 1 (by rfl) ⟨3626285, by rfl⟩ : syracuseStep 4835047 = 7252571) B7252571
theorem B1132263 : Blo 1128631 1132263 := bstep (se 1 (by rfl) ⟨849197, by rfl⟩ : syracuseStep 1132263 = 1698395) B1698395
theorem B2542247 : Blo 1128631 2542247 := bstep (se 1 (by rfl) ⟨1906685, by rfl⟩ : syracuseStep 2542247 = 3813371) B3813371
theorem B2542823 : Blo 1128631 2542823 := bstep (se 1 (by rfl) ⟨1907117, by rfl⟩ : syracuseStep 2542823 = 3814235) B3814235
theorem B10866095 : Blo 1128631 10866095 := bstep (se 1 (by rfl) ⟨8149571, by rfl⟩ : syracuseStep 10866095 = 16299143) B16299143
theorem B20598245 : Blo 1128631 20598245 := bstep (se 4 (by rfl) ⟨1931085, by rfl⟩ : syracuseStep 20598245 = 3862171) B3862171
theorem B72437327 : Blo 1128631 72437327 := bstep (se 1 (by rfl) ⟨54327995, by rfl⟩ : syracuseStep 72437327 = 108655991) B108655991
theorem B16535315 : Blo 1128631 16535315 := bstep (se 1 (by rfl) ⟨12401486, by rfl⟩ : syracuseStep 16535315 = 24802973) B24802973
theorem B2543579 : Blo 1128631 2543579 := bstep (se 1 (by rfl) ⟨1907684, by rfl⟩ : syracuseStep 2543579 = 3815369) B3815369
theorem B14668141 : Blo 1128631 14668141 := bstep (se 3 (by rfl) ⟨2750276, by rfl⟩ : syracuseStep 14668141 = 5500553) B5500553
theorem B1693049 : Blo 1128631 1693049 := bstep (se 2 (by rfl) ⟨634893, by rfl⟩ : syracuseStep 1693049 = 1269787) B1269787
theorem B104519159 : Blo 1128631 104519159 := bstep (se 1 (by rfl) ⟨78389369, by rfl⟩ : syracuseStep 104519159 = 156778739) B156778739
theorem B27514529 : Blo 1128631 27514529 := bstep (se 2 (by rfl) ⟨10317948, by rfl⟩ : syracuseStep 27514529 = 20635897) B20635897
theorem B1693391 : Blo 1128631 1693391 := bstep (se 1 (by rfl) ⟨1270043, by rfl⟩ : syracuseStep 1693391 = 2540087) B2540087
theorem B9164765 : Blo 1128631 9164765 := bstep (se 3 (by rfl) ⟨1718393, by rfl⟩ : syracuseStep 9164765 = 3436787) B3436787
theorem B1693673 : Blo 1128631 1693673 := bstep (se 2 (by rfl) ⟨635127, by rfl⟩ : syracuseStep 1693673 = 1270255) B1270255
theorem B1694495 : Blo 1128631 1694495 := bstep (se 1 (by rfl) ⟨1270871, by rfl⟩ : syracuseStep 1694495 = 2541743) B2541743
theorem B5430185 : Blo 1128631 5430185 := bstep (se 2 (by rfl) ⟨2036319, by rfl⟩ : syracuseStep 5430185 = 4072639) B4072639
theorem B2546927 : Blo 1128631 2546927 := bstep (se 1 (by rfl) ⟨1910195, by rfl⟩ : syracuseStep 2546927 = 3820391) B3820391
theorem B17620901 : Blo 1128631 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B1695881 : Blo 1128631 1695881 := bstep (se 2 (by rfl) ⟨635955, by rfl⟩ : syracuseStep 1695881 = 1271911) B1271911
theorem B2547899 : Blo 1128631 2547899 := bstep (se 1 (by rfl) ⟨1910924, by rfl⟩ : syracuseStep 2547899 = 3821849) B3821849
theorem B9790949 : Blo 1128631 9790949 := bstep (se 4 (by rfl) ⟨917901, by rfl⟩ : syracuseStep 9790949 = 1835803) B1835803
theorem B16279481 : Blo 1128631 16279481 := bstep (se 2 (by rfl) ⟨6104805, by rfl⟩ : syracuseStep 16279481 = 12209611) B12209611
theorem B6875131 : Blo 1128631 6875131 := bstep (se 1 (by rfl) ⟨5156348, by rfl⟩ : syracuseStep 6875131 = 10312697) B10312697
theorem B1272127 : Blo 1128631 1272127 := bstep (se 1 (by rfl) ⟨954095, by rfl⟩ : syracuseStep 1272127 = 1908191) B1908191
theorem B1698431 : Blo 1128631 1698431 := bstep (se 1 (by rfl) ⟨1273823, by rfl⟩ : syracuseStep 1698431 = 2547647) B2547647
theorem B1698473 : Blo 1128631 1698473 := bstep (se 2 (by rfl) ⟨636927, by rfl⟩ : syracuseStep 1698473 = 1273855) B1273855
theorem B1698815 : Blo 1128631 1698815 := bstep (se 1 (by rfl) ⟨1274111, by rfl⟩ : syracuseStep 1698815 = 2548223) B2548223
theorem B5730749 : Blo 1128631 5730749 := bstep (se 3 (by rfl) ⟨1074515, by rfl⟩ : syracuseStep 5730749 = 2149031) B2149031
theorem B5732855 : Blo 1128631 5732855 := bstep (se 1 (by rfl) ⟨4299641, by rfl⟩ : syracuseStep 5732855 = 8599283) B8599283
theorem B20642471 : Blo 1128631 20642471 := bstep (se 1 (by rfl) ⟨15481853, by rfl⟩ : syracuseStep 20642471 = 30963707) B30963707
theorem B1507589657 : Blo 1128631 1507589657 := bstep (se 2 (by rfl) ⟨565346121, by rfl⟩ : syracuseStep 1507589657 = 1130692243) B1130692243
theorem B10452583 : Blo 1128631 10452583 := bstep (se 1 (by rfl) ⟨7839437, by rfl⟩ : syracuseStep 10452583 = 15678875) B15678875
theorem B32997935 : Blo 1128631 32997935 := bstep (se 1 (by rfl) ⟨24748451, by rfl⟩ : syracuseStep 32997935 = 49496903) B49496903
theorem B18351323 : Blo 1128631 18351323 := bstep (se 1 (by rfl) ⟨13763492, by rfl⟩ : syracuseStep 18351323 = 27526985) B27526985
theorem B6883163 : Blo 1128631 6883163 := bstep (se 1 (by rfl) ⟨5162372, by rfl⟩ : syracuseStep 6883163 = 10324745) B10324745
theorem B7244063 : Blo 1128631 7244063 := bstep (se 1 (by rfl) ⟨5433047, by rfl⟩ : syracuseStep 7244063 = 10866095) B10866095
theorem B13732163 : Blo 1128631 13732163 := bstep (se 1 (by rfl) ⟨10299122, by rfl⟩ : syracuseStep 13732163 = 20598245) B20598245
theorem B111742267 : Blo 1128631 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B20912419 : Blo 1128631 20912419 := bstep (se 1 (by rfl) ⟨15684314, by rfl⟩ : syracuseStep 20912419 = 31368629) B31368629
theorem B6527299 : Blo 1128631 6527299 := bstep (se 1 (by rfl) ⟨4895474, by rfl⟩ : syracuseStep 6527299 = 9790949) B9790949
theorem B10852987 : Blo 1128631 10852987 := bstep (se 1 (by rfl) ⟨8139740, by rfl⟩ : syracuseStep 10852987 = 16279481) B16279481
theorem B1907975 : Blo 1128631 1907975 := bstep (se 1 (by rfl) ⟨1430981, by rfl⟩ : syracuseStep 1907975 = 2861963) B2861963
theorem B9182483 : Blo 1128631 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B55747109 : Blo 1128631 55747109 := bstep (se 4 (by rfl) ⟨5226291, by rfl⟩ : syracuseStep 55747109 = 10452583) B10452583
theorem B11023543 : Blo 1128631 11023543 := bstep (se 1 (by rfl) ⟨8267657, by rfl⟩ : syracuseStep 11023543 = 16535315) B16535315
theorem B2144225 : Blo 1128631 2144225 := bstep (se 2 (by rfl) ⟨804084, by rfl⟩ : syracuseStep 2144225 = 1608169) B1608169
theorem B5158903 : Blo 1128631 5158903 := bstep (se 1 (by rfl) ⟨3869177, by rfl⟩ : syracuseStep 5158903 = 7738355) B7738355
theorem B1128699 : Blo 1128631 1128699 := bstep (se 1 (by rfl) ⟨846524, by rfl⟩ : syracuseStep 1128699 = 1693049) B1693049
theorem B69679439 : Blo 1128631 69679439 := bstep (se 1 (by rfl) ⟨52259579, by rfl⟩ : syracuseStep 69679439 = 104519159) B104519159
theorem B1128927 : Blo 1128631 1128927 := bstep (se 1 (by rfl) ⟨846695, by rfl⟩ : syracuseStep 1128927 = 1693391) B1693391
theorem B6109843 : Blo 1128631 6109843 := bstep (se 1 (by rfl) ⟨4582382, by rfl⟩ : syracuseStep 6109843 = 9164765) B9164765
theorem B1129115 : Blo 1128631 1129115 := bstep (se 1 (by rfl) ⟨846836, by rfl⟩ : syracuseStep 1129115 = 1693673) B1693673
theorem B1129663 : Blo 1128631 1129663 := bstep (se 1 (by rfl) ⟨847247, by rfl⟩ : syracuseStep 1129663 = 1694495) B1694495
theorem B3620123 : Blo 1128631 3620123 := bstep (se 1 (by rfl) ⟨2715092, by rfl⟩ : syracuseStep 3620123 = 5430185) B5430185
theorem B11747267 : Blo 1128631 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B1130587 : Blo 1128631 1130587 := bstep (se 1 (by rfl) ⟨847940, by rfl⟩ : syracuseStep 1130587 = 1695881) B1695881
theorem B2539745 : Blo 1128631 2539745 := bstep (se 2 (by rfl) ⟨952404, by rfl⟩ : syracuseStep 2539745 = 1904809) B1904809
theorem B2540159 : Blo 1128631 2540159 := bstep (se 1 (by rfl) ⟨1905119, by rfl⟩ : syracuseStep 2540159 = 3810239) B3810239
theorem B52905325 : Blo 1128631 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B1132287 : Blo 1128631 1132287 := bstep (se 1 (by rfl) ⟨849215, by rfl⟩ : syracuseStep 1132287 = 1698431) B1698431
theorem B1132315 : Blo 1128631 1132315 := bstep (se 1 (by rfl) ⟨849236, by rfl⟩ : syracuseStep 1132315 = 1698473) B1698473
theorem B1132543 : Blo 1128631 1132543 := bstep (se 1 (by rfl) ⟨849407, by rfl⟩ : syracuseStep 1132543 = 1698815) B1698815
theorem B88131635 : Blo 1128631 88131635 := bstep (se 1 (by rfl) ⟨66098726, by rfl⟩ : syracuseStep 88131635 = 132197453) B132197453
theorem B88066115 : Blo 1128631 88066115 := bstep (se 1 (by rfl) ⟨66049586, by rfl⟩ : syracuseStep 88066115 = 132099173) B132099173
theorem B2541887 : Blo 1128631 2541887 := bstep (se 1 (by rfl) ⟨1906415, by rfl⟩ : syracuseStep 2541887 = 3812831) B3812831
theorem B3820499 : Blo 1128631 3820499 := bstep (se 1 (by rfl) ⟨2865374, by rfl⟩ : syracuseStep 3820499 = 5730749) B5730749
theorem B3821903 : Blo 1128631 3821903 := bstep (se 1 (by rfl) ⟨2866427, by rfl⟩ : syracuseStep 3821903 = 5732855) B5732855
theorem B2544119 : Blo 1128631 2544119 := bstep (se 1 (by rfl) ⟨1908089, by rfl⟩ : syracuseStep 2544119 = 3816179) B3816179
theorem B1430399 : Blo 1128631 1430399 := bstep (se 1 (by rfl) ⟨1072799, by rfl⟩ : syracuseStep 1430399 = 2145599) B2145599
theorem B5428127 : Blo 1128631 5428127 := bstep (se 1 (by rfl) ⟨4071095, by rfl⟩ : syracuseStep 5428127 = 8142191) B8142191
theorem B1693055 : Blo 1128631 1693055 := bstep (se 1 (by rfl) ⟨1269791, by rfl⟩ : syracuseStep 1693055 = 2539583) B2539583
theorem B2415329 : Blo 1128631 2415329 := bstep (se 2 (by rfl) ⟨905748, by rfl⟩ : syracuseStep 2415329 = 1811497) B1811497
theorem B1694831 : Blo 1128631 1694831 := bstep (se 1 (by rfl) ⟨1271123, by rfl⟩ : syracuseStep 1694831 = 2542247) B2542247
theorem B3628223 : Blo 1128631 3628223 := bstep (se 1 (by rfl) ⟨2721167, by rfl⟩ : syracuseStep 3628223 = 5442335) B5442335
theorem B1695215 : Blo 1128631 1695215 := bstep (se 1 (by rfl) ⟨1271411, by rfl⟩ : syracuseStep 1695215 = 2542823) B2542823
theorem B6446729 : Blo 1128631 6446729 := bstep (se 2 (by rfl) ⟨2417523, by rfl⟩ : syracuseStep 6446729 = 4835047) B4835047
theorem B48291551 : Blo 1128631 48291551 := bstep (se 1 (by rfl) ⟨36218663, by rfl⟩ : syracuseStep 48291551 = 72437327) B72437327
theorem B48881501 : Blo 1128631 48881501 := bstep (se 3 (by rfl) ⟨9165281, by rfl⟩ : syracuseStep 48881501 = 18330563) B18330563
theorem B1695719 : Blo 1128631 1695719 := bstep (se 1 (by rfl) ⟨1271789, by rfl⟩ : syracuseStep 1695719 = 2543579) B2543579
theorem B9166841 : Blo 1128631 9166841 := bstep (se 2 (by rfl) ⟨3437565, by rfl⟩ : syracuseStep 9166841 = 6875131) B6875131
theorem B2547881 : Blo 1128631 2547881 := bstep (se 2 (by rfl) ⟨955455, by rfl⟩ : syracuseStep 2547881 = 1910911) B1910911
theorem B1696169 : Blo 1128631 1696169 := bstep (se 2 (by rfl) ⟨636063, by rfl⟩ : syracuseStep 1696169 = 1272127) B1272127
theorem B18343019 : Blo 1128631 18343019 := bstep (se 1 (by rfl) ⟨13757264, by rfl⟩ : syracuseStep 18343019 = 27514529) B27514529
theorem B1271623 : Blo 1128631 1271623 := bstep (se 1 (by rfl) ⟨953717, by rfl⟩ : syracuseStep 1271623 = 1907435) B1907435
theorem B1697951 : Blo 1128631 1697951 := bstep (se 1 (by rfl) ⟨1273463, by rfl⟩ : syracuseStep 1697951 = 2546927) B2546927
theorem B7235963 : Blo 1128631 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B1698599 : Blo 1128631 1698599 := bstep (se 1 (by rfl) ⟨1273949, by rfl⟩ : syracuseStep 1698599 = 2547899) B2547899
theorem B19557521 : Blo 1128631 19557521 := bstep (se 2 (by rfl) ⟨7334070, by rfl⟩ : syracuseStep 19557521 = 14668141) B14668141
theorem B148468477 : Blo 1128631 148468477 := bstep (se 3 (by rfl) ⟨27837839, by rfl⟩ : syracuseStep 148468477 = 55675679) B55675679
theorem B9663259 : Blo 1128631 9663259 := bstep (se 1 (by rfl) ⟨7247444, by rfl⟩ : syracuseStep 9663259 = 14494889) B14494889
theorem B13761647 : Blo 1128631 13761647 := bstep (se 1 (by rfl) ⟨10321235, by rfl⟩ : syracuseStep 13761647 = 20642471) B20642471
theorem B1005059771 : Blo 1128631 1005059771 := bstep (se 1 (by rfl) ⟨753794828, by rfl⟩ : syracuseStep 1005059771 = 1507589657) B1507589657
theorem B4588775 : Blo 1128631 4588775 := bstep (se 1 (by rfl) ⟨3441581, by rfl⟩ : syracuseStep 4588775 = 6883163) B6883163
theorem B58754423 : Blo 1128631 58754423 := bstep (se 1 (by rfl) ⟨44065817, by rfl⟩ : syracuseStep 58754423 = 88131635) B88131635
theorem B1610219 : Blo 1128631 1610219 := bstep (se 1 (by rfl) ⟨1207664, by rfl⟩ : syracuseStep 1610219 = 2415329) B2415329
theorem B4297819 : Blo 1128631 4297819 := bstep (se 1 (by rfl) ⟨3223364, by rfl⟩ : syracuseStep 4297819 = 6446729) B6446729
theorem B37164739 : Blo 1128631 37164739 := bstep (se 1 (by rfl) ⟨27873554, by rfl⟩ : syracuseStep 37164739 = 55747109) B55747109
theorem B12228679 : Blo 1128631 12228679 := bstep (se 1 (by rfl) ⟨9171509, by rfl⟩ : syracuseStep 12228679 = 18343019) B18343019
theorem B197957969 : Blo 1128631 197957969 := bstep (se 2 (by rfl) ⟨74234238, by rfl⟩ : syracuseStep 197957969 = 148468477) B148468477
theorem B12884345 : Blo 1128631 12884345 := bstep (se 2 (by rfl) ⟨4831629, by rfl⟩ : syracuseStep 12884345 = 9663259) B9663259
theorem B4823975 : Blo 1128631 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B21998623 : Blo 1128631 21998623 := bstep (se 1 (by rfl) ⟨16498967, by rfl⟩ : syracuseStep 21998623 = 32997935) B32997935
theorem B12234215 : Blo 1128631 12234215 := bstep (se 1 (by rfl) ⟨9175661, by rfl⟩ : syracuseStep 12234215 = 18351323) B18351323
theorem B4829375 : Blo 1128631 4829375 := bstep (se 1 (by rfl) ⟨3622031, by rfl⟩ : syracuseStep 4829375 = 7244063) B7244063
theorem B9154775 : Blo 1128631 9154775 := bstep (se 1 (by rfl) ⟨6866081, by rfl⟩ : syracuseStep 9154775 = 13732163) B13732163
theorem B3814397 : Blo 1128631 3814397 := bstep (se 3 (by rfl) ⟨715199, by rfl⟩ : syracuseStep 3814397 = 1430399) B1430399
theorem B3618751 : Blo 1128631 3618751 := bstep (se 1 (by rfl) ⟨2714063, by rfl⟩ : syracuseStep 3618751 = 5428127) B5428127
theorem B1128703 : Blo 1128631 1128703 := bstep (se 1 (by rfl) ⟨846527, by rfl⟩ : syracuseStep 1128703 = 1693055) B1693055
theorem B1129887 : Blo 1128631 1129887 := bstep (se 1 (by rfl) ⟨847415, by rfl⟩ : syracuseStep 1129887 = 1694831) B1694831
theorem B1130143 : Blo 1128631 1130143 := bstep (se 1 (by rfl) ⟨847607, by rfl⟩ : syracuseStep 1130143 = 1695215) B1695215
theorem B32194367 : Blo 1128631 32194367 := bstep (se 1 (by rfl) ⟨24145775, by rfl⟩ : syracuseStep 32194367 = 48291551) B48291551
theorem B32587667 : Blo 1128631 32587667 := bstep (se 1 (by rfl) ⟨24440750, by rfl⟩ : syracuseStep 32587667 = 48881501) B48881501
theorem B1130479 : Blo 1128631 1130479 := bstep (se 1 (by rfl) ⟨847859, by rfl⟩ : syracuseStep 1130479 = 1695719) B1695719
theorem B6111227 : Blo 1128631 6111227 := bstep (se 1 (by rfl) ⟨4583420, by rfl⟩ : syracuseStep 6111227 = 9166841) B9166841
theorem B1130779 : Blo 1128631 1130779 := bstep (se 1 (by rfl) ⟨848084, by rfl⟩ : syracuseStep 1130779 = 1696169) B1696169
theorem B1131967 : Blo 1128631 1131967 := bstep (se 1 (by rfl) ⟨848975, by rfl⟩ : syracuseStep 1131967 = 1697951) B1697951
theorem B14698057 : Blo 1128631 14698057 := bstep (se 2 (by rfl) ⟨5511771, by rfl⟩ : syracuseStep 14698057 = 11023543) B11023543
theorem B1132399 : Blo 1128631 1132399 := bstep (se 1 (by rfl) ⟨849299, by rfl⟩ : syracuseStep 1132399 = 1698599) B1698599
theorem B8703065 : Blo 1128631 8703065 := bstep (se 2 (by rfl) ⟨3263649, by rfl⟩ : syracuseStep 8703065 = 6527299) B6527299
theorem B14470649 : Blo 1128631 14470649 := bstep (se 2 (by rfl) ⟨5426493, by rfl⟩ : syracuseStep 14470649 = 10852987) B10852987
theorem B8146457 : Blo 1128631 8146457 := bstep (se 2 (by rfl) ⟨3054921, by rfl⟩ : syracuseStep 8146457 = 6109843) B6109843
theorem B1429483 : Blo 1128631 1429483 := bstep (se 1 (by rfl) ⟨1072112, by rfl⟩ : syracuseStep 1429483 = 2144225) B2144225
theorem B46452959 : Blo 1128631 46452959 := bstep (se 1 (by rfl) ⟨34839719, by rfl⟩ : syracuseStep 46452959 = 69679439) B69679439
theorem B2413415 : Blo 1128631 2413415 := bstep (se 1 (by rfl) ⟨1810061, by rfl⟩ : syracuseStep 2413415 = 3620123) B3620123
theorem B1693163 : Blo 1128631 1693163 := bstep (se 1 (by rfl) ⟨1269872, by rfl⟩ : syracuseStep 1693163 = 2539745) B2539745
theorem B1693439 : Blo 1128631 1693439 := bstep (se 1 (by rfl) ⟨1270079, by rfl⟩ : syracuseStep 1693439 = 2540159) B2540159
theorem B58710743 : Blo 1128631 58710743 := bstep (se 1 (by rfl) ⟨44033057, by rfl⟩ : syracuseStep 58710743 = 88066115) B88066115
theorem B1694591 : Blo 1128631 1694591 := bstep (se 1 (by rfl) ⟨1270943, by rfl⟩ : syracuseStep 1694591 = 2541887) B2541887
theorem B70540433 : Blo 1128631 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B2546999 : Blo 1128631 2546999 := bstep (se 1 (by rfl) ⟨1910249, by rfl⟩ : syracuseStep 2546999 = 3820499) B3820499
theorem B1695497 : Blo 1128631 1695497 := bstep (se 2 (by rfl) ⟨635811, by rfl⟩ : syracuseStep 1695497 = 1271623) B1271623
theorem B2547935 : Blo 1128631 2547935 := bstep (se 1 (by rfl) ⟨1910951, by rfl⟩ : syracuseStep 2547935 = 3821903) B3821903
theorem B1696079 : Blo 1128631 1696079 := bstep (se 1 (by rfl) ⟨1272059, by rfl⟩ : syracuseStep 1696079 = 2544119) B2544119
theorem B148989689 : Blo 1128631 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B2418815 : Blo 1128631 2418815 := bstep (se 1 (by rfl) ⟨1814111, by rfl⟩ : syracuseStep 2418815 = 3628223) B3628223
theorem B1271983 : Blo 1128631 1271983 := bstep (se 1 (by rfl) ⟨953987, by rfl⟩ : syracuseStep 1271983 = 1907975) B1907975
theorem B6121655 : Blo 1128631 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B1698587 : Blo 1128631 1698587 := bstep (se 1 (by rfl) ⟨1273940, by rfl⟩ : syracuseStep 1698587 = 2547881) B2547881
theorem B13038347 : Blo 1128631 13038347 := bstep (se 1 (by rfl) ⟨9778760, by rfl⟩ : syracuseStep 13038347 = 19557521) B19557521
theorem B6878537 : Blo 1128631 6878537 := bstep (se 2 (by rfl) ⟨2579451, by rfl⟩ : syracuseStep 6878537 = 5158903) B5158903
theorem B27883225 : Blo 1128631 27883225 := bstep (se 2 (by rfl) ⟨10456209, by rfl⟩ : syracuseStep 27883225 = 20912419) B20912419
theorem B9174431 : Blo 1128631 9174431 := bstep (se 1 (by rfl) ⟨6880823, by rfl⟩ : syracuseStep 9174431 = 13761647) B13761647
theorem B670039847 : Blo 1128631 670039847 := bstep (se 1 (by rfl) ⟨502529885, by rfl⟩ : syracuseStep 670039847 = 1005059771) B1005059771
theorem B7831511 : Blo 1128631 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B4293917 : Blo 1128631 4293917 := bstep (se 3 (by rfl) ⟨805109, by rfl⟩ : syracuseStep 4293917 = 1610219) B1610219
theorem B5802043 : Blo 1128631 5802043 := bstep (se 1 (by rfl) ⟨4351532, by rfl⟩ : syracuseStep 5802043 = 8703065) B8703065
theorem B19597409 : Blo 1128631 19597409 := bstep (se 2 (by rfl) ⟨7349028, by rfl⟩ : syracuseStep 19597409 = 14698057) B14698057
theorem B30968639 : Blo 1128631 30968639 := bstep (se 1 (by rfl) ⟨23226479, by rfl⟩ : syracuseStep 30968639 = 46452959) B46452959
theorem B29331497 : Blo 1128631 29331497 := bstep (se 2 (by rfl) ⟨10999311, by rfl⟩ : syracuseStep 29331497 = 21998623) B21998623
theorem B8589563 : Blo 1128631 8589563 := bstep (se 1 (by rfl) ⟨6442172, by rfl⟩ : syracuseStep 8589563 = 12884345) B12884345
theorem B47026955 : Blo 1128631 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B1905977 : Blo 1128631 1905977 := bstep (se 2 (by rfl) ⟨714741, by rfl⟩ : syracuseStep 1905977 = 1429483) B1429483
theorem B99326459 : Blo 1128631 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B1612543 : Blo 1128631 1612543 := bstep (se 1 (by rfl) ⟨1209407, by rfl⟩ : syracuseStep 1612543 = 2418815) B2418815
theorem B49552985 : Blo 1128631 49552985 := bstep (se 2 (by rfl) ⟨18582369, by rfl⟩ : syracuseStep 49552985 = 37164739) B37164739
theorem B4825001 : Blo 1128631 4825001 := bstep (se 2 (by rfl) ⟨1809375, by rfl⟩ : syracuseStep 4825001 = 3618751) B3618751
theorem B3219583 : Blo 1128631 3219583 := bstep (se 1 (by rfl) ⟨2414687, by rfl⟩ : syracuseStep 3219583 = 4829375) B4829375
theorem B6103183 : Blo 1128631 6103183 := bstep (se 1 (by rfl) ⟨4577387, by rfl⟩ : syracuseStep 6103183 = 9154775) B9154775
theorem B8692231 : Blo 1128631 8692231 := bstep (se 1 (by rfl) ⟨6519173, by rfl⟩ : syracuseStep 8692231 = 13038347) B13038347
theorem B5221007 : Blo 1128631 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B4074151 : Blo 1128631 4074151 := bstep (se 1 (by rfl) ⟨3055613, by rfl⟩ : syracuseStep 4074151 = 6111227) B6111227
theorem B3059183 : Blo 1128631 3059183 := bstep (se 1 (by rfl) ⟨2294387, by rfl⟩ : syracuseStep 3059183 = 4588775) B4588775
theorem B39169615 : Blo 1128631 39169615 := bstep (se 1 (by rfl) ⟨29377211, by rfl⟩ : syracuseStep 39169615 = 58754423) B58754423
theorem B6435773 : Blo 1128631 6435773 := bstep (se 3 (by rfl) ⟨1206707, by rfl⟩ : syracuseStep 6435773 = 2413415) B2413415
theorem B9647099 : Blo 1128631 9647099 := bstep (se 1 (by rfl) ⟨7235324, by rfl⟩ : syracuseStep 9647099 = 14470649) B14470649
theorem B1128775 : Blo 1128631 1128775 := bstep (se 1 (by rfl) ⟨846581, by rfl⟩ : syracuseStep 1128775 = 1693163) B1693163
theorem B1128959 : Blo 1128631 1128959 := bstep (se 1 (by rfl) ⟨846719, by rfl⟩ : syracuseStep 1128959 = 1693439) B1693439
theorem B131971979 : Blo 1128631 131971979 := bstep (se 1 (by rfl) ⟨98978984, by rfl⟩ : syracuseStep 131971979 = 197957969) B197957969
theorem B39140495 : Blo 1128631 39140495 := bstep (se 1 (by rfl) ⟨29355371, by rfl⟩ : syracuseStep 39140495 = 58710743) B58710743
theorem B1129727 : Blo 1128631 1129727 := bstep (se 1 (by rfl) ⟨847295, by rfl⟩ : syracuseStep 1129727 = 1694591) B1694591
theorem B1130331 : Blo 1128631 1130331 := bstep (se 1 (by rfl) ⟨847748, by rfl⟩ : syracuseStep 1130331 = 1695497) B1695497
theorem B1130719 : Blo 1128631 1130719 := bstep (se 1 (by rfl) ⟨848039, by rfl⟩ : syracuseStep 1130719 = 1696079) B1696079
theorem B4081103 : Blo 1128631 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B1132391 : Blo 1128631 1132391 := bstep (se 1 (by rfl) ⟨849293, by rfl⟩ : syracuseStep 1132391 = 1698587) B1698587
theorem B37177633 : Blo 1128631 37177633 := bstep (se 2 (by rfl) ⟨13941612, by rfl⟩ : syracuseStep 37177633 = 27883225) B27883225
theorem B12863933 : Blo 1128631 12863933 := bstep (se 3 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 12863933 = 4823975) B4823975
theorem B16304905 : Blo 1128631 16304905 := bstep (se 2 (by rfl) ⟨6114339, by rfl⟩ : syracuseStep 16304905 = 12228679) B12228679
theorem B2542931 : Blo 1128631 2542931 := bstep (se 1 (by rfl) ⟨1907198, by rfl⟩ : syracuseStep 2542931 = 3814397) B3814397
theorem B24465149 : Blo 1128631 24465149 := bstep (se 3 (by rfl) ⟨4587215, by rfl⟩ : syracuseStep 24465149 = 9174431) B9174431
theorem B5430971 : Blo 1128631 5430971 := bstep (se 1 (by rfl) ⟨4073228, by rfl⟩ : syracuseStep 5430971 = 8146457) B8146457
theorem B1695977 : Blo 1128631 1695977 := bstep (se 2 (by rfl) ⟨635991, by rfl⟩ : syracuseStep 1695977 = 1271983) B1271983
theorem B1697999 : Blo 1128631 1697999 := bstep (se 1 (by rfl) ⟨1273499, by rfl⟩ : syracuseStep 1697999 = 2546999) B2546999
theorem B1698623 : Blo 1128631 1698623 := bstep (se 1 (by rfl) ⟨1273967, by rfl⟩ : syracuseStep 1698623 = 2547935) B2547935
theorem B5730425 : Blo 1128631 5730425 := bstep (se 2 (by rfl) ⟨2148909, by rfl⟩ : syracuseStep 5730425 = 4297819) B4297819
theorem B8156143 : Blo 1128631 8156143 := bstep (se 1 (by rfl) ⟨6117107, by rfl⟩ : syracuseStep 8156143 = 12234215) B12234215
theorem B4585691 : Blo 1128631 4585691 := bstep (se 1 (by rfl) ⟨3439268, by rfl⟩ : syracuseStep 4585691 = 6878537) B6878537
theorem B446693231 : Blo 1128631 446693231 := bstep (se 1 (by rfl) ⟨335019923, by rfl⟩ : syracuseStep 446693231 = 670039847) B670039847
theorem B21462911 : Blo 1128631 21462911 := bstep (se 1 (by rfl) ⟨16097183, by rfl⟩ : syracuseStep 21462911 = 32194367) B32194367
theorem B21725111 : Blo 1128631 21725111 := bstep (se 1 (by rfl) ⟨16293833, by rfl⟩ : syracuseStep 21725111 = 32587667) B32587667
theorem B78217325 : Blo 1128631 78217325 := bstep (se 3 (by rfl) ⟨14665748, by rfl⟩ : syracuseStep 78217325 = 29331497) B29331497
theorem B4292777 : Blo 1128631 4292777 := bstep (se 2 (by rfl) ⟨1609791, by rfl⟩ : syracuseStep 4292777 = 3219583) B3219583
theorem B2720735 : Blo 1128631 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B20645759 : Blo 1128631 20645759 := bstep (se 1 (by rfl) ⟨15484319, by rfl⟩ : syracuseStep 20645759 = 30968639) B30968639
theorem B7736057 : Blo 1128631 7736057 := bstep (se 2 (by rfl) ⟨2901021, by rfl⟩ : syracuseStep 7736057 = 5802043) B5802043
theorem B33035323 : Blo 1128631 33035323 := bstep (se 1 (by rfl) ⟨24776492, by rfl⟩ : syracuseStep 33035323 = 49552985) B49552985
theorem B3216667 : Blo 1128631 3216667 := bstep (se 1 (by rfl) ⟨2412500, by rfl⟩ : syracuseStep 3216667 = 4825001) B4825001
theorem B12228509 : Blo 1128631 12228509 := bstep (se 3 (by rfl) ⟨2292845, by rfl⟩ : syracuseStep 12228509 = 4585691) B4585691
theorem B264870557 : Blo 1128631 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B3480671 : Blo 1128631 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B2039455 : Blo 1128631 2039455 := bstep (se 1 (by rfl) ⟨1529591, by rfl⟩ : syracuseStep 2039455 = 3059183) B3059183
theorem B6431399 : Blo 1128631 6431399 := bstep (se 1 (by rfl) ⟨4823549, by rfl⟩ : syracuseStep 6431399 = 9647099) B9647099
theorem B26093663 : Blo 1128631 26093663 := bstep (se 1 (by rfl) ⟨19570247, by rfl⟩ : syracuseStep 26093663 = 39140495) B39140495
theorem B8137577 : Blo 1128631 8137577 := bstep (se 2 (by rfl) ⟨3051591, by rfl⟩ : syracuseStep 8137577 = 6103183) B6103183
theorem B2862611 : Blo 1128631 2862611 := bstep (se 1 (by rfl) ⟨2146958, by rfl⟩ : syracuseStep 2862611 = 4293917) B4293917
theorem B21739873 : Blo 1128631 21739873 := bstep (se 2 (by rfl) ⟨8152452, by rfl⟩ : syracuseStep 21739873 = 16304905) B16304905
theorem B3620647 : Blo 1128631 3620647 := bstep (se 1 (by rfl) ⟨2715485, by rfl⟩ : syracuseStep 3620647 = 5430971) B5430971
theorem B43499429 : Blo 1128631 43499429 := bstep (se 4 (by rfl) ⟨4078071, by rfl⟩ : syracuseStep 43499429 = 8156143) B8156143
theorem B1130651 : Blo 1128631 1130651 := bstep (se 1 (by rfl) ⟨847988, by rfl⟩ : syracuseStep 1130651 = 1695977) B1695977
theorem B1131999 : Blo 1128631 1131999 := bstep (se 1 (by rfl) ⟨848999, by rfl⟩ : syracuseStep 1131999 = 1697999) B1697999
theorem B1132415 : Blo 1128631 1132415 := bstep (se 1 (by rfl) ⟨849311, by rfl⟩ : syracuseStep 1132415 = 1698623) B1698623
theorem B3820283 : Blo 1128631 3820283 := bstep (se 1 (by rfl) ⟨2865212, by rfl⟩ : syracuseStep 3820283 = 5730425) B5730425
theorem B2150057 : Blo 1128631 2150057 := bstep (se 2 (by rfl) ⟨806271, by rfl⟩ : syracuseStep 2150057 = 1612543) B1612543
theorem B14308607 : Blo 1128631 14308607 := bstep (se 1 (by rfl) ⟨10731455, by rfl⟩ : syracuseStep 14308607 = 21462911) B21462911
theorem B11589641 : Blo 1128631 11589641 := bstep (se 2 (by rfl) ⟨4346115, by rfl⟩ : syracuseStep 11589641 = 8692231) B8692231
theorem B13064939 : Blo 1128631 13064939 := bstep (se 1 (by rfl) ⟨9798704, by rfl⟩ : syracuseStep 13064939 = 19597409) B19597409
theorem B8575955 : Blo 1128631 8575955 := bstep (se 1 (by rfl) ⟨6431966, by rfl⟩ : syracuseStep 8575955 = 12863933) B12863933
theorem B1695287 : Blo 1128631 1695287 := bstep (se 1 (by rfl) ⟨1271465, by rfl⟩ : syracuseStep 1695287 = 2542931) B2542931
theorem B16310099 : Blo 1128631 16310099 := bstep (se 1 (by rfl) ⟨12232574, by rfl⟩ : syracuseStep 16310099 = 24465149) B24465149
theorem B5726375 : Blo 1128631 5726375 := bstep (se 1 (by rfl) ⟨4294781, by rfl⟩ : syracuseStep 5726375 = 8589563) B8589563
theorem B49570177 : Blo 1128631 49570177 := bstep (se 2 (by rfl) ⟨18588816, by rfl⟩ : syracuseStep 49570177 = 37177633) B37177633
theorem B31351303 : Blo 1128631 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B1270651 : Blo 1128631 1270651 := bstep (se 1 (by rfl) ⟨952988, by rfl⟩ : syracuseStep 1270651 = 1905977) B1905977
theorem B5432201 : Blo 1128631 5432201 := bstep (se 2 (by rfl) ⟨2037075, by rfl⟩ : syracuseStep 5432201 = 4074151) B4074151
theorem B52226153 : Blo 1128631 52226153 := bstep (se 2 (by rfl) ⟨19584807, by rfl⟩ : syracuseStep 52226153 = 39169615) B39169615
theorem B4290515 : Blo 1128631 4290515 := bstep (se 1 (by rfl) ⟨3217886, by rfl⟩ : syracuseStep 4290515 = 6435773) B6435773
theorem B87981319 : Blo 1128631 87981319 := bstep (se 1 (by rfl) ⟨65985989, by rfl⟩ : syracuseStep 87981319 = 131971979) B131971979
theorem B297795487 : Blo 1128631 297795487 := bstep (se 1 (by rfl) ⟨223346615, by rfl⟩ : syracuseStep 297795487 = 446693231) B446693231
theorem B14483407 : Blo 1128631 14483407 := bstep (se 1 (by rfl) ⟨10862555, by rfl⟩ : syracuseStep 14483407 = 21725111) B21725111
theorem B66093569 : Blo 1128631 66093569 := bstep (se 2 (by rfl) ⟨24785088, by rfl⟩ : syracuseStep 66093569 = 49570177) B49570177
theorem B13763839 : Blo 1128631 13763839 := bstep (se 1 (by rfl) ⟨10322879, by rfl⟩ : syracuseStep 13763839 = 20645759) B20645759
theorem B44047097 : Blo 1128631 44047097 := bstep (se 2 (by rfl) ⟨16517661, by rfl⟩ : syracuseStep 44047097 = 33035323) B33035323
theorem B1908407 : Blo 1128631 1908407 := bstep (se 1 (by rfl) ⟨1431305, by rfl⟩ : syracuseStep 1908407 = 2862611) B2862611
theorem B9281789 : Blo 1128631 9281789 := bstep (se 3 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 9281789 = 3480671) B3480671
theorem B2860343 : Blo 1128631 2860343 := bstep (se 1 (by rfl) ⟨2145257, by rfl⟩ : syracuseStep 2860343 = 4290515) B4290515
theorem B4827529 : Blo 1128631 4827529 := bstep (se 2 (by rfl) ⟨1810323, by rfl⟩ : syracuseStep 4827529 = 3620647) B3620647
theorem B397060649 : Blo 1128631 397060649 := bstep (se 2 (by rfl) ⟨148897743, by rfl⟩ : syracuseStep 397060649 = 297795487) B297795487
theorem B19311209 : Blo 1128631 19311209 := bstep (se 2 (by rfl) ⟨7241703, by rfl⟩ : syracuseStep 19311209 = 14483407) B14483407
theorem B52144883 : Blo 1128631 52144883 := bstep (se 1 (by rfl) ⟨39108662, by rfl⟩ : syracuseStep 52144883 = 78217325) B78217325
theorem B2861851 : Blo 1128631 2861851 := bstep (se 1 (by rfl) ⟨2146388, by rfl⟩ : syracuseStep 2861851 = 4292777) B4292777
theorem B1813823 : Blo 1128631 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B5157371 : Blo 1128631 5157371 := bstep (se 1 (by rfl) ⟨3868028, by rfl⟩ : syracuseStep 5157371 = 7736057) B7736057
theorem B38156285 : Blo 1128631 38156285 := bstep (se 3 (by rfl) ⟨7154303, by rfl⟩ : syracuseStep 38156285 = 14308607) B14308607
theorem B5717303 : Blo 1128631 5717303 := bstep (se 1 (by rfl) ⟨4287977, by rfl⟩ : syracuseStep 5717303 = 8575955) B8575955
theorem B1130191 : Blo 1128631 1130191 := bstep (se 1 (by rfl) ⟨847643, by rfl⟩ : syracuseStep 1130191 = 1695287) B1695287
theorem B3817583 : Blo 1128631 3817583 := bstep (se 1 (by rfl) ⟨2863187, by rfl⟩ : syracuseStep 3817583 = 5726375) B5726375
theorem B3621467 : Blo 1128631 3621467 := bstep (se 1 (by rfl) ⟨2716100, by rfl⟩ : syracuseStep 3621467 = 5432201) B5432201
theorem B34817435 : Blo 1128631 34817435 := bstep (se 1 (by rfl) ⟨26113076, by rfl⟩ : syracuseStep 34817435 = 52226153) B52226153
theorem B5425051 : Blo 1128631 5425051 := bstep (se 1 (by rfl) ⟨4068788, by rfl⟩ : syracuseStep 5425051 = 8137577) B8137577
theorem B28986497 : Blo 1128631 28986497 := bstep (se 2 (by rfl) ⟨10869936, by rfl⟩ : syracuseStep 28986497 = 21739873) B21739873
theorem B1694201 : Blo 1128631 1694201 := bstep (se 2 (by rfl) ⟨635325, by rfl⟩ : syracuseStep 1694201 = 1270651) B1270651
theorem B2546855 : Blo 1128631 2546855 := bstep (se 1 (by rfl) ⟨1910141, by rfl⟩ : syracuseStep 2546855 = 3820283) B3820283
theorem B1433371 : Blo 1128631 1433371 := bstep (se 1 (by rfl) ⟨1075028, by rfl⟩ : syracuseStep 1433371 = 2150057) B2150057
theorem B167206949 : Blo 1128631 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B8152339 : Blo 1128631 8152339 := bstep (se 1 (by rfl) ⟨6114254, by rfl⟩ : syracuseStep 8152339 = 12228509) B12228509
theorem B7726427 : Blo 1128631 7726427 := bstep (se 1 (by rfl) ⟨5794820, by rfl⟩ : syracuseStep 7726427 = 11589641) B11589641
theorem B176580371 : Blo 1128631 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B8709959 : Blo 1128631 8709959 := bstep (se 1 (by rfl) ⟨6532469, by rfl⟩ : syracuseStep 8709959 = 13064939) B13064939
theorem B10873399 : Blo 1128631 10873399 := bstep (se 1 (by rfl) ⟨8155049, by rfl⟩ : syracuseStep 10873399 = 16310099) B16310099
theorem B4287599 : Blo 1128631 4287599 := bstep (se 1 (by rfl) ⟨3215699, by rfl⟩ : syracuseStep 4287599 = 6431399) B6431399
theorem B17395775 : Blo 1128631 17395775 := bstep (se 1 (by rfl) ⟨13046831, by rfl⟩ : syracuseStep 17395775 = 26093663) B26093663
theorem B4288889 : Blo 1128631 4288889 := bstep (se 2 (by rfl) ⟨1608333, by rfl⟩ : syracuseStep 4288889 = 3216667) B3216667
theorem B117308425 : Blo 1128631 117308425 := bstep (se 2 (by rfl) ⟨43990659, by rfl⟩ : syracuseStep 117308425 = 87981319) B87981319
theorem B2719273 : Blo 1128631 2719273 := bstep (se 2 (by rfl) ⟨1019727, by rfl⟩ : syracuseStep 2719273 = 2039455) B2039455
theorem B28999619 : Blo 1128631 28999619 := bstep (se 1 (by rfl) ⟨21749714, by rfl⟩ : syracuseStep 28999619 = 43499429) B43499429
theorem B18351785 : Blo 1128631 18351785 := bstep (se 2 (by rfl) ⟨6881919, by rfl⟩ : syracuseStep 18351785 = 13763839) B13763839
theorem B29364731 : Blo 1128631 29364731 := bstep (se 1 (by rfl) ⟨22023548, by rfl⟩ : syracuseStep 29364731 = 44047097) B44047097
theorem B470880989 : Blo 1128631 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B1906895 : Blo 1128631 1906895 := bstep (se 1 (by rfl) ⟨1430171, by rfl⟩ : syracuseStep 1906895 = 2860343) B2860343
theorem B5150951 : Blo 1128631 5150951 := bstep (se 1 (by rfl) ⟨3863213, by rfl⟩ : syracuseStep 5150951 = 7726427) B7726427
theorem B5806639 : Blo 1128631 5806639 := bstep (se 1 (by rfl) ⟨4354979, by rfl⟩ : syracuseStep 5806639 = 8709959) B8709959
theorem B264707099 : Blo 1128631 264707099 := bstep (se 1 (by rfl) ⟨198530324, by rfl⟩ : syracuseStep 264707099 = 397060649) B397060649
theorem B2858399 : Blo 1128631 2858399 := bstep (se 1 (by rfl) ⟨2143799, by rfl⟩ : syracuseStep 2858399 = 4287599) B4287599
theorem B2859259 : Blo 1128631 2859259 := bstep (se 1 (by rfl) ⟨2144444, by rfl⟩ : syracuseStep 2859259 = 4288889) B4288889
theorem B25437523 : Blo 1128631 25437523 := bstep (se 1 (by rfl) ⟨19078142, by rfl⟩ : syracuseStep 25437523 = 38156285) B38156285
theorem B156411233 : Blo 1128631 156411233 := bstep (se 2 (by rfl) ⟨58654212, by rfl⟩ : syracuseStep 156411233 = 117308425) B117308425
theorem B3811535 : Blo 1128631 3811535 := bstep (se 1 (by rfl) ⟨2858651, by rfl⟩ : syracuseStep 3811535 = 5717303) B5717303
theorem B1911161 : Blo 1128631 1911161 := bstep (se 2 (by rfl) ⟨716685, by rfl⟩ : syracuseStep 1911161 = 1433371) B1433371
theorem B23211623 : Blo 1128631 23211623 := bstep (se 1 (by rfl) ⟨17408717, by rfl⟩ : syracuseStep 23211623 = 34817435) B34817435
theorem B6436705 : Blo 1128631 6436705 := bstep (se 2 (by rfl) ⟨2413764, by rfl⟩ : syracuseStep 6436705 = 4827529) B4827529
theorem B14497865 : Blo 1128631 14497865 := bstep (se 2 (by rfl) ⟨5436699, by rfl⟩ : syracuseStep 14497865 = 10873399) B10873399
theorem B3815801 : Blo 1128631 3815801 := bstep (se 2 (by rfl) ⟨1430925, by rfl⟩ : syracuseStep 3815801 = 2861851) B2861851
theorem B1129467 : Blo 1128631 1129467 := bstep (se 1 (by rfl) ⟨847100, by rfl⟩ : syracuseStep 1129467 = 1694201) B1694201
theorem B3625697 : Blo 1128631 3625697 := bstep (se 2 (by rfl) ⟨1359636, by rfl⟩ : syracuseStep 3625697 = 2719273) B2719273
theorem B2545055 : Blo 1128631 2545055 := bstep (se 1 (by rfl) ⟨1908791, by rfl⟩ : syracuseStep 2545055 = 3817583) B3817583
theorem B44062379 : Blo 1128631 44062379 := bstep (se 1 (by rfl) ⟨33046784, by rfl⟩ : syracuseStep 44062379 = 66093569) B66093569
theorem B9657245 : Blo 1128631 9657245 := bstep (se 3 (by rfl) ⟨1810733, by rfl⟩ : syracuseStep 9657245 = 3621467) B3621467
theorem B10869785 : Blo 1128631 10869785 := bstep (se 2 (by rfl) ⟨4076169, by rfl⟩ : syracuseStep 10869785 = 8152339) B8152339
theorem B19324331 : Blo 1128631 19324331 := bstep (se 1 (by rfl) ⟨14493248, by rfl⟩ : syracuseStep 19324331 = 28986497) B28986497
theorem B7233401 : Blo 1128631 7233401 := bstep (se 2 (by rfl) ⟨2712525, by rfl⟩ : syracuseStep 7233401 = 5425051) B5425051
theorem B1697903 : Blo 1128631 1697903 := bstep (se 1 (by rfl) ⟨1273427, by rfl⟩ : syracuseStep 1697903 = 2546855) B2546855
theorem B1272271 : Blo 1128631 1272271 := bstep (se 1 (by rfl) ⟨954203, by rfl⟩ : syracuseStep 1272271 = 1908407) B1908407
theorem B111471299 : Blo 1128631 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B6187859 : Blo 1128631 6187859 := bstep (se 1 (by rfl) ⟨4640894, by rfl⟩ : syracuseStep 6187859 = 9281789) B9281789
theorem B12874139 : Blo 1128631 12874139 := bstep (se 1 (by rfl) ⟨9655604, by rfl⟩ : syracuseStep 12874139 = 19311209) B19311209
theorem B34763255 : Blo 1128631 34763255 := bstep (se 1 (by rfl) ⟨26072441, by rfl⟩ : syracuseStep 34763255 = 52144883) B52144883
theorem B1209215 : Blo 1128631 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B11597183 : Blo 1128631 11597183 := bstep (se 1 (by rfl) ⟨8697887, by rfl⟩ : syracuseStep 11597183 = 17395775) B17395775
theorem B3438247 : Blo 1128631 3438247 := bstep (se 1 (by rfl) ⟨2578685, by rfl⟩ : syracuseStep 3438247 = 5157371) B5157371
theorem B19333079 : Blo 1128631 19333079 := bstep (se 1 (by rfl) ⟨14499809, by rfl⟩ : syracuseStep 19333079 = 28999619) B28999619
theorem B33916697 : Blo 1128631 33916697 := bstep (se 2 (by rfl) ⟨12718761, by rfl⟩ : syracuseStep 33916697 = 25437523) B25437523
theorem B313920659 : Blo 1128631 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B7246523 : Blo 1128631 7246523 := bstep (se 1 (by rfl) ⟨5434892, by rfl⟩ : syracuseStep 7246523 = 10869785) B10869785
theorem B1905599 : Blo 1128631 1905599 := bstep (se 1 (by rfl) ⟨1429199, by rfl⟩ : syracuseStep 1905599 = 2858399) B2858399
theorem B12882887 : Blo 1128631 12882887 := bstep (se 1 (by rfl) ⟨9662165, by rfl⟩ : syracuseStep 12882887 = 19324331) B19324331
theorem B4822267 : Blo 1128631 4822267 := bstep (se 1 (by rfl) ⟨3616700, by rfl⟩ : syracuseStep 4822267 = 7233401) B7233401
theorem B104274155 : Blo 1128631 104274155 := bstep (se 1 (by rfl) ⟨78205616, by rfl⟩ : syracuseStep 104274155 = 156411233) B156411233
theorem B15474415 : Blo 1128631 15474415 := bstep (se 1 (by rfl) ⟨11605811, by rfl⟩ : syracuseStep 15474415 = 23211623) B23211623
theorem B23175503 : Blo 1128631 23175503 := bstep (se 1 (by rfl) ⟨17381627, by rfl⟩ : syracuseStep 23175503 = 34763255) B34763255
theorem B7742185 : Blo 1128631 7742185 := bstep (se 2 (by rfl) ⟨2903319, by rfl⟩ : syracuseStep 7742185 = 5806639) B5806639
theorem B12888719 : Blo 1128631 12888719 := bstep (se 1 (by rfl) ⟨9666539, by rfl⟩ : syracuseStep 12888719 = 19333079) B19333079
theorem B3812345 : Blo 1128631 3812345 := bstep (se 2 (by rfl) ⟨1429629, by rfl⟩ : syracuseStep 3812345 = 2859259) B2859259
theorem B12234523 : Blo 1128631 12234523 := bstep (se 1 (by rfl) ⟨9175892, by rfl⟩ : syracuseStep 12234523 = 18351785) B18351785
theorem B3224573 : Blo 1128631 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B19576487 : Blo 1128631 19576487 := bstep (se 1 (by rfl) ⟨14682365, by rfl⟩ : syracuseStep 19576487 = 29364731) B29364731
theorem B29374919 : Blo 1128631 29374919 := bstep (se 1 (by rfl) ⟨22031189, by rfl⟩ : syracuseStep 29374919 = 44062379) B44062379
theorem B6438163 : Blo 1128631 6438163 := bstep (se 1 (by rfl) ⟨4828622, by rfl⟩ : syracuseStep 6438163 = 9657245) B9657245
theorem B176471399 : Blo 1128631 176471399 := bstep (se 1 (by rfl) ⟨132353549, by rfl⟩ : syracuseStep 176471399 = 264707099) B264707099
theorem B1131935 : Blo 1128631 1131935 := bstep (se 1 (by rfl) ⟨848951, by rfl⟩ : syracuseStep 1131935 = 1697903) B1697903
theorem B2541023 : Blo 1128631 2541023 := bstep (se 1 (by rfl) ⟨1905767, by rfl⟩ : syracuseStep 2541023 = 3811535) B3811535
theorem B2543867 : Blo 1128631 2543867 := bstep (se 1 (by rfl) ⟨1907900, by rfl⟩ : syracuseStep 2543867 = 3815801) B3815801
theorem B2417131 : Blo 1128631 2417131 := bstep (se 1 (by rfl) ⟨1812848, by rfl⟩ : syracuseStep 2417131 = 3625697) B3625697
theorem B1696361 : Blo 1128631 1696361 := bstep (se 2 (by rfl) ⟨636135, by rfl⟩ : syracuseStep 1696361 = 1272271) B1272271
theorem B1696703 : Blo 1128631 1696703 := bstep (se 1 (by rfl) ⟨1272527, by rfl⟩ : syracuseStep 1696703 = 2545055) B2545055
theorem B1271263 : Blo 1128631 1271263 := bstep (se 1 (by rfl) ⟨953447, by rfl⟩ : syracuseStep 1271263 = 1906895) B1906895
theorem B3433967 : Blo 1128631 3433967 := bstep (se 1 (by rfl) ⟨2575475, by rfl⟩ : syracuseStep 3433967 = 5150951) B5150951
theorem B1274107 : Blo 1128631 1274107 := bstep (se 1 (by rfl) ⟨955580, by rfl⟩ : syracuseStep 1274107 = 1911161) B1911161
theorem B74314199 : Blo 1128631 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B4125239 : Blo 1128631 4125239 := bstep (se 1 (by rfl) ⟨3093929, by rfl⟩ : syracuseStep 4125239 = 6187859) B6187859
theorem B4584329 : Blo 1128631 4584329 := bstep (se 2 (by rfl) ⟨1719123, by rfl⟩ : syracuseStep 4584329 = 3438247) B3438247
theorem B8582273 : Blo 1128631 8582273 := bstep (se 2 (by rfl) ⟨3218352, by rfl⟩ : syracuseStep 8582273 = 6436705) B6436705
theorem B8582759 : Blo 1128631 8582759 := bstep (se 1 (by rfl) ⟨6437069, by rfl⟩ : syracuseStep 8582759 = 12874139) B12874139
theorem B7731455 : Blo 1128631 7731455 := bstep (se 1 (by rfl) ⟨5798591, by rfl⟩ : syracuseStep 7731455 = 11597183) B11597183
theorem B9665243 : Blo 1128631 9665243 := bstep (se 1 (by rfl) ⟨7248932, by rfl⟩ : syracuseStep 9665243 = 14497865) B14497865
theorem B22611131 : Blo 1128631 22611131 := bstep (se 1 (by rfl) ⟨16958348, by rfl⟩ : syracuseStep 22611131 = 33916697) B33916697
theorem B8588591 : Blo 1128631 8588591 := bstep (se 1 (by rfl) ⟨6441443, by rfl⟩ : syracuseStep 8588591 = 12882887) B12882887
theorem B41291653 : Blo 1128631 41291653 := bstep (se 4 (by rfl) ⟨3871092, by rfl⟩ : syracuseStep 41291653 = 7742185) B7742185
theorem B6429689 : Blo 1128631 6429689 := bstep (se 2 (by rfl) ⟨2411133, by rfl⟩ : syracuseStep 6429689 = 4822267) B4822267
theorem B8592479 : Blo 1128631 8592479 := bstep (se 1 (by rfl) ⟨6444359, by rfl⟩ : syracuseStep 8592479 = 12888719) B12888719
theorem B3056219 : Blo 1128631 3056219 := bstep (se 1 (by rfl) ⟨2292164, by rfl⟩ : syracuseStep 3056219 = 4584329) B4584329
theorem B13050991 : Blo 1128631 13050991 := bstep (se 1 (by rfl) ⟨9788243, by rfl⟩ : syracuseStep 13050991 = 19576487) B19576487
theorem B117647599 : Blo 1128631 117647599 := bstep (se 1 (by rfl) ⟨88235699, by rfl⟩ : syracuseStep 117647599 = 176471399) B176471399
theorem B3222841 : Blo 1128631 3222841 := bstep (se 2 (by rfl) ⟨1208565, by rfl⟩ : syracuseStep 3222841 = 2417131) B2417131
theorem B4831015 : Blo 1128631 4831015 := bstep (se 1 (by rfl) ⟨3623261, by rfl⟩ : syracuseStep 4831015 = 7246523) B7246523
theorem B69516103 : Blo 1128631 69516103 := bstep (se 1 (by rfl) ⟨52137077, by rfl⟩ : syracuseStep 69516103 = 104274155) B104274155
theorem B15450335 : Blo 1128631 15450335 := bstep (se 1 (by rfl) ⟨11587751, by rfl⟩ : syracuseStep 15450335 = 23175503) B23175503
theorem B1130907 : Blo 1128631 1130907 := bstep (se 1 (by rfl) ⟨848180, by rfl⟩ : syracuseStep 1130907 = 1696361) B1696361
theorem B1131135 : Blo 1128631 1131135 := bstep (se 1 (by rfl) ⟨848351, by rfl⟩ : syracuseStep 1131135 = 1696703) B1696703
theorem B2541563 : Blo 1128631 2541563 := bstep (se 1 (by rfl) ⟨1906172, by rfl⟩ : syracuseStep 2541563 = 3812345) B3812345
theorem B2149715 : Blo 1128631 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B5721515 : Blo 1128631 5721515 := bstep (se 1 (by rfl) ⟨4291136, by rfl⟩ : syracuseStep 5721515 = 8582273) B8582273
theorem B5721839 : Blo 1128631 5721839 := bstep (se 1 (by rfl) ⟨4291379, by rfl⟩ : syracuseStep 5721839 = 8582759) B8582759
theorem B19583279 : Blo 1128631 19583279 := bstep (se 1 (by rfl) ⟨14687459, by rfl⟩ : syracuseStep 19583279 = 29374919) B29374919
theorem B6443495 : Blo 1128631 6443495 := bstep (se 1 (by rfl) ⟨4832621, by rfl⟩ : syracuseStep 6443495 = 9665243) B9665243
theorem B20632553 : Blo 1128631 20632553 := bstep (se 2 (by rfl) ⟨7737207, by rfl⟩ : syracuseStep 20632553 = 15474415) B15474415
theorem B1694015 : Blo 1128631 1694015 := bstep (se 1 (by rfl) ⟨1270511, by rfl⟩ : syracuseStep 1694015 = 2541023) B2541023
theorem B1695017 : Blo 1128631 1695017 := bstep (se 2 (by rfl) ⟨635631, by rfl⟩ : syracuseStep 1695017 = 1271263) B1271263
theorem B209280439 : Blo 1128631 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B82468853 : Blo 1128631 82468853 := bstep (se 5 (by rfl) ⟨3865727, by rfl⟩ : syracuseStep 82468853 = 7731455) B7731455
theorem B1695911 : Blo 1128631 1695911 := bstep (se 1 (by rfl) ⟨1271933, by rfl⟩ : syracuseStep 1695911 = 2543867) B2543867
theorem B1270399 : Blo 1128631 1270399 := bstep (se 1 (by rfl) ⟨952799, by rfl⟩ : syracuseStep 1270399 = 1905599) B1905599
theorem B16312697 : Blo 1128631 16312697 := bstep (se 2 (by rfl) ⟨6117261, by rfl⟩ : syracuseStep 16312697 = 12234523) B12234523
theorem B1698809 : Blo 1128631 1698809 := bstep (se 2 (by rfl) ⟨637053, by rfl⟩ : syracuseStep 1698809 = 1274107) B1274107
theorem B2289311 : Blo 1128631 2289311 := bstep (se 1 (by rfl) ⟨1716983, by rfl⟩ : syracuseStep 2289311 = 3433967) B3433967
theorem B49542799 : Blo 1128631 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B2750159 : Blo 1128631 2750159 := bstep (se 1 (by rfl) ⟨2062619, by rfl⟩ : syracuseStep 2750159 = 4125239) B4125239
theorem B8584217 : Blo 1128631 8584217 := bstep (se 2 (by rfl) ⟨3219081, by rfl⟩ : syracuseStep 8584217 = 6438163) B6438163
theorem B15074087 : Blo 1128631 15074087 := bstep (se 1 (by rfl) ⟨11305565, by rfl⟩ : syracuseStep 15074087 = 22611131) B22611131
theorem B17401321 : Blo 1128631 17401321 := bstep (se 2 (by rfl) ⟨6525495, by rfl⟩ : syracuseStep 17401321 = 13050991) B13050991
theorem B156863465 : Blo 1128631 156863465 := bstep (se 2 (by rfl) ⟨58823799, by rfl⟩ : syracuseStep 156863465 = 117647599) B117647599
theorem B4295663 : Blo 1128631 4295663 := bstep (se 1 (by rfl) ⟨3221747, by rfl⟩ : syracuseStep 4295663 = 6443495) B6443495
theorem B4297121 : Blo 1128631 4297121 := bstep (se 2 (by rfl) ⟨1611420, by rfl⟩ : syracuseStep 4297121 = 3222841) B3222841
theorem B55055537 : Blo 1128631 55055537 := bstep (se 2 (by rfl) ⟨20645826, by rfl⟩ : syracuseStep 55055537 = 41291653) B41291653
theorem B2037479 : Blo 1128631 2037479 := bstep (se 1 (by rfl) ⟨1528109, by rfl⟩ : syracuseStep 2037479 = 3056219) B3056219
theorem B10300223 : Blo 1128631 10300223 := bstep (se 1 (by rfl) ⟨7725167, by rfl⟩ : syracuseStep 10300223 = 15450335) B15450335
theorem B3814343 : Blo 1128631 3814343 := bstep (se 1 (by rfl) ⟨2860757, by rfl⟩ : syracuseStep 3814343 = 5721515) B5721515
theorem B3814559 : Blo 1128631 3814559 := bstep (se 1 (by rfl) ⟨2860919, by rfl⟩ : syracuseStep 3814559 = 5721839) B5721839
theorem B13055519 : Blo 1128631 13055519 := bstep (se 1 (by rfl) ⟨9791639, by rfl⟩ : syracuseStep 13055519 = 19583279) B19583279
theorem B1129343 : Blo 1128631 1129343 := bstep (se 1 (by rfl) ⟨847007, by rfl⟩ : syracuseStep 1129343 = 1694015) B1694015
theorem B1130011 : Blo 1128631 1130011 := bstep (se 1 (by rfl) ⟨847508, by rfl⟩ : syracuseStep 1130011 = 1695017) B1695017
theorem B1130607 : Blo 1128631 1130607 := bstep (se 1 (by rfl) ⟨847955, by rfl⟩ : syracuseStep 1130607 = 1695911) B1695911
theorem B1132539 : Blo 1128631 1132539 := bstep (se 1 (by rfl) ⟨849404, by rfl⟩ : syracuseStep 1132539 = 1698809) B1698809
theorem B6441353 : Blo 1128631 6441353 := bstep (se 2 (by rfl) ⟨2415507, by rfl⟩ : syracuseStep 6441353 = 4831015) B4831015
theorem B1526207 : Blo 1128631 1526207 := bstep (se 1 (by rfl) ⟨1144655, by rfl⟩ : syracuseStep 1526207 = 2289311) B2289311
theorem B92688137 : Blo 1128631 92688137 := bstep (se 2 (by rfl) ⟨34758051, by rfl⟩ : syracuseStep 92688137 = 69516103) B69516103
theorem B279040585 : Blo 1128631 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B5722811 : Blo 1128631 5722811 := bstep (se 1 (by rfl) ⟨4292108, by rfl⟩ : syracuseStep 5722811 = 8584217) B8584217
theorem B1693865 : Blo 1128631 1693865 := bstep (se 2 (by rfl) ⟨635199, by rfl⟩ : syracuseStep 1693865 = 1270399) B1270399
theorem B1694375 : Blo 1128631 1694375 := bstep (se 1 (by rfl) ⟨1270781, by rfl⟩ : syracuseStep 1694375 = 2541563) B2541563
theorem B5725727 : Blo 1128631 5725727 := bstep (se 1 (by rfl) ⟨4294295, by rfl⟩ : syracuseStep 5725727 = 8588591) B8588591
theorem B1433143 : Blo 1128631 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B13755035 : Blo 1128631 13755035 := bstep (se 1 (by rfl) ⟨10316276, by rfl⟩ : syracuseStep 13755035 = 20632553) B20632553
theorem B4286459 : Blo 1128631 4286459 := bstep (se 1 (by rfl) ⟨3214844, by rfl⟩ : syracuseStep 4286459 = 6429689) B6429689
theorem B5728319 : Blo 1128631 5728319 := bstep (se 1 (by rfl) ⟨4296239, by rfl⟩ : syracuseStep 5728319 = 8592479) B8592479
theorem B54979235 : Blo 1128631 54979235 := bstep (se 1 (by rfl) ⟨41234426, by rfl⟩ : syracuseStep 54979235 = 82468853) B82468853
theorem B10875131 : Blo 1128631 10875131 := bstep (se 1 (by rfl) ⟨8156348, by rfl⟩ : syracuseStep 10875131 = 16312697) B16312697
theorem B66057065 : Blo 1128631 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B1833439 : Blo 1128631 1833439 := bstep (se 1 (by rfl) ⟨1375079, by rfl⟩ : syracuseStep 1833439 = 2750159) B2750159
theorem B4294235 : Blo 1128631 4294235 := bstep (se 1 (by rfl) ⟨3220676, by rfl⟩ : syracuseStep 4294235 = 6441353) B6441353
theorem B23201761 : Blo 1128631 23201761 := bstep (se 2 (by rfl) ⟨8700660, by rfl⟩ : syracuseStep 23201761 = 17401321) B17401321
theorem B36703691 : Blo 1128631 36703691 := bstep (se 1 (by rfl) ⟨27527768, by rfl⟩ : syracuseStep 36703691 = 55055537) B55055537
theorem B372054113 : Blo 1128631 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B4069885 : Blo 1128631 4069885 := bstep (se 3 (by rfl) ⟨763103, by rfl⟩ : syracuseStep 4069885 = 1526207) B1526207
theorem B2857639 : Blo 1128631 2857639 := bstep (se 1 (by rfl) ⟨2143229, by rfl⟩ : syracuseStep 2857639 = 4286459) B4286459
theorem B21733109 : Blo 1128631 21733109 := bstep (se 5 (by rfl) ⟨1018739, by rfl⟩ : syracuseStep 21733109 = 2037479) B2037479
theorem B7250087 : Blo 1128631 7250087 := bstep (se 1 (by rfl) ⟨5437565, by rfl⟩ : syracuseStep 7250087 = 10875131) B10875131
theorem B1910857 : Blo 1128631 1910857 := bstep (se 2 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 1910857 = 1433143) B1433143
theorem B104575643 : Blo 1128631 104575643 := bstep (se 1 (by rfl) ⟨78431732, by rfl⟩ : syracuseStep 104575643 = 156863465) B156863465
theorem B2863775 : Blo 1128631 2863775 := bstep (se 1 (by rfl) ⟨2147831, by rfl⟩ : syracuseStep 2863775 = 4295663) B4295663
theorem B2864747 : Blo 1128631 2864747 := bstep (se 1 (by rfl) ⟨2148560, by rfl⟩ : syracuseStep 2864747 = 4297121) B4297121
theorem B3815207 : Blo 1128631 3815207 := bstep (se 1 (by rfl) ⟨2861405, by rfl⟩ : syracuseStep 3815207 = 5722811) B5722811
theorem B34814717 : Blo 1128631 34814717 := bstep (se 3 (by rfl) ⟨6527759, by rfl⟩ : syracuseStep 34814717 = 13055519) B13055519
theorem B1129243 : Blo 1128631 1129243 := bstep (se 1 (by rfl) ⟨846932, by rfl⟩ : syracuseStep 1129243 = 1693865) B1693865
theorem B1129583 : Blo 1128631 1129583 := bstep (se 1 (by rfl) ⟨847187, by rfl⟩ : syracuseStep 1129583 = 1694375) B1694375
theorem B3817151 : Blo 1128631 3817151 := bstep (se 1 (by rfl) ⟨2862863, by rfl⟩ : syracuseStep 3817151 = 5725727) B5725727
theorem B3818879 : Blo 1128631 3818879 := bstep (se 1 (by rfl) ⟨2864159, by rfl⟩ : syracuseStep 3818879 = 5728319) B5728319
theorem B36652823 : Blo 1128631 36652823 := bstep (se 1 (by rfl) ⟨27489617, by rfl⟩ : syracuseStep 36652823 = 54979235) B54979235
theorem B6866815 : Blo 1128631 6866815 := bstep (se 1 (by rfl) ⟨5150111, by rfl⟩ : syracuseStep 6866815 = 10300223) B10300223
theorem B2444585 : Blo 1128631 2444585 := bstep (se 2 (by rfl) ⟨916719, by rfl⟩ : syracuseStep 2444585 = 1833439) B1833439
theorem B2542895 : Blo 1128631 2542895 := bstep (se 1 (by rfl) ⟨1907171, by rfl⟩ : syracuseStep 2542895 = 3814343) B3814343
theorem B2543039 : Blo 1128631 2543039 := bstep (se 1 (by rfl) ⟨1907279, by rfl⟩ : syracuseStep 2543039 = 3814559) B3814559
theorem B40197565 : Blo 1128631 40197565 := bstep (se 3 (by rfl) ⟨7537043, by rfl⟩ : syracuseStep 40197565 = 15074087) B15074087
theorem B61792091 : Blo 1128631 61792091 := bstep (se 1 (by rfl) ⟨46344068, by rfl⟩ : syracuseStep 61792091 = 92688137) B92688137
theorem B9170023 : Blo 1128631 9170023 := bstep (se 1 (by rfl) ⟨6877517, by rfl⟩ : syracuseStep 9170023 = 13755035) B13755035
theorem B44038043 : Blo 1128631 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B30935681 : Blo 1128631 30935681 := bstep (se 2 (by rfl) ⟨11600880, by rfl⟩ : syracuseStep 30935681 = 23201761) B23201761
theorem B12226697 : Blo 1128631 12226697 := bstep (se 2 (by rfl) ⟨4585011, by rfl⟩ : syracuseStep 12226697 = 9170023) B9170023
theorem B14488739 : Blo 1128631 14488739 := bstep (se 1 (by rfl) ⟨10866554, by rfl⟩ : syracuseStep 14488739 = 21733109) B21733109
theorem B41194727 : Blo 1128631 41194727 := bstep (se 1 (by rfl) ⟨30896045, by rfl⟩ : syracuseStep 41194727 = 61792091) B61792091
theorem B1909183 : Blo 1128631 1909183 := bstep (se 1 (by rfl) ⟨1431887, by rfl⟩ : syracuseStep 1909183 = 2863775) B2863775
theorem B3810185 : Blo 1128631 3810185 := bstep (se 2 (by rfl) ⟨1428819, by rfl⟩ : syracuseStep 3810185 = 2857639) B2857639
theorem B1909831 : Blo 1128631 1909831 := bstep (se 1 (by rfl) ⟨1432373, by rfl⟩ : syracuseStep 1909831 = 2864747) B2864747
theorem B23209811 : Blo 1128631 23209811 := bstep (se 1 (by rfl) ⟨17407358, by rfl⟩ : syracuseStep 23209811 = 34814717) B34814717
theorem B2862823 : Blo 1128631 2862823 := bstep (se 1 (by rfl) ⟨2147117, by rfl⟩ : syracuseStep 2862823 = 4294235) B4294235
theorem B9155753 : Blo 1128631 9155753 := bstep (se 2 (by rfl) ⟨3433407, by rfl⟩ : syracuseStep 9155753 = 6866815) B6866815
theorem B248036075 : Blo 1128631 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B4833391 : Blo 1128631 4833391 := bstep (se 1 (by rfl) ⟨3625043, by rfl⟩ : syracuseStep 4833391 = 7250087) B7250087
theorem B214387013 : Blo 1128631 214387013 := bstep (se 4 (by rfl) ⟨20098782, by rfl⟩ : syracuseStep 214387013 = 40197565) B40197565
theorem B69717095 : Blo 1128631 69717095 := bstep (se 1 (by rfl) ⟨52287821, by rfl⟩ : syracuseStep 69717095 = 104575643) B104575643
theorem B5426513 : Blo 1128631 5426513 := bstep (se 2 (by rfl) ⟨2034942, by rfl⟩ : syracuseStep 5426513 = 4069885) B4069885
theorem B2543471 : Blo 1128631 2543471 := bstep (se 1 (by rfl) ⟨1907603, by rfl⟩ : syracuseStep 2543471 = 3815207) B3815207
theorem B2544767 : Blo 1128631 2544767 := bstep (se 1 (by rfl) ⟨1908575, by rfl⟩ : syracuseStep 2544767 = 3817151) B3817151
theorem B2545919 : Blo 1128631 2545919 := bstep (se 1 (by rfl) ⟨1909439, by rfl⟩ : syracuseStep 2545919 = 3818879) B3818879
theorem B24435215 : Blo 1128631 24435215 := bstep (se 1 (by rfl) ⟨18326411, by rfl⟩ : syracuseStep 24435215 = 36652823) B36652823
theorem B1695263 : Blo 1128631 1695263 := bstep (se 1 (by rfl) ⟨1271447, by rfl⟩ : syracuseStep 1695263 = 2542895) B2542895
theorem B1695359 : Blo 1128631 1695359 := bstep (se 1 (by rfl) ⟨1271519, by rfl⟩ : syracuseStep 1695359 = 2543039) B2543039
theorem B24469127 : Blo 1128631 24469127 := bstep (se 1 (by rfl) ⟨18351845, by rfl⟩ : syracuseStep 24469127 = 36703691) B36703691
theorem B2547809 : Blo 1128631 2547809 := bstep (se 2 (by rfl) ⟨955428, by rfl⟩ : syracuseStep 2547809 = 1910857) B1910857
theorem B6518893 : Blo 1128631 6518893 := bstep (se 3 (by rfl) ⟨1222292, by rfl⟩ : syracuseStep 6518893 = 2444585) B2444585
theorem B29358695 : Blo 1128631 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B27463151 : Blo 1128631 27463151 := bstep (se 1 (by rfl) ⟨20597363, by rfl⟩ : syracuseStep 27463151 = 41194727) B41194727
theorem B16290143 : Blo 1128631 16290143 := bstep (se 1 (by rfl) ⟨12217607, by rfl⟩ : syracuseStep 16290143 = 24435215) B24435215
theorem B15473207 : Blo 1128631 15473207 := bstep (se 1 (by rfl) ⟨11604905, by rfl⟩ : syracuseStep 15473207 = 23209811) B23209811
theorem B8691857 : Blo 1128631 8691857 := bstep (se 2 (by rfl) ⟨3259446, by rfl⟩ : syracuseStep 8691857 = 6518893) B6518893
theorem B6103835 : Blo 1128631 6103835 := bstep (se 1 (by rfl) ⟨4577876, by rfl⟩ : syracuseStep 6103835 = 9155753) B9155753
theorem B19572463 : Blo 1128631 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B165357383 : Blo 1128631 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B20623787 : Blo 1128631 20623787 := bstep (se 1 (by rfl) ⟨15467840, by rfl⟩ : syracuseStep 20623787 = 30935681) B30935681
theorem B46478063 : Blo 1128631 46478063 := bstep (se 1 (by rfl) ⟨34858547, by rfl⟩ : syracuseStep 46478063 = 69717095) B69717095
theorem B3617675 : Blo 1128631 3617675 := bstep (se 1 (by rfl) ⟨2713256, by rfl⟩ : syracuseStep 3617675 = 5426513) B5426513
theorem B3817097 : Blo 1128631 3817097 := bstep (se 2 (by rfl) ⟨1431411, by rfl⟩ : syracuseStep 3817097 = 2862823) B2862823
theorem B1130175 : Blo 1128631 1130175 := bstep (se 1 (by rfl) ⟨847631, by rfl⟩ : syracuseStep 1130175 = 1695263) B1695263
theorem B1130239 : Blo 1128631 1130239 := bstep (se 1 (by rfl) ⟨847679, by rfl⟩ : syracuseStep 1130239 = 1695359) B1695359
theorem B2540123 : Blo 1128631 2540123 := bstep (se 1 (by rfl) ⟨1905092, by rfl⟩ : syracuseStep 2540123 = 3810185) B3810185
theorem B6444521 : Blo 1128631 6444521 := bstep (se 2 (by rfl) ⟨2416695, by rfl⟩ : syracuseStep 6444521 = 4833391) B4833391
theorem B2545577 : Blo 1128631 2545577 := bstep (se 2 (by rfl) ⟨954591, by rfl⟩ : syracuseStep 2545577 = 1909183) B1909183
theorem B2546441 : Blo 1128631 2546441 := bstep (se 2 (by rfl) ⟨954915, by rfl⟩ : syracuseStep 2546441 = 1909831) B1909831
theorem B142924675 : Blo 1128631 142924675 := bstep (se 1 (by rfl) ⟨107193506, by rfl⟩ : syracuseStep 142924675 = 214387013) B214387013
theorem B1695647 : Blo 1128631 1695647 := bstep (se 1 (by rfl) ⟨1271735, by rfl⟩ : syracuseStep 1695647 = 2543471) B2543471
theorem B8151131 : Blo 1128631 8151131 := bstep (se 1 (by rfl) ⟨6113348, by rfl⟩ : syracuseStep 8151131 = 12226697) B12226697
theorem B1696511 : Blo 1128631 1696511 := bstep (se 1 (by rfl) ⟨1272383, by rfl⟩ : syracuseStep 1696511 = 2544767) B2544767
theorem B9659159 : Blo 1128631 9659159 := bstep (se 1 (by rfl) ⟨7244369, by rfl⟩ : syracuseStep 9659159 = 14488739) B14488739
theorem B1697279 : Blo 1128631 1697279 := bstep (se 1 (by rfl) ⟨1272959, by rfl⟩ : syracuseStep 1697279 = 2545919) B2545919
theorem B16312751 : Blo 1128631 16312751 := bstep (se 1 (by rfl) ⟨12234563, by rfl⟩ : syracuseStep 16312751 = 24469127) B24469127
theorem B1698539 : Blo 1128631 1698539 := bstep (se 1 (by rfl) ⟨1273904, by rfl⟩ : syracuseStep 1698539 = 2547809) B2547809
theorem B4296347 : Blo 1128631 4296347 := bstep (se 1 (by rfl) ⟨3222260, by rfl⟩ : syracuseStep 4296347 = 6444521) B6444521
theorem B4069223 : Blo 1128631 4069223 := bstep (se 1 (by rfl) ⟨3051917, by rfl⟩ : syracuseStep 4069223 = 6103835) B6103835
theorem B26096617 : Blo 1128631 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B10860095 : Blo 1128631 10860095 := bstep (se 1 (by rfl) ⟨8145071, by rfl⟩ : syracuseStep 10860095 = 16290143) B16290143
theorem B1130431 : Blo 1128631 1130431 := bstep (se 1 (by rfl) ⟨847823, by rfl⟩ : syracuseStep 1130431 = 1695647) B1695647
theorem B1131007 : Blo 1128631 1131007 := bstep (se 1 (by rfl) ⟨848255, by rfl⟩ : syracuseStep 1131007 = 1696511) B1696511
theorem B6439439 : Blo 1128631 6439439 := bstep (se 1 (by rfl) ⟨4829579, by rfl⟩ : syracuseStep 6439439 = 9659159) B9659159
theorem B1131519 : Blo 1128631 1131519 := bstep (se 1 (by rfl) ⟨848639, by rfl⟩ : syracuseStep 1131519 = 1697279) B1697279
theorem B1132359 : Blo 1128631 1132359 := bstep (se 1 (by rfl) ⟨849269, by rfl⟩ : syracuseStep 1132359 = 1698539) B1698539
theorem B13749191 : Blo 1128631 13749191 := bstep (se 1 (by rfl) ⟨10311893, by rfl⟩ : syracuseStep 13749191 = 20623787) B20623787
theorem B30985375 : Blo 1128631 30985375 := bstep (se 1 (by rfl) ⟨23239031, by rfl⟩ : syracuseStep 30985375 = 46478063) B46478063
theorem B2411783 : Blo 1128631 2411783 := bstep (se 1 (by rfl) ⟨1808837, by rfl⟩ : syracuseStep 2411783 = 3617675) B3617675
theorem B190566233 : Blo 1128631 190566233 := bstep (se 2 (by rfl) ⟨71462337, by rfl⟩ : syracuseStep 190566233 = 142924675) B142924675
theorem B2544731 : Blo 1128631 2544731 := bstep (se 1 (by rfl) ⟨1908548, by rfl⟩ : syracuseStep 2544731 = 3817097) B3817097
theorem B1693415 : Blo 1128631 1693415 := bstep (se 1 (by rfl) ⟨1270061, by rfl⟩ : syracuseStep 1693415 = 2540123) B2540123
theorem B18308767 : Blo 1128631 18308767 := bstep (se 1 (by rfl) ⟨13731575, by rfl⟩ : syracuseStep 18308767 = 27463151) B27463151
theorem B1697051 : Blo 1128631 1697051 := bstep (se 1 (by rfl) ⟨1272788, by rfl⟩ : syracuseStep 1697051 = 2545577) B2545577
theorem B10315471 : Blo 1128631 10315471 := bstep (se 1 (by rfl) ⟨7736603, by rfl⟩ : syracuseStep 10315471 = 15473207) B15473207
theorem B1697627 : Blo 1128631 1697627 := bstep (se 1 (by rfl) ⟨1273220, by rfl⟩ : syracuseStep 1697627 = 2546441) B2546441
theorem B440953021 : Blo 1128631 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B5434087 : Blo 1128631 5434087 := bstep (se 1 (by rfl) ⟨4075565, by rfl⟩ : syracuseStep 5434087 = 8151131) B8151131
theorem B5794571 : Blo 1128631 5794571 := bstep (se 1 (by rfl) ⟨4345928, by rfl⟩ : syracuseStep 5794571 = 8691857) B8691857
theorem B10875167 : Blo 1128631 10875167 := bstep (se 1 (by rfl) ⟨8156375, by rfl⟩ : syracuseStep 10875167 = 16312751) B16312751
theorem B4292959 : Blo 1128631 4292959 := bstep (se 1 (by rfl) ⟨3219719, by rfl⟩ : syracuseStep 4292959 = 6439439) B6439439
theorem B1607855 : Blo 1128631 1607855 := bstep (se 1 (by rfl) ⟨1205891, by rfl⟩ : syracuseStep 1607855 = 2411783) B2411783
theorem B127044155 : Blo 1128631 127044155 := bstep (se 1 (by rfl) ⟨95283116, by rfl⟩ : syracuseStep 127044155 = 190566233) B190566233
theorem B7245449 : Blo 1128631 7245449 := bstep (se 2 (by rfl) ⟨2717043, by rfl⟩ : syracuseStep 7245449 = 5434087) B5434087
theorem B7250111 : Blo 1128631 7250111 := bstep (se 1 (by rfl) ⟨5437583, by rfl⟩ : syracuseStep 7250111 = 10875167) B10875167
theorem B2864231 : Blo 1128631 2864231 := bstep (se 1 (by rfl) ⟨2148173, by rfl⟩ : syracuseStep 2864231 = 4296347) B4296347
theorem B587937361 : Blo 1128631 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B1128943 : Blo 1128631 1128943 := bstep (se 1 (by rfl) ⟨846707, by rfl⟩ : syracuseStep 1128943 = 1693415) B1693415
theorem B1131367 : Blo 1128631 1131367 := bstep (se 1 (by rfl) ⟨848525, by rfl⟩ : syracuseStep 1131367 = 1697051) B1697051
theorem B1131751 : Blo 1128631 1131751 := bstep (se 1 (by rfl) ⟨848813, by rfl⟩ : syracuseStep 1131751 = 1697627) B1697627
theorem B9166127 : Blo 1128631 9166127 := bstep (se 1 (by rfl) ⟨6874595, by rfl⟩ : syracuseStep 9166127 = 13749191) B13749191
theorem B13753961 : Blo 1128631 13753961 := bstep (se 2 (by rfl) ⟨5157735, by rfl⟩ : syracuseStep 13753961 = 10315471) B10315471
theorem B1696487 : Blo 1128631 1696487 := bstep (se 1 (by rfl) ⟨1272365, by rfl⟩ : syracuseStep 1696487 = 2544731) B2544731
theorem B2712815 : Blo 1128631 2712815 := bstep (se 1 (by rfl) ⟨2034611, by rfl⟩ : syracuseStep 2712815 = 4069223) B4069223
theorem B28960253 : Blo 1128631 28960253 := bstep (se 3 (by rfl) ⟨5430047, by rfl⟩ : syracuseStep 28960253 = 10860095) B10860095
theorem B41313833 : Blo 1128631 41313833 := bstep (se 2 (by rfl) ⟨15492687, by rfl⟩ : syracuseStep 41313833 = 30985375) B30985375
theorem B34795489 : Blo 1128631 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B3863047 : Blo 1128631 3863047 := bstep (se 1 (by rfl) ⟨2897285, by rfl⟩ : syracuseStep 3863047 = 5794571) B5794571
theorem B24411689 : Blo 1128631 24411689 := bstep (se 2 (by rfl) ⟨9154383, by rfl⟩ : syracuseStep 24411689 = 18308767) B18308767
theorem B5150729 : Blo 1128631 5150729 := bstep (se 2 (by rfl) ⟨1931523, by rfl⟩ : syracuseStep 5150729 = 3863047) B3863047
theorem B1808543 : Blo 1128631 1808543 := bstep (se 1 (by rfl) ⟨1356407, by rfl⟩ : syracuseStep 1808543 = 2712815) B2712815
theorem B19306835 : Blo 1128631 19306835 := bstep (se 1 (by rfl) ⟨14480126, by rfl⟩ : syracuseStep 19306835 = 28960253) B28960253
theorem B783916481 : Blo 1128631 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B1909487 : Blo 1128631 1909487 := bstep (se 1 (by rfl) ⟨1432115, by rfl⟩ : syracuseStep 1909487 = 2864231) B2864231
theorem B4830299 : Blo 1128631 4830299 := bstep (se 1 (by rfl) ⟨3622724, by rfl⟩ : syracuseStep 4830299 = 7245449) B7245449
theorem B4833407 : Blo 1128631 4833407 := bstep (se 1 (by rfl) ⟨3625055, by rfl⟩ : syracuseStep 4833407 = 7250111) B7250111
theorem B1130991 : Blo 1128631 1130991 := bstep (se 1 (by rfl) ⟨848243, by rfl⟩ : syracuseStep 1130991 = 1696487) B1696487
theorem B27542555 : Blo 1128631 27542555 := bstep (se 1 (by rfl) ⟨20656916, by rfl⟩ : syracuseStep 27542555 = 41313833) B41313833
theorem B16274459 : Blo 1128631 16274459 := bstep (se 1 (by rfl) ⟨12205844, by rfl⟩ : syracuseStep 16274459 = 24411689) B24411689
theorem B5723945 : Blo 1128631 5723945 := bstep (se 2 (by rfl) ⟨2146479, by rfl⟩ : syracuseStep 5723945 = 4292959) B4292959
theorem B84696103 : Blo 1128631 84696103 := bstep (se 1 (by rfl) ⟨63522077, by rfl⟩ : syracuseStep 84696103 = 127044155) B127044155
theorem B9169307 : Blo 1128631 9169307 := bstep (se 1 (by rfl) ⟨6876980, by rfl⟩ : syracuseStep 9169307 = 13753961) B13753961
theorem B46393985 : Blo 1128631 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B4287613 : Blo 1128631 4287613 := bstep (se 3 (by rfl) ⟨803927, by rfl⟩ : syracuseStep 4287613 = 1607855) B1607855
theorem B24443005 : Blo 1128631 24443005 := bstep (se 3 (by rfl) ⟨4583063, by rfl⟩ : syracuseStep 24443005 = 9166127) B9166127
theorem B10849639 : Blo 1128631 10849639 := bstep (se 1 (by rfl) ⟨8137229, by rfl⟩ : syracuseStep 10849639 = 16274459) B16274459
theorem B13735277 : Blo 1128631 13735277 := bstep (se 3 (by rfl) ⟨2575364, by rfl⟩ : syracuseStep 13735277 = 5150729) B5150729
theorem B3220199 : Blo 1128631 3220199 := bstep (se 1 (by rfl) ⟨2415149, by rfl⟩ : syracuseStep 3220199 = 4830299) B4830299
theorem B112928137 : Blo 1128631 112928137 := bstep (se 2 (by rfl) ⟨42348051, by rfl⟩ : syracuseStep 112928137 = 84696103) B84696103
theorem B3222271 : Blo 1128631 3222271 := bstep (se 1 (by rfl) ⟨2416703, by rfl⟩ : syracuseStep 3222271 = 4833407) B4833407
theorem B18361703 : Blo 1128631 18361703 := bstep (se 1 (by rfl) ⟨13771277, by rfl⟩ : syracuseStep 18361703 = 27542555) B27542555
theorem B3815963 : Blo 1128631 3815963 := bstep (se 1 (by rfl) ⟨2861972, by rfl⟩ : syracuseStep 3815963 = 5723945) B5723945
theorem B5716817 : Blo 1128631 5716817 := bstep (se 2 (by rfl) ⟨2143806, by rfl⟩ : syracuseStep 5716817 = 4287613) B4287613
theorem B6112871 : Blo 1128631 6112871 := bstep (se 1 (by rfl) ⟨4584653, by rfl⟩ : syracuseStep 6112871 = 9169307) B9169307
theorem B123717293 : Blo 1128631 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B32590673 : Blo 1128631 32590673 := bstep (se 2 (by rfl) ⟨12221502, by rfl⟩ : syracuseStep 32590673 = 24443005) B24443005
theorem B1205695 : Blo 1128631 1205695 := bstep (se 1 (by rfl) ⟨904271, by rfl⟩ : syracuseStep 1205695 = 1808543) B1808543
theorem B12871223 : Blo 1128631 12871223 := bstep (se 1 (by rfl) ⟨9653417, by rfl⟩ : syracuseStep 12871223 = 19306835) B19306835
theorem B522610987 : Blo 1128631 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B1272991 : Blo 1128631 1272991 := bstep (se 1 (by rfl) ⟨954743, by rfl⟩ : syracuseStep 1272991 = 1909487) B1909487
theorem B82478195 : Blo 1128631 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B21727115 : Blo 1128631 21727115 := bstep (se 1 (by rfl) ⟨16295336, by rfl⟩ : syracuseStep 21727115 = 32590673) B32590673
theorem B696814649 : Blo 1128631 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B4296361 : Blo 1128631 4296361 := bstep (se 2 (by rfl) ⟨1611135, by rfl⟩ : syracuseStep 4296361 = 3222271) B3222271
theorem B6430373 : Blo 1128631 6430373 := bstep (se 4 (by rfl) ⟨602847, by rfl⟩ : syracuseStep 6430373 = 1205695) B1205695
theorem B3811211 : Blo 1128631 3811211 := bstep (se 1 (by rfl) ⟨2858408, by rfl⟩ : syracuseStep 3811211 = 5716817) B5716817
theorem B4075247 : Blo 1128631 4075247 := bstep (se 1 (by rfl) ⟨3056435, by rfl⟩ : syracuseStep 4075247 = 6112871) B6112871
theorem B9156851 : Blo 1128631 9156851 := bstep (se 1 (by rfl) ⟨6867638, by rfl⟩ : syracuseStep 9156851 = 13735277) B13735277
theorem B14466185 : Blo 1128631 14466185 := bstep (se 2 (by rfl) ⟨5424819, by rfl⟩ : syracuseStep 14466185 = 10849639) B10849639
theorem B2146799 : Blo 1128631 2146799 := bstep (se 1 (by rfl) ⟨1610099, by rfl⟩ : syracuseStep 2146799 = 3220199) B3220199
theorem B12241135 : Blo 1128631 12241135 := bstep (se 1 (by rfl) ⟨9180851, by rfl⟩ : syracuseStep 12241135 = 18361703) B18361703
theorem B2543975 : Blo 1128631 2543975 := bstep (se 1 (by rfl) ⟨1907981, by rfl⟩ : syracuseStep 2543975 = 3815963) B3815963
theorem B1697321 : Blo 1128631 1697321 := bstep (se 2 (by rfl) ⟨636495, by rfl⟩ : syracuseStep 1697321 = 1272991) B1272991
theorem B8580815 : Blo 1128631 8580815 := bstep (se 1 (by rfl) ⟨6435611, by rfl⟩ : syracuseStep 8580815 = 12871223) B12871223
theorem B2409133589 : Blo 1128631 2409133589 := bstep (se 6 (by rfl) ⟨56464068, by rfl⟩ : syracuseStep 2409133589 = 112928137) B112928137
theorem B54985463 : Blo 1128631 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B14484743 : Blo 1128631 14484743 := bstep (se 1 (by rfl) ⟨10863557, by rfl⟩ : syracuseStep 14484743 = 21727115) B21727115
theorem B16321513 : Blo 1128631 16321513 := bstep (se 2 (by rfl) ⟨6120567, by rfl⟩ : syracuseStep 16321513 = 12241135) B12241135
theorem B6104567 : Blo 1128631 6104567 := bstep (se 1 (by rfl) ⟨4578425, by rfl⟩ : syracuseStep 6104567 = 9156851) B9156851
theorem B9644123 : Blo 1128631 9644123 := bstep (se 1 (by rfl) ⟨7233092, by rfl⟩ : syracuseStep 9644123 = 14466185) B14466185
theorem B1131547 : Blo 1128631 1131547 := bstep (se 1 (by rfl) ⟨848660, by rfl⟩ : syracuseStep 1131547 = 1697321) B1697321
theorem B2540807 : Blo 1128631 2540807 := bstep (se 1 (by rfl) ⟨1905605, by rfl⟩ : syracuseStep 2540807 = 3811211) B3811211
theorem B5720543 : Blo 1128631 5720543 := bstep (se 1 (by rfl) ⟨4290407, by rfl⟩ : syracuseStep 5720543 = 8580815) B8580815
theorem B1431199 : Blo 1128631 1431199 := bstep (se 1 (by rfl) ⟨1073399, by rfl⟩ : syracuseStep 1431199 = 2146799) B2146799
theorem B464543099 : Blo 1128631 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B1695983 : Blo 1128631 1695983 := bstep (se 1 (by rfl) ⟨1271987, by rfl⟩ : syracuseStep 1695983 = 2543975) B2543975
theorem B5728481 : Blo 1128631 5728481 := bstep (se 2 (by rfl) ⟨2148180, by rfl⟩ : syracuseStep 5728481 = 4296361) B4296361
theorem B4286915 : Blo 1128631 4286915 := bstep (se 1 (by rfl) ⟨3215186, by rfl⟩ : syracuseStep 4286915 = 6430373) B6430373
theorem B2716831 : Blo 1128631 2716831 := bstep (se 1 (by rfl) ⟨2037623, by rfl⟩ : syracuseStep 2716831 = 4075247) B4075247
theorem B1606089059 : Blo 1128631 1606089059 := bstep (se 1 (by rfl) ⟨1204566794, by rfl⟩ : syracuseStep 1606089059 = 2409133589) B2409133589
theorem B21762017 : Blo 1128631 21762017 := bstep (se 2 (by rfl) ⟨8160756, by rfl⟩ : syracuseStep 21762017 = 16321513) B16321513
theorem B309695399 : Blo 1128631 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B14489765 : Blo 1128631 14489765 := bstep (se 4 (by rfl) ⟨1358415, by rfl⟩ : syracuseStep 14489765 = 2716831) B2716831
theorem B4069711 : Blo 1128631 4069711 := bstep (se 1 (by rfl) ⟨3052283, by rfl⟩ : syracuseStep 4069711 = 6104567) B6104567
theorem B6429415 : Blo 1128631 6429415 := bstep (se 1 (by rfl) ⟨4822061, by rfl⟩ : syracuseStep 6429415 = 9644123) B9644123
theorem B2857943 : Blo 1128631 2857943 := bstep (se 1 (by rfl) ⟨2143457, by rfl⟩ : syracuseStep 2857943 = 4286915) B4286915
theorem B1908265 : Blo 1128631 1908265 := bstep (se 2 (by rfl) ⟨715599, by rfl⟩ : syracuseStep 1908265 = 1431199) B1431199
theorem B3813695 : Blo 1128631 3813695 := bstep (se 1 (by rfl) ⟨2860271, by rfl⟩ : syracuseStep 3813695 = 5720543) B5720543
theorem B1130655 : Blo 1128631 1130655 := bstep (se 1 (by rfl) ⟨847991, by rfl⟩ : syracuseStep 1130655 = 1695983) B1695983
theorem B3818987 : Blo 1128631 3818987 := bstep (se 1 (by rfl) ⟨2864240, by rfl⟩ : syracuseStep 3818987 = 5728481) B5728481
theorem B36656975 : Blo 1128631 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B1693871 : Blo 1128631 1693871 := bstep (se 1 (by rfl) ⟨1270403, by rfl⟩ : syracuseStep 1693871 = 2540807) B2540807
theorem B9656495 : Blo 1128631 9656495 := bstep (se 1 (by rfl) ⟨7242371, by rfl⟩ : syracuseStep 9656495 = 14484743) B14484743
theorem B1070726039 : Blo 1128631 1070726039 := bstep (se 1 (by rfl) ⟨803044529, by rfl⟩ : syracuseStep 1070726039 = 1606089059) B1606089059
theorem B1905295 : Blo 1128631 1905295 := bstep (se 1 (by rfl) ⟨1428971, by rfl⟩ : syracuseStep 1905295 = 2857943) B2857943
theorem B1129247 : Blo 1128631 1129247 := bstep (se 1 (by rfl) ⟨846935, by rfl⟩ : syracuseStep 1129247 = 1693871) B1693871
theorem B6437663 : Blo 1128631 6437663 := bstep (se 1 (by rfl) ⟨4828247, by rfl⟩ : syracuseStep 6437663 = 9656495) B9656495
theorem B2542463 : Blo 1128631 2542463 := bstep (se 1 (by rfl) ⟨1906847, by rfl⟩ : syracuseStep 2542463 = 3813695) B3813695
theorem B5426281 : Blo 1128631 5426281 := bstep (se 2 (by rfl) ⟨2034855, by rfl⟩ : syracuseStep 5426281 = 4069711) B4069711
theorem B8572553 : Blo 1128631 8572553 := bstep (se 2 (by rfl) ⟨3214707, by rfl⟩ : syracuseStep 8572553 = 6429415) B6429415
theorem B2544353 : Blo 1128631 2544353 := bstep (se 2 (by rfl) ⟨954132, by rfl⟩ : syracuseStep 2544353 = 1908265) B1908265
theorem B2545991 : Blo 1128631 2545991 := bstep (se 1 (by rfl) ⟨1909493, by rfl⟩ : syracuseStep 2545991 = 3818987) B3818987
theorem B14508011 : Blo 1128631 14508011 := bstep (se 1 (by rfl) ⟨10881008, by rfl⟩ : syracuseStep 14508011 = 21762017) B21762017
theorem B206463599 : Blo 1128631 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B24437983 : Blo 1128631 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B9659843 : Blo 1128631 9659843 := bstep (se 1 (by rfl) ⟨7244882, by rfl⟩ : syracuseStep 9659843 = 14489765) B14489765
theorem B713817359 : Blo 1128631 713817359 := bstep (se 1 (by rfl) ⟨535363019, by rfl⟩ : syracuseStep 713817359 = 1070726039) B1070726039
theorem B9672007 : Blo 1128631 9672007 := bstep (se 1 (by rfl) ⟨7254005, by rfl⟩ : syracuseStep 9672007 = 14508011) B14508011
theorem B32583977 : Blo 1128631 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B5715035 : Blo 1128631 5715035 := bstep (se 1 (by rfl) ⟨4286276, by rfl⟩ : syracuseStep 5715035 = 8572553) B8572553
theorem B137642399 : Blo 1128631 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B2540393 : Blo 1128631 2540393 := bstep (se 2 (by rfl) ⟨952647, by rfl⟩ : syracuseStep 2540393 = 1905295) B1905295
theorem B6439895 : Blo 1128631 6439895 := bstep (se 1 (by rfl) ⟨4829921, by rfl⟩ : syracuseStep 6439895 = 9659843) B9659843
theorem B475878239 : Blo 1128631 475878239 := bstep (se 1 (by rfl) ⟨356908679, by rfl⟩ : syracuseStep 475878239 = 713817359) B713817359
theorem B1694975 : Blo 1128631 1694975 := bstep (se 1 (by rfl) ⟨1271231, by rfl⟩ : syracuseStep 1694975 = 2542463) B2542463
theorem B1696235 : Blo 1128631 1696235 := bstep (se 1 (by rfl) ⟨1272176, by rfl⟩ : syracuseStep 1696235 = 2544353) B2544353
theorem B7235041 : Blo 1128631 7235041 := bstep (se 2 (by rfl) ⟨2713140, by rfl⟩ : syracuseStep 7235041 = 5426281) B5426281
theorem B1697327 : Blo 1128631 1697327 := bstep (se 1 (by rfl) ⟨1272995, by rfl⟩ : syracuseStep 1697327 = 2545991) B2545991
theorem B4291775 : Blo 1128631 4291775 := bstep (se 1 (by rfl) ⟨3218831, by rfl⟩ : syracuseStep 4291775 = 6437663) B6437663
theorem B4293263 : Blo 1128631 4293263 := bstep (se 1 (by rfl) ⟨3219947, by rfl⟩ : syracuseStep 4293263 = 6439895) B6439895
theorem B3810023 : Blo 1128631 3810023 := bstep (se 1 (by rfl) ⟨2857517, by rfl⟩ : syracuseStep 3810023 = 5715035) B5715035
theorem B2861183 : Blo 1128631 2861183 := bstep (se 1 (by rfl) ⟨2145887, by rfl⟩ : syracuseStep 2861183 = 4291775) B4291775
theorem B91761599 : Blo 1128631 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B9646721 : Blo 1128631 9646721 := bstep (se 2 (by rfl) ⟨3617520, by rfl⟩ : syracuseStep 9646721 = 7235041) B7235041
theorem B1129983 : Blo 1128631 1129983 := bstep (se 1 (by rfl) ⟨847487, by rfl⟩ : syracuseStep 1129983 = 1694975) B1694975
theorem B1130823 : Blo 1128631 1130823 := bstep (se 1 (by rfl) ⟨848117, by rfl⟩ : syracuseStep 1130823 = 1696235) B1696235
theorem B1131551 : Blo 1128631 1131551 := bstep (se 1 (by rfl) ⟨848663, by rfl⟩ : syracuseStep 1131551 = 1697327) B1697327
theorem B12896009 : Blo 1128631 12896009 := bstep (se 2 (by rfl) ⟨4836003, by rfl⟩ : syracuseStep 12896009 = 9672007) B9672007
theorem B1693595 : Blo 1128631 1693595 := bstep (se 1 (by rfl) ⟨1270196, by rfl⟩ : syracuseStep 1693595 = 2540393) B2540393
theorem B317252159 : Blo 1128631 317252159 := bstep (se 1 (by rfl) ⟨237939119, by rfl⟩ : syracuseStep 317252159 = 475878239) B475878239
theorem B21722651 : Blo 1128631 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B1907455 : Blo 1128631 1907455 := bstep (se 1 (by rfl) ⟨1430591, by rfl⟩ : syracuseStep 1907455 = 2861183) B2861183
theorem B6431147 : Blo 1128631 6431147 := bstep (se 1 (by rfl) ⟨4823360, by rfl⟩ : syracuseStep 6431147 = 9646721) B9646721
theorem B2862175 : Blo 1128631 2862175 := bstep (se 1 (by rfl) ⟨2146631, by rfl⟩ : syracuseStep 2862175 = 4293263) B4293263
theorem B8597339 : Blo 1128631 8597339 := bstep (se 1 (by rfl) ⟨6448004, by rfl⟩ : syracuseStep 8597339 = 12896009) B12896009
theorem B1129063 : Blo 1128631 1129063 := bstep (se 1 (by rfl) ⟨846797, by rfl⟩ : syracuseStep 1129063 = 1693595) B1693595
theorem B211501439 : Blo 1128631 211501439 := bstep (se 1 (by rfl) ⟨158626079, by rfl⟩ : syracuseStep 211501439 = 317252159) B317252159
theorem B2540015 : Blo 1128631 2540015 := bstep (se 1 (by rfl) ⟨1905011, by rfl⟩ : syracuseStep 2540015 = 3810023) B3810023
theorem B61174399 : Blo 1128631 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B14481767 : Blo 1128631 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B141000959 : Blo 1128631 141000959 := bstep (se 1 (by rfl) ⟨105750719, by rfl⟩ : syracuseStep 141000959 = 211501439) B211501439
theorem B81565865 : Blo 1128631 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B3816233 : Blo 1128631 3816233 := bstep (se 2 (by rfl) ⟨1431087, by rfl⟩ : syracuseStep 3816233 = 2862175) B2862175
theorem B2543273 : Blo 1128631 2543273 := bstep (se 2 (by rfl) ⟨953727, by rfl⟩ : syracuseStep 2543273 = 1907455) B1907455
theorem B9654511 : Blo 1128631 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B1693343 : Blo 1128631 1693343 := bstep (se 1 (by rfl) ⟨1270007, by rfl⟩ : syracuseStep 1693343 = 2540015) B2540015
theorem B4287431 : Blo 1128631 4287431 := bstep (se 1 (by rfl) ⟨3215573, by rfl⟩ : syracuseStep 4287431 = 6431147) B6431147
theorem B5731559 : Blo 1128631 5731559 := bstep (se 1 (by rfl) ⟨4298669, by rfl⟩ : syracuseStep 5731559 = 8597339) B8597339
theorem B2858287 : Blo 1128631 2858287 := bstep (se 1 (by rfl) ⟨2143715, by rfl⟩ : syracuseStep 2858287 = 4287431) B4287431
theorem B1128895 : Blo 1128631 1128895 := bstep (se 1 (by rfl) ⟨846671, by rfl⟩ : syracuseStep 1128895 = 1693343) B1693343
theorem B54377243 : Blo 1128631 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B3821039 : Blo 1128631 3821039 := bstep (se 1 (by rfl) ⟨2865779, by rfl⟩ : syracuseStep 3821039 = 5731559) B5731559
theorem B2544155 : Blo 1128631 2544155 := bstep (se 1 (by rfl) ⟨1908116, by rfl⟩ : syracuseStep 2544155 = 3816233) B3816233
theorem B376002557 : Blo 1128631 376002557 := bstep (se 3 (by rfl) ⟨70500479, by rfl⟩ : syracuseStep 376002557 = 141000959) B141000959
theorem B1695515 : Blo 1128631 1695515 := bstep (se 1 (by rfl) ⟨1271636, by rfl⟩ : syracuseStep 1695515 = 2543273) B2543273
theorem B12872681 : Blo 1128631 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B3811049 : Blo 1128631 3811049 := bstep (se 2 (by rfl) ⟨1429143, by rfl⟩ : syracuseStep 3811049 = 2858287) B2858287
theorem B36251495 : Blo 1128631 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B1130343 : Blo 1128631 1130343 := bstep (se 1 (by rfl) ⟨847757, by rfl⟩ : syracuseStep 1130343 = 1695515) B1695515
theorem B2547359 : Blo 1128631 2547359 := bstep (se 1 (by rfl) ⟨1910519, by rfl⟩ : syracuseStep 2547359 = 3821039) B3821039
theorem B1696103 : Blo 1128631 1696103 := bstep (se 1 (by rfl) ⟨1272077, by rfl⟩ : syracuseStep 1696103 = 2544155) B2544155
theorem B250668371 : Blo 1128631 250668371 := bstep (se 1 (by rfl) ⟨188001278, by rfl⟩ : syracuseStep 250668371 = 376002557) B376002557
theorem B8581787 : Blo 1128631 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B1130735 : Blo 1128631 1130735 := bstep (se 1 (by rfl) ⟨848051, by rfl⟩ : syracuseStep 1130735 = 1696103) B1696103
theorem B2540699 : Blo 1128631 2540699 := bstep (se 1 (by rfl) ⟨1905524, by rfl⟩ : syracuseStep 2540699 = 3811049) B3811049
theorem B24167663 : Blo 1128631 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B5721191 : Blo 1128631 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B1698239 : Blo 1128631 1698239 := bstep (se 1 (by rfl) ⟨1273679, by rfl⟩ : syracuseStep 1698239 = 2547359) B2547359
theorem B167112247 : Blo 1128631 167112247 := bstep (se 1 (by rfl) ⟨125334185, by rfl⟩ : syracuseStep 167112247 = 250668371) B250668371
theorem B3814127 : Blo 1128631 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B1132159 : Blo 1128631 1132159 := bstep (se 1 (by rfl) ⟨849119, by rfl⟩ : syracuseStep 1132159 = 1698239) B1698239
theorem B1693799 : Blo 1128631 1693799 := bstep (se 1 (by rfl) ⟨1270349, by rfl⟩ : syracuseStep 1693799 = 2540699) B2540699
theorem B16111775 : Blo 1128631 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B222816329 : Blo 1128631 222816329 := bstep (se 2 (by rfl) ⟨83556123, by rfl⟩ : syracuseStep 222816329 = 167112247) B167112247
theorem B148544219 : Blo 1128631 148544219 := bstep (se 1 (by rfl) ⟨111408164, by rfl⟩ : syracuseStep 148544219 = 222816329) B222816329
theorem B1129199 : Blo 1128631 1129199 := bstep (se 1 (by rfl) ⟨846899, by rfl⟩ : syracuseStep 1129199 = 1693799) B1693799
theorem B2542751 : Blo 1128631 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B10741183 : Blo 1128631 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B99029479 : Blo 1128631 99029479 := bstep (se 1 (by rfl) ⟨74272109, by rfl⟩ : syracuseStep 99029479 = 148544219) B148544219
theorem B57286309 : Blo 1128631 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B1695167 : Blo 1128631 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B1130111 : Blo 1128631 1130111 := bstep (se 1 (by rfl) ⟨847583, by rfl⟩ : syracuseStep 1130111 = 1695167) B1695167
theorem B132039305 : Blo 1128631 132039305 := bstep (se 2 (by rfl) ⟨49514739, by rfl⟩ : syracuseStep 132039305 = 99029479) B99029479
theorem B76381745 : Blo 1128631 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B88026203 : Blo 1128631 88026203 := bstep (se 1 (by rfl) ⟨66019652, by rfl⟩ : syracuseStep 88026203 = 132039305) B132039305
theorem B203684653 : Blo 1128631 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B234736541 : Blo 1128631 234736541 := bstep (se 3 (by rfl) ⟨44013101, by rfl⟩ : syracuseStep 234736541 = 88026203) B88026203
theorem B271579537 : Blo 1128631 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B362106049 : Blo 1128631 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B156491027 : Blo 1128631 156491027 := bstep (se 1 (by rfl) ⟨117368270, by rfl⟩ : syracuseStep 156491027 = 234736541) B234736541
theorem B482808065 : Blo 1128631 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B104327351 : Blo 1128631 104327351 := bstep (se 1 (by rfl) ⟨78245513, by rfl⟩ : syracuseStep 104327351 = 156491027) B156491027
theorem B5149952693 : Blo 1128631 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B69551567 : Blo 1128631 69551567 := bstep (se 1 (by rfl) ⟨52163675, by rfl⟩ : syracuseStep 69551567 = 104327351) B104327351
theorem B46367711 : Blo 1128631 46367711 := bstep (se 1 (by rfl) ⟨34775783, by rfl⟩ : syracuseStep 46367711 = 69551567) B69551567
theorem B3433301795 : Blo 1128631 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B30911807 : Blo 1128631 30911807 := bstep (se 1 (by rfl) ⟨23183855, by rfl⟩ : syracuseStep 30911807 = 46367711) B46367711
theorem B2288867863 : Blo 1128631 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B3051823817 : Blo 1128631 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B20607871 : Blo 1128631 20607871 := bstep (se 1 (by rfl) ⟨15455903, by rfl⟩ : syracuseStep 20607871 = 30911807) B30911807
theorem B8138196845 : Blo 1128631 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B27477161 : Blo 1128631 27477161 := bstep (se 2 (by rfl) ⟨10303935, by rfl⟩ : syracuseStep 27477161 = 20607871) B20607871
theorem B18318107 : Blo 1128631 18318107 := bstep (se 1 (by rfl) ⟨13738580, by rfl⟩ : syracuseStep 18318107 = 27477161) B27477161
theorem B5425464563 : Blo 1128631 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B3616976375 : Blo 1128631 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B48848285 : Blo 1128631 48848285 := bstep (se 3 (by rfl) ⟨9159053, by rfl⟩ : syracuseStep 48848285 = 18318107) B18318107
theorem B2411317583 : Blo 1128631 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B32565523 : Blo 1128631 32565523 := bstep (se 1 (by rfl) ⟨24424142, by rfl⟩ : syracuseStep 32565523 = 48848285) B48848285
theorem B43420697 : Blo 1128631 43420697 := bstep (se 2 (by rfl) ⟨16282761, by rfl⟩ : syracuseStep 43420697 = 32565523) B32565523
theorem B1607545055 : Blo 1128631 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B28947131 : Blo 1128631 28947131 := bstep (se 1 (by rfl) ⟨21710348, by rfl⟩ : syracuseStep 28947131 = 43420697) B43420697
theorem B1071696703 : Blo 1128631 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B1428928937 : Blo 1128631 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B19298087 : Blo 1128631 19298087 := bstep (se 1 (by rfl) ⟨14473565, by rfl⟩ : syracuseStep 19298087 = 28947131) B28947131
theorem B12865391 : Blo 1128631 12865391 := bstep (se 1 (by rfl) ⟨9649043, by rfl⟩ : syracuseStep 12865391 = 19298087) B19298087
theorem B952619291 : Blo 1128631 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B635079527 : Blo 1128631 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B8576927 : Blo 1128631 8576927 := bstep (se 1 (by rfl) ⟨6432695, by rfl⟩ : syracuseStep 8576927 = 12865391) B12865391
theorem B5717951 : Blo 1128631 5717951 := bstep (se 1 (by rfl) ⟨4288463, by rfl⟩ : syracuseStep 5717951 = 8576927) B8576927
theorem B423386351 : Blo 1128631 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B3811967 : Blo 1128631 3811967 := bstep (se 1 (by rfl) ⟨2858975, by rfl⟩ : syracuseStep 3811967 = 5717951) B5717951
theorem B282257567 : Blo 1128631 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B188171711 : Blo 1128631 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B2541311 : Blo 1128631 2541311 := bstep (se 1 (by rfl) ⟨1905983, by rfl⟩ : syracuseStep 2541311 = 3811967) B3811967
theorem B125447807 : Blo 1128631 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B1694207 : Blo 1128631 1694207 := bstep (se 1 (by rfl) ⟨1270655, by rfl⟩ : syracuseStep 1694207 = 2541311) B2541311
theorem B83631871 : Blo 1128631 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B1129471 : Blo 1128631 1129471 := bstep (se 1 (by rfl) ⟨847103, by rfl⟩ : syracuseStep 1129471 = 1694207) B1694207
theorem B446036645 : Blo 1128631 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B297357763 : Blo 1128631 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B396477017 : Blo 1128631 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B264318011 : Blo 1128631 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B176212007 : Blo 1128631 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B117474671 : Blo 1128631 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B313265789 : Blo 1128631 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B208843859 : Blo 1128631 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B139229239 : Blo 1128631 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B185638985 : Blo 1128631 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B123759323 : Blo 1128631 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B82506215 : Blo 1128631 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B220016573 : Blo 1128631 220016573 := bstep (se 3 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 220016573 = 82506215) B82506215
theorem B146677715 : Blo 1128631 146677715 := bstep (se 1 (by rfl) ⟨110008286, by rfl⟩ : syracuseStep 146677715 = 220016573) B220016573
theorem B97785143 : Blo 1128631 97785143 := bstep (se 1 (by rfl) ⟨73338857, by rfl⟩ : syracuseStep 97785143 = 146677715) B146677715
theorem B65190095 : Blo 1128631 65190095 := bstep (se 1 (by rfl) ⟨48892571, by rfl⟩ : syracuseStep 65190095 = 97785143) B97785143
theorem B43460063 : Blo 1128631 43460063 := bstep (se 1 (by rfl) ⟨32595047, by rfl⟩ : syracuseStep 43460063 = 65190095) B65190095
theorem B28973375 : Blo 1128631 28973375 := bstep (se 1 (by rfl) ⟨21730031, by rfl⟩ : syracuseStep 28973375 = 43460063) B43460063
theorem B19315583 : Blo 1128631 19315583 := bstep (se 1 (by rfl) ⟨14486687, by rfl⟩ : syracuseStep 19315583 = 28973375) B28973375
theorem B12877055 : Blo 1128631 12877055 := bstep (se 1 (by rfl) ⟨9657791, by rfl⟩ : syracuseStep 12877055 = 19315583) B19315583
theorem B8584703 : Blo 1128631 8584703 := bstep (se 1 (by rfl) ⟨6438527, by rfl⟩ : syracuseStep 8584703 = 12877055) B12877055
theorem B5723135 : Blo 1128631 5723135 := bstep (se 1 (by rfl) ⟨4292351, by rfl⟩ : syracuseStep 5723135 = 8584703) B8584703
theorem B3815423 : Blo 1128631 3815423 := bstep (se 1 (by rfl) ⟨2861567, by rfl⟩ : syracuseStep 3815423 = 5723135) B5723135
theorem B2543615 : Blo 1128631 2543615 := bstep (se 1 (by rfl) ⟨1907711, by rfl⟩ : syracuseStep 2543615 = 3815423) B3815423
theorem B1695743 : Blo 1128631 1695743 := bstep (se 1 (by rfl) ⟨1271807, by rfl⟩ : syracuseStep 1695743 = 2543615) B2543615
theorem B1130495 : Blo 1128631 1130495 := bstep (se 1 (by rfl) ⟨847871, by rfl⟩ : syracuseStep 1130495 = 1695743) B1695743

theorem C0 (j : ℕ) (h1 : 282157 ≤ j) (h2 : j ≤ 282856) : Blo 1128631 (4 * j + 3) := by
  interval_cases j
  · exact B1128631
  · exact B1128635
  · exact B1128639
  · exact B1128643
  · exact B1128647
  · exact B1128651
  · exact B1128655
  · exact B1128659
  · exact B1128663
  · exact B1128667
  · exact B1128671
  · exact B1128675
  · exact B1128679
  · exact B1128683
  · exact B1128687
  · exact B1128691
  · exact B1128695
  · exact B1128699
  · exact B1128703
  · exact B1128707
  · exact B1128711
  · exact B1128715
  · exact B1128719
  · exact B1128723
  · exact B1128727
  · exact B1128731
  · exact B1128735
  · exact B1128739
  · exact B1128743
  · exact B1128747
  · exact B1128751
  · exact B1128755
  · exact B1128759
  · exact B1128763
  · exact B1128767
  · exact B1128771
  · exact B1128775
  · exact B1128779
  · exact B1128783
  · exact B1128787
  · exact B1128791
  · exact B1128795
  · exact B1128799
  · exact B1128803
  · exact B1128807
  · exact B1128811
  · exact B1128815
  · exact B1128819
  · exact B1128823
  · exact B1128827
  · exact B1128831
  · exact B1128835
  · exact B1128839
  · exact B1128843
  · exact B1128847
  · exact B1128851
  · exact B1128855
  · exact B1128859
  · exact B1128863
  · exact B1128867
  · exact B1128871
  · exact B1128875
  · exact B1128879
  · exact B1128883
  · exact B1128887
  · exact B1128891
  · exact B1128895
  · exact B1128899
  · exact B1128903
  · exact B1128907
  · exact B1128911
  · exact B1128915
  · exact B1128919
  · exact B1128923
  · exact B1128927
  · exact B1128931
  · exact B1128935
  · exact B1128939
  · exact B1128943
  · exact B1128947
  · exact B1128951
  · exact B1128955
  · exact B1128959
  · exact B1128963
  · exact B1128967
  · exact B1128971
  · exact B1128975
  · exact B1128979
  · exact B1128983
  · exact B1128987
  · exact B1128991
  · exact B1128995
  · exact B1128999
  · exact B1129003
  · exact B1129007
  · exact B1129011
  · exact B1129015
  · exact B1129019
  · exact B1129023
  · exact B1129027
  · exact B1129031
  · exact B1129035
  · exact B1129039
  · exact B1129043
  · exact B1129047
  · exact B1129051
  · exact B1129055
  · exact B1129059
  · exact B1129063
  · exact B1129067
  · exact B1129071
  · exact B1129075
  · exact B1129079
  · exact B1129083
  · exact B1129087
  · exact B1129091
  · exact B1129095
  · exact B1129099
  · exact B1129103
  · exact B1129107
  · exact B1129111
  · exact B1129115
  · exact B1129119
  · exact B1129123
  · exact B1129127
  · exact B1129131
  · exact B1129135
  · exact B1129139
  · exact B1129143
  · exact B1129147
  · exact B1129151
  · exact B1129155
  · exact B1129159
  · exact B1129163
  · exact B1129167
  · exact B1129171
  · exact B1129175
  · exact B1129179
  · exact B1129183
  · exact B1129187
  · exact B1129191
  · exact B1129195
  · exact B1129199
  · exact B1129203
  · exact B1129207
  · exact B1129211
  · exact B1129215
  · exact B1129219
  · exact B1129223
  · exact B1129227
  · exact B1129231
  · exact B1129235
  · exact B1129239
  · exact B1129243
  · exact B1129247
  · exact B1129251
  · exact B1129255
  · exact B1129259
  · exact B1129263
  · exact B1129267
  · exact B1129271
  · exact B1129275
  · exact B1129279
  · exact B1129283
  · exact B1129287
  · exact B1129291
  · exact B1129295
  · exact B1129299
  · exact B1129303
  · exact B1129307
  · exact B1129311
  · exact B1129315
  · exact B1129319
  · exact B1129323
  · exact B1129327
  · exact B1129331
  · exact B1129335
  · exact B1129339
  · exact B1129343
  · exact B1129347
  · exact B1129351
  · exact B1129355
  · exact B1129359
  · exact B1129363
  · exact B1129367
  · exact B1129371
  · exact B1129375
  · exact B1129379
  · exact B1129383
  · exact B1129387
  · exact B1129391
  · exact B1129395
  · exact B1129399
  · exact B1129403
  · exact B1129407
  · exact B1129411
  · exact B1129415
  · exact B1129419
  · exact B1129423
  · exact B1129427
  · exact B1129431
  · exact B1129435
  · exact B1129439
  · exact B1129443
  · exact B1129447
  · exact B1129451
  · exact B1129455
  · exact B1129459
  · exact B1129463
  · exact B1129467
  · exact B1129471
  · exact B1129475
  · exact B1129479
  · exact B1129483
  · exact B1129487
  · exact B1129491
  · exact B1129495
  · exact B1129499
  · exact B1129503
  · exact B1129507
  · exact B1129511
  · exact B1129515
  · exact B1129519
  · exact B1129523
  · exact B1129527
  · exact B1129531
  · exact B1129535
  · exact B1129539
  · exact B1129543
  · exact B1129547
  · exact B1129551
  · exact B1129555
  · exact B1129559
  · exact B1129563
  · exact B1129567
  · exact B1129571
  · exact B1129575
  · exact B1129579
  · exact B1129583
  · exact B1129587
  · exact B1129591
  · exact B1129595
  · exact B1129599
  · exact B1129603
  · exact B1129607
  · exact B1129611
  · exact B1129615
  · exact B1129619
  · exact B1129623
  · exact B1129627
  · exact B1129631
  · exact B1129635
  · exact B1129639
  · exact B1129643
  · exact B1129647
  · exact B1129651
  · exact B1129655
  · exact B1129659
  · exact B1129663
  · exact B1129667
  · exact B1129671
  · exact B1129675
  · exact B1129679
  · exact B1129683
  · exact B1129687
  · exact B1129691
  · exact B1129695
  · exact B1129699
  · exact B1129703
  · exact B1129707
  · exact B1129711
  · exact B1129715
  · exact B1129719
  · exact B1129723
  · exact B1129727
  · exact B1129731
  · exact B1129735
  · exact B1129739
  · exact B1129743
  · exact B1129747
  · exact B1129751
  · exact B1129755
  · exact B1129759
  · exact B1129763
  · exact B1129767
  · exact B1129771
  · exact B1129775
  · exact B1129779
  · exact B1129783
  · exact B1129787
  · exact B1129791
  · exact B1129795
  · exact B1129799
  · exact B1129803
  · exact B1129807
  · exact B1129811
  · exact B1129815
  · exact B1129819
  · exact B1129823
  · exact B1129827
  · exact B1129831
  · exact B1129835
  · exact B1129839
  · exact B1129843
  · exact B1129847
  · exact B1129851
  · exact B1129855
  · exact B1129859
  · exact B1129863
  · exact B1129867
  · exact B1129871
  · exact B1129875
  · exact B1129879
  · exact B1129883
  · exact B1129887
  · exact B1129891
  · exact B1129895
  · exact B1129899
  · exact B1129903
  · exact B1129907
  · exact B1129911
  · exact B1129915
  · exact B1129919
  · exact B1129923
  · exact B1129927
  · exact B1129931
  · exact B1129935
  · exact B1129939
  · exact B1129943
  · exact B1129947
  · exact B1129951
  · exact B1129955
  · exact B1129959
  · exact B1129963
  · exact B1129967
  · exact B1129971
  · exact B1129975
  · exact B1129979
  · exact B1129983
  · exact B1129987
  · exact B1129991
  · exact B1129995
  · exact B1129999
  · exact B1130003
  · exact B1130007
  · exact B1130011
  · exact B1130015
  · exact B1130019
  · exact B1130023
  · exact B1130027
  · exact B1130031
  · exact B1130035
  · exact B1130039
  · exact B1130043
  · exact B1130047
  · exact B1130051
  · exact B1130055
  · exact B1130059
  · exact B1130063
  · exact B1130067
  · exact B1130071
  · exact B1130075
  · exact B1130079
  · exact B1130083
  · exact B1130087
  · exact B1130091
  · exact B1130095
  · exact B1130099
  · exact B1130103
  · exact B1130107
  · exact B1130111
  · exact B1130115
  · exact B1130119
  · exact B1130123
  · exact B1130127
  · exact B1130131
  · exact B1130135
  · exact B1130139
  · exact B1130143
  · exact B1130147
  · exact B1130151
  · exact B1130155
  · exact B1130159
  · exact B1130163
  · exact B1130167
  · exact B1130171
  · exact B1130175
  · exact B1130179
  · exact B1130183
  · exact B1130187
  · exact B1130191
  · exact B1130195
  · exact B1130199
  · exact B1130203
  · exact B1130207
  · exact B1130211
  · exact B1130215
  · exact B1130219
  · exact B1130223
  · exact B1130227
  · exact B1130231
  · exact B1130235
  · exact B1130239
  · exact B1130243
  · exact B1130247
  · exact B1130251
  · exact B1130255
  · exact B1130259
  · exact B1130263
  · exact B1130267
  · exact B1130271
  · exact B1130275
  · exact B1130279
  · exact B1130283
  · exact B1130287
  · exact B1130291
  · exact B1130295
  · exact B1130299
  · exact B1130303
  · exact B1130307
  · exact B1130311
  · exact B1130315
  · exact B1130319
  · exact B1130323
  · exact B1130327
  · exact B1130331
  · exact B1130335
  · exact B1130339
  · exact B1130343
  · exact B1130347
  · exact B1130351
  · exact B1130355
  · exact B1130359
  · exact B1130363
  · exact B1130367
  · exact B1130371
  · exact B1130375
  · exact B1130379
  · exact B1130383
  · exact B1130387
  · exact B1130391
  · exact B1130395
  · exact B1130399
  · exact B1130403
  · exact B1130407
  · exact B1130411
  · exact B1130415
  · exact B1130419
  · exact B1130423
  · exact B1130427
  · exact B1130431
  · exact B1130435
  · exact B1130439
  · exact B1130443
  · exact B1130447
  · exact B1130451
  · exact B1130455
  · exact B1130459
  · exact B1130463
  · exact B1130467
  · exact B1130471
  · exact B1130475
  · exact B1130479
  · exact B1130483
  · exact B1130487
  · exact B1130491
  · exact B1130495
  · exact B1130499
  · exact B1130503
  · exact B1130507
  · exact B1130511
  · exact B1130515
  · exact B1130519
  · exact B1130523
  · exact B1130527
  · exact B1130531
  · exact B1130535
  · exact B1130539
  · exact B1130543
  · exact B1130547
  · exact B1130551
  · exact B1130555
  · exact B1130559
  · exact B1130563
  · exact B1130567
  · exact B1130571
  · exact B1130575
  · exact B1130579
  · exact B1130583
  · exact B1130587
  · exact B1130591
  · exact B1130595
  · exact B1130599
  · exact B1130603
  · exact B1130607
  · exact B1130611
  · exact B1130615
  · exact B1130619
  · exact B1130623
  · exact B1130627
  · exact B1130631
  · exact B1130635
  · exact B1130639
  · exact B1130643
  · exact B1130647
  · exact B1130651
  · exact B1130655
  · exact B1130659
  · exact B1130663
  · exact B1130667
  · exact B1130671
  · exact B1130675
  · exact B1130679
  · exact B1130683
  · exact B1130687
  · exact B1130691
  · exact B1130695
  · exact B1130699
  · exact B1130703
  · exact B1130707
  · exact B1130711
  · exact B1130715
  · exact B1130719
  · exact B1130723
  · exact B1130727
  · exact B1130731
  · exact B1130735
  · exact B1130739
  · exact B1130743
  · exact B1130747
  · exact B1130751
  · exact B1130755
  · exact B1130759
  · exact B1130763
  · exact B1130767
  · exact B1130771
  · exact B1130775
  · exact B1130779
  · exact B1130783
  · exact B1130787
  · exact B1130791
  · exact B1130795
  · exact B1130799
  · exact B1130803
  · exact B1130807
  · exact B1130811
  · exact B1130815
  · exact B1130819
  · exact B1130823
  · exact B1130827
  · exact B1130831
  · exact B1130835
  · exact B1130839
  · exact B1130843
  · exact B1130847
  · exact B1130851
  · exact B1130855
  · exact B1130859
  · exact B1130863
  · exact B1130867
  · exact B1130871
  · exact B1130875
  · exact B1130879
  · exact B1130883
  · exact B1130887
  · exact B1130891
  · exact B1130895
  · exact B1130899
  · exact B1130903
  · exact B1130907
  · exact B1130911
  · exact B1130915
  · exact B1130919
  · exact B1130923
  · exact B1130927
  · exact B1130931
  · exact B1130935
  · exact B1130939
  · exact B1130943
  · exact B1130947
  · exact B1130951
  · exact B1130955
  · exact B1130959
  · exact B1130963
  · exact B1130967
  · exact B1130971
  · exact B1130975
  · exact B1130979
  · exact B1130983
  · exact B1130987
  · exact B1130991
  · exact B1130995
  · exact B1130999
  · exact B1131003
  · exact B1131007
  · exact B1131011
  · exact B1131015
  · exact B1131019
  · exact B1131023
  · exact B1131027
  · exact B1131031
  · exact B1131035
  · exact B1131039
  · exact B1131043
  · exact B1131047
  · exact B1131051
  · exact B1131055
  · exact B1131059
  · exact B1131063
  · exact B1131067
  · exact B1131071
  · exact B1131075
  · exact B1131079
  · exact B1131083
  · exact B1131087
  · exact B1131091
  · exact B1131095
  · exact B1131099
  · exact B1131103
  · exact B1131107
  · exact B1131111
  · exact B1131115
  · exact B1131119
  · exact B1131123
  · exact B1131127
  · exact B1131131
  · exact B1131135
  · exact B1131139
  · exact B1131143
  · exact B1131147
  · exact B1131151
  · exact B1131155
  · exact B1131159
  · exact B1131163
  · exact B1131167
  · exact B1131171
  · exact B1131175
  · exact B1131179
  · exact B1131183
  · exact B1131187
  · exact B1131191
  · exact B1131195
  · exact B1131199
  · exact B1131203
  · exact B1131207
  · exact B1131211
  · exact B1131215
  · exact B1131219
  · exact B1131223
  · exact B1131227
  · exact B1131231
  · exact B1131235
  · exact B1131239
  · exact B1131243
  · exact B1131247
  · exact B1131251
  · exact B1131255
  · exact B1131259
  · exact B1131263
  · exact B1131267
  · exact B1131271
  · exact B1131275
  · exact B1131279
  · exact B1131283
  · exact B1131287
  · exact B1131291
  · exact B1131295
  · exact B1131299
  · exact B1131303
  · exact B1131307
  · exact B1131311
  · exact B1131315
  · exact B1131319
  · exact B1131323
  · exact B1131327
  · exact B1131331
  · exact B1131335
  · exact B1131339
  · exact B1131343
  · exact B1131347
  · exact B1131351
  · exact B1131355
  · exact B1131359
  · exact B1131363
  · exact B1131367
  · exact B1131371
  · exact B1131375
  · exact B1131379
  · exact B1131383
  · exact B1131387
  · exact B1131391
  · exact B1131395
  · exact B1131399
  · exact B1131403
  · exact B1131407
  · exact B1131411
  · exact B1131415
  · exact B1131419
  · exact B1131423
  · exact B1131427

theorem C1 (j : ℕ) (h1 : 282857 ≤ j) (h2 : j ≤ 283157) : Blo 1128631 (4 * j + 3) := by
  interval_cases j
  · exact B1131431
  · exact B1131435
  · exact B1131439
  · exact B1131443
  · exact B1131447
  · exact B1131451
  · exact B1131455
  · exact B1131459
  · exact B1131463
  · exact B1131467
  · exact B1131471
  · exact B1131475
  · exact B1131479
  · exact B1131483
  · exact B1131487
  · exact B1131491
  · exact B1131495
  · exact B1131499
  · exact B1131503
  · exact B1131507
  · exact B1131511
  · exact B1131515
  · exact B1131519
  · exact B1131523
  · exact B1131527
  · exact B1131531
  · exact B1131535
  · exact B1131539
  · exact B1131543
  · exact B1131547
  · exact B1131551
  · exact B1131555
  · exact B1131559
  · exact B1131563
  · exact B1131567
  · exact B1131571
  · exact B1131575
  · exact B1131579
  · exact B1131583
  · exact B1131587
  · exact B1131591
  · exact B1131595
  · exact B1131599
  · exact B1131603
  · exact B1131607
  · exact B1131611
  · exact B1131615
  · exact B1131619
  · exact B1131623
  · exact B1131627
  · exact B1131631
  · exact B1131635
  · exact B1131639
  · exact B1131643
  · exact B1131647
  · exact B1131651
  · exact B1131655
  · exact B1131659
  · exact B1131663
  · exact B1131667
  · exact B1131671
  · exact B1131675
  · exact B1131679
  · exact B1131683
  · exact B1131687
  · exact B1131691
  · exact B1131695
  · exact B1131699
  · exact B1131703
  · exact B1131707
  · exact B1131711
  · exact B1131715
  · exact B1131719
  · exact B1131723
  · exact B1131727
  · exact B1131731
  · exact B1131735
  · exact B1131739
  · exact B1131743
  · exact B1131747
  · exact B1131751
  · exact B1131755
  · exact B1131759
  · exact B1131763
  · exact B1131767
  · exact B1131771
  · exact B1131775
  · exact B1131779
  · exact B1131783
  · exact B1131787
  · exact B1131791
  · exact B1131795
  · exact B1131799
  · exact B1131803
  · exact B1131807
  · exact B1131811
  · exact B1131815
  · exact B1131819
  · exact B1131823
  · exact B1131827
  · exact B1131831
  · exact B1131835
  · exact B1131839
  · exact B1131843
  · exact B1131847
  · exact B1131851
  · exact B1131855
  · exact B1131859
  · exact B1131863
  · exact B1131867
  · exact B1131871
  · exact B1131875
  · exact B1131879
  · exact B1131883
  · exact B1131887
  · exact B1131891
  · exact B1131895
  · exact B1131899
  · exact B1131903
  · exact B1131907
  · exact B1131911
  · exact B1131915
  · exact B1131919
  · exact B1131923
  · exact B1131927
  · exact B1131931
  · exact B1131935
  · exact B1131939
  · exact B1131943
  · exact B1131947
  · exact B1131951
  · exact B1131955
  · exact B1131959
  · exact B1131963
  · exact B1131967
  · exact B1131971
  · exact B1131975
  · exact B1131979
  · exact B1131983
  · exact B1131987
  · exact B1131991
  · exact B1131995
  · exact B1131999
  · exact B1132003
  · exact B1132007
  · exact B1132011
  · exact B1132015
  · exact B1132019
  · exact B1132023
  · exact B1132027
  · exact B1132031
  · exact B1132035
  · exact B1132039
  · exact B1132043
  · exact B1132047
  · exact B1132051
  · exact B1132055
  · exact B1132059
  · exact B1132063
  · exact B1132067
  · exact B1132071
  · exact B1132075
  · exact B1132079
  · exact B1132083
  · exact B1132087
  · exact B1132091
  · exact B1132095
  · exact B1132099
  · exact B1132103
  · exact B1132107
  · exact B1132111
  · exact B1132115
  · exact B1132119
  · exact B1132123
  · exact B1132127
  · exact B1132131
  · exact B1132135
  · exact B1132139
  · exact B1132143
  · exact B1132147
  · exact B1132151
  · exact B1132155
  · exact B1132159
  · exact B1132163
  · exact B1132167
  · exact B1132171
  · exact B1132175
  · exact B1132179
  · exact B1132183
  · exact B1132187
  · exact B1132191
  · exact B1132195
  · exact B1132199
  · exact B1132203
  · exact B1132207
  · exact B1132211
  · exact B1132215
  · exact B1132219
  · exact B1132223
  · exact B1132227
  · exact B1132231
  · exact B1132235
  · exact B1132239
  · exact B1132243
  · exact B1132247
  · exact B1132251
  · exact B1132255
  · exact B1132259
  · exact B1132263
  · exact B1132267
  · exact B1132271
  · exact B1132275
  · exact B1132279
  · exact B1132283
  · exact B1132287
  · exact B1132291
  · exact B1132295
  · exact B1132299
  · exact B1132303
  · exact B1132307
  · exact B1132311
  · exact B1132315
  · exact B1132319
  · exact B1132323
  · exact B1132327
  · exact B1132331
  · exact B1132335
  · exact B1132339
  · exact B1132343
  · exact B1132347
  · exact B1132351
  · exact B1132355
  · exact B1132359
  · exact B1132363
  · exact B1132367
  · exact B1132371
  · exact B1132375
  · exact B1132379
  · exact B1132383
  · exact B1132387
  · exact B1132391
  · exact B1132395
  · exact B1132399
  · exact B1132403
  · exact B1132407
  · exact B1132411
  · exact B1132415
  · exact B1132419
  · exact B1132423
  · exact B1132427
  · exact B1132431
  · exact B1132435
  · exact B1132439
  · exact B1132443
  · exact B1132447
  · exact B1132451
  · exact B1132455
  · exact B1132459
  · exact B1132463
  · exact B1132467
  · exact B1132471
  · exact B1132475
  · exact B1132479
  · exact B1132483
  · exact B1132487
  · exact B1132491
  · exact B1132495
  · exact B1132499
  · exact B1132503
  · exact B1132507
  · exact B1132511
  · exact B1132515
  · exact B1132519
  · exact B1132523
  · exact B1132527
  · exact B1132531
  · exact B1132535
  · exact B1132539
  · exact B1132543
  · exact B1132547
  · exact B1132551
  · exact B1132555
  · exact B1132559
  · exact B1132563
  · exact B1132567
  · exact B1132571
  · exact B1132575
  · exact B1132579
  · exact B1132583
  · exact B1132587
  · exact B1132591
  · exact B1132595
  · exact B1132599
  · exact B1132603
  · exact B1132607
  · exact B1132611
  · exact B1132615
  · exact B1132619
  · exact B1132623
  · exact B1132627
  · exact B1132631

theorem solution (m : ℕ) (hlo : 1128631 ≤ m) (hhi : m ≤ 1132631) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 282157 ≤ j := by omega
    have hj2 : j ≤ 283157 := by omega
    have hb : Blo 1128631 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 282857 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
