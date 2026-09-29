-- Prove2me | solution 1 for syracuse_descends_range_1605001_1607001
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:11:14.281637+00:00
-- url     : https://prove2.me/submissions/5e791ce7-db4f-4711-a764-cf8cb6d1314a

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


theorem B2408453 : Blo 1605001 2408453 := bbase (se 4 (by rfl) ⟨225792, by rfl⟩ : syracuseStep 2408453 = 451585) (by norm_num)
theorem B3858445 : Blo 1605001 3858445 := bbase (se 3 (by rfl) ⟨723458, by rfl⟩ : syracuseStep 3858445 = 1446917) (by norm_num)
theorem B2031637 : Blo 1605001 2031637 := bbase (se 6 (by rfl) ⟨47616, by rfl⟩ : syracuseStep 2031637 = 95233) (by norm_num)
theorem B2408477 : Blo 1605001 2408477 := bbase (se 3 (by rfl) ⟨451589, by rfl⟩ : syracuseStep 2408477 = 903179) (by norm_num)
theorem B3612725 : Blo 1605001 3612725 := bbase (se 5 (by rfl) ⟨169346, by rfl⟩ : syracuseStep 3612725 = 338693) (by norm_num)
theorem B2408501 : Blo 1605001 2408501 := bbase (se 5 (by rfl) ⟨112898, by rfl⟩ : syracuseStep 2408501 = 225797) (by norm_num)
theorem B2408525 : Blo 1605001 2408525 := bbase (se 3 (by rfl) ⟨451598, by rfl⟩ : syracuseStep 2408525 = 903197) (by norm_num)
theorem B2408549 : Blo 1605001 2408549 := bbase (se 4 (by rfl) ⟨225801, by rfl⟩ : syracuseStep 2408549 = 451603) (by norm_num)
theorem B2031733 : Blo 1605001 2031733 := bbase (se 5 (by rfl) ⟨95237, by rfl⟩ : syracuseStep 2031733 = 190475) (by norm_num)
theorem B3612797 : Blo 1605001 3612797 := bbase (se 3 (by rfl) ⟨677399, by rfl⟩ : syracuseStep 3612797 = 1354799) (by norm_num)
theorem B2408573 : Blo 1605001 2408573 := bbase (se 3 (by rfl) ⟨451607, by rfl⟩ : syracuseStep 2408573 = 903215) (by norm_num)
theorem B2711677 : Blo 1605001 2711677 := bbase (se 3 (by rfl) ⟨508439, by rfl⟩ : syracuseStep 2711677 = 1016879) (by norm_num)
theorem B2441357 : Blo 1605001 2441357 := bbase (se 3 (by rfl) ⟨457754, by rfl⟩ : syracuseStep 2441357 = 915509) (by norm_num)
theorem B2408597 : Blo 1605001 2408597 := bbase (se 6 (by rfl) ⟨56451, by rfl⟩ : syracuseStep 2408597 = 112903) (by norm_num)
theorem B4063405 : Blo 1605001 4063405 := bbase (se 3 (by rfl) ⟨761888, by rfl⟩ : syracuseStep 4063405 = 1523777) (by norm_num)
theorem B2408621 : Blo 1605001 2408621 := bbase (se 3 (by rfl) ⟨451616, by rfl⟩ : syracuseStep 2408621 = 903233) (by norm_num)
theorem B3612869 : Blo 1605001 3612869 := bbase (se 4 (by rfl) ⟨338706, by rfl⟩ : syracuseStep 3612869 = 677413) (by norm_num)
theorem B2408645 : Blo 1605001 2408645 := bbase (se 4 (by rfl) ⟨225810, by rfl⟩ : syracuseStep 2408645 = 451621) (by norm_num)
theorem B2711765 : Blo 1605001 2711765 := bbase (se 7 (by rfl) ⟨31778, by rfl⟩ : syracuseStep 2711765 = 63557) (by norm_num)
theorem B3047645 : Blo 1605001 3047645 := bbase (se 3 (by rfl) ⟨571433, by rfl⟩ : syracuseStep 3047645 = 1142867) (by norm_num)
theorem B2408669 : Blo 1605001 2408669 := bbase (se 3 (by rfl) ⟨451625, by rfl⟩ : syracuseStep 2408669 = 903251) (by norm_num)
theorem B2408693 : Blo 1605001 2408693 := bbase (se 5 (by rfl) ⟨112907, by rfl⟩ : syracuseStep 2408693 = 225815) (by norm_num)
theorem B3612941 : Blo 1605001 3612941 := bbase (se 3 (by rfl) ⟨677426, by rfl⟩ : syracuseStep 3612941 = 1354853) (by norm_num)
theorem B2408717 : Blo 1605001 2408717 := bbase (se 3 (by rfl) ⟨451634, by rfl⟩ : syracuseStep 2408717 = 903269) (by norm_num)
theorem B5423381 : Blo 1605001 5423381 := bbase (se 6 (by rfl) ⟨127110, by rfl⟩ : syracuseStep 5423381 = 254221) (by norm_num)
theorem B4063517 : Blo 1605001 4063517 := bbase (se 3 (by rfl) ⟨761909, by rfl⟩ : syracuseStep 4063517 = 1523819) (by norm_num)
theorem B2572573 : Blo 1605001 2572573 := bbase (se 3 (by rfl) ⟨482357, by rfl⟩ : syracuseStep 2572573 = 964715) (by norm_num)
theorem B2031905 : Blo 1605001 2031905 := bbase (se 2 (by rfl) ⟨761964, by rfl⟩ : syracuseStep 2031905 = 1523929) (by norm_num)
theorem B2408741 : Blo 1605001 2408741 := bbase (se 4 (by rfl) ⟨225819, by rfl⟩ : syracuseStep 2408741 = 451639) (by norm_num)
theorem B2408765 : Blo 1605001 2408765 := bbase (se 3 (by rfl) ⟨451643, by rfl⟩ : syracuseStep 2408765 = 903287) (by norm_num)
theorem B3613013 : Blo 1605001 3613013 := bbase (se 10 (by rfl) ⟨5292, by rfl⟩ : syracuseStep 3613013 = 10585) (by norm_num)
theorem B2408789 : Blo 1605001 2408789 := bbase (se 10 (by rfl) ⟨3528, by rfl⟩ : syracuseStep 2408789 = 7057) (by norm_num)
theorem B2031961 : Blo 1605001 2031961 := bbase (se 2 (by rfl) ⟨761985, by rfl⟩ : syracuseStep 2031961 = 1523971) (by norm_num)
theorem B2408813 : Blo 1605001 2408813 := bbase (se 3 (by rfl) ⟨451652, by rfl⟩ : syracuseStep 2408813 = 903305) (by norm_num)
theorem B3047797 : Blo 1605001 3047797 := bbase (se 5 (by rfl) ⟨142865, by rfl⟩ : syracuseStep 3047797 = 285731) (by norm_num)
theorem B2408837 : Blo 1605001 2408837 := bbase (se 4 (by rfl) ⟨225828, by rfl⟩ : syracuseStep 2408837 = 451657) (by norm_num)
theorem B4882837 : Blo 1605001 4882837 := bbase (se 6 (by rfl) ⟨114441, by rfl⟩ : syracuseStep 4882837 = 228883) (by norm_num)
theorem B3613085 : Blo 1605001 3613085 := bbase (se 3 (by rfl) ⟨677453, by rfl⟩ : syracuseStep 3613085 = 1354907) (by norm_num)
theorem B2408861 : Blo 1605001 2408861 := bbase (se 3 (by rfl) ⟨451661, by rfl⟩ : syracuseStep 2408861 = 903323) (by norm_num)
theorem B1761713 : Blo 1605001 1761713 := bbase (se 2 (by rfl) ⟨660642, by rfl⟩ : syracuseStep 1761713 = 1321285) (by norm_num)
theorem B2408885 : Blo 1605001 2408885 := bbase (se 5 (by rfl) ⟨112916, by rfl⟩ : syracuseStep 2408885 = 225833) (by norm_num)
theorem B2032057 : Blo 1605001 2032057 := bbase (se 2 (by rfl) ⟨762021, by rfl⟩ : syracuseStep 2032057 = 1524043) (by norm_num)
theorem B2408909 : Blo 1605001 2408909 := bbase (se 3 (by rfl) ⟨451670, by rfl⟩ : syracuseStep 2408909 = 903341) (by norm_num)
theorem B4063709 : Blo 1605001 4063709 := bbase (se 3 (by rfl) ⟨761945, by rfl⟩ : syracuseStep 4063709 = 1523891) (by norm_num)
theorem B3613157 : Blo 1605001 3613157 := bbase (se 4 (by rfl) ⟨338733, by rfl⟩ : syracuseStep 3613157 = 677467) (by norm_num)
theorem B2408933 : Blo 1605001 2408933 := bbase (se 4 (by rfl) ⟨225837, by rfl⟩ : syracuseStep 2408933 = 451675) (by norm_num)
theorem B4882933 : Blo 1605001 4882933 := bbase (se 5 (by rfl) ⟨228887, by rfl⟩ : syracuseStep 4882933 = 457775) (by norm_num)
theorem B2408957 : Blo 1605001 2408957 := bbase (se 3 (by rfl) ⟨451679, by rfl⟩ : syracuseStep 2408957 = 903359) (by norm_num)
theorem B33399317 : Blo 1605001 33399317 := bbase (se 6 (by rfl) ⟨782796, by rfl⟩ : syracuseStep 33399317 = 1565593) (by norm_num)
theorem B6857237 : Blo 1605001 6857237 := bbase (se 6 (by rfl) ⟨160716, by rfl⟩ : syracuseStep 6857237 = 321433) (by norm_num)
theorem B2408981 : Blo 1605001 2408981 := bbase (se 6 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 2408981 = 112921) (by norm_num)
theorem B3613229 : Blo 1605001 3613229 := bbase (se 3 (by rfl) ⟨677480, by rfl⟩ : syracuseStep 3613229 = 1354961) (by norm_num)
theorem B2409005 : Blo 1605001 2409005 := bbase (se 3 (by rfl) ⟨451688, by rfl⟩ : syracuseStep 2409005 = 903377) (by norm_num)
theorem B2409029 : Blo 1605001 2409029 := bbase (se 4 (by rfl) ⟨225846, by rfl⟩ : syracuseStep 2409029 = 451693) (by norm_num)
theorem B5145157 : Blo 1605001 5145157 := bbase (se 4 (by rfl) ⟨482358, by rfl⟩ : syracuseStep 5145157 = 964717) (by norm_num)
theorem B2409053 : Blo 1605001 2409053 := bbase (se 3 (by rfl) ⟨451697, by rfl⟩ : syracuseStep 2409053 = 903395) (by norm_num)
theorem B2032229 : Blo 1605001 2032229 := bbase (se 4 (by rfl) ⟨190521, by rfl⟩ : syracuseStep 2032229 = 381043) (by norm_num)
theorem B4571765 : Blo 1605001 4571765 := bbase (se 5 (by rfl) ⟨214301, by rfl⟩ : syracuseStep 4571765 = 428603) (by norm_num)
theorem B3613301 : Blo 1605001 3613301 := bbase (se 5 (by rfl) ⟨169373, by rfl⟩ : syracuseStep 3613301 = 338747) (by norm_num)
theorem B2409077 : Blo 1605001 2409077 := bbase (se 5 (by rfl) ⟨112925, by rfl⟩ : syracuseStep 2409077 = 225851) (by norm_num)
theorem B2409101 : Blo 1605001 2409101 := bbase (se 3 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 2409101 = 903413) (by norm_num)
theorem B2032285 : Blo 1605001 2032285 := bbase (se 3 (by rfl) ⟨381053, by rfl⟩ : syracuseStep 2032285 = 762107) (by norm_num)
theorem B2507429 : Blo 1605001 2507429 := bbase (se 4 (by rfl) ⟨235071, by rfl⟩ : syracuseStep 2507429 = 470143) (by norm_num)
theorem B3048101 : Blo 1605001 3048101 := bbase (se 4 (by rfl) ⟨285759, by rfl⟩ : syracuseStep 3048101 = 571519) (by norm_num)
theorem B2409125 : Blo 1605001 2409125 := bbase (se 4 (by rfl) ⟨225855, by rfl⟩ : syracuseStep 2409125 = 451711) (by norm_num)
theorem B3613373 : Blo 1605001 3613373 := bbase (se 3 (by rfl) ⟨677507, by rfl⟩ : syracuseStep 3613373 = 1355015) (by norm_num)
theorem B2409149 : Blo 1605001 2409149 := bbase (se 3 (by rfl) ⟨451715, by rfl⟩ : syracuseStep 2409149 = 903431) (by norm_num)
theorem B7422661 : Blo 1605001 7422661 := bbase (se 4 (by rfl) ⟨695874, by rfl⟩ : syracuseStep 7422661 = 1391749) (by norm_num)
theorem B2409173 : Blo 1605001 2409173 := bbase (se 7 (by rfl) ⟨28232, by rfl⟩ : syracuseStep 2409173 = 56465) (by norm_num)
theorem B2409197 : Blo 1605001 2409197 := bbase (se 3 (by rfl) ⟨451724, by rfl⟩ : syracuseStep 2409197 = 903449) (by norm_num)
theorem B2032381 : Blo 1605001 2032381 := bbase (se 3 (by rfl) ⟨381071, by rfl⟩ : syracuseStep 2032381 = 762143) (by norm_num)
theorem B3613445 : Blo 1605001 3613445 := bbase (se 4 (by rfl) ⟨338760, by rfl⟩ : syracuseStep 3613445 = 677521) (by norm_num)
theorem B2441989 : Blo 1605001 2441989 := bbase (se 4 (by rfl) ⟨228936, by rfl⟩ : syracuseStep 2441989 = 457873) (by norm_num)
theorem B2409221 : Blo 1605001 2409221 := bbase (se 4 (by rfl) ⟨225864, by rfl⟩ : syracuseStep 2409221 = 451729) (by norm_num)
theorem B18293525 : Blo 1605001 18293525 := bbase (se 6 (by rfl) ⟨428754, by rfl⟩ : syracuseStep 18293525 = 857509) (by norm_num)
theorem B2409245 : Blo 1605001 2409245 := bbase (se 3 (by rfl) ⟨451733, by rfl⟩ : syracuseStep 2409245 = 903467) (by norm_num)
theorem B4064053 : Blo 1605001 4064053 := bbase (se 5 (by rfl) ⟨190502, by rfl⟩ : syracuseStep 4064053 = 381005) (by norm_num)
theorem B15434549 : Blo 1605001 15434549 := bbase (se 5 (by rfl) ⟨723494, by rfl⟩ : syracuseStep 15434549 = 1446989) (by norm_num)
theorem B2409269 : Blo 1605001 2409269 := bbase (se 5 (by rfl) ⟨112934, by rfl⟩ : syracuseStep 2409269 = 225869) (by norm_num)
theorem B3613517 : Blo 1605001 3613517 := bbase (se 3 (by rfl) ⟨677534, by rfl⟩ : syracuseStep 3613517 = 1355069) (by norm_num)
theorem B2409293 : Blo 1605001 2409293 := bbase (se 3 (by rfl) ⟨451742, by rfl⟩ : syracuseStep 2409293 = 903485) (by norm_num)
theorem B2409317 : Blo 1605001 2409317 := bbase (se 4 (by rfl) ⟨225873, by rfl⟩ : syracuseStep 2409317 = 451747) (by norm_num)
theorem B2409341 : Blo 1605001 2409341 := bbase (se 3 (by rfl) ⟨451751, by rfl⟩ : syracuseStep 2409341 = 903503) (by norm_num)
theorem B3613589 : Blo 1605001 3613589 := bbase (se 6 (by rfl) ⟨84693, by rfl⟩ : syracuseStep 3613589 = 169387) (by norm_num)
theorem B2409365 : Blo 1605001 2409365 := bbase (se 6 (by rfl) ⟨56469, by rfl⟩ : syracuseStep 2409365 = 112939) (by norm_num)
theorem B4064165 : Blo 1605001 4064165 := bbase (se 4 (by rfl) ⟨381015, by rfl⟩ : syracuseStep 4064165 = 762031) (by norm_num)
theorem B2032553 : Blo 1605001 2032553 := bbase (se 2 (by rfl) ⟨762207, by rfl⟩ : syracuseStep 2032553 = 1524415) (by norm_num)
theorem B2409389 : Blo 1605001 2409389 := bbase (se 3 (by rfl) ⟨451760, by rfl⟩ : syracuseStep 2409389 = 903521) (by norm_num)
theorem B2573245 : Blo 1605001 2573245 := bbase (se 3 (by rfl) ⟨482483, by rfl⟩ : syracuseStep 2573245 = 964967) (by norm_num)
theorem B2409413 : Blo 1605001 2409413 := bbase (se 4 (by rfl) ⟨225882, by rfl⟩ : syracuseStep 2409413 = 451765) (by norm_num)
theorem B3613661 : Blo 1605001 3613661 := bbase (se 3 (by rfl) ⟨677561, by rfl⟩ : syracuseStep 3613661 = 1355123) (by norm_num)
theorem B2409437 : Blo 1605001 2409437 := bbase (se 3 (by rfl) ⟨451769, by rfl⟩ : syracuseStep 2409437 = 903539) (by norm_num)
theorem B2032609 : Blo 1605001 2032609 := bbase (se 2 (by rfl) ⟨762228, by rfl⟩ : syracuseStep 2032609 = 1524457) (by norm_num)
theorem B2409461 : Blo 1605001 2409461 := bbase (se 5 (by rfl) ⟨112943, by rfl⟩ : syracuseStep 2409461 = 225887) (by norm_num)
theorem B2409485 : Blo 1605001 2409485 := bbase (se 3 (by rfl) ⟨451778, by rfl⟩ : syracuseStep 2409485 = 903557) (by norm_num)
theorem B4572197 : Blo 1605001 4572197 := bbase (se 4 (by rfl) ⟨428643, by rfl⟩ : syracuseStep 4572197 = 857287) (by norm_num)
theorem B3613733 : Blo 1605001 3613733 := bbase (se 4 (by rfl) ⟨338787, by rfl⟩ : syracuseStep 3613733 = 677575) (by norm_num)
theorem B2409509 : Blo 1605001 2409509 := bbase (se 4 (by rfl) ⟨225891, by rfl⟩ : syracuseStep 2409509 = 451783) (by norm_num)
theorem B2409533 : Blo 1605001 2409533 := bbase (se 3 (by rfl) ⟨451787, by rfl⟩ : syracuseStep 2409533 = 903575) (by norm_num)
theorem B2032705 : Blo 1605001 2032705 := bbase (se 2 (by rfl) ⟨762264, by rfl⟩ : syracuseStep 2032705 = 1524529) (by norm_num)
theorem B2409557 : Blo 1605001 2409557 := bbase (se 8 (by rfl) ⟨14118, by rfl⟩ : syracuseStep 2409557 = 28237) (by norm_num)
theorem B4064357 : Blo 1605001 4064357 := bbase (se 4 (by rfl) ⟨381033, by rfl⟩ : syracuseStep 4064357 = 762067) (by norm_num)
theorem B3613805 : Blo 1605001 3613805 := bbase (se 3 (by rfl) ⟨677588, by rfl⟩ : syracuseStep 3613805 = 1355177) (by norm_num)
theorem B2409581 : Blo 1605001 2409581 := bbase (se 3 (by rfl) ⟨451796, by rfl⟩ : syracuseStep 2409581 = 903593) (by norm_num)
theorem B6096005 : Blo 1605001 6096005 := bbase (se 4 (by rfl) ⟨571500, by rfl⟩ : syracuseStep 6096005 = 1143001) (by norm_num)
theorem B2409605 : Blo 1605001 2409605 := bbase (se 4 (by rfl) ⟨225900, by rfl⟩ : syracuseStep 2409605 = 451801) (by norm_num)
theorem B2409629 : Blo 1605001 2409629 := bbase (se 3 (by rfl) ⟨451805, by rfl⟩ : syracuseStep 2409629 = 903611) (by norm_num)
theorem B3613877 : Blo 1605001 3613877 := bbase (se 5 (by rfl) ⟨169400, by rfl⟩ : syracuseStep 3613877 = 338801) (by norm_num)
theorem B2409653 : Blo 1605001 2409653 := bbase (se 5 (by rfl) ⟨112952, by rfl⟩ : syracuseStep 2409653 = 225905) (by norm_num)
theorem B2409677 : Blo 1605001 2409677 := bbase (se 3 (by rfl) ⟨451814, by rfl⟩ : syracuseStep 2409677 = 903629) (by norm_num)
theorem B8127701 : Blo 1605001 8127701 := bbase (se 7 (by rfl) ⟨95246, by rfl⟩ : syracuseStep 8127701 = 190493) (by norm_num)
theorem B2286805 : Blo 1605001 2286805 := bbase (se 7 (by rfl) ⟨26798, by rfl⟩ : syracuseStep 2286805 = 53597) (by norm_num)
theorem B2409701 : Blo 1605001 2409701 := bbase (se 4 (by rfl) ⟨225909, by rfl⟩ : syracuseStep 2409701 = 451819) (by norm_num)
theorem B2032877 : Blo 1605001 2032877 := bbase (se 3 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 2032877 = 762329) (by norm_num)
theorem B3613949 : Blo 1605001 3613949 := bbase (se 3 (by rfl) ⟨677615, by rfl⟩ : syracuseStep 3613949 = 1355231) (by norm_num)
theorem B2409725 : Blo 1605001 2409725 := bbase (se 3 (by rfl) ⟨451823, by rfl⟩ : syracuseStep 2409725 = 903647) (by norm_num)
theorem B2409749 : Blo 1605001 2409749 := bbase (se 6 (by rfl) ⟨56478, by rfl⟩ : syracuseStep 2409749 = 112957) (by norm_num)
theorem B2032933 : Blo 1605001 2032933 := bbase (se 4 (by rfl) ⟨190587, by rfl⟩ : syracuseStep 2032933 = 381175) (by norm_num)
theorem B2409773 : Blo 1605001 2409773 := bbase (se 3 (by rfl) ⟨451832, by rfl⟩ : syracuseStep 2409773 = 903665) (by norm_num)
theorem B3614021 : Blo 1605001 3614021 := bbase (se 4 (by rfl) ⟨338814, by rfl⟩ : syracuseStep 3614021 = 677629) (by norm_num)
theorem B2409797 : Blo 1605001 2409797 := bbase (se 4 (by rfl) ⟨225918, by rfl⟩ : syracuseStep 2409797 = 451837) (by norm_num)
theorem B2409821 : Blo 1605001 2409821 := bbase (se 3 (by rfl) ⟨451841, by rfl⟩ : syracuseStep 2409821 = 903683) (by norm_num)
theorem B2573669 : Blo 1605001 2573669 := bbase (se 4 (by rfl) ⟨241281, by rfl⟩ : syracuseStep 2573669 = 482563) (by norm_num)
theorem B2409845 : Blo 1605001 2409845 := bbase (se 5 (by rfl) ⟨112961, by rfl⟩ : syracuseStep 2409845 = 225923) (by norm_num)
theorem B2033029 : Blo 1605001 2033029 := bbase (se 4 (by rfl) ⟨190596, by rfl⟩ : syracuseStep 2033029 = 381193) (by norm_num)
theorem B3614093 : Blo 1605001 3614093 := bbase (se 3 (by rfl) ⟨677642, by rfl⟩ : syracuseStep 3614093 = 1355285) (by norm_num)
theorem B2409869 : Blo 1605001 2409869 := bbase (se 3 (by rfl) ⟨451850, by rfl⟩ : syracuseStep 2409869 = 903701) (by norm_num)
theorem B3048853 : Blo 1605001 3048853 := bbase (se 6 (by rfl) ⟨71457, by rfl⟩ : syracuseStep 3048853 = 142915) (by norm_num)
theorem B6096293 : Blo 1605001 6096293 := bbase (se 4 (by rfl) ⟨571527, by rfl⟩ : syracuseStep 6096293 = 1143055) (by norm_num)
theorem B2409893 : Blo 1605001 2409893 := bbase (se 4 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 2409893 = 451855) (by norm_num)
theorem B2893229 : Blo 1605001 2893229 := bbase (se 3 (by rfl) ⟨542480, by rfl⟩ : syracuseStep 2893229 = 1084961) (by norm_num)
theorem B4064701 : Blo 1605001 4064701 := bbase (se 3 (by rfl) ⟨762131, by rfl⟩ : syracuseStep 4064701 = 1524263) (by norm_num)
theorem B3712445 : Blo 1605001 3712445 := bbase (se 3 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 3712445 = 1392167) (by norm_num)
theorem B2409917 : Blo 1605001 2409917 := bbase (se 3 (by rfl) ⟨451859, by rfl⟩ : syracuseStep 2409917 = 903719) (by norm_num)
theorem B3614165 : Blo 1605001 3614165 := bbase (se 7 (by rfl) ⟨42353, by rfl⟩ : syracuseStep 3614165 = 84707) (by norm_num)
theorem B2409941 : Blo 1605001 2409941 := bbase (se 7 (by rfl) ⟨28241, by rfl⟩ : syracuseStep 2409941 = 56483) (by norm_num)
theorem B2409965 : Blo 1605001 2409965 := bbase (se 3 (by rfl) ⟨451868, by rfl⟩ : syracuseStep 2409965 = 903737) (by norm_num)
theorem B2409989 : Blo 1605001 2409989 := bbase (se 4 (by rfl) ⟨225936, by rfl⟩ : syracuseStep 2409989 = 451873) (by norm_num)
theorem B3614237 : Blo 1605001 3614237 := bbase (se 3 (by rfl) ⟨677669, by rfl⟩ : syracuseStep 3614237 = 1355339) (by norm_num)
theorem B2410013 : Blo 1605001 2410013 := bbase (se 3 (by rfl) ⟨451877, by rfl⟩ : syracuseStep 2410013 = 903755) (by norm_num)
theorem B3048997 : Blo 1605001 3048997 := bbase (se 4 (by rfl) ⟨285843, by rfl⟩ : syracuseStep 3048997 = 571687) (by norm_num)
theorem B4064813 : Blo 1605001 4064813 := bbase (se 3 (by rfl) ⟨762152, by rfl⟩ : syracuseStep 4064813 = 1524305) (by norm_num)
theorem B2033201 : Blo 1605001 2033201 := bbase (se 2 (by rfl) ⟨762450, by rfl⟩ : syracuseStep 2033201 = 1524901) (by norm_num)
theorem B3860021 : Blo 1605001 3860021 := bbase (se 5 (by rfl) ⟨180938, by rfl⟩ : syracuseStep 3860021 = 361877) (by norm_num)
theorem B2410037 : Blo 1605001 2410037 := bbase (se 5 (by rfl) ⟨112970, by rfl⟩ : syracuseStep 2410037 = 225941) (by norm_num)
theorem B2410061 : Blo 1605001 2410061 := bbase (se 3 (by rfl) ⟨451886, by rfl⟩ : syracuseStep 2410061 = 903773) (by norm_num)
theorem B3614309 : Blo 1605001 3614309 := bbase (se 4 (by rfl) ⟨338841, by rfl⟩ : syracuseStep 3614309 = 677683) (by norm_num)
theorem B2410085 : Blo 1605001 2410085 := bbase (se 4 (by rfl) ⟨225945, by rfl⟩ : syracuseStep 2410085 = 451891) (by norm_num)
theorem B2033257 : Blo 1605001 2033257 := bbase (se 2 (by rfl) ⟨762471, by rfl⟩ : syracuseStep 2033257 = 1524943) (by norm_num)
theorem B2410109 : Blo 1605001 2410109 := bbase (se 3 (by rfl) ⟨451895, by rfl⟩ : syracuseStep 2410109 = 903791) (by norm_num)
theorem B2573957 : Blo 1605001 2573957 := bbase (se 4 (by rfl) ⟨241308, by rfl⟩ : syracuseStep 2573957 = 482617) (by norm_num)
theorem B14845589 : Blo 1605001 14845589 := bbase (se 6 (by rfl) ⟨347943, by rfl⟩ : syracuseStep 14845589 = 695887) (by norm_num)
theorem B2410133 : Blo 1605001 2410133 := bbase (se 6 (by rfl) ⟨56487, by rfl⟩ : syracuseStep 2410133 = 112975) (by norm_num)
theorem B3614381 : Blo 1605001 3614381 := bbase (se 3 (by rfl) ⟨677696, by rfl⟩ : syracuseStep 3614381 = 1355393) (by norm_num)
theorem B2410157 : Blo 1605001 2410157 := bbase (se 3 (by rfl) ⟨451904, by rfl⟩ : syracuseStep 2410157 = 903809) (by norm_num)
theorem B3049157 : Blo 1605001 3049157 := bbase (se 4 (by rfl) ⟨285858, by rfl⟩ : syracuseStep 3049157 = 571717) (by norm_num)
theorem B2410181 : Blo 1605001 2410181 := bbase (se 4 (by rfl) ⟨225954, by rfl⟩ : syracuseStep 2410181 = 451909) (by norm_num)
theorem B2033353 : Blo 1605001 2033353 := bbase (se 2 (by rfl) ⟨762507, by rfl⟩ : syracuseStep 2033353 = 1525015) (by norm_num)
theorem B2410205 : Blo 1605001 2410205 := bbase (se 3 (by rfl) ⟨451913, by rfl⟩ : syracuseStep 2410205 = 903827) (by norm_num)
theorem B4065005 : Blo 1605001 4065005 := bbase (se 3 (by rfl) ⟨762188, by rfl⟩ : syracuseStep 4065005 = 1524377) (by norm_num)
theorem B3614453 : Blo 1605001 3614453 := bbase (se 5 (by rfl) ⟨169427, by rfl⟩ : syracuseStep 3614453 = 338855) (by norm_num)
theorem B2410229 : Blo 1605001 2410229 := bbase (se 5 (by rfl) ⟨112979, by rfl⟩ : syracuseStep 2410229 = 225959) (by norm_num)
theorem B2410253 : Blo 1605001 2410253 := bbase (se 3 (by rfl) ⟨451922, by rfl⟩ : syracuseStep 2410253 = 903845) (by norm_num)
theorem B4572949 : Blo 1605001 4572949 := bbase (se 6 (by rfl) ⟨107178, by rfl⟩ : syracuseStep 4572949 = 214357) (by norm_num)
theorem B2287397 : Blo 1605001 2287397 := bbase (se 4 (by rfl) ⟨214443, by rfl⟩ : syracuseStep 2287397 = 428887) (by norm_num)
theorem B2410277 : Blo 1605001 2410277 := bbase (se 4 (by rfl) ⟨225963, by rfl⟩ : syracuseStep 2410277 = 451927) (by norm_num)
theorem B3663677 : Blo 1605001 3663677 := bbase (se 3 (by rfl) ⟨686939, by rfl⟩ : syracuseStep 3663677 = 1373879) (by norm_num)
theorem B3614525 : Blo 1605001 3614525 := bbase (se 3 (by rfl) ⟨677723, by rfl⟩ : syracuseStep 3614525 = 1355447) (by norm_num)
theorem B2410301 : Blo 1605001 2410301 := bbase (se 3 (by rfl) ⟨451931, by rfl⟩ : syracuseStep 2410301 = 903863) (by norm_num)
theorem B3049301 : Blo 1605001 3049301 := bbase (se 9 (by rfl) ⟨8933, by rfl⟩ : syracuseStep 3049301 = 17867) (by norm_num)
theorem B87934805 : Blo 1605001 87934805 := bbase (se 9 (by rfl) ⟨257621, by rfl⟩ : syracuseStep 87934805 = 515243) (by norm_num)
theorem B2410325 : Blo 1605001 2410325 := bbase (se 9 (by rfl) ⟨7061, by rfl⟩ : syracuseStep 2410325 = 14123) (by norm_num)
theorem B2410349 : Blo 1605001 2410349 := bbase (se 3 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 2410349 = 903881) (by norm_num)
theorem B2287477 : Blo 1605001 2287477 := bbase (se 5 (by rfl) ⟨107225, by rfl⟩ : syracuseStep 2287477 = 214451) (by norm_num)
theorem B2033525 : Blo 1605001 2033525 := bbase (se 5 (by rfl) ⟨95321, by rfl⟩ : syracuseStep 2033525 = 190643) (by norm_num)
theorem B3614597 : Blo 1605001 3614597 := bbase (se 4 (by rfl) ⟨338868, by rfl⟩ : syracuseStep 3614597 = 677737) (by norm_num)
theorem B2410373 : Blo 1605001 2410373 := bbase (se 4 (by rfl) ⟨225972, by rfl⟩ : syracuseStep 2410373 = 451945) (by norm_num)
theorem B5146517 : Blo 1605001 5146517 := bbase (se 6 (by rfl) ⟨120621, by rfl⟩ : syracuseStep 5146517 = 241243) (by norm_num)
theorem B2410397 : Blo 1605001 2410397 := bbase (se 3 (by rfl) ⟨451949, by rfl⟩ : syracuseStep 2410397 = 903899) (by norm_num)
theorem B2033581 : Blo 1605001 2033581 := bbase (se 3 (by rfl) ⟨381296, by rfl⟩ : syracuseStep 2033581 = 762593) (by norm_num)
theorem B2410421 : Blo 1605001 2410421 := bbase (se 5 (by rfl) ⟨112988, by rfl⟩ : syracuseStep 2410421 = 225977) (by norm_num)
theorem B5416901 : Blo 1605001 5416901 := bbase (se 4 (by rfl) ⟨507834, by rfl⟩ : syracuseStep 5416901 = 1015669) (by norm_num)
theorem B3614669 : Blo 1605001 3614669 := bbase (se 3 (by rfl) ⟨677750, by rfl⟩ : syracuseStep 3614669 = 1355501) (by norm_num)
theorem B2410445 : Blo 1605001 2410445 := bbase (se 3 (by rfl) ⟨451958, by rfl⟩ : syracuseStep 2410445 = 903917) (by norm_num)
theorem B2934749 : Blo 1605001 2934749 := bbase (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) (by norm_num)
theorem B2410469 : Blo 1605001 2410469 := bbase (se 4 (by rfl) ⟨225981, by rfl⟩ : syracuseStep 2410469 = 451963) (by norm_num)
theorem B2287597 : Blo 1605001 2287597 := bbase (se 3 (by rfl) ⟨428924, by rfl⟩ : syracuseStep 2287597 = 857849) (by norm_num)
theorem B2410493 : Blo 1605001 2410493 := bbase (se 3 (by rfl) ⟨451967, by rfl⟩ : syracuseStep 2410493 = 903935) (by norm_num)
theorem B1714181 : Blo 1605001 1714181 := bbase (se 4 (by rfl) ⟨160704, by rfl⟩ : syracuseStep 1714181 = 321409) (by norm_num)
theorem B2033677 : Blo 1605001 2033677 := bbase (se 3 (by rfl) ⟨381314, by rfl⟩ : syracuseStep 2033677 = 762629) (by norm_num)
theorem B3614741 : Blo 1605001 3614741 := bbase (se 6 (by rfl) ⟨84720, by rfl⟩ : syracuseStep 3614741 = 169441) (by norm_num)
theorem B1714241 : Blo 1605001 1714241 := bbase (se 2 (by rfl) ⟨642840, by rfl⟩ : syracuseStep 1714241 = 1285681) (by norm_num)
theorem B4065349 : Blo 1605001 4065349 := bbase (se 4 (by rfl) ⟨381126, by rfl⟩ : syracuseStep 4065349 = 762253) (by norm_num)
theorem B2746445 : Blo 1605001 2746445 := bbase (se 3 (by rfl) ⟨514958, by rfl⟩ : syracuseStep 2746445 = 1029917) (by norm_num)
theorem B2287693 : Blo 1605001 2287693 := bbase (se 3 (by rfl) ⟨428942, by rfl⟩ : syracuseStep 2287693 = 857885) (by norm_num)
theorem B3254357 : Blo 1605001 3254357 := bbase (se 8 (by rfl) ⟨19068, by rfl⟩ : syracuseStep 3254357 = 38137) (by norm_num)
theorem B3614813 : Blo 1605001 3614813 := bbase (se 3 (by rfl) ⟨677777, by rfl⟩ : syracuseStep 3614813 = 1355555) (by norm_num)
theorem B3049589 : Blo 1605001 3049589 := bbase (se 5 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 3049589 = 285899) (by norm_num)
theorem B3614885 : Blo 1605001 3614885 := bbase (se 4 (by rfl) ⟨338895, by rfl⟩ : syracuseStep 3614885 = 677791) (by norm_num)
theorem B4065461 : Blo 1605001 4065461 := bbase (se 5 (by rfl) ⟨190568, by rfl⟩ : syracuseStep 4065461 = 381137) (by norm_num)
theorem B2033849 : Blo 1605001 2033849 := bbase (se 2 (by rfl) ⟨762693, by rfl⟩ : syracuseStep 2033849 = 1525387) (by norm_num)
theorem B3254461 : Blo 1605001 3254461 := bbase (se 3 (by rfl) ⟨610211, by rfl⟩ : syracuseStep 3254461 = 1220423) (by norm_num)
theorem B1714369 : Blo 1605001 1714369 := bbase (se 2 (by rfl) ⟨642888, by rfl⟩ : syracuseStep 1714369 = 1285777) (by norm_num)
theorem B4950245 : Blo 1605001 4950245 := bbase (se 4 (by rfl) ⟨464085, by rfl⟩ : syracuseStep 4950245 = 928171) (by norm_num)
theorem B3614957 : Blo 1605001 3614957 := bbase (se 3 (by rfl) ⟨677804, by rfl⟩ : syracuseStep 3614957 = 1355609) (by norm_num)
theorem B3049741 : Blo 1605001 3049741 := bbase (se 3 (by rfl) ⟨571826, by rfl⟩ : syracuseStep 3049741 = 1143653) (by norm_num)
theorem B3615029 : Blo 1605001 3615029 := bbase (se 5 (by rfl) ⟨169454, by rfl⟩ : syracuseStep 3615029 = 338909) (by norm_num)
theorem B5417333 : Blo 1605001 5417333 := bbase (se 5 (by rfl) ⟨253937, by rfl⟩ : syracuseStep 5417333 = 507875) (by norm_num)
theorem B4065653 : Blo 1605001 4065653 := bbase (se 5 (by rfl) ⟨190577, by rfl⟩ : syracuseStep 4065653 = 381155) (by norm_num)
theorem B3615101 : Blo 1605001 3615101 := bbase (se 3 (by rfl) ⟨677831, by rfl⟩ : syracuseStep 3615101 = 1355663) (by norm_num)
theorem B3615173 : Blo 1605001 3615173 := bbase (se 4 (by rfl) ⟨338922, by rfl⟩ : syracuseStep 3615173 = 677845) (by norm_num)
theorem B8128997 : Blo 1605001 8128997 := bbase (se 4 (by rfl) ⟨762093, by rfl⟩ : syracuseStep 8128997 = 1524187) (by norm_num)
theorem B3615245 : Blo 1605001 3615245 := bbase (se 3 (by rfl) ⟨677858, by rfl⟩ : syracuseStep 3615245 = 1355717) (by norm_num)
theorem B3050045 : Blo 1605001 3050045 := bbase (se 3 (by rfl) ⟨571883, by rfl⟩ : syracuseStep 3050045 = 1143767) (by norm_num)
theorem B6097477 : Blo 1605001 6097477 := bbase (se 4 (by rfl) ⟨571638, by rfl⟩ : syracuseStep 6097477 = 1143277) (by norm_num)
theorem B3615317 : Blo 1605001 3615317 := bbase (se 8 (by rfl) ⟨21183, by rfl⟩ : syracuseStep 3615317 = 42367) (by norm_num)
theorem B1714813 : Blo 1605001 1714813 := bbase (se 3 (by rfl) ⟨321527, by rfl⟩ : syracuseStep 1714813 = 643055) (by norm_num)
theorem B3615389 : Blo 1605001 3615389 := bbase (se 3 (by rfl) ⟨677885, by rfl⟩ : syracuseStep 3615389 = 1355771) (by norm_num)
theorem B4065997 : Blo 1605001 4065997 := bbase (se 3 (by rfl) ⟨762374, by rfl⟩ : syracuseStep 4065997 = 1524749) (by norm_num)
theorem B3615461 : Blo 1605001 3615461 := bbase (se 4 (by rfl) ⟨338949, by rfl⟩ : syracuseStep 3615461 = 677899) (by norm_num)
theorem B1714933 : Blo 1605001 1714933 := bbase (se 5 (by rfl) ⟨80387, by rfl⟩ : syracuseStep 1714933 = 160775) (by norm_num)
theorem B5417765 : Blo 1605001 5417765 := bbase (se 4 (by rfl) ⟨507915, by rfl⟩ : syracuseStep 5417765 = 1015831) (by norm_num)
theorem B3615533 : Blo 1605001 3615533 := bbase (se 3 (by rfl) ⟨677912, by rfl⟩ : syracuseStep 3615533 = 1355825) (by norm_num)
theorem B4066109 : Blo 1605001 4066109 := bbase (se 3 (by rfl) ⟨762395, by rfl⟩ : syracuseStep 4066109 = 1524791) (by norm_num)
theorem B6097781 : Blo 1605001 6097781 := bbase (se 5 (by rfl) ⟨285833, by rfl⟩ : syracuseStep 6097781 = 571667) (by norm_num)
theorem B3615605 : Blo 1605001 3615605 := bbase (se 5 (by rfl) ⟨169481, by rfl⟩ : syracuseStep 3615605 = 338963) (by norm_num)
theorem B3615677 : Blo 1605001 3615677 := bbase (se 3 (by rfl) ⟨677939, by rfl⟩ : syracuseStep 3615677 = 1355879) (by norm_num)
theorem B1715185 : Blo 1605001 1715185 := bbase (se 2 (by rfl) ⟨643194, by rfl⟩ : syracuseStep 1715185 = 1286389) (by norm_num)
theorem B1715189 : Blo 1605001 1715189 := bbase (se 5 (by rfl) ⟨80399, by rfl⟩ : syracuseStep 1715189 = 160799) (by norm_num)
theorem B4066301 : Blo 1605001 4066301 := bbase (se 3 (by rfl) ⟨762431, by rfl⟩ : syracuseStep 4066301 = 1524863) (by norm_num)
theorem B3615749 : Blo 1605001 3615749 := bbase (se 4 (by rfl) ⟨338976, by rfl⟩ : syracuseStep 3615749 = 677953) (by norm_num)
theorem B27438101 : Blo 1605001 27438101 := bbase (se 6 (by rfl) ⟨643080, by rfl⟩ : syracuseStep 27438101 = 1286161) (by norm_num)
theorem B1928281 : Blo 1605001 1928281 := bbase (se 2 (by rfl) ⟨723105, by rfl⟩ : syracuseStep 1928281 = 1446211) (by norm_num)
theorem B6261877 : Blo 1605001 6261877 := bbase (se 5 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 6261877 = 587051) (by norm_num)
theorem B8244341 : Blo 1605001 8244341 := bbase (se 5 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 8244341 = 772907) (by norm_num)
theorem B3714221 : Blo 1605001 3714221 := bbase (se 3 (by rfl) ⟨696416, by rfl⟩ : syracuseStep 3714221 = 1392833) (by norm_num)
theorem B1928377 : Blo 1605001 1928377 := bbase (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) (by norm_num)
theorem B5418197 : Blo 1605001 5418197 := bbase (se 7 (by rfl) ⟨63494, by rfl⟩ : syracuseStep 5418197 = 126989) (by norm_num)
theorem B3255589 : Blo 1605001 3255589 := bbase (se 4 (by rfl) ⟨305211, by rfl⟩ : syracuseStep 3255589 = 610423) (by norm_num)
theorem B1805629 : Blo 1605001 1805629 := bbase (se 3 (by rfl) ⟨338555, by rfl⟩ : syracuseStep 1805629 = 677111) (by norm_num)
theorem B2198869 : Blo 1605001 2198869 := bbase (se 11 (by rfl) ⟨1610, by rfl⟩ : syracuseStep 2198869 = 3221) (by norm_num)
theorem B4066645 : Blo 1605001 4066645 := bbase (se 11 (by rfl) ⟨2978, by rfl⟩ : syracuseStep 4066645 = 5957) (by norm_num)
theorem B1805665 : Blo 1605001 1805665 := bbase (se 2 (by rfl) ⟨677124, by rfl⟩ : syracuseStep 1805665 = 1354249) (by norm_num)
theorem B6950245 : Blo 1605001 6950245 := bbase (se 4 (by rfl) ⟨651585, by rfl⟩ : syracuseStep 6950245 = 1303171) (by norm_num)
theorem B1805701 : Blo 1605001 1805701 := bbase (se 4 (by rfl) ⟨169284, by rfl⟩ : syracuseStep 1805701 = 338569) (by norm_num)
theorem B3526021 : Blo 1605001 3526021 := bbase (se 4 (by rfl) ⟨330564, by rfl⟩ : syracuseStep 3526021 = 661129) (by norm_num)
theorem B8686997 : Blo 1605001 8686997 := bbase (se 6 (by rfl) ⟨203601, by rfl⟩ : syracuseStep 8686997 = 407203) (by norm_num)
theorem B1805737 : Blo 1605001 1805737 := bbase (se 2 (by rfl) ⟨677151, by rfl⟩ : syracuseStep 1805737 = 1354303) (by norm_num)
theorem B4066757 : Blo 1605001 4066757 := bbase (se 4 (by rfl) ⟨381258, by rfl⟩ : syracuseStep 4066757 = 762517) (by norm_num)
theorem B1805773 : Blo 1605001 1805773 := bbase (se 3 (by rfl) ⟨338582, by rfl⟩ : syracuseStep 1805773 = 677165) (by norm_num)
theorem B1805809 : Blo 1605001 1805809 := bbase (se 2 (by rfl) ⟨677178, by rfl⟩ : syracuseStep 1805809 = 1354357) (by norm_num)
theorem B14855669 : Blo 1605001 14855669 := bbase (se 5 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 14855669 = 1392719) (by norm_num)
theorem B1805845 : Blo 1605001 1805845 := bbase (se 6 (by rfl) ⟨42324, by rfl⟩ : syracuseStep 1805845 = 84649) (by norm_num)
theorem B1715753 : Blo 1605001 1715753 := bbase (se 2 (by rfl) ⟨643407, by rfl⟩ : syracuseStep 1715753 = 1286815) (by norm_num)
theorem B1805881 : Blo 1605001 1805881 := bbase (se 2 (by rfl) ⟨677205, by rfl⟩ : syracuseStep 1805881 = 1354411) (by norm_num)
theorem B1805917 : Blo 1605001 1805917 := bbase (se 3 (by rfl) ⟨338609, by rfl⟩ : syracuseStep 1805917 = 677219) (by norm_num)
theorem B1805953 : Blo 1605001 1805953 := bbase (se 2 (by rfl) ⟨677232, by rfl⟩ : syracuseStep 1805953 = 1354465) (by norm_num)
theorem B5418629 : Blo 1605001 5418629 := bbase (se 4 (by rfl) ⟨507996, by rfl⟩ : syracuseStep 5418629 = 1015993) (by norm_num)
theorem B4066949 : Blo 1605001 4066949 := bbase (se 4 (by rfl) ⟨381276, by rfl⟩ : syracuseStep 4066949 = 762553) (by norm_num)
theorem B1805989 : Blo 1605001 1805989 := bbase (se 4 (by rfl) ⟨169311, by rfl⟩ : syracuseStep 1805989 = 338623) (by norm_num)
theorem B3428021 : Blo 1605001 3428021 := bbase (se 5 (by rfl) ⟨160688, by rfl⟩ : syracuseStep 3428021 = 321377) (by norm_num)
theorem B1806025 : Blo 1605001 1806025 := bbase (se 2 (by rfl) ⟨677259, by rfl⟩ : syracuseStep 1806025 = 1354519) (by norm_num)
theorem B1715941 : Blo 1605001 1715941 := bbase (se 4 (by rfl) ⟨160869, by rfl⟩ : syracuseStep 1715941 = 321739) (by norm_num)
theorem B1806061 : Blo 1605001 1806061 := bbase (se 3 (by rfl) ⟨338636, by rfl⟩ : syracuseStep 1806061 = 677273) (by norm_num)
theorem B8130293 : Blo 1605001 8130293 := bbase (se 5 (by rfl) ⟨381107, by rfl⟩ : syracuseStep 8130293 = 762215) (by norm_num)
theorem B3092213 : Blo 1605001 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B1806097 : Blo 1605001 1806097 := bbase (se 2 (by rfl) ⟨677286, by rfl⟩ : syracuseStep 1806097 = 1354573) (by norm_num)
theorem B1806133 : Blo 1605001 1806133 := bbase (se 5 (by rfl) ⟨84662, by rfl⟩ : syracuseStep 1806133 = 169325) (by norm_num)
theorem B1806169 : Blo 1605001 1806169 := bbase (se 2 (by rfl) ⟨677313, by rfl⟩ : syracuseStep 1806169 = 1354627) (by norm_num)
theorem B1806205 : Blo 1605001 1806205 := bbase (se 3 (by rfl) ⟨338663, by rfl⟩ : syracuseStep 1806205 = 677327) (by norm_num)
theorem B3256213 : Blo 1605001 3256213 := bbase (se 6 (by rfl) ⟨76317, by rfl⟩ : syracuseStep 3256213 = 152635) (by norm_num)
theorem B1806241 : Blo 1605001 1806241 := bbase (se 2 (by rfl) ⟨677340, by rfl⟩ : syracuseStep 1806241 = 1354681) (by norm_num)
theorem B1806277 : Blo 1605001 1806277 := bbase (se 4 (by rfl) ⟨169338, by rfl⟩ : syracuseStep 1806277 = 338677) (by norm_num)
theorem B4067293 : Blo 1605001 4067293 := bbase (se 3 (by rfl) ⟨762617, by rfl⟩ : syracuseStep 4067293 = 1525235) (by norm_num)
theorem B1806313 : Blo 1605001 1806313 := bbase (se 2 (by rfl) ⟨677367, by rfl⟩ : syracuseStep 1806313 = 1354735) (by norm_num)
theorem B1806349 : Blo 1605001 1806349 := bbase (se 3 (by rfl) ⟨338690, by rfl⟩ : syracuseStep 1806349 = 677381) (by norm_num)
theorem B1806385 : Blo 1605001 1806385 := bbase (se 2 (by rfl) ⟨677394, by rfl⟩ : syracuseStep 1806385 = 1354789) (by norm_num)
theorem B5419061 : Blo 1605001 5419061 := bbase (se 5 (by rfl) ⟨254018, by rfl⟩ : syracuseStep 5419061 = 508037) (by norm_num)
theorem B4067405 : Blo 1605001 4067405 := bbase (se 3 (by rfl) ⟨762638, by rfl⟩ : syracuseStep 4067405 = 1525277) (by norm_num)
theorem B1806421 : Blo 1605001 1806421 := bbase (se 8 (by rfl) ⟨10584, by rfl⟩ : syracuseStep 1806421 = 21169) (by norm_num)
theorem B1806457 : Blo 1605001 1806457 := bbase (se 2 (by rfl) ⟨677421, by rfl⟩ : syracuseStep 1806457 = 1354843) (by norm_num)
theorem B1806493 : Blo 1605001 1806493 := bbase (se 3 (by rfl) ⟨338717, by rfl⟩ : syracuseStep 1806493 = 677435) (by norm_num)
theorem B1806529 : Blo 1605001 1806529 := bbase (se 2 (by rfl) ⟨677448, by rfl⟩ : syracuseStep 1806529 = 1354897) (by norm_num)
theorem B1806565 : Blo 1605001 1806565 := bbase (se 4 (by rfl) ⟨169365, by rfl⟩ : syracuseStep 1806565 = 338731) (by norm_num)
theorem B1806601 : Blo 1605001 1806601 := bbase (se 2 (by rfl) ⟨677475, by rfl⟩ : syracuseStep 1806601 = 1354951) (by norm_num)
theorem B4067597 : Blo 1605001 4067597 := bbase (se 3 (by rfl) ⟨762674, by rfl⟩ : syracuseStep 4067597 = 1525349) (by norm_num)
theorem B2748709 : Blo 1605001 2748709 := bbase (se 4 (by rfl) ⟨257691, by rfl⟩ : syracuseStep 2748709 = 515383) (by norm_num)
theorem B1806637 : Blo 1605001 1806637 := bbase (se 3 (by rfl) ⟨338744, by rfl⟩ : syracuseStep 1806637 = 677489) (by norm_num)
theorem B1929521 : Blo 1605001 1929521 := bbase (se 2 (by rfl) ⟨723570, by rfl⟩ : syracuseStep 1929521 = 1447141) (by norm_num)
theorem B1806673 : Blo 1605001 1806673 := bbase (se 2 (by rfl) ⟨677502, by rfl⟩ : syracuseStep 1806673 = 1355005) (by norm_num)
theorem B6025589 : Blo 1605001 6025589 := bbase (se 5 (by rfl) ⟨282449, by rfl⟩ : syracuseStep 6025589 = 564899) (by norm_num)
theorem B5493109 : Blo 1605001 5493109 := bbase (se 5 (by rfl) ⟨257489, by rfl⟩ : syracuseStep 5493109 = 514979) (by norm_num)
theorem B1806709 : Blo 1605001 1806709 := bbase (se 5 (by rfl) ⟨84689, by rfl⟩ : syracuseStep 1806709 = 169379) (by norm_num)
theorem B1806745 : Blo 1605001 1806745 := bbase (se 2 (by rfl) ⟨677529, by rfl⟩ : syracuseStep 1806745 = 1355059) (by norm_num)
theorem B7819685 : Blo 1605001 7819685 := bbase (se 4 (by rfl) ⟨733095, by rfl⟩ : syracuseStep 7819685 = 1466191) (by norm_num)
theorem B1806781 : Blo 1605001 1806781 := bbase (se 3 (by rfl) ⟨338771, by rfl⟩ : syracuseStep 1806781 = 677543) (by norm_num)
theorem B17355221 : Blo 1605001 17355221 := bbase (se 7 (by rfl) ⟨203381, by rfl⟩ : syracuseStep 17355221 = 406763) (by norm_num)
theorem B1806817 : Blo 1605001 1806817 := bbase (se 2 (by rfl) ⟨677556, by rfl⟩ : syracuseStep 1806817 = 1355113) (by norm_num)
theorem B5419493 : Blo 1605001 5419493 := bbase (se 4 (by rfl) ⟨508077, by rfl⟩ : syracuseStep 5419493 = 1016155) (by norm_num)
theorem B1806853 : Blo 1605001 1806853 := bbase (se 4 (by rfl) ⟨169392, by rfl⟩ : syracuseStep 1806853 = 338785) (by norm_num)
theorem B1806889 : Blo 1605001 1806889 := bbase (se 2 (by rfl) ⟨677583, by rfl⟩ : syracuseStep 1806889 = 1355167) (by norm_num)
theorem B3428909 : Blo 1605001 3428909 := bbase (se 3 (by rfl) ⟨642920, by rfl⟩ : syracuseStep 3428909 = 1285841) (by norm_num)
theorem B4575797 : Blo 1605001 4575797 := bbase (se 5 (by rfl) ⟨214490, by rfl⟩ : syracuseStep 4575797 = 428981) (by norm_num)
theorem B1806925 : Blo 1605001 1806925 := bbase (se 3 (by rfl) ⟨338798, by rfl⟩ : syracuseStep 1806925 = 677597) (by norm_num)
theorem B1831529 : Blo 1605001 1831529 := bbase (se 2 (by rfl) ⟨686823, by rfl⟩ : syracuseStep 1831529 = 1373647) (by norm_num)
theorem B1806961 : Blo 1605001 1806961 := bbase (se 2 (by rfl) ⟨677610, by rfl⟩ : syracuseStep 1806961 = 1355221) (by norm_num)
theorem B1929853 : Blo 1605001 1929853 := bbase (se 3 (by rfl) ⟨361847, by rfl⟩ : syracuseStep 1929853 = 723695) (by norm_num)
theorem B7713413 : Blo 1605001 7713413 := bbase (se 4 (by rfl) ⟨723132, by rfl⟩ : syracuseStep 7713413 = 1446265) (by norm_num)
theorem B1806997 : Blo 1605001 1806997 := bbase (se 6 (by rfl) ⟨42351, by rfl⟩ : syracuseStep 1806997 = 84703) (by norm_num)
theorem B3429029 : Blo 1605001 3429029 := bbase (se 4 (by rfl) ⟨321471, by rfl⟩ : syracuseStep 3429029 = 642943) (by norm_num)
theorem B1807033 : Blo 1605001 1807033 := bbase (se 2 (by rfl) ⟨677637, by rfl⟩ : syracuseStep 1807033 = 1355275) (by norm_num)
theorem B6861509 : Blo 1605001 6861509 := bbase (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) (by norm_num)
theorem B1807069 : Blo 1605001 1807069 := bbase (se 3 (by rfl) ⟨338825, by rfl⟩ : syracuseStep 1807069 = 677651) (by norm_num)
theorem B1807105 : Blo 1605001 1807105 := bbase (se 2 (by rfl) ⟨677664, by rfl⟩ : syracuseStep 1807105 = 1355329) (by norm_num)
theorem B1807141 : Blo 1605001 1807141 := bbase (se 4 (by rfl) ⟨169419, by rfl⟩ : syracuseStep 1807141 = 338839) (by norm_num)
theorem B3175229 : Blo 1605001 3175229 := bbase (se 3 (by rfl) ⟨595355, by rfl⟩ : syracuseStep 3175229 = 1190711) (by norm_num)
theorem B1807177 : Blo 1605001 1807177 := bbase (se 2 (by rfl) ⟨677691, by rfl⟩ : syracuseStep 1807177 = 1355383) (by norm_num)
theorem B1807213 : Blo 1605001 1807213 := bbase (se 3 (by rfl) ⟨338852, by rfl⟩ : syracuseStep 1807213 = 677705) (by norm_num)
theorem B1807249 : Blo 1605001 1807249 := bbase (se 2 (by rfl) ⟨677718, by rfl⟩ : syracuseStep 1807249 = 1355437) (by norm_num)
theorem B5419925 : Blo 1605001 5419925 := bbase (se 6 (by rfl) ⟨127029, by rfl⟩ : syracuseStep 5419925 = 254059) (by norm_num)
theorem B3478421 : Blo 1605001 3478421 := bbase (se 6 (by rfl) ⟨81525, by rfl⟩ : syracuseStep 3478421 = 163051) (by norm_num)
theorem B1807285 : Blo 1605001 1807285 := bbase (se 5 (by rfl) ⟨84716, by rfl⟩ : syracuseStep 1807285 = 169433) (by norm_num)
theorem B6099893 : Blo 1605001 6099893 := bbase (se 5 (by rfl) ⟨285932, by rfl⟩ : syracuseStep 6099893 = 571865) (by norm_num)
theorem B2823101 : Blo 1605001 2823101 := bbase (se 3 (by rfl) ⟨529331, by rfl⟩ : syracuseStep 2823101 = 1058663) (by norm_num)
theorem B1831889 : Blo 1605001 1831889 := bbase (se 2 (by rfl) ⟨686958, by rfl⟩ : syracuseStep 1831889 = 1373917) (by norm_num)
theorem B1807321 : Blo 1605001 1807321 := bbase (se 2 (by rfl) ⟨677745, by rfl⟩ : syracuseStep 1807321 = 1355491) (by norm_num)
theorem B1807357 : Blo 1605001 1807357 := bbase (se 3 (by rfl) ⟨338879, by rfl⟩ : syracuseStep 1807357 = 677759) (by norm_num)
theorem B8131589 : Blo 1605001 8131589 := bbase (se 4 (by rfl) ⟨762336, by rfl⟩ : syracuseStep 8131589 = 1524673) (by norm_num)
theorem B1807393 : Blo 1605001 1807393 := bbase (se 2 (by rfl) ⟨677772, by rfl⟩ : syracuseStep 1807393 = 1355545) (by norm_num)
theorem B2708525 : Blo 1605001 2708525 := bbase (se 3 (by rfl) ⟨507848, by rfl⟩ : syracuseStep 2708525 = 1015697) (by norm_num)
theorem B2061373 : Blo 1605001 2061373 := bbase (se 3 (by rfl) ⟨386507, by rfl⟩ : syracuseStep 2061373 = 773015) (by norm_num)
theorem B1807429 : Blo 1605001 1807429 := bbase (se 4 (by rfl) ⟨169446, by rfl⟩ : syracuseStep 1807429 = 338893) (by norm_num)
theorem B8246357 : Blo 1605001 8246357 := bbase (se 8 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 8246357 = 96637) (by norm_num)
theorem B1807465 : Blo 1605001 1807465 := bbase (se 2 (by rfl) ⟨677799, by rfl⟩ : syracuseStep 1807465 = 1355599) (by norm_num)
theorem B1807501 : Blo 1605001 1807501 := bbase (se 3 (by rfl) ⟨338906, by rfl⟩ : syracuseStep 1807501 = 677813) (by norm_num)
theorem B2708653 : Blo 1605001 2708653 := bbase (se 3 (by rfl) ⟨507872, by rfl⟩ : syracuseStep 2708653 = 1015745) (by norm_num)
theorem B1807537 : Blo 1605001 1807537 := bbase (se 2 (by rfl) ⟨677826, by rfl⟩ : syracuseStep 1807537 = 1355653) (by norm_num)
theorem B6100181 : Blo 1605001 6100181 := bbase (se 7 (by rfl) ⟨71486, by rfl⟩ : syracuseStep 6100181 = 142973) (by norm_num)
theorem B1807573 : Blo 1605001 1807573 := bbase (se 7 (by rfl) ⟨21182, by rfl⟩ : syracuseStep 1807573 = 42365) (by norm_num)
theorem B1832185 : Blo 1605001 1832185 := bbase (se 2 (by rfl) ⟨687069, by rfl⟩ : syracuseStep 1832185 = 1374139) (by norm_num)
theorem B1807609 : Blo 1605001 1807609 := bbase (se 2 (by rfl) ⟨677853, by rfl⟩ : syracuseStep 1807609 = 1355707) (by norm_num)
theorem B2708741 : Blo 1605001 2708741 := bbase (se 4 (by rfl) ⟨253944, by rfl⟩ : syracuseStep 2708741 = 507889) (by norm_num)
theorem B1627409 : Blo 1605001 1627409 := bbase (se 2 (by rfl) ⟨610278, by rfl⟩ : syracuseStep 1627409 = 1220557) (by norm_num)
theorem B3429661 : Blo 1605001 3429661 := bbase (se 3 (by rfl) ⟨643061, by rfl⟩ : syracuseStep 3429661 = 1286123) (by norm_num)
theorem B1807645 : Blo 1605001 1807645 := bbase (se 3 (by rfl) ⟨338933, by rfl⟩ : syracuseStep 1807645 = 677867) (by norm_num)
theorem B1930549 : Blo 1605001 1930549 := bbase (se 5 (by rfl) ⟨90494, by rfl⟩ : syracuseStep 1930549 = 180989) (by norm_num)
theorem B1807681 : Blo 1605001 1807681 := bbase (se 2 (by rfl) ⟨677880, by rfl⟩ : syracuseStep 1807681 = 1355761) (by norm_num)
theorem B5420357 : Blo 1605001 5420357 := bbase (se 4 (by rfl) ⟨508158, by rfl⟩ : syracuseStep 5420357 = 1016317) (by norm_num)
theorem B1807717 : Blo 1605001 1807717 := bbase (se 4 (by rfl) ⟨169473, by rfl⟩ : syracuseStep 1807717 = 338947) (by norm_num)
theorem B2708869 : Blo 1605001 2708869 := bbase (se 4 (by rfl) ⟨253956, by rfl⟩ : syracuseStep 2708869 = 507913) (by norm_num)
theorem B1807753 : Blo 1605001 1807753 := bbase (se 2 (by rfl) ⟨677907, by rfl⟩ : syracuseStep 1807753 = 1355815) (by norm_num)
theorem B1807789 : Blo 1605001 1807789 := bbase (se 3 (by rfl) ⟨338960, by rfl⟩ : syracuseStep 1807789 = 677921) (by norm_num)
theorem B1807825 : Blo 1605001 1807825 := bbase (se 2 (by rfl) ⟨677934, by rfl⟩ : syracuseStep 1807825 = 1355869) (by norm_num)
theorem B2708957 : Blo 1605001 2708957 := bbase (se 3 (by rfl) ⟨507929, by rfl⟩ : syracuseStep 2708957 = 1015859) (by norm_num)
theorem B1807861 : Blo 1605001 1807861 := bbase (se 5 (by rfl) ⟨84743, by rfl⟩ : syracuseStep 1807861 = 169487) (by norm_num)
theorem B1627709 : Blo 1605001 1627709 := bbase (se 3 (by rfl) ⟨305195, by rfl⟩ : syracuseStep 1627709 = 610391) (by norm_num)
theorem B2709085 : Blo 1605001 2709085 := bbase (se 3 (by rfl) ⟨507953, by rfl⟩ : syracuseStep 2709085 = 1015907) (by norm_num)
theorem B5142133 : Blo 1605001 5142133 := bbase (se 5 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 5142133 = 482075) (by norm_num)
theorem B2709173 : Blo 1605001 2709173 := bbase (se 5 (by rfl) ⟨126992, by rfl⟩ : syracuseStep 2709173 = 253985) (by norm_num)
theorem B9148085 : Blo 1605001 9148085 := bbase (se 5 (by rfl) ⟨428816, by rfl⟩ : syracuseStep 9148085 = 857633) (by norm_num)
theorem B5420789 : Blo 1605001 5420789 := bbase (se 5 (by rfl) ⟨254099, by rfl⟩ : syracuseStep 5420789 = 508199) (by norm_num)
theorem B10295029 : Blo 1605001 10295029 := bbase (se 5 (by rfl) ⟨482579, by rfl⟩ : syracuseStep 10295029 = 965159) (by norm_num)
theorem B2709301 : Blo 1605001 2709301 := bbase (se 5 (by rfl) ⟨126998, by rfl⟩ : syracuseStep 2709301 = 253997) (by norm_num)
theorem B2201413 : Blo 1605001 2201413 := bbase (se 4 (by rfl) ⟨206382, by rfl⟩ : syracuseStep 2201413 = 412765) (by norm_num)
theorem B5945221 : Blo 1605001 5945221 := bbase (se 4 (by rfl) ⟨557364, by rfl⟩ : syracuseStep 5945221 = 1114729) (by norm_num)
theorem B2709389 : Blo 1605001 2709389 := bbase (se 3 (by rfl) ⟨508010, by rfl⟩ : syracuseStep 2709389 = 1016021) (by norm_num)
theorem B2709517 : Blo 1605001 2709517 := bbase (se 3 (by rfl) ⟨508034, by rfl⟩ : syracuseStep 2709517 = 1016069) (by norm_num)
theorem B2709605 : Blo 1605001 2709605 := bbase (se 4 (by rfl) ⟨254025, by rfl⟩ : syracuseStep 2709605 = 508051) (by norm_num)
theorem B1628293 : Blo 1605001 1628293 := bbase (se 4 (by rfl) ⟨152652, by rfl⟩ : syracuseStep 1628293 = 305305) (by norm_num)
theorem B17356949 : Blo 1605001 17356949 := bbase (se 6 (by rfl) ⟨406803, by rfl⟩ : syracuseStep 17356949 = 813607) (by norm_num)
theorem B1955989 : Blo 1605001 1955989 := bbase (se 6 (by rfl) ⟨45843, by rfl⟩ : syracuseStep 1955989 = 91687) (by norm_num)
theorem B3430549 : Blo 1605001 3430549 := bbase (se 6 (by rfl) ⟨80403, by rfl⟩ : syracuseStep 3430549 = 160807) (by norm_num)
theorem B1628317 : Blo 1605001 1628317 := bbase (se 3 (by rfl) ⟨305309, by rfl⟩ : syracuseStep 1628317 = 610619) (by norm_num)
theorem B5421221 : Blo 1605001 5421221 := bbase (se 4 (by rfl) ⟨508239, by rfl⟩ : syracuseStep 5421221 = 1016479) (by norm_num)
theorem B2709733 : Blo 1605001 2709733 := bbase (se 4 (by rfl) ⟨254037, by rfl⟩ : syracuseStep 2709733 = 508075) (by norm_num)
theorem B3430669 : Blo 1605001 3430669 := bbase (se 3 (by rfl) ⟨643250, by rfl⟩ : syracuseStep 3430669 = 1286501) (by norm_num)
theorem B13203733 : Blo 1605001 13203733 := bbase (se 6 (by rfl) ⟨309462, by rfl⟩ : syracuseStep 13203733 = 618925) (by norm_num)
theorem B8132885 : Blo 1605001 8132885 := bbase (se 6 (by rfl) ⟨190614, by rfl⟩ : syracuseStep 8132885 = 381229) (by norm_num)
theorem B3299621 : Blo 1605001 3299621 := bbase (se 4 (by rfl) ⟨309339, by rfl⟩ : syracuseStep 3299621 = 618679) (by norm_num)
theorem B2709821 : Blo 1605001 2709821 := bbase (se 3 (by rfl) ⟨508091, by rfl⟩ : syracuseStep 2709821 = 1016183) (by norm_num)
theorem B6101365 : Blo 1605001 6101365 := bbase (se 5 (by rfl) ⟨286001, by rfl⟩ : syracuseStep 6101365 = 572003) (by norm_num)
theorem B6863285 : Blo 1605001 6863285 := bbase (se 5 (by rfl) ⟨321716, by rfl⟩ : syracuseStep 6863285 = 643433) (by norm_num)
theorem B2709949 : Blo 1605001 2709949 := bbase (se 3 (by rfl) ⟨508115, by rfl⟩ : syracuseStep 2709949 = 1016231) (by norm_num)
theorem B1628605 : Blo 1605001 1628605 := bbase (se 3 (by rfl) ⟨305363, by rfl⟩ : syracuseStep 1628605 = 610727) (by norm_num)
theorem B5790149 : Blo 1605001 5790149 := bbase (se 4 (by rfl) ⟨542826, by rfl⟩ : syracuseStep 5790149 = 1085653) (by norm_num)
theorem B3430925 : Blo 1605001 3430925 := bbase (se 3 (by rfl) ⟨643298, by rfl⟩ : syracuseStep 3430925 = 1286597) (by norm_num)
theorem B21142037 : Blo 1605001 21142037 := bbase (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) (by norm_num)
theorem B2710037 : Blo 1605001 2710037 := bbase (se 6 (by rfl) ⟨63516, by rfl⟩ : syracuseStep 2710037 = 127033) (by norm_num)
theorem B5421653 : Blo 1605001 5421653 := bbase (se 8 (by rfl) ⟨31767, by rfl⟩ : syracuseStep 5421653 = 63535) (by norm_num)
theorem B7715429 : Blo 1605001 7715429 := bbase (se 4 (by rfl) ⟨723321, by rfl⟩ : syracuseStep 7715429 = 1446643) (by norm_num)
theorem B3611285 : Blo 1605001 3611285 := bbase (se 6 (by rfl) ⟨84639, by rfl⟩ : syracuseStep 3611285 = 169279) (by norm_num)
theorem B2710165 : Blo 1605001 2710165 := bbase (se 6 (by rfl) ⟨63519, by rfl⟩ : syracuseStep 2710165 = 127039) (by norm_num)
theorem B6863525 : Blo 1605001 6863525 := bbase (se 4 (by rfl) ⟨643455, by rfl⟩ : syracuseStep 6863525 = 1286911) (by norm_num)
theorem B2570933 : Blo 1605001 2570933 := bbase (se 5 (by rfl) ⟨120512, by rfl⟩ : syracuseStep 2570933 = 241025) (by norm_num)
theorem B3611357 : Blo 1605001 3611357 := bbase (se 3 (by rfl) ⟨677129, by rfl⟩ : syracuseStep 3611357 = 1354259) (by norm_num)
theorem B5790437 : Blo 1605001 5790437 := bbase (se 4 (by rfl) ⟨542853, by rfl⟩ : syracuseStep 5790437 = 1085707) (by norm_num)
theorem B2710253 : Blo 1605001 2710253 := bbase (se 3 (by rfl) ⟨508172, by rfl⟩ : syracuseStep 2710253 = 1016345) (by norm_num)
theorem B5143301 : Blo 1605001 5143301 := bbase (se 4 (by rfl) ⟨482184, by rfl⟩ : syracuseStep 5143301 = 964369) (by norm_num)
theorem B3611429 : Blo 1605001 3611429 := bbase (se 4 (by rfl) ⟨338571, by rfl⟩ : syracuseStep 3611429 = 677143) (by norm_num)
theorem B3611501 : Blo 1605001 3611501 := bbase (se 3 (by rfl) ⟨677156, by rfl⟩ : syracuseStep 3611501 = 1354313) (by norm_num)
theorem B2710381 : Blo 1605001 2710381 := bbase (se 3 (by rfl) ⟨508196, by rfl⟩ : syracuseStep 2710381 = 1016393) (by norm_num)
theorem B3611573 : Blo 1605001 3611573 := bbase (se 5 (by rfl) ⟨169292, by rfl⟩ : syracuseStep 3611573 = 338585) (by norm_num)
theorem B2710469 : Blo 1605001 2710469 := bbase (se 4 (by rfl) ⟨254106, by rfl⟩ : syracuseStep 2710469 = 508213) (by norm_num)
theorem B3611645 : Blo 1605001 3611645 := bbase (se 3 (by rfl) ⟨677183, by rfl⟩ : syracuseStep 3611645 = 1354367) (by norm_num)
theorem B5422085 : Blo 1605001 5422085 := bbase (se 4 (by rfl) ⟨508320, by rfl⟩ : syracuseStep 5422085 = 1016641) (by norm_num)
theorem B3611717 : Blo 1605001 3611717 := bbase (se 4 (by rfl) ⟨338598, by rfl⟩ : syracuseStep 3611717 = 677197) (by norm_num)
theorem B2710597 : Blo 1605001 2710597 := bbase (se 4 (by rfl) ⟨254118, by rfl⟩ : syracuseStep 2710597 = 508237) (by norm_num)
theorem B2407517 : Blo 1605001 2407517 := bbase (se 3 (by rfl) ⟨451409, by rfl⟩ : syracuseStep 2407517 = 902819) (by norm_num)
theorem B2407541 : Blo 1605001 2407541 := bbase (se 5 (by rfl) ⟨112853, by rfl⟩ : syracuseStep 2407541 = 225707) (by norm_num)
theorem B11140213 : Blo 1605001 11140213 := bbase (se 5 (by rfl) ⟨522197, by rfl⟩ : syracuseStep 11140213 = 1044395) (by norm_num)
theorem B3013757 : Blo 1605001 3013757 := bbase (se 3 (by rfl) ⟨565079, by rfl⟩ : syracuseStep 3013757 = 1130159) (by norm_num)
theorem B2407565 : Blo 1605001 2407565 := bbase (se 3 (by rfl) ⟨451418, by rfl⟩ : syracuseStep 2407565 = 902837) (by norm_num)
theorem B3611789 : Blo 1605001 3611789 := bbase (se 3 (by rfl) ⟨677210, by rfl⟩ : syracuseStep 3611789 = 1354421) (by norm_num)
theorem B5790869 : Blo 1605001 5790869 := bbase (se 6 (by rfl) ⟨135723, by rfl⟩ : syracuseStep 5790869 = 271447) (by norm_num)
theorem B2710685 : Blo 1605001 2710685 := bbase (se 3 (by rfl) ⟨508253, by rfl⟩ : syracuseStep 2710685 = 1016507) (by norm_num)
theorem B2407589 : Blo 1605001 2407589 := bbase (se 4 (by rfl) ⟨225711, by rfl⟩ : syracuseStep 2407589 = 451423) (by norm_num)
theorem B2407613 : Blo 1605001 2407613 := bbase (se 3 (by rfl) ⟨451427, by rfl⟩ : syracuseStep 2407613 = 902855) (by norm_num)
theorem B2407637 : Blo 1605001 2407637 := bbase (se 7 (by rfl) ⟨28214, by rfl⟩ : syracuseStep 2407637 = 56429) (by norm_num)
theorem B3611861 : Blo 1605001 3611861 := bbase (se 7 (by rfl) ⟨42326, by rfl⟩ : syracuseStep 3611861 = 84653) (by norm_num)
theorem B4119781 : Blo 1605001 4119781 := bbase (se 4 (by rfl) ⟨386229, by rfl⟩ : syracuseStep 4119781 = 772459) (by norm_num)
theorem B2407661 : Blo 1605001 2407661 := bbase (se 3 (by rfl) ⟨451436, by rfl⟩ : syracuseStep 2407661 = 902873) (by norm_num)
theorem B2407685 : Blo 1605001 2407685 := bbase (se 4 (by rfl) ⟨225720, by rfl⟩ : syracuseStep 2407685 = 451441) (by norm_num)
theorem B12197141 : Blo 1605001 12197141 := bbase (se 6 (by rfl) ⟨285870, by rfl⟩ : syracuseStep 12197141 = 571741) (by norm_num)
theorem B2407709 : Blo 1605001 2407709 := bbase (se 3 (by rfl) ⟨451445, by rfl⟩ : syracuseStep 2407709 = 902891) (by norm_num)
theorem B3611933 : Blo 1605001 3611933 := bbase (se 3 (by rfl) ⟨677237, by rfl⟩ : syracuseStep 3611933 = 1354475) (by norm_num)
theorem B2710813 : Blo 1605001 2710813 := bbase (se 3 (by rfl) ⟨508277, by rfl⟩ : syracuseStep 2710813 = 1016555) (by norm_num)
theorem B2407733 : Blo 1605001 2407733 := bbase (se 5 (by rfl) ⟨112862, by rfl⟩ : syracuseStep 2407733 = 225725) (by norm_num)
theorem B2407757 : Blo 1605001 2407757 := bbase (se 3 (by rfl) ⟨451454, by rfl⟩ : syracuseStep 2407757 = 902909) (by norm_num)
theorem B2571605 : Blo 1605001 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B7716181 : Blo 1605001 7716181 := bbase (se 11 (by rfl) ⟨5651, by rfl⟩ : syracuseStep 7716181 = 11303) (by norm_num)
theorem B4341077 : Blo 1605001 4341077 := bbase (se 11 (by rfl) ⟨3179, by rfl⟩ : syracuseStep 4341077 = 6359) (by norm_num)
theorem B2407781 : Blo 1605001 2407781 := bbase (se 4 (by rfl) ⟨225729, by rfl⟩ : syracuseStep 2407781 = 451459) (by norm_num)
theorem B3612005 : Blo 1605001 3612005 := bbase (se 4 (by rfl) ⟨338625, by rfl⟩ : syracuseStep 3612005 = 677251) (by norm_num)
theorem B2710901 : Blo 1605001 2710901 := bbase (se 5 (by rfl) ⟨127073, by rfl⟩ : syracuseStep 2710901 = 254147) (by norm_num)
theorem B2407805 : Blo 1605001 2407805 := bbase (se 3 (by rfl) ⟨451463, by rfl⟩ : syracuseStep 2407805 = 902927) (by norm_num)
theorem B3431813 : Blo 1605001 3431813 := bbase (se 4 (by rfl) ⟨321732, by rfl⟩ : syracuseStep 3431813 = 643465) (by norm_num)
theorem B2407829 : Blo 1605001 2407829 := bbase (se 6 (by rfl) ⟨56433, by rfl⟩ : syracuseStep 2407829 = 112867) (by norm_num)
theorem B4881829 : Blo 1605001 4881829 := bbase (se 4 (by rfl) ⟨457671, by rfl⟩ : syracuseStep 4881829 = 915343) (by norm_num)
theorem B2407853 : Blo 1605001 2407853 := bbase (se 3 (by rfl) ⟨451472, by rfl⟩ : syracuseStep 2407853 = 902945) (by norm_num)
theorem B3612077 : Blo 1605001 3612077 := bbase (se 3 (by rfl) ⟨677264, by rfl⟩ : syracuseStep 3612077 = 1354529) (by norm_num)
theorem B5422517 : Blo 1605001 5422517 := bbase (se 5 (by rfl) ⟨254180, by rfl⟩ : syracuseStep 5422517 = 508361) (by norm_num)
theorem B2407877 : Blo 1605001 2407877 := bbase (se 4 (by rfl) ⟨225738, by rfl⟩ : syracuseStep 2407877 = 451477) (by norm_num)
theorem B3857861 : Blo 1605001 3857861 := bbase (se 4 (by rfl) ⟨361674, by rfl⟩ : syracuseStep 3857861 = 723349) (by norm_num)
theorem B2407901 : Blo 1605001 2407901 := bbase (se 3 (by rfl) ⟨451481, by rfl⟩ : syracuseStep 2407901 = 902963) (by norm_num)
theorem B2407925 : Blo 1605001 2407925 := bbase (se 5 (by rfl) ⟨112871, by rfl⟩ : syracuseStep 2407925 = 225743) (by norm_num)
theorem B3612149 : Blo 1605001 3612149 := bbase (se 5 (by rfl) ⟨169319, by rfl⟩ : syracuseStep 3612149 = 338639) (by norm_num)
theorem B2711029 : Blo 1605001 2711029 := bbase (se 5 (by rfl) ⟨127079, by rfl⟩ : syracuseStep 2711029 = 254159) (by norm_num)
theorem B3300869 : Blo 1605001 3300869 := bbase (se 4 (by rfl) ⟨309456, by rfl⟩ : syracuseStep 3300869 = 618913) (by norm_num)
theorem B2407949 : Blo 1605001 2407949 := bbase (se 3 (by rfl) ⟨451490, by rfl⟩ : syracuseStep 2407949 = 902981) (by norm_num)
theorem B4062757 : Blo 1605001 4062757 := bbase (se 4 (by rfl) ⟨380883, by rfl⟩ : syracuseStep 4062757 = 761767) (by norm_num)
theorem B2407973 : Blo 1605001 2407973 := bbase (se 4 (by rfl) ⟨225747, by rfl⟩ : syracuseStep 2407973 = 451495) (by norm_num)
theorem B6512165 : Blo 1605001 6512165 := bbase (se 4 (by rfl) ⟨610515, by rfl⟩ : syracuseStep 6512165 = 1221031) (by norm_num)
theorem B8134181 : Blo 1605001 8134181 := bbase (se 4 (by rfl) ⟨762579, by rfl⟩ : syracuseStep 8134181 = 1525159) (by norm_num)
theorem B2407997 : Blo 1605001 2407997 := bbase (se 3 (by rfl) ⟨451499, by rfl⟩ : syracuseStep 2407997 = 902999) (by norm_num)
theorem B3612221 : Blo 1605001 3612221 := bbase (se 3 (by rfl) ⟨677291, by rfl⟩ : syracuseStep 3612221 = 1354583) (by norm_num)
theorem B2711117 : Blo 1605001 2711117 := bbase (se 3 (by rfl) ⟨508334, by rfl⟩ : syracuseStep 2711117 = 1016669) (by norm_num)
theorem B2408021 : Blo 1605001 2408021 := bbase (se 8 (by rfl) ⟨14109, by rfl⟩ : syracuseStep 2408021 = 28219) (by norm_num)
theorem B2408045 : Blo 1605001 2408045 := bbase (se 3 (by rfl) ⟨451508, by rfl⟩ : syracuseStep 2408045 = 903017) (by norm_num)
theorem B3432053 : Blo 1605001 3432053 := bbase (se 5 (by rfl) ⟨160877, by rfl⟩ : syracuseStep 3432053 = 321755) (by norm_num)
theorem B2408069 : Blo 1605001 2408069 := bbase (se 4 (by rfl) ⟨225756, by rfl⟩ : syracuseStep 2408069 = 451513) (by norm_num)
theorem B3612293 : Blo 1605001 3612293 := bbase (se 4 (by rfl) ⟨338652, by rfl⟩ : syracuseStep 3612293 = 677305) (by norm_num)
theorem B3047053 : Blo 1605001 3047053 := bbase (se 3 (by rfl) ⟨571322, by rfl⟩ : syracuseStep 3047053 = 1142645) (by norm_num)
theorem B4062869 : Blo 1605001 4062869 := bbase (se 6 (by rfl) ⟨95223, by rfl⟩ : syracuseStep 4062869 = 190447) (by norm_num)
theorem B21978773 : Blo 1605001 21978773 := bbase (se 6 (by rfl) ⟨515127, by rfl⟩ : syracuseStep 21978773 = 1030255) (by norm_num)
theorem B2408093 : Blo 1605001 2408093 := bbase (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) (by norm_num)
theorem B12189365 : Blo 1605001 12189365 := bbase (se 5 (by rfl) ⟨571376, by rfl⟩ : syracuseStep 12189365 = 1142753) (by norm_num)
theorem B2408117 : Blo 1605001 2408117 := bbase (se 5 (by rfl) ⟨112880, by rfl⟩ : syracuseStep 2408117 = 225761) (by norm_num)
theorem B2408141 : Blo 1605001 2408141 := bbase (se 3 (by rfl) ⟨451526, by rfl⟩ : syracuseStep 2408141 = 903053) (by norm_num)
theorem B3612365 : Blo 1605001 3612365 := bbase (se 3 (by rfl) ⟨677318, by rfl⟩ : syracuseStep 3612365 = 1354637) (by norm_num)
theorem B2711245 : Blo 1605001 2711245 := bbase (se 3 (by rfl) ⟨508358, by rfl⟩ : syracuseStep 2711245 = 1016717) (by norm_num)
theorem B2408165 : Blo 1605001 2408165 := bbase (se 4 (by rfl) ⟨225765, by rfl⟩ : syracuseStep 2408165 = 451531) (by norm_num)
theorem B2408189 : Blo 1605001 2408189 := bbase (se 3 (by rfl) ⟨451535, by rfl⟩ : syracuseStep 2408189 = 903071) (by norm_num)
theorem B2408213 : Blo 1605001 2408213 := bbase (se 6 (by rfl) ⟨56442, by rfl⟩ : syracuseStep 2408213 = 112885) (by norm_num)
theorem B3612437 : Blo 1605001 3612437 := bbase (se 6 (by rfl) ⟨84666, by rfl⟩ : syracuseStep 3612437 = 169333) (by norm_num)
theorem B2711333 : Blo 1605001 2711333 := bbase (se 4 (by rfl) ⟨254187, by rfl⟩ : syracuseStep 2711333 = 508375) (by norm_num)
theorem B3047213 : Blo 1605001 3047213 := bbase (se 3 (by rfl) ⟨571352, by rfl⟩ : syracuseStep 3047213 = 1142705) (by norm_num)
theorem B2408237 : Blo 1605001 2408237 := bbase (se 3 (by rfl) ⟨451544, by rfl⟩ : syracuseStep 2408237 = 903089) (by norm_num)
theorem B2031409 : Blo 1605001 2031409 := bbase (se 2 (by rfl) ⟨761778, by rfl⟩ : syracuseStep 2031409 = 1523557) (by norm_num)
theorem B2285381 : Blo 1605001 2285381 := bbase (se 4 (by rfl) ⟨214254, by rfl⟩ : syracuseStep 2285381 = 428509) (by norm_num)
theorem B2408261 : Blo 1605001 2408261 := bbase (se 4 (by rfl) ⟨225774, by rfl⟩ : syracuseStep 2408261 = 451549) (by norm_num)
theorem B3858245 : Blo 1605001 3858245 := bbase (se 4 (by rfl) ⟨361710, by rfl⟩ : syracuseStep 3858245 = 723421) (by norm_num)
theorem B4063061 : Blo 1605001 4063061 := bbase (se 9 (by rfl) ⟨11903, by rfl⟩ : syracuseStep 4063061 = 23807) (by norm_num)
theorem B2572117 : Blo 1605001 2572117 := bbase (se 9 (by rfl) ⟨7535, by rfl⟩ : syracuseStep 2572117 = 15071) (by norm_num)
theorem B2408285 : Blo 1605001 2408285 := bbase (se 3 (by rfl) ⟨451553, by rfl⟩ : syracuseStep 2408285 = 903107) (by norm_num)
theorem B3612509 : Blo 1605001 3612509 := bbase (se 3 (by rfl) ⟨677345, by rfl⟩ : syracuseStep 3612509 = 1354691) (by norm_num)
theorem B5422949 : Blo 1605001 5422949 := bbase (se 4 (by rfl) ⟨508401, by rfl⟩ : syracuseStep 5422949 = 1016803) (by norm_num)
theorem B2408309 : Blo 1605001 2408309 := bbase (se 5 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 2408309 = 225779) (by norm_num)
theorem B2408333 : Blo 1605001 2408333 := bbase (se 3 (by rfl) ⟨451562, by rfl⟩ : syracuseStep 2408333 = 903125) (by norm_num)
theorem B2408357 : Blo 1605001 2408357 := bbase (se 4 (by rfl) ⟨225783, by rfl⟩ : syracuseStep 2408357 = 451567) (by norm_num)
theorem B3612581 : Blo 1605001 3612581 := bbase (se 4 (by rfl) ⟨338679, by rfl⟩ : syracuseStep 3612581 = 677359) (by norm_num)
theorem B2711461 : Blo 1605001 2711461 := bbase (se 4 (by rfl) ⟨254199, by rfl⟩ : syracuseStep 2711461 = 508399) (by norm_num)
theorem B3047357 : Blo 1605001 3047357 := bbase (se 3 (by rfl) ⟨571379, by rfl⟩ : syracuseStep 3047357 = 1142759) (by norm_num)
theorem B2408381 : Blo 1605001 2408381 := bbase (se 3 (by rfl) ⟨451571, by rfl⟩ : syracuseStep 2408381 = 903143) (by norm_num)
theorem B8126405 : Blo 1605001 8126405 := bbase (se 4 (by rfl) ⟨761850, by rfl⟩ : syracuseStep 8126405 = 1523701) (by norm_num)
theorem B4571093 : Blo 1605001 4571093 := bbase (se 7 (by rfl) ⟨53567, by rfl⟩ : syracuseStep 4571093 = 107135) (by norm_num)
theorem B2408405 : Blo 1605001 2408405 := bbase (se 7 (by rfl) ⟨28223, by rfl⟩ : syracuseStep 2408405 = 56447) (by norm_num)
theorem B2031581 : Blo 1605001 2031581 := bbase (se 3 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 2031581 = 761843) (by norm_num)
theorem B2408429 : Blo 1605001 2408429 := bbase (se 3 (by rfl) ⟨451580, by rfl⟩ : syracuseStep 2408429 = 903161) (by norm_num)
theorem B3612653 : Blo 1605001 3612653 := bbase (se 3 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 3612653 = 1354745) (by norm_num)
theorem B2711549 : Blo 1605001 2711549 := bbase (se 3 (by rfl) ⟨508415, by rfl⟩ : syracuseStep 2711549 = 1016831) (by norm_num)
theorem B1605635 : Blo 1605001 1605635 := bstep (se 1 (by rfl) ⟨1204226, by rfl⟩ : syracuseStep 1605635 = 2408453) B2408453
theorem B4571149 : Blo 1605001 4571149 := bstep (se 3 (by rfl) ⟨857090, by rfl⟩ : syracuseStep 4571149 = 1714181) B1714181
theorem B3612689 : Blo 1605001 3612689 := bstep (se 2 (by rfl) ⟨1354758, by rfl⟩ : syracuseStep 3612689 = 2709517) B2709517
theorem B2408465 : Blo 1605001 2408465 := bstep (se 2 (by rfl) ⟨903174, by rfl⟩ : syracuseStep 2408465 = 1806349) B1806349
theorem B1605651 : Blo 1605001 1605651 := bstep (se 1 (by rfl) ⟨1204238, by rfl⟩ : syracuseStep 1605651 = 2408477) B2408477
theorem B2711569 : Blo 1605001 2711569 := bstep (se 2 (by rfl) ⟨1016838, by rfl⟩ : syracuseStep 2711569 = 2033677) B2033677
theorem B3612707 : Blo 1605001 3612707 := bstep (se 1 (by rfl) ⟨2709530, by rfl⟩ : syracuseStep 3612707 = 5419061) B5419061
theorem B2408483 : Blo 1605001 2408483 := bstep (se 1 (by rfl) ⟨1806362, by rfl⟩ : syracuseStep 2408483 = 3612725) B3612725
theorem B1605667 : Blo 1605001 1605667 := bstep (se 1 (by rfl) ⟨1204250, by rfl⟩ : syracuseStep 1605667 = 2408501) B2408501
theorem B1605683 : Blo 1605001 1605683 := bstep (se 1 (by rfl) ⟨1204262, by rfl⟩ : syracuseStep 1605683 = 2408525) B2408525
theorem B2711603 : Blo 1605001 2711603 := bstep (se 1 (by rfl) ⟨2033702, by rfl⟩ : syracuseStep 2711603 = 4067405) B4067405
theorem B2408513 : Blo 1605001 2408513 := bstep (se 2 (by rfl) ⟨903192, by rfl⟩ : syracuseStep 2408513 = 1806385) B1806385
theorem B1605699 : Blo 1605001 1605699 := bstep (se 1 (by rfl) ⟨1204274, by rfl⟩ : syracuseStep 1605699 = 2408549) B2408549
theorem B20578373 : Blo 1605001 20578373 := bstep (se 4 (by rfl) ⟨1929222, by rfl⟩ : syracuseStep 20578373 = 3858445) B3858445
theorem B2408531 : Blo 1605001 2408531 := bstep (se 1 (by rfl) ⟨1806398, by rfl⟩ : syracuseStep 2408531 = 3612797) B3612797
theorem B1605715 : Blo 1605001 1605715 := bstep (se 1 (by rfl) ⟨1204286, by rfl⟩ : syracuseStep 1605715 = 2408573) B2408573
theorem B1605731 : Blo 1605001 1605731 := bstep (se 1 (by rfl) ⟨1204298, by rfl⟩ : syracuseStep 1605731 = 2408597) B2408597
theorem B2408561 : Blo 1605001 2408561 := bstep (se 2 (by rfl) ⟨903210, by rfl⟩ : syracuseStep 2408561 = 1806421) B1806421
theorem B1605747 : Blo 1605001 1605747 := bstep (se 1 (by rfl) ⟨1204310, by rfl⟩ : syracuseStep 1605747 = 2408621) B2408621
theorem B2408579 : Blo 1605001 2408579 := bstep (se 1 (by rfl) ⟨1806434, by rfl⟩ : syracuseStep 2408579 = 3612869) B3612869
theorem B1605763 : Blo 1605001 1605763 := bstep (se 1 (by rfl) ⟨1204322, by rfl⟩ : syracuseStep 1605763 = 2408645) B2408645
theorem B1605779 : Blo 1605001 1605779 := bstep (se 1 (by rfl) ⟨1204334, by rfl⟩ : syracuseStep 1605779 = 2408669) B2408669
theorem B2408609 : Blo 1605001 2408609 := bstep (se 2 (by rfl) ⟨903228, by rfl⟩ : syracuseStep 2408609 = 1806457) B1806457
theorem B1605795 : Blo 1605001 1605795 := bstep (se 1 (by rfl) ⟨1204346, by rfl⟩ : syracuseStep 1605795 = 2408693) B2408693
theorem B4571309 : Blo 1605001 4571309 := bstep (se 3 (by rfl) ⟨857120, by rfl⟩ : syracuseStep 4571309 = 1714241) B1714241
theorem B2408627 : Blo 1605001 2408627 := bstep (se 1 (by rfl) ⟨1806470, by rfl⟩ : syracuseStep 2408627 = 3612941) B3612941
theorem B1605811 : Blo 1605001 1605811 := bstep (se 1 (by rfl) ⟨1204358, by rfl⟩ : syracuseStep 1605811 = 2408717) B2408717
theorem B2171057 : Blo 1605001 2171057 := bstep (se 2 (by rfl) ⟨814146, by rfl⟩ : syracuseStep 2171057 = 1628293) B1628293
theorem B2711731 : Blo 1605001 2711731 := bstep (se 1 (by rfl) ⟨2033798, by rfl⟩ : syracuseStep 2711731 = 4067597) B4067597
theorem B1605827 : Blo 1605001 1605827 := bstep (se 1 (by rfl) ⟨1204370, by rfl⟩ : syracuseStep 1605827 = 2408741) B2408741
theorem B7323853 : Blo 1605001 7323853 := bstep (se 3 (by rfl) ⟨1373222, by rfl⟩ : syracuseStep 7323853 = 2746445) B2746445
theorem B2408657 : Blo 1605001 2408657 := bstep (se 2 (by rfl) ⟨903246, by rfl⟩ : syracuseStep 2408657 = 1806493) B1806493
theorem B1605843 : Blo 1605001 1605843 := bstep (se 1 (by rfl) ⟨1204382, by rfl⟩ : syracuseStep 1605843 = 2408765) B2408765
theorem B2171089 : Blo 1605001 2171089 := bstep (se 2 (by rfl) ⟨814158, by rfl⟩ : syracuseStep 2171089 = 1628317) B1628317
theorem B2408675 : Blo 1605001 2408675 := bstep (se 1 (by rfl) ⟨1806506, by rfl⟩ : syracuseStep 2408675 = 3613013) B3613013
theorem B1605859 : Blo 1605001 1605859 := bstep (se 1 (by rfl) ⟨1204394, by rfl⟩ : syracuseStep 1605859 = 2408789) B2408789
theorem B1605875 : Blo 1605001 1605875 := bstep (se 1 (by rfl) ⟨1204406, by rfl⟩ : syracuseStep 1605875 = 2408813) B2408813
theorem B2285825 : Blo 1605001 2285825 := bstep (se 2 (by rfl) ⟨857184, by rfl⟩ : syracuseStep 2285825 = 1714369) B1714369
theorem B2408705 : Blo 1605001 2408705 := bstep (se 2 (by rfl) ⟨903264, by rfl⟩ : syracuseStep 2408705 = 1806529) B1806529
theorem B1605891 : Blo 1605001 1605891 := bstep (se 1 (by rfl) ⟨1204418, by rfl⟩ : syracuseStep 1605891 = 2408837) B2408837
theorem B2408723 : Blo 1605001 2408723 := bstep (se 1 (by rfl) ⟨1806542, by rfl⟩ : syracuseStep 2408723 = 3613085) B3613085
theorem B1605907 : Blo 1605001 1605907 := bstep (se 1 (by rfl) ⟨1204430, by rfl⟩ : syracuseStep 1605907 = 2408861) B2408861
theorem B1605923 : Blo 1605001 1605923 := bstep (se 1 (by rfl) ⟨1204442, by rfl⟩ : syracuseStep 1605923 = 2408885) B2408885
theorem B3612977 : Blo 1605001 3612977 := bstep (se 2 (by rfl) ⟨1354866, by rfl⟩ : syracuseStep 3612977 = 2709733) B2709733
theorem B2408753 : Blo 1605001 2408753 := bstep (se 2 (by rfl) ⟨903282, by rfl⟩ : syracuseStep 2408753 = 1806565) B1806565
theorem B1605939 : Blo 1605001 1605939 := bstep (se 1 (by rfl) ⟨1204454, by rfl⟩ : syracuseStep 1605939 = 2408909) B2408909
theorem B3612995 : Blo 1605001 3612995 := bstep (se 1 (by rfl) ⟨2709746, by rfl⟩ : syracuseStep 3612995 = 5419493) B5419493
theorem B2408771 : Blo 1605001 2408771 := bstep (se 1 (by rfl) ⟨1806578, by rfl⟩ : syracuseStep 2408771 = 3613157) B3613157
theorem B1605955 : Blo 1605001 1605955 := bstep (se 1 (by rfl) ⟨1204466, by rfl⟩ : syracuseStep 1605955 = 2408933) B2408933
theorem B1605971 : Blo 1605001 1605971 := bstep (se 1 (by rfl) ⟨1204478, by rfl⟩ : syracuseStep 1605971 = 2408957) B2408957
theorem B2408801 : Blo 1605001 2408801 := bstep (se 2 (by rfl) ⟨903300, by rfl⟩ : syracuseStep 2408801 = 1806601) B1806601
theorem B22266211 : Blo 1605001 22266211 := bstep (se 1 (by rfl) ⟨16699658, by rfl⟩ : syracuseStep 22266211 = 33399317) B33399317
theorem B4571491 : Blo 1605001 4571491 := bstep (se 1 (by rfl) ⟨3428618, by rfl⟩ : syracuseStep 4571491 = 6857237) B6857237
theorem B1605987 : Blo 1605001 1605987 := bstep (se 1 (by rfl) ⟨1204490, by rfl⟩ : syracuseStep 1605987 = 2408981) B2408981
theorem B17604977 : Blo 1605001 17604977 := bstep (se 2 (by rfl) ⟨6601866, by rfl⟩ : syracuseStep 17604977 = 13203733) B13203733
theorem B2285939 : Blo 1605001 2285939 := bstep (se 1 (by rfl) ⟨1714454, by rfl⟩ : syracuseStep 2285939 = 3428909) B3428909
theorem B2408819 : Blo 1605001 2408819 := bstep (se 1 (by rfl) ⟨1806614, by rfl⟩ : syracuseStep 2408819 = 3613229) B3613229
theorem B1606003 : Blo 1605001 1606003 := bstep (se 1 (by rfl) ⟨1204502, by rfl⟩ : syracuseStep 1606003 = 2409005) B2409005
theorem B1606019 : Blo 1605001 1606019 := bstep (se 1 (by rfl) ⟨1204514, by rfl⟩ : syracuseStep 1606019 = 2409029) B2409029
theorem B2408849 : Blo 1605001 2408849 := bstep (se 2 (by rfl) ⟨903318, by rfl⟩ : syracuseStep 2408849 = 1806637) B1806637
theorem B1606035 : Blo 1605001 1606035 := bstep (se 1 (by rfl) ⟨1204526, by rfl⟩ : syracuseStep 1606035 = 2409053) B2409053
theorem B3047843 : Blo 1605001 3047843 := bstep (se 1 (by rfl) ⟨2285882, by rfl⟩ : syracuseStep 3047843 = 4571765) B4571765
theorem B2408867 : Blo 1605001 2408867 := bstep (se 1 (by rfl) ⟨1806650, by rfl⟩ : syracuseStep 2408867 = 3613301) B3613301
theorem B1606051 : Blo 1605001 1606051 := bstep (se 1 (by rfl) ⟨1204538, by rfl⟩ : syracuseStep 1606051 = 2409077) B2409077
theorem B1606067 : Blo 1605001 1606067 := bstep (se 1 (by rfl) ⟨1204550, by rfl⟩ : syracuseStep 1606067 = 2409101) B2409101
theorem B2286019 : Blo 1605001 2286019 := bstep (se 1 (by rfl) ⟨1714514, by rfl⟩ : syracuseStep 2286019 = 3429029) B3429029
theorem B2032067 : Blo 1605001 2032067 := bstep (se 1 (by rfl) ⟨1524050, by rfl⟩ : syracuseStep 2032067 = 3048101) B3048101
theorem B2408897 : Blo 1605001 2408897 := bstep (se 2 (by rfl) ⟨903336, by rfl⟩ : syracuseStep 2408897 = 1806673) B1806673
theorem B1606083 : Blo 1605001 1606083 := bstep (se 1 (by rfl) ⟨1204562, by rfl⟩ : syracuseStep 1606083 = 2409125) B2409125
theorem B9904589 : Blo 1605001 9904589 := bstep (se 3 (by rfl) ⟨1857110, by rfl⟩ : syracuseStep 9904589 = 3714221) B3714221
theorem B2408915 : Blo 1605001 2408915 := bstep (se 1 (by rfl) ⟨1806686, by rfl⟩ : syracuseStep 2408915 = 3613373) B3613373
theorem B1606099 : Blo 1605001 1606099 := bstep (se 1 (by rfl) ⟨1204574, by rfl⟩ : syracuseStep 1606099 = 2409149) B2409149
theorem B1606115 : Blo 1605001 1606115 := bstep (se 1 (by rfl) ⟨1204586, by rfl⟩ : syracuseStep 1606115 = 2409173) B2409173
theorem B5423597 : Blo 1605001 5423597 := bstep (se 3 (by rfl) ⟨1016924, by rfl⟩ : syracuseStep 5423597 = 2033849) B2033849
theorem B4063729 : Blo 1605001 4063729 := bstep (se 2 (by rfl) ⟨1523898, by rfl⟩ : syracuseStep 4063729 = 3047797) B3047797
theorem B7324145 : Blo 1605001 7324145 := bstep (se 2 (by rfl) ⟨2746554, by rfl⟩ : syracuseStep 7324145 = 5493109) B5493109
theorem B2408945 : Blo 1605001 2408945 := bstep (se 2 (by rfl) ⟨903354, by rfl⟩ : syracuseStep 2408945 = 1806709) B1806709
theorem B1606131 : Blo 1605001 1606131 := bstep (se 1 (by rfl) ⟨1204598, by rfl⟩ : syracuseStep 1606131 = 2409197) B2409197
theorem B8135153 : Blo 1605001 8135153 := bstep (se 2 (by rfl) ⟨3050682, by rfl⟩ : syracuseStep 8135153 = 6101365) B6101365
theorem B2408963 : Blo 1605001 2408963 := bstep (se 1 (by rfl) ⟨1806722, by rfl⟩ : syracuseStep 2408963 = 3613445) B3613445
theorem B1606147 : Blo 1605001 1606147 := bstep (se 1 (by rfl) ⟨1204610, by rfl⟩ : syracuseStep 1606147 = 2409221) B2409221
theorem B1606163 : Blo 1605001 1606163 := bstep (se 1 (by rfl) ⟨1204622, by rfl⟩ : syracuseStep 1606163 = 2409245) B2409245
theorem B2408993 : Blo 1605001 2408993 := bstep (se 2 (by rfl) ⟨903372, by rfl⟩ : syracuseStep 2408993 = 1806745) B1806745
theorem B10289699 : Blo 1605001 10289699 := bstep (se 1 (by rfl) ⟨7717274, by rfl⟩ : syracuseStep 10289699 = 15434549) B15434549
theorem B1606179 : Blo 1605001 1606179 := bstep (se 1 (by rfl) ⟨1204634, by rfl⟩ : syracuseStep 1606179 = 2409269) B2409269
theorem B2409011 : Blo 1605001 2409011 := bstep (se 1 (by rfl) ⟨1806758, by rfl⟩ : syracuseStep 2409011 = 3613517) B3613517
theorem B1606195 : Blo 1605001 1606195 := bstep (se 1 (by rfl) ⟨1204646, by rfl⟩ : syracuseStep 1606195 = 2409293) B2409293
theorem B1606211 : Blo 1605001 1606211 := bstep (se 1 (by rfl) ⟨1204658, by rfl⟩ : syracuseStep 1606211 = 2409317) B2409317
theorem B8127053 : Blo 1605001 8127053 := bstep (se 3 (by rfl) ⟨1523822, by rfl⟩ : syracuseStep 8127053 = 3047645) B3047645
theorem B3613265 : Blo 1605001 3613265 := bstep (se 2 (by rfl) ⟨1354974, by rfl⟩ : syracuseStep 3613265 = 2709949) B2709949
theorem B2409041 : Blo 1605001 2409041 := bstep (se 2 (by rfl) ⟨903390, by rfl⟩ : syracuseStep 2409041 = 1806781) B1806781
theorem B1606227 : Blo 1605001 1606227 := bstep (se 1 (by rfl) ⟨1204670, by rfl⟩ : syracuseStep 1606227 = 2409341) B2409341
theorem B3613283 : Blo 1605001 3613283 := bstep (se 1 (by rfl) ⟨2709962, by rfl⟩ : syracuseStep 3613283 = 5419925) B5419925
theorem B2409059 : Blo 1605001 2409059 := bstep (se 1 (by rfl) ⟨1806794, by rfl⟩ : syracuseStep 2409059 = 3613589) B3613589
theorem B1606243 : Blo 1605001 1606243 := bstep (se 1 (by rfl) ⟨1204682, by rfl⟩ : syracuseStep 1606243 = 2409365) B2409365
theorem B1606259 : Blo 1605001 1606259 := bstep (se 1 (by rfl) ⟨1204694, by rfl⟩ : syracuseStep 1606259 = 2409389) B2409389
theorem B2409089 : Blo 1605001 2409089 := bstep (se 2 (by rfl) ⟨903408, by rfl⟩ : syracuseStep 2409089 = 1806817) B1806817
theorem B1606275 : Blo 1605001 1606275 := bstep (se 1 (by rfl) ⟨1204706, by rfl⟩ : syracuseStep 1606275 = 2409413) B2409413
theorem B2409107 : Blo 1605001 2409107 := bstep (se 1 (by rfl) ⟨1806830, by rfl⟩ : syracuseStep 2409107 = 3613661) B3613661
theorem B1606291 : Blo 1605001 1606291 := bstep (se 1 (by rfl) ⟨1204718, by rfl⟩ : syracuseStep 1606291 = 2409437) B2409437
theorem B1606307 : Blo 1605001 1606307 := bstep (se 1 (by rfl) ⟨1204730, by rfl⟩ : syracuseStep 1606307 = 2409461) B2409461
theorem B2409137 : Blo 1605001 2409137 := bstep (se 2 (by rfl) ⟨903426, by rfl⟩ : syracuseStep 2409137 = 1806853) B1806853
theorem B1606323 : Blo 1605001 1606323 := bstep (se 1 (by rfl) ⟨1204742, by rfl⟩ : syracuseStep 1606323 = 2409485) B2409485
theorem B3048131 : Blo 1605001 3048131 := bstep (se 1 (by rfl) ⟨2286098, by rfl⟩ : syracuseStep 3048131 = 4572197) B4572197
theorem B2409155 : Blo 1605001 2409155 := bstep (se 1 (by rfl) ⟨1806866, by rfl⟩ : syracuseStep 2409155 = 3613733) B3613733
theorem B1606339 : Blo 1605001 1606339 := bstep (se 1 (by rfl) ⟨1204754, by rfl⟩ : syracuseStep 1606339 = 2409509) B2409509
theorem B1606355 : Blo 1605001 1606355 := bstep (se 1 (by rfl) ⟨1204766, by rfl⟩ : syracuseStep 1606355 = 2409533) B2409533
theorem B2409185 : Blo 1605001 2409185 := bstep (se 2 (by rfl) ⟨903444, by rfl⟩ : syracuseStep 2409185 = 1806889) B1806889
theorem B1606371 : Blo 1605001 1606371 := bstep (se 1 (by rfl) ⟨1204778, by rfl⟩ : syracuseStep 1606371 = 2409557) B2409557
theorem B5497571 : Blo 1605001 5497571 := bstep (se 1 (by rfl) ⟨4123178, by rfl⟩ : syracuseStep 5497571 = 8246357) B8246357
theorem B2409203 : Blo 1605001 2409203 := bstep (se 1 (by rfl) ⟨1806902, by rfl⟩ : syracuseStep 2409203 = 3613805) B3613805
theorem B1606387 : Blo 1605001 1606387 := bstep (se 1 (by rfl) ⟨1204790, by rfl⟩ : syracuseStep 1606387 = 2409581) B2409581
theorem B4064003 : Blo 1605001 4064003 := bstep (se 1 (by rfl) ⟨3048002, by rfl⟩ : syracuseStep 4064003 = 6096005) B6096005
theorem B1606403 : Blo 1605001 1606403 := bstep (se 1 (by rfl) ⟨1204802, by rfl⟩ : syracuseStep 1606403 = 2409605) B2409605
theorem B8798989 : Blo 1605001 8798989 := bstep (se 3 (by rfl) ⟨1649810, by rfl⟩ : syracuseStep 8798989 = 3299621) B3299621
theorem B2409233 : Blo 1605001 2409233 := bstep (se 2 (by rfl) ⟨903462, by rfl⟩ : syracuseStep 2409233 = 1806925) B1806925
theorem B1606419 : Blo 1605001 1606419 := bstep (se 1 (by rfl) ⟨1204814, by rfl⟩ : syracuseStep 1606419 = 2409629) B2409629
theorem B2409251 : Blo 1605001 2409251 := bstep (se 1 (by rfl) ⟨1806938, by rfl⟩ : syracuseStep 2409251 = 3613877) B3613877
theorem B1606435 : Blo 1605001 1606435 := bstep (se 1 (by rfl) ⟨1204826, by rfl⟩ : syracuseStep 1606435 = 2409653) B2409653
theorem B5145389 : Blo 1605001 5145389 := bstep (se 3 (by rfl) ⟨964760, by rfl⟩ : syracuseStep 5145389 = 1929521) B1929521
theorem B1606451 : Blo 1605001 1606451 := bstep (se 1 (by rfl) ⟨1204838, by rfl⟩ : syracuseStep 1606451 = 2409677) B2409677
theorem B2409281 : Blo 1605001 2409281 := bstep (se 2 (by rfl) ⟨903480, by rfl⟩ : syracuseStep 2409281 = 1806961) B1806961
theorem B1606467 : Blo 1605001 1606467 := bstep (se 1 (by rfl) ⟨1204850, by rfl⟩ : syracuseStep 1606467 = 2409701) B2409701
theorem B2573137 : Blo 1605001 2573137 := bstep (se 2 (by rfl) ⟨964926, by rfl⟩ : syracuseStep 2573137 = 1929853) B1929853
theorem B2409299 : Blo 1605001 2409299 := bstep (se 1 (by rfl) ⟨1806974, by rfl⟩ : syracuseStep 2409299 = 3613949) B3613949
theorem B1606483 : Blo 1605001 1606483 := bstep (se 1 (by rfl) ⟨1204862, by rfl⟩ : syracuseStep 1606483 = 2409725) B2409725
theorem B1606499 : Blo 1605001 1606499 := bstep (se 1 (by rfl) ⟨1204874, by rfl⟩ : syracuseStep 1606499 = 2409749) B2409749
theorem B3613553 : Blo 1605001 3613553 := bstep (se 2 (by rfl) ⟨1355082, by rfl⟩ : syracuseStep 3613553 = 2710165) B2710165
theorem B2409329 : Blo 1605001 2409329 := bstep (se 2 (by rfl) ⟨903498, by rfl⟩ : syracuseStep 2409329 = 1806997) B1806997
theorem B1606515 : Blo 1605001 1606515 := bstep (se 1 (by rfl) ⟨1204886, by rfl⟩ : syracuseStep 1606515 = 2409773) B2409773
theorem B3613571 : Blo 1605001 3613571 := bstep (se 1 (by rfl) ⟨2710178, by rfl⟩ : syracuseStep 3613571 = 5420357) B5420357
theorem B2409347 : Blo 1605001 2409347 := bstep (se 1 (by rfl) ⟨1807010, by rfl⟩ : syracuseStep 2409347 = 3614021) B3614021
theorem B1606531 : Blo 1605001 1606531 := bstep (se 1 (by rfl) ⟨1204898, by rfl⟩ : syracuseStep 1606531 = 2409797) B2409797
theorem B1606547 : Blo 1605001 1606547 := bstep (se 1 (by rfl) ⟨1204910, by rfl⟩ : syracuseStep 1606547 = 2409821) B2409821
theorem B2409377 : Blo 1605001 2409377 := bstep (se 2 (by rfl) ⟨903516, by rfl⟩ : syracuseStep 2409377 = 1807033) B1807033
theorem B1606563 : Blo 1605001 1606563 := bstep (se 1 (by rfl) ⟨1204922, by rfl⟩ : syracuseStep 1606563 = 2409845) B2409845
theorem B2409395 : Blo 1605001 2409395 := bstep (se 1 (by rfl) ⟨1807046, by rfl⟩ : syracuseStep 2409395 = 3614093) B3614093
theorem B1606579 : Blo 1605001 1606579 := bstep (se 1 (by rfl) ⟨1204934, by rfl⟩ : syracuseStep 1606579 = 2409869) B2409869
theorem B4064195 : Blo 1605001 4064195 := bstep (se 1 (by rfl) ⟨3048146, by rfl⟩ : syracuseStep 4064195 = 6096293) B6096293
theorem B1606595 : Blo 1605001 1606595 := bstep (se 1 (by rfl) ⟨1204946, by rfl⟩ : syracuseStep 1606595 = 2409893) B2409893
theorem B2409425 : Blo 1605001 2409425 := bstep (se 2 (by rfl) ⟨903534, by rfl⟩ : syracuseStep 2409425 = 1807069) B1807069
theorem B2474963 : Blo 1605001 2474963 := bstep (se 1 (by rfl) ⟨1856222, by rfl⟩ : syracuseStep 2474963 = 3712445) B3712445
theorem B1606611 : Blo 1605001 1606611 := bstep (se 1 (by rfl) ⟨1204958, by rfl⟩ : syracuseStep 1606611 = 2409917) B2409917
theorem B2409443 : Blo 1605001 2409443 := bstep (se 1 (by rfl) ⟨1807082, by rfl⟩ : syracuseStep 2409443 = 3614165) B3614165
theorem B1606627 : Blo 1605001 1606627 := bstep (se 1 (by rfl) ⟨1204970, by rfl⟩ : syracuseStep 1606627 = 2409941) B2409941
theorem B2286577 : Blo 1605001 2286577 := bstep (se 2 (by rfl) ⟨857466, by rfl⟩ : syracuseStep 2286577 = 1714933) B1714933
theorem B1606643 : Blo 1605001 1606643 := bstep (se 1 (by rfl) ⟨1204982, by rfl⟩ : syracuseStep 1606643 = 2409965) B2409965
theorem B2409473 : Blo 1605001 2409473 := bstep (se 2 (by rfl) ⟨903552, by rfl⟩ : syracuseStep 2409473 = 1807105) B1807105
theorem B1606659 : Blo 1605001 1606659 := bstep (se 1 (by rfl) ⟨1204994, by rfl⟩ : syracuseStep 1606659 = 2409989) B2409989
theorem B9151501 : Blo 1605001 9151501 := bstep (se 3 (by rfl) ⟨1715906, by rfl⟩ : syracuseStep 9151501 = 3431813) B3431813
theorem B2409491 : Blo 1605001 2409491 := bstep (se 1 (by rfl) ⟨1807118, by rfl⟩ : syracuseStep 2409491 = 3614237) B3614237
theorem B1606675 : Blo 1605001 1606675 := bstep (se 1 (by rfl) ⟨1205006, by rfl⟩ : syracuseStep 1606675 = 2410013) B2410013
theorem B1606691 : Blo 1605001 1606691 := bstep (se 1 (by rfl) ⟨1205018, by rfl⟩ : syracuseStep 1606691 = 2410037) B2410037
theorem B2409521 : Blo 1605001 2409521 := bstep (se 2 (by rfl) ⟨903570, by rfl⟩ : syracuseStep 2409521 = 1807141) B1807141
theorem B1606707 : Blo 1605001 1606707 := bstep (se 1 (by rfl) ⟨1205030, by rfl⟩ : syracuseStep 1606707 = 2410061) B2410061
theorem B2409539 : Blo 1605001 2409539 := bstep (se 1 (by rfl) ⟨1807154, by rfl⟩ : syracuseStep 2409539 = 3614309) B3614309
theorem B1606723 : Blo 1605001 1606723 := bstep (se 1 (by rfl) ⟨1205042, by rfl⟩ : syracuseStep 1606723 = 2410085) B2410085
theorem B1606739 : Blo 1605001 1606739 := bstep (se 1 (by rfl) ⟨1205054, by rfl⟩ : syracuseStep 1606739 = 2410109) B2410109
theorem B2409569 : Blo 1605001 2409569 := bstep (se 2 (by rfl) ⟨903588, by rfl⟩ : syracuseStep 2409569 = 1807177) B1807177
theorem B9897059 : Blo 1605001 9897059 := bstep (se 1 (by rfl) ⟨7422794, by rfl⟩ : syracuseStep 9897059 = 14845589) B14845589
theorem B1606755 : Blo 1605001 1606755 := bstep (se 1 (by rfl) ⟨1205066, by rfl⟩ : syracuseStep 1606755 = 2410133) B2410133
theorem B2409587 : Blo 1605001 2409587 := bstep (se 1 (by rfl) ⟨1807190, by rfl⟩ : syracuseStep 2409587 = 3614381) B3614381
theorem B1606771 : Blo 1605001 1606771 := bstep (se 1 (by rfl) ⟨1205078, by rfl⟩ : syracuseStep 1606771 = 2410157) B2410157
theorem B2032771 : Blo 1605001 2032771 := bstep (se 1 (by rfl) ⟨1524578, by rfl⟩ : syracuseStep 2032771 = 3049157) B3049157
theorem B1606787 : Blo 1605001 1606787 := bstep (se 1 (by rfl) ⟨1205090, by rfl⟩ : syracuseStep 1606787 = 2410181) B2410181
theorem B3613841 : Blo 1605001 3613841 := bstep (se 2 (by rfl) ⟨1355190, by rfl⟩ : syracuseStep 3613841 = 2710381) B2710381
theorem B2409617 : Blo 1605001 2409617 := bstep (se 2 (by rfl) ⟨903606, by rfl⟩ : syracuseStep 2409617 = 1807213) B1807213
theorem B1606803 : Blo 1605001 1606803 := bstep (se 1 (by rfl) ⟨1205102, by rfl⟩ : syracuseStep 1606803 = 2410205) B2410205
theorem B3613859 : Blo 1605001 3613859 := bstep (se 1 (by rfl) ⟨2710394, by rfl⟩ : syracuseStep 3613859 = 5420789) B5420789
theorem B2409635 : Blo 1605001 2409635 := bstep (se 1 (by rfl) ⟨1807226, by rfl⟩ : syracuseStep 2409635 = 3614453) B3614453
theorem B1606819 : Blo 1605001 1606819 := bstep (se 1 (by rfl) ⟨1205114, by rfl⟩ : syracuseStep 1606819 = 2410229) B2410229
theorem B1606835 : Blo 1605001 1606835 := bstep (se 1 (by rfl) ⟨1205126, by rfl⟩ : syracuseStep 1606835 = 2410253) B2410253
theorem B2409665 : Blo 1605001 2409665 := bstep (se 2 (by rfl) ⟨903624, by rfl⟩ : syracuseStep 2409665 = 1807249) B1807249
theorem B1606851 : Blo 1605001 1606851 := bstep (se 1 (by rfl) ⟨1205138, by rfl⟩ : syracuseStep 1606851 = 2410277) B2410277
theorem B2409683 : Blo 1605001 2409683 := bstep (se 1 (by rfl) ⟨1807262, by rfl⟩ : syracuseStep 2409683 = 3614525) B3614525
theorem B1606867 : Blo 1605001 1606867 := bstep (se 1 (by rfl) ⟨1205150, by rfl⟩ : syracuseStep 1606867 = 2410301) B2410301
theorem B2032867 : Blo 1605001 2032867 := bstep (se 1 (by rfl) ⟨1524650, by rfl⟩ : syracuseStep 2032867 = 3049301) B3049301
theorem B58623203 : Blo 1605001 58623203 := bstep (se 1 (by rfl) ⟨43967402, by rfl⟩ : syracuseStep 58623203 = 87934805) B87934805
theorem B1606883 : Blo 1605001 1606883 := bstep (se 1 (by rfl) ⟨1205162, by rfl⟩ : syracuseStep 1606883 = 2410325) B2410325
theorem B2409713 : Blo 1605001 2409713 := bstep (se 2 (by rfl) ⟨903642, by rfl⟩ : syracuseStep 2409713 = 1807285) B1807285
theorem B1606899 : Blo 1605001 1606899 := bstep (se 1 (by rfl) ⟨1205174, by rfl⟩ : syracuseStep 1606899 = 2410349) B2410349
theorem B2409731 : Blo 1605001 2409731 := bstep (se 1 (by rfl) ⟨1807298, by rfl⟩ : syracuseStep 2409731 = 3614597) B3614597
theorem B1606915 : Blo 1605001 1606915 := bstep (se 1 (by rfl) ⟨1205186, by rfl⟩ : syracuseStep 1606915 = 2410373) B2410373
theorem B1606931 : Blo 1605001 1606931 := bstep (se 1 (by rfl) ⟨1205198, by rfl⟩ : syracuseStep 1606931 = 2410397) B2410397
theorem B2409761 : Blo 1605001 2409761 := bstep (se 2 (by rfl) ⟨903660, by rfl⟩ : syracuseStep 2409761 = 1807321) B1807321
theorem B1606947 : Blo 1605001 1606947 := bstep (se 1 (by rfl) ⟨1205210, by rfl⟩ : syracuseStep 1606947 = 2410421) B2410421
theorem B2409779 : Blo 1605001 2409779 := bstep (se 1 (by rfl) ⟨1807334, by rfl⟩ : syracuseStep 2409779 = 3614669) B3614669
theorem B1606963 : Blo 1605001 1606963 := bstep (se 1 (by rfl) ⟨1205222, by rfl⟩ : syracuseStep 1606963 = 2410445) B2410445
theorem B1606979 : Blo 1605001 1606979 := bstep (se 1 (by rfl) ⟨1205234, by rfl⟩ : syracuseStep 1606979 = 2410469) B2410469
theorem B2409809 : Blo 1605001 2409809 := bstep (se 2 (by rfl) ⟨903678, by rfl⟩ : syracuseStep 2409809 = 1807357) B1807357
theorem B1606995 : Blo 1605001 1606995 := bstep (se 1 (by rfl) ⟨1205246, by rfl⟩ : syracuseStep 1606995 = 2410493) B2410493
theorem B2409827 : Blo 1605001 2409827 := bstep (se 1 (by rfl) ⟨1807370, by rfl⟩ : syracuseStep 2409827 = 3614741) B3614741
theorem B2409857 : Blo 1605001 2409857 := bstep (se 2 (by rfl) ⟨903696, by rfl⟩ : syracuseStep 2409857 = 1807393) B1807393
theorem B2409875 : Blo 1605001 2409875 := bstep (se 1 (by rfl) ⟨1807406, by rfl⟩ : syracuseStep 2409875 = 3614813) B3614813
theorem B3614129 : Blo 1605001 3614129 := bstep (se 2 (by rfl) ⟨1355298, by rfl⟩ : syracuseStep 3614129 = 2710597) B2710597
theorem B2409905 : Blo 1605001 2409905 := bstep (se 2 (by rfl) ⟨903714, by rfl⟩ : syracuseStep 2409905 = 1807429) B1807429
theorem B3614147 : Blo 1605001 3614147 := bstep (se 1 (by rfl) ⟨2710610, by rfl⟩ : syracuseStep 3614147 = 5421221) B5421221
theorem B2409923 : Blo 1605001 2409923 := bstep (se 1 (by rfl) ⟨1807442, by rfl⟩ : syracuseStep 2409923 = 3614885) B3614885
theorem B2409953 : Blo 1605001 2409953 := bstep (se 2 (by rfl) ⟨903732, by rfl⟩ : syracuseStep 2409953 = 1807465) B1807465
theorem B8349169 : Blo 1605001 8349169 := bstep (se 2 (by rfl) ⟨3130938, by rfl⟩ : syracuseStep 8349169 = 6261877) B6261877
theorem B14853617 : Blo 1605001 14853617 := bstep (se 2 (by rfl) ⟨5570106, by rfl⟩ : syracuseStep 14853617 = 11140213) B11140213
theorem B2409971 : Blo 1605001 2409971 := bstep (se 1 (by rfl) ⟨1807478, by rfl⟩ : syracuseStep 2409971 = 3614957) B3614957
theorem B2410001 : Blo 1605001 2410001 := bstep (se 2 (by rfl) ⟨903750, by rfl⟩ : syracuseStep 2410001 = 1807501) B1807501
theorem B2410019 : Blo 1605001 2410019 := bstep (se 1 (by rfl) ⟨1807514, by rfl⟩ : syracuseStep 2410019 = 3615029) B3615029
theorem B2410049 : Blo 1605001 2410049 := bstep (se 2 (by rfl) ⟨903768, by rfl⟩ : syracuseStep 2410049 = 1807537) B1807537
theorem B2410067 : Blo 1605001 2410067 := bstep (se 1 (by rfl) ⟨1807550, by rfl⟩ : syracuseStep 2410067 = 3615101) B3615101
theorem B4884077 : Blo 1605001 4884077 := bstep (se 3 (by rfl) ⟨915764, by rfl⟩ : syracuseStep 4884077 = 1831529) B1831529
theorem B3049073 : Blo 1605001 3049073 := bstep (se 2 (by rfl) ⟨1143402, by rfl⟩ : syracuseStep 3049073 = 2286805) B2286805
theorem B2410097 : Blo 1605001 2410097 := bstep (se 2 (by rfl) ⟨903786, by rfl⟩ : syracuseStep 2410097 = 1807573) B1807573
theorem B3860099 : Blo 1605001 3860099 := bstep (se 1 (by rfl) ⟨2895074, by rfl⟩ : syracuseStep 3860099 = 5790149) B5790149
theorem B2410115 : Blo 1605001 2410115 := bstep (se 1 (by rfl) ⟨1807586, by rfl⟩ : syracuseStep 2410115 = 3615173) B3615173
theorem B2410145 : Blo 1605001 2410145 := bstep (se 2 (by rfl) ⟨903804, by rfl⟩ : syracuseStep 2410145 = 1807609) B1807609
theorem B2287283 : Blo 1605001 2287283 := bstep (se 1 (by rfl) ⟨1715462, by rfl⟩ : syracuseStep 2287283 = 3430925) B3430925
theorem B2410163 : Blo 1605001 2410163 := bstep (se 1 (by rfl) ⟨1807622, by rfl⟩ : syracuseStep 2410163 = 3615245) B3615245
theorem B4572881 : Blo 1605001 4572881 := bstep (se 2 (by rfl) ⟨1714830, by rfl⟩ : syracuseStep 4572881 = 3429661) B3429661
theorem B3614417 : Blo 1605001 3614417 := bstep (se 2 (by rfl) ⟨1355406, by rfl⟩ : syracuseStep 3614417 = 2710813) B2710813
theorem B2033363 : Blo 1605001 2033363 := bstep (se 1 (by rfl) ⟨1525022, by rfl⟩ : syracuseStep 2033363 = 3050045) B3050045
theorem B2410193 : Blo 1605001 2410193 := bstep (se 2 (by rfl) ⟨903822, by rfl⟩ : syracuseStep 2410193 = 1807645) B1807645
theorem B3614435 : Blo 1605001 3614435 := bstep (se 1 (by rfl) ⟨2710826, by rfl⟩ : syracuseStep 3614435 = 5421653) B5421653
theorem B2410211 : Blo 1605001 2410211 := bstep (se 1 (by rfl) ⟨1807658, by rfl⟩ : syracuseStep 2410211 = 3615317) B3615317
theorem B2574065 : Blo 1605001 2574065 := bstep (se 2 (by rfl) ⟨965274, by rfl⟩ : syracuseStep 2574065 = 1930549) B1930549
theorem B2410241 : Blo 1605001 2410241 := bstep (se 2 (by rfl) ⟨903840, by rfl⟩ : syracuseStep 2410241 = 1807681) B1807681
theorem B6686477 : Blo 1605001 6686477 := bstep (se 3 (by rfl) ⟨1253714, by rfl⟩ : syracuseStep 6686477 = 2507429) B2507429
theorem B2410259 : Blo 1605001 2410259 := bstep (se 1 (by rfl) ⟨1807694, by rfl⟩ : syracuseStep 2410259 = 3615389) B3615389
theorem B46909205 : Blo 1605001 46909205 := bstep (se 6 (by rfl) ⟨1099434, by rfl⟩ : syracuseStep 46909205 = 2198869) B2198869
theorem B1713955 : Blo 1605001 1713955 := bstep (se 1 (by rfl) ⟨1285466, by rfl⟩ : syracuseStep 1713955 = 2570933) B2570933
theorem B9266993 : Blo 1605001 9266993 := bstep (se 2 (by rfl) ⟨3475122, by rfl⟩ : syracuseStep 9266993 = 6950245) B6950245
theorem B2410289 : Blo 1605001 2410289 := bstep (se 2 (by rfl) ⟨903858, by rfl⟩ : syracuseStep 2410289 = 1807717) B1807717
theorem B3860291 : Blo 1605001 3860291 := bstep (se 1 (by rfl) ⟨2895218, by rfl⟩ : syracuseStep 3860291 = 5790437) B5790437
theorem B2410307 : Blo 1605001 2410307 := bstep (se 1 (by rfl) ⟨1807730, by rfl⟩ : syracuseStep 2410307 = 3615461) B3615461
theorem B2410337 : Blo 1605001 2410337 := bstep (se 2 (by rfl) ⟨903876, by rfl⟩ : syracuseStep 2410337 = 1807753) B1807753
theorem B4065137 : Blo 1605001 4065137 := bstep (se 2 (by rfl) ⟨1524426, by rfl⟩ : syracuseStep 4065137 = 3048853) B3048853
theorem B2410355 : Blo 1605001 2410355 := bstep (se 1 (by rfl) ⟨1807766, by rfl⟩ : syracuseStep 2410355 = 3615533) B3615533
theorem B2410385 : Blo 1605001 2410385 := bstep (se 2 (by rfl) ⟨903894, by rfl⟩ : syracuseStep 2410385 = 1807789) B1807789
theorem B4065187 : Blo 1605001 4065187 := bstep (se 1 (by rfl) ⟨3048890, by rfl⟩ : syracuseStep 4065187 = 6097781) B6097781
theorem B2410403 : Blo 1605001 2410403 := bstep (se 1 (by rfl) ⟨1807802, by rfl⟩ : syracuseStep 2410403 = 3615605) B3615605
theorem B2410433 : Blo 1605001 2410433 := bstep (se 2 (by rfl) ⟨903912, by rfl⟩ : syracuseStep 2410433 = 1807825) B1807825
theorem B2410451 : Blo 1605001 2410451 := bstep (se 1 (by rfl) ⟨1807838, by rfl⟩ : syracuseStep 2410451 = 3615677) B3615677
theorem B3614705 : Blo 1605001 3614705 := bstep (se 2 (by rfl) ⟨1355514, by rfl⟩ : syracuseStep 3614705 = 2711029) B2711029
theorem B2410481 : Blo 1605001 2410481 := bstep (se 2 (by rfl) ⟨903930, by rfl⟩ : syracuseStep 2410481 = 1807861) B1807861
theorem B3614723 : Blo 1605001 3614723 := bstep (se 1 (by rfl) ⟨2711042, by rfl⟩ : syracuseStep 3614723 = 5422085) B5422085
theorem B2410499 : Blo 1605001 2410499 := bstep (se 1 (by rfl) ⟨1807874, by rfl⟩ : syracuseStep 2410499 = 3615749) B3615749
theorem B5417009 : Blo 1605001 5417009 := bstep (se 2 (by rfl) ⟨2031378, by rfl⟩ : syracuseStep 5417009 = 4062757) B4062757
theorem B4065329 : Blo 1605001 4065329 := bstep (se 2 (by rfl) ⟨1524498, by rfl⟩ : syracuseStep 4065329 = 3048997) B3048997
theorem B2009171 : Blo 1605001 2009171 := bstep (se 1 (by rfl) ⟨1506878, by rfl⟩ : syracuseStep 2009171 = 3013757) B3013757
theorem B3860579 : Blo 1605001 3860579 := bstep (se 1 (by rfl) ⟨2895434, by rfl⟩ : syracuseStep 3860579 = 5790869) B5790869
theorem B1714403 : Blo 1605001 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B2894051 : Blo 1605001 2894051 := bstep (se 1 (by rfl) ⟨2170538, by rfl⟩ : syracuseStep 2894051 = 4341077) B4341077
theorem B3614993 : Blo 1605001 3614993 := bstep (se 2 (by rfl) ⟨1355622, by rfl⟩ : syracuseStep 3614993 = 2711245) B2711245
theorem B3615011 : Blo 1605001 3615011 := bstep (se 1 (by rfl) ⟨2711258, by rfl⟩ : syracuseStep 3615011 = 5422517) B5422517
theorem B2287921 : Blo 1605001 2287921 := bstep (se 2 (by rfl) ⟨857970, by rfl⟩ : syracuseStep 2287921 = 1715941) B1715941
theorem B8685893 : Blo 1605001 8685893 := bstep (se 4 (by rfl) ⟨814302, by rfl⟩ : syracuseStep 8685893 = 1628605) B1628605
theorem B6097265 : Blo 1605001 6097265 := bstep (se 2 (by rfl) ⟨2286474, by rfl⟩ : syracuseStep 6097265 = 4572949) B4572949
theorem B9275789 : Blo 1605001 9275789 := bstep (se 3 (by rfl) ⟨1739210, by rfl⟩ : syracuseStep 9275789 = 3478421) B3478421
theorem B2288035 : Blo 1605001 2288035 := bstep (se 1 (by rfl) ⟨1716026, by rfl⟩ : syracuseStep 2288035 = 3432053) B3432053
theorem B2935217 : Blo 1605001 2935217 := bstep (se 2 (by rfl) ⟨1100706, by rfl⟩ : syracuseStep 2935217 = 2201413) B2201413
theorem B3049969 : Blo 1605001 3049969 := bstep (se 2 (by rfl) ⟨1143738, by rfl⟩ : syracuseStep 3049969 = 2287477) B2287477
theorem B4885037 : Blo 1605001 4885037 := bstep (se 3 (by rfl) ⟨915944, by rfl⟩ : syracuseStep 4885037 = 1831889) B1831889
theorem B3615281 : Blo 1605001 3615281 := bstep (se 2 (by rfl) ⟨1355730, by rfl⟩ : syracuseStep 3615281 = 2711461) B2711461
theorem B3615299 : Blo 1605001 3615299 := bstep (se 1 (by rfl) ⟨2711474, by rfl⟩ : syracuseStep 3615299 = 5422949) B5422949
theorem B5417549 : Blo 1605001 5417549 := bstep (se 3 (by rfl) ⟨1015790, by rfl⟩ : syracuseStep 5417549 = 2031581) B2031581
theorem B7825997 : Blo 1605001 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B5417603 : Blo 1605001 5417603 := bstep (se 1 (by rfl) ⟨4063202, by rfl⟩ : syracuseStep 5417603 = 8126405) B8126405
theorem B4573837 : Blo 1605001 4573837 := bstep (se 3 (by rfl) ⟨857594, by rfl⟩ : syracuseStep 4573837 = 1715189) B1715189
theorem B3050129 : Blo 1605001 3050129 := bstep (se 2 (by rfl) ⟨1143798, by rfl⟩ : syracuseStep 3050129 = 2287597) B2287597
theorem B3615569 : Blo 1605001 3615569 := bstep (se 2 (by rfl) ⟨1355838, by rfl⟩ : syracuseStep 3615569 = 2711677) B2711677
theorem B3615587 : Blo 1605001 3615587 := bstep (se 1 (by rfl) ⟨2711690, by rfl⟩ : syracuseStep 3615587 = 5423381) B5423381
theorem B2607985 : Blo 1605001 2607985 := bstep (se 2 (by rfl) ⟨977994, by rfl⟩ : syracuseStep 2607985 = 1955989) B1955989
theorem B4574065 : Blo 1605001 4574065 := bstep (se 2 (by rfl) ⟨1715274, by rfl⟩ : syracuseStep 4574065 = 3430549) B3430549
theorem B5417873 : Blo 1605001 5417873 := bstep (se 2 (by rfl) ⟨2031702, by rfl⟩ : syracuseStep 5417873 = 4063405) B4063405
theorem B4017059 : Blo 1605001 4017059 := bstep (se 1 (by rfl) ⟨3012794, by rfl⟩ : syracuseStep 4017059 = 6025589) B6025589
theorem B5213123 : Blo 1605001 5213123 := bstep (se 1 (by rfl) ⟨3909842, by rfl⟩ : syracuseStep 5213123 = 7819685) B7819685
theorem B11570147 : Blo 1605001 11570147 := bstep (se 1 (by rfl) ⟨8677610, by rfl⟩ : syracuseStep 11570147 = 17355221) B17355221
theorem B4574225 : Blo 1605001 4574225 := bstep (se 2 (by rfl) ⟨1715334, by rfl⟩ : syracuseStep 4574225 = 3430669) B3430669
theorem B4066321 : Blo 1605001 4066321 := bstep (se 2 (by rfl) ⟨1524870, by rfl⟩ : syracuseStep 4066321 = 3049741) B3049741
theorem B3050531 : Blo 1605001 3050531 := bstep (se 1 (by rfl) ⟨2287898, by rfl⟩ : syracuseStep 3050531 = 4575797) B4575797
theorem B3664945 : Blo 1605001 3664945 := bstep (se 2 (by rfl) ⟨1374354, by rfl⟩ : syracuseStep 3664945 = 2748709) B2748709
theorem B12201029 : Blo 1605001 12201029 := bstep (se 4 (by rfl) ⟨1143846, by rfl⟩ : syracuseStep 12201029 = 2287693) B2287693
theorem B4574339 : Blo 1605001 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B2116819 : Blo 1605001 2116819 := bstep (se 1 (by rfl) ⟨1587614, by rfl⟩ : syracuseStep 2116819 = 3175229) B3175229
theorem B13200653 : Blo 1605001 13200653 := bstep (se 3 (by rfl) ⟨2475122, by rfl⟩ : syracuseStep 13200653 = 4950245) B4950245
theorem B4066595 : Blo 1605001 4066595 := bstep (se 1 (by rfl) ⟨3049946, by rfl⟩ : syracuseStep 4066595 = 6099893) B6099893
theorem B9145669 : Blo 1605001 9145669 := bstep (se 4 (by rfl) ⟨857406, by rfl⟩ : syracuseStep 9145669 = 1714813) B1714813
theorem B1805683 : Blo 1605001 1805683 := bstep (se 1 (by rfl) ⟨1354262, by rfl⟩ : syracuseStep 1805683 = 2708525) B2708525
theorem B5418413 : Blo 1605001 5418413 := bstep (se 3 (by rfl) ⟨1015952, by rfl⟩ : syracuseStep 5418413 = 2031905) B2031905
theorem B8129969 : Blo 1605001 8129969 := bstep (se 2 (by rfl) ⟨3048738, by rfl⟩ : syracuseStep 8129969 = 6097477) B6097477
theorem B6860209 : Blo 1605001 6860209 := bstep (se 2 (by rfl) ⟨2572578, by rfl⟩ : syracuseStep 6860209 = 5145157) B5145157
theorem B5418467 : Blo 1605001 5418467 := bstep (se 1 (by rfl) ⟨4063850, by rfl⟩ : syracuseStep 5418467 = 8127701) B8127701
theorem B4066787 : Blo 1605001 4066787 := bstep (se 1 (by rfl) ⟨3050090, by rfl⟩ : syracuseStep 4066787 = 6100181) B6100181
theorem B1805827 : Blo 1605001 1805827 := bstep (se 1 (by rfl) ⟨1354370, by rfl⟩ : syracuseStep 1805827 = 2708741) B2708741
theorem B1715779 : Blo 1605001 1715779 := bstep (se 1 (by rfl) ⟨1286834, by rfl⟩ : syracuseStep 1715779 = 2573669) B2573669
theorem B1928819 : Blo 1605001 1928819 := bstep (se 1 (by rfl) ⟨1446614, by rfl⟩ : syracuseStep 1928819 = 2893229) B2893229
theorem B10284677 : Blo 1605001 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B1805971 : Blo 1605001 1805971 := bstep (se 1 (by rfl) ⟨1354478, by rfl⟩ : syracuseStep 1805971 = 2708957) B2708957
theorem B3255985 : Blo 1605001 3255985 := bstep (se 2 (by rfl) ⟨1220994, by rfl⟩ : syracuseStep 3255985 = 2441989) B2441989
theorem B39587525 : Blo 1605001 39587525 := bstep (se 4 (by rfl) ⟨3711330, by rfl⟩ : syracuseStep 39587525 = 7422661) B7422661
theorem B5418737 : Blo 1605001 5418737 := bstep (se 2 (by rfl) ⟨2032026, by rfl⟩ : syracuseStep 5418737 = 4064053) B4064053
theorem B1806115 : Blo 1605001 1806115 := bstep (se 1 (by rfl) ⟨1354586, by rfl⟩ : syracuseStep 1806115 = 2709173) B2709173
theorem B6098723 : Blo 1605001 6098723 := bstep (se 1 (by rfl) ⟨4574042, by rfl⟩ : syracuseStep 6098723 = 9148085) B9148085
theorem B1806259 : Blo 1605001 1806259 := bstep (se 1 (by rfl) ⟨1354694, by rfl⟩ : syracuseStep 1806259 = 2709389) B2709389
theorem B8802317 : Blo 1605001 8802317 := bstep (se 3 (by rfl) ⟨1650434, by rfl⟩ : syracuseStep 8802317 = 3300869) B3300869
theorem B1806403 : Blo 1605001 1806403 := bstep (se 1 (by rfl) ⟨1354802, by rfl⟩ : syracuseStep 1806403 = 2709605) B2709605
theorem B2748497 : Blo 1605001 2748497 := bstep (se 2 (by rfl) ⟨1030686, by rfl⟩ : syracuseStep 2748497 = 2061373) B2061373
theorem B11571299 : Blo 1605001 11571299 := bstep (se 1 (by rfl) ⟨8678474, by rfl⟩ : syracuseStep 11571299 = 17356949) B17356949
theorem B4575341 : Blo 1605001 4575341 := bstep (se 3 (by rfl) ⟨857876, by rfl⟩ : syracuseStep 4575341 = 1715753) B1715753
theorem B10293389 : Blo 1605001 10293389 := bstep (se 3 (by rfl) ⟨1930010, by rfl⟩ : syracuseStep 10293389 = 3860021) B3860021
theorem B1806547 : Blo 1605001 1806547 := bstep (se 1 (by rfl) ⟨1354910, by rfl⟩ : syracuseStep 1806547 = 2709821) B2709821
theorem B5419277 : Blo 1605001 5419277 := bstep (se 3 (by rfl) ⟨1016114, by rfl⟩ : syracuseStep 5419277 = 2032229) B2032229
theorem B4575523 : Blo 1605001 4575523 := bstep (se 1 (by rfl) ⟨3431642, by rfl⟩ : syracuseStep 4575523 = 6863285) B6863285
theorem B5493041 : Blo 1605001 5493041 := bstep (se 2 (by rfl) ⟨2059890, by rfl⟩ : syracuseStep 5493041 = 4119781) B4119781
theorem B5419331 : Blo 1605001 5419331 := bstep (se 1 (by rfl) ⟨4064498, by rfl⟩ : syracuseStep 5419331 = 8128997) B8128997
theorem B14094691 : Blo 1605001 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B1806691 : Blo 1605001 1806691 := bstep (se 1 (by rfl) ⟨1355018, by rfl⟩ : syracuseStep 1806691 = 2710037) B2710037
theorem B4575683 : Blo 1605001 4575683 := bstep (se 1 (by rfl) ⟨3431762, by rfl⟩ : syracuseStep 4575683 = 6863525) B6863525
theorem B13717957 : Blo 1605001 13717957 := bstep (se 4 (by rfl) ⟨1286058, by rfl⟩ : syracuseStep 13717957 = 2572117) B2572117
theorem B1806835 : Blo 1605001 1806835 := bstep (se 1 (by rfl) ⟨1355126, by rfl⟩ : syracuseStep 1806835 = 2710253) B2710253
theorem B3428867 : Blo 1605001 3428867 := bstep (se 1 (by rfl) ⟨2571650, by rfl⟩ : syracuseStep 3428867 = 5143301) B5143301
theorem B6509105 : Blo 1605001 6509105 := bstep (se 2 (by rfl) ⟨2440914, by rfl⟩ : syracuseStep 6509105 = 4881829) B4881829
theorem B5419601 : Blo 1605001 5419601 := bstep (se 2 (by rfl) ⟨2032350, by rfl⟩ : syracuseStep 5419601 = 4064701) B4064701
theorem B1806979 : Blo 1605001 1806979 := bstep (se 1 (by rfl) ⟨1355234, by rfl⟩ : syracuseStep 1806979 = 2710469) B2710469
theorem B8245901 : Blo 1605001 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B31707845 : Blo 1605001 31707845 := bstep (se 4 (by rfl) ⟨2972610, by rfl⟩ : syracuseStep 31707845 = 5945221) B5945221
theorem B18805445 : Blo 1605001 18805445 := bstep (se 4 (by rfl) ⟨1763010, by rfl⟩ : syracuseStep 18805445 = 3526021) B3526021
theorem B6099725 : Blo 1605001 6099725 := bstep (se 3 (by rfl) ⟨1143698, by rfl⟩ : syracuseStep 6099725 = 2287397) B2287397
theorem B1807123 : Blo 1605001 1807123 := bstep (se 1 (by rfl) ⟨1355342, by rfl⟩ : syracuseStep 1807123 = 2710685) B2710685
theorem B9769805 : Blo 1605001 9769805 := bstep (se 3 (by rfl) ⟨1831838, by rfl⟩ : syracuseStep 9769805 = 3663677) B3663677
theorem B8131427 : Blo 1605001 8131427 := bstep (se 1 (by rfl) ⟨6098570, by rfl⟩ : syracuseStep 8131427 = 12197141) B12197141
theorem B1807267 : Blo 1605001 1807267 := bstep (se 1 (by rfl) ⟨1355450, by rfl⟩ : syracuseStep 1807267 = 2710901) B2710901
theorem B13726705 : Blo 1605001 13726705 := bstep (se 2 (by rfl) ⟨5147514, by rfl⟩ : syracuseStep 13726705 = 10295029) B10295029
theorem B1807411 : Blo 1605001 1807411 := bstep (se 1 (by rfl) ⟨1355558, by rfl⟩ : syracuseStep 1807411 = 2711117) B2711117
theorem B2708545 : Blo 1605001 2708545 := bstep (se 2 (by rfl) ⟨1015704, by rfl⟩ : syracuseStep 2708545 = 2031409) B2031409
theorem B2708579 : Blo 1605001 2708579 := bstep (se 1 (by rfl) ⟨2031434, by rfl⟩ : syracuseStep 2708579 = 4062869) B4062869
theorem B14652515 : Blo 1605001 14652515 := bstep (se 1 (by rfl) ⟨10989386, by rfl⟩ : syracuseStep 14652515 = 21978773) B21978773
theorem B5420141 : Blo 1605001 5420141 := bstep (se 3 (by rfl) ⟨1016276, by rfl⟩ : syracuseStep 5420141 = 2032553) B2032553
theorem B5420195 : Blo 1605001 5420195 := bstep (se 1 (by rfl) ⟨4065146, by rfl⟩ : syracuseStep 5420195 = 8130293) B8130293
theorem B1807555 : Blo 1605001 1807555 := bstep (se 1 (by rfl) ⟨1355666, by rfl⟩ : syracuseStep 1807555 = 2711333) B2711333
theorem B2708707 : Blo 1605001 2708707 := bstep (se 1 (by rfl) ⟨2031530, by rfl⟩ : syracuseStep 2708707 = 4063061) B4063061
theorem B9147653 : Blo 1605001 9147653 := bstep (se 4 (by rfl) ⟨857592, by rfl⟩ : syracuseStep 9147653 = 1715185) B1715185
theorem B1807699 : Blo 1605001 1807699 := bstep (se 1 (by rfl) ⟨1355774, by rfl⟩ : syracuseStep 1807699 = 2711549) B2711549
theorem B2708849 : Blo 1605001 2708849 := bstep (se 2 (by rfl) ⟨1015818, by rfl⟩ : syracuseStep 2708849 = 2031637) B2031637
theorem B5420465 : Blo 1605001 5420465 := bstep (se 2 (by rfl) ⟨2032674, by rfl⟩ : syracuseStep 5420465 = 4065349) B4065349
theorem B1627571 : Blo 1605001 1627571 := bstep (se 1 (by rfl) ⟨1220678, by rfl⟩ : syracuseStep 1627571 = 2441357) B2441357
theorem B1807843 : Blo 1605001 1807843 := bstep (se 1 (by rfl) ⟨1355882, by rfl⟩ : syracuseStep 1807843 = 2711765) B2711765
theorem B2708977 : Blo 1605001 2708977 := bstep (se 2 (by rfl) ⟨1015866, by rfl⟩ : syracuseStep 2708977 = 2031733) B2031733
theorem B2709011 : Blo 1605001 2709011 := bstep (se 1 (by rfl) ⟨2031758, by rfl⟩ : syracuseStep 2709011 = 4063517) B4063517
theorem B8132237 : Blo 1605001 8132237 := bstep (se 3 (by rfl) ⟨1524794, by rfl⟩ : syracuseStep 8132237 = 3049589) B3049589
theorem B2709139 : Blo 1605001 2709139 := bstep (se 1 (by rfl) ⟨2031854, by rfl⟩ : syracuseStep 2709139 = 4063709) B4063709
theorem B3430097 : Blo 1605001 3430097 := bstep (se 2 (by rfl) ⟨1286286, by rfl⟩ : syracuseStep 3430097 = 2572573) B2572573
theorem B5142275 : Blo 1605001 5142275 := bstep (se 1 (by rfl) ⟨3856706, by rfl⟩ : syracuseStep 5142275 = 7713413) B7713413
theorem B2709281 : Blo 1605001 2709281 := bstep (se 2 (by rfl) ⟨1015980, by rfl⟩ : syracuseStep 2709281 = 2031961) B2031961
theorem B12195683 : Blo 1605001 12195683 := bstep (se 1 (by rfl) ⟨9146762, by rfl⟩ : syracuseStep 12195683 = 18293525) B18293525
theorem B6510449 : Blo 1605001 6510449 := bstep (se 2 (by rfl) ⟨2441418, by rfl⟩ : syracuseStep 6510449 = 4882837) B4882837
theorem B2709409 : Blo 1605001 2709409 := bstep (se 2 (by rfl) ⟨1016028, by rfl⟩ : syracuseStep 2709409 = 2032057) B2032057
theorem B2709443 : Blo 1605001 2709443 := bstep (se 1 (by rfl) ⟨2032082, by rfl⟩ : syracuseStep 2709443 = 4064165) B4064165
theorem B5421005 : Blo 1605001 5421005 := bstep (se 3 (by rfl) ⟨1016438, by rfl⟩ : syracuseStep 5421005 = 2032877) B2032877
theorem B1882067 : Blo 1605001 1882067 := bstep (se 1 (by rfl) ⟨1411550, by rfl⟩ : syracuseStep 1882067 = 2823101) B2823101
theorem B6510577 : Blo 1605001 6510577 := bstep (se 2 (by rfl) ⟨2441466, by rfl⟩ : syracuseStep 6510577 = 4882933) B4882933
theorem B5421059 : Blo 1605001 5421059 := bstep (se 1 (by rfl) ⟨4065794, by rfl⟩ : syracuseStep 5421059 = 8131589) B8131589
theorem B4339757 : Blo 1605001 4339757 := bstep (se 3 (by rfl) ⟨813704, by rfl⟩ : syracuseStep 4339757 = 1627409) B1627409
theorem B2709571 : Blo 1605001 2709571 := bstep (se 1 (by rfl) ⟨2032178, by rfl⟩ : syracuseStep 2709571 = 4064357) B4064357
theorem B2709713 : Blo 1605001 2709713 := bstep (se 2 (by rfl) ⟨1016142, by rfl⟩ : syracuseStep 2709713 = 2032285) B2032285
theorem B5421329 : Blo 1605001 5421329 := bstep (se 2 (by rfl) ⟨2032998, by rfl⟩ : syracuseStep 5421329 = 4065997) B4065997
theorem B17357125 : Blo 1605001 17357125 := bstep (se 4 (by rfl) ⟨1627230, by rfl⟩ : syracuseStep 17357125 = 3254461) B3254461
theorem B2709841 : Blo 1605001 2709841 := bstep (se 2 (by rfl) ⟨1016190, by rfl⟩ : syracuseStep 2709841 = 2032381) B2032381
theorem B2709875 : Blo 1605001 2709875 := bstep (se 1 (by rfl) ⟨2032406, by rfl⟩ : syracuseStep 2709875 = 4064813) B4064813
theorem B2710003 : Blo 1605001 2710003 := bstep (se 1 (by rfl) ⟨2032502, by rfl⟩ : syracuseStep 2710003 = 4065005) B4065005
theorem B3430993 : Blo 1605001 3430993 := bstep (se 2 (by rfl) ⟨1286622, by rfl⟩ : syracuseStep 3430993 = 2573245) B2573245
theorem B3431011 : Blo 1605001 3431011 := bstep (se 1 (by rfl) ⟨2573258, by rfl⟩ : syracuseStep 3431011 = 5146517) B5146517
theorem B2710145 : Blo 1605001 2710145 := bstep (se 2 (by rfl) ⟨1016304, by rfl⟩ : syracuseStep 2710145 = 2032609) B2032609
theorem B3611267 : Blo 1605001 3611267 := bstep (se 1 (by rfl) ⟨2708450, by rfl⟩ : syracuseStep 3611267 = 5416901) B5416901
theorem B9771653 : Blo 1605001 9771653 := bstep (se 4 (by rfl) ⟨916092, by rfl⟩ : syracuseStep 9771653 = 1832185) B1832185
theorem B2169571 : Blo 1605001 2169571 := bstep (se 1 (by rfl) ⟨1627178, by rfl⟩ : syracuseStep 2169571 = 3254357) B3254357
theorem B2710273 : Blo 1605001 2710273 := bstep (se 2 (by rfl) ⟨1016352, by rfl⟩ : syracuseStep 2710273 = 2032705) B2032705
theorem B2571041 : Blo 1605001 2571041 := bstep (se 2 (by rfl) ⟨964140, by rfl⟩ : syracuseStep 2571041 = 1928281) B1928281
theorem B2710307 : Blo 1605001 2710307 := bstep (se 1 (by rfl) ⟨2032730, by rfl⟩ : syracuseStep 2710307 = 4065461) B4065461
theorem B5421869 : Blo 1605001 5421869 := bstep (se 3 (by rfl) ⟨1016600, by rfl⟩ : syracuseStep 5421869 = 2033201) B2033201
theorem B4340557 : Blo 1605001 4340557 := bstep (se 3 (by rfl) ⟨813854, by rfl⟩ : syracuseStep 4340557 = 1627709) B1627709
theorem B5421923 : Blo 1605001 5421923 := bstep (se 1 (by rfl) ⟨4066442, by rfl⟩ : syracuseStep 5421923 = 8132885) B8132885
theorem B3611537 : Blo 1605001 3611537 := bstep (se 2 (by rfl) ⟨1354326, by rfl⟩ : syracuseStep 3611537 = 2708653) B2708653
theorem B3611555 : Blo 1605001 3611555 := bstep (se 1 (by rfl) ⟨2708666, by rfl⟩ : syracuseStep 3611555 = 5417333) B5417333
theorem B2710435 : Blo 1605001 2710435 := bstep (se 1 (by rfl) ⟨2032826, by rfl⟩ : syracuseStep 2710435 = 4065653) B4065653
theorem B6863885 : Blo 1605001 6863885 := bstep (se 3 (by rfl) ⟨1286978, by rfl⟩ : syracuseStep 6863885 = 2573957) B2573957
theorem B4340785 : Blo 1605001 4340785 := bstep (se 2 (by rfl) ⟨1627794, by rfl⟩ : syracuseStep 4340785 = 3255589) B3255589
theorem B2710577 : Blo 1605001 2710577 := bstep (se 2 (by rfl) ⟨1016466, by rfl⟩ : syracuseStep 2710577 = 2032933) B2032933
theorem B5143619 : Blo 1605001 5143619 := bstep (se 1 (by rfl) ⟨3857714, by rfl⟩ : syracuseStep 5143619 = 7715429) B7715429
theorem B2407505 : Blo 1605001 2407505 := bstep (se 2 (by rfl) ⟨902814, by rfl⟩ : syracuseStep 2407505 = 1805629) B1805629
theorem B2407523 : Blo 1605001 2407523 := bstep (se 1 (by rfl) ⟨1805642, by rfl⟩ : syracuseStep 2407523 = 3611285) B3611285
theorem B10288241 : Blo 1605001 10288241 := bstep (se 2 (by rfl) ⟨3858090, by rfl⟩ : syracuseStep 10288241 = 7716181) B7716181
theorem B5422193 : Blo 1605001 5422193 := bstep (se 2 (by rfl) ⟨2033322, by rfl⟩ : syracuseStep 5422193 = 4066645) B4066645
theorem B2407553 : Blo 1605001 2407553 := bstep (se 2 (by rfl) ⟨902832, by rfl⟩ : syracuseStep 2407553 = 1805665) B1805665
theorem B2407571 : Blo 1605001 2407571 := bstep (se 1 (by rfl) ⟨1805678, by rfl⟩ : syracuseStep 2407571 = 3611357) B3611357
theorem B2407601 : Blo 1605001 2407601 := bstep (se 2 (by rfl) ⟨902850, by rfl⟩ : syracuseStep 2407601 = 1805701) B1805701
theorem B3611825 : Blo 1605001 3611825 := bstep (se 2 (by rfl) ⟨1354434, by rfl⟩ : syracuseStep 3611825 = 2708869) B2708869
theorem B2710705 : Blo 1605001 2710705 := bstep (se 2 (by rfl) ⟨1016514, by rfl⟩ : syracuseStep 2710705 = 2033029) B2033029
theorem B18791605 : Blo 1605001 18791605 := bstep (se 5 (by rfl) ⟨880856, by rfl⟩ : syracuseStep 18791605 = 1761713) B1761713
theorem B2407619 : Blo 1605001 2407619 := bstep (se 1 (by rfl) ⟨1805714, by rfl⟩ : syracuseStep 2407619 = 3611429) B3611429
theorem B3611843 : Blo 1605001 3611843 := bstep (se 1 (by rfl) ⟨2708882, by rfl⟩ : syracuseStep 3611843 = 5417765) B5417765
theorem B2710739 : Blo 1605001 2710739 := bstep (se 1 (by rfl) ⟨2033054, by rfl⟩ : syracuseStep 2710739 = 4066109) B4066109
theorem B2407649 : Blo 1605001 2407649 := bstep (se 2 (by rfl) ⟨902868, by rfl⟩ : syracuseStep 2407649 = 1805737) B1805737
theorem B2407667 : Blo 1605001 2407667 := bstep (se 1 (by rfl) ⟨1805750, by rfl⟩ : syracuseStep 2407667 = 3611501) B3611501
theorem B2407697 : Blo 1605001 2407697 := bstep (se 2 (by rfl) ⟨902886, by rfl⟩ : syracuseStep 2407697 = 1805773) B1805773
theorem B2407715 : Blo 1605001 2407715 := bstep (se 1 (by rfl) ⟨1805786, by rfl⟩ : syracuseStep 2407715 = 3611573) B3611573
theorem B2407745 : Blo 1605001 2407745 := bstep (se 2 (by rfl) ⟨902904, by rfl⟩ : syracuseStep 2407745 = 1805809) B1805809
theorem B2407763 : Blo 1605001 2407763 := bstep (se 1 (by rfl) ⟨1805822, by rfl⟩ : syracuseStep 2407763 = 3611645) B3611645
theorem B2710867 : Blo 1605001 2710867 := bstep (se 1 (by rfl) ⟨2033150, by rfl⟩ : syracuseStep 2710867 = 4066301) B4066301
theorem B18292067 : Blo 1605001 18292067 := bstep (se 1 (by rfl) ⟨13719050, by rfl⟩ : syracuseStep 18292067 = 27438101) B27438101
theorem B2407793 : Blo 1605001 2407793 := bstep (se 2 (by rfl) ⟨902922, by rfl⟩ : syracuseStep 2407793 = 1805845) B1805845
theorem B2407811 : Blo 1605001 2407811 := bstep (se 1 (by rfl) ⟨1805858, by rfl⟩ : syracuseStep 2407811 = 3611717) B3611717
theorem B1605011 : Blo 1605001 1605011 := bstep (se 1 (by rfl) ⟨1203758, by rfl⟩ : syracuseStep 1605011 = 2407517) B2407517
theorem B2407841 : Blo 1605001 2407841 := bstep (se 2 (by rfl) ⟨902940, by rfl⟩ : syracuseStep 2407841 = 1805881) B1805881
theorem B1605027 : Blo 1605001 1605027 := bstep (se 1 (by rfl) ⟨1203770, by rfl⟩ : syracuseStep 1605027 = 2407541) B2407541
theorem B5496227 : Blo 1605001 5496227 := bstep (se 1 (by rfl) ⟨4122170, by rfl⟩ : syracuseStep 5496227 = 8244341) B8244341
theorem B1605043 : Blo 1605001 1605043 := bstep (se 1 (by rfl) ⟨1203782, by rfl⟩ : syracuseStep 1605043 = 2407565) B2407565
theorem B2407859 : Blo 1605001 2407859 := bstep (se 1 (by rfl) ⟨1805894, by rfl⟩ : syracuseStep 2407859 = 3611789) B3611789
theorem B1605059 : Blo 1605001 1605059 := bstep (se 1 (by rfl) ⟨1203794, by rfl⟩ : syracuseStep 1605059 = 2407589) B2407589
theorem B2407889 : Blo 1605001 2407889 := bstep (se 2 (by rfl) ⟨902958, by rfl⟩ : syracuseStep 2407889 = 1805917) B1805917
theorem B3612113 : Blo 1605001 3612113 := bstep (se 2 (by rfl) ⟨1354542, by rfl⟩ : syracuseStep 3612113 = 2709085) B2709085
theorem B1605075 : Blo 1605001 1605075 := bstep (se 1 (by rfl) ⟨1203806, by rfl⟩ : syracuseStep 1605075 = 2407613) B2407613
theorem B2711009 : Blo 1605001 2711009 := bstep (se 2 (by rfl) ⟨1016628, by rfl⟩ : syracuseStep 2711009 = 2033257) B2033257
theorem B1605091 : Blo 1605001 1605091 := bstep (se 1 (by rfl) ⟨1203818, by rfl⟩ : syracuseStep 1605091 = 2407637) B2407637
theorem B2407907 : Blo 1605001 2407907 := bstep (se 1 (by rfl) ⟨1805930, by rfl⟩ : syracuseStep 2407907 = 3611861) B3611861
theorem B3612131 : Blo 1605001 3612131 := bstep (se 1 (by rfl) ⟨2709098, by rfl⟩ : syracuseStep 3612131 = 5418197) B5418197
theorem B6856177 : Blo 1605001 6856177 := bstep (se 2 (by rfl) ⟨2571066, by rfl⟩ : syracuseStep 6856177 = 5142133) B5142133
theorem B1605107 : Blo 1605001 1605107 := bstep (se 1 (by rfl) ⟨1203830, by rfl⟩ : syracuseStep 1605107 = 2407661) B2407661
theorem B2407937 : Blo 1605001 2407937 := bstep (se 2 (by rfl) ⟨902976, by rfl⟩ : syracuseStep 2407937 = 1805953) B1805953
theorem B1605123 : Blo 1605001 1605123 := bstep (se 1 (by rfl) ⟨1203842, by rfl⟩ : syracuseStep 1605123 = 2407685) B2407685
theorem B6094349 : Blo 1605001 6094349 := bstep (se 3 (by rfl) ⟨1142690, by rfl⟩ : syracuseStep 6094349 = 2285381) B2285381
theorem B4062737 : Blo 1605001 4062737 := bstep (se 2 (by rfl) ⟨1523526, by rfl⟩ : syracuseStep 4062737 = 3047053) B3047053
theorem B1605139 : Blo 1605001 1605139 := bstep (se 1 (by rfl) ⟨1203854, by rfl⟩ : syracuseStep 1605139 = 2407709) B2407709
theorem B2407955 : Blo 1605001 2407955 := bstep (se 1 (by rfl) ⟨1805966, by rfl⟩ : syracuseStep 2407955 = 3611933) B3611933
theorem B1605155 : Blo 1605001 1605155 := bstep (se 1 (by rfl) ⟨1203866, by rfl⟩ : syracuseStep 1605155 = 2407733) B2407733
theorem B2407985 : Blo 1605001 2407985 := bstep (se 2 (by rfl) ⟨902994, by rfl⟩ : syracuseStep 2407985 = 1805989) B1805989
theorem B1605171 : Blo 1605001 1605171 := bstep (se 1 (by rfl) ⟨1203878, by rfl⟩ : syracuseStep 1605171 = 2407757) B2407757
theorem B1605187 : Blo 1605001 1605187 := bstep (se 1 (by rfl) ⟨1203890, by rfl⟩ : syracuseStep 1605187 = 2407781) B2407781
theorem B2408003 : Blo 1605001 2408003 := bstep (se 1 (by rfl) ⟨1806002, by rfl⟩ : syracuseStep 2408003 = 3612005) B3612005
theorem B1605203 : Blo 1605001 1605203 := bstep (se 1 (by rfl) ⟨1203902, by rfl⟩ : syracuseStep 1605203 = 2407805) B2407805
theorem B2408033 : Blo 1605001 2408033 := bstep (se 2 (by rfl) ⟨903012, by rfl⟩ : syracuseStep 2408033 = 1806025) B1806025
theorem B1605219 : Blo 1605001 1605219 := bstep (se 1 (by rfl) ⟨1203914, by rfl⟩ : syracuseStep 1605219 = 2407829) B2407829
theorem B2711137 : Blo 1605001 2711137 := bstep (se 2 (by rfl) ⟨1016676, by rfl⟩ : syracuseStep 2711137 = 2033353) B2033353
theorem B5791331 : Blo 1605001 5791331 := bstep (se 1 (by rfl) ⟨4343498, by rfl⟩ : syracuseStep 5791331 = 8686997) B8686997
theorem B1605235 : Blo 1605001 1605235 := bstep (se 1 (by rfl) ⟨1203926, by rfl⟩ : syracuseStep 1605235 = 2407853) B2407853
theorem B2408051 : Blo 1605001 2408051 := bstep (se 1 (by rfl) ⟨1806038, by rfl⟩ : syracuseStep 2408051 = 3612077) B3612077
theorem B1605251 : Blo 1605001 1605251 := bstep (se 1 (by rfl) ⟨1203938, by rfl⟩ : syracuseStep 1605251 = 2407877) B2407877
theorem B2571907 : Blo 1605001 2571907 := bstep (se 1 (by rfl) ⟨1928930, by rfl⟩ : syracuseStep 2571907 = 3857861) B3857861
theorem B2711171 : Blo 1605001 2711171 := bstep (se 1 (by rfl) ⟨2033378, by rfl⟩ : syracuseStep 2711171 = 4066757) B4066757
theorem B5422733 : Blo 1605001 5422733 := bstep (se 3 (by rfl) ⟨1016762, by rfl⟩ : syracuseStep 5422733 = 2033525) B2033525
theorem B2408081 : Blo 1605001 2408081 := bstep (se 2 (by rfl) ⟨903030, by rfl⟩ : syracuseStep 2408081 = 1806061) B1806061
theorem B1605267 : Blo 1605001 1605267 := bstep (se 1 (by rfl) ⟨1203950, by rfl⟩ : syracuseStep 1605267 = 2407901) B2407901
theorem B1605283 : Blo 1605001 1605283 := bstep (se 1 (by rfl) ⟨1203962, by rfl⟩ : syracuseStep 1605283 = 2407925) B2407925
theorem B2408099 : Blo 1605001 2408099 := bstep (se 1 (by rfl) ⟨1806074, by rfl⟩ : syracuseStep 2408099 = 3612149) B3612149
theorem B9903779 : Blo 1605001 9903779 := bstep (se 1 (by rfl) ⟨7427834, by rfl⟩ : syracuseStep 9903779 = 14855669) B14855669
theorem B1605299 : Blo 1605001 1605299 := bstep (se 1 (by rfl) ⟨1203974, by rfl⟩ : syracuseStep 1605299 = 2407949) B2407949
theorem B2408129 : Blo 1605001 2408129 := bstep (se 2 (by rfl) ⟨903048, by rfl⟩ : syracuseStep 2408129 = 1806097) B1806097
theorem B1605315 : Blo 1605001 1605315 := bstep (se 1 (by rfl) ⟨1203986, by rfl⟩ : syracuseStep 1605315 = 2407973) B2407973
theorem B4341443 : Blo 1605001 4341443 := bstep (se 1 (by rfl) ⟨3256082, by rfl⟩ : syracuseStep 4341443 = 6512165) B6512165
theorem B5422787 : Blo 1605001 5422787 := bstep (se 1 (by rfl) ⟨4067090, by rfl⟩ : syracuseStep 5422787 = 8134181) B8134181
theorem B1605331 : Blo 1605001 1605331 := bstep (se 1 (by rfl) ⟨1203998, by rfl⟩ : syracuseStep 1605331 = 2407997) B2407997
theorem B2408147 : Blo 1605001 2408147 := bstep (se 1 (by rfl) ⟨1806110, by rfl⟩ : syracuseStep 2408147 = 3612221) B3612221
theorem B1605347 : Blo 1605001 1605347 := bstep (se 1 (by rfl) ⟨1204010, by rfl⟩ : syracuseStep 1605347 = 2408021) B2408021
theorem B2408177 : Blo 1605001 2408177 := bstep (se 2 (by rfl) ⟨903066, by rfl⟩ : syracuseStep 2408177 = 1806133) B1806133
theorem B3612401 : Blo 1605001 3612401 := bstep (se 2 (by rfl) ⟨1354650, by rfl⟩ : syracuseStep 3612401 = 2709301) B2709301
theorem B1605363 : Blo 1605001 1605363 := bstep (se 1 (by rfl) ⟨1204022, by rfl⟩ : syracuseStep 1605363 = 2408045) B2408045
theorem B1605379 : Blo 1605001 1605379 := bstep (se 1 (by rfl) ⟨1204034, by rfl⟩ : syracuseStep 1605379 = 2408069) B2408069
theorem B2408195 : Blo 1605001 2408195 := bstep (se 1 (by rfl) ⟨1806146, by rfl⟩ : syracuseStep 2408195 = 3612293) B3612293
theorem B3612419 : Blo 1605001 3612419 := bstep (se 1 (by rfl) ⟨2709314, by rfl⟩ : syracuseStep 3612419 = 5418629) B5418629
theorem B2711299 : Blo 1605001 2711299 := bstep (se 1 (by rfl) ⟨2033474, by rfl⟩ : syracuseStep 2711299 = 4066949) B4066949
theorem B1605395 : Blo 1605001 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B2408225 : Blo 1605001 2408225 := bstep (se 2 (by rfl) ⟨903084, by rfl⟩ : syracuseStep 2408225 = 1806169) B1806169
theorem B2285347 : Blo 1605001 2285347 := bstep (se 1 (by rfl) ⟨1714010, by rfl⟩ : syracuseStep 2285347 = 3428021) B3428021
theorem B8126243 : Blo 1605001 8126243 := bstep (se 1 (by rfl) ⟨6094682, by rfl⟩ : syracuseStep 8126243 = 12189365) B12189365
theorem B1605411 : Blo 1605001 1605411 := bstep (se 1 (by rfl) ⟨1204058, by rfl⟩ : syracuseStep 1605411 = 2408117) B2408117
theorem B1605427 : Blo 1605001 1605427 := bstep (se 1 (by rfl) ⟨1204070, by rfl⟩ : syracuseStep 1605427 = 2408141) B2408141
theorem B2408243 : Blo 1605001 2408243 := bstep (se 1 (by rfl) ⟨1806182, by rfl⟩ : syracuseStep 2408243 = 3612365) B3612365
theorem B1605443 : Blo 1605001 1605443 := bstep (se 1 (by rfl) ⟨1204082, by rfl⟩ : syracuseStep 1605443 = 2408165) B2408165
theorem B2408273 : Blo 1605001 2408273 := bstep (se 2 (by rfl) ⟨903102, by rfl⟩ : syracuseStep 2408273 = 1806205) B1806205
theorem B1605459 : Blo 1605001 1605459 := bstep (se 1 (by rfl) ⟨1204094, by rfl⟩ : syracuseStep 1605459 = 2408189) B2408189
theorem B1605475 : Blo 1605001 1605475 := bstep (se 1 (by rfl) ⟨1204106, by rfl⟩ : syracuseStep 1605475 = 2408213) B2408213
theorem B2408291 : Blo 1605001 2408291 := bstep (se 1 (by rfl) ⟨1806218, by rfl⟩ : syracuseStep 2408291 = 3612437) B3612437
theorem B4341617 : Blo 1605001 4341617 := bstep (se 2 (by rfl) ⟨1628106, by rfl⟩ : syracuseStep 4341617 = 3256213) B3256213
theorem B2031475 : Blo 1605001 2031475 := bstep (se 1 (by rfl) ⟨1523606, by rfl⟩ : syracuseStep 2031475 = 3047213) B3047213
theorem B1605491 : Blo 1605001 1605491 := bstep (se 1 (by rfl) ⟨1204118, by rfl⟩ : syracuseStep 1605491 = 2408237) B2408237
theorem B2408321 : Blo 1605001 2408321 := bstep (se 2 (by rfl) ⟨903120, by rfl⟩ : syracuseStep 2408321 = 1806241) B1806241
theorem B1605507 : Blo 1605001 1605507 := bstep (se 1 (by rfl) ⟨1204130, by rfl⟩ : syracuseStep 1605507 = 2408261) B2408261
theorem B2572163 : Blo 1605001 2572163 := bstep (se 1 (by rfl) ⟨1929122, by rfl⟩ : syracuseStep 2572163 = 3858245) B3858245
theorem B2711441 : Blo 1605001 2711441 := bstep (se 2 (by rfl) ⟨1016790, by rfl⟩ : syracuseStep 2711441 = 2033581) B2033581
theorem B1605523 : Blo 1605001 1605523 := bstep (se 1 (by rfl) ⟨1204142, by rfl⟩ : syracuseStep 1605523 = 2408285) B2408285
theorem B2408339 : Blo 1605001 2408339 := bstep (se 1 (by rfl) ⟨1806254, by rfl⟩ : syracuseStep 2408339 = 3612509) B3612509
theorem B1605539 : Blo 1605001 1605539 := bstep (se 1 (by rfl) ⟨1204154, by rfl⟩ : syracuseStep 1605539 = 2408309) B2408309
theorem B2408369 : Blo 1605001 2408369 := bstep (se 2 (by rfl) ⟨903138, by rfl⟩ : syracuseStep 2408369 = 1806277) B1806277
theorem B1605555 : Blo 1605001 1605555 := bstep (se 1 (by rfl) ⟨1204166, by rfl⟩ : syracuseStep 1605555 = 2408333) B2408333
theorem B1605571 : Blo 1605001 1605571 := bstep (se 1 (by rfl) ⟨1204178, by rfl⟩ : syracuseStep 1605571 = 2408357) B2408357
theorem B2408387 : Blo 1605001 2408387 := bstep (se 1 (by rfl) ⟨1806290, by rfl⟩ : syracuseStep 2408387 = 3612581) B3612581
theorem B5423057 : Blo 1605001 5423057 := bstep (se 2 (by rfl) ⟨2033646, by rfl⟩ : syracuseStep 5423057 = 4067293) B4067293
theorem B2031571 : Blo 1605001 2031571 := bstep (se 1 (by rfl) ⟨1523678, by rfl⟩ : syracuseStep 2031571 = 3047357) B3047357
theorem B1605587 : Blo 1605001 1605587 := bstep (se 1 (by rfl) ⟨1204190, by rfl⟩ : syracuseStep 1605587 = 2408381) B2408381
theorem B2408417 : Blo 1605001 2408417 := bstep (se 2 (by rfl) ⟨903156, by rfl⟩ : syracuseStep 2408417 = 1806313) B1806313
theorem B3047395 : Blo 1605001 3047395 := bstep (se 1 (by rfl) ⟨2285546, by rfl⟩ : syracuseStep 3047395 = 4571093) B4571093
theorem B1605603 : Blo 1605001 1605603 := bstep (se 1 (by rfl) ⟨1204202, by rfl⟩ : syracuseStep 1605603 = 2408405) B2408405
theorem B1605619 : Blo 1605001 1605619 := bstep (se 1 (by rfl) ⟨1204214, by rfl⟩ : syracuseStep 1605619 = 2408429) B2408429
theorem B2408435 : Blo 1605001 2408435 := bstep (se 1 (by rfl) ⟨1806326, by rfl⟩ : syracuseStep 2408435 = 3612653) B3612653
theorem B2408459 : Blo 1605001 2408459 := bstep (se 1 (by rfl) ⟨1806344, by rfl⟩ : syracuseStep 2408459 = 3612689) B3612689
theorem B1605643 : Blo 1605001 1605643 := bstep (se 1 (by rfl) ⟨1204232, by rfl⟩ : syracuseStep 1605643 = 2408465) B2408465
theorem B6094865 : Blo 1605001 6094865 := bstep (se 2 (by rfl) ⟨2285574, by rfl⟩ : syracuseStep 6094865 = 4571149) B4571149
theorem B2408471 : Blo 1605001 2408471 := bstep (se 1 (by rfl) ⟨1806353, by rfl⟩ : syracuseStep 2408471 = 3612707) B3612707
theorem B1605655 : Blo 1605001 1605655 := bstep (se 1 (by rfl) ⟨1204241, by rfl⟩ : syracuseStep 1605655 = 2408483) B2408483
theorem B1605675 : Blo 1605001 1605675 := bstep (se 1 (by rfl) ⟨1204256, by rfl⟩ : syracuseStep 1605675 = 2408513) B2408513
theorem B1605687 : Blo 1605001 1605687 := bstep (se 1 (by rfl) ⟨1204265, by rfl⟩ : syracuseStep 1605687 = 2408531) B2408531
theorem B1605707 : Blo 1605001 1605707 := bstep (se 1 (by rfl) ⟨1204280, by rfl⟩ : syracuseStep 1605707 = 2408561) B2408561
theorem B1605719 : Blo 1605001 1605719 := bstep (se 1 (by rfl) ⟨1204289, by rfl⟩ : syracuseStep 1605719 = 2408579) B2408579
theorem B3612761 : Blo 1605001 3612761 := bstep (se 2 (by rfl) ⟨1354785, by rfl⟩ : syracuseStep 3612761 = 2709571) B2709571
theorem B2408537 : Blo 1605001 2408537 := bstep (se 2 (by rfl) ⟨903201, by rfl⟩ : syracuseStep 2408537 = 1806403) B1806403
theorem B1605739 : Blo 1605001 1605739 := bstep (se 1 (by rfl) ⟨1204304, by rfl⟩ : syracuseStep 1605739 = 2408609) B2408609
theorem B3047539 : Blo 1605001 3047539 := bstep (se 1 (by rfl) ⟨2285654, by rfl⟩ : syracuseStep 3047539 = 4571309) B4571309
theorem B1605751 : Blo 1605001 1605751 := bstep (se 1 (by rfl) ⟨1204313, by rfl⟩ : syracuseStep 1605751 = 2408627) B2408627
theorem B1605771 : Blo 1605001 1605771 := bstep (se 1 (by rfl) ⟨1204328, by rfl⟩ : syracuseStep 1605771 = 2408657) B2408657
theorem B1605783 : Blo 1605001 1605783 := bstep (se 1 (by rfl) ⟨1204337, by rfl⟩ : syracuseStep 1605783 = 2408675) B2408675
theorem B1605803 : Blo 1605001 1605803 := bstep (se 1 (by rfl) ⟨1204352, by rfl⟩ : syracuseStep 1605803 = 2408705) B2408705
theorem B3612851 : Blo 1605001 3612851 := bstep (se 1 (by rfl) ⟨2709638, by rfl⟩ : syracuseStep 3612851 = 5419277) B5419277
theorem B1605815 : Blo 1605001 1605815 := bstep (se 1 (by rfl) ⟨1204361, by rfl⟩ : syracuseStep 1605815 = 2408723) B2408723
theorem B3662027 : Blo 1605001 3662027 := bstep (se 1 (by rfl) ⟨2746520, by rfl⟩ : syracuseStep 3662027 = 5493041) B5493041
theorem B2408651 : Blo 1605001 2408651 := bstep (se 1 (by rfl) ⟨1806488, by rfl⟩ : syracuseStep 2408651 = 3612977) B3612977
theorem B1605835 : Blo 1605001 1605835 := bstep (se 1 (by rfl) ⟨1204376, by rfl⟩ : syracuseStep 1605835 = 2408753) B2408753
theorem B3612887 : Blo 1605001 3612887 := bstep (se 1 (by rfl) ⟨2709665, by rfl⟩ : syracuseStep 3612887 = 5419331) B5419331
theorem B2408663 : Blo 1605001 2408663 := bstep (se 1 (by rfl) ⟨1806497, by rfl⟩ : syracuseStep 2408663 = 3612995) B3612995
theorem B1605847 : Blo 1605001 1605847 := bstep (se 1 (by rfl) ⟨1204385, by rfl⟩ : syracuseStep 1605847 = 2408771) B2408771
theorem B5357789 : Blo 1605001 5357789 := bstep (se 3 (by rfl) ⟨1004585, by rfl⟩ : syracuseStep 5357789 = 2009171) B2009171
theorem B1605867 : Blo 1605001 1605867 := bstep (se 1 (by rfl) ⟨1204400, by rfl⟩ : syracuseStep 1605867 = 2408801) B2408801
theorem B1605879 : Blo 1605001 1605879 := bstep (se 1 (by rfl) ⟨1204409, by rfl⟩ : syracuseStep 1605879 = 2408819) B2408819
theorem B19546373 : Blo 1605001 19546373 := bstep (se 4 (by rfl) ⟨1832472, by rfl⟩ : syracuseStep 19546373 = 3664945) B3664945
theorem B1605899 : Blo 1605001 1605899 := bstep (se 1 (by rfl) ⟨1204424, by rfl⟩ : syracuseStep 1605899 = 2408849) B2408849
theorem B9765137 : Blo 1605001 9765137 := bstep (se 2 (by rfl) ⟨3661926, by rfl⟩ : syracuseStep 9765137 = 7323853) B7323853
theorem B2031895 : Blo 1605001 2031895 := bstep (se 1 (by rfl) ⟨1523921, by rfl⟩ : syracuseStep 2031895 = 3047843) B3047843
theorem B1605911 : Blo 1605001 1605911 := bstep (se 1 (by rfl) ⟨1204433, by rfl⟩ : syracuseStep 1605911 = 2408867) B2408867
theorem B2408729 : Blo 1605001 2408729 := bstep (se 2 (by rfl) ⟨903273, by rfl⟩ : syracuseStep 2408729 = 1806547) B1806547
theorem B1605931 : Blo 1605001 1605931 := bstep (se 1 (by rfl) ⟨1204448, by rfl⟩ : syracuseStep 1605931 = 2408897) B2408897
theorem B6603059 : Blo 1605001 6603059 := bstep (se 1 (by rfl) ⟨4952294, by rfl⟩ : syracuseStep 6603059 = 9904589) B9904589
theorem B1605943 : Blo 1605001 1605943 := bstep (se 1 (by rfl) ⟨1204457, by rfl⟩ : syracuseStep 1605943 = 2408915) B2408915
theorem B4882763 : Blo 1605001 4882763 := bstep (se 1 (by rfl) ⟨3662072, by rfl⟩ : syracuseStep 4882763 = 7324145) B7324145
theorem B1605963 : Blo 1605001 1605963 := bstep (se 1 (by rfl) ⟨1204472, by rfl⟩ : syracuseStep 1605963 = 2408945) B2408945
theorem B5423435 : Blo 1605001 5423435 := bstep (se 1 (by rfl) ⟨4067576, by rfl⟩ : syracuseStep 5423435 = 8135153) B8135153
theorem B2285911 : Blo 1605001 2285911 := bstep (se 1 (by rfl) ⟨1714433, by rfl⟩ : syracuseStep 2285911 = 3428867) B3428867
theorem B1605975 : Blo 1605001 1605975 := bstep (se 1 (by rfl) ⟨1204481, by rfl⟩ : syracuseStep 1605975 = 2408963) B2408963
theorem B1605995 : Blo 1605001 1605995 := bstep (se 1 (by rfl) ⟨1204496, by rfl⟩ : syracuseStep 1605995 = 2408993) B2408993
theorem B1606007 : Blo 1605001 1606007 := bstep (se 1 (by rfl) ⟨1204505, by rfl⟩ : syracuseStep 1606007 = 2409011) B2409011
theorem B3613067 : Blo 1605001 3613067 := bstep (se 1 (by rfl) ⟨2709800, by rfl⟩ : syracuseStep 3613067 = 5419601) B5419601
theorem B2408843 : Blo 1605001 2408843 := bstep (se 1 (by rfl) ⟨1806632, by rfl⟩ : syracuseStep 2408843 = 3613265) B3613265
theorem B1606027 : Blo 1605001 1606027 := bstep (se 1 (by rfl) ⟨1204520, by rfl⟩ : syracuseStep 1606027 = 2409041) B2409041
theorem B2408855 : Blo 1605001 2408855 := bstep (se 1 (by rfl) ⟨1806641, by rfl⟩ : syracuseStep 2408855 = 3613283) B3613283
theorem B1606039 : Blo 1605001 1606039 := bstep (se 1 (by rfl) ⟨1204529, by rfl⟩ : syracuseStep 1606039 = 2409059) B2409059
theorem B1606059 : Blo 1605001 1606059 := bstep (se 1 (by rfl) ⟨1204544, by rfl⟩ : syracuseStep 1606059 = 2409089) B2409089
theorem B23142833 : Blo 1605001 23142833 := bstep (se 2 (by rfl) ⟨8678562, by rfl⟩ : syracuseStep 23142833 = 17357125) B17357125
theorem B1606071 : Blo 1605001 1606071 := bstep (se 1 (by rfl) ⟨1204553, by rfl⟩ : syracuseStep 1606071 = 2409107) B2409107
theorem B5497267 : Blo 1605001 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B3613121 : Blo 1605001 3613121 := bstep (se 2 (by rfl) ⟨1354920, by rfl⟩ : syracuseStep 3613121 = 2709841) B2709841
theorem B1606091 : Blo 1605001 1606091 := bstep (se 1 (by rfl) ⟨1204568, by rfl⟩ : syracuseStep 1606091 = 2409137) B2409137
theorem B1606103 : Blo 1605001 1606103 := bstep (se 1 (by rfl) ⟨1204577, by rfl⟩ : syracuseStep 1606103 = 2409155) B2409155
theorem B29688281 : Blo 1605001 29688281 := bstep (se 2 (by rfl) ⟨11133105, by rfl⟩ : syracuseStep 29688281 = 22266211) B22266211
theorem B6095321 : Blo 1605001 6095321 := bstep (se 2 (by rfl) ⟨2285745, by rfl⟩ : syracuseStep 6095321 = 4571491) B4571491
theorem B2408921 : Blo 1605001 2408921 := bstep (se 2 (by rfl) ⟨903345, by rfl⟩ : syracuseStep 2408921 = 1806691) B1806691
theorem B1606123 : Blo 1605001 1606123 := bstep (se 1 (by rfl) ⟨1204592, by rfl⟩ : syracuseStep 1606123 = 2409185) B2409185
theorem B1606135 : Blo 1605001 1606135 := bstep (se 1 (by rfl) ⟨1204601, by rfl⟩ : syracuseStep 1606135 = 2409203) B2409203
theorem B1606155 : Blo 1605001 1606155 := bstep (se 1 (by rfl) ⟨1204616, by rfl⟩ : syracuseStep 1606155 = 2409233) B2409233
theorem B1606167 : Blo 1605001 1606167 := bstep (se 1 (by rfl) ⟨1204625, by rfl⟩ : syracuseStep 1606167 = 2409251) B2409251
theorem B1606187 : Blo 1605001 1606187 := bstep (se 1 (by rfl) ⟨1204640, by rfl⟩ : syracuseStep 1606187 = 2409281) B2409281
theorem B6513203 : Blo 1605001 6513203 := bstep (se 1 (by rfl) ⟨4884902, by rfl⟩ : syracuseStep 6513203 = 9769805) B9769805
theorem B1606199 : Blo 1605001 1606199 := bstep (se 1 (by rfl) ⟨1204649, by rfl⟩ : syracuseStep 1606199 = 2409299) B2409299
theorem B2409035 : Blo 1605001 2409035 := bstep (se 1 (by rfl) ⟨1806776, by rfl⟩ : syracuseStep 2409035 = 3613553) B3613553
theorem B1606219 : Blo 1605001 1606219 := bstep (se 1 (by rfl) ⟨1204664, by rfl⟩ : syracuseStep 1606219 = 2409329) B2409329
theorem B2409047 : Blo 1605001 2409047 := bstep (se 1 (by rfl) ⟨1806785, by rfl⟩ : syracuseStep 2409047 = 3613571) B3613571
theorem B1606231 : Blo 1605001 1606231 := bstep (se 1 (by rfl) ⟨1204673, by rfl⟩ : syracuseStep 1606231 = 2409347) B2409347
theorem B3048025 : Blo 1605001 3048025 := bstep (se 2 (by rfl) ⟨1143009, by rfl⟩ : syracuseStep 3048025 = 2286019) B2286019
theorem B4571741 : Blo 1605001 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B1606251 : Blo 1605001 1606251 := bstep (se 1 (by rfl) ⟨1204688, by rfl⟩ : syracuseStep 1606251 = 2409377) B2409377
theorem B1606263 : Blo 1605001 1606263 := bstep (se 1 (by rfl) ⟨1204697, by rfl⟩ : syracuseStep 1606263 = 2409395) B2409395
theorem B1606283 : Blo 1605001 1606283 := bstep (se 1 (by rfl) ⟨1204712, by rfl⟩ : syracuseStep 1606283 = 2409425) B2409425
theorem B1606295 : Blo 1605001 1606295 := bstep (se 1 (by rfl) ⟨1204721, by rfl⟩ : syracuseStep 1606295 = 2409443) B2409443
theorem B3613337 : Blo 1605001 3613337 := bstep (se 2 (by rfl) ⟨1355001, by rfl⟩ : syracuseStep 3613337 = 2710003) B2710003
theorem B2409113 : Blo 1605001 2409113 := bstep (se 2 (by rfl) ⟨903417, by rfl⟩ : syracuseStep 2409113 = 1806835) B1806835
theorem B6095533 : Blo 1605001 6095533 := bstep (se 3 (by rfl) ⟨1142912, by rfl⟩ : syracuseStep 6095533 = 2285825) B2285825
theorem B1606315 : Blo 1605001 1606315 := bstep (se 1 (by rfl) ⟨1204736, by rfl⟩ : syracuseStep 1606315 = 2409473) B2409473
theorem B1606327 : Blo 1605001 1606327 := bstep (se 1 (by rfl) ⟨1204745, by rfl⟩ : syracuseStep 1606327 = 2409491) B2409491
theorem B1606347 : Blo 1605001 1606347 := bstep (se 1 (by rfl) ⟨1204760, by rfl⟩ : syracuseStep 1606347 = 2409521) B2409521
theorem B1606359 : Blo 1605001 1606359 := bstep (se 1 (by rfl) ⟨1204769, by rfl⟩ : syracuseStep 1606359 = 2409539) B2409539
theorem B1606379 : Blo 1605001 1606379 := bstep (se 1 (by rfl) ⟨1204784, by rfl⟩ : syracuseStep 1606379 = 2409569) B2409569
theorem B3613427 : Blo 1605001 3613427 := bstep (se 1 (by rfl) ⟨2710070, by rfl⟩ : syracuseStep 3613427 = 5420141) B5420141
theorem B1606391 : Blo 1605001 1606391 := bstep (se 1 (by rfl) ⟨1204793, by rfl⟩ : syracuseStep 1606391 = 2409587) B2409587
theorem B2409227 : Blo 1605001 2409227 := bstep (se 1 (by rfl) ⟨1806920, by rfl⟩ : syracuseStep 2409227 = 3613841) B3613841
theorem B1606411 : Blo 1605001 1606411 := bstep (se 1 (by rfl) ⟨1204808, by rfl⟩ : syracuseStep 1606411 = 2409617) B2409617
theorem B3613463 : Blo 1605001 3613463 := bstep (se 1 (by rfl) ⟨2710097, by rfl⟩ : syracuseStep 3613463 = 5420195) B5420195
theorem B2409239 : Blo 1605001 2409239 := bstep (se 1 (by rfl) ⟨1806929, by rfl⟩ : syracuseStep 2409239 = 3613859) B3613859
theorem B1606423 : Blo 1605001 1606423 := bstep (se 1 (by rfl) ⟨1204817, by rfl⟩ : syracuseStep 1606423 = 2409635) B2409635
theorem B1606443 : Blo 1605001 1606443 := bstep (se 1 (by rfl) ⟨1204832, by rfl⟩ : syracuseStep 1606443 = 2409665) B2409665
theorem B1606455 : Blo 1605001 1606455 := bstep (se 1 (by rfl) ⟨1204841, by rfl⟩ : syracuseStep 1606455 = 2409683) B2409683
theorem B1606475 : Blo 1605001 1606475 := bstep (se 1 (by rfl) ⟨1204856, by rfl⟩ : syracuseStep 1606475 = 2409713) B2409713
theorem B1606487 : Blo 1605001 1606487 := bstep (se 1 (by rfl) ⟨1204865, by rfl⟩ : syracuseStep 1606487 = 2409731) B2409731
theorem B2409305 : Blo 1605001 2409305 := bstep (se 2 (by rfl) ⟨903489, by rfl⟩ : syracuseStep 2409305 = 1806979) B1806979
theorem B1606507 : Blo 1605001 1606507 := bstep (se 1 (by rfl) ⟨1204880, by rfl⟩ : syracuseStep 1606507 = 2409761) B2409761
theorem B1606519 : Blo 1605001 1606519 := bstep (se 1 (by rfl) ⟨1204889, by rfl⟩ : syracuseStep 1606519 = 2409779) B2409779
theorem B1606539 : Blo 1605001 1606539 := bstep (se 1 (by rfl) ⟨1204904, by rfl⟩ : syracuseStep 1606539 = 2409809) B2409809
theorem B1606551 : Blo 1605001 1606551 := bstep (se 1 (by rfl) ⟨1204913, by rfl⟩ : syracuseStep 1606551 = 2409827) B2409827
theorem B1606571 : Blo 1605001 1606571 := bstep (se 1 (by rfl) ⟨1204928, by rfl⟩ : syracuseStep 1606571 = 2409857) B2409857
theorem B1606583 : Blo 1605001 1606583 := bstep (se 1 (by rfl) ⟨1204937, by rfl⟩ : syracuseStep 1606583 = 2409875) B2409875
theorem B3613643 : Blo 1605001 3613643 := bstep (se 1 (by rfl) ⟨2710232, by rfl⟩ : syracuseStep 3613643 = 5420465) B5420465
theorem B2409419 : Blo 1605001 2409419 := bstep (se 1 (by rfl) ⟨1807064, by rfl⟩ : syracuseStep 2409419 = 3614129) B3614129
theorem B1606603 : Blo 1605001 1606603 := bstep (se 1 (by rfl) ⟨1204952, by rfl⟩ : syracuseStep 1606603 = 2409905) B2409905
theorem B2409431 : Blo 1605001 2409431 := bstep (se 1 (by rfl) ⟨1807073, by rfl⟩ : syracuseStep 2409431 = 3614147) B3614147
theorem B2892761 : Blo 1605001 2892761 := bstep (se 2 (by rfl) ⟨1084785, by rfl⟩ : syracuseStep 2892761 = 2169571) B2169571
theorem B1606615 : Blo 1605001 1606615 := bstep (se 1 (by rfl) ⟨1204961, by rfl⟩ : syracuseStep 1606615 = 2409923) B2409923
theorem B6095837 : Blo 1605001 6095837 := bstep (se 3 (by rfl) ⟨1142969, by rfl⟩ : syracuseStep 6095837 = 2285939) B2285939
theorem B1606635 : Blo 1605001 1606635 := bstep (se 1 (by rfl) ⟨1204976, by rfl⟩ : syracuseStep 1606635 = 2409953) B2409953
theorem B1606647 : Blo 1605001 1606647 := bstep (se 1 (by rfl) ⟨1204985, by rfl⟩ : syracuseStep 1606647 = 2409971) B2409971
theorem B3613697 : Blo 1605001 3613697 := bstep (se 2 (by rfl) ⟨1355136, by rfl⟩ : syracuseStep 3613697 = 2710273) B2710273
theorem B1606667 : Blo 1605001 1606667 := bstep (se 1 (by rfl) ⟨1205000, by rfl⟩ : syracuseStep 1606667 = 2410001) B2410001
theorem B11731985 : Blo 1605001 11731985 := bstep (se 2 (by rfl) ⟨4399494, by rfl⟩ : syracuseStep 11731985 = 8798989) B8798989
theorem B1606679 : Blo 1605001 1606679 := bstep (se 1 (by rfl) ⟨1205009, by rfl⟩ : syracuseStep 1606679 = 2410019) B2410019
theorem B2409497 : Blo 1605001 2409497 := bstep (se 2 (by rfl) ⟨903561, by rfl⟩ : syracuseStep 2409497 = 1807123) B1807123
theorem B1606699 : Blo 1605001 1606699 := bstep (se 1 (by rfl) ⟨1205024, by rfl⟩ : syracuseStep 1606699 = 2410049) B2410049
theorem B1606711 : Blo 1605001 1606711 := bstep (se 1 (by rfl) ⟨1205033, by rfl⟩ : syracuseStep 1606711 = 2410067) B2410067
theorem B2032715 : Blo 1605001 2032715 := bstep (se 1 (by rfl) ⟨1524536, by rfl⟩ : syracuseStep 2032715 = 3049073) B3049073
theorem B1606731 : Blo 1605001 1606731 := bstep (se 1 (by rfl) ⟨1205048, by rfl⟩ : syracuseStep 1606731 = 2410097) B2410097
theorem B2573399 : Blo 1605001 2573399 := bstep (se 1 (by rfl) ⟨1930049, by rfl⟩ : syracuseStep 2573399 = 3860099) B3860099
theorem B1606743 : Blo 1605001 1606743 := bstep (se 1 (by rfl) ⟨1205057, by rfl⟩ : syracuseStep 1606743 = 2410115) B2410115
theorem B11289701 : Blo 1605001 11289701 := bstep (se 4 (by rfl) ⟨1058409, by rfl⟩ : syracuseStep 11289701 = 2116819) B2116819
theorem B1606763 : Blo 1605001 1606763 := bstep (se 1 (by rfl) ⟨1205072, by rfl⟩ : syracuseStep 1606763 = 2410145) B2410145
theorem B1606775 : Blo 1605001 1606775 := bstep (se 1 (by rfl) ⟨1205081, by rfl⟩ : syracuseStep 1606775 = 2410163) B2410163
theorem B3048587 : Blo 1605001 3048587 := bstep (se 1 (by rfl) ⟨2286440, by rfl⟩ : syracuseStep 3048587 = 4572881) B4572881
theorem B2286731 : Blo 1605001 2286731 := bstep (se 1 (by rfl) ⟨1715048, by rfl⟩ : syracuseStep 2286731 = 3430097) B3430097
theorem B2409611 : Blo 1605001 2409611 := bstep (se 1 (by rfl) ⟨1807208, by rfl⟩ : syracuseStep 2409611 = 3614417) B3614417
theorem B1606795 : Blo 1605001 1606795 := bstep (se 1 (by rfl) ⟨1205096, by rfl⟩ : syracuseStep 1606795 = 2410193) B2410193
theorem B2409623 : Blo 1605001 2409623 := bstep (se 1 (by rfl) ⟨1807217, by rfl⟩ : syracuseStep 2409623 = 3614435) B3614435
theorem B1606807 : Blo 1605001 1606807 := bstep (se 1 (by rfl) ⟨1205105, by rfl⟩ : syracuseStep 1606807 = 2410211) B2410211
theorem B1606827 : Blo 1605001 1606827 := bstep (se 1 (by rfl) ⟨1205120, by rfl⟩ : syracuseStep 1606827 = 2410241) B2410241
theorem B4457651 : Blo 1605001 4457651 := bstep (se 1 (by rfl) ⟨3343238, by rfl⟩ : syracuseStep 4457651 = 6686477) B6686477
theorem B187786421 : Blo 1605001 187786421 := bstep (se 5 (by rfl) ⟨8802488, by rfl⟩ : syracuseStep 187786421 = 17604977) B17604977
theorem B1606839 : Blo 1605001 1606839 := bstep (se 1 (by rfl) ⟨1205129, by rfl⟩ : syracuseStep 1606839 = 2410259) B2410259
theorem B6177995 : Blo 1605001 6177995 := bstep (se 1 (by rfl) ⟨4633496, by rfl⟩ : syracuseStep 6177995 = 9266993) B9266993
theorem B1606859 : Blo 1605001 1606859 := bstep (se 1 (by rfl) ⟨1205144, by rfl⟩ : syracuseStep 1606859 = 2410289) B2410289
theorem B3613913 : Blo 1605001 3613913 := bstep (se 2 (by rfl) ⟨1355217, by rfl⟩ : syracuseStep 3613913 = 2710435) B2710435
theorem B2409689 : Blo 1605001 2409689 := bstep (se 2 (by rfl) ⟨903633, by rfl⟩ : syracuseStep 2409689 = 1807267) B1807267
theorem B2573527 : Blo 1605001 2573527 := bstep (se 1 (by rfl) ⟨1930145, by rfl⟩ : syracuseStep 2573527 = 3860291) B3860291
theorem B1606871 : Blo 1605001 1606871 := bstep (se 1 (by rfl) ⟨1205153, by rfl⟩ : syracuseStep 1606871 = 2410307) B2410307
theorem B1606891 : Blo 1605001 1606891 := bstep (se 1 (by rfl) ⟨1205168, by rfl⟩ : syracuseStep 1606891 = 2410337) B2410337
theorem B1606903 : Blo 1605001 1606903 := bstep (se 1 (by rfl) ⟨1205177, by rfl⟩ : syracuseStep 1606903 = 2410355) B2410355
theorem B1606923 : Blo 1605001 1606923 := bstep (se 1 (by rfl) ⟨1205192, by rfl⟩ : syracuseStep 1606923 = 2410385) B2410385
theorem B1606935 : Blo 1605001 1606935 := bstep (se 1 (by rfl) ⟨1205201, by rfl⟩ : syracuseStep 1606935 = 2410403) B2410403
theorem B1606955 : Blo 1605001 1606955 := bstep (se 1 (by rfl) ⟨1205216, by rfl⟩ : syracuseStep 1606955 = 2410433) B2410433
theorem B3614003 : Blo 1605001 3614003 := bstep (se 1 (by rfl) ⟨2710502, by rfl⟩ : syracuseStep 3614003 = 5421005) B5421005
theorem B1606967 : Blo 1605001 1606967 := bstep (se 1 (by rfl) ⟨1205225, by rfl⟩ : syracuseStep 1606967 = 2410451) B2410451
theorem B3048769 : Blo 1605001 3048769 := bstep (se 2 (by rfl) ⟨1143288, by rfl⟩ : syracuseStep 3048769 = 2286577) B2286577
theorem B18302273 : Blo 1605001 18302273 := bstep (se 2 (by rfl) ⟨6863352, by rfl⟩ : syracuseStep 18302273 = 13726705) B13726705
theorem B2409803 : Blo 1605001 2409803 := bstep (se 1 (by rfl) ⟨1807352, by rfl⟩ : syracuseStep 2409803 = 3614705) B3614705
theorem B1606987 : Blo 1605001 1606987 := bstep (se 1 (by rfl) ⟨1205240, by rfl⟩ : syracuseStep 1606987 = 2410481) B2410481
theorem B3614039 : Blo 1605001 3614039 := bstep (se 1 (by rfl) ⟨2710529, by rfl⟩ : syracuseStep 3614039 = 5421059) B5421059
theorem B2409815 : Blo 1605001 2409815 := bstep (se 1 (by rfl) ⟨1807361, by rfl⟩ : syracuseStep 2409815 = 3614723) B3614723
theorem B1606999 : Blo 1605001 1606999 := bstep (se 1 (by rfl) ⟨1205249, by rfl⟩ : syracuseStep 1606999 = 2410499) B2410499
theorem B2893171 : Blo 1605001 2893171 := bstep (se 1 (by rfl) ⟨2169878, by rfl⟩ : syracuseStep 2893171 = 4339757) B4339757
theorem B2409881 : Blo 1605001 2409881 := bstep (se 2 (by rfl) ⟨903705, by rfl⟩ : syracuseStep 2409881 = 1807411) B1807411
theorem B3614219 : Blo 1605001 3614219 := bstep (se 1 (by rfl) ⟨2710664, by rfl⟩ : syracuseStep 3614219 = 5421329) B5421329
theorem B2409995 : Blo 1605001 2409995 := bstep (se 1 (by rfl) ⟨1807496, by rfl⟩ : syracuseStep 2409995 = 3614993) B3614993
theorem B2410007 : Blo 1605001 2410007 := bstep (se 1 (by rfl) ⟨1807505, by rfl⟩ : syracuseStep 2410007 = 3615011) B3615011
theorem B3614273 : Blo 1605001 3614273 := bstep (se 2 (by rfl) ⟨1355352, by rfl⟩ : syracuseStep 3614273 = 2710705) B2710705
theorem B4064843 : Blo 1605001 4064843 := bstep (se 1 (by rfl) ⟨3048632, by rfl⟩ : syracuseStep 4064843 = 6097265) B6097265
theorem B2410073 : Blo 1605001 2410073 := bstep (se 2 (by rfl) ⟨903777, by rfl⟩ : syracuseStep 2410073 = 1807555) B1807555
theorem B2410187 : Blo 1605001 2410187 := bstep (se 1 (by rfl) ⟨1807640, by rfl⟩ : syracuseStep 2410187 = 3615281) B3615281
theorem B2410199 : Blo 1605001 2410199 := bstep (se 1 (by rfl) ⟨1807649, by rfl⟩ : syracuseStep 2410199 = 3615299) B3615299
theorem B6514435 : Blo 1605001 6514435 := bstep (se 1 (by rfl) ⟨4885826, by rfl⟩ : syracuseStep 6514435 = 9771653) B9771653
theorem B2033419 : Blo 1605001 2033419 := bstep (se 1 (by rfl) ⟨1525064, by rfl⟩ : syracuseStep 2033419 = 3050129) B3050129
theorem B3614489 : Blo 1605001 3614489 := bstep (se 2 (by rfl) ⟨1355433, by rfl⟩ : syracuseStep 3614489 = 2710867) B2710867
theorem B2410265 : Blo 1605001 2410265 := bstep (se 2 (by rfl) ⟨903849, by rfl⟩ : syracuseStep 2410265 = 1807699) B1807699
theorem B8128349 : Blo 1605001 8128349 := bstep (se 3 (by rfl) ⟨1524065, by rfl⟩ : syracuseStep 8128349 = 3048131) B3048131
theorem B11577181 : Blo 1605001 11577181 := bstep (se 3 (by rfl) ⟨2170721, by rfl⟩ : syracuseStep 11577181 = 4341443) B4341443
theorem B75171685 : Blo 1605001 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B3614579 : Blo 1605001 3614579 := bstep (se 1 (by rfl) ⟨2710934, by rfl⟩ : syracuseStep 3614579 = 5421869) B5421869
theorem B2410379 : Blo 1605001 2410379 := bstep (se 1 (by rfl) ⟨1807784, by rfl⟩ : syracuseStep 2410379 = 3615569) B3615569
theorem B3614615 : Blo 1605001 3614615 := bstep (se 1 (by rfl) ⟨2710961, by rfl⟩ : syracuseStep 3614615 = 5421923) B5421923
theorem B2410391 : Blo 1605001 2410391 := bstep (se 1 (by rfl) ⟨1807793, by rfl⟩ : syracuseStep 2410391 = 3615587) B3615587
theorem B3475415 : Blo 1605001 3475415 := bstep (se 1 (by rfl) ⟨2606561, by rfl⟩ : syracuseStep 3475415 = 5213123) B5213123
theorem B2410457 : Blo 1605001 2410457 := bstep (se 2 (by rfl) ⟨903921, by rfl⟩ : syracuseStep 2410457 = 1807843) B1807843
theorem B3049483 : Blo 1605001 3049483 := bstep (se 1 (by rfl) ⟨2287112, by rfl⟩ : syracuseStep 3049483 = 4574225) B4574225
theorem B2033687 : Blo 1605001 2033687 := bstep (se 1 (by rfl) ⟨1525265, by rfl⟩ : syracuseStep 2033687 = 3050531) B3050531
theorem B6858827 : Blo 1605001 6858827 := bstep (se 1 (by rfl) ⟨5144120, by rfl⟩ : syracuseStep 6858827 = 10288241) B10288241
theorem B3614795 : Blo 1605001 3614795 := bstep (se 1 (by rfl) ⟨2711096, by rfl⟩ : syracuseStep 3614795 = 5422193) B5422193
theorem B3049559 : Blo 1605001 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B2287705 : Blo 1605001 2287705 := bstep (se 2 (by rfl) ⟨857889, by rfl⟩ : syracuseStep 2287705 = 1715779) B1715779
theorem B3614849 : Blo 1605001 3614849 := bstep (se 2 (by rfl) ⟨1355568, by rfl⟩ : syracuseStep 3614849 = 2711137) B2711137
theorem B8800435 : Blo 1605001 8800435 := bstep (se 1 (by rfl) ⟨6600326, by rfl⟩ : syracuseStep 8800435 = 13200653) B13200653
theorem B3664151 : Blo 1605001 3664151 := bstep (se 1 (by rfl) ⟨2748113, by rfl⟩ : syracuseStep 3664151 = 5496227) B5496227
theorem B3615065 : Blo 1605001 3615065 := bstep (se 2 (by rfl) ⟨1355649, by rfl⟩ : syracuseStep 3615065 = 2711299) B2711299
theorem B3860887 : Blo 1605001 3860887 := bstep (se 1 (by rfl) ⟨2895665, by rfl⟩ : syracuseStep 3860887 = 5791331) B5791331
theorem B3615155 : Blo 1605001 3615155 := bstep (se 1 (by rfl) ⟨2711366, by rfl⟩ : syracuseStep 3615155 = 5422733) B5422733
theorem B3615191 : Blo 1605001 3615191 := bstep (se 1 (by rfl) ⟨2711393, by rfl⟩ : syracuseStep 3615191 = 5422787) B5422787
theorem B5417495 : Blo 1605001 5417495 := bstep (se 1 (by rfl) ⟨4063121, by rfl⟩ : syracuseStep 5417495 = 8126243) B8126243
theorem B4065815 : Blo 1605001 4065815 := bstep (se 1 (by rfl) ⟨3049361, by rfl⟩ : syracuseStep 4065815 = 6098723) B6098723
theorem B2894411 : Blo 1605001 2894411 := bstep (se 1 (by rfl) ⟨2170808, by rfl⟩ : syracuseStep 2894411 = 4341617) B4341617
theorem B1714775 : Blo 1605001 1714775 := bstep (se 1 (by rfl) ⟨1286081, by rfl⟩ : syracuseStep 1714775 = 2572163) B2572163
theorem B3615371 : Blo 1605001 3615371 := bstep (se 1 (by rfl) ⟨2711528, by rfl⟩ : syracuseStep 3615371 = 5423057) B5423057
theorem B5868211 : Blo 1605001 5868211 := bstep (se 1 (by rfl) ⟨4401158, by rfl⟩ : syracuseStep 5868211 = 8802317) B8802317
theorem B3615425 : Blo 1605001 3615425 := bstep (se 2 (by rfl) ⟨1355784, by rfl⟩ : syracuseStep 3615425 = 2711569) B2711569
theorem B3050227 : Blo 1605001 3050227 := bstep (se 1 (by rfl) ⟨2287670, by rfl⟩ : syracuseStep 3050227 = 4575341) B4575341
theorem B13716317 : Blo 1605001 13716317 := bstep (se 3 (by rfl) ⟨2571809, by rfl⟩ : syracuseStep 13716317 = 5143619) B5143619
theorem B3615641 : Blo 1605001 3615641 := bstep (se 2 (by rfl) ⟨1355865, by rfl⟩ : syracuseStep 3615641 = 2711731) B2711731
theorem B2894785 : Blo 1605001 2894785 := bstep (se 2 (by rfl) ⟨1085544, by rfl⟩ : syracuseStep 2894785 = 2171089) B2171089
theorem B3050455 : Blo 1605001 3050455 := bstep (se 1 (by rfl) ⟨2287841, by rfl⟩ : syracuseStep 3050455 = 4575683) B4575683
theorem B3615731 : Blo 1605001 3615731 := bstep (se 1 (by rfl) ⟨2711798, by rfl⟩ : syracuseStep 3615731 = 5423597) B5423597
theorem B6859799 : Blo 1605001 6859799 := bstep (se 1 (by rfl) ⟨5144849, by rfl⟩ : syracuseStep 6859799 = 10289699) B10289699
theorem B5418035 : Blo 1605001 5418035 := bstep (se 1 (by rfl) ⟨4063526, by rfl⟩ : syracuseStep 5418035 = 8127053) B8127053
theorem B3050561 : Blo 1605001 3050561 := bstep (se 2 (by rfl) ⟨1143960, by rfl⟩ : syracuseStep 3050561 = 2287921) B2287921
theorem B21138563 : Blo 1605001 21138563 := bstep (se 1 (by rfl) ⟨15853922, by rfl⟩ : syracuseStep 21138563 = 31707845) B31707845
theorem B12536963 : Blo 1605001 12536963 := bstep (se 1 (by rfl) ⟨9402722, by rfl⟩ : syracuseStep 12536963 = 18805445) B18805445
theorem B4066483 : Blo 1605001 4066483 := bstep (se 1 (by rfl) ⟨3049862, by rfl⟩ : syracuseStep 4066483 = 6099725) B6099725
theorem B3050713 : Blo 1605001 3050713 := bstep (se 2 (by rfl) ⟨1144017, by rfl⟩ : syracuseStep 3050713 = 2288035) B2288035
theorem B1649975 : Blo 1605001 1649975 := bstep (se 1 (by rfl) ⟨1237481, by rfl⟩ : syracuseStep 1649975 = 2474963) B2474963
theorem B5418305 : Blo 1605001 5418305 := bstep (se 2 (by rfl) ⟨2031864, by rfl⟩ : syracuseStep 5418305 = 4063729) B4063729
theorem B4066625 : Blo 1605001 4066625 := bstep (se 2 (by rfl) ⟨1524984, by rfl⟩ : syracuseStep 4066625 = 3049969) B3049969
theorem B1805719 : Blo 1605001 1805719 := bstep (se 1 (by rfl) ⟨1354289, by rfl⟩ : syracuseStep 1805719 = 2708579) B2708579
theorem B6598039 : Blo 1605001 6598039 := bstep (se 1 (by rfl) ⟨4948529, by rfl⟩ : syracuseStep 6598039 = 9897059) B9897059
theorem B9768343 : Blo 1605001 9768343 := bstep (se 1 (by rfl) ⟨7326257, by rfl⟩ : syracuseStep 9768343 = 14652515) B14652515
theorem B4574657 : Blo 1605001 4574657 := bstep (se 2 (by rfl) ⟨1715496, by rfl⟩ : syracuseStep 4574657 = 3430993) B3430993
theorem B4574681 : Blo 1605001 4574681 := bstep (se 2 (by rfl) ⟨1715505, by rfl⟩ : syracuseStep 4574681 = 3431011) B3431011
theorem B6098435 : Blo 1605001 6098435 := bstep (se 1 (by rfl) ⟨4573826, by rfl⟩ : syracuseStep 6098435 = 9147653) B9147653
theorem B23162381 : Blo 1605001 23162381 := bstep (se 3 (by rfl) ⟨4342946, by rfl⟩ : syracuseStep 23162381 = 8685893) B8685893
theorem B6098449 : Blo 1605001 6098449 := bstep (se 2 (by rfl) ⟨2286918, by rfl⟩ : syracuseStep 6098449 = 4573837) B4573837
theorem B1805899 : Blo 1605001 1805899 := bstep (se 1 (by rfl) ⟨1354424, by rfl⟩ : syracuseStep 1805899 = 2708849) B2708849
theorem B1806007 : Blo 1605001 1806007 := bstep (se 1 (by rfl) ⟨1354505, by rfl⟩ : syracuseStep 1806007 = 2709011) B2709011
theorem B3256051 : Blo 1605001 3256051 := bstep (se 1 (by rfl) ⟨2442038, by rfl⟩ : syracuseStep 3256051 = 4884077) B4884077
theorem B3477313 : Blo 1605001 3477313 := bstep (se 2 (by rfl) ⟨1303992, by rfl⟩ : syracuseStep 3477313 = 2607985) B2607985
theorem B6098753 : Blo 1605001 6098753 := bstep (se 2 (by rfl) ⟨2287032, by rfl⟩ : syracuseStep 6098753 = 4574065) B4574065
theorem B3428183 : Blo 1605001 3428183 := bstep (se 1 (by rfl) ⟨2571137, by rfl⟩ : syracuseStep 3428183 = 5142275) B5142275
theorem B5418845 : Blo 1605001 5418845 := bstep (se 3 (by rfl) ⟨1016033, by rfl⟩ : syracuseStep 5418845 = 2032067) B2032067
theorem B31272803 : Blo 1605001 31272803 := bstep (se 1 (by rfl) ⟨23454602, by rfl⟩ : syracuseStep 31272803 = 46909205) B46909205
theorem B1806187 : Blo 1605001 1806187 := bstep (se 1 (by rfl) ⟨1354640, by rfl⟩ : syracuseStep 1806187 = 2709281) B2709281
theorem B8130455 : Blo 1605001 8130455 := bstep (se 1 (by rfl) ⟨6097841, by rfl⟩ : syracuseStep 8130455 = 12195683) B12195683
theorem B1806295 : Blo 1605001 1806295 := bstep (se 1 (by rfl) ⟨1354721, by rfl⟩ : syracuseStep 1806295 = 2709443) B2709443
theorem B12202001 : Blo 1605001 12202001 := bstep (se 2 (by rfl) ⟨4575750, by rfl⟩ : syracuseStep 12202001 = 9151501) B9151501
theorem B5787713 : Blo 1605001 5787713 := bstep (se 2 (by rfl) ⟨2170392, by rfl⟩ : syracuseStep 5787713 = 4340785) B4340785
theorem B1806475 : Blo 1605001 1806475 := bstep (se 1 (by rfl) ⟨1354856, by rfl⟩ : syracuseStep 1806475 = 2709713) B2709713
theorem B1929367 : Blo 1605001 1929367 := bstep (se 1 (by rfl) ⟨1447025, by rfl⟩ : syracuseStep 1929367 = 2894051) B2894051
theorem B25055473 : Blo 1605001 25055473 := bstep (se 2 (by rfl) ⟨9395802, by rfl⟩ : syracuseStep 25055473 = 18791605) B18791605
theorem B1806583 : Blo 1605001 1806583 := bstep (se 1 (by rfl) ⟨1354937, by rfl⟩ : syracuseStep 1806583 = 2709875) B2709875
theorem B3256691 : Blo 1605001 3256691 := bstep (se 1 (by rfl) ⟨2442518, by rfl⟩ : syracuseStep 3256691 = 4885037) B4885037
theorem B1806763 : Blo 1605001 1806763 := bstep (se 1 (by rfl) ⟨1355072, by rfl⟩ : syracuseStep 1806763 = 2710145) B2710145
theorem B12194225 : Blo 1605001 12194225 := bstep (se 2 (by rfl) ⟨4572834, by rfl⟩ : syracuseStep 12194225 = 9145669) B9145669
theorem B6099421 : Blo 1605001 6099421 := bstep (se 3 (by rfl) ⟨1143641, by rfl⟩ : syracuseStep 6099421 = 2287283) B2287283
theorem B1806871 : Blo 1605001 1806871 := bstep (se 1 (by rfl) ⟨1355153, by rfl⟩ : syracuseStep 1806871 = 2710307) B2710307
theorem B9146945 : Blo 1605001 9146945 := bstep (se 2 (by rfl) ⟨3430104, by rfl⟩ : syracuseStep 9146945 = 6860209) B6860209
theorem B14660189 : Blo 1605001 14660189 := bstep (se 3 (by rfl) ⟨2748785, by rfl⟩ : syracuseStep 14660189 = 5497571) B5497571
theorem B7713431 : Blo 1605001 7713431 := bstep (se 1 (by rfl) ⟨5785073, by rfl⟩ : syracuseStep 7713431 = 11570147) B11570147
theorem B4575923 : Blo 1605001 4575923 := bstep (se 1 (by rfl) ⟨3431942, by rfl⟩ : syracuseStep 4575923 = 6863885) B6863885
theorem B1807051 : Blo 1605001 1807051 := bstep (se 1 (by rfl) ⟨1355288, by rfl⟩ : syracuseStep 1807051 = 2710577) B2710577
theorem B1807159 : Blo 1605001 1807159 := bstep (se 1 (by rfl) ⟨1355369, by rfl⟩ : syracuseStep 1807159 = 2710739) B2710739
theorem B3429209 : Blo 1605001 3429209 := bstep (se 2 (by rfl) ⟨1285953, by rfl⟩ : syracuseStep 3429209 = 2571907) B2571907
theorem B12194711 : Blo 1605001 12194711 := bstep (se 1 (by rfl) ⟨9146033, by rfl⟩ : syracuseStep 12194711 = 18292067) B18292067
theorem B5419979 : Blo 1605001 5419979 := bstep (se 1 (by rfl) ⟨4064984, by rfl⟩ : syracuseStep 5419979 = 8129969) B8129969
theorem B1807339 : Blo 1605001 1807339 := bstep (se 1 (by rfl) ⟨1355504, by rfl⟩ : syracuseStep 1807339 = 2711009) B2711009
theorem B2708491 : Blo 1605001 2708491 := bstep (se 1 (by rfl) ⟨2031368, by rfl⟩ : syracuseStep 2708491 = 4062737) B4062737
theorem B1807447 : Blo 1605001 1807447 := bstep (se 1 (by rfl) ⟨1355585, by rfl⟩ : syracuseStep 1807447 = 2711171) B2711171
theorem B26391683 : Blo 1605001 26391683 := bstep (se 1 (by rfl) ⟨19793762, by rfl⟩ : syracuseStep 26391683 = 39587525) B39587525
theorem B2708633 : Blo 1605001 2708633 := bstep (se 2 (by rfl) ⟨1015737, by rfl⟩ : syracuseStep 2708633 = 2031475) B2031475
theorem B5420249 : Blo 1605001 5420249 := bstep (se 2 (by rfl) ⟨2032593, by rfl⟩ : syracuseStep 5420249 = 4065187) B4065187
theorem B5018845 : Blo 1605001 5018845 := bstep (se 3 (by rfl) ⟨941033, by rfl⟩ : syracuseStep 5018845 = 1882067) B1882067
theorem B1807627 : Blo 1605001 1807627 := bstep (se 1 (by rfl) ⟨1355720, by rfl⟩ : syracuseStep 1807627 = 2711441) B2711441
theorem B2708761 : Blo 1605001 2708761 := bstep (se 2 (by rfl) ⟨1015785, by rfl⟩ : syracuseStep 2708761 = 2031571) B2031571
theorem B8680769 : Blo 1605001 8680769 := bstep (se 2 (by rfl) ⟨3255288, by rfl⟩ : syracuseStep 8680769 = 6510577) B6510577
theorem B1807735 : Blo 1605001 1807735 := bstep (se 1 (by rfl) ⟨1355801, by rfl⟩ : syracuseStep 1807735 = 2711603) B2711603
theorem B13718915 : Blo 1605001 13718915 := bstep (se 1 (by rfl) ⟨10289186, by rfl⟩ : syracuseStep 13718915 = 20578373) B20578373
theorem B7714199 : Blo 1605001 7714199 := bstep (se 1 (by rfl) ⟨5785649, by rfl⟩ : syracuseStep 7714199 = 11571299) B11571299
theorem B6862259 : Blo 1605001 6862259 := bstep (se 1 (by rfl) ⟨5146694, by rfl⟩ : syracuseStep 6862259 = 10293389) B10293389
theorem B7329325 : Blo 1605001 7329325 := bstep (se 3 (by rfl) ⟨1374248, by rfl⟩ : syracuseStep 7329325 = 2748497) B2748497
theorem B10294877 : Blo 1605001 10294877 := bstep (se 3 (by rfl) ⟨1930289, by rfl⟩ : syracuseStep 10294877 = 3860579) B3860579
theorem B4339403 : Blo 1605001 4339403 := bstep (se 1 (by rfl) ⟨3254552, by rfl⟩ : syracuseStep 4339403 = 6509105) B6509105
theorem B6100697 : Blo 1605001 6100697 := bstep (se 2 (by rfl) ⟨2287761, by rfl⟩ : syracuseStep 6100697 = 4575523) B4575523
theorem B5789485 : Blo 1605001 5789485 := bstep (se 3 (by rfl) ⟨1085528, by rfl⟩ : syracuseStep 5789485 = 2171057) B2171057
theorem B2709335 : Blo 1605001 2709335 := bstep (se 1 (by rfl) ⟨2032001, by rfl⟩ : syracuseStep 2709335 = 4064003) B4064003
theorem B3430259 : Blo 1605001 3430259 := bstep (se 1 (by rfl) ⟨2572694, by rfl⟩ : syracuseStep 3430259 = 5145389) B5145389
theorem B5420951 : Blo 1605001 5420951 := bstep (se 1 (by rfl) ⟨4065713, by rfl⟩ : syracuseStep 5420951 = 8131427) B8131427
theorem B18290609 : Blo 1605001 18290609 := bstep (se 2 (by rfl) ⟨6858978, by rfl⟩ : syracuseStep 18290609 = 13717957) B13717957
theorem B2709463 : Blo 1605001 2709463 := bstep (se 1 (by rfl) ⟨2032097, by rfl⟩ : syracuseStep 2709463 = 4064195) B4064195
theorem B39082135 : Blo 1605001 39082135 := bstep (se 1 (by rfl) ⟨29311601, by rfl⟩ : syracuseStep 39082135 = 58623203) B58623203
theorem B9902411 : Blo 1605001 9902411 := bstep (se 1 (by rfl) ⟨7426808, by rfl⟩ : syracuseStep 9902411 = 14853617) B14853617
theorem B5421491 : Blo 1605001 5421491 := bstep (se 1 (by rfl) ⟨4066118, by rfl⟩ : syracuseStep 5421491 = 8132237) B8132237
theorem B3430849 : Blo 1605001 3430849 := bstep (se 2 (by rfl) ⟨1286568, by rfl⟩ : syracuseStep 3430849 = 2573137) B2573137
theorem B4340189 : Blo 1605001 4340189 := bstep (se 3 (by rfl) ⟨813785, by rfl⟩ : syracuseStep 4340189 = 1627571) B1627571
theorem B4340299 : Blo 1605001 4340299 := bstep (se 1 (by rfl) ⟨3255224, by rfl⟩ : syracuseStep 4340299 = 6510449) B6510449
theorem B2710091 : Blo 1605001 2710091 := bstep (se 1 (by rfl) ⟨2032568, by rfl⟩ : syracuseStep 2710091 = 4065137) B4065137
theorem B5421761 : Blo 1605001 5421761 := bstep (se 2 (by rfl) ⟨2033160, by rfl⟩ : syracuseStep 5421761 = 4066321) B4066321
theorem B3611339 : Blo 1605001 3611339 := bstep (se 1 (by rfl) ⟨2708504, by rfl⟩ : syracuseStep 3611339 = 5417009) B5417009
theorem B2710219 : Blo 1605001 2710219 := bstep (se 1 (by rfl) ⟨2032664, by rfl⟩ : syracuseStep 2710219 = 4065329) B4065329
theorem B3611393 : Blo 1605001 3611393 := bstep (se 2 (by rfl) ⟨1354272, by rfl⟩ : syracuseStep 3611393 = 2708545) B2708545
theorem B2710361 : Blo 1605001 2710361 := bstep (se 2 (by rfl) ⟨1016385, by rfl⟩ : syracuseStep 2710361 = 2032771) B2032771
theorem B6183859 : Blo 1605001 6183859 := bstep (se 1 (by rfl) ⟨4637894, by rfl⟩ : syracuseStep 6183859 = 9275789) B9275789
theorem B1956811 : Blo 1605001 1956811 := bstep (se 1 (by rfl) ⟨1467608, by rfl⟩ : syracuseStep 1956811 = 2935217) B2935217
theorem B3611609 : Blo 1605001 3611609 := bstep (se 2 (by rfl) ⟨1354353, by rfl⟩ : syracuseStep 3611609 = 2708707) B2708707
theorem B2710489 : Blo 1605001 2710489 := bstep (se 2 (by rfl) ⟨1016433, by rfl⟩ : syracuseStep 2710489 = 2032867) B2032867
theorem B5143517 : Blo 1605001 5143517 := bstep (se 3 (by rfl) ⟨964409, by rfl⟩ : syracuseStep 5143517 = 1928819) B1928819
theorem B3611699 : Blo 1605001 3611699 := bstep (se 1 (by rfl) ⟨2708774, by rfl⟩ : syracuseStep 3611699 = 5417549) B5417549
theorem B5217331 : Blo 1605001 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B23149637 : Blo 1605001 23149637 := bstep (se 4 (by rfl) ⟨2170278, by rfl⟩ : syracuseStep 23149637 = 4340557) B4340557
theorem B2407511 : Blo 1605001 2407511 := bstep (se 1 (by rfl) ⟨1805633, by rfl⟩ : syracuseStep 2407511 = 3611267) B3611267
theorem B3611735 : Blo 1605001 3611735 := bstep (se 1 (by rfl) ⟨2708801, by rfl⟩ : syracuseStep 3611735 = 5417603) B5417603
theorem B2407577 : Blo 1605001 2407577 := bstep (se 2 (by rfl) ⟨902841, by rfl⟩ : syracuseStep 2407577 = 1805683) B1805683
theorem B5422301 : Blo 1605001 5422301 := bstep (se 3 (by rfl) ⟨1016681, by rfl⟩ : syracuseStep 5422301 = 2033363) B2033363
theorem B2407691 : Blo 1605001 2407691 := bstep (se 1 (by rfl) ⟨1805768, by rfl⟩ : syracuseStep 2407691 = 3611537) B3611537
theorem B3611915 : Blo 1605001 3611915 := bstep (se 1 (by rfl) ⟨2708936, by rfl⟩ : syracuseStep 3611915 = 5417873) B5417873
theorem B2407703 : Blo 1605001 2407703 := bstep (se 1 (by rfl) ⟨1805777, by rfl⟩ : syracuseStep 2407703 = 3611555) B3611555
theorem B2678039 : Blo 1605001 2678039 := bstep (se 1 (by rfl) ⟨2008529, by rfl⟩ : syracuseStep 2678039 = 4017059) B4017059
theorem B6864173 : Blo 1605001 6864173 := bstep (se 3 (by rfl) ⟨1287032, by rfl⟩ : syracuseStep 6864173 = 2574065) B2574065
theorem B9141569 : Blo 1605001 9141569 := bstep (se 2 (by rfl) ⟨3428088, by rfl⟩ : syracuseStep 9141569 = 6856177) B6856177
theorem B11132225 : Blo 1605001 11132225 := bstep (se 2 (by rfl) ⟨4174584, by rfl⟩ : syracuseStep 11132225 = 8349169) B8349169
theorem B3611969 : Blo 1605001 3611969 := bstep (se 2 (by rfl) ⟨1354488, by rfl⟩ : syracuseStep 3611969 = 2708977) B2708977
theorem B2407769 : Blo 1605001 2407769 := bstep (se 2 (by rfl) ⟨902913, by rfl⟩ : syracuseStep 2407769 = 1805827) B1805827
theorem B8134019 : Blo 1605001 8134019 := bstep (se 1 (by rfl) ⟨6100514, by rfl⟩ : syracuseStep 8134019 = 12201029) B12201029
theorem B1605003 : Blo 1605001 1605003 := bstep (se 1 (by rfl) ⟨1203752, by rfl⟩ : syracuseStep 1605003 = 2407505) B2407505
theorem B1605015 : Blo 1605001 1605015 := bstep (se 1 (by rfl) ⟨1203761, by rfl⟩ : syracuseStep 1605015 = 2407523) B2407523
theorem B1605035 : Blo 1605001 1605035 := bstep (se 1 (by rfl) ⟨1203776, by rfl⟩ : syracuseStep 1605035 = 2407553) B2407553
theorem B6856109 : Blo 1605001 6856109 := bstep (se 3 (by rfl) ⟨1285520, by rfl⟩ : syracuseStep 6856109 = 2571041) B2571041
theorem B1605047 : Blo 1605001 1605047 := bstep (se 1 (by rfl) ⟨1203785, by rfl⟩ : syracuseStep 1605047 = 2407571) B2407571
theorem B1605067 : Blo 1605001 1605067 := bstep (se 1 (by rfl) ⟨1203800, by rfl⟩ : syracuseStep 1605067 = 2407601) B2407601
theorem B2407883 : Blo 1605001 2407883 := bstep (se 1 (by rfl) ⟨1805912, by rfl⟩ : syracuseStep 2407883 = 3611825) B3611825
theorem B1605079 : Blo 1605001 1605079 := bstep (se 1 (by rfl) ⟨1203809, by rfl⟩ : syracuseStep 1605079 = 2407619) B2407619
theorem B2407895 : Blo 1605001 2407895 := bstep (se 1 (by rfl) ⟨1805921, by rfl⟩ : syracuseStep 2407895 = 3611843) B3611843
theorem B1605099 : Blo 1605001 1605099 := bstep (se 1 (by rfl) ⟨1203824, by rfl⟩ : syracuseStep 1605099 = 2407649) B2407649
theorem B1605111 : Blo 1605001 1605111 := bstep (se 1 (by rfl) ⟨1203833, by rfl⟩ : syracuseStep 1605111 = 2407667) B2407667
theorem B1605131 : Blo 1605001 1605131 := bstep (se 1 (by rfl) ⟨1203848, by rfl⟩ : syracuseStep 1605131 = 2407697) B2407697
theorem B1605143 : Blo 1605001 1605143 := bstep (se 1 (by rfl) ⟨1203857, by rfl⟩ : syracuseStep 1605143 = 2407715) B2407715
theorem B2407961 : Blo 1605001 2407961 := bstep (se 2 (by rfl) ⟨902985, by rfl⟩ : syracuseStep 2407961 = 1805971) B1805971
theorem B3612185 : Blo 1605001 3612185 := bstep (se 2 (by rfl) ⟨1354569, by rfl⟩ : syracuseStep 3612185 = 2709139) B2709139
theorem B2711063 : Blo 1605001 2711063 := bstep (se 1 (by rfl) ⟨2033297, by rfl⟩ : syracuseStep 2711063 = 4066595) B4066595
theorem B1605163 : Blo 1605001 1605163 := bstep (se 1 (by rfl) ⟨1203872, by rfl⟩ : syracuseStep 1605163 = 2407745) B2407745
theorem B1605175 : Blo 1605001 1605175 := bstep (se 1 (by rfl) ⟨1203881, by rfl⟩ : syracuseStep 1605175 = 2407763) B2407763
theorem B4341313 : Blo 1605001 4341313 := bstep (se 2 (by rfl) ⟨1627992, by rfl⟩ : syracuseStep 4341313 = 3255985) B3255985
theorem B1605195 : Blo 1605001 1605195 := bstep (se 1 (by rfl) ⟨1203896, by rfl⟩ : syracuseStep 1605195 = 2407793) B2407793
theorem B1605207 : Blo 1605001 1605207 := bstep (se 1 (by rfl) ⟨1203905, by rfl⟩ : syracuseStep 1605207 = 2407811) B2407811
theorem B1605227 : Blo 1605001 1605227 := bstep (se 1 (by rfl) ⟨1203920, by rfl⟩ : syracuseStep 1605227 = 2407841) B2407841
theorem B3612275 : Blo 1605001 3612275 := bstep (se 1 (by rfl) ⟨2709206, by rfl⟩ : syracuseStep 3612275 = 5418413) B5418413
theorem B1605239 : Blo 1605001 1605239 := bstep (se 1 (by rfl) ⟨1203929, by rfl⟩ : syracuseStep 1605239 = 2407859) B2407859
theorem B1605259 : Blo 1605001 1605259 := bstep (se 1 (by rfl) ⟨1203944, by rfl⟩ : syracuseStep 1605259 = 2407889) B2407889
theorem B2408075 : Blo 1605001 2408075 := bstep (se 1 (by rfl) ⟨1806056, by rfl⟩ : syracuseStep 2408075 = 3612113) B3612113
theorem B1605271 : Blo 1605001 1605271 := bstep (se 1 (by rfl) ⟨1203953, by rfl⟩ : syracuseStep 1605271 = 2407907) B2407907
theorem B2408087 : Blo 1605001 2408087 := bstep (se 1 (by rfl) ⟨1806065, by rfl⟩ : syracuseStep 2408087 = 3612131) B3612131
theorem B3612311 : Blo 1605001 3612311 := bstep (se 1 (by rfl) ⟨2709233, by rfl⟩ : syracuseStep 3612311 = 5418467) B5418467
theorem B2711191 : Blo 1605001 2711191 := bstep (se 1 (by rfl) ⟨2033393, by rfl⟩ : syracuseStep 2711191 = 4066787) B4066787
theorem B1605291 : Blo 1605001 1605291 := bstep (se 1 (by rfl) ⟨1203968, by rfl⟩ : syracuseStep 1605291 = 2407937) B2407937
theorem B4062899 : Blo 1605001 4062899 := bstep (se 1 (by rfl) ⟨3047174, by rfl⟩ : syracuseStep 4062899 = 6094349) B6094349
theorem B1605303 : Blo 1605001 1605303 := bstep (se 1 (by rfl) ⟨1203977, by rfl⟩ : syracuseStep 1605303 = 2407955) B2407955
theorem B1605323 : Blo 1605001 1605323 := bstep (se 1 (by rfl) ⟨1203992, by rfl⟩ : syracuseStep 1605323 = 2407985) B2407985
theorem B1605335 : Blo 1605001 1605335 := bstep (se 1 (by rfl) ⟨1204001, by rfl⟩ : syracuseStep 1605335 = 2408003) B2408003
theorem B2285273 : Blo 1605001 2285273 := bstep (se 2 (by rfl) ⟨856977, by rfl⟩ : syracuseStep 2285273 = 1713955) B1713955
theorem B3047129 : Blo 1605001 3047129 := bstep (se 2 (by rfl) ⟨1142673, by rfl⟩ : syracuseStep 3047129 = 2285347) B2285347
theorem B2408153 : Blo 1605001 2408153 := bstep (se 2 (by rfl) ⟨903057, by rfl⟩ : syracuseStep 2408153 = 1806115) B1806115
theorem B1605355 : Blo 1605001 1605355 := bstep (se 1 (by rfl) ⟨1204016, by rfl⟩ : syracuseStep 1605355 = 2408033) B2408033
theorem B1605367 : Blo 1605001 1605367 := bstep (se 1 (by rfl) ⟨1204025, by rfl⟩ : syracuseStep 1605367 = 2408051) B2408051
theorem B6856451 : Blo 1605001 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B1605387 : Blo 1605001 1605387 := bstep (se 1 (by rfl) ⟨1204040, by rfl⟩ : syracuseStep 1605387 = 2408081) B2408081
theorem B1605399 : Blo 1605001 1605399 := bstep (se 1 (by rfl) ⟨1204049, by rfl⟩ : syracuseStep 1605399 = 2408099) B2408099
theorem B6602519 : Blo 1605001 6602519 := bstep (se 1 (by rfl) ⟨4951889, by rfl⟩ : syracuseStep 6602519 = 9903779) B9903779
theorem B1605419 : Blo 1605001 1605419 := bstep (se 1 (by rfl) ⟨1204064, by rfl⟩ : syracuseStep 1605419 = 2408129) B2408129
theorem B1605431 : Blo 1605001 1605431 := bstep (se 1 (by rfl) ⟨1204073, by rfl⟩ : syracuseStep 1605431 = 2408147) B2408147
theorem B1605451 : Blo 1605001 1605451 := bstep (se 1 (by rfl) ⟨1204088, by rfl⟩ : syracuseStep 1605451 = 2408177) B2408177
theorem B2408267 : Blo 1605001 2408267 := bstep (se 1 (by rfl) ⟨1806200, by rfl⟩ : syracuseStep 2408267 = 3612401) B3612401
theorem B3612491 : Blo 1605001 3612491 := bstep (se 1 (by rfl) ⟨2709368, by rfl⟩ : syracuseStep 3612491 = 5418737) B5418737
theorem B1605463 : Blo 1605001 1605463 := bstep (se 1 (by rfl) ⟨1204097, by rfl⟩ : syracuseStep 1605463 = 2408195) B2408195
theorem B2408279 : Blo 1605001 2408279 := bstep (se 1 (by rfl) ⟨1806209, by rfl⟩ : syracuseStep 2408279 = 3612419) B3612419
theorem B1605483 : Blo 1605001 1605483 := bstep (se 1 (by rfl) ⟨1204112, by rfl⟩ : syracuseStep 1605483 = 2408225) B2408225
theorem B1605495 : Blo 1605001 1605495 := bstep (se 1 (by rfl) ⟨1204121, by rfl⟩ : syracuseStep 1605495 = 2408243) B2408243
theorem B3612545 : Blo 1605001 3612545 := bstep (se 2 (by rfl) ⟨1354704, by rfl⟩ : syracuseStep 3612545 = 2709409) B2709409
theorem B1605515 : Blo 1605001 1605515 := bstep (se 1 (by rfl) ⟨1204136, by rfl⟩ : syracuseStep 1605515 = 2408273) B2408273
theorem B1605527 : Blo 1605001 1605527 := bstep (se 1 (by rfl) ⟨1204145, by rfl⟩ : syracuseStep 1605527 = 2408291) B2408291
theorem B2408345 : Blo 1605001 2408345 := bstep (se 2 (by rfl) ⟨903129, by rfl⟩ : syracuseStep 2408345 = 1806259) B1806259
theorem B1605547 : Blo 1605001 1605547 := bstep (se 1 (by rfl) ⟨1204160, by rfl⟩ : syracuseStep 1605547 = 2408321) B2408321
theorem B1605559 : Blo 1605001 1605559 := bstep (se 1 (by rfl) ⟨1204169, by rfl⟩ : syracuseStep 1605559 = 2408339) B2408339
theorem B1605579 : Blo 1605001 1605579 := bstep (se 1 (by rfl) ⟨1204184, by rfl⟩ : syracuseStep 1605579 = 2408369) B2408369
theorem B1605591 : Blo 1605001 1605591 := bstep (se 1 (by rfl) ⟨1204193, by rfl⟩ : syracuseStep 1605591 = 2408387) B2408387
theorem B4063193 : Blo 1605001 4063193 := bstep (se 2 (by rfl) ⟨1523697, by rfl⟩ : syracuseStep 4063193 = 3047395) B3047395
theorem B1605611 : Blo 1605001 1605611 := bstep (se 1 (by rfl) ⟨1204208, by rfl⟩ : syracuseStep 1605611 = 2408417) B2408417
theorem B1605623 : Blo 1605001 1605623 := bstep (se 1 (by rfl) ⟨1204217, by rfl⟩ : syracuseStep 1605623 = 2408435) B2408435
theorem B1605639 : Blo 1605001 1605639 := bstep (se 1 (by rfl) ⟨1204229, by rfl⟩ : syracuseStep 1605639 = 2408459) B2408459
theorem B4063243 : Blo 1605001 4063243 := bstep (se 1 (by rfl) ⟨3047432, by rfl⟩ : syracuseStep 4063243 = 6094865) B6094865
theorem B1605647 : Blo 1605001 1605647 := bstep (se 1 (by rfl) ⟨1204235, by rfl⟩ : syracuseStep 1605647 = 2408471) B2408471
theorem B2408507 : Blo 1605001 2408507 := bstep (se 1 (by rfl) ⟨1806380, by rfl⟩ : syracuseStep 2408507 = 3612761) B3612761
theorem B1605691 : Blo 1605001 1605691 := bstep (se 1 (by rfl) ⟨1204268, by rfl⟩ : syracuseStep 1605691 = 2408537) B2408537
theorem B5423165 : Blo 1605001 5423165 := bstep (se 3 (by rfl) ⟨1016843, by rfl⟩ : syracuseStep 5423165 = 2033687) B2033687
theorem B2408567 : Blo 1605001 2408567 := bstep (se 1 (by rfl) ⟨1806425, by rfl⟩ : syracuseStep 2408567 = 3612851) B3612851
theorem B2441351 : Blo 1605001 2441351 := bstep (se 1 (by rfl) ⟨1831013, by rfl⟩ : syracuseStep 2441351 = 3662027) B3662027
theorem B1605767 : Blo 1605001 1605767 := bstep (se 1 (by rfl) ⟨1204325, by rfl⟩ : syracuseStep 1605767 = 2408651) B2408651
theorem B2408591 : Blo 1605001 2408591 := bstep (se 1 (by rfl) ⟨1806443, by rfl⟩ : syracuseStep 2408591 = 3612887) B3612887
theorem B1605775 : Blo 1605001 1605775 := bstep (se 1 (by rfl) ⟨1204331, by rfl⟩ : syracuseStep 1605775 = 2408663) B2408663
theorem B3571859 : Blo 1605001 3571859 := bstep (se 1 (by rfl) ⟨2678894, by rfl⟩ : syracuseStep 3571859 = 5357789) B5357789
theorem B4063385 : Blo 1605001 4063385 := bstep (se 2 (by rfl) ⟨1523769, by rfl⟩ : syracuseStep 4063385 = 3047539) B3047539
theorem B15433901 : Blo 1605001 15433901 := bstep (se 3 (by rfl) ⟨2893856, by rfl⟩ : syracuseStep 15433901 = 5787713) B5787713
theorem B2408633 : Blo 1605001 2408633 := bstep (se 2 (by rfl) ⟨903237, by rfl⟩ : syracuseStep 2408633 = 1806475) B1806475
theorem B1605819 : Blo 1605001 1605819 := bstep (se 1 (by rfl) ⟨1204364, by rfl⟩ : syracuseStep 1605819 = 2408729) B2408729
theorem B2572489 : Blo 1605001 2572489 := bstep (se 2 (by rfl) ⟨964683, by rfl⟩ : syracuseStep 2572489 = 1929367) B1929367
theorem B52109513 : Blo 1605001 52109513 := bstep (se 2 (by rfl) ⟨19541067, by rfl⟩ : syracuseStep 52109513 = 39082135) B39082135
theorem B2408711 : Blo 1605001 2408711 := bstep (se 1 (by rfl) ⟨1806533, by rfl⟩ : syracuseStep 2408711 = 3613067) B3613067
theorem B1605895 : Blo 1605001 1605895 := bstep (se 1 (by rfl) ⟨1204421, by rfl⟩ : syracuseStep 1605895 = 2408843) B2408843
theorem B1605903 : Blo 1605001 1605903 := bstep (se 1 (by rfl) ⟨1204427, by rfl⟩ : syracuseStep 1605903 = 2408855) B2408855
theorem B2408747 : Blo 1605001 2408747 := bstep (se 1 (by rfl) ⟨1806560, by rfl⟩ : syracuseStep 2408747 = 3613121) B3613121
theorem B8134667 : Blo 1605001 8134667 := bstep (se 1 (by rfl) ⟨6101000, by rfl⟩ : syracuseStep 8134667 = 12202001) B12202001
theorem B19792187 : Blo 1605001 19792187 := bstep (se 1 (by rfl) ⟨14844140, by rfl⟩ : syracuseStep 19792187 = 29688281) B29688281
theorem B4063547 : Blo 1605001 4063547 := bstep (se 1 (by rfl) ⟨3047660, by rfl⟩ : syracuseStep 4063547 = 6095321) B6095321
theorem B1605947 : Blo 1605001 1605947 := bstep (se 1 (by rfl) ⟨1204460, by rfl⟩ : syracuseStep 1605947 = 2408921) B2408921
theorem B33407297 : Blo 1605001 33407297 := bstep (se 2 (by rfl) ⟨12527736, by rfl⟩ : syracuseStep 33407297 = 25055473) B25055473
theorem B2408777 : Blo 1605001 2408777 := bstep (se 2 (by rfl) ⟨903291, by rfl⟩ : syracuseStep 2408777 = 1806583) B1806583
theorem B70377821 : Blo 1605001 70377821 := bstep (se 3 (by rfl) ⟨13195841, by rfl⟩ : syracuseStep 70377821 = 26391683) B26391683
theorem B4342135 : Blo 1605001 4342135 := bstep (se 1 (by rfl) ⟨3256601, by rfl⟩ : syracuseStep 4342135 = 6513203) B6513203
theorem B1606023 : Blo 1605001 1606023 := bstep (se 1 (by rfl) ⟨1204517, by rfl⟩ : syracuseStep 1606023 = 2409035) B2409035
theorem B1606031 : Blo 1605001 1606031 := bstep (se 1 (by rfl) ⟨1204523, by rfl⟩ : syracuseStep 1606031 = 2409047) B2409047
theorem B9773459 : Blo 1605001 9773459 := bstep (se 1 (by rfl) ⟨7330094, by rfl⟩ : syracuseStep 9773459 = 14660189) B14660189
theorem B2408891 : Blo 1605001 2408891 := bstep (se 1 (by rfl) ⟨1806668, by rfl⟩ : syracuseStep 2408891 = 3613337) B3613337
theorem B1606075 : Blo 1605001 1606075 := bstep (se 1 (by rfl) ⟨1204556, by rfl⟩ : syracuseStep 1606075 = 2409113) B2409113
theorem B3047881 : Blo 1605001 3047881 := bstep (se 2 (by rfl) ⟨1142955, by rfl⟩ : syracuseStep 3047881 = 2285911) B2285911
theorem B11887069 : Blo 1605001 11887069 := bstep (se 3 (by rfl) ⟨2228825, by rfl⟩ : syracuseStep 11887069 = 4457651) B4457651
theorem B2408951 : Blo 1605001 2408951 := bstep (se 1 (by rfl) ⟨1806713, by rfl⟩ : syracuseStep 2408951 = 3613427) B3613427
theorem B1606151 : Blo 1605001 1606151 := bstep (se 1 (by rfl) ⟨1204613, by rfl⟩ : syracuseStep 1606151 = 2409227) B2409227
theorem B2408975 : Blo 1605001 2408975 := bstep (se 1 (by rfl) ⟨1806731, by rfl⟩ : syracuseStep 2408975 = 3613463) B3613463
theorem B1606159 : Blo 1605001 1606159 := bstep (se 1 (by rfl) ⟨1204619, by rfl⟩ : syracuseStep 1606159 = 2409239) B2409239
theorem B2409017 : Blo 1605001 2409017 := bstep (se 2 (by rfl) ⟨903381, by rfl⟩ : syracuseStep 2409017 = 1806763) B1806763
theorem B2286139 : Blo 1605001 2286139 := bstep (se 1 (by rfl) ⟨1714604, by rfl⟩ : syracuseStep 2286139 = 3429209) B3429209
theorem B1606203 : Blo 1605001 1606203 := bstep (se 1 (by rfl) ⟨1204652, by rfl⟩ : syracuseStep 1606203 = 2409305) B2409305
theorem B3613319 : Blo 1605001 3613319 := bstep (se 1 (by rfl) ⟨2709989, by rfl⟩ : syracuseStep 3613319 = 5419979) B5419979
theorem B2409095 : Blo 1605001 2409095 := bstep (se 1 (by rfl) ⟨1806821, by rfl⟩ : syracuseStep 2409095 = 3613643) B3613643
theorem B1606279 : Blo 1605001 1606279 := bstep (se 1 (by rfl) ⟨1204709, by rfl⟩ : syracuseStep 1606279 = 2409419) B2409419
theorem B1606287 : Blo 1605001 1606287 := bstep (se 1 (by rfl) ⟨1204715, by rfl⟩ : syracuseStep 1606287 = 2409431) B2409431
theorem B4063891 : Blo 1605001 4063891 := bstep (se 1 (by rfl) ⟨3047918, by rfl⟩ : syracuseStep 4063891 = 6095837) B6095837
theorem B2409131 : Blo 1605001 2409131 := bstep (se 1 (by rfl) ⟨1806848, by rfl⟩ : syracuseStep 2409131 = 3613697) B3613697
theorem B1606331 : Blo 1605001 1606331 := bstep (se 1 (by rfl) ⟨1204748, by rfl⟩ : syracuseStep 1606331 = 2409497) B2409497
theorem B2409161 : Blo 1605001 2409161 := bstep (se 2 (by rfl) ⟨903435, by rfl⟩ : syracuseStep 2409161 = 1806871) B1806871
theorem B2032391 : Blo 1605001 2032391 := bstep (se 1 (by rfl) ⟨1524293, by rfl⟩ : syracuseStep 2032391 = 3048587) B3048587
theorem B1606407 : Blo 1605001 1606407 := bstep (se 1 (by rfl) ⟨1204805, by rfl⟩ : syracuseStep 1606407 = 2409611) B2409611
theorem B1606415 : Blo 1605001 1606415 := bstep (se 1 (by rfl) ⟨1204811, by rfl⟩ : syracuseStep 1606415 = 2409623) B2409623
theorem B4064033 : Blo 1605001 4064033 := bstep (se 2 (by rfl) ⟨1524012, by rfl⟩ : syracuseStep 4064033 = 3048025) B3048025
theorem B125190947 : Blo 1605001 125190947 := bstep (se 1 (by rfl) ⟨93893210, by rfl⟩ : syracuseStep 125190947 = 187786421) B187786421
theorem B3613499 : Blo 1605001 3613499 := bstep (se 1 (by rfl) ⟨2710124, by rfl⟩ : syracuseStep 3613499 = 5420249) B5420249
theorem B2409275 : Blo 1605001 2409275 := bstep (se 1 (by rfl) ⟨1806956, by rfl⟩ : syracuseStep 2409275 = 3613913) B3613913
theorem B4399933 : Blo 1605001 4399933 := bstep (se 3 (by rfl) ⟨824987, by rfl⟩ : syracuseStep 4399933 = 1649975) B1649975
theorem B1606459 : Blo 1605001 1606459 := bstep (se 1 (by rfl) ⟨1204844, by rfl⟩ : syracuseStep 1606459 = 2409689) B2409689
theorem B2409335 : Blo 1605001 2409335 := bstep (se 1 (by rfl) ⟨1807001, by rfl⟩ : syracuseStep 2409335 = 3614003) B3614003
theorem B1606535 : Blo 1605001 1606535 := bstep (se 1 (by rfl) ⟨1204901, by rfl⟩ : syracuseStep 1606535 = 2409803) B2409803
theorem B2409359 : Blo 1605001 2409359 := bstep (se 1 (by rfl) ⟨1807019, by rfl⟩ : syracuseStep 2409359 = 3614039) B3614039
theorem B1606543 : Blo 1605001 1606543 := bstep (se 1 (by rfl) ⟨1204907, by rfl⟩ : syracuseStep 1606543 = 2409815) B2409815
theorem B8127377 : Blo 1605001 8127377 := bstep (se 2 (by rfl) ⟨3047766, by rfl⟩ : syracuseStep 8127377 = 6095533) B6095533
theorem B7824281 : Blo 1605001 7824281 := bstep (se 2 (by rfl) ⟨2934105, by rfl⟩ : syracuseStep 7824281 = 5868211) B5868211
theorem B3613625 : Blo 1605001 3613625 := bstep (se 2 (by rfl) ⟨1355109, by rfl⟩ : syracuseStep 3613625 = 2710219) B2710219
theorem B2409401 : Blo 1605001 2409401 := bstep (se 2 (by rfl) ⟨903525, by rfl⟩ : syracuseStep 2409401 = 1807051) B1807051
theorem B1606587 : Blo 1605001 1606587 := bstep (se 1 (by rfl) ⟨1204940, by rfl⟩ : syracuseStep 1606587 = 2409881) B2409881
theorem B8684509 : Blo 1605001 8684509 := bstep (se 3 (by rfl) ⟨1628345, by rfl⟩ : syracuseStep 8684509 = 3256691) B3256691
theorem B2409479 : Blo 1605001 2409479 := bstep (se 1 (by rfl) ⟨1807109, by rfl⟩ : syracuseStep 2409479 = 3614219) B3614219
theorem B1606663 : Blo 1605001 1606663 := bstep (se 1 (by rfl) ⟨1204997, by rfl⟩ : syracuseStep 1606663 = 2409995) B2409995
theorem B1606671 : Blo 1605001 1606671 := bstep (se 1 (by rfl) ⟨1205003, by rfl⟩ : syracuseStep 1606671 = 2410007) B2410007
theorem B2409515 : Blo 1605001 2409515 := bstep (se 1 (by rfl) ⟨1807136, by rfl⟩ : syracuseStep 2409515 = 3614273) B3614273
theorem B1606715 : Blo 1605001 1606715 := bstep (se 1 (by rfl) ⟨1205036, by rfl⟩ : syracuseStep 1606715 = 2410073) B2410073
theorem B2409545 : Blo 1605001 2409545 := bstep (se 2 (by rfl) ⟨903579, by rfl⟩ : syracuseStep 2409545 = 1807159) B1807159
theorem B8134829 : Blo 1605001 8134829 := bstep (se 3 (by rfl) ⟨1525280, by rfl⟩ : syracuseStep 8134829 = 3050561) B3050561
theorem B2892935 : Blo 1605001 2892935 := bstep (se 1 (by rfl) ⟨2169701, by rfl⟩ : syracuseStep 2892935 = 4339403) B4339403
theorem B1606791 : Blo 1605001 1606791 := bstep (se 1 (by rfl) ⟨1205093, by rfl⟩ : syracuseStep 1606791 = 2410187) B2410187
theorem B1606799 : Blo 1605001 1606799 := bstep (se 1 (by rfl) ⟨1205099, by rfl⟩ : syracuseStep 1606799 = 2410199) B2410199
theorem B12199085 : Blo 1605001 12199085 := bstep (se 3 (by rfl) ⟨2287328, by rfl⟩ : syracuseStep 12199085 = 4574657) B4574657
theorem B2409659 : Blo 1605001 2409659 := bstep (se 1 (by rfl) ⟨1807244, by rfl⟩ : syracuseStep 2409659 = 3614489) B3614489
theorem B1606843 : Blo 1605001 1606843 := bstep (se 1 (by rfl) ⟨1205132, by rfl⟩ : syracuseStep 1606843 = 2410265) B2410265
theorem B2286839 : Blo 1605001 2286839 := bstep (se 1 (by rfl) ⟨1715129, by rfl⟩ : syracuseStep 2286839 = 3430259) B3430259
theorem B2409719 : Blo 1605001 2409719 := bstep (se 1 (by rfl) ⟨1807289, by rfl⟩ : syracuseStep 2409719 = 3614579) B3614579
theorem B1606919 : Blo 1605001 1606919 := bstep (se 1 (by rfl) ⟨1205189, by rfl⟩ : syracuseStep 1606919 = 2410379) B2410379
theorem B3613967 : Blo 1605001 3613967 := bstep (se 1 (by rfl) ⟨2710475, by rfl⟩ : syracuseStep 3613967 = 5420951) B5420951
theorem B2409743 : Blo 1605001 2409743 := bstep (se 1 (by rfl) ⟨1807307, by rfl⟩ : syracuseStep 2409743 = 3614615) B3614615
theorem B1606927 : Blo 1605001 1606927 := bstep (se 1 (by rfl) ⟨1205195, by rfl⟩ : syracuseStep 1606927 = 2410391) B2410391
theorem B3613985 : Blo 1605001 3613985 := bstep (se 2 (by rfl) ⟨1355244, by rfl⟩ : syracuseStep 3613985 = 2710489) B2710489
theorem B2409785 : Blo 1605001 2409785 := bstep (se 2 (by rfl) ⟨903669, by rfl⟩ : syracuseStep 2409785 = 1807339) B1807339
theorem B1606971 : Blo 1605001 1606971 := bstep (se 1 (by rfl) ⟨1205228, by rfl⟩ : syracuseStep 1606971 = 2410457) B2410457
theorem B34743653 : Blo 1605001 34743653 := bstep (se 4 (by rfl) ⟨3257217, by rfl⟩ : syracuseStep 34743653 = 6514435) B6514435
theorem B4572551 : Blo 1605001 4572551 := bstep (se 1 (by rfl) ⟨3429413, by rfl⟩ : syracuseStep 4572551 = 6858827) B6858827
theorem B2409863 : Blo 1605001 2409863 := bstep (se 1 (by rfl) ⟨1807397, by rfl⟩ : syracuseStep 2409863 = 3614795) B3614795
theorem B2033039 : Blo 1605001 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B6956441 : Blo 1605001 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B2409899 : Blo 1605001 2409899 := bstep (se 1 (by rfl) ⟨1807424, by rfl⟩ : syracuseStep 2409899 = 3614849) B3614849
theorem B2409929 : Blo 1605001 2409929 := bstep (se 2 (by rfl) ⟨903723, by rfl⟩ : syracuseStep 2409929 = 1807447) B1807447
theorem B2442767 : Blo 1605001 2442767 := bstep (se 1 (by rfl) ⟨1832075, by rfl⟩ : syracuseStep 2442767 = 3664151) B3664151
theorem B7718429 : Blo 1605001 7718429 := bstep (se 3 (by rfl) ⟨1447205, by rfl⟩ : syracuseStep 7718429 = 2894411) B2894411
theorem B2410043 : Blo 1605001 2410043 := bstep (se 1 (by rfl) ⟨1807532, by rfl⟩ : syracuseStep 2410043 = 3615065) B3615065
theorem B4572733 : Blo 1605001 4572733 := bstep (se 3 (by rfl) ⟨857387, by rfl⟩ : syracuseStep 4572733 = 1714775) B1714775
theorem B12191309 : Blo 1605001 12191309 := bstep (se 3 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 12191309 = 4571741) B4571741
theorem B3614327 : Blo 1605001 3614327 := bstep (se 1 (by rfl) ⟨2710745, by rfl⟩ : syracuseStep 3614327 = 5421491) B5421491
theorem B2410103 : Blo 1605001 2410103 := bstep (se 1 (by rfl) ⟨1807577, by rfl⟩ : syracuseStep 2410103 = 3615155) B3615155
theorem B2410127 : Blo 1605001 2410127 := bstep (se 1 (by rfl) ⟨1807595, by rfl⟩ : syracuseStep 2410127 = 3615191) B3615191
theorem B2410169 : Blo 1605001 2410169 := bstep (se 2 (by rfl) ⟨903813, by rfl⟩ : syracuseStep 2410169 = 1807627) B1807627
theorem B4065025 : Blo 1605001 4065025 := bstep (se 2 (by rfl) ⟨1524384, by rfl⟩ : syracuseStep 4065025 = 3048769) B3048769
theorem B2410247 : Blo 1605001 2410247 := bstep (se 1 (by rfl) ⟨1807685, by rfl⟩ : syracuseStep 2410247 = 3615371) B3615371
theorem B3614507 : Blo 1605001 3614507 := bstep (se 1 (by rfl) ⟨2710880, by rfl⟩ : syracuseStep 3614507 = 5421761) B5421761
theorem B2410283 : Blo 1605001 2410283 := bstep (se 1 (by rfl) ⟨1807712, by rfl⟩ : syracuseStep 2410283 = 3615425) B3615425
theorem B2410313 : Blo 1605001 2410313 := bstep (se 2 (by rfl) ⟨903867, by rfl⟩ : syracuseStep 2410313 = 1807735) B1807735
theorem B9144211 : Blo 1605001 9144211 := bstep (se 1 (by rfl) ⟨6858158, by rfl⟩ : syracuseStep 9144211 = 13716317) B13716317
theorem B2410427 : Blo 1605001 2410427 := bstep (se 1 (by rfl) ⟨1807820, by rfl⟩ : syracuseStep 2410427 = 3615641) B3615641
theorem B2410487 : Blo 1605001 2410487 := bstep (se 1 (by rfl) ⟨1807865, by rfl⟩ : syracuseStep 2410487 = 3615731) B3615731
theorem B4573199 : Blo 1605001 4573199 := bstep (se 1 (by rfl) ⟨3429899, by rfl⟩ : syracuseStep 4573199 = 6859799) B6859799
theorem B17606717 : Blo 1605001 17606717 := bstep (se 3 (by rfl) ⟨3301259, by rfl⟩ : syracuseStep 17606717 = 6602519) B6602519
theorem B14092375 : Blo 1605001 14092375 := bstep (se 1 (by rfl) ⟨10569281, by rfl⟩ : syracuseStep 14092375 = 21138563) B21138563
theorem B8357975 : Blo 1605001 8357975 := bstep (se 1 (by rfl) ⟨6268481, by rfl⟩ : syracuseStep 8357975 = 12536963) B12536963
theorem B3614867 : Blo 1605001 3614867 := bstep (se 1 (by rfl) ⟨2711150, by rfl⟩ : syracuseStep 3614867 = 5422301) B5422301
theorem B3614921 : Blo 1605001 3614921 := bstep (se 2 (by rfl) ⟨1355595, by rfl⟩ : syracuseStep 3614921 = 2711191) B2711191
theorem B3049787 : Blo 1605001 3049787 := bstep (se 1 (by rfl) ⟨2287340, by rfl⟩ : syracuseStep 3049787 = 4574681) B4574681
theorem B4065623 : Blo 1605001 4065623 := bstep (se 1 (by rfl) ⟨3049217, by rfl⟩ : syracuseStep 4065623 = 6098435) B6098435
theorem B7719313 : Blo 1605001 7719313 := bstep (se 2 (by rfl) ⟨2894742, by rfl⟩ : syracuseStep 7719313 = 5789485) B5789485
theorem B15436241 : Blo 1605001 15436241 := bstep (se 2 (by rfl) ⟨5788590, by rfl⟩ : syracuseStep 15436241 = 11577181) B11577181
theorem B4065835 : Blo 1605001 4065835 := bstep (se 1 (by rfl) ⟨3049376, by rfl⟩ : syracuseStep 4065835 = 6098753) B6098753
theorem B4065977 : Blo 1605001 4065977 := bstep (se 2 (by rfl) ⟨1524741, by rfl⟩ : syracuseStep 4065977 = 3049483) B3049483
theorem B3050273 : Blo 1605001 3050273 := bstep (se 2 (by rfl) ⟨1143852, by rfl⟩ : syracuseStep 3050273 = 2287705) B2287705
theorem B4402039 : Blo 1605001 4402039 := bstep (se 1 (by rfl) ⟨3301529, by rfl⟩ : syracuseStep 4402039 = 6603059) B6603059
theorem B3255175 : Blo 1605001 3255175 := bstep (se 1 (by rfl) ⟨2441381, by rfl⟩ : syracuseStep 3255175 = 4882763) B4882763
theorem B3615623 : Blo 1605001 3615623 := bstep (se 1 (by rfl) ⟨2711717, by rfl⟩ : syracuseStep 3615623 = 5423435) B5423435
theorem B11733913 : Blo 1605001 11733913 := bstep (se 2 (by rfl) ⟨4400217, by rfl⟩ : syracuseStep 11733913 = 8800435) B8800435
theorem B15428555 : Blo 1605001 15428555 := bstep (se 1 (by rfl) ⟨11571416, by rfl⟩ : syracuseStep 15428555 = 23142833) B23142833
theorem B8129483 : Blo 1605001 8129483 := bstep (se 1 (by rfl) ⟨6097112, by rfl⟩ : syracuseStep 8129483 = 12194225) B12194225
theorem B6097949 : Blo 1605001 6097949 := bstep (se 3 (by rfl) ⟨1143365, by rfl⟩ : syracuseStep 6097949 = 2286731) B2286731
theorem B6097963 : Blo 1605001 6097963 := bstep (se 1 (by rfl) ⟨4573472, by rfl⟩ : syracuseStep 6097963 = 9146945) B9146945
theorem B3050615 : Blo 1605001 3050615 := bstep (se 1 (by rfl) ⟨2287961, by rfl⟩ : syracuseStep 3050615 = 4575923) B4575923
theorem B5147849 : Blo 1605001 5147849 := bstep (se 2 (by rfl) ⟨1930443, by rfl⟩ : syracuseStep 5147849 = 3860887) B3860887
theorem B4574465 : Blo 1605001 4574465 := bstep (se 2 (by rfl) ⟨1715424, by rfl⟩ : syracuseStep 4574465 = 3430849) B3430849
theorem B8129807 : Blo 1605001 8129807 := bstep (se 1 (by rfl) ⟨6097355, by rfl⟩ : syracuseStep 8129807 = 12194711) B12194711
theorem B1928507 : Blo 1605001 1928507 := bstep (se 1 (by rfl) ⟨1446380, by rfl⟩ : syracuseStep 1928507 = 2892761) B2892761
theorem B1715599 : Blo 1605001 1715599 := bstep (se 1 (by rfl) ⟨1286699, by rfl⟩ : syracuseStep 1715599 = 2573399) B2573399
theorem B5787065 : Blo 1605001 5787065 := bstep (se 2 (by rfl) ⟨2170149, by rfl⟩ : syracuseStep 5787065 = 4340299) B4340299
theorem B1805755 : Blo 1605001 1805755 := bstep (se 1 (by rfl) ⟨1354316, by rfl⟩ : syracuseStep 1805755 = 2708633) B2708633
theorem B5787179 : Blo 1605001 5787179 := bstep (se 1 (by rfl) ⟨4340384, by rfl⟩ : syracuseStep 5787179 = 8680769) B8680769
theorem B12201515 : Blo 1605001 12201515 := bstep (se 1 (by rfl) ⟨9151136, by rfl⟩ : syracuseStep 12201515 = 18302273) B18302273
theorem B9145943 : Blo 1605001 9145943 := bstep (se 1 (by rfl) ⟨6859457, by rfl⟩ : syracuseStep 9145943 = 13718915) B13718915
theorem B4066969 : Blo 1605001 4066969 := bstep (se 2 (by rfl) ⟨1525113, by rfl⟩ : syracuseStep 4066969 = 3050227) B3050227
theorem B4067131 : Blo 1605001 4067131 := bstep (se 1 (by rfl) ⟨3050348, by rfl⟩ : syracuseStep 4067131 = 6100697) B6100697
theorem B1806223 : Blo 1605001 1806223 := bstep (se 1 (by rfl) ⟨1354667, by rfl⟩ : syracuseStep 1806223 = 2709335) B2709335
theorem B5418899 : Blo 1605001 5418899 := bstep (se 1 (by rfl) ⟨4064174, by rfl⟩ : syracuseStep 5418899 = 8128349) B8128349
theorem B8245145 : Blo 1605001 8245145 := bstep (se 2 (by rfl) ⟨3091929, by rfl⟩ : syracuseStep 8245145 = 6183859) B6183859
theorem B2609081 : Blo 1605001 2609081 := bstep (se 2 (by rfl) ⟨978405, by rfl⟩ : syracuseStep 2609081 = 1956811) B1956811
theorem B4067273 : Blo 1605001 4067273 := bstep (se 2 (by rfl) ⟨1525227, by rfl⟩ : syracuseStep 4067273 = 3050455) B3050455
theorem B12193739 : Blo 1605001 12193739 := bstep (se 1 (by rfl) ⟨9145304, by rfl⟩ : syracuseStep 12193739 = 18290609) B18290609
theorem B4067617 : Blo 1605001 4067617 := bstep (se 2 (by rfl) ⟨1525356, by rfl⟩ : syracuseStep 4067617 = 3050713) B3050713
theorem B1806727 : Blo 1605001 1806727 := bstep (se 1 (by rfl) ⟨1355045, by rfl⟩ : syracuseStep 1806727 = 2710091) B2710091
theorem B1806907 : Blo 1605001 1806907 := bstep (se 1 (by rfl) ⟨1355180, by rfl⟩ : syracuseStep 1806907 = 2710361) B2710361
theorem B3429011 : Blo 1605001 3429011 := bstep (se 1 (by rfl) ⟨2571758, by rfl⟩ : syracuseStep 3429011 = 5143517) B5143517
theorem B8131265 : Blo 1605001 8131265 := bstep (se 2 (by rfl) ⟨3049224, by rfl⟩ : syracuseStep 8131265 = 6098449) B6098449
theorem B5788417 : Blo 1605001 5788417 := bstep (se 2 (by rfl) ⟨2170656, by rfl⟩ : syracuseStep 5788417 = 4341313) B4341313
theorem B4576115 : Blo 1605001 4576115 := bstep (se 1 (by rfl) ⟨3432086, by rfl⟩ : syracuseStep 4576115 = 6864173) B6864173
theorem B15438853 : Blo 1605001 15438853 := bstep (se 4 (by rfl) ⟨1447392, by rfl⟩ : syracuseStep 15438853 = 2894785) B2894785
theorem B1807375 : Blo 1605001 1807375 := bstep (se 1 (by rfl) ⟨1355531, by rfl⟩ : syracuseStep 1807375 = 2711063) B2711063
theorem B2708599 : Blo 1605001 2708599 := bstep (se 1 (by rfl) ⟨2031449, by rfl⟩ : syracuseStep 2708599 = 4062899) B4062899
theorem B5420303 : Blo 1605001 5420303 := bstep (se 1 (by rfl) ⟨4065227, by rfl⟩ : syracuseStep 5420303 = 8130455) B8130455
theorem B2708795 : Blo 1605001 2708795 := bstep (se 1 (by rfl) ⟨2031596, by rfl⟩ : syracuseStep 2708795 = 4063193) B4063193
theorem B6510091 : Blo 1605001 6510091 := bstep (se 1 (by rfl) ⟨4882568, by rfl⟩ : syracuseStep 6510091 = 9765137) B9765137
theorem B5420573 : Blo 1605001 5420573 := bstep (se 3 (by rfl) ⟨1016357, by rfl⟩ : syracuseStep 5420573 = 2032715) B2032715
theorem B2709193 : Blo 1605001 2709193 := bstep (se 2 (by rfl) ⟨1015947, by rfl⟩ : syracuseStep 2709193 = 2031895) B2031895
theorem B5142287 : Blo 1605001 5142287 := bstep (se 1 (by rfl) ⟨3856715, by rfl⟩ : syracuseStep 5142287 = 7713431) B7713431
theorem B7329689 : Blo 1605001 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B8132561 : Blo 1605001 8132561 := bstep (se 2 (by rfl) ⟨3049710, by rfl⟩ : syracuseStep 8132561 = 6099421) B6099421
theorem B7821323 : Blo 1605001 7821323 := bstep (se 1 (by rfl) ⟨5865992, by rfl⟩ : syracuseStep 7821323 = 11731985) B11731985
theorem B52123661 : Blo 1605001 52123661 := bstep (se 3 (by rfl) ⟨9773186, by rfl⟩ : syracuseStep 52123661 = 19546373) B19546373
theorem B7526467 : Blo 1605001 7526467 := bstep (se 1 (by rfl) ⟨5644850, by rfl⟩ : syracuseStep 7526467 = 11289701) B11289701
theorem B4118663 : Blo 1605001 4118663 := bstep (se 1 (by rfl) ⟨3088997, by rfl⟩ : syracuseStep 4118663 = 6177995) B6177995
theorem B5142799 : Blo 1605001 5142799 := bstep (se 1 (by rfl) ⟨3857099, by rfl⟩ : syracuseStep 5142799 = 7714199) B7714199
theorem B2709895 : Blo 1605001 2709895 := bstep (se 1 (by rfl) ⟨2032421, by rfl⟩ : syracuseStep 2709895 = 4064843) B4064843
theorem B6863251 : Blo 1605001 6863251 := bstep (se 1 (by rfl) ⟨5147438, by rfl⟩ : syracuseStep 6863251 = 10294877) B10294877
theorem B18299357 : Blo 1605001 18299357 := bstep (se 3 (by rfl) ⟨3431129, by rfl⟩ : syracuseStep 18299357 = 6862259) B6862259
theorem B11573837 : Blo 1605001 11573837 := bstep (se 3 (by rfl) ⟨2170094, by rfl⟩ : syracuseStep 11573837 = 4340189) B4340189
theorem B2316943 : Blo 1605001 2316943 := bstep (se 1 (by rfl) ⟨1737707, by rfl⟩ : syracuseStep 2316943 = 3475415) B3475415
theorem B3611321 : Blo 1605001 3611321 := bstep (se 2 (by rfl) ⟨1354245, by rfl⟩ : syracuseStep 3611321 = 2708491) B2708491
theorem B6601607 : Blo 1605001 6601607 := bstep (se 1 (by rfl) ⟨4951205, by rfl⟩ : syracuseStep 6601607 = 9902411) B9902411
theorem B5421977 : Blo 1605001 5421977 := bstep (se 2 (by rfl) ⟨2033241, by rfl⟩ : syracuseStep 5421977 = 4066483) B4066483
theorem B3431369 : Blo 1605001 3431369 := bstep (se 2 (by rfl) ⟨1286763, by rfl⟩ : syracuseStep 3431369 = 2573527) B2573527
theorem B6691793 : Blo 1605001 6691793 := bstep (se 2 (by rfl) ⟨2509422, by rfl⟩ : syracuseStep 6691793 = 5018845) B5018845
theorem B18545669 : Blo 1605001 18545669 := bstep (se 4 (by rfl) ⟨1738656, by rfl⟩ : syracuseStep 18545669 = 3477313) B3477313
theorem B3611663 : Blo 1605001 3611663 := bstep (se 1 (by rfl) ⟨2708747, by rfl⟩ : syracuseStep 3611663 = 5417495) B5417495
theorem B2710543 : Blo 1605001 2710543 := bstep (se 1 (by rfl) ⟨2032907, by rfl⟩ : syracuseStep 2710543 = 4065815) B4065815
theorem B3611681 : Blo 1605001 3611681 := bstep (se 2 (by rfl) ⟨1354380, by rfl⟩ : syracuseStep 3611681 = 2708761) B2708761
theorem B2407559 : Blo 1605001 2407559 := bstep (se 1 (by rfl) ⟨1805669, by rfl⟩ : syracuseStep 2407559 = 3611339) B3611339
theorem B3857561 : Blo 1605001 3857561 := bstep (se 2 (by rfl) ⟨1446585, by rfl⟩ : syracuseStep 3857561 = 2893171) B2893171
theorem B2407595 : Blo 1605001 2407595 := bstep (se 1 (by rfl) ⟨1805696, by rfl⟩ : syracuseStep 2407595 = 3611393) B3611393
theorem B2407625 : Blo 1605001 2407625 := bstep (se 2 (by rfl) ⟨902859, by rfl⟩ : syracuseStep 2407625 = 1805719) B1805719
theorem B8797385 : Blo 1605001 8797385 := bstep (se 2 (by rfl) ⟨3299019, by rfl⟩ : syracuseStep 8797385 = 6598039) B6598039
theorem B13024457 : Blo 1605001 13024457 := bstep (se 2 (by rfl) ⟨4884171, by rfl⟩ : syracuseStep 13024457 = 9768343) B9768343
theorem B6094061 : Blo 1605001 6094061 := bstep (se 3 (by rfl) ⟨1142636, by rfl⟩ : syracuseStep 6094061 = 2285273) B2285273
theorem B2407739 : Blo 1605001 2407739 := bstep (se 1 (by rfl) ⟨1805804, by rfl⟩ : syracuseStep 2407739 = 3611609) B3611609
theorem B2407799 : Blo 1605001 2407799 := bstep (se 1 (by rfl) ⟨1805849, by rfl⟩ : syracuseStep 2407799 = 3611699) B3611699
theorem B3612023 : Blo 1605001 3612023 := bstep (se 1 (by rfl) ⟨2709017, by rfl⟩ : syracuseStep 3612023 = 5418035) B5418035
theorem B15433091 : Blo 1605001 15433091 := bstep (se 1 (by rfl) ⟨11574818, by rfl⟩ : syracuseStep 15433091 = 23149637) B23149637
theorem B1605007 : Blo 1605001 1605007 := bstep (se 1 (by rfl) ⟨1203755, by rfl⟩ : syracuseStep 1605007 = 2407511) B2407511
theorem B2407823 : Blo 1605001 2407823 := bstep (se 1 (by rfl) ⟨1805867, by rfl⟩ : syracuseStep 2407823 = 3611735) B3611735
theorem B9772433 : Blo 1605001 9772433 := bstep (se 2 (by rfl) ⟨3664662, by rfl⟩ : syracuseStep 9772433 = 7329325) B7329325
theorem B2407865 : Blo 1605001 2407865 := bstep (se 2 (by rfl) ⟨902949, by rfl⟩ : syracuseStep 2407865 = 1805899) B1805899
theorem B1605051 : Blo 1605001 1605051 := bstep (se 1 (by rfl) ⟨1203788, by rfl⟩ : syracuseStep 1605051 = 2407577) B2407577
theorem B1605127 : Blo 1605001 1605127 := bstep (se 1 (by rfl) ⟨1203845, by rfl⟩ : syracuseStep 1605127 = 2407691) B2407691
theorem B2407943 : Blo 1605001 2407943 := bstep (se 1 (by rfl) ⟨1805957, by rfl⟩ : syracuseStep 2407943 = 3611915) B3611915
theorem B1605135 : Blo 1605001 1605135 := bstep (se 1 (by rfl) ⟨1203851, by rfl⟩ : syracuseStep 1605135 = 2407703) B2407703
theorem B1785359 : Blo 1605001 1785359 := bstep (se 1 (by rfl) ⟨1339019, by rfl⟩ : syracuseStep 1785359 = 2678039) B2678039
theorem B6094379 : Blo 1605001 6094379 := bstep (se 1 (by rfl) ⟨4570784, by rfl⟩ : syracuseStep 6094379 = 9141569) B9141569
theorem B7421483 : Blo 1605001 7421483 := bstep (se 1 (by rfl) ⟨5566112, by rfl⟩ : syracuseStep 7421483 = 11132225) B11132225
theorem B2407979 : Blo 1605001 2407979 := bstep (se 1 (by rfl) ⟨1805984, by rfl⟩ : syracuseStep 2407979 = 3611969) B3611969
theorem B3612203 : Blo 1605001 3612203 := bstep (se 1 (by rfl) ⟨2709152, by rfl⟩ : syracuseStep 3612203 = 5418305) B5418305
theorem B2711083 : Blo 1605001 2711083 := bstep (se 1 (by rfl) ⟨2033312, by rfl⟩ : syracuseStep 2711083 = 4066625) B4066625
theorem B1605179 : Blo 1605001 1605179 := bstep (se 1 (by rfl) ⟨1203884, by rfl⟩ : syracuseStep 1605179 = 2407769) B2407769
theorem B9141821 : Blo 1605001 9141821 := bstep (se 3 (by rfl) ⟨1714091, by rfl⟩ : syracuseStep 9141821 = 3428183) B3428183
theorem B2408009 : Blo 1605001 2408009 := bstep (se 2 (by rfl) ⟨903003, by rfl⟩ : syracuseStep 2408009 = 1806007) B1806007
theorem B5422679 : Blo 1605001 5422679 := bstep (se 1 (by rfl) ⟨4067009, by rfl⟩ : syracuseStep 5422679 = 8134019) B8134019
theorem B4570739 : Blo 1605001 4570739 := bstep (se 1 (by rfl) ⟨3428054, by rfl⟩ : syracuseStep 4570739 = 6856109) B6856109
theorem B1605255 : Blo 1605001 1605255 := bstep (se 1 (by rfl) ⟨1203941, by rfl⟩ : syracuseStep 1605255 = 2407883) B2407883
theorem B1605263 : Blo 1605001 1605263 := bstep (se 1 (by rfl) ⟨1203947, by rfl⟩ : syracuseStep 1605263 = 2407895) B2407895
theorem B4341401 : Blo 1605001 4341401 := bstep (se 2 (by rfl) ⟨1628025, by rfl⟩ : syracuseStep 4341401 = 3256051) B3256051
theorem B15441587 : Blo 1605001 15441587 := bstep (se 1 (by rfl) ⟨11581190, by rfl⟩ : syracuseStep 15441587 = 23162381) B23162381
theorem B2711225 : Blo 1605001 2711225 := bstep (se 2 (by rfl) ⟨1016709, by rfl⟩ : syracuseStep 2711225 = 2033419) B2033419
theorem B1605307 : Blo 1605001 1605307 := bstep (se 1 (by rfl) ⟨1203980, by rfl⟩ : syracuseStep 1605307 = 2407961) B2407961
theorem B2408123 : Blo 1605001 2408123 := bstep (se 1 (by rfl) ⟨1806092, by rfl⟩ : syracuseStep 2408123 = 3612185) B3612185
theorem B2408183 : Blo 1605001 2408183 := bstep (se 1 (by rfl) ⟨1806137, by rfl⟩ : syracuseStep 2408183 = 3612275) B3612275
theorem B1605383 : Blo 1605001 1605383 := bstep (se 1 (by rfl) ⟨1204037, by rfl⟩ : syracuseStep 1605383 = 2408075) B2408075
theorem B1605391 : Blo 1605001 1605391 := bstep (se 1 (by rfl) ⟨1204043, by rfl⟩ : syracuseStep 1605391 = 2408087) B2408087
theorem B2408207 : Blo 1605001 2408207 := bstep (se 1 (by rfl) ⟨1806155, by rfl⟩ : syracuseStep 2408207 = 3612311) B3612311
theorem B100228913 : Blo 1605001 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B2408249 : Blo 1605001 2408249 := bstep (se 2 (by rfl) ⟨903093, by rfl⟩ : syracuseStep 2408249 = 1806187) B1806187
theorem B2031419 : Blo 1605001 2031419 := bstep (se 1 (by rfl) ⟨1523564, by rfl⟩ : syracuseStep 2031419 = 3047129) B3047129
theorem B1605435 : Blo 1605001 1605435 := bstep (se 1 (by rfl) ⟨1204076, by rfl⟩ : syracuseStep 1605435 = 2408153) B2408153
theorem B4570967 : Blo 1605001 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B1605511 : Blo 1605001 1605511 := bstep (se 1 (by rfl) ⟨1204133, by rfl⟩ : syracuseStep 1605511 = 2408267) B2408267
theorem B2408327 : Blo 1605001 2408327 := bstep (se 1 (by rfl) ⟨1806245, by rfl⟩ : syracuseStep 2408327 = 3612491) B3612491
theorem B1605519 : Blo 1605001 1605519 := bstep (se 1 (by rfl) ⟨1204139, by rfl⟩ : syracuseStep 1605519 = 2408279) B2408279
theorem B3612563 : Blo 1605001 3612563 := bstep (se 1 (by rfl) ⟨2709422, by rfl⟩ : syracuseStep 3612563 = 5418845) B5418845
theorem B20848535 : Blo 1605001 20848535 := bstep (se 1 (by rfl) ⟨15636401, by rfl⟩ : syracuseStep 20848535 = 31272803) B31272803
theorem B2408363 : Blo 1605001 2408363 := bstep (se 1 (by rfl) ⟨1806272, by rfl⟩ : syracuseStep 2408363 = 3612545) B3612545
theorem B1605563 : Blo 1605001 1605563 := bstep (se 1 (by rfl) ⟨1204172, by rfl⟩ : syracuseStep 1605563 = 2408345) B2408345
theorem B2408393 : Blo 1605001 2408393 := bstep (se 2 (by rfl) ⟨903147, by rfl⟩ : syracuseStep 2408393 = 1806295) B1806295
theorem B3612617 : Blo 1605001 3612617 := bstep (se 2 (by rfl) ⟨1354731, by rfl⟩ : syracuseStep 3612617 = 2709463) B2709463
theorem B5423111 : Blo 1605001 5423111 := bstep (se 1 (by rfl) ⟨4067333, by rfl⟩ : syracuseStep 5423111 = 8134667) B8134667
theorem B1605671 : Blo 1605001 1605671 := bstep (se 1 (by rfl) ⟨1204253, by rfl⟩ : syracuseStep 1605671 = 2408507) B2408507
theorem B1605711 : Blo 1605001 1605711 := bstep (se 1 (by rfl) ⟨1204283, by rfl⟩ : syracuseStep 1605711 = 2408567) B2408567
theorem B10035289 : Blo 1605001 10035289 := bstep (se 2 (by rfl) ⟨3763233, by rfl⟩ : syracuseStep 10035289 = 7526467) B7526467
theorem B1605727 : Blo 1605001 1605727 := bstep (se 1 (by rfl) ⟨1204295, by rfl⟩ : syracuseStep 1605727 = 2408591) B2408591
theorem B10289267 : Blo 1605001 10289267 := bstep (se 1 (by rfl) ⟨7716950, by rfl⟩ : syracuseStep 10289267 = 15433901) B15433901
theorem B5423219 : Blo 1605001 5423219 := bstep (se 1 (by rfl) ⟨4067414, by rfl⟩ : syracuseStep 5423219 = 8134829) B8134829
theorem B1605755 : Blo 1605001 1605755 := bstep (se 1 (by rfl) ⟨1204316, by rfl⟩ : syracuseStep 1605755 = 2408633) B2408633
theorem B1605807 : Blo 1605001 1605807 := bstep (se 1 (by rfl) ⟨1204355, by rfl⟩ : syracuseStep 1605807 = 2408711) B2408711
theorem B1605831 : Blo 1605001 1605831 := bstep (se 1 (by rfl) ⟨1204373, by rfl⟩ : syracuseStep 1605831 = 2408747) B2408747
theorem B1605851 : Blo 1605001 1605851 := bstep (se 1 (by rfl) ⟨1204388, by rfl⟩ : syracuseStep 1605851 = 2408777) B2408777
theorem B1605927 : Blo 1605001 1605927 := bstep (se 1 (by rfl) ⟨1204445, by rfl⟩ : syracuseStep 1605927 = 2408891) B2408891
theorem B1605967 : Blo 1605001 1605967 := bstep (se 1 (by rfl) ⟨1204475, by rfl⟩ : syracuseStep 1605967 = 2408951) B2408951
theorem B1605983 : Blo 1605001 1605983 := bstep (se 1 (by rfl) ⟨1204487, by rfl⟩ : syracuseStep 1605983 = 2408975) B2408975
theorem B6857065 : Blo 1605001 6857065 := bstep (se 2 (by rfl) ⟨2571399, by rfl⟩ : syracuseStep 6857065 = 5142799) B5142799
theorem B1606011 : Blo 1605001 1606011 := bstep (se 1 (by rfl) ⟨1204508, by rfl⟩ : syracuseStep 1606011 = 2409017) B2409017
theorem B5423489 : Blo 1605001 5423489 := bstep (se 2 (by rfl) ⟨2033808, by rfl⟩ : syracuseStep 5423489 = 4067617) B4067617
theorem B2408879 : Blo 1605001 2408879 := bstep (se 1 (by rfl) ⟨1806659, by rfl⟩ : syracuseStep 2408879 = 3613319) B3613319
theorem B1606063 : Blo 1605001 1606063 := bstep (se 1 (by rfl) ⟨1204547, by rfl⟩ : syracuseStep 1606063 = 2409095) B2409095
theorem B1606087 : Blo 1605001 1606087 := bstep (se 1 (by rfl) ⟨1204565, by rfl⟩ : syracuseStep 1606087 = 2409131) B2409131
theorem B1606107 : Blo 1605001 1606107 := bstep (se 1 (by rfl) ⟨1204580, by rfl⟩ : syracuseStep 1606107 = 2409161) B2409161
theorem B3613193 : Blo 1605001 3613193 := bstep (se 2 (by rfl) ⟨1354947, by rfl⟩ : syracuseStep 3613193 = 2709895) B2709895
theorem B2408969 : Blo 1605001 2408969 := bstep (se 2 (by rfl) ⟨903363, by rfl⟩ : syracuseStep 2408969 = 1806727) B1806727
theorem B83460631 : Blo 1605001 83460631 := bstep (se 1 (by rfl) ⟨62595473, by rfl⟩ : syracuseStep 83460631 = 125190947) B125190947
theorem B9151001 : Blo 1605001 9151001 := bstep (se 2 (by rfl) ⟨3431625, by rfl⟩ : syracuseStep 9151001 = 6863251) B6863251
theorem B2408999 : Blo 1605001 2408999 := bstep (se 1 (by rfl) ⟨1806749, by rfl⟩ : syracuseStep 2408999 = 3613499) B3613499
theorem B1606183 : Blo 1605001 1606183 := bstep (se 1 (by rfl) ⟨1204637, by rfl⟩ : syracuseStep 1606183 = 2409275) B2409275
theorem B1606223 : Blo 1605001 1606223 := bstep (se 1 (by rfl) ⟨1204667, by rfl⟩ : syracuseStep 1606223 = 2409335) B2409335
theorem B1606239 : Blo 1605001 1606239 := bstep (se 1 (by rfl) ⟨1204679, by rfl⟩ : syracuseStep 1606239 = 2409359) B2409359
theorem B4063841 : Blo 1605001 4063841 := bstep (se 2 (by rfl) ⟨1523940, by rfl⟩ : syracuseStep 4063841 = 3047881) B3047881
theorem B2409083 : Blo 1605001 2409083 := bstep (se 1 (by rfl) ⟨1806812, by rfl⟩ : syracuseStep 2409083 = 3613625) B3613625
theorem B1606267 : Blo 1605001 1606267 := bstep (se 1 (by rfl) ⟨1204700, by rfl⟩ : syracuseStep 1606267 = 2409401) B2409401
theorem B1606319 : Blo 1605001 1606319 := bstep (se 1 (by rfl) ⟨1204739, by rfl⟩ : syracuseStep 1606319 = 2409479) B2409479
theorem B1606343 : Blo 1605001 1606343 := bstep (se 1 (by rfl) ⟨1204757, by rfl⟩ : syracuseStep 1606343 = 2409515) B2409515
theorem B1606363 : Blo 1605001 1606363 := bstep (se 1 (by rfl) ⟨1204772, by rfl⟩ : syracuseStep 1606363 = 2409545) B2409545
theorem B3048185 : Blo 1605001 3048185 := bstep (se 2 (by rfl) ⟨1143069, by rfl⟩ : syracuseStep 3048185 = 2286139) B2286139
theorem B2409209 : Blo 1605001 2409209 := bstep (se 2 (by rfl) ⟨903453, by rfl⟩ : syracuseStep 2409209 = 1806907) B1806907
theorem B1606439 : Blo 1605001 1606439 := bstep (se 1 (by rfl) ⟨1204829, by rfl⟩ : syracuseStep 1606439 = 2409659) B2409659
theorem B1606479 : Blo 1605001 1606479 := bstep (se 1 (by rfl) ⟨1204859, by rfl⟩ : syracuseStep 1606479 = 2409719) B2409719
theorem B3613535 : Blo 1605001 3613535 := bstep (se 1 (by rfl) ⟨2710151, by rfl⟩ : syracuseStep 3613535 = 5420303) B5420303
theorem B2409311 : Blo 1605001 2409311 := bstep (se 1 (by rfl) ⟨1806983, by rfl⟩ : syracuseStep 2409311 = 3613967) B3613967
theorem B1606495 : Blo 1605001 1606495 := bstep (se 1 (by rfl) ⟨1204871, by rfl⟩ : syracuseStep 1606495 = 2409743) B2409743
theorem B2409323 : Blo 1605001 2409323 := bstep (se 1 (by rfl) ⟨1806992, by rfl⟩ : syracuseStep 2409323 = 3613985) B3613985
theorem B1606523 : Blo 1605001 1606523 := bstep (se 1 (by rfl) ⟨1204892, by rfl⟩ : syracuseStep 1606523 = 2409785) B2409785
theorem B3048367 : Blo 1605001 3048367 := bstep (se 1 (by rfl) ⟨2286275, by rfl⟩ : syracuseStep 3048367 = 4572551) B4572551
theorem B1606575 : Blo 1605001 1606575 := bstep (se 1 (by rfl) ⟨1204931, by rfl⟩ : syracuseStep 1606575 = 2409863) B2409863
theorem B4637627 : Blo 1605001 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B1606599 : Blo 1605001 1606599 := bstep (se 1 (by rfl) ⟨1204949, by rfl⟩ : syracuseStep 1606599 = 2409899) B2409899
theorem B1606619 : Blo 1605001 1606619 := bstep (se 1 (by rfl) ⟨1204964, by rfl⟩ : syracuseStep 1606619 = 2409929) B2409929
theorem B7717889 : Blo 1605001 7717889 := bstep (se 2 (by rfl) ⟨2894208, by rfl⟩ : syracuseStep 7717889 = 5788417) B5788417
theorem B3613715 : Blo 1605001 3613715 := bstep (se 1 (by rfl) ⟨2710286, by rfl⟩ : syracuseStep 3613715 = 5420573) B5420573
theorem B5145619 : Blo 1605001 5145619 := bstep (se 1 (by rfl) ⟨3859214, by rfl⟩ : syracuseStep 5145619 = 7718429) B7718429
theorem B1606695 : Blo 1605001 1606695 := bstep (se 1 (by rfl) ⟨1205021, by rfl⟩ : syracuseStep 1606695 = 2410043) B2410043
theorem B8127539 : Blo 1605001 8127539 := bstep (se 1 (by rfl) ⟨6095654, by rfl⟩ : syracuseStep 8127539 = 12191309) B12191309
theorem B2409551 : Blo 1605001 2409551 := bstep (se 1 (by rfl) ⟨1807163, by rfl⟩ : syracuseStep 2409551 = 3614327) B3614327
theorem B1606735 : Blo 1605001 1606735 := bstep (se 1 (by rfl) ⟨1205051, by rfl⟩ : syracuseStep 1606735 = 2410103) B2410103
theorem B5866577 : Blo 1605001 5866577 := bstep (se 2 (by rfl) ⟨2199966, by rfl⟩ : syracuseStep 5866577 = 4399933) B4399933
theorem B1606751 : Blo 1605001 1606751 := bstep (se 1 (by rfl) ⟨1205063, by rfl⟩ : syracuseStep 1606751 = 2410127) B2410127
theorem B1606779 : Blo 1605001 1606779 := bstep (se 1 (by rfl) ⟨1205084, by rfl⟩ : syracuseStep 1606779 = 2410169) B2410169
theorem B1606831 : Blo 1605001 1606831 := bstep (se 1 (by rfl) ⟨1205123, by rfl⟩ : syracuseStep 1606831 = 2410247) B2410247
theorem B2409671 : Blo 1605001 2409671 := bstep (se 1 (by rfl) ⟨1807253, by rfl⟩ : syracuseStep 2409671 = 3614507) B3614507
theorem B1606855 : Blo 1605001 1606855 := bstep (se 1 (by rfl) ⟨1205141, by rfl⟩ : syracuseStep 1606855 = 2410283) B2410283
theorem B1606875 : Blo 1605001 1606875 := bstep (se 1 (by rfl) ⟨1205156, by rfl⟩ : syracuseStep 1606875 = 2410313) B2410313
theorem B1606951 : Blo 1605001 1606951 := bstep (se 1 (by rfl) ⟨1205213, by rfl⟩ : syracuseStep 1606951 = 2410427) B2410427
theorem B1606991 : Blo 1605001 1606991 := bstep (se 1 (by rfl) ⟨1205243, by rfl⟩ : syracuseStep 1606991 = 2410487) B2410487
theorem B3614057 : Blo 1605001 3614057 := bstep (se 2 (by rfl) ⟨1355271, by rfl⟩ : syracuseStep 3614057 = 2710543) B2710543
theorem B2409833 : Blo 1605001 2409833 := bstep (se 2 (by rfl) ⟨903687, by rfl⟩ : syracuseStep 2409833 = 1807375) B1807375
theorem B4760957 : Blo 1605001 4760957 := bstep (se 3 (by rfl) ⟨892679, by rfl⟩ : syracuseStep 4760957 = 1785359) B1785359
theorem B5571983 : Blo 1605001 5571983 := bstep (se 1 (by rfl) ⟨4178987, by rfl⟩ : syracuseStep 5571983 = 8357975) B8357975
theorem B2745775 : Blo 1605001 2745775 := bstep (se 1 (by rfl) ⟨2059331, by rfl⟩ : syracuseStep 2745775 = 4118663) B4118663
theorem B2409911 : Blo 1605001 2409911 := bstep (se 1 (by rfl) ⟨1807433, by rfl⟩ : syracuseStep 2409911 = 3614867) B3614867
theorem B2409947 : Blo 1605001 2409947 := bstep (se 1 (by rfl) ⟨1807460, by rfl⟩ : syracuseStep 2409947 = 3614921) B3614921
theorem B2033191 : Blo 1605001 2033191 := bstep (se 1 (by rfl) ⟨1524893, by rfl⟩ : syracuseStep 2033191 = 3049787) B3049787
theorem B10290827 : Blo 1605001 10290827 := bstep (se 1 (by rfl) ⟨7718120, by rfl⟩ : syracuseStep 10290827 = 15436241) B15436241
theorem B12199571 : Blo 1605001 12199571 := bstep (se 1 (by rfl) ⟨9149678, by rfl⟩ : syracuseStep 12199571 = 18299357) B18299357
theorem B9144029 : Blo 1605001 9144029 := bstep (se 3 (by rfl) ⟨1714505, by rfl⟩ : syracuseStep 9144029 = 3429011) B3429011
theorem B2033515 : Blo 1605001 2033515 := bstep (se 1 (by rfl) ⟨1525136, by rfl⟩ : syracuseStep 2033515 = 3050273) B3050273
theorem B4401071 : Blo 1605001 4401071 := bstep (se 1 (by rfl) ⟨3300803, by rfl⟩ : syracuseStep 4401071 = 6601607) B6601607
theorem B2410415 : Blo 1605001 2410415 := bstep (se 1 (by rfl) ⟨1807811, by rfl⟩ : syracuseStep 2410415 = 3615623) B3615623
theorem B3614651 : Blo 1605001 3614651 := bstep (se 1 (by rfl) ⟨2710988, by rfl⟩ : syracuseStep 3614651 = 5421977) B5421977
theorem B12363779 : Blo 1605001 12363779 := bstep (se 1 (by rfl) ⟨9272834, by rfl⟩ : syracuseStep 12363779 = 18545669) B18545669
theorem B4065299 : Blo 1605001 4065299 := bstep (se 1 (by rfl) ⟨3048974, by rfl⟩ : syracuseStep 4065299 = 6097949) B6097949
theorem B3614777 : Blo 1605001 3614777 := bstep (se 2 (by rfl) ⟨1355541, by rfl⟩ : syracuseStep 3614777 = 2711083) B2711083
theorem B2033743 : Blo 1605001 2033743 := bstep (se 1 (by rfl) ⟨1525307, by rfl⟩ : syracuseStep 2033743 = 3050615) B3050615
theorem B6096977 : Blo 1605001 6096977 := bstep (se 2 (by rfl) ⟨2286366, by rfl⟩ : syracuseStep 6096977 = 4572733) B4572733
theorem B62580869 : Blo 1605001 62580869 := bstep (se 4 (by rfl) ⟨5866956, by rfl⟩ : syracuseStep 62580869 = 11733913) B11733913
theorem B5417117 : Blo 1605001 5417117 := bstep (se 3 (by rfl) ⟨1015709, by rfl⟩ : syracuseStep 5417117 = 2031419) B2031419
theorem B3049643 : Blo 1605001 3049643 := bstep (se 1 (by rfl) ⟨2287232, by rfl⟩ : syracuseStep 3049643 = 4574465) B4574465
theorem B6514955 : Blo 1605001 6514955 := bstep (se 1 (by rfl) ⟨4886216, by rfl⟩ : syracuseStep 6514955 = 9772433) B9772433
theorem B6097295 : Blo 1605001 6097295 := bstep (se 1 (by rfl) ⟨4572971, by rfl⟩ : syracuseStep 6097295 = 9145943) B9145943
theorem B3615119 : Blo 1605001 3615119 := bstep (se 1 (by rfl) ⟨2711339, by rfl⟩ : syracuseStep 3615119 = 5422679) B5422679
theorem B2894267 : Blo 1605001 2894267 := bstep (se 1 (by rfl) ⟨2170700, by rfl⟩ : syracuseStep 2894267 = 4341401) B4341401
theorem B12192281 : Blo 1605001 12192281 := bstep (se 2 (by rfl) ⟨4572105, by rfl⟩ : syracuseStep 12192281 = 9144211) B9144211
theorem B17844781 : Blo 1605001 17844781 := bstep (se 3 (by rfl) ⟨3345896, by rfl⟩ : syracuseStep 17844781 = 6691793) B6691793
theorem B2711515 : Blo 1605001 2711515 := bstep (se 1 (by rfl) ⟨2033636, by rfl⟩ : syracuseStep 2711515 = 4067273) B4067273
theorem B1739387 : Blo 1605001 1739387 := bstep (se 1 (by rfl) ⟨1304540, by rfl⟩ : syracuseStep 1739387 = 2609081) B2609081
theorem B8129159 : Blo 1605001 8129159 := bstep (se 1 (by rfl) ⟨6096869, by rfl⟩ : syracuseStep 8129159 = 12193739) B12193739
theorem B5417657 : Blo 1605001 5417657 := bstep (se 2 (by rfl) ⟨2031621, by rfl⟩ : syracuseStep 5417657 = 4063243) B4063243
theorem B3615443 : Blo 1605001 3615443 := bstep (se 1 (by rfl) ⟨2711582, by rfl⟩ : syracuseStep 3615443 = 5423165) B5423165
theorem B46918547 : Blo 1605001 46918547 := bstep (se 1 (by rfl) ⟨35188910, by rfl⟩ : syracuseStep 46918547 = 70377821) B70377821
theorem B6515639 : Blo 1605001 6515639 := bstep (se 1 (by rfl) ⟨4886729, by rfl⟩ : syracuseStep 6515639 = 9773459) B9773459
theorem B10292417 : Blo 1605001 10292417 := bstep (se 2 (by rfl) ⟨3859656, by rfl⟩ : syracuseStep 10292417 = 7719313) B7719313
theorem B5418251 : Blo 1605001 5418251 := bstep (se 1 (by rfl) ⟨4063688, by rfl⟩ : syracuseStep 5418251 = 8127377) B8127377
theorem B6098237 : Blo 1605001 6098237 := bstep (se 3 (by rfl) ⟨1143419, by rfl⟩ : syracuseStep 6098237 = 2286839) B2286839
theorem B12357029 : Blo 1605001 12357029 := bstep (se 4 (by rfl) ⟨1158471, by rfl⟩ : syracuseStep 12357029 = 2316943) B2316943
theorem B1928623 : Blo 1605001 1928623 := bstep (se 1 (by rfl) ⟨1446467, by rfl⟩ : syracuseStep 1928623 = 2892935) B2892935
theorem B5418521 : Blo 1605001 5418521 := bstep (se 2 (by rfl) ⟨2031945, by rfl⟩ : syracuseStep 5418521 = 4063891) B4063891
theorem B1805863 : Blo 1605001 1805863 := bstep (se 1 (by rfl) ⟨1354397, by rfl⟩ : syracuseStep 1805863 = 2708795) B2708795
theorem B23162435 : Blo 1605001 23162435 := bstep (se 1 (by rfl) ⟨17371826, by rfl⟩ : syracuseStep 23162435 = 34743653) B34743653
theorem B5869385 : Blo 1605001 5869385 := bstep (se 2 (by rfl) ⟨2201019, by rfl⟩ : syracuseStep 5869385 = 4402039) B4402039
theorem B3428191 : Blo 1605001 3428191 := bstep (se 1 (by rfl) ⟨2571143, by rfl⟩ : syracuseStep 3428191 = 5142287) B5142287
theorem B4886459 : Blo 1605001 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B11579345 : Blo 1605001 11579345 := bstep (se 2 (by rfl) ⟨4342254, by rfl⟩ : syracuseStep 11579345 = 8684509) B8684509
theorem B5214215 : Blo 1605001 5214215 := bstep (se 1 (by rfl) ⟨3910661, by rfl⟩ : syracuseStep 5214215 = 7821323) B7821323
theorem B8130617 : Blo 1605001 8130617 := bstep (se 2 (by rfl) ⟨3048981, by rfl⟩ : syracuseStep 8130617 = 6097963) B6097963
theorem B10285703 : Blo 1605001 10285703 := bstep (se 1 (by rfl) ⟨7714277, by rfl⟩ : syracuseStep 10285703 = 15428555) B15428555
theorem B5419655 : Blo 1605001 5419655 := bstep (se 1 (by rfl) ⟨4064741, by rfl⟩ : syracuseStep 5419655 = 8129483) B8129483
theorem B8680121 : Blo 1605001 8680121 := bstep (se 2 (by rfl) ⟨3255045, by rfl⟩ : syracuseStep 8680121 = 6510091) B6510091
theorem B5419709 : Blo 1605001 5419709 := bstep (se 3 (by rfl) ⟨1016195, by rfl⟩ : syracuseStep 5419709 = 2032391) B2032391
theorem B5419871 : Blo 1605001 5419871 := bstep (se 1 (by rfl) ⟨4064903, by rfl⟩ : syracuseStep 5419871 = 8129807) B8129807
theorem B12202973 : Blo 1605001 12202973 := bstep (se 3 (by rfl) ⟨2288057, by rfl⟩ : syracuseStep 12202973 = 4576115) B4576115
theorem B5420033 : Blo 1605001 5420033 := bstep (se 2 (by rfl) ⟨2032512, by rfl⟩ : syracuseStep 5420033 = 4065025) B4065025
theorem B10294391 : Blo 1605001 10294391 := bstep (se 1 (by rfl) ⟨7720793, by rfl⟩ : syracuseStep 10294391 = 15441587) B15441587
theorem B1807483 : Blo 1605001 1807483 := bstep (se 1 (by rfl) ⟨1355612, by rfl⟩ : syracuseStep 1807483 = 2711225) B2711225
theorem B66819275 : Blo 1605001 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B13899023 : Blo 1605001 13899023 := bstep (se 1 (by rfl) ⟨10424267, by rfl⟩ : syracuseStep 13899023 = 20848535) B20848535
theorem B12195197 : Blo 1605001 12195197 := bstep (se 3 (by rfl) ⟨2286599, by rfl⟩ : syracuseStep 12195197 = 4573199) B4573199
theorem B2381239 : Blo 1605001 2381239 := bstep (se 1 (by rfl) ⟨1785929, by rfl⟩ : syracuseStep 2381239 = 3571859) B3571859
theorem B2708923 : Blo 1605001 2708923 := bstep (se 1 (by rfl) ⟨2031692, by rfl⟩ : syracuseStep 2708923 = 4063385) B4063385
theorem B18789833 : Blo 1605001 18789833 := bstep (se 2 (by rfl) ⟨7046187, by rfl⟩ : syracuseStep 18789833 = 14092375) B14092375
theorem B34739675 : Blo 1605001 34739675 := bstep (se 1 (by rfl) ⟨26054756, by rfl⟩ : syracuseStep 34739675 = 52109513) B52109513
theorem B26056181 : Blo 1605001 26056181 := bstep (se 5 (by rfl) ⟨1221383, by rfl⟩ : syracuseStep 26056181 = 2442767) B2442767
theorem B13194791 : Blo 1605001 13194791 := bstep (se 1 (by rfl) ⟨9896093, by rfl⟩ : syracuseStep 13194791 = 19792187) B19792187
theorem B2709031 : Blo 1605001 2709031 := bstep (se 1 (by rfl) ⟨2031773, by rfl⟩ : syracuseStep 2709031 = 4063547) B4063547
theorem B22271531 : Blo 1605001 22271531 := bstep (se 1 (by rfl) ⟨16703648, by rfl⟩ : syracuseStep 22271531 = 33407297) B33407297
theorem B6510269 : Blo 1605001 6510269 := bstep (se 3 (by rfl) ⟨1220675, by rfl⟩ : syracuseStep 6510269 = 2441351) B2441351
theorem B5420843 : Blo 1605001 5420843 := bstep (se 1 (by rfl) ⟨4065632, by rfl⟩ : syracuseStep 5420843 = 8131265) B8131265
theorem B5789513 : Blo 1605001 5789513 := bstep (se 2 (by rfl) ⟨2171067, by rfl⟩ : syracuseStep 5789513 = 4342135) B4342135
theorem B2709355 : Blo 1605001 2709355 := bstep (se 1 (by rfl) ⟨2032016, by rfl⟩ : syracuseStep 2709355 = 4064033) B4064033
theorem B15849425 : Blo 1605001 15849425 := bstep (se 2 (by rfl) ⟨5943534, by rfl⟩ : syracuseStep 15849425 = 11887069) B11887069
theorem B5421113 : Blo 1605001 5421113 := bstep (se 2 (by rfl) ⟨2032917, by rfl⟩ : syracuseStep 5421113 = 4065835) B4065835
theorem B8132723 : Blo 1605001 8132723 := bstep (se 1 (by rfl) ⟨6099542, by rfl⟩ : syracuseStep 8132723 = 12199085) B12199085
theorem B5142685 : Blo 1605001 5142685 := bstep (se 3 (by rfl) ⟨964253, by rfl⟩ : syracuseStep 5142685 = 1928507) B1928507
theorem B5421437 : Blo 1605001 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B13719941 : Blo 1605001 13719941 := bstep (se 4 (by rfl) ⟨1286244, by rfl⟩ : syracuseStep 13719941 = 2572489) B2572489
theorem B4340233 : Blo 1605001 4340233 := bstep (se 2 (by rfl) ⟨1627587, by rfl⟩ : syracuseStep 4340233 = 3255175) B3255175
theorem B5421707 : Blo 1605001 5421707 := bstep (se 1 (by rfl) ⟨4066280, by rfl⟩ : syracuseStep 5421707 = 8132561) B8132561
theorem B20585137 : Blo 1605001 20585137 := bstep (se 2 (by rfl) ⟨7719426, by rfl⟩ : syracuseStep 20585137 = 15438853) B15438853
theorem B34749107 : Blo 1605001 34749107 := bstep (se 1 (by rfl) ⟨26061830, by rfl⟩ : syracuseStep 34749107 = 52123661) B52123661
theorem B11737811 : Blo 1605001 11737811 := bstep (se 1 (by rfl) ⟨8803358, by rfl⟩ : syracuseStep 11737811 = 17606717) B17606717
theorem B8134343 : Blo 1605001 8134343 := bstep (se 1 (by rfl) ⟨6100757, by rfl⟩ : syracuseStep 8134343 = 12201515) B12201515
theorem B3611465 : Blo 1605001 3611465 := bstep (se 2 (by rfl) ⟨1354299, by rfl⟩ : syracuseStep 3611465 = 2708599) B2708599
theorem B2710415 : Blo 1605001 2710415 := bstep (se 1 (by rfl) ⟨2032811, by rfl⟩ : syracuseStep 2710415 = 4065623) B4065623
theorem B83458997 : Blo 1605001 83458997 := bstep (se 5 (by rfl) ⟨3912140, by rfl⟩ : syracuseStep 83458997 = 7824281) B7824281
theorem B7715891 : Blo 1605001 7715891 := bstep (se 1 (by rfl) ⟨5786918, by rfl⟩ : syracuseStep 7715891 = 11573837) B11573837
theorem B2407547 : Blo 1605001 2407547 := bstep (se 1 (by rfl) ⟨1805660, by rfl⟩ : syracuseStep 2407547 = 3611321) B3611321
theorem B2710651 : Blo 1605001 2710651 := bstep (se 1 (by rfl) ⟨2032988, by rfl⟩ : syracuseStep 2710651 = 4065977) B4065977
theorem B2407673 : Blo 1605001 2407673 := bstep (se 2 (by rfl) ⟨902877, by rfl⟩ : syracuseStep 2407673 = 1805755) B1805755
theorem B2407775 : Blo 1605001 2407775 := bstep (se 1 (by rfl) ⟨1805831, by rfl⟩ : syracuseStep 2407775 = 3611663) B3611663
theorem B2407787 : Blo 1605001 2407787 := bstep (se 1 (by rfl) ⟨1805840, by rfl⟩ : syracuseStep 2407787 = 3611681) B3611681
theorem B9149861 : Blo 1605001 9149861 := bstep (se 4 (by rfl) ⟨857799, by rfl⟩ : syracuseStep 9149861 = 1715599) B1715599
theorem B1605039 : Blo 1605001 1605039 := bstep (se 1 (by rfl) ⟨1203779, by rfl⟩ : syracuseStep 1605039 = 2407559) B2407559
theorem B2571707 : Blo 1605001 2571707 := bstep (se 1 (by rfl) ⟨1928780, by rfl⟩ : syracuseStep 2571707 = 3857561) B3857561
theorem B1605063 : Blo 1605001 1605063 := bstep (se 1 (by rfl) ⟨1203797, by rfl⟩ : syracuseStep 1605063 = 2407595) B2407595
theorem B1605083 : Blo 1605001 1605083 := bstep (se 1 (by rfl) ⟨1203812, by rfl⟩ : syracuseStep 1605083 = 2407625) B2407625
theorem B5864923 : Blo 1605001 5864923 := bstep (se 1 (by rfl) ⟨4398692, by rfl⟩ : syracuseStep 5864923 = 8797385) B8797385
theorem B8682971 : Blo 1605001 8682971 := bstep (se 1 (by rfl) ⟨6512228, by rfl⟩ : syracuseStep 8682971 = 13024457) B13024457
theorem B3431899 : Blo 1605001 3431899 := bstep (se 1 (by rfl) ⟨2573924, by rfl⟩ : syracuseStep 3431899 = 5147849) B5147849
theorem B4062707 : Blo 1605001 4062707 := bstep (se 1 (by rfl) ⟨3047030, by rfl⟩ : syracuseStep 4062707 = 6094061) B6094061
theorem B5422625 : Blo 1605001 5422625 := bstep (se 2 (by rfl) ⟨2033484, by rfl⟩ : syracuseStep 5422625 = 4066969) B4066969
theorem B1605159 : Blo 1605001 1605159 := bstep (se 1 (by rfl) ⟨1203869, by rfl⟩ : syracuseStep 1605159 = 2407739) B2407739
theorem B1605199 : Blo 1605001 1605199 := bstep (se 1 (by rfl) ⟨1203899, by rfl⟩ : syracuseStep 1605199 = 2407799) B2407799
theorem B2408015 : Blo 1605001 2408015 := bstep (se 1 (by rfl) ⟨1806011, by rfl⟩ : syracuseStep 2408015 = 3612023) B3612023
theorem B10288727 : Blo 1605001 10288727 := bstep (se 1 (by rfl) ⟨7716545, by rfl⟩ : syracuseStep 10288727 = 15433091) B15433091
theorem B1605215 : Blo 1605001 1605215 := bstep (se 1 (by rfl) ⟨1203911, by rfl⟩ : syracuseStep 1605215 = 2407823) B2407823
theorem B3612257 : Blo 1605001 3612257 := bstep (se 2 (by rfl) ⟨1354596, by rfl⟩ : syracuseStep 3612257 = 2709193) B2709193
theorem B1605243 : Blo 1605001 1605243 := bstep (se 1 (by rfl) ⟨1203932, by rfl⟩ : syracuseStep 1605243 = 2407865) B2407865
theorem B3858043 : Blo 1605001 3858043 := bstep (se 1 (by rfl) ⟨2893532, by rfl⟩ : syracuseStep 3858043 = 5787065) B5787065
theorem B1605295 : Blo 1605001 1605295 := bstep (se 1 (by rfl) ⟨1203971, by rfl⟩ : syracuseStep 1605295 = 2407943) B2407943
theorem B3858119 : Blo 1605001 3858119 := bstep (se 1 (by rfl) ⟨2893589, by rfl⟩ : syracuseStep 3858119 = 5787179) B5787179
theorem B4062919 : Blo 1605001 4062919 := bstep (se 1 (by rfl) ⟨3047189, by rfl⟩ : syracuseStep 4062919 = 6094379) B6094379
theorem B4947655 : Blo 1605001 4947655 := bstep (se 1 (by rfl) ⟨3710741, by rfl⟩ : syracuseStep 4947655 = 7421483) B7421483
theorem B1605319 : Blo 1605001 1605319 := bstep (se 1 (by rfl) ⟨1203989, by rfl⟩ : syracuseStep 1605319 = 2407979) B2407979
theorem B2408135 : Blo 1605001 2408135 := bstep (se 1 (by rfl) ⟨1806101, by rfl⟩ : syracuseStep 2408135 = 3612203) B3612203
theorem B6094547 : Blo 1605001 6094547 := bstep (se 1 (by rfl) ⟨4570910, by rfl⟩ : syracuseStep 6094547 = 9141821) B9141821
theorem B1605339 : Blo 1605001 1605339 := bstep (se 1 (by rfl) ⟨1204004, by rfl⟩ : syracuseStep 1605339 = 2408009) B2408009
theorem B3047159 : Blo 1605001 3047159 := bstep (se 1 (by rfl) ⟨2285369, by rfl⟩ : syracuseStep 3047159 = 4570739) B4570739
theorem B5422841 : Blo 1605001 5422841 := bstep (se 2 (by rfl) ⟨2033565, by rfl⟩ : syracuseStep 5422841 = 4067131) B4067131
theorem B1605415 : Blo 1605001 1605415 := bstep (se 1 (by rfl) ⟨1204061, by rfl⟩ : syracuseStep 1605415 = 2408123) B2408123
theorem B1605455 : Blo 1605001 1605455 := bstep (se 1 (by rfl) ⟨1204091, by rfl⟩ : syracuseStep 1605455 = 2408183) B2408183
theorem B1605471 : Blo 1605001 1605471 := bstep (se 1 (by rfl) ⟨1204103, by rfl⟩ : syracuseStep 1605471 = 2408207) B2408207
theorem B2408297 : Blo 1605001 2408297 := bstep (se 2 (by rfl) ⟨903111, by rfl⟩ : syracuseStep 2408297 = 1806223) B1806223
theorem B9150317 : Blo 1605001 9150317 := bstep (se 3 (by rfl) ⟨1715684, by rfl⟩ : syracuseStep 9150317 = 3431369) B3431369
theorem B1605499 : Blo 1605001 1605499 := bstep (se 1 (by rfl) ⟨1204124, by rfl⟩ : syracuseStep 1605499 = 2408249) B2408249
theorem B3047311 : Blo 1605001 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B1605551 : Blo 1605001 1605551 := bstep (se 1 (by rfl) ⟨1204163, by rfl⟩ : syracuseStep 1605551 = 2408327) B2408327
theorem B2408375 : Blo 1605001 2408375 := bstep (se 1 (by rfl) ⟨1806281, by rfl⟩ : syracuseStep 2408375 = 3612563) B3612563
theorem B3612599 : Blo 1605001 3612599 := bstep (se 1 (by rfl) ⟨2709449, by rfl⟩ : syracuseStep 3612599 = 5418899) B5418899
theorem B5496763 : Blo 1605001 5496763 := bstep (se 1 (by rfl) ⟨4122572, by rfl⟩ : syracuseStep 5496763 = 8245145) B8245145
theorem B1605575 : Blo 1605001 1605575 := bstep (se 1 (by rfl) ⟨1204181, by rfl⟩ : syracuseStep 1605575 = 2408363) B2408363
theorem B1605595 : Blo 1605001 1605595 := bstep (se 1 (by rfl) ⟨1204196, by rfl⟩ : syracuseStep 1605595 = 2408393) B2408393
theorem B2408411 : Blo 1605001 2408411 := bstep (se 1 (by rfl) ⟨1806308, by rfl⟩ : syracuseStep 2408411 = 3612617) B3612617
theorem B2711657 : Blo 1605001 2711657 := bstep (se 2 (by rfl) ⟨1016871, by rfl⟩ : syracuseStep 2711657 = 2033743) B2033743
theorem B6856913 : Blo 1605001 6856913 := bstep (se 2 (by rfl) ⟨2571342, by rfl⟩ : syracuseStep 6856913 = 5142685) B5142685
theorem B1605919 : Blo 1605001 1605919 := bstep (se 1 (by rfl) ⟨1204439, by rfl⟩ : syracuseStep 1605919 = 2408879) B2408879
theorem B2408795 : Blo 1605001 2408795 := bstep (se 1 (by rfl) ⟨1806596, by rfl⟩ : syracuseStep 2408795 = 3613193) B3613193
theorem B1605979 : Blo 1605001 1605979 := bstep (se 1 (by rfl) ⟨1204484, by rfl⟩ : syracuseStep 1605979 = 2408969) B2408969
theorem B1605999 : Blo 1605001 1605999 := bstep (se 1 (by rfl) ⟨1204499, by rfl⟩ : syracuseStep 1605999 = 2408999) B2408999
theorem B1606055 : Blo 1605001 1606055 := bstep (se 1 (by rfl) ⟨1204541, by rfl⟩ : syracuseStep 1606055 = 2409083) B2409083
theorem B6857135 : Blo 1605001 6857135 := bstep (se 1 (by rfl) ⟨5142851, by rfl⟩ : syracuseStep 6857135 = 10285703) B10285703
theorem B3613103 : Blo 1605001 3613103 := bstep (se 1 (by rfl) ⟨2709827, by rfl⟩ : syracuseStep 3613103 = 5419655) B5419655
theorem B3613139 : Blo 1605001 3613139 := bstep (se 1 (by rfl) ⟨2709854, by rfl⟩ : syracuseStep 3613139 = 5419709) B5419709
theorem B9142753 : Blo 1605001 9142753 := bstep (se 2 (by rfl) ⟨3428532, by rfl⟩ : syracuseStep 9142753 = 6857065) B6857065
theorem B2032123 : Blo 1605001 2032123 := bstep (se 1 (by rfl) ⟨1524092, by rfl⟩ : syracuseStep 2032123 = 3048185) B3048185
theorem B1606139 : Blo 1605001 1606139 := bstep (se 1 (by rfl) ⟨1204604, by rfl⟩ : syracuseStep 1606139 = 2409209) B2409209
theorem B3613247 : Blo 1605001 3613247 := bstep (se 1 (by rfl) ⟨2709935, by rfl⟩ : syracuseStep 3613247 = 5419871) B5419871
theorem B2409023 : Blo 1605001 2409023 := bstep (se 1 (by rfl) ⟨1806767, by rfl⟩ : syracuseStep 2409023 = 3613535) B3613535
theorem B1606207 : Blo 1605001 1606207 := bstep (se 1 (by rfl) ⟨1204655, by rfl⟩ : syracuseStep 1606207 = 2409311) B2409311
theorem B1606215 : Blo 1605001 1606215 := bstep (se 1 (by rfl) ⟨1204661, by rfl⟩ : syracuseStep 1606215 = 2409323) B2409323
theorem B8135315 : Blo 1605001 8135315 := bstep (se 1 (by rfl) ⟨6101486, by rfl⟩ : syracuseStep 8135315 = 12202973) B12202973
theorem B3613355 : Blo 1605001 3613355 := bstep (se 1 (by rfl) ⟨2710016, by rfl⟩ : syracuseStep 3613355 = 5420033) B5420033
theorem B2409143 : Blo 1605001 2409143 := bstep (se 1 (by rfl) ⟨1806857, by rfl⟩ : syracuseStep 2409143 = 3613715) B3613715
theorem B111280841 : Blo 1605001 111280841 := bstep (se 2 (by rfl) ⟨41730315, by rfl⟩ : syracuseStep 111280841 = 83460631) B83460631
theorem B1606367 : Blo 1605001 1606367 := bstep (se 1 (by rfl) ⟨1204775, by rfl⟩ : syracuseStep 1606367 = 2409551) B2409551
theorem B1606447 : Blo 1605001 1606447 := bstep (se 1 (by rfl) ⟨1204835, by rfl⟩ : syracuseStep 1606447 = 2409671) B2409671
theorem B9266015 : Blo 1605001 9266015 := bstep (se 1 (by rfl) ⟨6949511, by rfl⟩ : syracuseStep 9266015 = 13899023) B13899023
theorem B2409371 : Blo 1605001 2409371 := bstep (se 1 (by rfl) ⟨1807028, by rfl⟩ : syracuseStep 2409371 = 3614057) B3614057
theorem B1606555 : Blo 1605001 1606555 := bstep (se 1 (by rfl) ⟨1204916, by rfl⟩ : syracuseStep 1606555 = 2409833) B2409833
theorem B1606607 : Blo 1605001 1606607 := bstep (se 1 (by rfl) ⟨1204955, by rfl⟩ : syracuseStep 1606607 = 2409911) B2409911
theorem B23159783 : Blo 1605001 23159783 := bstep (se 1 (by rfl) ⟨17369837, by rfl⟩ : syracuseStep 23159783 = 34739675) B34739675
theorem B1606631 : Blo 1605001 1606631 := bstep (se 1 (by rfl) ⟨1204973, by rfl⟩ : syracuseStep 1606631 = 2409947) B2409947
theorem B6096019 : Blo 1605001 6096019 := bstep (se 1 (by rfl) ⟨4572014, by rfl⟩ : syracuseStep 6096019 = 9144029) B9144029
theorem B6857885 : Blo 1605001 6857885 := bstep (se 3 (by rfl) ⟨1285853, by rfl⟩ : syracuseStep 6857885 = 2571707) B2571707
theorem B3613895 : Blo 1605001 3613895 := bstep (se 1 (by rfl) ⟨2710421, by rfl⟩ : syracuseStep 3613895 = 5420843) B5420843
theorem B4064489 : Blo 1605001 4064489 := bstep (se 2 (by rfl) ⟨1524183, by rfl⟩ : syracuseStep 4064489 = 3048367) B3048367
theorem B2934047 : Blo 1605001 2934047 := bstep (se 1 (by rfl) ⟨2200535, by rfl⟩ : syracuseStep 2934047 = 4401071) B4401071
theorem B1606943 : Blo 1605001 1606943 := bstep (se 1 (by rfl) ⟨1205207, by rfl⟩ : syracuseStep 1606943 = 2410415) B2410415
theorem B2409767 : Blo 1605001 2409767 := bstep (se 1 (by rfl) ⟨1807325, by rfl⟩ : syracuseStep 2409767 = 3614651) B3614651
theorem B8242519 : Blo 1605001 8242519 := bstep (se 1 (by rfl) ⟨6181889, by rfl⟩ : syracuseStep 8242519 = 12363779) B12363779
theorem B3614075 : Blo 1605001 3614075 := bstep (se 1 (by rfl) ⟨2710556, by rfl⟩ : syracuseStep 3614075 = 5421113) B5421113
theorem B2409851 : Blo 1605001 2409851 := bstep (se 1 (by rfl) ⟨1807388, by rfl⟩ : syracuseStep 2409851 = 3614777) B3614777
theorem B4064651 : Blo 1605001 4064651 := bstep (se 1 (by rfl) ⟨3048488, by rfl⟩ : syracuseStep 4064651 = 6096977) B6096977
theorem B2033095 : Blo 1605001 2033095 := bstep (se 1 (by rfl) ⟨1524821, by rfl⟩ : syracuseStep 2033095 = 3049643) B3049643
theorem B3614201 : Blo 1605001 3614201 := bstep (se 2 (by rfl) ⟨1355325, by rfl⟩ : syracuseStep 3614201 = 2710651) B2710651
theorem B2409977 : Blo 1605001 2409977 := bstep (se 2 (by rfl) ⟨903741, by rfl⟩ : syracuseStep 2409977 = 1807483) B1807483
theorem B4343303 : Blo 1605001 4343303 := bstep (se 1 (by rfl) ⟨3257477, by rfl⟩ : syracuseStep 4343303 = 6514955) B6514955
theorem B3614291 : Blo 1605001 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B4064863 : Blo 1605001 4064863 := bstep (se 1 (by rfl) ⟨3048647, by rfl⟩ : syracuseStep 4064863 = 6097295) B6097295
theorem B2410079 : Blo 1605001 2410079 := bstep (se 1 (by rfl) ⟨1807559, by rfl⟩ : syracuseStep 2410079 = 3615119) B3615119
theorem B4638365 : Blo 1605001 4638365 := bstep (se 3 (by rfl) ⟨869693, by rfl⟩ : syracuseStep 4638365 = 1739387) B1739387
theorem B8128187 : Blo 1605001 8128187 := bstep (se 1 (by rfl) ⟨6096140, by rfl⟩ : syracuseStep 8128187 = 12192281) B12192281
theorem B3614471 : Blo 1605001 3614471 := bstep (se 1 (by rfl) ⟨2710853, by rfl⟩ : syracuseStep 3614471 = 5421707) B5421707
theorem B7825207 : Blo 1605001 7825207 := bstep (se 1 (by rfl) ⟨5868905, by rfl⟩ : syracuseStep 7825207 = 11737811) B11737811
theorem B2410295 : Blo 1605001 2410295 := bstep (se 1 (by rfl) ⟨1807721, by rfl⟩ : syracuseStep 2410295 = 3615443) B3615443
theorem B31279031 : Blo 1605001 31279031 := bstep (se 1 (by rfl) ⟨23459273, by rfl⟩ : syracuseStep 31279031 = 46918547) B46918547
theorem B4343759 : Blo 1605001 4343759 := bstep (se 1 (by rfl) ⟨3257819, by rfl⟩ : syracuseStep 4343759 = 6515639) B6515639
theorem B4065491 : Blo 1605001 4065491 := bstep (se 1 (by rfl) ⟨3049118, by rfl⟩ : syracuseStep 4065491 = 6098237) B6098237
theorem B5417225 : Blo 1605001 5417225 := bstep (se 2 (by rfl) ⟨2031459, by rfl⟩ : syracuseStep 5417225 = 4062919) B4062919
theorem B6596873 : Blo 1605001 6596873 := bstep (se 2 (by rfl) ⟨2473827, by rfl⟩ : syracuseStep 6596873 = 4947655) B4947655
theorem B3615083 : Blo 1605001 3615083 := bstep (se 1 (by rfl) ⟨2711312, by rfl⟩ : syracuseStep 3615083 = 5422625) B5422625
theorem B6859151 : Blo 1605001 6859151 := bstep (se 1 (by rfl) ⟨5144363, by rfl⟩ : syracuseStep 6859151 = 10288727) B10288727
theorem B3615227 : Blo 1605001 3615227 := bstep (se 1 (by rfl) ⟨2711420, by rfl⟩ : syracuseStep 3615227 = 5422841) B5422841
theorem B3615353 : Blo 1605001 3615353 := bstep (se 2 (by rfl) ⟨1355757, by rfl⟩ : syracuseStep 3615353 = 2711515) B2711515
theorem B7719563 : Blo 1605001 7719563 := bstep (se 1 (by rfl) ⟨5789672, by rfl⟩ : syracuseStep 7719563 = 11579345) B11579345
theorem B20581037 : Blo 1605001 20581037 := bstep (se 3 (by rfl) ⟨3858944, by rfl⟩ : syracuseStep 20581037 = 7717889) B7717889
theorem B3476143 : Blo 1605001 3476143 := bstep (se 1 (by rfl) ⟨2607107, by rfl⟩ : syracuseStep 3476143 = 5214215) B5214215
theorem B3615407 : Blo 1605001 3615407 := bstep (se 1 (by rfl) ⟨2711555, by rfl⟩ : syracuseStep 3615407 = 5423111) B5423111
theorem B6859511 : Blo 1605001 6859511 := bstep (se 1 (by rfl) ⟨5144633, by rfl⟩ : syracuseStep 6859511 = 10289267) B10289267
theorem B3615479 : Blo 1605001 3615479 := bstep (se 1 (by rfl) ⟨2711609, by rfl⟩ : syracuseStep 3615479 = 5423219) B5423219
theorem B13380385 : Blo 1605001 13380385 := bstep (se 2 (by rfl) ⟨5017644, by rfl⟩ : syracuseStep 13380385 = 10035289) B10035289
theorem B3615659 : Blo 1605001 3615659 := bstep (se 1 (by rfl) ⟨2711744, by rfl⟩ : syracuseStep 3615659 = 5423489) B5423489
theorem B5786747 : Blo 1605001 5786747 := bstep (se 1 (by rfl) ⟨4340060, by rfl⟩ : syracuseStep 5786747 = 8680121) B8680121
theorem B3091751 : Blo 1605001 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B5786977 : Blo 1605001 5786977 := bstep (se 2 (by rfl) ⟨2170116, by rfl⟩ : syracuseStep 5786977 = 4340233) B4340233
theorem B5418359 : Blo 1605001 5418359 := bstep (se 1 (by rfl) ⟨4063769, by rfl⟩ : syracuseStep 5418359 = 8127539) B8127539
theorem B3911051 : Blo 1605001 3911051 := bstep (se 1 (by rfl) ⟨2933288, by rfl⟩ : syracuseStep 3911051 = 5866577) B5866577
theorem B23793041 : Blo 1605001 23793041 := bstep (se 2 (by rfl) ⟨8922390, by rfl⟩ : syracuseStep 23793041 = 17844781) B17844781
theorem B27446849 : Blo 1605001 27446849 := bstep (se 2 (by rfl) ⟨10292568, by rfl⟩ : syracuseStep 27446849 = 20585137) B20585137
theorem B3173971 : Blo 1605001 3173971 := bstep (se 1 (by rfl) ⟨2380478, by rfl⟩ : syracuseStep 3173971 = 4760957) B4760957
theorem B8130131 : Blo 1605001 8130131 := bstep (se 1 (by rfl) ⟨6097598, by rfl⟩ : syracuseStep 8130131 = 12195197) B12195197
theorem B3714655 : Blo 1605001 3714655 := bstep (se 1 (by rfl) ⟨2785991, by rfl⟩ : syracuseStep 3714655 = 5571983) B5571983
theorem B17370787 : Blo 1605001 17370787 := bstep (se 1 (by rfl) ⟨13028090, by rfl⟩ : syracuseStep 17370787 = 26056181) B26056181
theorem B6860551 : Blo 1605001 6860551 := bstep (se 1 (by rfl) ⟨5145413, by rfl⟩ : syracuseStep 6860551 = 10290827) B10290827
theorem B50106221 : Blo 1605001 50106221 := bstep (se 3 (by rfl) ⟨9394916, by rfl⟩ : syracuseStep 50106221 = 18789833) B18789833
theorem B23154589 : Blo 1605001 23154589 := bstep (se 3 (by rfl) ⟨4341485, by rfl⟩ : syracuseStep 23154589 = 8682971) B8682971
theorem B6860825 : Blo 1605001 6860825 := bstep (se 2 (by rfl) ⟨2572809, by rfl⟩ : syracuseStep 6860825 = 5145619) B5145619
theorem B9146627 : Blo 1605001 9146627 := bstep (se 1 (by rfl) ⟨6859970, by rfl⟩ : syracuseStep 9146627 = 13719941) B13719941
theorem B1929511 : Blo 1605001 1929511 := bstep (se 1 (by rfl) ⟨1447133, by rfl⟩ : syracuseStep 1929511 = 2894267) B2894267
theorem B5419439 : Blo 1605001 5419439 := bstep (se 1 (by rfl) ⟨4064579, by rfl⟩ : syracuseStep 5419439 = 8129159) B8129159
theorem B3174985 : Blo 1605001 3174985 := bstep (se 2 (by rfl) ⟨1190619, by rfl⟩ : syracuseStep 3174985 = 2381239) B2381239
theorem B1806943 : Blo 1605001 1806943 := bstep (se 1 (by rfl) ⟨1355207, by rfl⟩ : syracuseStep 1806943 = 2710415) B2710415
theorem B7819897 : Blo 1605001 7819897 := bstep (se 2 (by rfl) ⟨2932461, by rfl⟩ : syracuseStep 7819897 = 5864923) B5864923
theorem B4575865 : Blo 1605001 4575865 := bstep (se 2 (by rfl) ⟨1715949, by rfl⟩ : syracuseStep 4575865 = 3431899) B3431899
theorem B6861611 : Blo 1605001 6861611 := bstep (se 1 (by rfl) ⟨5146208, by rfl⟩ : syracuseStep 6861611 = 10292417) B10292417
theorem B15438701 : Blo 1605001 15438701 := bstep (se 3 (by rfl) ⟨2894756, by rfl⟩ : syracuseStep 15438701 = 5789513) B5789513
theorem B8238019 : Blo 1605001 8238019 := bstep (se 1 (by rfl) ⟨6178514, by rfl⟩ : syracuseStep 8238019 = 12357029) B12357029
theorem B6099907 : Blo 1605001 6099907 := bstep (se 1 (by rfl) ⟨4574930, by rfl⟩ : syracuseStep 6099907 = 9149861) B9149861
theorem B2708471 : Blo 1605001 2708471 := bstep (se 1 (by rfl) ⟨2031353, by rfl⟩ : syracuseStep 2708471 = 4062707) B4062707
theorem B3912923 : Blo 1605001 3912923 := bstep (se 1 (by rfl) ⟨2934692, by rfl⟩ : syracuseStep 3912923 = 5869385) B5869385
theorem B6100211 : Blo 1605001 6100211 := bstep (se 1 (by rfl) ⟨4575158, by rfl⟩ : syracuseStep 6100211 = 9150317) B9150317
theorem B7329017 : Blo 1605001 7329017 := bstep (se 2 (by rfl) ⟨2748381, by rfl⟩ : syracuseStep 7329017 = 5496763) B5496763
theorem B3257639 : Blo 1605001 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B5420411 : Blo 1605001 5420411 := bstep (se 1 (by rfl) ⟨4065308, by rfl⟩ : syracuseStep 5420411 = 8130617) B8130617
theorem B6100667 : Blo 1605001 6100667 := bstep (se 1 (by rfl) ⟨4575500, by rfl⟩ : syracuseStep 6100667 = 9151001) B9151001
theorem B2709227 : Blo 1605001 2709227 := bstep (se 1 (by rfl) ⟨2031920, by rfl⟩ : syracuseStep 2709227 = 4063841) B4063841
theorem B6862927 : Blo 1605001 6862927 := bstep (se 1 (by rfl) ⟨5147195, by rfl⟩ : syracuseStep 6862927 = 10294391) B10294391
theorem B44546183 : Blo 1605001 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B8796527 : Blo 1605001 8796527 := bstep (se 1 (by rfl) ⟨6597395, by rfl⟩ : syracuseStep 8796527 = 13194791) B13194791
theorem B8133047 : Blo 1605001 8133047 := bstep (se 1 (by rfl) ⟨6099785, by rfl⟩ : syracuseStep 8133047 = 12199571) B12199571
theorem B4340179 : Blo 1605001 4340179 := bstep (se 1 (by rfl) ⟨3255134, by rfl⟩ : syracuseStep 4340179 = 6510269) B6510269
theorem B10566283 : Blo 1605001 10566283 := bstep (se 1 (by rfl) ⟨7924712, by rfl⟩ : syracuseStep 10566283 = 15849425) B15849425
theorem B2710199 : Blo 1605001 2710199 := bstep (se 1 (by rfl) ⟨2032649, by rfl⟩ : syracuseStep 2710199 = 4065299) B4065299
theorem B5421815 : Blo 1605001 5421815 := bstep (se 1 (by rfl) ⟨4066361, by rfl⟩ : syracuseStep 5421815 = 8132723) B8132723
theorem B41720579 : Blo 1605001 41720579 := bstep (se 1 (by rfl) ⟨31290434, by rfl⟩ : syracuseStep 41720579 = 62580869) B62580869
theorem B3611411 : Blo 1605001 3611411 := bstep (se 1 (by rfl) ⟨2708558, by rfl⟩ : syracuseStep 3611411 = 5417117) B5417117
theorem B59390749 : Blo 1605001 59390749 := bstep (se 3 (by rfl) ⟨11135765, by rfl⟩ : syracuseStep 59390749 = 22271531) B22271531
theorem B23166071 : Blo 1605001 23166071 := bstep (se 1 (by rfl) ⟨17374553, by rfl⟩ : syracuseStep 23166071 = 34749107) B34749107
theorem B3611771 : Blo 1605001 3611771 := bstep (se 1 (by rfl) ⟨2708828, by rfl⟩ : syracuseStep 3611771 = 5417657) B5417657
theorem B2407643 : Blo 1605001 2407643 := bstep (se 1 (by rfl) ⟨1805732, by rfl⟩ : syracuseStep 2407643 = 3611465) B3611465
theorem B3661033 : Blo 1605001 3661033 := bstep (se 2 (by rfl) ⟨1372887, by rfl⟩ : syracuseStep 3661033 = 2745775) B2745775
theorem B2571497 : Blo 1605001 2571497 := bstep (se 2 (by rfl) ⟨964311, by rfl⟩ : syracuseStep 2571497 = 1928623) B1928623
theorem B3611897 : Blo 1605001 3611897 := bstep (se 2 (by rfl) ⟨1354461, by rfl⟩ : syracuseStep 3611897 = 2708923) B2708923
theorem B55639331 : Blo 1605001 55639331 := bstep (se 1 (by rfl) ⟨41729498, by rfl⟩ : syracuseStep 55639331 = 83458997) B83458997
theorem B8125757 : Blo 1605001 8125757 := bstep (se 3 (by rfl) ⟨1523579, by rfl⟩ : syracuseStep 8125757 = 3047159) B3047159
theorem B5143927 : Blo 1605001 5143927 := bstep (se 1 (by rfl) ⟨3857945, by rfl⟩ : syracuseStep 5143927 = 7715891) B7715891
theorem B2407817 : Blo 1605001 2407817 := bstep (se 2 (by rfl) ⟨902931, by rfl⟩ : syracuseStep 2407817 = 1805863) B1805863
theorem B3612041 : Blo 1605001 3612041 := bstep (se 2 (by rfl) ⟨1354515, by rfl⟩ : syracuseStep 3612041 = 2709031) B2709031
theorem B2710921 : Blo 1605001 2710921 := bstep (se 2 (by rfl) ⟨1016595, by rfl⟩ : syracuseStep 2710921 = 2033191) B2033191
theorem B1605031 : Blo 1605001 1605031 := bstep (se 1 (by rfl) ⟨1203773, by rfl⟩ : syracuseStep 1605031 = 2407547) B2407547
theorem B5144057 : Blo 1605001 5144057 := bstep (se 2 (by rfl) ⟨1929021, by rfl⟩ : syracuseStep 5144057 = 3858043) B3858043
theorem B1605115 : Blo 1605001 1605115 := bstep (se 1 (by rfl) ⟨1203836, by rfl⟩ : syracuseStep 1605115 = 2407673) B2407673
theorem B3612167 : Blo 1605001 3612167 := bstep (se 1 (by rfl) ⟨2709125, by rfl⟩ : syracuseStep 3612167 = 5418251) B5418251
theorem B1605183 : Blo 1605001 1605183 := bstep (se 1 (by rfl) ⟨1203887, by rfl⟩ : syracuseStep 1605183 = 2407775) B2407775
theorem B1605191 : Blo 1605001 1605191 := bstep (se 1 (by rfl) ⟨1203893, by rfl⟩ : syracuseStep 1605191 = 2407787) B2407787
theorem B3612347 : Blo 1605001 3612347 := bstep (se 1 (by rfl) ⟨2709260, by rfl⟩ : syracuseStep 3612347 = 5418521) B5418521
theorem B15441623 : Blo 1605001 15441623 := bstep (se 1 (by rfl) ⟨11581217, by rfl⟩ : syracuseStep 15441623 = 23162435) B23162435
theorem B1605343 : Blo 1605001 1605343 := bstep (se 1 (by rfl) ⟨1204007, by rfl⟩ : syracuseStep 1605343 = 2408015) B2408015
theorem B2408171 : Blo 1605001 2408171 := bstep (se 1 (by rfl) ⟨1806128, by rfl⟩ : syracuseStep 2408171 = 3612257) B3612257
theorem B4570921 : Blo 1605001 4570921 := bstep (se 2 (by rfl) ⟨1714095, by rfl⟩ : syracuseStep 4570921 = 3428191) B3428191
theorem B2572079 : Blo 1605001 2572079 := bstep (se 1 (by rfl) ⟨1929059, by rfl⟩ : syracuseStep 2572079 = 3858119) B3858119
theorem B1605423 : Blo 1605001 1605423 := bstep (se 1 (by rfl) ⟨1204067, by rfl⟩ : syracuseStep 1605423 = 2408135) B2408135
theorem B5422895 : Blo 1605001 5422895 := bstep (se 1 (by rfl) ⟨4067171, by rfl⟩ : syracuseStep 5422895 = 8134343) B8134343
theorem B4063031 : Blo 1605001 4063031 := bstep (se 1 (by rfl) ⟨3047273, by rfl⟩ : syracuseStep 4063031 = 6094547) B6094547
theorem B3612473 : Blo 1605001 3612473 := bstep (se 2 (by rfl) ⟨1354677, by rfl⟩ : syracuseStep 3612473 = 2709355) B2709355
theorem B2711353 : Blo 1605001 2711353 := bstep (se 2 (by rfl) ⟨1016757, by rfl⟩ : syracuseStep 2711353 = 2033515) B2033515
theorem B4063081 : Blo 1605001 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B1605531 : Blo 1605001 1605531 := bstep (se 1 (by rfl) ⟨1204148, by rfl⟩ : syracuseStep 1605531 = 2408297) B2408297
theorem B1605583 : Blo 1605001 1605583 := bstep (se 1 (by rfl) ⟨1204187, by rfl⟩ : syracuseStep 1605583 = 2408375) B2408375
theorem B2408399 : Blo 1605001 2408399 := bstep (se 1 (by rfl) ⟨1806299, by rfl⟩ : syracuseStep 2408399 = 3612599) B3612599
theorem B1605607 : Blo 1605001 1605607 := bstep (se 1 (by rfl) ⟨1204205, by rfl⟩ : syracuseStep 1605607 = 2408411) B2408411
theorem B9150569 : Blo 1605001 9150569 := bstep (se 2 (by rfl) ⟨3431463, by rfl⟩ : syracuseStep 9150569 = 6862927) B6862927
theorem B4571275 : Blo 1605001 4571275 := bstep (se 1 (by rfl) ⟨3428456, by rfl⟩ : syracuseStep 4571275 = 6856913) B6856913
theorem B1605863 : Blo 1605001 1605863 := bstep (se 1 (by rfl) ⟨1204397, by rfl⟩ : syracuseStep 1605863 = 2408795) B2408795
theorem B4571423 : Blo 1605001 4571423 := bstep (se 1 (by rfl) ⟨3428567, by rfl⟩ : syracuseStep 4571423 = 6857135) B6857135
theorem B3612959 : Blo 1605001 3612959 := bstep (se 1 (by rfl) ⟨2709719, by rfl⟩ : syracuseStep 3612959 = 5419439) B5419439
theorem B2408735 : Blo 1605001 2408735 := bstep (se 1 (by rfl) ⟨1806551, by rfl⟩ : syracuseStep 2408735 = 3613103) B3613103
theorem B2408759 : Blo 1605001 2408759 := bstep (se 1 (by rfl) ⟨1806569, by rfl⟩ : syracuseStep 2408759 = 3613139) B3613139
theorem B2408831 : Blo 1605001 2408831 := bstep (se 1 (by rfl) ⟨1806623, by rfl⟩ : syracuseStep 2408831 = 3613247) B3613247
theorem B1606015 : Blo 1605001 1606015 := bstep (se 1 (by rfl) ⟨1204511, by rfl⟩ : syracuseStep 1606015 = 2409023) B2409023
theorem B5423543 : Blo 1605001 5423543 := bstep (se 1 (by rfl) ⟨4067657, by rfl⟩ : syracuseStep 5423543 = 8135315) B8135315
theorem B2408903 : Blo 1605001 2408903 := bstep (se 1 (by rfl) ⟨1806677, by rfl⟩ : syracuseStep 2408903 = 3613355) B3613355
theorem B1606095 : Blo 1605001 1606095 := bstep (se 1 (by rfl) ⟨1204571, by rfl⟩ : syracuseStep 1606095 = 2409143) B2409143
theorem B74187227 : Blo 1605001 74187227 := bstep (se 1 (by rfl) ⟨55640420, by rfl⟩ : syracuseStep 74187227 = 111280841) B111280841
theorem B1606247 : Blo 1605001 1606247 := bstep (se 1 (by rfl) ⟨1204685, by rfl⟩ : syracuseStep 1606247 = 2409371) B2409371
theorem B12190337 : Blo 1605001 12190337 := bstep (se 2 (by rfl) ⟨4571376, by rfl⟩ : syracuseStep 12190337 = 9142753) B9142753
theorem B2409257 : Blo 1605001 2409257 := bstep (se 2 (by rfl) ⟨903471, by rfl⟩ : syracuseStep 2409257 = 1806943) B1806943
theorem B2409263 : Blo 1605001 2409263 := bstep (se 1 (by rfl) ⟨1806947, by rfl⟩ : syracuseStep 2409263 = 3613895) B3613895
theorem B1606511 : Blo 1605001 1606511 := bstep (se 1 (by rfl) ⟨1204883, by rfl⟩ : syracuseStep 1606511 = 2409767) B2409767
theorem B3613607 : Blo 1605001 3613607 := bstep (se 1 (by rfl) ⟨2710205, by rfl⟩ : syracuseStep 3613607 = 5420411) B5420411
theorem B2409383 : Blo 1605001 2409383 := bstep (se 1 (by rfl) ⟨1807037, by rfl⟩ : syracuseStep 2409383 = 3614075) B3614075
theorem B1606567 : Blo 1605001 1606567 := bstep (se 1 (by rfl) ⟨1204925, by rfl⟩ : syracuseStep 1606567 = 2409851) B2409851
theorem B2409467 : Blo 1605001 2409467 := bstep (se 1 (by rfl) ⟨1807100, by rfl⟩ : syracuseStep 2409467 = 3614201) B3614201
theorem B1606651 : Blo 1605001 1606651 := bstep (se 1 (by rfl) ⟨1204988, by rfl⟩ : syracuseStep 1606651 = 2409977) B2409977
theorem B10429469 : Blo 1605001 10429469 := bstep (se 3 (by rfl) ⟨1955525, by rfl⟩ : syracuseStep 10429469 = 3911051) B3911051
theorem B2409527 : Blo 1605001 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B1606719 : Blo 1605001 1606719 := bstep (se 1 (by rfl) ⟨1205039, by rfl⟩ : syracuseStep 1606719 = 2410079) B2410079
theorem B2409647 : Blo 1605001 2409647 := bstep (se 1 (by rfl) ⟨1807235, by rfl⟩ : syracuseStep 2409647 = 3614471) B3614471
theorem B1606863 : Blo 1605001 1606863 := bstep (se 1 (by rfl) ⟨1205147, by rfl⟩ : syracuseStep 1606863 = 2410295) B2410295
theorem B29697455 : Blo 1605001 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B8128025 : Blo 1605001 8128025 := bstep (se 2 (by rfl) ⟨3048009, by rfl⟩ : syracuseStep 8128025 = 6096019) B6096019
theorem B10290725 : Blo 1605001 10290725 := bstep (se 4 (by rfl) ⟨964755, by rfl⟩ : syracuseStep 10290725 = 1929511) B1929511
theorem B2410055 : Blo 1605001 2410055 := bstep (se 1 (by rfl) ⟨1807541, by rfl⟩ : syracuseStep 2410055 = 3615083) B3615083
theorem B4572767 : Blo 1605001 4572767 := bstep (se 1 (by rfl) ⟨3429575, by rfl⟩ : syracuseStep 4572767 = 6859151) B6859151
theorem B2410151 : Blo 1605001 2410151 := bstep (se 1 (by rfl) ⟨1807613, by rfl⟩ : syracuseStep 2410151 = 3615227) B3615227
theorem B2410235 : Blo 1605001 2410235 := bstep (se 1 (by rfl) ⟨1807676, by rfl⟩ : syracuseStep 2410235 = 3615353) B3615353
theorem B2410271 : Blo 1605001 2410271 := bstep (se 1 (by rfl) ⟨1807703, by rfl⟩ : syracuseStep 2410271 = 3615407) B3615407
theorem B6858569 : Blo 1605001 6858569 := bstep (se 2 (by rfl) ⟨2571963, by rfl⟩ : syracuseStep 6858569 = 5143927) B5143927
theorem B4573007 : Blo 1605001 4573007 := bstep (se 1 (by rfl) ⟨3429755, by rfl⟩ : syracuseStep 4573007 = 6859511) B6859511
theorem B3614543 : Blo 1605001 3614543 := bstep (se 1 (by rfl) ⟨2710907, by rfl⟩ : syracuseStep 3614543 = 5421815) B5421815
theorem B2410319 : Blo 1605001 2410319 := bstep (se 1 (by rfl) ⟨1807739, by rfl⟩ : syracuseStep 2410319 = 3615479) B3615479
theorem B27813719 : Blo 1605001 27813719 := bstep (se 1 (by rfl) ⟨20860289, by rfl⟩ : syracuseStep 27813719 = 41720579) B41720579
theorem B3614561 : Blo 1605001 3614561 := bstep (se 2 (by rfl) ⟨1355460, by rfl⟩ : syracuseStep 3614561 = 2710921) B2710921
theorem B2410439 : Blo 1605001 2410439 := bstep (se 1 (by rfl) ⟨1807829, by rfl⟩ : syracuseStep 2410439 = 3615659) B3615659
theorem B15444047 : Blo 1605001 15444047 := bstep (se 1 (by rfl) ⟨11583035, by rfl⟩ : syracuseStep 15444047 = 23166071) B23166071
theorem B6858877 : Blo 1605001 6858877 := bstep (se 3 (by rfl) ⟨1286039, by rfl⟩ : syracuseStep 6858877 = 2572079) B2572079
theorem B1714331 : Blo 1605001 1714331 := bstep (se 1 (by rfl) ⟨1285748, by rfl⟩ : syracuseStep 1714331 = 2571497) B2571497
theorem B5417171 : Blo 1605001 5417171 := bstep (se 1 (by rfl) ⟨4062878, by rfl⟩ : syracuseStep 5417171 = 8125757) B8125757
theorem B23161049 : Blo 1605001 23161049 := bstep (se 2 (by rfl) ⟨8685393, by rfl⟩ : syracuseStep 23161049 = 17370787) B17370787
theorem B24709373 : Blo 1605001 24709373 := bstep (se 3 (by rfl) ⟨4633007, by rfl⟩ : syracuseStep 24709373 = 9266015) B9266015
theorem B15862027 : Blo 1605001 15862027 := bstep (se 1 (by rfl) ⟨11896520, by rfl⟩ : syracuseStep 15862027 = 23793041) B23793041
theorem B3615137 : Blo 1605001 3615137 := bstep (se 2 (by rfl) ⟨1355676, by rfl⟩ : syracuseStep 3615137 = 2711353) B2711353
theorem B5417441 : Blo 1605001 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B3615263 : Blo 1605001 3615263 := bstep (se 1 (by rfl) ⟨2711447, by rfl⟩ : syracuseStep 3615263 = 5422895) B5422895
theorem B4573883 : Blo 1605001 4573883 := bstep (se 1 (by rfl) ⟨3430412, by rfl⟩ : syracuseStep 4573883 = 6860825) B6860825
theorem B6097751 : Blo 1605001 6097751 := bstep (se 1 (by rfl) ⟨4573313, by rfl⟩ : syracuseStep 6097751 = 9146627) B9146627
theorem B18287693 : Blo 1605001 18287693 := bstep (se 3 (by rfl) ⟨3428942, by rfl⟩ : syracuseStep 18287693 = 6857885) B6857885
theorem B4574407 : Blo 1605001 4574407 := bstep (se 1 (by rfl) ⟨3430805, by rfl⟩ : syracuseStep 4574407 = 6861611) B6861611
theorem B10292467 : Blo 1605001 10292467 := bstep (se 1 (by rfl) ⟨7719350, by rfl⟩ : syracuseStep 10292467 = 15438701) B15438701
theorem B5786905 : Blo 1605001 5786905 := bstep (se 2 (by rfl) ⟨2170089, by rfl⟩ : syracuseStep 5786905 = 4340179) B4340179
theorem B1805647 : Blo 1605001 1805647 := bstep (se 1 (by rfl) ⟨1354235, by rfl⟩ : syracuseStep 1805647 = 2708471) B2708471
theorem B2608615 : Blo 1605001 2608615 := bstep (se 1 (by rfl) ⟨1956461, by rfl⟩ : syracuseStep 2608615 = 3912923) B3912923
theorem B4066807 : Blo 1605001 4066807 := bstep (se 1 (by rfl) ⟨3050105, by rfl⟩ : syracuseStep 4066807 = 6100211) B6100211
theorem B4886011 : Blo 1605001 4886011 := bstep (se 1 (by rfl) ⟨3664508, by rfl⟩ : syracuseStep 4886011 = 7329017) B7329017
theorem B2895535 : Blo 1605001 2895535 := bstep (se 1 (by rfl) ⟨2171651, by rfl⟩ : syracuseStep 2895535 = 4343303) B4343303
theorem B3092243 : Blo 1605001 3092243 := bstep (se 1 (by rfl) ⟨2319182, by rfl⟩ : syracuseStep 3092243 = 4638365) B4638365
theorem B5418791 : Blo 1605001 5418791 := bstep (se 1 (by rfl) ⟨4064093, by rfl⟩ : syracuseStep 5418791 = 8128187) B8128187
theorem B4067111 : Blo 1605001 4067111 := bstep (se 1 (by rfl) ⟨3050333, by rfl⟩ : syracuseStep 4067111 = 6100667) B6100667
theorem B1806151 : Blo 1605001 1806151 := bstep (se 1 (by rfl) ⟨1354613, by rfl⟩ : syracuseStep 1806151 = 2709227) B2709227
theorem B20852687 : Blo 1605001 20852687 := bstep (se 1 (by rfl) ⟨15639515, by rfl⟩ : syracuseStep 20852687 = 31279031) B31279031
theorem B2895839 : Blo 1605001 2895839 := bstep (se 1 (by rfl) ⟨2171879, by rfl⟩ : syracuseStep 2895839 = 4343759) B4343759
theorem B10990025 : Blo 1605001 10990025 := bstep (se 2 (by rfl) ⟨4121259, by rfl⟩ : syracuseStep 10990025 = 8242519) B8242519
theorem B1806799 : Blo 1605001 1806799 := bstep (se 1 (by rfl) ⟨1355099, by rfl⟩ : syracuseStep 1806799 = 2710199) B2710199
theorem B4231961 : Blo 1605001 4231961 := bstep (se 2 (by rfl) ⟨1586985, by rfl⟩ : syracuseStep 4231961 = 3173971) B3173971
theorem B5419817 : Blo 1605001 5419817 := bstep (se 2 (by rfl) ⟨2032431, by rfl⟩ : syracuseStep 5419817 = 4064863) B4064863
theorem B4952873 : Blo 1605001 4952873 := bstep (se 2 (by rfl) ⟨1857327, by rfl⟩ : syracuseStep 4952873 = 3714655) B3714655
theorem B2061167 : Blo 1605001 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B3429371 : Blo 1605001 3429371 := bstep (se 1 (by rfl) ⟨2572028, by rfl⟩ : syracuseStep 3429371 = 5144057) B5144057
theorem B9147401 : Blo 1605001 9147401 := bstep (se 2 (by rfl) ⟨3430275, by rfl⟩ : syracuseStep 9147401 = 6860551) B6860551
theorem B18297899 : Blo 1605001 18297899 := bstep (se 1 (by rfl) ⟨13723424, by rfl⟩ : syracuseStep 18297899 = 27446849) B27446849
theorem B5420087 : Blo 1605001 5420087 := bstep (se 1 (by rfl) ⟨4065065, by rfl⟩ : syracuseStep 5420087 = 8130131) B8130131
theorem B10433609 : Blo 1605001 10433609 := bstep (se 2 (by rfl) ⟨3912603, by rfl⟩ : syracuseStep 10433609 = 7825207) B7825207
theorem B10294415 : Blo 1605001 10294415 := bstep (se 1 (by rfl) ⟨7720811, by rfl⟩ : syracuseStep 10294415 = 15441623) B15441623
theorem B2708687 : Blo 1605001 2708687 := bstep (se 1 (by rfl) ⟨2031515, by rfl⟩ : syracuseStep 2708687 = 4063031) B4063031
theorem B30872785 : Blo 1605001 30872785 := bstep (se 2 (by rfl) ⟨11577294, by rfl⟩ : syracuseStep 30872785 = 23154589) B23154589
theorem B33404147 : Blo 1605001 33404147 := bstep (se 1 (by rfl) ⟨25053110, by rfl⟩ : syracuseStep 33404147 = 50106221) B50106221
theorem B1807771 : Blo 1605001 1807771 := bstep (se 1 (by rfl) ⟨1355828, by rfl⟩ : syracuseStep 1807771 = 2711657) B2711657
theorem B34748149 : Blo 1605001 34748149 := bstep (se 5 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 34748149 = 3257639) B3257639
theorem B15439855 : Blo 1605001 15439855 := bstep (se 1 (by rfl) ⟨11579891, by rfl⟩ : syracuseStep 15439855 = 23159783) B23159783
theorem B2709497 : Blo 1605001 2709497 := bstep (se 2 (by rfl) ⟨1016061, by rfl⟩ : syracuseStep 2709497 = 2032123) B2032123
theorem B4233313 : Blo 1605001 4233313 := bstep (se 2 (by rfl) ⟨1587492, by rfl⟩ : syracuseStep 4233313 = 3174985) B3174985
theorem B2709659 : Blo 1605001 2709659 := bstep (se 1 (by rfl) ⟨2032244, by rfl⟩ : syracuseStep 2709659 = 4064489) B4064489
theorem B10426529 : Blo 1605001 10426529 := bstep (se 2 (by rfl) ⟨3909948, by rfl⟩ : syracuseStep 10426529 = 7819897) B7819897
theorem B6101153 : Blo 1605001 6101153 := bstep (se 2 (by rfl) ⟨2287932, by rfl⟩ : syracuseStep 6101153 = 4575865) B4575865
theorem B14088377 : Blo 1605001 14088377 := bstep (se 2 (by rfl) ⟨5283141, by rfl⟩ : syracuseStep 14088377 = 10566283) B10566283
theorem B1956031 : Blo 1605001 1956031 := bstep (se 1 (by rfl) ⟨1467023, by rfl⟩ : syracuseStep 1956031 = 2934047) B2934047
theorem B4634857 : Blo 1605001 4634857 := bstep (se 2 (by rfl) ⟨1738071, by rfl⟩ : syracuseStep 4634857 = 3476143) B3476143
theorem B2709767 : Blo 1605001 2709767 := bstep (se 1 (by rfl) ⟨2032325, by rfl⟩ : syracuseStep 2709767 = 4064651) B4064651
theorem B17840513 : Blo 1605001 17840513 := bstep (se 2 (by rfl) ⟨6690192, by rfl⟩ : syracuseStep 17840513 = 13380385) B13380385
theorem B10984025 : Blo 1605001 10984025 := bstep (se 2 (by rfl) ⟨4119009, by rfl⟩ : syracuseStep 10984025 = 8238019) B8238019
theorem B8133209 : Blo 1605001 8133209 := bstep (se 2 (by rfl) ⟨3049953, by rfl⟩ : syracuseStep 8133209 = 6099907) B6099907
theorem B2710327 : Blo 1605001 2710327 := bstep (se 1 (by rfl) ⟨2032745, by rfl⟩ : syracuseStep 2710327 = 4065491) B4065491
theorem B316750661 : Blo 1605001 316750661 := bstep (se 4 (by rfl) ⟨29695374, by rfl⟩ : syracuseStep 316750661 = 59390749) B59390749
theorem B3611483 : Blo 1605001 3611483 := bstep (se 1 (by rfl) ⟨2708612, by rfl⟩ : syracuseStep 3611483 = 5417225) B5417225
theorem B4397915 : Blo 1605001 4397915 := bstep (se 1 (by rfl) ⟨3298436, by rfl⟩ : syracuseStep 4397915 = 6596873) B6596873
theorem B5864351 : Blo 1605001 5864351 := bstep (se 1 (by rfl) ⟨4398263, by rfl⟩ : syracuseStep 5864351 = 8796527) B8796527
theorem B5422031 : Blo 1605001 5422031 := bstep (se 1 (by rfl) ⟨4066523, by rfl⟩ : syracuseStep 5422031 = 8133047) B8133047
theorem B4881377 : Blo 1605001 4881377 := bstep (se 2 (by rfl) ⟨1830516, by rfl⟩ : syracuseStep 4881377 = 3661033) B3661033
theorem B20585501 : Blo 1605001 20585501 := bstep (se 3 (by rfl) ⟨3859781, by rfl⟩ : syracuseStep 20585501 = 7719563) B7719563
theorem B13720691 : Blo 1605001 13720691 := bstep (se 1 (by rfl) ⟨10290518, by rfl⟩ : syracuseStep 13720691 = 20581037) B20581037
theorem B7715969 : Blo 1605001 7715969 := bstep (se 2 (by rfl) ⟨2893488, by rfl⟩ : syracuseStep 7715969 = 5786977) B5786977
theorem B2407607 : Blo 1605001 2407607 := bstep (se 1 (by rfl) ⟨1805705, by rfl⟩ : syracuseStep 2407607 = 3611411) B3611411
theorem B2710793 : Blo 1605001 2710793 := bstep (se 2 (by rfl) ⟨1016547, by rfl⟩ : syracuseStep 2710793 = 2033095) B2033095
theorem B3857831 : Blo 1605001 3857831 := bstep (se 1 (by rfl) ⟨2893373, by rfl⟩ : syracuseStep 3857831 = 5786747) B5786747
theorem B2407847 : Blo 1605001 2407847 := bstep (se 1 (by rfl) ⟨1805885, by rfl⟩ : syracuseStep 2407847 = 3611771) B3611771
theorem B1605095 : Blo 1605001 1605095 := bstep (se 1 (by rfl) ⟨1203821, by rfl⟩ : syracuseStep 1605095 = 2407643) B2407643
theorem B2407931 : Blo 1605001 2407931 := bstep (se 1 (by rfl) ⟨1805948, by rfl⟩ : syracuseStep 2407931 = 3611897) B3611897
theorem B37092887 : Blo 1605001 37092887 := bstep (se 1 (by rfl) ⟨27819665, by rfl⟩ : syracuseStep 37092887 = 55639331) B55639331
theorem B3612239 : Blo 1605001 3612239 := bstep (se 1 (by rfl) ⟨2709179, by rfl⟩ : syracuseStep 3612239 = 5418359) B5418359
theorem B1605211 : Blo 1605001 1605211 := bstep (se 1 (by rfl) ⟨1203908, by rfl⟩ : syracuseStep 1605211 = 2407817) B2407817
theorem B2408027 : Blo 1605001 2408027 := bstep (se 1 (by rfl) ⟨1806020, by rfl⟩ : syracuseStep 2408027 = 3612041) B3612041
theorem B2408111 : Blo 1605001 2408111 := bstep (se 1 (by rfl) ⟨1806083, by rfl⟩ : syracuseStep 2408111 = 3612167) B3612167
theorem B6094561 : Blo 1605001 6094561 := bstep (se 2 (by rfl) ⟨2285460, by rfl⟩ : syracuseStep 6094561 = 4570921) B4570921
theorem B2408231 : Blo 1605001 2408231 := bstep (se 1 (by rfl) ⟨1806173, by rfl⟩ : syracuseStep 2408231 = 3612347) B3612347
theorem B1605447 : Blo 1605001 1605447 := bstep (se 1 (by rfl) ⟨1204085, by rfl⟩ : syracuseStep 1605447 = 2408171) B2408171
theorem B2408315 : Blo 1605001 2408315 := bstep (se 1 (by rfl) ⟨1806236, by rfl⟩ : syracuseStep 2408315 = 3612473) B3612473
theorem B1605599 : Blo 1605001 1605599 := bstep (se 1 (by rfl) ⟨1204199, by rfl⟩ : syracuseStep 1605599 = 2408399) B2408399
theorem B5644417 : Blo 1605001 5644417 := bstep (se 2 (by rfl) ⟨2116656, by rfl⟩ : syracuseStep 5644417 = 4233313) B4233313
theorem B6095033 : Blo 1605001 6095033 := bstep (se 2 (by rfl) ⟨2285637, by rfl⟩ : syracuseStep 6095033 = 4571275) B4571275
theorem B3047615 : Blo 1605001 3047615 := bstep (se 1 (by rfl) ⟨2285711, by rfl⟩ : syracuseStep 3047615 = 4571423) B4571423
theorem B2408639 : Blo 1605001 2408639 := bstep (se 1 (by rfl) ⟨1806479, by rfl⟩ : syracuseStep 2408639 = 3612959) B3612959
theorem B1605823 : Blo 1605001 1605823 := bstep (se 1 (by rfl) ⟨1204367, by rfl⟩ : syracuseStep 1605823 = 2408735) B2408735
theorem B1605839 : Blo 1605001 1605839 := bstep (se 1 (by rfl) ⟨1204379, by rfl⟩ : syracuseStep 1605839 = 2408759) B2408759
theorem B1605887 : Blo 1605001 1605887 := bstep (se 1 (by rfl) ⟨1204415, by rfl⟩ : syracuseStep 1605887 = 2408831) B2408831
theorem B1605935 : Blo 1605001 1605935 := bstep (se 1 (by rfl) ⟨1204451, by rfl⟩ : syracuseStep 1605935 = 2408903) B2408903
theorem B4571549 : Blo 1605001 4571549 := bstep (se 3 (by rfl) ⟨857165, by rfl⟩ : syracuseStep 4571549 = 1714331) B1714331
theorem B8126891 : Blo 1605001 8126891 := bstep (se 1 (by rfl) ⟨6095168, by rfl⟩ : syracuseStep 8126891 = 12190337) B12190337
theorem B37569005 : Blo 1605001 37569005 := bstep (se 3 (by rfl) ⟨7044188, by rfl⟩ : syracuseStep 37569005 = 14088377) B14088377
theorem B3613211 : Blo 1605001 3613211 := bstep (se 1 (by rfl) ⟨2709908, by rfl⟩ : syracuseStep 3613211 = 5419817) B5419817
theorem B1606171 : Blo 1605001 1606171 := bstep (se 1 (by rfl) ⟨1204628, by rfl⟩ : syracuseStep 1606171 = 2409257) B2409257
theorem B3301915 : Blo 1605001 3301915 := bstep (se 1 (by rfl) ⟨2476436, by rfl⟩ : syracuseStep 3301915 = 4952873) B4952873
theorem B1606175 : Blo 1605001 1606175 := bstep (se 1 (by rfl) ⟨1204631, by rfl⟩ : syracuseStep 1606175 = 2409263) B2409263
theorem B2409065 : Blo 1605001 2409065 := bstep (se 2 (by rfl) ⟨903399, by rfl⟩ : syracuseStep 2409065 = 1806799) B1806799
theorem B2409071 : Blo 1605001 2409071 := bstep (se 1 (by rfl) ⟨1806803, by rfl⟩ : syracuseStep 2409071 = 3613607) B3613607
theorem B1606255 : Blo 1605001 1606255 := bstep (se 1 (by rfl) ⟨1204691, by rfl⟩ : syracuseStep 1606255 = 2409383) B2409383
theorem B2286247 : Blo 1605001 2286247 := bstep (se 1 (by rfl) ⟨1714685, by rfl⟩ : syracuseStep 2286247 = 3429371) B3429371
theorem B1606311 : Blo 1605001 1606311 := bstep (se 1 (by rfl) ⟨1204733, by rfl⟩ : syracuseStep 1606311 = 2409467) B2409467
theorem B12198599 : Blo 1605001 12198599 := bstep (se 1 (by rfl) ⟨9148949, by rfl⟩ : syracuseStep 12198599 = 18297899) B18297899
theorem B3613391 : Blo 1605001 3613391 := bstep (se 1 (by rfl) ⟨2710043, by rfl⟩ : syracuseStep 3613391 = 5420087) B5420087
theorem B1606351 : Blo 1605001 1606351 := bstep (se 1 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 1606351 = 2409527) B2409527
theorem B6955739 : Blo 1605001 6955739 := bstep (se 1 (by rfl) ⟨5216804, by rfl⟩ : syracuseStep 6955739 = 10433609) B10433609
theorem B1606431 : Blo 1605001 1606431 := bstep (se 1 (by rfl) ⟨1204823, by rfl⟩ : syracuseStep 1606431 = 2409647) B2409647
theorem B1606703 : Blo 1605001 1606703 := bstep (se 1 (by rfl) ⟨1205027, by rfl⟩ : syracuseStep 1606703 = 2410055) B2410055
theorem B3048511 : Blo 1605001 3048511 := bstep (se 1 (by rfl) ⟨2286383, by rfl⟩ : syracuseStep 3048511 = 4572767) B4572767
theorem B3613769 : Blo 1605001 3613769 := bstep (se 2 (by rfl) ⟨1355163, by rfl⟩ : syracuseStep 3613769 = 2710327) B2710327
theorem B1606767 : Blo 1605001 1606767 := bstep (se 1 (by rfl) ⟨1205075, by rfl⟩ : syracuseStep 1606767 = 2410151) B2410151
theorem B79193213 : Blo 1605001 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B1606823 : Blo 1605001 1606823 := bstep (se 1 (by rfl) ⟨1205117, by rfl⟩ : syracuseStep 1606823 = 2410235) B2410235
theorem B1606847 : Blo 1605001 1606847 := bstep (se 1 (by rfl) ⟨1205135, by rfl⟩ : syracuseStep 1606847 = 2410271) B2410271
theorem B4572379 : Blo 1605001 4572379 := bstep (se 1 (by rfl) ⟨3429284, by rfl⟩ : syracuseStep 4572379 = 6858569) B6858569
theorem B3048671 : Blo 1605001 3048671 := bstep (se 1 (by rfl) ⟨2286503, by rfl⟩ : syracuseStep 3048671 = 4573007) B4573007
theorem B2409695 : Blo 1605001 2409695 := bstep (se 1 (by rfl) ⟨1807271, by rfl⟩ : syracuseStep 2409695 = 3614543) B3614543
theorem B1606879 : Blo 1605001 1606879 := bstep (se 1 (by rfl) ⟨1205159, by rfl⟩ : syracuseStep 1606879 = 2410319) B2410319
theorem B2409707 : Blo 1605001 2409707 := bstep (se 1 (by rfl) ⟨1807280, by rfl⟩ : syracuseStep 2409707 = 3614561) B3614561
theorem B1606959 : Blo 1605001 1606959 := bstep (se 1 (by rfl) ⟨1205219, by rfl⟩ : syracuseStep 1606959 = 2410439) B2410439
theorem B2410091 : Blo 1605001 2410091 := bstep (se 1 (by rfl) ⟨1807568, by rfl⟩ : syracuseStep 2410091 = 3615137) B3615137
theorem B13723289 : Blo 1605001 13723289 := bstep (se 2 (by rfl) ⟨5146233, by rfl⟩ : syracuseStep 13723289 = 10292467) B10292467
theorem B2410175 : Blo 1605001 2410175 := bstep (se 1 (by rfl) ⟨1807631, by rfl⟩ : syracuseStep 2410175 = 3615263) B3615263
theorem B3049255 : Blo 1605001 3049255 := bstep (se 1 (by rfl) ⟨2286941, by rfl⟩ : syracuseStep 3049255 = 4573883) B4573883
theorem B2410361 : Blo 1605001 2410361 := bstep (se 2 (by rfl) ⟨903885, by rfl⟩ : syracuseStep 2410361 = 1807771) B1807771
theorem B211167107 : Blo 1605001 211167107 := bstep (se 1 (by rfl) ⟨158375330, by rfl⟩ : syracuseStep 211167107 = 316750661) B316750661
theorem B4065167 : Blo 1605001 4065167 := bstep (se 1 (by rfl) ⟨3048875, by rfl⟩ : syracuseStep 4065167 = 6097751) B6097751
theorem B3614687 : Blo 1605001 3614687 := bstep (se 1 (by rfl) ⟨2711015, by rfl⟩ : syracuseStep 3614687 = 5422031) B5422031
theorem B3254251 : Blo 1605001 3254251 := bstep (se 1 (by rfl) ⟨2440688, by rfl⟩ : syracuseStep 3254251 = 4881377) B4881377
theorem B6514681 : Blo 1605001 6514681 := bstep (se 2 (by rfl) ⟨2443005, by rfl⟩ : syracuseStep 6514681 = 4886011) B4886011
theorem B13723667 : Blo 1605001 13723667 := bstep (se 1 (by rfl) ⟨10292750, by rfl⟩ : syracuseStep 13723667 = 20585501) B20585501
theorem B12191795 : Blo 1605001 12191795 := bstep (se 1 (by rfl) ⟨9143846, by rfl⟩ : syracuseStep 12191795 = 18287693) B18287693
theorem B3860713 : Blo 1605001 3860713 := bstep (se 2 (by rfl) ⟨1447767, by rfl⟩ : syracuseStep 3860713 = 2895535) B2895535
theorem B9145169 : Blo 1605001 9145169 := bstep (se 2 (by rfl) ⟨3429438, by rfl⟩ : syracuseStep 9145169 = 6858877) B6858877
theorem B3615695 : Blo 1605001 3615695 := bstep (se 1 (by rfl) ⟨2711771, by rfl⟩ : syracuseStep 3615695 = 5423543) B5423543
theorem B7326683 : Blo 1605001 7326683 := bstep (se 1 (by rfl) ⟨5495012, by rfl⟩ : syracuseStep 7326683 = 10990025) B10990025
theorem B6179809 : Blo 1605001 6179809 := bstep (se 2 (by rfl) ⟨2317428, by rfl⟩ : syracuseStep 6179809 = 4634857) B4634857
theorem B49458151 : Blo 1605001 49458151 := bstep (se 1 (by rfl) ⟨37093613, by rfl⟩ : syracuseStep 49458151 = 74187227) B74187227
theorem B2821307 : Blo 1605001 2821307 := bstep (se 1 (by rfl) ⟨2115980, by rfl⟩ : syracuseStep 2821307 = 4231961) B4231961
theorem B6098267 : Blo 1605001 6098267 := bstep (se 1 (by rfl) ⟨4573700, by rfl⟩ : syracuseStep 6098267 = 9147401) B9147401
theorem B1805791 : Blo 1605001 1805791 := bstep (se 1 (by rfl) ⟨1354343, by rfl⟩ : syracuseStep 1805791 = 2708687) B2708687
theorem B22269431 : Blo 1605001 22269431 := bstep (se 1 (by rfl) ⟨16702073, by rfl⟩ : syracuseStep 22269431 = 33404147) B33404147
theorem B10432165 : Blo 1605001 10432165 := bstep (se 4 (by rfl) ⟨978015, by rfl⟩ : syracuseStep 10432165 = 1956031) B1956031
theorem B47574701 : Blo 1605001 47574701 := bstep (se 3 (by rfl) ⟨8920256, by rfl⟩ : syracuseStep 47574701 = 17840513) B17840513
theorem B5418683 : Blo 1605001 5418683 := bstep (se 1 (by rfl) ⟨4064012, by rfl⟩ : syracuseStep 5418683 = 8128025) B8128025
theorem B6860483 : Blo 1605001 6860483 := bstep (se 1 (by rfl) ⟨5145362, by rfl⟩ : syracuseStep 6860483 = 10290725) B10290725
theorem B18542479 : Blo 1605001 18542479 := bstep (se 1 (by rfl) ⟨13906859, by rfl⟩ : syracuseStep 18542479 = 27813719) B27813719
theorem B1806331 : Blo 1605001 1806331 := bstep (se 1 (by rfl) ⟨1354748, by rfl⟩ : syracuseStep 1806331 = 2709497) B2709497
theorem B1806439 : Blo 1605001 1806439 := bstep (se 1 (by rfl) ⟨1354829, by rfl⟩ : syracuseStep 1806439 = 2709659) B2709659
theorem B6951019 : Blo 1605001 6951019 := bstep (se 1 (by rfl) ⟨5213264, by rfl⟩ : syracuseStep 6951019 = 10426529) B10426529
theorem B4067435 : Blo 1605001 4067435 := bstep (se 1 (by rfl) ⟨3050576, by rfl⟩ : syracuseStep 4067435 = 6101153) B6101153
theorem B1806511 : Blo 1605001 1806511 := bstep (se 1 (by rfl) ⟨1354883, by rfl⟩ : syracuseStep 1806511 = 2709767) B2709767
theorem B29290733 : Blo 1605001 29290733 := bstep (se 3 (by rfl) ⟨5492012, by rfl⟩ : syracuseStep 29290733 = 10984025) B10984025
theorem B6099209 : Blo 1605001 6099209 := bstep (se 2 (by rfl) ⟨2287203, by rfl⟩ : syracuseStep 6099209 = 4574407) B4574407
theorem B3478153 : Blo 1605001 3478153 := bstep (se 2 (by rfl) ⟨1304307, by rfl⟩ : syracuseStep 3478153 = 2608615) B2608615
theorem B8245981 : Blo 1605001 8245981 := bstep (se 3 (by rfl) ⟨1546121, by rfl⟩ : syracuseStep 8245981 = 3092243) B3092243
theorem B9147127 : Blo 1605001 9147127 := bstep (se 1 (by rfl) ⟨6860345, by rfl⟩ : syracuseStep 9147127 = 13720691) B13720691
theorem B1807195 : Blo 1605001 1807195 := bstep (se 1 (by rfl) ⟨1355396, by rfl⟩ : syracuseStep 1807195 = 2710793) B2710793
theorem B11727773 : Blo 1605001 11727773 := bstep (se 3 (by rfl) ⟨2198957, by rfl⟩ : syracuseStep 11727773 = 4397915) B4397915
theorem B46330865 : Blo 1605001 46330865 := bstep (se 2 (by rfl) ⟨17374074, by rfl⟩ : syracuseStep 46330865 = 34748149) B34748149
theorem B24728591 : Blo 1605001 24728591 := bstep (se 1 (by rfl) ⟨18546443, by rfl⟩ : syracuseStep 24728591 = 37092887) B37092887
theorem B1930559 : Blo 1605001 1930559 := bstep (se 1 (by rfl) ⟨1447919, by rfl⟩ : syracuseStep 1930559 = 2895839) B2895839
theorem B6100379 : Blo 1605001 6100379 := bstep (se 1 (by rfl) ⟨4575284, by rfl⟩ : syracuseStep 6100379 = 9150569) B9150569
theorem B21149369 : Blo 1605001 21149369 := bstep (se 2 (by rfl) ⟨7931013, by rfl⟩ : syracuseStep 21149369 = 15862027) B15862027
theorem B6952979 : Blo 1605001 6952979 := bstep (se 1 (by rfl) ⟨5214734, by rfl⟩ : syracuseStep 6952979 = 10429469) B10429469
theorem B6862943 : Blo 1605001 6862943 := bstep (se 1 (by rfl) ⟨5147207, by rfl⟩ : syracuseStep 6862943 = 10294415) B10294415
theorem B10296031 : Blo 1605001 10296031 := bstep (se 1 (by rfl) ⟨7722023, by rfl⟩ : syracuseStep 10296031 = 15444047) B15444047
theorem B3611447 : Blo 1605001 3611447 := bstep (se 1 (by rfl) ⟨2708585, by rfl⟩ : syracuseStep 3611447 = 5417171) B5417171
theorem B15440699 : Blo 1605001 15440699 := bstep (se 1 (by rfl) ⟨11580524, by rfl⟩ : syracuseStep 15440699 = 23161049) B23161049
theorem B16472915 : Blo 1605001 16472915 := bstep (se 1 (by rfl) ⟨12354686, by rfl⟩ : syracuseStep 16472915 = 24709373) B24709373
theorem B41163713 : Blo 1605001 41163713 := bstep (se 2 (by rfl) ⟨15436392, by rfl⟩ : syracuseStep 41163713 = 30872785) B30872785
theorem B3611627 : Blo 1605001 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B7715873 : Blo 1605001 7715873 := bstep (se 2 (by rfl) ⟨2893452, by rfl⟩ : syracuseStep 7715873 = 5786905) B5786905
theorem B5422139 : Blo 1605001 5422139 := bstep (se 1 (by rfl) ⟨4066604, by rfl⟩ : syracuseStep 5422139 = 8133209) B8133209
theorem B2407529 : Blo 1605001 2407529 := bstep (se 2 (by rfl) ⟨902823, by rfl⟩ : syracuseStep 2407529 = 1805647) B1805647
theorem B2407655 : Blo 1605001 2407655 := bstep (se 1 (by rfl) ⟨1805741, by rfl⟩ : syracuseStep 2407655 = 3611483) B3611483
theorem B5422409 : Blo 1605001 5422409 := bstep (se 2 (by rfl) ⟨2033403, by rfl⟩ : syracuseStep 5422409 = 4066807) B4066807
theorem B5143979 : Blo 1605001 5143979 := bstep (se 1 (by rfl) ⟨3857984, by rfl⟩ : syracuseStep 5143979 = 7715969) B7715969
theorem B1605071 : Blo 1605001 1605071 := bstep (se 1 (by rfl) ⟨1203803, by rfl⟩ : syracuseStep 1605071 = 2407607) B2407607
theorem B1605231 : Blo 1605001 1605231 := bstep (se 1 (by rfl) ⟨1203923, by rfl⟩ : syracuseStep 1605231 = 2407847) B2407847
theorem B2571887 : Blo 1605001 2571887 := bstep (se 1 (by rfl) ⟨1928915, by rfl⟩ : syracuseStep 2571887 = 3857831) B3857831
theorem B5496445 : Blo 1605001 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B8126081 : Blo 1605001 8126081 := bstep (se 2 (by rfl) ⟨3047280, by rfl⟩ : syracuseStep 8126081 = 6094561) B6094561
theorem B1605287 : Blo 1605001 1605287 := bstep (se 1 (by rfl) ⟨1203965, by rfl⟩ : syracuseStep 1605287 = 2407931) B2407931
theorem B2408159 : Blo 1605001 2408159 := bstep (se 1 (by rfl) ⟨1806119, by rfl⟩ : syracuseStep 2408159 = 3612239) B3612239
theorem B1605351 : Blo 1605001 1605351 := bstep (se 1 (by rfl) ⟨1204013, by rfl⟩ : syracuseStep 1605351 = 2408027) B2408027
theorem B15638269 : Blo 1605001 15638269 := bstep (se 3 (by rfl) ⟨2932175, by rfl⟩ : syracuseStep 15638269 = 5864351) B5864351
theorem B2408201 : Blo 1605001 2408201 := bstep (se 2 (by rfl) ⟨903075, by rfl⟩ : syracuseStep 2408201 = 1806151) B1806151
theorem B1605407 : Blo 1605001 1605407 := bstep (se 1 (by rfl) ⟨1204055, by rfl⟩ : syracuseStep 1605407 = 2408111) B2408111
theorem B1605487 : Blo 1605001 1605487 := bstep (se 1 (by rfl) ⟨1204115, by rfl⟩ : syracuseStep 1605487 = 2408231) B2408231
theorem B3612527 : Blo 1605001 3612527 := bstep (se 1 (by rfl) ⟨2709395, by rfl⟩ : syracuseStep 3612527 = 5418791) B5418791
theorem B2711407 : Blo 1605001 2711407 := bstep (se 1 (by rfl) ⟨2033555, by rfl⟩ : syracuseStep 2711407 = 4067111) B4067111
theorem B1605543 : Blo 1605001 1605543 := bstep (se 1 (by rfl) ⟨1204157, by rfl⟩ : syracuseStep 1605543 = 2408315) B2408315
theorem B13901791 : Blo 1605001 13901791 := bstep (se 1 (by rfl) ⟨10426343, by rfl⟩ : syracuseStep 13901791 = 20852687) B20852687
theorem B20586473 : Blo 1605001 20586473 := bstep (se 2 (by rfl) ⟨7719927, by rfl⟩ : syracuseStep 20586473 = 15439855) B15439855
theorem B2711623 : Blo 1605001 2711623 := bstep (se 1 (by rfl) ⟨2033717, by rfl⟩ : syracuseStep 2711623 = 4067435) B4067435
theorem B4063355 : Blo 1605001 4063355 := bstep (se 1 (by rfl) ⟨3047516, by rfl⟩ : syracuseStep 4063355 = 6095033) B6095033
theorem B2031743 : Blo 1605001 2031743 := bstep (se 1 (by rfl) ⟨1523807, by rfl⟩ : syracuseStep 2031743 = 3047615) B3047615
theorem B1605759 : Blo 1605001 1605759 := bstep (se 1 (by rfl) ⟨1204319, by rfl⟩ : syracuseStep 1605759 = 2408639) B2408639
theorem B2408585 : Blo 1605001 2408585 := bstep (se 2 (by rfl) ⟨903219, by rfl⟩ : syracuseStep 2408585 = 1806439) B1806439
theorem B2408681 : Blo 1605001 2408681 := bstep (se 2 (by rfl) ⟨903255, by rfl⟩ : syracuseStep 2408681 = 1806511) B1806511
theorem B3047699 : Blo 1605001 3047699 := bstep (se 1 (by rfl) ⟨2285774, by rfl⟩ : syracuseStep 3047699 = 4571549) B4571549
theorem B2408807 : Blo 1605001 2408807 := bstep (se 1 (by rfl) ⟨1806605, by rfl⟩ : syracuseStep 2408807 = 3613211) B3613211
theorem B1606043 : Blo 1605001 1606043 := bstep (se 1 (by rfl) ⟨1204532, by rfl⟩ : syracuseStep 1606043 = 2409065) B2409065
theorem B1606047 : Blo 1605001 1606047 := bstep (se 1 (by rfl) ⟨1204535, by rfl⟩ : syracuseStep 1606047 = 2409071) B2409071
theorem B2408927 : Blo 1605001 2408927 := bstep (se 1 (by rfl) ⟨1806695, by rfl⟩ : syracuseStep 2408927 = 3613391) B3613391
theorem B4637159 : Blo 1605001 4637159 := bstep (se 1 (by rfl) ⟨3477869, by rfl⟩ : syracuseStep 4637159 = 6955739) B6955739
theorem B2409179 : Blo 1605001 2409179 := bstep (se 1 (by rfl) ⟨1806884, by rfl⟩ : syracuseStep 2409179 = 3613769) B3613769
theorem B2032447 : Blo 1605001 2032447 := bstep (se 1 (by rfl) ⟨1524335, by rfl⟩ : syracuseStep 2032447 = 3048671) B3048671
theorem B1606463 : Blo 1605001 1606463 := bstep (se 1 (by rfl) ⟨1204847, by rfl⟩ : syracuseStep 1606463 = 2409695) B2409695
theorem B1606471 : Blo 1605001 1606471 := bstep (se 1 (by rfl) ⟨1204853, by rfl⟩ : syracuseStep 1606471 = 2409707) B2409707
theorem B4637537 : Blo 1605001 4637537 := bstep (se 2 (by rfl) ⟨1739076, by rfl⟩ : syracuseStep 4637537 = 3478153) B3478153
theorem B3048329 : Blo 1605001 3048329 := bstep (se 2 (by rfl) ⟨1143123, by rfl⟩ : syracuseStep 3048329 = 2286247) B2286247
theorem B1606727 : Blo 1605001 1606727 := bstep (se 1 (by rfl) ⟨1205045, by rfl⟩ : syracuseStep 1606727 = 2410091) B2410091
theorem B2409593 : Blo 1605001 2409593 := bstep (se 2 (by rfl) ⟨903597, by rfl⟩ : syracuseStep 2409593 = 1807195) B1807195
theorem B14099579 : Blo 1605001 14099579 := bstep (se 1 (by rfl) ⟨10574684, by rfl⟩ : syracuseStep 14099579 = 21149369) B21149369
theorem B1606783 : Blo 1605001 1606783 := bstep (se 1 (by rfl) ⟨1205087, by rfl⟩ : syracuseStep 1606783 = 2410175) B2410175
theorem B1606907 : Blo 1605001 1606907 := bstep (se 1 (by rfl) ⟨1205180, by rfl⟩ : syracuseStep 1606907 = 2410361) B2410361
theorem B2409791 : Blo 1605001 2409791 := bstep (se 1 (by rfl) ⟨1807343, by rfl⟩ : syracuseStep 2409791 = 3614687) B3614687
theorem B8127863 : Blo 1605001 8127863 := bstep (se 1 (by rfl) ⟨6095897, by rfl⟩ : syracuseStep 8127863 = 12191795) B12191795
theorem B4064681 : Blo 1605001 4064681 := bstep (se 2 (by rfl) ⟨1524255, by rfl⟩ : syracuseStep 4064681 = 3048511) B3048511
theorem B6096505 : Blo 1605001 6096505 := bstep (se 2 (by rfl) ⟨2286189, by rfl⟩ : syracuseStep 6096505 = 4572379) B4572379
theorem B6096779 : Blo 1605001 6096779 := bstep (se 1 (by rfl) ⟨4572584, by rfl⟩ : syracuseStep 6096779 = 9145169) B9145169
theorem B2410463 : Blo 1605001 2410463 := bstep (se 1 (by rfl) ⟨1807847, by rfl⟩ : syracuseStep 2410463 = 3615695) B3615695
theorem B4884455 : Blo 1605001 4884455 := bstep (se 1 (by rfl) ⟨3663341, by rfl⟩ : syracuseStep 4884455 = 7326683) B7326683
theorem B3614759 : Blo 1605001 3614759 := bstep (se 1 (by rfl) ⟨2711069, by rfl⟩ : syracuseStep 3614759 = 5422139) B5422139
theorem B3614939 : Blo 1605001 3614939 := bstep (se 1 (by rfl) ⟨2711204, by rfl⟩ : syracuseStep 3614939 = 5422409) B5422409
theorem B4065511 : Blo 1605001 4065511 := bstep (se 1 (by rfl) ⟨3049133, by rfl⟩ : syracuseStep 4065511 = 6098267) B6098267
theorem B14846287 : Blo 1605001 14846287 := bstep (se 1 (by rfl) ⟨11134715, by rfl⟩ : syracuseStep 14846287 = 22269431) B22269431
theorem B20851025 : Blo 1605001 20851025 := bstep (se 2 (by rfl) ⟨7819134, by rfl⟩ : syracuseStep 20851025 = 15638269) B15638269
theorem B4065673 : Blo 1605001 4065673 := bstep (se 2 (by rfl) ⟨1524627, by rfl⟩ : syracuseStep 4065673 = 3049255) B3049255
theorem B1714591 : Blo 1605001 1714591 := bstep (se 1 (by rfl) ⟨1285943, by rfl⟩ : syracuseStep 1714591 = 2571887) B2571887
theorem B5417387 : Blo 1605001 5417387 := bstep (se 1 (by rfl) ⟨4063040, by rfl⟩ : syracuseStep 5417387 = 8126081) B8126081
theorem B4573655 : Blo 1605001 4573655 := bstep (se 1 (by rfl) ⟨3430241, by rfl⟩ : syracuseStep 4573655 = 6860483) B6860483
theorem B3615209 : Blo 1605001 3615209 := bstep (se 2 (by rfl) ⟨1355703, by rfl⟩ : syracuseStep 3615209 = 2711407) B2711407
theorem B13724315 : Blo 1605001 13724315 := bstep (se 1 (by rfl) ⟨10293236, by rfl⟩ : syracuseStep 13724315 = 20586473) B20586473
theorem B8686241 : Blo 1605001 8686241 := bstep (se 2 (by rfl) ⟨3257340, by rfl⟩ : syracuseStep 8686241 = 6514681) B6514681
theorem B9268025 : Blo 1605001 9268025 := bstep (se 2 (by rfl) ⟨3475509, by rfl⟩ : syracuseStep 9268025 = 6951019) B6951019
theorem B4066139 : Blo 1605001 4066139 := bstep (se 1 (by rfl) ⟨3049604, by rfl⟩ : syracuseStep 4066139 = 6099209) B6099209
theorem B5417927 : Blo 1605001 5417927 := bstep (se 1 (by rfl) ⟨4063445, by rfl⟩ : syracuseStep 5417927 = 8126891) B8126891
theorem B25046003 : Blo 1605001 25046003 := bstep (se 1 (by rfl) ⟨18784502, by rfl⟩ : syracuseStep 25046003 = 37569005) B37569005
theorem B7523485 : Blo 1605001 7523485 := bstep (se 3 (by rfl) ⟨1410653, by rfl⟩ : syracuseStep 7523485 = 2821307) B2821307
theorem B7818515 : Blo 1605001 7818515 := bstep (se 1 (by rfl) ⟨5863886, by rfl⟩ : syracuseStep 7818515 = 11727773) B11727773
theorem B30887243 : Blo 1605001 30887243 := bstep (se 1 (by rfl) ⟨23165432, by rfl⟩ : syracuseStep 30887243 = 46330865) B46330865
theorem B16485727 : Blo 1605001 16485727 := bstep (se 1 (by rfl) ⟨12364295, by rfl⟩ : syracuseStep 16485727 = 24728591) B24728591
theorem B4402553 : Blo 1605001 4402553 := bstep (se 2 (by rfl) ⟨1650957, by rfl⟩ : syracuseStep 4402553 = 3301915) B3301915
theorem B5148157 : Blo 1605001 5148157 := bstep (se 3 (by rfl) ⟨965279, by rfl⟩ : syracuseStep 5148157 = 1930559) B1930559
theorem B4066919 : Blo 1605001 4066919 := bstep (se 1 (by rfl) ⟨3050189, by rfl⟩ : syracuseStep 4066919 = 6100379) B6100379
theorem B43978565 : Blo 1605001 43978565 := bstep (se 4 (by rfl) ⟨4122990, by rfl⟩ : syracuseStep 43978565 = 8245981) B8245981
theorem B20590469 : Blo 1605001 20590469 := bstep (se 4 (by rfl) ⟨1930356, by rfl⟩ : syracuseStep 20590469 = 3860713) B3860713
theorem B4575295 : Blo 1605001 4575295 := bstep (se 1 (by rfl) ⟨3431471, by rfl⟩ : syracuseStep 4575295 = 6862943) B6862943
theorem B10293799 : Blo 1605001 10293799 := bstep (se 1 (by rfl) ⟨7720349, by rfl⟩ : syracuseStep 10293799 = 15440699) B15440699
theorem B10981943 : Blo 1605001 10981943 := bstep (se 1 (by rfl) ⟨8236457, by rfl⟩ : syracuseStep 10981943 = 16472915) B16472915
theorem B7328593 : Blo 1605001 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B3429319 : Blo 1605001 3429319 := bstep (se 1 (by rfl) ⟨2571989, by rfl⟩ : syracuseStep 3429319 = 5143979) B5143979
theorem B31716467 : Blo 1605001 31716467 := bstep (se 1 (by rfl) ⟨23787350, by rfl⟩ : syracuseStep 31716467 = 47574701) B47574701
theorem B18535721 : Blo 1605001 18535721 := bstep (se 2 (by rfl) ⟨6950895, by rfl⟩ : syracuseStep 18535721 = 13901791) B13901791
theorem B4339001 : Blo 1605001 4339001 := bstep (se 2 (by rfl) ⟨1627125, by rfl⟩ : syracuseStep 4339001 = 3254251) B3254251
theorem B19527155 : Blo 1605001 19527155 := bstep (se 1 (by rfl) ⟨14645366, by rfl⟩ : syracuseStep 19527155 = 29290733) B29290733
theorem B7525889 : Blo 1605001 7525889 := bstep (se 2 (by rfl) ⟨2822208, by rfl⟩ : syracuseStep 7525889 = 5644417) B5644417
theorem B8132399 : Blo 1605001 8132399 := bstep (se 1 (by rfl) ⟨6099299, by rfl⟩ : syracuseStep 8132399 = 12198599) B12198599
theorem B52795475 : Blo 1605001 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B13728041 : Blo 1605001 13728041 := bstep (se 2 (by rfl) ⟨5148015, by rfl⟩ : syracuseStep 13728041 = 10296031) B10296031
theorem B12196169 : Blo 1605001 12196169 := bstep (se 2 (by rfl) ⟨4573563, by rfl⟩ : syracuseStep 12196169 = 9147127) B9147127
theorem B9148859 : Blo 1605001 9148859 := bstep (se 1 (by rfl) ⟨6861644, by rfl⟩ : syracuseStep 9148859 = 13723289) B13723289
theorem B140778071 : Blo 1605001 140778071 := bstep (se 1 (by rfl) ⟨105583553, by rfl⟩ : syracuseStep 140778071 = 211167107) B211167107
theorem B2710111 : Blo 1605001 2710111 := bstep (se 1 (by rfl) ⟨2032583, by rfl⟩ : syracuseStep 2710111 = 4065167) B4065167
theorem B8239745 : Blo 1605001 8239745 := bstep (se 2 (by rfl) ⟨3089904, by rfl⟩ : syracuseStep 8239745 = 6179809) B6179809
theorem B65944201 : Blo 1605001 65944201 := bstep (se 2 (by rfl) ⟨24729075, by rfl⟩ : syracuseStep 65944201 = 49458151) B49458151
theorem B4635319 : Blo 1605001 4635319 := bstep (se 1 (by rfl) ⟨3476489, by rfl⟩ : syracuseStep 4635319 = 6952979) B6952979
theorem B9149111 : Blo 1605001 9149111 := bstep (se 1 (by rfl) ⟨6861833, by rfl⟩ : syracuseStep 9149111 = 13723667) B13723667
theorem B2407631 : Blo 1605001 2407631 := bstep (se 1 (by rfl) ⟨1805723, by rfl⟩ : syracuseStep 2407631 = 3611447) B3611447
theorem B2407721 : Blo 1605001 2407721 := bstep (se 2 (by rfl) ⟨902895, by rfl⟩ : syracuseStep 2407721 = 1805791) B1805791
theorem B27442475 : Blo 1605001 27442475 := bstep (se 1 (by rfl) ⟨20581856, by rfl⟩ : syracuseStep 27442475 = 41163713) B41163713
theorem B2407751 : Blo 1605001 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B5143915 : Blo 1605001 5143915 := bstep (se 1 (by rfl) ⟨3857936, by rfl⟩ : syracuseStep 5143915 = 7715873) B7715873
theorem B1605019 : Blo 1605001 1605019 := bstep (se 1 (by rfl) ⟨1203764, by rfl⟩ : syracuseStep 1605019 = 2407529) B2407529
theorem B1605103 : Blo 1605001 1605103 := bstep (se 1 (by rfl) ⟨1203827, by rfl⟩ : syracuseStep 1605103 = 2407655) B2407655
theorem B13909553 : Blo 1605001 13909553 := bstep (se 2 (by rfl) ⟨5216082, by rfl⟩ : syracuseStep 13909553 = 10432165) B10432165
theorem B3612455 : Blo 1605001 3612455 := bstep (se 1 (by rfl) ⟨2709341, by rfl⟩ : syracuseStep 3612455 = 5418683) B5418683
theorem B1605439 : Blo 1605001 1605439 := bstep (se 1 (by rfl) ⟨1204079, by rfl⟩ : syracuseStep 1605439 = 2408159) B2408159
theorem B1605467 : Blo 1605001 1605467 := bstep (se 1 (by rfl) ⟨1204100, by rfl⟩ : syracuseStep 1605467 = 2408201) B2408201
theorem B24723305 : Blo 1605001 24723305 := bstep (se 2 (by rfl) ⟨9271239, by rfl⟩ : syracuseStep 24723305 = 18542479) B18542479
theorem B2408351 : Blo 1605001 2408351 := bstep (se 1 (by rfl) ⟨1806263, by rfl⟩ : syracuseStep 2408351 = 3612527) B3612527
theorem B2408441 : Blo 1605001 2408441 := bstep (se 2 (by rfl) ⟨903165, by rfl⟩ : syracuseStep 2408441 = 1806331) B1806331
theorem B1605723 : Blo 1605001 1605723 := bstep (se 1 (by rfl) ⟨1204292, by rfl⟩ : syracuseStep 1605723 = 2408585) B2408585
theorem B1605787 : Blo 1605001 1605787 := bstep (se 1 (by rfl) ⟨1204340, by rfl⟩ : syracuseStep 1605787 = 2408681) B2408681
theorem B2031799 : Blo 1605001 2031799 := bstep (se 1 (by rfl) ⟨1523849, by rfl⟩ : syracuseStep 2031799 = 3047699) B3047699
theorem B1605871 : Blo 1605001 1605871 := bstep (se 1 (by rfl) ⟨1204403, by rfl⟩ : syracuseStep 1605871 = 2408807) B2408807
theorem B1605951 : Blo 1605001 1605951 := bstep (se 1 (by rfl) ⟨1204463, by rfl⟩ : syracuseStep 1605951 = 2408927) B2408927
theorem B1606119 : Blo 1605001 1606119 := bstep (se 1 (by rfl) ⟨1204589, by rfl⟩ : syracuseStep 1606119 = 2409179) B2409179
theorem B2032219 : Blo 1605001 2032219 := bstep (se 1 (by rfl) ⟨1524164, by rfl⟩ : syracuseStep 2032219 = 3048329) B3048329
theorem B21144311 : Blo 1605001 21144311 := bstep (se 1 (by rfl) ⟨15858233, by rfl⟩ : syracuseStep 21144311 = 31716467) B31716467
theorem B1606395 : Blo 1605001 1606395 := bstep (se 1 (by rfl) ⟨1204796, by rfl⟩ : syracuseStep 1606395 = 2409593) B2409593
theorem B3613481 : Blo 1605001 3613481 := bstep (se 2 (by rfl) ⟨1355055, by rfl⟩ : syracuseStep 3613481 = 2710111) B2710111
theorem B87925601 : Blo 1605001 87925601 := bstep (se 2 (by rfl) ⟨32972100, by rfl⟩ : syracuseStep 87925601 = 65944201) B65944201
theorem B2892667 : Blo 1605001 2892667 := bstep (se 1 (by rfl) ⟨2169500, by rfl⟩ : syracuseStep 2892667 = 4339001) B4339001
theorem B1606527 : Blo 1605001 1606527 := bstep (se 1 (by rfl) ⟨1204895, by rfl⟩ : syracuseStep 1606527 = 2409791) B2409791
theorem B11740141 : Blo 1605001 11740141 := bstep (se 3 (by rfl) ⟨2201276, by rfl⟩ : syracuseStep 11740141 = 4402553) B4402553
theorem B13018103 : Blo 1605001 13018103 := bstep (se 1 (by rfl) ⟨9763577, by rfl⟩ : syracuseStep 13018103 = 19527155) B19527155
theorem B4064519 : Blo 1605001 4064519 := bstep (se 1 (by rfl) ⟨3048389, by rfl⟩ : syracuseStep 4064519 = 6096779) B6096779
theorem B4572425 : Blo 1605001 4572425 := bstep (se 2 (by rfl) ⟨1714659, by rfl⟩ : syracuseStep 4572425 = 3429319) B3429319
theorem B1606975 : Blo 1605001 1606975 := bstep (se 1 (by rfl) ⟨1205231, by rfl⟩ : syracuseStep 1606975 = 2410463) B2410463
theorem B2409839 : Blo 1605001 2409839 := bstep (se 1 (by rfl) ⟨1807379, by rfl⟩ : syracuseStep 2409839 = 3614759) B3614759
theorem B2409959 : Blo 1605001 2409959 := bstep (se 1 (by rfl) ⟨1807469, by rfl⟩ : syracuseStep 2409959 = 3614939) B3614939
theorem B9152027 : Blo 1605001 9152027 := bstep (se 1 (by rfl) ⟨6864020, by rfl⟩ : syracuseStep 9152027 = 13728041) B13728041
theorem B3049103 : Blo 1605001 3049103 := bstep (se 1 (by rfl) ⟨2286827, by rfl⟩ : syracuseStep 3049103 = 4573655) B4573655
theorem B2410139 : Blo 1605001 2410139 := bstep (se 1 (by rfl) ⟨1807604, by rfl⟩ : syracuseStep 2410139 = 3615209) B3615209
theorem B21972653 : Blo 1605001 21972653 := bstep (se 3 (by rfl) ⟨4119872, by rfl⟩ : syracuseStep 21972653 = 8239745) B8239745
theorem B21980969 : Blo 1605001 21980969 := bstep (se 2 (by rfl) ⟨8242863, by rfl⟩ : syracuseStep 21980969 = 16485727) B16485727
theorem B6858553 : Blo 1605001 6858553 := bstep (se 2 (by rfl) ⟨2571957, by rfl⟩ : syracuseStep 6858553 = 5143915) B5143915
theorem B16697335 : Blo 1605001 16697335 := bstep (se 1 (by rfl) ⟨12523001, by rfl⟩ : syracuseStep 16697335 = 25046003) B25046003
theorem B8128673 : Blo 1605001 8128673 := bstep (se 2 (by rfl) ⟨3048252, by rfl⟩ : syracuseStep 8128673 = 6096505) B6096505
theorem B9144485 : Blo 1605001 9144485 := bstep (se 4 (by rfl) ⟨857295, by rfl⟩ : syracuseStep 9144485 = 1714591) B1714591
theorem B5212343 : Blo 1605001 5212343 := bstep (se 1 (by rfl) ⟨3909257, by rfl⟩ : syracuseStep 5212343 = 7818515) B7818515
theorem B18294983 : Blo 1605001 18294983 := bstep (se 1 (by rfl) ⟨13721237, by rfl⟩ : syracuseStep 18294983 = 27442475) B27442475
theorem B3615497 : Blo 1605001 3615497 := bstep (se 2 (by rfl) ⟨1355811, by rfl⟩ : syracuseStep 3615497 = 2711623) B2711623
theorem B3091439 : Blo 1605001 3091439 := bstep (se 1 (by rfl) ⟨2318579, by rfl⟩ : syracuseStep 3091439 = 4637159) B4637159
theorem B5417981 : Blo 1605001 5417981 := bstep (se 3 (by rfl) ⟨1015871, by rfl⟩ : syracuseStep 5417981 = 2031743) B2031743
theorem B19795049 : Blo 1605001 19795049 := bstep (se 2 (by rfl) ⟨7423143, by rfl⟩ : syracuseStep 19795049 = 14846287) B14846287
theorem B3091691 : Blo 1605001 3091691 := bstep (se 1 (by rfl) ⟨2318768, by rfl⟩ : syracuseStep 3091691 = 4637537) B4637537
theorem B160501013 : Blo 1605001 160501013 := bstep (se 6 (by rfl) ⟨3761742, by rfl⟩ : syracuseStep 160501013 = 7523485) B7523485
theorem B13725065 : Blo 1605001 13725065 := bstep (se 2 (by rfl) ⟨5146899, by rfl⟩ : syracuseStep 13725065 = 10293799) B10293799
theorem B9399719 : Blo 1605001 9399719 := bstep (se 1 (by rfl) ⟨7049789, by rfl⟩ : syracuseStep 9399719 = 14099579) B14099579
theorem B55602733 : Blo 1605001 55602733 := bstep (se 3 (by rfl) ⟨10425512, by rfl⟩ : syracuseStep 55602733 = 20851025) B20851025
theorem B6180425 : Blo 1605001 6180425 := bstep (se 2 (by rfl) ⟨2317659, by rfl⟩ : syracuseStep 6180425 = 4635319) B4635319
theorem B5418575 : Blo 1605001 5418575 := bstep (se 1 (by rfl) ⟨4063931, by rfl⟩ : syracuseStep 5418575 = 8127863) B8127863
theorem B5017259 : Blo 1605001 5017259 := bstep (se 1 (by rfl) ⟨3762944, by rfl⟩ : syracuseStep 5017259 = 7525889) B7525889
theorem B3256303 : Blo 1605001 3256303 := bstep (se 1 (by rfl) ⟨2442227, by rfl⟩ : syracuseStep 3256303 = 4884455) B4884455
theorem B35196983 : Blo 1605001 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B8130779 : Blo 1605001 8130779 := bstep (se 1 (by rfl) ⟨6098084, by rfl⟩ : syracuseStep 8130779 = 12196169) B12196169
theorem B6099239 : Blo 1605001 6099239 := bstep (se 1 (by rfl) ⟨4574429, by rfl⟩ : syracuseStep 6099239 = 9148859) B9148859
theorem B93852047 : Blo 1605001 93852047 := bstep (se 1 (by rfl) ⟨70389035, by rfl⟩ : syracuseStep 93852047 = 140778071) B140778071
theorem B6099407 : Blo 1605001 6099407 := bstep (se 1 (by rfl) ⟨4574555, by rfl⟩ : syracuseStep 6099407 = 9149111) B9149111
theorem B20591495 : Blo 1605001 20591495 := bstep (se 1 (by rfl) ⟨15443621, by rfl⟩ : syracuseStep 20591495 = 30887243) B30887243
theorem B13726979 : Blo 1605001 13726979 := bstep (se 1 (by rfl) ⟨10295234, by rfl⟩ : syracuseStep 13726979 = 20590469) B20590469
theorem B2708903 : Blo 1605001 2708903 := bstep (se 1 (by rfl) ⟨2031677, by rfl⟩ : syracuseStep 2708903 = 4063355) B4063355
theorem B6100393 : Blo 1605001 6100393 := bstep (se 2 (by rfl) ⟨2287647, by rfl⟩ : syracuseStep 6100393 = 4575295) B4575295
theorem B5420681 : Blo 1605001 5420681 := bstep (se 2 (by rfl) ⟨2032755, by rfl⟩ : syracuseStep 5420681 = 4065511) B4065511
theorem B7321295 : Blo 1605001 7321295 := bstep (se 1 (by rfl) ⟨5490971, by rfl⟩ : syracuseStep 7321295 = 10981943) B10981943
theorem B5420897 : Blo 1605001 5420897 := bstep (se 2 (by rfl) ⟨2032836, by rfl⟩ : syracuseStep 5420897 = 4065673) B4065673
theorem B49428589 : Blo 1605001 49428589 := bstep (se 3 (by rfl) ⟨9267860, by rfl⟩ : syracuseStep 49428589 = 18535721) B18535721
theorem B2709787 : Blo 1605001 2709787 := bstep (se 1 (by rfl) ⟨2032340, by rfl⟩ : syracuseStep 2709787 = 4064681) B4064681
theorem B2709929 : Blo 1605001 2709929 := bstep (se 2 (by rfl) ⟨1016223, by rfl⟩ : syracuseStep 2709929 = 2032447) B2032447
theorem B9771457 : Blo 1605001 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B5421599 : Blo 1605001 5421599 := bstep (se 1 (by rfl) ⟨4066199, by rfl⟩ : syracuseStep 5421599 = 8132399) B8132399
theorem B3611591 : Blo 1605001 3611591 := bstep (se 1 (by rfl) ⟨2708693, by rfl⟩ : syracuseStep 3611591 = 5417387) B5417387
theorem B9149543 : Blo 1605001 9149543 := bstep (se 1 (by rfl) ⟨6862157, by rfl⟩ : syracuseStep 9149543 = 13724315) B13724315
theorem B5790827 : Blo 1605001 5790827 := bstep (se 1 (by rfl) ⟨4343120, by rfl⟩ : syracuseStep 5790827 = 8686241) B8686241
theorem B2710759 : Blo 1605001 2710759 := bstep (se 1 (by rfl) ⟨2033069, by rfl⟩ : syracuseStep 2710759 = 4066139) B4066139
theorem B3611951 : Blo 1605001 3611951 := bstep (se 1 (by rfl) ⟨2708963, by rfl⟩ : syracuseStep 3611951 = 5417927) B5417927
theorem B6864209 : Blo 1605001 6864209 := bstep (se 2 (by rfl) ⟨2574078, by rfl⟩ : syracuseStep 6864209 = 5148157) B5148157
theorem B1605087 : Blo 1605001 1605087 := bstep (se 1 (by rfl) ⟨1203815, by rfl⟩ : syracuseStep 1605087 = 2407631) B2407631
theorem B24714733 : Blo 1605001 24714733 := bstep (se 3 (by rfl) ⟨4634012, by rfl⟩ : syracuseStep 24714733 = 9268025) B9268025
theorem B1605147 : Blo 1605001 1605147 := bstep (se 1 (by rfl) ⟨1203860, by rfl⟩ : syracuseStep 1605147 = 2407721) B2407721
theorem B1605167 : Blo 1605001 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B9273035 : Blo 1605001 9273035 := bstep (se 1 (by rfl) ⟨6954776, by rfl⟩ : syracuseStep 9273035 = 13909553) B13909553
theorem B2711279 : Blo 1605001 2711279 := bstep (se 1 (by rfl) ⟨2033459, by rfl⟩ : syracuseStep 2711279 = 4066919) B4066919
theorem B2408303 : Blo 1605001 2408303 := bstep (se 1 (by rfl) ⟨1806227, by rfl⟩ : syracuseStep 2408303 = 3612455) B3612455
theorem B29319043 : Blo 1605001 29319043 := bstep (se 1 (by rfl) ⟨21989282, by rfl⟩ : syracuseStep 29319043 = 43978565) B43978565
theorem B16482203 : Blo 1605001 16482203 := bstep (se 1 (by rfl) ⟨12361652, by rfl⟩ : syracuseStep 16482203 = 24723305) B24723305
theorem B1605567 : Blo 1605001 1605567 := bstep (se 1 (by rfl) ⟨1204175, by rfl⟩ : syracuseStep 1605567 = 2408351) B2408351
theorem B1605627 : Blo 1605001 1605627 := bstep (se 1 (by rfl) ⟨1204220, by rfl⟩ : syracuseStep 1605627 = 2408441) B2408441
theorem B65904785 : Blo 1605001 65904785 := bstep (se 2 (by rfl) ⟨24714294, by rfl⟩ : syracuseStep 65904785 = 49428589) B49428589
theorem B3613049 : Blo 1605001 3613049 := bstep (se 2 (by rfl) ⟨1354893, by rfl⟩ : syracuseStep 3613049 = 2709787) B2709787
theorem B2408987 : Blo 1605001 2408987 := bstep (se 1 (by rfl) ⟨1806740, by rfl⟩ : syracuseStep 2408987 = 3613481) B3613481
theorem B9151319 : Blo 1605001 9151319 := bstep (se 1 (by rfl) ⟨6863489, by rfl⟩ : syracuseStep 9151319 = 13726979) B13726979
theorem B3048283 : Blo 1605001 3048283 := bstep (se 1 (by rfl) ⟨2286212, by rfl⟩ : syracuseStep 3048283 = 4572425) B4572425
theorem B1606559 : Blo 1605001 1606559 := bstep (se 1 (by rfl) ⟨1204919, by rfl⟩ : syracuseStep 1606559 = 2409839) B2409839
theorem B1606639 : Blo 1605001 1606639 := bstep (se 1 (by rfl) ⟨1204979, by rfl⟩ : syracuseStep 1606639 = 2409959) B2409959
theorem B3613787 : Blo 1605001 3613787 := bstep (se 1 (by rfl) ⟨2710340, by rfl⟩ : syracuseStep 3613787 = 5420681) B5420681
theorem B1606759 : Blo 1605001 1606759 := bstep (se 1 (by rfl) ⟨1205069, by rfl⟩ : syracuseStep 1606759 = 2410139) B2410139
theorem B14648435 : Blo 1605001 14648435 := bstep (se 1 (by rfl) ⟨10986326, by rfl⟩ : syracuseStep 14648435 = 21972653) B21972653
theorem B3613931 : Blo 1605001 3613931 := bstep (se 1 (by rfl) ⟨2710448, by rfl⟩ : syracuseStep 3613931 = 5420897) B5420897
theorem B6096323 : Blo 1605001 6096323 := bstep (se 1 (by rfl) ⟨4572242, by rfl⟩ : syracuseStep 6096323 = 9144485) B9144485
theorem B3474895 : Blo 1605001 3474895 := bstep (se 1 (by rfl) ⟨2606171, by rfl⟩ : syracuseStep 3474895 = 5212343) B5212343
theorem B3614345 : Blo 1605001 3614345 := bstep (se 2 (by rfl) ⟨1355379, by rfl⟩ : syracuseStep 3614345 = 2710759) B2710759
theorem B3614399 : Blo 1605001 3614399 := bstep (se 1 (by rfl) ⟨2710799, by rfl⟩ : syracuseStep 3614399 = 5421599) B5421599
theorem B2410331 : Blo 1605001 2410331 := bstep (se 1 (by rfl) ⟨1807748, by rfl⟩ : syracuseStep 2410331 = 3615497) B3615497
theorem B3860551 : Blo 1605001 3860551 := bstep (se 1 (by rfl) ⟨2895413, by rfl⟩ : syracuseStep 3860551 = 5790827) B5790827
theorem B9144737 : Blo 1605001 9144737 := bstep (se 2 (by rfl) ⟨3429276, by rfl⟩ : syracuseStep 9144737 = 6858553) B6858553
theorem B3344839 : Blo 1605001 3344839 := bstep (se 1 (by rfl) ⟨2508629, by rfl⟩ : syracuseStep 3344839 = 5017259) B5017259
theorem B10988135 : Blo 1605001 10988135 := bstep (se 1 (by rfl) ⟨8241101, by rfl⟩ : syracuseStep 10988135 = 16482203) B16482203
theorem B23464655 : Blo 1605001 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B4066159 : Blo 1605001 4066159 := bstep (se 1 (by rfl) ⟨3049619, by rfl⟩ : syracuseStep 4066159 = 6099239) B6099239
theorem B4066271 : Blo 1605001 4066271 := bstep (se 1 (by rfl) ⟨3049703, by rfl⟩ : syracuseStep 4066271 = 6099407) B6099407
theorem B58617067 : Blo 1605001 58617067 := bstep (se 1 (by rfl) ⟨43962800, by rfl⟩ : syracuseStep 58617067 = 87925601) B87925601
theorem B13028609 : Blo 1605001 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B8678735 : Blo 1605001 8678735 := bstep (se 1 (by rfl) ⟨6509051, by rfl⟩ : syracuseStep 8678735 = 13018103) B13018103
theorem B1805935 : Blo 1605001 1805935 := bstep (se 1 (by rfl) ⟨1354451, by rfl⟩ : syracuseStep 1805935 = 2708903) B2708903
theorem B5419115 : Blo 1605001 5419115 := bstep (se 1 (by rfl) ⟨4064336, by rfl⟩ : syracuseStep 5419115 = 8128673) B8128673
theorem B1806619 : Blo 1605001 1806619 := bstep (se 1 (by rfl) ⟨1354964, by rfl⟩ : syracuseStep 1806619 = 2709929) B2709929
theorem B8130941 : Blo 1605001 8130941 := bstep (se 3 (by rfl) ⟨1524551, by rfl⟩ : syracuseStep 8130941 = 3049103) B3049103
theorem B32952977 : Blo 1605001 32952977 := bstep (se 2 (by rfl) ⟨12357366, by rfl⟩ : syracuseStep 32952977 = 24714733) B24714733
theorem B2060959 : Blo 1605001 2060959 := bstep (se 1 (by rfl) ⟨1545719, by rfl⟩ : syracuseStep 2060959 = 3091439) B3091439
theorem B6099695 : Blo 1605001 6099695 := bstep (se 1 (by rfl) ⟨4574771, by rfl⟩ : syracuseStep 6099695 = 9149543) B9149543
theorem B2061127 : Blo 1605001 2061127 := bstep (se 1 (by rfl) ⟨1545845, by rfl⟩ : syracuseStep 2061127 = 3091691) B3091691
theorem B107000675 : Blo 1605001 107000675 := bstep (se 1 (by rfl) ⟨80250506, by rfl⟩ : syracuseStep 107000675 = 160501013) B160501013
theorem B4576139 : Blo 1605001 4576139 := bstep (se 1 (by rfl) ⟨3432104, by rfl⟩ : syracuseStep 4576139 = 6864209) B6864209
theorem B6182023 : Blo 1605001 6182023 := bstep (se 1 (by rfl) ⟨4636517, by rfl⟩ : syracuseStep 6182023 = 9273035) B9273035
theorem B1807519 : Blo 1605001 1807519 := bstep (se 1 (by rfl) ⟨1355639, by rfl⟩ : syracuseStep 1807519 = 2711279) B2711279
theorem B22263113 : Blo 1605001 22263113 := bstep (se 2 (by rfl) ⟨8348667, by rfl⟩ : syracuseStep 22263113 = 16697335) B16697335
theorem B5420519 : Blo 1605001 5420519 := bstep (se 1 (by rfl) ⟨4065389, by rfl⟩ : syracuseStep 5420519 = 8130779) B8130779
theorem B2709065 : Blo 1605001 2709065 := bstep (se 2 (by rfl) ⟨1015899, by rfl⟩ : syracuseStep 2709065 = 2031799) B2031799
theorem B14096207 : Blo 1605001 14096207 := bstep (se 1 (by rfl) ⟨10572155, by rfl⟩ : syracuseStep 14096207 = 21144311) B21144311
theorem B13727663 : Blo 1605001 13727663 := bstep (se 1 (by rfl) ⟨10295747, by rfl⟩ : syracuseStep 13727663 = 20591495) B20591495
theorem B2709625 : Blo 1605001 2709625 := bstep (se 2 (by rfl) ⟨1016109, by rfl⟩ : syracuseStep 2709625 = 2032219) B2032219
theorem B2709679 : Blo 1605001 2709679 := bstep (se 1 (by rfl) ⟨2032259, by rfl⟩ : syracuseStep 2709679 = 4064519) B4064519
theorem B6101351 : Blo 1605001 6101351 := bstep (se 1 (by rfl) ⟨4576013, by rfl⟩ : syracuseStep 6101351 = 9152027) B9152027
theorem B250272125 : Blo 1605001 250272125 := bstep (se 3 (by rfl) ⟨46926023, by rfl⟩ : syracuseStep 250272125 = 93852047) B93852047
theorem B4880863 : Blo 1605001 4880863 := bstep (se 1 (by rfl) ⟨3660647, by rfl⟩ : syracuseStep 4880863 = 7321295) B7321295
theorem B3856889 : Blo 1605001 3856889 := bstep (se 2 (by rfl) ⟨1446333, by rfl⟩ : syracuseStep 3856889 = 2892667) B2892667
theorem B14653979 : Blo 1605001 14653979 := bstep (se 1 (by rfl) ⟨10990484, by rfl⟩ : syracuseStep 14653979 = 21980969) B21980969
theorem B15653521 : Blo 1605001 15653521 := bstep (se 2 (by rfl) ⟨5870070, by rfl⟩ : syracuseStep 15653521 = 11740141) B11740141
theorem B12196655 : Blo 1605001 12196655 := bstep (se 1 (by rfl) ⟨9147491, by rfl⟩ : syracuseStep 12196655 = 18294983) B18294983
theorem B8133857 : Blo 1605001 8133857 := bstep (se 2 (by rfl) ⟨3050196, by rfl⟩ : syracuseStep 8133857 = 6100393) B6100393
theorem B2407727 : Blo 1605001 2407727 := bstep (se 1 (by rfl) ⟨1805795, by rfl⟩ : syracuseStep 2407727 = 3611591) B3611591
theorem B3611987 : Blo 1605001 3611987 := bstep (se 1 (by rfl) ⟨2708990, by rfl⟩ : syracuseStep 3611987 = 5417981) B5417981
theorem B74136977 : Blo 1605001 74136977 := bstep (se 2 (by rfl) ⟨27801366, by rfl⟩ : syracuseStep 74136977 = 55602733) B55602733
theorem B13196699 : Blo 1605001 13196699 := bstep (se 1 (by rfl) ⟨9897524, by rfl⟩ : syracuseStep 13196699 = 19795049) B19795049
theorem B2407967 : Blo 1605001 2407967 := bstep (se 1 (by rfl) ⟨1805975, by rfl⟩ : syracuseStep 2407967 = 3611951) B3611951
theorem B9150043 : Blo 1605001 9150043 := bstep (se 1 (by rfl) ⟨6862532, by rfl⟩ : syracuseStep 9150043 = 13725065) B13725065
theorem B6266479 : Blo 1605001 6266479 := bstep (se 1 (by rfl) ⟨4699859, by rfl⟩ : syracuseStep 6266479 = 9399719) B9399719
theorem B4120283 : Blo 1605001 4120283 := bstep (se 1 (by rfl) ⟨3090212, by rfl⟩ : syracuseStep 4120283 = 6180425) B6180425
theorem B3612383 : Blo 1605001 3612383 := bstep (se 1 (by rfl) ⟨2709287, by rfl⟩ : syracuseStep 3612383 = 5418575) B5418575
theorem B39092057 : Blo 1605001 39092057 := bstep (se 2 (by rfl) ⟨14659521, by rfl⟩ : syracuseStep 39092057 = 29319043) B29319043
theorem B1605535 : Blo 1605001 1605535 := bstep (se 1 (by rfl) ⟨1204151, by rfl⟩ : syracuseStep 1605535 = 2408303) B2408303
theorem B4341737 : Blo 1605001 4341737 := bstep (se 2 (by rfl) ⟨1628151, by rfl⟩ : syracuseStep 4341737 = 3256303) B3256303
theorem B3612743 : Blo 1605001 3612743 := bstep (se 1 (by rfl) ⟨2709557, by rfl⟩ : syracuseStep 3612743 = 5419115) B5419115
theorem B3612833 : Blo 1605001 3612833 := bstep (se 2 (by rfl) ⟨1354812, by rfl⟩ : syracuseStep 3612833 = 2709625) B2709625
theorem B3612905 : Blo 1605001 3612905 := bstep (se 2 (by rfl) ⟨1354839, by rfl⟩ : syracuseStep 3612905 = 2709679) B2709679
theorem B2408699 : Blo 1605001 2408699 := bstep (se 1 (by rfl) ⟨1806524, by rfl⟩ : syracuseStep 2408699 = 3613049) B3613049
theorem B1605991 : Blo 1605001 1605991 := bstep (se 1 (by rfl) ⟨1204493, by rfl⟩ : syracuseStep 1605991 = 2408987) B2408987
theorem B2408825 : Blo 1605001 2408825 := bstep (se 2 (by rfl) ⟨903309, by rfl⟩ : syracuseStep 2408825 = 1806619) B1806619
theorem B2409191 : Blo 1605001 2409191 := bstep (se 1 (by rfl) ⟨1806893, by rfl⟩ : syracuseStep 2409191 = 3613787) B3613787
theorem B9765623 : Blo 1605001 9765623 := bstep (se 1 (by rfl) ⟨7324217, by rfl⟩ : syracuseStep 9765623 = 14648435) B14648435
theorem B2409287 : Blo 1605001 2409287 := bstep (se 1 (by rfl) ⟨1806965, by rfl⟩ : syracuseStep 2409287 = 3613931) B3613931
theorem B4064215 : Blo 1605001 4064215 := bstep (se 1 (by rfl) ⟨3048161, by rfl⟩ : syracuseStep 4064215 = 6096323) B6096323
theorem B3613679 : Blo 1605001 3613679 := bstep (se 1 (by rfl) ⟨2710259, by rfl⟩ : syracuseStep 3613679 = 5420519) B5420519
theorem B2409563 : Blo 1605001 2409563 := bstep (se 1 (by rfl) ⟨1807172, by rfl⟩ : syracuseStep 2409563 = 3614345) B3614345
theorem B4064377 : Blo 1605001 4064377 := bstep (se 2 (by rfl) ⟨1524141, by rfl⟩ : syracuseStep 4064377 = 3048283) B3048283
theorem B2409599 : Blo 1605001 2409599 := bstep (se 1 (by rfl) ⟨1807199, by rfl⟩ : syracuseStep 2409599 = 3614399) B3614399
theorem B9397471 : Blo 1605001 9397471 := bstep (se 1 (by rfl) ⟨7048103, by rfl⟩ : syracuseStep 9397471 = 14096207) B14096207
theorem B1606887 : Blo 1605001 1606887 := bstep (se 1 (by rfl) ⟨1205165, by rfl⟩ : syracuseStep 1606887 = 2410331) B2410331
theorem B9151775 : Blo 1605001 9151775 := bstep (se 1 (by rfl) ⟨6863831, by rfl⟩ : syracuseStep 9151775 = 13727663) B13727663
theorem B8242697 : Blo 1605001 8242697 := bstep (se 2 (by rfl) ⟨3091011, by rfl⟩ : syracuseStep 8242697 = 6182023) B6182023
theorem B2410025 : Blo 1605001 2410025 := bstep (se 2 (by rfl) ⟨903759, by rfl⟩ : syracuseStep 2410025 = 1807519) B1807519
theorem B166848083 : Blo 1605001 166848083 := bstep (se 1 (by rfl) ⟨125136062, by rfl⟩ : syracuseStep 166848083 = 250272125) B250272125
theorem B6096491 : Blo 1605001 6096491 := bstep (se 1 (by rfl) ⟨4572368, by rfl⟩ : syracuseStep 6096491 = 9144737) B9144737
theorem B7325423 : Blo 1605001 7325423 := bstep (se 1 (by rfl) ⟨5494067, by rfl⟩ : syracuseStep 7325423 = 10988135) B10988135
theorem B12200057 : Blo 1605001 12200057 := bstep (se 2 (by rfl) ⟨4575021, by rfl⟩ : syracuseStep 12200057 = 9150043) B9150043
theorem B8685739 : Blo 1605001 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B5785823 : Blo 1605001 5785823 := bstep (se 1 (by rfl) ⟨4339367, by rfl⟩ : syracuseStep 5785823 = 8678735) B8678735
theorem B49424651 : Blo 1605001 49424651 := bstep (se 1 (by rfl) ⟨37068488, by rfl⟩ : syracuseStep 49424651 = 74136977) B74136977
theorem B2746855 : Blo 1605001 2746855 := bstep (se 1 (by rfl) ⟨2060141, by rfl⟩ : syracuseStep 2746855 = 4120283) B4120283
theorem B26061371 : Blo 1605001 26061371 := bstep (se 1 (by rfl) ⟨19546028, by rfl⟩ : syracuseStep 26061371 = 39092057) B39092057
theorem B2894491 : Blo 1605001 2894491 := bstep (se 1 (by rfl) ⟨2170868, by rfl⟩ : syracuseStep 2894491 = 4341737) B4341737
theorem B5147401 : Blo 1605001 5147401 := bstep (se 2 (by rfl) ⟨1930275, by rfl⟩ : syracuseStep 5147401 = 3860551) B3860551
theorem B43936523 : Blo 1605001 43936523 := bstep (se 1 (by rfl) ⟨32952392, by rfl⟩ : syracuseStep 43936523 = 65904785) B65904785
theorem B4066463 : Blo 1605001 4066463 := bstep (se 1 (by rfl) ⟨3049847, by rfl⟩ : syracuseStep 4066463 = 6099695) B6099695
theorem B3050759 : Blo 1605001 3050759 := bstep (se 1 (by rfl) ⟨2288069, by rfl⟩ : syracuseStep 3050759 = 4576139) B4576139
theorem B2747945 : Blo 1605001 2747945 := bstep (se 2 (by rfl) ⟨1030479, by rfl⟩ : syracuseStep 2747945 = 2060959) B2060959
theorem B1806043 : Blo 1605001 1806043 := bstep (se 1 (by rfl) ⟨1354532, by rfl⟩ : syracuseStep 1806043 = 2709065) B2709065
theorem B2748169 : Blo 1605001 2748169 := bstep (se 2 (by rfl) ⟨1030563, by rfl⟩ : syracuseStep 2748169 = 2061127) B2061127
theorem B71356565 : Blo 1605001 71356565 := bstep (se 6 (by rfl) ⟨1672419, by rfl⟩ : syracuseStep 71356565 = 3344839) B3344839
theorem B4067567 : Blo 1605001 4067567 := bstep (se 1 (by rfl) ⟨3050675, by rfl⟩ : syracuseStep 4067567 = 6101351) B6101351
theorem B78156089 : Blo 1605001 78156089 := bstep (se 2 (by rfl) ⟨29308533, by rfl⟩ : syracuseStep 78156089 = 58617067) B58617067
theorem B9769319 : Blo 1605001 9769319 := bstep (se 1 (by rfl) ⟨7326989, by rfl⟩ : syracuseStep 9769319 = 14653979) B14653979
theorem B15643103 : Blo 1605001 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B8131103 : Blo 1605001 8131103 := bstep (se 1 (by rfl) ⟨6098327, by rfl⟩ : syracuseStep 8131103 = 12196655) B12196655
theorem B4633193 : Blo 1605001 4633193 := bstep (se 2 (by rfl) ⟨1737447, by rfl⟩ : syracuseStep 4633193 = 3474895) B3474895
theorem B26031269 : Blo 1605001 26031269 := bstep (se 4 (by rfl) ⟨2440431, by rfl⟩ : syracuseStep 26031269 = 4880863) B4880863
theorem B5420627 : Blo 1605001 5420627 := bstep (se 1 (by rfl) ⟨4065470, by rfl⟩ : syracuseStep 5420627 = 8130941) B8130941
theorem B21968651 : Blo 1605001 21968651 := bstep (se 1 (by rfl) ⟨16476488, by rfl⟩ : syracuseStep 21968651 = 32952977) B32952977
theorem B6100879 : Blo 1605001 6100879 := bstep (se 1 (by rfl) ⟨4575659, by rfl⟩ : syracuseStep 6100879 = 9151319) B9151319
theorem B71333783 : Blo 1605001 71333783 := bstep (se 1 (by rfl) ⟨53500337, by rfl⟩ : syracuseStep 71333783 = 107000675) B107000675
theorem B20871361 : Blo 1605001 20871361 := bstep (se 2 (by rfl) ⟨7826760, by rfl⟩ : syracuseStep 20871361 = 15653521) B15653521
theorem B14842075 : Blo 1605001 14842075 := bstep (se 1 (by rfl) ⟨11131556, by rfl⟩ : syracuseStep 14842075 = 22263113) B22263113
theorem B5421545 : Blo 1605001 5421545 := bstep (se 2 (by rfl) ⟨2033079, by rfl⟩ : syracuseStep 5421545 = 4066159) B4066159
theorem B2571259 : Blo 1605001 2571259 := bstep (se 1 (by rfl) ⟨1928444, by rfl⟩ : syracuseStep 2571259 = 3856889) B3856889
theorem B2710847 : Blo 1605001 2710847 := bstep (se 1 (by rfl) ⟨2033135, by rfl⟩ : syracuseStep 2710847 = 4066271) B4066271
theorem B2407913 : Blo 1605001 2407913 := bstep (se 2 (by rfl) ⟨902967, by rfl⟩ : syracuseStep 2407913 = 1805935) B1805935
theorem B8355305 : Blo 1605001 8355305 := bstep (se 2 (by rfl) ⟨3133239, by rfl⟩ : syracuseStep 8355305 = 6266479) B6266479
theorem B5422571 : Blo 1605001 5422571 := bstep (se 1 (by rfl) ⟨4066928, by rfl⟩ : syracuseStep 5422571 = 8133857) B8133857
theorem B1605151 : Blo 1605001 1605151 := bstep (se 1 (by rfl) ⟨1203863, by rfl⟩ : syracuseStep 1605151 = 2407727) B2407727
theorem B2407991 : Blo 1605001 2407991 := bstep (se 1 (by rfl) ⟨1805993, by rfl⟩ : syracuseStep 2407991 = 3611987) B3611987
theorem B8797799 : Blo 1605001 8797799 := bstep (se 1 (by rfl) ⟨6598349, by rfl⟩ : syracuseStep 8797799 = 13196699) B13196699
theorem B1605311 : Blo 1605001 1605311 := bstep (se 1 (by rfl) ⟨1203983, by rfl⟩ : syracuseStep 1605311 = 2407967) B2407967
theorem B2408255 : Blo 1605001 2408255 := bstep (se 1 (by rfl) ⟨1806191, by rfl⟩ : syracuseStep 2408255 = 3612383) B3612383
theorem B2408495 : Blo 1605001 2408495 := bstep (se 1 (by rfl) ⟨1806371, by rfl⟩ : syracuseStep 2408495 = 3612743) B3612743
theorem B2408555 : Blo 1605001 2408555 := bstep (se 1 (by rfl) ⟨1806416, by rfl⟩ : syracuseStep 2408555 = 3612833) B3612833
theorem B2408603 : Blo 1605001 2408603 := bstep (se 1 (by rfl) ⟨1806452, by rfl⟩ : syracuseStep 2408603 = 3612905) B3612905
theorem B2711711 : Blo 1605001 2711711 := bstep (se 1 (by rfl) ⟨2033783, by rfl⟩ : syracuseStep 2711711 = 4067567) B4067567
theorem B1605799 : Blo 1605001 1605799 := bstep (se 1 (by rfl) ⟨1204349, by rfl⟩ : syracuseStep 1605799 = 2408699) B2408699
theorem B6512879 : Blo 1605001 6512879 := bstep (se 1 (by rfl) ⟨4884659, by rfl⟩ : syracuseStep 6512879 = 9769319) B9769319
theorem B1605883 : Blo 1605001 1605883 := bstep (se 1 (by rfl) ⟨1204412, by rfl⟩ : syracuseStep 1605883 = 2408825) B2408825
theorem B27828481 : Blo 1605001 27828481 := bstep (se 2 (by rfl) ⟨10435680, by rfl⟩ : syracuseStep 27828481 = 20871361) B20871361
theorem B190284173 : Blo 1605001 190284173 := bstep (se 3 (by rfl) ⟨35678282, by rfl⟩ : syracuseStep 190284173 = 71356565) B71356565
theorem B3088795 : Blo 1605001 3088795 := bstep (se 1 (by rfl) ⟨2316596, by rfl⟩ : syracuseStep 3088795 = 4633193) B4633193
theorem B1606127 : Blo 1605001 1606127 := bstep (se 1 (by rfl) ⟨1204595, by rfl⟩ : syracuseStep 1606127 = 2409191) B2409191
theorem B1606191 : Blo 1605001 1606191 := bstep (se 1 (by rfl) ⟨1204643, by rfl⟩ : syracuseStep 1606191 = 2409287) B2409287
theorem B2409119 : Blo 1605001 2409119 := bstep (se 1 (by rfl) ⟨1806839, by rfl⟩ : syracuseStep 2409119 = 3613679) B3613679
theorem B1606375 : Blo 1605001 1606375 := bstep (se 1 (by rfl) ⟨1204781, by rfl⟩ : syracuseStep 1606375 = 2409563) B2409563
theorem B1606399 : Blo 1605001 1606399 := bstep (se 1 (by rfl) ⟨1204799, by rfl⟩ : syracuseStep 1606399 = 2409599) B2409599
theorem B3859321 : Blo 1605001 3859321 := bstep (se 2 (by rfl) ⟨1447245, by rfl⟩ : syracuseStep 3859321 = 2894491) B2894491
theorem B1606683 : Blo 1605001 1606683 := bstep (se 1 (by rfl) ⟨1205012, by rfl⟩ : syracuseStep 1606683 = 2410025) B2410025
theorem B111232055 : Blo 1605001 111232055 := bstep (se 1 (by rfl) ⟨83424041, by rfl⟩ : syracuseStep 111232055 = 166848083) B166848083
theorem B3613751 : Blo 1605001 3613751 := bstep (se 1 (by rfl) ⟨2710313, by rfl⟩ : syracuseStep 3613751 = 5420627) B5420627
theorem B4064327 : Blo 1605001 4064327 := bstep (se 1 (by rfl) ⟨3048245, by rfl⟩ : syracuseStep 4064327 = 6096491) B6096491
theorem B4883615 : Blo 1605001 4883615 := bstep (se 1 (by rfl) ⟨3662711, by rfl⟩ : syracuseStep 4883615 = 7325423) B7325423
theorem B41714941 : Blo 1605001 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B47555855 : Blo 1605001 47555855 := bstep (se 1 (by rfl) ⟨35666891, by rfl⟩ : syracuseStep 47555855 = 71333783) B71333783
theorem B32949767 : Blo 1605001 32949767 := bstep (se 1 (by rfl) ⟨24712325, by rfl⟩ : syracuseStep 32949767 = 49424651) B49424651
theorem B3614363 : Blo 1605001 3614363 := bstep (se 1 (by rfl) ⟨2710772, by rfl⟩ : syracuseStep 3614363 = 5421545) B5421545
theorem B2033839 : Blo 1605001 2033839 := bstep (se 1 (by rfl) ⟨1525379, by rfl⟩ : syracuseStep 2033839 = 3050759) B3050759
theorem B3615047 : Blo 1605001 3615047 := bstep (se 1 (by rfl) ⟨2711285, by rfl⟩ : syracuseStep 3615047 = 5422571) B5422571
theorem B3664225 : Blo 1605001 3664225 := bstep (se 2 (by rfl) ⟨1374084, by rfl⟩ : syracuseStep 3664225 = 2748169) B2748169
theorem B14649893 : Blo 1605001 14649893 := bstep (se 4 (by rfl) ⟨1373427, by rfl⟩ : syracuseStep 14649893 = 2746855) B2746855
theorem B52104059 : Blo 1605001 52104059 := bstep (se 1 (by rfl) ⟨39078044, by rfl⟩ : syracuseStep 52104059 = 78156089) B78156089
theorem B17354179 : Blo 1605001 17354179 := bstep (se 1 (by rfl) ⟨13015634, by rfl⟩ : syracuseStep 17354179 = 26031269) B26031269
theorem B5418953 : Blo 1605001 5418953 := bstep (se 2 (by rfl) ⟨2032107, by rfl⟩ : syracuseStep 5418953 = 4064215) B4064215
theorem B3428345 : Blo 1605001 3428345 := bstep (se 2 (by rfl) ⟨1285629, by rfl⟩ : syracuseStep 3428345 = 2571259) B2571259
theorem B7327853 : Blo 1605001 7327853 := bstep (se 3 (by rfl) ⟨1373972, by rfl⟩ : syracuseStep 7327853 = 2747945) B2747945
theorem B5419169 : Blo 1605001 5419169 := bstep (se 2 (by rfl) ⟨2032188, by rfl⟩ : syracuseStep 5419169 = 4064377) B4064377
theorem B12529961 : Blo 1605001 12529961 := bstep (se 2 (by rfl) ⟨4698735, by rfl⟩ : syracuseStep 12529961 = 9397471) B9397471
theorem B29291015 : Blo 1605001 29291015 := bstep (se 1 (by rfl) ⟨21968261, by rfl⟩ : syracuseStep 29291015 = 43936523) B43936523
theorem B1807231 : Blo 1605001 1807231 := bstep (se 1 (by rfl) ⟨1355423, by rfl⟩ : syracuseStep 1807231 = 2710847) B2710847
theorem B11580985 : Blo 1605001 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B19789433 : Blo 1605001 19789433 := bstep (se 2 (by rfl) ⟨7421037, by rfl⟩ : syracuseStep 19789433 = 14842075) B14842075
theorem B5420735 : Blo 1605001 5420735 := bstep (se 1 (by rfl) ⟨4065551, by rfl⟩ : syracuseStep 5420735 = 8131103) B8131103
theorem B6510415 : Blo 1605001 6510415 := bstep (se 1 (by rfl) ⟨4882811, by rfl⟩ : syracuseStep 6510415 = 9765623) B9765623
theorem B6101183 : Blo 1605001 6101183 := bstep (se 1 (by rfl) ⟨4575887, by rfl⟩ : syracuseStep 6101183 = 9151775) B9151775
theorem B5495131 : Blo 1605001 5495131 := bstep (se 1 (by rfl) ⟨4121348, by rfl⟩ : syracuseStep 5495131 = 8242697) B8242697
theorem B6863201 : Blo 1605001 6863201 := bstep (se 2 (by rfl) ⟨2573700, by rfl⟩ : syracuseStep 6863201 = 5147401) B5147401
theorem B14645767 : Blo 1605001 14645767 := bstep (se 1 (by rfl) ⟨10984325, by rfl⟩ : syracuseStep 14645767 = 21968651) B21968651
theorem B8133371 : Blo 1605001 8133371 := bstep (se 1 (by rfl) ⟨6100028, by rfl⟩ : syracuseStep 8133371 = 12200057) B12200057
theorem B3857215 : Blo 1605001 3857215 := bstep (se 1 (by rfl) ⟨2892911, by rfl⟩ : syracuseStep 3857215 = 5785823) B5785823
theorem B17374247 : Blo 1605001 17374247 := bstep (se 1 (by rfl) ⟨13030685, by rfl⟩ : syracuseStep 17374247 = 26061371) B26061371
theorem B2710975 : Blo 1605001 2710975 := bstep (se 1 (by rfl) ⟨2033231, by rfl⟩ : syracuseStep 2710975 = 4066463) B4066463
theorem B2408057 : Blo 1605001 2408057 := bstep (se 2 (by rfl) ⟨903021, by rfl⟩ : syracuseStep 2408057 = 1806043) B1806043
theorem B1605275 : Blo 1605001 1605275 := bstep (se 1 (by rfl) ⟨1203956, by rfl⟩ : syracuseStep 1605275 = 2407913) B2407913
theorem B5570203 : Blo 1605001 5570203 := bstep (se 1 (by rfl) ⟨4177652, by rfl⟩ : syracuseStep 5570203 = 8355305) B8355305
theorem B1605327 : Blo 1605001 1605327 := bstep (se 1 (by rfl) ⟨1203995, by rfl⟩ : syracuseStep 1605327 = 2407991) B2407991
theorem B5865199 : Blo 1605001 5865199 := bstep (se 1 (by rfl) ⟨4398899, by rfl⟩ : syracuseStep 5865199 = 8797799) B8797799
theorem B8134505 : Blo 1605001 8134505 := bstep (se 2 (by rfl) ⟨3050439, by rfl⟩ : syracuseStep 8134505 = 6100879) B6100879
theorem B1605503 : Blo 1605001 1605503 := bstep (se 1 (by rfl) ⟨1204127, by rfl⟩ : syracuseStep 1605503 = 2408255) B2408255
theorem B1605663 : Blo 1605001 1605663 := bstep (se 1 (by rfl) ⟨1204247, by rfl⟩ : syracuseStep 1605663 = 2408495) B2408495
theorem B1605703 : Blo 1605001 1605703 := bstep (se 1 (by rfl) ⟨1204277, by rfl⟩ : syracuseStep 1605703 = 2408555) B2408555
theorem B1605735 : Blo 1605001 1605735 := bstep (se 1 (by rfl) ⟨1204301, by rfl⟩ : syracuseStep 1605735 = 2408603) B2408603
theorem B3612779 : Blo 1605001 3612779 := bstep (se 1 (by rfl) ⟨2709584, by rfl⟩ : syracuseStep 3612779 = 5419169) B5419169
theorem B4341919 : Blo 1605001 4341919 := bstep (se 1 (by rfl) ⟨3256439, by rfl⟩ : syracuseStep 4341919 = 6512879) B6512879
theorem B2711785 : Blo 1605001 2711785 := bstep (se 2 (by rfl) ⟨1016919, by rfl⟩ : syracuseStep 2711785 = 2033839) B2033839
theorem B1606079 : Blo 1605001 1606079 := bstep (se 1 (by rfl) ⟨1204559, by rfl⟩ : syracuseStep 1606079 = 2409119) B2409119
theorem B2409167 : Blo 1605001 2409167 := bstep (se 1 (by rfl) ⟨1806875, by rfl⟩ : syracuseStep 2409167 = 3613751) B3613751
theorem B31703903 : Blo 1605001 31703903 := bstep (se 1 (by rfl) ⟨23777927, by rfl⟩ : syracuseStep 31703903 = 47555855) B47555855
theorem B2409575 : Blo 1605001 2409575 := bstep (se 1 (by rfl) ⟨1807181, by rfl⟩ : syracuseStep 2409575 = 3614363) B3614363
theorem B3613823 : Blo 1605001 3613823 := bstep (se 1 (by rfl) ⟨2710367, by rfl⟩ : syracuseStep 3613823 = 5420735) B5420735
theorem B5145761 : Blo 1605001 5145761 := bstep (se 2 (by rfl) ⟨1929660, by rfl⟩ : syracuseStep 5145761 = 3859321) B3859321
theorem B2409641 : Blo 1605001 2409641 := bstep (se 2 (by rfl) ⟨903615, by rfl⟩ : syracuseStep 2409641 = 1807231) B1807231
theorem B2410031 : Blo 1605001 2410031 := bstep (se 1 (by rfl) ⟨1807523, by rfl⟩ : syracuseStep 2410031 = 3615047) B3615047
theorem B9766595 : Blo 1605001 9766595 := bstep (se 1 (by rfl) ⟨7324946, by rfl⟩ : syracuseStep 9766595 = 14649893) B14649893
theorem B34736039 : Blo 1605001 34736039 := bstep (se 1 (by rfl) ⟨26052029, by rfl⟩ : syracuseStep 34736039 = 52104059) B52104059
theorem B3614633 : Blo 1605001 3614633 := bstep (se 2 (by rfl) ⟨1355487, by rfl⟩ : syracuseStep 3614633 = 2710975) B2710975
theorem B4885235 : Blo 1605001 4885235 := bstep (se 1 (by rfl) ⟨3663926, by rfl⟩ : syracuseStep 4885235 = 7327853) B7327853
theorem B296618813 : Blo 1605001 296618813 := bstep (se 3 (by rfl) ⟨55616027, by rfl⟩ : syracuseStep 296618813 = 111232055) B111232055
theorem B126856115 : Blo 1605001 126856115 := bstep (se 1 (by rfl) ⟨95142086, by rfl⟩ : syracuseStep 126856115 = 190284173) B190284173
theorem B37104641 : Blo 1605001 37104641 := bstep (se 2 (by rfl) ⟨13914240, by rfl⟩ : syracuseStep 37104641 = 27828481) B27828481
theorem B4885633 : Blo 1605001 4885633 := bstep (se 2 (by rfl) ⟨1832112, by rfl⟩ : syracuseStep 4885633 = 3664225) B3664225
theorem B3255743 : Blo 1605001 3255743 := bstep (se 1 (by rfl) ⟨2441807, by rfl⟩ : syracuseStep 3255743 = 4883615) B4883615
theorem B21966511 : Blo 1605001 21966511 := bstep (se 1 (by rfl) ⟨16474883, by rfl⟩ : syracuseStep 21966511 = 32949767) B32949767
theorem B13192955 : Blo 1605001 13192955 := bstep (se 1 (by rfl) ⟨9894716, by rfl⟩ : syracuseStep 13192955 = 19789433) B19789433
theorem B31281061 : Blo 1605001 31281061 := bstep (se 4 (by rfl) ⟨2932599, by rfl⟩ : syracuseStep 31281061 = 5865199) B5865199
theorem B4067455 : Blo 1605001 4067455 := bstep (se 1 (by rfl) ⟨3050591, by rfl⟩ : syracuseStep 4067455 = 6101183) B6101183
theorem B4575467 : Blo 1605001 4575467 := bstep (se 1 (by rfl) ⟨3431600, by rfl⟩ : syracuseStep 4575467 = 6863201) B6863201
theorem B55619921 : Blo 1605001 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B29307365 : Blo 1605001 29307365 := bstep (se 4 (by rfl) ⟨2747565, by rfl⟩ : syracuseStep 29307365 = 5495131) B5495131
theorem B23138905 : Blo 1605001 23138905 := bstep (se 2 (by rfl) ⟨8677089, by rfl⟩ : syracuseStep 23138905 = 17354179) B17354179
theorem B7426937 : Blo 1605001 7426937 := bstep (se 2 (by rfl) ⟨2785101, by rfl⟩ : syracuseStep 7426937 = 5570203) B5570203
theorem B8680553 : Blo 1605001 8680553 := bstep (se 2 (by rfl) ⟨3255207, by rfl⟩ : syracuseStep 8680553 = 6510415) B6510415
theorem B1807807 : Blo 1605001 1807807 := bstep (se 1 (by rfl) ⟨1355855, by rfl⟩ : syracuseStep 1807807 = 2711711) B2711711
theorem B8353307 : Blo 1605001 8353307 := bstep (se 1 (by rfl) ⟨6264980, by rfl⟩ : syracuseStep 8353307 = 12529961) B12529961
theorem B61765253 : Blo 1605001 61765253 := bstep (se 4 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 61765253 = 11580985) B11580985
theorem B4118393 : Blo 1605001 4118393 := bstep (se 2 (by rfl) ⟨1544397, by rfl⟩ : syracuseStep 4118393 = 3088795) B3088795
theorem B19527689 : Blo 1605001 19527689 := bstep (se 2 (by rfl) ⟨7322883, by rfl⟩ : syracuseStep 19527689 = 14645767) B14645767
theorem B2709551 : Blo 1605001 2709551 := bstep (se 1 (by rfl) ⟨2032163, by rfl⟩ : syracuseStep 2709551 = 4064327) B4064327
theorem B5142953 : Blo 1605001 5142953 := bstep (se 2 (by rfl) ⟨1928607, by rfl⟩ : syracuseStep 5142953 = 3857215) B3857215
theorem B78109373 : Blo 1605001 78109373 := bstep (se 3 (by rfl) ⟨14645507, by rfl⟩ : syracuseStep 78109373 = 29291015) B29291015
theorem B5422247 : Blo 1605001 5422247 := bstep (se 1 (by rfl) ⟨4066685, by rfl⟩ : syracuseStep 5422247 = 8133371) B8133371
theorem B11582831 : Blo 1605001 11582831 := bstep (se 1 (by rfl) ⟨8687123, by rfl⟩ : syracuseStep 11582831 = 17374247) B17374247
theorem B1605371 : Blo 1605001 1605371 := bstep (se 1 (by rfl) ⟨1204028, by rfl⟩ : syracuseStep 1605371 = 2408057) B2408057
theorem B5423003 : Blo 1605001 5423003 := bstep (se 1 (by rfl) ⟨4067252, by rfl⟩ : syracuseStep 5423003 = 8134505) B8134505
theorem B3612635 : Blo 1605001 3612635 := bstep (se 1 (by rfl) ⟨2709476, by rfl⟩ : syracuseStep 3612635 = 5418953) B5418953
theorem B9142253 : Blo 1605001 9142253 := bstep (se 3 (by rfl) ⟨1714172, by rfl⟩ : syracuseStep 9142253 = 3428345) B3428345
theorem B2408519 : Blo 1605001 2408519 := bstep (se 1 (by rfl) ⟨1806389, by rfl⟩ : syracuseStep 2408519 = 3612779) B3612779
theorem B5423273 : Blo 1605001 5423273 := bstep (se 2 (by rfl) ⟨2033727, by rfl⟩ : syracuseStep 5423273 = 4067455) B4067455
theorem B19538243 : Blo 1605001 19538243 := bstep (se 1 (by rfl) ⟨14653682, by rfl⟩ : syracuseStep 19538243 = 29307365) B29307365
theorem B1606111 : Blo 1605001 1606111 := bstep (se 1 (by rfl) ⟨1204583, by rfl⟩ : syracuseStep 1606111 = 2409167) B2409167
theorem B21135935 : Blo 1605001 21135935 := bstep (se 1 (by rfl) ⟨15851951, by rfl⟩ : syracuseStep 21135935 = 31703903) B31703903
theorem B1606383 : Blo 1605001 1606383 := bstep (se 1 (by rfl) ⟨1204787, by rfl⟩ : syracuseStep 1606383 = 2409575) B2409575
theorem B2409215 : Blo 1605001 2409215 := bstep (se 1 (by rfl) ⟨1806911, by rfl⟩ : syracuseStep 2409215 = 3613823) B3613823
theorem B1606427 : Blo 1605001 1606427 := bstep (se 1 (by rfl) ⟨1204820, by rfl⟩ : syracuseStep 1606427 = 2409641) B2409641
theorem B30851873 : Blo 1605001 30851873 := bstep (se 2 (by rfl) ⟨11569452, by rfl⟩ : syracuseStep 30851873 = 23138905) B23138905
theorem B1606687 : Blo 1605001 1606687 := bstep (se 1 (by rfl) ⟨1205015, by rfl⟩ : syracuseStep 1606687 = 2410031) B2410031
theorem B13714541 : Blo 1605001 13714541 := bstep (se 3 (by rfl) ⟨2571476, by rfl⟩ : syracuseStep 13714541 = 5142953) B5142953
theorem B2745595 : Blo 1605001 2745595 := bstep (se 1 (by rfl) ⟨2059196, by rfl⟩ : syracuseStep 2745595 = 4118393) B4118393
theorem B2409755 : Blo 1605001 2409755 := bstep (se 1 (by rfl) ⟨1807316, by rfl⟩ : syracuseStep 2409755 = 3614633) B3614633
theorem B22275485 : Blo 1605001 22275485 := bstep (se 3 (by rfl) ⟨4176653, by rfl⟩ : syracuseStep 22275485 = 8353307) B8353307
theorem B6514177 : Blo 1605001 6514177 := bstep (se 2 (by rfl) ⟨2442816, by rfl⟩ : syracuseStep 6514177 = 4885633) B4885633
theorem B26044253 : Blo 1605001 26044253 := bstep (se 3 (by rfl) ⟨4883297, by rfl⟩ : syracuseStep 26044253 = 9766595) B9766595
theorem B2410409 : Blo 1605001 2410409 := bstep (se 2 (by rfl) ⟨903903, by rfl⟩ : syracuseStep 2410409 = 1807807) B1807807
theorem B3614831 : Blo 1605001 3614831 := bstep (se 1 (by rfl) ⟨2711123, by rfl⟩ : syracuseStep 3614831 = 5422247) B5422247
theorem B29288681 : Blo 1605001 29288681 := bstep (se 2 (by rfl) ⟨10983255, by rfl⟩ : syracuseStep 29288681 = 21966511) B21966511
theorem B41708081 : Blo 1605001 41708081 := bstep (se 2 (by rfl) ⟨15640530, by rfl⟩ : syracuseStep 41708081 = 31281061) B31281061
theorem B3615335 : Blo 1605001 3615335 := bstep (se 1 (by rfl) ⟨2711501, by rfl⟩ : syracuseStep 3615335 = 5423003) B5423003
theorem B3050311 : Blo 1605001 3050311 := bstep (se 1 (by rfl) ⟨2287733, by rfl⟩ : syracuseStep 3050311 = 4575467) B4575467
theorem B37079947 : Blo 1605001 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B3615713 : Blo 1605001 3615713 := bstep (se 2 (by rfl) ⟨1355892, by rfl⟩ : syracuseStep 3615713 = 2711785) B2711785
theorem B5787035 : Blo 1605001 5787035 := bstep (se 1 (by rfl) ⟨4340276, by rfl⟩ : syracuseStep 5787035 = 8680553) B8680553
theorem B41176835 : Blo 1605001 41176835 := bstep (se 1 (by rfl) ⟨30882626, by rfl⟩ : syracuseStep 41176835 = 61765253) B61765253
theorem B1806367 : Blo 1605001 1806367 := bstep (se 1 (by rfl) ⟨1354775, by rfl⟩ : syracuseStep 1806367 = 2709551) B2709551
theorem B52072915 : Blo 1605001 52072915 := bstep (se 1 (by rfl) ⟨39054686, by rfl⟩ : syracuseStep 52072915 = 78109373) B78109373
theorem B3256823 : Blo 1605001 3256823 := bstep (se 1 (by rfl) ⟨2442617, by rfl⟩ : syracuseStep 3256823 = 4885235) B4885235
theorem B84570743 : Blo 1605001 84570743 := bstep (se 1 (by rfl) ⟨63428057, by rfl⟩ : syracuseStep 84570743 = 126856115) B126856115
theorem B24736427 : Blo 1605001 24736427 := bstep (se 1 (by rfl) ⟨18552320, by rfl⟩ : syracuseStep 24736427 = 37104641) B37104641
theorem B7721887 : Blo 1605001 7721887 := bstep (se 1 (by rfl) ⟨5791415, by rfl⟩ : syracuseStep 7721887 = 11582831) B11582831
theorem B19805165 : Blo 1605001 19805165 := bstep (se 3 (by rfl) ⟨3713468, by rfl⟩ : syracuseStep 19805165 = 7426937) B7426937
theorem B8795303 : Blo 1605001 8795303 := bstep (se 1 (by rfl) ⟨6596477, by rfl⟩ : syracuseStep 8795303 = 13192955) B13192955
theorem B52073837 : Blo 1605001 52073837 := bstep (se 3 (by rfl) ⟨9763844, by rfl⟩ : syracuseStep 52073837 = 19527689) B19527689
theorem B5789225 : Blo 1605001 5789225 := bstep (se 2 (by rfl) ⟨2170959, by rfl⟩ : syracuseStep 5789225 = 4341919) B4341919
theorem B3430507 : Blo 1605001 3430507 := bstep (se 1 (by rfl) ⟨2572880, by rfl⟩ : syracuseStep 3430507 = 5145761) B5145761
theorem B23157359 : Blo 1605001 23157359 := bstep (se 1 (by rfl) ⟨17368019, by rfl⟩ : syracuseStep 23157359 = 34736039) B34736039
theorem B197745875 : Blo 1605001 197745875 := bstep (se 1 (by rfl) ⟨148309406, by rfl⟩ : syracuseStep 197745875 = 296618813) B296618813
theorem B2170495 : Blo 1605001 2170495 := bstep (se 1 (by rfl) ⟨1627871, by rfl⟩ : syracuseStep 2170495 = 3255743) B3255743
theorem B2408423 : Blo 1605001 2408423 := bstep (se 1 (by rfl) ⟨1806317, by rfl⟩ : syracuseStep 2408423 = 3612635) B3612635
theorem B6094835 : Blo 1605001 6094835 := bstep (se 1 (by rfl) ⟨4571126, by rfl⟩ : syracuseStep 6094835 = 9142253) B9142253
theorem B2408489 : Blo 1605001 2408489 := bstep (se 2 (by rfl) ⟨903183, by rfl⟩ : syracuseStep 2408489 = 1806367) B1806367
theorem B1605679 : Blo 1605001 1605679 := bstep (se 1 (by rfl) ⟨1204259, by rfl⟩ : syracuseStep 1605679 = 2408519) B2408519
theorem B13025495 : Blo 1605001 13025495 := bstep (se 1 (by rfl) ⟨9769121, by rfl⟩ : syracuseStep 13025495 = 19538243) B19538243
theorem B2171215 : Blo 1605001 2171215 := bstep (se 1 (by rfl) ⟨1628411, by rfl⟩ : syracuseStep 2171215 = 3256823) B3256823
theorem B16490951 : Blo 1605001 16490951 := bstep (se 1 (by rfl) ⟨12368213, by rfl⟩ : syracuseStep 16490951 = 24736427) B24736427
theorem B1606143 : Blo 1605001 1606143 := bstep (se 1 (by rfl) ⟨1204607, by rfl⟩ : syracuseStep 1606143 = 2409215) B2409215
theorem B11575973 : Blo 1605001 11575973 := bstep (se 4 (by rfl) ⟨1085247, by rfl⟩ : syracuseStep 11575973 = 2170495) B2170495
theorem B9143027 : Blo 1605001 9143027 := bstep (se 1 (by rfl) ⟨6857270, by rfl⟩ : syracuseStep 9143027 = 13714541) B13714541
theorem B1606503 : Blo 1605001 1606503 := bstep (se 1 (by rfl) ⟨1204877, by rfl⟩ : syracuseStep 1606503 = 2409755) B2409755
theorem B3859483 : Blo 1605001 3859483 := bstep (se 1 (by rfl) ⟨2894612, by rfl⟩ : syracuseStep 3859483 = 5789225) B5789225
theorem B1606939 : Blo 1605001 1606939 := bstep (se 1 (by rfl) ⟨1205204, by rfl⟩ : syracuseStep 1606939 = 2410409) B2410409
theorem B2409887 : Blo 1605001 2409887 := bstep (se 1 (by rfl) ⟨1807415, by rfl⟩ : syracuseStep 2409887 = 3614831) B3614831
theorem B56362493 : Blo 1605001 56362493 := bstep (se 3 (by rfl) ⟨10567967, by rfl⟩ : syracuseStep 56362493 = 21135935) B21135935
theorem B2410223 : Blo 1605001 2410223 := bstep (se 1 (by rfl) ⟨1807667, by rfl⟩ : syracuseStep 2410223 = 3615335) B3615335
theorem B2410475 : Blo 1605001 2410475 := bstep (se 1 (by rfl) ⟨1807856, by rfl⟩ : syracuseStep 2410475 = 3615713) B3615713
theorem B8685569 : Blo 1605001 8685569 := bstep (se 2 (by rfl) ⟨3257088, by rfl⟩ : syracuseStep 8685569 = 6514177) B6514177
theorem B3615515 : Blo 1605001 3615515 := bstep (se 1 (by rfl) ⟨2711636, by rfl⟩ : syracuseStep 3615515 = 5423273) B5423273
theorem B4574009 : Blo 1605001 4574009 := bstep (se 2 (by rfl) ⟨1715253, by rfl⟩ : syracuseStep 4574009 = 3430507) B3430507
theorem B56380495 : Blo 1605001 56380495 := bstep (se 1 (by rfl) ⟨42285371, by rfl⟩ : syracuseStep 56380495 = 84570743) B84570743
theorem B69430553 : Blo 1605001 69430553 := bstep (se 2 (by rfl) ⟨26036457, by rfl⟩ : syracuseStep 69430553 = 52072915) B52072915
theorem B4067081 : Blo 1605001 4067081 := bstep (se 2 (by rfl) ⟨1525155, by rfl⟩ : syracuseStep 4067081 = 3050311) B3050311
theorem B17362835 : Blo 1605001 17362835 := bstep (se 1 (by rfl) ⟨13022126, by rfl⟩ : syracuseStep 17362835 = 26044253) B26044253
theorem B4063223 : Blo 1605001 4063223 := bstep (se 1 (by rfl) ⟨3047417, by rfl⟩ : syracuseStep 4063223 = 6094835) B6094835
theorem B14643173 : Blo 1605001 14643173 := bstep (se 4 (by rfl) ⟨1372797, by rfl⟩ : syracuseStep 14643173 = 2745595) B2745595
theorem B19525787 : Blo 1605001 19525787 := bstep (se 1 (by rfl) ⟨14644340, by rfl⟩ : syracuseStep 19525787 = 29288681) B29288681
theorem B15438239 : Blo 1605001 15438239 := bstep (se 1 (by rfl) ⟨11578679, by rfl⟩ : syracuseStep 15438239 = 23157359) B23157359
theorem B197759717 : Blo 1605001 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B131830583 : Blo 1605001 131830583 := bstep (se 1 (by rfl) ⟨98872937, by rfl⟩ : syracuseStep 131830583 = 197745875) B197745875
theorem B20567915 : Blo 1605001 20567915 := bstep (se 1 (by rfl) ⟨15425936, by rfl⟩ : syracuseStep 20567915 = 30851873) B30851873
theorem B13203443 : Blo 1605001 13203443 := bstep (se 1 (by rfl) ⟨9902582, by rfl⟩ : syracuseStep 13203443 = 19805165) B19805165
theorem B5863535 : Blo 1605001 5863535 := bstep (se 1 (by rfl) ⟨4397651, by rfl⟩ : syracuseStep 5863535 = 8795303) B8795303
theorem B34715891 : Blo 1605001 34715891 := bstep (se 1 (by rfl) ⟨26036918, by rfl⟩ : syracuseStep 34715891 = 52073837) B52073837
theorem B14850323 : Blo 1605001 14850323 := bstep (se 1 (by rfl) ⟨11137742, by rfl⟩ : syracuseStep 14850323 = 22275485) B22275485
theorem B10295849 : Blo 1605001 10295849 := bstep (se 2 (by rfl) ⟨3860943, by rfl⟩ : syracuseStep 10295849 = 7721887) B7721887
theorem B111221549 : Blo 1605001 111221549 := bstep (se 3 (by rfl) ⟨20854040, by rfl⟩ : syracuseStep 111221549 = 41708081) B41708081
theorem B3858023 : Blo 1605001 3858023 := bstep (se 1 (by rfl) ⟨2893517, by rfl⟩ : syracuseStep 3858023 = 5787035) B5787035
theorem B27451223 : Blo 1605001 27451223 := bstep (se 1 (by rfl) ⟨20588417, by rfl⟩ : syracuseStep 27451223 = 41176835) B41176835
theorem B1605615 : Blo 1605001 1605615 := bstep (se 1 (by rfl) ⟨1204211, by rfl⟩ : syracuseStep 1605615 = 2408423) B2408423
theorem B1605659 : Blo 1605001 1605659 := bstep (se 1 (by rfl) ⟨1204244, by rfl⟩ : syracuseStep 1605659 = 2408489) B2408489
theorem B13017191 : Blo 1605001 13017191 := bstep (se 1 (by rfl) ⟨9762893, by rfl⟩ : syracuseStep 13017191 = 19525787) B19525787
theorem B10993967 : Blo 1605001 10993967 := bstep (se 1 (by rfl) ⟨8245475, by rfl⟩ : syracuseStep 10993967 = 16490951) B16490951
theorem B7717315 : Blo 1605001 7717315 := bstep (se 1 (by rfl) ⟨5787986, by rfl⟩ : syracuseStep 7717315 = 11575973) B11575973
theorem B6095351 : Blo 1605001 6095351 := bstep (se 1 (by rfl) ⟨4571513, by rfl⟩ : syracuseStep 6095351 = 9143027) B9143027
theorem B34734653 : Blo 1605001 34734653 := bstep (se 3 (by rfl) ⟨6512747, by rfl⟩ : syracuseStep 34734653 = 13025495) B13025495
theorem B1606591 : Blo 1605001 1606591 := bstep (se 1 (by rfl) ⟨1204943, by rfl⟩ : syracuseStep 1606591 = 2409887) B2409887
theorem B1606815 : Blo 1605001 1606815 := bstep (se 1 (by rfl) ⟨1205111, by rfl⟩ : syracuseStep 1606815 = 2410223) B2410223
theorem B1606983 : Blo 1605001 1606983 := bstep (se 1 (by rfl) ⟨1205237, by rfl⟩ : syracuseStep 1606983 = 2410475) B2410475
theorem B150299981 : Blo 1605001 150299981 := bstep (se 3 (by rfl) ⟨28181246, by rfl⟩ : syracuseStep 150299981 = 56362493) B56362493
theorem B5145977 : Blo 1605001 5145977 := bstep (se 2 (by rfl) ⟨1929741, by rfl⟩ : syracuseStep 5145977 = 3859483) B3859483
theorem B3909023 : Blo 1605001 3909023 := bstep (se 1 (by rfl) ⟨2931767, by rfl⟩ : syracuseStep 3909023 = 5863535) B5863535
theorem B23143927 : Blo 1605001 23143927 := bstep (se 1 (by rfl) ⟨17357945, by rfl⟩ : syracuseStep 23143927 = 34715891) B34715891
theorem B2410343 : Blo 1605001 2410343 := bstep (se 1 (by rfl) ⟨1807757, by rfl⟩ : syracuseStep 2410343 = 3615515) B3615515
theorem B74147699 : Blo 1605001 74147699 := bstep (se 1 (by rfl) ⟨55610774, by rfl⟩ : syracuseStep 74147699 = 111221549) B111221549
theorem B3049339 : Blo 1605001 3049339 := bstep (se 1 (by rfl) ⟨2287004, by rfl⟩ : syracuseStep 3049339 = 4574009) B4574009
theorem B46287035 : Blo 1605001 46287035 := bstep (se 1 (by rfl) ⟨34715276, by rfl⟩ : syracuseStep 46287035 = 69430553) B69430553
theorem B10292159 : Blo 1605001 10292159 := bstep (se 1 (by rfl) ⟨7719119, by rfl⟩ : syracuseStep 10292159 = 15438239) B15438239
theorem B2894953 : Blo 1605001 2894953 := bstep (se 2 (by rfl) ⟨1085607, by rfl⟩ : syracuseStep 2894953 = 2171215) B2171215
theorem B75173993 : Blo 1605001 75173993 := bstep (se 2 (by rfl) ⟨28190247, by rfl⟩ : syracuseStep 75173993 = 56380495) B56380495
theorem B27455597 : Blo 1605001 27455597 := bstep (se 3 (by rfl) ⟨5147924, by rfl⟩ : syracuseStep 27455597 = 10295849) B10295849
theorem B9900215 : Blo 1605001 9900215 := bstep (se 1 (by rfl) ⟨7425161, by rfl⟩ : syracuseStep 9900215 = 14850323) B14850323
theorem B351548221 : Blo 1605001 351548221 := bstep (se 3 (by rfl) ⟨65915291, by rfl⟩ : syracuseStep 351548221 = 131830583) B131830583
theorem B9762115 : Blo 1605001 9762115 := bstep (se 1 (by rfl) ⟨7321586, by rfl⟩ : syracuseStep 9762115 = 14643173) B14643173
theorem B2708815 : Blo 1605001 2708815 := bstep (se 1 (by rfl) ⟨2031611, by rfl⟩ : syracuseStep 2708815 = 4063223) B4063223
theorem B131839811 : Blo 1605001 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B13711943 : Blo 1605001 13711943 := bstep (se 1 (by rfl) ⟨10283957, by rfl⟩ : syracuseStep 13711943 = 20567915) B20567915
theorem B5790379 : Blo 1605001 5790379 := bstep (se 1 (by rfl) ⟨4342784, by rfl⟩ : syracuseStep 5790379 = 8685569) B8685569
theorem B2572015 : Blo 1605001 2572015 := bstep (se 1 (by rfl) ⟨1929011, by rfl⟩ : syracuseStep 2572015 = 3858023) B3858023
theorem B2711387 : Blo 1605001 2711387 := bstep (se 1 (by rfl) ⟨2033540, by rfl⟩ : syracuseStep 2711387 = 4067081) B4067081
theorem B18300815 : Blo 1605001 18300815 := bstep (se 1 (by rfl) ⟨13725611, by rfl⟩ : syracuseStep 18300815 = 27451223) B27451223
theorem B11575223 : Blo 1605001 11575223 := bstep (se 1 (by rfl) ⟨8681417, by rfl⟩ : syracuseStep 11575223 = 17362835) B17362835
theorem B35209181 : Blo 1605001 35209181 := bstep (se 3 (by rfl) ⟨6601721, by rfl⟩ : syracuseStep 35209181 = 13203443) B13203443
theorem B4063567 : Blo 1605001 4063567 := bstep (se 1 (by rfl) ⟨3047675, by rfl⟩ : syracuseStep 4063567 = 6095351) B6095351
theorem B10289753 : Blo 1605001 10289753 := bstep (se 2 (by rfl) ⟨3858657, by rfl⟩ : syracuseStep 10289753 = 7717315) B7717315
theorem B2606015 : Blo 1605001 2606015 := bstep (se 1 (by rfl) ⟨1954511, by rfl⟩ : syracuseStep 2606015 = 3909023) B3909023
theorem B13722605 : Blo 1605001 13722605 := bstep (se 3 (by rfl) ⟨2572988, by rfl⟩ : syracuseStep 13722605 = 5145977) B5145977
theorem B468730961 : Blo 1605001 468730961 := bstep (se 2 (by rfl) ⟨175774110, by rfl⟩ : syracuseStep 468730961 = 351548221) B351548221
theorem B87893207 : Blo 1605001 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B1606895 : Blo 1605001 1606895 := bstep (se 1 (by rfl) ⟨1205171, by rfl⟩ : syracuseStep 1606895 = 2410343) B2410343
theorem B49431799 : Blo 1605001 49431799 := bstep (se 1 (by rfl) ⟨37073849, by rfl⟩ : syracuseStep 49431799 = 74147699) B74147699
theorem B3859937 : Blo 1605001 3859937 := bstep (se 2 (by rfl) ⟨1447476, by rfl⟩ : syracuseStep 3859937 = 2894953) B2894953
theorem B4065785 : Blo 1605001 4065785 := bstep (se 2 (by rfl) ⟨1524669, by rfl⟩ : syracuseStep 4065785 = 3049339) B3049339
theorem B12200543 : Blo 1605001 12200543 := bstep (se 1 (by rfl) ⟨9150407, by rfl⟩ : syracuseStep 12200543 = 18300815) B18300815
theorem B23472787 : Blo 1605001 23472787 := bstep (se 1 (by rfl) ⟨17604590, by rfl⟩ : syracuseStep 23472787 = 35209181) B35209181
theorem B18303731 : Blo 1605001 18303731 := bstep (se 1 (by rfl) ⟨13727798, by rfl⟩ : syracuseStep 18303731 = 27455597) B27455597
theorem B34712509 : Blo 1605001 34712509 := bstep (se 3 (by rfl) ⟨6508595, by rfl⟩ : syracuseStep 34712509 = 13017191) B13017191
theorem B100199987 : Blo 1605001 100199987 := bstep (se 1 (by rfl) ⟨75149990, by rfl⟩ : syracuseStep 100199987 = 150299981) B150299981
theorem B7720505 : Blo 1605001 7720505 := bstep (se 2 (by rfl) ⟨2895189, by rfl⟩ : syracuseStep 7720505 = 5790379) B5790379
theorem B6861439 : Blo 1605001 6861439 := bstep (se 1 (by rfl) ⟨5146079, by rfl⟩ : syracuseStep 6861439 = 10292159) B10292159
theorem B3429353 : Blo 1605001 3429353 := bstep (se 2 (by rfl) ⟨1286007, by rfl⟩ : syracuseStep 3429353 = 2572015) B2572015
theorem B1807591 : Blo 1605001 1807591 := bstep (se 1 (by rfl) ⟨1355693, by rfl⟩ : syracuseStep 1807591 = 2711387) B2711387
theorem B50115995 : Blo 1605001 50115995 := bstep (se 1 (by rfl) ⟨37586996, by rfl⟩ : syracuseStep 50115995 = 75173993) B75173993
theorem B6600143 : Blo 1605001 6600143 := bstep (se 1 (by rfl) ⟨4950107, by rfl⟩ : syracuseStep 6600143 = 9900215) B9900215
theorem B7329311 : Blo 1605001 7329311 := bstep (se 1 (by rfl) ⟨5496983, by rfl⟩ : syracuseStep 7329311 = 10993967) B10993967
theorem B23156435 : Blo 1605001 23156435 := bstep (se 1 (by rfl) ⟨17367326, by rfl⟩ : syracuseStep 23156435 = 34734653) B34734653
theorem B30858023 : Blo 1605001 30858023 := bstep (se 1 (by rfl) ⟨23143517, by rfl⟩ : syracuseStep 30858023 = 46287035) B46287035
theorem B9141295 : Blo 1605001 9141295 := bstep (se 1 (by rfl) ⟨6855971, by rfl⟩ : syracuseStep 9141295 = 13711943) B13711943
theorem B13016153 : Blo 1605001 13016153 := bstep (se 2 (by rfl) ⟨4881057, by rfl⟩ : syracuseStep 13016153 = 9762115) B9762115
theorem B3611753 : Blo 1605001 3611753 := bstep (se 2 (by rfl) ⟨1354407, by rfl⟩ : syracuseStep 3611753 = 2708815) B2708815
theorem B30858569 : Blo 1605001 30858569 := bstep (se 2 (by rfl) ⟨11571963, by rfl⟩ : syracuseStep 30858569 = 23143927) B23143927
theorem B7716815 : Blo 1605001 7716815 := bstep (se 1 (by rfl) ⟨5787611, by rfl⟩ : syracuseStep 7716815 = 11575223) B11575223
theorem B34709741 : Blo 1605001 34709741 := bstep (se 3 (by rfl) ⟨6508076, by rfl⟩ : syracuseStep 34709741 = 13016153) B13016153
theorem B2286235 : Blo 1605001 2286235 := bstep (se 1 (by rfl) ⟨1714676, by rfl⟩ : syracuseStep 2286235 = 3429353) B3429353
theorem B2573291 : Blo 1605001 2573291 := bstep (se 1 (by rfl) ⟨1929968, by rfl⟩ : syracuseStep 2573291 = 3859937) B3859937
theorem B2410121 : Blo 1605001 2410121 := bstep (se 2 (by rfl) ⟨903795, by rfl⟩ : syracuseStep 2410121 = 1807591) B1807591
theorem B20572015 : Blo 1605001 20572015 := bstep (se 1 (by rfl) ⟨15429011, by rfl⟩ : syracuseStep 20572015 = 30858023) B30858023
theorem B20572379 : Blo 1605001 20572379 := bstep (se 1 (by rfl) ⟨15429284, by rfl⟩ : syracuseStep 20572379 = 30858569) B30858569
theorem B66799991 : Blo 1605001 66799991 := bstep (se 1 (by rfl) ⟨50099993, by rfl⟩ : syracuseStep 66799991 = 100199987) B100199987
theorem B5147003 : Blo 1605001 5147003 := bstep (se 1 (by rfl) ⟨3860252, by rfl⟩ : syracuseStep 5147003 = 7720505) B7720505
theorem B6949373 : Blo 1605001 6949373 := bstep (se 3 (by rfl) ⟨1303007, by rfl⟩ : syracuseStep 6949373 = 2606015) B2606015
theorem B6859835 : Blo 1605001 6859835 := bstep (se 1 (by rfl) ⟨5144876, by rfl⟩ : syracuseStep 6859835 = 10289753) B10289753
theorem B5418089 : Blo 1605001 5418089 := bstep (se 2 (by rfl) ⟨2031783, by rfl⟩ : syracuseStep 5418089 = 4063567) B4063567
theorem B312487307 : Blo 1605001 312487307 := bstep (se 1 (by rfl) ⟨234365480, by rfl⟩ : syracuseStep 312487307 = 468730961) B468730961
theorem B31297049 : Blo 1605001 31297049 := bstep (se 2 (by rfl) ⟨11736393, by rfl⟩ : syracuseStep 31297049 = 23472787) B23472787
theorem B33410663 : Blo 1605001 33410663 := bstep (se 1 (by rfl) ⟨25057997, by rfl⟩ : syracuseStep 33410663 = 50115995) B50115995
theorem B4886207 : Blo 1605001 4886207 := bstep (se 1 (by rfl) ⟨3664655, by rfl⟩ : syracuseStep 4886207 = 7329311) B7329311
theorem B15437623 : Blo 1605001 15437623 := bstep (se 1 (by rfl) ⟨11578217, by rfl⟩ : syracuseStep 15437623 = 23156435) B23156435
theorem B17600381 : Blo 1605001 17600381 := bstep (se 3 (by rfl) ⟨3300071, by rfl⟩ : syracuseStep 17600381 = 6600143) B6600143
theorem B65909065 : Blo 1605001 65909065 := bstep (se 2 (by rfl) ⟨24715899, by rfl⟩ : syracuseStep 65909065 = 49431799) B49431799
theorem B12202487 : Blo 1605001 12202487 := bstep (se 1 (by rfl) ⟨9151865, by rfl⟩ : syracuseStep 12202487 = 18303731) B18303731
theorem B9148403 : Blo 1605001 9148403 := bstep (se 1 (by rfl) ⟨6861302, by rfl⟩ : syracuseStep 9148403 = 13722605) B13722605
theorem B58595471 : Blo 1605001 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B9148585 : Blo 1605001 9148585 := bstep (se 2 (by rfl) ⟨3430719, by rfl⟩ : syracuseStep 9148585 = 6861439) B6861439
theorem B46283345 : Blo 1605001 46283345 := bstep (se 2 (by rfl) ⟨17356254, by rfl⟩ : syracuseStep 46283345 = 34712509) B34712509
theorem B12188393 : Blo 1605001 12188393 := bstep (se 2 (by rfl) ⟨4570647, by rfl⟩ : syracuseStep 12188393 = 9141295) B9141295
theorem B2710523 : Blo 1605001 2710523 := bstep (se 1 (by rfl) ⟨2032892, by rfl⟩ : syracuseStep 2710523 = 4065785) B4065785
theorem B8133695 : Blo 1605001 8133695 := bstep (se 1 (by rfl) ⟨6100271, by rfl⟩ : syracuseStep 8133695 = 12200543) B12200543
theorem B2407835 : Blo 1605001 2407835 := bstep (se 1 (by rfl) ⟨1805876, by rfl⟩ : syracuseStep 2407835 = 3611753) B3611753
theorem B5144543 : Blo 1605001 5144543 := bstep (se 1 (by rfl) ⟨3858407, by rfl⟩ : syracuseStep 5144543 = 7716815) B7716815
theorem B12198113 : Blo 1605001 12198113 := bstep (se 2 (by rfl) ⟨4574292, by rfl⟩ : syracuseStep 12198113 = 9148585) B9148585
theorem B1606747 : Blo 1605001 1606747 := bstep (se 1 (by rfl) ⟨1205060, by rfl⟩ : syracuseStep 1606747 = 2410121) B2410121
theorem B18531661 : Blo 1605001 18531661 := bstep (se 3 (by rfl) ⟨3474686, by rfl⟩ : syracuseStep 18531661 = 6949373) B6949373
theorem B13714919 : Blo 1605001 13714919 := bstep (se 1 (by rfl) ⟨10286189, by rfl⟩ : syracuseStep 13714919 = 20572379) B20572379
theorem B44533327 : Blo 1605001 44533327 := bstep (se 1 (by rfl) ⟨33399995, by rfl⟩ : syracuseStep 44533327 = 66799991) B66799991
theorem B8134991 : Blo 1605001 8134991 := bstep (se 1 (by rfl) ⟨6101243, by rfl⟩ : syracuseStep 8134991 = 12202487) B12202487
theorem B4573223 : Blo 1605001 4573223 := bstep (se 1 (by rfl) ⟨3429917, by rfl⟩ : syracuseStep 4573223 = 6859835) B6859835
theorem B208324871 : Blo 1605001 208324871 := bstep (se 1 (by rfl) ⟨156243653, by rfl⟩ : syracuseStep 208324871 = 312487307) B312487307
theorem B27429353 : Blo 1605001 27429353 := bstep (se 2 (by rfl) ⟨10286007, by rfl⟩ : syracuseStep 27429353 = 20572015) B20572015
theorem B11733587 : Blo 1605001 11733587 := bstep (se 1 (by rfl) ⟨8800190, by rfl⟩ : syracuseStep 11733587 = 17600381) B17600381
theorem B87878753 : Blo 1605001 87878753 := bstep (se 2 (by rfl) ⟨32954532, by rfl⟩ : syracuseStep 87878753 = 65909065) B65909065
theorem B1715527 : Blo 1605001 1715527 := bstep (se 1 (by rfl) ⟨1286645, by rfl⟩ : syracuseStep 1715527 = 2573291) B2573291
theorem B12193253 : Blo 1605001 12193253 := bstep (se 4 (by rfl) ⟨1143117, by rfl⟩ : syracuseStep 12193253 = 2286235) B2286235
theorem B6098935 : Blo 1605001 6098935 := bstep (se 1 (by rfl) ⟨4574201, by rfl⟩ : syracuseStep 6098935 = 9148403) B9148403
theorem B39063647 : Blo 1605001 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B30855563 : Blo 1605001 30855563 := bstep (se 1 (by rfl) ⟨23141672, by rfl⟩ : syracuseStep 30855563 = 46283345) B46283345
theorem B1807015 : Blo 1605001 1807015 := bstep (se 1 (by rfl) ⟨1355261, by rfl⟩ : syracuseStep 1807015 = 2710523) B2710523
theorem B20583497 : Blo 1605001 20583497 := bstep (se 2 (by rfl) ⟨7718811, by rfl⟩ : syracuseStep 20583497 = 15437623) B15437623
theorem B3257471 : Blo 1605001 3257471 := bstep (se 1 (by rfl) ⟨2443103, by rfl⟩ : syracuseStep 3257471 = 4886207) B4886207
theorem B3429695 : Blo 1605001 3429695 := bstep (se 1 (by rfl) ⟨2572271, by rfl⟩ : syracuseStep 3429695 = 5144543) B5144543
theorem B23139827 : Blo 1605001 23139827 := bstep (se 1 (by rfl) ⟨17354870, by rfl⟩ : syracuseStep 23139827 = 34709741) B34709741
theorem B3431335 : Blo 1605001 3431335 := bstep (se 1 (by rfl) ⟨2573501, by rfl⟩ : syracuseStep 3431335 = 5147003) B5147003
theorem B8125595 : Blo 1605001 8125595 := bstep (se 1 (by rfl) ⟨6094196, by rfl⟩ : syracuseStep 8125595 = 12188393) B12188393
theorem B5422463 : Blo 1605001 5422463 := bstep (se 1 (by rfl) ⟨4066847, by rfl⟩ : syracuseStep 5422463 = 8133695) B8133695
theorem B3612059 : Blo 1605001 3612059 := bstep (se 1 (by rfl) ⟨2709044, by rfl⟩ : syracuseStep 3612059 = 5418089) B5418089
theorem B1605223 : Blo 1605001 1605223 := bstep (se 1 (by rfl) ⟨1203917, by rfl⟩ : syracuseStep 1605223 = 2407835) B2407835
theorem B20864699 : Blo 1605001 20864699 := bstep (se 1 (by rfl) ⟨15648524, by rfl⟩ : syracuseStep 20864699 = 31297049) B31297049
theorem B22273775 : Blo 1605001 22273775 := bstep (se 1 (by rfl) ⟨16705331, by rfl⟩ : syracuseStep 22273775 = 33410663) B33410663
theorem B26042431 : Blo 1605001 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B5423327 : Blo 1605001 5423327 := bstep (se 1 (by rfl) ⟨4067495, by rfl⟩ : syracuseStep 5423327 = 8134991) B8134991
theorem B20570375 : Blo 1605001 20570375 := bstep (se 1 (by rfl) ⟨15427781, by rfl⟩ : syracuseStep 20570375 = 30855563) B30855563
theorem B13722331 : Blo 1605001 13722331 := bstep (se 1 (by rfl) ⟨10291748, by rfl⟩ : syracuseStep 13722331 = 20583497) B20583497
theorem B2171647 : Blo 1605001 2171647 := bstep (se 1 (by rfl) ⟨1628735, by rfl⟩ : syracuseStep 2171647 = 3257471) B3257471
theorem B2286463 : Blo 1605001 2286463 := bstep (se 1 (by rfl) ⟨1714847, by rfl⟩ : syracuseStep 2286463 = 3429695) B3429695
theorem B2409353 : Blo 1605001 2409353 := bstep (se 2 (by rfl) ⟨903507, by rfl⟩ : syracuseStep 2409353 = 1807015) B1807015
theorem B9143279 : Blo 1605001 9143279 := bstep (se 1 (by rfl) ⟨6857459, by rfl⟩ : syracuseStep 9143279 = 13714919) B13714919
theorem B15426551 : Blo 1605001 15426551 := bstep (se 1 (by rfl) ⟨11569913, by rfl⟩ : syracuseStep 15426551 = 23139827) B23139827
theorem B3048815 : Blo 1605001 3048815 := bstep (se 1 (by rfl) ⟨2286611, by rfl⟩ : syracuseStep 3048815 = 4573223) B4573223
theorem B18286235 : Blo 1605001 18286235 := bstep (se 1 (by rfl) ⟨13714676, by rfl⟩ : syracuseStep 18286235 = 27429353) B27429353
theorem B2287369 : Blo 1605001 2287369 := bstep (se 2 (by rfl) ⟨857763, by rfl⟩ : syracuseStep 2287369 = 1715527) B1715527
theorem B24708881 : Blo 1605001 24708881 := bstep (se 2 (by rfl) ⟨9265830, by rfl⟩ : syracuseStep 24708881 = 18531661) B18531661
theorem B5417063 : Blo 1605001 5417063 := bstep (se 1 (by rfl) ⟨4062797, by rfl⟩ : syracuseStep 5417063 = 8125595) B8125595
theorem B59377769 : Blo 1605001 59377769 := bstep (se 2 (by rfl) ⟨22266663, by rfl⟩ : syracuseStep 59377769 = 44533327) B44533327
theorem B3614975 : Blo 1605001 3614975 := bstep (se 1 (by rfl) ⟨2711231, by rfl⟩ : syracuseStep 3614975 = 5422463) B5422463
theorem B8128835 : Blo 1605001 8128835 := bstep (se 1 (by rfl) ⟨6096626, by rfl⟩ : syracuseStep 8128835 = 12193253) B12193253
theorem B4575113 : Blo 1605001 4575113 := bstep (se 2 (by rfl) ⟨1715667, by rfl⟩ : syracuseStep 4575113 = 3431335) B3431335
theorem B138883247 : Blo 1605001 138883247 := bstep (se 1 (by rfl) ⟨104162435, by rfl⟩ : syracuseStep 138883247 = 208324871) B208324871
theorem B58585835 : Blo 1605001 58585835 := bstep (se 1 (by rfl) ⟨43939376, by rfl⟩ : syracuseStep 58585835 = 87878753) B87878753
theorem B14849183 : Blo 1605001 14849183 := bstep (se 1 (by rfl) ⟨11136887, by rfl⟩ : syracuseStep 14849183 = 22273775) B22273775
theorem B8131913 : Blo 1605001 8131913 := bstep (se 2 (by rfl) ⟨3049467, by rfl⟩ : syracuseStep 8131913 = 6098935) B6098935
theorem B8132075 : Blo 1605001 8132075 := bstep (se 1 (by rfl) ⟨6099056, by rfl⟩ : syracuseStep 8132075 = 12198113) B12198113
theorem B7822391 : Blo 1605001 7822391 := bstep (se 1 (by rfl) ⟨5866793, by rfl⟩ : syracuseStep 7822391 = 11733587) B11733587
theorem B2408039 : Blo 1605001 2408039 := bstep (se 1 (by rfl) ⟨1806029, by rfl⟩ : syracuseStep 2408039 = 3612059) B3612059
theorem B13909799 : Blo 1605001 13909799 := bstep (se 1 (by rfl) ⟨10432349, by rfl⟩ : syracuseStep 13909799 = 20864699) B20864699
theorem B13713583 : Blo 1605001 13713583 := bstep (se 1 (by rfl) ⟨10285187, by rfl⟩ : syracuseStep 13713583 = 20570375) B20570375
theorem B1606235 : Blo 1605001 1606235 := bstep (se 1 (by rfl) ⟨1204676, by rfl⟩ : syracuseStep 1606235 = 2409353) B2409353
theorem B6095519 : Blo 1605001 6095519 := bstep (se 1 (by rfl) ⟨4571639, by rfl⟩ : syracuseStep 6095519 = 9143279) B9143279
theorem B2032543 : Blo 1605001 2032543 := bstep (se 1 (by rfl) ⟨1524407, by rfl⟩ : syracuseStep 2032543 = 3048815) B3048815
theorem B12190823 : Blo 1605001 12190823 := bstep (se 1 (by rfl) ⟨9143117, by rfl⟩ : syracuseStep 12190823 = 18286235) B18286235
theorem B3048617 : Blo 1605001 3048617 := bstep (se 2 (by rfl) ⟨1143231, by rfl⟩ : syracuseStep 3048617 = 2286463) B2286463
theorem B39585179 : Blo 1605001 39585179 := bstep (se 1 (by rfl) ⟨29688884, by rfl⟩ : syracuseStep 39585179 = 59377769) B59377769
theorem B2409983 : Blo 1605001 2409983 := bstep (se 1 (by rfl) ⟨1807487, by rfl⟩ : syracuseStep 2409983 = 3614975) B3614975
theorem B3049825 : Blo 1605001 3049825 := bstep (se 2 (by rfl) ⟨1143684, by rfl⟩ : syracuseStep 3049825 = 2287369) B2287369
theorem B3050075 : Blo 1605001 3050075 := bstep (se 1 (by rfl) ⟨2287556, by rfl⟩ : syracuseStep 3050075 = 4575113) B4575113
theorem B92588831 : Blo 1605001 92588831 := bstep (se 1 (by rfl) ⟨69441623, by rfl⟩ : syracuseStep 92588831 = 138883247) B138883247
theorem B20859709 : Blo 1605001 20859709 := bstep (se 3 (by rfl) ⟨3911195, by rfl⟩ : syracuseStep 20859709 = 7822391) B7822391
theorem B3615551 : Blo 1605001 3615551 := bstep (se 1 (by rfl) ⟨2711663, by rfl⟩ : syracuseStep 3615551 = 5423327) B5423327
theorem B18296441 : Blo 1605001 18296441 := bstep (se 2 (by rfl) ⟨6861165, by rfl⟩ : syracuseStep 18296441 = 13722331) B13722331
theorem B2895529 : Blo 1605001 2895529 := bstep (se 2 (by rfl) ⟨1085823, by rfl⟩ : syracuseStep 2895529 = 2171647) B2171647
theorem B5419223 : Blo 1605001 5419223 := bstep (se 1 (by rfl) ⟨4064417, by rfl⟩ : syracuseStep 5419223 = 8128835) B8128835
theorem B41137469 : Blo 1605001 41137469 := bstep (se 3 (by rfl) ⟨7713275, by rfl⟩ : syracuseStep 41137469 = 15426551) B15426551
theorem B34723241 : Blo 1605001 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B39597821 : Blo 1605001 39597821 := bstep (se 3 (by rfl) ⟨7424591, by rfl⟩ : syracuseStep 39597821 = 14849183) B14849183
theorem B39057223 : Blo 1605001 39057223 := bstep (se 1 (by rfl) ⟨29292917, by rfl⟩ : syracuseStep 39057223 = 58585835) B58585835
theorem B5421275 : Blo 1605001 5421275 := bstep (se 1 (by rfl) ⟨4065956, by rfl⟩ : syracuseStep 5421275 = 8131913) B8131913
theorem B5421383 : Blo 1605001 5421383 := bstep (se 1 (by rfl) ⟨4066037, by rfl⟩ : syracuseStep 5421383 = 8132075) B8132075
theorem B16472587 : Blo 1605001 16472587 := bstep (se 1 (by rfl) ⟨12354440, by rfl⟩ : syracuseStep 16472587 = 24708881) B24708881
theorem B3611375 : Blo 1605001 3611375 := bstep (se 1 (by rfl) ⟨2708531, by rfl⟩ : syracuseStep 3611375 = 5417063) B5417063
theorem B1605359 : Blo 1605001 1605359 := bstep (se 1 (by rfl) ⟨1204019, by rfl⟩ : syracuseStep 1605359 = 2408039) B2408039
theorem B9273199 : Blo 1605001 9273199 := bstep (se 1 (by rfl) ⟨6954899, by rfl⟩ : syracuseStep 9273199 = 13909799) B13909799
theorem B3612815 : Blo 1605001 3612815 := bstep (se 1 (by rfl) ⟨2709611, by rfl⟩ : syracuseStep 3612815 = 5419223) B5419223
theorem B18284777 : Blo 1605001 18284777 := bstep (se 2 (by rfl) ⟨6856791, by rfl⟩ : syracuseStep 18284777 = 13713583) B13713583
theorem B4063679 : Blo 1605001 4063679 := bstep (se 1 (by rfl) ⟨3047759, by rfl⟩ : syracuseStep 4063679 = 6095519) B6095519
theorem B21963449 : Blo 1605001 21963449 := bstep (se 2 (by rfl) ⟨8236293, by rfl⟩ : syracuseStep 21963449 = 16472587) B16472587
theorem B8127215 : Blo 1605001 8127215 := bstep (se 1 (by rfl) ⟨6095411, by rfl⟩ : syracuseStep 8127215 = 12190823) B12190823
theorem B1606655 : Blo 1605001 1606655 := bstep (se 1 (by rfl) ⟨1204991, by rfl⟩ : syracuseStep 1606655 = 2409983) B2409983
theorem B27812945 : Blo 1605001 27812945 := bstep (se 2 (by rfl) ⟨10429854, by rfl⟩ : syracuseStep 27812945 = 20859709) B20859709
theorem B3614183 : Blo 1605001 3614183 := bstep (se 1 (by rfl) ⟨2710637, by rfl⟩ : syracuseStep 3614183 = 5421275) B5421275
theorem B3614255 : Blo 1605001 3614255 := bstep (se 1 (by rfl) ⟨2710691, by rfl⟩ : syracuseStep 3614255 = 5421383) B5421383
theorem B2410367 : Blo 1605001 2410367 := bstep (se 1 (by rfl) ⟨1807775, by rfl⟩ : syracuseStep 2410367 = 3615551) B3615551
theorem B3860705 : Blo 1605001 3860705 := bstep (se 2 (by rfl) ⟨1447764, by rfl⟩ : syracuseStep 3860705 = 2895529) B2895529
theorem B12364265 : Blo 1605001 12364265 := bstep (se 2 (by rfl) ⟨4636599, by rfl⟩ : syracuseStep 12364265 = 9273199) B9273199
theorem B8129645 : Blo 1605001 8129645 := bstep (se 3 (by rfl) ⟨1524308, by rfl⟩ : syracuseStep 8129645 = 3048617) B3048617
theorem B4066433 : Blo 1605001 4066433 := bstep (se 2 (by rfl) ⟨1524912, by rfl⟩ : syracuseStep 4066433 = 3049825) B3049825
theorem B26390119 : Blo 1605001 26390119 := bstep (se 1 (by rfl) ⟨19792589, by rfl⟩ : syracuseStep 26390119 = 39585179) B39585179
theorem B26398547 : Blo 1605001 26398547 := bstep (se 1 (by rfl) ⟨19798910, by rfl⟩ : syracuseStep 26398547 = 39597821) B39597821
theorem B27424979 : Blo 1605001 27424979 := bstep (se 1 (by rfl) ⟨20568734, by rfl⟩ : syracuseStep 27424979 = 41137469) B41137469
theorem B23148827 : Blo 1605001 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B2710057 : Blo 1605001 2710057 := bstep (se 2 (by rfl) ⟨1016271, by rfl⟩ : syracuseStep 2710057 = 2032543) B2032543
theorem B8133533 : Blo 1605001 8133533 := bstep (se 3 (by rfl) ⟨1525037, by rfl⟩ : syracuseStep 8133533 = 3050075) B3050075
theorem B2407583 : Blo 1605001 2407583 := bstep (se 1 (by rfl) ⟨1805687, by rfl⟩ : syracuseStep 2407583 = 3611375) B3611375
theorem B61725887 : Blo 1605001 61725887 := bstep (se 1 (by rfl) ⟨46294415, by rfl⟩ : syracuseStep 61725887 = 92588831) B92588831
theorem B12197627 : Blo 1605001 12197627 := bstep (se 1 (by rfl) ⟨9148220, by rfl⟩ : syracuseStep 12197627 = 18296441) B18296441
theorem B52076297 : Blo 1605001 52076297 := bstep (se 2 (by rfl) ⟨19528611, by rfl⟩ : syracuseStep 52076297 = 39057223) B39057223
theorem B2408543 : Blo 1605001 2408543 := bstep (se 1 (by rfl) ⟨1806407, by rfl⟩ : syracuseStep 2408543 = 3612815) B3612815
theorem B12189851 : Blo 1605001 12189851 := bstep (se 1 (by rfl) ⟨9142388, by rfl⟩ : syracuseStep 12189851 = 18284777) B18284777
theorem B3613409 : Blo 1605001 3613409 := bstep (se 2 (by rfl) ⟨1355028, by rfl⟩ : syracuseStep 3613409 = 2710057) B2710057
theorem B2409455 : Blo 1605001 2409455 := bstep (se 1 (by rfl) ⟨1807091, by rfl⟩ : syracuseStep 2409455 = 3614183) B3614183
theorem B2409503 : Blo 1605001 2409503 := bstep (se 1 (by rfl) ⟨1807127, by rfl⟩ : syracuseStep 2409503 = 3614255) B3614255
theorem B1606911 : Blo 1605001 1606911 := bstep (se 1 (by rfl) ⟨1205183, by rfl⟩ : syracuseStep 1606911 = 2410367) B2410367
theorem B2573803 : Blo 1605001 2573803 := bstep (se 1 (by rfl) ⟨1930352, by rfl⟩ : syracuseStep 2573803 = 3860705) B3860705
theorem B41150591 : Blo 1605001 41150591 := bstep (se 1 (by rfl) ⟨30862943, by rfl⟩ : syracuseStep 41150591 = 61725887) B61725887
theorem B35186825 : Blo 1605001 35186825 := bstep (se 2 (by rfl) ⟨13195059, by rfl⟩ : syracuseStep 35186825 = 26390119) B26390119
theorem B17599031 : Blo 1605001 17599031 := bstep (se 1 (by rfl) ⟨13199273, by rfl⟩ : syracuseStep 17599031 = 26398547) B26398547
theorem B14642299 : Blo 1605001 14642299 := bstep (se 1 (by rfl) ⟨10981724, by rfl⟩ : syracuseStep 14642299 = 21963449) B21963449
theorem B5418143 : Blo 1605001 5418143 := bstep (se 1 (by rfl) ⟨4063607, by rfl⟩ : syracuseStep 5418143 = 8127215) B8127215
theorem B18541963 : Blo 1605001 18541963 := bstep (se 1 (by rfl) ⟨13906472, by rfl⟩ : syracuseStep 18541963 = 27812945) B27812945
theorem B5419763 : Blo 1605001 5419763 := bstep (se 1 (by rfl) ⟨4064822, by rfl⟩ : syracuseStep 5419763 = 8129645) B8129645
theorem B8131751 : Blo 1605001 8131751 := bstep (se 1 (by rfl) ⟨6098813, by rfl⟩ : syracuseStep 8131751 = 12197627) B12197627
theorem B2709119 : Blo 1605001 2709119 := bstep (se 1 (by rfl) ⟨2031839, by rfl⟩ : syracuseStep 2709119 = 4063679) B4063679
theorem B32971373 : Blo 1605001 32971373 := bstep (se 3 (by rfl) ⟨6182132, by rfl⟩ : syracuseStep 32971373 = 12364265) B12364265
theorem B18283319 : Blo 1605001 18283319 := bstep (se 1 (by rfl) ⟨13712489, by rfl⟩ : syracuseStep 18283319 = 27424979) B27424979
theorem B15432551 : Blo 1605001 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B5422355 : Blo 1605001 5422355 := bstep (se 1 (by rfl) ⟨4066766, by rfl⟩ : syracuseStep 5422355 = 8133533) B8133533
theorem B2710955 : Blo 1605001 2710955 := bstep (se 1 (by rfl) ⟨2033216, by rfl⟩ : syracuseStep 2710955 = 4066433) B4066433
theorem B1605055 : Blo 1605001 1605055 := bstep (se 1 (by rfl) ⟨1203791, by rfl⟩ : syracuseStep 1605055 = 2407583) B2407583
theorem B34717531 : Blo 1605001 34717531 := bstep (se 1 (by rfl) ⟨26038148, by rfl⟩ : syracuseStep 34717531 = 52076297) B52076297
theorem B1605695 : Blo 1605001 1605695 := bstep (se 1 (by rfl) ⟨1204271, by rfl⟩ : syracuseStep 1605695 = 2408543) B2408543
theorem B8126567 : Blo 1605001 8126567 := bstep (se 1 (by rfl) ⟨6094925, by rfl⟩ : syracuseStep 8126567 = 12189851) B12189851
theorem B2408939 : Blo 1605001 2408939 := bstep (se 1 (by rfl) ⟨1806704, by rfl⟩ : syracuseStep 2408939 = 3613409) B3613409
theorem B3613175 : Blo 1605001 3613175 := bstep (se 1 (by rfl) ⟨2709881, by rfl⟩ : syracuseStep 3613175 = 5419763) B5419763
theorem B1606303 : Blo 1605001 1606303 := bstep (se 1 (by rfl) ⟨1204727, by rfl⟩ : syracuseStep 1606303 = 2409455) B2409455
theorem B1606335 : Blo 1605001 1606335 := bstep (se 1 (by rfl) ⟨1204751, by rfl⟩ : syracuseStep 1606335 = 2409503) B2409503
theorem B19523065 : Blo 1605001 19523065 := bstep (se 2 (by rfl) ⟨7321149, by rfl⟩ : syracuseStep 19523065 = 14642299) B14642299
theorem B11732687 : Blo 1605001 11732687 := bstep (se 1 (by rfl) ⟨8799515, by rfl⟩ : syracuseStep 11732687 = 17599031) B17599031
theorem B21980915 : Blo 1605001 21980915 := bstep (se 1 (by rfl) ⟨16485686, by rfl⟩ : syracuseStep 21980915 = 32971373) B32971373
theorem B3614903 : Blo 1605001 3614903 := bstep (se 1 (by rfl) ⟨2711177, by rfl⟩ : syracuseStep 3614903 = 5422355) B5422355
theorem B1806079 : Blo 1605001 1806079 := bstep (se 1 (by rfl) ⟨1354559, by rfl⟩ : syracuseStep 1806079 = 2709119) B2709119
theorem B23457883 : Blo 1605001 23457883 := bstep (se 1 (by rfl) ⟨17593412, by rfl⟩ : syracuseStep 23457883 = 35186825) B35186825
theorem B98890469 : Blo 1605001 98890469 := bstep (se 4 (by rfl) ⟨9270981, by rfl⟩ : syracuseStep 98890469 = 18541963) B18541963
theorem B1807303 : Blo 1605001 1807303 := bstep (se 1 (by rfl) ⟨1355477, by rfl⟩ : syracuseStep 1807303 = 2710955) B2710955
theorem B46290041 : Blo 1605001 46290041 := bstep (se 2 (by rfl) ⟨17358765, by rfl⟩ : syracuseStep 46290041 = 34717531) B34717531
theorem B5421167 : Blo 1605001 5421167 := bstep (se 1 (by rfl) ⟨4065875, by rfl⟩ : syracuseStep 5421167 = 8131751) B8131751
theorem B27433727 : Blo 1605001 27433727 := bstep (se 1 (by rfl) ⟨20575295, by rfl⟩ : syracuseStep 27433727 = 41150591) B41150591
theorem B12188879 : Blo 1605001 12188879 := bstep (se 1 (by rfl) ⟨9141659, by rfl⟩ : syracuseStep 12188879 = 18283319) B18283319
theorem B10288367 : Blo 1605001 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B3431737 : Blo 1605001 3431737 := bstep (se 2 (by rfl) ⟨1286901, by rfl⟩ : syracuseStep 3431737 = 2573803) B2573803
theorem B3612095 : Blo 1605001 3612095 := bstep (se 1 (by rfl) ⟨2709071, by rfl⟩ : syracuseStep 3612095 = 5418143) B5418143
theorem B31277177 : Blo 1605001 31277177 := bstep (se 2 (by rfl) ⟨11728941, by rfl⟩ : syracuseStep 31277177 = 23457883) B23457883
theorem B1605959 : Blo 1605001 1605959 := bstep (se 1 (by rfl) ⟨1204469, by rfl⟩ : syracuseStep 1605959 = 2408939) B2408939
theorem B2408783 : Blo 1605001 2408783 := bstep (se 1 (by rfl) ⟨1806587, by rfl⟩ : syracuseStep 2408783 = 3613175) B3613175
theorem B30860027 : Blo 1605001 30860027 := bstep (se 1 (by rfl) ⟨23145020, by rfl⟩ : syracuseStep 30860027 = 46290041) B46290041
theorem B2409737 : Blo 1605001 2409737 := bstep (se 2 (by rfl) ⟨903651, by rfl⟩ : syracuseStep 2409737 = 1807303) B1807303
theorem B3614111 : Blo 1605001 3614111 := bstep (se 1 (by rfl) ⟨2710583, by rfl⟩ : syracuseStep 3614111 = 5421167) B5421167
theorem B2409935 : Blo 1605001 2409935 := bstep (se 1 (by rfl) ⟨1807451, by rfl⟩ : syracuseStep 2409935 = 3614903) B3614903
theorem B6858911 : Blo 1605001 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B5417711 : Blo 1605001 5417711 := bstep (se 1 (by rfl) ⟨4063283, by rfl⟩ : syracuseStep 5417711 = 8126567) B8126567
theorem B4575649 : Blo 1605001 4575649 := bstep (se 2 (by rfl) ⟨1715868, by rfl⟩ : syracuseStep 4575649 = 3431737) B3431737
theorem B18289151 : Blo 1605001 18289151 := bstep (se 1 (by rfl) ⟨13716863, by rfl⟩ : syracuseStep 18289151 = 27433727) B27433727
theorem B26030753 : Blo 1605001 26030753 := bstep (se 2 (by rfl) ⟨9761532, by rfl⟩ : syracuseStep 26030753 = 19523065) B19523065
theorem B65926979 : Blo 1605001 65926979 := bstep (se 1 (by rfl) ⟨49445234, by rfl⟩ : syracuseStep 65926979 = 98890469) B98890469
theorem B7821791 : Blo 1605001 7821791 := bstep (se 1 (by rfl) ⟨5866343, by rfl⟩ : syracuseStep 7821791 = 11732687) B11732687
theorem B14653943 : Blo 1605001 14653943 := bstep (se 1 (by rfl) ⟨10990457, by rfl⟩ : syracuseStep 14653943 = 21980915) B21980915
theorem B8125919 : Blo 1605001 8125919 := bstep (se 1 (by rfl) ⟨6094439, by rfl⟩ : syracuseStep 8125919 = 12188879) B12188879
theorem B2408063 : Blo 1605001 2408063 := bstep (se 1 (by rfl) ⟨1806047, by rfl⟩ : syracuseStep 2408063 = 3612095) B3612095
theorem B2408105 : Blo 1605001 2408105 := bstep (se 2 (by rfl) ⟨903039, by rfl⟩ : syracuseStep 2408105 = 1806079) B1806079
theorem B1605855 : Blo 1605001 1605855 := bstep (se 1 (by rfl) ⟨1204391, by rfl⟩ : syracuseStep 1605855 = 2408783) B2408783
theorem B1606491 : Blo 1605001 1606491 := bstep (se 1 (by rfl) ⟨1204868, by rfl⟩ : syracuseStep 1606491 = 2409737) B2409737
theorem B2409407 : Blo 1605001 2409407 := bstep (se 1 (by rfl) ⟨1807055, by rfl⟩ : syracuseStep 2409407 = 3614111) B3614111
theorem B1606623 : Blo 1605001 1606623 := bstep (se 1 (by rfl) ⟨1204967, by rfl⟩ : syracuseStep 1606623 = 2409935) B2409935
theorem B43951319 : Blo 1605001 43951319 := bstep (se 1 (by rfl) ⟨32963489, by rfl⟩ : syracuseStep 43951319 = 65926979) B65926979
theorem B4572607 : Blo 1605001 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B5417279 : Blo 1605001 5417279 := bstep (se 1 (by rfl) ⟨4062959, by rfl⟩ : syracuseStep 5417279 = 8125919) B8125919
theorem B20851451 : Blo 1605001 20851451 := bstep (se 1 (by rfl) ⟨15638588, by rfl⟩ : syracuseStep 20851451 = 31277177) B31277177
theorem B12192767 : Blo 1605001 12192767 := bstep (se 1 (by rfl) ⟨9144575, by rfl⟩ : syracuseStep 12192767 = 18289151) B18289151
theorem B17353835 : Blo 1605001 17353835 := bstep (se 1 (by rfl) ⟨13015376, by rfl⟩ : syracuseStep 17353835 = 26030753) B26030753
theorem B20573351 : Blo 1605001 20573351 := bstep (se 1 (by rfl) ⟨15430013, by rfl⟩ : syracuseStep 20573351 = 30860027) B30860027
theorem B5214527 : Blo 1605001 5214527 := bstep (se 1 (by rfl) ⟨3910895, by rfl⟩ : syracuseStep 5214527 = 7821791) B7821791
theorem B9769295 : Blo 1605001 9769295 := bstep (se 1 (by rfl) ⟨7326971, by rfl⟩ : syracuseStep 9769295 = 14653943) B14653943
theorem B6100865 : Blo 1605001 6100865 := bstep (se 2 (by rfl) ⟨2287824, by rfl⟩ : syracuseStep 6100865 = 4575649) B4575649
theorem B3611807 : Blo 1605001 3611807 := bstep (se 1 (by rfl) ⟨2708855, by rfl⟩ : syracuseStep 3611807 = 5417711) B5417711
theorem B1605375 : Blo 1605001 1605375 := bstep (se 1 (by rfl) ⟨1204031, by rfl⟩ : syracuseStep 1605375 = 2408063) B2408063
theorem B1605403 : Blo 1605001 1605403 := bstep (se 1 (by rfl) ⟨1204052, by rfl⟩ : syracuseStep 1605403 = 2408105) B2408105
theorem B1606271 : Blo 1605001 1606271 := bstep (se 1 (by rfl) ⟨1204703, by rfl⟩ : syracuseStep 1606271 = 2409407) B2409407
theorem B26051453 : Blo 1605001 26051453 := bstep (se 3 (by rfl) ⟨4884647, by rfl⟩ : syracuseStep 26051453 = 9769295) B9769295
theorem B6096809 : Blo 1605001 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B8128511 : Blo 1605001 8128511 := bstep (se 1 (by rfl) ⟨6096383, by rfl⟩ : syracuseStep 8128511 = 12192767) B12192767
theorem B11569223 : Blo 1605001 11569223 := bstep (se 1 (by rfl) ⟨8676917, by rfl⟩ : syracuseStep 11569223 = 17353835) B17353835
theorem B13715567 : Blo 1605001 13715567 := bstep (se 1 (by rfl) ⟨10286675, by rfl⟩ : syracuseStep 13715567 = 20573351) B20573351
theorem B3476351 : Blo 1605001 3476351 := bstep (se 1 (by rfl) ⟨2607263, by rfl⟩ : syracuseStep 3476351 = 5214527) B5214527
theorem B4067243 : Blo 1605001 4067243 := bstep (se 1 (by rfl) ⟨3050432, by rfl⟩ : syracuseStep 4067243 = 6100865) B6100865
theorem B29300879 : Blo 1605001 29300879 := bstep (se 1 (by rfl) ⟨21975659, by rfl⟩ : syracuseStep 29300879 = 43951319) B43951319
theorem B3611519 : Blo 1605001 3611519 := bstep (se 1 (by rfl) ⟨2708639, by rfl⟩ : syracuseStep 3611519 = 5417279) B5417279
theorem B13900967 : Blo 1605001 13900967 := bstep (se 1 (by rfl) ⟨10425725, by rfl⟩ : syracuseStep 13900967 = 20851451) B20851451
theorem B2407871 : Blo 1605001 2407871 := bstep (se 1 (by rfl) ⟨1805903, by rfl⟩ : syracuseStep 2407871 = 3611807) B3611807
theorem B17367635 : Blo 1605001 17367635 := bstep (se 1 (by rfl) ⟨13025726, by rfl⟩ : syracuseStep 17367635 = 26051453) B26051453
theorem B4064539 : Blo 1605001 4064539 := bstep (se 1 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 4064539 = 6096809) B6096809
theorem B9143711 : Blo 1605001 9143711 := bstep (se 1 (by rfl) ⟨6857783, by rfl⟩ : syracuseStep 9143711 = 13715567) B13715567
theorem B9267311 : Blo 1605001 9267311 := bstep (se 1 (by rfl) ⟨6950483, by rfl⟩ : syracuseStep 9267311 = 13900967) B13900967
theorem B5419007 : Blo 1605001 5419007 := bstep (se 1 (by rfl) ⟨4064255, by rfl⟩ : syracuseStep 5419007 = 8128511) B8128511
theorem B7712815 : Blo 1605001 7712815 := bstep (se 1 (by rfl) ⟨5784611, by rfl⟩ : syracuseStep 7712815 = 11569223) B11569223
theorem B19533919 : Blo 1605001 19533919 := bstep (se 1 (by rfl) ⟨14650439, by rfl⟩ : syracuseStep 19533919 = 29300879) B29300879
theorem B2407679 : Blo 1605001 2407679 := bstep (se 1 (by rfl) ⟨1805759, by rfl⟩ : syracuseStep 2407679 = 3611519) B3611519
theorem B2317567 : Blo 1605001 2317567 := bstep (se 1 (by rfl) ⟨1738175, by rfl⟩ : syracuseStep 2317567 = 3476351) B3476351
theorem B1605247 : Blo 1605001 1605247 := bstep (se 1 (by rfl) ⟨1203935, by rfl⟩ : syracuseStep 1605247 = 2407871) B2407871
theorem B2711495 : Blo 1605001 2711495 := bstep (se 1 (by rfl) ⟨2033621, by rfl⟩ : syracuseStep 2711495 = 4067243) B4067243
theorem B6095807 : Blo 1605001 6095807 := bstep (se 1 (by rfl) ⟨4571855, by rfl⟩ : syracuseStep 6095807 = 9143711) B9143711
theorem B6178207 : Blo 1605001 6178207 := bstep (se 1 (by rfl) ⟨4633655, by rfl⟩ : syracuseStep 6178207 = 9267311) B9267311
theorem B3090089 : Blo 1605001 3090089 := bstep (se 2 (by rfl) ⟨1158783, by rfl⟩ : syracuseStep 3090089 = 2317567) B2317567
theorem B10283753 : Blo 1605001 10283753 := bstep (se 2 (by rfl) ⟨3856407, by rfl⟩ : syracuseStep 10283753 = 7712815) B7712815
theorem B26045225 : Blo 1605001 26045225 := bstep (se 2 (by rfl) ⟨9766959, by rfl⟩ : syracuseStep 26045225 = 19533919) B19533919
theorem B11578423 : Blo 1605001 11578423 := bstep (se 1 (by rfl) ⟨8683817, by rfl⟩ : syracuseStep 11578423 = 17367635) B17367635
theorem B5419385 : Blo 1605001 5419385 := bstep (se 2 (by rfl) ⟨2032269, by rfl⟩ : syracuseStep 5419385 = 4064539) B4064539
theorem B1807663 : Blo 1605001 1807663 := bstep (se 1 (by rfl) ⟨1355747, by rfl⟩ : syracuseStep 1807663 = 2711495) B2711495
theorem B1605119 : Blo 1605001 1605119 := bstep (se 1 (by rfl) ⟨1203839, by rfl⟩ : syracuseStep 1605119 = 2407679) B2407679
theorem B3612671 : Blo 1605001 3612671 := bstep (se 1 (by rfl) ⟨2709503, by rfl⟩ : syracuseStep 3612671 = 5419007) B5419007
theorem B3612923 : Blo 1605001 3612923 := bstep (se 1 (by rfl) ⟨2709692, by rfl⟩ : syracuseStep 3612923 = 5419385) B5419385
theorem B4063871 : Blo 1605001 4063871 := bstep (se 1 (by rfl) ⟨3047903, by rfl⟩ : syracuseStep 4063871 = 6095807) B6095807
theorem B2408447 : Blo 1605001 2408447 := bstep (se 1 (by rfl) ⟨1806335, by rfl⟩ : syracuseStep 2408447 = 3612671) B3612671
theorem B2410217 : Blo 1605001 2410217 := bstep (se 2 (by rfl) ⟨903831, by rfl⟩ : syracuseStep 2410217 = 1807663) B1807663
theorem B15437897 : Blo 1605001 15437897 := bstep (se 2 (by rfl) ⟨5789211, by rfl⟩ : syracuseStep 15437897 = 11578423) B11578423
theorem B17363483 : Blo 1605001 17363483 := bstep (se 1 (by rfl) ⟨13022612, by rfl⟩ : syracuseStep 17363483 = 26045225) B26045225
theorem B8237609 : Blo 1605001 8237609 := bstep (se 2 (by rfl) ⟨3089103, by rfl⟩ : syracuseStep 8237609 = 6178207) B6178207
theorem B8240237 : Blo 1605001 8240237 := bstep (se 3 (by rfl) ⟨1545044, by rfl⟩ : syracuseStep 8240237 = 3090089) B3090089
theorem B6855835 : Blo 1605001 6855835 := bstep (se 1 (by rfl) ⟨5141876, by rfl⟩ : syracuseStep 6855835 = 10283753) B10283753
theorem B2408615 : Blo 1605001 2408615 := bstep (se 1 (by rfl) ⟨1806461, by rfl⟩ : syracuseStep 2408615 = 3612923) B3612923
theorem B11575655 : Blo 1605001 11575655 := bstep (se 1 (by rfl) ⟨8681741, by rfl⟩ : syracuseStep 11575655 = 17363483) B17363483
theorem B1605631 : Blo 1605001 1605631 := bstep (se 1 (by rfl) ⟨1204223, by rfl⟩ : syracuseStep 1605631 = 2408447) B2408447
theorem B1606811 : Blo 1605001 1606811 := bstep (se 1 (by rfl) ⟨1205108, by rfl⟩ : syracuseStep 1606811 = 2410217) B2410217
theorem B10291931 : Blo 1605001 10291931 := bstep (se 1 (by rfl) ⟨7718948, by rfl⟩ : syracuseStep 10291931 = 15437897) B15437897
theorem B5491739 : Blo 1605001 5491739 := bstep (se 1 (by rfl) ⟨4118804, by rfl⟩ : syracuseStep 5491739 = 8237609) B8237609
theorem B5493491 : Blo 1605001 5493491 := bstep (se 1 (by rfl) ⟨4120118, by rfl⟩ : syracuseStep 5493491 = 8240237) B8240237
theorem B2709247 : Blo 1605001 2709247 := bstep (se 1 (by rfl) ⟨2031935, by rfl⟩ : syracuseStep 2709247 = 4063871) B4063871
theorem B9141113 : Blo 1605001 9141113 := bstep (se 2 (by rfl) ⟨3427917, by rfl⟩ : syracuseStep 9141113 = 6855835) B6855835
theorem B1605743 : Blo 1605001 1605743 := bstep (se 1 (by rfl) ⟨1204307, by rfl⟩ : syracuseStep 1605743 = 2408615) B2408615
theorem B7717103 : Blo 1605001 7717103 := bstep (se 1 (by rfl) ⟨5787827, by rfl⟩ : syracuseStep 7717103 = 11575655) B11575655
theorem B3662327 : Blo 1605001 3662327 := bstep (se 1 (by rfl) ⟨2746745, by rfl⟩ : syracuseStep 3662327 = 5493491) B5493491
theorem B6861287 : Blo 1605001 6861287 := bstep (se 1 (by rfl) ⟨5145965, by rfl⟩ : syracuseStep 6861287 = 10291931) B10291931
theorem B14644637 : Blo 1605001 14644637 := bstep (se 3 (by rfl) ⟨2745869, by rfl⟩ : syracuseStep 14644637 = 5491739) B5491739
theorem B6094075 : Blo 1605001 6094075 := bstep (se 1 (by rfl) ⟨4570556, by rfl⟩ : syracuseStep 6094075 = 9141113) B9141113
theorem B3612329 : Blo 1605001 3612329 := bstep (se 2 (by rfl) ⟨1354623, by rfl⟩ : syracuseStep 3612329 = 2709247) B2709247
theorem B5144735 : Blo 1605001 5144735 := bstep (se 1 (by rfl) ⟨3858551, by rfl⟩ : syracuseStep 5144735 = 7717103) B7717103
theorem B2441551 : Blo 1605001 2441551 := bstep (se 1 (by rfl) ⟨1831163, by rfl⟩ : syracuseStep 2441551 = 3662327) B3662327
theorem B4574191 : Blo 1605001 4574191 := bstep (se 1 (by rfl) ⟨3430643, by rfl⟩ : syracuseStep 4574191 = 6861287) B6861287
theorem B9763091 : Blo 1605001 9763091 := bstep (se 1 (by rfl) ⟨7322318, by rfl⟩ : syracuseStep 9763091 = 14644637) B14644637
theorem B8125433 : Blo 1605001 8125433 := bstep (se 2 (by rfl) ⟨3047037, by rfl⟩ : syracuseStep 8125433 = 6094075) B6094075
theorem B2408219 : Blo 1605001 2408219 := bstep (se 1 (by rfl) ⟨1806164, by rfl⟩ : syracuseStep 2408219 = 3612329) B3612329
theorem B5416955 : Blo 1605001 5416955 := bstep (se 1 (by rfl) ⟨4062716, by rfl⟩ : syracuseStep 5416955 = 8125433) B8125433
theorem B3255401 : Blo 1605001 3255401 := bstep (se 2 (by rfl) ⟨1220775, by rfl⟩ : syracuseStep 3255401 = 2441551) B2441551
theorem B6098921 : Blo 1605001 6098921 := bstep (se 2 (by rfl) ⟨2287095, by rfl⟩ : syracuseStep 6098921 = 4574191) B4574191
theorem B6508727 : Blo 1605001 6508727 := bstep (se 1 (by rfl) ⟨4881545, by rfl⟩ : syracuseStep 6508727 = 9763091) B9763091
theorem B13719293 : Blo 1605001 13719293 := bstep (se 3 (by rfl) ⟨2572367, by rfl⟩ : syracuseStep 13719293 = 5144735) B5144735
theorem B1605479 : Blo 1605001 1605479 := bstep (se 1 (by rfl) ⟨1204109, by rfl⟩ : syracuseStep 1605479 = 2408219) B2408219
theorem B4065947 : Blo 1605001 4065947 := bstep (se 1 (by rfl) ⟨3049460, by rfl⟩ : syracuseStep 4065947 = 6098921) B6098921
theorem B9146195 : Blo 1605001 9146195 := bstep (se 1 (by rfl) ⟨6859646, by rfl⟩ : syracuseStep 9146195 = 13719293) B13719293
theorem B4339151 : Blo 1605001 4339151 := bstep (se 1 (by rfl) ⟨3254363, by rfl⟩ : syracuseStep 4339151 = 6508727) B6508727
theorem B8681069 : Blo 1605001 8681069 := bstep (se 3 (by rfl) ⟨1627700, by rfl⟩ : syracuseStep 8681069 = 3255401) B3255401
theorem B3611303 : Blo 1605001 3611303 := bstep (se 1 (by rfl) ⟨2708477, by rfl⟩ : syracuseStep 3611303 = 5416955) B5416955
theorem B2892767 : Blo 1605001 2892767 := bstep (se 1 (by rfl) ⟨2169575, by rfl⟩ : syracuseStep 2892767 = 4339151) B4339151
theorem B6097463 : Blo 1605001 6097463 := bstep (se 1 (by rfl) ⟨4573097, by rfl⟩ : syracuseStep 6097463 = 9146195) B9146195
theorem B5787379 : Blo 1605001 5787379 := bstep (se 1 (by rfl) ⟨4340534, by rfl⟩ : syracuseStep 5787379 = 8681069) B8681069
theorem B2710631 : Blo 1605001 2710631 := bstep (se 1 (by rfl) ⟨2032973, by rfl⟩ : syracuseStep 2710631 = 4065947) B4065947
theorem B2407535 : Blo 1605001 2407535 := bstep (se 1 (by rfl) ⟨1805651, by rfl⟩ : syracuseStep 2407535 = 3611303) B3611303
theorem B4064975 : Blo 1605001 4064975 := bstep (se 1 (by rfl) ⟨3048731, by rfl⟩ : syracuseStep 4064975 = 6097463) B6097463
theorem B1807087 : Blo 1605001 1807087 := bstep (se 1 (by rfl) ⟨1355315, by rfl⟩ : syracuseStep 1807087 = 2710631) B2710631
theorem B7714045 : Blo 1605001 7714045 := bstep (se 3 (by rfl) ⟨1446383, by rfl⟩ : syracuseStep 7714045 = 2892767) B2892767
theorem B30866021 : Blo 1605001 30866021 := bstep (se 4 (by rfl) ⟨2893689, by rfl⟩ : syracuseStep 30866021 = 5787379) B5787379
theorem B1605023 : Blo 1605001 1605023 := bstep (se 1 (by rfl) ⟨1203767, by rfl⟩ : syracuseStep 1605023 = 2407535) B2407535
theorem B2409449 : Blo 1605001 2409449 := bstep (se 2 (by rfl) ⟨903543, by rfl⟩ : syracuseStep 2409449 = 1807087) B1807087
theorem B10285393 : Blo 1605001 10285393 := bstep (se 2 (by rfl) ⟨3857022, by rfl⟩ : syracuseStep 10285393 = 7714045) B7714045
theorem B2709983 : Blo 1605001 2709983 := bstep (se 1 (by rfl) ⟨2032487, by rfl⟩ : syracuseStep 2709983 = 4064975) B4064975
theorem B20577347 : Blo 1605001 20577347 := bstep (se 1 (by rfl) ⟨15433010, by rfl⟩ : syracuseStep 20577347 = 30866021) B30866021
theorem B13713857 : Blo 1605001 13713857 := bstep (se 2 (by rfl) ⟨5142696, by rfl⟩ : syracuseStep 13713857 = 10285393) B10285393
theorem B1606299 : Blo 1605001 1606299 := bstep (se 1 (by rfl) ⟨1204724, by rfl⟩ : syracuseStep 1606299 = 2409449) B2409449
theorem B1806655 : Blo 1605001 1806655 := bstep (se 1 (by rfl) ⟨1354991, by rfl⟩ : syracuseStep 1806655 = 2709983) B2709983
theorem B13718231 : Blo 1605001 13718231 := bstep (se 1 (by rfl) ⟨10288673, by rfl⟩ : syracuseStep 13718231 = 20577347) B20577347
theorem B9142571 : Blo 1605001 9142571 := bstep (se 1 (by rfl) ⟨6856928, by rfl⟩ : syracuseStep 9142571 = 13713857) B13713857
theorem B2408873 : Blo 1605001 2408873 := bstep (se 2 (by rfl) ⟨903327, by rfl⟩ : syracuseStep 2408873 = 1806655) B1806655
theorem B9145487 : Blo 1605001 9145487 := bstep (se 1 (by rfl) ⟨6859115, by rfl⟩ : syracuseStep 9145487 = 13718231) B13718231
theorem B6095047 : Blo 1605001 6095047 := bstep (se 1 (by rfl) ⟨4571285, by rfl⟩ : syracuseStep 6095047 = 9142571) B9142571
theorem B1605915 : Blo 1605001 1605915 := bstep (se 1 (by rfl) ⟨1204436, by rfl⟩ : syracuseStep 1605915 = 2408873) B2408873
theorem B6096991 : Blo 1605001 6096991 := bstep (se 1 (by rfl) ⟨4572743, by rfl⟩ : syracuseStep 6096991 = 9145487) B9145487
theorem B8126729 : Blo 1605001 8126729 := bstep (se 2 (by rfl) ⟨3047523, by rfl⟩ : syracuseStep 8126729 = 6095047) B6095047
theorem B8129321 : Blo 1605001 8129321 := bstep (se 2 (by rfl) ⟨3048495, by rfl⟩ : syracuseStep 8129321 = 6096991) B6096991
theorem B5417819 : Blo 1605001 5417819 := bstep (se 1 (by rfl) ⟨4063364, by rfl⟩ : syracuseStep 5417819 = 8126729) B8126729
theorem B5419547 : Blo 1605001 5419547 := bstep (se 1 (by rfl) ⟨4064660, by rfl⟩ : syracuseStep 5419547 = 8129321) B8129321
theorem B3613031 : Blo 1605001 3613031 := bstep (se 1 (by rfl) ⟨2709773, by rfl⟩ : syracuseStep 3613031 = 5419547) B5419547
theorem B3611879 : Blo 1605001 3611879 := bstep (se 1 (by rfl) ⟨2708909, by rfl⟩ : syracuseStep 3611879 = 5417819) B5417819
theorem B2408687 : Blo 1605001 2408687 := bstep (se 1 (by rfl) ⟨1806515, by rfl⟩ : syracuseStep 2408687 = 3613031) B3613031
theorem B2407919 : Blo 1605001 2407919 := bstep (se 1 (by rfl) ⟨1805939, by rfl⟩ : syracuseStep 2407919 = 3611879) B3611879
theorem B1605791 : Blo 1605001 1605791 := bstep (se 1 (by rfl) ⟨1204343, by rfl⟩ : syracuseStep 1605791 = 2408687) B2408687
theorem B1605279 : Blo 1605001 1605279 := bstep (se 1 (by rfl) ⟨1203959, by rfl⟩ : syracuseStep 1605279 = 2407919) B2407919

theorem C0 (j : ℕ) (h1 : 401250 ≤ j) (h2 : j ≤ 401749) : Blo 1605001 (4 * j + 3) := by
  interval_cases j
  · exact B1605003
  · exact B1605007
  · exact B1605011
  · exact B1605015
  · exact B1605019
  · exact B1605023
  · exact B1605027
  · exact B1605031
  · exact B1605035
  · exact B1605039
  · exact B1605043
  · exact B1605047
  · exact B1605051
  · exact B1605055
  · exact B1605059
  · exact B1605063
  · exact B1605067
  · exact B1605071
  · exact B1605075
  · exact B1605079
  · exact B1605083
  · exact B1605087
  · exact B1605091
  · exact B1605095
  · exact B1605099
  · exact B1605103
  · exact B1605107
  · exact B1605111
  · exact B1605115
  · exact B1605119
  · exact B1605123
  · exact B1605127
  · exact B1605131
  · exact B1605135
  · exact B1605139
  · exact B1605143
  · exact B1605147
  · exact B1605151
  · exact B1605155
  · exact B1605159
  · exact B1605163
  · exact B1605167
  · exact B1605171
  · exact B1605175
  · exact B1605179
  · exact B1605183
  · exact B1605187
  · exact B1605191
  · exact B1605195
  · exact B1605199
  · exact B1605203
  · exact B1605207
  · exact B1605211
  · exact B1605215
  · exact B1605219
  · exact B1605223
  · exact B1605227
  · exact B1605231
  · exact B1605235
  · exact B1605239
  · exact B1605243
  · exact B1605247
  · exact B1605251
  · exact B1605255
  · exact B1605259
  · exact B1605263
  · exact B1605267
  · exact B1605271
  · exact B1605275
  · exact B1605279
  · exact B1605283
  · exact B1605287
  · exact B1605291
  · exact B1605295
  · exact B1605299
  · exact B1605303
  · exact B1605307
  · exact B1605311
  · exact B1605315
  · exact B1605319
  · exact B1605323
  · exact B1605327
  · exact B1605331
  · exact B1605335
  · exact B1605339
  · exact B1605343
  · exact B1605347
  · exact B1605351
  · exact B1605355
  · exact B1605359
  · exact B1605363
  · exact B1605367
  · exact B1605371
  · exact B1605375
  · exact B1605379
  · exact B1605383
  · exact B1605387
  · exact B1605391
  · exact B1605395
  · exact B1605399
  · exact B1605403
  · exact B1605407
  · exact B1605411
  · exact B1605415
  · exact B1605419
  · exact B1605423
  · exact B1605427
  · exact B1605431
  · exact B1605435
  · exact B1605439
  · exact B1605443
  · exact B1605447
  · exact B1605451
  · exact B1605455
  · exact B1605459
  · exact B1605463
  · exact B1605467
  · exact B1605471
  · exact B1605475
  · exact B1605479
  · exact B1605483
  · exact B1605487
  · exact B1605491
  · exact B1605495
  · exact B1605499
  · exact B1605503
  · exact B1605507
  · exact B1605511
  · exact B1605515
  · exact B1605519
  · exact B1605523
  · exact B1605527
  · exact B1605531
  · exact B1605535
  · exact B1605539
  · exact B1605543
  · exact B1605547
  · exact B1605551
  · exact B1605555
  · exact B1605559
  · exact B1605563
  · exact B1605567
  · exact B1605571
  · exact B1605575
  · exact B1605579
  · exact B1605583
  · exact B1605587
  · exact B1605591
  · exact B1605595
  · exact B1605599
  · exact B1605603
  · exact B1605607
  · exact B1605611
  · exact B1605615
  · exact B1605619
  · exact B1605623
  · exact B1605627
  · exact B1605631
  · exact B1605635
  · exact B1605639
  · exact B1605643
  · exact B1605647
  · exact B1605651
  · exact B1605655
  · exact B1605659
  · exact B1605663
  · exact B1605667
  · exact B1605671
  · exact B1605675
  · exact B1605679
  · exact B1605683
  · exact B1605687
  · exact B1605691
  · exact B1605695
  · exact B1605699
  · exact B1605703
  · exact B1605707
  · exact B1605711
  · exact B1605715
  · exact B1605719
  · exact B1605723
  · exact B1605727
  · exact B1605731
  · exact B1605735
  · exact B1605739
  · exact B1605743
  · exact B1605747
  · exact B1605751
  · exact B1605755
  · exact B1605759
  · exact B1605763
  · exact B1605767
  · exact B1605771
  · exact B1605775
  · exact B1605779
  · exact B1605783
  · exact B1605787
  · exact B1605791
  · exact B1605795
  · exact B1605799
  · exact B1605803
  · exact B1605807
  · exact B1605811
  · exact B1605815
  · exact B1605819
  · exact B1605823
  · exact B1605827
  · exact B1605831
  · exact B1605835
  · exact B1605839
  · exact B1605843
  · exact B1605847
  · exact B1605851
  · exact B1605855
  · exact B1605859
  · exact B1605863
  · exact B1605867
  · exact B1605871
  · exact B1605875
  · exact B1605879
  · exact B1605883
  · exact B1605887
  · exact B1605891
  · exact B1605895
  · exact B1605899
  · exact B1605903
  · exact B1605907
  · exact B1605911
  · exact B1605915
  · exact B1605919
  · exact B1605923
  · exact B1605927
  · exact B1605931
  · exact B1605935
  · exact B1605939
  · exact B1605943
  · exact B1605947
  · exact B1605951
  · exact B1605955
  · exact B1605959
  · exact B1605963
  · exact B1605967
  · exact B1605971
  · exact B1605975
  · exact B1605979
  · exact B1605983
  · exact B1605987
  · exact B1605991
  · exact B1605995
  · exact B1605999
  · exact B1606003
  · exact B1606007
  · exact B1606011
  · exact B1606015
  · exact B1606019
  · exact B1606023
  · exact B1606027
  · exact B1606031
  · exact B1606035
  · exact B1606039
  · exact B1606043
  · exact B1606047
  · exact B1606051
  · exact B1606055
  · exact B1606059
  · exact B1606063
  · exact B1606067
  · exact B1606071
  · exact B1606075
  · exact B1606079
  · exact B1606083
  · exact B1606087
  · exact B1606091
  · exact B1606095
  · exact B1606099
  · exact B1606103
  · exact B1606107
  · exact B1606111
  · exact B1606115
  · exact B1606119
  · exact B1606123
  · exact B1606127
  · exact B1606131
  · exact B1606135
  · exact B1606139
  · exact B1606143
  · exact B1606147
  · exact B1606151
  · exact B1606155
  · exact B1606159
  · exact B1606163
  · exact B1606167
  · exact B1606171
  · exact B1606175
  · exact B1606179
  · exact B1606183
  · exact B1606187
  · exact B1606191
  · exact B1606195
  · exact B1606199
  · exact B1606203
  · exact B1606207
  · exact B1606211
  · exact B1606215
  · exact B1606219
  · exact B1606223
  · exact B1606227
  · exact B1606231
  · exact B1606235
  · exact B1606239
  · exact B1606243
  · exact B1606247
  · exact B1606251
  · exact B1606255
  · exact B1606259
  · exact B1606263
  · exact B1606267
  · exact B1606271
  · exact B1606275
  · exact B1606279
  · exact B1606283
  · exact B1606287
  · exact B1606291
  · exact B1606295
  · exact B1606299
  · exact B1606303
  · exact B1606307
  · exact B1606311
  · exact B1606315
  · exact B1606319
  · exact B1606323
  · exact B1606327
  · exact B1606331
  · exact B1606335
  · exact B1606339
  · exact B1606343
  · exact B1606347
  · exact B1606351
  · exact B1606355
  · exact B1606359
  · exact B1606363
  · exact B1606367
  · exact B1606371
  · exact B1606375
  · exact B1606379
  · exact B1606383
  · exact B1606387
  · exact B1606391
  · exact B1606395
  · exact B1606399
  · exact B1606403
  · exact B1606407
  · exact B1606411
  · exact B1606415
  · exact B1606419
  · exact B1606423
  · exact B1606427
  · exact B1606431
  · exact B1606435
  · exact B1606439
  · exact B1606443
  · exact B1606447
  · exact B1606451
  · exact B1606455
  · exact B1606459
  · exact B1606463
  · exact B1606467
  · exact B1606471
  · exact B1606475
  · exact B1606479
  · exact B1606483
  · exact B1606487
  · exact B1606491
  · exact B1606495
  · exact B1606499
  · exact B1606503
  · exact B1606507
  · exact B1606511
  · exact B1606515
  · exact B1606519
  · exact B1606523
  · exact B1606527
  · exact B1606531
  · exact B1606535
  · exact B1606539
  · exact B1606543
  · exact B1606547
  · exact B1606551
  · exact B1606555
  · exact B1606559
  · exact B1606563
  · exact B1606567
  · exact B1606571
  · exact B1606575
  · exact B1606579
  · exact B1606583
  · exact B1606587
  · exact B1606591
  · exact B1606595
  · exact B1606599
  · exact B1606603
  · exact B1606607
  · exact B1606611
  · exact B1606615
  · exact B1606619
  · exact B1606623
  · exact B1606627
  · exact B1606631
  · exact B1606635
  · exact B1606639
  · exact B1606643
  · exact B1606647
  · exact B1606651
  · exact B1606655
  · exact B1606659
  · exact B1606663
  · exact B1606667
  · exact B1606671
  · exact B1606675
  · exact B1606679
  · exact B1606683
  · exact B1606687
  · exact B1606691
  · exact B1606695
  · exact B1606699
  · exact B1606703
  · exact B1606707
  · exact B1606711
  · exact B1606715
  · exact B1606719
  · exact B1606723
  · exact B1606727
  · exact B1606731
  · exact B1606735
  · exact B1606739
  · exact B1606743
  · exact B1606747
  · exact B1606751
  · exact B1606755
  · exact B1606759
  · exact B1606763
  · exact B1606767
  · exact B1606771
  · exact B1606775
  · exact B1606779
  · exact B1606783
  · exact B1606787
  · exact B1606791
  · exact B1606795
  · exact B1606799
  · exact B1606803
  · exact B1606807
  · exact B1606811
  · exact B1606815
  · exact B1606819
  · exact B1606823
  · exact B1606827
  · exact B1606831
  · exact B1606835
  · exact B1606839
  · exact B1606843
  · exact B1606847
  · exact B1606851
  · exact B1606855
  · exact B1606859
  · exact B1606863
  · exact B1606867
  · exact B1606871
  · exact B1606875
  · exact B1606879
  · exact B1606883
  · exact B1606887
  · exact B1606891
  · exact B1606895
  · exact B1606899
  · exact B1606903
  · exact B1606907
  · exact B1606911
  · exact B1606915
  · exact B1606919
  · exact B1606923
  · exact B1606927
  · exact B1606931
  · exact B1606935
  · exact B1606939
  · exact B1606943
  · exact B1606947
  · exact B1606951
  · exact B1606955
  · exact B1606959
  · exact B1606963
  · exact B1606967
  · exact B1606971
  · exact B1606975
  · exact B1606979
  · exact B1606983
  · exact B1606987
  · exact B1606991
  · exact B1606995
  · exact B1606999

theorem solution (m : ℕ) (hlo : 1605001 ≤ m) (hhi : m ≤ 1607001) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 401250 ≤ j := by omega
    have hj2 : j ≤ 401749 := by omega
    have hb : Blo 1605001 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
