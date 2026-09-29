-- Prove2me | solution 1 for syracuse_descends_range_738327_742327
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:13.10289+00:00
-- url     : https://prove2.me/submissions/24f4acc4-49c0-41b4-b661-0d251273c28e

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


theorem B1441813 : Blo 738327 1441813 := bbase (se 6 (by rfl) ⟨33792, by rfl⟩ : syracuseStep 1441813 = 67585) (by norm_num)
theorem B2818421 : Blo 738327 2818421 := bbase (se 5 (by rfl) ⟨132113, by rfl⟩ : syracuseStep 2818421 = 264227) (by norm_num)
theorem B950717 : Blo 738327 950717 := bbase (se 3 (by rfl) ⟨178259, by rfl⟩ : syracuseStep 950717 = 356519) (by norm_num)
theorem B1901333 : Blo 738327 1901333 := bbase (se 6 (by rfl) ⟨44562, by rfl⟩ : syracuseStep 1901333 = 89125) (by norm_num)
theorem B1245989 : Blo 738327 1245989 := bbase (se 4 (by rfl) ⟨116811, by rfl⟩ : syracuseStep 1245989 = 233623) (by norm_num)
theorem B1246117 : Blo 738327 1246117 := bbase (se 4 (by rfl) ⟨116823, by rfl⟩ : syracuseStep 1246117 = 233647) (by norm_num)
theorem B1246205 : Blo 738327 1246205 := bbase (se 3 (by rfl) ⟨233663, by rfl⟩ : syracuseStep 1246205 = 467327) (by norm_num)
theorem B6947893 : Blo 738327 6947893 := bbase (se 5 (by rfl) ⟨325682, by rfl⟩ : syracuseStep 6947893 = 651365) (by norm_num)
theorem B1246333 : Blo 738327 1246333 := bbase (se 3 (by rfl) ⟨233687, by rfl⟩ : syracuseStep 1246333 = 467375) (by norm_num)
theorem B1868933 : Blo 738327 1868933 := bbase (se 4 (by rfl) ⟨175212, by rfl⟩ : syracuseStep 1868933 = 350425) (by norm_num)
theorem B1246421 : Blo 738327 1246421 := bbase (se 7 (by rfl) ⟨14606, by rfl⟩ : syracuseStep 1246421 = 29213) (by norm_num)
theorem B951517 : Blo 738327 951517 := bbase (se 3 (by rfl) ⟨178409, by rfl⟩ : syracuseStep 951517 = 356819) (by norm_num)
theorem B4818197 : Blo 738327 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B1246549 : Blo 738327 1246549 := bbase (se 12 (by rfl) ⟨456, by rfl⟩ : syracuseStep 1246549 = 913) (by norm_num)
theorem B1246637 : Blo 738327 1246637 := bbase (se 3 (by rfl) ⟨233744, by rfl⟩ : syracuseStep 1246637 = 467489) (by norm_num)
theorem B951733 : Blo 738327 951733 := bbase (se 5 (by rfl) ⟨44612, by rfl⟩ : syracuseStep 951733 = 89225) (by norm_num)
theorem B1869277 : Blo 738327 1869277 := bbase (se 3 (by rfl) ⟨350489, by rfl⟩ : syracuseStep 1869277 = 700979) (by norm_num)
theorem B1246765 : Blo 738327 1246765 := bbase (se 3 (by rfl) ⟨233768, by rfl⟩ : syracuseStep 1246765 = 467537) (by norm_num)
theorem B1869389 : Blo 738327 1869389 := bbase (se 3 (by rfl) ⟨350510, by rfl⟩ : syracuseStep 1869389 = 701021) (by norm_num)
theorem B1246853 : Blo 738327 1246853 := bbase (se 4 (by rfl) ⟨116892, by rfl⟩ : syracuseStep 1246853 = 233785) (by norm_num)
theorem B1246981 : Blo 738327 1246981 := bbase (se 4 (by rfl) ⟨116904, by rfl⟩ : syracuseStep 1246981 = 233809) (by norm_num)
theorem B1869581 : Blo 738327 1869581 := bbase (se 3 (by rfl) ⟨350546, by rfl⟩ : syracuseStep 1869581 = 701093) (by norm_num)
theorem B1247069 : Blo 738327 1247069 := bbase (se 3 (by rfl) ⟨233825, by rfl⟩ : syracuseStep 1247069 = 467651) (by norm_num)
theorem B2492261 : Blo 738327 2492261 := bbase (se 4 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 2492261 = 467299) (by norm_num)
theorem B952225 : Blo 738327 952225 := bbase (se 2 (by rfl) ⟨357084, by rfl⟩ : syracuseStep 952225 = 714169) (by norm_num)
theorem B2000821 : Blo 738327 2000821 := bbase (se 5 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 2000821 = 187577) (by norm_num)
theorem B1247197 : Blo 738327 1247197 := bbase (se 3 (by rfl) ⟨233849, by rfl⟩ : syracuseStep 1247197 = 467699) (by norm_num)
theorem B788465 : Blo 738327 788465 := bbase (se 2 (by rfl) ⟨295674, by rfl⟩ : syracuseStep 788465 = 591349) (by norm_num)
theorem B1247285 : Blo 738327 1247285 := bbase (se 5 (by rfl) ⟨58466, by rfl⟩ : syracuseStep 1247285 = 116933) (by norm_num)
theorem B1869925 : Blo 738327 1869925 := bbase (se 4 (by rfl) ⟨175305, by rfl⟩ : syracuseStep 1869925 = 350611) (by norm_num)
theorem B10389653 : Blo 738327 10389653 := bbase (se 6 (by rfl) ⟨243507, by rfl⟩ : syracuseStep 10389653 = 487015) (by norm_num)
theorem B1083541 : Blo 738327 1083541 := bbase (se 6 (by rfl) ⟨25395, by rfl⟩ : syracuseStep 1083541 = 50791) (by norm_num)
theorem B788653 : Blo 738327 788653 := bbase (se 3 (by rfl) ⟨147872, by rfl⟩ : syracuseStep 788653 = 295745) (by norm_num)
theorem B1247413 : Blo 738327 1247413 := bbase (se 5 (by rfl) ⟨58472, by rfl⟩ : syracuseStep 1247413 = 116945) (by norm_num)
theorem B1870037 : Blo 738327 1870037 := bbase (se 7 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 1870037 = 43829) (by norm_num)
theorem B887053 : Blo 738327 887053 := bbase (se 3 (by rfl) ⟨166322, by rfl⟩ : syracuseStep 887053 = 332645) (by norm_num)
theorem B1247501 : Blo 738327 1247501 := bbase (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) (by norm_num)
theorem B2492693 : Blo 738327 2492693 := bbase (se 6 (by rfl) ⟨58422, by rfl⟩ : syracuseStep 2492693 = 116845) (by norm_num)
theorem B1247629 : Blo 738327 1247629 := bbase (se 3 (by rfl) ⟨233930, by rfl⟩ : syracuseStep 1247629 = 467861) (by norm_num)
theorem B1870229 : Blo 738327 1870229 := bbase (se 6 (by rfl) ⟨43833, by rfl⟩ : syracuseStep 1870229 = 87667) (by norm_num)
theorem B2853317 : Blo 738327 2853317 := bbase (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) (by norm_num)
theorem B887269 : Blo 738327 887269 := bbase (se 4 (by rfl) ⟨83181, by rfl⟩ : syracuseStep 887269 = 166363) (by norm_num)
theorem B1247717 : Blo 738327 1247717 := bbase (se 4 (by rfl) ⟨116973, by rfl⟩ : syracuseStep 1247717 = 233947) (by norm_num)
theorem B3738149 : Blo 738327 3738149 := bbase (se 4 (by rfl) ⟨350451, by rfl⟩ : syracuseStep 3738149 = 700903) (by norm_num)
theorem B1247845 : Blo 738327 1247845 := bbase (se 4 (by rfl) ⟨116985, by rfl⟩ : syracuseStep 1247845 = 233971) (by norm_num)
theorem B1051309 : Blo 738327 1051309 := bbase (se 3 (by rfl) ⟨197120, by rfl⟩ : syracuseStep 1051309 = 394241) (by norm_num)
theorem B1247933 : Blo 738327 1247933 := bbase (se 3 (by rfl) ⟨233987, by rfl⟩ : syracuseStep 1247933 = 467975) (by norm_num)
theorem B2493125 : Blo 738327 2493125 := bbase (se 4 (by rfl) ⟨233730, by rfl⟩ : syracuseStep 2493125 = 467461) (by norm_num)
theorem B1870573 : Blo 738327 1870573 := bbase (se 3 (by rfl) ⟨350732, by rfl⟩ : syracuseStep 1870573 = 701465) (by norm_num)
theorem B1248061 : Blo 738327 1248061 := bbase (se 3 (by rfl) ⟨234011, by rfl⟩ : syracuseStep 1248061 = 468023) (by norm_num)
theorem B1870685 : Blo 738327 1870685 := bbase (se 3 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 1870685 = 701507) (by norm_num)
theorem B1248149 : Blo 738327 1248149 := bbase (se 6 (by rfl) ⟨29253, by rfl⟩ : syracuseStep 1248149 = 58507) (by norm_num)
theorem B789473 : Blo 738327 789473 := bbase (se 2 (by rfl) ⟨296052, by rfl⟩ : syracuseStep 789473 = 592105) (by norm_num)
theorem B1248277 : Blo 738327 1248277 := bbase (se 6 (by rfl) ⟨29256, by rfl⟩ : syracuseStep 1248277 = 58513) (by norm_num)
theorem B1870877 : Blo 738327 1870877 := bbase (se 3 (by rfl) ⟨350789, by rfl⟩ : syracuseStep 1870877 = 701579) (by norm_num)
theorem B887869 : Blo 738327 887869 := bbase (se 3 (by rfl) ⟨166475, by rfl⟩ : syracuseStep 887869 = 332951) (by norm_num)
theorem B1248365 : Blo 738327 1248365 := bbase (se 3 (by rfl) ⟨234068, by rfl⟩ : syracuseStep 1248365 = 468137) (by norm_num)
theorem B2493557 : Blo 738327 2493557 := bbase (se 5 (by rfl) ⟨116885, by rfl⟩ : syracuseStep 2493557 = 233771) (by norm_num)
theorem B1051805 : Blo 738327 1051805 := bbase (se 3 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 1051805 = 394427) (by norm_num)
theorem B1248493 : Blo 738327 1248493 := bbase (se 3 (by rfl) ⟨234092, by rfl⟩ : syracuseStep 1248493 = 468185) (by norm_num)
theorem B9506069 : Blo 738327 9506069 := bbase (se 6 (by rfl) ⟨222798, by rfl⟩ : syracuseStep 9506069 = 445597) (by norm_num)
theorem B1248581 : Blo 738327 1248581 := bbase (se 4 (by rfl) ⟨117054, by rfl⟩ : syracuseStep 1248581 = 234109) (by norm_num)
theorem B1871221 : Blo 738327 1871221 := bbase (se 5 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 1871221 = 175427) (by norm_num)
theorem B1183133 : Blo 738327 1183133 := bbase (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) (by norm_num)
theorem B789917 : Blo 738327 789917 := bbase (se 3 (by rfl) ⟨148109, by rfl⟩ : syracuseStep 789917 = 296219) (by norm_num)
theorem B1248709 : Blo 738327 1248709 := bbase (se 4 (by rfl) ⟨117066, by rfl⟩ : syracuseStep 1248709 = 234133) (by norm_num)
theorem B855517 : Blo 738327 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B1871333 : Blo 738327 1871333 := bbase (se 4 (by rfl) ⟨175437, by rfl⟩ : syracuseStep 1871333 = 350875) (by norm_num)
theorem B4754933 : Blo 738327 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B1248797 : Blo 738327 1248797 := bbase (se 3 (by rfl) ⟨234149, by rfl⟩ : syracuseStep 1248797 = 468299) (by norm_num)
theorem B2493989 : Blo 738327 2493989 := bbase (se 4 (by rfl) ⟨233811, by rfl⟩ : syracuseStep 2493989 = 467623) (by norm_num)
theorem B790165 : Blo 738327 790165 := bbase (se 6 (by rfl) ⟨18519, by rfl⟩ : syracuseStep 790165 = 37039) (by norm_num)
theorem B1248925 : Blo 738327 1248925 := bbase (se 3 (by rfl) ⟨234173, by rfl⟩ : syracuseStep 1248925 = 468347) (by norm_num)
theorem B1871525 : Blo 738327 1871525 := bbase (se 4 (by rfl) ⟨175455, by rfl⟩ : syracuseStep 1871525 = 350911) (by norm_num)
theorem B1052357 : Blo 738327 1052357 := bbase (se 4 (by rfl) ⟨98658, by rfl⟩ : syracuseStep 1052357 = 197317) (by norm_num)
theorem B1249013 : Blo 738327 1249013 := bbase (se 5 (by rfl) ⟨58547, by rfl⟩ : syracuseStep 1249013 = 117095) (by norm_num)
theorem B3739445 : Blo 738327 3739445 := bbase (se 5 (by rfl) ⟨175286, by rfl⟩ : syracuseStep 3739445 = 350573) (by norm_num)
theorem B1183589 : Blo 738327 1183589 := bbase (se 4 (by rfl) ⟨110961, by rfl⟩ : syracuseStep 1183589 = 221923) (by norm_num)
theorem B1249141 : Blo 738327 1249141 := bbase (se 5 (by rfl) ⟨58553, by rfl⟩ : syracuseStep 1249141 = 117107) (by norm_num)
theorem B1249229 : Blo 738327 1249229 := bbase (se 3 (by rfl) ⟨234230, by rfl⟩ : syracuseStep 1249229 = 468461) (by norm_num)
theorem B2494421 : Blo 738327 2494421 := bbase (se 7 (by rfl) ⟨29231, by rfl⟩ : syracuseStep 2494421 = 58463) (by norm_num)
theorem B1871869 : Blo 738327 1871869 := bbase (se 3 (by rfl) ⟨350975, by rfl⟩ : syracuseStep 1871869 = 701951) (by norm_num)
theorem B790597 : Blo 738327 790597 := bbase (se 4 (by rfl) ⟨74118, by rfl⟩ : syracuseStep 790597 = 148237) (by norm_num)
theorem B1249357 : Blo 738327 1249357 := bbase (se 3 (by rfl) ⟨234254, by rfl⟩ : syracuseStep 1249357 = 468509) (by norm_num)
theorem B1871981 : Blo 738327 1871981 := bbase (se 3 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 1871981 = 701993) (by norm_num)
theorem B790669 : Blo 738327 790669 := bbase (se 3 (by rfl) ⟨148250, by rfl⟩ : syracuseStep 790669 = 296501) (by norm_num)
theorem B1249445 : Blo 738327 1249445 := bbase (se 4 (by rfl) ⟨117135, by rfl⟩ : syracuseStep 1249445 = 234271) (by norm_num)
theorem B889013 : Blo 738327 889013 := bbase (se 5 (by rfl) ⟨41672, by rfl⟩ : syracuseStep 889013 = 83345) (by norm_num)
theorem B889061 : Blo 738327 889061 := bbase (se 4 (by rfl) ⟨83349, by rfl⟩ : syracuseStep 889061 = 166699) (by norm_num)
theorem B1577237 : Blo 738327 1577237 := bbase (se 6 (by rfl) ⟨36966, by rfl⟩ : syracuseStep 1577237 = 73933) (by norm_num)
theorem B1249573 : Blo 738327 1249573 := bbase (se 4 (by rfl) ⟨117147, by rfl⟩ : syracuseStep 1249573 = 234295) (by norm_num)
theorem B1872173 : Blo 738327 1872173 := bbase (se 3 (by rfl) ⟨351032, by rfl⟩ : syracuseStep 1872173 = 702065) (by norm_num)
theorem B889157 : Blo 738327 889157 := bbase (se 4 (by rfl) ⟨83358, by rfl⟩ : syracuseStep 889157 = 166717) (by norm_num)
theorem B1249661 : Blo 738327 1249661 := bbase (se 3 (by rfl) ⟨234311, by rfl⟩ : syracuseStep 1249661 = 468623) (by norm_num)
theorem B2494853 : Blo 738327 2494853 := bbase (se 4 (by rfl) ⟨233892, by rfl⟩ : syracuseStep 2494853 = 467785) (by norm_num)
theorem B1053109 : Blo 738327 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B6951349 : Blo 738327 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B889321 : Blo 738327 889321 := bbase (se 2 (by rfl) ⟨333495, by rfl⟩ : syracuseStep 889321 = 666991) (by norm_num)
theorem B1249789 : Blo 738327 1249789 := bbase (se 3 (by rfl) ⟨234335, by rfl⟩ : syracuseStep 1249789 = 468671) (by norm_num)
theorem B791041 : Blo 738327 791041 := bbase (se 2 (by rfl) ⟨296640, by rfl⟩ : syracuseStep 791041 = 593281) (by norm_num)
theorem B1577477 : Blo 738327 1577477 := bbase (se 4 (by rfl) ⟨147888, by rfl⟩ : syracuseStep 1577477 = 295777) (by norm_num)
theorem B1249877 : Blo 738327 1249877 := bbase (se 8 (by rfl) ⟨7323, by rfl⟩ : syracuseStep 1249877 = 14647) (by norm_num)
theorem B1774181 : Blo 738327 1774181 := bbase (se 4 (by rfl) ⟨166329, by rfl⟩ : syracuseStep 1774181 = 332659) (by norm_num)
theorem B1872517 : Blo 738327 1872517 := bbase (se 4 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 1872517 = 351097) (by norm_num)
theorem B889537 : Blo 738327 889537 := bbase (se 2 (by rfl) ⟨333576, by rfl⟩ : syracuseStep 889537 = 667153) (by norm_num)
theorem B1250005 : Blo 738327 1250005 := bbase (se 7 (by rfl) ⟨14648, by rfl⟩ : syracuseStep 1250005 = 29297) (by norm_num)
theorem B1872629 : Blo 738327 1872629 := bbase (se 5 (by rfl) ⟨87779, by rfl⟩ : syracuseStep 1872629 = 175559) (by norm_num)
theorem B2003717 : Blo 738327 2003717 := bbase (se 4 (by rfl) ⟨187848, by rfl⟩ : syracuseStep 2003717 = 375697) (by norm_num)
theorem B1250093 : Blo 738327 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B2495285 : Blo 738327 2495285 := bbase (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) (by norm_num)
theorem B889705 : Blo 738327 889705 := bbase (se 2 (by rfl) ⟨333639, by rfl⟩ : syracuseStep 889705 = 667279) (by norm_num)
theorem B791417 : Blo 738327 791417 := bbase (se 2 (by rfl) ⟨296781, by rfl⟩ : syracuseStep 791417 = 593563) (by norm_num)
theorem B1250221 : Blo 738327 1250221 := bbase (se 3 (by rfl) ⟨234416, by rfl⟩ : syracuseStep 1250221 = 468833) (by norm_num)
theorem B1872821 : Blo 738327 1872821 := bbase (se 5 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 1872821 = 175577) (by norm_num)
theorem B791489 : Blo 738327 791489 := bbase (se 2 (by rfl) ⟨296808, by rfl⟩ : syracuseStep 791489 = 593617) (by norm_num)
theorem B3085285 : Blo 738327 3085285 := bbase (se 4 (by rfl) ⟨289245, by rfl⟩ : syracuseStep 3085285 = 578491) (by norm_num)
theorem B1577981 : Blo 738327 1577981 := bbase (se 3 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 1577981 = 591743) (by norm_num)
theorem B1577989 : Blo 738327 1577989 := bbase (se 4 (by rfl) ⟨147936, by rfl⟩ : syracuseStep 1577989 = 295873) (by norm_num)
theorem B1250309 : Blo 738327 1250309 := bbase (se 4 (by rfl) ⟨117216, by rfl⟩ : syracuseStep 1250309 = 234433) (by norm_num)
theorem B3740741 : Blo 738327 3740741 := bbase (se 4 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 3740741 = 701389) (by norm_num)
theorem B791677 : Blo 738327 791677 := bbase (se 3 (by rfl) ⟨148439, by rfl⟩ : syracuseStep 791677 = 296879) (by norm_num)
theorem B1250437 : Blo 738327 1250437 := bbase (se 4 (by rfl) ⟨117228, by rfl⟩ : syracuseStep 1250437 = 234457) (by norm_num)
theorem B1053901 : Blo 738327 1053901 := bbase (se 3 (by rfl) ⟨197606, by rfl⟩ : syracuseStep 1053901 = 395213) (by norm_num)
theorem B1250525 : Blo 738327 1250525 := bbase (se 3 (by rfl) ⟨234473, by rfl⟩ : syracuseStep 1250525 = 468947) (by norm_num)
theorem B2495717 : Blo 738327 2495717 := bbase (se 4 (by rfl) ⟨233973, by rfl⟩ : syracuseStep 2495717 = 467947) (by norm_num)
theorem B1185005 : Blo 738327 1185005 := bbase (se 3 (by rfl) ⟨222188, by rfl⟩ : syracuseStep 1185005 = 444377) (by norm_num)
theorem B1873165 : Blo 738327 1873165 := bbase (se 3 (by rfl) ⟨351218, by rfl⟩ : syracuseStep 1873165 = 702437) (by norm_num)
theorem B791861 : Blo 738327 791861 := bbase (se 5 (by rfl) ⟨37118, by rfl⟩ : syracuseStep 791861 = 74237) (by norm_num)
theorem B1250653 : Blo 738327 1250653 := bbase (se 3 (by rfl) ⟨234497, by rfl⟩ : syracuseStep 1250653 = 468995) (by norm_num)
theorem B5051765 : Blo 738327 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B890233 : Blo 738327 890233 := bbase (se 2 (by rfl) ⟨333837, by rfl⟩ : syracuseStep 890233 = 667675) (by norm_num)
theorem B1873277 : Blo 738327 1873277 := bbase (se 3 (by rfl) ⟨351239, by rfl⟩ : syracuseStep 1873277 = 702479) (by norm_num)
theorem B1250741 : Blo 738327 1250741 := bbase (se 5 (by rfl) ⟨58628, by rfl⟩ : syracuseStep 1250741 = 117257) (by norm_num)
theorem B1185229 : Blo 738327 1185229 := bbase (se 3 (by rfl) ⟨222230, by rfl⟩ : syracuseStep 1185229 = 444461) (by norm_num)
theorem B1054237 : Blo 738327 1054237 := bbase (se 3 (by rfl) ⟨197669, by rfl⟩ : syracuseStep 1054237 = 395339) (by norm_num)
theorem B1250869 : Blo 738327 1250869 := bbase (se 5 (by rfl) ⟨58634, by rfl⟩ : syracuseStep 1250869 = 117269) (by norm_num)
theorem B1873469 : Blo 738327 1873469 := bbase (se 3 (by rfl) ⟨351275, by rfl⟩ : syracuseStep 1873469 = 702551) (by norm_num)
theorem B1250957 : Blo 738327 1250957 := bbase (se 3 (by rfl) ⟨234554, by rfl⟩ : syracuseStep 1250957 = 469109) (by norm_num)
theorem B2496149 : Blo 738327 2496149 := bbase (se 6 (by rfl) ⟨58503, by rfl⟩ : syracuseStep 2496149 = 117007) (by norm_num)
theorem B2103029 : Blo 738327 2103029 := bbase (se 5 (by rfl) ⟨98579, by rfl⟩ : syracuseStep 2103029 = 197159) (by norm_num)
theorem B1054453 : Blo 738327 1054453 := bbase (se 5 (by rfl) ⟨49427, by rfl⟩ : syracuseStep 1054453 = 98855) (by norm_num)
theorem B1251085 : Blo 738327 1251085 := bbase (se 3 (by rfl) ⟨234578, by rfl⟩ : syracuseStep 1251085 = 469157) (by norm_num)
theorem B1251173 : Blo 738327 1251173 := bbase (se 4 (by rfl) ⟨117297, by rfl⟩ : syracuseStep 1251173 = 234595) (by norm_num)
theorem B1873813 : Blo 738327 1873813 := bbase (se 6 (by rfl) ⟨43917, by rfl⟩ : syracuseStep 1873813 = 87835) (by norm_num)
theorem B1251301 : Blo 738327 1251301 := bbase (se 4 (by rfl) ⟨117309, by rfl⟩ : syracuseStep 1251301 = 234619) (by norm_num)
theorem B1873925 : Blo 738327 1873925 := bbase (se 4 (by rfl) ⟨175680, by rfl⟩ : syracuseStep 1873925 = 351361) (by norm_num)
theorem B792613 : Blo 738327 792613 := bbase (se 4 (by rfl) ⟨74307, by rfl⟩ : syracuseStep 792613 = 148615) (by norm_num)
theorem B1251389 : Blo 738327 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B2496581 : Blo 738327 2496581 := bbase (se 4 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 2496581 = 468109) (by norm_num)
theorem B1579117 : Blo 738327 1579117 := bbase (se 3 (by rfl) ⟨296084, by rfl⟩ : syracuseStep 1579117 = 592169) (by norm_num)
theorem B1054829 : Blo 738327 1054829 := bbase (se 3 (by rfl) ⟨197780, by rfl⟩ : syracuseStep 1054829 = 395561) (by norm_num)
theorem B792685 : Blo 738327 792685 := bbase (se 3 (by rfl) ⟨148628, by rfl⟩ : syracuseStep 792685 = 297257) (by norm_num)
theorem B1251517 : Blo 738327 1251517 := bbase (se 3 (by rfl) ⟨234659, by rfl⟩ : syracuseStep 1251517 = 469319) (by norm_num)
theorem B1874117 : Blo 738327 1874117 := bbase (se 4 (by rfl) ⟨175698, by rfl⟩ : syracuseStep 1874117 = 351397) (by norm_num)
theorem B1251605 : Blo 738327 1251605 := bbase (se 6 (by rfl) ⟨29334, by rfl⟩ : syracuseStep 1251605 = 58669) (by norm_num)
theorem B3742037 : Blo 738327 3742037 := bbase (se 10 (by rfl) ⟨5481, by rfl⟩ : syracuseStep 3742037 = 10963) (by norm_num)
theorem B1251733 : Blo 738327 1251733 := bbase (se 6 (by rfl) ⟨29337, by rfl⟩ : syracuseStep 1251733 = 58675) (by norm_num)
theorem B891329 : Blo 738327 891329 := bbase (se 2 (by rfl) ⟨334248, by rfl⟩ : syracuseStep 891329 = 668497) (by norm_num)
theorem B1579493 : Blo 738327 1579493 := bbase (se 4 (by rfl) ⟨148077, by rfl⟩ : syracuseStep 1579493 = 296155) (by norm_num)
theorem B1251821 : Blo 738327 1251821 := bbase (se 3 (by rfl) ⟨234716, by rfl⟩ : syracuseStep 1251821 = 469433) (by norm_num)
theorem B2497013 : Blo 738327 2497013 := bbase (se 5 (by rfl) ⟨117047, by rfl⟩ : syracuseStep 2497013 = 234095) (by norm_num)
theorem B1874461 : Blo 738327 1874461 := bbase (se 3 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 1874461 = 702923) (by norm_num)
theorem B1776181 : Blo 738327 1776181 := bbase (se 5 (by rfl) ⟨83258, by rfl⟩ : syracuseStep 1776181 = 166517) (by norm_num)
theorem B1251949 : Blo 738327 1251949 := bbase (se 3 (by rfl) ⟨234740, by rfl⟩ : syracuseStep 1251949 = 469481) (by norm_num)
theorem B1874573 : Blo 738327 1874573 := bbase (se 3 (by rfl) ⟨351482, by rfl⟩ : syracuseStep 1874573 = 702965) (by norm_num)
theorem B1252037 : Blo 738327 1252037 := bbase (se 4 (by rfl) ⟨117378, by rfl⟩ : syracuseStep 1252037 = 234757) (by norm_num)
theorem B3414757 : Blo 738327 3414757 := bbase (se 4 (by rfl) ⟨320133, by rfl⟩ : syracuseStep 3414757 = 640267) (by norm_num)
theorem B1252165 : Blo 738327 1252165 := bbase (se 4 (by rfl) ⟨117390, by rfl⟩ : syracuseStep 1252165 = 234781) (by norm_num)
theorem B1874765 : Blo 738327 1874765 := bbase (se 3 (by rfl) ⟨351518, by rfl⟩ : syracuseStep 1874765 = 703037) (by norm_num)
theorem B2366293 : Blo 738327 2366293 := bbase (se 9 (by rfl) ⟨6932, by rfl⟩ : syracuseStep 2366293 = 13865) (by norm_num)
theorem B1186645 : Blo 738327 1186645 := bbase (se 9 (by rfl) ⟨3476, by rfl⟩ : syracuseStep 1186645 = 6953) (by norm_num)
theorem B2104213 : Blo 738327 2104213 := bbase (se 6 (by rfl) ⟨49317, by rfl⟩ : syracuseStep 2104213 = 98635) (by norm_num)
theorem B1252253 : Blo 738327 1252253 := bbase (se 3 (by rfl) ⟨234797, by rfl⟩ : syracuseStep 1252253 = 469595) (by norm_num)
theorem B2497445 : Blo 738327 2497445 := bbase (se 4 (by rfl) ⟨234135, by rfl⟩ : syracuseStep 2497445 = 468271) (by norm_num)
theorem B2562997 : Blo 738327 2562997 := bbase (se 5 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 2562997 = 240281) (by norm_num)
theorem B1252381 : Blo 738327 1252381 := bbase (se 3 (by rfl) ⟨234821, by rfl⟩ : syracuseStep 1252381 = 469643) (by norm_num)
theorem B2104373 : Blo 738327 2104373 := bbase (se 5 (by rfl) ⟨98642, by rfl⟩ : syracuseStep 2104373 = 197285) (by norm_num)
theorem B2661461 : Blo 738327 2661461 := bbase (se 8 (by rfl) ⟨15594, by rfl⟩ : syracuseStep 2661461 = 31189) (by norm_num)
theorem B1186901 : Blo 738327 1186901 := bbase (se 8 (by rfl) ⟨6954, by rfl⟩ : syracuseStep 1186901 = 13909) (by norm_num)
theorem B1252469 : Blo 738327 1252469 := bbase (se 5 (by rfl) ⟨58709, by rfl⟩ : syracuseStep 1252469 = 117419) (by norm_num)
theorem B1875109 : Blo 738327 1875109 := bbase (se 4 (by rfl) ⟨175791, by rfl⟩ : syracuseStep 1875109 = 351583) (by norm_num)
theorem B1252597 : Blo 738327 1252597 := bbase (se 5 (by rfl) ⟨58715, by rfl⟩ : syracuseStep 1252597 = 117431) (by norm_num)
theorem B1875221 : Blo 738327 1875221 := bbase (se 6 (by rfl) ⟨43950, by rfl⟩ : syracuseStep 1875221 = 87901) (by norm_num)
theorem B1187093 : Blo 738327 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B2104613 : Blo 738327 2104613 := bbase (se 4 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 2104613 = 394615) (by norm_num)
theorem B2497877 : Blo 738327 2497877 := bbase (se 11 (by rfl) ⟨1829, by rfl⟩ : syracuseStep 2497877 = 3659) (by norm_num)
theorem B5610869 : Blo 738327 5610869 := bbase (se 5 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 5610869 = 526019) (by norm_num)
theorem B3612053 : Blo 738327 3612053 := bbase (se 6 (by rfl) ⟨84657, by rfl⟩ : syracuseStep 3612053 = 169315) (by norm_num)
theorem B1875413 : Blo 738327 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B2104805 : Blo 738327 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B1056253 : Blo 738327 1056253 := bbase (se 3 (by rfl) ⟨198047, by rfl⟩ : syracuseStep 1056253 = 396095) (by norm_num)
theorem B3743333 : Blo 738327 3743333 := bbase (se 4 (by rfl) ⟨350937, by rfl⟩ : syracuseStep 3743333 = 701875) (by norm_num)
theorem B6004469 : Blo 738327 6004469 := bbase (se 5 (by rfl) ⟨281459, by rfl⟩ : syracuseStep 6004469 = 562919) (by norm_num)
theorem B2498309 : Blo 738327 2498309 := bbase (se 4 (by rfl) ⟨234216, by rfl⟩ : syracuseStep 2498309 = 468433) (by norm_num)
theorem B1875757 : Blo 738327 1875757 := bbase (se 3 (by rfl) ⟨351704, by rfl⟩ : syracuseStep 1875757 = 703409) (by norm_num)
theorem B1777565 : Blo 738327 1777565 := bbase (se 3 (by rfl) ⟨333293, by rfl⟩ : syracuseStep 1777565 = 666587) (by norm_num)
theorem B1875869 : Blo 738327 1875869 := bbase (se 3 (by rfl) ⟨351725, by rfl⟩ : syracuseStep 1875869 = 703451) (by norm_num)
theorem B2400245 : Blo 738327 2400245 := bbase (se 5 (by rfl) ⟨112511, by rfl⟩ : syracuseStep 2400245 = 225023) (by norm_num)
theorem B1581133 : Blo 738327 1581133 := bbase (se 3 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 1581133 = 592925) (by norm_num)
theorem B1056845 : Blo 738327 1056845 := bbase (se 3 (by rfl) ⟨198158, by rfl⟩ : syracuseStep 1056845 = 396317) (by norm_num)
theorem B1876061 : Blo 738327 1876061 := bbase (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) (by norm_num)
theorem B1056925 : Blo 738327 1056925 := bbase (se 3 (by rfl) ⟨198173, by rfl⟩ : syracuseStep 1056925 = 396347) (by norm_num)
theorem B2498741 : Blo 738327 2498741 := bbase (se 5 (by rfl) ⟨117128, by rfl⟩ : syracuseStep 2498741 = 234257) (by norm_num)
theorem B1188029 : Blo 738327 1188029 := bbase (se 3 (by rfl) ⟨222755, by rfl⟩ : syracuseStep 1188029 = 445511) (by norm_num)
theorem B3154133 : Blo 738327 3154133 := bbase (se 7 (by rfl) ⟨36962, by rfl⟩ : syracuseStep 3154133 = 73925) (by norm_num)
theorem B1777997 : Blo 738327 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B2662741 : Blo 738327 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B1876405 : Blo 738327 1876405 := bbase (se 5 (by rfl) ⟨87956, by rfl⟩ : syracuseStep 1876405 = 175913) (by norm_num)
theorem B3154373 : Blo 738327 3154373 := bbase (se 4 (by rfl) ⟨295722, by rfl⟩ : syracuseStep 3154373 = 591445) (by norm_num)
theorem B2105797 : Blo 738327 2105797 := bbase (se 4 (by rfl) ⟨197418, by rfl⟩ : syracuseStep 2105797 = 394837) (by norm_num)
theorem B1876517 : Blo 738327 1876517 := bbase (se 4 (by rfl) ⟨175923, by rfl⟩ : syracuseStep 1876517 = 351847) (by norm_num)
theorem B2531893 : Blo 738327 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B1188413 : Blo 738327 1188413 := bbase (se 3 (by rfl) ⟨222827, by rfl⟩ : syracuseStep 1188413 = 445655) (by norm_num)
theorem B2499173 : Blo 738327 2499173 := bbase (se 4 (by rfl) ⟨234297, by rfl⟩ : syracuseStep 2499173 = 468595) (by norm_num)
theorem B1352341 : Blo 738327 1352341 := bbase (se 6 (by rfl) ⟨31695, by rfl⟩ : syracuseStep 1352341 = 63391) (by norm_num)
theorem B1188541 : Blo 738327 1188541 := bbase (se 3 (by rfl) ⟨222851, by rfl⟩ : syracuseStep 1188541 = 445703) (by norm_num)
theorem B1876709 : Blo 738327 1876709 := bbase (se 4 (by rfl) ⟨175941, by rfl⟩ : syracuseStep 1876709 = 351883) (by norm_num)
theorem B3744629 : Blo 738327 3744629 := bbase (se 5 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 3744629 = 351059) (by norm_num)
theorem B1582021 : Blo 738327 1582021 := bbase (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) (by norm_num)
theorem B2499605 : Blo 738327 2499605 := bbase (se 6 (by rfl) ⟨58584, by rfl⟩ : syracuseStep 2499605 = 117169) (by norm_num)
theorem B1877053 : Blo 738327 1877053 := bbase (se 3 (by rfl) ⟨351947, by rfl⟩ : syracuseStep 1877053 = 703895) (by norm_num)
theorem B1877165 : Blo 738327 1877165 := bbase (se 3 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 1877165 = 703937) (by norm_num)
theorem B1877357 : Blo 738327 1877357 := bbase (se 3 (by rfl) ⟨352004, by rfl⟩ : syracuseStep 1877357 = 704009) (by norm_num)
theorem B1582517 : Blo 738327 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B2500037 : Blo 738327 2500037 := bbase (se 4 (by rfl) ⟨234378, by rfl⟩ : syracuseStep 2500037 = 468757) (by norm_num)
theorem B2106901 : Blo 738327 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B2369189 : Blo 738327 2369189 := bbase (se 4 (by rfl) ⟨222111, by rfl⟩ : syracuseStep 2369189 = 444223) (by norm_num)
theorem B1877701 : Blo 738327 1877701 := bbase (se 4 (by rfl) ⟨176034, by rfl⟩ : syracuseStep 1877701 = 352069) (by norm_num)
theorem B1877813 : Blo 738327 1877813 := bbase (se 5 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 1877813 = 176045) (by norm_num)
theorem B2500469 : Blo 738327 2500469 := bbase (se 5 (by rfl) ⟨117209, by rfl⟩ : syracuseStep 2500469 = 234419) (by norm_num)
theorem B1124221 : Blo 738327 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B12036053 : Blo 738327 12036053 := bbase (se 7 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 12036053 = 282095) (by norm_num)
theorem B1878005 : Blo 738327 1878005 := bbase (se 5 (by rfl) ⟨88031, by rfl⟩ : syracuseStep 1878005 = 176063) (by norm_num)
theorem B4499509 : Blo 738327 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B3745925 : Blo 738327 3745925 := bbase (se 4 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 3745925 = 702361) (by norm_num)
theorem B6334645 : Blo 738327 6334645 := bbase (se 5 (by rfl) ⟨296936, by rfl⟩ : syracuseStep 6334645 = 593873) (by norm_num)
theorem B1583381 : Blo 738327 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B2500901 : Blo 738327 2500901 := bbase (se 4 (by rfl) ⟨234459, by rfl⟩ : syracuseStep 2500901 = 468919) (by norm_num)
theorem B1878349 : Blo 738327 1878349 := bbase (se 3 (by rfl) ⟨352190, by rfl⟩ : syracuseStep 1878349 = 704381) (by norm_num)
theorem B7317845 : Blo 738327 7317845 := bbase (se 10 (by rfl) ⟨10719, by rfl⟩ : syracuseStep 7317845 = 21439) (by norm_num)
theorem B1583525 : Blo 738327 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B1878461 : Blo 738327 1878461 := bbase (se 3 (by rfl) ⟨352211, by rfl⟩ : syracuseStep 1878461 = 704423) (by norm_num)
theorem B1878653 : Blo 738327 1878653 := bbase (se 3 (by rfl) ⟨352247, by rfl⟩ : syracuseStep 1878653 = 704495) (by norm_num)
theorem B3156661 : Blo 738327 3156661 := bbase (se 5 (by rfl) ⟨147968, by rfl⟩ : syracuseStep 3156661 = 295937) (by norm_num)
theorem B2501333 : Blo 738327 2501333 := bbase (se 7 (by rfl) ⟨29312, by rfl⟩ : syracuseStep 2501333 = 58625) (by norm_num)
theorem B1878997 : Blo 738327 1878997 := bbase (se 7 (by rfl) ⟨22019, by rfl⟩ : syracuseStep 1878997 = 44039) (by norm_num)
theorem B1354733 : Blo 738327 1354733 := bbase (se 3 (by rfl) ⟨254012, by rfl⟩ : syracuseStep 1354733 = 508025) (by norm_num)
theorem B2108405 : Blo 738327 2108405 := bbase (se 5 (by rfl) ⟨98831, by rfl⟩ : syracuseStep 2108405 = 197663) (by norm_num)
theorem B1125389 : Blo 738327 1125389 := bbase (se 3 (by rfl) ⟨211010, by rfl⟩ : syracuseStep 1125389 = 422021) (by norm_num)
theorem B2501765 : Blo 738327 2501765 := bbase (se 4 (by rfl) ⟨234540, by rfl⟩ : syracuseStep 2501765 = 469081) (by norm_num)
theorem B1584269 : Blo 738327 1584269 := bbase (se 3 (by rfl) ⟨297050, by rfl⟩ : syracuseStep 1584269 = 594101) (by norm_num)
theorem B830641 : Blo 738327 830641 := bbase (se 2 (by rfl) ⟨311490, by rfl⟩ : syracuseStep 830641 = 622981) (by norm_num)
theorem B830677 : Blo 738327 830677 := bbase (se 7 (by rfl) ⟨9734, by rfl⟩ : syracuseStep 830677 = 19469) (by norm_num)
theorem B830713 : Blo 738327 830713 := bbase (se 2 (by rfl) ⟨311517, by rfl⟩ : syracuseStep 830713 = 623035) (by norm_num)
theorem B830749 : Blo 738327 830749 := bbase (se 3 (by rfl) ⟨155765, by rfl⟩ : syracuseStep 830749 = 311531) (by norm_num)
theorem B830785 : Blo 738327 830785 := bbase (se 2 (by rfl) ⟨311544, by rfl⟩ : syracuseStep 830785 = 623089) (by norm_num)
theorem B830821 : Blo 738327 830821 := bbase (se 4 (by rfl) ⟨77889, by rfl⟩ : syracuseStep 830821 = 155779) (by norm_num)
theorem B830857 : Blo 738327 830857 := bbase (se 2 (by rfl) ⟨311571, by rfl⟩ : syracuseStep 830857 = 623143) (by norm_num)
theorem B3747221 : Blo 738327 3747221 := bbase (se 6 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 3747221 = 175651) (by norm_num)
theorem B830893 : Blo 738327 830893 := bbase (se 3 (by rfl) ⟨155792, by rfl⟩ : syracuseStep 830893 = 311585) (by norm_num)
theorem B830929 : Blo 738327 830929 := bbase (se 2 (by rfl) ⟨311598, by rfl⟩ : syracuseStep 830929 = 623197) (by norm_num)
theorem B830965 : Blo 738327 830965 := bbase (se 5 (by rfl) ⟨38951, by rfl⟩ : syracuseStep 830965 = 77903) (by norm_num)
theorem B831001 : Blo 738327 831001 := bbase (se 2 (by rfl) ⟨311625, by rfl⟩ : syracuseStep 831001 = 623251) (by norm_num)
theorem B2502197 : Blo 738327 2502197 := bbase (se 5 (by rfl) ⟨117290, by rfl⟩ : syracuseStep 2502197 = 234581) (by norm_num)
theorem B831037 : Blo 738327 831037 := bbase (se 3 (by rfl) ⟨155819, by rfl⟩ : syracuseStep 831037 = 311639) (by norm_num)
theorem B831073 : Blo 738327 831073 := bbase (se 2 (by rfl) ⟨311652, by rfl⟩ : syracuseStep 831073 = 623305) (by norm_num)
theorem B831109 : Blo 738327 831109 := bbase (se 4 (by rfl) ⟨77916, by rfl⟩ : syracuseStep 831109 = 155833) (by norm_num)
theorem B1781389 : Blo 738327 1781389 := bbase (se 3 (by rfl) ⟨334010, by rfl⟩ : syracuseStep 1781389 = 668021) (by norm_num)
theorem B7614101 : Blo 738327 7614101 := bbase (se 6 (by rfl) ⟨178455, by rfl⟩ : syracuseStep 7614101 = 356911) (by norm_num)
theorem B831145 : Blo 738327 831145 := bbase (se 2 (by rfl) ⟨311679, by rfl⟩ : syracuseStep 831145 = 623359) (by norm_num)
theorem B831181 : Blo 738327 831181 := bbase (se 3 (by rfl) ⟨155846, by rfl⟩ : syracuseStep 831181 = 311693) (by norm_num)
theorem B831217 : Blo 738327 831217 := bbase (se 2 (by rfl) ⟨311706, by rfl⟩ : syracuseStep 831217 = 623413) (by norm_num)
theorem B831253 : Blo 738327 831253 := bbase (se 6 (by rfl) ⟨19482, by rfl⟩ : syracuseStep 831253 = 38965) (by norm_num)
theorem B831289 : Blo 738327 831289 := bbase (se 2 (by rfl) ⟨311733, by rfl⟩ : syracuseStep 831289 = 623467) (by norm_num)
theorem B831325 : Blo 738327 831325 := bbase (se 3 (by rfl) ⟨155873, by rfl⟩ : syracuseStep 831325 = 311747) (by norm_num)
theorem B1585021 : Blo 738327 1585021 := bbase (se 3 (by rfl) ⟨297191, by rfl⟩ : syracuseStep 1585021 = 594383) (by norm_num)
theorem B831361 : Blo 738327 831361 := bbase (se 2 (by rfl) ⟨311760, by rfl⟩ : syracuseStep 831361 = 623521) (by norm_num)
theorem B831397 : Blo 738327 831397 := bbase (se 4 (by rfl) ⟨77943, by rfl⟩ : syracuseStep 831397 = 155887) (by norm_num)
theorem B831433 : Blo 738327 831433 := bbase (se 2 (by rfl) ⟨311787, by rfl⟩ : syracuseStep 831433 = 623575) (by norm_num)
theorem B2502629 : Blo 738327 2502629 := bbase (se 4 (by rfl) ⟨234621, by rfl⟩ : syracuseStep 2502629 = 469243) (by norm_num)
theorem B831469 : Blo 738327 831469 := bbase (se 3 (by rfl) ⟨155900, by rfl⟩ : syracuseStep 831469 = 311801) (by norm_num)
theorem B1585165 : Blo 738327 1585165 := bbase (se 3 (by rfl) ⟨297218, by rfl⟩ : syracuseStep 1585165 = 594437) (by norm_num)
theorem B831505 : Blo 738327 831505 := bbase (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) (by norm_num)
theorem B831541 : Blo 738327 831541 := bbase (se 5 (by rfl) ⟨38978, by rfl⟩ : syracuseStep 831541 = 77957) (by norm_num)
theorem B1781813 : Blo 738327 1781813 := bbase (se 5 (by rfl) ⟨83522, by rfl⟩ : syracuseStep 1781813 = 167045) (by norm_num)
theorem B831577 : Blo 738327 831577 := bbase (se 2 (by rfl) ⟨311841, by rfl⟩ : syracuseStep 831577 = 623683) (by norm_num)
theorem B1650797 : Blo 738327 1650797 := bbase (se 3 (by rfl) ⟨309524, by rfl⟩ : syracuseStep 1650797 = 619049) (by norm_num)
theorem B6336629 : Blo 738327 6336629 := bbase (se 5 (by rfl) ⟨297029, by rfl⟩ : syracuseStep 6336629 = 594059) (by norm_num)
theorem B831613 : Blo 738327 831613 := bbase (se 3 (by rfl) ⟨155927, by rfl⟩ : syracuseStep 831613 = 311855) (by norm_num)
theorem B3158149 : Blo 738327 3158149 := bbase (se 4 (by rfl) ⟨296076, by rfl⟩ : syracuseStep 3158149 = 592153) (by norm_num)
theorem B3158165 : Blo 738327 3158165 := bbase (se 6 (by rfl) ⟨74019, by rfl⟩ : syracuseStep 3158165 = 148039) (by norm_num)
theorem B831649 : Blo 738327 831649 := bbase (se 2 (by rfl) ⟨311868, by rfl⟩ : syracuseStep 831649 = 623737) (by norm_num)
theorem B831685 : Blo 738327 831685 := bbase (se 4 (by rfl) ⟨77970, by rfl⟩ : syracuseStep 831685 = 155941) (by norm_num)
theorem B831721 : Blo 738327 831721 := bbase (se 2 (by rfl) ⟨311895, by rfl⟩ : syracuseStep 831721 = 623791) (by norm_num)
theorem B831757 : Blo 738327 831757 := bbase (se 3 (by rfl) ⟨155954, by rfl⟩ : syracuseStep 831757 = 311909) (by norm_num)
theorem B831793 : Blo 738327 831793 := bbase (se 2 (by rfl) ⟨311922, by rfl⟩ : syracuseStep 831793 = 623845) (by norm_num)
theorem B831829 : Blo 738327 831829 := bbase (se 10 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 831829 = 2437) (by norm_num)
theorem B2666837 : Blo 738327 2666837 := bbase (se 10 (by rfl) ⟨3906, by rfl⟩ : syracuseStep 2666837 = 7813) (by norm_num)
theorem B1782101 : Blo 738327 1782101 := bbase (se 10 (by rfl) ⟨2610, by rfl⟩ : syracuseStep 1782101 = 5221) (by norm_num)
theorem B831865 : Blo 738327 831865 := bbase (se 2 (by rfl) ⟨311949, by rfl⟩ : syracuseStep 831865 = 623899) (by norm_num)
theorem B2503061 : Blo 738327 2503061 := bbase (se 6 (by rfl) ⟨58665, by rfl⟩ : syracuseStep 2503061 = 117331) (by norm_num)
theorem B831901 : Blo 738327 831901 := bbase (se 3 (by rfl) ⟨155981, by rfl⟩ : syracuseStep 831901 = 311963) (by norm_num)
theorem B831937 : Blo 738327 831937 := bbase (se 2 (by rfl) ⟨311976, by rfl⟩ : syracuseStep 831937 = 623953) (by norm_num)
theorem B2994661 : Blo 738327 2994661 := bbase (se 4 (by rfl) ⟨280749, by rfl⟩ : syracuseStep 2994661 = 561499) (by norm_num)
theorem B831973 : Blo 738327 831973 := bbase (se 4 (by rfl) ⟨77997, by rfl⟩ : syracuseStep 831973 = 155995) (by norm_num)
theorem B832009 : Blo 738327 832009 := bbase (se 2 (by rfl) ⟨312003, by rfl⟩ : syracuseStep 832009 = 624007) (by norm_num)
theorem B2109989 : Blo 738327 2109989 := bbase (se 4 (by rfl) ⟨197811, by rfl⟩ : syracuseStep 2109989 = 395623) (by norm_num)
theorem B832045 : Blo 738327 832045 := bbase (se 3 (by rfl) ⟨156008, by rfl⟩ : syracuseStep 832045 = 312017) (by norm_num)
theorem B832081 : Blo 738327 832081 := bbase (se 2 (by rfl) ⟨312030, by rfl⟩ : syracuseStep 832081 = 624061) (by norm_num)
theorem B1684061 : Blo 738327 1684061 := bbase (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) (by norm_num)
theorem B799345 : Blo 738327 799345 := bbase (se 2 (by rfl) ⟨299754, by rfl⟩ : syracuseStep 799345 = 599509) (by norm_num)
theorem B832117 : Blo 738327 832117 := bbase (se 5 (by rfl) ⟨39005, by rfl⟩ : syracuseStep 832117 = 78011) (by norm_num)
theorem B832153 : Blo 738327 832153 := bbase (se 2 (by rfl) ⟨312057, by rfl⟩ : syracuseStep 832153 = 624115) (by norm_num)
theorem B3748517 : Blo 738327 3748517 := bbase (se 4 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 3748517 = 702847) (by norm_num)
theorem B832189 : Blo 738327 832189 := bbase (se 3 (by rfl) ⟨156035, by rfl⟩ : syracuseStep 832189 = 312071) (by norm_num)
theorem B832225 : Blo 738327 832225 := bbase (se 2 (by rfl) ⟨312084, by rfl⟩ : syracuseStep 832225 = 624169) (by norm_num)
theorem B2372341 : Blo 738327 2372341 := bbase (se 5 (by rfl) ⟨111203, by rfl⟩ : syracuseStep 2372341 = 222407) (by norm_num)
theorem B832261 : Blo 738327 832261 := bbase (se 4 (by rfl) ⟨78024, by rfl⟩ : syracuseStep 832261 = 156049) (by norm_num)
theorem B2667269 : Blo 738327 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B832297 : Blo 738327 832297 := bbase (se 2 (by rfl) ⟨312111, by rfl⟩ : syracuseStep 832297 = 624223) (by norm_num)
theorem B2503493 : Blo 738327 2503493 := bbase (se 4 (by rfl) ⟨234702, by rfl⟩ : syracuseStep 2503493 = 469405) (by norm_num)
theorem B832333 : Blo 738327 832333 := bbase (se 3 (by rfl) ⟨156062, by rfl⟩ : syracuseStep 832333 = 312125) (by norm_num)
theorem B832369 : Blo 738327 832369 := bbase (se 2 (by rfl) ⟨312138, by rfl⟩ : syracuseStep 832369 = 624277) (by norm_num)
theorem B799621 : Blo 738327 799621 := bbase (se 4 (by rfl) ⟨74964, by rfl⟩ : syracuseStep 799621 = 149929) (by norm_num)
theorem B832405 : Blo 738327 832405 := bbase (se 6 (by rfl) ⟨19509, by rfl⟩ : syracuseStep 832405 = 39019) (by norm_num)
theorem B832441 : Blo 738327 832441 := bbase (se 2 (by rfl) ⟨312165, by rfl⟩ : syracuseStep 832441 = 624331) (by norm_num)
theorem B832477 : Blo 738327 832477 := bbase (se 3 (by rfl) ⟨156089, by rfl⟩ : syracuseStep 832477 = 312179) (by norm_num)
theorem B832513 : Blo 738327 832513 := bbase (se 2 (by rfl) ⟨312192, by rfl⟩ : syracuseStep 832513 = 624385) (by norm_num)
theorem B832549 : Blo 738327 832549 := bbase (se 4 (by rfl) ⟨78051, by rfl⟩ : syracuseStep 832549 = 156103) (by norm_num)
theorem B832585 : Blo 738327 832585 := bbase (se 2 (by rfl) ⟨312219, by rfl⟩ : syracuseStep 832585 = 624439) (by norm_num)
theorem B832621 : Blo 738327 832621 := bbase (se 3 (by rfl) ⟨156116, by rfl⟩ : syracuseStep 832621 = 312233) (by norm_num)
theorem B832657 : Blo 738327 832657 := bbase (se 2 (by rfl) ⟨312246, by rfl⟩ : syracuseStep 832657 = 624493) (by norm_num)
theorem B832693 : Blo 738327 832693 := bbase (se 5 (by rfl) ⟨39032, by rfl⟩ : syracuseStep 832693 = 78065) (by norm_num)
theorem B2110661 : Blo 738327 2110661 := bbase (se 4 (by rfl) ⟨197874, by rfl⟩ : syracuseStep 2110661 = 395749) (by norm_num)
theorem B4011221 : Blo 738327 4011221 := bbase (se 7 (by rfl) ⟨47006, by rfl⟩ : syracuseStep 4011221 = 94013) (by norm_num)
theorem B832729 : Blo 738327 832729 := bbase (se 2 (by rfl) ⟨312273, by rfl⟩ : syracuseStep 832729 = 624547) (by norm_num)
theorem B2503925 : Blo 738327 2503925 := bbase (se 5 (by rfl) ⟨117371, by rfl⟩ : syracuseStep 2503925 = 234743) (by norm_num)
theorem B832765 : Blo 738327 832765 := bbase (se 3 (by rfl) ⟨156143, by rfl⟩ : syracuseStep 832765 = 312287) (by norm_num)
theorem B832801 : Blo 738327 832801 := bbase (se 2 (by rfl) ⟨312300, by rfl⟩ : syracuseStep 832801 = 624601) (by norm_num)
theorem B832837 : Blo 738327 832837 := bbase (se 4 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 832837 = 156157) (by norm_num)
theorem B832873 : Blo 738327 832873 := bbase (se 2 (by rfl) ⟨312327, by rfl⟩ : syracuseStep 832873 = 624655) (by norm_num)
theorem B832909 : Blo 738327 832909 := bbase (se 3 (by rfl) ⟨156170, by rfl⟩ : syracuseStep 832909 = 312341) (by norm_num)
theorem B1684909 : Blo 738327 1684909 := bbase (se 3 (by rfl) ⟨315920, by rfl⟩ : syracuseStep 1684909 = 631841) (by norm_num)
theorem B832945 : Blo 738327 832945 := bbase (se 2 (by rfl) ⟨312354, by rfl⟩ : syracuseStep 832945 = 624709) (by norm_num)
theorem B832981 : Blo 738327 832981 := bbase (se 7 (by rfl) ⟨9761, by rfl⟩ : syracuseStep 832981 = 19523) (by norm_num)
theorem B833017 : Blo 738327 833017 := bbase (se 2 (by rfl) ⟨312381, by rfl⟩ : syracuseStep 833017 = 624763) (by norm_num)
theorem B833053 : Blo 738327 833053 := bbase (se 3 (by rfl) ⟨156197, by rfl⟩ : syracuseStep 833053 = 312395) (by norm_num)
theorem B833089 : Blo 738327 833089 := bbase (se 2 (by rfl) ⟨312408, by rfl⟩ : syracuseStep 833089 = 624817) (by norm_num)
theorem B833125 : Blo 738327 833125 := bbase (se 4 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 833125 = 156211) (by norm_num)
theorem B2111093 : Blo 738327 2111093 := bbase (se 5 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 2111093 = 197915) (by norm_num)
theorem B833161 : Blo 738327 833161 := bbase (se 2 (by rfl) ⟨312435, by rfl⟩ : syracuseStep 833161 = 624871) (by norm_num)
theorem B9483925 : Blo 738327 9483925 := bbase (se 6 (by rfl) ⟨222279, by rfl⟩ : syracuseStep 9483925 = 444559) (by norm_num)
theorem B2504357 : Blo 738327 2504357 := bbase (se 4 (by rfl) ⟨234783, by rfl⟩ : syracuseStep 2504357 = 469567) (by norm_num)
theorem B833197 : Blo 738327 833197 := bbase (se 3 (by rfl) ⟨156224, by rfl⟩ : syracuseStep 833197 = 312449) (by norm_num)
theorem B833233 : Blo 738327 833233 := bbase (se 2 (by rfl) ⟨312462, by rfl⟩ : syracuseStep 833233 = 624925) (by norm_num)
theorem B833269 : Blo 738327 833269 := bbase (se 5 (by rfl) ⟨39059, by rfl⟩ : syracuseStep 833269 = 78119) (by norm_num)
theorem B833305 : Blo 738327 833305 := bbase (se 2 (by rfl) ⟨312489, by rfl⟩ : syracuseStep 833305 = 624979) (by norm_num)
theorem B833341 : Blo 738327 833341 := bbase (se 3 (by rfl) ⟨156251, by rfl⟩ : syracuseStep 833341 = 312503) (by norm_num)
theorem B1128253 : Blo 738327 1128253 := bbase (se 3 (by rfl) ⟨211547, by rfl⟩ : syracuseStep 1128253 = 423095) (by norm_num)
theorem B833377 : Blo 738327 833377 := bbase (se 2 (by rfl) ⟨312516, by rfl⟩ : syracuseStep 833377 = 625033) (by norm_num)
theorem B4732789 : Blo 738327 4732789 := bbase (se 5 (by rfl) ⟨221849, by rfl⟩ : syracuseStep 4732789 = 443699) (by norm_num)
theorem B833413 : Blo 738327 833413 := bbase (se 4 (by rfl) ⟨78132, by rfl⟩ : syracuseStep 833413 = 156265) (by norm_num)
theorem B833449 : Blo 738327 833449 := bbase (se 2 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 833449 = 625087) (by norm_num)
theorem B3749813 : Blo 738327 3749813 := bbase (se 5 (by rfl) ⟨175772, by rfl⟩ : syracuseStep 3749813 = 351545) (by norm_num)
theorem B833485 : Blo 738327 833485 := bbase (se 3 (by rfl) ⟨156278, by rfl⟩ : syracuseStep 833485 = 312557) (by norm_num)
theorem B833521 : Blo 738327 833521 := bbase (se 2 (by rfl) ⟨312570, by rfl⟩ : syracuseStep 833521 = 625141) (by norm_num)
theorem B833557 : Blo 738327 833557 := bbase (se 6 (by rfl) ⟨19536, by rfl⟩ : syracuseStep 833557 = 39073) (by norm_num)
theorem B833593 : Blo 738327 833593 := bbase (se 2 (by rfl) ⟨312597, by rfl⟩ : syracuseStep 833593 = 625195) (by norm_num)
theorem B800833 : Blo 738327 800833 := bbase (se 2 (by rfl) ⟨300312, by rfl⟩ : syracuseStep 800833 = 600625) (by norm_num)
theorem B2504789 : Blo 738327 2504789 := bbase (se 8 (by rfl) ⟨14676, by rfl⟩ : syracuseStep 2504789 = 29353) (by norm_num)
theorem B833629 : Blo 738327 833629 := bbase (se 3 (by rfl) ⟨156305, by rfl⟩ : syracuseStep 833629 = 312611) (by norm_num)
theorem B3553397 : Blo 738327 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B833665 : Blo 738327 833665 := bbase (se 2 (by rfl) ⟨312624, by rfl⟩ : syracuseStep 833665 = 625249) (by norm_num)
theorem B833701 : Blo 738327 833701 := bbase (se 4 (by rfl) ⟨78159, by rfl⟩ : syracuseStep 833701 = 156319) (by norm_num)
theorem B833737 : Blo 738327 833737 := bbase (se 2 (by rfl) ⟨312651, by rfl⟩ : syracuseStep 833737 = 625303) (by norm_num)
theorem B833773 : Blo 738327 833773 := bbase (se 3 (by rfl) ⟨156332, by rfl⟩ : syracuseStep 833773 = 312665) (by norm_num)
theorem B833809 : Blo 738327 833809 := bbase (se 2 (by rfl) ⟨312678, by rfl⟩ : syracuseStep 833809 = 625357) (by norm_num)
theorem B833845 : Blo 738327 833845 := bbase (se 5 (by rfl) ⟨39086, by rfl⟩ : syracuseStep 833845 = 78173) (by norm_num)
theorem B833881 : Blo 738327 833881 := bbase (se 2 (by rfl) ⟨312705, by rfl⟩ : syracuseStep 833881 = 625411) (by norm_num)
theorem B3160421 : Blo 738327 3160421 := bbase (se 4 (by rfl) ⟨296289, by rfl⟩ : syracuseStep 3160421 = 592579) (by norm_num)
theorem B2111845 : Blo 738327 2111845 := bbase (se 4 (by rfl) ⟨197985, by rfl⟩ : syracuseStep 2111845 = 395971) (by norm_num)
theorem B1849717 : Blo 738327 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B833917 : Blo 738327 833917 := bbase (se 3 (by rfl) ⟨156359, by rfl⟩ : syracuseStep 833917 = 312719) (by norm_num)
theorem B833953 : Blo 738327 833953 := bbase (se 2 (by rfl) ⟨312732, by rfl⟩ : syracuseStep 833953 = 625465) (by norm_num)
theorem B833989 : Blo 738327 833989 := bbase (se 4 (by rfl) ⟨78186, by rfl⟩ : syracuseStep 833989 = 156373) (by norm_num)
theorem B8010197 : Blo 738327 8010197 := bbase (se 7 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 8010197 = 187739) (by norm_num)
theorem B834025 : Blo 738327 834025 := bbase (se 2 (by rfl) ⟨312759, by rfl⟩ : syracuseStep 834025 = 625519) (by norm_num)
theorem B2505221 : Blo 738327 2505221 := bbase (se 4 (by rfl) ⟨234864, by rfl⟩ : syracuseStep 2505221 = 469729) (by norm_num)
theorem B834061 : Blo 738327 834061 := bbase (se 3 (by rfl) ⟨156386, by rfl⟩ : syracuseStep 834061 = 312773) (by norm_num)
theorem B834097 : Blo 738327 834097 := bbase (se 2 (by rfl) ⟨312786, by rfl⟩ : syracuseStep 834097 = 625573) (by norm_num)
theorem B834133 : Blo 738327 834133 := bbase (se 8 (by rfl) ⟨4887, by rfl⟩ : syracuseStep 834133 = 9775) (by norm_num)
theorem B834169 : Blo 738327 834169 := bbase (se 2 (by rfl) ⟨312813, by rfl⟩ : syracuseStep 834169 = 625627) (by norm_num)
theorem B834205 : Blo 738327 834205 := bbase (se 3 (by rfl) ⟨156413, by rfl⟩ : syracuseStep 834205 = 312827) (by norm_num)
theorem B834241 : Blo 738327 834241 := bbase (se 2 (by rfl) ⟨312840, by rfl⟩ : syracuseStep 834241 = 625681) (by norm_num)
theorem B834277 : Blo 738327 834277 := bbase (se 4 (by rfl) ⟨78213, by rfl⟩ : syracuseStep 834277 = 156427) (by norm_num)
theorem B834313 : Blo 738327 834313 := bbase (se 2 (by rfl) ⟨312867, by rfl⟩ : syracuseStep 834313 = 625735) (by norm_num)
theorem B834349 : Blo 738327 834349 := bbase (se 3 (by rfl) ⟨156440, by rfl⟩ : syracuseStep 834349 = 312881) (by norm_num)
theorem B834385 : Blo 738327 834385 := bbase (se 2 (by rfl) ⟨312894, by rfl⟩ : syracuseStep 834385 = 625789) (by norm_num)
theorem B5323637 : Blo 738327 5323637 := bbase (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) (by norm_num)
theorem B834421 : Blo 738327 834421 := bbase (se 5 (by rfl) ⟨39113, by rfl⟩ : syracuseStep 834421 = 78227) (by norm_num)
theorem B834457 : Blo 738327 834457 := bbase (se 2 (by rfl) ⟨312921, by rfl⟩ : syracuseStep 834457 = 625843) (by norm_num)
theorem B2702261 : Blo 738327 2702261 := bbase (se 5 (by rfl) ⟨126668, by rfl⟩ : syracuseStep 2702261 = 253337) (by norm_num)
theorem B834493 : Blo 738327 834493 := bbase (se 3 (by rfl) ⟨156467, by rfl⟩ : syracuseStep 834493 = 312935) (by norm_num)
theorem B5618645 : Blo 738327 5618645 := bbase (se 7 (by rfl) ⟨65843, by rfl⟩ : syracuseStep 5618645 = 131687) (by norm_num)
theorem B7322581 : Blo 738327 7322581 := bbase (se 7 (by rfl) ⟨85811, by rfl⟩ : syracuseStep 7322581 = 171623) (by norm_num)
theorem B834529 : Blo 738327 834529 := bbase (se 2 (by rfl) ⟨312948, by rfl⟩ : syracuseStep 834529 = 625897) (by norm_num)
theorem B867305 : Blo 738327 867305 := bbase (se 2 (by rfl) ⟨325239, by rfl⟩ : syracuseStep 867305 = 650479) (by norm_num)
theorem B834565 : Blo 738327 834565 := bbase (se 4 (by rfl) ⟨78240, by rfl⟩ : syracuseStep 834565 = 156481) (by norm_num)
theorem B834601 : Blo 738327 834601 := bbase (se 2 (by rfl) ⟨312975, by rfl⟩ : syracuseStep 834601 = 625951) (by norm_num)
theorem B834637 : Blo 738327 834637 := bbase (se 3 (by rfl) ⟨156494, by rfl⟩ : syracuseStep 834637 = 312989) (by norm_num)
theorem B834673 : Blo 738327 834673 := bbase (se 2 (by rfl) ⟨313002, by rfl⟩ : syracuseStep 834673 = 626005) (by norm_num)
theorem B834709 : Blo 738327 834709 := bbase (se 6 (by rfl) ⟨19563, by rfl⟩ : syracuseStep 834709 = 39127) (by norm_num)
theorem B834745 : Blo 738327 834745 := bbase (se 2 (by rfl) ⟨313029, by rfl⟩ : syracuseStep 834745 = 626059) (by norm_num)
theorem B3751109 : Blo 738327 3751109 := bbase (se 4 (by rfl) ⟨351666, by rfl⟩ : syracuseStep 3751109 = 703333) (by norm_num)
theorem B834781 : Blo 738327 834781 := bbase (se 3 (by rfl) ⟨156521, by rfl⟩ : syracuseStep 834781 = 313043) (by norm_num)
theorem B834817 : Blo 738327 834817 := bbase (se 2 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 834817 = 626113) (by norm_num)
theorem B834853 : Blo 738327 834853 := bbase (se 4 (by rfl) ⟨78267, by rfl⟩ : syracuseStep 834853 = 156535) (by norm_num)
theorem B7126325 : Blo 738327 7126325 := bbase (se 5 (by rfl) ⟨334046, by rfl⟩ : syracuseStep 7126325 = 668093) (by norm_num)
theorem B834889 : Blo 738327 834889 := bbase (se 2 (by rfl) ⟨313083, by rfl⟩ : syracuseStep 834889 = 626167) (by norm_num)
theorem B834925 : Blo 738327 834925 := bbase (se 3 (by rfl) ⟨156548, by rfl⟩ : syracuseStep 834925 = 313097) (by norm_num)
theorem B834961 : Blo 738327 834961 := bbase (se 2 (by rfl) ⟨313110, by rfl⟩ : syracuseStep 834961 = 626221) (by norm_num)
theorem B834997 : Blo 738327 834997 := bbase (se 5 (by rfl) ⟨39140, by rfl⟩ : syracuseStep 834997 = 78281) (by norm_num)
theorem B835033 : Blo 738327 835033 := bbase (se 2 (by rfl) ⟨313137, by rfl⟩ : syracuseStep 835033 = 626275) (by norm_num)
theorem B835069 : Blo 738327 835069 := bbase (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) (by norm_num)
theorem B2375173 : Blo 738327 2375173 := bbase (se 4 (by rfl) ⟨222672, by rfl⟩ : syracuseStep 2375173 = 445345) (by norm_num)
theorem B835105 : Blo 738327 835105 := bbase (se 2 (by rfl) ⟨313164, by rfl⟩ : syracuseStep 835105 = 626329) (by norm_num)
theorem B2375237 : Blo 738327 2375237 := bbase (se 4 (by rfl) ⟨222678, by rfl⟩ : syracuseStep 2375237 = 445357) (by norm_num)
theorem B1425181 : Blo 738327 1425181 := bbase (se 3 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 1425181 = 534443) (by norm_num)
theorem B2408309 : Blo 738327 2408309 := bbase (se 5 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 2408309 = 225779) (by norm_num)
theorem B4210613 : Blo 738327 4210613 := bbase (se 5 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 4210613 = 394745) (by norm_num)
theorem B999869 : Blo 738327 999869 := bbase (se 3 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 999869 = 374951) (by norm_num)
theorem B3752405 : Blo 738327 3752405 := bbase (se 7 (by rfl) ⟨43973, by rfl⟩ : syracuseStep 3752405 = 87947) (by norm_num)
theorem B934517 : Blo 738327 934517 := bbase (se 5 (by rfl) ⟨43805, by rfl⟩ : syracuseStep 934517 = 87611) (by norm_num)
theorem B1000085 : Blo 738327 1000085 := bbase (se 6 (by rfl) ⟨23439, by rfl⟩ : syracuseStep 1000085 = 46879) (by norm_num)
theorem B934573 : Blo 738327 934573 := bbase (se 3 (by rfl) ⟨175232, by rfl⟩ : syracuseStep 934573 = 350465) (by norm_num)
theorem B1622749 : Blo 738327 1622749 := bbase (se 3 (by rfl) ⟨304265, by rfl⟩ : syracuseStep 1622749 = 608531) (by norm_num)
theorem B934669 : Blo 738327 934669 := bbase (se 3 (by rfl) ⟨175250, by rfl⟩ : syracuseStep 934669 = 350501) (by norm_num)
theorem B1000237 : Blo 738327 1000237 := bbase (se 3 (by rfl) ⟨187544, by rfl⟩ : syracuseStep 1000237 = 375089) (by norm_num)
theorem B3556165 : Blo 738327 3556165 := bbase (se 4 (by rfl) ⟨333390, by rfl⟩ : syracuseStep 3556165 = 666781) (by norm_num)
theorem B934841 : Blo 738327 934841 := bbase (se 2 (by rfl) ⟨350565, by rfl⟩ : syracuseStep 934841 = 701131) (by norm_num)
theorem B934897 : Blo 738327 934897 := bbase (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) (by norm_num)
theorem B934993 : Blo 738327 934993 := bbase (se 2 (by rfl) ⟨350622, by rfl⟩ : syracuseStep 934993 = 701245) (by norm_num)
theorem B4211797 : Blo 738327 4211797 := bbase (se 8 (by rfl) ⟨24678, by rfl⟩ : syracuseStep 4211797 = 49357) (by norm_num)
theorem B2999477 : Blo 738327 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B935165 : Blo 738327 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B935221 : Blo 738327 935221 := bbase (se 5 (by rfl) ⟨43838, by rfl⟩ : syracuseStep 935221 = 87677) (by norm_num)
theorem B935317 : Blo 738327 935317 := bbase (se 6 (by rfl) ⟨21921, by rfl⟩ : syracuseStep 935317 = 43843) (by norm_num)
theorem B935489 : Blo 738327 935489 := bbase (se 2 (by rfl) ⟨350808, by rfl⟩ : syracuseStep 935489 = 701617) (by norm_num)
theorem B2737781 : Blo 738327 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B935545 : Blo 738327 935545 := bbase (se 2 (by rfl) ⟨350829, by rfl⟩ : syracuseStep 935545 = 701659) (by norm_num)
theorem B935641 : Blo 738327 935641 := bbase (se 2 (by rfl) ⟨350865, by rfl⟩ : syracuseStep 935641 = 701731) (by norm_num)
theorem B3753701 : Blo 738327 3753701 := bbase (se 4 (by rfl) ⟨351909, by rfl⟩ : syracuseStep 3753701 = 703819) (by norm_num)
theorem B1689341 : Blo 738327 1689341 := bbase (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) (by norm_num)
theorem B935813 : Blo 738327 935813 := bbase (se 4 (by rfl) ⟨87732, by rfl⟩ : syracuseStep 935813 = 175465) (by norm_num)
theorem B935869 : Blo 738327 935869 := bbase (se 3 (by rfl) ⟨175475, by rfl⟩ : syracuseStep 935869 = 350951) (by norm_num)
theorem B1689541 : Blo 738327 1689541 := bbase (se 4 (by rfl) ⟨158394, by rfl⟩ : syracuseStep 1689541 = 316789) (by norm_num)
theorem B935965 : Blo 738327 935965 := bbase (se 3 (by rfl) ⟨175493, by rfl⟩ : syracuseStep 935965 = 350987) (by norm_num)
theorem B1263653 : Blo 738327 1263653 := bbase (se 4 (by rfl) ⟨118467, by rfl⟩ : syracuseStep 1263653 = 236935) (by norm_num)
theorem B936137 : Blo 738327 936137 := bbase (se 2 (by rfl) ⟨351051, by rfl⟩ : syracuseStep 936137 = 702103) (by norm_num)
theorem B1427701 : Blo 738327 1427701 := bbase (se 5 (by rfl) ⟨66923, by rfl⟩ : syracuseStep 1427701 = 133847) (by norm_num)
theorem B936193 : Blo 738327 936193 := bbase (se 2 (by rfl) ⟨351072, by rfl⟩ : syracuseStep 936193 = 702145) (by norm_num)
theorem B3164453 : Blo 738327 3164453 := bbase (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) (by norm_num)
theorem B936289 : Blo 738327 936289 := bbase (se 2 (by rfl) ⟨351108, by rfl⟩ : syracuseStep 936289 = 702217) (by norm_num)
theorem B936461 : Blo 738327 936461 := bbase (se 3 (by rfl) ⟨175586, by rfl⟩ : syracuseStep 936461 = 351173) (by norm_num)
theorem B936517 : Blo 738327 936517 := bbase (se 4 (by rfl) ⟨87798, by rfl⟩ : syracuseStep 936517 = 175597) (by norm_num)
theorem B2804341 : Blo 738327 2804341 := bbase (se 5 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 2804341 = 262907) (by norm_num)
theorem B936613 : Blo 738327 936613 := bbase (se 4 (by rfl) ⟨87807, by rfl⟩ : syracuseStep 936613 = 175615) (by norm_num)
theorem B1428277 : Blo 738327 1428277 := bbase (se 5 (by rfl) ⟨66950, by rfl⟩ : syracuseStep 1428277 = 133901) (by norm_num)
theorem B936785 : Blo 738327 936785 := bbase (se 2 (by rfl) ⟨351294, by rfl⟩ : syracuseStep 936785 = 702589) (by norm_num)
theorem B936841 : Blo 738327 936841 := bbase (se 2 (by rfl) ⟨351315, by rfl⟩ : syracuseStep 936841 = 702631) (by norm_num)
theorem B2804645 : Blo 738327 2804645 := bbase (se 4 (by rfl) ⟨262935, by rfl⟩ : syracuseStep 2804645 = 525871) (by norm_num)
theorem B13519829 : Blo 738327 13519829 := bbase (se 7 (by rfl) ⟨158435, by rfl⟩ : syracuseStep 13519829 = 316871) (by norm_num)
theorem B936937 : Blo 738327 936937 := bbase (se 2 (by rfl) ⟨351351, by rfl⟩ : syracuseStep 936937 = 702703) (by norm_num)
theorem B3754997 : Blo 738327 3754997 := bbase (se 5 (by rfl) ⟨176015, by rfl⟩ : syracuseStep 3754997 = 352031) (by norm_num)
theorem B4213781 : Blo 738327 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B7588981 : Blo 738327 7588981 := bbase (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) (by norm_num)
theorem B1002637 : Blo 738327 1002637 := bbase (se 3 (by rfl) ⟨187994, by rfl⟩ : syracuseStep 1002637 = 375989) (by norm_num)
theorem B937109 : Blo 738327 937109 := bbase (se 6 (by rfl) ⟨21963, by rfl⟩ : syracuseStep 937109 = 43927) (by norm_num)
theorem B937165 : Blo 738327 937165 := bbase (se 3 (by rfl) ⟨175718, by rfl⟩ : syracuseStep 937165 = 351437) (by norm_num)
theorem B937261 : Blo 738327 937261 := bbase (se 3 (by rfl) ⟨175736, by rfl⟩ : syracuseStep 937261 = 351473) (by norm_num)
theorem B1002853 : Blo 738327 1002853 := bbase (se 4 (by rfl) ⟨94017, by rfl⟩ : syracuseStep 1002853 = 188035) (by norm_num)
theorem B937433 : Blo 738327 937433 := bbase (se 2 (by rfl) ⟨351537, by rfl⟩ : syracuseStep 937433 = 703075) (by norm_num)
theorem B3558917 : Blo 738327 3558917 := bbase (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) (by norm_num)
theorem B937489 : Blo 738327 937489 := bbase (se 2 (by rfl) ⟨351558, by rfl⟩ : syracuseStep 937489 = 703117) (by norm_num)
theorem B937585 : Blo 738327 937585 := bbase (se 2 (by rfl) ⟨351594, by rfl⟩ : syracuseStep 937585 = 703189) (by norm_num)
theorem B1068701 : Blo 738327 1068701 := bbase (se 3 (by rfl) ⟨200381, by rfl⟩ : syracuseStep 1068701 = 400763) (by norm_num)
theorem B8113877 : Blo 738327 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B2674421 : Blo 738327 2674421 := bbase (se 5 (by rfl) ⟨125363, by rfl⟩ : syracuseStep 2674421 = 250727) (by norm_num)
theorem B2248469 : Blo 738327 2248469 := bbase (se 6 (by rfl) ⟨52698, by rfl⟩ : syracuseStep 2248469 = 105397) (by norm_num)
theorem B937757 : Blo 738327 937757 := bbase (se 3 (by rfl) ⟨175829, by rfl⟩ : syracuseStep 937757 = 351659) (by norm_num)
theorem B937813 : Blo 738327 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B1199965 : Blo 738327 1199965 := bbase (se 3 (by rfl) ⟨224993, by rfl⟩ : syracuseStep 1199965 = 449987) (by norm_num)
theorem B2674565 : Blo 738327 2674565 := bbase (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) (by norm_num)
theorem B937909 : Blo 738327 937909 := bbase (se 5 (by rfl) ⟨43964, by rfl⟩ : syracuseStep 937909 = 87929) (by norm_num)
theorem B4739093 : Blo 738327 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B3166229 : Blo 738327 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B938081 : Blo 738327 938081 := bbase (se 2 (by rfl) ⟨351780, by rfl⟩ : syracuseStep 938081 = 703561) (by norm_num)
theorem B938137 : Blo 738327 938137 := bbase (se 2 (by rfl) ⟨351801, by rfl⟩ : syracuseStep 938137 = 703603) (by norm_num)
theorem B2674853 : Blo 738327 2674853 := bbase (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) (by norm_num)
theorem B25972949 : Blo 738327 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B938233 : Blo 738327 938233 := bbase (se 2 (by rfl) ⟨351837, by rfl⟩ : syracuseStep 938233 = 703675) (by norm_num)
theorem B3756293 : Blo 738327 3756293 := bbase (se 4 (by rfl) ⟨352152, by rfl⟩ : syracuseStep 3756293 = 704305) (by norm_num)
theorem B3658133 : Blo 738327 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B1266077 : Blo 738327 1266077 := bbase (se 3 (by rfl) ⟨237389, by rfl⟩ : syracuseStep 1266077 = 474779) (by norm_num)
theorem B938405 : Blo 738327 938405 := bbase (se 4 (by rfl) ⟨87975, by rfl⟩ : syracuseStep 938405 = 175951) (by norm_num)
theorem B1331653 : Blo 738327 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B938461 : Blo 738327 938461 := bbase (se 3 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 938461 = 351923) (by norm_num)
theorem B938557 : Blo 738327 938557 := bbase (se 3 (by rfl) ⟨175979, by rfl⟩ : syracuseStep 938557 = 351959) (by norm_num)
theorem B1692389 : Blo 738327 1692389 := bbase (se 4 (by rfl) ⟨158661, by rfl⟩ : syracuseStep 1692389 = 317323) (by norm_num)
theorem B938729 : Blo 738327 938729 := bbase (se 2 (by rfl) ⟨352023, by rfl⟩ : syracuseStep 938729 = 704047) (by norm_num)
theorem B1921781 : Blo 738327 1921781 := bbase (se 5 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 1921781 = 180167) (by norm_num)
theorem B1266445 : Blo 738327 1266445 := bbase (se 3 (by rfl) ⟨237458, by rfl⟩ : syracuseStep 1266445 = 474917) (by norm_num)
theorem B938785 : Blo 738327 938785 := bbase (se 2 (by rfl) ⟨352044, by rfl⟩ : syracuseStep 938785 = 704089) (by norm_num)
theorem B1692461 : Blo 738327 1692461 := bbase (se 3 (by rfl) ⟨317336, by rfl⟩ : syracuseStep 1692461 = 634673) (by norm_num)
theorem B938881 : Blo 738327 938881 := bbase (se 2 (by rfl) ⟨352080, by rfl⟩ : syracuseStep 938881 = 704161) (by norm_num)
theorem B2806757 : Blo 738327 2806757 := bbase (se 4 (by rfl) ⟨263133, by rfl⟩ : syracuseStep 2806757 = 526267) (by norm_num)
theorem B3167221 : Blo 738327 3167221 := bbase (se 5 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 3167221 = 296927) (by norm_num)
theorem B939053 : Blo 738327 939053 := bbase (se 3 (by rfl) ⟨176072, by rfl⟩ : syracuseStep 939053 = 352145) (by norm_num)
theorem B939109 : Blo 738327 939109 := bbase (se 4 (by rfl) ⟨88041, by rfl⟩ : syracuseStep 939109 = 176083) (by norm_num)
theorem B4215989 : Blo 738327 4215989 := bbase (se 5 (by rfl) ⟨197624, by rfl⟩ : syracuseStep 4215989 = 395249) (by norm_num)
theorem B1266877 : Blo 738327 1266877 := bbase (se 3 (by rfl) ⟨237539, by rfl⟩ : syracuseStep 1266877 = 475079) (by norm_num)
theorem B939205 : Blo 738327 939205 := bbase (se 4 (by rfl) ⟨88050, by rfl⟩ : syracuseStep 939205 = 176101) (by norm_num)
theorem B2807045 : Blo 738327 2807045 := bbase (se 4 (by rfl) ⟨263160, by rfl⟩ : syracuseStep 2807045 = 526321) (by norm_num)
theorem B939377 : Blo 738327 939377 := bbase (se 2 (by rfl) ⟨352266, by rfl⟩ : syracuseStep 939377 = 704533) (by norm_num)
theorem B939433 : Blo 738327 939433 := bbase (se 2 (by rfl) ⟨352287, by rfl⟩ : syracuseStep 939433 = 704575) (by norm_num)
theorem B1332749 : Blo 738327 1332749 := bbase (se 3 (by rfl) ⟨249890, by rfl⟩ : syracuseStep 1332749 = 499781) (by norm_num)
theorem B3757589 : Blo 738327 3757589 := bbase (se 6 (by rfl) ⟨88068, by rfl⟩ : syracuseStep 3757589 = 176137) (by norm_num)
theorem B4511477 : Blo 738327 4511477 := bbase (se 5 (by rfl) ⟨211475, by rfl⟩ : syracuseStep 4511477 = 422951) (by norm_num)
theorem B1333037 : Blo 738327 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B3561317 : Blo 738327 3561317 := bbase (se 4 (by rfl) ⟨333873, by rfl⟩ : syracuseStep 3561317 = 667747) (by norm_num)
theorem B22763477 : Blo 738327 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B1661237 : Blo 738327 1661237 := bbase (se 5 (by rfl) ⟨77870, by rfl⟩ : syracuseStep 1661237 = 155741) (by norm_num)
theorem B1661309 : Blo 738327 1661309 := bbase (se 3 (by rfl) ⟨311495, by rfl⟩ : syracuseStep 1661309 = 622991) (by norm_num)
theorem B2808229 : Blo 738327 2808229 := bbase (se 4 (by rfl) ⟨263271, by rfl⟩ : syracuseStep 2808229 = 526543) (by norm_num)
theorem B1497533 : Blo 738327 1497533 := bbase (se 3 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 1497533 = 561575) (by norm_num)
theorem B1661381 : Blo 738327 1661381 := bbase (se 4 (by rfl) ⟨155754, by rfl⟩ : syracuseStep 1661381 = 311509) (by norm_num)
theorem B1661453 : Blo 738327 1661453 := bbase (se 3 (by rfl) ⟨311522, by rfl⟩ : syracuseStep 1661453 = 623045) (by norm_num)
theorem B5626421 : Blo 738327 5626421 := bbase (se 5 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 5626421 = 527477) (by norm_num)
theorem B1661525 : Blo 738327 1661525 := bbase (se 8 (by rfl) ⟨9735, by rfl⟩ : syracuseStep 1661525 = 19471) (by norm_num)
theorem B5331541 : Blo 738327 5331541 := bbase (se 8 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 5331541 = 62479) (by norm_num)
theorem B1661597 : Blo 738327 1661597 := bbase (se 3 (by rfl) ⟨311549, by rfl⟩ : syracuseStep 1661597 = 623099) (by norm_num)
theorem B2808533 : Blo 738327 2808533 := bbase (se 7 (by rfl) ⟨32912, by rfl⟩ : syracuseStep 2808533 = 65825) (by norm_num)
theorem B1661669 : Blo 738327 1661669 := bbase (se 4 (by rfl) ⟨155781, by rfl⟩ : syracuseStep 1661669 = 311563) (by norm_num)
theorem B1661741 : Blo 738327 1661741 := bbase (se 3 (by rfl) ⟨311576, by rfl⟩ : syracuseStep 1661741 = 623153) (by norm_num)
theorem B1661813 : Blo 738327 1661813 := bbase (se 5 (by rfl) ⟨77897, by rfl⟩ : syracuseStep 1661813 = 155795) (by norm_num)
theorem B13523861 : Blo 738327 13523861 := bbase (se 6 (by rfl) ⟨316965, by rfl⟩ : syracuseStep 13523861 = 633931) (by norm_num)
theorem B1661885 : Blo 738327 1661885 := bbase (se 3 (by rfl) ⟨311603, by rfl⟩ : syracuseStep 1661885 = 623207) (by norm_num)
theorem B2841605 : Blo 738327 2841605 := bbase (se 4 (by rfl) ⟨266400, by rfl⟩ : syracuseStep 2841605 = 532801) (by norm_num)
theorem B1661957 : Blo 738327 1661957 := bbase (se 4 (by rfl) ⟨155808, by rfl⟩ : syracuseStep 1661957 = 311617) (by norm_num)
theorem B1498117 : Blo 738327 1498117 := bbase (se 4 (by rfl) ⟨140448, by rfl⟩ : syracuseStep 1498117 = 280897) (by norm_num)
theorem B1334341 : Blo 738327 1334341 := bbase (se 4 (by rfl) ⟨125094, by rfl⟩ : syracuseStep 1334341 = 250189) (by norm_num)
theorem B1662029 : Blo 738327 1662029 := bbase (se 3 (by rfl) ⟨311630, by rfl⟩ : syracuseStep 1662029 = 623261) (by norm_num)
theorem B1662101 : Blo 738327 1662101 := bbase (se 6 (by rfl) ⟨38955, by rfl⟩ : syracuseStep 1662101 = 77911) (by norm_num)
theorem B7298261 : Blo 738327 7298261 := bbase (se 7 (by rfl) ⟨85526, by rfl⟩ : syracuseStep 7298261 = 171053) (by norm_num)
theorem B1334485 : Blo 738327 1334485 := bbase (se 7 (by rfl) ⟨15638, by rfl⟩ : syracuseStep 1334485 = 31277) (by norm_num)
theorem B1662173 : Blo 738327 1662173 := bbase (se 3 (by rfl) ⟨311657, by rfl⟩ : syracuseStep 1662173 = 623315) (by norm_num)
theorem B1662245 : Blo 738327 1662245 := bbase (se 4 (by rfl) ⟨155835, by rfl⟩ : syracuseStep 1662245 = 311671) (by norm_num)
theorem B1662317 : Blo 738327 1662317 := bbase (se 3 (by rfl) ⟨311684, by rfl⟩ : syracuseStep 1662317 = 623369) (by norm_num)
theorem B1662389 : Blo 738327 1662389 := bbase (se 5 (by rfl) ⟨77924, by rfl⟩ : syracuseStep 1662389 = 155849) (by norm_num)
theorem B6315509 : Blo 738327 6315509 := bbase (se 5 (by rfl) ⟨296039, by rfl⟩ : syracuseStep 6315509 = 592079) (by norm_num)
theorem B1662461 : Blo 738327 1662461 := bbase (se 3 (by rfl) ⟨311711, by rfl⟩ : syracuseStep 1662461 = 623423) (by norm_num)
theorem B1498637 : Blo 738327 1498637 := bbase (se 3 (by rfl) ⟨280994, by rfl⟩ : syracuseStep 1498637 = 561989) (by norm_num)
theorem B1662533 : Blo 738327 1662533 := bbase (se 4 (by rfl) ⟨155862, by rfl⟩ : syracuseStep 1662533 = 311725) (by norm_num)
theorem B843385 : Blo 738327 843385 := bbase (se 2 (by rfl) ⟨316269, by rfl⟩ : syracuseStep 843385 = 632539) (by norm_num)
theorem B1662605 : Blo 738327 1662605 := bbase (se 3 (by rfl) ⟨311738, by rfl⟩ : syracuseStep 1662605 = 623477) (by norm_num)
theorem B1662677 : Blo 738327 1662677 := bbase (se 7 (by rfl) ⟨19484, by rfl⟩ : syracuseStep 1662677 = 38969) (by norm_num)
theorem B1335061 : Blo 738327 1335061 := bbase (se 6 (by rfl) ⟨31290, by rfl⟩ : syracuseStep 1335061 = 62581) (by norm_num)
theorem B1662749 : Blo 738327 1662749 := bbase (se 3 (by rfl) ⟨311765, by rfl⟩ : syracuseStep 1662749 = 623531) (by norm_num)
theorem B1662821 : Blo 738327 1662821 := bbase (se 4 (by rfl) ⟨155889, by rfl⟩ : syracuseStep 1662821 = 311779) (by norm_num)
theorem B3006341 : Blo 738327 3006341 := bbase (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) (by norm_num)
theorem B1662893 : Blo 738327 1662893 := bbase (se 3 (by rfl) ⟨311792, by rfl⟩ : syracuseStep 1662893 = 623585) (by norm_num)
theorem B1662965 : Blo 738327 1662965 := bbase (se 5 (by rfl) ⟨77951, by rfl⟩ : syracuseStep 1662965 = 155903) (by norm_num)
theorem B974845 : Blo 738327 974845 := bbase (se 3 (by rfl) ⟨182783, by rfl⟩ : syracuseStep 974845 = 365567) (by norm_num)
theorem B1663037 : Blo 738327 1663037 := bbase (se 3 (by rfl) ⟨311819, by rfl⟩ : syracuseStep 1663037 = 623639) (by norm_num)
theorem B1663109 : Blo 738327 1663109 := bbase (se 4 (by rfl) ⟨155916, by rfl⟩ : syracuseStep 1663109 = 311833) (by norm_num)
theorem B1663181 : Blo 738327 1663181 := bbase (se 3 (by rfl) ⟨311846, by rfl⟩ : syracuseStep 1663181 = 623693) (by norm_num)
theorem B1663253 : Blo 738327 1663253 := bbase (se 6 (by rfl) ⟨38982, by rfl⟩ : syracuseStep 1663253 = 77965) (by norm_num)
theorem B1663325 : Blo 738327 1663325 := bbase (se 3 (by rfl) ⟨311873, by rfl⟩ : syracuseStep 1663325 = 623747) (by norm_num)
theorem B1663397 : Blo 738327 1663397 := bbase (se 4 (by rfl) ⟨155943, by rfl⟩ : syracuseStep 1663397 = 311887) (by norm_num)
theorem B1663469 : Blo 738327 1663469 := bbase (se 3 (by rfl) ⟨311900, by rfl⟩ : syracuseStep 1663469 = 623801) (by norm_num)
theorem B1663541 : Blo 738327 1663541 := bbase (se 5 (by rfl) ⟨77978, by rfl⟩ : syracuseStep 1663541 = 155957) (by norm_num)
theorem B1335869 : Blo 738327 1335869 := bbase (se 3 (by rfl) ⟨250475, by rfl⟩ : syracuseStep 1335869 = 500951) (by norm_num)
theorem B1663613 : Blo 738327 1663613 := bbase (se 3 (by rfl) ⟨311927, by rfl⟩ : syracuseStep 1663613 = 623855) (by norm_num)
theorem B4809365 : Blo 738327 4809365 := bbase (se 6 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 4809365 = 225439) (by norm_num)
theorem B1663685 : Blo 738327 1663685 := bbase (se 4 (by rfl) ⟨155970, by rfl⟩ : syracuseStep 1663685 = 311941) (by norm_num)
theorem B1663757 : Blo 738327 1663757 := bbase (se 3 (by rfl) ⟨311954, by rfl⟩ : syracuseStep 1663757 = 623909) (by norm_num)
theorem B2810645 : Blo 738327 2810645 := bbase (se 6 (by rfl) ⟨65874, by rfl⟩ : syracuseStep 2810645 = 131749) (by norm_num)
theorem B844625 : Blo 738327 844625 := bbase (se 2 (by rfl) ⟨316734, by rfl⟩ : syracuseStep 844625 = 633469) (by norm_num)
theorem B1663829 : Blo 738327 1663829 := bbase (se 9 (by rfl) ⟨4874, by rfl⟩ : syracuseStep 1663829 = 9749) (by norm_num)
theorem B1663901 : Blo 738327 1663901 := bbase (se 3 (by rfl) ⟨311981, by rfl⟩ : syracuseStep 1663901 = 623963) (by norm_num)
theorem B2253781 : Blo 738327 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B1663973 : Blo 738327 1663973 := bbase (se 4 (by rfl) ⟨155997, by rfl⟩ : syracuseStep 1663973 = 311995) (by norm_num)
theorem B1664045 : Blo 738327 1664045 := bbase (se 3 (by rfl) ⟨312008, by rfl⟩ : syracuseStep 1664045 = 624017) (by norm_num)
theorem B2810933 : Blo 738327 2810933 := bbase (se 5 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 2810933 = 263525) (by norm_num)
theorem B844877 : Blo 738327 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B1664117 : Blo 738327 1664117 := bbase (se 5 (by rfl) ⟨78005, by rfl⟩ : syracuseStep 1664117 = 156011) (by norm_num)
theorem B1664189 : Blo 738327 1664189 := bbase (se 3 (by rfl) ⟨312035, by rfl⟩ : syracuseStep 1664189 = 624071) (by norm_num)
theorem B1664261 : Blo 738327 1664261 := bbase (se 4 (by rfl) ⟨156024, by rfl⟩ : syracuseStep 1664261 = 312049) (by norm_num)
theorem B812353 : Blo 738327 812353 := bbase (se 2 (by rfl) ⟨304632, by rfl⟩ : syracuseStep 812353 = 609265) (by norm_num)
theorem B1664333 : Blo 738327 1664333 := bbase (se 3 (by rfl) ⟨312062, by rfl⟩ : syracuseStep 1664333 = 624125) (by norm_num)
theorem B845173 : Blo 738327 845173 := bbase (se 5 (by rfl) ⟨39617, by rfl⟩ : syracuseStep 845173 = 79235) (by norm_num)
theorem B1664405 : Blo 738327 1664405 := bbase (se 6 (by rfl) ⟨39009, by rfl⟩ : syracuseStep 1664405 = 78019) (by norm_num)
theorem B1402285 : Blo 738327 1402285 := bbase (se 3 (by rfl) ⟨262928, by rfl⟩ : syracuseStep 1402285 = 525857) (by norm_num)
theorem B1664477 : Blo 738327 1664477 := bbase (se 3 (by rfl) ⟨312089, by rfl⟩ : syracuseStep 1664477 = 624179) (by norm_num)
theorem B845329 : Blo 738327 845329 := bbase (se 2 (by rfl) ⟨316998, by rfl⟩ : syracuseStep 845329 = 633997) (by norm_num)
theorem B1664549 : Blo 738327 1664549 := bbase (se 4 (by rfl) ⟨156051, by rfl⟩ : syracuseStep 1664549 = 312103) (by norm_num)
theorem B1107509 : Blo 738327 1107509 := bbase (se 5 (by rfl) ⟨51914, by rfl⟩ : syracuseStep 1107509 = 103829) (by norm_num)
theorem B1402429 : Blo 738327 1402429 := bbase (se 3 (by rfl) ⟨262955, by rfl⟩ : syracuseStep 1402429 = 525911) (by norm_num)
theorem B1107533 : Blo 738327 1107533 := bbase (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) (by norm_num)
theorem B1107557 : Blo 738327 1107557 := bbase (se 4 (by rfl) ⟨103833, by rfl⟩ : syracuseStep 1107557 = 207667) (by norm_num)
theorem B1664621 : Blo 738327 1664621 := bbase (se 3 (by rfl) ⟨312116, by rfl⟩ : syracuseStep 1664621 = 624233) (by norm_num)
theorem B1107581 : Blo 738327 1107581 := bbase (se 3 (by rfl) ⟨207671, by rfl⟩ : syracuseStep 1107581 = 415343) (by norm_num)
theorem B1107605 : Blo 738327 1107605 := bbase (se 6 (by rfl) ⟨25959, by rfl⟩ : syracuseStep 1107605 = 51919) (by norm_num)
theorem B1107629 : Blo 738327 1107629 := bbase (se 3 (by rfl) ⟨207680, by rfl⟩ : syracuseStep 1107629 = 415361) (by norm_num)
theorem B1664693 : Blo 738327 1664693 := bbase (se 5 (by rfl) ⟨78032, by rfl⟩ : syracuseStep 1664693 = 156065) (by norm_num)
theorem B1107653 : Blo 738327 1107653 := bbase (se 4 (by rfl) ⟨103842, by rfl⟩ : syracuseStep 1107653 = 207685) (by norm_num)
theorem B1107677 : Blo 738327 1107677 := bbase (se 3 (by rfl) ⟨207689, by rfl⟩ : syracuseStep 1107677 = 415379) (by norm_num)
theorem B1402589 : Blo 738327 1402589 := bbase (se 3 (by rfl) ⟨262985, by rfl⟩ : syracuseStep 1402589 = 525971) (by norm_num)
theorem B1107701 : Blo 738327 1107701 := bbase (se 5 (by rfl) ⟨51923, by rfl⟩ : syracuseStep 1107701 = 103847) (by norm_num)
theorem B1664765 : Blo 738327 1664765 := bbase (se 3 (by rfl) ⟨312143, by rfl⟩ : syracuseStep 1664765 = 624287) (by norm_num)
theorem B1107725 : Blo 738327 1107725 := bbase (se 3 (by rfl) ⟨207698, by rfl⟩ : syracuseStep 1107725 = 415397) (by norm_num)
theorem B1107749 : Blo 738327 1107749 := bbase (se 4 (by rfl) ⟨103851, by rfl⟩ : syracuseStep 1107749 = 207703) (by norm_num)
theorem B1107773 : Blo 738327 1107773 := bbase (se 3 (by rfl) ⟨207707, by rfl⟩ : syracuseStep 1107773 = 415415) (by norm_num)
theorem B1664837 : Blo 738327 1664837 := bbase (se 4 (by rfl) ⟨156078, by rfl⟩ : syracuseStep 1664837 = 312157) (by norm_num)
theorem B1107797 : Blo 738327 1107797 := bbase (se 9 (by rfl) ⟨3245, by rfl⟩ : syracuseStep 1107797 = 6491) (by norm_num)
theorem B1107821 : Blo 738327 1107821 := bbase (se 3 (by rfl) ⟨207716, by rfl⟩ : syracuseStep 1107821 = 415433) (by norm_num)
theorem B1402733 : Blo 738327 1402733 := bbase (se 3 (by rfl) ⟨263012, by rfl⟩ : syracuseStep 1402733 = 526025) (by norm_num)
theorem B1107845 : Blo 738327 1107845 := bbase (se 4 (by rfl) ⟨103860, by rfl⟩ : syracuseStep 1107845 = 207721) (by norm_num)
theorem B1664909 : Blo 738327 1664909 := bbase (se 3 (by rfl) ⟨312170, by rfl⟩ : syracuseStep 1664909 = 624341) (by norm_num)
theorem B1107869 : Blo 738327 1107869 := bbase (se 3 (by rfl) ⟨207725, by rfl⟩ : syracuseStep 1107869 = 415451) (by norm_num)
theorem B1107893 : Blo 738327 1107893 := bbase (se 5 (by rfl) ⟨51932, by rfl⟩ : syracuseStep 1107893 = 103865) (by norm_num)
theorem B1107917 : Blo 738327 1107917 := bbase (se 3 (by rfl) ⟨207734, by rfl⟩ : syracuseStep 1107917 = 415469) (by norm_num)
theorem B1664981 : Blo 738327 1664981 := bbase (se 7 (by rfl) ⟨19511, by rfl⟩ : syracuseStep 1664981 = 39023) (by norm_num)
theorem B1107941 : Blo 738327 1107941 := bbase (se 4 (by rfl) ⟨103869, by rfl⟩ : syracuseStep 1107941 = 207739) (by norm_num)
theorem B1107965 : Blo 738327 1107965 := bbase (se 3 (by rfl) ⟨207743, by rfl⟩ : syracuseStep 1107965 = 415487) (by norm_num)
theorem B1107989 : Blo 738327 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B1665053 : Blo 738327 1665053 := bbase (se 3 (by rfl) ⟨312197, by rfl⟩ : syracuseStep 1665053 = 624395) (by norm_num)
theorem B1108013 : Blo 738327 1108013 := bbase (se 3 (by rfl) ⟨207752, by rfl⟩ : syracuseStep 1108013 = 415505) (by norm_num)
theorem B1108037 : Blo 738327 1108037 := bbase (se 4 (by rfl) ⟨103878, by rfl⟩ : syracuseStep 1108037 = 207757) (by norm_num)
theorem B1108061 : Blo 738327 1108061 := bbase (se 3 (by rfl) ⟨207761, by rfl⟩ : syracuseStep 1108061 = 415523) (by norm_num)
theorem B1665125 : Blo 738327 1665125 := bbase (se 4 (by rfl) ⟨156105, by rfl⟩ : syracuseStep 1665125 = 312211) (by norm_num)
theorem B1108085 : Blo 738327 1108085 := bbase (se 5 (by rfl) ⟨51941, by rfl⟩ : syracuseStep 1108085 = 103883) (by norm_num)
theorem B1108109 : Blo 738327 1108109 := bbase (se 3 (by rfl) ⟨207770, by rfl⟩ : syracuseStep 1108109 = 415541) (by norm_num)
theorem B1403021 : Blo 738327 1403021 := bbase (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) (by norm_num)
theorem B1108133 : Blo 738327 1108133 := bbase (se 4 (by rfl) ⟨103887, by rfl⟩ : syracuseStep 1108133 = 207775) (by norm_num)
theorem B1665197 : Blo 738327 1665197 := bbase (se 3 (by rfl) ⟨312224, by rfl⟩ : syracuseStep 1665197 = 624449) (by norm_num)
theorem B1108157 : Blo 738327 1108157 := bbase (se 3 (by rfl) ⟨207779, by rfl⟩ : syracuseStep 1108157 = 415559) (by norm_num)
theorem B1108181 : Blo 738327 1108181 := bbase (se 7 (by rfl) ⟨12986, by rfl⟩ : syracuseStep 1108181 = 25973) (by norm_num)
theorem B2812117 : Blo 738327 2812117 := bbase (se 7 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 2812117 = 65909) (by norm_num)
theorem B1108205 : Blo 738327 1108205 := bbase (se 3 (by rfl) ⟨207788, by rfl⟩ : syracuseStep 1108205 = 415577) (by norm_num)
theorem B1665269 : Blo 738327 1665269 := bbase (se 5 (by rfl) ⟨78059, by rfl⟩ : syracuseStep 1665269 = 156119) (by norm_num)
theorem B1894661 : Blo 738327 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B1108229 : Blo 738327 1108229 := bbase (se 4 (by rfl) ⟨103896, by rfl⟩ : syracuseStep 1108229 = 207793) (by norm_num)
theorem B1108253 : Blo 738327 1108253 := bbase (se 3 (by rfl) ⟨207797, by rfl⟩ : syracuseStep 1108253 = 415595) (by norm_num)
theorem B1403173 : Blo 738327 1403173 := bbase (se 4 (by rfl) ⟨131547, by rfl⟩ : syracuseStep 1403173 = 263095) (by norm_num)
theorem B1108277 : Blo 738327 1108277 := bbase (se 5 (by rfl) ⟨51950, by rfl⟩ : syracuseStep 1108277 = 103901) (by norm_num)
theorem B1665341 : Blo 738327 1665341 := bbase (se 3 (by rfl) ⟨312251, by rfl⟩ : syracuseStep 1665341 = 624503) (by norm_num)
theorem B1108301 : Blo 738327 1108301 := bbase (se 3 (by rfl) ⟨207806, by rfl⟩ : syracuseStep 1108301 = 415613) (by norm_num)
theorem B1108325 : Blo 738327 1108325 := bbase (se 4 (by rfl) ⟨103905, by rfl⟩ : syracuseStep 1108325 = 207811) (by norm_num)
theorem B1108349 : Blo 738327 1108349 := bbase (se 3 (by rfl) ⟨207815, by rfl⟩ : syracuseStep 1108349 = 415631) (by norm_num)
theorem B1665413 : Blo 738327 1665413 := bbase (se 4 (by rfl) ⟨156132, by rfl⟩ : syracuseStep 1665413 = 312265) (by norm_num)
theorem B1501573 : Blo 738327 1501573 := bbase (se 4 (by rfl) ⟨140772, by rfl⟩ : syracuseStep 1501573 = 281545) (by norm_num)
theorem B780689 : Blo 738327 780689 := bbase (se 2 (by rfl) ⟨292758, by rfl⟩ : syracuseStep 780689 = 585517) (by norm_num)
theorem B1108373 : Blo 738327 1108373 := bbase (se 6 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 1108373 = 51955) (by norm_num)
theorem B6318485 : Blo 738327 6318485 := bbase (se 6 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 6318485 = 296179) (by norm_num)
theorem B1108397 : Blo 738327 1108397 := bbase (se 3 (by rfl) ⟨207824, by rfl⟩ : syracuseStep 1108397 = 415649) (by norm_num)
theorem B1108421 : Blo 738327 1108421 := bbase (se 4 (by rfl) ⟨103914, by rfl⟩ : syracuseStep 1108421 = 207829) (by norm_num)
theorem B1665485 : Blo 738327 1665485 := bbase (se 3 (by rfl) ⟨312278, by rfl⟩ : syracuseStep 1665485 = 624557) (by norm_num)
theorem B1108445 : Blo 738327 1108445 := bbase (se 3 (by rfl) ⟨207833, by rfl⟩ : syracuseStep 1108445 = 415667) (by norm_num)
theorem B1108469 : Blo 738327 1108469 := bbase (se 5 (by rfl) ⟨51959, by rfl⟩ : syracuseStep 1108469 = 103919) (by norm_num)
theorem B2812421 : Blo 738327 2812421 := bbase (se 4 (by rfl) ⟨263664, by rfl⟩ : syracuseStep 2812421 = 527329) (by norm_num)
theorem B1108493 : Blo 738327 1108493 := bbase (se 3 (by rfl) ⟨207842, by rfl⟩ : syracuseStep 1108493 = 415685) (by norm_num)
theorem B1665557 : Blo 738327 1665557 := bbase (se 6 (by rfl) ⟨39036, by rfl⟩ : syracuseStep 1665557 = 78073) (by norm_num)
theorem B1108517 : Blo 738327 1108517 := bbase (se 4 (by rfl) ⟨103923, by rfl⟩ : syracuseStep 1108517 = 207847) (by norm_num)
theorem B1108541 : Blo 738327 1108541 := bbase (se 3 (by rfl) ⟨207851, by rfl⟩ : syracuseStep 1108541 = 415703) (by norm_num)
theorem B1108565 : Blo 738327 1108565 := bbase (se 8 (by rfl) ⟨6495, by rfl⟩ : syracuseStep 1108565 = 12991) (by norm_num)
theorem B1403477 : Blo 738327 1403477 := bbase (se 8 (by rfl) ⟨8223, by rfl⟩ : syracuseStep 1403477 = 16447) (by norm_num)
theorem B1665629 : Blo 738327 1665629 := bbase (se 3 (by rfl) ⟨312305, by rfl⟩ : syracuseStep 1665629 = 624611) (by norm_num)
theorem B1108589 : Blo 738327 1108589 := bbase (se 3 (by rfl) ⟨207860, by rfl⟩ : syracuseStep 1108589 = 415721) (by norm_num)
theorem B1108613 : Blo 738327 1108613 := bbase (se 4 (by rfl) ⟨103932, by rfl⟩ : syracuseStep 1108613 = 207865) (by norm_num)
theorem B1108637 : Blo 738327 1108637 := bbase (se 3 (by rfl) ⟨207869, by rfl⟩ : syracuseStep 1108637 = 415739) (by norm_num)
theorem B1665701 : Blo 738327 1665701 := bbase (se 4 (by rfl) ⟨156159, by rfl⟩ : syracuseStep 1665701 = 312319) (by norm_num)
theorem B1108661 : Blo 738327 1108661 := bbase (se 5 (by rfl) ⟨51968, by rfl⟩ : syracuseStep 1108661 = 103937) (by norm_num)
theorem B1108685 : Blo 738327 1108685 := bbase (se 3 (by rfl) ⟨207878, by rfl⟩ : syracuseStep 1108685 = 415757) (by norm_num)
theorem B1108709 : Blo 738327 1108709 := bbase (se 4 (by rfl) ⟨103941, by rfl⟩ : syracuseStep 1108709 = 207883) (by norm_num)
theorem B1665773 : Blo 738327 1665773 := bbase (se 3 (by rfl) ⟨312332, by rfl⟩ : syracuseStep 1665773 = 624665) (by norm_num)
theorem B1108733 : Blo 738327 1108733 := bbase (se 3 (by rfl) ⟨207887, by rfl⟩ : syracuseStep 1108733 = 415775) (by norm_num)
theorem B1108757 : Blo 738327 1108757 := bbase (se 6 (by rfl) ⟨25986, by rfl⟩ : syracuseStep 1108757 = 51973) (by norm_num)
theorem B1108781 : Blo 738327 1108781 := bbase (se 3 (by rfl) ⟨207896, by rfl⟩ : syracuseStep 1108781 = 415793) (by norm_num)
theorem B1665845 : Blo 738327 1665845 := bbase (se 5 (by rfl) ⟨78086, by rfl⟩ : syracuseStep 1665845 = 156173) (by norm_num)
theorem B1108805 : Blo 738327 1108805 := bbase (se 4 (by rfl) ⟨103950, by rfl⟩ : syracuseStep 1108805 = 207901) (by norm_num)
theorem B1108829 : Blo 738327 1108829 := bbase (se 3 (by rfl) ⟨207905, by rfl⟩ : syracuseStep 1108829 = 415811) (by norm_num)
theorem B1108853 : Blo 738327 1108853 := bbase (se 5 (by rfl) ⟨51977, by rfl⟩ : syracuseStep 1108853 = 103955) (by norm_num)
theorem B1665917 : Blo 738327 1665917 := bbase (se 3 (by rfl) ⟨312359, by rfl⟩ : syracuseStep 1665917 = 624719) (by norm_num)
theorem B1108877 : Blo 738327 1108877 := bbase (se 3 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 1108877 = 415829) (by norm_num)
theorem B1108901 : Blo 738327 1108901 := bbase (se 4 (by rfl) ⟨103959, by rfl⟩ : syracuseStep 1108901 = 207919) (by norm_num)
theorem B1108925 : Blo 738327 1108925 := bbase (se 3 (by rfl) ⟨207923, by rfl⟩ : syracuseStep 1108925 = 415847) (by norm_num)
theorem B1665989 : Blo 738327 1665989 := bbase (se 4 (by rfl) ⟨156186, by rfl⟩ : syracuseStep 1665989 = 312373) (by norm_num)
theorem B1108949 : Blo 738327 1108949 := bbase (se 7 (by rfl) ⟨12995, by rfl⟩ : syracuseStep 1108949 = 25991) (by norm_num)
theorem B1108973 : Blo 738327 1108973 := bbase (se 3 (by rfl) ⟨207932, by rfl⟩ : syracuseStep 1108973 = 415865) (by norm_num)
theorem B1108997 : Blo 738327 1108997 := bbase (se 4 (by rfl) ⟨103968, by rfl⟩ : syracuseStep 1108997 = 207937) (by norm_num)
theorem B1666061 : Blo 738327 1666061 := bbase (se 3 (by rfl) ⟨312386, by rfl⟩ : syracuseStep 1666061 = 624773) (by norm_num)
theorem B1109021 : Blo 738327 1109021 := bbase (se 3 (by rfl) ⟨207941, by rfl⟩ : syracuseStep 1109021 = 415883) (by norm_num)
theorem B1109045 : Blo 738327 1109045 := bbase (se 5 (by rfl) ⟨51986, by rfl⟩ : syracuseStep 1109045 = 103973) (by norm_num)
theorem B748613 : Blo 738327 748613 := bbase (se 4 (by rfl) ⟨70182, by rfl⟩ : syracuseStep 748613 = 140365) (by norm_num)
theorem B1109069 : Blo 738327 1109069 := bbase (se 3 (by rfl) ⟨207950, by rfl⟩ : syracuseStep 1109069 = 415901) (by norm_num)
theorem B1666133 : Blo 738327 1666133 := bbase (se 8 (by rfl) ⟨9762, by rfl⟩ : syracuseStep 1666133 = 19525) (by norm_num)
theorem B8449109 : Blo 738327 8449109 := bbase (se 8 (by rfl) ⟨49506, by rfl⟩ : syracuseStep 8449109 = 99013) (by norm_num)
theorem B1109093 : Blo 738327 1109093 := bbase (se 4 (by rfl) ⟨103977, by rfl⟩ : syracuseStep 1109093 = 207955) (by norm_num)
theorem B1109117 : Blo 738327 1109117 := bbase (se 3 (by rfl) ⟨207959, by rfl⟩ : syracuseStep 1109117 = 415919) (by norm_num)
theorem B1109141 : Blo 738327 1109141 := bbase (se 6 (by rfl) ⟨25995, by rfl⟩ : syracuseStep 1109141 = 51991) (by norm_num)
theorem B1666205 : Blo 738327 1666205 := bbase (se 3 (by rfl) ⟨312413, by rfl⟩ : syracuseStep 1666205 = 624827) (by norm_num)
theorem B1109165 : Blo 738327 1109165 := bbase (se 3 (by rfl) ⟨207968, by rfl⟩ : syracuseStep 1109165 = 415937) (by norm_num)
theorem B1109189 : Blo 738327 1109189 := bbase (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) (by norm_num)
theorem B1109213 : Blo 738327 1109213 := bbase (se 3 (by rfl) ⟨207977, by rfl⟩ : syracuseStep 1109213 = 415955) (by norm_num)
theorem B1666277 : Blo 738327 1666277 := bbase (se 4 (by rfl) ⟨156213, by rfl⟩ : syracuseStep 1666277 = 312427) (by norm_num)
theorem B1109237 : Blo 738327 1109237 := bbase (se 5 (by rfl) ⟨51995, by rfl⟩ : syracuseStep 1109237 = 103991) (by norm_num)
theorem B1109261 : Blo 738327 1109261 := bbase (se 3 (by rfl) ⟨207986, by rfl⟩ : syracuseStep 1109261 = 415973) (by norm_num)
theorem B1109285 : Blo 738327 1109285 := bbase (se 4 (by rfl) ⟨103995, by rfl⟩ : syracuseStep 1109285 = 207991) (by norm_num)
theorem B1666349 : Blo 738327 1666349 := bbase (se 3 (by rfl) ⟨312440, by rfl⟩ : syracuseStep 1666349 = 624881) (by norm_num)
theorem B1142069 : Blo 738327 1142069 := bbase (se 5 (by rfl) ⟨53534, by rfl⟩ : syracuseStep 1142069 = 107069) (by norm_num)
theorem B1109309 : Blo 738327 1109309 := bbase (se 3 (by rfl) ⟨207995, by rfl⟩ : syracuseStep 1109309 = 415991) (by norm_num)
theorem B1404229 : Blo 738327 1404229 := bbase (se 4 (by rfl) ⟨131646, by rfl⟩ : syracuseStep 1404229 = 263293) (by norm_num)
theorem B748873 : Blo 738327 748873 := bbase (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) (by norm_num)
theorem B1109333 : Blo 738327 1109333 := bbase (se 11 (by rfl) ⟨812, by rfl⟩ : syracuseStep 1109333 = 1625) (by norm_num)
theorem B814429 : Blo 738327 814429 := bbase (se 3 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 814429 = 305411) (by norm_num)
theorem B1109357 : Blo 738327 1109357 := bbase (se 3 (by rfl) ⟨208004, by rfl⟩ : syracuseStep 1109357 = 416009) (by norm_num)
theorem B1666421 : Blo 738327 1666421 := bbase (se 5 (by rfl) ⟨78113, by rfl⟩ : syracuseStep 1666421 = 156227) (by norm_num)
theorem B1109381 : Blo 738327 1109381 := bbase (se 4 (by rfl) ⟨104004, by rfl⟩ : syracuseStep 1109381 = 208009) (by norm_num)
theorem B748945 : Blo 738327 748945 := bbase (se 2 (by rfl) ⟨280854, by rfl⟩ : syracuseStep 748945 = 561709) (by norm_num)
theorem B1109405 : Blo 738327 1109405 := bbase (se 3 (by rfl) ⟨208013, by rfl⟩ : syracuseStep 1109405 = 416027) (by norm_num)
theorem B1109429 : Blo 738327 1109429 := bbase (se 5 (by rfl) ⟨52004, by rfl⟩ : syracuseStep 1109429 = 104009) (by norm_num)
theorem B1666493 : Blo 738327 1666493 := bbase (se 3 (by rfl) ⟨312467, by rfl⟩ : syracuseStep 1666493 = 624935) (by norm_num)
theorem B1109453 : Blo 738327 1109453 := bbase (se 3 (by rfl) ⟨208022, by rfl⟩ : syracuseStep 1109453 = 416045) (by norm_num)
theorem B1404373 : Blo 738327 1404373 := bbase (se 7 (by rfl) ⟨16457, by rfl⟩ : syracuseStep 1404373 = 32915) (by norm_num)
theorem B1109477 : Blo 738327 1109477 := bbase (se 4 (by rfl) ⟨104013, by rfl⟩ : syracuseStep 1109477 = 208027) (by norm_num)
theorem B1109501 : Blo 738327 1109501 := bbase (se 3 (by rfl) ⟨208031, by rfl⟩ : syracuseStep 1109501 = 416063) (by norm_num)
theorem B1666565 : Blo 738327 1666565 := bbase (se 4 (by rfl) ⟨156240, by rfl⟩ : syracuseStep 1666565 = 312481) (by norm_num)
theorem B1109525 : Blo 738327 1109525 := bbase (se 6 (by rfl) ⟨26004, by rfl⟩ : syracuseStep 1109525 = 52009) (by norm_num)
theorem B1109549 : Blo 738327 1109549 := bbase (se 3 (by rfl) ⟨208040, by rfl⟩ : syracuseStep 1109549 = 416081) (by norm_num)
theorem B1109573 : Blo 738327 1109573 := bbase (se 4 (by rfl) ⟨104022, by rfl⟩ : syracuseStep 1109573 = 208045) (by norm_num)
theorem B1666637 : Blo 738327 1666637 := bbase (se 3 (by rfl) ⟨312494, by rfl⟩ : syracuseStep 1666637 = 624989) (by norm_num)
theorem B1109597 : Blo 738327 1109597 := bbase (se 3 (by rfl) ⟨208049, by rfl⟩ : syracuseStep 1109597 = 416099) (by norm_num)
theorem B1109621 : Blo 738327 1109621 := bbase (se 5 (by rfl) ⟨52013, by rfl⟩ : syracuseStep 1109621 = 104027) (by norm_num)
theorem B1404533 : Blo 738327 1404533 := bbase (se 5 (by rfl) ⟨65837, by rfl⟩ : syracuseStep 1404533 = 131675) (by norm_num)
theorem B1109645 : Blo 738327 1109645 := bbase (se 3 (by rfl) ⟨208058, by rfl⟩ : syracuseStep 1109645 = 416117) (by norm_num)
theorem B1666709 : Blo 738327 1666709 := bbase (se 6 (by rfl) ⟨39063, by rfl⟩ : syracuseStep 1666709 = 78127) (by norm_num)
theorem B1109669 : Blo 738327 1109669 := bbase (se 4 (by rfl) ⟨104031, by rfl⟩ : syracuseStep 1109669 = 208063) (by norm_num)
theorem B1109693 : Blo 738327 1109693 := bbase (se 3 (by rfl) ⟨208067, by rfl⟩ : syracuseStep 1109693 = 416135) (by norm_num)
theorem B1109717 : Blo 738327 1109717 := bbase (se 7 (by rfl) ⟨13004, by rfl⟩ : syracuseStep 1109717 = 26009) (by norm_num)
theorem B1666781 : Blo 738327 1666781 := bbase (se 3 (by rfl) ⟨312521, by rfl⟩ : syracuseStep 1666781 = 625043) (by norm_num)
theorem B1109741 : Blo 738327 1109741 := bbase (se 3 (by rfl) ⟨208076, by rfl⟩ : syracuseStep 1109741 = 416153) (by norm_num)
theorem B1109765 : Blo 738327 1109765 := bbase (se 4 (by rfl) ⟨104040, by rfl⟩ : syracuseStep 1109765 = 208081) (by norm_num)
theorem B1404677 : Blo 738327 1404677 := bbase (se 4 (by rfl) ⟨131688, by rfl⟩ : syracuseStep 1404677 = 263377) (by norm_num)
theorem B1109789 : Blo 738327 1109789 := bbase (se 3 (by rfl) ⟨208085, by rfl⟩ : syracuseStep 1109789 = 416171) (by norm_num)
theorem B1666853 : Blo 738327 1666853 := bbase (se 4 (by rfl) ⟨156267, by rfl⟩ : syracuseStep 1666853 = 312535) (by norm_num)
theorem B1109813 : Blo 738327 1109813 := bbase (se 5 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 1109813 = 104045) (by norm_num)
theorem B1109837 : Blo 738327 1109837 := bbase (se 3 (by rfl) ⟨208094, by rfl⟩ : syracuseStep 1109837 = 416189) (by norm_num)
theorem B1109861 : Blo 738327 1109861 := bbase (se 4 (by rfl) ⟨104049, by rfl⟩ : syracuseStep 1109861 = 208099) (by norm_num)
theorem B1666925 : Blo 738327 1666925 := bbase (se 3 (by rfl) ⟨312548, by rfl⟩ : syracuseStep 1666925 = 625097) (by norm_num)
theorem B1109885 : Blo 738327 1109885 := bbase (se 3 (by rfl) ⟨208103, by rfl⟩ : syracuseStep 1109885 = 416207) (by norm_num)
theorem B7106453 : Blo 738327 7106453 := bbase (se 6 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 7106453 = 333115) (by norm_num)
theorem B1109909 : Blo 738327 1109909 := bbase (se 6 (by rfl) ⟨26013, by rfl⟩ : syracuseStep 1109909 = 52027) (by norm_num)
theorem B1109933 : Blo 738327 1109933 := bbase (se 3 (by rfl) ⟨208112, by rfl⟩ : syracuseStep 1109933 = 416225) (by norm_num)
theorem B1666997 : Blo 738327 1666997 := bbase (se 5 (by rfl) ⟨78140, by rfl⟩ : syracuseStep 1666997 = 156281) (by norm_num)
theorem B1109957 : Blo 738327 1109957 := bbase (se 4 (by rfl) ⟨104058, by rfl⟩ : syracuseStep 1109957 = 208117) (by norm_num)
theorem B749521 : Blo 738327 749521 := bbase (se 2 (by rfl) ⟨281070, by rfl⟩ : syracuseStep 749521 = 562141) (by norm_num)
theorem B1109981 : Blo 738327 1109981 := bbase (se 3 (by rfl) ⟨208121, by rfl⟩ : syracuseStep 1109981 = 416243) (by norm_num)
theorem B1110005 : Blo 738327 1110005 := bbase (se 5 (by rfl) ⟨52031, by rfl⟩ : syracuseStep 1110005 = 104063) (by norm_num)
theorem B1667069 : Blo 738327 1667069 := bbase (se 3 (by rfl) ⟨312575, by rfl⟩ : syracuseStep 1667069 = 625151) (by norm_num)
theorem B1110029 : Blo 738327 1110029 := bbase (se 3 (by rfl) ⟨208130, by rfl⟩ : syracuseStep 1110029 = 416261) (by norm_num)
theorem B1110053 : Blo 738327 1110053 := bbase (se 4 (by rfl) ⟨104067, by rfl⟩ : syracuseStep 1110053 = 208135) (by norm_num)
theorem B1404965 : Blo 738327 1404965 := bbase (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) (by norm_num)
theorem B1110077 : Blo 738327 1110077 := bbase (se 3 (by rfl) ⟨208139, by rfl⟩ : syracuseStep 1110077 = 416279) (by norm_num)
theorem B1667141 : Blo 738327 1667141 := bbase (se 4 (by rfl) ⟨156294, by rfl⟩ : syracuseStep 1667141 = 312589) (by norm_num)
theorem B1110101 : Blo 738327 1110101 := bbase (se 8 (by rfl) ⟨6504, by rfl⟩ : syracuseStep 1110101 = 13009) (by norm_num)
theorem B1110125 : Blo 738327 1110125 := bbase (se 3 (by rfl) ⟨208148, by rfl⟩ : syracuseStep 1110125 = 416297) (by norm_num)
theorem B1110149 : Blo 738327 1110149 := bbase (se 4 (by rfl) ⟨104076, by rfl⟩ : syracuseStep 1110149 = 208153) (by norm_num)
theorem B1667213 : Blo 738327 1667213 := bbase (se 3 (by rfl) ⟨312602, by rfl⟩ : syracuseStep 1667213 = 625205) (by norm_num)
theorem B1503373 : Blo 738327 1503373 := bbase (se 3 (by rfl) ⟨281882, by rfl⟩ : syracuseStep 1503373 = 563765) (by norm_num)
theorem B1110173 : Blo 738327 1110173 := bbase (se 3 (by rfl) ⟨208157, by rfl⟩ : syracuseStep 1110173 = 416315) (by norm_num)
theorem B1896629 : Blo 738327 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B1110197 : Blo 738327 1110197 := bbase (se 5 (by rfl) ⟨52040, by rfl⟩ : syracuseStep 1110197 = 104081) (by norm_num)
theorem B1405117 : Blo 738327 1405117 := bbase (se 3 (by rfl) ⟨263459, by rfl⟩ : syracuseStep 1405117 = 526919) (by norm_num)
theorem B1110221 : Blo 738327 1110221 := bbase (se 3 (by rfl) ⟨208166, by rfl⟩ : syracuseStep 1110221 = 416333) (by norm_num)
theorem B1667285 : Blo 738327 1667285 := bbase (se 7 (by rfl) ⟨19538, by rfl⟩ : syracuseStep 1667285 = 39077) (by norm_num)
theorem B1110245 : Blo 738327 1110245 := bbase (se 4 (by rfl) ⟨104085, by rfl⟩ : syracuseStep 1110245 = 208171) (by norm_num)
theorem B1503469 : Blo 738327 1503469 := bbase (se 3 (by rfl) ⟨281900, by rfl⟩ : syracuseStep 1503469 = 563801) (by norm_num)
theorem B1110269 : Blo 738327 1110269 := bbase (se 3 (by rfl) ⟨208175, by rfl⟩ : syracuseStep 1110269 = 416351) (by norm_num)
theorem B1110293 : Blo 738327 1110293 := bbase (se 6 (by rfl) ⟨26022, by rfl⟩ : syracuseStep 1110293 = 52045) (by norm_num)
theorem B1667357 : Blo 738327 1667357 := bbase (se 3 (by rfl) ⟨312629, by rfl⟩ : syracuseStep 1667357 = 625259) (by norm_num)
theorem B1110317 : Blo 738327 1110317 := bbase (se 3 (by rfl) ⟨208184, by rfl⟩ : syracuseStep 1110317 = 416369) (by norm_num)
theorem B1110341 : Blo 738327 1110341 := bbase (se 4 (by rfl) ⟨104094, by rfl⟩ : syracuseStep 1110341 = 208189) (by norm_num)
theorem B3993941 : Blo 738327 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B1110365 : Blo 738327 1110365 := bbase (se 3 (by rfl) ⟨208193, by rfl⟩ : syracuseStep 1110365 = 416387) (by norm_num)
theorem B1667429 : Blo 738327 1667429 := bbase (se 4 (by rfl) ⟨156321, by rfl⟩ : syracuseStep 1667429 = 312643) (by norm_num)
theorem B1110389 : Blo 738327 1110389 := bbase (se 5 (by rfl) ⟨52049, by rfl⟩ : syracuseStep 1110389 = 104099) (by norm_num)
theorem B1110413 : Blo 738327 1110413 := bbase (se 3 (by rfl) ⟨208202, by rfl⟩ : syracuseStep 1110413 = 416405) (by norm_num)
theorem B1012133 : Blo 738327 1012133 := bbase (se 4 (by rfl) ⟨94887, by rfl⟩ : syracuseStep 1012133 = 189775) (by norm_num)
theorem B1110437 : Blo 738327 1110437 := bbase (se 4 (by rfl) ⟨104103, by rfl⟩ : syracuseStep 1110437 = 208207) (by norm_num)
theorem B1667501 : Blo 738327 1667501 := bbase (se 3 (by rfl) ⟨312656, by rfl⟩ : syracuseStep 1667501 = 625313) (by norm_num)
theorem B1110461 : Blo 738327 1110461 := bbase (se 3 (by rfl) ⟨208211, by rfl⟩ : syracuseStep 1110461 = 416423) (by norm_num)
theorem B1110485 : Blo 738327 1110485 := bbase (se 7 (by rfl) ⟨13013, by rfl⟩ : syracuseStep 1110485 = 26027) (by norm_num)
theorem B1405421 : Blo 738327 1405421 := bbase (se 3 (by rfl) ⟨263516, by rfl⟩ : syracuseStep 1405421 = 527033) (by norm_num)
theorem B1110509 : Blo 738327 1110509 := bbase (se 3 (by rfl) ⟨208220, by rfl⟩ : syracuseStep 1110509 = 416441) (by norm_num)
theorem B1667573 : Blo 738327 1667573 := bbase (se 5 (by rfl) ⟨78167, by rfl⟩ : syracuseStep 1667573 = 156335) (by norm_num)
theorem B1110533 : Blo 738327 1110533 := bbase (se 4 (by rfl) ⟨104112, by rfl⟩ : syracuseStep 1110533 = 208225) (by norm_num)
theorem B750097 : Blo 738327 750097 := bbase (se 2 (by rfl) ⟨281286, by rfl⟩ : syracuseStep 750097 = 562573) (by norm_num)
theorem B1110557 : Blo 738327 1110557 := bbase (se 3 (by rfl) ⟨208229, by rfl⟩ : syracuseStep 1110557 = 416459) (by norm_num)
theorem B1110581 : Blo 738327 1110581 := bbase (se 5 (by rfl) ⟨52058, by rfl⟩ : syracuseStep 1110581 = 104117) (by norm_num)
theorem B1667645 : Blo 738327 1667645 := bbase (se 3 (by rfl) ⟨312683, by rfl⟩ : syracuseStep 1667645 = 625367) (by norm_num)
theorem B2814533 : Blo 738327 2814533 := bbase (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) (by norm_num)
theorem B1110605 : Blo 738327 1110605 := bbase (se 3 (by rfl) ⟨208238, by rfl⟩ : syracuseStep 1110605 = 416477) (by norm_num)
theorem B1110629 : Blo 738327 1110629 := bbase (se 4 (by rfl) ⟨104121, by rfl⟩ : syracuseStep 1110629 = 208243) (by norm_num)
theorem B1110653 : Blo 738327 1110653 := bbase (se 3 (by rfl) ⟨208247, by rfl⟩ : syracuseStep 1110653 = 416495) (by norm_num)
theorem B1667717 : Blo 738327 1667717 := bbase (se 4 (by rfl) ⟨156348, by rfl⟩ : syracuseStep 1667717 = 312697) (by norm_num)
theorem B1110677 : Blo 738327 1110677 := bbase (se 6 (by rfl) ⟨26031, by rfl⟩ : syracuseStep 1110677 = 52063) (by norm_num)
theorem B1110701 : Blo 738327 1110701 := bbase (se 3 (by rfl) ⟨208256, by rfl⟩ : syracuseStep 1110701 = 416513) (by norm_num)
theorem B1110725 : Blo 738327 1110725 := bbase (se 4 (by rfl) ⟨104130, by rfl⟩ : syracuseStep 1110725 = 208261) (by norm_num)
theorem B1667789 : Blo 738327 1667789 := bbase (se 3 (by rfl) ⟨312710, by rfl⟩ : syracuseStep 1667789 = 625421) (by norm_num)
theorem B1110749 : Blo 738327 1110749 := bbase (se 3 (by rfl) ⟨208265, by rfl⟩ : syracuseStep 1110749 = 416531) (by norm_num)
theorem B1110773 : Blo 738327 1110773 := bbase (se 5 (by rfl) ⟨52067, by rfl⟩ : syracuseStep 1110773 = 104135) (by norm_num)
theorem B1110797 : Blo 738327 1110797 := bbase (se 3 (by rfl) ⟨208274, by rfl⟩ : syracuseStep 1110797 = 416549) (by norm_num)
theorem B1667861 : Blo 738327 1667861 := bbase (se 6 (by rfl) ⟨39090, by rfl⟩ : syracuseStep 1667861 = 78181) (by norm_num)
theorem B1110821 : Blo 738327 1110821 := bbase (se 4 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 1110821 = 208279) (by norm_num)
theorem B2028341 : Blo 738327 2028341 := bbase (se 5 (by rfl) ⟨95078, by rfl⟩ : syracuseStep 2028341 = 190157) (by norm_num)
theorem B1110845 : Blo 738327 1110845 := bbase (se 3 (by rfl) ⟨208283, by rfl⟩ : syracuseStep 1110845 = 416567) (by norm_num)
theorem B1110869 : Blo 738327 1110869 := bbase (se 9 (by rfl) ⟨3254, by rfl⟩ : syracuseStep 1110869 = 6509) (by norm_num)
theorem B1667933 : Blo 738327 1667933 := bbase (se 3 (by rfl) ⟨312737, by rfl⟩ : syracuseStep 1667933 = 625475) (by norm_num)
theorem B2814821 : Blo 738327 2814821 := bbase (se 4 (by rfl) ⟨263889, by rfl⟩ : syracuseStep 2814821 = 527779) (by norm_num)
theorem B1110893 : Blo 738327 1110893 := bbase (se 3 (by rfl) ⟨208292, by rfl⟩ : syracuseStep 1110893 = 416585) (by norm_num)
theorem B1110917 : Blo 738327 1110917 := bbase (se 4 (by rfl) ⟨104148, by rfl⟩ : syracuseStep 1110917 = 208297) (by norm_num)
theorem B1110941 : Blo 738327 1110941 := bbase (se 3 (by rfl) ⟨208301, by rfl⟩ : syracuseStep 1110941 = 416603) (by norm_num)
theorem B1668005 : Blo 738327 1668005 := bbase (se 4 (by rfl) ⟨156375, by rfl⟩ : syracuseStep 1668005 = 312751) (by norm_num)
theorem B1110965 : Blo 738327 1110965 := bbase (se 5 (by rfl) ⟨52076, by rfl⟩ : syracuseStep 1110965 = 104153) (by norm_num)
theorem B914377 : Blo 738327 914377 := bbase (se 2 (by rfl) ⟨342891, by rfl⟩ : syracuseStep 914377 = 685783) (by norm_num)
theorem B1110989 : Blo 738327 1110989 := bbase (se 3 (by rfl) ⟨208310, by rfl⟩ : syracuseStep 1110989 = 416621) (by norm_num)
theorem B1111013 : Blo 738327 1111013 := bbase (se 4 (by rfl) ⟨104157, by rfl⟩ : syracuseStep 1111013 = 208315) (by norm_num)
theorem B1668077 : Blo 738327 1668077 := bbase (se 3 (by rfl) ⟨312764, by rfl⟩ : syracuseStep 1668077 = 625529) (by norm_num)
theorem B1111037 : Blo 738327 1111037 := bbase (se 3 (by rfl) ⟨208319, by rfl⟩ : syracuseStep 1111037 = 416639) (by norm_num)
theorem B1111061 : Blo 738327 1111061 := bbase (se 6 (by rfl) ⟨26040, by rfl⟩ : syracuseStep 1111061 = 52081) (by norm_num)
theorem B1111085 : Blo 738327 1111085 := bbase (se 3 (by rfl) ⟨208328, by rfl⟩ : syracuseStep 1111085 = 416657) (by norm_num)
theorem B1668149 : Blo 738327 1668149 := bbase (se 5 (by rfl) ⟨78194, by rfl⟩ : syracuseStep 1668149 = 156389) (by norm_num)
theorem B1111109 : Blo 738327 1111109 := bbase (se 4 (by rfl) ⟨104166, by rfl⟩ : syracuseStep 1111109 = 208333) (by norm_num)
theorem B750665 : Blo 738327 750665 := bbase (se 2 (by rfl) ⟨281499, by rfl⟩ : syracuseStep 750665 = 562999) (by norm_num)
theorem B1111133 : Blo 738327 1111133 := bbase (se 3 (by rfl) ⟨208337, by rfl⟩ : syracuseStep 1111133 = 416675) (by norm_num)
theorem B1897573 : Blo 738327 1897573 := bbase (se 4 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 1897573 = 355795) (by norm_num)
theorem B1111157 : Blo 738327 1111157 := bbase (se 5 (by rfl) ⟨52085, by rfl⟩ : syracuseStep 1111157 = 104171) (by norm_num)
theorem B1668221 : Blo 738327 1668221 := bbase (se 3 (by rfl) ⟨312791, by rfl⟩ : syracuseStep 1668221 = 625583) (by norm_num)
theorem B1111181 : Blo 738327 1111181 := bbase (se 3 (by rfl) ⟨208346, by rfl⟩ : syracuseStep 1111181 = 416693) (by norm_num)
theorem B1111205 : Blo 738327 1111205 := bbase (se 4 (by rfl) ⟨104175, by rfl⟩ : syracuseStep 1111205 = 208351) (by norm_num)
theorem B1111229 : Blo 738327 1111229 := bbase (se 3 (by rfl) ⟨208355, by rfl⟩ : syracuseStep 1111229 = 416711) (by norm_num)
theorem B1668293 : Blo 738327 1668293 := bbase (se 4 (by rfl) ⟨156402, by rfl⟩ : syracuseStep 1668293 = 312805) (by norm_num)
theorem B1111253 : Blo 738327 1111253 := bbase (se 7 (by rfl) ⟨13022, by rfl⟩ : syracuseStep 1111253 = 26045) (by norm_num)
theorem B1406173 : Blo 738327 1406173 := bbase (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) (by norm_num)
theorem B1111277 : Blo 738327 1111277 := bbase (se 3 (by rfl) ⟨208364, by rfl⟩ : syracuseStep 1111277 = 416729) (by norm_num)
theorem B1111301 : Blo 738327 1111301 := bbase (se 4 (by rfl) ⟨104184, by rfl⟩ : syracuseStep 1111301 = 208369) (by norm_num)
theorem B1668365 : Blo 738327 1668365 := bbase (se 3 (by rfl) ⟨312818, by rfl⟩ : syracuseStep 1668365 = 625637) (by norm_num)
theorem B1111325 : Blo 738327 1111325 := bbase (se 3 (by rfl) ⟨208373, by rfl⟩ : syracuseStep 1111325 = 416747) (by norm_num)
theorem B1111349 : Blo 738327 1111349 := bbase (se 5 (by rfl) ⟨52094, by rfl⟩ : syracuseStep 1111349 = 104189) (by norm_num)
theorem B1111373 : Blo 738327 1111373 := bbase (se 3 (by rfl) ⟨208382, by rfl⟩ : syracuseStep 1111373 = 416765) (by norm_num)
theorem B1668437 : Blo 738327 1668437 := bbase (se 13 (by rfl) ⟨305, by rfl⟩ : syracuseStep 1668437 = 611) (by norm_num)
theorem B1504597 : Blo 738327 1504597 := bbase (se 13 (by rfl) ⟨275, by rfl⟩ : syracuseStep 1504597 = 551) (by norm_num)
theorem B1111397 : Blo 738327 1111397 := bbase (se 4 (by rfl) ⟨104193, by rfl⟩ : syracuseStep 1111397 = 208387) (by norm_num)
theorem B1406317 : Blo 738327 1406317 := bbase (se 3 (by rfl) ⟨263684, by rfl⟩ : syracuseStep 1406317 = 527369) (by norm_num)
theorem B1111421 : Blo 738327 1111421 := bbase (se 3 (by rfl) ⟨208391, by rfl⟩ : syracuseStep 1111421 = 416783) (by norm_num)
theorem B1111445 : Blo 738327 1111445 := bbase (se 6 (by rfl) ⟨26049, by rfl⟩ : syracuseStep 1111445 = 52099) (by norm_num)
theorem B1668509 : Blo 738327 1668509 := bbase (se 3 (by rfl) ⟨312845, by rfl⟩ : syracuseStep 1668509 = 625691) (by norm_num)
theorem B751021 : Blo 738327 751021 := bbase (se 3 (by rfl) ⟨140816, by rfl⟩ : syracuseStep 751021 = 281633) (by norm_num)
theorem B1111469 : Blo 738327 1111469 := bbase (se 3 (by rfl) ⟨208400, by rfl⟩ : syracuseStep 1111469 = 416801) (by norm_num)
theorem B1111493 : Blo 738327 1111493 := bbase (se 4 (by rfl) ⟨104202, by rfl⟩ : syracuseStep 1111493 = 208405) (by norm_num)
theorem B1111517 : Blo 738327 1111517 := bbase (se 3 (by rfl) ⟨208409, by rfl⟩ : syracuseStep 1111517 = 416819) (by norm_num)
theorem B1668581 : Blo 738327 1668581 := bbase (se 4 (by rfl) ⟨156429, by rfl⟩ : syracuseStep 1668581 = 312859) (by norm_num)
theorem B1111541 : Blo 738327 1111541 := bbase (se 5 (by rfl) ⟨52103, by rfl⟩ : syracuseStep 1111541 = 104207) (by norm_num)
theorem B1406477 : Blo 738327 1406477 := bbase (se 3 (by rfl) ⟨263714, by rfl⟩ : syracuseStep 1406477 = 527429) (by norm_num)
theorem B1111565 : Blo 738327 1111565 := bbase (se 3 (by rfl) ⟨208418, by rfl⟩ : syracuseStep 1111565 = 416837) (by norm_num)
theorem B1111589 : Blo 738327 1111589 := bbase (se 4 (by rfl) ⟨104211, by rfl⟩ : syracuseStep 1111589 = 208423) (by norm_num)
theorem B1668653 : Blo 738327 1668653 := bbase (se 3 (by rfl) ⟨312872, by rfl⟩ : syracuseStep 1668653 = 625745) (by norm_num)
theorem B1111613 : Blo 738327 1111613 := bbase (se 3 (by rfl) ⟨208427, by rfl⟩ : syracuseStep 1111613 = 416855) (by norm_num)
theorem B1111637 : Blo 738327 1111637 := bbase (se 8 (by rfl) ⟨6513, by rfl⟩ : syracuseStep 1111637 = 13027) (by norm_num)
theorem B1111661 : Blo 738327 1111661 := bbase (se 3 (by rfl) ⟨208436, by rfl⟩ : syracuseStep 1111661 = 416873) (by norm_num)
theorem B1668725 : Blo 738327 1668725 := bbase (se 5 (by rfl) ⟨78221, by rfl⟩ : syracuseStep 1668725 = 156443) (by norm_num)
theorem B1111685 : Blo 738327 1111685 := bbase (se 4 (by rfl) ⟨104220, by rfl⟩ : syracuseStep 1111685 = 208441) (by norm_num)
theorem B1406621 : Blo 738327 1406621 := bbase (se 3 (by rfl) ⟨263741, by rfl⟩ : syracuseStep 1406621 = 527483) (by norm_num)
theorem B1111709 : Blo 738327 1111709 := bbase (se 3 (by rfl) ⟨208445, by rfl⟩ : syracuseStep 1111709 = 416891) (by norm_num)
theorem B1111733 : Blo 738327 1111733 := bbase (se 5 (by rfl) ⟨52112, by rfl⟩ : syracuseStep 1111733 = 104225) (by norm_num)
theorem B1668797 : Blo 738327 1668797 := bbase (se 3 (by rfl) ⟨312899, by rfl⟩ : syracuseStep 1668797 = 625799) (by norm_num)
theorem B1111757 : Blo 738327 1111757 := bbase (se 3 (by rfl) ⟨208454, by rfl⟩ : syracuseStep 1111757 = 416909) (by norm_num)
theorem B1111781 : Blo 738327 1111781 := bbase (se 4 (by rfl) ⟨104229, by rfl⟩ : syracuseStep 1111781 = 208459) (by norm_num)
theorem B751337 : Blo 738327 751337 := bbase (se 2 (by rfl) ⟨281751, by rfl⟩ : syracuseStep 751337 = 563503) (by norm_num)
theorem B1111805 : Blo 738327 1111805 := bbase (se 3 (by rfl) ⟨208463, by rfl⟩ : syracuseStep 1111805 = 416927) (by norm_num)
theorem B1668869 : Blo 738327 1668869 := bbase (se 4 (by rfl) ⟨156456, by rfl⟩ : syracuseStep 1668869 = 312913) (by norm_num)
theorem B1111829 : Blo 738327 1111829 := bbase (se 6 (by rfl) ⟨26058, by rfl⟩ : syracuseStep 1111829 = 52117) (by norm_num)
theorem B1111853 : Blo 738327 1111853 := bbase (se 3 (by rfl) ⟨208472, by rfl⟩ : syracuseStep 1111853 = 416945) (by norm_num)
theorem B1111877 : Blo 738327 1111877 := bbase (se 4 (by rfl) ⟨104238, by rfl⟩ : syracuseStep 1111877 = 208477) (by norm_num)
theorem B1668941 : Blo 738327 1668941 := bbase (se 3 (by rfl) ⟨312926, by rfl⟩ : syracuseStep 1668941 = 625853) (by norm_num)
theorem B1111901 : Blo 738327 1111901 := bbase (se 3 (by rfl) ⟨208481, by rfl⟩ : syracuseStep 1111901 = 416963) (by norm_num)
theorem B1111925 : Blo 738327 1111925 := bbase (se 5 (by rfl) ⟨52121, by rfl⟩ : syracuseStep 1111925 = 104243) (by norm_num)
theorem B1111949 : Blo 738327 1111949 := bbase (se 3 (by rfl) ⟨208490, by rfl⟩ : syracuseStep 1111949 = 416981) (by norm_num)
theorem B1669013 : Blo 738327 1669013 := bbase (se 6 (by rfl) ⟨39117, by rfl⟩ : syracuseStep 1669013 = 78235) (by norm_num)
theorem B1111973 : Blo 738327 1111973 := bbase (se 4 (by rfl) ⟨104247, by rfl⟩ : syracuseStep 1111973 = 208495) (by norm_num)
theorem B1406909 : Blo 738327 1406909 := bbase (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) (by norm_num)
theorem B1111997 : Blo 738327 1111997 := bbase (se 3 (by rfl) ⟨208499, by rfl⟩ : syracuseStep 1111997 = 416999) (by norm_num)
theorem B751565 : Blo 738327 751565 := bbase (se 3 (by rfl) ⟨140918, by rfl⟩ : syracuseStep 751565 = 281837) (by norm_num)
theorem B1112021 : Blo 738327 1112021 := bbase (se 7 (by rfl) ⟨13031, by rfl⟩ : syracuseStep 1112021 = 26063) (by norm_num)
theorem B1669085 : Blo 738327 1669085 := bbase (se 3 (by rfl) ⟨312953, by rfl⟩ : syracuseStep 1669085 = 625907) (by norm_num)
theorem B1112045 : Blo 738327 1112045 := bbase (se 3 (by rfl) ⟨208508, by rfl⟩ : syracuseStep 1112045 = 417017) (by norm_num)
theorem B1112069 : Blo 738327 1112069 := bbase (se 4 (by rfl) ⟨104256, by rfl⟩ : syracuseStep 1112069 = 208513) (by norm_num)
theorem B2816005 : Blo 738327 2816005 := bbase (se 4 (by rfl) ⟨264000, by rfl⟩ : syracuseStep 2816005 = 528001) (by norm_num)
theorem B1112093 : Blo 738327 1112093 := bbase (se 3 (by rfl) ⟨208517, by rfl⟩ : syracuseStep 1112093 = 417035) (by norm_num)
theorem B1669157 : Blo 738327 1669157 := bbase (se 4 (by rfl) ⟨156483, by rfl⟩ : syracuseStep 1669157 = 312967) (by norm_num)
theorem B1112117 : Blo 738327 1112117 := bbase (se 5 (by rfl) ⟨52130, by rfl⟩ : syracuseStep 1112117 = 104261) (by norm_num)
theorem B1112141 : Blo 738327 1112141 := bbase (se 3 (by rfl) ⟨208526, by rfl⟩ : syracuseStep 1112141 = 417053) (by norm_num)
theorem B1407061 : Blo 738327 1407061 := bbase (se 8 (by rfl) ⟨8244, by rfl⟩ : syracuseStep 1407061 = 16489) (by norm_num)
theorem B1112165 : Blo 738327 1112165 := bbase (se 4 (by rfl) ⟨104265, by rfl⟩ : syracuseStep 1112165 = 208531) (by norm_num)
theorem B1669229 : Blo 738327 1669229 := bbase (se 3 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 1669229 = 625961) (by norm_num)
theorem B1112189 : Blo 738327 1112189 := bbase (se 3 (by rfl) ⟨208535, by rfl⟩ : syracuseStep 1112189 = 417071) (by norm_num)
theorem B1112213 : Blo 738327 1112213 := bbase (se 6 (by rfl) ⟨26067, by rfl⟩ : syracuseStep 1112213 = 52135) (by norm_num)
theorem B5634197 : Blo 738327 5634197 := bbase (se 6 (by rfl) ⟨132051, by rfl⟩ : syracuseStep 5634197 = 264103) (by norm_num)
theorem B1112237 : Blo 738327 1112237 := bbase (se 3 (by rfl) ⟨208544, by rfl⟩ : syracuseStep 1112237 = 417089) (by norm_num)
theorem B1669301 : Blo 738327 1669301 := bbase (se 5 (by rfl) ⟨78248, by rfl⟩ : syracuseStep 1669301 = 156497) (by norm_num)
theorem B1112261 : Blo 738327 1112261 := bbase (se 4 (by rfl) ⟨104274, by rfl⟩ : syracuseStep 1112261 = 208549) (by norm_num)
theorem B1112285 : Blo 738327 1112285 := bbase (se 3 (by rfl) ⟨208553, by rfl⟩ : syracuseStep 1112285 = 417107) (by norm_num)
theorem B1112309 : Blo 738327 1112309 := bbase (se 5 (by rfl) ⟨52139, by rfl⟩ : syracuseStep 1112309 = 104279) (by norm_num)
theorem B1669373 : Blo 738327 1669373 := bbase (se 3 (by rfl) ⟨313007, by rfl⟩ : syracuseStep 1669373 = 626015) (by norm_num)
theorem B1112333 : Blo 738327 1112333 := bbase (se 3 (by rfl) ⟨208562, by rfl⟩ : syracuseStep 1112333 = 417125) (by norm_num)
theorem B1112357 : Blo 738327 1112357 := bbase (se 4 (by rfl) ⟨104283, by rfl⟩ : syracuseStep 1112357 = 208567) (by norm_num)
theorem B2816309 : Blo 738327 2816309 := bbase (se 5 (by rfl) ⟨132014, by rfl⟩ : syracuseStep 2816309 = 264029) (by norm_num)
theorem B1112381 : Blo 738327 1112381 := bbase (se 3 (by rfl) ⟨208571, by rfl⟩ : syracuseStep 1112381 = 417143) (by norm_num)
theorem B1669445 : Blo 738327 1669445 := bbase (se 4 (by rfl) ⟨156510, by rfl⟩ : syracuseStep 1669445 = 313021) (by norm_num)
theorem B1112405 : Blo 738327 1112405 := bbase (se 10 (by rfl) ⟨1629, by rfl⟩ : syracuseStep 1112405 = 3259) (by norm_num)
theorem B1112429 : Blo 738327 1112429 := bbase (se 3 (by rfl) ⟨208580, by rfl⟩ : syracuseStep 1112429 = 417161) (by norm_num)
theorem B1407365 : Blo 738327 1407365 := bbase (se 4 (by rfl) ⟨131940, by rfl⟩ : syracuseStep 1407365 = 263881) (by norm_num)
theorem B1112453 : Blo 738327 1112453 := bbase (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) (by norm_num)
theorem B1669517 : Blo 738327 1669517 := bbase (se 3 (by rfl) ⟨313034, by rfl⟩ : syracuseStep 1669517 = 626069) (by norm_num)
theorem B1112477 : Blo 738327 1112477 := bbase (se 3 (by rfl) ⟨208589, by rfl⟩ : syracuseStep 1112477 = 417179) (by norm_num)
theorem B1112501 : Blo 738327 1112501 := bbase (se 5 (by rfl) ⟨52148, by rfl⟩ : syracuseStep 1112501 = 104297) (by norm_num)
theorem B1112525 : Blo 738327 1112525 := bbase (se 3 (by rfl) ⟨208598, by rfl⟩ : syracuseStep 1112525 = 417197) (by norm_num)
theorem B1669589 : Blo 738327 1669589 := bbase (se 7 (by rfl) ⟨19565, by rfl⟩ : syracuseStep 1669589 = 39131) (by norm_num)
theorem B1112549 : Blo 738327 1112549 := bbase (se 4 (by rfl) ⟨104301, by rfl⟩ : syracuseStep 1112549 = 208603) (by norm_num)
theorem B1112573 : Blo 738327 1112573 := bbase (se 3 (by rfl) ⟨208607, by rfl⟩ : syracuseStep 1112573 = 417215) (by norm_num)
theorem B1112597 : Blo 738327 1112597 := bbase (se 6 (by rfl) ⟨26076, by rfl⟩ : syracuseStep 1112597 = 52153) (by norm_num)
theorem B1669661 : Blo 738327 1669661 := bbase (se 3 (by rfl) ⟨313061, by rfl⟩ : syracuseStep 1669661 = 626123) (by norm_num)
theorem B1112621 : Blo 738327 1112621 := bbase (se 3 (by rfl) ⟨208616, by rfl⟩ : syracuseStep 1112621 = 417233) (by norm_num)
theorem B1112645 : Blo 738327 1112645 := bbase (se 4 (by rfl) ⟨104310, by rfl⟩ : syracuseStep 1112645 = 208621) (by norm_num)
theorem B1112669 : Blo 738327 1112669 := bbase (se 3 (by rfl) ⟨208625, by rfl⟩ : syracuseStep 1112669 = 417251) (by norm_num)
theorem B1669733 : Blo 738327 1669733 := bbase (se 4 (by rfl) ⟨156537, by rfl⟩ : syracuseStep 1669733 = 313075) (by norm_num)
theorem B1112693 : Blo 738327 1112693 := bbase (se 5 (by rfl) ⟨52157, by rfl⟩ : syracuseStep 1112693 = 104315) (by norm_num)
theorem B1112717 : Blo 738327 1112717 := bbase (se 3 (by rfl) ⟨208634, by rfl⟩ : syracuseStep 1112717 = 417269) (by norm_num)
theorem B1112741 : Blo 738327 1112741 := bbase (se 4 (by rfl) ⟨104319, by rfl⟩ : syracuseStep 1112741 = 208639) (by norm_num)
theorem B1669805 : Blo 738327 1669805 := bbase (se 3 (by rfl) ⟨313088, by rfl⟩ : syracuseStep 1669805 = 626177) (by norm_num)
theorem B1899197 : Blo 738327 1899197 := bbase (se 3 (by rfl) ⟨356099, by rfl⟩ : syracuseStep 1899197 = 712199) (by norm_num)
theorem B1112765 : Blo 738327 1112765 := bbase (se 3 (by rfl) ⟨208643, by rfl⟩ : syracuseStep 1112765 = 417287) (by norm_num)
theorem B1112789 : Blo 738327 1112789 := bbase (se 7 (by rfl) ⟨13040, by rfl⟩ : syracuseStep 1112789 = 26081) (by norm_num)
theorem B1112813 : Blo 738327 1112813 := bbase (se 3 (by rfl) ⟨208652, by rfl⟩ : syracuseStep 1112813 = 417305) (by norm_num)
theorem B1669877 : Blo 738327 1669877 := bbase (se 5 (by rfl) ⟨78275, by rfl⟩ : syracuseStep 1669877 = 156551) (by norm_num)
theorem B1112837 : Blo 738327 1112837 := bbase (se 4 (by rfl) ⟨104328, by rfl⟩ : syracuseStep 1112837 = 208657) (by norm_num)
theorem B1112861 : Blo 738327 1112861 := bbase (se 3 (by rfl) ⟨208661, by rfl⟩ : syracuseStep 1112861 = 417323) (by norm_num)
theorem B1112885 : Blo 738327 1112885 := bbase (se 5 (by rfl) ⟨52166, by rfl⟩ : syracuseStep 1112885 = 104333) (by norm_num)
theorem B1669949 : Blo 738327 1669949 := bbase (se 3 (by rfl) ⟨313115, by rfl⟩ : syracuseStep 1669949 = 626231) (by norm_num)
theorem B1112909 : Blo 738327 1112909 := bbase (se 3 (by rfl) ⟨208670, by rfl⟩ : syracuseStep 1112909 = 417341) (by norm_num)
theorem B1604437 : Blo 738327 1604437 := bbase (se 9 (by rfl) ⟨4700, by rfl⟩ : syracuseStep 1604437 = 9401) (by norm_num)
theorem B4225877 : Blo 738327 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B1112933 : Blo 738327 1112933 := bbase (se 4 (by rfl) ⟨104337, by rfl⟩ : syracuseStep 1112933 = 208675) (by norm_num)
theorem B1112957 : Blo 738327 1112957 := bbase (se 3 (by rfl) ⟨208679, by rfl⟩ : syracuseStep 1112957 = 417359) (by norm_num)
theorem B1670021 : Blo 738327 1670021 := bbase (se 4 (by rfl) ⟨156564, by rfl⟩ : syracuseStep 1670021 = 313129) (by norm_num)
theorem B1112981 : Blo 738327 1112981 := bbase (se 6 (by rfl) ⟨26085, by rfl⟩ : syracuseStep 1112981 = 52171) (by norm_num)
theorem B3799973 : Blo 738327 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B1113005 : Blo 738327 1113005 := bbase (se 3 (by rfl) ⟨208688, by rfl⟩ : syracuseStep 1113005 = 417377) (by norm_num)
theorem B1113029 : Blo 738327 1113029 := bbase (se 4 (by rfl) ⟨104346, by rfl⟩ : syracuseStep 1113029 = 208693) (by norm_num)
theorem B1670093 : Blo 738327 1670093 := bbase (se 3 (by rfl) ⟨313142, by rfl⟩ : syracuseStep 1670093 = 626285) (by norm_num)
theorem B1113053 : Blo 738327 1113053 := bbase (se 3 (by rfl) ⟨208697, by rfl⟩ : syracuseStep 1113053 = 417395) (by norm_num)
theorem B1113077 : Blo 738327 1113077 := bbase (se 5 (by rfl) ⟨52175, by rfl⟩ : syracuseStep 1113077 = 104351) (by norm_num)
theorem B1113101 : Blo 738327 1113101 := bbase (se 3 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 1113101 = 417413) (by norm_num)
theorem B1670165 : Blo 738327 1670165 := bbase (se 6 (by rfl) ⟨39144, by rfl⟩ : syracuseStep 1670165 = 78289) (by norm_num)
theorem B1113125 : Blo 738327 1113125 := bbase (se 4 (by rfl) ⟨104355, by rfl⟩ : syracuseStep 1113125 = 208711) (by norm_num)
theorem B1113149 : Blo 738327 1113149 := bbase (se 3 (by rfl) ⟨208715, by rfl⟩ : syracuseStep 1113149 = 417431) (by norm_num)
theorem B1113173 : Blo 738327 1113173 := bbase (se 8 (by rfl) ⟨6522, by rfl⟩ : syracuseStep 1113173 = 13045) (by norm_num)
theorem B1670237 : Blo 738327 1670237 := bbase (se 3 (by rfl) ⟨313169, by rfl⟩ : syracuseStep 1670237 = 626339) (by norm_num)
theorem B1113197 : Blo 738327 1113197 := bbase (se 3 (by rfl) ⟨208724, by rfl⟩ : syracuseStep 1113197 = 417449) (by norm_num)
theorem B1408117 : Blo 738327 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B1113221 : Blo 738327 1113221 := bbase (se 4 (by rfl) ⟨104364, by rfl⟩ : syracuseStep 1113221 = 208729) (by norm_num)
theorem B1113245 : Blo 738327 1113245 := bbase (se 3 (by rfl) ⟨208733, by rfl⟩ : syracuseStep 1113245 = 417467) (by norm_num)
theorem B1113269 : Blo 738327 1113269 := bbase (se 5 (by rfl) ⟨52184, by rfl⟩ : syracuseStep 1113269 = 104369) (by norm_num)
theorem B1113293 : Blo 738327 1113293 := bbase (se 3 (by rfl) ⟨208742, by rfl⟩ : syracuseStep 1113293 = 417485) (by norm_num)
theorem B1998053 : Blo 738327 1998053 := bbase (se 4 (by rfl) ⟨187317, by rfl⟩ : syracuseStep 1998053 = 374635) (by norm_num)
theorem B1113317 : Blo 738327 1113317 := bbase (se 4 (by rfl) ⟨104373, by rfl⟩ : syracuseStep 1113317 = 208747) (by norm_num)
theorem B1113341 : Blo 738327 1113341 := bbase (se 3 (by rfl) ⟨208751, by rfl⟩ : syracuseStep 1113341 = 417503) (by norm_num)
theorem B1408261 : Blo 738327 1408261 := bbase (se 4 (by rfl) ⟨132024, by rfl⟩ : syracuseStep 1408261 = 264049) (by norm_num)
theorem B1113365 : Blo 738327 1113365 := bbase (se 6 (by rfl) ⟨26094, by rfl⟩ : syracuseStep 1113365 = 52189) (by norm_num)
theorem B1113389 : Blo 738327 1113389 := bbase (se 3 (by rfl) ⟨208760, by rfl⟩ : syracuseStep 1113389 = 417521) (by norm_num)
theorem B1113413 : Blo 738327 1113413 := bbase (se 4 (by rfl) ⟨104382, by rfl⟩ : syracuseStep 1113413 = 208765) (by norm_num)
theorem B1113437 : Blo 738327 1113437 := bbase (se 3 (by rfl) ⟨208769, by rfl⟩ : syracuseStep 1113437 = 417539) (by norm_num)
theorem B1113461 : Blo 738327 1113461 := bbase (se 5 (by rfl) ⟨52193, by rfl⟩ : syracuseStep 1113461 = 104387) (by norm_num)
theorem B1113485 : Blo 738327 1113485 := bbase (se 3 (by rfl) ⟨208778, by rfl⟩ : syracuseStep 1113485 = 417557) (by norm_num)
theorem B1408421 : Blo 738327 1408421 := bbase (se 4 (by rfl) ⟨132039, by rfl⟩ : syracuseStep 1408421 = 264079) (by norm_num)
theorem B2883077 : Blo 738327 2883077 := bbase (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) (by norm_num)
theorem B1408565 : Blo 738327 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B3211093 : Blo 738327 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B1408853 : Blo 738327 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B1409005 : Blo 738327 1409005 := bbase (se 3 (by rfl) ⟨264188, by rfl⟩ : syracuseStep 1409005 = 528377) (by norm_num)
theorem B2818253 : Blo 738327 2818253 := bstep (se 3 (by rfl) ⟨528422, by rfl⟩ : syracuseStep 2818253 = 1056845) B1056845
theorem B1409233 : Blo 738327 1409233 := bstep (se 2 (by rfl) ⟨528462, by rfl⟩ : syracuseStep 1409233 = 1056925) B1056925
theorem B4227653 : Blo 738327 4227653 := bstep (se 4 (by rfl) ⟨396342, by rfl⟩ : syracuseStep 4227653 = 792685) B792685
theorem B3375857 : Blo 738327 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B1245955 : Blo 738327 1245955 := bstep (se 1 (by rfl) ⟨934466, by rfl⟩ : syracuseStep 1245955 = 1868933) B1868933
theorem B1999651 : Blo 738327 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B3212131 : Blo 738327 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B4752269 : Blo 738327 4752269 := bstep (se 3 (by rfl) ⟨891050, by rfl⟩ : syracuseStep 4752269 = 1782101) B1782101
theorem B1246097 : Blo 738327 1246097 := bstep (se 2 (by rfl) ⟨467286, by rfl⟩ : syracuseStep 1246097 = 934573) B934573
theorem B2163665 : Blo 738327 2163665 := bstep (se 2 (by rfl) ⟨811374, by rfl⟩ : syracuseStep 2163665 = 1622749) B1622749
theorem B1246225 : Blo 738327 1246225 := bstep (se 2 (by rfl) ⟨467334, by rfl⟩ : syracuseStep 1246225 = 934669) B934669
theorem B1246259 : Blo 738327 1246259 := bstep (se 1 (by rfl) ⟨934694, by rfl⟩ : syracuseStep 1246259 = 1869389) B1869389
theorem B3376205 : Blo 738327 3376205 := bstep (se 3 (by rfl) ⟨633038, by rfl⟩ : syracuseStep 3376205 = 1266077) B1266077
theorem B1246387 : Blo 738327 1246387 := bstep (se 1 (by rfl) ⟨934790, by rfl⟩ : syracuseStep 1246387 = 1869581) B1869581
theorem B1246529 : Blo 738327 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B1246657 : Blo 738327 1246657 := bstep (se 2 (by rfl) ⟨467496, by rfl⟩ : syracuseStep 1246657 = 934993) B934993
theorem B1246691 : Blo 738327 1246691 := bstep (se 1 (by rfl) ⟨935018, by rfl⟩ : syracuseStep 1246691 = 1870037) B1870037
theorem B1246819 : Blo 738327 1246819 := bstep (se 1 (by rfl) ⟨935114, by rfl⟩ : syracuseStep 1246819 = 1870229) B1870229
theorem B2492045 : Blo 738327 2492045 := bstep (se 3 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 2492045 = 934517) B934517
theorem B2492099 : Blo 738327 2492099 := bstep (se 1 (by rfl) ⟨1869074, by rfl⟩ : syracuseStep 2492099 = 3738149) B3738149
theorem B1246961 : Blo 738327 1246961 := bstep (se 2 (by rfl) ⟨467610, by rfl⟩ : syracuseStep 1246961 = 935221) B935221
theorem B1083137 : Blo 738327 1083137 := bstep (se 2 (by rfl) ⟨406176, by rfl⟩ : syracuseStep 1083137 = 812353) B812353
theorem B1247089 : Blo 738327 1247089 := bstep (se 2 (by rfl) ⟨467658, by rfl⟩ : syracuseStep 1247089 = 935317) B935317
theorem B1869713 : Blo 738327 1869713 := bstep (se 2 (by rfl) ⟨701142, by rfl⟩ : syracuseStep 1869713 = 1402285) B1402285
theorem B1247123 : Blo 738327 1247123 := bstep (se 1 (by rfl) ⟨935342, by rfl⟩ : syracuseStep 1247123 = 1870685) B1870685
theorem B1869763 : Blo 738327 1869763 := bstep (se 1 (by rfl) ⟨1402322, by rfl⟩ : syracuseStep 1869763 = 2804645) B2804645
theorem B2492369 : Blo 738327 2492369 := bstep (se 2 (by rfl) ⟨934638, by rfl⟩ : syracuseStep 2492369 = 1869277) B1869277
theorem B7112717 : Blo 738327 7112717 := bstep (se 3 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 7112717 = 2667269) B2667269
theorem B5343245 : Blo 738327 5343245 := bstep (se 3 (by rfl) ⟨1001858, by rfl⟩ : syracuseStep 5343245 = 2003717) B2003717
theorem B1247251 : Blo 738327 1247251 := bstep (se 1 (by rfl) ⟨935438, by rfl⟩ : syracuseStep 1247251 = 1870877) B1870877
theorem B1869905 : Blo 738327 1869905 := bstep (se 2 (by rfl) ⟨701214, by rfl⟩ : syracuseStep 1869905 = 1402429) B1402429
theorem B1247393 : Blo 738327 1247393 := bstep (se 2 (by rfl) ⟨467772, by rfl⟩ : syracuseStep 1247393 = 935545) B935545
theorem B1247521 : Blo 738327 1247521 := bstep (se 2 (by rfl) ⟨467820, by rfl⟩ : syracuseStep 1247521 = 935641) B935641
theorem B1247555 : Blo 738327 1247555 := bstep (se 1 (by rfl) ⟨935666, by rfl⟩ : syracuseStep 1247555 = 1871333) B1871333
theorem B1247683 : Blo 738327 1247683 := bstep (se 1 (by rfl) ⟨935762, by rfl⟩ : syracuseStep 1247683 = 1871525) B1871525
theorem B5409251 : Blo 738327 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B2492909 : Blo 738327 2492909 := bstep (se 3 (by rfl) ⟨467420, by rfl⟩ : syracuseStep 2492909 = 934841) B934841
theorem B2492963 : Blo 738327 2492963 := bstep (se 1 (by rfl) ⟨1869722, by rfl⟩ : syracuseStep 2492963 = 3739445) B3739445
theorem B789059 : Blo 738327 789059 := bstep (se 1 (by rfl) ⟨591794, by rfl⟩ : syracuseStep 789059 = 1183589) B1183589
theorem B1247825 : Blo 738327 1247825 := bstep (se 2 (by rfl) ⟨467934, by rfl⟩ : syracuseStep 1247825 = 935869) B935869
theorem B1247953 : Blo 738327 1247953 := bstep (se 2 (by rfl) ⟨467982, by rfl⟩ : syracuseStep 1247953 = 935965) B935965
theorem B5999345 : Blo 738327 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B1247987 : Blo 738327 1247987 := bstep (se 1 (by rfl) ⟨935990, by rfl⟩ : syracuseStep 1247987 = 1871981) B1871981
theorem B2493233 : Blo 738327 2493233 := bstep (se 2 (by rfl) ⟨934962, by rfl⟩ : syracuseStep 2493233 = 1869925) B1869925
theorem B2001773 : Blo 738327 2001773 := bstep (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) B750665
theorem B1444721 : Blo 738327 1444721 := bstep (se 2 (by rfl) ⟨541770, by rfl⟩ : syracuseStep 1444721 = 1083541) B1083541
theorem B1248115 : Blo 738327 1248115 := bstep (se 1 (by rfl) ⟨936086, by rfl⟩ : syracuseStep 1248115 = 1872173) B1872173
theorem B1051537 : Blo 738327 1051537 := bstep (se 2 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 1051537 = 788653) B788653
theorem B1903601 : Blo 738327 1903601 := bstep (se 2 (by rfl) ⟨713850, by rfl⟩ : syracuseStep 1903601 = 1427701) B1427701
theorem B1248257 : Blo 738327 1248257 := bstep (se 2 (by rfl) ⟨468096, by rfl⟩ : syracuseStep 1248257 = 936193) B936193
theorem B1051651 : Blo 738327 1051651 := bstep (se 1 (by rfl) ⟨788738, by rfl⟩ : syracuseStep 1051651 = 1577477) B1577477
theorem B1182737 : Blo 738327 1182737 := bstep (se 2 (by rfl) ⟨443526, by rfl⟩ : syracuseStep 1182737 = 887053) B887053
theorem B1870897 : Blo 738327 1870897 := bstep (se 2 (by rfl) ⟨701586, by rfl⟩ : syracuseStep 1870897 = 1403173) B1403173
theorem B1248385 : Blo 738327 1248385 := bstep (se 2 (by rfl) ⟨468144, by rfl⟩ : syracuseStep 1248385 = 936289) B936289
theorem B1281187 : Blo 738327 1281187 := bstep (se 1 (by rfl) ⟨960890, by rfl⟩ : syracuseStep 1281187 = 1921781) B1921781
theorem B1248419 : Blo 738327 1248419 := bstep (se 1 (by rfl) ⟨936314, by rfl⟩ : syracuseStep 1248419 = 1872629) B1872629
theorem B2002097 : Blo 738327 2002097 := bstep (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) B1501573
theorem B1248547 : Blo 738327 1248547 := bstep (se 1 (by rfl) ⟨936410, by rfl⟩ : syracuseStep 1248547 = 1872821) B1872821
theorem B1183025 : Blo 738327 1183025 := bstep (se 2 (by rfl) ⟨443634, by rfl⟩ : syracuseStep 1183025 = 887269) B887269
theorem B1871171 : Blo 738327 1871171 := bstep (se 1 (by rfl) ⟨1403378, by rfl⟩ : syracuseStep 1871171 = 2806757) B2806757
theorem B2493773 : Blo 738327 2493773 := bstep (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) B935165
theorem B2493827 : Blo 738327 2493827 := bstep (se 1 (by rfl) ⟨1870370, by rfl⟩ : syracuseStep 2493827 = 3740741) B3740741
theorem B1248689 : Blo 738327 1248689 := bstep (se 2 (by rfl) ⟨468258, by rfl⟩ : syracuseStep 1248689 = 936517) B936517
theorem B7212485 : Blo 738327 7212485 := bstep (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) B1352341
theorem B3739121 : Blo 738327 3739121 := bstep (se 2 (by rfl) ⟨1402170, by rfl⟩ : syracuseStep 3739121 = 2804341) B2804341
theorem B790003 : Blo 738327 790003 := bstep (se 1 (by rfl) ⟨592502, by rfl⟩ : syracuseStep 790003 = 1185005) B1185005
theorem B1871363 : Blo 738327 1871363 := bstep (se 1 (by rfl) ⟨1403522, by rfl⟩ : syracuseStep 1871363 = 2807045) B2807045
theorem B1248817 : Blo 738327 1248817 := bstep (se 2 (by rfl) ⟨468306, by rfl⟩ : syracuseStep 1248817 = 936613) B936613
theorem B5606981 : Blo 738327 5606981 := bstep (se 4 (by rfl) ⟨525654, by rfl⟩ : syracuseStep 5606981 = 1051309) B1051309
theorem B1248851 : Blo 738327 1248851 := bstep (se 1 (by rfl) ⟨936638, by rfl⟩ : syracuseStep 1248851 = 1873277) B1873277
theorem B13471373 : Blo 738327 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B2494097 : Blo 738327 2494097 := bstep (se 2 (by rfl) ⟨935286, by rfl⟩ : syracuseStep 2494097 = 1870573) B1870573
theorem B888499 : Blo 738327 888499 := bstep (se 1 (by rfl) ⟨666374, by rfl⟩ : syracuseStep 888499 = 1332749) B1332749
theorem B1248979 : Blo 738327 1248979 := bstep (se 1 (by rfl) ⟨936734, by rfl⟩ : syracuseStep 1248979 = 1873469) B1873469
theorem B1904369 : Blo 738327 1904369 := bstep (se 2 (by rfl) ⟨714138, by rfl⟩ : syracuseStep 1904369 = 1428277) B1428277
theorem B1249121 : Blo 738327 1249121 := bstep (se 2 (by rfl) ⟨468420, by rfl⟩ : syracuseStep 1249121 = 936841) B936841
theorem B1249249 : Blo 738327 1249249 := bstep (se 2 (by rfl) ⟨468468, by rfl⟩ : syracuseStep 1249249 = 936937) B936937
theorem B1249283 : Blo 738327 1249283 := bstep (se 1 (by rfl) ⟨936962, by rfl⟩ : syracuseStep 1249283 = 1873925) B1873925
theorem B6754373 : Blo 738327 6754373 := bstep (se 4 (by rfl) ⟨633222, by rfl⟩ : syracuseStep 6754373 = 1266445) B1266445
theorem B1183825 : Blo 738327 1183825 := bstep (se 2 (by rfl) ⟨443934, by rfl⟩ : syracuseStep 1183825 = 887869) B887869
theorem B1249411 : Blo 738327 1249411 := bstep (se 1 (by rfl) ⟨937058, by rfl⟩ : syracuseStep 1249411 = 1874117) B1874117
theorem B2494637 : Blo 738327 2494637 := bstep (se 3 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 2494637 = 935489) B935489
theorem B2494691 : Blo 738327 2494691 := bstep (se 1 (by rfl) ⟨1871018, by rfl⟩ : syracuseStep 2494691 = 3742037) B3742037
theorem B1249553 : Blo 738327 1249553 := bstep (se 2 (by rfl) ⟨468582, by rfl⟩ : syracuseStep 1249553 = 937165) B937165
theorem B8425781 : Blo 738327 8425781 := bstep (se 5 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 8425781 = 789917) B789917
theorem B1052995 : Blo 738327 1052995 := bstep (se 1 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 1052995 = 1579493) B1579493
theorem B1249681 : Blo 738327 1249681 := bstep (se 2 (by rfl) ⟨468630, by rfl⟩ : syracuseStep 1249681 = 937261) B937261
theorem B1872305 : Blo 738327 1872305 := bstep (se 2 (by rfl) ⟨702114, by rfl⟩ : syracuseStep 1872305 = 1404229) B1404229
theorem B1249715 : Blo 738327 1249715 := bstep (se 1 (by rfl) ⟨937286, by rfl⟩ : syracuseStep 1249715 = 1874573) B1874573
theorem B8556997 : Blo 738327 8556997 := bstep (se 4 (by rfl) ⟨802218, by rfl⟩ : syracuseStep 8556997 = 1604437) B1604437
theorem B1085905 : Blo 738327 1085905 := bstep (se 2 (by rfl) ⟨407214, by rfl⟩ : syracuseStep 1085905 = 814429) B814429
theorem B1872355 : Blo 738327 1872355 := bstep (se 1 (by rfl) ⟨1404266, by rfl⟩ : syracuseStep 1872355 = 2808533) B2808533
theorem B2494961 : Blo 738327 2494961 := bstep (se 2 (by rfl) ⟨935610, by rfl⟩ : syracuseStep 2494961 = 1871221) B1871221
theorem B1249843 : Blo 738327 1249843 := bstep (se 1 (by rfl) ⟨937382, by rfl⟩ : syracuseStep 1249843 = 1874765) B1874765
theorem B9015907 : Blo 738327 9015907 := bstep (se 1 (by rfl) ⟨6761930, by rfl⟩ : syracuseStep 9015907 = 13523861) B13523861
theorem B1872497 : Blo 738327 1872497 := bstep (se 2 (by rfl) ⟨702186, by rfl⟩ : syracuseStep 1872497 = 1404373) B1404373
theorem B12030605 : Blo 738327 12030605 := bstep (se 3 (by rfl) ⟨2255738, by rfl⟩ : syracuseStep 12030605 = 4511477) B4511477
theorem B1249985 : Blo 738327 1249985 := bstep (se 2 (by rfl) ⟨468744, by rfl⟩ : syracuseStep 1249985 = 937489) B937489
theorem B4264645 : Blo 738327 4264645 := bstep (se 4 (by rfl) ⟨399810, by rfl⟩ : syracuseStep 4264645 = 799621) B799621
theorem B1774307 : Blo 738327 1774307 := bstep (se 1 (by rfl) ⟨1330730, by rfl⟩ : syracuseStep 1774307 = 2661461) B2661461
theorem B791267 : Blo 738327 791267 := bstep (se 1 (by rfl) ⟨593450, by rfl⟩ : syracuseStep 791267 = 1186901) B1186901
theorem B1250113 : Blo 738327 1250113 := bstep (se 2 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 1250113 = 937585) B937585
theorem B1250147 : Blo 738327 1250147 := bstep (se 1 (by rfl) ⟨937610, by rfl⟩ : syracuseStep 1250147 = 1875221) B1875221
theorem B3740579 : Blo 738327 3740579 := bstep (se 1 (by rfl) ⟨2805434, by rfl⟩ : syracuseStep 3740579 = 5610869) B5610869
theorem B1250275 : Blo 738327 1250275 := bstep (se 1 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 1250275 = 1875413) B1875413
theorem B2495501 : Blo 738327 2495501 := bstep (se 3 (by rfl) ⟨467906, by rfl⟩ : syracuseStep 2495501 = 935813) B935813
theorem B2495555 : Blo 738327 2495555 := bstep (se 1 (by rfl) ⟨1871666, by rfl⟩ : syracuseStep 2495555 = 3743333) B3743333
theorem B1250417 : Blo 738327 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B2004173 : Blo 738327 2004173 := bstep (se 3 (by rfl) ⟨375782, by rfl⟩ : syracuseStep 2004173 = 751565) B751565
theorem B1250545 : Blo 738327 1250545 := bstep (se 2 (by rfl) ⟨468954, by rfl⟩ : syracuseStep 1250545 = 937909) B937909
theorem B2004227 : Blo 738327 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B1185043 : Blo 738327 1185043 := bstep (se 1 (by rfl) ⟨888782, by rfl⟩ : syracuseStep 1185043 = 1777565) B1777565
theorem B1250579 : Blo 738327 1250579 := bstep (se 1 (by rfl) ⟨937934, by rfl⟩ : syracuseStep 1250579 = 1875869) B1875869
theorem B2102573 : Blo 738327 2102573 := bstep (se 3 (by rfl) ⟨394232, by rfl⟩ : syracuseStep 2102573 = 788465) B788465
theorem B2495825 : Blo 738327 2495825 := bstep (se 2 (by rfl) ⟨935934, by rfl⟩ : syracuseStep 2495825 = 1871869) B1871869
theorem B1250707 : Blo 738327 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B1054129 : Blo 738327 1054129 := bstep (se 2 (by rfl) ⟨395298, by rfl⟩ : syracuseStep 1054129 = 790597) B790597
theorem B792019 : Blo 738327 792019 := bstep (se 1 (by rfl) ⟨594014, by rfl⟩ : syracuseStep 792019 = 1188029) B1188029
theorem B2102755 : Blo 738327 2102755 := bstep (se 1 (by rfl) ⟨1577066, by rfl⟩ : syracuseStep 2102755 = 3154133) B3154133
theorem B1054225 : Blo 738327 1054225 := bstep (se 2 (by rfl) ⟨395334, by rfl⟩ : syracuseStep 1054225 = 790669) B790669
theorem B2004497 : Blo 738327 2004497 := bstep (se 2 (by rfl) ⟨751686, by rfl⟩ : syracuseStep 2004497 = 1503373) B1503373
theorem B1250849 : Blo 738327 1250849 := bstep (se 2 (by rfl) ⟨469068, by rfl⟩ : syracuseStep 1250849 = 938137) B938137
theorem B1873489 : Blo 738327 1873489 := bstep (se 2 (by rfl) ⟨702558, by rfl⟩ : syracuseStep 1873489 = 1405117) B1405117
theorem B2102915 : Blo 738327 2102915 := bstep (se 1 (by rfl) ⟨1577186, by rfl⟩ : syracuseStep 2102915 = 3154373) B3154373
theorem B2004625 : Blo 738327 2004625 := bstep (se 2 (by rfl) ⟨751734, by rfl⟩ : syracuseStep 2004625 = 1503469) B1503469
theorem B1250977 : Blo 738327 1250977 := bstep (se 2 (by rfl) ⟨469116, by rfl⟩ : syracuseStep 1250977 = 938233) B938233
theorem B1251011 : Blo 738327 1251011 := bstep (se 1 (by rfl) ⟨938258, by rfl⟩ : syracuseStep 1251011 = 1876517) B1876517
theorem B3741389 : Blo 738327 3741389 := bstep (se 3 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 3741389 = 1403021) B1403021
theorem B890579 : Blo 738327 890579 := bstep (se 1 (by rfl) ⟨667934, by rfl⟩ : syracuseStep 890579 = 1335869) B1335869
theorem B792275 : Blo 738327 792275 := bstep (se 1 (by rfl) ⟨594206, by rfl⟩ : syracuseStep 792275 = 1188413) B1188413
theorem B1251139 : Blo 738327 1251139 := bstep (se 1 (by rfl) ⟨938354, by rfl⟩ : syracuseStep 1251139 = 1876709) B1876709
theorem B1873763 : Blo 738327 1873763 := bstep (se 1 (by rfl) ⟨1405322, by rfl⟩ : syracuseStep 1873763 = 2810645) B2810645
theorem B2496365 : Blo 738327 2496365 := bstep (se 3 (by rfl) ⟨468068, by rfl⟩ : syracuseStep 2496365 = 936137) B936137
theorem B2496419 : Blo 738327 2496419 := bstep (se 1 (by rfl) ⟨1872314, by rfl⟩ : syracuseStep 2496419 = 3744629) B3744629
theorem B1775537 : Blo 738327 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B1251281 : Blo 738327 1251281 := bstep (se 2 (by rfl) ⟨469230, by rfl⟩ : syracuseStep 1251281 = 938461) B938461
theorem B1185761 : Blo 738327 1185761 := bstep (se 2 (by rfl) ⟨444660, by rfl⟩ : syracuseStep 1185761 = 889321) B889321
theorem B1054721 : Blo 738327 1054721 := bstep (se 2 (by rfl) ⟨395520, by rfl⟩ : syracuseStep 1054721 = 791041) B791041
theorem B1873955 : Blo 738327 1873955 := bstep (se 1 (by rfl) ⟨1405466, by rfl⟩ : syracuseStep 1873955 = 2810933) B2810933
theorem B5347397 : Blo 738327 5347397 := bstep (se 4 (by rfl) ⟨501318, by rfl⟩ : syracuseStep 5347397 = 1002637) B1002637
theorem B1251409 : Blo 738327 1251409 := bstep (se 2 (by rfl) ⟨469278, by rfl⟩ : syracuseStep 1251409 = 938557) B938557
theorem B1251443 : Blo 738327 1251443 := bstep (se 1 (by rfl) ⟨938582, by rfl⟩ : syracuseStep 1251443 = 1877165) B1877165
theorem B2496689 : Blo 738327 2496689 := bstep (se 2 (by rfl) ⟨936258, by rfl⟩ : syracuseStep 2496689 = 1872517) B1872517
theorem B1251571 : Blo 738327 1251571 := bstep (se 1 (by rfl) ⟨938678, by rfl⟩ : syracuseStep 1251571 = 1877357) B1877357
theorem B1186049 : Blo 738327 1186049 := bstep (se 2 (by rfl) ⟨444768, by rfl⟩ : syracuseStep 1186049 = 889537) B889537
theorem B1251713 : Blo 738327 1251713 := bstep (se 2 (by rfl) ⟨469392, by rfl⟩ : syracuseStep 1251713 = 938785) B938785
theorem B1579459 : Blo 738327 1579459 := bstep (se 1 (by rfl) ⟨1184594, by rfl⟩ : syracuseStep 1579459 = 2369189) B2369189
theorem B1186273 : Blo 738327 1186273 := bstep (se 2 (by rfl) ⟨444852, by rfl⟩ : syracuseStep 1186273 = 889705) B889705
theorem B1251841 : Blo 738327 1251841 := bstep (se 2 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 1251841 = 938881) B938881
theorem B7608845 : Blo 738327 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B1251875 : Blo 738327 1251875 := bstep (se 1 (by rfl) ⟨938906, by rfl⟩ : syracuseStep 1251875 = 1877813) B1877813
theorem B1219169 : Blo 738327 1219169 := bstep (se 2 (by rfl) ⟨457188, by rfl⟩ : syracuseStep 1219169 = 914377) B914377
theorem B1252003 : Blo 738327 1252003 := bstep (se 1 (by rfl) ⟨939002, by rfl⟩ : syracuseStep 1252003 = 1878005) B1878005
theorem B2103985 : Blo 738327 2103985 := bstep (se 2 (by rfl) ⟨788994, by rfl⟩ : syracuseStep 2103985 = 1577989) B1577989
theorem B2497229 : Blo 738327 2497229 := bstep (se 3 (by rfl) ⟨468230, by rfl⟩ : syracuseStep 2497229 = 936461) B936461
theorem B2497283 : Blo 738327 2497283 := bstep (se 1 (by rfl) ⟨1872962, by rfl⟩ : syracuseStep 2497283 = 3745925) B3745925
theorem B2530097 : Blo 738327 2530097 := bstep (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) B1897573
theorem B1252145 : Blo 738327 1252145 := bstep (se 2 (by rfl) ⟨469554, by rfl⟩ : syracuseStep 1252145 = 939109) B939109
theorem B1055587 : Blo 738327 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B1252273 : Blo 738327 1252273 := bstep (se 2 (by rfl) ⟨469602, by rfl⟩ : syracuseStep 1252273 = 939205) B939205
theorem B1055683 : Blo 738327 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B1874897 : Blo 738327 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B1252307 : Blo 738327 1252307 := bstep (se 1 (by rfl) ⟨939230, by rfl⟩ : syracuseStep 1252307 = 1878461) B1878461
theorem B1874947 : Blo 738327 1874947 := bstep (se 1 (by rfl) ⟨1406210, by rfl⟩ : syracuseStep 1874947 = 2812421) B2812421
theorem B2497553 : Blo 738327 2497553 := bstep (se 2 (by rfl) ⟨936582, by rfl⟩ : syracuseStep 2497553 = 1873165) B1873165
theorem B1252435 : Blo 738327 1252435 := bstep (se 1 (by rfl) ⟨939326, by rfl⟩ : syracuseStep 1252435 = 1878653) B1878653
theorem B2006129 : Blo 738327 2006129 := bstep (se 2 (by rfl) ⟨752298, by rfl⟩ : syracuseStep 2006129 = 1504597) B1504597
theorem B1875089 : Blo 738327 1875089 := bstep (se 2 (by rfl) ⟨703158, by rfl⟩ : syracuseStep 1875089 = 1406317) B1406317
theorem B1252577 : Blo 738327 1252577 := bstep (se 2 (by rfl) ⟨469716, by rfl⟩ : syracuseStep 1252577 = 939433) B939433
theorem B1580305 : Blo 738327 1580305 := bstep (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) B1185229
theorem B1056179 : Blo 738327 1056179 := bstep (se 1 (by rfl) ⟨792134, by rfl⟩ : syracuseStep 1056179 = 1584269) B1584269
theorem B2498093 : Blo 738327 2498093 := bstep (se 3 (by rfl) ⟨468392, by rfl⟩ : syracuseStep 2498093 = 936785) B936785
theorem B4005445 : Blo 738327 4005445 := bstep (se 4 (by rfl) ⟨375510, by rfl⟩ : syracuseStep 4005445 = 751021) B751021
theorem B2498147 : Blo 738327 2498147 := bstep (se 1 (by rfl) ⟨1873610, by rfl⟩ : syracuseStep 2498147 = 3747221) B3747221
theorem B10133261 : Blo 738327 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B2498417 : Blo 738327 2498417 := bstep (se 2 (by rfl) ⟨936906, by rfl⟩ : syracuseStep 2498417 = 1873813) B1873813
theorem B36052877 : Blo 738327 36052877 := bstep (se 3 (by rfl) ⟨6759914, by rfl⟩ : syracuseStep 36052877 = 13519829) B13519829
theorem B2105261 : Blo 738327 2105261 := bstep (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) B789473
theorem B1187875 : Blo 738327 1187875 := bstep (se 1 (by rfl) ⟨890906, by rfl⟩ : syracuseStep 1187875 = 1781813) B1781813
theorem B1056817 : Blo 738327 1056817 := bstep (se 2 (by rfl) ⟨396306, by rfl⟩ : syracuseStep 1056817 = 792613) B792613
theorem B2105443 : Blo 738327 2105443 := bstep (se 1 (by rfl) ⟨1579082, by rfl⟩ : syracuseStep 2105443 = 3158165) B3158165
theorem B1876081 : Blo 738327 1876081 := bstep (se 2 (by rfl) ⟨703530, by rfl⟩ : syracuseStep 1876081 = 1407061) B1407061
theorem B2105489 : Blo 738327 2105489 := bstep (se 2 (by rfl) ⟨789558, by rfl⟩ : syracuseStep 2105489 = 1579117) B1579117
theorem B2662627 : Blo 738327 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B1777891 : Blo 738327 1777891 := bstep (se 1 (by rfl) ⟨1333418, by rfl⟩ : syracuseStep 1777891 = 2666837) B2666837
theorem B1876355 : Blo 738327 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B2498957 : Blo 738327 2498957 := bstep (se 3 (by rfl) ⟨468554, by rfl⟩ : syracuseStep 2498957 = 937109) B937109
theorem B1122707 : Blo 738327 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B2499011 : Blo 738327 2499011 := bstep (se 1 (by rfl) ⟨1874258, by rfl⟩ : syracuseStep 2499011 = 3748517) B3748517
theorem B2466289 : Blo 738327 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B1352227 : Blo 738327 1352227 := bstep (se 1 (by rfl) ⟨1014170, by rfl⟩ : syracuseStep 1352227 = 2028341) B2028341
theorem B3744305 : Blo 738327 3744305 := bstep (se 2 (by rfl) ⟨1404114, by rfl⟩ : syracuseStep 3744305 = 2808229) B2808229
theorem B1876547 : Blo 738327 1876547 := bstep (se 1 (by rfl) ⟨1407410, by rfl⟩ : syracuseStep 1876547 = 2814821) B2814821
theorem B2499281 : Blo 738327 2499281 := bstep (se 2 (by rfl) ⟨937230, by rfl⟩ : syracuseStep 2499281 = 1874461) B1874461
theorem B2368241 : Blo 738327 2368241 := bstep (se 2 (by rfl) ⟨888090, by rfl⟩ : syracuseStep 2368241 = 1776181) B1776181
theorem B3155021 : Blo 738327 3155021 := bstep (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) B1183133
theorem B3155057 : Blo 738327 3155057 := bstep (se 2 (by rfl) ⟨1183146, by rfl⟩ : syracuseStep 3155057 = 2366293) B2366293
theorem B1582193 : Blo 738327 1582193 := bstep (se 2 (by rfl) ⟨593322, by rfl⟩ : syracuseStep 1582193 = 1186645) B1186645
theorem B2499821 : Blo 738327 2499821 := bstep (se 3 (by rfl) ⟨468716, by rfl⟩ : syracuseStep 2499821 = 937433) B937433
theorem B3417329 : Blo 738327 3417329 := bstep (se 2 (by rfl) ⟨1281498, by rfl⟩ : syracuseStep 3417329 = 2562997) B2562997
theorem B5612813 : Blo 738327 5612813 := bstep (se 3 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 5612813 = 2104805) B2104805
theorem B2499875 : Blo 738327 2499875 := bstep (se 1 (by rfl) ⟨1874906, by rfl⟩ : syracuseStep 2499875 = 3749813) B3749813
theorem B2368931 : Blo 738327 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B1779121 : Blo 738327 1779121 := bstep (se 2 (by rfl) ⟨667170, by rfl⟩ : syracuseStep 1779121 = 1334341) B1334341
theorem B7120325 : Blo 738327 7120325 := bstep (se 4 (by rfl) ⟨667530, by rfl⟩ : syracuseStep 7120325 = 1335061) B1335061
theorem B1877489 : Blo 738327 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B1877539 : Blo 738327 1877539 := bstep (se 1 (by rfl) ⟨1408154, by rfl⟩ : syracuseStep 1877539 = 2816309) B2816309
theorem B2500145 : Blo 738327 2500145 := bstep (se 2 (by rfl) ⟨937554, by rfl⟩ : syracuseStep 2500145 = 1875109) B1875109
theorem B2106947 : Blo 738327 2106947 := bstep (se 1 (by rfl) ⟨1580210, by rfl⟩ : syracuseStep 2106947 = 3160421) B3160421
theorem B1779313 : Blo 738327 1779313 := bstep (se 2 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 1779313 = 1334485) B1334485
theorem B1877681 : Blo 738327 1877681 := bstep (se 2 (by rfl) ⟨704130, by rfl⟩ : syracuseStep 1877681 = 1408261) B1408261
theorem B32057045 : Blo 738327 32057045 := bstep (se 7 (by rfl) ⟨375668, by rfl⟩ : syracuseStep 32057045 = 751337) B751337
theorem B3549091 : Blo 738327 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B3745763 : Blo 738327 3745763 := bstep (se 1 (by rfl) ⟨2809322, by rfl⟩ : syracuseStep 3745763 = 5618645) B5618645
theorem B2500685 : Blo 738327 2500685 := bstep (se 3 (by rfl) ⟨468878, by rfl⟩ : syracuseStep 2500685 = 937757) B937757
theorem B2500739 : Blo 738327 2500739 := bstep (se 1 (by rfl) ⟨1875554, by rfl⟩ : syracuseStep 2500739 = 3751109) B3751109
theorem B1124513 : Blo 738327 1124513 := bstep (se 2 (by rfl) ⟨421692, by rfl⟩ : syracuseStep 1124513 = 843385) B843385
theorem B1583491 : Blo 738327 1583491 := bstep (se 1 (by rfl) ⟨1187618, by rfl⟩ : syracuseStep 1583491 = 2375237) B2375237
theorem B2501009 : Blo 738327 2501009 := bstep (se 2 (by rfl) ⟨937878, by rfl⟩ : syracuseStep 2501009 = 1875757) B1875757
theorem B1878673 : Blo 738327 1878673 := bstep (se 2 (by rfl) ⟨704502, by rfl⟩ : syracuseStep 1878673 = 1409005) B1409005
theorem B3746573 : Blo 738327 3746573 := bstep (se 3 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 3746573 = 1404965) B1404965
theorem B2108177 : Blo 738327 2108177 := bstep (se 2 (by rfl) ⟨790566, by rfl⟩ : syracuseStep 2108177 = 1581133) B1581133
theorem B1878947 : Blo 738327 1878947 := bstep (se 1 (by rfl) ⟨1409210, by rfl⟩ : syracuseStep 1878947 = 2818421) B2818421
theorem B2501549 : Blo 738327 2501549 := bstep (se 3 (by rfl) ⟨469040, by rfl⟩ : syracuseStep 2501549 = 938081) B938081
theorem B2501603 : Blo 738327 2501603 := bstep (se 1 (by rfl) ⟨1876202, by rfl⟩ : syracuseStep 2501603 = 3752405) B3752405
theorem B3550321 : Blo 738327 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B5057677 : Blo 738327 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B2370701 : Blo 738327 2370701 := bstep (se 3 (by rfl) ⟨444506, by rfl⟩ : syracuseStep 2370701 = 889013) B889013
theorem B830659 : Blo 738327 830659 := bstep (se 1 (by rfl) ⟨622994, by rfl⟩ : syracuseStep 830659 = 1245989) B1245989
theorem B2501873 : Blo 738327 2501873 := bstep (se 2 (by rfl) ⟨938202, by rfl⟩ : syracuseStep 2501873 = 1876405) B1876405
theorem B2370829 : Blo 738327 2370829 := bstep (se 3 (by rfl) ⟨444530, by rfl⟩ : syracuseStep 2370829 = 889061) B889061
theorem B830803 : Blo 738327 830803 := bstep (se 1 (by rfl) ⟨623102, by rfl⟩ : syracuseStep 830803 = 1246205) B1246205
theorem B4205965 : Blo 738327 4205965 := bstep (se 3 (by rfl) ⟨788618, by rfl⟩ : syracuseStep 4205965 = 1577237) B1577237
theorem B830947 : Blo 738327 830947 := bstep (se 1 (by rfl) ⟨623210, by rfl⟩ : syracuseStep 830947 = 1246421) B1246421
theorem B2371085 : Blo 738327 2371085 := bstep (se 3 (by rfl) ⟨444578, by rfl⟩ : syracuseStep 2371085 = 889157) B889157
theorem B1584721 : Blo 738327 1584721 := bstep (se 2 (by rfl) ⟨594270, by rfl⟩ : syracuseStep 1584721 = 1188541) B1188541
theorem B831091 : Blo 738327 831091 := bstep (se 1 (by rfl) ⟨623318, by rfl⟩ : syracuseStep 831091 = 1246637) B1246637
theorem B831235 : Blo 738327 831235 := bstep (se 1 (by rfl) ⟨623426, by rfl⟩ : syracuseStep 831235 = 1246853) B1246853
theorem B2699021 : Blo 738327 2699021 := bstep (se 3 (by rfl) ⟨506066, by rfl⟩ : syracuseStep 2699021 = 1012133) B1012133
theorem B2502413 : Blo 738327 2502413 := bstep (se 3 (by rfl) ⟨469202, by rfl⟩ : syracuseStep 2502413 = 938405) B938405
theorem B2502467 : Blo 738327 2502467 := bstep (se 1 (by rfl) ⟨1876850, by rfl⟩ : syracuseStep 2502467 = 3753701) B3753701
theorem B2535245 : Blo 738327 2535245 := bstep (se 3 (by rfl) ⟨475358, by rfl⟩ : syracuseStep 2535245 = 950717) B950717
theorem B831379 : Blo 738327 831379 := bstep (se 1 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 831379 = 1247069) B1247069
theorem B831523 : Blo 738327 831523 := bstep (se 1 (by rfl) ⟨623642, by rfl⟩ : syracuseStep 831523 = 1247285) B1247285
theorem B2502737 : Blo 738327 2502737 := bstep (se 2 (by rfl) ⟨938526, by rfl⟩ : syracuseStep 2502737 = 1877053) B1877053
theorem B6926435 : Blo 738327 6926435 := bstep (se 1 (by rfl) ⟨5194826, by rfl⟩ : syracuseStep 6926435 = 10389653) B10389653
theorem B5615729 : Blo 738327 5615729 := bstep (se 2 (by rfl) ⟨2105898, by rfl⟩ : syracuseStep 5615729 = 4211797) B4211797
theorem B831667 : Blo 738327 831667 := bstep (se 1 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 831667 = 1247501) B1247501
theorem B2109635 : Blo 738327 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B4731149 : Blo 738327 4731149 := bstep (se 3 (by rfl) ⟨887090, by rfl⟩ : syracuseStep 4731149 = 1774181) B1774181
theorem B831811 : Blo 738327 831811 := bstep (se 1 (by rfl) ⟨623858, by rfl⟩ : syracuseStep 831811 = 1247717) B1247717
theorem B2666893 : Blo 738327 2666893 := bstep (se 3 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 2666893 = 1000085) B1000085
theorem B831955 : Blo 738327 831955 := bstep (se 1 (by rfl) ⟨623966, by rfl⟩ : syracuseStep 831955 = 1247933) B1247933
theorem B832099 : Blo 738327 832099 := bstep (se 1 (by rfl) ⟨624074, by rfl⟩ : syracuseStep 832099 = 1248149) B1248149
theorem B2503277 : Blo 738327 2503277 := bstep (se 3 (by rfl) ⟨469364, by rfl⟩ : syracuseStep 2503277 = 938729) B938729
theorem B2503331 : Blo 738327 2503331 := bstep (se 1 (by rfl) ⟨1877498, by rfl⟩ : syracuseStep 2503331 = 3754997) B3754997
theorem B1127105 : Blo 738327 1127105 := bstep (se 2 (by rfl) ⟨422664, by rfl⟩ : syracuseStep 1127105 = 845329) B845329
theorem B832243 : Blo 738327 832243 := bstep (se 1 (by rfl) ⟨624182, by rfl⟩ : syracuseStep 832243 = 1248365) B1248365
theorem B6337379 : Blo 738327 6337379 := bstep (se 1 (by rfl) ⟨4753034, by rfl⟩ : syracuseStep 6337379 = 9506069) B9506069
theorem B832387 : Blo 738327 832387 := bstep (se 1 (by rfl) ⟨624290, by rfl⟩ : syracuseStep 832387 = 1248581) B1248581
theorem B2503601 : Blo 738327 2503601 := bstep (se 2 (by rfl) ⟨938850, by rfl⟩ : syracuseStep 2503601 = 1877701) B1877701
theorem B2110445 : Blo 738327 2110445 := bstep (se 3 (by rfl) ⟨395708, by rfl⟩ : syracuseStep 2110445 = 791417) B791417
theorem B2372611 : Blo 738327 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B832531 : Blo 738327 832531 := bstep (se 1 (by rfl) ⟨624398, by rfl⟩ : syracuseStep 832531 = 1248797) B1248797
theorem B832675 : Blo 738327 832675 := bstep (se 1 (by rfl) ⟨624506, by rfl⟩ : syracuseStep 832675 = 1249013) B1249013
theorem B1782947 : Blo 738327 1782947 := bstep (se 1 (by rfl) ⟨1337210, by rfl⟩ : syracuseStep 1782947 = 2674421) B2674421
theorem B2110637 : Blo 738327 2110637 := bstep (se 3 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 2110637 = 791489) B791489
theorem B15971525 : Blo 738327 15971525 := bstep (se 4 (by rfl) ⟨1497330, by rfl⟩ : syracuseStep 15971525 = 2994661) B2994661
theorem B2667761 : Blo 738327 2667761 := bstep (se 2 (by rfl) ⟨1000410, by rfl⟩ : syracuseStep 2667761 = 2000821) B2000821
theorem B1783043 : Blo 738327 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B832819 : Blo 738327 832819 := bstep (se 1 (by rfl) ⟨624614, by rfl⟩ : syracuseStep 832819 = 1249229) B1249229
theorem B4207949 : Blo 738327 4207949 := bstep (se 3 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 4207949 = 1577981) B1577981
theorem B3159395 : Blo 738327 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B832963 : Blo 738327 832963 := bstep (se 1 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 832963 = 1249445) B1249445
theorem B1783235 : Blo 738327 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B2504141 : Blo 738327 2504141 := bstep (se 3 (by rfl) ⟨469526, by rfl⟩ : syracuseStep 2504141 = 939053) B939053
theorem B17315299 : Blo 738327 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B2504195 : Blo 738327 2504195 := bstep (se 1 (by rfl) ⟨1878146, by rfl⟩ : syracuseStep 2504195 = 3756293) B3756293
theorem B833107 : Blo 738327 833107 := bstep (se 1 (by rfl) ⟨624830, by rfl⟩ : syracuseStep 833107 = 1249661) B1249661
theorem B2438755 : Blo 738327 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B3749489 : Blo 738327 3749489 := bstep (se 2 (by rfl) ⟨1406058, by rfl⟩ : syracuseStep 3749489 = 2812117) B2812117
theorem B833251 : Blo 738327 833251 := bstep (se 1 (by rfl) ⟨624938, by rfl⟩ : syracuseStep 833251 = 1249877) B1249877
theorem B2504465 : Blo 738327 2504465 := bstep (se 2 (by rfl) ⟨939174, by rfl⟩ : syracuseStep 2504465 = 1878349) B1878349
theorem B1128259 : Blo 738327 1128259 := bstep (se 1 (by rfl) ⟨846194, by rfl⟩ : syracuseStep 1128259 = 1692389) B1692389
theorem B833395 : Blo 738327 833395 := bstep (se 1 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 833395 = 1250093) B1250093
theorem B833539 : Blo 738327 833539 := bstep (se 1 (by rfl) ⟨625154, by rfl⟩ : syracuseStep 833539 = 1250309) B1250309
theorem B2111629 : Blo 738327 2111629 := bstep (se 3 (by rfl) ⟨395930, by rfl⟩ : syracuseStep 2111629 = 791861) B791861
theorem B833683 : Blo 738327 833683 := bstep (se 1 (by rfl) ⟨625262, by rfl⟩ : syracuseStep 833683 = 1250525) B1250525
theorem B4208881 : Blo 738327 4208881 := bstep (se 2 (by rfl) ⟨1578330, by rfl⟩ : syracuseStep 4208881 = 3156661) B3156661
theorem B833827 : Blo 738327 833827 := bstep (se 1 (by rfl) ⟨625370, by rfl⟩ : syracuseStep 833827 = 1250741) B1250741
theorem B2505005 : Blo 738327 2505005 := bstep (se 3 (by rfl) ⟨469688, by rfl⟩ : syracuseStep 2505005 = 939377) B939377
theorem B2505059 : Blo 738327 2505059 := bstep (se 1 (by rfl) ⟨1878794, by rfl⟩ : syracuseStep 2505059 = 3757589) B3757589
theorem B833971 : Blo 738327 833971 := bstep (se 1 (by rfl) ⟨625478, by rfl⟩ : syracuseStep 833971 = 1250957) B1250957
theorem B2374211 : Blo 738327 2374211 := bstep (se 1 (by rfl) ⟨1780658, by rfl⟩ : syracuseStep 2374211 = 3561317) B3561317
theorem B834115 : Blo 738327 834115 := bstep (se 1 (by rfl) ⟨625586, by rfl⟩ : syracuseStep 834115 = 1251173) B1251173
theorem B2505329 : Blo 738327 2505329 := bstep (se 2 (by rfl) ⟨939498, by rfl⟩ : syracuseStep 2505329 = 1878997) B1878997
theorem B834259 : Blo 738327 834259 := bstep (se 1 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 834259 = 1251389) B1251389
theorem B834403 : Blo 738327 834403 := bstep (se 1 (by rfl) ⟨625802, by rfl⟩ : syracuseStep 834403 = 1251605) B1251605
theorem B834547 : Blo 738327 834547 := bstep (se 1 (by rfl) ⟨625910, by rfl⟩ : syracuseStep 834547 = 1251821) B1251821
theorem B3750947 : Blo 738327 3750947 := bstep (se 1 (by rfl) ⟨2813210, by rfl⟩ : syracuseStep 3750947 = 5626421) B5626421
theorem B998497 : Blo 738327 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B834691 : Blo 738327 834691 := bstep (se 1 (by rfl) ⟨626018, by rfl⟩ : syracuseStep 834691 = 1252037) B1252037
theorem B834835 : Blo 738327 834835 := bstep (se 1 (by rfl) ⟨626126, by rfl⟩ : syracuseStep 834835 = 1252253) B1252253
theorem B10665269 : Blo 738327 10665269 := bstep (se 5 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 10665269 = 999869) B999869
theorem B4504909 : Blo 738327 4504909 := bstep (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) B1689341
theorem B834979 : Blo 738327 834979 := bstep (se 1 (by rfl) ⟨626234, by rfl⟩ : syracuseStep 834979 = 1252469) B1252469
theorem B3554765 : Blo 738327 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B4865507 : Blo 738327 4865507 := bstep (se 1 (by rfl) ⟨3649130, by rfl⟩ : syracuseStep 4865507 = 7298261) B7298261
theorem B2375185 : Blo 738327 2375185 := bstep (se 2 (by rfl) ⟨890694, by rfl⟩ : syracuseStep 2375185 = 1781389) B1781389
theorem B4210339 : Blo 738327 4210339 := bstep (se 1 (by rfl) ⟨3157754, by rfl⟩ : syracuseStep 4210339 = 6315509) B6315509
theorem B999091 : Blo 738327 999091 := bstep (se 1 (by rfl) ⟨749318, by rfl⟩ : syracuseStep 999091 = 1498637) B1498637
theorem B8437445 : Blo 738327 8437445 := bstep (se 4 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 8437445 = 1582021) B1582021
theorem B3751757 : Blo 738327 3751757 := bstep (se 3 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 3751757 = 1406909) B1406909
theorem B2113361 : Blo 738327 2113361 := bstep (se 2 (by rfl) ⟨792510, by rfl⟩ : syracuseStep 2113361 = 1585021) B1585021
theorem B60702605 : Blo 738327 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B999361 : Blo 738327 999361 := bstep (se 2 (by rfl) ⟨374760, by rfl⟩ : syracuseStep 999361 = 749521) B749521
theorem B2113553 : Blo 738327 2113553 := bstep (se 2 (by rfl) ⟨792582, by rfl⟩ : syracuseStep 2113553 = 1585165) B1585165
theorem B4210865 : Blo 738327 4210865 := bstep (se 2 (by rfl) ⟨1579074, by rfl⟩ : syracuseStep 4210865 = 3158149) B3158149
theorem B1000129 : Blo 738327 1000129 := bstep (se 2 (by rfl) ⟨375048, by rfl⟩ : syracuseStep 1000129 = 750097) B750097
theorem B1065793 : Blo 738327 1065793 := bstep (se 2 (by rfl) ⟨399672, by rfl⟩ : syracuseStep 1065793 = 799345) B799345
theorem B3163121 : Blo 738327 3163121 := bstep (se 2 (by rfl) ⟨1186170, by rfl⟩ : syracuseStep 3163121 = 2372341) B2372341
theorem B738339 : Blo 738327 738339 := bstep (se 1 (by rfl) ⟨553754, by rfl⟩ : syracuseStep 738339 = 1107509) B1107509
theorem B2081837 : Blo 738327 2081837 := bstep (se 3 (by rfl) ⟨390344, by rfl⟩ : syracuseStep 2081837 = 780689) B780689
theorem B738355 : Blo 738327 738355 := bstep (se 1 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 738355 = 1107533) B1107533
theorem B738371 : Blo 738327 738371 := bstep (se 1 (by rfl) ⟨553778, by rfl⟩ : syracuseStep 738371 = 1107557) B1107557
theorem B738387 : Blo 738327 738387 := bstep (se 1 (by rfl) ⟨553790, by rfl⟩ : syracuseStep 738387 = 1107581) B1107581
theorem B738403 : Blo 738327 738403 := bstep (se 1 (by rfl) ⟨553802, by rfl⟩ : syracuseStep 738403 = 1107605) B1107605
theorem B738419 : Blo 738327 738419 := bstep (se 1 (by rfl) ⟨553814, by rfl⟩ : syracuseStep 738419 = 1107629) B1107629
theorem B738435 : Blo 738327 738435 := bstep (se 1 (by rfl) ⟨553826, by rfl⟩ : syracuseStep 738435 = 1107653) B1107653
theorem B738451 : Blo 738327 738451 := bstep (se 1 (by rfl) ⟨553838, by rfl⟩ : syracuseStep 738451 = 1107677) B1107677
theorem B935059 : Blo 738327 935059 := bstep (se 1 (by rfl) ⟨701294, by rfl⟩ : syracuseStep 935059 = 1402589) B1402589
theorem B738467 : Blo 738327 738467 := bstep (se 1 (by rfl) ⟨553850, by rfl⟩ : syracuseStep 738467 = 1107701) B1107701
theorem B2376877 : Blo 738327 2376877 := bstep (se 3 (by rfl) ⟨445664, by rfl⟩ : syracuseStep 2376877 = 891329) B891329
theorem B738483 : Blo 738327 738483 := bstep (se 1 (by rfl) ⟨553862, by rfl⟩ : syracuseStep 738483 = 1107725) B1107725
theorem B738499 : Blo 738327 738499 := bstep (se 1 (by rfl) ⟨553874, by rfl⟩ : syracuseStep 738499 = 1107749) B1107749
theorem B738515 : Blo 738327 738515 := bstep (se 1 (by rfl) ⟨553886, by rfl⟩ : syracuseStep 738515 = 1107773) B1107773
theorem B738531 : Blo 738327 738531 := bstep (se 1 (by rfl) ⟨553898, by rfl⟩ : syracuseStep 738531 = 1107797) B1107797
theorem B738547 : Blo 738327 738547 := bstep (se 1 (by rfl) ⟨553910, by rfl⟩ : syracuseStep 738547 = 1107821) B1107821
theorem B935155 : Blo 738327 935155 := bstep (se 1 (by rfl) ⟨701366, by rfl⟩ : syracuseStep 935155 = 1402733) B1402733
theorem B738563 : Blo 738327 738563 := bstep (se 1 (by rfl) ⟨553922, by rfl⟩ : syracuseStep 738563 = 1107845) B1107845
theorem B738579 : Blo 738327 738579 := bstep (se 1 (by rfl) ⟨553934, by rfl⟩ : syracuseStep 738579 = 1107869) B1107869
theorem B738595 : Blo 738327 738595 := bstep (se 1 (by rfl) ⟨553946, by rfl⟩ : syracuseStep 738595 = 1107893) B1107893
theorem B4113713 : Blo 738327 4113713 := bstep (se 2 (by rfl) ⟨1542642, by rfl⟩ : syracuseStep 4113713 = 3085285) B3085285
theorem B738611 : Blo 738327 738611 := bstep (se 1 (by rfl) ⟨553958, by rfl⟩ : syracuseStep 738611 = 1107917) B1107917
theorem B738627 : Blo 738327 738627 := bstep (se 1 (by rfl) ⟨553970, by rfl⟩ : syracuseStep 738627 = 1107941) B1107941
theorem B738643 : Blo 738327 738643 := bstep (se 1 (by rfl) ⟨553982, by rfl⟩ : syracuseStep 738643 = 1107965) B1107965
theorem B738659 : Blo 738327 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B738675 : Blo 738327 738675 := bstep (se 1 (by rfl) ⟨554006, by rfl⟩ : syracuseStep 738675 = 1108013) B1108013
theorem B738691 : Blo 738327 738691 := bstep (se 1 (by rfl) ⟨554018, by rfl⟩ : syracuseStep 738691 = 1108037) B1108037
theorem B738707 : Blo 738327 738707 := bstep (se 1 (by rfl) ⟨554030, by rfl⟩ : syracuseStep 738707 = 1108061) B1108061
theorem B738723 : Blo 738327 738723 := bstep (se 1 (by rfl) ⟨554042, by rfl⟩ : syracuseStep 738723 = 1108085) B1108085
theorem B738739 : Blo 738327 738739 := bstep (se 1 (by rfl) ⟨554054, by rfl⟩ : syracuseStep 738739 = 1108109) B1108109
theorem B738755 : Blo 738327 738755 := bstep (se 1 (by rfl) ⟨554066, by rfl⟩ : syracuseStep 738755 = 1108133) B1108133
theorem B738771 : Blo 738327 738771 := bstep (se 1 (by rfl) ⟨554078, by rfl⟩ : syracuseStep 738771 = 1108157) B1108157
theorem B738787 : Blo 738327 738787 := bstep (se 1 (by rfl) ⟨554090, by rfl⟩ : syracuseStep 738787 = 1108181) B1108181
theorem B738803 : Blo 738327 738803 := bstep (se 1 (by rfl) ⟨554102, by rfl⟩ : syracuseStep 738803 = 1108205) B1108205
theorem B1263107 : Blo 738327 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B738819 : Blo 738327 738819 := bstep (se 1 (by rfl) ⟨554114, by rfl⟩ : syracuseStep 738819 = 1108229) B1108229
theorem B738835 : Blo 738327 738835 := bstep (se 1 (by rfl) ⟨554126, by rfl⟩ : syracuseStep 738835 = 1108253) B1108253
theorem B738851 : Blo 738327 738851 := bstep (se 1 (by rfl) ⟨554138, by rfl⟩ : syracuseStep 738851 = 1108277) B1108277
theorem B738867 : Blo 738327 738867 := bstep (se 1 (by rfl) ⟨554150, by rfl⟩ : syracuseStep 738867 = 1108301) B1108301
theorem B738883 : Blo 738327 738883 := bstep (se 1 (by rfl) ⟨554162, by rfl⟩ : syracuseStep 738883 = 1108325) B1108325
theorem B1689169 : Blo 738327 1689169 := bstep (se 2 (by rfl) ⟨633438, by rfl⟩ : syracuseStep 1689169 = 1266877) B1266877
theorem B738899 : Blo 738327 738899 := bstep (se 1 (by rfl) ⟨554174, by rfl⟩ : syracuseStep 738899 = 1108349) B1108349
theorem B738915 : Blo 738327 738915 := bstep (se 1 (by rfl) ⟨554186, by rfl⟩ : syracuseStep 738915 = 1108373) B1108373
theorem B4212323 : Blo 738327 4212323 := bstep (se 1 (by rfl) ⟨3159242, by rfl⟩ : syracuseStep 4212323 = 6318485) B6318485
theorem B738931 : Blo 738327 738931 := bstep (se 1 (by rfl) ⟨554198, by rfl⟩ : syracuseStep 738931 = 1108397) B1108397
theorem B738947 : Blo 738327 738947 := bstep (se 1 (by rfl) ⟨554210, by rfl⟩ : syracuseStep 738947 = 1108421) B1108421
theorem B738963 : Blo 738327 738963 := bstep (se 1 (by rfl) ⟨554222, by rfl⟩ : syracuseStep 738963 = 1108445) B1108445
theorem B738979 : Blo 738327 738979 := bstep (se 1 (by rfl) ⟨554234, by rfl⟩ : syracuseStep 738979 = 1108469) B1108469
theorem B738995 : Blo 738327 738995 := bstep (se 1 (by rfl) ⟨554246, by rfl⟩ : syracuseStep 738995 = 1108493) B1108493
theorem B739011 : Blo 738327 739011 := bstep (se 1 (by rfl) ⟨554258, by rfl⟩ : syracuseStep 739011 = 1108517) B1108517
theorem B739027 : Blo 738327 739027 := bstep (se 1 (by rfl) ⟨554270, by rfl⟩ : syracuseStep 739027 = 1108541) B1108541
theorem B739043 : Blo 738327 739043 := bstep (se 1 (by rfl) ⟨554282, by rfl⟩ : syracuseStep 739043 = 1108565) B1108565
theorem B935651 : Blo 738327 935651 := bstep (se 1 (by rfl) ⟨701738, by rfl⟩ : syracuseStep 935651 = 1403477) B1403477
theorem B739059 : Blo 738327 739059 := bstep (se 1 (by rfl) ⟨554294, by rfl⟩ : syracuseStep 739059 = 1108589) B1108589
theorem B739075 : Blo 738327 739075 := bstep (se 1 (by rfl) ⟨554306, by rfl⟩ : syracuseStep 739075 = 1108613) B1108613
theorem B739091 : Blo 738327 739091 := bstep (se 1 (by rfl) ⟨554318, by rfl⟩ : syracuseStep 739091 = 1108637) B1108637
theorem B739107 : Blo 738327 739107 := bstep (se 1 (by rfl) ⟨554330, by rfl⟩ : syracuseStep 739107 = 1108661) B1108661
theorem B739123 : Blo 738327 739123 := bstep (se 1 (by rfl) ⟨554342, by rfl⟩ : syracuseStep 739123 = 1108685) B1108685
theorem B739139 : Blo 738327 739139 := bstep (se 1 (by rfl) ⟨554354, by rfl⟩ : syracuseStep 739139 = 1108709) B1108709
theorem B739155 : Blo 738327 739155 := bstep (se 1 (by rfl) ⟨554366, by rfl⟩ : syracuseStep 739155 = 1108733) B1108733
theorem B739171 : Blo 738327 739171 := bstep (se 1 (by rfl) ⟨554378, by rfl⟩ : syracuseStep 739171 = 1108757) B1108757
theorem B739187 : Blo 738327 739187 := bstep (se 1 (by rfl) ⟨554390, by rfl⟩ : syracuseStep 739187 = 1108781) B1108781
theorem B739203 : Blo 738327 739203 := bstep (se 1 (by rfl) ⟨554402, by rfl⟩ : syracuseStep 739203 = 1108805) B1108805
theorem B2246545 : Blo 738327 2246545 := bstep (se 2 (by rfl) ⟨842454, by rfl⟩ : syracuseStep 2246545 = 1684909) B1684909
theorem B739219 : Blo 738327 739219 := bstep (se 1 (by rfl) ⟨554414, by rfl⟩ : syracuseStep 739219 = 1108829) B1108829
theorem B739235 : Blo 738327 739235 := bstep (se 1 (by rfl) ⟨554426, by rfl⟩ : syracuseStep 739235 = 1108853) B1108853
theorem B739251 : Blo 738327 739251 := bstep (se 1 (by rfl) ⟨554438, by rfl⟩ : syracuseStep 739251 = 1108877) B1108877
theorem B739267 : Blo 738327 739267 := bstep (se 1 (by rfl) ⟨554450, by rfl⟩ : syracuseStep 739267 = 1108901) B1108901
theorem B4507589 : Blo 738327 4507589 := bstep (se 4 (by rfl) ⟨422586, by rfl⟩ : syracuseStep 4507589 = 845173) B845173
theorem B739283 : Blo 738327 739283 := bstep (se 1 (by rfl) ⟨554462, by rfl⟩ : syracuseStep 739283 = 1108925) B1108925
theorem B739299 : Blo 738327 739299 := bstep (se 1 (by rfl) ⟨554474, by rfl⟩ : syracuseStep 739299 = 1108949) B1108949
theorem B739315 : Blo 738327 739315 := bstep (se 1 (by rfl) ⟨554486, by rfl⟩ : syracuseStep 739315 = 1108973) B1108973
theorem B903155 : Blo 738327 903155 := bstep (se 1 (by rfl) ⟨677366, by rfl⟩ : syracuseStep 903155 = 1354733) B1354733
theorem B739331 : Blo 738327 739331 := bstep (se 1 (by rfl) ⟨554498, by rfl⟩ : syracuseStep 739331 = 1108997) B1108997
theorem B739347 : Blo 738327 739347 := bstep (se 1 (by rfl) ⟨554510, by rfl⟩ : syracuseStep 739347 = 1109021) B1109021
theorem B739363 : Blo 738327 739363 := bstep (se 1 (by rfl) ⟨554522, by rfl⟩ : syracuseStep 739363 = 1109045) B1109045
theorem B739379 : Blo 738327 739379 := bstep (se 1 (by rfl) ⟨554534, by rfl⟩ : syracuseStep 739379 = 1109069) B1109069
theorem B739395 : Blo 738327 739395 := bstep (se 1 (by rfl) ⟨554546, by rfl⟩ : syracuseStep 739395 = 1109093) B1109093
theorem B739411 : Blo 738327 739411 := bstep (se 1 (by rfl) ⟨554558, by rfl⟩ : syracuseStep 739411 = 1109117) B1109117
theorem B739427 : Blo 738327 739427 := bstep (se 1 (by rfl) ⟨554570, by rfl⟩ : syracuseStep 739427 = 1109141) B1109141
theorem B739443 : Blo 738327 739443 := bstep (se 1 (by rfl) ⟨554582, by rfl⟩ : syracuseStep 739443 = 1109165) B1109165
theorem B739459 : Blo 738327 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B739475 : Blo 738327 739475 := bstep (se 1 (by rfl) ⟨554606, by rfl⟩ : syracuseStep 739475 = 1109213) B1109213
theorem B739491 : Blo 738327 739491 := bstep (se 1 (by rfl) ⟨554618, by rfl⟩ : syracuseStep 739491 = 1109237) B1109237
theorem B739507 : Blo 738327 739507 := bstep (se 1 (by rfl) ⟨554630, by rfl⟩ : syracuseStep 739507 = 1109261) B1109261
theorem B739523 : Blo 738327 739523 := bstep (se 1 (by rfl) ⟨554642, by rfl⟩ : syracuseStep 739523 = 1109285) B1109285
theorem B739539 : Blo 738327 739539 := bstep (se 1 (by rfl) ⟨554654, by rfl⟩ : syracuseStep 739539 = 1109309) B1109309
theorem B739555 : Blo 738327 739555 := bstep (se 1 (by rfl) ⟨554666, by rfl⟩ : syracuseStep 739555 = 1109333) B1109333
theorem B739571 : Blo 738327 739571 := bstep (se 1 (by rfl) ⟨554678, by rfl⟩ : syracuseStep 739571 = 1109357) B1109357
theorem B739587 : Blo 738327 739587 := bstep (se 1 (by rfl) ⟨554690, by rfl⟩ : syracuseStep 739587 = 1109381) B1109381
theorem B739603 : Blo 738327 739603 := bstep (se 1 (by rfl) ⟨554702, by rfl⟩ : syracuseStep 739603 = 1109405) B1109405
theorem B739619 : Blo 738327 739619 := bstep (se 1 (by rfl) ⟨554714, by rfl⟩ : syracuseStep 739619 = 1109429) B1109429
theorem B739635 : Blo 738327 739635 := bstep (se 1 (by rfl) ⟨554726, by rfl⟩ : syracuseStep 739635 = 1109453) B1109453
theorem B739651 : Blo 738327 739651 := bstep (se 1 (by rfl) ⟨554738, by rfl⟩ : syracuseStep 739651 = 1109477) B1109477
theorem B739667 : Blo 738327 739667 := bstep (se 1 (by rfl) ⟨554750, by rfl⟩ : syracuseStep 739667 = 1109501) B1109501
theorem B739683 : Blo 738327 739683 := bstep (se 1 (by rfl) ⟨554762, by rfl⟩ : syracuseStep 739683 = 1109525) B1109525
theorem B739699 : Blo 738327 739699 := bstep (se 1 (by rfl) ⟨554774, by rfl⟩ : syracuseStep 739699 = 1109549) B1109549
theorem B739715 : Blo 738327 739715 := bstep (se 1 (by rfl) ⟨554786, by rfl⟩ : syracuseStep 739715 = 1109573) B1109573
theorem B739731 : Blo 738327 739731 := bstep (se 1 (by rfl) ⟨554798, by rfl⟩ : syracuseStep 739731 = 1109597) B1109597
theorem B739747 : Blo 738327 739747 := bstep (se 1 (by rfl) ⟨554810, by rfl⟩ : syracuseStep 739747 = 1109621) B1109621
theorem B936355 : Blo 738327 936355 := bstep (se 1 (by rfl) ⟨702266, by rfl⟩ : syracuseStep 936355 = 1404533) B1404533
theorem B739763 : Blo 738327 739763 := bstep (se 1 (by rfl) ⟨554822, by rfl⟩ : syracuseStep 739763 = 1109645) B1109645
theorem B739779 : Blo 738327 739779 := bstep (se 1 (by rfl) ⟨554834, by rfl⟩ : syracuseStep 739779 = 1109669) B1109669
theorem B739795 : Blo 738327 739795 := bstep (se 1 (by rfl) ⟨554846, by rfl⟩ : syracuseStep 739795 = 1109693) B1109693
theorem B739811 : Blo 738327 739811 := bstep (se 1 (by rfl) ⟨554858, by rfl⟩ : syracuseStep 739811 = 1109717) B1109717
theorem B6310385 : Blo 738327 6310385 := bstep (se 2 (by rfl) ⟨2366394, by rfl⟩ : syracuseStep 6310385 = 4732789) B4732789
theorem B739827 : Blo 738327 739827 := bstep (se 1 (by rfl) ⟨554870, by rfl⟩ : syracuseStep 739827 = 1109741) B1109741
theorem B739843 : Blo 738327 739843 := bstep (se 1 (by rfl) ⟨554882, by rfl⟩ : syracuseStep 739843 = 1109765) B1109765
theorem B936451 : Blo 738327 936451 := bstep (se 1 (by rfl) ⟨702338, by rfl⟩ : syracuseStep 936451 = 1404677) B1404677
theorem B739859 : Blo 738327 739859 := bstep (se 1 (by rfl) ⟨554894, by rfl⟩ : syracuseStep 739859 = 1109789) B1109789
theorem B739875 : Blo 738327 739875 := bstep (se 1 (by rfl) ⟨554906, by rfl⟩ : syracuseStep 739875 = 1109813) B1109813
theorem B739891 : Blo 738327 739891 := bstep (se 1 (by rfl) ⟨554918, by rfl⟩ : syracuseStep 739891 = 1109837) B1109837
theorem B739907 : Blo 738327 739907 := bstep (se 1 (by rfl) ⟨554930, by rfl⟩ : syracuseStep 739907 = 1109861) B1109861
theorem B739923 : Blo 738327 739923 := bstep (se 1 (by rfl) ⟨554942, by rfl⟩ : syracuseStep 739923 = 1109885) B1109885
theorem B4737635 : Blo 738327 4737635 := bstep (se 1 (by rfl) ⟨3553226, by rfl⟩ : syracuseStep 4737635 = 7106453) B7106453
theorem B739939 : Blo 738327 739939 := bstep (se 1 (by rfl) ⟨554954, by rfl⟩ : syracuseStep 739939 = 1109909) B1109909
theorem B2312813 : Blo 738327 2312813 := bstep (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) B867305
theorem B739955 : Blo 738327 739955 := bstep (se 1 (by rfl) ⟨554966, by rfl⟩ : syracuseStep 739955 = 1109933) B1109933
theorem B739971 : Blo 738327 739971 := bstep (se 1 (by rfl) ⟨554978, by rfl⟩ : syracuseStep 739971 = 1109957) B1109957
theorem B739987 : Blo 738327 739987 := bstep (se 1 (by rfl) ⟨554990, by rfl⟩ : syracuseStep 739987 = 1109981) B1109981
theorem B740003 : Blo 738327 740003 := bstep (se 1 (by rfl) ⟨555002, by rfl⟩ : syracuseStep 740003 = 1110005) B1110005
theorem B3754673 : Blo 738327 3754673 := bstep (se 2 (by rfl) ⟨1408002, by rfl⟩ : syracuseStep 3754673 = 2816005) B2816005
theorem B740019 : Blo 738327 740019 := bstep (se 1 (by rfl) ⟨555014, by rfl⟩ : syracuseStep 740019 = 1110029) B1110029
theorem B740035 : Blo 738327 740035 := bstep (se 1 (by rfl) ⟨555026, by rfl⟩ : syracuseStep 740035 = 1110053) B1110053
theorem B740051 : Blo 738327 740051 := bstep (se 1 (by rfl) ⟨555038, by rfl⟩ : syracuseStep 740051 = 1110077) B1110077
theorem B740067 : Blo 738327 740067 := bstep (se 1 (by rfl) ⟨555050, by rfl⟩ : syracuseStep 740067 = 1110101) B1110101
theorem B740083 : Blo 738327 740083 := bstep (se 1 (by rfl) ⟨555062, by rfl⟩ : syracuseStep 740083 = 1110125) B1110125
theorem B1100531 : Blo 738327 1100531 := bstep (se 1 (by rfl) ⟨825398, by rfl⟩ : syracuseStep 1100531 = 1650797) B1650797
theorem B1067777 : Blo 738327 1067777 := bstep (se 2 (by rfl) ⟨400416, by rfl⟩ : syracuseStep 1067777 = 800833) B800833
theorem B740099 : Blo 738327 740099 := bstep (se 1 (by rfl) ⟨555074, by rfl⟩ : syracuseStep 740099 = 1110149) B1110149
theorem B740115 : Blo 738327 740115 := bstep (se 1 (by rfl) ⟨555086, by rfl⟩ : syracuseStep 740115 = 1110173) B1110173
theorem B740131 : Blo 738327 740131 := bstep (se 1 (by rfl) ⟨555098, by rfl⟩ : syracuseStep 740131 = 1110197) B1110197
theorem B740147 : Blo 738327 740147 := bstep (se 1 (by rfl) ⟨555110, by rfl⟩ : syracuseStep 740147 = 1110221) B1110221
theorem B740163 : Blo 738327 740163 := bstep (se 1 (by rfl) ⟨555122, by rfl⟩ : syracuseStep 740163 = 1110245) B1110245
theorem B740179 : Blo 738327 740179 := bstep (se 1 (by rfl) ⟨555134, by rfl⟩ : syracuseStep 740179 = 1110269) B1110269
theorem B740195 : Blo 738327 740195 := bstep (se 1 (by rfl) ⟨555146, by rfl⟩ : syracuseStep 740195 = 1110293) B1110293
theorem B740211 : Blo 738327 740211 := bstep (se 1 (by rfl) ⟨555158, by rfl⟩ : syracuseStep 740211 = 1110317) B1110317
theorem B740227 : Blo 738327 740227 := bstep (se 1 (by rfl) ⟨555170, by rfl⟩ : syracuseStep 740227 = 1110341) B1110341
theorem B740243 : Blo 738327 740243 := bstep (se 1 (by rfl) ⟨555182, by rfl⟩ : syracuseStep 740243 = 1110365) B1110365
theorem B740259 : Blo 738327 740259 := bstep (se 1 (by rfl) ⟨555194, by rfl⟩ : syracuseStep 740259 = 1110389) B1110389
theorem B740275 : Blo 738327 740275 := bstep (se 1 (by rfl) ⟨555206, by rfl⟩ : syracuseStep 740275 = 1110413) B1110413
theorem B740291 : Blo 738327 740291 := bstep (se 1 (by rfl) ⟨555218, by rfl⟩ : syracuseStep 740291 = 1110437) B1110437
theorem B740307 : Blo 738327 740307 := bstep (se 1 (by rfl) ⟨555230, by rfl⟩ : syracuseStep 740307 = 1110461) B1110461
theorem B740323 : Blo 738327 740323 := bstep (se 1 (by rfl) ⟨555242, by rfl⟩ : syracuseStep 740323 = 1110485) B1110485
theorem B936947 : Blo 738327 936947 := bstep (se 1 (by rfl) ⟨702710, by rfl⟩ : syracuseStep 936947 = 1405421) B1405421
theorem B740339 : Blo 738327 740339 := bstep (se 1 (by rfl) ⟨555254, by rfl⟩ : syracuseStep 740339 = 1110509) B1110509
theorem B740355 : Blo 738327 740355 := bstep (se 1 (by rfl) ⟨555266, by rfl⟩ : syracuseStep 740355 = 1110533) B1110533
theorem B740371 : Blo 738327 740371 := bstep (se 1 (by rfl) ⟨555278, by rfl⟩ : syracuseStep 740371 = 1110557) B1110557
theorem B740387 : Blo 738327 740387 := bstep (se 1 (by rfl) ⟨555290, by rfl⟩ : syracuseStep 740387 = 1110581) B1110581
theorem B740403 : Blo 738327 740403 := bstep (se 1 (by rfl) ⟨555302, by rfl⟩ : syracuseStep 740403 = 1110605) B1110605
theorem B740419 : Blo 738327 740419 := bstep (se 1 (by rfl) ⟨555314, by rfl⟩ : syracuseStep 740419 = 1110629) B1110629
theorem B2804813 : Blo 738327 2804813 := bstep (se 3 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 2804813 = 1051805) B1051805
theorem B740435 : Blo 738327 740435 := bstep (se 1 (by rfl) ⟨555326, by rfl⟩ : syracuseStep 740435 = 1110653) B1110653
theorem B740451 : Blo 738327 740451 := bstep (se 1 (by rfl) ⟨555338, by rfl⟩ : syracuseStep 740451 = 1110677) B1110677
theorem B740467 : Blo 738327 740467 := bstep (se 1 (by rfl) ⟨555350, by rfl⟩ : syracuseStep 740467 = 1110701) B1110701
theorem B740483 : Blo 738327 740483 := bstep (se 1 (by rfl) ⟨555362, by rfl⟩ : syracuseStep 740483 = 1110725) B1110725
theorem B740499 : Blo 738327 740499 := bstep (se 1 (by rfl) ⟨555374, by rfl⟩ : syracuseStep 740499 = 1110749) B1110749
theorem B740515 : Blo 738327 740515 := bstep (se 1 (by rfl) ⟨555386, by rfl⟩ : syracuseStep 740515 = 1110773) B1110773
theorem B740531 : Blo 738327 740531 := bstep (se 1 (by rfl) ⟨555398, by rfl⟩ : syracuseStep 740531 = 1110797) B1110797
theorem B740547 : Blo 738327 740547 := bstep (se 1 (by rfl) ⟨555410, by rfl⟩ : syracuseStep 740547 = 1110821) B1110821
theorem B740563 : Blo 738327 740563 := bstep (se 1 (by rfl) ⟨555422, by rfl⟩ : syracuseStep 740563 = 1110845) B1110845
theorem B740579 : Blo 738327 740579 := bstep (se 1 (by rfl) ⟨555434, by rfl⟩ : syracuseStep 740579 = 1110869) B1110869
theorem B740595 : Blo 738327 740595 := bstep (se 1 (by rfl) ⟨555446, by rfl⟩ : syracuseStep 740595 = 1110893) B1110893
theorem B740611 : Blo 738327 740611 := bstep (se 1 (by rfl) ⟨555458, by rfl⟩ : syracuseStep 740611 = 1110917) B1110917
theorem B740627 : Blo 738327 740627 := bstep (se 1 (by rfl) ⟨555470, by rfl⟩ : syracuseStep 740627 = 1110941) B1110941
theorem B740643 : Blo 738327 740643 := bstep (se 1 (by rfl) ⟨555482, by rfl⟩ : syracuseStep 740643 = 1110965) B1110965
theorem B740659 : Blo 738327 740659 := bstep (se 1 (by rfl) ⟨555494, by rfl⟩ : syracuseStep 740659 = 1110989) B1110989
theorem B740675 : Blo 738327 740675 := bstep (se 1 (by rfl) ⟨555506, by rfl⟩ : syracuseStep 740675 = 1111013) B1111013
theorem B740691 : Blo 738327 740691 := bstep (se 1 (by rfl) ⟨555518, by rfl⟩ : syracuseStep 740691 = 1111037) B1111037
theorem B740707 : Blo 738327 740707 := bstep (se 1 (by rfl) ⟨555530, by rfl⟩ : syracuseStep 740707 = 1111061) B1111061
theorem B740723 : Blo 738327 740723 := bstep (se 1 (by rfl) ⟨555542, by rfl⟩ : syracuseStep 740723 = 1111085) B1111085
theorem B740739 : Blo 738327 740739 := bstep (se 1 (by rfl) ⟨555554, by rfl⟩ : syracuseStep 740739 = 1111109) B1111109
theorem B3165581 : Blo 738327 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B740755 : Blo 738327 740755 := bstep (se 1 (by rfl) ⟨555566, by rfl⟩ : syracuseStep 740755 = 1111133) B1111133
theorem B740771 : Blo 738327 740771 := bstep (se 1 (by rfl) ⟨555578, by rfl⟩ : syracuseStep 740771 = 1111157) B1111157
theorem B740787 : Blo 738327 740787 := bstep (se 1 (by rfl) ⟨555590, by rfl⟩ : syracuseStep 740787 = 1111181) B1111181
theorem B740803 : Blo 738327 740803 := bstep (se 1 (by rfl) ⟨555602, by rfl⟩ : syracuseStep 740803 = 1111205) B1111205
theorem B4214213 : Blo 738327 4214213 := bstep (se 4 (by rfl) ⟨395082, by rfl⟩ : syracuseStep 4214213 = 790165) B790165
theorem B740819 : Blo 738327 740819 := bstep (se 1 (by rfl) ⟨555614, by rfl⟩ : syracuseStep 740819 = 1111229) B1111229
theorem B740835 : Blo 738327 740835 := bstep (se 1 (by rfl) ⟨555626, by rfl⟩ : syracuseStep 740835 = 1111253) B1111253
theorem B2674147 : Blo 738327 2674147 := bstep (se 1 (by rfl) ⟨2005610, by rfl⟩ : syracuseStep 2674147 = 4011221) B4011221
theorem B740851 : Blo 738327 740851 := bstep (se 1 (by rfl) ⟨555638, by rfl⟩ : syracuseStep 740851 = 1111277) B1111277
theorem B740867 : Blo 738327 740867 := bstep (se 1 (by rfl) ⟨555650, by rfl⟩ : syracuseStep 740867 = 1111301) B1111301
theorem B740883 : Blo 738327 740883 := bstep (se 1 (by rfl) ⟨555662, by rfl⟩ : syracuseStep 740883 = 1111325) B1111325
theorem B740899 : Blo 738327 740899 := bstep (se 1 (by rfl) ⟨555674, by rfl⟩ : syracuseStep 740899 = 1111349) B1111349
theorem B740915 : Blo 738327 740915 := bstep (se 1 (by rfl) ⟨555686, by rfl⟩ : syracuseStep 740915 = 1111373) B1111373
theorem B740931 : Blo 738327 740931 := bstep (se 1 (by rfl) ⟨555698, by rfl⟩ : syracuseStep 740931 = 1111397) B1111397
theorem B740947 : Blo 738327 740947 := bstep (se 1 (by rfl) ⟨555710, by rfl⟩ : syracuseStep 740947 = 1111421) B1111421
theorem B740963 : Blo 738327 740963 := bstep (se 1 (by rfl) ⟨555722, by rfl⟩ : syracuseStep 740963 = 1111445) B1111445
theorem B740979 : Blo 738327 740979 := bstep (se 1 (by rfl) ⟨555734, by rfl⟩ : syracuseStep 740979 = 1111469) B1111469
theorem B740995 : Blo 738327 740995 := bstep (se 1 (by rfl) ⟨555746, by rfl⟩ : syracuseStep 740995 = 1111493) B1111493
theorem B741011 : Blo 738327 741011 := bstep (se 1 (by rfl) ⟨555758, by rfl⟩ : syracuseStep 741011 = 1111517) B1111517
theorem B741027 : Blo 738327 741027 := bstep (se 1 (by rfl) ⟨555770, by rfl⟩ : syracuseStep 741027 = 1111541) B1111541
theorem B937651 : Blo 738327 937651 := bstep (se 1 (by rfl) ⟨703238, by rfl⟩ : syracuseStep 937651 = 1406477) B1406477
theorem B741043 : Blo 738327 741043 := bstep (se 1 (by rfl) ⟨555782, by rfl⟩ : syracuseStep 741043 = 1111565) B1111565
theorem B741059 : Blo 738327 741059 := bstep (se 1 (by rfl) ⟨555794, by rfl⟩ : syracuseStep 741059 = 1111589) B1111589
theorem B741075 : Blo 738327 741075 := bstep (se 1 (by rfl) ⟨555806, by rfl⟩ : syracuseStep 741075 = 1111613) B1111613
theorem B741091 : Blo 738327 741091 := bstep (se 1 (by rfl) ⟨555818, by rfl⟩ : syracuseStep 741091 = 1111637) B1111637
theorem B741107 : Blo 738327 741107 := bstep (se 1 (by rfl) ⟨555830, by rfl⟩ : syracuseStep 741107 = 1111661) B1111661
theorem B741123 : Blo 738327 741123 := bstep (se 1 (by rfl) ⟨555842, by rfl⟩ : syracuseStep 741123 = 1111685) B1111685
theorem B937747 : Blo 738327 937747 := bstep (se 1 (by rfl) ⟨703310, by rfl⟩ : syracuseStep 937747 = 1406621) B1406621
theorem B741139 : Blo 738327 741139 := bstep (se 1 (by rfl) ⟨555854, by rfl⟩ : syracuseStep 741139 = 1111709) B1111709
theorem B741155 : Blo 738327 741155 := bstep (se 1 (by rfl) ⟨555866, by rfl⟩ : syracuseStep 741155 = 1111733) B1111733
theorem B741171 : Blo 738327 741171 := bstep (se 1 (by rfl) ⟨555878, by rfl⟩ : syracuseStep 741171 = 1111757) B1111757
theorem B741187 : Blo 738327 741187 := bstep (se 1 (by rfl) ⟨555890, by rfl⟩ : syracuseStep 741187 = 1111781) B1111781
theorem B741203 : Blo 738327 741203 := bstep (se 1 (by rfl) ⟨555902, by rfl⟩ : syracuseStep 741203 = 1111805) B1111805
theorem B741219 : Blo 738327 741219 := bstep (se 1 (by rfl) ⟨555914, by rfl⟩ : syracuseStep 741219 = 1111829) B1111829
theorem B2805617 : Blo 738327 2805617 := bstep (se 2 (by rfl) ⟨1052106, by rfl⟩ : syracuseStep 2805617 = 2104213) B2104213
theorem B741235 : Blo 738327 741235 := bstep (se 1 (by rfl) ⟨555926, by rfl⟩ : syracuseStep 741235 = 1111853) B1111853
theorem B741251 : Blo 738327 741251 := bstep (se 1 (by rfl) ⟨555938, by rfl⟩ : syracuseStep 741251 = 1111877) B1111877
theorem B741267 : Blo 738327 741267 := bstep (se 1 (by rfl) ⟨555950, by rfl⟩ : syracuseStep 741267 = 1111901) B1111901
theorem B741283 : Blo 738327 741283 := bstep (se 1 (by rfl) ⟨555962, by rfl⟩ : syracuseStep 741283 = 1111925) B1111925
theorem B741299 : Blo 738327 741299 := bstep (se 1 (by rfl) ⟨555974, by rfl⟩ : syracuseStep 741299 = 1111949) B1111949
theorem B741315 : Blo 738327 741315 := bstep (se 1 (by rfl) ⟨555986, by rfl⟩ : syracuseStep 741315 = 1111973) B1111973
theorem B741331 : Blo 738327 741331 := bstep (se 1 (by rfl) ⟨555998, by rfl⟩ : syracuseStep 741331 = 1111997) B1111997
theorem B741347 : Blo 738327 741347 := bstep (se 1 (by rfl) ⟨556010, by rfl⟩ : syracuseStep 741347 = 1112021) B1112021
theorem B741363 : Blo 738327 741363 := bstep (se 1 (by rfl) ⟨556022, by rfl⟩ : syracuseStep 741363 = 1112045) B1112045
theorem B741379 : Blo 738327 741379 := bstep (se 1 (by rfl) ⟨556034, by rfl⟩ : syracuseStep 741379 = 1112069) B1112069
theorem B741395 : Blo 738327 741395 := bstep (se 1 (by rfl) ⟨556046, by rfl⟩ : syracuseStep 741395 = 1112093) B1112093
theorem B741411 : Blo 738327 741411 := bstep (se 1 (by rfl) ⟨556058, by rfl⟩ : syracuseStep 741411 = 1112117) B1112117
theorem B741427 : Blo 738327 741427 := bstep (se 1 (by rfl) ⟨556070, by rfl⟩ : syracuseStep 741427 = 1112141) B1112141
theorem B741443 : Blo 738327 741443 := bstep (se 1 (by rfl) ⟨556082, by rfl⟩ : syracuseStep 741443 = 1112165) B1112165
theorem B741459 : Blo 738327 741459 := bstep (se 1 (by rfl) ⟨556094, by rfl⟩ : syracuseStep 741459 = 1112189) B1112189
theorem B741475 : Blo 738327 741475 := bstep (se 1 (by rfl) ⟨556106, by rfl⟩ : syracuseStep 741475 = 1112213) B1112213
theorem B3756131 : Blo 738327 3756131 := bstep (se 1 (by rfl) ⟨2817098, by rfl⟩ : syracuseStep 3756131 = 5634197) B5634197
theorem B741491 : Blo 738327 741491 := bstep (se 1 (by rfl) ⟨556118, by rfl⟩ : syracuseStep 741491 = 1112237) B1112237
theorem B741507 : Blo 738327 741507 := bstep (se 1 (by rfl) ⟨556130, by rfl⟩ : syracuseStep 741507 = 1112261) B1112261
theorem B741523 : Blo 738327 741523 := bstep (se 1 (by rfl) ⟨556142, by rfl⟩ : syracuseStep 741523 = 1112285) B1112285
theorem B741539 : Blo 738327 741539 := bstep (se 1 (by rfl) ⟨556154, by rfl⟩ : syracuseStep 741539 = 1112309) B1112309
theorem B741555 : Blo 738327 741555 := bstep (se 1 (by rfl) ⟨556166, by rfl⟩ : syracuseStep 741555 = 1112333) B1112333
theorem B741571 : Blo 738327 741571 := bstep (se 1 (by rfl) ⟨556178, by rfl⟩ : syracuseStep 741571 = 1112357) B1112357
theorem B741587 : Blo 738327 741587 := bstep (se 1 (by rfl) ⟨556190, by rfl⟩ : syracuseStep 741587 = 1112381) B1112381
theorem B741603 : Blo 738327 741603 := bstep (se 1 (by rfl) ⟨556202, by rfl⟩ : syracuseStep 741603 = 1112405) B1112405
theorem B741619 : Blo 738327 741619 := bstep (se 1 (by rfl) ⟨556214, by rfl⟩ : syracuseStep 741619 = 1112429) B1112429
theorem B938243 : Blo 738327 938243 := bstep (se 1 (by rfl) ⟨703682, by rfl⟩ : syracuseStep 938243 = 1407365) B1407365
theorem B741635 : Blo 738327 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B741651 : Blo 738327 741651 := bstep (se 1 (by rfl) ⟨556238, by rfl⟩ : syracuseStep 741651 = 1112477) B1112477
theorem B741667 : Blo 738327 741667 := bstep (se 1 (by rfl) ⟨556250, by rfl⟩ : syracuseStep 741667 = 1112501) B1112501
theorem B741683 : Blo 738327 741683 := bstep (se 1 (by rfl) ⟨556262, by rfl⟩ : syracuseStep 741683 = 1112525) B1112525
theorem B741699 : Blo 738327 741699 := bstep (se 1 (by rfl) ⟨556274, by rfl⟩ : syracuseStep 741699 = 1112549) B1112549
theorem B741715 : Blo 738327 741715 := bstep (se 1 (by rfl) ⟨556286, by rfl⟩ : syracuseStep 741715 = 1112573) B1112573
theorem B741731 : Blo 738327 741731 := bstep (se 1 (by rfl) ⟨556298, by rfl⟩ : syracuseStep 741731 = 1112597) B1112597
theorem B741747 : Blo 738327 741747 := bstep (se 1 (by rfl) ⟨556310, by rfl⟩ : syracuseStep 741747 = 1112621) B1112621
theorem B741763 : Blo 738327 741763 := bstep (se 1 (by rfl) ⟨556322, by rfl⟩ : syracuseStep 741763 = 1112645) B1112645
theorem B20304269 : Blo 738327 20304269 := bstep (se 3 (by rfl) ⟨3807050, by rfl⟩ : syracuseStep 20304269 = 7614101) B7614101
theorem B741779 : Blo 738327 741779 := bstep (se 1 (by rfl) ⟨556334, by rfl⟩ : syracuseStep 741779 = 1112669) B1112669
theorem B741795 : Blo 738327 741795 := bstep (se 1 (by rfl) ⟨556346, by rfl⟩ : syracuseStep 741795 = 1112693) B1112693
theorem B741811 : Blo 738327 741811 := bstep (se 1 (by rfl) ⟨556358, by rfl⟩ : syracuseStep 741811 = 1112717) B1112717
theorem B741827 : Blo 738327 741827 := bstep (se 1 (by rfl) ⟨556370, by rfl⟩ : syracuseStep 741827 = 1112741) B1112741
theorem B17125829 : Blo 738327 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B1266131 : Blo 738327 1266131 := bstep (se 1 (by rfl) ⟨949598, by rfl⟩ : syracuseStep 1266131 = 1899197) B1899197
theorem B741843 : Blo 738327 741843 := bstep (se 1 (by rfl) ⟨556382, by rfl⟩ : syracuseStep 741843 = 1112765) B1112765
theorem B741859 : Blo 738327 741859 := bstep (se 1 (by rfl) ⟨556394, by rfl⟩ : syracuseStep 741859 = 1112789) B1112789
theorem B741875 : Blo 738327 741875 := bstep (se 1 (by rfl) ⟨556406, by rfl⟩ : syracuseStep 741875 = 1112813) B1112813
theorem B741891 : Blo 738327 741891 := bstep (se 1 (by rfl) ⟨556418, by rfl⟩ : syracuseStep 741891 = 1112837) B1112837
theorem B2806285 : Blo 738327 2806285 := bstep (se 3 (by rfl) ⟨526178, by rfl⟩ : syracuseStep 2806285 = 1052357) B1052357
theorem B741907 : Blo 738327 741907 := bstep (se 1 (by rfl) ⟨556430, by rfl⟩ : syracuseStep 741907 = 1112861) B1112861
theorem B741923 : Blo 738327 741923 := bstep (se 1 (by rfl) ⟨556442, by rfl⟩ : syracuseStep 741923 = 1112885) B1112885
theorem B741939 : Blo 738327 741939 := bstep (se 1 (by rfl) ⟨556454, by rfl⟩ : syracuseStep 741939 = 1112909) B1112909
theorem B741955 : Blo 738327 741955 := bstep (se 1 (by rfl) ⟨556466, by rfl⟩ : syracuseStep 741955 = 1112933) B1112933
theorem B741971 : Blo 738327 741971 := bstep (se 1 (by rfl) ⟨556478, by rfl⟩ : syracuseStep 741971 = 1112957) B1112957
theorem B741987 : Blo 738327 741987 := bstep (se 1 (by rfl) ⟨556490, by rfl⟩ : syracuseStep 741987 = 1112981) B1112981
theorem B742003 : Blo 738327 742003 := bstep (se 1 (by rfl) ⟨556502, by rfl⟩ : syracuseStep 742003 = 1113005) B1113005
theorem B742019 : Blo 738327 742019 := bstep (se 1 (by rfl) ⟨556514, by rfl⟩ : syracuseStep 742019 = 1113029) B1113029
theorem B16011917 : Blo 738327 16011917 := bstep (se 3 (by rfl) ⟨3002234, by rfl⟩ : syracuseStep 16011917 = 6004469) B6004469
theorem B742035 : Blo 738327 742035 := bstep (se 1 (by rfl) ⟨556526, by rfl⟩ : syracuseStep 742035 = 1113053) B1113053
theorem B742051 : Blo 738327 742051 := bstep (se 1 (by rfl) ⟨556538, by rfl⟩ : syracuseStep 742051 = 1113077) B1113077
theorem B3166897 : Blo 738327 3166897 := bstep (se 2 (by rfl) ⟨1187586, by rfl⟩ : syracuseStep 3166897 = 2375173) B2375173
theorem B742067 : Blo 738327 742067 := bstep (se 1 (by rfl) ⟨556550, by rfl⟩ : syracuseStep 742067 = 1113101) B1113101
theorem B742083 : Blo 738327 742083 := bstep (se 1 (by rfl) ⟨556562, by rfl⟩ : syracuseStep 742083 = 1113125) B1113125
theorem B742099 : Blo 738327 742099 := bstep (se 1 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 742099 = 1113149) B1113149
theorem B742115 : Blo 738327 742115 := bstep (se 1 (by rfl) ⟨556586, by rfl⟩ : syracuseStep 742115 = 1113173) B1113173
theorem B742131 : Blo 738327 742131 := bstep (se 1 (by rfl) ⟨556598, by rfl⟩ : syracuseStep 742131 = 1113197) B1113197
theorem B742147 : Blo 738327 742147 := bstep (se 1 (by rfl) ⟨556610, by rfl⟩ : syracuseStep 742147 = 1113221) B1113221
theorem B742163 : Blo 738327 742163 := bstep (se 1 (by rfl) ⟨556622, by rfl⟩ : syracuseStep 742163 = 1113245) B1113245
theorem B742179 : Blo 738327 742179 := bstep (se 1 (by rfl) ⟨556634, by rfl⟩ : syracuseStep 742179 = 1113269) B1113269
theorem B742195 : Blo 738327 742195 := bstep (se 1 (by rfl) ⟨556646, by rfl⟩ : syracuseStep 742195 = 1113293) B1113293
theorem B1332035 : Blo 738327 1332035 := bstep (se 1 (by rfl) ⟨999026, by rfl⟩ : syracuseStep 1332035 = 1998053) B1998053
theorem B742211 : Blo 738327 742211 := bstep (se 1 (by rfl) ⟨556658, by rfl⟩ : syracuseStep 742211 = 1113317) B1113317
theorem B742227 : Blo 738327 742227 := bstep (se 1 (by rfl) ⟨556670, by rfl⟩ : syracuseStep 742227 = 1113341) B1113341
theorem B742243 : Blo 738327 742243 := bstep (se 1 (by rfl) ⟨556682, by rfl⟩ : syracuseStep 742243 = 1113365) B1113365
theorem B742259 : Blo 738327 742259 := bstep (se 1 (by rfl) ⟨556694, by rfl⟩ : syracuseStep 742259 = 1113389) B1113389
theorem B742275 : Blo 738327 742275 := bstep (se 1 (by rfl) ⟨556706, by rfl⟩ : syracuseStep 742275 = 1113413) B1113413
theorem B3756941 : Blo 738327 3756941 := bstep (se 3 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 3756941 = 1408853) B1408853
theorem B742291 : Blo 738327 742291 := bstep (se 1 (by rfl) ⟨556718, by rfl⟩ : syracuseStep 742291 = 1113437) B1113437
theorem B742307 : Blo 738327 742307 := bstep (se 1 (by rfl) ⟨556730, by rfl⟩ : syracuseStep 742307 = 1113461) B1113461
theorem B742323 : Blo 738327 742323 := bstep (se 1 (by rfl) ⟨556742, by rfl⟩ : syracuseStep 742323 = 1113485) B1113485
theorem B938947 : Blo 738327 938947 := bstep (se 1 (by rfl) ⟨704210, by rfl⟩ : syracuseStep 938947 = 1408421) B1408421
theorem B1922051 : Blo 738327 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B939043 : Blo 738327 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B2807075 : Blo 738327 2807075 := bstep (se 1 (by rfl) ⟨2105306, by rfl⟩ : syracuseStep 2807075 = 4210613) B4210613
theorem B5199173 : Blo 738327 5199173 := bstep (se 4 (by rfl) ⟨487422, by rfl⟩ : syracuseStep 5199173 = 974845) B974845
theorem B1922417 : Blo 738327 1922417 := bstep (se 2 (by rfl) ⟨720906, by rfl⟩ : syracuseStep 1922417 = 1441813) B1441813
theorem B8443277 : Blo 738327 8443277 := bstep (se 3 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 8443277 = 3166229) B3166229
theorem B1267555 : Blo 738327 1267555 := bstep (se 1 (by rfl) ⟨950666, by rfl⟩ : syracuseStep 1267555 = 1901333) B1901333
theorem B2807729 : Blo 738327 2807729 := bstep (se 2 (by rfl) ⟨1052898, by rfl⟩ : syracuseStep 2807729 = 2105797) B2105797
theorem B4741325 : Blo 738327 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B1333649 : Blo 738327 1333649 := bstep (se 2 (by rfl) ⟨500118, by rfl⟩ : syracuseStep 1333649 = 1000237) B1000237
theorem B1825187 : Blo 738327 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B4741553 : Blo 738327 4741553 := bstep (se 2 (by rfl) ⟨1778082, by rfl⟩ : syracuseStep 4741553 = 3556165) B3556165
theorem B1661489 : Blo 738327 1661489 := bstep (se 2 (by rfl) ⟨623058, by rfl⟩ : syracuseStep 1661489 = 1246117) B1246117
theorem B1661507 : Blo 738327 1661507 := bstep (se 1 (by rfl) ⟨1246130, by rfl⟩ : syracuseStep 1661507 = 2492261) B2492261
theorem B3005041 : Blo 738327 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B842435 : Blo 738327 842435 := bstep (se 1 (by rfl) ⟨631826, by rfl⟩ : syracuseStep 842435 = 1263653) B1263653
theorem B9263857 : Blo 738327 9263857 := bstep (se 2 (by rfl) ⟨3473946, by rfl⟩ : syracuseStep 9263857 = 6947893) B6947893
theorem B1661777 : Blo 738327 1661777 := bstep (se 2 (by rfl) ⟨623166, by rfl⟩ : syracuseStep 1661777 = 1246333) B1246333
theorem B1661795 : Blo 738327 1661795 := bstep (se 1 (by rfl) ⟨1246346, by rfl⟩ : syracuseStep 1661795 = 2492693) B2492693
theorem B1662065 : Blo 738327 1662065 := bstep (se 2 (by rfl) ⟨623274, by rfl⟩ : syracuseStep 1662065 = 1246549) B1246549
theorem B1662083 : Blo 738327 1662083 := bstep (se 1 (by rfl) ⟨1246562, by rfl⟩ : syracuseStep 1662083 = 2493125) B2493125
theorem B2809187 : Blo 738327 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B2809201 : Blo 738327 2809201 := bstep (se 2 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 2809201 = 2106901) B2106901
theorem B1662353 : Blo 738327 1662353 := bstep (se 2 (by rfl) ⟨623382, by rfl⟩ : syracuseStep 1662353 = 1246765) B1246765
theorem B1662371 : Blo 738327 1662371 := bstep (se 1 (by rfl) ⟨1246778, by rfl⟩ : syracuseStep 1662371 = 2493557) B2493557
theorem B4513229 : Blo 738327 4513229 := bstep (se 3 (by rfl) ⟨846230, by rfl⟩ : syracuseStep 4513229 = 1692461) B1692461
theorem B2252333 : Blo 738327 2252333 := bstep (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) B844625
theorem B3169955 : Blo 738327 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B1662641 : Blo 738327 1662641 := bstep (se 2 (by rfl) ⟨623490, by rfl⟩ : syracuseStep 1662641 = 1246981) B1246981
theorem B1662659 : Blo 738327 1662659 := bstep (se 1 (by rfl) ⟨1246994, by rfl⟩ : syracuseStep 1662659 = 2493989) B2493989
theorem B1498961 : Blo 738327 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B1498979 : Blo 738327 1498979 := bstep (se 1 (by rfl) ⟨1124234, by rfl⟩ : syracuseStep 1498979 = 2248469) B2248469
theorem B1662929 : Blo 738327 1662929 := bstep (se 2 (by rfl) ⟨623598, by rfl⟩ : syracuseStep 1662929 = 1247197) B1247197
theorem B1662947 : Blo 738327 1662947 := bstep (se 1 (by rfl) ⟨1247210, by rfl⟩ : syracuseStep 1662947 = 2494421) B2494421
theorem B2253005 : Blo 738327 2253005 := bstep (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) B844877
theorem B1663217 : Blo 738327 1663217 := bstep (se 2 (by rfl) ⟨623706, by rfl⟩ : syracuseStep 1663217 = 1247413) B1247413
theorem B8446193 : Blo 738327 8446193 := bstep (se 2 (by rfl) ⟨3167322, by rfl⟩ : syracuseStep 8446193 = 6334645) B6334645
theorem B1663235 : Blo 738327 1663235 := bstep (se 1 (by rfl) ⟨1247426, by rfl⟩ : syracuseStep 1663235 = 2494853) B2494853
theorem B1663505 : Blo 738327 1663505 := bstep (se 2 (by rfl) ⟨623814, by rfl⟩ : syracuseStep 1663505 = 1247629) B1247629
theorem B1663523 : Blo 738327 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B12182069 : Blo 738327 12182069 := bstep (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) B1142069
theorem B2810659 : Blo 738327 2810659 := bstep (se 1 (by rfl) ⟨2107994, by rfl⟩ : syracuseStep 2810659 = 4215989) B4215989
theorem B1663793 : Blo 738327 1663793 := bstep (se 2 (by rfl) ⟨623922, by rfl⟩ : syracuseStep 1663793 = 1247845) B1247845
theorem B1663811 : Blo 738327 1663811 := bstep (se 1 (by rfl) ⟨1247858, by rfl⟩ : syracuseStep 1663811 = 2495717) B2495717
theorem B1664081 : Blo 738327 1664081 := bstep (se 2 (by rfl) ⟨624030, by rfl⟩ : syracuseStep 1664081 = 1248061) B1248061
theorem B1664099 : Blo 738327 1664099 := bstep (se 1 (by rfl) ⟨1248074, by rfl⟩ : syracuseStep 1664099 = 2496149) B2496149
theorem B4220045 : Blo 738327 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B1402019 : Blo 738327 1402019 := bstep (se 1 (by rfl) ⟨1051514, by rfl⟩ : syracuseStep 1402019 = 2103029) B2103029
theorem B1664369 : Blo 738327 1664369 := bstep (se 2 (by rfl) ⟨624138, by rfl⟩ : syracuseStep 1664369 = 1248277) B1248277
theorem B1664387 : Blo 738327 1664387 := bstep (se 1 (by rfl) ⟨1248290, by rfl⟩ : syracuseStep 1664387 = 2496581) B2496581
theorem B10118641 : Blo 738327 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B1107491 : Blo 738327 1107491 := bstep (se 1 (by rfl) ⟨830618, by rfl⟩ : syracuseStep 1107491 = 1661237) B1661237
theorem B1107521 : Blo 738327 1107521 := bstep (se 2 (by rfl) ⟨415320, by rfl⟩ : syracuseStep 1107521 = 830641) B830641
theorem B1107539 : Blo 738327 1107539 := bstep (se 1 (by rfl) ⟨830654, by rfl⟩ : syracuseStep 1107539 = 1661309) B1661309
theorem B1107569 : Blo 738327 1107569 := bstep (se 2 (by rfl) ⟨415338, by rfl⟩ : syracuseStep 1107569 = 830677) B830677
theorem B1107587 : Blo 738327 1107587 := bstep (se 1 (by rfl) ⟨830690, by rfl⟩ : syracuseStep 1107587 = 1661381) B1661381
theorem B1664657 : Blo 738327 1664657 := bstep (se 2 (by rfl) ⟨624246, by rfl⟩ : syracuseStep 1664657 = 1248493) B1248493
theorem B1107617 : Blo 738327 1107617 := bstep (se 2 (by rfl) ⟨415356, by rfl⟩ : syracuseStep 1107617 = 830713) B830713
theorem B1664675 : Blo 738327 1664675 := bstep (se 1 (by rfl) ⟨1248506, by rfl⟩ : syracuseStep 1664675 = 2497013) B2497013
theorem B1107635 : Blo 738327 1107635 := bstep (se 1 (by rfl) ⟨830726, by rfl⟩ : syracuseStep 1107635 = 1661453) B1661453
theorem B1107665 : Blo 738327 1107665 := bstep (se 2 (by rfl) ⟨415374, by rfl⟩ : syracuseStep 1107665 = 830749) B830749
theorem B1107683 : Blo 738327 1107683 := bstep (se 1 (by rfl) ⟨830762, by rfl⟩ : syracuseStep 1107683 = 1661525) B1661525
theorem B1107713 : Blo 738327 1107713 := bstep (se 2 (by rfl) ⟨415392, by rfl⟩ : syracuseStep 1107713 = 830785) B830785
theorem B1107731 : Blo 738327 1107731 := bstep (se 1 (by rfl) ⟨830798, by rfl⟩ : syracuseStep 1107731 = 1661597) B1661597
theorem B1107761 : Blo 738327 1107761 := bstep (se 2 (by rfl) ⟨415410, by rfl⟩ : syracuseStep 1107761 = 830821) B830821
theorem B1337137 : Blo 738327 1337137 := bstep (se 2 (by rfl) ⟨501426, by rfl⟩ : syracuseStep 1337137 = 1002853) B1002853
theorem B1107779 : Blo 738327 1107779 := bstep (se 1 (by rfl) ⟨830834, by rfl⟩ : syracuseStep 1107779 = 1661669) B1661669
theorem B1107809 : Blo 738327 1107809 := bstep (se 2 (by rfl) ⟨415428, by rfl⟩ : syracuseStep 1107809 = 830857) B830857
theorem B1107827 : Blo 738327 1107827 := bstep (se 1 (by rfl) ⟨830870, by rfl⟩ : syracuseStep 1107827 = 1661741) B1661741
theorem B1107857 : Blo 738327 1107857 := bstep (se 2 (by rfl) ⟨415446, by rfl⟩ : syracuseStep 1107857 = 830893) B830893
theorem B1107875 : Blo 738327 1107875 := bstep (se 1 (by rfl) ⟨830906, by rfl⟩ : syracuseStep 1107875 = 1661813) B1661813
theorem B1664945 : Blo 738327 1664945 := bstep (se 2 (by rfl) ⟨624354, by rfl⟩ : syracuseStep 1664945 = 1248709) B1248709
theorem B1107905 : Blo 738327 1107905 := bstep (se 2 (by rfl) ⟨415464, by rfl⟩ : syracuseStep 1107905 = 830929) B830929
theorem B1664963 : Blo 738327 1664963 := bstep (se 1 (by rfl) ⟨1248722, by rfl⟩ : syracuseStep 1664963 = 2497445) B2497445
theorem B1140689 : Blo 738327 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B1107923 : Blo 738327 1107923 := bstep (se 1 (by rfl) ⟨830942, by rfl⟩ : syracuseStep 1107923 = 1661885) B1661885
theorem B1107953 : Blo 738327 1107953 := bstep (se 2 (by rfl) ⟨415482, by rfl⟩ : syracuseStep 1107953 = 830965) B830965
theorem B1894403 : Blo 738327 1894403 := bstep (se 1 (by rfl) ⟨1420802, by rfl⟩ : syracuseStep 1894403 = 2841605) B2841605
theorem B1107971 : Blo 738327 1107971 := bstep (se 1 (by rfl) ⟨830978, by rfl⟩ : syracuseStep 1107971 = 1661957) B1661957
theorem B1108001 : Blo 738327 1108001 := bstep (se 2 (by rfl) ⟨415500, by rfl⟩ : syracuseStep 1108001 = 831001) B831001
theorem B1402915 : Blo 738327 1402915 := bstep (se 1 (by rfl) ⟨1052186, by rfl⟩ : syracuseStep 1402915 = 2104373) B2104373
theorem B1108019 : Blo 738327 1108019 := bstep (se 1 (by rfl) ⟨831014, by rfl⟩ : syracuseStep 1108019 = 1662029) B1662029
theorem B1108049 : Blo 738327 1108049 := bstep (se 2 (by rfl) ⟨415518, by rfl⟩ : syracuseStep 1108049 = 831037) B831037
theorem B1108067 : Blo 738327 1108067 := bstep (se 1 (by rfl) ⟨831050, by rfl⟩ : syracuseStep 1108067 = 1662101) B1662101
theorem B1108097 : Blo 738327 1108097 := bstep (se 2 (by rfl) ⟨415536, by rfl⟩ : syracuseStep 1108097 = 831073) B831073
theorem B1108115 : Blo 738327 1108115 := bstep (se 1 (by rfl) ⟨831086, by rfl⟩ : syracuseStep 1108115 = 1662173) B1662173
theorem B1108145 : Blo 738327 1108145 := bstep (se 2 (by rfl) ⟨415554, by rfl⟩ : syracuseStep 1108145 = 831109) B831109
theorem B1108163 : Blo 738327 1108163 := bstep (se 1 (by rfl) ⟨831122, by rfl⟩ : syracuseStep 1108163 = 1662245) B1662245
theorem B1403075 : Blo 738327 1403075 := bstep (se 1 (by rfl) ⟨1052306, by rfl⟩ : syracuseStep 1403075 = 2104613) B2104613
theorem B1665233 : Blo 738327 1665233 := bstep (se 2 (by rfl) ⟨624462, by rfl⟩ : syracuseStep 1665233 = 1248925) B1248925
theorem B1108193 : Blo 738327 1108193 := bstep (se 2 (by rfl) ⟨415572, by rfl⟩ : syracuseStep 1108193 = 831145) B831145
theorem B1665251 : Blo 738327 1665251 := bstep (se 1 (by rfl) ⟨1248938, by rfl⟩ : syracuseStep 1665251 = 2497877) B2497877
theorem B1108211 : Blo 738327 1108211 := bstep (se 1 (by rfl) ⟨831158, by rfl⟩ : syracuseStep 1108211 = 1662317) B1662317
theorem B1108241 : Blo 738327 1108241 := bstep (se 2 (by rfl) ⟨415590, by rfl⟩ : syracuseStep 1108241 = 831181) B831181
theorem B1108259 : Blo 738327 1108259 := bstep (se 1 (by rfl) ⟨831194, by rfl⟩ : syracuseStep 1108259 = 1662389) B1662389
theorem B1108289 : Blo 738327 1108289 := bstep (se 2 (by rfl) ⟨415608, by rfl⟩ : syracuseStep 1108289 = 831217) B831217
theorem B1108307 : Blo 738327 1108307 := bstep (se 1 (by rfl) ⟨831230, by rfl⟩ : syracuseStep 1108307 = 1662461) B1662461
theorem B1108337 : Blo 738327 1108337 := bstep (se 2 (by rfl) ⟨415626, by rfl⟩ : syracuseStep 1108337 = 831253) B831253
theorem B1108355 : Blo 738327 1108355 := bstep (se 1 (by rfl) ⟨831266, by rfl⟩ : syracuseStep 1108355 = 1662533) B1662533
theorem B1108385 : Blo 738327 1108385 := bstep (se 2 (by rfl) ⟨415644, by rfl⟩ : syracuseStep 1108385 = 831289) B831289
theorem B1108403 : Blo 738327 1108403 := bstep (se 1 (by rfl) ⟨831302, by rfl⟩ : syracuseStep 1108403 = 1662605) B1662605
theorem B39053765 : Blo 738327 39053765 := bstep (se 4 (by rfl) ⟨3661290, by rfl⟩ : syracuseStep 39053765 = 7322581) B7322581
theorem B1108433 : Blo 738327 1108433 := bstep (se 2 (by rfl) ⟨415662, by rfl⟩ : syracuseStep 1108433 = 831325) B831325
theorem B1599953 : Blo 738327 1599953 := bstep (se 2 (by rfl) ⟨599982, by rfl⟩ : syracuseStep 1599953 = 1199965) B1199965
theorem B1108451 : Blo 738327 1108451 := bstep (se 1 (by rfl) ⟨831338, by rfl⟩ : syracuseStep 1108451 = 1662677) B1662677
theorem B1665521 : Blo 738327 1665521 := bstep (se 2 (by rfl) ⟨624570, by rfl⟩ : syracuseStep 1665521 = 1249141) B1249141
theorem B1108481 : Blo 738327 1108481 := bstep (se 2 (by rfl) ⟨415680, by rfl⟩ : syracuseStep 1108481 = 831361) B831361
theorem B1665539 : Blo 738327 1665539 := bstep (se 1 (by rfl) ⟨1249154, by rfl⟩ : syracuseStep 1665539 = 2498309) B2498309
theorem B1108499 : Blo 738327 1108499 := bstep (se 1 (by rfl) ⟨831374, by rfl⟩ : syracuseStep 1108499 = 1662749) B1662749
theorem B1108529 : Blo 738327 1108529 := bstep (se 2 (by rfl) ⟨415698, by rfl⟩ : syracuseStep 1108529 = 831397) B831397
theorem B1108547 : Blo 738327 1108547 := bstep (se 1 (by rfl) ⟨831410, by rfl⟩ : syracuseStep 1108547 = 1662821) B1662821
theorem B1108577 : Blo 738327 1108577 := bstep (se 2 (by rfl) ⟨415716, by rfl⟩ : syracuseStep 1108577 = 831433) B831433
theorem B1108595 : Blo 738327 1108595 := bstep (se 1 (by rfl) ⟨831446, by rfl⟩ : syracuseStep 1108595 = 1662893) B1662893
theorem B1108625 : Blo 738327 1108625 := bstep (se 2 (by rfl) ⟨415734, by rfl⟩ : syracuseStep 1108625 = 831469) B831469
theorem B1108643 : Blo 738327 1108643 := bstep (se 1 (by rfl) ⟨831482, by rfl⟩ : syracuseStep 1108643 = 1662965) B1662965
theorem B1600163 : Blo 738327 1600163 := bstep (se 1 (by rfl) ⟨1200122, by rfl⟩ : syracuseStep 1600163 = 2400245) B2400245
theorem B1108673 : Blo 738327 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B1108691 : Blo 738327 1108691 := bstep (se 1 (by rfl) ⟨831518, by rfl⟩ : syracuseStep 1108691 = 1663037) B1663037
theorem B1108721 : Blo 738327 1108721 := bstep (se 2 (by rfl) ⟨415770, by rfl⟩ : syracuseStep 1108721 = 831541) B831541
theorem B1108739 : Blo 738327 1108739 := bstep (se 1 (by rfl) ⟨831554, by rfl⟩ : syracuseStep 1108739 = 1663109) B1663109
theorem B1665809 : Blo 738327 1665809 := bstep (se 2 (by rfl) ⟨624678, by rfl⟩ : syracuseStep 1665809 = 1249357) B1249357
theorem B1108769 : Blo 738327 1108769 := bstep (se 2 (by rfl) ⟨415788, by rfl⟩ : syracuseStep 1108769 = 831577) B831577
theorem B1665827 : Blo 738327 1665827 := bstep (se 1 (by rfl) ⟨1249370, by rfl⟩ : syracuseStep 1665827 = 2498741) B2498741
theorem B1108787 : Blo 738327 1108787 := bstep (se 1 (by rfl) ⟨831590, by rfl⟩ : syracuseStep 1108787 = 1663181) B1663181
theorem B1108817 : Blo 738327 1108817 := bstep (se 2 (by rfl) ⟨415806, by rfl⟩ : syracuseStep 1108817 = 831613) B831613
theorem B1108835 : Blo 738327 1108835 := bstep (se 1 (by rfl) ⟨831626, by rfl⟩ : syracuseStep 1108835 = 1663253) B1663253
theorem B1108865 : Blo 738327 1108865 := bstep (se 2 (by rfl) ⟨415824, by rfl⟩ : syracuseStep 1108865 = 831649) B831649
theorem B1108883 : Blo 738327 1108883 := bstep (se 1 (by rfl) ⟨831662, by rfl⟩ : syracuseStep 1108883 = 1663325) B1663325
theorem B1108913 : Blo 738327 1108913 := bstep (se 2 (by rfl) ⟨415842, by rfl⟩ : syracuseStep 1108913 = 831685) B831685
theorem B1108931 : Blo 738327 1108931 := bstep (se 1 (by rfl) ⟨831698, by rfl⟩ : syracuseStep 1108931 = 1663397) B1663397
theorem B2812877 : Blo 738327 2812877 := bstep (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) B1054829
theorem B1108961 : Blo 738327 1108961 := bstep (se 2 (by rfl) ⟨415860, by rfl⟩ : syracuseStep 1108961 = 831721) B831721
theorem B1108979 : Blo 738327 1108979 := bstep (se 1 (by rfl) ⟨831734, by rfl⟩ : syracuseStep 1108979 = 1663469) B1663469
theorem B1109009 : Blo 738327 1109009 := bstep (se 2 (by rfl) ⟨415878, by rfl⟩ : syracuseStep 1109009 = 831757) B831757
theorem B1109027 : Blo 738327 1109027 := bstep (se 1 (by rfl) ⟨831770, by rfl⟩ : syracuseStep 1109027 = 1663541) B1663541
theorem B1666097 : Blo 738327 1666097 := bstep (se 2 (by rfl) ⟨624786, by rfl⟩ : syracuseStep 1666097 = 1249573) B1249573
theorem B1109057 : Blo 738327 1109057 := bstep (se 2 (by rfl) ⟨415896, by rfl⟩ : syracuseStep 1109057 = 831793) B831793
theorem B1666115 : Blo 738327 1666115 := bstep (se 1 (by rfl) ⟨1249586, by rfl⟩ : syracuseStep 1666115 = 2499173) B2499173
theorem B1109075 : Blo 738327 1109075 := bstep (se 1 (by rfl) ⟨831806, by rfl⟩ : syracuseStep 1109075 = 1663613) B1663613
theorem B3206243 : Blo 738327 3206243 := bstep (se 1 (by rfl) ⟨2404682, by rfl⟩ : syracuseStep 3206243 = 4809365) B4809365
theorem B1109105 : Blo 738327 1109105 := bstep (se 2 (by rfl) ⟨415914, by rfl⟩ : syracuseStep 1109105 = 831829) B831829
theorem B1109123 : Blo 738327 1109123 := bstep (se 1 (by rfl) ⟨831842, by rfl⟩ : syracuseStep 1109123 = 1663685) B1663685
theorem B1109153 : Blo 738327 1109153 := bstep (se 2 (by rfl) ⟨415932, by rfl⟩ : syracuseStep 1109153 = 831865) B831865
theorem B1109171 : Blo 738327 1109171 := bstep (se 1 (by rfl) ⟨831878, by rfl⟩ : syracuseStep 1109171 = 1663757) B1663757
theorem B1109201 : Blo 738327 1109201 := bstep (se 2 (by rfl) ⟨415950, by rfl⟩ : syracuseStep 1109201 = 831901) B831901
theorem B1109219 : Blo 738327 1109219 := bstep (se 1 (by rfl) ⟨831914, by rfl⟩ : syracuseStep 1109219 = 1663829) B1663829
theorem B1404145 : Blo 738327 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B9268465 : Blo 738327 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B1109249 : Blo 738327 1109249 := bstep (se 2 (by rfl) ⟨415968, by rfl⟩ : syracuseStep 1109249 = 831937) B831937
theorem B1109267 : Blo 738327 1109267 := bstep (se 1 (by rfl) ⟨831950, by rfl⟩ : syracuseStep 1109267 = 1663901) B1663901
theorem B1109297 : Blo 738327 1109297 := bstep (se 2 (by rfl) ⟨415986, by rfl⟩ : syracuseStep 1109297 = 831973) B831973
theorem B1109315 : Blo 738327 1109315 := bstep (se 1 (by rfl) ⟨831986, by rfl⟩ : syracuseStep 1109315 = 1663973) B1663973
theorem B4222277 : Blo 738327 4222277 := bstep (se 4 (by rfl) ⟨395838, by rfl⟩ : syracuseStep 4222277 = 791677) B791677
theorem B1666385 : Blo 738327 1666385 := bstep (se 2 (by rfl) ⟨624894, by rfl⟩ : syracuseStep 1666385 = 1249789) B1249789
theorem B1109345 : Blo 738327 1109345 := bstep (se 2 (by rfl) ⟨416004, by rfl⟩ : syracuseStep 1109345 = 832009) B832009
theorem B1666403 : Blo 738327 1666403 := bstep (se 1 (by rfl) ⟨1249802, by rfl⟩ : syracuseStep 1666403 = 2499605) B2499605
theorem B1109363 : Blo 738327 1109363 := bstep (se 1 (by rfl) ⟨832022, by rfl⟩ : syracuseStep 1109363 = 1664045) B1664045
theorem B1109393 : Blo 738327 1109393 := bstep (se 2 (by rfl) ⟨416022, by rfl⟩ : syracuseStep 1109393 = 832045) B832045
theorem B1109411 : Blo 738327 1109411 := bstep (se 1 (by rfl) ⟨832058, by rfl⟩ : syracuseStep 1109411 = 1664117) B1664117
theorem B1109441 : Blo 738327 1109441 := bstep (se 2 (by rfl) ⟨416040, by rfl⟩ : syracuseStep 1109441 = 832081) B832081
theorem B1109459 : Blo 738327 1109459 := bstep (se 1 (by rfl) ⟨832094, by rfl⟩ : syracuseStep 1109459 = 1664189) B1664189
theorem B1109489 : Blo 738327 1109489 := bstep (se 2 (by rfl) ⟨416058, by rfl⟩ : syracuseStep 1109489 = 832117) B832117
theorem B1109507 : Blo 738327 1109507 := bstep (se 1 (by rfl) ⟨832130, by rfl⟩ : syracuseStep 1109507 = 1664261) B1664261
theorem B1109537 : Blo 738327 1109537 := bstep (se 2 (by rfl) ⟨416076, by rfl⟩ : syracuseStep 1109537 = 832153) B832153
theorem B1109555 : Blo 738327 1109555 := bstep (se 1 (by rfl) ⟨832166, by rfl⟩ : syracuseStep 1109555 = 1664333) B1664333
theorem B1109585 : Blo 738327 1109585 := bstep (se 2 (by rfl) ⟨416094, by rfl⟩ : syracuseStep 1109585 = 832189) B832189
theorem B1109603 : Blo 738327 1109603 := bstep (se 1 (by rfl) ⟨832202, by rfl⟩ : syracuseStep 1109603 = 1664405) B1664405
theorem B1666673 : Blo 738327 1666673 := bstep (se 2 (by rfl) ⟨625002, by rfl⟩ : syracuseStep 1666673 = 1250005) B1250005
theorem B1109633 : Blo 738327 1109633 := bstep (se 2 (by rfl) ⟨416112, by rfl⟩ : syracuseStep 1109633 = 832225) B832225
theorem B1666691 : Blo 738327 1666691 := bstep (se 1 (by rfl) ⟨1250018, by rfl⟩ : syracuseStep 1666691 = 2500037) B2500037
theorem B1109651 : Blo 738327 1109651 := bstep (se 1 (by rfl) ⟨832238, by rfl⟩ : syracuseStep 1109651 = 1664477) B1664477
theorem B1109681 : Blo 738327 1109681 := bstep (se 2 (by rfl) ⟨416130, by rfl⟩ : syracuseStep 1109681 = 832261) B832261
theorem B1109699 : Blo 738327 1109699 := bstep (se 1 (by rfl) ⟨832274, by rfl⟩ : syracuseStep 1109699 = 1664549) B1664549
theorem B1109729 : Blo 738327 1109729 := bstep (se 2 (by rfl) ⟨416148, by rfl⟩ : syracuseStep 1109729 = 832297) B832297
theorem B1109747 : Blo 738327 1109747 := bstep (se 1 (by rfl) ⟨832310, by rfl⟩ : syracuseStep 1109747 = 1664621) B1664621
theorem B1109777 : Blo 738327 1109777 := bstep (se 2 (by rfl) ⟨416166, by rfl⟩ : syracuseStep 1109777 = 832333) B832333
theorem B1109795 : Blo 738327 1109795 := bstep (se 1 (by rfl) ⟨832346, by rfl⟩ : syracuseStep 1109795 = 1664693) B1664693
theorem B1109825 : Blo 738327 1109825 := bstep (se 2 (by rfl) ⟨416184, by rfl⟩ : syracuseStep 1109825 = 832369) B832369
theorem B5074757 : Blo 738327 5074757 := bstep (se 4 (by rfl) ⟨475758, by rfl⟩ : syracuseStep 5074757 = 951517) B951517
theorem B3993421 : Blo 738327 3993421 := bstep (se 3 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 3993421 = 1497533) B1497533
theorem B1109843 : Blo 738327 1109843 := bstep (se 1 (by rfl) ⟨832382, by rfl⟩ : syracuseStep 1109843 = 1664765) B1664765
theorem B1109873 : Blo 738327 1109873 := bstep (se 2 (by rfl) ⟨416202, by rfl⟩ : syracuseStep 1109873 = 832405) B832405
theorem B1109891 : Blo 738327 1109891 := bstep (se 1 (by rfl) ⟨832418, by rfl⟩ : syracuseStep 1109891 = 1664837) B1664837
theorem B1666961 : Blo 738327 1666961 := bstep (se 2 (by rfl) ⟨625110, by rfl⟩ : syracuseStep 1666961 = 1250221) B1250221
theorem B1109921 : Blo 738327 1109921 := bstep (se 2 (by rfl) ⟨416220, by rfl⟩ : syracuseStep 1109921 = 832441) B832441
theorem B1666979 : Blo 738327 1666979 := bstep (se 1 (by rfl) ⟨1250234, by rfl⟩ : syracuseStep 1666979 = 2500469) B2500469
theorem B1109939 : Blo 738327 1109939 := bstep (se 1 (by rfl) ⟨832454, by rfl⟩ : syracuseStep 1109939 = 1664909) B1664909
theorem B1109969 : Blo 738327 1109969 := bstep (se 2 (by rfl) ⟨416238, by rfl⟩ : syracuseStep 1109969 = 832477) B832477
theorem B1109987 : Blo 738327 1109987 := bstep (se 1 (by rfl) ⟨832490, by rfl⟩ : syracuseStep 1109987 = 1664981) B1664981
theorem B8024035 : Blo 738327 8024035 := bstep (se 1 (by rfl) ⟨6018026, by rfl⟩ : syracuseStep 8024035 = 12036053) B12036053
theorem B4222961 : Blo 738327 4222961 := bstep (se 2 (by rfl) ⟨1583610, by rfl⟩ : syracuseStep 4222961 = 3167221) B3167221
theorem B1110017 : Blo 738327 1110017 := bstep (se 2 (by rfl) ⟨416256, by rfl⟩ : syracuseStep 1110017 = 832513) B832513
theorem B1110035 : Blo 738327 1110035 := bstep (se 1 (by rfl) ⟨832526, by rfl⟩ : syracuseStep 1110035 = 1665053) B1665053
theorem B1110065 : Blo 738327 1110065 := bstep (se 2 (by rfl) ⟨416274, by rfl⟩ : syracuseStep 1110065 = 832549) B832549
theorem B1110083 : Blo 738327 1110083 := bstep (se 1 (by rfl) ⟨832562, by rfl⟩ : syracuseStep 1110083 = 1665125) B1665125
theorem B1110113 : Blo 738327 1110113 := bstep (se 2 (by rfl) ⟨416292, by rfl⟩ : syracuseStep 1110113 = 832585) B832585
theorem B1110131 : Blo 738327 1110131 := bstep (se 1 (by rfl) ⟨832598, by rfl⟩ : syracuseStep 1110131 = 1665197) B1665197
theorem B1110161 : Blo 738327 1110161 := bstep (se 2 (by rfl) ⟨416310, by rfl⟩ : syracuseStep 1110161 = 832621) B832621
theorem B1110179 : Blo 738327 1110179 := bstep (se 1 (by rfl) ⟨832634, by rfl⟩ : syracuseStep 1110179 = 1665269) B1665269
theorem B1667249 : Blo 738327 1667249 := bstep (se 2 (by rfl) ⟨625218, by rfl⟩ : syracuseStep 1667249 = 1250437) B1250437
theorem B1110209 : Blo 738327 1110209 := bstep (se 2 (by rfl) ⟨416328, by rfl⟩ : syracuseStep 1110209 = 832657) B832657
theorem B1667267 : Blo 738327 1667267 := bstep (se 1 (by rfl) ⟨1250450, by rfl⟩ : syracuseStep 1667267 = 2500901) B2500901
theorem B1110227 : Blo 738327 1110227 := bstep (se 1 (by rfl) ⟨832670, by rfl⟩ : syracuseStep 1110227 = 1665341) B1665341
theorem B4878563 : Blo 738327 4878563 := bstep (se 1 (by rfl) ⟨3658922, by rfl⟩ : syracuseStep 4878563 = 7317845) B7317845
theorem B1110257 : Blo 738327 1110257 := bstep (se 2 (by rfl) ⟨416346, by rfl⟩ : syracuseStep 1110257 = 832693) B832693
theorem B1110275 : Blo 738327 1110275 := bstep (se 1 (by rfl) ⟨832706, by rfl⟩ : syracuseStep 1110275 = 1665413) B1665413
theorem B1405201 : Blo 738327 1405201 := bstep (se 2 (by rfl) ⟨526950, by rfl⟩ : syracuseStep 1405201 = 1053901) B1053901
theorem B1110305 : Blo 738327 1110305 := bstep (se 2 (by rfl) ⟨416364, by rfl⟩ : syracuseStep 1110305 = 832729) B832729
theorem B1110323 : Blo 738327 1110323 := bstep (se 1 (by rfl) ⟨832742, by rfl⟩ : syracuseStep 1110323 = 1665485) B1665485
theorem B1110353 : Blo 738327 1110353 := bstep (se 2 (by rfl) ⟨416382, by rfl⟩ : syracuseStep 1110353 = 832765) B832765
theorem B1110371 : Blo 738327 1110371 := bstep (se 1 (by rfl) ⟨832778, by rfl⟩ : syracuseStep 1110371 = 1665557) B1665557
theorem B1110401 : Blo 738327 1110401 := bstep (se 2 (by rfl) ⟨416400, by rfl⟩ : syracuseStep 1110401 = 832801) B832801
theorem B1110419 : Blo 738327 1110419 := bstep (se 1 (by rfl) ⟨832814, by rfl⟩ : syracuseStep 1110419 = 1665629) B1665629
theorem B1110449 : Blo 738327 1110449 := bstep (se 2 (by rfl) ⟨416418, by rfl⟩ : syracuseStep 1110449 = 832837) B832837
theorem B1110467 : Blo 738327 1110467 := bstep (se 1 (by rfl) ⟨832850, by rfl⟩ : syracuseStep 1110467 = 1665701) B1665701
theorem B1667537 : Blo 738327 1667537 := bstep (se 2 (by rfl) ⟨625326, by rfl⟩ : syracuseStep 1667537 = 1250653) B1250653
theorem B1110497 : Blo 738327 1110497 := bstep (se 2 (by rfl) ⟨416436, by rfl⟩ : syracuseStep 1110497 = 832873) B832873
theorem B1667555 : Blo 738327 1667555 := bstep (se 1 (by rfl) ⟨1250666, by rfl⟩ : syracuseStep 1667555 = 2501333) B2501333
theorem B1110515 : Blo 738327 1110515 := bstep (se 1 (by rfl) ⟨832886, by rfl⟩ : syracuseStep 1110515 = 1665773) B1665773
theorem B1110545 : Blo 738327 1110545 := bstep (se 2 (by rfl) ⟨416454, by rfl⟩ : syracuseStep 1110545 = 832909) B832909
theorem B1110563 : Blo 738327 1110563 := bstep (se 1 (by rfl) ⟨832922, by rfl⟩ : syracuseStep 1110563 = 1665845) B1665845
theorem B1110593 : Blo 738327 1110593 := bstep (se 2 (by rfl) ⟨416472, by rfl⟩ : syracuseStep 1110593 = 832945) B832945
theorem B1110611 : Blo 738327 1110611 := bstep (se 1 (by rfl) ⟨832958, by rfl⟩ : syracuseStep 1110611 = 1665917) B1665917
theorem B1110641 : Blo 738327 1110641 := bstep (se 2 (by rfl) ⟨416490, by rfl⟩ : syracuseStep 1110641 = 832981) B832981
theorem B1110659 : Blo 738327 1110659 := bstep (se 1 (by rfl) ⟨832994, by rfl⟩ : syracuseStep 1110659 = 1665989) B1665989
theorem B4747909 : Blo 738327 4747909 := bstep (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) B890233
theorem B1110689 : Blo 738327 1110689 := bstep (se 2 (by rfl) ⟨416508, by rfl⟩ : syracuseStep 1110689 = 833017) B833017
theorem B1405603 : Blo 738327 1405603 := bstep (se 1 (by rfl) ⟨1054202, by rfl⟩ : syracuseStep 1405603 = 2108405) B2108405
theorem B750259 : Blo 738327 750259 := bstep (se 1 (by rfl) ⟨562694, by rfl⟩ : syracuseStep 750259 = 1125389) B1125389
theorem B1110707 : Blo 738327 1110707 := bstep (se 1 (by rfl) ⟨833030, by rfl⟩ : syracuseStep 1110707 = 1666061) B1666061
theorem B1405649 : Blo 738327 1405649 := bstep (se 2 (by rfl) ⟨527118, by rfl⟩ : syracuseStep 1405649 = 1054237) B1054237
theorem B1110737 : Blo 738327 1110737 := bstep (se 2 (by rfl) ⟨416526, by rfl⟩ : syracuseStep 1110737 = 833053) B833053
theorem B1110755 : Blo 738327 1110755 := bstep (se 1 (by rfl) ⟨833066, by rfl⟩ : syracuseStep 1110755 = 1666133) B1666133
theorem B5632739 : Blo 738327 5632739 := bstep (se 1 (by rfl) ⟨4224554, by rfl⟩ : syracuseStep 5632739 = 8449109) B8449109
theorem B1667825 : Blo 738327 1667825 := bstep (se 2 (by rfl) ⟨625434, by rfl⟩ : syracuseStep 1667825 = 1250869) B1250869
theorem B1110785 : Blo 738327 1110785 := bstep (se 2 (by rfl) ⟨416544, by rfl⟩ : syracuseStep 1110785 = 833089) B833089
theorem B1667843 : Blo 738327 1667843 := bstep (se 1 (by rfl) ⟨1250882, by rfl⟩ : syracuseStep 1667843 = 2501765) B2501765
theorem B3994373 : Blo 738327 3994373 := bstep (se 4 (by rfl) ⟨374472, by rfl⟩ : syracuseStep 3994373 = 748945) B748945
theorem B1110803 : Blo 738327 1110803 := bstep (se 1 (by rfl) ⟨833102, by rfl⟩ : syracuseStep 1110803 = 1666205) B1666205
theorem B1110833 : Blo 738327 1110833 := bstep (se 2 (by rfl) ⟨416562, by rfl⟩ : syracuseStep 1110833 = 833125) B833125
theorem B1110851 : Blo 738327 1110851 := bstep (se 1 (by rfl) ⟨833138, by rfl⟩ : syracuseStep 1110851 = 1666277) B1666277
theorem B1110881 : Blo 738327 1110881 := bstep (se 2 (by rfl) ⟨416580, by rfl⟩ : syracuseStep 1110881 = 833161) B833161
theorem B12645233 : Blo 738327 12645233 := bstep (se 2 (by rfl) ⟨4741962, by rfl⟩ : syracuseStep 12645233 = 9483925) B9483925
theorem B1110899 : Blo 738327 1110899 := bstep (se 1 (by rfl) ⟨833174, by rfl⟩ : syracuseStep 1110899 = 1666349) B1666349
theorem B1110929 : Blo 738327 1110929 := bstep (se 2 (by rfl) ⟨416598, by rfl⟩ : syracuseStep 1110929 = 833197) B833197
theorem B1110947 : Blo 738327 1110947 := bstep (se 1 (by rfl) ⟨833210, by rfl⟩ : syracuseStep 1110947 = 1666421) B1666421
theorem B1110977 : Blo 738327 1110977 := bstep (se 2 (by rfl) ⟨416616, by rfl⟩ : syracuseStep 1110977 = 833233) B833233
theorem B5075909 : Blo 738327 5075909 := bstep (se 4 (by rfl) ⟨475866, by rfl⟩ : syracuseStep 5075909 = 951733) B951733
theorem B1110995 : Blo 738327 1110995 := bstep (se 1 (by rfl) ⟨833246, by rfl⟩ : syracuseStep 1110995 = 1666493) B1666493
theorem B1405937 : Blo 738327 1405937 := bstep (se 2 (by rfl) ⟨527226, by rfl⟩ : syracuseStep 1405937 = 1054453) B1054453
theorem B1111025 : Blo 738327 1111025 := bstep (se 2 (by rfl) ⟨416634, by rfl⟩ : syracuseStep 1111025 = 833269) B833269
theorem B1111043 : Blo 738327 1111043 := bstep (se 1 (by rfl) ⟨833282, by rfl⟩ : syracuseStep 1111043 = 1666565) B1666565
theorem B1668113 : Blo 738327 1668113 := bstep (se 2 (by rfl) ⟨625542, by rfl⟩ : syracuseStep 1668113 = 1251085) B1251085
theorem B1111073 : Blo 738327 1111073 := bstep (se 2 (by rfl) ⟨416652, by rfl⟩ : syracuseStep 1111073 = 833305) B833305
theorem B1668131 : Blo 738327 1668131 := bstep (se 1 (by rfl) ⟨1251098, by rfl⟩ : syracuseStep 1668131 = 2502197) B2502197
theorem B1111091 : Blo 738327 1111091 := bstep (se 1 (by rfl) ⟨833318, by rfl⟩ : syracuseStep 1111091 = 1666637) B1666637
theorem B1111121 : Blo 738327 1111121 := bstep (se 2 (by rfl) ⟨416670, by rfl⟩ : syracuseStep 1111121 = 833341) B833341
theorem B1504337 : Blo 738327 1504337 := bstep (se 2 (by rfl) ⟨564126, by rfl⟩ : syracuseStep 1504337 = 1128253) B1128253
theorem B1111139 : Blo 738327 1111139 := bstep (se 1 (by rfl) ⟨833354, by rfl⟩ : syracuseStep 1111139 = 1666709) B1666709
theorem B1111169 : Blo 738327 1111169 := bstep (se 2 (by rfl) ⟨416688, by rfl⟩ : syracuseStep 1111169 = 833377) B833377
theorem B7206029 : Blo 738327 7206029 := bstep (se 3 (by rfl) ⟨1351130, by rfl⟩ : syracuseStep 7206029 = 2702261) B2702261
theorem B1111187 : Blo 738327 1111187 := bstep (se 1 (by rfl) ⟨833390, by rfl⟩ : syracuseStep 1111187 = 1666781) B1666781
theorem B1111217 : Blo 738327 1111217 := bstep (se 2 (by rfl) ⟨416706, by rfl⟩ : syracuseStep 1111217 = 833413) B833413
theorem B1111235 : Blo 738327 1111235 := bstep (se 1 (by rfl) ⟨833426, by rfl⟩ : syracuseStep 1111235 = 1666853) B1666853
theorem B1111265 : Blo 738327 1111265 := bstep (se 2 (by rfl) ⟨416724, by rfl⟩ : syracuseStep 1111265 = 833449) B833449
theorem B1111283 : Blo 738327 1111283 := bstep (se 1 (by rfl) ⟨833462, by rfl⟩ : syracuseStep 1111283 = 1666925) B1666925
theorem B1111313 : Blo 738327 1111313 := bstep (se 2 (by rfl) ⟨416742, by rfl⟩ : syracuseStep 1111313 = 833485) B833485
theorem B1111331 : Blo 738327 1111331 := bstep (se 1 (by rfl) ⟨833498, by rfl⟩ : syracuseStep 1111331 = 1666997) B1666997
theorem B1668401 : Blo 738327 1668401 := bstep (se 2 (by rfl) ⟨625650, by rfl⟩ : syracuseStep 1668401 = 1251301) B1251301
theorem B1111361 : Blo 738327 1111361 := bstep (se 2 (by rfl) ⟨416760, by rfl⟩ : syracuseStep 1111361 = 833521) B833521
theorem B1668419 : Blo 738327 1668419 := bstep (se 1 (by rfl) ⟨1251314, by rfl⟩ : syracuseStep 1668419 = 2502629) B2502629
theorem B1111379 : Blo 738327 1111379 := bstep (se 1 (by rfl) ⟨833534, by rfl⟩ : syracuseStep 1111379 = 1667069) B1667069
theorem B1111409 : Blo 738327 1111409 := bstep (se 2 (by rfl) ⟨416778, by rfl⟩ : syracuseStep 1111409 = 833557) B833557
theorem B1111427 : Blo 738327 1111427 := bstep (se 1 (by rfl) ⟨833570, by rfl⟩ : syracuseStep 1111427 = 1667141) B1667141
theorem B1111457 : Blo 738327 1111457 := bstep (se 2 (by rfl) ⟨416796, by rfl⟩ : syracuseStep 1111457 = 833593) B833593
theorem B4224419 : Blo 738327 4224419 := bstep (se 1 (by rfl) ⟨3168314, by rfl⟩ : syracuseStep 4224419 = 6336629) B6336629
theorem B1111475 : Blo 738327 1111475 := bstep (se 1 (by rfl) ⟨833606, by rfl⟩ : syracuseStep 1111475 = 1667213) B1667213
theorem B1111505 : Blo 738327 1111505 := bstep (se 2 (by rfl) ⟨416814, by rfl⟩ : syracuseStep 1111505 = 833629) B833629
theorem B1111523 : Blo 738327 1111523 := bstep (se 1 (by rfl) ⟨833642, by rfl⟩ : syracuseStep 1111523 = 1667285) B1667285
theorem B1111553 : Blo 738327 1111553 := bstep (se 2 (by rfl) ⟨416832, by rfl⟩ : syracuseStep 1111553 = 833665) B833665
theorem B1996301 : Blo 738327 1996301 := bstep (se 3 (by rfl) ⟨374306, by rfl⟩ : syracuseStep 1996301 = 748613) B748613
theorem B1111571 : Blo 738327 1111571 := bstep (se 1 (by rfl) ⟨833678, by rfl⟩ : syracuseStep 1111571 = 1667357) B1667357
theorem B1111601 : Blo 738327 1111601 := bstep (se 2 (by rfl) ⟨416850, by rfl⟩ : syracuseStep 1111601 = 833701) B833701
theorem B1111619 : Blo 738327 1111619 := bstep (se 1 (by rfl) ⟨833714, by rfl⟩ : syracuseStep 1111619 = 1667429) B1667429
theorem B1668689 : Blo 738327 1668689 := bstep (se 2 (by rfl) ⟨625758, by rfl⟩ : syracuseStep 1668689 = 1251517) B1251517
theorem B1111649 : Blo 738327 1111649 := bstep (se 2 (by rfl) ⟨416868, by rfl⟩ : syracuseStep 1111649 = 833737) B833737
theorem B1668707 : Blo 738327 1668707 := bstep (se 1 (by rfl) ⟨1251530, by rfl⟩ : syracuseStep 1668707 = 2503061) B2503061
theorem B1111667 : Blo 738327 1111667 := bstep (se 1 (by rfl) ⟨833750, by rfl⟩ : syracuseStep 1111667 = 1667501) B1667501
theorem B1111697 : Blo 738327 1111697 := bstep (se 2 (by rfl) ⟨416886, by rfl⟩ : syracuseStep 1111697 = 833773) B833773
theorem B1111715 : Blo 738327 1111715 := bstep (se 1 (by rfl) ⟨833786, by rfl⟩ : syracuseStep 1111715 = 1667573) B1667573
theorem B1111745 : Blo 738327 1111745 := bstep (se 2 (by rfl) ⟨416904, by rfl⟩ : syracuseStep 1111745 = 833809) B833809
theorem B1406659 : Blo 738327 1406659 := bstep (se 1 (by rfl) ⟨1054994, by rfl⟩ : syracuseStep 1406659 = 2109989) B2109989
theorem B1111763 : Blo 738327 1111763 := bstep (se 1 (by rfl) ⟨833822, by rfl⟩ : syracuseStep 1111763 = 1667645) B1667645
theorem B1111793 : Blo 738327 1111793 := bstep (se 2 (by rfl) ⟨416922, by rfl⟩ : syracuseStep 1111793 = 833845) B833845
theorem B1111811 : Blo 738327 1111811 := bstep (se 1 (by rfl) ⟨833858, by rfl⟩ : syracuseStep 1111811 = 1667717) B1667717
theorem B1111841 : Blo 738327 1111841 := bstep (se 2 (by rfl) ⟨416940, by rfl⟩ : syracuseStep 1111841 = 833881) B833881
theorem B2815793 : Blo 738327 2815793 := bstep (se 2 (by rfl) ⟨1055922, by rfl⟩ : syracuseStep 2815793 = 2111845) B2111845
theorem B1111859 : Blo 738327 1111859 := bstep (se 1 (by rfl) ⟨833894, by rfl⟩ : syracuseStep 1111859 = 1667789) B1667789
theorem B1111889 : Blo 738327 1111889 := bstep (se 2 (by rfl) ⟨416958, by rfl⟩ : syracuseStep 1111889 = 833917) B833917
theorem B1111907 : Blo 738327 1111907 := bstep (se 1 (by rfl) ⟨833930, by rfl⟩ : syracuseStep 1111907 = 1667861) B1667861
theorem B1668977 : Blo 738327 1668977 := bstep (se 2 (by rfl) ⟨625866, by rfl⟩ : syracuseStep 1668977 = 1251733) B1251733
theorem B1111937 : Blo 738327 1111937 := bstep (se 2 (by rfl) ⟨416976, by rfl⟩ : syracuseStep 1111937 = 833953) B833953
theorem B1668995 : Blo 738327 1668995 := bstep (se 1 (by rfl) ⟨1251746, by rfl⟩ : syracuseStep 1668995 = 2503493) B2503493
theorem B1111955 : Blo 738327 1111955 := bstep (se 1 (by rfl) ⟨833966, by rfl⟩ : syracuseStep 1111955 = 1667933) B1667933
theorem B1111985 : Blo 738327 1111985 := bstep (se 2 (by rfl) ⟨416994, by rfl⟩ : syracuseStep 1111985 = 833989) B833989
theorem B1112003 : Blo 738327 1112003 := bstep (se 1 (by rfl) ⟨834002, by rfl⟩ : syracuseStep 1112003 = 1668005) B1668005
theorem B1112033 : Blo 738327 1112033 := bstep (se 2 (by rfl) ⟨417012, by rfl⟩ : syracuseStep 1112033 = 834025) B834025
theorem B1112051 : Blo 738327 1112051 := bstep (se 1 (by rfl) ⟨834038, by rfl⟩ : syracuseStep 1112051 = 1668077) B1668077
theorem B1112081 : Blo 738327 1112081 := bstep (se 2 (by rfl) ⟨417030, by rfl⟩ : syracuseStep 1112081 = 834061) B834061
theorem B1112099 : Blo 738327 1112099 := bstep (se 1 (by rfl) ⟨834074, by rfl⟩ : syracuseStep 1112099 = 1668149) B1668149
theorem B1112129 : Blo 738327 1112129 := bstep (se 2 (by rfl) ⟨417048, by rfl⟩ : syracuseStep 1112129 = 834097) B834097
theorem B1112147 : Blo 738327 1112147 := bstep (se 1 (by rfl) ⟨834110, by rfl⟩ : syracuseStep 1112147 = 1668221) B1668221
theorem B7108721 : Blo 738327 7108721 := bstep (se 2 (by rfl) ⟨2665770, by rfl⟩ : syracuseStep 7108721 = 5331541) B5331541
theorem B1112177 : Blo 738327 1112177 := bstep (se 2 (by rfl) ⟨417066, by rfl⟩ : syracuseStep 1112177 = 834133) B834133
theorem B1407107 : Blo 738327 1407107 := bstep (se 1 (by rfl) ⟨1055330, by rfl⟩ : syracuseStep 1407107 = 2110661) B2110661
theorem B1112195 : Blo 738327 1112195 := bstep (se 1 (by rfl) ⟨834146, by rfl⟩ : syracuseStep 1112195 = 1668293) B1668293
theorem B1669265 : Blo 738327 1669265 := bstep (se 2 (by rfl) ⟨625974, by rfl⟩ : syracuseStep 1669265 = 1251949) B1251949
theorem B1112225 : Blo 738327 1112225 := bstep (se 2 (by rfl) ⟨417084, by rfl⟩ : syracuseStep 1112225 = 834169) B834169
theorem B1669283 : Blo 738327 1669283 := bstep (se 1 (by rfl) ⟨1251962, by rfl⟩ : syracuseStep 1669283 = 2503925) B2503925
theorem B1112243 : Blo 738327 1112243 := bstep (se 1 (by rfl) ⟨834182, by rfl⟩ : syracuseStep 1112243 = 1668365) B1668365
theorem B1112273 : Blo 738327 1112273 := bstep (se 2 (by rfl) ⟨417102, by rfl⟩ : syracuseStep 1112273 = 834205) B834205
theorem B1112291 : Blo 738327 1112291 := bstep (se 1 (by rfl) ⟨834218, by rfl⟩ : syracuseStep 1112291 = 1668437) B1668437
theorem B1112321 : Blo 738327 1112321 := bstep (se 2 (by rfl) ⟨417120, by rfl⟩ : syracuseStep 1112321 = 834241) B834241
theorem B1112339 : Blo 738327 1112339 := bstep (se 1 (by rfl) ⟨834254, by rfl⟩ : syracuseStep 1112339 = 1668509) B1668509
theorem B4553009 : Blo 738327 4553009 := bstep (se 2 (by rfl) ⟨1707378, by rfl⟩ : syracuseStep 4553009 = 3414757) B3414757
theorem B1112369 : Blo 738327 1112369 := bstep (se 2 (by rfl) ⟨417138, by rfl⟩ : syracuseStep 1112369 = 834277) B834277
theorem B1112387 : Blo 738327 1112387 := bstep (se 1 (by rfl) ⟨834290, by rfl⟩ : syracuseStep 1112387 = 1668581) B1668581
theorem B1112417 : Blo 738327 1112417 := bstep (se 2 (by rfl) ⟨417156, by rfl⟩ : syracuseStep 1112417 = 834313) B834313
theorem B1112435 : Blo 738327 1112435 := bstep (se 1 (by rfl) ⟨834326, by rfl⟩ : syracuseStep 1112435 = 1668653) B1668653
theorem B9632141 : Blo 738327 9632141 := bstep (se 3 (by rfl) ⟨1806026, by rfl⟩ : syracuseStep 9632141 = 3612053) B3612053
theorem B1112465 : Blo 738327 1112465 := bstep (se 2 (by rfl) ⟨417174, by rfl⟩ : syracuseStep 1112465 = 834349) B834349
theorem B1407395 : Blo 738327 1407395 := bstep (se 1 (by rfl) ⟨1055546, by rfl⟩ : syracuseStep 1407395 = 2111093) B2111093
theorem B1112483 : Blo 738327 1112483 := bstep (se 1 (by rfl) ⟨834362, by rfl⟩ : syracuseStep 1112483 = 1668725) B1668725
theorem B1669553 : Blo 738327 1669553 := bstep (se 2 (by rfl) ⟨626082, by rfl⟩ : syracuseStep 1669553 = 1252165) B1252165
theorem B1112513 : Blo 738327 1112513 := bstep (se 2 (by rfl) ⟨417192, by rfl⟩ : syracuseStep 1112513 = 834385) B834385
theorem B1669571 : Blo 738327 1669571 := bstep (se 1 (by rfl) ⟨1252178, by rfl⟩ : syracuseStep 1669571 = 2504357) B2504357
theorem B1112531 : Blo 738327 1112531 := bstep (se 1 (by rfl) ⟨834398, by rfl⟩ : syracuseStep 1112531 = 1668797) B1668797
theorem B1112561 : Blo 738327 1112561 := bstep (se 2 (by rfl) ⟨417210, by rfl⟩ : syracuseStep 1112561 = 834421) B834421
theorem B1112579 : Blo 738327 1112579 := bstep (se 1 (by rfl) ⟨834434, by rfl⟩ : syracuseStep 1112579 = 1668869) B1668869
theorem B1112609 : Blo 738327 1112609 := bstep (se 2 (by rfl) ⟨417228, by rfl⟩ : syracuseStep 1112609 = 834457) B834457
theorem B1112627 : Blo 738327 1112627 := bstep (se 1 (by rfl) ⟨834470, by rfl⟩ : syracuseStep 1112627 = 1668941) B1668941
theorem B1112657 : Blo 738327 1112657 := bstep (se 2 (by rfl) ⟨417246, by rfl⟩ : syracuseStep 1112657 = 834493) B834493
theorem B1112675 : Blo 738327 1112675 := bstep (se 1 (by rfl) ⟨834506, by rfl⟩ : syracuseStep 1112675 = 1669013) B1669013
theorem B1112705 : Blo 738327 1112705 := bstep (se 2 (by rfl) ⟨417264, by rfl⟩ : syracuseStep 1112705 = 834529) B834529
theorem B1112723 : Blo 738327 1112723 := bstep (se 1 (by rfl) ⟨834542, by rfl⟩ : syracuseStep 1112723 = 1669085) B1669085
theorem B1997489 : Blo 738327 1997489 := bstep (se 2 (by rfl) ⟨749058, by rfl⟩ : syracuseStep 1997489 = 1498117) B1498117
theorem B1112753 : Blo 738327 1112753 := bstep (se 2 (by rfl) ⟨417282, by rfl⟩ : syracuseStep 1112753 = 834565) B834565
theorem B1112771 : Blo 738327 1112771 := bstep (se 1 (by rfl) ⟨834578, by rfl⟩ : syracuseStep 1112771 = 1669157) B1669157
theorem B1669841 : Blo 738327 1669841 := bstep (se 2 (by rfl) ⟨626190, by rfl⟩ : syracuseStep 1669841 = 1252381) B1252381
theorem B1112801 : Blo 738327 1112801 := bstep (se 2 (by rfl) ⟨417300, by rfl⟩ : syracuseStep 1112801 = 834601) B834601
theorem B1669859 : Blo 738327 1669859 := bstep (se 1 (by rfl) ⟨1252394, by rfl⟩ : syracuseStep 1669859 = 2504789) B2504789
theorem B1112819 : Blo 738327 1112819 := bstep (se 1 (by rfl) ⟨834614, by rfl⟩ : syracuseStep 1112819 = 1669229) B1669229
theorem B1112849 : Blo 738327 1112849 := bstep (se 2 (by rfl) ⟨417318, by rfl⟩ : syracuseStep 1112849 = 834637) B834637
theorem B1112867 : Blo 738327 1112867 := bstep (se 1 (by rfl) ⟨834650, by rfl⟩ : syracuseStep 1112867 = 1669301) B1669301
theorem B1112897 : Blo 738327 1112897 := bstep (se 2 (by rfl) ⟨417336, by rfl⟩ : syracuseStep 1112897 = 834673) B834673
theorem B1112915 : Blo 738327 1112915 := bstep (se 1 (by rfl) ⟨834686, by rfl⟩ : syracuseStep 1112915 = 1669373) B1669373
theorem B1112945 : Blo 738327 1112945 := bstep (se 2 (by rfl) ⟨417354, by rfl⟩ : syracuseStep 1112945 = 834709) B834709
theorem B1112963 : Blo 738327 1112963 := bstep (se 1 (by rfl) ⟨834722, by rfl⟩ : syracuseStep 1112963 = 1669445) B1669445
theorem B1112993 : Blo 738327 1112993 := bstep (se 2 (by rfl) ⟨417372, by rfl⟩ : syracuseStep 1112993 = 834745) B834745
theorem B1113011 : Blo 738327 1113011 := bstep (se 1 (by rfl) ⟨834758, by rfl⟩ : syracuseStep 1113011 = 1669517) B1669517
theorem B1113041 : Blo 738327 1113041 := bstep (se 2 (by rfl) ⟨417390, by rfl⟩ : syracuseStep 1113041 = 834781) B834781
theorem B5340131 : Blo 738327 5340131 := bstep (se 1 (by rfl) ⟨4005098, by rfl⟩ : syracuseStep 5340131 = 8010197) B8010197
theorem B1113059 : Blo 738327 1113059 := bstep (se 1 (by rfl) ⟨834794, by rfl⟩ : syracuseStep 1113059 = 1669589) B1669589
theorem B1670129 : Blo 738327 1670129 := bstep (se 2 (by rfl) ⟨626298, by rfl⟩ : syracuseStep 1670129 = 1252597) B1252597
theorem B1113089 : Blo 738327 1113089 := bstep (se 2 (by rfl) ⟨417408, by rfl⟩ : syracuseStep 1113089 = 834817) B834817
theorem B1670147 : Blo 738327 1670147 := bstep (se 1 (by rfl) ⟨1252610, by rfl⟩ : syracuseStep 1670147 = 2505221) B2505221
theorem B1113107 : Blo 738327 1113107 := bstep (se 1 (by rfl) ⟨834830, by rfl⟩ : syracuseStep 1113107 = 1669661) B1669661
theorem B1113137 : Blo 738327 1113137 := bstep (se 2 (by rfl) ⟨417426, by rfl⟩ : syracuseStep 1113137 = 834853) B834853
theorem B1113155 : Blo 738327 1113155 := bstep (se 1 (by rfl) ⟨834866, by rfl⟩ : syracuseStep 1113155 = 1669733) B1669733
theorem B2849869 : Blo 738327 2849869 := bstep (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) B1068701
theorem B1113185 : Blo 738327 1113185 := bstep (se 2 (by rfl) ⟨417444, by rfl⟩ : syracuseStep 1113185 = 834889) B834889
theorem B1113203 : Blo 738327 1113203 := bstep (se 1 (by rfl) ⟨834902, by rfl⟩ : syracuseStep 1113203 = 1669805) B1669805
theorem B1113233 : Blo 738327 1113233 := bstep (se 2 (by rfl) ⟨417462, by rfl⟩ : syracuseStep 1113233 = 834925) B834925
theorem B1113251 : Blo 738327 1113251 := bstep (se 1 (by rfl) ⟨834938, by rfl⟩ : syracuseStep 1113251 = 1669877) B1669877
theorem B1113281 : Blo 738327 1113281 := bstep (se 2 (by rfl) ⟨417480, by rfl⟩ : syracuseStep 1113281 = 834961) B834961
theorem B1113299 : Blo 738327 1113299 := bstep (se 1 (by rfl) ⟨834974, by rfl⟩ : syracuseStep 1113299 = 1669949) B1669949
theorem B2817251 : Blo 738327 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B1113329 : Blo 738327 1113329 := bstep (se 2 (by rfl) ⟨417498, by rfl⟩ : syracuseStep 1113329 = 834997) B834997
theorem B1113347 : Blo 738327 1113347 := bstep (se 1 (by rfl) ⟨835010, by rfl⟩ : syracuseStep 1113347 = 1670021) B1670021
theorem B1113377 : Blo 738327 1113377 := bstep (se 2 (by rfl) ⟨417516, by rfl⟩ : syracuseStep 1113377 = 835033) B835033
theorem B1113395 : Blo 738327 1113395 := bstep (se 1 (by rfl) ⟨835046, by rfl⟩ : syracuseStep 1113395 = 1670093) B1670093
theorem B1408337 : Blo 738327 1408337 := bstep (se 2 (by rfl) ⟨528126, by rfl⟩ : syracuseStep 1408337 = 1056253) B1056253
theorem B1113425 : Blo 738327 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B1113443 : Blo 738327 1113443 := bstep (se 1 (by rfl) ⟨835082, by rfl⟩ : syracuseStep 1113443 = 1670165) B1670165
theorem B1113473 : Blo 738327 1113473 := bstep (se 2 (by rfl) ⟨417552, by rfl⟩ : syracuseStep 1113473 = 835105) B835105
theorem B1113491 : Blo 738327 1113491 := bstep (se 1 (by rfl) ⟨835118, by rfl⟩ : syracuseStep 1113491 = 1670237) B1670237
theorem B5078533 : Blo 738327 5078533 := bstep (se 4 (by rfl) ⟨476112, by rfl⟩ : syracuseStep 5078533 = 952225) B952225
theorem B4750883 : Blo 738327 4750883 := bstep (se 1 (by rfl) ⟨3563162, by rfl⟩ : syracuseStep 4750883 = 7126325) B7126325
theorem B9010885 : Blo 738327 9010885 := bstep (se 4 (by rfl) ⟨844770, by rfl⟩ : syracuseStep 9010885 = 1689541) B1689541
theorem B1900241 : Blo 738327 1900241 := bstep (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) B1425181
theorem B1605539 : Blo 738327 1605539 := bstep (se 1 (by rfl) ⟨1204154, by rfl⟩ : syracuseStep 1605539 = 2408309) B2408309
theorem B5636141 : Blo 738327 5636141 := bstep (se 3 (by rfl) ⟨1056776, by rfl⟩ : syracuseStep 5636141 = 2113553) B2113553
theorem B1409089 : Blo 738327 1409089 := bstep (se 2 (by rfl) ⟨528408, by rfl⟩ : syracuseStep 1409089 = 1056817) B1056817
theorem B2818435 : Blo 738327 2818435 := bstep (se 1 (by rfl) ⟨2113826, by rfl⟩ : syracuseStep 2818435 = 4227653) B4227653
theorem B13009501 : Blo 738327 13009501 := bstep (se 3 (by rfl) ⟨2439281, by rfl⟩ : syracuseStep 13009501 = 4878563) B4878563
theorem B1442443 : Blo 738327 1442443 := bstep (se 1 (by rfl) ⟨1081832, by rfl⟩ : syracuseStep 1442443 = 2163665) B2163665
theorem B1802969 : Blo 738327 1802969 := bstep (se 2 (by rfl) ⟨676113, by rfl⟩ : syracuseStep 1802969 = 1352227) B1352227
theorem B3376349 : Blo 738327 3376349 := bstep (se 3 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 3376349 = 1266131) B1266131
theorem B1246475 : Blo 738327 1246475 := bstep (se 1 (by rfl) ⟨934856, by rfl⟩ : syracuseStep 1246475 = 1869713) B1869713
theorem B1246603 : Blo 738327 1246603 := bstep (se 1 (by rfl) ⟨934952, by rfl⟩ : syracuseStep 1246603 = 1869905) B1869905
theorem B1246745 : Blo 738327 1246745 := bstep (se 2 (by rfl) ⟨467529, by rfl⟩ : syracuseStep 1246745 = 935059) B935059
theorem B3606167 : Blo 738327 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B1246873 : Blo 738327 1246873 := bstep (se 2 (by rfl) ⟨467577, by rfl⟩ : syracuseStep 1246873 = 935155) B935155
theorem B3999563 : Blo 738327 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B788491 : Blo 738327 788491 := bstep (se 1 (by rfl) ⟨591368, by rfl⟩ : syracuseStep 788491 = 1182737) B1182737
theorem B10651661 : Blo 738327 10651661 := bstep (se 3 (by rfl) ⟨1997186, by rfl⟩ : syracuseStep 10651661 = 3994373) B3994373
theorem B1869875 : Blo 738327 1869875 := bstep (se 1 (by rfl) ⟨1402406, by rfl⟩ : syracuseStep 1869875 = 2804813) B2804813
theorem B1247447 : Blo 738327 1247447 := bstep (se 1 (by rfl) ⟨935585, by rfl⟩ : syracuseStep 1247447 = 1871171) B1871171
theorem B2492747 : Blo 738327 2492747 := bstep (se 1 (by rfl) ⟨1869560, by rfl⟩ : syracuseStep 2492747 = 3739121) B3739121
theorem B1247575 : Blo 738327 1247575 := bstep (se 1 (by rfl) ⟨935681, by rfl⟩ : syracuseStep 1247575 = 1871363) B1871363
theorem B3737987 : Blo 738327 3737987 := bstep (se 1 (by rfl) ⟨2803490, by rfl⟩ : syracuseStep 3737987 = 5606981) B5606981
theorem B1870411 : Blo 738327 1870411 := bstep (se 1 (by rfl) ⟨1402808, by rfl⟩ : syracuseStep 1870411 = 2805617) B2805617
theorem B2493017 : Blo 738327 2493017 := bstep (se 2 (by rfl) ⟨934881, by rfl⟩ : syracuseStep 2493017 = 1869763) B1869763
theorem B1870553 : Blo 738327 1870553 := bstep (se 2 (by rfl) ⟨701457, by rfl⟩ : syracuseStep 1870553 = 1402915) B1402915
theorem B13536179 : Blo 738327 13536179 := bstep (se 1 (by rfl) ⟨10152134, by rfl⟩ : syracuseStep 13536179 = 20304269) B20304269
theorem B1248203 : Blo 738327 1248203 := bstep (se 1 (by rfl) ⟨936152, by rfl⟩ : syracuseStep 1248203 = 1872305) B1872305
theorem B1248331 : Blo 738327 1248331 := bstep (se 1 (by rfl) ⟨936248, by rfl⟩ : syracuseStep 1248331 = 1872497) B1872497
theorem B1182871 : Blo 738327 1182871 := bstep (se 1 (by rfl) ⟨887153, by rfl⟩ : syracuseStep 1182871 = 1774307) B1774307
theorem B888023 : Blo 738327 888023 := bstep (se 1 (by rfl) ⟨666017, by rfl⟩ : syracuseStep 888023 = 1332035) B1332035
theorem B1248473 : Blo 738327 1248473 := bstep (se 2 (by rfl) ⟨468177, by rfl⟩ : syracuseStep 1248473 = 936355) B936355
theorem B2493719 : Blo 738327 2493719 := bstep (se 1 (by rfl) ⟨1870289, by rfl⟩ : syracuseStep 2493719 = 3740579) B3740579
theorem B1281367 : Blo 738327 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B1248601 : Blo 738327 1248601 := bstep (se 2 (by rfl) ⟨468225, by rfl⟩ : syracuseStep 1248601 = 936451) B936451
theorem B1871383 : Blo 738327 1871383 := bstep (se 1 (by rfl) ⟨1403537, by rfl⟩ : syracuseStep 1871383 = 2807075) B2807075
theorem B1281611 : Blo 738327 1281611 := bstep (se 1 (by rfl) ⟨961208, by rfl⟩ : syracuseStep 1281611 = 1922417) B1922417
theorem B2494259 : Blo 738327 2494259 := bstep (se 1 (by rfl) ⟨1870694, by rfl⟩ : syracuseStep 2494259 = 3741389) B3741389
theorem B1249175 : Blo 738327 1249175 := bstep (se 1 (by rfl) ⟨936881, by rfl⟩ : syracuseStep 1249175 = 1873763) B1873763
theorem B1183691 : Blo 738327 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B1871819 : Blo 738327 1871819 := bstep (se 1 (by rfl) ⟨1403864, by rfl⟩ : syracuseStep 1871819 = 2807729) B2807729
theorem B790507 : Blo 738327 790507 := bstep (se 1 (by rfl) ⟨592880, by rfl⟩ : syracuseStep 790507 = 1185761) B1185761
theorem B1249303 : Blo 738327 1249303 := bstep (se 1 (by rfl) ⟨936977, by rfl⟩ : syracuseStep 1249303 = 1873955) B1873955
theorem B2494529 : Blo 738327 2494529 := bstep (se 2 (by rfl) ⟨935448, by rfl⟩ : syracuseStep 2494529 = 1870897) B1870897
theorem B1708249 : Blo 738327 1708249 := bstep (se 2 (by rfl) ⟨640593, by rfl⟩ : syracuseStep 1708249 = 1281187) B1281187
theorem B889099 : Blo 738327 889099 := bstep (se 1 (by rfl) ⟨666824, by rfl⟩ : syracuseStep 889099 = 1333649) B1333649
theorem B1872193 : Blo 738327 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B12357953 : Blo 738327 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B5607953 : Blo 738327 5607953 := bstep (se 2 (by rfl) ⟨2102982, by rfl⟩ : syracuseStep 5607953 = 4205965) B4205965
theorem B2495069 : Blo 738327 2495069 := bstep (se 3 (by rfl) ⟨467825, by rfl⟩ : syracuseStep 2495069 = 935651) B935651
theorem B1249931 : Blo 738327 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B1053337 : Blo 738327 1053337 := bstep (se 2 (by rfl) ⟨395001, by rfl⟩ : syracuseStep 1053337 = 790003) B790003
theorem B1250059 : Blo 738327 1250059 := bstep (se 1 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 1250059 = 1875089) B1875089
theorem B1872791 : Blo 738327 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B1250201 : Blo 738327 1250201 := bstep (se 2 (by rfl) ⟨468825, by rfl⟩ : syracuseStep 1250201 = 937651) B937651
theorem B1250329 : Blo 738327 1250329 := bstep (se 2 (by rfl) ⟨468873, by rfl⟩ : syracuseStep 1250329 = 937747) B937747
theorem B6755507 : Blo 738327 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B1250903 : Blo 738327 1250903 := bstep (se 1 (by rfl) ⟨938177, by rfl⟩ : syracuseStep 1250903 = 1876355) B1876355
theorem B1873601 : Blo 738327 1873601 := bstep (se 2 (by rfl) ⟨702600, by rfl⟩ : syracuseStep 1873601 = 1405201) B1405201
theorem B2496203 : Blo 738327 2496203 := bstep (se 1 (by rfl) ⟨1872152, by rfl⟩ : syracuseStep 2496203 = 3744305) B3744305
theorem B1251031 : Blo 738327 1251031 := bstep (se 1 (by rfl) ⟨938273, by rfl⟩ : syracuseStep 1251031 = 1876547) B1876547
theorem B1578827 : Blo 738327 1578827 := bstep (se 1 (by rfl) ⟨1184120, by rfl⟩ : syracuseStep 1578827 = 2368241) B2368241
theorem B11409329 : Blo 738327 11409329 := bstep (se 2 (by rfl) ⟨4278498, by rfl⟩ : syracuseStep 11409329 = 8556997) B8556997
theorem B2496473 : Blo 738327 2496473 := bstep (se 2 (by rfl) ⟨936177, by rfl⟩ : syracuseStep 2496473 = 1872355) B1872355
theorem B3741713 : Blo 738327 3741713 := bstep (se 2 (by rfl) ⟨1403142, by rfl⟩ : syracuseStep 3741713 = 2806285) B2806285
theorem B2103347 : Blo 738327 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B2103371 : Blo 738327 2103371 := bstep (se 1 (by rfl) ⟨1577528, by rfl⟩ : syracuseStep 2103371 = 3155057) B3155057
theorem B1054795 : Blo 738327 1054795 := bstep (se 1 (by rfl) ⟨791096, by rfl⟩ : syracuseStep 1054795 = 1582193) B1582193
theorem B3741875 : Blo 738327 3741875 := bstep (se 1 (by rfl) ⟨2806406, by rfl⟩ : syracuseStep 3741875 = 5612813) B5612813
theorem B6330545 : Blo 738327 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B1874137 : Blo 738327 1874137 := bstep (se 2 (by rfl) ⟨702801, by rfl⟩ : syracuseStep 1874137 = 1405603) B1405603
theorem B1251659 : Blo 738327 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B1251787 : Blo 738327 1251787 := bstep (se 1 (by rfl) ⟨938840, by rfl⟩ : syracuseStep 1251787 = 1877681) B1877681
theorem B21371363 : Blo 738327 21371363 := bstep (se 1 (by rfl) ⟨16028522, by rfl⟩ : syracuseStep 21371363 = 32057045) B32057045
theorem B4266541 : Blo 738327 4266541 := bstep (se 3 (by rfl) ⟨799976, by rfl⟩ : syracuseStep 4266541 = 1599953) B1599953
theorem B1251929 : Blo 738327 1251929 := bstep (se 2 (by rfl) ⟨469473, by rfl⟩ : syracuseStep 1251929 = 938947) B938947
theorem B2497175 : Blo 738327 2497175 := bstep (se 1 (by rfl) ⟨1872881, by rfl⟩ : syracuseStep 2497175 = 3745763) B3745763
theorem B1252057 : Blo 738327 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B2104157 : Blo 738327 2104157 := bstep (se 3 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 2104157 = 789059) B789059
theorem B6331229 : Blo 738327 6331229 := bstep (se 3 (by rfl) ⟨1187105, by rfl⟩ : syracuseStep 6331229 = 2374211) B2374211
theorem B3251117 : Blo 738327 3251117 := bstep (se 3 (by rfl) ⟨609584, by rfl⟩ : syracuseStep 3251117 = 1219169) B1219169
theorem B6167501 : Blo 738327 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B1580057 : Blo 738327 1580057 := bstep (se 2 (by rfl) ⟨592521, by rfl⟩ : syracuseStep 1580057 = 1185043) B1185043
theorem B2497715 : Blo 738327 2497715 := bstep (se 1 (by rfl) ⟨1873286, by rfl⟩ : syracuseStep 2497715 = 3746573) B3746573
theorem B1252631 : Blo 738327 1252631 := bstep (se 1 (by rfl) ⟨939473, by rfl⟩ : syracuseStep 1252631 = 1878947) B1878947
theorem B1056025 : Blo 738327 1056025 := bstep (se 2 (by rfl) ⟨396009, by rfl⟩ : syracuseStep 1056025 = 792019) B792019
theorem B1875251 : Blo 738327 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B8985973 : Blo 738327 8985973 := bstep (se 5 (by rfl) ⟨421217, by rfl⟩ : syracuseStep 8985973 = 842435) B842435
theorem B2137495 : Blo 738327 2137495 := bstep (se 1 (by rfl) ⟨1603121, by rfl⟩ : syracuseStep 2137495 = 3206243) B3206243
theorem B1580467 : Blo 738327 1580467 := bstep (se 1 (by rfl) ⟨1185350, by rfl⟩ : syracuseStep 1580467 = 2370701) B2370701
theorem B2497985 : Blo 738327 2497985 := bstep (se 2 (by rfl) ⟨936744, by rfl⟩ : syracuseStep 2497985 = 1873489) B1873489
theorem B1875545 : Blo 738327 1875545 := bstep (se 2 (by rfl) ⟨703329, by rfl⟩ : syracuseStep 1875545 = 1406659) B1406659
theorem B1580723 : Blo 738327 1580723 := bstep (se 1 (by rfl) ⟨1185542, by rfl⟩ : syracuseStep 1580723 = 2371085) B2371085
theorem B92348261 : Blo 738327 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B3383171 : Blo 738327 3383171 := bstep (se 1 (by rfl) ⟨2537378, by rfl⟩ : syracuseStep 3383171 = 5074757) B5074757
theorem B2498525 : Blo 738327 2498525 := bstep (se 3 (by rfl) ⟨468473, by rfl⟩ : syracuseStep 2498525 = 936947) B936947
theorem B3743819 : Blo 738327 3743819 := bstep (se 1 (by rfl) ⟨2807864, by rfl⟩ : syracuseStep 3743819 = 5615729) B5615729
theorem B3154099 : Blo 738327 3154099 := bstep (se 1 (by rfl) ⟨2365574, by rfl⟩ : syracuseStep 3154099 = 4731149) B4731149
theorem B5611841 : Blo 738327 5611841 := bstep (se 2 (by rfl) ⟨2104440, by rfl⟩ : syracuseStep 5611841 = 4208881) B4208881
theorem B8430155 : Blo 738327 8430155 := bstep (se 1 (by rfl) ⟨6322616, by rfl⟩ : syracuseStep 8430155 = 12645233) B12645233
theorem B2105945 : Blo 738327 2105945 := bstep (se 2 (by rfl) ⟨789729, by rfl⟩ : syracuseStep 2105945 = 1579459) B1579459
theorem B1581697 : Blo 738327 1581697 := bstep (se 2 (by rfl) ⟨593136, by rfl⟩ : syracuseStep 1581697 = 1186273) B1186273
theorem B3383939 : Blo 738327 3383939 := bstep (se 1 (by rfl) ⟨2537954, by rfl⟩ : syracuseStep 3383939 = 5075909) B5075909
theorem B1188631 : Blo 738327 1188631 := bstep (se 1 (by rfl) ⟨891473, by rfl⟩ : syracuseStep 1188631 = 1782947) B1782947
theorem B3154733 : Blo 738327 3154733 := bstep (se 3 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 3154733 = 1183025) B1183025
theorem B4006721 : Blo 738327 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B1778507 : Blo 738327 1778507 := bstep (se 1 (by rfl) ⟨1333880, by rfl⟩ : syracuseStep 1778507 = 2667761) B2667761
theorem B1188695 : Blo 738327 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B2106263 : Blo 738327 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B1188823 : Blo 738327 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B2499659 : Blo 738327 2499659 := bstep (se 1 (by rfl) ⟨1874744, by rfl⟩ : syracuseStep 2499659 = 3749489) B3749489
theorem B1877195 : Blo 738327 1877195 := bstep (se 1 (by rfl) ⟨1407896, by rfl⟩ : syracuseStep 1877195 = 2815793) B2815793
theorem B2499929 : Blo 738327 2499929 := bstep (se 2 (by rfl) ⟨937473, by rfl⟩ : syracuseStep 2499929 = 1874947) B1874947
theorem B6006221 : Blo 738327 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B2107073 : Blo 738327 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B35923661 : Blo 738327 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B6006545 : Blo 738327 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B3745601 : Blo 738327 3745601 := bstep (se 2 (by rfl) ⟨1404600, by rfl⟩ : syracuseStep 3745601 = 2809201) B2809201
theorem B2500631 : Blo 738327 2500631 := bstep (se 1 (by rfl) ⟨1875473, by rfl⟩ : syracuseStep 2500631 = 3750947) B3750947
theorem B1878167 : Blo 738327 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B5613785 : Blo 738327 5613785 := bstep (se 2 (by rfl) ⟨2105169, by rfl⟩ : syracuseStep 5613785 = 4210339) B4210339
theorem B2369843 : Blo 738327 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B2501171 : Blo 738327 2501171 := bstep (se 1 (by rfl) ⟨1875878, by rfl⟩ : syracuseStep 2501171 = 3751757) B3751757
theorem B1583833 : Blo 738327 1583833 := bstep (se 2 (by rfl) ⟨593937, by rfl⟩ : syracuseStep 1583833 = 1187875) B1187875
theorem B1878835 : Blo 738327 1878835 := bstep (se 1 (by rfl) ⟨1409126, by rfl⟩ : syracuseStep 1878835 = 2818253) B2818253
theorem B2501441 : Blo 738327 2501441 := bstep (se 2 (by rfl) ⟨938040, by rfl⟩ : syracuseStep 2501441 = 1876081) B1876081
theorem B1878977 : Blo 738327 1878977 := bstep (se 2 (by rfl) ⟨704616, by rfl⟩ : syracuseStep 1878977 = 1409233) B1409233
theorem B3550169 : Blo 738327 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B2370521 : Blo 738327 2370521 := bstep (se 2 (by rfl) ⟨888945, by rfl⟩ : syracuseStep 2370521 = 1777891) B1777891
theorem B830731 : Blo 738327 830731 := bstep (se 1 (by rfl) ⟨623048, by rfl⟩ : syracuseStep 830731 = 1246097) B1246097
theorem B3288385 : Blo 738327 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B2108747 : Blo 738327 2108747 := bstep (se 1 (by rfl) ⟨1581560, by rfl⟩ : syracuseStep 2108747 = 3163121) B3163121
theorem B2501981 : Blo 738327 2501981 := bstep (se 3 (by rfl) ⟨469121, by rfl⟩ : syracuseStep 2501981 = 938243) B938243
theorem B1387891 : Blo 738327 1387891 := bstep (se 1 (by rfl) ⟨1040918, by rfl⟩ : syracuseStep 1387891 = 2081837) B2081837
theorem B830839 : Blo 738327 830839 := bstep (se 1 (by rfl) ⟨623129, by rfl⟩ : syracuseStep 830839 = 1246259) B1246259
theorem B831019 : Blo 738327 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B831127 : Blo 738327 831127 := bstep (se 1 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 831127 = 1246691) B1246691
theorem B2666201 : Blo 738327 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B3747545 : Blo 738327 3747545 := bstep (se 2 (by rfl) ⟨1405329, by rfl⟩ : syracuseStep 3747545 = 2810659) B2810659
theorem B2993885 : Blo 738327 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B1421057 : Blo 738327 1421057 := bstep (se 2 (by rfl) ⟨532896, by rfl⟩ : syracuseStep 1421057 = 1065793) B1065793
theorem B831307 : Blo 738327 831307 := bstep (se 1 (by rfl) ⟨623480, by rfl⟩ : syracuseStep 831307 = 1246961) B1246961
theorem B831415 : Blo 738327 831415 := bstep (se 1 (by rfl) ⟨623561, by rfl⟩ : syracuseStep 831415 = 1247123) B1247123
theorem B831595 : Blo 738327 831595 := bstep (se 1 (by rfl) ⟨623696, by rfl⟩ : syracuseStep 831595 = 1247393) B1247393
theorem B831703 : Blo 738327 831703 := bstep (se 1 (by rfl) ⟨623777, by rfl⟩ : syracuseStep 831703 = 1247555) B1247555
theorem B4206923 : Blo 738327 4206923 := bstep (se 1 (by rfl) ⟨3155192, by rfl⟩ : syracuseStep 4206923 = 6310385) B6310385
theorem B831883 : Blo 738327 831883 := bstep (se 1 (by rfl) ⟨623912, by rfl⟩ : syracuseStep 831883 = 1247825) B1247825
theorem B3158423 : Blo 738327 3158423 := bstep (se 1 (by rfl) ⟨2368817, by rfl⟩ : syracuseStep 3158423 = 4737635) B4737635
theorem B2503115 : Blo 738327 2503115 := bstep (se 1 (by rfl) ⟨1877336, by rfl⟩ : syracuseStep 2503115 = 3754673) B3754673
theorem B831991 : Blo 738327 831991 := bstep (se 1 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 831991 = 1247987) B1247987
theorem B2372161 : Blo 738327 2372161 := bstep (se 2 (by rfl) ⟨889560, by rfl⟩ : syracuseStep 2372161 = 1779121) B1779121
theorem B2110045 : Blo 738327 2110045 := bstep (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) B791267
theorem B832171 : Blo 738327 832171 := bstep (se 1 (by rfl) ⟨624128, by rfl⟩ : syracuseStep 832171 = 1248257) B1248257
theorem B2503385 : Blo 738327 2503385 := bstep (se 2 (by rfl) ⟨938769, by rfl⟩ : syracuseStep 2503385 = 1877539) B1877539
theorem B832279 : Blo 738327 832279 := bstep (se 1 (by rfl) ⟨624209, by rfl⟩ : syracuseStep 832279 = 1248419) B1248419
theorem B2372417 : Blo 738327 2372417 := bstep (se 2 (by rfl) ⟨889656, by rfl⟩ : syracuseStep 2372417 = 1779313) B1779313
theorem B2110387 : Blo 738327 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B832459 : Blo 738327 832459 := bstep (se 1 (by rfl) ⟨624344, by rfl⟩ : syracuseStep 832459 = 1248689) B1248689
theorem B832567 : Blo 738327 832567 := bstep (se 1 (by rfl) ⟨624425, by rfl⟩ : syracuseStep 832567 = 1248851) B1248851
theorem B2995393 : Blo 738327 2995393 := bstep (se 2 (by rfl) ⟨1123272, by rfl⟩ : syracuseStep 2995393 = 2246545) B2246545
theorem B4732121 : Blo 738327 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B832747 : Blo 738327 832747 := bstep (se 1 (by rfl) ⟨624560, by rfl⟩ : syracuseStep 832747 = 1249121) B1249121
theorem B3749165 : Blo 738327 3749165 := bstep (se 3 (by rfl) ⟨702968, by rfl⟩ : syracuseStep 3749165 = 1405937) B1405937
theorem B832855 : Blo 738327 832855 := bstep (se 1 (by rfl) ⟨624641, by rfl⟩ : syracuseStep 832855 = 1249283) B1249283
theorem B4502915 : Blo 738327 4502915 := bstep (se 1 (by rfl) ⟨3377186, by rfl⟩ : syracuseStep 4502915 = 6754373) B6754373
theorem B2504087 : Blo 738327 2504087 := bstep (se 1 (by rfl) ⟨1878065, by rfl⟩ : syracuseStep 2504087 = 3756131) B3756131
theorem B833035 : Blo 738327 833035 := bstep (se 1 (by rfl) ⟨624776, by rfl⟩ : syracuseStep 833035 = 1249553) B1249553
theorem B5617187 : Blo 738327 5617187 := bstep (se 1 (by rfl) ⟨4212890, by rfl⟩ : syracuseStep 5617187 = 8425781) B8425781
theorem B833143 : Blo 738327 833143 := bstep (se 1 (by rfl) ⟨624857, by rfl⟩ : syracuseStep 833143 = 1249715) B1249715
theorem B11417219 : Blo 738327 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B833323 : Blo 738327 833323 := bstep (se 1 (by rfl) ⟨624992, by rfl⟩ : syracuseStep 833323 = 1249985) B1249985
theorem B2111321 : Blo 738327 2111321 := bstep (se 2 (by rfl) ⟨791745, by rfl⟩ : syracuseStep 2111321 = 1583491) B1583491
theorem B833431 : Blo 738327 833431 := bstep (se 1 (by rfl) ⟨625073, by rfl⟩ : syracuseStep 833431 = 1250147) B1250147
theorem B2504627 : Blo 738327 2504627 := bstep (se 1 (by rfl) ⟨1878470, by rfl⟩ : syracuseStep 2504627 = 3756941) B3756941
theorem B833611 : Blo 738327 833611 := bstep (se 1 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 833611 = 1250417) B1250417
theorem B833719 : Blo 738327 833719 := bstep (se 1 (by rfl) ⟨625289, by rfl⟩ : syracuseStep 833719 = 1250579) B1250579
theorem B2504897 : Blo 738327 2504897 := bstep (se 2 (by rfl) ⟨939336, by rfl⟩ : syracuseStep 2504897 = 1878673) B1878673
theorem B833899 : Blo 738327 833899 := bstep (se 1 (by rfl) ⟨625424, by rfl⟩ : syracuseStep 833899 = 1250849) B1250849
theorem B834007 : Blo 738327 834007 := bstep (se 1 (by rfl) ⟨625505, by rfl⟩ : syracuseStep 834007 = 1251011) B1251011
theorem B18987533 : Blo 738327 18987533 := bstep (se 3 (by rfl) ⟨3560162, by rfl⟩ : syracuseStep 18987533 = 7120325) B7120325
theorem B834187 : Blo 738327 834187 := bstep (se 1 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 834187 = 1251281) B1251281
theorem B834295 : Blo 738327 834295 := bstep (se 1 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 834295 = 1251443) B1251443
theorem B3160883 : Blo 738327 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B834475 : Blo 738327 834475 := bstep (se 1 (by rfl) ⟨625856, by rfl⟩ : syracuseStep 834475 = 1251713) B1251713
theorem B3161035 : Blo 738327 3161035 := bstep (se 1 (by rfl) ⟨2370776, by rfl⟩ : syracuseStep 3161035 = 4741553) B4741553
theorem B3161105 : Blo 738327 3161105 := bstep (se 2 (by rfl) ⟨1185414, by rfl⟩ : syracuseStep 3161105 = 2370829) B2370829
theorem B834583 : Blo 738327 834583 := bstep (se 1 (by rfl) ⟨625937, by rfl⟩ : syracuseStep 834583 = 1251875) B1251875
theorem B834763 : Blo 738327 834763 := bstep (se 1 (by rfl) ⟨626072, by rfl⟩ : syracuseStep 834763 = 1252145) B1252145
theorem B2374877 : Blo 738327 2374877 := bstep (se 3 (by rfl) ⟨445289, by rfl⟩ : syracuseStep 2374877 = 890579) B890579
theorem B2112733 : Blo 738327 2112733 := bstep (se 3 (by rfl) ⟨396137, by rfl⟩ : syracuseStep 2112733 = 792275) B792275
theorem B834871 : Blo 738327 834871 := bstep (se 1 (by rfl) ⟨626153, by rfl⟩ : syracuseStep 834871 = 1252307) B1252307
theorem B2112961 : Blo 738327 2112961 := bstep (se 2 (by rfl) ⟨792360, by rfl⟩ : syracuseStep 2112961 = 1584721) B1584721
theorem B835051 : Blo 738327 835051 := bstep (se 1 (by rfl) ⟨626288, by rfl⟩ : syracuseStep 835051 = 1252577) B1252577
theorem B5324561 : Blo 738327 5324561 := bstep (se 2 (by rfl) ⟨1996710, by rfl⟩ : syracuseStep 5324561 = 3993421) B3993421
theorem B2113303 : Blo 738327 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B999307 : Blo 738327 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B999319 : Blo 738327 999319 := bstep (se 1 (by rfl) ⟨749489, by rfl⟩ : syracuseStep 999319 = 1498979) B1498979
theorem B24035251 : Blo 738327 24035251 := bstep (se 1 (by rfl) ⟨18026438, by rfl⟩ : syracuseStep 24035251 = 36052877) B36052877
theorem B10698713 : Blo 738327 10698713 := bstep (se 2 (by rfl) ⟨4012017, by rfl⟩ : syracuseStep 10698713 = 8024035) B8024035
theorem B3555857 : Blo 738327 3555857 := bstep (se 2 (by rfl) ⟨1333446, by rfl⟩ : syracuseStep 3555857 = 2666893) B2666893
theorem B3162797 : Blo 738327 3162797 := bstep (se 3 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 3162797 = 1186049) B1186049
theorem B934679 : Blo 738327 934679 := bstep (se 1 (by rfl) ⟨701009, by rfl⟩ : syracuseStep 934679 = 1402019) B1402019
theorem B2278219 : Blo 738327 2278219 := bstep (se 1 (by rfl) ⟨1708664, by rfl⟩ : syracuseStep 2278219 = 3417329) B3417329
theorem B1000345 : Blo 738327 1000345 := bstep (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) B750259
theorem B5686193 : Blo 738327 5686193 := bstep (se 2 (by rfl) ⟨2132322, by rfl⟩ : syracuseStep 5686193 = 4264645) B4264645
theorem B738327 : Blo 738327 738327 := bstep (se 1 (by rfl) ⟨553745, by rfl⟩ : syracuseStep 738327 = 1107491) B1107491
theorem B738347 : Blo 738327 738347 := bstep (se 1 (by rfl) ⟨553760, by rfl⟩ : syracuseStep 738347 = 1107521) B1107521
theorem B738359 : Blo 738327 738359 := bstep (se 1 (by rfl) ⟨553769, by rfl⟩ : syracuseStep 738359 = 1107539) B1107539
theorem B738379 : Blo 738327 738379 := bstep (se 1 (by rfl) ⟨553784, by rfl⟩ : syracuseStep 738379 = 1107569) B1107569
theorem B738391 : Blo 738327 738391 := bstep (se 1 (by rfl) ⟨553793, by rfl⟩ : syracuseStep 738391 = 1107587) B1107587
theorem B4867165 : Blo 738327 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B3753053 : Blo 738327 3753053 := bstep (se 3 (by rfl) ⟨703697, by rfl⟩ : syracuseStep 3753053 = 1407395) B1407395
theorem B738411 : Blo 738327 738411 := bstep (se 1 (by rfl) ⟨553808, by rfl⟩ : syracuseStep 738411 = 1107617) B1107617
theorem B738423 : Blo 738327 738423 := bstep (se 1 (by rfl) ⟨553817, by rfl⟩ : syracuseStep 738423 = 1107635) B1107635
theorem B738443 : Blo 738327 738443 := bstep (se 1 (by rfl) ⟨553832, by rfl⟩ : syracuseStep 738443 = 1107665) B1107665
theorem B738455 : Blo 738327 738455 := bstep (se 1 (by rfl) ⟨553841, by rfl⟩ : syracuseStep 738455 = 1107683) B1107683
theorem B738475 : Blo 738327 738475 := bstep (se 1 (by rfl) ⟨553856, by rfl⟩ : syracuseStep 738475 = 1107713) B1107713
theorem B738487 : Blo 738327 738487 := bstep (se 1 (by rfl) ⟨553865, by rfl⟩ : syracuseStep 738487 = 1107731) B1107731
theorem B738507 : Blo 738327 738507 := bstep (se 1 (by rfl) ⟨553880, by rfl⟩ : syracuseStep 738507 = 1107761) B1107761
theorem B738519 : Blo 738327 738519 := bstep (se 1 (by rfl) ⟨553889, by rfl⟩ : syracuseStep 738519 = 1107779) B1107779
theorem B738539 : Blo 738327 738539 := bstep (se 1 (by rfl) ⟨553904, by rfl⟩ : syracuseStep 738539 = 1107809) B1107809
theorem B738551 : Blo 738327 738551 := bstep (se 1 (by rfl) ⟨553913, by rfl⟩ : syracuseStep 738551 = 1107827) B1107827
theorem B738571 : Blo 738327 738571 := bstep (se 1 (by rfl) ⟨553928, by rfl⟩ : syracuseStep 738571 = 1107857) B1107857
theorem B738583 : Blo 738327 738583 := bstep (se 1 (by rfl) ⟨553937, by rfl⟩ : syracuseStep 738583 = 1107875) B1107875
theorem B738603 : Blo 738327 738603 := bstep (se 1 (by rfl) ⟨553952, by rfl⟩ : syracuseStep 738603 = 1107905) B1107905
theorem B738615 : Blo 738327 738615 := bstep (se 1 (by rfl) ⟨553961, by rfl⟩ : syracuseStep 738615 = 1107923) B1107923
theorem B738635 : Blo 738327 738635 := bstep (se 1 (by rfl) ⟨553976, by rfl⟩ : syracuseStep 738635 = 1107953) B1107953
theorem B1262935 : Blo 738327 1262935 := bstep (se 1 (by rfl) ⟨947201, by rfl⟩ : syracuseStep 1262935 = 1894403) B1894403
theorem B738647 : Blo 738327 738647 := bstep (se 1 (by rfl) ⟨553985, by rfl⟩ : syracuseStep 738647 = 1107971) B1107971
theorem B3163481 : Blo 738327 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B738667 : Blo 738327 738667 := bstep (se 1 (by rfl) ⟨554000, by rfl⟩ : syracuseStep 738667 = 1108001) B1108001
theorem B738679 : Blo 738327 738679 := bstep (se 1 (by rfl) ⟨554009, by rfl⟩ : syracuseStep 738679 = 1108019) B1108019
theorem B738699 : Blo 738327 738699 := bstep (se 1 (by rfl) ⟨554024, by rfl⟩ : syracuseStep 738699 = 1108049) B1108049
theorem B738711 : Blo 738327 738711 := bstep (se 1 (by rfl) ⟨554033, by rfl⟩ : syracuseStep 738711 = 1108067) B1108067
theorem B738731 : Blo 738327 738731 := bstep (se 1 (by rfl) ⟨554048, by rfl⟩ : syracuseStep 738731 = 1108097) B1108097
theorem B738743 : Blo 738327 738743 := bstep (se 1 (by rfl) ⟨554057, by rfl⟩ : syracuseStep 738743 = 1108115) B1108115
theorem B738763 : Blo 738327 738763 := bstep (se 1 (by rfl) ⟨554072, by rfl⟩ : syracuseStep 738763 = 1108145) B1108145
theorem B738775 : Blo 738327 738775 := bstep (se 1 (by rfl) ⟨554081, by rfl⟩ : syracuseStep 738775 = 1108163) B1108163
theorem B935383 : Blo 738327 935383 := bstep (se 1 (by rfl) ⟨701537, by rfl⟩ : syracuseStep 935383 = 1403075) B1403075
theorem B738795 : Blo 738327 738795 := bstep (se 1 (by rfl) ⟨554096, by rfl⟩ : syracuseStep 738795 = 1108193) B1108193
theorem B738807 : Blo 738327 738807 := bstep (se 1 (by rfl) ⟨554105, by rfl⟩ : syracuseStep 738807 = 1108211) B1108211
theorem B738827 : Blo 738327 738827 := bstep (se 1 (by rfl) ⟨554120, by rfl⟩ : syracuseStep 738827 = 1108241) B1108241
theorem B738839 : Blo 738327 738839 := bstep (se 1 (by rfl) ⟨554129, by rfl⟩ : syracuseStep 738839 = 1108259) B1108259
theorem B738859 : Blo 738327 738859 := bstep (se 1 (by rfl) ⟨554144, by rfl⟩ : syracuseStep 738859 = 1108289) B1108289
theorem B738871 : Blo 738327 738871 := bstep (se 1 (by rfl) ⟨554153, by rfl⟩ : syracuseStep 738871 = 1108307) B1108307
theorem B738891 : Blo 738327 738891 := bstep (se 1 (by rfl) ⟨554168, by rfl⟩ : syracuseStep 738891 = 1108337) B1108337
theorem B738903 : Blo 738327 738903 := bstep (se 1 (by rfl) ⟨554177, by rfl⟩ : syracuseStep 738903 = 1108355) B1108355
theorem B738923 : Blo 738327 738923 := bstep (se 1 (by rfl) ⟨554192, by rfl⟩ : syracuseStep 738923 = 1108385) B1108385
theorem B738935 : Blo 738327 738935 := bstep (se 1 (by rfl) ⟨554201, by rfl⟩ : syracuseStep 738935 = 1108403) B1108403
theorem B26035843 : Blo 738327 26035843 := bstep (se 1 (by rfl) ⟨19526882, by rfl⟩ : syracuseStep 26035843 = 39053765) B39053765
theorem B738955 : Blo 738327 738955 := bstep (se 1 (by rfl) ⟨554216, by rfl⟩ : syracuseStep 738955 = 1108433) B1108433
theorem B738967 : Blo 738327 738967 := bstep (se 1 (by rfl) ⟨554225, by rfl⟩ : syracuseStep 738967 = 1108451) B1108451
theorem B738987 : Blo 738327 738987 := bstep (se 1 (by rfl) ⟨554240, by rfl⟩ : syracuseStep 738987 = 1108481) B1108481
theorem B738999 : Blo 738327 738999 := bstep (se 1 (by rfl) ⟨554249, by rfl⟩ : syracuseStep 738999 = 1108499) B1108499
theorem B739019 : Blo 738327 739019 := bstep (se 1 (by rfl) ⟨554264, by rfl⟩ : syracuseStep 739019 = 1108529) B1108529
theorem B739031 : Blo 738327 739031 := bstep (se 1 (by rfl) ⟨554273, by rfl⟩ : syracuseStep 739031 = 1108547) B1108547
theorem B739051 : Blo 738327 739051 := bstep (se 1 (by rfl) ⟨554288, by rfl⟩ : syracuseStep 739051 = 1108577) B1108577
theorem B739063 : Blo 738327 739063 := bstep (se 1 (by rfl) ⟨554297, by rfl⟩ : syracuseStep 739063 = 1108595) B1108595
theorem B739083 : Blo 738327 739083 := bstep (se 1 (by rfl) ⟨554312, by rfl⟩ : syracuseStep 739083 = 1108625) B1108625
theorem B739095 : Blo 738327 739095 := bstep (se 1 (by rfl) ⟨554321, by rfl⟩ : syracuseStep 739095 = 1108643) B1108643
theorem B1066775 : Blo 738327 1066775 := bstep (se 1 (by rfl) ⟨800081, by rfl⟩ : syracuseStep 1066775 = 1600163) B1600163
theorem B739115 : Blo 738327 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B739127 : Blo 738327 739127 := bstep (se 1 (by rfl) ⟨554345, by rfl⟩ : syracuseStep 739127 = 1108691) B1108691
theorem B739147 : Blo 738327 739147 := bstep (se 1 (by rfl) ⟨554360, by rfl⟩ : syracuseStep 739147 = 1108721) B1108721
theorem B739159 : Blo 738327 739159 := bstep (se 1 (by rfl) ⟨554369, by rfl⟩ : syracuseStep 739159 = 1108739) B1108739
theorem B739179 : Blo 738327 739179 := bstep (se 1 (by rfl) ⟨554384, by rfl⟩ : syracuseStep 739179 = 1108769) B1108769
theorem B739191 : Blo 738327 739191 := bstep (se 1 (by rfl) ⟨554393, by rfl⟩ : syracuseStep 739191 = 1108787) B1108787
theorem B739211 : Blo 738327 739211 := bstep (se 1 (by rfl) ⟨554408, by rfl⟩ : syracuseStep 739211 = 1108817) B1108817
theorem B739223 : Blo 738327 739223 := bstep (se 1 (by rfl) ⟨554417, by rfl⟩ : syracuseStep 739223 = 1108835) B1108835
theorem B739243 : Blo 738327 739243 := bstep (se 1 (by rfl) ⟨554432, by rfl⟩ : syracuseStep 739243 = 1108865) B1108865
theorem B739255 : Blo 738327 739255 := bstep (se 1 (by rfl) ⟨554441, by rfl⟩ : syracuseStep 739255 = 1108883) B1108883
theorem B739275 : Blo 738327 739275 := bstep (se 1 (by rfl) ⟨554456, by rfl⟩ : syracuseStep 739275 = 1108913) B1108913
theorem B739287 : Blo 738327 739287 := bstep (se 1 (by rfl) ⟨554465, by rfl⟩ : syracuseStep 739287 = 1108931) B1108931
theorem B2803673 : Blo 738327 2803673 := bstep (se 2 (by rfl) ⟨1051377, by rfl⟩ : syracuseStep 2803673 = 2102755) B2102755
theorem B2934749 : Blo 738327 2934749 := bstep (se 3 (by rfl) ⟨550265, by rfl⟩ : syracuseStep 2934749 = 1100531) B1100531
theorem B739307 : Blo 738327 739307 := bstep (se 1 (by rfl) ⟨554480, by rfl⟩ : syracuseStep 739307 = 1108961) B1108961
theorem B739319 : Blo 738327 739319 := bstep (se 1 (by rfl) ⟨554489, by rfl⟩ : syracuseStep 739319 = 1108979) B1108979
theorem B739339 : Blo 738327 739339 := bstep (se 1 (by rfl) ⟨554504, by rfl⟩ : syracuseStep 739339 = 1109009) B1109009
theorem B739351 : Blo 738327 739351 := bstep (se 1 (by rfl) ⟨554513, by rfl⟩ : syracuseStep 739351 = 1109027) B1109027
theorem B739371 : Blo 738327 739371 := bstep (se 1 (by rfl) ⟨554528, by rfl⟩ : syracuseStep 739371 = 1109057) B1109057
theorem B739383 : Blo 738327 739383 := bstep (se 1 (by rfl) ⟨554537, by rfl⟩ : syracuseStep 739383 = 1109075) B1109075
theorem B739403 : Blo 738327 739403 := bstep (se 1 (by rfl) ⟨554552, by rfl⟩ : syracuseStep 739403 = 1109105) B1109105
theorem B739415 : Blo 738327 739415 := bstep (se 1 (by rfl) ⟨554561, by rfl⟩ : syracuseStep 739415 = 1109123) B1109123
theorem B739435 : Blo 738327 739435 := bstep (se 1 (by rfl) ⟨554576, by rfl⟩ : syracuseStep 739435 = 1109153) B1109153
theorem B739447 : Blo 738327 739447 := bstep (se 1 (by rfl) ⟨554585, by rfl⟩ : syracuseStep 739447 = 1109171) B1109171
theorem B739467 : Blo 738327 739467 := bstep (se 1 (by rfl) ⟨554600, by rfl⟩ : syracuseStep 739467 = 1109201) B1109201
theorem B739479 : Blo 738327 739479 := bstep (se 1 (by rfl) ⟨554609, by rfl⟩ : syracuseStep 739479 = 1109219) B1109219
theorem B739499 : Blo 738327 739499 := bstep (se 1 (by rfl) ⟨554624, by rfl⟩ : syracuseStep 739499 = 1109249) B1109249
theorem B20269237 : Blo 738327 20269237 := bstep (se 5 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 20269237 = 1900241) B1900241
theorem B739511 : Blo 738327 739511 := bstep (se 1 (by rfl) ⟨554633, by rfl⟩ : syracuseStep 739511 = 1109267) B1109267
theorem B2672833 : Blo 738327 2672833 := bstep (se 2 (by rfl) ⟨1002312, by rfl⟩ : syracuseStep 2672833 = 2004625) B2004625
theorem B739531 : Blo 738327 739531 := bstep (se 1 (by rfl) ⟨554648, by rfl⟩ : syracuseStep 739531 = 1109297) B1109297
theorem B739543 : Blo 738327 739543 := bstep (se 1 (by rfl) ⟨554657, by rfl⟩ : syracuseStep 739543 = 1109315) B1109315
theorem B739563 : Blo 738327 739563 := bstep (se 1 (by rfl) ⟨554672, by rfl⟩ : syracuseStep 739563 = 1109345) B1109345
theorem B739575 : Blo 738327 739575 := bstep (se 1 (by rfl) ⟨554681, by rfl⟩ : syracuseStep 739575 = 1109363) B1109363
theorem B739595 : Blo 738327 739595 := bstep (se 1 (by rfl) ⟨554696, by rfl⟩ : syracuseStep 739595 = 1109393) B1109393
theorem B739607 : Blo 738327 739607 := bstep (se 1 (by rfl) ⟨554705, by rfl⟩ : syracuseStep 739607 = 1109411) B1109411
theorem B739627 : Blo 738327 739627 := bstep (se 1 (by rfl) ⟨554720, by rfl⟩ : syracuseStep 739627 = 1109441) B1109441
theorem B3852589 : Blo 738327 3852589 := bstep (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) B1444721
theorem B739639 : Blo 738327 739639 := bstep (se 1 (by rfl) ⟨554729, by rfl⟩ : syracuseStep 739639 = 1109459) B1109459
theorem B739659 : Blo 738327 739659 := bstep (se 1 (by rfl) ⟨554744, by rfl⟩ : syracuseStep 739659 = 1109489) B1109489
theorem B739671 : Blo 738327 739671 := bstep (se 1 (by rfl) ⟨554753, by rfl⟩ : syracuseStep 739671 = 1109507) B1109507
theorem B739691 : Blo 738327 739691 := bstep (se 1 (by rfl) ⟨554768, by rfl⟩ : syracuseStep 739691 = 1109537) B1109537
theorem B739703 : Blo 738327 739703 := bstep (se 1 (by rfl) ⟨554777, by rfl⟩ : syracuseStep 739703 = 1109555) B1109555
theorem B739723 : Blo 738327 739723 := bstep (se 1 (by rfl) ⟨554792, by rfl⟩ : syracuseStep 739723 = 1109585) B1109585
theorem B739735 : Blo 738327 739735 := bstep (se 1 (by rfl) ⟨554801, by rfl⟩ : syracuseStep 739735 = 1109603) B1109603
theorem B739755 : Blo 738327 739755 := bstep (se 1 (by rfl) ⟨554816, by rfl⟩ : syracuseStep 739755 = 1109633) B1109633
theorem B739767 : Blo 738327 739767 := bstep (se 1 (by rfl) ⟨554825, by rfl⟩ : syracuseStep 739767 = 1109651) B1109651
theorem B739787 : Blo 738327 739787 := bstep (se 1 (by rfl) ⟨554840, by rfl⟩ : syracuseStep 739787 = 1109681) B1109681
theorem B739799 : Blo 738327 739799 := bstep (se 1 (by rfl) ⟨554849, by rfl⟩ : syracuseStep 739799 = 1109699) B1109699
theorem B1690073 : Blo 738327 1690073 := bstep (se 2 (by rfl) ⟨633777, by rfl⟩ : syracuseStep 1690073 = 1267555) B1267555
theorem B739819 : Blo 738327 739819 := bstep (se 1 (by rfl) ⟨554864, by rfl⟩ : syracuseStep 739819 = 1109729) B1109729
theorem B739831 : Blo 738327 739831 := bstep (se 1 (by rfl) ⟨554873, by rfl⟩ : syracuseStep 739831 = 1109747) B1109747
theorem B739851 : Blo 738327 739851 := bstep (se 1 (by rfl) ⟨554888, by rfl⟩ : syracuseStep 739851 = 1109777) B1109777
theorem B739863 : Blo 738327 739863 := bstep (se 1 (by rfl) ⟨554897, by rfl⟩ : syracuseStep 739863 = 1109795) B1109795
theorem B739883 : Blo 738327 739883 := bstep (se 1 (by rfl) ⟨554912, by rfl⟩ : syracuseStep 739883 = 1109825) B1109825
theorem B1690163 : Blo 738327 1690163 := bstep (se 1 (by rfl) ⟨1267622, by rfl⟩ : syracuseStep 1690163 = 2535245) B2535245
theorem B739895 : Blo 738327 739895 := bstep (se 1 (by rfl) ⟨554921, by rfl⟩ : syracuseStep 739895 = 1109843) B1109843
theorem B739915 : Blo 738327 739915 := bstep (se 1 (by rfl) ⟨554936, by rfl⟩ : syracuseStep 739915 = 1109873) B1109873
theorem B739927 : Blo 738327 739927 := bstep (se 1 (by rfl) ⟨554945, by rfl⟩ : syracuseStep 739927 = 1109891) B1109891
theorem B739947 : Blo 738327 739947 := bstep (se 1 (by rfl) ⟨554960, by rfl⟩ : syracuseStep 739947 = 1109921) B1109921
theorem B739959 : Blo 738327 739959 := bstep (se 1 (by rfl) ⟨554969, by rfl⟩ : syracuseStep 739959 = 1109939) B1109939
theorem B739979 : Blo 738327 739979 := bstep (se 1 (by rfl) ⟨554984, by rfl⟩ : syracuseStep 739979 = 1109969) B1109969
theorem B739991 : Blo 738327 739991 := bstep (se 1 (by rfl) ⟨554993, by rfl⟩ : syracuseStep 739991 = 1109987) B1109987
theorem B740011 : Blo 738327 740011 := bstep (se 1 (by rfl) ⟨555008, by rfl⟩ : syracuseStep 740011 = 1110017) B1110017
theorem B11389621 : Blo 738327 11389621 := bstep (se 5 (by rfl) ⟨533888, by rfl⟩ : syracuseStep 11389621 = 1067777) B1067777
theorem B11553461 : Blo 738327 11553461 := bstep (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) B1083137
theorem B740023 : Blo 738327 740023 := bstep (se 1 (by rfl) ⟨555017, by rfl⟩ : syracuseStep 740023 = 1110035) B1110035
theorem B740043 : Blo 738327 740043 := bstep (se 1 (by rfl) ⟨555032, by rfl⟩ : syracuseStep 740043 = 1110065) B1110065
theorem B740055 : Blo 738327 740055 := bstep (se 1 (by rfl) ⟨555041, by rfl⟩ : syracuseStep 740055 = 1110083) B1110083
theorem B740075 : Blo 738327 740075 := bstep (se 1 (by rfl) ⟨555056, by rfl⟩ : syracuseStep 740075 = 1110113) B1110113
theorem B740087 : Blo 738327 740087 := bstep (se 1 (by rfl) ⟨555065, by rfl⟩ : syracuseStep 740087 = 1110131) B1110131
theorem B5622533 : Blo 738327 5622533 := bstep (se 4 (by rfl) ⟨527112, by rfl⟩ : syracuseStep 5622533 = 1054225) B1054225
theorem B740107 : Blo 738327 740107 := bstep (se 1 (by rfl) ⟨555080, by rfl⟩ : syracuseStep 740107 = 1110161) B1110161
theorem B740119 : Blo 738327 740119 := bstep (se 1 (by rfl) ⟨555089, by rfl⟩ : syracuseStep 740119 = 1110179) B1110179
theorem B740139 : Blo 738327 740139 := bstep (se 1 (by rfl) ⟨555104, by rfl⟩ : syracuseStep 740139 = 1110209) B1110209
theorem B740151 : Blo 738327 740151 := bstep (se 1 (by rfl) ⟨555113, by rfl⟩ : syracuseStep 740151 = 1110227) B1110227
theorem B740171 : Blo 738327 740171 := bstep (se 1 (by rfl) ⟨555128, by rfl⟩ : syracuseStep 740171 = 1110257) B1110257
theorem B740183 : Blo 738327 740183 := bstep (se 1 (by rfl) ⟨555137, by rfl⟩ : syracuseStep 740183 = 1110275) B1110275
theorem B740203 : Blo 738327 740203 := bstep (se 1 (by rfl) ⟨555152, by rfl⟩ : syracuseStep 740203 = 1110305) B1110305
theorem B740215 : Blo 738327 740215 := bstep (se 1 (by rfl) ⟨555161, by rfl⟩ : syracuseStep 740215 = 1110323) B1110323
theorem B740235 : Blo 738327 740235 := bstep (se 1 (by rfl) ⟨555176, by rfl⟩ : syracuseStep 740235 = 1110353) B1110353
theorem B740247 : Blo 738327 740247 := bstep (se 1 (by rfl) ⟨555185, by rfl⟩ : syracuseStep 740247 = 1110371) B1110371
theorem B740267 : Blo 738327 740267 := bstep (se 1 (by rfl) ⟨555200, by rfl⟩ : syracuseStep 740267 = 1110401) B1110401
theorem B740279 : Blo 738327 740279 := bstep (se 1 (by rfl) ⟨555209, by rfl⟩ : syracuseStep 740279 = 1110419) B1110419
theorem B740299 : Blo 738327 740299 := bstep (se 1 (by rfl) ⟨555224, by rfl⟩ : syracuseStep 740299 = 1110449) B1110449
theorem B740311 : Blo 738327 740311 := bstep (se 1 (by rfl) ⟨555233, by rfl⟩ : syracuseStep 740311 = 1110467) B1110467
theorem B740331 : Blo 738327 740331 := bstep (se 1 (by rfl) ⟨555248, by rfl⟩ : syracuseStep 740331 = 1110497) B1110497
theorem B740343 : Blo 738327 740343 := bstep (se 1 (by rfl) ⟨555257, by rfl⟩ : syracuseStep 740343 = 1110515) B1110515
theorem B740363 : Blo 738327 740363 := bstep (se 1 (by rfl) ⟨555272, by rfl⟩ : syracuseStep 740363 = 1110545) B1110545
theorem B740375 : Blo 738327 740375 := bstep (se 1 (by rfl) ⟨555281, by rfl⟩ : syracuseStep 740375 = 1110563) B1110563
theorem B740395 : Blo 738327 740395 := bstep (se 1 (by rfl) ⟨555296, by rfl⟩ : syracuseStep 740395 = 1110593) B1110593
theorem B740407 : Blo 738327 740407 := bstep (se 1 (by rfl) ⟨555305, by rfl⟩ : syracuseStep 740407 = 1110611) B1110611
theorem B740427 : Blo 738327 740427 := bstep (se 1 (by rfl) ⟨555320, by rfl⟩ : syracuseStep 740427 = 1110641) B1110641
theorem B740439 : Blo 738327 740439 := bstep (se 1 (by rfl) ⟨555329, by rfl⟩ : syracuseStep 740439 = 1110659) B1110659
theorem B740459 : Blo 738327 740459 := bstep (se 1 (by rfl) ⟨555344, by rfl⟩ : syracuseStep 740459 = 1110689) B1110689
theorem B740471 : Blo 738327 740471 := bstep (se 1 (by rfl) ⟨555353, by rfl⟩ : syracuseStep 740471 = 1110707) B1110707
theorem B937099 : Blo 738327 937099 := bstep (se 1 (by rfl) ⟨702824, by rfl⟩ : syracuseStep 937099 = 1405649) B1405649
theorem B740491 : Blo 738327 740491 := bstep (se 1 (by rfl) ⟨555368, by rfl⟩ : syracuseStep 740491 = 1110737) B1110737
theorem B740503 : Blo 738327 740503 := bstep (se 1 (by rfl) ⟨555377, by rfl⟩ : syracuseStep 740503 = 1110755) B1110755
theorem B3755159 : Blo 738327 3755159 := bstep (se 1 (by rfl) ⟨2816369, by rfl⟩ : syracuseStep 3755159 = 5632739) B5632739
theorem B740523 : Blo 738327 740523 := bstep (se 1 (by rfl) ⟨555392, by rfl⟩ : syracuseStep 740523 = 1110785) B1110785
theorem B26987701 : Blo 738327 26987701 := bstep (se 5 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 26987701 = 2530097) B2530097
theorem B740535 : Blo 738327 740535 := bstep (se 1 (by rfl) ⟨555401, by rfl⟩ : syracuseStep 740535 = 1110803) B1110803
theorem B740555 : Blo 738327 740555 := bstep (se 1 (by rfl) ⟨555416, by rfl⟩ : syracuseStep 740555 = 1110833) B1110833
theorem B740567 : Blo 738327 740567 := bstep (se 1 (by rfl) ⟨555425, by rfl⟩ : syracuseStep 740567 = 1110851) B1110851
theorem B740587 : Blo 738327 740587 := bstep (se 1 (by rfl) ⟨555440, by rfl⟩ : syracuseStep 740587 = 1110881) B1110881
theorem B740599 : Blo 738327 740599 := bstep (se 1 (by rfl) ⟨555449, by rfl⟩ : syracuseStep 740599 = 1110899) B1110899
theorem B740619 : Blo 738327 740619 := bstep (se 1 (by rfl) ⟨555464, by rfl⟩ : syracuseStep 740619 = 1110929) B1110929
theorem B740631 : Blo 738327 740631 := bstep (se 1 (by rfl) ⟨555473, by rfl⟩ : syracuseStep 740631 = 1110947) B1110947
theorem B740651 : Blo 738327 740651 := bstep (se 1 (by rfl) ⟨555488, by rfl⟩ : syracuseStep 740651 = 1110977) B1110977
theorem B740663 : Blo 738327 740663 := bstep (se 1 (by rfl) ⟨555497, by rfl⟩ : syracuseStep 740663 = 1110995) B1110995
theorem B740683 : Blo 738327 740683 := bstep (se 1 (by rfl) ⟨555512, by rfl⟩ : syracuseStep 740683 = 1111025) B1111025
theorem B740695 : Blo 738327 740695 := bstep (se 1 (by rfl) ⟨555521, by rfl⟩ : syracuseStep 740695 = 1111043) B1111043
theorem B740715 : Blo 738327 740715 := bstep (se 1 (by rfl) ⟨555536, by rfl⟩ : syracuseStep 740715 = 1111073) B1111073
theorem B740727 : Blo 738327 740727 := bstep (se 1 (by rfl) ⟨555545, by rfl⟩ : syracuseStep 740727 = 1111091) B1111091
theorem B740747 : Blo 738327 740747 := bstep (se 1 (by rfl) ⟨555560, by rfl⟩ : syracuseStep 740747 = 1111121) B1111121
theorem B740759 : Blo 738327 740759 := bstep (se 1 (by rfl) ⟨555569, by rfl⟩ : syracuseStep 740759 = 1111139) B1111139
theorem B740779 : Blo 738327 740779 := bstep (se 1 (by rfl) ⟨555584, by rfl⟩ : syracuseStep 740779 = 1111169) B1111169
theorem B4804019 : Blo 738327 4804019 := bstep (se 1 (by rfl) ⟨3603014, by rfl⟩ : syracuseStep 4804019 = 7206029) B7206029
theorem B740791 : Blo 738327 740791 := bstep (se 1 (by rfl) ⟨555593, by rfl⟩ : syracuseStep 740791 = 1111187) B1111187
theorem B740811 : Blo 738327 740811 := bstep (se 1 (by rfl) ⟨555608, by rfl⟩ : syracuseStep 740811 = 1111217) B1111217
theorem B740823 : Blo 738327 740823 := bstep (se 1 (by rfl) ⟨555617, by rfl⟩ : syracuseStep 740823 = 1111235) B1111235
theorem B740843 : Blo 738327 740843 := bstep (se 1 (by rfl) ⟨555632, by rfl⟩ : syracuseStep 740843 = 1111265) B1111265
theorem B740855 : Blo 738327 740855 := bstep (se 1 (by rfl) ⟨555641, by rfl⟩ : syracuseStep 740855 = 1111283) B1111283
theorem B740875 : Blo 738327 740875 := bstep (se 1 (by rfl) ⟨555656, by rfl⟩ : syracuseStep 740875 = 1111313) B1111313
theorem B740887 : Blo 738327 740887 := bstep (se 1 (by rfl) ⟨555665, by rfl⟩ : syracuseStep 740887 = 1111331) B1111331
theorem B740907 : Blo 738327 740907 := bstep (se 1 (by rfl) ⟨555680, by rfl⟩ : syracuseStep 740907 = 1111361) B1111361
theorem B2805299 : Blo 738327 2805299 := bstep (se 1 (by rfl) ⟨2103974, by rfl⟩ : syracuseStep 2805299 = 4207949) B4207949
theorem B740919 : Blo 738327 740919 := bstep (se 1 (by rfl) ⟨555689, by rfl⟩ : syracuseStep 740919 = 1111379) B1111379
theorem B2805313 : Blo 738327 2805313 := bstep (se 2 (by rfl) ⟨1051992, by rfl⟩ : syracuseStep 2805313 = 2103985) B2103985
theorem B740939 : Blo 738327 740939 := bstep (se 1 (by rfl) ⟨555704, by rfl⟩ : syracuseStep 740939 = 1111409) B1111409
theorem B740951 : Blo 738327 740951 := bstep (se 1 (by rfl) ⟨555713, by rfl⟩ : syracuseStep 740951 = 1111427) B1111427
theorem B4738661 : Blo 738327 4738661 := bstep (se 4 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 4738661 = 888499) B888499
theorem B740971 : Blo 738327 740971 := bstep (se 1 (by rfl) ⟨555728, by rfl⟩ : syracuseStep 740971 = 1111457) B1111457
theorem B740983 : Blo 738327 740983 := bstep (se 1 (by rfl) ⟨555737, by rfl⟩ : syracuseStep 740983 = 1111475) B1111475
theorem B741003 : Blo 738327 741003 := bstep (se 1 (by rfl) ⟨555752, by rfl⟩ : syracuseStep 741003 = 1111505) B1111505
theorem B741015 : Blo 738327 741015 := bstep (se 1 (by rfl) ⟨555761, by rfl⟩ : syracuseStep 741015 = 1111523) B1111523
theorem B741035 : Blo 738327 741035 := bstep (se 1 (by rfl) ⟨555776, by rfl⟩ : syracuseStep 741035 = 1111553) B1111553
theorem B1330867 : Blo 738327 1330867 := bstep (se 1 (by rfl) ⟨998150, by rfl⟩ : syracuseStep 1330867 = 1996301) B1996301
theorem B741047 : Blo 738327 741047 := bstep (se 1 (by rfl) ⟨555785, by rfl⟩ : syracuseStep 741047 = 1111571) B1111571
theorem B741067 : Blo 738327 741067 := bstep (se 1 (by rfl) ⟨555800, by rfl⟩ : syracuseStep 741067 = 1111601) B1111601
theorem B741079 : Blo 738327 741079 := bstep (se 1 (by rfl) ⟨555809, by rfl⟩ : syracuseStep 741079 = 1111619) B1111619
theorem B741099 : Blo 738327 741099 := bstep (se 1 (by rfl) ⟨555824, by rfl⟩ : syracuseStep 741099 = 1111649) B1111649
theorem B741111 : Blo 738327 741111 := bstep (se 1 (by rfl) ⟨555833, by rfl⟩ : syracuseStep 741111 = 1111667) B1111667
theorem B741131 : Blo 738327 741131 := bstep (se 1 (by rfl) ⟨555848, by rfl⟩ : syracuseStep 741131 = 1111697) B1111697
theorem B741143 : Blo 738327 741143 := bstep (se 1 (by rfl) ⟨555857, by rfl⟩ : syracuseStep 741143 = 1111715) B1111715
theorem B741163 : Blo 738327 741163 := bstep (se 1 (by rfl) ⟨555872, by rfl⟩ : syracuseStep 741163 = 1111745) B1111745
theorem B741175 : Blo 738327 741175 := bstep (se 1 (by rfl) ⟨555881, by rfl⟩ : syracuseStep 741175 = 1111763) B1111763
theorem B741195 : Blo 738327 741195 := bstep (se 1 (by rfl) ⟨555896, by rfl⟩ : syracuseStep 741195 = 1111793) B1111793
theorem B741207 : Blo 738327 741207 := bstep (se 1 (by rfl) ⟨555905, by rfl⟩ : syracuseStep 741207 = 1111811) B1111811
theorem B741227 : Blo 738327 741227 := bstep (se 1 (by rfl) ⟨555920, by rfl⟩ : syracuseStep 741227 = 1111841) B1111841
theorem B741239 : Blo 738327 741239 := bstep (se 1 (by rfl) ⟨555929, by rfl⟩ : syracuseStep 741239 = 1111859) B1111859
theorem B741259 : Blo 738327 741259 := bstep (se 1 (by rfl) ⟨555944, by rfl⟩ : syracuseStep 741259 = 1111889) B1111889
theorem B741271 : Blo 738327 741271 := bstep (se 1 (by rfl) ⟨555953, by rfl⟩ : syracuseStep 741271 = 1111907) B1111907
theorem B741291 : Blo 738327 741291 := bstep (se 1 (by rfl) ⟨555968, by rfl⟩ : syracuseStep 741291 = 1111937) B1111937
theorem B741303 : Blo 738327 741303 := bstep (se 1 (by rfl) ⟨555977, by rfl⟩ : syracuseStep 741303 = 1111955) B1111955
theorem B741323 : Blo 738327 741323 := bstep (se 1 (by rfl) ⟨555992, by rfl⟩ : syracuseStep 741323 = 1111985) B1111985
theorem B741335 : Blo 738327 741335 := bstep (se 1 (by rfl) ⟨556001, by rfl⟩ : syracuseStep 741335 = 1112003) B1112003
theorem B741355 : Blo 738327 741355 := bstep (se 1 (by rfl) ⟨556016, by rfl⟩ : syracuseStep 741355 = 1112033) B1112033
theorem B741367 : Blo 738327 741367 := bstep (se 1 (by rfl) ⟨556025, by rfl⟩ : syracuseStep 741367 = 1112051) B1112051
theorem B741387 : Blo 738327 741387 := bstep (se 1 (by rfl) ⟨556040, by rfl⟩ : syracuseStep 741387 = 1112081) B1112081
theorem B741399 : Blo 738327 741399 := bstep (se 1 (by rfl) ⟨556049, by rfl⟩ : syracuseStep 741399 = 1112099) B1112099
theorem B741419 : Blo 738327 741419 := bstep (se 1 (by rfl) ⟨556064, by rfl⟩ : syracuseStep 741419 = 1112129) B1112129
theorem B741431 : Blo 738327 741431 := bstep (se 1 (by rfl) ⟨556073, by rfl⟩ : syracuseStep 741431 = 1112147) B1112147
theorem B4739147 : Blo 738327 4739147 := bstep (se 1 (by rfl) ⟨3554360, by rfl⟩ : syracuseStep 4739147 = 7108721) B7108721
theorem B741451 : Blo 738327 741451 := bstep (se 1 (by rfl) ⟨556088, by rfl⟩ : syracuseStep 741451 = 1112177) B1112177
theorem B741463 : Blo 738327 741463 := bstep (se 1 (by rfl) ⟨556097, by rfl⟩ : syracuseStep 741463 = 1112195) B1112195
theorem B938071 : Blo 738327 938071 := bstep (se 1 (by rfl) ⟨703553, by rfl⟩ : syracuseStep 938071 = 1407107) B1407107
theorem B741483 : Blo 738327 741483 := bstep (se 1 (by rfl) ⟨556112, by rfl⟩ : syracuseStep 741483 = 1112225) B1112225
theorem B741495 : Blo 738327 741495 := bstep (se 1 (by rfl) ⟨556121, by rfl⟩ : syracuseStep 741495 = 1112243) B1112243
theorem B1331329 : Blo 738327 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B741515 : Blo 738327 741515 := bstep (se 1 (by rfl) ⟨556136, by rfl⟩ : syracuseStep 741515 = 1112273) B1112273
theorem B741527 : Blo 738327 741527 := bstep (se 1 (by rfl) ⟨556145, by rfl⟩ : syracuseStep 741527 = 1112291) B1112291
theorem B741547 : Blo 738327 741547 := bstep (se 1 (by rfl) ⟨556160, by rfl⟩ : syracuseStep 741547 = 1112321) B1112321
theorem B741559 : Blo 738327 741559 := bstep (se 1 (by rfl) ⟨556169, by rfl⟩ : syracuseStep 741559 = 1112339) B1112339
theorem B3035339 : Blo 738327 3035339 := bstep (se 1 (by rfl) ⟨2276504, by rfl⟩ : syracuseStep 3035339 = 4553009) B4553009
theorem B741579 : Blo 738327 741579 := bstep (se 1 (by rfl) ⟨556184, by rfl⟩ : syracuseStep 741579 = 1112369) B1112369
theorem B741591 : Blo 738327 741591 := bstep (se 1 (by rfl) ⟨556193, by rfl⟩ : syracuseStep 741591 = 1112387) B1112387
theorem B741611 : Blo 738327 741611 := bstep (se 1 (by rfl) ⟨556208, by rfl⟩ : syracuseStep 741611 = 1112417) B1112417
theorem B741623 : Blo 738327 741623 := bstep (se 1 (by rfl) ⟨556217, by rfl⟩ : syracuseStep 741623 = 1112435) B1112435
theorem B7131397 : Blo 738327 7131397 := bstep (se 4 (by rfl) ⟨668568, by rfl⟩ : syracuseStep 7131397 = 1337137) B1337137
theorem B741643 : Blo 738327 741643 := bstep (se 1 (by rfl) ⟨556232, by rfl⟩ : syracuseStep 741643 = 1112465) B1112465
theorem B741655 : Blo 738327 741655 := bstep (se 1 (by rfl) ⟨556241, by rfl⟩ : syracuseStep 741655 = 1112483) B1112483
theorem B741675 : Blo 738327 741675 := bstep (se 1 (by rfl) ⟨556256, by rfl⟩ : syracuseStep 741675 = 1112513) B1112513
theorem B741687 : Blo 738327 741687 := bstep (se 1 (by rfl) ⟨556265, by rfl⟩ : syracuseStep 741687 = 1112531) B1112531
theorem B741707 : Blo 738327 741707 := bstep (se 1 (by rfl) ⟨556280, by rfl⟩ : syracuseStep 741707 = 1112561) B1112561
theorem B741719 : Blo 738327 741719 := bstep (se 1 (by rfl) ⟨556289, by rfl⟩ : syracuseStep 741719 = 1112579) B1112579
theorem B741739 : Blo 738327 741739 := bstep (se 1 (by rfl) ⟨556304, by rfl⟩ : syracuseStep 741739 = 1112609) B1112609
theorem B741751 : Blo 738327 741751 := bstep (se 1 (by rfl) ⟨556313, by rfl⟩ : syracuseStep 741751 = 1112627) B1112627
theorem B741771 : Blo 738327 741771 := bstep (se 1 (by rfl) ⟨556328, by rfl⟩ : syracuseStep 741771 = 1112657) B1112657
theorem B741783 : Blo 738327 741783 := bstep (se 1 (by rfl) ⟨556337, by rfl⟩ : syracuseStep 741783 = 1112675) B1112675
theorem B741803 : Blo 738327 741803 := bstep (se 1 (by rfl) ⟨556352, by rfl⟩ : syracuseStep 741803 = 1112705) B1112705
theorem B741815 : Blo 738327 741815 := bstep (se 1 (by rfl) ⟨556361, by rfl⟩ : syracuseStep 741815 = 1112723) B1112723
theorem B1331659 : Blo 738327 1331659 := bstep (se 1 (by rfl) ⟨998744, by rfl⟩ : syracuseStep 1331659 = 1997489) B1997489
theorem B741835 : Blo 738327 741835 := bstep (se 1 (by rfl) ⟨556376, by rfl⟩ : syracuseStep 741835 = 1112753) B1112753
theorem B741847 : Blo 738327 741847 := bstep (se 1 (by rfl) ⟨556385, by rfl⟩ : syracuseStep 741847 = 1112771) B1112771
theorem B741867 : Blo 738327 741867 := bstep (se 1 (by rfl) ⟨556400, by rfl⟩ : syracuseStep 741867 = 1112801) B1112801
theorem B741879 : Blo 738327 741879 := bstep (se 1 (by rfl) ⟨556409, by rfl⟩ : syracuseStep 741879 = 1112819) B1112819
theorem B741899 : Blo 738327 741899 := bstep (se 1 (by rfl) ⟨556424, by rfl⟩ : syracuseStep 741899 = 1112849) B1112849
theorem B741911 : Blo 738327 741911 := bstep (se 1 (by rfl) ⟨556433, by rfl⟩ : syracuseStep 741911 = 1112867) B1112867
theorem B741931 : Blo 738327 741931 := bstep (se 1 (by rfl) ⟨556448, by rfl⟩ : syracuseStep 741931 = 1112897) B1112897
theorem B741943 : Blo 738327 741943 := bstep (se 1 (by rfl) ⟨556457, by rfl⟩ : syracuseStep 741943 = 1112915) B1112915
theorem B741963 : Blo 738327 741963 := bstep (se 1 (by rfl) ⟨556472, by rfl⟩ : syracuseStep 741963 = 1112945) B1112945
theorem B741975 : Blo 738327 741975 := bstep (se 1 (by rfl) ⟨556481, by rfl⟩ : syracuseStep 741975 = 1112963) B1112963
theorem B741995 : Blo 738327 741995 := bstep (se 1 (by rfl) ⟨556496, by rfl⟩ : syracuseStep 741995 = 1112993) B1112993
theorem B742007 : Blo 738327 742007 := bstep (se 1 (by rfl) ⟨556505, by rfl⟩ : syracuseStep 742007 = 1113011) B1113011
theorem B742027 : Blo 738327 742027 := bstep (se 1 (by rfl) ⟨556520, by rfl⟩ : syracuseStep 742027 = 1113041) B1113041
theorem B3560087 : Blo 738327 3560087 := bstep (se 1 (by rfl) ⟨2670065, by rfl⟩ : syracuseStep 3560087 = 5340131) B5340131
theorem B742039 : Blo 738327 742039 := bstep (se 1 (by rfl) ⟨556529, by rfl⟩ : syracuseStep 742039 = 1113059) B1113059
theorem B742059 : Blo 738327 742059 := bstep (se 1 (by rfl) ⟨556544, by rfl⟩ : syracuseStep 742059 = 1113089) B1113089
theorem B6771377 : Blo 738327 6771377 := bstep (se 2 (by rfl) ⟨2539266, by rfl⟩ : syracuseStep 6771377 = 5078533) B5078533
theorem B742071 : Blo 738327 742071 := bstep (se 1 (by rfl) ⟨556553, by rfl⟩ : syracuseStep 742071 = 1113107) B1113107
theorem B3166913 : Blo 738327 3166913 := bstep (se 2 (by rfl) ⟨1187592, by rfl⟩ : syracuseStep 3166913 = 2375185) B2375185
theorem B742091 : Blo 738327 742091 := bstep (se 1 (by rfl) ⟨556568, by rfl⟩ : syracuseStep 742091 = 1113137) B1113137
theorem B742103 : Blo 738327 742103 := bstep (se 1 (by rfl) ⟨556577, by rfl⟩ : syracuseStep 742103 = 1113155) B1113155
theorem B742123 : Blo 738327 742123 := bstep (se 1 (by rfl) ⟨556592, by rfl⟩ : syracuseStep 742123 = 1113185) B1113185
theorem B742135 : Blo 738327 742135 := bstep (se 1 (by rfl) ⟨556601, by rfl⟩ : syracuseStep 742135 = 1113203) B1113203
theorem B742155 : Blo 738327 742155 := bstep (se 1 (by rfl) ⟨556616, by rfl⟩ : syracuseStep 742155 = 1113233) B1113233
theorem B742167 : Blo 738327 742167 := bstep (se 1 (by rfl) ⟨556625, by rfl⟩ : syracuseStep 742167 = 1113251) B1113251
theorem B742187 : Blo 738327 742187 := bstep (se 1 (by rfl) ⟨556640, by rfl⟩ : syracuseStep 742187 = 1113281) B1113281
theorem B742199 : Blo 738327 742199 := bstep (se 1 (by rfl) ⟨556649, by rfl⟩ : syracuseStep 742199 = 1113299) B1113299
theorem B742219 : Blo 738327 742219 := bstep (se 1 (by rfl) ⟨556664, by rfl⟩ : syracuseStep 742219 = 1113329) B1113329
theorem B742231 : Blo 738327 742231 := bstep (se 1 (by rfl) ⟨556673, by rfl⟩ : syracuseStep 742231 = 1113347) B1113347
theorem B742251 : Blo 738327 742251 := bstep (se 1 (by rfl) ⟨556688, by rfl⟩ : syracuseStep 742251 = 1113377) B1113377
theorem B742263 : Blo 738327 742263 := bstep (se 1 (by rfl) ⟨556697, by rfl⟩ : syracuseStep 742263 = 1113395) B1113395
theorem B938891 : Blo 738327 938891 := bstep (se 1 (by rfl) ⟨704168, by rfl⟩ : syracuseStep 938891 = 1408337) B1408337
theorem B742283 : Blo 738327 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B742295 : Blo 738327 742295 := bstep (se 1 (by rfl) ⟨556721, by rfl⟩ : syracuseStep 742295 = 1113443) B1113443
theorem B1332121 : Blo 738327 1332121 := bstep (se 2 (by rfl) ⟨499545, by rfl⟩ : syracuseStep 1332121 = 999091) B999091
theorem B742315 : Blo 738327 742315 := bstep (se 1 (by rfl) ⟨556736, by rfl⟩ : syracuseStep 742315 = 1113473) B1113473
theorem B12014513 : Blo 738327 12014513 := bstep (se 2 (by rfl) ⟨4505442, by rfl⟩ : syracuseStep 12014513 = 9010885) B9010885
theorem B742327 : Blo 738327 742327 := bstep (se 1 (by rfl) ⟨556745, by rfl⟩ : syracuseStep 742327 = 1113491) B1113491
theorem B5329925 : Blo 738327 5329925 := bstep (se 4 (by rfl) ⟨499680, by rfl⟩ : syracuseStep 5329925 = 999361) B999361
theorem B3167255 : Blo 738327 3167255 := bstep (se 1 (by rfl) ⟨2375441, by rfl⟩ : syracuseStep 3167255 = 4750883) B4750883
theorem B4281437 : Blo 738327 4281437 := bstep (se 3 (by rfl) ⟨802769, by rfl⟩ : syracuseStep 4281437 = 1605539) B1605539
theorem B5624963 : Blo 738327 5624963 := bstep (se 1 (by rfl) ⟨4218722, by rfl⟩ : syracuseStep 5624963 = 8437445) B8437445
theorem B2807243 : Blo 738327 2807243 := bstep (se 1 (by rfl) ⟨2105432, by rfl⟩ : syracuseStep 2807243 = 4210865) B4210865
theorem B2807257 : Blo 738327 2807257 := bstep (se 2 (by rfl) ⟨1052721, by rfl⟩ : syracuseStep 2807257 = 2105443) B2105443
theorem B6313733 : Blo 738327 6313733 := bstep (se 4 (by rfl) ⟨591912, by rfl⟩ : syracuseStep 6313733 = 1183825) B1183825
theorem B3168179 : Blo 738327 3168179 := bstep (se 1 (by rfl) ⟨2376134, by rfl⟩ : syracuseStep 3168179 = 4752269) B4752269
theorem B2250803 : Blo 738327 2250803 := bstep (se 1 (by rfl) ⟨1688102, by rfl⟩ : syracuseStep 2250803 = 3376205) B3376205
theorem B16046261 : Blo 738327 16046261 := bstep (se 5 (by rfl) ⟨752168, by rfl⟩ : syracuseStep 16046261 = 1504337) B1504337
theorem B1333505 : Blo 738327 1333505 := bstep (se 2 (by rfl) ⟨500064, by rfl⟩ : syracuseStep 1333505 = 1000129) B1000129
theorem B842071 : Blo 738327 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B1661273 : Blo 738327 1661273 := bstep (se 2 (by rfl) ⟨622977, by rfl⟩ : syracuseStep 1661273 = 1245955) B1245955
theorem B2808215 : Blo 738327 2808215 := bstep (se 1 (by rfl) ⟨2106161, by rfl⟩ : syracuseStep 2808215 = 4212323) B4212323
theorem B1661363 : Blo 738327 1661363 := bstep (se 1 (by rfl) ⟨1246022, by rfl⟩ : syracuseStep 1661363 = 2492045) B2492045
theorem B1661399 : Blo 738327 1661399 := bstep (se 1 (by rfl) ⟨1246049, by rfl⟩ : syracuseStep 1661399 = 2492099) B2492099
theorem B4282841 : Blo 738327 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B3005059 : Blo 738327 3005059 := bstep (se 1 (by rfl) ⟨2253794, by rfl⟩ : syracuseStep 3005059 = 4507589) B4507589
theorem B1661579 : Blo 738327 1661579 := bstep (se 1 (by rfl) ⟨1246184, by rfl⟩ : syracuseStep 1661579 = 2492369) B2492369
theorem B4741811 : Blo 738327 4741811 := bstep (se 1 (by rfl) ⟨3556358, by rfl⟩ : syracuseStep 4741811 = 7112717) B7112717
theorem B3562163 : Blo 738327 3562163 := bstep (se 1 (by rfl) ⟨2671622, by rfl⟩ : syracuseStep 3562163 = 5343245) B5343245
theorem B1661633 : Blo 738327 1661633 := bstep (se 2 (by rfl) ⟨623112, by rfl⟩ : syracuseStep 1661633 = 1246225) B1246225
theorem B3169169 : Blo 738327 3169169 := bstep (se 2 (by rfl) ⟨1188438, by rfl⟩ : syracuseStep 3169169 = 2376877) B2376877
theorem B1661849 : Blo 738327 1661849 := bstep (se 2 (by rfl) ⟨623193, by rfl⟩ : syracuseStep 1661849 = 1246387) B1246387
theorem B1661939 : Blo 738327 1661939 := bstep (se 1 (by rfl) ⟨1246454, by rfl⟩ : syracuseStep 1661939 = 2492909) B2492909
theorem B1661975 : Blo 738327 1661975 := bstep (se 1 (by rfl) ⟨1246481, by rfl⟩ : syracuseStep 1661975 = 2492963) B2492963
theorem B1662155 : Blo 738327 1662155 := bstep (se 1 (by rfl) ⟨1246616, by rfl⟩ : syracuseStep 1662155 = 2493233) B2493233
theorem B1334515 : Blo 738327 1334515 := bstep (se 1 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 1334515 = 2001773) B2001773
theorem B1662209 : Blo 738327 1662209 := bstep (se 2 (by rfl) ⟨623328, by rfl⟩ : syracuseStep 1662209 = 1246657) B1246657
theorem B9002285 : Blo 738327 9002285 := bstep (se 3 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 9002285 = 3375857) B3375857
theorem B13491521 : Blo 738327 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B2252225 : Blo 738327 2252225 := bstep (se 2 (by rfl) ⟨844584, by rfl⟩ : syracuseStep 2252225 = 1689169) B1689169
theorem B1334731 : Blo 738327 1334731 := bstep (se 1 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 1334731 = 2002097) B2002097
theorem B1662425 : Blo 738327 1662425 := bstep (se 2 (by rfl) ⟨623409, by rfl⟩ : syracuseStep 1662425 = 1246819) B1246819
theorem B1662515 : Blo 738327 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B1662551 : Blo 738327 1662551 := bstep (se 1 (by rfl) ⟨1246913, by rfl⟩ : syracuseStep 1662551 = 2493827) B2493827
theorem B2809475 : Blo 738327 2809475 := bstep (se 1 (by rfl) ⟨2107106, by rfl⟩ : syracuseStep 2809475 = 4214213) B4214213
theorem B4808323 : Blo 738327 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B5791493 : Blo 738327 5791493 := bstep (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) B1085905
theorem B1662731 : Blo 738327 1662731 := bstep (se 1 (by rfl) ⟨1247048, by rfl⟩ : syracuseStep 1662731 = 2494097) B2494097
theorem B1662785 : Blo 738327 1662785 := bstep (se 2 (by rfl) ⟨623544, by rfl⟩ : syracuseStep 1662785 = 1247089) B1247089
theorem B1663001 : Blo 738327 1663001 := bstep (se 2 (by rfl) ⟨623625, by rfl⟩ : syracuseStep 1663001 = 1247251) B1247251
theorem B1663091 : Blo 738327 1663091 := bstep (se 1 (by rfl) ⟨1247318, by rfl⟩ : syracuseStep 1663091 = 2494637) B2494637
theorem B1663127 : Blo 738327 1663127 := bstep (se 1 (by rfl) ⟨1247345, by rfl⟩ : syracuseStep 1663127 = 2494691) B2494691
theorem B1663307 : Blo 738327 1663307 := bstep (se 1 (by rfl) ⟨1247480, by rfl⟩ : syracuseStep 1663307 = 2494961) B2494961
theorem B1663361 : Blo 738327 1663361 := bstep (se 2 (by rfl) ⟨623760, by rfl⟩ : syracuseStep 1663361 = 1247521) B1247521
theorem B10674611 : Blo 738327 10674611 := bstep (se 1 (by rfl) ⟨8005958, by rfl⟩ : syracuseStep 10674611 = 16011917) B16011917
theorem B8020403 : Blo 738327 8020403 := bstep (se 1 (by rfl) ⟨6015302, by rfl⟩ : syracuseStep 8020403 = 12030605) B12030605
theorem B5628365 : Blo 738327 5628365 := bstep (se 3 (by rfl) ⟨1055318, by rfl⟩ : syracuseStep 5628365 = 2110637) B2110637
theorem B1663577 : Blo 738327 1663577 := bstep (se 2 (by rfl) ⟨623841, by rfl⟩ : syracuseStep 1663577 = 1247683) B1247683
theorem B1663667 : Blo 738327 1663667 := bstep (se 1 (by rfl) ⟨1247750, by rfl⟩ : syracuseStep 1663667 = 2495501) B2495501
theorem B1663703 : Blo 738327 1663703 := bstep (se 1 (by rfl) ⟨1247777, by rfl⟩ : syracuseStep 1663703 = 2495555) B2495555
theorem B10969901 : Blo 738327 10969901 := bstep (se 3 (by rfl) ⟨2056856, by rfl⟩ : syracuseStep 10969901 = 4113713) B4113713
theorem B1336115 : Blo 738327 1336115 := bstep (se 1 (by rfl) ⟨1002086, by rfl⟩ : syracuseStep 1336115 = 2004173) B2004173
theorem B1336151 : Blo 738327 1336151 := bstep (se 1 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 1336151 = 2004227) B2004227
theorem B1401715 : Blo 738327 1401715 := bstep (se 1 (by rfl) ⟨1051286, by rfl⟩ : syracuseStep 1401715 = 2102573) B2102573
theorem B3466115 : Blo 738327 3466115 := bstep (se 1 (by rfl) ⟨2599586, by rfl⟩ : syracuseStep 3466115 = 5199173) B5199173
theorem B1663883 : Blo 738327 1663883 := bstep (se 1 (by rfl) ⟨1247912, by rfl⟩ : syracuseStep 1663883 = 2495825) B2495825
theorem B5628851 : Blo 738327 5628851 := bstep (se 1 (by rfl) ⟨4221638, by rfl⟩ : syracuseStep 5628851 = 8443277) B8443277
theorem B1663937 : Blo 738327 1663937 := bstep (se 2 (by rfl) ⟨623976, by rfl⟩ : syracuseStep 1663937 = 1247953) B1247953
theorem B1336331 : Blo 738327 1336331 := bstep (se 1 (by rfl) ⟨1002248, by rfl⟩ : syracuseStep 1336331 = 2004497) B2004497
theorem B1401943 : Blo 738327 1401943 := bstep (se 1 (by rfl) ⟨1051457, by rfl⟩ : syracuseStep 1401943 = 2102915) B2102915
theorem B6317149 : Blo 738327 6317149 := bstep (se 3 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 6317149 = 2368931) B2368931
theorem B1664153 : Blo 738327 1664153 := bstep (se 2 (by rfl) ⟨624057, by rfl⟩ : syracuseStep 1664153 = 1248115) B1248115
theorem B1402049 : Blo 738327 1402049 := bstep (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) B1051537
theorem B1664243 : Blo 738327 1664243 := bstep (se 1 (by rfl) ⟨1248182, by rfl⟩ : syracuseStep 1664243 = 2496365) B2496365
theorem B1664279 : Blo 738327 1664279 := bstep (se 1 (by rfl) ⟨1248209, by rfl⟩ : syracuseStep 1664279 = 2496419) B2496419
theorem B1402201 : Blo 738327 1402201 := bstep (se 2 (by rfl) ⟨525825, by rfl⟩ : syracuseStep 1402201 = 1051651) B1051651
theorem B3564931 : Blo 738327 3564931 := bstep (se 1 (by rfl) ⟨2673698, by rfl⟩ : syracuseStep 3564931 = 5347397) B5347397
theorem B1664459 : Blo 738327 1664459 := bstep (se 1 (by rfl) ⟨1248344, by rfl⟩ : syracuseStep 1664459 = 2496689) B2496689
theorem B1664513 : Blo 738327 1664513 := bstep (se 2 (by rfl) ⟨624192, by rfl⟩ : syracuseStep 1664513 = 1248385) B1248385
theorem B6743569 : Blo 738327 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1107545 : Blo 738327 1107545 := bstep (se 2 (by rfl) ⟨415329, by rfl⟩ : syracuseStep 1107545 = 830659) B830659
theorem B5072563 : Blo 738327 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B1107659 : Blo 738327 1107659 := bstep (se 1 (by rfl) ⟨830744, by rfl⟩ : syracuseStep 1107659 = 1661489) B1661489
theorem B1107671 : Blo 738327 1107671 := bstep (se 1 (by rfl) ⟨830753, by rfl⟩ : syracuseStep 1107671 = 1661507) B1661507
theorem B1664729 : Blo 738327 1664729 := bstep (se 2 (by rfl) ⟨624273, by rfl⟩ : syracuseStep 1664729 = 1248547) B1248547
theorem B1107737 : Blo 738327 1107737 := bstep (se 2 (by rfl) ⟨415401, by rfl⟩ : syracuseStep 1107737 = 830803) B830803
theorem B1664819 : Blo 738327 1664819 := bstep (se 1 (by rfl) ⟨1248614, by rfl⟩ : syracuseStep 1664819 = 2497229) B2497229
theorem B1664855 : Blo 738327 1664855 := bstep (se 1 (by rfl) ⟨1248641, by rfl⟩ : syracuseStep 1664855 = 2497283) B2497283
theorem B1107851 : Blo 738327 1107851 := bstep (se 1 (by rfl) ⟨830888, by rfl⟩ : syracuseStep 1107851 = 1661777) B1661777
theorem B1107863 : Blo 738327 1107863 := bstep (se 1 (by rfl) ⟨830897, by rfl⟩ : syracuseStep 1107863 = 1661795) B1661795
theorem B1107929 : Blo 738327 1107929 := bstep (se 2 (by rfl) ⟨415473, by rfl⟩ : syracuseStep 1107929 = 830947) B830947
theorem B3565529 : Blo 738327 3565529 := bstep (se 2 (by rfl) ⟨1337073, by rfl⟩ : syracuseStep 3565529 = 2674147) B2674147
theorem B1665035 : Blo 738327 1665035 := bstep (se 1 (by rfl) ⟨1248776, by rfl⟩ : syracuseStep 1665035 = 2497553) B2497553
theorem B1665089 : Blo 738327 1665089 := bstep (se 2 (by rfl) ⟨624408, by rfl⟩ : syracuseStep 1665089 = 1248817) B1248817
theorem B1108043 : Blo 738327 1108043 := bstep (se 1 (by rfl) ⟨831032, by rfl⟩ : syracuseStep 1108043 = 1662065) B1662065
theorem B1337419 : Blo 738327 1337419 := bstep (se 1 (by rfl) ⟨1003064, by rfl⟩ : syracuseStep 1337419 = 2006129) B2006129
theorem B1108055 : Blo 738327 1108055 := bstep (se 1 (by rfl) ⟨831041, by rfl⟩ : syracuseStep 1108055 = 1662083) B1662083
theorem B1108121 : Blo 738327 1108121 := bstep (se 2 (by rfl) ⟨415545, by rfl⟩ : syracuseStep 1108121 = 831091) B831091
theorem B1108235 : Blo 738327 1108235 := bstep (se 1 (by rfl) ⟨831176, by rfl⟩ : syracuseStep 1108235 = 1662353) B1662353
theorem B1108247 : Blo 738327 1108247 := bstep (se 1 (by rfl) ⟨831185, by rfl⟩ : syracuseStep 1108247 = 1662371) B1662371
theorem B1665305 : Blo 738327 1665305 := bstep (se 2 (by rfl) ⟨624489, by rfl⟩ : syracuseStep 1665305 = 1248979) B1248979
theorem B3008819 : Blo 738327 3008819 := bstep (se 1 (by rfl) ⟨2256614, by rfl⟩ : syracuseStep 3008819 = 4513229) B4513229
theorem B1108313 : Blo 738327 1108313 := bstep (se 2 (by rfl) ⟨415617, by rfl⟩ : syracuseStep 1108313 = 831235) B831235
theorem B5630309 : Blo 738327 5630309 := bstep (se 4 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 5630309 = 1055683) B1055683
theorem B1665395 : Blo 738327 1665395 := bstep (se 1 (by rfl) ⟨1249046, by rfl⟩ : syracuseStep 1665395 = 2498093) B2498093
theorem B1665431 : Blo 738327 1665431 := bstep (se 1 (by rfl) ⟨1249073, by rfl⟩ : syracuseStep 1665431 = 2498147) B2498147
theorem B1108427 : Blo 738327 1108427 := bstep (se 1 (by rfl) ⟨831320, by rfl⟩ : syracuseStep 1108427 = 1662641) B1662641
theorem B1108439 : Blo 738327 1108439 := bstep (se 1 (by rfl) ⟨831329, by rfl⟩ : syracuseStep 1108439 = 1662659) B1662659
theorem B1108505 : Blo 738327 1108505 := bstep (se 2 (by rfl) ⟨415689, by rfl⟩ : syracuseStep 1108505 = 831379) B831379
theorem B3041837 : Blo 738327 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B1665611 : Blo 738327 1665611 := bstep (se 1 (by rfl) ⟨1249208, by rfl⟩ : syracuseStep 1665611 = 2498417) B2498417
theorem B1403507 : Blo 738327 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B1665665 : Blo 738327 1665665 := bstep (se 2 (by rfl) ⟨624624, by rfl⟩ : syracuseStep 1665665 = 1249249) B1249249
theorem B1108619 : Blo 738327 1108619 := bstep (se 1 (by rfl) ⟨831464, by rfl⟩ : syracuseStep 1108619 = 1662929) B1662929
theorem B1108631 : Blo 738327 1108631 := bstep (se 1 (by rfl) ⟨831473, by rfl⟩ : syracuseStep 1108631 = 1662947) B1662947
theorem B2812589 : Blo 738327 2812589 := bstep (se 3 (by rfl) ⟨527360, by rfl⟩ : syracuseStep 2812589 = 1054721) B1054721
theorem B1108697 : Blo 738327 1108697 := bstep (se 2 (by rfl) ⟨415761, by rfl⟩ : syracuseStep 1108697 = 831523) B831523
theorem B1403659 : Blo 738327 1403659 := bstep (se 1 (by rfl) ⟨1052744, by rfl⟩ : syracuseStep 1403659 = 2105489) B2105489
theorem B1502003 : Blo 738327 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1108811 : Blo 738327 1108811 := bstep (se 1 (by rfl) ⟨831608, by rfl⟩ : syracuseStep 1108811 = 1663217) B1663217
theorem B5630795 : Blo 738327 5630795 := bstep (se 1 (by rfl) ⟨4223096, by rfl⟩ : syracuseStep 5630795 = 8446193) B8446193
theorem B1108823 : Blo 738327 1108823 := bstep (se 1 (by rfl) ⟨831617, by rfl⟩ : syracuseStep 1108823 = 1663235) B1663235
theorem B1665881 : Blo 738327 1665881 := bstep (se 2 (by rfl) ⟨624705, by rfl⟩ : syracuseStep 1665881 = 1249411) B1249411
theorem B1108889 : Blo 738327 1108889 := bstep (se 2 (by rfl) ⟨415833, by rfl⟩ : syracuseStep 1108889 = 831667) B831667
theorem B1665971 : Blo 738327 1665971 := bstep (se 1 (by rfl) ⟨1249478, by rfl⟩ : syracuseStep 1665971 = 2498957) B2498957
theorem B1666007 : Blo 738327 1666007 := bstep (se 1 (by rfl) ⟨1249505, by rfl⟩ : syracuseStep 1666007 = 2499011) B2499011
theorem B1109003 : Blo 738327 1109003 := bstep (se 1 (by rfl) ⟨831752, by rfl⟩ : syracuseStep 1109003 = 1663505) B1663505
theorem B1109015 : Blo 738327 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B8121379 : Blo 738327 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B15199301 : Blo 738327 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1109081 : Blo 738327 1109081 := bstep (se 2 (by rfl) ⟨415905, by rfl⟩ : syracuseStep 1109081 = 831811) B831811
theorem B1403993 : Blo 738327 1403993 := bstep (se 2 (by rfl) ⟨526497, by rfl⟩ : syracuseStep 1403993 = 1052995) B1052995
theorem B1666187 : Blo 738327 1666187 := bstep (se 1 (by rfl) ⟨1249640, by rfl⟩ : syracuseStep 1666187 = 2499281) B2499281
theorem B1666241 : Blo 738327 1666241 := bstep (se 2 (by rfl) ⟨624840, by rfl⟩ : syracuseStep 1666241 = 1249681) B1249681
theorem B1109195 : Blo 738327 1109195 := bstep (se 1 (by rfl) ⟨831896, by rfl⟩ : syracuseStep 1109195 = 1663793) B1663793
theorem B1109207 : Blo 738327 1109207 := bstep (se 1 (by rfl) ⟨831905, by rfl⟩ : syracuseStep 1109207 = 1663811) B1663811
theorem B18935045 : Blo 738327 18935045 := bstep (se 4 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 18935045 = 3550321) B3550321
theorem B1109273 : Blo 738327 1109273 := bstep (se 2 (by rfl) ⟨415977, by rfl⟩ : syracuseStep 1109273 = 831955) B831955
theorem B1109387 : Blo 738327 1109387 := bstep (se 1 (by rfl) ⟨832040, by rfl⟩ : syracuseStep 1109387 = 1664081) B1664081
theorem B1109399 : Blo 738327 1109399 := bstep (se 1 (by rfl) ⟨832049, by rfl⟩ : syracuseStep 1109399 = 1664099) B1664099
theorem B1666457 : Blo 738327 1666457 := bstep (se 2 (by rfl) ⟨624921, by rfl⟩ : syracuseStep 1666457 = 1249843) B1249843
theorem B2813363 : Blo 738327 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B1109465 : Blo 738327 1109465 := bstep (se 2 (by rfl) ⟨416049, by rfl⟩ : syracuseStep 1109465 = 832099) B832099
theorem B12021209 : Blo 738327 12021209 := bstep (se 2 (by rfl) ⟨4507953, by rfl⟩ : syracuseStep 12021209 = 9015907) B9015907
theorem B1666547 : Blo 738327 1666547 := bstep (se 1 (by rfl) ⟨1249910, by rfl⟩ : syracuseStep 1666547 = 2499821) B2499821
theorem B1666583 : Blo 738327 1666583 := bstep (se 1 (by rfl) ⟨1249937, by rfl⟩ : syracuseStep 1666583 = 2499875) B2499875
theorem B4222529 : Blo 738327 4222529 := bstep (se 2 (by rfl) ⟨1583448, by rfl⟩ : syracuseStep 4222529 = 3166897) B3166897
theorem B1109579 : Blo 738327 1109579 := bstep (se 1 (by rfl) ⟨832184, by rfl⟩ : syracuseStep 1109579 = 1664369) B1664369
theorem B1109591 : Blo 738327 1109591 := bstep (se 1 (by rfl) ⟨832193, by rfl⟩ : syracuseStep 1109591 = 1664387) B1664387
theorem B1109657 : Blo 738327 1109657 := bstep (se 2 (by rfl) ⟨416121, by rfl⟩ : syracuseStep 1109657 = 832243) B832243
theorem B1666763 : Blo 738327 1666763 := bstep (se 1 (by rfl) ⟨1250072, by rfl⟩ : syracuseStep 1666763 = 2500145) B2500145
theorem B1404631 : Blo 738327 1404631 := bstep (se 1 (by rfl) ⟨1053473, by rfl⟩ : syracuseStep 1404631 = 2106947) B2106947
theorem B1666817 : Blo 738327 1666817 := bstep (se 2 (by rfl) ⟨625056, by rfl⟩ : syracuseStep 1666817 = 1250113) B1250113
theorem B1109771 : Blo 738327 1109771 := bstep (se 1 (by rfl) ⟨832328, by rfl⟩ : syracuseStep 1109771 = 1664657) B1664657
theorem B1109783 : Blo 738327 1109783 := bstep (se 1 (by rfl) ⟨832337, by rfl⟩ : syracuseStep 1109783 = 1664675) B1664675
theorem B1109849 : Blo 738327 1109849 := bstep (se 2 (by rfl) ⟨416193, by rfl⟩ : syracuseStep 1109849 = 832387) B832387
theorem B1109963 : Blo 738327 1109963 := bstep (se 1 (by rfl) ⟨832472, by rfl⟩ : syracuseStep 1109963 = 1664945) B1664945
theorem B1109975 : Blo 738327 1109975 := bstep (se 1 (by rfl) ⟨832481, by rfl⟩ : syracuseStep 1109975 = 1664963) B1664963
theorem B1667033 : Blo 738327 1667033 := bstep (se 2 (by rfl) ⟨625137, by rfl⟩ : syracuseStep 1667033 = 1250275) B1250275
theorem B1110041 : Blo 738327 1110041 := bstep (se 2 (by rfl) ⟨416265, by rfl⟩ : syracuseStep 1110041 = 832531) B832531
theorem B1667123 : Blo 738327 1667123 := bstep (se 1 (by rfl) ⟨1250342, by rfl⟩ : syracuseStep 1667123 = 2500685) B2500685
theorem B1667159 : Blo 738327 1667159 := bstep (se 1 (by rfl) ⟨1250369, by rfl⟩ : syracuseStep 1667159 = 2500739) B2500739
theorem B749675 : Blo 738327 749675 := bstep (se 1 (by rfl) ⟨562256, by rfl⟩ : syracuseStep 749675 = 1124513) B1124513
theorem B1110155 : Blo 738327 1110155 := bstep (se 1 (by rfl) ⟨832616, by rfl⟩ : syracuseStep 1110155 = 1665233) B1665233
theorem B1110167 : Blo 738327 1110167 := bstep (se 1 (by rfl) ⟨832625, by rfl⟩ : syracuseStep 1110167 = 1665251) B1665251
theorem B1110233 : Blo 738327 1110233 := bstep (se 2 (by rfl) ⟨416337, by rfl⟩ : syracuseStep 1110233 = 832675) B832675
theorem B1667339 : Blo 738327 1667339 := bstep (se 1 (by rfl) ⟨1250504, by rfl⟩ : syracuseStep 1667339 = 2501009) B2501009
theorem B1667393 : Blo 738327 1667393 := bstep (se 2 (by rfl) ⟨625272, by rfl⟩ : syracuseStep 1667393 = 1250545) B1250545
theorem B1110347 : Blo 738327 1110347 := bstep (se 1 (by rfl) ⟨832760, by rfl⟩ : syracuseStep 1110347 = 1665521) B1665521
theorem B1110359 : Blo 738327 1110359 := bstep (se 1 (by rfl) ⟨832769, by rfl⟩ : syracuseStep 1110359 = 1665539) B1665539
theorem B1110425 : Blo 738327 1110425 := bstep (se 2 (by rfl) ⟨416409, by rfl⟩ : syracuseStep 1110425 = 832819) B832819
theorem B1405451 : Blo 738327 1405451 := bstep (se 1 (by rfl) ⟨1054088, by rfl⟩ : syracuseStep 1405451 = 2108177) B2108177
theorem B1110539 : Blo 738327 1110539 := bstep (se 1 (by rfl) ⟨832904, by rfl⟩ : syracuseStep 1110539 = 1665809) B1665809
theorem B1110551 : Blo 738327 1110551 := bstep (se 1 (by rfl) ⟨832913, by rfl⟩ : syracuseStep 1110551 = 1665827) B1665827
theorem B1667609 : Blo 738327 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B1405505 : Blo 738327 1405505 := bstep (se 2 (by rfl) ⟨527064, by rfl⟩ : syracuseStep 1405505 = 1054129) B1054129
theorem B1110617 : Blo 738327 1110617 := bstep (se 2 (by rfl) ⟨416481, by rfl⟩ : syracuseStep 1110617 = 832963) B832963
theorem B1667699 : Blo 738327 1667699 := bstep (se 1 (by rfl) ⟨1250774, by rfl⟩ : syracuseStep 1667699 = 2501549) B2501549
theorem B1667735 : Blo 738327 1667735 := bstep (se 1 (by rfl) ⟨1250801, by rfl⟩ : syracuseStep 1667735 = 2501603) B2501603
theorem B1110731 : Blo 738327 1110731 := bstep (se 1 (by rfl) ⟨833048, by rfl⟩ : syracuseStep 1110731 = 1666097) B1666097
theorem B1110743 : Blo 738327 1110743 := bstep (se 1 (by rfl) ⟨833057, by rfl⟩ : syracuseStep 1110743 = 1666115) B1666115
theorem B1110809 : Blo 738327 1110809 := bstep (se 2 (by rfl) ⟨416553, by rfl⟩ : syracuseStep 1110809 = 833107) B833107
theorem B1667915 : Blo 738327 1667915 := bstep (se 1 (by rfl) ⟨1250936, by rfl⟩ : syracuseStep 1667915 = 2501873) B2501873
theorem B1667969 : Blo 738327 1667969 := bstep (se 2 (by rfl) ⟨625488, by rfl⟩ : syracuseStep 1667969 = 1250977) B1250977
theorem B2814851 : Blo 738327 2814851 := bstep (se 1 (by rfl) ⟨2111138, by rfl⟩ : syracuseStep 2814851 = 4222277) B4222277
theorem B1110923 : Blo 738327 1110923 := bstep (se 1 (by rfl) ⟨833192, by rfl⟩ : syracuseStep 1110923 = 1666385) B1666385
theorem B1110935 : Blo 738327 1110935 := bstep (se 1 (by rfl) ⟨833201, by rfl⟩ : syracuseStep 1110935 = 1666403) B1666403
theorem B1111001 : Blo 738327 1111001 := bstep (se 2 (by rfl) ⟨416625, by rfl⟩ : syracuseStep 1111001 = 833251) B833251
theorem B1111115 : Blo 738327 1111115 := bstep (se 1 (by rfl) ⟨833336, by rfl⟩ : syracuseStep 1111115 = 1666673) B1666673
theorem B1111127 : Blo 738327 1111127 := bstep (se 1 (by rfl) ⟨833345, by rfl⟩ : syracuseStep 1111127 = 1666691) B1666691
theorem B1668185 : Blo 738327 1668185 := bstep (se 2 (by rfl) ⟨625569, by rfl⟩ : syracuseStep 1668185 = 1251139) B1251139
theorem B1504345 : Blo 738327 1504345 := bstep (se 2 (by rfl) ⟨564129, by rfl⟩ : syracuseStep 1504345 = 1128259) B1128259
theorem B1111193 : Blo 738327 1111193 := bstep (se 2 (by rfl) ⟨416697, by rfl⟩ : syracuseStep 1111193 = 833395) B833395
theorem B1799347 : Blo 738327 1799347 := bstep (se 1 (by rfl) ⟨1349510, by rfl⟩ : syracuseStep 1799347 = 2699021) B2699021
theorem B1668275 : Blo 738327 1668275 := bstep (se 1 (by rfl) ⟨1251206, by rfl⟩ : syracuseStep 1668275 = 2502413) B2502413
theorem B1668311 : Blo 738327 1668311 := bstep (se 1 (by rfl) ⟨1251233, by rfl⟩ : syracuseStep 1668311 = 2502467) B2502467
theorem B1111307 : Blo 738327 1111307 := bstep (se 1 (by rfl) ⟨833480, by rfl⟩ : syracuseStep 1111307 = 1666961) B1666961
theorem B1111319 : Blo 738327 1111319 := bstep (se 1 (by rfl) ⟨833489, by rfl⟩ : syracuseStep 1111319 = 1666979) B1666979
theorem B5076269 : Blo 738327 5076269 := bstep (se 3 (by rfl) ⟨951800, by rfl⟩ : syracuseStep 5076269 = 1903601) B1903601
theorem B2815307 : Blo 738327 2815307 := bstep (se 1 (by rfl) ⟨2111480, by rfl⟩ : syracuseStep 2815307 = 4222961) B4222961
theorem B1111385 : Blo 738327 1111385 := bstep (se 2 (by rfl) ⟨416769, by rfl⟩ : syracuseStep 1111385 = 833539) B833539
theorem B1668491 : Blo 738327 1668491 := bstep (se 1 (by rfl) ⟨1251368, by rfl⟩ : syracuseStep 1668491 = 2502737) B2502737
theorem B4617623 : Blo 738327 4617623 := bstep (se 1 (by rfl) ⟨3463217, by rfl⟩ : syracuseStep 4617623 = 6926435) B6926435
theorem B1668545 : Blo 738327 1668545 := bstep (se 2 (by rfl) ⟨625704, by rfl⟩ : syracuseStep 1668545 = 1251409) B1251409
theorem B1111499 : Blo 738327 1111499 := bstep (se 1 (by rfl) ⟨833624, by rfl⟩ : syracuseStep 1111499 = 1667249) B1667249
theorem B1406423 : Blo 738327 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B1111511 : Blo 738327 1111511 := bstep (se 1 (by rfl) ⟨833633, by rfl⟩ : syracuseStep 1111511 = 1667267) B1667267
theorem B2815505 : Blo 738327 2815505 := bstep (se 2 (by rfl) ⟨1055814, by rfl⟩ : syracuseStep 2815505 = 2111629) B2111629
theorem B1111577 : Blo 738327 1111577 := bstep (se 2 (by rfl) ⟨416841, by rfl⟩ : syracuseStep 1111577 = 833683) B833683
theorem B1111691 : Blo 738327 1111691 := bstep (se 1 (by rfl) ⟨833768, by rfl⟩ : syracuseStep 1111691 = 1667537) B1667537
theorem B1111703 : Blo 738327 1111703 := bstep (se 1 (by rfl) ⟨833777, by rfl⟩ : syracuseStep 1111703 = 1667555) B1667555
theorem B1668761 : Blo 738327 1668761 := bstep (se 2 (by rfl) ⟨625785, by rfl⟩ : syracuseStep 1668761 = 1251571) B1251571
theorem B1111769 : Blo 738327 1111769 := bstep (se 2 (by rfl) ⟨416913, by rfl⟩ : syracuseStep 1111769 = 833827) B833827
theorem B1668851 : Blo 738327 1668851 := bstep (se 1 (by rfl) ⟨1251638, by rfl⟩ : syracuseStep 1668851 = 2503277) B2503277
theorem B1668887 : Blo 738327 1668887 := bstep (se 1 (by rfl) ⟨1251665, by rfl⟩ : syracuseStep 1668887 = 2503331) B2503331
theorem B751403 : Blo 738327 751403 := bstep (se 1 (by rfl) ⟨563552, by rfl⟩ : syracuseStep 751403 = 1127105) B1127105
theorem B1111883 : Blo 738327 1111883 := bstep (se 1 (by rfl) ⟨833912, by rfl⟩ : syracuseStep 1111883 = 1667825) B1667825
theorem B1111895 : Blo 738327 1111895 := bstep (se 1 (by rfl) ⟨833921, by rfl⟩ : syracuseStep 1111895 = 1667843) B1667843
theorem B13006693 : Blo 738327 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B4224919 : Blo 738327 4224919 := bstep (se 1 (by rfl) ⟨3168689, by rfl⟩ : syracuseStep 4224919 = 6337379) B6337379
theorem B1111961 : Blo 738327 1111961 := bstep (se 2 (by rfl) ⟨416985, by rfl⟩ : syracuseStep 1111961 = 833971) B833971
theorem B1669067 : Blo 738327 1669067 := bstep (se 1 (by rfl) ⟨1251800, by rfl⟩ : syracuseStep 1669067 = 2503601) B2503601
theorem B1406963 : Blo 738327 1406963 := bstep (se 1 (by rfl) ⟨1055222, by rfl⟩ : syracuseStep 1406963 = 2110445) B2110445
theorem B1669121 : Blo 738327 1669121 := bstep (se 2 (by rfl) ⟨625920, by rfl⟩ : syracuseStep 1669121 = 1251841) B1251841
theorem B1112075 : Blo 738327 1112075 := bstep (se 1 (by rfl) ⟨834056, by rfl⟩ : syracuseStep 1112075 = 1668113) B1668113
theorem B1112087 : Blo 738327 1112087 := bstep (se 1 (by rfl) ⟨834065, by rfl⟩ : syracuseStep 1112087 = 1668131) B1668131
theorem B1112153 : Blo 738327 1112153 := bstep (se 2 (by rfl) ⟨417057, by rfl⟩ : syracuseStep 1112153 = 834115) B834115
theorem B10647683 : Blo 738327 10647683 := bstep (se 1 (by rfl) ⟨7985762, by rfl⟩ : syracuseStep 10647683 = 15971525) B15971525
theorem B1112267 : Blo 738327 1112267 := bstep (se 1 (by rfl) ⟨834200, by rfl⟩ : syracuseStep 1112267 = 1668401) B1668401
theorem B1112279 : Blo 738327 1112279 := bstep (se 1 (by rfl) ⟨834209, by rfl⟩ : syracuseStep 1112279 = 1668419) B1668419
theorem B1669337 : Blo 738327 1669337 := bstep (se 2 (by rfl) ⟨626001, by rfl⟩ : syracuseStep 1669337 = 1252003) B1252003
theorem B2816279 : Blo 738327 2816279 := bstep (se 1 (by rfl) ⟨2112209, by rfl⟩ : syracuseStep 2816279 = 4224419) B4224419
theorem B1112345 : Blo 738327 1112345 := bstep (se 2 (by rfl) ⟨417129, by rfl⟩ : syracuseStep 1112345 = 834259) B834259
theorem B1669427 : Blo 738327 1669427 := bstep (se 1 (by rfl) ⟨1252070, by rfl⟩ : syracuseStep 1669427 = 2504141) B2504141
theorem B12351809 : Blo 738327 12351809 := bstep (se 2 (by rfl) ⟨4631928, by rfl⟩ : syracuseStep 12351809 = 9263857) B9263857
theorem B1669463 : Blo 738327 1669463 := bstep (se 1 (by rfl) ⟨1252097, by rfl⟩ : syracuseStep 1669463 = 2504195) B2504195
theorem B1112459 : Blo 738327 1112459 := bstep (se 1 (by rfl) ⟨834344, by rfl⟩ : syracuseStep 1112459 = 1668689) B1668689
theorem B1112471 : Blo 738327 1112471 := bstep (se 1 (by rfl) ⟨834353, by rfl⟩ : syracuseStep 1112471 = 1668707) B1668707
theorem B1407449 : Blo 738327 1407449 := bstep (se 2 (by rfl) ⟨527793, by rfl⟩ : syracuseStep 1407449 = 1055587) B1055587
theorem B1112537 : Blo 738327 1112537 := bstep (se 2 (by rfl) ⟨417201, by rfl⟩ : syracuseStep 1112537 = 834403) B834403
theorem B2816477 : Blo 738327 2816477 := bstep (se 3 (by rfl) ⟨528089, by rfl⟩ : syracuseStep 2816477 = 1056179) B1056179
theorem B1669643 : Blo 738327 1669643 := bstep (se 1 (by rfl) ⟨1252232, by rfl⟩ : syracuseStep 1669643 = 2504465) B2504465
theorem B1669697 : Blo 738327 1669697 := bstep (se 2 (by rfl) ⟨626136, by rfl⟩ : syracuseStep 1669697 = 1252273) B1252273
theorem B1112651 : Blo 738327 1112651 := bstep (se 1 (by rfl) ⟨834488, by rfl⟩ : syracuseStep 1112651 = 1668977) B1668977
theorem B1112663 : Blo 738327 1112663 := bstep (se 1 (by rfl) ⟨834497, by rfl⟩ : syracuseStep 1112663 = 1668995) B1668995
theorem B1112729 : Blo 738327 1112729 := bstep (se 2 (by rfl) ⟨417273, by rfl⟩ : syracuseStep 1112729 = 834547) B834547
theorem B1112843 : Blo 738327 1112843 := bstep (se 1 (by rfl) ⟨834632, by rfl⟩ : syracuseStep 1112843 = 1669265) B1669265
theorem B1112855 : Blo 738327 1112855 := bstep (se 1 (by rfl) ⟨834641, by rfl⟩ : syracuseStep 1112855 = 1669283) B1669283
theorem B1669913 : Blo 738327 1669913 := bstep (se 2 (by rfl) ⟨626217, by rfl⟩ : syracuseStep 1669913 = 1252435) B1252435
theorem B1112921 : Blo 738327 1112921 := bstep (se 2 (by rfl) ⟨417345, by rfl⟩ : syracuseStep 1112921 = 834691) B834691
theorem B1670003 : Blo 738327 1670003 := bstep (se 1 (by rfl) ⟨1252502, by rfl⟩ : syracuseStep 1670003 = 2505005) B2505005
theorem B1670039 : Blo 738327 1670039 := bstep (se 1 (by rfl) ⟨1252529, by rfl⟩ : syracuseStep 1670039 = 2505059) B2505059
theorem B6421427 : Blo 738327 6421427 := bstep (se 1 (by rfl) ⟨4816070, by rfl⟩ : syracuseStep 6421427 = 9632141) B9632141
theorem B1113035 : Blo 738327 1113035 := bstep (se 1 (by rfl) ⟨834776, by rfl⟩ : syracuseStep 1113035 = 1669553) B1669553
theorem B1113047 : Blo 738327 1113047 := bstep (se 1 (by rfl) ⟨834785, by rfl⟩ : syracuseStep 1113047 = 1669571) B1669571
theorem B1113113 : Blo 738327 1113113 := bstep (se 2 (by rfl) ⟨417417, by rfl⟩ : syracuseStep 1113113 = 834835) B834835
theorem B1670219 : Blo 738327 1670219 := bstep (se 1 (by rfl) ⟨1252664, by rfl⟩ : syracuseStep 1670219 = 2505329) B2505329
theorem B1113227 : Blo 738327 1113227 := bstep (se 1 (by rfl) ⟨834920, by rfl⟩ : syracuseStep 1113227 = 1669841) B1669841
theorem B1113239 : Blo 738327 1113239 := bstep (se 1 (by rfl) ⟨834929, by rfl⟩ : syracuseStep 1113239 = 1669859) B1669859
theorem B1113305 : Blo 738327 1113305 := bstep (se 2 (by rfl) ⟨417489, by rfl⟩ : syracuseStep 1113305 = 834979) B834979
theorem B5078317 : Blo 738327 5078317 := bstep (se 3 (by rfl) ⟨952184, by rfl⟩ : syracuseStep 5078317 = 1904369) B1904369
theorem B1113419 : Blo 738327 1113419 := bstep (se 1 (by rfl) ⟨835064, by rfl⟩ : syracuseStep 1113419 = 1670129) B1670129
theorem B1113431 : Blo 738327 1113431 := bstep (se 1 (by rfl) ⟨835073, by rfl⟩ : syracuseStep 1113431 = 1670147) B1670147
theorem B5340593 : Blo 738327 5340593 := bstep (se 2 (by rfl) ⟨2002722, by rfl⟩ : syracuseStep 5340593 = 4005445) B4005445
theorem B7110179 : Blo 738327 7110179 := bstep (se 1 (by rfl) ⟨5332634, by rfl⟩ : syracuseStep 7110179 = 10665269) B10665269
theorem B3243671 : Blo 738327 3243671 := bstep (se 1 (by rfl) ⟨2432753, by rfl⟩ : syracuseStep 3243671 = 4865507) B4865507
theorem B9633653 : Blo 738327 9633653 := bstep (se 5 (by rfl) ⟨451577, by rfl⟩ : syracuseStep 9633653 = 903155) B903155
theorem B1408907 : Blo 738327 1408907 := bstep (se 1 (by rfl) ⟨1056680, by rfl⟩ : syracuseStep 1408907 = 2113361) B2113361
theorem B40468403 : Blo 738327 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B1999133 : Blo 738327 1999133 := bstep (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) B749675
theorem B1868953 : Blo 738327 1868953 := bstep (se 2 (by rfl) ⟨700857, by rfl⟩ : syracuseStep 1868953 = 1401715) B1401715
theorem B1869115 : Blo 738327 1869115 := bstep (se 1 (by rfl) ⟨1401836, by rfl⟩ : syracuseStep 1869115 = 2803673) B2803673
theorem B1246583 : Blo 738327 1246583 := bstep (se 1 (by rfl) ⟨934937, by rfl⟩ : syracuseStep 1246583 = 1869875) B1869875
theorem B1869257 : Blo 738327 1869257 := bstep (se 2 (by rfl) ⟨700971, by rfl⟩ : syracuseStep 1869257 = 1401943) B1401943
theorem B6489553 : Blo 738327 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B8422865 : Blo 738327 8422865 := bstep (se 2 (by rfl) ⟨3158574, by rfl⟩ : syracuseStep 8422865 = 6317149) B6317149
theorem B2491991 : Blo 738327 2491991 := bstep (se 1 (by rfl) ⟨1868993, by rfl⟩ : syracuseStep 2491991 = 3737987) B3737987
theorem B1869601 : Blo 738327 1869601 := bstep (se 2 (by rfl) ⟨701100, by rfl⟩ : syracuseStep 1869601 = 1402201) B1402201
theorem B7702307 : Blo 738327 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B1247035 : Blo 738327 1247035 := bstep (se 1 (by rfl) ⟨935276, by rfl⟩ : syracuseStep 1247035 = 1870553) B1870553
theorem B4753241 : Blo 738327 4753241 := bstep (se 2 (by rfl) ⟨1782465, by rfl⟩ : syracuseStep 4753241 = 3564931) B3564931
theorem B1247177 : Blo 738327 1247177 := bstep (se 2 (by rfl) ⟨467691, by rfl⟩ : syracuseStep 1247177 = 935383) B935383
theorem B2492477 : Blo 738327 2492477 := bstep (se 3 (by rfl) ⟨467339, by rfl⟩ : syracuseStep 2492477 = 934679) B934679
theorem B1870199 : Blo 738327 1870199 := bstep (se 1 (by rfl) ⟨1402649, by rfl⟩ : syracuseStep 1870199 = 2805299) B2805299
theorem B854407 : Blo 738327 854407 := bstep (se 1 (by rfl) ⟨640805, by rfl⟩ : syracuseStep 854407 = 1281611) B1281611
theorem B1247879 : Blo 738327 1247879 := bstep (se 1 (by rfl) ⟨935909, by rfl⟩ : syracuseStep 1247879 = 1871819) B1871819
theorem B1051321 : Blo 738327 1051321 := bstep (se 2 (by rfl) ⟨394245, by rfl⟩ : syracuseStep 1051321 = 788491) B788491
theorem B3738635 : Blo 738327 3738635 := bstep (se 1 (by rfl) ⟨2803976, by rfl⟩ : syracuseStep 3738635 = 5607953) B5607953
theorem B3738797 : Blo 738327 3738797 := bstep (se 3 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 3738797 = 1402049) B1402049
theorem B12618989 : Blo 738327 12618989 := bstep (se 3 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 12618989 = 4732121) B4732121
theorem B1248527 : Blo 738327 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B2854291 : Blo 738327 2854291 := bstep (se 1 (by rfl) ⟨2140718, by rfl⟩ : syracuseStep 2854291 = 4281437) B4281437
theorem B2493881 : Blo 738327 2493881 := bstep (se 2 (by rfl) ⟨935205, by rfl⟩ : syracuseStep 2493881 = 1870411) B1870411
theorem B1871495 : Blo 738327 1871495 := bstep (se 1 (by rfl) ⟨1403621, by rfl⟩ : syracuseStep 1871495 = 2807243) B2807243
theorem B1871545 : Blo 738327 1871545 := bstep (se 2 (by rfl) ⟨701829, by rfl⟩ : syracuseStep 1871545 = 1403659) B1403659
theorem B1249067 : Blo 738327 1249067 := bstep (se 1 (by rfl) ⟨936800, by rfl⟩ : syracuseStep 1249067 = 1873601) B1873601
theorem B1052551 : Blo 738327 1052551 := bstep (se 1 (by rfl) ⟨789413, by rfl⟩ : syracuseStep 1052551 = 1578827) B1578827
theorem B7606219 : Blo 738327 7606219 := bstep (se 1 (by rfl) ⟨5704664, by rfl⟩ : syracuseStep 7606219 = 11409329) B11409329
theorem B2494475 : Blo 738327 2494475 := bstep (se 1 (by rfl) ⟨1870856, by rfl⟩ : syracuseStep 2494475 = 3741713) B3741713
theorem B2494583 : Blo 738327 2494583 := bstep (se 1 (by rfl) ⟨1870937, by rfl⟩ : syracuseStep 2494583 = 3741875) B3741875
theorem B889003 : Blo 738327 889003 := bstep (se 1 (by rfl) ⟨666752, by rfl⟩ : syracuseStep 889003 = 1333505) B1333505
theorem B1249465 : Blo 738327 1249465 := bstep (se 2 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 1249465 = 937099) B937099
theorem B1577161 : Blo 738327 1577161 := bstep (se 2 (by rfl) ⟨591435, by rfl⟩ : syracuseStep 1577161 = 1182871) B1182871
theorem B35983601 : Blo 738327 35983601 := bstep (se 2 (by rfl) ⟨13493850, by rfl⟩ : syracuseStep 35983601 = 26987701) B26987701
theorem B1872143 : Blo 738327 1872143 := bstep (se 1 (by rfl) ⟨1404107, by rfl⟩ : syracuseStep 1872143 = 2808215) B2808215
theorem B2855227 : Blo 738327 2855227 := bstep (se 1 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 2855227 = 4282841) B4282841
theorem B1708489 : Blo 738327 1708489 := bstep (se 2 (by rfl) ⟨640683, by rfl⟩ : syracuseStep 1708489 = 1281367) B1281367
theorem B1053371 : Blo 738327 1053371 := bstep (se 1 (by rfl) ⟨790028, by rfl⟩ : syracuseStep 1053371 = 1580057) B1580057
theorem B2495177 : Blo 738327 2495177 := bstep (se 2 (by rfl) ⟨935691, by rfl⟩ : syracuseStep 2495177 = 1871383) B1871383
theorem B3740417 : Blo 738327 3740417 := bstep (se 2 (by rfl) ⟨1402656, by rfl⟩ : syracuseStep 3740417 = 2805313) B2805313
theorem B2003741 : Blo 738327 2003741 := bstep (se 3 (by rfl) ⟨375701, by rfl⟩ : syracuseStep 2003741 = 751403) B751403
theorem B6001523 : Blo 738327 6001523 := bstep (se 1 (by rfl) ⟨4501142, by rfl⟩ : syracuseStep 6001523 = 9002285) B9002285
theorem B1250167 : Blo 738327 1250167 := bstep (se 1 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 1250167 = 1875251) B1875251
theorem B1774489 : Blo 738327 1774489 := bstep (se 2 (by rfl) ⟨665433, by rfl⟩ : syracuseStep 1774489 = 1330867) B1330867
theorem B1872841 : Blo 738327 1872841 := bstep (se 2 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 1872841 = 1404631) B1404631
theorem B1250363 : Blo 738327 1250363 := bstep (se 1 (by rfl) ⟨937772, by rfl⟩ : syracuseStep 1250363 = 1875545) B1875545
theorem B1872983 : Blo 738327 1872983 := bstep (se 1 (by rfl) ⟨1404737, by rfl⟩ : syracuseStep 1872983 = 2809475) B2809475
theorem B1053815 : Blo 738327 1053815 := bstep (se 1 (by rfl) ⟨790361, by rfl⟩ : syracuseStep 1053815 = 1580723) B1580723
theorem B1054009 : Blo 738327 1054009 := bstep (se 2 (by rfl) ⟨395253, by rfl⟩ : syracuseStep 1054009 = 790507) B790507
theorem B2495879 : Blo 738327 2495879 := bstep (se 1 (by rfl) ⟨1871909, by rfl⟩ : syracuseStep 2495879 = 3743819) B3743819
theorem B1250761 : Blo 738327 1250761 := bstep (se 2 (by rfl) ⟨469035, by rfl⟩ : syracuseStep 1250761 = 938071) B938071
theorem B5608925 : Blo 738327 5608925 := bstep (se 3 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 5608925 = 2103347) B2103347
theorem B1775105 : Blo 738327 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B3741227 : Blo 738327 3741227 := bstep (se 1 (by rfl) ⟨2805920, by rfl⟩ : syracuseStep 3741227 = 5611841) B5611841
theorem B7116407 : Blo 738327 7116407 := bstep (se 1 (by rfl) ⟨5337305, by rfl⟩ : syracuseStep 7116407 = 10674611) B10674611
theorem B5346935 : Blo 738327 5346935 := bstep (se 1 (by rfl) ⟨4010201, by rfl⟩ : syracuseStep 5346935 = 8020403) B8020403
theorem B9508529 : Blo 738327 9508529 := bstep (se 2 (by rfl) ⟨3565698, by rfl⟩ : syracuseStep 9508529 = 7131397) B7131397
theorem B2496257 : Blo 738327 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B2103155 : Blo 738327 2103155 := bstep (se 1 (by rfl) ⟨1577366, by rfl⟩ : syracuseStep 2103155 = 3154733) B3154733
theorem B7313267 : Blo 738327 7313267 := bstep (se 1 (by rfl) ⟨5484950, by rfl⟩ : syracuseStep 7313267 = 10969901) B10969901
theorem B1185671 : Blo 738327 1185671 := bstep (se 1 (by rfl) ⟨889253, by rfl⟩ : syracuseStep 1185671 = 1778507) B1778507
theorem B890767 : Blo 738327 890767 := bstep (se 1 (by rfl) ⟨668075, by rfl⟩ : syracuseStep 890767 = 1336151) B1336151
theorem B890887 : Blo 738327 890887 := bstep (se 1 (by rfl) ⟨668165, by rfl⟩ : syracuseStep 890887 = 1336331) B1336331
theorem B1251463 : Blo 738327 1251463 := bstep (se 1 (by rfl) ⟨938597, by rfl⟩ : syracuseStep 1251463 = 1877195) B1877195
theorem B32938157 : Blo 738327 32938157 := bstep (se 3 (by rfl) ⟨6175904, by rfl⟩ : syracuseStep 32938157 = 12351809) B12351809
theorem B4004147 : Blo 738327 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B4004363 : Blo 738327 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B1776161 : Blo 738327 1776161 := bstep (se 2 (by rfl) ⟨666060, by rfl⟩ : syracuseStep 1776161 = 1332121) B1332121
theorem B2497067 : Blo 738327 2497067 := bstep (se 1 (by rfl) ⟨1872800, by rfl⟩ : syracuseStep 2497067 = 3745601) B3745601
theorem B1252111 : Blo 738327 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B2005793 : Blo 738327 2005793 := bstep (se 2 (by rfl) ⟨752172, by rfl⟩ : syracuseStep 2005793 = 1504345) B1504345
theorem B3742523 : Blo 738327 3742523 := bstep (se 1 (by rfl) ⟨2806892, by rfl⟩ : syracuseStep 3742523 = 5613785) B5613785
theorem B1579895 : Blo 738327 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B2005879 : Blo 738327 2005879 := bstep (se 1 (by rfl) ⟨1504409, by rfl⟩ : syracuseStep 2005879 = 3008819) B3008819
theorem B2399129 : Blo 738327 2399129 := bstep (se 2 (by rfl) ⟨899673, by rfl⟩ : syracuseStep 2399129 = 1799347) B1799347
theorem B3742685 : Blo 738327 3742685 := bstep (se 3 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 3742685 = 1403507) B1403507
theorem B17538053 : Blo 738327 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B1875059 : Blo 738327 1875059 := bstep (se 1 (by rfl) ⟨1406294, by rfl⟩ : syracuseStep 1875059 = 2812589) B2812589
theorem B3743009 : Blo 738327 3743009 := bstep (se 2 (by rfl) ⟨1403628, by rfl⟩ : syracuseStep 3743009 = 2807257) B2807257
theorem B1252651 : Blo 738327 1252651 := bstep (se 1 (by rfl) ⟨939488, by rfl⟩ : syracuseStep 1252651 = 1878977) B1878977
theorem B2366779 : Blo 738327 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B1580347 : Blo 738327 1580347 := bstep (se 1 (by rfl) ⟨1185260, by rfl⟩ : syracuseStep 1580347 = 2370521) B2370521
theorem B10132867 : Blo 738327 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B12623363 : Blo 738327 12623363 := bstep (se 1 (by rfl) ⟨9467522, by rfl⟩ : syracuseStep 12623363 = 18935045) B18935045
theorem B1875575 : Blo 738327 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B17342257 : Blo 738327 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B2498363 : Blo 738327 2498363 := bstep (se 1 (by rfl) ⟨1873772, by rfl⟩ : syracuseStep 2498363 = 3747545) B3747545
theorem B3743981 : Blo 738327 3743981 := bstep (se 3 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 3743981 = 1403993) B1403993
theorem B2105615 : Blo 738327 2105615 := bstep (se 1 (by rfl) ⟨1579211, by rfl⟩ : syracuseStep 2105615 = 3158423) B3158423
theorem B2498849 : Blo 738327 2498849 := bstep (se 2 (by rfl) ⟨937068, by rfl⟩ : syracuseStep 2498849 = 1874137) B1874137
theorem B1122761 : Blo 738327 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B1581611 : Blo 738327 1581611 := bstep (se 1 (by rfl) ⟨1186208, by rfl⟩ : syracuseStep 1581611 = 2372417) B2372417
theorem B2368061 : Blo 738327 2368061 := bstep (se 3 (by rfl) ⟨444011, by rfl⟩ : syracuseStep 2368061 = 888023) B888023
theorem B6333005 : Blo 738327 6333005 := bstep (se 3 (by rfl) ⟨1187438, by rfl⟩ : syracuseStep 6333005 = 2374877) B2374877
theorem B1876567 : Blo 738327 1876567 := bstep (se 1 (by rfl) ⟨1407425, by rfl⟩ : syracuseStep 1876567 = 2814851) B2814851
theorem B4006745 : Blo 738327 4006745 := bstep (se 2 (by rfl) ⟨1502529, by rfl⟩ : syracuseStep 4006745 = 3005059) B3005059
theorem B2499443 : Blo 738327 2499443 := bstep (se 1 (by rfl) ⟨1874582, by rfl⟩ : syracuseStep 2499443 = 3749165) B3749165
theorem B3384179 : Blo 738327 3384179 := bstep (se 1 (by rfl) ⟨2538134, by rfl⟩ : syracuseStep 3384179 = 5076269) B5076269
theorem B1876871 : Blo 738327 1876871 := bstep (se 1 (by rfl) ⟨1407653, by rfl⟩ : syracuseStep 1876871 = 2815307) B2815307
theorem B1877003 : Blo 738327 1877003 := bstep (se 1 (by rfl) ⟨1407752, by rfl⟩ : syracuseStep 1877003 = 2815505) B2815505
theorem B3744791 : Blo 738327 3744791 := bstep (se 1 (by rfl) ⟨2808593, by rfl⟩ : syracuseStep 3744791 = 5617187) B5617187
theorem B7611479 : Blo 738327 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B1877519 : Blo 738327 1877519 := bstep (se 1 (by rfl) ⟨1408139, by rfl⟩ : syracuseStep 1877519 = 2816279) B2816279
theorem B1877651 : Blo 738327 1877651 := bstep (se 1 (by rfl) ⟨1408238, by rfl⟩ : syracuseStep 1877651 = 2816477) B2816477
theorem B1779353 : Blo 738327 1779353 := bstep (se 2 (by rfl) ⟨667257, by rfl⟩ : syracuseStep 1779353 = 1334515) B1334515
theorem B12658355 : Blo 738327 12658355 := bstep (se 1 (by rfl) ⟨9493766, by rfl⟩ : syracuseStep 12658355 = 18987533) B18987533
theorem B2107255 : Blo 738327 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B2107289 : Blo 738327 2107289 := bstep (se 2 (by rfl) ⟨790233, by rfl⟩ : syracuseStep 2107289 = 1580467) B1580467
theorem B1779641 : Blo 738327 1779641 := bstep (se 2 (by rfl) ⟨667365, by rfl⟩ : syracuseStep 1779641 = 1334731) B1334731
theorem B2107403 : Blo 738327 2107403 := bstep (se 1 (by rfl) ⟨1580552, by rfl⟩ : syracuseStep 2107403 = 3161105) B3161105
theorem B3549707 : Blo 738327 3549707 := bstep (se 1 (by rfl) ⟨2662280, by rfl⟩ : syracuseStep 3549707 = 5324561) B5324561
theorem B3156509 : Blo 738327 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B26978935 : Blo 738327 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B1878785 : Blo 738327 1878785 := bstep (se 2 (by rfl) ⟨704544, by rfl⟩ : syracuseStep 1878785 = 1409089) B1409089
theorem B4205465 : Blo 738327 4205465 := bstep (se 2 (by rfl) ⟨1577049, by rfl⟩ : syracuseStep 4205465 = 3154099) B3154099
theorem B2108531 : Blo 738327 2108531 := bstep (se 1 (by rfl) ⟨1581398, by rfl⟩ : syracuseStep 2108531 = 3162797) B3162797
theorem B2502035 : Blo 738327 2502035 := bstep (se 1 (by rfl) ⟨1876526, by rfl⟩ : syracuseStep 2502035 = 3753053) B3753053
theorem B17346001 : Blo 738327 17346001 := bstep (se 2 (by rfl) ⟨6504750, by rfl⟩ : syracuseStep 17346001 = 13009501) B13009501
theorem B2108929 : Blo 738327 2108929 := bstep (se 2 (by rfl) ⟨790848, by rfl⟩ : syracuseStep 2108929 = 1581697) B1581697
theorem B830983 : Blo 738327 830983 := bstep (se 1 (by rfl) ⟨623237, by rfl⟩ : syracuseStep 830983 = 1246475) B1246475
theorem B2108987 : Blo 738327 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B831163 : Blo 738327 831163 := bstep (se 1 (by rfl) ⟨623372, by rfl⟩ : syracuseStep 831163 = 1246745) B1246745
theorem B1584841 : Blo 738327 1584841 := bstep (se 2 (by rfl) ⟨594315, by rfl⟩ : syracuseStep 1584841 = 1188631) B1188631
theorem B2666375 : Blo 738327 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B1585097 : Blo 738327 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B3747869 : Blo 738327 3747869 := bstep (se 3 (by rfl) ⟨702725, by rfl⟩ : syracuseStep 3747869 = 1405451) B1405451
theorem B9482285 : Blo 738327 9482285 := bstep (se 3 (by rfl) ⟨1777928, by rfl⟩ : syracuseStep 9482285 = 3555857) B3555857
theorem B831631 : Blo 738327 831631 := bstep (se 1 (by rfl) ⟨623723, by rfl⟩ : syracuseStep 831631 = 1247447) B1247447
theorem B1126715 : Blo 738327 1126715 := bstep (se 1 (by rfl) ⟨845036, by rfl⟩ : syracuseStep 1126715 = 1690073) B1690073
theorem B1126775 : Blo 738327 1126775 := bstep (se 1 (by rfl) ⟨845081, by rfl⟩ : syracuseStep 1126775 = 1690163) B1690163
theorem B3748355 : Blo 738327 3748355 := bstep (se 1 (by rfl) ⟨2811266, by rfl⟩ : syracuseStep 3748355 = 5622533) B5622533
theorem B9024119 : Blo 738327 9024119 := bstep (se 1 (by rfl) ⟨6768089, by rfl⟩ : syracuseStep 9024119 = 13536179) B13536179
theorem B832135 : Blo 738327 832135 := bstep (se 1 (by rfl) ⟨624101, by rfl⟩ : syracuseStep 832135 = 1248203) B1248203
theorem B8991425 : Blo 738327 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B2503439 : Blo 738327 2503439 := bstep (se 1 (by rfl) ⟨1877579, by rfl⟩ : syracuseStep 2503439 = 3755159) B3755159
theorem B832315 : Blo 738327 832315 := bstep (se 1 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 832315 = 1248473) B1248473
theorem B34714457 : Blo 738327 34714457 := bstep (se 2 (by rfl) ⟨13017921, by rfl⟩ : syracuseStep 34714457 = 26035843) B26035843
theorem B2503709 : Blo 738327 2503709 := bstep (se 3 (by rfl) ⟨469445, by rfl⟩ : syracuseStep 2503709 = 938891) B938891
theorem B5616701 : Blo 738327 5616701 := bstep (se 3 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 5616701 = 2106263) B2106263
theorem B3159107 : Blo 738327 3159107 := bstep (se 1 (by rfl) ⟨2369330, by rfl⟩ : syracuseStep 3159107 = 4738661) B4738661
theorem B832783 : Blo 738327 832783 := bstep (se 1 (by rfl) ⟨624587, by rfl⟩ : syracuseStep 832783 = 1249175) B1249175
theorem B3159431 : Blo 738327 3159431 := bstep (se 1 (by rfl) ⟨2369573, by rfl⟩ : syracuseStep 3159431 = 4739147) B4739147
theorem B1783225 : Blo 738327 1783225 := bstep (se 2 (by rfl) ⟨668709, by rfl⟩ : syracuseStep 1783225 = 1337419) B1337419
theorem B8238635 : Blo 738327 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B833287 : Blo 738327 833287 := bstep (se 1 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 833287 = 1249931) B1249931
theorem B2373391 : Blo 738327 2373391 := bstep (se 1 (by rfl) ⟨1780043, by rfl⟩ : syracuseStep 2373391 = 3560087) B3560087
theorem B2111275 : Blo 738327 2111275 := bstep (se 1 (by rfl) ⟨1583456, by rfl⟩ : syracuseStep 2111275 = 3166913) B3166913
theorem B833467 : Blo 738327 833467 := bstep (se 1 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 833467 = 1250201) B1250201
theorem B8009675 : Blo 738327 8009675 := bstep (se 1 (by rfl) ⟨6007256, by rfl⟩ : syracuseStep 8009675 = 12014513) B12014513
theorem B3553283 : Blo 738327 3553283 := bstep (se 1 (by rfl) ⟨2664962, by rfl⟩ : syracuseStep 3553283 = 5329925) B5329925
theorem B2111503 : Blo 738327 2111503 := bstep (se 1 (by rfl) ⟨1583627, by rfl⟩ : syracuseStep 2111503 = 3167255) B3167255
theorem B3749975 : Blo 738327 3749975 := bstep (se 1 (by rfl) ⟨2812481, by rfl⟩ : syracuseStep 3749975 = 5624963) B5624963
theorem B4503671 : Blo 738327 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B15186161 : Blo 738327 15186161 := bstep (se 2 (by rfl) ⟨5694810, by rfl⟩ : syracuseStep 15186161 = 11389621) B11389621
theorem B2111777 : Blo 738327 2111777 := bstep (se 2 (by rfl) ⟨791916, by rfl⟩ : syracuseStep 2111777 = 1583833) B1583833
theorem B833935 : Blo 738327 833935 := bstep (se 1 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 833935 = 1250903) B1250903
theorem B2505113 : Blo 738327 2505113 := bstep (se 2 (by rfl) ⟨939417, by rfl⟩ : syracuseStep 2505113 = 1878835) B1878835
theorem B4209155 : Blo 738327 4209155 := bstep (se 1 (by rfl) ⟨3156866, by rfl⟩ : syracuseStep 4209155 = 6313733) B6313733
theorem B3750461 : Blo 738327 3750461 := bstep (se 3 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 3750461 = 1406423) B1406423
theorem B2112119 : Blo 738327 2112119 := bstep (se 1 (by rfl) ⟨1584089, by rfl⟩ : syracuseStep 2112119 = 3168179) B3168179
theorem B10828505 : Blo 738327 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B10697507 : Blo 738327 10697507 := bstep (se 1 (by rfl) ⟨8023130, by rfl⟩ : syracuseStep 10697507 = 16046261) B16046261
theorem B834439 : Blo 738327 834439 := bstep (se 1 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 834439 = 1251659) B1251659
theorem B834619 : Blo 738327 834619 := bstep (se 1 (by rfl) ⟨625964, by rfl⟩ : syracuseStep 834619 = 1251929) B1251929
theorem B9616445 : Blo 738327 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B3161207 : Blo 738327 3161207 := bstep (se 1 (by rfl) ⟨2370905, by rfl⟩ : syracuseStep 3161207 = 4741811) B4741811
theorem B2374775 : Blo 738327 2374775 := bstep (se 1 (by rfl) ⟨1781081, by rfl⟩ : syracuseStep 2374775 = 3562163) B3562163
theorem B1850521 : Blo 738327 1850521 := bstep (se 2 (by rfl) ⟨693945, by rfl⟩ : syracuseStep 1850521 = 1387891) B1387891
theorem B2112779 : Blo 738327 2112779 := bstep (se 1 (by rfl) ⟨1584584, by rfl⟩ : syracuseStep 2112779 = 3169169) B3169169
theorem B4111667 : Blo 738327 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B835087 : Blo 738327 835087 := bstep (se 1 (by rfl) ⟨626315, by rfl⟩ : syracuseStep 835087 = 1252631) B1252631
theorem B8994347 : Blo 738327 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B2277665 : Blo 738327 2277665 := bstep (se 2 (by rfl) ⟨854124, by rfl⟩ : syracuseStep 2277665 = 1708249) B1708249
theorem B3752243 : Blo 738327 3752243 := bstep (se 1 (by rfl) ⟨2814182, by rfl⟩ : syracuseStep 3752243 = 5628365) B5628365
theorem B5620103 : Blo 738327 5620103 := bstep (se 1 (by rfl) ⟨4215077, by rfl⟩ : syracuseStep 5620103 = 8430155) B8430155
theorem B2671147 : Blo 738327 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B2310743 : Blo 738327 2310743 := bstep (se 1 (by rfl) ⟨1733057, by rfl⟩ : syracuseStep 2310743 = 3466115) B3466115
theorem B3752567 : Blo 738327 3752567 := bstep (se 1 (by rfl) ⟨2814425, by rfl⟩ : syracuseStep 3752567 = 5628851) B5628851
theorem B3162881 : Blo 738327 3162881 := bstep (se 2 (by rfl) ⟨1186080, by rfl⟩ : syracuseStep 3162881 = 2372161) B2372161
theorem B738363 : Blo 738327 738363 := bstep (se 1 (by rfl) ⟨553772, by rfl⟩ : syracuseStep 738363 = 1107545) B1107545
theorem B738439 : Blo 738327 738439 := bstep (se 1 (by rfl) ⟨553829, by rfl⟩ : syracuseStep 738439 = 1107659) B1107659
theorem B738447 : Blo 738327 738447 := bstep (se 1 (by rfl) ⟨553835, by rfl⟩ : syracuseStep 738447 = 1107671) B1107671
theorem B738491 : Blo 738327 738491 := bstep (se 1 (by rfl) ⟨553868, by rfl⟩ : syracuseStep 738491 = 1107737) B1107737
theorem B738567 : Blo 738327 738567 := bstep (se 1 (by rfl) ⟨553925, by rfl⟩ : syracuseStep 738567 = 1107851) B1107851
theorem B738575 : Blo 738327 738575 := bstep (se 1 (by rfl) ⟨553931, by rfl⟩ : syracuseStep 738575 = 1107863) B1107863
theorem B738619 : Blo 738327 738619 := bstep (se 1 (by rfl) ⟨553964, by rfl⟩ : syracuseStep 738619 = 1107929) B1107929
theorem B2377019 : Blo 738327 2377019 := bstep (se 1 (by rfl) ⟨1782764, by rfl⟩ : syracuseStep 2377019 = 3565529) B3565529
theorem B738695 : Blo 738327 738695 := bstep (se 1 (by rfl) ⟨554021, by rfl⟩ : syracuseStep 738695 = 1108043) B1108043
theorem B738703 : Blo 738327 738703 := bstep (se 1 (by rfl) ⟨554027, by rfl⟩ : syracuseStep 738703 = 1108055) B1108055
theorem B738747 : Blo 738327 738747 := bstep (se 1 (by rfl) ⟨554060, by rfl⟩ : syracuseStep 738747 = 1108121) B1108121
theorem B738823 : Blo 738327 738823 := bstep (se 1 (by rfl) ⟨554117, by rfl⟩ : syracuseStep 738823 = 1108235) B1108235
theorem B738831 : Blo 738327 738831 := bstep (se 1 (by rfl) ⟨554123, by rfl⟩ : syracuseStep 738831 = 1108247) B1108247
theorem B738875 : Blo 738327 738875 := bstep (se 1 (by rfl) ⟨554156, by rfl⟩ : syracuseStep 738875 = 1108313) B1108313
theorem B3753539 : Blo 738327 3753539 := bstep (se 1 (by rfl) ⟨2815154, by rfl⟩ : syracuseStep 3753539 = 5630309) B5630309
theorem B738951 : Blo 738327 738951 := bstep (se 1 (by rfl) ⟨554213, by rfl⟩ : syracuseStep 738951 = 1108427) B1108427
theorem B738959 : Blo 738327 738959 := bstep (se 1 (by rfl) ⟨554219, by rfl⟩ : syracuseStep 738959 = 1108439) B1108439
theorem B739003 : Blo 738327 739003 := bstep (se 1 (by rfl) ⟨554252, by rfl⟩ : syracuseStep 739003 = 1108505) B1108505
theorem B739079 : Blo 738327 739079 := bstep (se 1 (by rfl) ⟨554309, by rfl⟩ : syracuseStep 739079 = 1108619) B1108619
theorem B739087 : Blo 738327 739087 := bstep (se 1 (by rfl) ⟨554315, by rfl⟩ : syracuseStep 739087 = 1108631) B1108631
theorem B6735653 : Blo 738327 6735653 := bstep (se 4 (by rfl) ⟨631467, by rfl⟩ : syracuseStep 6735653 = 1262935) B1262935
theorem B739131 : Blo 738327 739131 := bstep (se 1 (by rfl) ⟨554348, by rfl⟩ : syracuseStep 739131 = 1108697) B1108697
theorem B1001335 : Blo 738327 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B739207 : Blo 738327 739207 := bstep (se 1 (by rfl) ⟨554405, by rfl⟩ : syracuseStep 739207 = 1108811) B1108811
theorem B3753863 : Blo 738327 3753863 := bstep (se 1 (by rfl) ⟨2815397, by rfl⟩ : syracuseStep 3753863 = 5630795) B5630795
theorem B739215 : Blo 738327 739215 := bstep (se 1 (by rfl) ⟨554411, by rfl⟩ : syracuseStep 739215 = 1108823) B1108823
theorem B739259 : Blo 738327 739259 := bstep (se 1 (by rfl) ⟨554444, by rfl⟩ : syracuseStep 739259 = 1108889) B1108889
theorem B739335 : Blo 738327 739335 := bstep (se 1 (by rfl) ⟨554501, by rfl⟩ : syracuseStep 739335 = 1109003) B1109003
theorem B739343 : Blo 738327 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B739387 : Blo 738327 739387 := bstep (se 1 (by rfl) ⟨554540, by rfl⟩ : syracuseStep 739387 = 1109081) B1109081
theorem B739463 : Blo 738327 739463 := bstep (se 1 (by rfl) ⟨554597, by rfl⟩ : syracuseStep 739463 = 1109195) B1109195
theorem B739471 : Blo 738327 739471 := bstep (se 1 (by rfl) ⟨554603, by rfl⟩ : syracuseStep 739471 = 1109207) B1109207
theorem B739515 : Blo 738327 739515 := bstep (se 1 (by rfl) ⟨554636, by rfl⟩ : syracuseStep 739515 = 1109273) B1109273
theorem B739591 : Blo 738327 739591 := bstep (se 1 (by rfl) ⟨554693, by rfl⟩ : syracuseStep 739591 = 1109387) B1109387
theorem B739599 : Blo 738327 739599 := bstep (se 1 (by rfl) ⟨554699, by rfl⟩ : syracuseStep 739599 = 1109399) B1109399
theorem B739643 : Blo 738327 739643 := bstep (se 1 (by rfl) ⟨554732, by rfl⟩ : syracuseStep 739643 = 1109465) B1109465
theorem B8014139 : Blo 738327 8014139 := bstep (se 1 (by rfl) ⟨6010604, by rfl⟩ : syracuseStep 8014139 = 12021209) B12021209
theorem B739719 : Blo 738327 739719 := bstep (se 1 (by rfl) ⟨554789, by rfl⟩ : syracuseStep 739719 = 1109579) B1109579
theorem B739727 : Blo 738327 739727 := bstep (se 1 (by rfl) ⟨554795, by rfl⟩ : syracuseStep 739727 = 1109591) B1109591
theorem B739771 : Blo 738327 739771 := bstep (se 1 (by rfl) ⟨554828, by rfl⟩ : syracuseStep 739771 = 1109657) B1109657
theorem B8669645 : Blo 738327 8669645 := bstep (se 3 (by rfl) ⟨1625558, by rfl⟩ : syracuseStep 8669645 = 3251117) B3251117
theorem B739847 : Blo 738327 739847 := bstep (se 1 (by rfl) ⟨554885, by rfl⟩ : syracuseStep 739847 = 1109771) B1109771
theorem B739855 : Blo 738327 739855 := bstep (se 1 (by rfl) ⟨554891, by rfl⟩ : syracuseStep 739855 = 1109783) B1109783
theorem B739899 : Blo 738327 739899 := bstep (se 1 (by rfl) ⟨554924, by rfl⟩ : syracuseStep 739899 = 1109849) B1109849
theorem B739975 : Blo 738327 739975 := bstep (se 1 (by rfl) ⟨554981, by rfl⟩ : syracuseStep 739975 = 1109963) B1109963
theorem B739983 : Blo 738327 739983 := bstep (se 1 (by rfl) ⟨554987, by rfl⟩ : syracuseStep 739983 = 1109975) B1109975
theorem B740027 : Blo 738327 740027 := bstep (se 1 (by rfl) ⟨555020, by rfl⟩ : syracuseStep 740027 = 1110041) B1110041
theorem B740103 : Blo 738327 740103 := bstep (se 1 (by rfl) ⟨555077, by rfl⟩ : syracuseStep 740103 = 1110155) B1110155
theorem B740111 : Blo 738327 740111 := bstep (se 1 (by rfl) ⟨555083, by rfl⟩ : syracuseStep 740111 = 1110167) B1110167
theorem B740155 : Blo 738327 740155 := bstep (se 1 (by rfl) ⟨555116, by rfl⟩ : syracuseStep 740155 = 1110233) B1110233
theorem B2804615 : Blo 738327 2804615 := bstep (se 1 (by rfl) ⟨2103461, by rfl⟩ : syracuseStep 2804615 = 4206923) B4206923
theorem B740231 : Blo 738327 740231 := bstep (se 1 (by rfl) ⟨555173, by rfl⟩ : syracuseStep 740231 = 1110347) B1110347
theorem B740239 : Blo 738327 740239 := bstep (se 1 (by rfl) ⟨555179, by rfl⟩ : syracuseStep 740239 = 1110359) B1110359
theorem B740283 : Blo 738327 740283 := bstep (se 1 (by rfl) ⟨555212, by rfl⟩ : syracuseStep 740283 = 1110425) B1110425
theorem B740359 : Blo 738327 740359 := bstep (se 1 (by rfl) ⟨555269, by rfl⟩ : syracuseStep 740359 = 1110539) B1110539
theorem B740367 : Blo 738327 740367 := bstep (se 1 (by rfl) ⟨555275, by rfl⟩ : syracuseStep 740367 = 1110551) B1110551
theorem B937003 : Blo 738327 937003 := bstep (se 1 (by rfl) ⟨702752, by rfl⟩ : syracuseStep 937003 = 1405505) B1405505
theorem B740411 : Blo 738327 740411 := bstep (se 1 (by rfl) ⟨555308, by rfl⟩ : syracuseStep 740411 = 1110617) B1110617
theorem B740487 : Blo 738327 740487 := bstep (se 1 (by rfl) ⟨555365, by rfl⟩ : syracuseStep 740487 = 1110731) B1110731
theorem B740495 : Blo 738327 740495 := bstep (se 1 (by rfl) ⟨555371, by rfl⟩ : syracuseStep 740495 = 1110743) B1110743
theorem B740539 : Blo 738327 740539 := bstep (se 1 (by rfl) ⟨555404, by rfl⟩ : syracuseStep 740539 = 1110809) B1110809
theorem B740615 : Blo 738327 740615 := bstep (se 1 (by rfl) ⟨555461, by rfl⟩ : syracuseStep 740615 = 1110923) B1110923
theorem B740623 : Blo 738327 740623 := bstep (se 1 (by rfl) ⟨555467, by rfl⟩ : syracuseStep 740623 = 1110935) B1110935
theorem B740667 : Blo 738327 740667 := bstep (se 1 (by rfl) ⟨555500, by rfl⟩ : syracuseStep 740667 = 1111001) B1111001
theorem B740743 : Blo 738327 740743 := bstep (se 1 (by rfl) ⟨555557, by rfl⟩ : syracuseStep 740743 = 1111115) B1111115
theorem B740751 : Blo 738327 740751 := bstep (se 1 (by rfl) ⟨555563, by rfl⟩ : syracuseStep 740751 = 1111127) B1111127
theorem B5688721 : Blo 738327 5688721 := bstep (se 2 (by rfl) ⟨2133270, by rfl⟩ : syracuseStep 5688721 = 4266541) B4266541
theorem B740795 : Blo 738327 740795 := bstep (se 1 (by rfl) ⟨555596, by rfl⟩ : syracuseStep 740795 = 1111193) B1111193
theorem B740871 : Blo 738327 740871 := bstep (se 1 (by rfl) ⟨555653, by rfl⟩ : syracuseStep 740871 = 1111307) B1111307
theorem B740879 : Blo 738327 740879 := bstep (se 1 (by rfl) ⟨555659, by rfl⟩ : syracuseStep 740879 = 1111319) B1111319
theorem B740923 : Blo 738327 740923 := bstep (se 1 (by rfl) ⟨555692, by rfl⟩ : syracuseStep 740923 = 1111385) B1111385
theorem B3001943 : Blo 738327 3001943 := bstep (se 1 (by rfl) ⟨2251457, by rfl⟩ : syracuseStep 3001943 = 4502915) B4502915
theorem B27053669 : Blo 738327 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B740999 : Blo 738327 740999 := bstep (se 1 (by rfl) ⟨555749, by rfl⟩ : syracuseStep 740999 = 1111499) B1111499
theorem B741007 : Blo 738327 741007 := bstep (se 1 (by rfl) ⟨555755, by rfl⟩ : syracuseStep 741007 = 1111511) B1111511
theorem B741051 : Blo 738327 741051 := bstep (se 1 (by rfl) ⟨555788, by rfl⟩ : syracuseStep 741051 = 1111577) B1111577
theorem B741127 : Blo 738327 741127 := bstep (se 1 (by rfl) ⟨555845, by rfl⟩ : syracuseStep 741127 = 1111691) B1111691
theorem B741135 : Blo 738327 741135 := bstep (se 1 (by rfl) ⟨555851, by rfl⟩ : syracuseStep 741135 = 1111703) B1111703
theorem B741179 : Blo 738327 741179 := bstep (se 1 (by rfl) ⟨555884, by rfl⟩ : syracuseStep 741179 = 1111769) B1111769
theorem B741255 : Blo 738327 741255 := bstep (se 1 (by rfl) ⟨555941, by rfl⟩ : syracuseStep 741255 = 1111883) B1111883
theorem B741263 : Blo 738327 741263 := bstep (se 1 (by rfl) ⟨555947, by rfl⟩ : syracuseStep 741263 = 1111895) B1111895
theorem B4214713 : Blo 738327 4214713 := bstep (se 2 (by rfl) ⟨1580517, by rfl⟩ : syracuseStep 4214713 = 3161035) B3161035
theorem B741307 : Blo 738327 741307 := bstep (se 1 (by rfl) ⟨555980, by rfl⟩ : syracuseStep 741307 = 1111961) B1111961
theorem B937975 : Blo 738327 937975 := bstep (se 1 (by rfl) ⟨703481, by rfl⟩ : syracuseStep 937975 = 1406963) B1406963
theorem B741383 : Blo 738327 741383 := bstep (se 1 (by rfl) ⟨556037, by rfl⟩ : syracuseStep 741383 = 1112075) B1112075
theorem B741391 : Blo 738327 741391 := bstep (se 1 (by rfl) ⟨556043, by rfl⟩ : syracuseStep 741391 = 1112087) B1112087
theorem B741435 : Blo 738327 741435 := bstep (se 1 (by rfl) ⟨556076, by rfl⟩ : syracuseStep 741435 = 1112153) B1112153
theorem B7098455 : Blo 738327 7098455 := bstep (se 1 (by rfl) ⟨5323841, by rfl⟩ : syracuseStep 7098455 = 10647683) B10647683
theorem B741511 : Blo 738327 741511 := bstep (se 1 (by rfl) ⟨556133, by rfl⟩ : syracuseStep 741511 = 1112267) B1112267
theorem B741519 : Blo 738327 741519 := bstep (se 1 (by rfl) ⟨556139, by rfl⟩ : syracuseStep 741519 = 1112279) B1112279
theorem B741563 : Blo 738327 741563 := bstep (se 1 (by rfl) ⟨556172, by rfl⟩ : syracuseStep 741563 = 1112345) B1112345
theorem B741639 : Blo 738327 741639 := bstep (se 1 (by rfl) ⟨556229, by rfl⟩ : syracuseStep 741639 = 1112459) B1112459
theorem B741647 : Blo 738327 741647 := bstep (se 1 (by rfl) ⟨556235, by rfl⟩ : syracuseStep 741647 = 1112471) B1112471
theorem B938299 : Blo 738327 938299 := bstep (se 1 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 938299 = 1407449) B1407449
theorem B741691 : Blo 738327 741691 := bstep (se 1 (by rfl) ⟨556268, by rfl⟩ : syracuseStep 741691 = 1112537) B1112537
theorem B741767 : Blo 738327 741767 := bstep (se 1 (by rfl) ⟨556325, by rfl⟩ : syracuseStep 741767 = 1112651) B1112651
theorem B741775 : Blo 738327 741775 := bstep (se 1 (by rfl) ⟨556331, by rfl⟩ : syracuseStep 741775 = 1112663) B1112663
theorem B6771089 : Blo 738327 6771089 := bstep (se 2 (by rfl) ⟨2539158, by rfl⟩ : syracuseStep 6771089 = 5078317) B5078317
theorem B741819 : Blo 738327 741819 := bstep (se 1 (by rfl) ⟨556364, by rfl⟩ : syracuseStep 741819 = 1112729) B1112729
theorem B11981297 : Blo 738327 11981297 := bstep (se 2 (by rfl) ⟨4492986, by rfl⟩ : syracuseStep 11981297 = 8985973) B8985973
theorem B741895 : Blo 738327 741895 := bstep (se 1 (by rfl) ⟨556421, by rfl⟩ : syracuseStep 741895 = 1112843) B1112843
theorem B741903 : Blo 738327 741903 := bstep (se 1 (by rfl) ⟨556427, by rfl⟩ : syracuseStep 741903 = 1112855) B1112855
theorem B741947 : Blo 738327 741947 := bstep (se 1 (by rfl) ⟨556460, by rfl⟩ : syracuseStep 741947 = 1112921) B1112921
theorem B4280951 : Blo 738327 4280951 := bstep (se 1 (by rfl) ⟨3210713, by rfl⟩ : syracuseStep 4280951 = 6421427) B6421427
theorem B742023 : Blo 738327 742023 := bstep (se 1 (by rfl) ⟨556517, by rfl⟩ : syracuseStep 742023 = 1113035) B1113035
theorem B742031 : Blo 738327 742031 := bstep (se 1 (by rfl) ⟨556523, by rfl⟩ : syracuseStep 742031 = 1113047) B1113047
theorem B742075 : Blo 738327 742075 := bstep (se 1 (by rfl) ⟨556556, by rfl⟩ : syracuseStep 742075 = 1113113) B1113113
theorem B5329637 : Blo 738327 5329637 := bstep (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) B999307
theorem B742151 : Blo 738327 742151 := bstep (se 1 (by rfl) ⟨556613, by rfl⟩ : syracuseStep 742151 = 1113227) B1113227
theorem B742159 : Blo 738327 742159 := bstep (se 1 (by rfl) ⟨556619, by rfl⟩ : syracuseStep 742159 = 1113239) B1113239
theorem B742203 : Blo 738327 742203 := bstep (se 1 (by rfl) ⟨556652, by rfl⟩ : syracuseStep 742203 = 1113305) B1113305
theorem B6411097 : Blo 738327 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B742279 : Blo 738327 742279 := bstep (se 1 (by rfl) ⟨556709, by rfl⟩ : syracuseStep 742279 = 1113419) B1113419
theorem B742287 : Blo 738327 742287 := bstep (se 1 (by rfl) ⟨556715, by rfl⟩ : syracuseStep 742287 = 1113431) B1113431
theorem B3560395 : Blo 738327 3560395 := bstep (se 1 (by rfl) ⟨2670296, by rfl⟩ : syracuseStep 3560395 = 5340593) B5340593
theorem B4740119 : Blo 738327 4740119 := bstep (se 1 (by rfl) ⟨3555089, by rfl⟩ : syracuseStep 4740119 = 7110179) B7110179
theorem B1332425 : Blo 738327 1332425 := bstep (se 2 (by rfl) ⟨499659, by rfl⟩ : syracuseStep 1332425 = 999319) B999319
theorem B939271 : Blo 738327 939271 := bstep (se 1 (by rfl) ⟨704453, by rfl⟩ : syracuseStep 939271 = 1408907) B1408907
theorem B7132475 : Blo 738327 7132475 := bstep (se 1 (by rfl) ⟨5349356, by rfl⟩ : syracuseStep 7132475 = 10698713) B10698713
theorem B3757427 : Blo 738327 3757427 := bstep (se 1 (by rfl) ⟨2818070, by rfl⟩ : syracuseStep 3757427 = 5636141) B5636141
theorem B1201979 : Blo 738327 1201979 := bstep (se 1 (by rfl) ⟨901484, by rfl⟩ : syracuseStep 1201979 = 1802969) B1802969
theorem B3757913 : Blo 738327 3757913 := bstep (se 2 (by rfl) ⟨1409217, by rfl⟩ : syracuseStep 3757913 = 2818435) B2818435
theorem B3790795 : Blo 738327 3790795 := bstep (se 1 (by rfl) ⟨2843096, by rfl⟩ : syracuseStep 3790795 = 5686193) B5686193
theorem B2250899 : Blo 738327 2250899 := bstep (se 1 (by rfl) ⟨1688174, by rfl⟩ : syracuseStep 2250899 = 3376349) B3376349
theorem B1923257 : Blo 738327 1923257 := bstep (se 2 (by rfl) ⟨721221, by rfl⟩ : syracuseStep 1923257 = 1442443) B1442443
theorem B3037625 : Blo 738327 3037625 := bstep (se 2 (by rfl) ⟨1139109, by rfl⟩ : syracuseStep 3037625 = 2278219) B2278219
theorem B1333793 : Blo 738327 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B7101107 : Blo 738327 7101107 := bstep (se 1 (by rfl) ⟨5325830, by rfl⟩ : syracuseStep 7101107 = 10651661) B10651661
theorem B4741861 : Blo 738327 4741861 := bstep (se 4 (by rfl) ⟨444549, by rfl⟩ : syracuseStep 4741861 = 889099) B889099
theorem B1661831 : Blo 738327 1661831 := bstep (se 1 (by rfl) ⟨1246373, by rfl⟩ : syracuseStep 1661831 = 2492747) B2492747
theorem B1662011 : Blo 738327 1662011 := bstep (se 1 (by rfl) ⟨1246508, by rfl⟩ : syracuseStep 1662011 = 2493017) B2493017
theorem B1662137 : Blo 738327 1662137 := bstep (se 2 (by rfl) ⟨623301, by rfl⟩ : syracuseStep 1662137 = 1246603) B1246603
theorem B3562973 : Blo 738327 3562973 := bstep (se 3 (by rfl) ⟨668057, by rfl⟩ : syracuseStep 3562973 = 1336115) B1336115
theorem B1662479 : Blo 738327 1662479 := bstep (se 1 (by rfl) ⟨1246859, by rfl⟩ : syracuseStep 1662479 = 2493719) B2493719
theorem B1662497 : Blo 738327 1662497 := bstep (se 2 (by rfl) ⟨623436, by rfl⟩ : syracuseStep 1662497 = 1246873) B1246873
theorem B3169853 : Blo 738327 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B3202679 : Blo 738327 3202679 := bstep (se 1 (by rfl) ⟨2402009, by rfl⟩ : syracuseStep 3202679 = 4804019) B4804019
theorem B7102181 : Blo 738327 7102181 := bstep (se 4 (by rfl) ⟨665829, by rfl⟩ : syracuseStep 7102181 = 1331659) B1331659
theorem B1662839 : Blo 738327 1662839 := bstep (se 1 (by rfl) ⟨1247129, by rfl⟩ : syracuseStep 1662839 = 2494259) B2494259
theorem B1663019 : Blo 738327 1663019 := bstep (se 1 (by rfl) ⟨1247264, by rfl⟩ : syracuseStep 1663019 = 2494529) B2494529
theorem B2023559 : Blo 738327 2023559 := bstep (se 1 (by rfl) ⟨1517669, by rfl⟩ : syracuseStep 2023559 = 3035339) B3035339
theorem B27025649 : Blo 738327 27025649 := bstep (se 2 (by rfl) ⟨10134618, by rfl⟩ : syracuseStep 27025649 = 20269237) B20269237
theorem B3563777 : Blo 738327 3563777 := bstep (se 2 (by rfl) ⟨1336416, by rfl⟩ : syracuseStep 3563777 = 2672833) B2672833
theorem B5136785 : Blo 738327 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B1663379 : Blo 738327 1663379 := bstep (se 1 (by rfl) ⟨1247534, by rfl⟩ : syracuseStep 1663379 = 2495069) B2495069
theorem B1663433 : Blo 738327 1663433 := bstep (se 2 (by rfl) ⟨623787, by rfl⟩ : syracuseStep 1663433 = 1247575) B1247575
theorem B4514251 : Blo 738327 4514251 := bstep (se 1 (by rfl) ⟨3385688, by rfl⟩ : syracuseStep 4514251 = 6771377) B6771377
theorem B1664135 : Blo 738327 1664135 := bstep (se 1 (by rfl) ⟨1248101, by rfl⟩ : syracuseStep 1664135 = 2496203) B2496203
theorem B1664315 : Blo 738327 1664315 := bstep (se 1 (by rfl) ⟨1248236, by rfl⟩ : syracuseStep 1664315 = 2496473) B2496473
theorem B1500535 : Blo 738327 1500535 := bstep (se 1 (by rfl) ⟨1125401, by rfl⟩ : syracuseStep 1500535 = 2250803) B2250803
theorem B1402247 : Blo 738327 1402247 := bstep (se 1 (by rfl) ⟨1051685, by rfl⟩ : syracuseStep 1402247 = 2103371) B2103371
theorem B1664441 : Blo 738327 1664441 := bstep (se 2 (by rfl) ⟨624165, by rfl⟩ : syracuseStep 1664441 = 1248331) B1248331
theorem B4220363 : Blo 738327 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B1107515 : Blo 738327 1107515 := bstep (se 1 (by rfl) ⟨830636, by rfl⟩ : syracuseStep 1107515 = 1661273) B1661273
theorem B1107575 : Blo 738327 1107575 := bstep (se 1 (by rfl) ⟨830681, by rfl⟩ : syracuseStep 1107575 = 1661363) B1661363
theorem B1107599 : Blo 738327 1107599 := bstep (se 1 (by rfl) ⟨830699, by rfl⟩ : syracuseStep 1107599 = 1661399) B1661399
theorem B14247575 : Blo 738327 14247575 := bstep (se 1 (by rfl) ⟨10685681, by rfl⟩ : syracuseStep 14247575 = 21371363) B21371363
theorem B1107641 : Blo 738327 1107641 := bstep (se 2 (by rfl) ⟨415365, by rfl⟩ : syracuseStep 1107641 = 830731) B830731
theorem B1107719 : Blo 738327 1107719 := bstep (se 1 (by rfl) ⟨830789, by rfl⟩ : syracuseStep 1107719 = 1661579) B1661579
theorem B1664783 : Blo 738327 1664783 := bstep (se 1 (by rfl) ⟨1248587, by rfl⟩ : syracuseStep 1664783 = 2497175) B2497175
theorem B1664801 : Blo 738327 1664801 := bstep (se 2 (by rfl) ⟨624300, by rfl⟩ : syracuseStep 1664801 = 1248601) B1248601
theorem B1107755 : Blo 738327 1107755 := bstep (se 1 (by rfl) ⟨830816, by rfl⟩ : syracuseStep 1107755 = 1661633) B1661633
theorem B1107785 : Blo 738327 1107785 := bstep (se 2 (by rfl) ⟨415419, by rfl⟩ : syracuseStep 1107785 = 830839) B830839
theorem B1402771 : Blo 738327 1402771 := bstep (se 1 (by rfl) ⟨1052078, by rfl⟩ : syracuseStep 1402771 = 2104157) B2104157
theorem B4220819 : Blo 738327 4220819 := bstep (se 1 (by rfl) ⟨3165614, by rfl⟩ : syracuseStep 4220819 = 6331229) B6331229
theorem B1107899 : Blo 738327 1107899 := bstep (se 1 (by rfl) ⟨830924, by rfl⟩ : syracuseStep 1107899 = 1661849) B1661849
theorem B1107959 : Blo 738327 1107959 := bstep (se 1 (by rfl) ⟨830969, by rfl⟩ : syracuseStep 1107959 = 1661939) B1661939
theorem B1107983 : Blo 738327 1107983 := bstep (se 1 (by rfl) ⟨830987, by rfl⟩ : syracuseStep 1107983 = 1661975) B1661975
theorem B1108025 : Blo 738327 1108025 := bstep (se 2 (by rfl) ⟨415509, by rfl⟩ : syracuseStep 1108025 = 831019) B831019
theorem B2844733 : Blo 738327 2844733 := bstep (se 3 (by rfl) ⟨533387, by rfl⟩ : syracuseStep 2844733 = 1066775) B1066775
theorem B1665143 : Blo 738327 1665143 := bstep (se 1 (by rfl) ⟨1248857, by rfl⟩ : syracuseStep 1665143 = 2497715) B2497715
theorem B1108103 : Blo 738327 1108103 := bstep (se 1 (by rfl) ⟨831077, by rfl⟩ : syracuseStep 1108103 = 1662155) B1662155
theorem B1108139 : Blo 738327 1108139 := bstep (se 1 (by rfl) ⟨831104, by rfl⟩ : syracuseStep 1108139 = 1662209) B1662209
theorem B1108169 : Blo 738327 1108169 := bstep (se 2 (by rfl) ⟨415563, by rfl⟩ : syracuseStep 1108169 = 831127) B831127
theorem B1665323 : Blo 738327 1665323 := bstep (se 1 (by rfl) ⟨1248992, by rfl⟩ : syracuseStep 1665323 = 2497985) B2497985
theorem B1501483 : Blo 738327 1501483 := bstep (se 1 (by rfl) ⟨1126112, by rfl⟩ : syracuseStep 1501483 = 2252225) B2252225
theorem B1108283 : Blo 738327 1108283 := bstep (se 1 (by rfl) ⟨831212, by rfl⟩ : syracuseStep 1108283 = 1662425) B1662425
theorem B1108343 : Blo 738327 1108343 := bstep (se 1 (by rfl) ⟨831257, by rfl⟩ : syracuseStep 1108343 = 1662515) B1662515
theorem B1108367 : Blo 738327 1108367 := bstep (se 1 (by rfl) ⟨831275, by rfl⟩ : syracuseStep 1108367 = 1662551) B1662551
theorem B1108409 : Blo 738327 1108409 := bstep (se 2 (by rfl) ⟨415653, by rfl⟩ : syracuseStep 1108409 = 831307) B831307
theorem B3860995 : Blo 738327 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B1108487 : Blo 738327 1108487 := bstep (se 1 (by rfl) ⟨831365, by rfl⟩ : syracuseStep 1108487 = 1662731) B1662731
theorem B1108523 : Blo 738327 1108523 := bstep (se 1 (by rfl) ⟨831392, by rfl⟩ : syracuseStep 1108523 = 1662785) B1662785
theorem B61565507 : Blo 738327 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B1108553 : Blo 738327 1108553 := bstep (se 2 (by rfl) ⟨415707, by rfl⟩ : syracuseStep 1108553 = 831415) B831415
theorem B7825997 : Blo 738327 7825997 := bstep (se 3 (by rfl) ⟨1467374, by rfl⟩ : syracuseStep 7825997 = 2934749) B2934749
theorem B2255447 : Blo 738327 2255447 := bstep (se 1 (by rfl) ⟨1691585, by rfl⟩ : syracuseStep 2255447 = 3383171) B3383171
theorem B1665683 : Blo 738327 1665683 := bstep (se 1 (by rfl) ⟨1249262, by rfl⟩ : syracuseStep 1665683 = 2498525) B2498525
theorem B1108667 : Blo 738327 1108667 := bstep (se 1 (by rfl) ⟨831500, by rfl⟩ : syracuseStep 1108667 = 1663001) B1663001
theorem B1665737 : Blo 738327 1665737 := bstep (se 2 (by rfl) ⟨624651, by rfl⟩ : syracuseStep 1665737 = 1249303) B1249303
theorem B1108727 : Blo 738327 1108727 := bstep (se 1 (by rfl) ⟨831545, by rfl⟩ : syracuseStep 1108727 = 1663091) B1663091
theorem B1108751 : Blo 738327 1108751 := bstep (se 1 (by rfl) ⟨831563, by rfl⟩ : syracuseStep 1108751 = 1663127) B1663127
theorem B1108793 : Blo 738327 1108793 := bstep (se 2 (by rfl) ⟨415797, by rfl⟩ : syracuseStep 1108793 = 831595) B831595
theorem B1108871 : Blo 738327 1108871 := bstep (se 1 (by rfl) ⟨831653, by rfl⟩ : syracuseStep 1108871 = 1663307) B1663307
theorem B1108907 : Blo 738327 1108907 := bstep (se 1 (by rfl) ⟨831680, by rfl⟩ : syracuseStep 1108907 = 1663361) B1663361
theorem B1108937 : Blo 738327 1108937 := bstep (se 2 (by rfl) ⟨415851, by rfl⟩ : syracuseStep 1108937 = 831703) B831703
theorem B1109051 : Blo 738327 1109051 := bstep (se 1 (by rfl) ⟨831788, by rfl⟩ : syracuseStep 1109051 = 1663577) B1663577
theorem B1403963 : Blo 738327 1403963 := bstep (se 1 (by rfl) ⟨1052972, by rfl⟩ : syracuseStep 1403963 = 2105945) B2105945
theorem B2255959 : Blo 738327 2255959 := bstep (se 1 (by rfl) ⟨1691969, by rfl⟩ : syracuseStep 2255959 = 3383939) B3383939
theorem B1109111 : Blo 738327 1109111 := bstep (se 1 (by rfl) ⟨831833, by rfl⟩ : syracuseStep 1109111 = 1663667) B1663667
theorem B1109135 : Blo 738327 1109135 := bstep (se 1 (by rfl) ⟨831851, by rfl⟩ : syracuseStep 1109135 = 1663703) B1663703
theorem B1109177 : Blo 738327 1109177 := bstep (se 2 (by rfl) ⟨415941, by rfl⟩ : syracuseStep 1109177 = 831883) B831883
theorem B1109255 : Blo 738327 1109255 := bstep (se 1 (by rfl) ⟨831941, by rfl⟩ : syracuseStep 1109255 = 1663883) B1663883
theorem B1109291 : Blo 738327 1109291 := bstep (se 1 (by rfl) ⟨831968, by rfl⟩ : syracuseStep 1109291 = 1663937) B1663937
theorem B1109321 : Blo 738327 1109321 := bstep (se 2 (by rfl) ⟨415995, by rfl⟩ : syracuseStep 1109321 = 831991) B831991
theorem B1666439 : Blo 738327 1666439 := bstep (se 1 (by rfl) ⟨1249829, by rfl⟩ : syracuseStep 1666439 = 2499659) B2499659
theorem B1109435 : Blo 738327 1109435 := bstep (se 1 (by rfl) ⟨832076, by rfl⟩ : syracuseStep 1109435 = 1664153) B1664153
theorem B2813393 : Blo 738327 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B1109495 : Blo 738327 1109495 := bstep (se 1 (by rfl) ⟨832121, by rfl⟩ : syracuseStep 1109495 = 1664243) B1664243
theorem B1109519 : Blo 738327 1109519 := bstep (se 1 (by rfl) ⟨832139, by rfl⟩ : syracuseStep 1109519 = 1664279) B1664279
theorem B1404449 : Blo 738327 1404449 := bstep (se 2 (by rfl) ⟨526668, by rfl⟩ : syracuseStep 1404449 = 1053337) B1053337
theorem B1109561 : Blo 738327 1109561 := bstep (se 2 (by rfl) ⟨416085, by rfl⟩ : syracuseStep 1109561 = 832171) B832171
theorem B1666619 : Blo 738327 1666619 := bstep (se 1 (by rfl) ⟨1249964, by rfl⟩ : syracuseStep 1666619 = 2499929) B2499929
theorem B1109639 : Blo 738327 1109639 := bstep (se 1 (by rfl) ⟨832229, by rfl⟩ : syracuseStep 1109639 = 1664459) B1664459
theorem B1109675 : Blo 738327 1109675 := bstep (se 1 (by rfl) ⟨832256, by rfl⟩ : syracuseStep 1109675 = 1664513) B1664513
theorem B1666745 : Blo 738327 1666745 := bstep (se 2 (by rfl) ⟨625029, by rfl⟩ : syracuseStep 1666745 = 1250059) B1250059
theorem B1109705 : Blo 738327 1109705 := bstep (se 2 (by rfl) ⟨416139, by rfl⟩ : syracuseStep 1109705 = 832279) B832279
theorem B1404715 : Blo 738327 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B23949107 : Blo 738327 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B1109819 : Blo 738327 1109819 := bstep (se 1 (by rfl) ⟨832364, by rfl⟩ : syracuseStep 1109819 = 1664729) B1664729
theorem B1109879 : Blo 738327 1109879 := bstep (se 1 (by rfl) ⟨832409, by rfl⟩ : syracuseStep 1109879 = 1664819) B1664819
theorem B1109903 : Blo 738327 1109903 := bstep (se 1 (by rfl) ⟨832427, by rfl⟩ : syracuseStep 1109903 = 1664855) B1664855
theorem B2813849 : Blo 738327 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B1109945 : Blo 738327 1109945 := bstep (se 2 (by rfl) ⟨416229, by rfl⟩ : syracuseStep 1109945 = 832459) B832459
theorem B1110023 : Blo 738327 1110023 := bstep (se 1 (by rfl) ⟨832517, by rfl⟩ : syracuseStep 1110023 = 1665035) B1665035
theorem B1667087 : Blo 738327 1667087 := bstep (se 1 (by rfl) ⟨1250315, by rfl⟩ : syracuseStep 1667087 = 2500631) B2500631
theorem B1667105 : Blo 738327 1667105 := bstep (se 2 (by rfl) ⟨625164, by rfl⟩ : syracuseStep 1667105 = 1250329) B1250329
theorem B1110059 : Blo 738327 1110059 := bstep (se 1 (by rfl) ⟨832544, by rfl⟩ : syracuseStep 1110059 = 1665089) B1665089
theorem B1110089 : Blo 738327 1110089 := bstep (se 2 (by rfl) ⟨416283, by rfl⟩ : syracuseStep 1110089 = 832567) B832567
theorem B1110203 : Blo 738327 1110203 := bstep (se 1 (by rfl) ⟨832652, by rfl⟩ : syracuseStep 1110203 = 1665305) B1665305
theorem B1110263 : Blo 738327 1110263 := bstep (se 1 (by rfl) ⟨832697, by rfl⟩ : syracuseStep 1110263 = 1665395) B1665395
theorem B3993857 : Blo 738327 3993857 := bstep (se 2 (by rfl) ⟨1497696, by rfl⟩ : syracuseStep 3993857 = 2995393) B2995393
theorem B1110287 : Blo 738327 1110287 := bstep (se 1 (by rfl) ⟨832715, by rfl⟩ : syracuseStep 1110287 = 1665431) B1665431
theorem B1110329 : Blo 738327 1110329 := bstep (se 2 (by rfl) ⟨416373, by rfl⟩ : syracuseStep 1110329 = 832747) B832747
theorem B2027891 : Blo 738327 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B1667447 : Blo 738327 1667447 := bstep (se 1 (by rfl) ⟨1250585, by rfl⟩ : syracuseStep 1667447 = 2501171) B2501171
theorem B1110407 : Blo 738327 1110407 := bstep (se 1 (by rfl) ⟨832805, by rfl⟩ : syracuseStep 1110407 = 1665611) B1665611
theorem B1110443 : Blo 738327 1110443 := bstep (se 1 (by rfl) ⟨832832, by rfl⟩ : syracuseStep 1110443 = 1665665) B1665665
theorem B1110473 : Blo 738327 1110473 := bstep (se 2 (by rfl) ⟨416427, by rfl⟩ : syracuseStep 1110473 = 832855) B832855
theorem B1667627 : Blo 738327 1667627 := bstep (se 1 (by rfl) ⟨1250720, by rfl⟩ : syracuseStep 1667627 = 2501441) B2501441
theorem B1110587 : Blo 738327 1110587 := bstep (se 1 (by rfl) ⟨832940, by rfl⟩ : syracuseStep 1110587 = 1665881) B1665881
theorem B1110647 : Blo 738327 1110647 := bstep (se 1 (by rfl) ⟨832985, by rfl⟩ : syracuseStep 1110647 = 1665971) B1665971
theorem B1110671 : Blo 738327 1110671 := bstep (se 1 (by rfl) ⟨833003, by rfl⟩ : syracuseStep 1110671 = 1666007) B1666007
theorem B1110713 : Blo 738327 1110713 := bstep (se 2 (by rfl) ⟨416517, by rfl⟩ : syracuseStep 1110713 = 833035) B833035
theorem B1110791 : Blo 738327 1110791 := bstep (se 1 (by rfl) ⟨833093, by rfl⟩ : syracuseStep 1110791 = 1666187) B1666187
theorem B1110827 : Blo 738327 1110827 := bstep (se 1 (by rfl) ⟨833120, by rfl⟩ : syracuseStep 1110827 = 1666241) B1666241
theorem B1110857 : Blo 738327 1110857 := bstep (se 2 (by rfl) ⟨416571, by rfl⟩ : syracuseStep 1110857 = 833143) B833143
theorem B1405831 : Blo 738327 1405831 := bstep (se 1 (by rfl) ⟨1054373, by rfl⟩ : syracuseStep 1405831 = 2108747) B2108747
theorem B1667987 : Blo 738327 1667987 := bstep (se 1 (by rfl) ⟨1250990, by rfl⟩ : syracuseStep 1667987 = 2501981) B2501981
theorem B1110971 : Blo 738327 1110971 := bstep (se 1 (by rfl) ⟨833228, by rfl⟩ : syracuseStep 1110971 = 1666457) B1666457
theorem B1668041 : Blo 738327 1668041 := bstep (se 2 (by rfl) ⟨625515, by rfl⟩ : syracuseStep 1668041 = 1251031) B1251031
theorem B1111031 : Blo 738327 1111031 := bstep (se 1 (by rfl) ⟨833273, by rfl⟩ : syracuseStep 1111031 = 1666547) B1666547
theorem B1111055 : Blo 738327 1111055 := bstep (se 1 (by rfl) ⟨833291, by rfl⟩ : syracuseStep 1111055 = 1666583) B1666583
theorem B2815019 : Blo 738327 2815019 := bstep (se 1 (by rfl) ⟨2111264, by rfl⟩ : syracuseStep 2815019 = 4222529) B4222529
theorem B1111097 : Blo 738327 1111097 := bstep (se 2 (by rfl) ⟨416661, by rfl⟩ : syracuseStep 1111097 = 833323) B833323
theorem B1111175 : Blo 738327 1111175 := bstep (se 1 (by rfl) ⟨833381, by rfl⟩ : syracuseStep 1111175 = 1666763) B1666763
theorem B1995923 : Blo 738327 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B947371 : Blo 738327 947371 := bstep (se 1 (by rfl) ⟨710528, by rfl⟩ : syracuseStep 947371 = 1421057) B1421057
theorem B1111211 : Blo 738327 1111211 := bstep (se 1 (by rfl) ⟨833408, by rfl⟩ : syracuseStep 1111211 = 1666817) B1666817
theorem B1111241 : Blo 738327 1111241 := bstep (se 2 (by rfl) ⟨416715, by rfl⟩ : syracuseStep 1111241 = 833431) B833431
theorem B5633225 : Blo 738327 5633225 := bstep (se 2 (by rfl) ⟨2112459, by rfl⟩ : syracuseStep 5633225 = 4224919) B4224919
theorem B1111355 : Blo 738327 1111355 := bstep (se 1 (by rfl) ⟨833516, by rfl⟩ : syracuseStep 1111355 = 1667033) B1667033
theorem B1111415 : Blo 738327 1111415 := bstep (se 1 (by rfl) ⟨833561, by rfl⟩ : syracuseStep 1111415 = 1667123) B1667123
theorem B1111439 : Blo 738327 1111439 := bstep (se 1 (by rfl) ⟨833579, by rfl⟩ : syracuseStep 1111439 = 1667159) B1667159
theorem B1406393 : Blo 738327 1406393 := bstep (se 2 (by rfl) ⟨527397, by rfl⟩ : syracuseStep 1406393 = 1054795) B1054795
theorem B1111481 : Blo 738327 1111481 := bstep (se 2 (by rfl) ⟨416805, by rfl⟩ : syracuseStep 1111481 = 833611) B833611
theorem B1111559 : Blo 738327 1111559 := bstep (se 1 (by rfl) ⟨833669, by rfl⟩ : syracuseStep 1111559 = 1667339) B1667339
theorem B1111595 : Blo 738327 1111595 := bstep (se 1 (by rfl) ⟨833696, by rfl⟩ : syracuseStep 1111595 = 1667393) B1667393
theorem B1111625 : Blo 738327 1111625 := bstep (se 2 (by rfl) ⟨416859, by rfl⟩ : syracuseStep 1111625 = 833719) B833719
theorem B1668743 : Blo 738327 1668743 := bstep (se 1 (by rfl) ⟨1251557, by rfl⟩ : syracuseStep 1668743 = 2503115) B2503115
theorem B1111739 : Blo 738327 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B1111799 : Blo 738327 1111799 := bstep (se 1 (by rfl) ⟨833849, by rfl⟩ : syracuseStep 1111799 = 1667699) B1667699
theorem B1111823 : Blo 738327 1111823 := bstep (se 1 (by rfl) ⟨833867, by rfl⟩ : syracuseStep 1111823 = 1667735) B1667735
theorem B1111865 : Blo 738327 1111865 := bstep (se 2 (by rfl) ⟨416949, by rfl⟩ : syracuseStep 1111865 = 833899) B833899
theorem B1668923 : Blo 738327 1668923 := bstep (se 1 (by rfl) ⟨1251692, by rfl⟩ : syracuseStep 1668923 = 2503385) B2503385
theorem B1111943 : Blo 738327 1111943 := bstep (se 1 (by rfl) ⟨833957, by rfl⟩ : syracuseStep 1111943 = 1667915) B1667915
theorem B1111979 : Blo 738327 1111979 := bstep (se 1 (by rfl) ⟨833984, by rfl⟩ : syracuseStep 1111979 = 1667969) B1667969
theorem B1669049 : Blo 738327 1669049 := bstep (se 2 (by rfl) ⟨625893, by rfl⟩ : syracuseStep 1669049 = 1251787) B1251787
theorem B1112009 : Blo 738327 1112009 := bstep (se 2 (by rfl) ⟨417003, by rfl⟩ : syracuseStep 1112009 = 834007) B834007
theorem B1112123 : Blo 738327 1112123 := bstep (se 1 (by rfl) ⟨834092, by rfl⟩ : syracuseStep 1112123 = 1668185) B1668185
theorem B1112183 : Blo 738327 1112183 := bstep (se 1 (by rfl) ⟨834137, by rfl⟩ : syracuseStep 1112183 = 1668275) B1668275
theorem B1112207 : Blo 738327 1112207 := bstep (se 1 (by rfl) ⟨834155, by rfl⟩ : syracuseStep 1112207 = 1668311) B1668311
theorem B1112249 : Blo 738327 1112249 := bstep (se 2 (by rfl) ⟨417093, by rfl⟩ : syracuseStep 1112249 = 834187) B834187
theorem B1112327 : Blo 738327 1112327 := bstep (se 1 (by rfl) ⟨834245, by rfl⟩ : syracuseStep 1112327 = 1668491) B1668491
theorem B3078415 : Blo 738327 3078415 := bstep (se 1 (by rfl) ⟨2308811, by rfl⟩ : syracuseStep 3078415 = 4617623) B4617623
theorem B1669391 : Blo 738327 1669391 := bstep (se 1 (by rfl) ⟨1252043, by rfl⟩ : syracuseStep 1669391 = 2504087) B2504087
theorem B1669409 : Blo 738327 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B1112363 : Blo 738327 1112363 := bstep (se 1 (by rfl) ⟨834272, by rfl⟩ : syracuseStep 1112363 = 1668545) B1668545
theorem B1112393 : Blo 738327 1112393 := bstep (se 2 (by rfl) ⟨417147, by rfl⟩ : syracuseStep 1112393 = 834295) B834295
theorem B1112507 : Blo 738327 1112507 := bstep (se 1 (by rfl) ⟨834380, by rfl⟩ : syracuseStep 1112507 = 1668761) B1668761
theorem B1112567 : Blo 738327 1112567 := bstep (se 1 (by rfl) ⟨834425, by rfl⟩ : syracuseStep 1112567 = 1668851) B1668851
theorem B1112591 : Blo 738327 1112591 := bstep (se 1 (by rfl) ⟨834443, by rfl⟩ : syracuseStep 1112591 = 1668887) B1668887
theorem B1112633 : Blo 738327 1112633 := bstep (se 2 (by rfl) ⟨417237, by rfl⟩ : syracuseStep 1112633 = 834475) B834475
theorem B1407547 : Blo 738327 1407547 := bstep (se 1 (by rfl) ⟨1055660, by rfl⟩ : syracuseStep 1407547 = 2111321) B2111321
theorem B1669751 : Blo 738327 1669751 := bstep (se 1 (by rfl) ⟨1252313, by rfl⟩ : syracuseStep 1669751 = 2504627) B2504627
theorem B1112711 : Blo 738327 1112711 := bstep (se 1 (by rfl) ⟨834533, by rfl⟩ : syracuseStep 1112711 = 1669067) B1669067
theorem B1112747 : Blo 738327 1112747 := bstep (se 1 (by rfl) ⟨834560, by rfl⟩ : syracuseStep 1112747 = 1669121) B1669121
theorem B1112777 : Blo 738327 1112777 := bstep (se 2 (by rfl) ⟨417291, by rfl⟩ : syracuseStep 1112777 = 834583) B834583
theorem B1669931 : Blo 738327 1669931 := bstep (se 1 (by rfl) ⟨1252448, by rfl⟩ : syracuseStep 1669931 = 2504897) B2504897
theorem B1112891 : Blo 738327 1112891 := bstep (se 1 (by rfl) ⟨834668, by rfl⟩ : syracuseStep 1112891 = 1669337) B1669337
theorem B1112951 : Blo 738327 1112951 := bstep (se 1 (by rfl) ⟨834713, by rfl⟩ : syracuseStep 1112951 = 1669427) B1669427
theorem B1112975 : Blo 738327 1112975 := bstep (se 1 (by rfl) ⟨834731, by rfl⟩ : syracuseStep 1112975 = 1669463) B1669463
theorem B1113017 : Blo 738327 1113017 := bstep (se 2 (by rfl) ⟨417381, by rfl⟩ : syracuseStep 1113017 = 834763) B834763
theorem B2816977 : Blo 738327 2816977 := bstep (se 2 (by rfl) ⟨1056366, by rfl⟩ : syracuseStep 2816977 = 2112733) B2112733
theorem B1113095 : Blo 738327 1113095 := bstep (se 1 (by rfl) ⟨834821, by rfl⟩ : syracuseStep 1113095 = 1669643) B1669643
theorem B1408033 : Blo 738327 1408033 := bstep (se 2 (by rfl) ⟨528012, by rfl⟩ : syracuseStep 1408033 = 1056025) B1056025
theorem B1113131 : Blo 738327 1113131 := bstep (se 1 (by rfl) ⟨834848, by rfl⟩ : syracuseStep 1113131 = 1669697) B1669697
theorem B1113161 : Blo 738327 1113161 := bstep (se 2 (by rfl) ⟨417435, by rfl⟩ : syracuseStep 1113161 = 834871) B834871
theorem B1113275 : Blo 738327 1113275 := bstep (se 1 (by rfl) ⟨834956, by rfl⟩ : syracuseStep 1113275 = 1669913) B1669913
theorem B2849993 : Blo 738327 2849993 := bstep (se 2 (by rfl) ⟨1068747, by rfl⟩ : syracuseStep 2849993 = 2137495) B2137495
theorem B7109869 : Blo 738327 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B1113335 : Blo 738327 1113335 := bstep (se 1 (by rfl) ⟨835001, by rfl⟩ : syracuseStep 1113335 = 1670003) B1670003
theorem B2817281 : Blo 738327 2817281 := bstep (se 2 (by rfl) ⟨1056480, by rfl⟩ : syracuseStep 2817281 = 2112961) B2112961
theorem B1113359 : Blo 738327 1113359 := bstep (se 1 (by rfl) ⟨835019, by rfl⟩ : syracuseStep 1113359 = 1670039) B1670039
theorem B1113401 : Blo 738327 1113401 := bstep (se 2 (by rfl) ⟨417525, by rfl⟩ : syracuseStep 1113401 = 835051) B835051
theorem B1113479 : Blo 738327 1113479 := bstep (se 1 (by rfl) ⟨835109, by rfl⟩ : syracuseStep 1113479 = 1670219) B1670219
theorem B2817737 : Blo 738327 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B2162447 : Blo 738327 2162447 := bstep (se 1 (by rfl) ⟨1621835, by rfl⟩ : syracuseStep 2162447 = 3243671) B3243671
theorem B32047001 : Blo 738327 32047001 := bstep (se 2 (by rfl) ⟨12017625, by rfl⟩ : syracuseStep 32047001 = 24035251) B24035251
theorem B6422435 : Blo 738327 6422435 := bstep (se 1 (by rfl) ⟨4816826, by rfl⟩ : syracuseStep 6422435 = 9633653) B9633653
theorem B1540495 : Blo 738327 1540495 := bstep (se 1 (by rfl) ⟨1155371, by rfl⟩ : syracuseStep 1540495 = 2310743) B2310743
theorem B9503405 : Blo 738327 9503405 := bstep (se 3 (by rfl) ⟨1781888, by rfl⟩ : syracuseStep 9503405 = 3563777) B3563777
theorem B1246171 : Blo 738327 1246171 := bstep (se 1 (by rfl) ⟨934628, by rfl⟩ : syracuseStep 1246171 = 1869257) B1869257
theorem B4490435 : Blo 738327 4490435 := bstep (se 1 (by rfl) ⟨3367826, by rfl⟩ : syracuseStep 4490435 = 6735653) B6735653
theorem B31950125 : Blo 738327 31950125 := bstep (se 3 (by rfl) ⟨5990648, by rfl⟩ : syracuseStep 31950125 = 11981297) B11981297
theorem B16418213 : Blo 738327 16418213 := bstep (se 4 (by rfl) ⟨1539207, by rfl⟩ : syracuseStep 16418213 = 3078415) B3078415
theorem B2491937 : Blo 738327 2491937 := bstep (se 2 (by rfl) ⟨934476, by rfl⟩ : syracuseStep 2491937 = 1868953) B1868953
theorem B5342759 : Blo 738327 5342759 := bstep (se 1 (by rfl) ⟨4007069, by rfl⟩ : syracuseStep 5342759 = 8014139) B8014139
theorem B1246799 : Blo 738327 1246799 := bstep (se 1 (by rfl) ⟨935099, by rfl⟩ : syracuseStep 1246799 = 1870199) B1870199
theorem B2492153 : Blo 738327 2492153 := bstep (se 2 (by rfl) ⟨934557, by rfl⟩ : syracuseStep 2492153 = 1869115) B1869115
theorem B2000713 : Blo 738327 2000713 := bstep (se 2 (by rfl) ⟨750267, by rfl⟩ : syracuseStep 2000713 = 1500535) B1500535
theorem B1869743 : Blo 738327 1869743 := bstep (se 1 (by rfl) ⟨1402307, by rfl⟩ : syracuseStep 1869743 = 2804615) B2804615
theorem B8652737 : Blo 738327 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B2492423 : Blo 738327 2492423 := bstep (se 1 (by rfl) ⟨1869317, by rfl⟩ : syracuseStep 2492423 = 3738635) B3738635
theorem B4556837 : Blo 738327 4556837 := bstep (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) B854407
theorem B2492531 : Blo 738327 2492531 := bstep (se 1 (by rfl) ⟨1869398, by rfl⟩ : syracuseStep 2492531 = 3738797) B3738797
theorem B2492801 : Blo 738327 2492801 := bstep (se 2 (by rfl) ⟨934800, by rfl⟩ : syracuseStep 2492801 = 1869601) B1869601
theorem B2001295 : Blo 738327 2001295 := bstep (se 1 (by rfl) ⟨1500971, by rfl⟩ : syracuseStep 2001295 = 3001943) B3001943
theorem B1247663 : Blo 738327 1247663 := bstep (se 1 (by rfl) ⟨935747, by rfl⟩ : syracuseStep 1247663 = 1871495) B1871495
theorem B1870361 : Blo 738327 1870361 := bstep (se 2 (by rfl) ⟨701385, by rfl⟩ : syracuseStep 1870361 = 1402771) B1402771
theorem B23989067 : Blo 738327 23989067 := bstep (se 1 (by rfl) ⟨17991800, by rfl⟩ : syracuseStep 23989067 = 35983601) B35983601
theorem B1248095 : Blo 738327 1248095 := bstep (se 1 (by rfl) ⟨936071, by rfl⟩ : syracuseStep 1248095 = 1872143) B1872143
theorem B2001977 : Blo 738327 2001977 := bstep (se 2 (by rfl) ⟨750741, by rfl⟩ : syracuseStep 2001977 = 1501483) B1501483
theorem B2853967 : Blo 738327 2853967 := bstep (se 1 (by rfl) ⟨2140475, by rfl⟩ : syracuseStep 2853967 = 4280951) B4280951
theorem B2493611 : Blo 738327 2493611 := bstep (se 1 (by rfl) ⟨1870208, by rfl⟩ : syracuseStep 2493611 = 3740417) B3740417
theorem B4001015 : Blo 738327 4001015 := bstep (se 1 (by rfl) ⟨3000761, by rfl⟩ : syracuseStep 4001015 = 6001523) B6001523
theorem B5147993 : Blo 738327 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B1248655 : Blo 738327 1248655 := bstep (se 1 (by rfl) ⟨936491, by rfl⟩ : syracuseStep 1248655 = 1872983) B1872983
theorem B888283 : Blo 738327 888283 := bstep (se 1 (by rfl) ⟨666212, by rfl⟩ : syracuseStep 888283 = 1332425) B1332425
theorem B4754983 : Blo 738327 4754983 := bstep (se 1 (by rfl) ⟨3566237, by rfl⟩ : syracuseStep 4754983 = 7132475) B7132475
theorem B3739283 : Blo 738327 3739283 := bstep (se 1 (by rfl) ⟨2804462, by rfl⟩ : syracuseStep 3739283 = 5608925) B5608925
theorem B1183403 : Blo 738327 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B2494151 : Blo 738327 2494151 := bstep (se 1 (by rfl) ⟨1870613, by rfl⟩ : syracuseStep 2494151 = 3741227) B3741227
theorem B790447 : Blo 738327 790447 := bstep (se 1 (by rfl) ⟨592835, by rfl⟩ : syracuseStep 790447 = 1185671) B1185671
theorem B1249337 : Blo 738327 1249337 := bstep (se 2 (by rfl) ⟨468501, by rfl⟩ : syracuseStep 1249337 = 937003) B937003
theorem B21958771 : Blo 738327 21958771 := bstep (se 1 (by rfl) ⟨16469078, by rfl⟩ : syracuseStep 21958771 = 32938157) B32938157
theorem B1282171 : Blo 738327 1282171 := bstep (se 1 (by rfl) ⟨961628, by rfl⟩ : syracuseStep 1282171 = 1923257) B1923257
theorem B1184107 : Blo 738327 1184107 := bstep (se 1 (by rfl) ⟨888080, by rfl⟩ : syracuseStep 1184107 = 1776161) B1776161
theorem B3805721 : Blo 738327 3805721 := bstep (se 2 (by rfl) ⟨1427145, by rfl⟩ : syracuseStep 3805721 = 2854291) B2854291
theorem B2495015 : Blo 738327 2495015 := bstep (se 1 (by rfl) ⟨1871261, by rfl⟩ : syracuseStep 2495015 = 3742523) B3742523
theorem B1053263 : Blo 738327 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B2495123 : Blo 738327 2495123 := bstep (se 1 (by rfl) ⟨1871342, by rfl⟩ : syracuseStep 2495123 = 3742685) B3742685
theorem B1250039 : Blo 738327 1250039 := bstep (se 1 (by rfl) ⟨937529, by rfl⟩ : syracuseStep 1250039 = 1875059) B1875059
theorem B2495339 : Blo 738327 2495339 := bstep (se 1 (by rfl) ⟨1871504, by rfl⟩ : syracuseStep 2495339 = 3743009) B3743009
theorem B2495393 : Blo 738327 2495393 := bstep (se 2 (by rfl) ⟨935772, by rfl⟩ : syracuseStep 2495393 = 1871545) B1871545
theorem B19502045 : Blo 738327 19502045 := bstep (se 3 (by rfl) ⟨3656633, by rfl⟩ : syracuseStep 19502045 = 7313267) B7313267
theorem B1872953 : Blo 738327 1872953 := bstep (se 2 (by rfl) ⟨702357, by rfl⟩ : syracuseStep 1872953 = 1404715) B1404715
theorem B1250383 : Blo 738327 1250383 := bstep (se 1 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 1250383 = 1875575) B1875575
theorem B1250633 : Blo 738327 1250633 := bstep (se 2 (by rfl) ⟨468987, by rfl⟩ : syracuseStep 1250633 = 937975) B937975
theorem B1349039 : Blo 738327 1349039 := bstep (se 1 (by rfl) ⟨1011779, by rfl⟩ : syracuseStep 1349039 = 2023559) B2023559
theorem B2495987 : Blo 738327 2495987 := bstep (se 1 (by rfl) ⟨1871990, by rfl⟩ : syracuseStep 2495987 = 3743981) B3743981
theorem B1185337 : Blo 738327 1185337 := bstep (se 2 (by rfl) ⟨444501, by rfl⟩ : syracuseStep 1185337 = 889003) B889003
theorem B2102881 : Blo 738327 2102881 := bstep (se 2 (by rfl) ⟨788580, by rfl⟩ : syracuseStep 2102881 = 1577161) B1577161
theorem B1578707 : Blo 738327 1578707 := bstep (se 1 (by rfl) ⟨1184030, by rfl⟩ : syracuseStep 1578707 = 2368061) B2368061
theorem B1251065 : Blo 738327 1251065 := bstep (se 2 (by rfl) ⟨469149, by rfl⟩ : syracuseStep 1251065 = 938299) B938299
theorem B3806969 : Blo 738327 3806969 := bstep (se 2 (by rfl) ⟨1427613, by rfl⟩ : syracuseStep 3806969 = 2855227) B2855227
theorem B1251247 : Blo 738327 1251247 := bstep (se 1 (by rfl) ⟨938435, by rfl⟩ : syracuseStep 1251247 = 1876871) B1876871
theorem B1251335 : Blo 738327 1251335 := bstep (se 1 (by rfl) ⟨938501, by rfl⟩ : syracuseStep 1251335 = 1877003) B1877003
theorem B2496527 : Blo 738327 2496527 := bstep (se 1 (by rfl) ⟨1872395, by rfl⟩ : syracuseStep 2496527 = 3744791) B3744791
theorem B1251679 : Blo 738327 1251679 := bstep (se 1 (by rfl) ⟨938759, by rfl⟩ : syracuseStep 1251679 = 1877519) B1877519
theorem B1251767 : Blo 738327 1251767 := bstep (se 1 (by rfl) ⟨938825, by rfl⟩ : syracuseStep 1251767 = 1877651) B1877651
theorem B1186235 : Blo 738327 1186235 := bstep (se 1 (by rfl) ⟨889676, by rfl⟩ : syracuseStep 1186235 = 1779353) B1779353
theorem B1874441 : Blo 738327 1874441 := bstep (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) B1405831
theorem B2365985 : Blo 738327 2365985 := bstep (se 2 (by rfl) ⟨887244, by rfl⟩ : syracuseStep 2365985 = 1774489) B1774489
theorem B2497121 : Blo 738327 2497121 := bstep (se 2 (by rfl) ⟨936420, by rfl⟩ : syracuseStep 2497121 = 1872841) B1872841
theorem B1186427 : Blo 738327 1186427 := bstep (se 1 (by rfl) ⟨889820, by rfl⟩ : syracuseStep 1186427 = 1779641) B1779641
theorem B2366471 : Blo 738327 2366471 := bstep (se 1 (by rfl) ⟨1774853, by rfl⟩ : syracuseStep 2366471 = 3549707) B3549707
theorem B1252361 : Blo 738327 1252361 := bstep (se 2 (by rfl) ⟨469635, by rfl⟩ : syracuseStep 1252361 = 939271) B939271
theorem B2104339 : Blo 738327 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B5217331 : Blo 738327 5217331 := bstep (se 1 (by rfl) ⟨3912998, by rfl⟩ : syracuseStep 5217331 = 7825997) B7825997
theorem B1252523 : Blo 738327 1252523 := bstep (se 1 (by rfl) ⟨939392, by rfl⟩ : syracuseStep 1252523 = 1878785) B1878785
theorem B9510533 : Blo 738327 9510533 := bstep (se 4 (by rfl) ⟨891612, by rfl⟩ : syracuseStep 9510533 = 1783225) B1783225
theorem B1875595 : Blo 738327 1875595 := bstep (se 1 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 1875595 = 2813393) B2813393
theorem B15966071 : Blo 738327 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B1777583 : Blo 738327 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B5054393 : Blo 738327 5054393 := bstep (se 2 (by rfl) ⟨1895397, by rfl⟩ : syracuseStep 5054393 = 3790795) B3790795
theorem B1875899 : Blo 738327 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B1056731 : Blo 738327 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B1187849 : Blo 738327 1187849 := bstep (se 2 (by rfl) ⟨445443, by rfl⟩ : syracuseStep 1187849 = 890887) B890887
theorem B46768141 : Blo 738327 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B2498579 : Blo 738327 2498579 := bstep (se 1 (by rfl) ⟨1873934, by rfl⟩ : syracuseStep 2498579 = 3747869) B3747869
theorem B2662571 : Blo 738327 2662571 := bstep (se 1 (by rfl) ⟨1996928, by rfl⟩ : syracuseStep 2662571 = 3993857) B3993857
theorem B1351927 : Blo 738327 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B2498903 : Blo 738327 2498903 := bstep (se 1 (by rfl) ⟨1874177, by rfl⟩ : syracuseStep 2498903 = 3748355) B3748355
theorem B23142971 : Blo 738327 23142971 := bstep (se 1 (by rfl) ⟨17357228, by rfl⟩ : syracuseStep 23142971 = 34714457) B34714457
theorem B1876679 : Blo 738327 1876679 := bstep (se 1 (by rfl) ⟨1407509, by rfl⟩ : syracuseStep 1876679 = 2815019) B2815019
theorem B3744467 : Blo 738327 3744467 := bstep (se 1 (by rfl) ⟨2808350, by rfl⟩ : syracuseStep 3744467 = 5616701) B5616701
theorem B2106071 : Blo 738327 2106071 := bstep (se 1 (by rfl) ⟨1579553, by rfl⟩ : syracuseStep 2106071 = 3159107) B3159107
theorem B1876729 : Blo 738327 1876729 := bstep (se 2 (by rfl) ⟨703773, by rfl⟩ : syracuseStep 1876729 = 1407547) B1407547
theorem B2106287 : Blo 738327 2106287 := bstep (se 1 (by rfl) ⟨1579715, by rfl⟩ : syracuseStep 2106287 = 3159431) B3159431
theorem B2368855 : Blo 738327 2368855 := bstep (se 1 (by rfl) ⟨1776641, by rfl⟩ : syracuseStep 2368855 = 3553283) B3553283
theorem B1877377 : Blo 738327 1877377 := bstep (se 2 (by rfl) ⟨704016, by rfl⟩ : syracuseStep 1877377 = 1408033) B1408033
theorem B2499983 : Blo 738327 2499983 := bstep (se 1 (by rfl) ⟨1874987, by rfl⟩ : syracuseStep 2499983 = 3749975) B3749975
theorem B2467361 : Blo 738327 2467361 := bstep (se 2 (by rfl) ⟨925260, by rfl⟩ : syracuseStep 2467361 = 1850521) B1850521
theorem B9479825 : Blo 738327 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B2500307 : Blo 738327 2500307 := bstep (se 1 (by rfl) ⟨1875230, by rfl⟩ : syracuseStep 2500307 = 3750461) B3750461
theorem B3155705 : Blo 738327 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B2107129 : Blo 738327 2107129 := bstep (se 2 (by rfl) ⟨790173, by rfl⟩ : syracuseStep 2107129 = 1580347) B1580347
theorem B7219003 : Blo 738327 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B13510489 : Blo 738327 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B2107471 : Blo 738327 2107471 := bstep (se 1 (by rfl) ⟨1580603, by rfl⟩ : syracuseStep 2107471 = 3161207) B3161207
theorem B1583183 : Blo 738327 1583183 := bstep (se 1 (by rfl) ⟨1187387, by rfl⟩ : syracuseStep 1583183 = 2374775) B2374775
theorem B1878187 : Blo 738327 1878187 := bstep (se 1 (by rfl) ⟨1408640, by rfl⟩ : syracuseStep 1878187 = 2817281) B2817281
theorem B1878491 : Blo 738327 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B1518443 : Blo 738327 1518443 := bstep (se 1 (by rfl) ⟨1138832, by rfl⟩ : syracuseStep 1518443 = 2277665) B2277665
theorem B2501495 : Blo 738327 2501495 := bstep (se 1 (by rfl) ⟨1876121, by rfl⟩ : syracuseStep 2501495 = 3752243) B3752243
theorem B3746735 : Blo 738327 3746735 := bstep (se 1 (by rfl) ⟨2810051, by rfl⟩ : syracuseStep 3746735 = 5620103) B5620103
theorem B2501711 : Blo 738327 2501711 := bstep (se 1 (by rfl) ⟨1876283, by rfl⟩ : syracuseStep 2501711 = 3752567) B3752567
theorem B2108587 : Blo 738327 2108587 := bstep (se 1 (by rfl) ⟨1581440, by rfl⟩ : syracuseStep 2108587 = 3162881) B3162881
theorem B2502089 : Blo 738327 2502089 := bstep (se 2 (by rfl) ⟨938283, by rfl⟩ : syracuseStep 2502089 = 1876567) B1876567
theorem B1584679 : Blo 738327 1584679 := bstep (se 1 (by rfl) ⟨1188509, by rfl⟩ : syracuseStep 1584679 = 2377019) B2377019
theorem B831055 : Blo 738327 831055 := bstep (se 1 (by rfl) ⟨623291, by rfl⟩ : syracuseStep 831055 = 1246583) B1246583
theorem B5615243 : Blo 738327 5615243 := bstep (se 1 (by rfl) ⟨4211432, by rfl⟩ : syracuseStep 5615243 = 8422865) B8422865
theorem B2502359 : Blo 738327 2502359 := bstep (se 1 (by rfl) ⟨1876769, by rfl⟩ : syracuseStep 2502359 = 3753539) B3753539
theorem B2994029 : Blo 738327 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B2502575 : Blo 738327 2502575 := bstep (se 1 (by rfl) ⟨1876931, by rfl⟩ : syracuseStep 2502575 = 3753863) B3753863
theorem B831451 : Blo 738327 831451 := bstep (se 1 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 831451 = 1247177) B1247177
theorem B5779763 : Blo 738327 5779763 := bstep (se 1 (by rfl) ⟨4334822, by rfl⟩ : syracuseStep 5779763 = 8669645) B8669645
theorem B831919 : Blo 738327 831919 := bstep (se 1 (by rfl) ⟨623939, by rfl⟩ : syracuseStep 831919 = 1247879) B1247879
theorem B832351 : Blo 738327 832351 := bstep (se 1 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 832351 = 1248527) B1248527
theorem B18035779 : Blo 738327 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B832711 : Blo 738327 832711 := bstep (se 1 (by rfl) ⟨624533, by rfl⟩ : syracuseStep 832711 = 1249067) B1249067
theorem B4732303 : Blo 738327 4732303 := bstep (se 1 (by rfl) ⟨3549227, by rfl⟩ : syracuseStep 4732303 = 7098455) B7098455
theorem B3553091 : Blo 738327 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B3160079 : Blo 738327 3160079 := bstep (se 1 (by rfl) ⟨2370059, by rfl⟩ : syracuseStep 3160079 = 4740119) B4740119
theorem B833575 : Blo 738327 833575 := bstep (se 1 (by rfl) ⟨625181, by rfl⟩ : syracuseStep 833575 = 1250363) B1250363
theorem B2504951 : Blo 738327 2504951 := bstep (se 1 (by rfl) ⟨1878713, by rfl⟩ : syracuseStep 2504951 = 3757427) B3757427
theorem B6339019 : Blo 738327 6339019 := bstep (se 1 (by rfl) ⟨4754264, by rfl⟩ : syracuseStep 6339019 = 9508529) B9508529
theorem B2505275 : Blo 738327 2505275 := bstep (se 1 (by rfl) ⟨1878956, by rfl⟩ : syracuseStep 2505275 = 3757913) B3757913
theorem B2669431 : Blo 738327 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B4734071 : Blo 738327 4734071 := bstep (se 1 (by rfl) ⟨3550553, by rfl⟩ : syracuseStep 4734071 = 7101107) B7101107
theorem B7584961 : Blo 738327 7584961 := bstep (se 2 (by rfl) ⟨2844360, by rfl⟩ : syracuseStep 7584961 = 5688721) B5688721
theorem B2113121 : Blo 738327 2113121 := bstep (se 2 (by rfl) ⟨792420, by rfl⟩ : syracuseStep 2113121 = 1584841) B1584841
theorem B2375315 : Blo 738327 2375315 := bstep (se 1 (by rfl) ⟨1781486, by rfl⟩ : syracuseStep 2375315 = 3562973) B3562973
theorem B2113235 : Blo 738327 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B4734787 : Blo 738327 4734787 := bstep (se 1 (by rfl) ⟨3551090, by rfl⟩ : syracuseStep 4734787 = 7102181) B7102181
theorem B5619617 : Blo 738327 5619617 := bstep (se 2 (by rfl) ⟨2107356, by rfl⟩ : syracuseStep 5619617 = 4214713) B4214713
theorem B10141625 : Blo 738327 10141625 := bstep (se 2 (by rfl) ⟨3803109, by rfl⟩ : syracuseStep 10141625 = 7606219) B7606219
theorem B3424523 : Blo 738327 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B2671163 : Blo 738327 2671163 := bstep (se 1 (by rfl) ⟨2003372, by rfl⟩ : syracuseStep 2671163 = 4006745) B4006745
theorem B2277985 : Blo 738327 2277985 := bstep (se 2 (by rfl) ⟨854244, by rfl⟩ : syracuseStep 2277985 = 1708489) B1708489
theorem B934831 : Blo 738327 934831 := bstep (se 1 (by rfl) ⟨701123, by rfl⟩ : syracuseStep 934831 = 1402247) B1402247
theorem B738343 : Blo 738327 738343 := bstep (se 1 (by rfl) ⟨553757, by rfl⟩ : syracuseStep 738343 = 1107515) B1107515
theorem B738383 : Blo 738327 738383 := bstep (se 1 (by rfl) ⟨553787, by rfl⟩ : syracuseStep 738383 = 1107575) B1107575
theorem B738399 : Blo 738327 738399 := bstep (se 1 (by rfl) ⟨553799, by rfl⟩ : syracuseStep 738399 = 1107599) B1107599
theorem B8438903 : Blo 738327 8438903 := bstep (se 1 (by rfl) ⟨6329177, by rfl⟩ : syracuseStep 8438903 = 12658355) B12658355
theorem B738427 : Blo 738327 738427 := bstep (se 1 (by rfl) ⟨553820, by rfl⟩ : syracuseStep 738427 = 1107641) B1107641
theorem B738479 : Blo 738327 738479 := bstep (se 1 (by rfl) ⟨553859, by rfl⟩ : syracuseStep 738479 = 1107719) B1107719
theorem B738503 : Blo 738327 738503 := bstep (se 1 (by rfl) ⟨553877, by rfl⟩ : syracuseStep 738503 = 1107755) B1107755
theorem B738523 : Blo 738327 738523 := bstep (se 1 (by rfl) ⟨553892, by rfl⟩ : syracuseStep 738523 = 1107785) B1107785
theorem B738599 : Blo 738327 738599 := bstep (se 1 (by rfl) ⟨553949, by rfl⟩ : syracuseStep 738599 = 1107899) B1107899
theorem B738639 : Blo 738327 738639 := bstep (se 1 (by rfl) ⟨553979, by rfl⟩ : syracuseStep 738639 = 1107959) B1107959
theorem B738655 : Blo 738327 738655 := bstep (se 1 (by rfl) ⟨553991, by rfl⟩ : syracuseStep 738655 = 1107983) B1107983
theorem B738683 : Blo 738327 738683 := bstep (se 1 (by rfl) ⟨554012, by rfl⟩ : syracuseStep 738683 = 1108025) B1108025
theorem B3556781 : Blo 738327 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B738735 : Blo 738327 738735 := bstep (se 1 (by rfl) ⟨554051, by rfl⟩ : syracuseStep 738735 = 1108103) B1108103
theorem B738759 : Blo 738327 738759 := bstep (se 1 (by rfl) ⟨554069, by rfl⟩ : syracuseStep 738759 = 1108139) B1108139
theorem B738779 : Blo 738327 738779 := bstep (se 1 (by rfl) ⟨554084, by rfl⟩ : syracuseStep 738779 = 1108169) B1108169
theorem B738855 : Blo 738327 738855 := bstep (se 1 (by rfl) ⟨554141, by rfl⟩ : syracuseStep 738855 = 1108283) B1108283
theorem B1263161 : Blo 738327 1263161 := bstep (se 2 (by rfl) ⟨473685, by rfl⟩ : syracuseStep 1263161 = 947371) B947371
theorem B738895 : Blo 738327 738895 := bstep (se 1 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 738895 = 1108343) B1108343
theorem B738911 : Blo 738327 738911 := bstep (se 1 (by rfl) ⟨554183, by rfl⟩ : syracuseStep 738911 = 1108367) B1108367
theorem B738939 : Blo 738327 738939 := bstep (se 1 (by rfl) ⟨554204, by rfl⟩ : syracuseStep 738939 = 1108409) B1108409
theorem B738991 : Blo 738327 738991 := bstep (se 1 (by rfl) ⟨554243, by rfl⟩ : syracuseStep 738991 = 1108487) B1108487
theorem B739015 : Blo 738327 739015 := bstep (se 1 (by rfl) ⟨554261, by rfl⟩ : syracuseStep 739015 = 1108523) B1108523
theorem B41043671 : Blo 738327 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B739035 : Blo 738327 739035 := bstep (se 1 (by rfl) ⟨554276, by rfl⟩ : syracuseStep 739035 = 1108553) B1108553
theorem B739111 : Blo 738327 739111 := bstep (se 1 (by rfl) ⟨554333, by rfl⟩ : syracuseStep 739111 = 1108667) B1108667
theorem B739151 : Blo 738327 739151 := bstep (se 1 (by rfl) ⟨554363, by rfl⟩ : syracuseStep 739151 = 1108727) B1108727
theorem B739167 : Blo 738327 739167 := bstep (se 1 (by rfl) ⟨554375, by rfl⟩ : syracuseStep 739167 = 1108751) B1108751
theorem B739195 : Blo 738327 739195 := bstep (se 1 (by rfl) ⟨554396, by rfl⟩ : syracuseStep 739195 = 1108793) B1108793
theorem B739247 : Blo 738327 739247 := bstep (se 1 (by rfl) ⟨554435, by rfl⟩ : syracuseStep 739247 = 1108871) B1108871
theorem B2803643 : Blo 738327 2803643 := bstep (se 1 (by rfl) ⟨2102732, by rfl⟩ : syracuseStep 2803643 = 4205465) B4205465
theorem B739271 : Blo 738327 739271 := bstep (se 1 (by rfl) ⟨554453, by rfl⟩ : syracuseStep 739271 = 1108907) B1108907
theorem B739291 : Blo 738327 739291 := bstep (se 1 (by rfl) ⟨554468, by rfl⟩ : syracuseStep 739291 = 1108937) B1108937
theorem B739367 : Blo 738327 739367 := bstep (se 1 (by rfl) ⟨554525, by rfl⟩ : syracuseStep 739367 = 1109051) B1109051
theorem B935975 : Blo 738327 935975 := bstep (se 1 (by rfl) ⟨701981, by rfl⟩ : syracuseStep 935975 = 1403963) B1403963
theorem B739407 : Blo 738327 739407 := bstep (se 1 (by rfl) ⟨554555, by rfl⟩ : syracuseStep 739407 = 1109111) B1109111
theorem B739423 : Blo 738327 739423 := bstep (se 1 (by rfl) ⟨554567, by rfl⟩ : syracuseStep 739423 = 1109135) B1109135
theorem B739451 : Blo 738327 739451 := bstep (se 1 (by rfl) ⟨554588, by rfl⟩ : syracuseStep 739451 = 1109177) B1109177
theorem B739503 : Blo 738327 739503 := bstep (se 1 (by rfl) ⟨554627, by rfl⟩ : syracuseStep 739503 = 1109255) B1109255
theorem B739527 : Blo 738327 739527 := bstep (se 1 (by rfl) ⟨554645, by rfl⟩ : syracuseStep 739527 = 1109291) B1109291
theorem B739547 : Blo 738327 739547 := bstep (se 1 (by rfl) ⟨554660, by rfl⟩ : syracuseStep 739547 = 1109321) B1109321
theorem B739623 : Blo 738327 739623 := bstep (se 1 (by rfl) ⟨554717, by rfl⟩ : syracuseStep 739623 = 1109435) B1109435
theorem B739663 : Blo 738327 739663 := bstep (se 1 (by rfl) ⟨554747, by rfl⟩ : syracuseStep 739663 = 1109495) B1109495
theorem B739679 : Blo 738327 739679 := bstep (se 1 (by rfl) ⟨554759, by rfl⟩ : syracuseStep 739679 = 1109519) B1109519
theorem B3164521 : Blo 738327 3164521 := bstep (se 2 (by rfl) ⟨1186695, by rfl⟩ : syracuseStep 3164521 = 2373391) B2373391
theorem B936299 : Blo 738327 936299 := bstep (se 1 (by rfl) ⟨702224, by rfl⟩ : syracuseStep 936299 = 1404449) B1404449
theorem B739707 : Blo 738327 739707 := bstep (se 1 (by rfl) ⟨554780, by rfl⟩ : syracuseStep 739707 = 1109561) B1109561
theorem B739759 : Blo 738327 739759 := bstep (se 1 (by rfl) ⟨554819, by rfl⟩ : syracuseStep 739759 = 1109639) B1109639
theorem B739783 : Blo 738327 739783 := bstep (se 1 (by rfl) ⟨554837, by rfl⟩ : syracuseStep 739783 = 1109675) B1109675
theorem B739803 : Blo 738327 739803 := bstep (se 1 (by rfl) ⟨554852, by rfl⟩ : syracuseStep 739803 = 1109705) B1109705
theorem B739879 : Blo 738327 739879 := bstep (se 1 (by rfl) ⟨554909, by rfl⟩ : syracuseStep 739879 = 1109819) B1109819
theorem B739919 : Blo 738327 739919 := bstep (se 1 (by rfl) ⟨554939, by rfl⟩ : syracuseStep 739919 = 1109879) B1109879
theorem B739935 : Blo 738327 739935 := bstep (se 1 (by rfl) ⟨554951, by rfl⟩ : syracuseStep 739935 = 1109903) B1109903
theorem B739963 : Blo 738327 739963 := bstep (se 1 (by rfl) ⟨554972, by rfl⟩ : syracuseStep 739963 = 1109945) B1109945
theorem B740015 : Blo 738327 740015 := bstep (se 1 (by rfl) ⟨555011, by rfl⟩ : syracuseStep 740015 = 1110023) B1110023
theorem B740039 : Blo 738327 740039 := bstep (se 1 (by rfl) ⟨555029, by rfl⟩ : syracuseStep 740039 = 1110059) B1110059
theorem B740059 : Blo 738327 740059 := bstep (se 1 (by rfl) ⟨555044, by rfl⟩ : syracuseStep 740059 = 1110089) B1110089
theorem B740135 : Blo 738327 740135 := bstep (se 1 (by rfl) ⟨555101, by rfl⟩ : syracuseStep 740135 = 1110203) B1110203
theorem B740175 : Blo 738327 740175 := bstep (se 1 (by rfl) ⟨555131, by rfl⟩ : syracuseStep 740175 = 1110263) B1110263
theorem B740191 : Blo 738327 740191 := bstep (se 1 (by rfl) ⟨555143, by rfl⟩ : syracuseStep 740191 = 1110287) B1110287
theorem B740219 : Blo 738327 740219 := bstep (se 1 (by rfl) ⟨555164, by rfl⟩ : syracuseStep 740219 = 1110329) B1110329
theorem B740271 : Blo 738327 740271 := bstep (se 1 (by rfl) ⟨555203, by rfl⟩ : syracuseStep 740271 = 1110407) B1110407
theorem B740295 : Blo 738327 740295 := bstep (se 1 (by rfl) ⟨555221, by rfl⟩ : syracuseStep 740295 = 1110443) B1110443
theorem B740315 : Blo 738327 740315 := bstep (se 1 (by rfl) ⟨555236, by rfl⟩ : syracuseStep 740315 = 1110473) B1110473
theorem B740391 : Blo 738327 740391 := bstep (se 1 (by rfl) ⟨555293, by rfl⟩ : syracuseStep 740391 = 1110587) B1110587
theorem B740431 : Blo 738327 740431 := bstep (se 1 (by rfl) ⟨555323, by rfl⟩ : syracuseStep 740431 = 1110647) B1110647
theorem B6016079 : Blo 738327 6016079 := bstep (se 1 (by rfl) ⟨4512059, by rfl⟩ : syracuseStep 6016079 = 9024119) B9024119
theorem B740447 : Blo 738327 740447 := bstep (se 1 (by rfl) ⟨555335, by rfl⟩ : syracuseStep 740447 = 1110671) B1110671
theorem B740475 : Blo 738327 740475 := bstep (se 1 (by rfl) ⟨555356, by rfl⟩ : syracuseStep 740475 = 1110713) B1110713
theorem B740527 : Blo 738327 740527 := bstep (se 1 (by rfl) ⟨555395, by rfl⟩ : syracuseStep 740527 = 1110791) B1110791
theorem B740551 : Blo 738327 740551 := bstep (se 1 (by rfl) ⟨555413, by rfl⟩ : syracuseStep 740551 = 1110827) B1110827
theorem B740571 : Blo 738327 740571 := bstep (se 1 (by rfl) ⟨555428, by rfl⟩ : syracuseStep 740571 = 1110857) B1110857
theorem B740647 : Blo 738327 740647 := bstep (se 1 (by rfl) ⟨555485, by rfl⟩ : syracuseStep 740647 = 1110971) B1110971
theorem B740687 : Blo 738327 740687 := bstep (se 1 (by rfl) ⟨555515, by rfl⟩ : syracuseStep 740687 = 1111031) B1111031
theorem B740703 : Blo 738327 740703 := bstep (se 1 (by rfl) ⟨555527, by rfl⟩ : syracuseStep 740703 = 1111055) B1111055
theorem B740731 : Blo 738327 740731 := bstep (se 1 (by rfl) ⟨555548, by rfl⟩ : syracuseStep 740731 = 1111097) B1111097
theorem B740783 : Blo 738327 740783 := bstep (se 1 (by rfl) ⟨555587, by rfl⟩ : syracuseStep 740783 = 1111175) B1111175
theorem B1330615 : Blo 738327 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B740807 : Blo 738327 740807 := bstep (se 1 (by rfl) ⟨555605, by rfl⟩ : syracuseStep 740807 = 1111211) B1111211
theorem B740827 : Blo 738327 740827 := bstep (se 1 (by rfl) ⟨555620, by rfl⟩ : syracuseStep 740827 = 1111241) B1111241
theorem B3755483 : Blo 738327 3755483 := bstep (se 1 (by rfl) ⟨2816612, by rfl⟩ : syracuseStep 3755483 = 5633225) B5633225
theorem B740903 : Blo 738327 740903 := bstep (se 1 (by rfl) ⟨555677, by rfl⟩ : syracuseStep 740903 = 1111355) B1111355
theorem B740943 : Blo 738327 740943 := bstep (se 1 (by rfl) ⟨555707, by rfl⟩ : syracuseStep 740943 = 1111415) B1111415
theorem B740959 : Blo 738327 740959 := bstep (se 1 (by rfl) ⟨555719, by rfl⟩ : syracuseStep 740959 = 1111439) B1111439
theorem B937595 : Blo 738327 937595 := bstep (se 1 (by rfl) ⟨703196, by rfl⟩ : syracuseStep 937595 = 1406393) B1406393
theorem B740987 : Blo 738327 740987 := bstep (se 1 (by rfl) ⟨555740, by rfl⟩ : syracuseStep 740987 = 1111481) B1111481
theorem B741039 : Blo 738327 741039 := bstep (se 1 (by rfl) ⟨555779, by rfl⟩ : syracuseStep 741039 = 1111559) B1111559
theorem B741063 : Blo 738327 741063 := bstep (se 1 (by rfl) ⟨555797, by rfl⟩ : syracuseStep 741063 = 1111595) B1111595
theorem B5492423 : Blo 738327 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B741083 : Blo 738327 741083 := bstep (se 1 (by rfl) ⟨555812, by rfl⟩ : syracuseStep 741083 = 1111625) B1111625
theorem B741159 : Blo 738327 741159 := bstep (se 1 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 741159 = 1111739) B1111739
theorem B2674505 : Blo 738327 2674505 := bstep (se 2 (by rfl) ⟨1002939, by rfl⟩ : syracuseStep 2674505 = 2005879) B2005879
theorem B741199 : Blo 738327 741199 := bstep (se 1 (by rfl) ⟨555899, by rfl⟩ : syracuseStep 741199 = 1111799) B1111799
theorem B741215 : Blo 738327 741215 := bstep (se 1 (by rfl) ⟨555911, by rfl⟩ : syracuseStep 741215 = 1111823) B1111823
theorem B741243 : Blo 738327 741243 := bstep (se 1 (by rfl) ⟨555932, by rfl⟩ : syracuseStep 741243 = 1111865) B1111865
theorem B741295 : Blo 738327 741295 := bstep (se 1 (by rfl) ⟨555971, by rfl⟩ : syracuseStep 741295 = 1111943) B1111943
theorem B3755969 : Blo 738327 3755969 := bstep (se 2 (by rfl) ⟨1408488, by rfl⟩ : syracuseStep 3755969 = 2816977) B2816977
theorem B741319 : Blo 738327 741319 := bstep (se 1 (by rfl) ⟨555989, by rfl⟩ : syracuseStep 741319 = 1111979) B1111979
theorem B741339 : Blo 738327 741339 := bstep (se 1 (by rfl) ⟨556004, by rfl⟩ : syracuseStep 741339 = 1112009) B1112009
theorem B741415 : Blo 738327 741415 := bstep (se 1 (by rfl) ⟨556061, by rfl⟩ : syracuseStep 741415 = 1112123) B1112123
theorem B3002447 : Blo 738327 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B741455 : Blo 738327 741455 := bstep (se 1 (by rfl) ⟨556091, by rfl⟩ : syracuseStep 741455 = 1112183) B1112183
theorem B741471 : Blo 738327 741471 := bstep (se 1 (by rfl) ⟨556103, by rfl⟩ : syracuseStep 741471 = 1112207) B1112207
theorem B741499 : Blo 738327 741499 := bstep (se 1 (by rfl) ⟨556124, by rfl⟩ : syracuseStep 741499 = 1112249) B1112249
theorem B741551 : Blo 738327 741551 := bstep (se 1 (by rfl) ⟨556163, by rfl⟩ : syracuseStep 741551 = 1112327) B1112327
theorem B741575 : Blo 738327 741575 := bstep (se 1 (by rfl) ⟨556181, by rfl⟩ : syracuseStep 741575 = 1112363) B1112363
theorem B741595 : Blo 738327 741595 := bstep (se 1 (by rfl) ⟨556196, by rfl⟩ : syracuseStep 741595 = 1112393) B1112393
theorem B741671 : Blo 738327 741671 := bstep (se 1 (by rfl) ⟨556253, by rfl⟩ : syracuseStep 741671 = 1112507) B1112507
theorem B8540477 : Blo 738327 8540477 := bstep (se 3 (by rfl) ⟨1601339, by rfl⟩ : syracuseStep 8540477 = 3202679) B3202679
theorem B741711 : Blo 738327 741711 := bstep (se 1 (by rfl) ⟨556283, by rfl⟩ : syracuseStep 741711 = 1112567) B1112567
theorem B2806103 : Blo 738327 2806103 := bstep (se 1 (by rfl) ⟨2104577, by rfl⟩ : syracuseStep 2806103 = 4209155) B4209155
theorem B741727 : Blo 738327 741727 := bstep (se 1 (by rfl) ⟨556295, by rfl⟩ : syracuseStep 741727 = 1112591) B1112591
theorem B741755 : Blo 738327 741755 := bstep (se 1 (by rfl) ⟨556316, by rfl⟩ : syracuseStep 741755 = 1112633) B1112633
theorem B741807 : Blo 738327 741807 := bstep (se 1 (by rfl) ⟨556355, by rfl⟩ : syracuseStep 741807 = 1112711) B1112711
theorem B741831 : Blo 738327 741831 := bstep (se 1 (by rfl) ⟨556373, by rfl⟩ : syracuseStep 741831 = 1112747) B1112747
theorem B741851 : Blo 738327 741851 := bstep (se 1 (by rfl) ⟨556388, by rfl⟩ : syracuseStep 741851 = 1112777) B1112777
theorem B7131671 : Blo 738327 7131671 := bstep (se 1 (by rfl) ⟨5348753, by rfl⟩ : syracuseStep 7131671 = 10697507) B10697507
theorem B741927 : Blo 738327 741927 := bstep (se 1 (by rfl) ⟨556445, by rfl⟩ : syracuseStep 741927 = 1112891) B1112891
theorem B741967 : Blo 738327 741967 := bstep (se 1 (by rfl) ⟨556475, by rfl⟩ : syracuseStep 741967 = 1112951) B1112951
theorem B741983 : Blo 738327 741983 := bstep (se 1 (by rfl) ⟨556487, by rfl⟩ : syracuseStep 741983 = 1112975) B1112975
theorem B742011 : Blo 738327 742011 := bstep (se 1 (by rfl) ⟨556508, by rfl⟩ : syracuseStep 742011 = 1113017) B1113017
theorem B742063 : Blo 738327 742063 := bstep (se 1 (by rfl) ⟨556547, by rfl⟩ : syracuseStep 742063 = 1113095) B1113095
theorem B742087 : Blo 738327 742087 := bstep (se 1 (by rfl) ⟨556565, by rfl⟩ : syracuseStep 742087 = 1113131) B1113131
theorem B6410963 : Blo 738327 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B742107 : Blo 738327 742107 := bstep (se 1 (by rfl) ⟨556580, by rfl⟩ : syracuseStep 742107 = 1113161) B1113161
theorem B742183 : Blo 738327 742183 := bstep (se 1 (by rfl) ⟨556637, by rfl⟩ : syracuseStep 742183 = 1113275) B1113275
theorem B742223 : Blo 738327 742223 := bstep (se 1 (by rfl) ⟨556667, by rfl⟩ : syracuseStep 742223 = 1113335) B1113335
theorem B742239 : Blo 738327 742239 := bstep (se 1 (by rfl) ⟨556679, by rfl⟩ : syracuseStep 742239 = 1113359) B1113359
theorem B2741111 : Blo 738327 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B742267 : Blo 738327 742267 := bstep (se 1 (by rfl) ⟨556700, by rfl⟩ : syracuseStep 742267 = 1113401) B1113401
theorem B742319 : Blo 738327 742319 := bstep (se 1 (by rfl) ⟨556739, by rfl⟩ : syracuseStep 742319 = 1113479) B1113479
theorem B23123009 : Blo 738327 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B4281623 : Blo 738327 4281623 := bstep (se 1 (by rfl) ⟨3211217, by rfl⟩ : syracuseStep 4281623 = 6422435) B6422435
theorem B1332755 : Blo 738327 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B6019001 : Blo 738327 6019001 := bstep (se 2 (by rfl) ⟨2257125, by rfl⟩ : syracuseStep 6019001 = 4514251) B4514251
theorem B3004573 : Blo 738327 3004573 := bstep (se 3 (by rfl) ⟨563357, by rfl⟩ : syracuseStep 3004573 = 1126715) B1126715
theorem B3004733 : Blo 738327 3004733 := bstep (se 3 (by rfl) ⟨563387, by rfl⟩ : syracuseStep 3004733 = 1126775) B1126775
theorem B1661327 : Blo 738327 1661327 := bstep (se 1 (by rfl) ⟨1245995, by rfl⟩ : syracuseStep 1661327 = 2491991) B2491991
theorem B5134871 : Blo 738327 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B3168827 : Blo 738327 3168827 := bstep (se 1 (by rfl) ⟨2376620, by rfl⟩ : syracuseStep 3168827 = 4753241) B4753241
theorem B1661651 : Blo 738327 1661651 := bstep (se 1 (by rfl) ⟨1246238, by rfl⟩ : syracuseStep 1661651 = 2492477) B2492477
theorem B4217629 : Blo 738327 4217629 := bstep (se 3 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 4217629 = 1581611) B1581611
theorem B2808989 : Blo 738327 2808989 := bstep (se 3 (by rfl) ⟨526685, by rfl⟩ : syracuseStep 2808989 = 1053371) B1053371
theorem B8412659 : Blo 738327 8412659 := bstep (se 1 (by rfl) ⟨6309494, by rfl⟩ : syracuseStep 8412659 = 12618989) B12618989
theorem B1662587 : Blo 738327 1662587 := bstep (se 1 (by rfl) ⟨1246940, by rfl⟩ : syracuseStep 1662587 = 2493881) B2493881
theorem B1662713 : Blo 738327 1662713 := bstep (se 2 (by rfl) ⟨623517, by rfl⟩ : syracuseStep 1662713 = 1247035) B1247035
theorem B2809673 : Blo 738327 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B1335113 : Blo 738327 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B1662983 : Blo 738327 1662983 := bstep (se 1 (by rfl) ⟨1247237, by rfl⟩ : syracuseStep 1662983 = 2494475) B2494475
theorem B1663055 : Blo 738327 1663055 := bstep (se 1 (by rfl) ⟨1247291, by rfl⟩ : syracuseStep 1663055 = 2494583) B2494583
theorem B3792977 : Blo 738327 3792977 := bstep (se 2 (by rfl) ⟨1422366, by rfl⟩ : syracuseStep 3792977 = 2844733) B2844733
theorem B14246117 : Blo 738327 14246117 := bstep (se 4 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 14246117 = 2671147) B2671147
theorem B4514059 : Blo 738327 4514059 := bstep (se 1 (by rfl) ⟨3385544, by rfl⟩ : syracuseStep 4514059 = 6771089) B6771089
theorem B2810173 : Blo 738327 2810173 := bstep (se 3 (by rfl) ⟨526907, by rfl⟩ : syracuseStep 2810173 = 1053815) B1053815
theorem B1663451 : Blo 738327 1663451 := bstep (se 1 (by rfl) ⟨1247588, by rfl⟩ : syracuseStep 1663451 = 2495177) B2495177
theorem B1335827 : Blo 738327 1335827 := bstep (se 1 (by rfl) ⟨1001870, by rfl⟩ : syracuseStep 1335827 = 2003741) B2003741
theorem B35971913 : Blo 738327 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B1401761 : Blo 738327 1401761 := bstep (se 2 (by rfl) ⟨525660, by rfl⟩ : syracuseStep 1401761 = 1051321) B1051321
theorem B1663919 : Blo 738327 1663919 := bstep (se 1 (by rfl) ⟨1247939, by rfl⟩ : syracuseStep 1663919 = 2495879) B2495879
theorem B4744271 : Blo 738327 4744271 := bstep (se 1 (by rfl) ⟨3558203, by rfl⟩ : syracuseStep 4744271 = 7116407) B7116407
theorem B3564623 : Blo 738327 3564623 := bstep (se 1 (by rfl) ⟨2673467, by rfl⟩ : syracuseStep 3564623 = 5346935) B5346935
theorem B1664171 : Blo 738327 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B1402103 : Blo 738327 1402103 := bstep (se 1 (by rfl) ⟨1051577, by rfl⟩ : syracuseStep 1402103 = 2103155) B2103155
theorem B1500599 : Blo 738327 1500599 := bstep (se 1 (by rfl) ⟨1125449, by rfl⟩ : syracuseStep 1500599 = 2250899) B2250899
theorem B3007945 : Blo 738327 3007945 := bstep (se 2 (by rfl) ⟨1127979, by rfl⟩ : syracuseStep 3007945 = 2255959) B2255959
theorem B2025083 : Blo 738327 2025083 := bstep (se 1 (by rfl) ⟨1518812, by rfl⟩ : syracuseStep 2025083 = 3037625) B3037625
theorem B1664711 : Blo 738327 1664711 := bstep (se 1 (by rfl) ⟨1248533, by rfl⟩ : syracuseStep 1664711 = 2497067) B2497067
theorem B1337195 : Blo 738327 1337195 := bstep (se 1 (by rfl) ⟨1002896, by rfl⟩ : syracuseStep 1337195 = 2005793) B2005793
theorem B1107887 : Blo 738327 1107887 := bstep (se 1 (by rfl) ⟨830915, by rfl⟩ : syracuseStep 1107887 = 1661831) B1661831
theorem B1599419 : Blo 738327 1599419 := bstep (se 1 (by rfl) ⟨1199564, by rfl⟩ : syracuseStep 1599419 = 2399129) B2399129
theorem B23128001 : Blo 738327 23128001 := bstep (se 2 (by rfl) ⟨8673000, by rfl⟩ : syracuseStep 23128001 = 17346001) B17346001
theorem B2811905 : Blo 738327 2811905 := bstep (se 2 (by rfl) ⟨1054464, by rfl⟩ : syracuseStep 2811905 = 2108929) B2108929
theorem B1107977 : Blo 738327 1107977 := bstep (se 2 (by rfl) ⟨415491, by rfl⟩ : syracuseStep 1107977 = 830983) B830983
theorem B1108007 : Blo 738327 1108007 := bstep (se 1 (by rfl) ⟨831005, by rfl⟩ : syracuseStep 1108007 = 1662011) B1662011
theorem B1108091 : Blo 738327 1108091 := bstep (se 1 (by rfl) ⟨831068, by rfl⟩ : syracuseStep 1108091 = 1662137) B1662137
theorem B3205277 : Blo 738327 3205277 := bstep (se 3 (by rfl) ⟨600989, by rfl⟩ : syracuseStep 3205277 = 1201979) B1201979
theorem B1108217 : Blo 738327 1108217 := bstep (se 2 (by rfl) ⟨415581, by rfl⟩ : syracuseStep 1108217 = 831163) B831163
theorem B8415575 : Blo 738327 8415575 := bstep (se 1 (by rfl) ⟨6311681, by rfl⟩ : syracuseStep 8415575 = 12623363) B12623363
theorem B1108319 : Blo 738327 1108319 := bstep (se 1 (by rfl) ⟨831239, by rfl⟩ : syracuseStep 1108319 = 1662479) B1662479
theorem B1108331 : Blo 738327 1108331 := bstep (se 1 (by rfl) ⟨831248, by rfl⟩ : syracuseStep 1108331 = 1662497) B1662497
theorem B1403401 : Blo 738327 1403401 := bstep (se 2 (by rfl) ⟨526275, by rfl⟩ : syracuseStep 1403401 = 1052551) B1052551
theorem B1665575 : Blo 738327 1665575 := bstep (se 1 (by rfl) ⟨1249181, by rfl⟩ : syracuseStep 1665575 = 2498363) B2498363
theorem B1108559 : Blo 738327 1108559 := bstep (se 1 (by rfl) ⟨831419, by rfl⟩ : syracuseStep 1108559 = 1662839) B1662839
theorem B1108679 : Blo 738327 1108679 := bstep (se 1 (by rfl) ⟨831509, by rfl⟩ : syracuseStep 1108679 = 1663019) B1663019
theorem B18017099 : Blo 738327 18017099 := bstep (se 1 (by rfl) ⟨13512824, by rfl⟩ : syracuseStep 18017099 = 27025649) B27025649
theorem B1403743 : Blo 738327 1403743 := bstep (se 1 (by rfl) ⟨1052807, by rfl⟩ : syracuseStep 1403743 = 2105615) B2105615
theorem B1108841 : Blo 738327 1108841 := bstep (se 2 (by rfl) ⟨415815, by rfl⟩ : syracuseStep 1108841 = 831631) B831631
theorem B1665899 : Blo 738327 1665899 := bstep (se 1 (by rfl) ⟨1249424, by rfl⟩ : syracuseStep 1665899 = 2498849) B2498849
theorem B1665953 : Blo 738327 1665953 := bstep (se 2 (by rfl) ⟨624732, by rfl⟩ : syracuseStep 1665953 = 1249465) B1249465
theorem B1108919 : Blo 738327 1108919 := bstep (se 1 (by rfl) ⟨831689, by rfl⟩ : syracuseStep 1108919 = 1663379) B1663379
theorem B1108955 : Blo 738327 1108955 := bstep (se 1 (by rfl) ⟨831716, by rfl⟩ : syracuseStep 1108955 = 1663433) B1663433
theorem B4222003 : Blo 738327 4222003 := bstep (se 1 (by rfl) ⟨3166502, by rfl⟩ : syracuseStep 4222003 = 6333005) B6333005
theorem B1666295 : Blo 738327 1666295 := bstep (se 1 (by rfl) ⟨1249721, by rfl⟩ : syracuseStep 1666295 = 2499443) B2499443
theorem B2256119 : Blo 738327 2256119 := bstep (se 1 (by rfl) ⟨1692089, by rfl⟩ : syracuseStep 2256119 = 3384179) B3384179
theorem B40496429 : Blo 738327 40496429 := bstep (se 3 (by rfl) ⟨7593080, by rfl⟩ : syracuseStep 40496429 = 15186161) B15186161
theorem B5074319 : Blo 738327 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1109423 : Blo 738327 1109423 := bstep (se 1 (by rfl) ⟨832067, by rfl⟩ : syracuseStep 1109423 = 1664135) B1664135
theorem B1109513 : Blo 738327 1109513 := bstep (se 2 (by rfl) ⟨416067, by rfl⟩ : syracuseStep 1109513 = 832135) B832135
theorem B1109543 : Blo 738327 1109543 := bstep (se 1 (by rfl) ⟨832157, by rfl⟩ : syracuseStep 1109543 = 1664315) B1664315
theorem B1109627 : Blo 738327 1109627 := bstep (se 1 (by rfl) ⟨832220, by rfl⟩ : syracuseStep 1109627 = 1664441) B1664441
theorem B2813575 : Blo 738327 2813575 := bstep (se 1 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 2813575 = 4220363) B4220363
theorem B1109753 : Blo 738327 1109753 := bstep (se 2 (by rfl) ⟨416157, by rfl⟩ : syracuseStep 1109753 = 832315) B832315
theorem B9498383 : Blo 738327 9498383 := bstep (se 1 (by rfl) ⟨7123787, by rfl⟩ : syracuseStep 9498383 = 14247575) B14247575
theorem B8548129 : Blo 738327 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B1666889 : Blo 738327 1666889 := bstep (se 2 (by rfl) ⟨625083, by rfl⟩ : syracuseStep 1666889 = 1250167) B1250167
theorem B1109855 : Blo 738327 1109855 := bstep (se 1 (by rfl) ⟨832391, by rfl⟩ : syracuseStep 1109855 = 1664783) B1664783
theorem B1109867 : Blo 738327 1109867 := bstep (se 1 (by rfl) ⟨832400, by rfl⟩ : syracuseStep 1109867 = 1664801) B1664801
theorem B2813879 : Blo 738327 2813879 := bstep (se 1 (by rfl) ⟨2110409, by rfl⟩ : syracuseStep 2813879 = 4220819) B4220819
theorem B4747193 : Blo 738327 4747193 := bstep (se 2 (by rfl) ⟨1780197, by rfl⟩ : syracuseStep 4747193 = 3560395) B3560395
theorem B1404859 : Blo 738327 1404859 := bstep (se 1 (by rfl) ⟨1053644, by rfl⟩ : syracuseStep 1404859 = 2107289) B2107289
theorem B1404935 : Blo 738327 1404935 := bstep (se 1 (by rfl) ⟨1053701, by rfl⟩ : syracuseStep 1404935 = 2107403) B2107403
theorem B10678301 : Blo 738327 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B1110095 : Blo 738327 1110095 := bstep (se 1 (by rfl) ⟨832571, by rfl⟩ : syracuseStep 1110095 = 1665143) B1665143
theorem B1110215 : Blo 738327 1110215 := bstep (se 1 (by rfl) ⟨832661, by rfl⟩ : syracuseStep 1110215 = 1665323) B1665323
theorem B1110377 : Blo 738327 1110377 := bstep (se 2 (by rfl) ⟨416391, by rfl⟩ : syracuseStep 1110377 = 832783) B832783
theorem B1503631 : Blo 738327 1503631 := bstep (se 1 (by rfl) ⟨1127723, by rfl⟩ : syracuseStep 1503631 = 2255447) B2255447
theorem B1405345 : Blo 738327 1405345 := bstep (se 2 (by rfl) ⟨527004, by rfl⟩ : syracuseStep 1405345 = 1054009) B1054009
theorem B1110455 : Blo 738327 1110455 := bstep (se 1 (by rfl) ⟨832841, by rfl⟩ : syracuseStep 1110455 = 1665683) B1665683
theorem B1110491 : Blo 738327 1110491 := bstep (se 1 (by rfl) ⟨832868, by rfl⟩ : syracuseStep 1110491 = 1665737) B1665737
theorem B1667681 : Blo 738327 1667681 := bstep (se 2 (by rfl) ⟨625380, by rfl⟩ : syracuseStep 1667681 = 1250761) B1250761
theorem B1405687 : Blo 738327 1405687 := bstep (se 1 (by rfl) ⟨1054265, by rfl⟩ : syracuseStep 1405687 = 2108531) B2108531
theorem B1110959 : Blo 738327 1110959 := bstep (se 1 (by rfl) ⟨833219, by rfl⟩ : syracuseStep 1110959 = 1666439) B1666439
theorem B1668023 : Blo 738327 1668023 := bstep (se 1 (by rfl) ⟨1251017, by rfl⟩ : syracuseStep 1668023 = 2502035) B2502035
theorem B1111049 : Blo 738327 1111049 := bstep (se 2 (by rfl) ⟨416643, by rfl⟩ : syracuseStep 1111049 = 833287) B833287
theorem B1405991 : Blo 738327 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B1111079 : Blo 738327 1111079 := bstep (se 1 (by rfl) ⟨833309, by rfl⟩ : syracuseStep 1111079 = 1666619) B1666619
theorem B2815033 : Blo 738327 2815033 := bstep (se 2 (by rfl) ⟨1055637, by rfl⟩ : syracuseStep 2815033 = 2111275) B2111275
theorem B1111163 : Blo 738327 1111163 := bstep (se 1 (by rfl) ⟨833372, by rfl⟩ : syracuseStep 1111163 = 1666745) B1666745
theorem B1111289 : Blo 738327 1111289 := bstep (se 2 (by rfl) ⟨416733, by rfl⟩ : syracuseStep 1111289 = 833467) B833467
theorem B1111391 : Blo 738327 1111391 := bstep (se 1 (by rfl) ⟨833543, by rfl⟩ : syracuseStep 1111391 = 1667087) B1667087
theorem B2815337 : Blo 738327 2815337 := bstep (se 2 (by rfl) ⟨1055751, by rfl⟩ : syracuseStep 2815337 = 2111503) B2111503
theorem B1111403 : Blo 738327 1111403 := bstep (se 1 (by rfl) ⟨833552, by rfl⟩ : syracuseStep 1111403 = 1667105) B1667105
theorem B6321523 : Blo 738327 6321523 := bstep (se 1 (by rfl) ⟨4741142, by rfl⟩ : syracuseStep 6321523 = 9482285) B9482285
theorem B1668617 : Blo 738327 1668617 := bstep (se 2 (by rfl) ⟨625731, by rfl⟩ : syracuseStep 1668617 = 1251463) B1251463
theorem B1111631 : Blo 738327 1111631 := bstep (se 1 (by rfl) ⟨833723, by rfl⟩ : syracuseStep 1111631 = 1667447) B1667447
theorem B1111751 : Blo 738327 1111751 := bstep (se 1 (by rfl) ⟨833813, by rfl⟩ : syracuseStep 1111751 = 1667627) B1667627
theorem B5994283 : Blo 738327 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B1668959 : Blo 738327 1668959 := bstep (se 1 (by rfl) ⟨1251719, by rfl⟩ : syracuseStep 1668959 = 2503439) B2503439
theorem B1111913 : Blo 738327 1111913 := bstep (se 2 (by rfl) ⟨416967, by rfl⟩ : syracuseStep 1111913 = 833935) B833935
theorem B1111991 : Blo 738327 1111991 := bstep (se 1 (by rfl) ⟨833993, by rfl⟩ : syracuseStep 1111991 = 1667987) B1667987
theorem B1112027 : Blo 738327 1112027 := bstep (se 1 (by rfl) ⟨834020, by rfl⟩ : syracuseStep 1112027 = 1668041) B1668041
theorem B1669139 : Blo 738327 1669139 := bstep (se 1 (by rfl) ⟨1251854, by rfl⟩ : syracuseStep 1669139 = 2503709) B2503709
theorem B6322481 : Blo 738327 6322481 := bstep (se 2 (by rfl) ⟨2370930, by rfl⟩ : syracuseStep 6322481 = 4741861) B4741861
theorem B1669481 : Blo 738327 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B1112495 : Blo 738327 1112495 := bstep (se 1 (by rfl) ⟨834371, by rfl⟩ : syracuseStep 1112495 = 1668743) B1668743
theorem B1112585 : Blo 738327 1112585 := bstep (se 2 (by rfl) ⟨417219, by rfl⟩ : syracuseStep 1112585 = 834439) B834439
theorem B1112615 : Blo 738327 1112615 := bstep (se 1 (by rfl) ⟨834461, by rfl⟩ : syracuseStep 1112615 = 1668923) B1668923
theorem B1112699 : Blo 738327 1112699 := bstep (se 1 (by rfl) ⟨834524, by rfl⟩ : syracuseStep 1112699 = 1669049) B1669049
theorem B5339783 : Blo 738327 5339783 := bstep (se 1 (by rfl) ⟨4004837, by rfl⟩ : syracuseStep 5339783 = 8009675) B8009675
theorem B1112825 : Blo 738327 1112825 := bstep (se 2 (by rfl) ⟨417309, by rfl⟩ : syracuseStep 1112825 = 834619) B834619
theorem B1112927 : Blo 738327 1112927 := bstep (se 1 (by rfl) ⟨834695, by rfl⟩ : syracuseStep 1112927 = 1669391) B1669391
theorem B1407851 : Blo 738327 1407851 := bstep (se 1 (by rfl) ⟨1055888, by rfl⟩ : syracuseStep 1407851 = 2111777) B2111777
theorem B1112939 : Blo 738327 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B1670075 : Blo 738327 1670075 := bstep (se 1 (by rfl) ⟨1252556, by rfl⟩ : syracuseStep 1670075 = 2505113) B2505113
theorem B1670201 : Blo 738327 1670201 := bstep (se 2 (by rfl) ⟨626325, by rfl⟩ : syracuseStep 1670201 = 1252651) B1252651
theorem B1408079 : Blo 738327 1408079 := bstep (se 1 (by rfl) ⟨1056059, by rfl⟩ : syracuseStep 1408079 = 2112119) B2112119
theorem B1113167 : Blo 738327 1113167 := bstep (se 1 (by rfl) ⟨834875, by rfl⟩ : syracuseStep 1113167 = 1669751) B1669751
theorem B1113287 : Blo 738327 1113287 := bstep (se 1 (by rfl) ⟨834965, by rfl⟩ : syracuseStep 1113287 = 1669931) B1669931
theorem B1113449 : Blo 738327 1113449 := bstep (se 2 (by rfl) ⟨417543, by rfl⟩ : syracuseStep 1113449 = 835087) B835087
theorem B4750757 : Blo 738327 4750757 := bstep (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) B890767
theorem B1899995 : Blo 738327 1899995 := bstep (se 1 (by rfl) ⟨1424996, by rfl⟩ : syracuseStep 1899995 = 2849993) B2849993
theorem B1408519 : Blo 738327 1408519 := bstep (se 1 (by rfl) ⟨1056389, by rfl⟩ : syracuseStep 1408519 = 2112779) B2112779
theorem B5996231 : Blo 738327 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B1441631 : Blo 738327 1441631 := bstep (se 1 (by rfl) ⟨1081223, by rfl⟩ : syracuseStep 1441631 = 2162447) B2162447
theorem B21364667 : Blo 738327 21364667 := bstep (se 1 (by rfl) ⟨16023500, by rfl⟩ : syracuseStep 21364667 = 32047001) B32047001
theorem B62357521 : Blo 738327 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B1802569 : Blo 738327 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B21300083 : Blo 738327 21300083 := bstep (se 1 (by rfl) ⟨15975062, by rfl⟩ : syracuseStep 21300083 = 31950125) B31950125
theorem B10945475 : Blo 738327 10945475 := bstep (se 1 (by rfl) ⟨8209106, by rfl⟩ : syracuseStep 10945475 = 16418213) B16418213
theorem B27362447 : Blo 738327 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B1246441 : Blo 738327 1246441 := bstep (se 2 (by rfl) ⟨467415, by rfl⟩ : syracuseStep 1246441 = 934831) B934831
theorem B1246495 : Blo 738327 1246495 := bstep (se 1 (by rfl) ⟨934871, by rfl⟩ : syracuseStep 1246495 = 1869743) B1869743
theorem B1869095 : Blo 738327 1869095 := bstep (se 1 (by rfl) ⟨1401821, by rfl⟩ : syracuseStep 1869095 = 2803643) B2803643
theorem B5768491 : Blo 738327 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B1246907 : Blo 738327 1246907 := bstep (se 1 (by rfl) ⟨935180, by rfl⟩ : syracuseStep 1246907 = 1870361) B1870361
theorem B15992711 : Blo 738327 15992711 := bstep (se 1 (by rfl) ⟨11994533, by rfl⟩ : syracuseStep 15992711 = 23989067) B23989067
theorem B2492855 : Blo 738327 2492855 := bstep (se 1 (by rfl) ⟨1869641, by rfl⟩ : syracuseStep 2492855 = 3739283) B3739283
theorem B788935 : Blo 738327 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B1870735 : Blo 738327 1870735 := bstep (se 1 (by rfl) ⟨1403051, by rfl⟩ : syracuseStep 1870735 = 2806103) B2806103
theorem B4754447 : Blo 738327 4754447 := bstep (se 1 (by rfl) ⟨3565835, by rfl⟩ : syracuseStep 4754447 = 7131671) B7131671
theorem B1871201 : Blo 738327 1871201 := bstep (se 2 (by rfl) ⟨701700, by rfl⟩ : syracuseStep 1871201 = 1403401) B1403401
theorem B1248635 : Blo 738327 1248635 := bstep (se 1 (by rfl) ⟨936476, by rfl⟩ : syracuseStep 1248635 = 1872953) B1872953
theorem B2854415 : Blo 738327 2854415 := bstep (se 1 (by rfl) ⟨2140811, by rfl⟩ : syracuseStep 2854415 = 4281623) B4281623
theorem B888503 : Blo 738327 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B1871657 : Blo 738327 1871657 := bstep (se 2 (by rfl) ⟨701871, by rfl⟩ : syracuseStep 1871657 = 1403743) B1403743
theorem B1052471 : Blo 738327 1052471 := bstep (se 1 (by rfl) ⟨789353, by rfl⟩ : syracuseStep 1052471 = 1578707) B1578707
theorem B3805289 : Blo 738327 3805289 := bstep (se 2 (by rfl) ⟨1426983, by rfl⟩ : syracuseStep 3805289 = 2853967) B2853967
theorem B790823 : Blo 738327 790823 := bstep (se 1 (by rfl) ⟨593117, by rfl⟩ : syracuseStep 790823 = 1186235) B1186235
theorem B1249627 : Blo 738327 1249627 := bstep (se 1 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 1249627 = 1874441) B1874441
theorem B1577323 : Blo 738327 1577323 := bstep (se 1 (by rfl) ⟨1182992, by rfl⟩ : syracuseStep 1577323 = 2365985) B2365985
theorem B1774153 : Blo 738327 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B1184377 : Blo 738327 1184377 := bstep (se 2 (by rfl) ⟨444141, by rfl⟩ : syracuseStep 1184377 = 888283) B888283
theorem B1577647 : Blo 738327 1577647 := bstep (se 1 (by rfl) ⟨1183235, by rfl⟩ : syracuseStep 1577647 = 2366471) B2366471
theorem B1872659 : Blo 738327 1872659 := bstep (se 1 (by rfl) ⟨1404494, by rfl⟩ : syracuseStep 1872659 = 2808989) B2808989
theorem B5608439 : Blo 738327 5608439 := bstep (se 1 (by rfl) ⟨4206329, by rfl⟩ : syracuseStep 5608439 = 8412659) B8412659
theorem B1873115 : Blo 738327 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B890075 : Blo 738327 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B1053929 : Blo 738327 1053929 := bstep (se 2 (by rfl) ⟨395223, by rfl⟩ : syracuseStep 1053929 = 790447) B790447
theorem B1873145 : Blo 738327 1873145 := bstep (se 2 (by rfl) ⟨702429, by rfl⟩ : syracuseStep 1873145 = 1404859) B1404859
theorem B1250599 : Blo 738327 1250599 := bstep (se 1 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 1250599 = 1875899) B1875899
theorem B791899 : Blo 738327 791899 := bstep (se 1 (by rfl) ⟨593924, by rfl⟩ : syracuseStep 791899 = 1187849) B1187849
theorem B2528651 : Blo 738327 2528651 := bstep (se 1 (by rfl) ⟨1896488, by rfl⟩ : syracuseStep 2528651 = 3792977) B3792977
theorem B2495933 : Blo 738327 2495933 := bstep (se 3 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 2495933 = 935975) B935975
theorem B1775047 : Blo 738327 1775047 := bstep (se 1 (by rfl) ⟨1331285, by rfl⟩ : syracuseStep 1775047 = 2662571) B2662571
theorem B1709561 : Blo 738327 1709561 := bstep (se 2 (by rfl) ⟨641085, by rfl⟩ : syracuseStep 1709561 = 1282171) B1282171
theorem B890551 : Blo 738327 890551 := bstep (se 1 (by rfl) ⟨667913, by rfl⟩ : syracuseStep 890551 = 1335827) B1335827
theorem B1251119 : Blo 738327 1251119 := bstep (se 1 (by rfl) ⟨938339, by rfl⟩ : syracuseStep 1251119 = 1876679) B1876679
theorem B2496311 : Blo 738327 2496311 := bstep (se 1 (by rfl) ⟨1872233, by rfl⟩ : syracuseStep 2496311 = 3744467) B3744467
theorem B1578809 : Blo 738327 1578809 := bstep (se 2 (by rfl) ⟨592053, by rfl⟩ : syracuseStep 1578809 = 1184107) B1184107
theorem B2004841 : Blo 738327 2004841 := bstep (se 2 (by rfl) ⟨751815, by rfl⟩ : syracuseStep 2004841 = 1503631) B1503631
theorem B1873793 : Blo 738327 1873793 := bstep (se 2 (by rfl) ⟨702672, by rfl⟩ : syracuseStep 1873793 = 1405345) B1405345
theorem B2496797 : Blo 738327 2496797 := bstep (se 3 (by rfl) ⟨468149, by rfl⟩ : syracuseStep 2496797 = 936299) B936299
theorem B1874249 : Blo 738327 1874249 := bstep (se 2 (by rfl) ⟨702843, by rfl⟩ : syracuseStep 1874249 = 1405687) B1405687
theorem B1644907 : Blo 738327 1644907 := bstep (se 1 (by rfl) ⟨1233680, by rfl⟩ : syracuseStep 1644907 = 2467361) B2467361
theorem B1350055 : Blo 738327 1350055 := bstep (se 1 (by rfl) ⟨1012541, by rfl⟩ : syracuseStep 1350055 = 2025083) B2025083
theorem B2103803 : Blo 738327 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B1874603 : Blo 738327 1874603 := bstep (se 1 (by rfl) ⟨1405952, by rfl⟩ : syracuseStep 1874603 = 2811905) B2811905
theorem B2136851 : Blo 738327 2136851 := bstep (se 1 (by rfl) ⟨1602638, by rfl⟩ : syracuseStep 2136851 = 3205277) B3205277
theorem B5610383 : Blo 738327 5610383 := bstep (se 1 (by rfl) ⟨4207787, by rfl⟩ : syracuseStep 5610383 = 8415575) B8415575
theorem B1252327 : Blo 738327 1252327 := bstep (se 1 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 1252327 = 1878491) B1878491
theorem B8428697 : Blo 738327 8428697 := bstep (se 2 (by rfl) ⟨3160761, by rfl⟩ : syracuseStep 8428697 = 6321523) B6321523
theorem B2497823 : Blo 738327 2497823 := bstep (se 1 (by rfl) ⟨1873367, by rfl⟩ : syracuseStep 2497823 = 3746735) B3746735
theorem B3382879 : Blo 738327 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B3743495 : Blo 738327 3743495 := bstep (se 1 (by rfl) ⟨2807621, by rfl⟩ : syracuseStep 3743495 = 5615243) B5615243
theorem B6332255 : Blo 738327 6332255 := bstep (se 1 (by rfl) ⟨4749191, by rfl⟩ : syracuseStep 6332255 = 9498383) B9498383
theorem B40607669 : Blo 738327 40607669 := bstep (se 5 (by rfl) ⟨1903484, by rfl⟩ : syracuseStep 40607669 = 3806969) B3806969
theorem B1875919 : Blo 738327 1875919 := bstep (se 1 (by rfl) ⟨1406939, by rfl⟩ : syracuseStep 1875919 = 2813879) B2813879
theorem B7118867 : Blo 738327 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B4006097 : Blo 738327 4006097 := bstep (se 2 (by rfl) ⟨1502286, by rfl⟩ : syracuseStep 4006097 = 3004573) B3004573
theorem B1876891 : Blo 738327 1876891 := bstep (se 1 (by rfl) ⟨1407668, by rfl⟩ : syracuseStep 1876891 = 2815337) B2815337
theorem B2368727 : Blo 738327 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B2106719 : Blo 738327 2106719 := bstep (se 1 (by rfl) ⟨1580039, by rfl⟩ : syracuseStep 2106719 = 3160079) B3160079
theorem B6956441 : Blo 738327 6956441 := bstep (se 2 (by rfl) ⟨2608665, by rfl⟩ : syracuseStep 6956441 = 5217331) B5217331
theorem B2500253 : Blo 738327 2500253 := bstep (se 3 (by rfl) ⟨468797, by rfl⟩ : syracuseStep 2500253 = 937595) B937595
theorem B1878025 : Blo 738327 1878025 := bstep (se 2 (by rfl) ⟨704259, by rfl⟩ : syracuseStep 1878025 = 1408519) B1408519
theorem B3156047 : Blo 738327 3156047 := bstep (se 1 (by rfl) ⟨2367035, by rfl⟩ : syracuseStep 3156047 = 4734071) B4734071
theorem B2500793 : Blo 738327 2500793 := bstep (se 2 (by rfl) ⟨937797, by rfl⟩ : syracuseStep 2500793 = 1875595) B1875595
theorem B1583543 : Blo 738327 1583543 := bstep (se 1 (by rfl) ⟨1187657, by rfl⟩ : syracuseStep 1583543 = 2375315) B2375315
theorem B961087 : Blo 738327 961087 := bstep (se 1 (by rfl) ⟨720815, by rfl⟩ : syracuseStep 961087 = 1441631) B1441631
theorem B3746411 : Blo 738327 3746411 := bstep (se 1 (by rfl) ⟨2809808, by rfl⟩ : syracuseStep 3746411 = 5619617) B5619617
theorem B6761083 : Blo 738327 6761083 := bstep (se 1 (by rfl) ⟨5070812, by rfl⟩ : syracuseStep 6761083 = 10141625) B10141625
theorem B8006525 : Blo 738327 8006525 := bstep (se 3 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 8006525 = 3002447) B3002447
theorem B1780775 : Blo 738327 1780775 := bstep (se 1 (by rfl) ⟨1335581, by rfl⟩ : syracuseStep 1780775 = 2671163) B2671163
theorem B3746897 : Blo 738327 3746897 := bstep (se 2 (by rfl) ⟨1405086, by rfl⟩ : syracuseStep 3746897 = 2810173) B2810173
theorem B6335603 : Blo 738327 6335603 := bstep (se 1 (by rfl) ⟨4751702, by rfl⟩ : syracuseStep 6335603 = 9503405) B9503405
theorem B2371187 : Blo 738327 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B2502305 : Blo 738327 2502305 := bstep (se 2 (by rfl) ⟨938364, by rfl⟩ : syracuseStep 2502305 = 1876729) B1876729
theorem B831199 : Blo 738327 831199 := bstep (se 1 (by rfl) ⟨623399, by rfl⟩ : syracuseStep 831199 = 1246799) B1246799
theorem B831775 : Blo 738327 831775 := bstep (se 1 (by rfl) ⟨623831, by rfl⟩ : syracuseStep 831775 = 1247663) B1247663
theorem B3158473 : Blo 738327 3158473 := bstep (se 2 (by rfl) ⟨1184427, by rfl⟩ : syracuseStep 3158473 = 2368855) B2368855
theorem B2503169 : Blo 738327 2503169 := bstep (se 2 (by rfl) ⟨938688, by rfl⟩ : syracuseStep 2503169 = 1877377) B1877377
theorem B832063 : Blo 738327 832063 := bstep (se 1 (by rfl) ⟨624047, by rfl⟩ : syracuseStep 832063 = 1248095) B1248095
theorem B4010593 : Blo 738327 4010593 := bstep (se 2 (by rfl) ⟨1503972, by rfl⟩ : syracuseStep 4010593 = 3007945) B3007945
theorem B4010719 : Blo 738327 4010719 := bstep (se 1 (by rfl) ⟨3008039, by rfl⟩ : syracuseStep 4010719 = 6016079) B6016079
theorem B2667343 : Blo 738327 2667343 := bstep (se 1 (by rfl) ⟨2000507, by rfl⟩ : syracuseStep 2667343 = 4001015) B4001015
theorem B2503655 : Blo 738327 2503655 := bstep (se 1 (by rfl) ⟨1877741, by rfl⟩ : syracuseStep 2503655 = 3755483) B3755483
theorem B2667617 : Blo 738327 2667617 := bstep (se 2 (by rfl) ⟨1000356, by rfl⟩ : syracuseStep 2667617 = 2000713) B2000713
theorem B2503979 : Blo 738327 2503979 := bstep (se 1 (by rfl) ⟨1877984, by rfl⟩ : syracuseStep 2503979 = 3755969) B3755969
theorem B832891 : Blo 738327 832891 := bstep (se 1 (by rfl) ⟨624668, by rfl⟩ : syracuseStep 832891 = 1249337) B1249337
theorem B2504249 : Blo 738327 2504249 := bstep (se 2 (by rfl) ⟨939093, by rfl⟩ : syracuseStep 2504249 = 1878187) B1878187
theorem B2537147 : Blo 738327 2537147 := bstep (se 1 (by rfl) ⟨1902860, by rfl⟩ : syracuseStep 2537147 = 3805721) B3805721
theorem B4273975 : Blo 738327 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B833359 : Blo 738327 833359 := bstep (se 1 (by rfl) ⟨625019, by rfl⟩ : syracuseStep 833359 = 1250039) B1250039
theorem B11974493 : Blo 738327 11974493 := bstep (se 3 (by rfl) ⟨2245217, by rfl⟩ : syracuseStep 11974493 = 4490435) B4490435
theorem B2668393 : Blo 738327 2668393 := bstep (se 2 (by rfl) ⟨1000647, by rfl⟩ : syracuseStep 2668393 = 2001295) B2001295
theorem B833755 : Blo 738327 833755 := bstep (se 1 (by rfl) ⟨625316, by rfl⟩ : syracuseStep 833755 = 1250633) B1250633
theorem B899359 : Blo 738327 899359 := bstep (se 1 (by rfl) ⟨674519, by rfl⟩ : syracuseStep 899359 = 1349039) B1349039
theorem B834043 : Blo 738327 834043 := bstep (se 1 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 834043 = 1251065) B1251065
theorem B4012667 : Blo 738327 4012667 := bstep (se 1 (by rfl) ⟨3009500, by rfl⟩ : syracuseStep 4012667 = 6019001) B6019001
theorem B834223 : Blo 738327 834223 := bstep (se 1 (by rfl) ⟨625667, by rfl⟩ : syracuseStep 834223 = 1251335) B1251335
theorem B834511 : Blo 738327 834511 := bstep (se 1 (by rfl) ⟨625883, by rfl⟩ : syracuseStep 834511 = 1251767) B1251767
theorem B2112551 : Blo 738327 2112551 := bstep (se 1 (by rfl) ⟨1584413, by rfl⟩ : syracuseStep 2112551 = 3168827) B3168827
theorem B834907 : Blo 738327 834907 := bstep (se 1 (by rfl) ⟨626180, by rfl⟩ : syracuseStep 834907 = 1252361) B1252361
theorem B2112905 : Blo 738327 2112905 := bstep (se 2 (by rfl) ⟨792339, by rfl⟩ : syracuseStep 2112905 = 1584679) B1584679
theorem B6339977 : Blo 738327 6339977 := bstep (se 2 (by rfl) ⟨2377491, by rfl⟩ : syracuseStep 6339977 = 4754983) B4754983
theorem B835015 : Blo 738327 835015 := bstep (se 1 (by rfl) ⟨626261, by rfl⟩ : syracuseStep 835015 = 1252523) B1252523
theorem B3751433 : Blo 738327 3751433 := bstep (se 2 (by rfl) ⟨1406787, by rfl⟩ : syracuseStep 3751433 = 2813575) B2813575
theorem B6340355 : Blo 738327 6340355 := bstep (se 1 (by rfl) ⟨4755266, by rfl⟩ : syracuseStep 6340355 = 9510533) B9510533
theorem B29278361 : Blo 738327 29278361 := bstep (se 2 (by rfl) ⟨10979385, by rfl⟩ : syracuseStep 29278361 = 21958771) B21958771
theorem B934507 : Blo 738327 934507 := bstep (se 1 (by rfl) ⟨700880, by rfl⟩ : syracuseStep 934507 = 1401761) B1401761
theorem B3162847 : Blo 738327 3162847 := bstep (se 1 (by rfl) ⟨2372135, by rfl⟩ : syracuseStep 3162847 = 4744271) B4744271
theorem B2376415 : Blo 738327 2376415 := bstep (se 1 (by rfl) ⟨1782311, by rfl⟩ : syracuseStep 2376415 = 3564623) B3564623
theorem B8012621 : Blo 738327 8012621 := bstep (se 3 (by rfl) ⟨1502366, by rfl⟩ : syracuseStep 8012621 = 3004733) B3004733
theorem B934735 : Blo 738327 934735 := bstep (se 1 (by rfl) ⟨701051, by rfl⟩ : syracuseStep 934735 = 1402103) B1402103
theorem B1000399 : Blo 738327 1000399 := bstep (se 1 (by rfl) ⟨750299, by rfl⟩ : syracuseStep 1000399 = 1500599) B1500599
theorem B738591 : Blo 738327 738591 := bstep (se 1 (by rfl) ⟨553943, by rfl⟩ : syracuseStep 738591 = 1107887) B1107887
theorem B1066279 : Blo 738327 1066279 := bstep (se 1 (by rfl) ⟨799709, by rfl⟩ : syracuseStep 1066279 = 1599419) B1599419
theorem B15418667 : Blo 738327 15418667 := bstep (se 1 (by rfl) ⟨11564000, by rfl⟩ : syracuseStep 15418667 = 23128001) B23128001
theorem B738651 : Blo 738327 738651 := bstep (se 1 (by rfl) ⟨553988, by rfl⟩ : syracuseStep 738651 = 1107977) B1107977
theorem B738671 : Blo 738327 738671 := bstep (se 1 (by rfl) ⟨554003, by rfl⟩ : syracuseStep 738671 = 1108007) B1108007
theorem B3753377 : Blo 738327 3753377 := bstep (se 2 (by rfl) ⟨1407516, by rfl⟩ : syracuseStep 3753377 = 2815033) B2815033
theorem B738727 : Blo 738327 738727 := bstep (se 1 (by rfl) ⟨554045, by rfl⟩ : syracuseStep 738727 = 1108091) B1108091
theorem B738811 : Blo 738327 738811 := bstep (se 1 (by rfl) ⟨554108, by rfl⟩ : syracuseStep 738811 = 1108217) B1108217
theorem B738879 : Blo 738327 738879 := bstep (se 1 (by rfl) ⟨554159, by rfl⟩ : syracuseStep 738879 = 1108319) B1108319
theorem B738887 : Blo 738327 738887 := bstep (se 1 (by rfl) ⟨554165, by rfl⟩ : syracuseStep 738887 = 1108331) B1108331
theorem B3163805 : Blo 738327 3163805 := bstep (se 3 (by rfl) ⟨593213, by rfl⟩ : syracuseStep 3163805 = 1186427) B1186427
theorem B14239421 : Blo 738327 14239421 := bstep (se 3 (by rfl) ⟨2669891, by rfl⟩ : syracuseStep 14239421 = 5339783) B5339783
theorem B739039 : Blo 738327 739039 := bstep (se 1 (by rfl) ⟨554279, by rfl⟩ : syracuseStep 739039 = 1108559) B1108559
theorem B739119 : Blo 738327 739119 := bstep (se 1 (by rfl) ⟨554339, by rfl⟩ : syracuseStep 739119 = 1108679) B1108679
theorem B6309737 : Blo 738327 6309737 := bstep (se 2 (by rfl) ⟨2366151, by rfl⟩ : syracuseStep 6309737 = 4732303) B4732303
theorem B12011399 : Blo 738327 12011399 := bstep (se 1 (by rfl) ⟨9008549, by rfl⟩ : syracuseStep 12011399 = 18017099) B18017099
theorem B739227 : Blo 738327 739227 := bstep (se 1 (by rfl) ⟨554420, by rfl⟩ : syracuseStep 739227 = 1108841) B1108841
theorem B739279 : Blo 738327 739279 := bstep (se 1 (by rfl) ⟨554459, by rfl⟩ : syracuseStep 739279 = 1108919) B1108919
theorem B739303 : Blo 738327 739303 := bstep (se 1 (by rfl) ⟨554477, by rfl⟩ : syracuseStep 739303 = 1108955) B1108955
theorem B2803841 : Blo 738327 2803841 := bstep (se 2 (by rfl) ⟨1051440, by rfl⟩ : syracuseStep 2803841 = 2102881) B2102881
theorem B739615 : Blo 738327 739615 := bstep (se 1 (by rfl) ⟨554711, by rfl⟩ : syracuseStep 739615 = 1109423) B1109423
theorem B739675 : Blo 738327 739675 := bstep (se 1 (by rfl) ⟨554756, by rfl⟩ : syracuseStep 739675 = 1109513) B1109513
theorem B739695 : Blo 738327 739695 := bstep (se 1 (by rfl) ⟨554771, by rfl⟩ : syracuseStep 739695 = 1109543) B1109543
theorem B739751 : Blo 738327 739751 := bstep (se 1 (by rfl) ⟨554813, by rfl⟩ : syracuseStep 739751 = 1109627) B1109627
theorem B739835 : Blo 738327 739835 := bstep (se 1 (by rfl) ⟨554876, by rfl⟩ : syracuseStep 739835 = 1109753) B1109753
theorem B739903 : Blo 738327 739903 := bstep (se 1 (by rfl) ⟨554927, by rfl⟩ : syracuseStep 739903 = 1109855) B1109855
theorem B739911 : Blo 738327 739911 := bstep (se 1 (by rfl) ⟨554933, by rfl⟩ : syracuseStep 739911 = 1109867) B1109867
theorem B3164795 : Blo 738327 3164795 := bstep (se 1 (by rfl) ⟨2373596, by rfl⟩ : syracuseStep 3164795 = 4747193) B4747193
theorem B936623 : Blo 738327 936623 := bstep (se 1 (by rfl) ⟨702467, by rfl⟩ : syracuseStep 936623 = 1404935) B1404935
theorem B740063 : Blo 738327 740063 := bstep (se 1 (by rfl) ⟨555047, by rfl⟩ : syracuseStep 740063 = 1110095) B1110095
theorem B740143 : Blo 738327 740143 := bstep (se 1 (by rfl) ⟨555107, by rfl⟩ : syracuseStep 740143 = 1110215) B1110215
theorem B3853175 : Blo 738327 3853175 := bstep (se 1 (by rfl) ⟨2889881, by rfl⟩ : syracuseStep 3853175 = 5779763) B5779763
theorem B740251 : Blo 738327 740251 := bstep (se 1 (by rfl) ⟨555188, by rfl⟩ : syracuseStep 740251 = 1110377) B1110377
theorem B740303 : Blo 738327 740303 := bstep (se 1 (by rfl) ⟨555227, by rfl⟩ : syracuseStep 740303 = 1110455) B1110455
theorem B740327 : Blo 738327 740327 := bstep (se 1 (by rfl) ⟨555245, by rfl⟩ : syracuseStep 740327 = 1110491) B1110491
theorem B740639 : Blo 738327 740639 := bstep (se 1 (by rfl) ⟨555479, by rfl⟩ : syracuseStep 740639 = 1110959) B1110959
theorem B740699 : Blo 738327 740699 := bstep (se 1 (by rfl) ⟨555524, by rfl⟩ : syracuseStep 740699 = 1111049) B1111049
theorem B937327 : Blo 738327 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B740719 : Blo 738327 740719 := bstep (se 1 (by rfl) ⟨555539, by rfl⟩ : syracuseStep 740719 = 1111079) B1111079
theorem B740775 : Blo 738327 740775 := bstep (se 1 (by rfl) ⟨555581, by rfl⟩ : syracuseStep 740775 = 1111163) B1111163
theorem B740859 : Blo 738327 740859 := bstep (se 1 (by rfl) ⟨555644, by rfl⟩ : syracuseStep 740859 = 1111289) B1111289
theorem B740927 : Blo 738327 740927 := bstep (se 1 (by rfl) ⟨555695, by rfl⟩ : syracuseStep 740927 = 1111391) B1111391
theorem B740935 : Blo 738327 740935 := bstep (se 1 (by rfl) ⟨555701, by rfl⟩ : syracuseStep 740935 = 1111403) B1111403
theorem B5623505 : Blo 738327 5623505 := bstep (se 2 (by rfl) ⟨2108814, by rfl⟩ : syracuseStep 5623505 = 4217629) B4217629
theorem B741087 : Blo 738327 741087 := bstep (se 1 (by rfl) ⟨555815, by rfl⟩ : syracuseStep 741087 = 1111631) B1111631
theorem B741167 : Blo 738327 741167 := bstep (se 1 (by rfl) ⟨555875, by rfl⟩ : syracuseStep 741167 = 1111751) B1111751
theorem B3559241 : Blo 738327 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B741275 : Blo 738327 741275 := bstep (se 1 (by rfl) ⟨555956, by rfl⟩ : syracuseStep 741275 = 1111913) B1111913
theorem B5066653 : Blo 738327 5066653 := bstep (se 3 (by rfl) ⟨949997, by rfl⟩ : syracuseStep 5066653 = 1899995) B1899995
theorem B741327 : Blo 738327 741327 := bstep (se 1 (by rfl) ⟨555995, by rfl⟩ : syracuseStep 741327 = 1111991) B1111991
theorem B741351 : Blo 738327 741351 := bstep (se 1 (by rfl) ⟨556013, by rfl⟩ : syracuseStep 741351 = 1112027) B1112027
theorem B2805785 : Blo 738327 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B4214987 : Blo 738327 4214987 := bstep (se 1 (by rfl) ⟨3161240, by rfl⟩ : syracuseStep 4214987 = 6322481) B6322481
theorem B10113281 : Blo 738327 10113281 := bstep (se 2 (by rfl) ⟨3792480, by rfl⟩ : syracuseStep 10113281 = 7584961) B7584961
theorem B741663 : Blo 738327 741663 := bstep (se 1 (by rfl) ⟨556247, by rfl⟩ : syracuseStep 741663 = 1112495) B1112495
theorem B741723 : Blo 738327 741723 := bstep (se 1 (by rfl) ⟨556292, by rfl⟩ : syracuseStep 741723 = 1112585) B1112585
theorem B741743 : Blo 738327 741743 := bstep (se 1 (by rfl) ⟨556307, by rfl⟩ : syracuseStep 741743 = 1112615) B1112615
theorem B741799 : Blo 738327 741799 := bstep (se 1 (by rfl) ⟨556349, by rfl⟩ : syracuseStep 741799 = 1112699) B1112699
theorem B741883 : Blo 738327 741883 := bstep (se 1 (by rfl) ⟨556412, by rfl⟩ : syracuseStep 741883 = 1112825) B1112825
theorem B741951 : Blo 738327 741951 := bstep (se 1 (by rfl) ⟨556463, by rfl⟩ : syracuseStep 741951 = 1112927) B1112927
theorem B938567 : Blo 738327 938567 := bstep (se 1 (by rfl) ⟨703925, by rfl⟩ : syracuseStep 938567 = 1407851) B1407851
theorem B741959 : Blo 738327 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B938719 : Blo 738327 938719 := bstep (se 1 (by rfl) ⟨704039, by rfl⟩ : syracuseStep 938719 = 1408079) B1408079
theorem B742111 : Blo 738327 742111 := bstep (se 1 (by rfl) ⟨556583, by rfl⟩ : syracuseStep 742111 = 1113167) B1113167
theorem B742191 : Blo 738327 742191 := bstep (se 1 (by rfl) ⟨556643, by rfl⟩ : syracuseStep 742191 = 1113287) B1113287
theorem B7132013 : Blo 738327 7132013 := bstep (se 3 (by rfl) ⟨1337252, by rfl⟩ : syracuseStep 7132013 = 2674505) B2674505
theorem B742299 : Blo 738327 742299 := bstep (se 1 (by rfl) ⟨556724, by rfl⟩ : syracuseStep 742299 = 1113449) B1113449
theorem B3167171 : Blo 738327 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B6313049 : Blo 738327 6313049 := bstep (se 2 (by rfl) ⟨2367393, by rfl⟩ : syracuseStep 6313049 = 4734787) B4734787
theorem B4740221 : Blo 738327 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B14243111 : Blo 738327 14243111 := bstep (se 1 (by rfl) ⟨10682333, by rfl⟩ : syracuseStep 14243111 = 21364667) B21364667
theorem B6018745 : Blo 738327 6018745 := bstep (se 2 (by rfl) ⟨2257029, by rfl⟩ : syracuseStep 6018745 = 4514059) B4514059
theorem B2053993 : Blo 738327 2053993 := bstep (se 2 (by rfl) ⟨770247, by rfl⟩ : syracuseStep 2053993 = 1540495) B1540495
theorem B5625935 : Blo 738327 5625935 := bstep (se 1 (by rfl) ⟨4219451, by rfl⟩ : syracuseStep 5625935 = 8438903) B8438903
theorem B3037313 : Blo 738327 3037313 := bstep (se 2 (by rfl) ⟨1138992, by rfl⟩ : syracuseStep 3037313 = 2277985) B2277985
theorem B1661291 : Blo 738327 1661291 := bstep (se 1 (by rfl) ⟨1245968, by rfl⟩ : syracuseStep 1661291 = 2491937) B2491937
theorem B3561839 : Blo 738327 3561839 := bstep (se 1 (by rfl) ⟨2671379, by rfl⟩ : syracuseStep 3561839 = 5342759) B5342759
theorem B1661435 : Blo 738327 1661435 := bstep (se 1 (by rfl) ⟨1246076, by rfl⟩ : syracuseStep 1661435 = 2492153) B2492153
theorem B1661561 : Blo 738327 1661561 := bstep (se 2 (by rfl) ⟨623085, by rfl⟩ : syracuseStep 1661561 = 1246171) B1246171
theorem B1661615 : Blo 738327 1661615 := bstep (se 1 (by rfl) ⟨1246211, by rfl⟩ : syracuseStep 1661615 = 2492423) B2492423
theorem B1661687 : Blo 738327 1661687 := bstep (se 1 (by rfl) ⟨1246265, by rfl⟩ : syracuseStep 1661687 = 2492531) B2492531
theorem B2808701 : Blo 738327 2808701 := bstep (se 3 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 2808701 = 1053263) B1053263
theorem B1661867 : Blo 738327 1661867 := bstep (se 1 (by rfl) ⟨1246400, by rfl⟩ : syracuseStep 1661867 = 2492801) B2492801
theorem B1334651 : Blo 738327 1334651 := bstep (se 1 (by rfl) ⟨1000988, by rfl⟩ : syracuseStep 1334651 = 2001977) B2001977
theorem B1662407 : Blo 738327 1662407 := bstep (se 1 (by rfl) ⟨1246805, by rfl⟩ : syracuseStep 1662407 = 2493611) B2493611
theorem B2809505 : Blo 738327 2809505 := bstep (se 2 (by rfl) ⟨1053564, by rfl⟩ : syracuseStep 2809505 = 2107129) B2107129
theorem B9625337 : Blo 738327 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B18013985 : Blo 738327 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B1662767 : Blo 738327 1662767 := bstep (se 1 (by rfl) ⟨1247075, by rfl⟩ : syracuseStep 1662767 = 2494151) B2494151
theorem B3661615 : Blo 738327 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B2809961 : Blo 738327 2809961 := bstep (se 2 (by rfl) ⟨1053735, by rfl⟩ : syracuseStep 2809961 = 2107471) B2107471
theorem B36528245 : Blo 738327 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B61661357 : Blo 738327 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B5693651 : Blo 738327 5693651 := bstep (se 1 (by rfl) ⟨4270238, by rfl⟩ : syracuseStep 5693651 = 8540477) B8540477
theorem B1663343 : Blo 738327 1663343 := bstep (se 1 (by rfl) ⟨1247507, by rfl⟩ : syracuseStep 1663343 = 2495015) B2495015
theorem B1663415 : Blo 738327 1663415 := bstep (se 1 (by rfl) ⟨1247561, by rfl⟩ : syracuseStep 1663415 = 2495123) B2495123
theorem B4219361 : Blo 738327 4219361 := bstep (se 2 (by rfl) ⟨1582260, by rfl⟩ : syracuseStep 4219361 = 3164521) B3164521
theorem B1663559 : Blo 738327 1663559 := bstep (se 1 (by rfl) ⟨1247669, by rfl⟩ : syracuseStep 1663559 = 2495339) B2495339
theorem B1827407 : Blo 738327 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B1663595 : Blo 738327 1663595 := bstep (se 1 (by rfl) ⟨1247696, by rfl⟩ : syracuseStep 1663595 = 2495393) B2495393
theorem B13001363 : Blo 738327 13001363 := bstep (se 1 (by rfl) ⟨9751022, by rfl⟩ : syracuseStep 13001363 = 19502045) B19502045
theorem B1663991 : Blo 738327 1663991 := bstep (se 1 (by rfl) ⟨1247993, by rfl⟩ : syracuseStep 1663991 = 2495987) B2495987
theorem B1664351 : Blo 738327 1664351 := bstep (se 1 (by rfl) ⟨1248263, by rfl⟩ : syracuseStep 1664351 = 2496527) B2496527
theorem B5629337 : Blo 738327 5629337 := bstep (se 2 (by rfl) ⟨2111001, by rfl⟩ : syracuseStep 5629337 = 4222003) B4222003
theorem B3368429 : Blo 738327 3368429 := bstep (se 3 (by rfl) ⟨631580, by rfl⟩ : syracuseStep 3368429 = 1263161) B1263161
theorem B2811449 : Blo 738327 2811449 := bstep (se 2 (by rfl) ⟨1054293, by rfl⟩ : syracuseStep 2811449 = 2108587) B2108587
theorem B1107551 : Blo 738327 1107551 := bstep (se 1 (by rfl) ⟨830663, by rfl⟩ : syracuseStep 1107551 = 1661327) B1661327
theorem B1664747 : Blo 738327 1664747 := bstep (se 1 (by rfl) ⟨1248560, by rfl⟩ : syracuseStep 1664747 = 2497121) B2497121
theorem B1107767 : Blo 738327 1107767 := bstep (se 1 (by rfl) ⟨830825, by rfl⟩ : syracuseStep 1107767 = 1661651) B1661651
theorem B1664873 : Blo 738327 1664873 := bstep (se 2 (by rfl) ⟨624327, by rfl⟩ : syracuseStep 1664873 = 1248655) B1248655
theorem B1108073 : Blo 738327 1108073 := bstep (se 2 (by rfl) ⟨415527, by rfl⟩ : syracuseStep 1108073 = 831055) B831055
theorem B3565853 : Blo 738327 3565853 := bstep (se 3 (by rfl) ⟨668597, by rfl⟩ : syracuseStep 3565853 = 1337195) B1337195
theorem B11397505 : Blo 738327 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B1108391 : Blo 738327 1108391 := bstep (se 1 (by rfl) ⟨831293, by rfl⟩ : syracuseStep 1108391 = 1662587) B1662587
theorem B1108475 : Blo 738327 1108475 := bstep (se 1 (by rfl) ⟨831356, by rfl⟩ : syracuseStep 1108475 = 1662713) B1662713
theorem B10644047 : Blo 738327 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B1108601 : Blo 738327 1108601 := bstep (se 2 (by rfl) ⟨415725, by rfl⟩ : syracuseStep 1108601 = 831451) B831451
theorem B3369595 : Blo 738327 3369595 := bstep (se 1 (by rfl) ⟨2527196, by rfl⟩ : syracuseStep 3369595 = 5054393) B5054393
theorem B1108655 : Blo 738327 1108655 := bstep (se 1 (by rfl) ⟨831491, by rfl⟩ : syracuseStep 1108655 = 1662983) B1662983
theorem B1665719 : Blo 738327 1665719 := bstep (se 1 (by rfl) ⟨1249289, by rfl⟩ : syracuseStep 1665719 = 2498579) B2498579
theorem B1108703 : Blo 738327 1108703 := bstep (se 1 (by rfl) ⟨831527, by rfl⟩ : syracuseStep 1108703 = 1663055) B1663055
theorem B12151565 : Blo 738327 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B9497411 : Blo 738327 9497411 := bstep (se 1 (by rfl) ⟨7123058, by rfl⟩ : syracuseStep 9497411 = 14246117) B14246117
theorem B4221821 : Blo 738327 4221821 := bstep (se 3 (by rfl) ⟨791591, by rfl⟩ : syracuseStep 4221821 = 1583183) B1583183
theorem B1665935 : Blo 738327 1665935 := bstep (se 1 (by rfl) ⟨1249451, by rfl⟩ : syracuseStep 1665935 = 2498903) B2498903
theorem B1108967 : Blo 738327 1108967 := bstep (se 1 (by rfl) ⟨831725, by rfl⟩ : syracuseStep 1108967 = 1663451) B1663451
theorem B15428647 : Blo 738327 15428647 := bstep (se 1 (by rfl) ⟨11571485, by rfl⟩ : syracuseStep 15428647 = 23142971) B23142971
theorem B1404047 : Blo 738327 1404047 := bstep (se 1 (by rfl) ⟨1053035, by rfl⟩ : syracuseStep 1404047 = 2106071) B2106071
theorem B23981275 : Blo 738327 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B1109225 : Blo 738327 1109225 := bstep (se 2 (by rfl) ⟨415959, by rfl⟩ : syracuseStep 1109225 = 831919) B831919
theorem B1109279 : Blo 738327 1109279 := bstep (se 1 (by rfl) ⟨831959, by rfl⟩ : syracuseStep 1109279 = 1663919) B1663919
theorem B1404191 : Blo 738327 1404191 := bstep (se 1 (by rfl) ⟨1053143, by rfl⟩ : syracuseStep 1404191 = 2106287) B2106287
theorem B1109447 : Blo 738327 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B1666655 : Blo 738327 1666655 := bstep (se 1 (by rfl) ⟨1249991, by rfl⟩ : syracuseStep 1666655 = 2499983) B2499983
theorem B6319883 : Blo 738327 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B1109801 : Blo 738327 1109801 := bstep (se 2 (by rfl) ⟨416175, by rfl⟩ : syracuseStep 1109801 = 832351) B832351
theorem B1109807 : Blo 738327 1109807 := bstep (se 1 (by rfl) ⟨832355, by rfl⟩ : syracuseStep 1109807 = 1664711) B1664711
theorem B1666871 : Blo 738327 1666871 := bstep (se 1 (by rfl) ⟨1250153, by rfl⟩ : syracuseStep 1666871 = 2500307) B2500307
theorem B13692989 : Blo 738327 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B24047705 : Blo 738327 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B1667177 : Blo 738327 1667177 := bstep (se 2 (by rfl) ⟨625191, by rfl⟩ : syracuseStep 1667177 = 1250383) B1250383
theorem B1110281 : Blo 738327 1110281 := bstep (se 2 (by rfl) ⟨416355, by rfl⟩ : syracuseStep 1110281 = 832711) B832711
theorem B1110383 : Blo 738327 1110383 := bstep (se 1 (by rfl) ⟨832787, by rfl⟩ : syracuseStep 1110383 = 1665575) B1665575
theorem B1012295 : Blo 738327 1012295 := bstep (se 1 (by rfl) ⟨759221, by rfl⟩ : syracuseStep 1012295 = 1518443) B1518443
theorem B1110599 : Blo 738327 1110599 := bstep (se 1 (by rfl) ⟨832949, by rfl⟩ : syracuseStep 1110599 = 1665899) B1665899
theorem B1667663 : Blo 738327 1667663 := bstep (se 1 (by rfl) ⟨1250747, by rfl⟩ : syracuseStep 1667663 = 2501495) B2501495
theorem B1110635 : Blo 738327 1110635 := bstep (se 1 (by rfl) ⟨832976, by rfl⟩ : syracuseStep 1110635 = 1665953) B1665953
theorem B1667807 : Blo 738327 1667807 := bstep (se 1 (by rfl) ⟨1250855, by rfl⟩ : syracuseStep 1667807 = 2501711) B2501711
theorem B1110863 : Blo 738327 1110863 := bstep (se 1 (by rfl) ⟨833147, by rfl⟩ : syracuseStep 1110863 = 1666295) B1666295
theorem B1504079 : Blo 738327 1504079 := bstep (se 1 (by rfl) ⟨1128059, by rfl⟩ : syracuseStep 1504079 = 2256119) B2256119
theorem B26997619 : Blo 738327 26997619 := bstep (se 1 (by rfl) ⟨20248214, by rfl⟩ : syracuseStep 26997619 = 40496429) B40496429
theorem B1668059 : Blo 738327 1668059 := bstep (se 1 (by rfl) ⟨1251044, by rfl⟩ : syracuseStep 1668059 = 2502089) B2502089
theorem B7992377 : Blo 738327 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B1668239 : Blo 738327 1668239 := bstep (se 1 (by rfl) ⟨1251179, by rfl⟩ : syracuseStep 1668239 = 2502359) B2502359
theorem B1111259 : Blo 738327 1111259 := bstep (se 1 (by rfl) ⟨833444, by rfl⟩ : syracuseStep 1111259 = 1666889) B1666889
theorem B1668329 : Blo 738327 1668329 := bstep (se 2 (by rfl) ⟨625623, by rfl⟩ : syracuseStep 1668329 = 1251247) B1251247
theorem B1996019 : Blo 738327 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B1668383 : Blo 738327 1668383 := bstep (se 1 (by rfl) ⟨1251287, by rfl⟩ : syracuseStep 1668383 = 2502575) B2502575
theorem B1111433 : Blo 738327 1111433 := bstep (se 2 (by rfl) ⟨416787, by rfl⟩ : syracuseStep 1111433 = 833575) B833575
theorem B6321797 : Blo 738327 6321797 := bstep (se 4 (by rfl) ⟨592668, by rfl⟩ : syracuseStep 6321797 = 1185337) B1185337
theorem B1111787 : Blo 738327 1111787 := bstep (se 1 (by rfl) ⟨833840, by rfl⟩ : syracuseStep 1111787 = 1667681) B1667681
theorem B1668905 : Blo 738327 1668905 := bstep (se 2 (by rfl) ⟨625839, by rfl⟩ : syracuseStep 1668905 = 1251679) B1251679
theorem B8452025 : Blo 738327 8452025 := bstep (se 2 (by rfl) ⟨3169509, by rfl⟩ : syracuseStep 8452025 = 6339019) B6339019
theorem B1112015 : Blo 738327 1112015 := bstep (se 1 (by rfl) ⟨834011, by rfl⟩ : syracuseStep 1112015 = 1668023) B1668023
theorem B13727981 : Blo 738327 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B1112411 : Blo 738327 1112411 := bstep (se 1 (by rfl) ⟨834308, by rfl⟩ : syracuseStep 1112411 = 1668617) B1668617
theorem B1112639 : Blo 738327 1112639 := bstep (se 1 (by rfl) ⟨834479, by rfl⟩ : syracuseStep 1112639 = 1668959) B1668959
theorem B1112759 : Blo 738327 1112759 := bstep (se 1 (by rfl) ⟨834569, by rfl⟩ : syracuseStep 1112759 = 1669139) B1669139
theorem B1669967 : Blo 738327 1669967 := bstep (se 1 (by rfl) ⟨1252475, by rfl⟩ : syracuseStep 1669967 = 2504951) B2504951
theorem B1112987 : Blo 738327 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B1670183 : Blo 738327 1670183 := bstep (se 1 (by rfl) ⟨1252637, by rfl⟩ : syracuseStep 1670183 = 2505275) B2505275
theorem B1113383 : Blo 738327 1113383 := bstep (se 1 (by rfl) ⟨835037, by rfl⟩ : syracuseStep 1113383 = 1670075) B1670075
theorem B1113467 : Blo 738327 1113467 := bstep (se 1 (by rfl) ⟨835100, by rfl⟩ : syracuseStep 1113467 = 1670201) B1670201
theorem B1408747 : Blo 738327 1408747 := bstep (se 1 (by rfl) ⟨1056560, by rfl⟩ : syracuseStep 1408747 = 2113121) B2113121
theorem B3997487 : Blo 738327 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B1408823 : Blo 738327 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B2817949 : Blo 738327 2817949 := bstep (se 3 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 2817949 = 1056731) B1056731
theorem B64127213 : Blo 738327 64127213 := bstep (se 3 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 64127213 = 24047705) B24047705
theorem B5341747 : Blo 738327 5341747 := bstep (se 1 (by rfl) ⟨4006310, by rfl⟩ : syracuseStep 5341747 = 8012621) B8012621
theorem B1246009 : Blo 738327 1246009 := bstep (se 2 (by rfl) ⟨467253, by rfl⟩ : syracuseStep 1246009 = 934507) B934507
theorem B1246063 : Blo 738327 1246063 := bstep (se 1 (by rfl) ⟨934547, by rfl⟩ : syracuseStep 1246063 = 1869095) B1869095
theorem B1246313 : Blo 738327 1246313 := bstep (se 2 (by rfl) ⟨467367, by rfl⟩ : syracuseStep 1246313 = 934735) B934735
theorem B1869227 : Blo 738327 1869227 := bstep (se 1 (by rfl) ⟨1401920, by rfl⟩ : syracuseStep 1869227 = 2803841) B2803841
theorem B1247467 : Blo 738327 1247467 := bstep (se 1 (by rfl) ⟨935600, by rfl⟩ : syracuseStep 1247467 = 1871201) B1871201
theorem B1902943 : Blo 738327 1902943 := bstep (se 1 (by rfl) ⟨1427207, by rfl⟩ : syracuseStep 1902943 = 2854415) B2854415
theorem B1247771 : Blo 738327 1247771 := bstep (se 1 (by rfl) ⟨935828, by rfl⟩ : syracuseStep 1247771 = 1871657) B1871657
theorem B1870523 : Blo 738327 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B1248439 : Blo 738327 1248439 := bstep (se 1 (by rfl) ⟨936329, by rfl⟩ : syracuseStep 1248439 = 1872659) B1872659
theorem B4754675 : Blo 738327 4754675 := bstep (se 1 (by rfl) ⟨3566006, by rfl⟩ : syracuseStep 4754675 = 7132013) B7132013
theorem B1051913 : Blo 738327 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B3738959 : Blo 738327 3738959 := bstep (se 1 (by rfl) ⟨2804219, by rfl⟩ : syracuseStep 3738959 = 5608439) B5608439
theorem B1281449 : Blo 738327 1281449 := bstep (se 2 (by rfl) ⟨480543, by rfl⟩ : syracuseStep 1281449 = 961087) B961087
theorem B1248743 : Blo 738327 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B4492793 : Blo 738327 4492793 := bstep (se 2 (by rfl) ⟨1684797, by rfl⟩ : syracuseStep 4492793 = 3369595) B3369595
theorem B9014777 : Blo 738327 9014777 := bstep (se 2 (by rfl) ⟨3380541, by rfl⟩ : syracuseStep 9014777 = 6761083) B6761083
theorem B1248763 : Blo 738327 1248763 := bstep (se 1 (by rfl) ⟨936572, by rfl⟩ : syracuseStep 1248763 = 1873145) B1873145
theorem B2494313 : Blo 738327 2494313 := bstep (se 2 (by rfl) ⟨935367, by rfl⟩ : syracuseStep 2494313 = 1870735) B1870735
theorem B1249195 : Blo 738327 1249195 := bstep (se 1 (by rfl) ⟨936896, by rfl⟩ : syracuseStep 1249195 = 1873793) B1873793
theorem B1249499 : Blo 738327 1249499 := bstep (se 1 (by rfl) ⟨937124, by rfl⟩ : syracuseStep 1249499 = 1874249) B1874249
theorem B1249735 : Blo 738327 1249735 := bstep (se 1 (by rfl) ⟨937301, by rfl⟩ : syracuseStep 1249735 = 1874603) B1874603
theorem B1249769 : Blo 738327 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B1872467 : Blo 738327 1872467 := bstep (se 1 (by rfl) ⟨1404350, by rfl⟩ : syracuseStep 1872467 = 2808701) B2808701
theorem B3740255 : Blo 738327 3740255 := bstep (se 1 (by rfl) ⟨2805191, by rfl⟩ : syracuseStep 3740255 = 5610383) B5610383
theorem B1873003 : Blo 738327 1873003 := bstep (se 1 (by rfl) ⟨1404752, by rfl⟩ : syracuseStep 1873003 = 2809505) B2809505
theorem B2495663 : Blo 738327 2495663 := bstep (se 1 (by rfl) ⟨1871747, by rfl⟩ : syracuseStep 2495663 = 3743495) B3743495
theorem B6755537 : Blo 738327 6755537 := bstep (se 2 (by rfl) ⟨2533326, by rfl⟩ : syracuseStep 6755537 = 5066653) B5066653
theorem B27071779 : Blo 738327 27071779 := bstep (se 1 (by rfl) ⟨20303834, by rfl⟩ : syracuseStep 27071779 = 40607669) B40607669
theorem B1873307 : Blo 738327 1873307 := bstep (se 1 (by rfl) ⟨1404980, by rfl⟩ : syracuseStep 1873307 = 2809961) B2809961
theorem B24352163 : Blo 738327 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B82286117 : Blo 738327 82286117 := bstep (se 4 (by rfl) ⟨7714323, by rfl⟩ : syracuseStep 82286117 = 15428647) B15428647
theorem B2103097 : Blo 738327 2103097 := bstep (se 2 (by rfl) ⟨788661, by rfl⟩ : syracuseStep 2103097 = 1577323) B1577323
theorem B2365537 : Blo 738327 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B5347457 : Blo 738327 5347457 := bstep (se 2 (by rfl) ⟨2005296, by rfl⟩ : syracuseStep 5347457 = 4010593) B4010593
theorem B1579151 : Blo 738327 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B1579169 : Blo 738327 1579169 := bstep (se 2 (by rfl) ⟨592188, by rfl⟩ : syracuseStep 1579169 = 1184377) B1184377
theorem B1251625 : Blo 738327 1251625 := bstep (se 2 (by rfl) ⟨469359, by rfl⟩ : syracuseStep 1251625 = 938719) B938719
theorem B5347625 : Blo 738327 5347625 := bstep (se 2 (by rfl) ⟨2005359, by rfl⟩ : syracuseStep 5347625 = 4010719) B4010719
theorem B1874299 : Blo 738327 1874299 := bstep (se 1 (by rfl) ⟨1405724, by rfl⟩ : syracuseStep 1874299 = 2811449) B2811449
theorem B2104031 : Blo 738327 2104031 := bstep (se 1 (by rfl) ⟨1578023, by rfl⟩ : syracuseStep 2104031 = 3156047) B3156047
theorem B1055695 : Blo 738327 1055695 := bstep (se 1 (by rfl) ⟨791771, by rfl⟩ : syracuseStep 1055695 = 1583543) B1583543
theorem B2497607 : Blo 738327 2497607 := bstep (se 1 (by rfl) ⟨1873205, by rfl⟩ : syracuseStep 2497607 = 3746411) B3746411
theorem B2497661 : Blo 738327 2497661 := bstep (se 3 (by rfl) ⟨468311, by rfl⟩ : syracuseStep 2497661 = 936623) B936623
theorem B8101043 : Blo 738327 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B6331607 : Blo 738327 6331607 := bstep (se 1 (by rfl) ⟨4748705, by rfl⟩ : syracuseStep 6331607 = 9497411) B9497411
theorem B2366729 : Blo 738327 2366729 := bstep (se 2 (by rfl) ⟨887523, by rfl⟩ : syracuseStep 2366729 = 1775047) B1775047
theorem B1187183 : Blo 738327 1187183 := bstep (se 1 (by rfl) ⟨890387, by rfl⟩ : syracuseStep 1187183 = 1780775) B1780775
theorem B2497931 : Blo 738327 2497931 := bstep (se 1 (by rfl) ⟨1873448, by rfl⟩ : syracuseStep 2497931 = 3746897) B3746897
theorem B1187401 : Blo 738327 1187401 := bstep (se 2 (by rfl) ⟨445275, by rfl⟩ : syracuseStep 1187401 = 890551) B890551
theorem B1580791 : Blo 738327 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B1778411 : Blo 738327 1778411 := bstep (se 1 (by rfl) ⟨1333808, by rfl⟩ : syracuseStep 1778411 = 2667617) B2667617
theorem B41100533 : Blo 738327 41100533 := bstep (se 5 (by rfl) ⟨1926587, by rfl⟩ : syracuseStep 41100533 = 3853175) B3853175
theorem B9151987 : Blo 738327 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B2369341 : Blo 738327 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B10692485 : Blo 738327 10692485 := bstep (se 4 (by rfl) ⟨1002420, by rfl⟩ : syracuseStep 10692485 = 2004841) B2004841
theorem B1878329 : Blo 738327 1878329 := bstep (se 2 (by rfl) ⟨704373, by rfl⟩ : syracuseStep 1878329 = 1408747) B1408747
theorem B2500955 : Blo 738327 2500955 := bstep (se 1 (by rfl) ⟨1875716, by rfl⟩ : syracuseStep 2500955 = 3751433) B3751433
theorem B2664991 : Blo 738327 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B2501225 : Blo 738327 2501225 := bstep (se 2 (by rfl) ⟨937959, by rfl⟩ : syracuseStep 2501225 = 1875919) B1875919
theorem B83143361 : Blo 738327 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B2403425 : Blo 738327 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B14200055 : Blo 738327 14200055 := bstep (se 1 (by rfl) ⟨10650041, by rfl⟩ : syracuseStep 14200055 = 21300083) B21300083
theorem B2108861 : Blo 738327 2108861 := bstep (se 3 (by rfl) ⟨395411, by rfl⟩ : syracuseStep 2108861 = 790823) B790823
theorem B2502251 : Blo 738327 2502251 := bstep (se 1 (by rfl) ⟨1876688, by rfl⟩ : syracuseStep 2502251 = 3753377) B3753377
theorem B2109203 : Blo 738327 2109203 := bstep (se 1 (by rfl) ⟨1581902, by rfl⟩ : syracuseStep 2109203 = 3163805) B3163805
theorem B831271 : Blo 738327 831271 := bstep (se 1 (by rfl) ⟨623453, by rfl⟩ : syracuseStep 831271 = 1246907) B1246907
theorem B2502521 : Blo 738327 2502521 := bstep (se 2 (by rfl) ⟨938445, by rfl⟩ : syracuseStep 2502521 = 1876891) B1876891
theorem B4206491 : Blo 738327 4206491 := bstep (se 1 (by rfl) ⟨3154868, by rfl⟩ : syracuseStep 4206491 = 6309737) B6309737
theorem B10661807 : Blo 738327 10661807 := bstep (se 1 (by rfl) ⟨7996355, by rfl⟩ : syracuseStep 10661807 = 15992711) B15992711
theorem B8007599 : Blo 738327 8007599 := bstep (se 1 (by rfl) ⟨6005699, by rfl⟩ : syracuseStep 8007599 = 12011399) B12011399
theorem B4796581 : Blo 738327 4796581 := bstep (se 4 (by rfl) ⟨449679, by rfl⟩ : syracuseStep 4796581 = 899359) B899359
theorem B2502845 : Blo 738327 2502845 := bstep (se 3 (by rfl) ⟨469283, by rfl⟩ : syracuseStep 2502845 = 938567) B938567
theorem B2699453 : Blo 738327 2699453 := bstep (se 3 (by rfl) ⟨506147, by rfl⟩ : syracuseStep 2699453 = 1012295) B1012295
theorem B1421705 : Blo 738327 1421705 := bstep (se 2 (by rfl) ⟨533139, by rfl⟩ : syracuseStep 1421705 = 1066279) B1066279
theorem B2109863 : Blo 738327 2109863 := bstep (se 1 (by rfl) ⟨1582397, by rfl⟩ : syracuseStep 2109863 = 3164795) B3164795
theorem B832423 : Blo 738327 832423 := bstep (se 1 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 832423 = 1248635) B1248635
theorem B3749003 : Blo 738327 3749003 := bstep (se 1 (by rfl) ⟨2811752, by rfl⟩ : syracuseStep 3749003 = 5623505) B5623505
theorem B2372827 : Blo 738327 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B2504033 : Blo 738327 2504033 := bstep (se 2 (by rfl) ⟨939012, by rfl⟩ : syracuseStep 2504033 = 1878025) B1878025
theorem B2536859 : Blo 738327 2536859 := bstep (se 1 (by rfl) ⟨1902644, by rfl⟩ : syracuseStep 2536859 = 3805289) B3805289
theorem B2373533 : Blo 738327 2373533 := bstep (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) B890075
theorem B2111447 : Blo 738327 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B4208699 : Blo 738327 4208699 := bstep (se 1 (by rfl) ⟨3156524, by rfl⟩ : syracuseStep 4208699 = 6313049) B6313049
theorem B3160147 : Blo 738327 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B1685767 : Blo 738327 1685767 := bstep (se 1 (by rfl) ⟨1264325, by rfl⟩ : syracuseStep 1685767 = 2528651) B2528651
theorem B834079 : Blo 738327 834079 := bstep (se 1 (by rfl) ⟨625559, by rfl⟩ : syracuseStep 834079 = 1251119) B1251119
theorem B3750623 : Blo 738327 3750623 := bstep (se 1 (by rfl) ⟨2812967, by rfl⟩ : syracuseStep 3750623 = 5625935) B5625935
theorem B2374559 : Blo 738327 2374559 := bstep (se 1 (by rfl) ⟨1780919, by rfl⟩ : syracuseStep 2374559 = 3561839) B3561839
theorem B1424567 : Blo 738327 1424567 := bstep (se 1 (by rfl) ⟨1068425, by rfl⟩ : syracuseStep 1424567 = 2136851) B2136851
theorem B5619131 : Blo 738327 5619131 := bstep (se 1 (by rfl) ⟨4214348, by rfl⟩ : syracuseStep 5619131 = 8428697) B8428697
theorem B4210157 : Blo 738327 4210157 := bstep (se 3 (by rfl) ⟨789404, by rfl⟩ : syracuseStep 4210157 = 1578809) B1578809
theorem B12009323 : Blo 738327 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B41107571 : Blo 738327 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B2670731 : Blo 738327 2670731 := bstep (se 1 (by rfl) ⟨2003048, by rfl⟩ : syracuseStep 2670731 = 4006097) B4006097
theorem B8667575 : Blo 738327 8667575 := bstep (se 1 (by rfl) ⟨6500681, by rfl⟩ : syracuseStep 8667575 = 13001363) B13001363
theorem B4211297 : Blo 738327 4211297 := bstep (se 2 (by rfl) ⟨1579236, by rfl⟩ : syracuseStep 4211297 = 3158473) B3158473
theorem B3752891 : Blo 738327 3752891 := bstep (se 1 (by rfl) ⟨2814668, by rfl⟩ : syracuseStep 3752891 = 5629337) B5629337
theorem B4637627 : Blo 738327 4637627 := bstep (se 1 (by rfl) ⟨3478220, by rfl⟩ : syracuseStep 4637627 = 6956441) B6956441
theorem B2245619 : Blo 738327 2245619 := bstep (se 1 (by rfl) ⟨1684214, by rfl⟩ : syracuseStep 2245619 = 3368429) B3368429
theorem B738367 : Blo 738327 738367 := bstep (se 1 (by rfl) ⟨553775, by rfl⟩ : syracuseStep 738367 = 1107551) B1107551
theorem B3556457 : Blo 738327 3556457 := bstep (se 2 (by rfl) ⟨1333671, by rfl⟩ : syracuseStep 3556457 = 2667343) B2667343
theorem B35996825 : Blo 738327 35996825 := bstep (se 2 (by rfl) ⟨13498809, by rfl⟩ : syracuseStep 35996825 = 26997619) B26997619
theorem B738511 : Blo 738327 738511 := bstep (se 1 (by rfl) ⟨553883, by rfl⟩ : syracuseStep 738511 = 1107767) B1107767
theorem B738715 : Blo 738327 738715 := bstep (se 1 (by rfl) ⟨554036, by rfl⟩ : syracuseStep 738715 = 1108073) B1108073
theorem B2377235 : Blo 738327 2377235 := bstep (se 1 (by rfl) ⟨1782926, by rfl⟩ : syracuseStep 2377235 = 3565853) B3565853
theorem B738927 : Blo 738327 738927 := bstep (se 1 (by rfl) ⟨554195, by rfl⟩ : syracuseStep 738927 = 1108391) B1108391
theorem B738983 : Blo 738327 738983 := bstep (se 1 (by rfl) ⟨554237, by rfl⟩ : syracuseStep 738983 = 1108475) B1108475
theorem B7096031 : Blo 738327 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B739067 : Blo 738327 739067 := bstep (se 1 (by rfl) ⟨554300, by rfl⟩ : syracuseStep 739067 = 1108601) B1108601
theorem B739103 : Blo 738327 739103 := bstep (se 1 (by rfl) ⟨554327, by rfl⟩ : syracuseStep 739103 = 1108655) B1108655
theorem B739135 : Blo 738327 739135 := bstep (se 1 (by rfl) ⟨554351, by rfl⟩ : syracuseStep 739135 = 1108703) B1108703
theorem B739311 : Blo 738327 739311 := bstep (se 1 (by rfl) ⟨554483, by rfl⟩ : syracuseStep 739311 = 1108967) B1108967
theorem B936031 : Blo 738327 936031 := bstep (se 1 (by rfl) ⟨702023, by rfl⟩ : syracuseStep 936031 = 1404047) B1404047
theorem B739483 : Blo 738327 739483 := bstep (se 1 (by rfl) ⟨554612, by rfl⟩ : syracuseStep 739483 = 1109225) B1109225
theorem B739519 : Blo 738327 739519 := bstep (se 1 (by rfl) ⟨554639, by rfl⟩ : syracuseStep 739519 = 1109279) B1109279
theorem B936127 : Blo 738327 936127 := bstep (se 1 (by rfl) ⟨702095, by rfl⟩ : syracuseStep 936127 = 1404191) B1404191
theorem B739631 : Blo 738327 739631 := bstep (se 1 (by rfl) ⟨554723, by rfl⟩ : syracuseStep 739631 = 1109447) B1109447
theorem B3557857 : Blo 738327 3557857 := bstep (se 2 (by rfl) ⟨1334196, by rfl⟩ : syracuseStep 3557857 = 2668393) B2668393
theorem B2738657 : Blo 738327 2738657 := bstep (se 2 (by rfl) ⟨1026996, by rfl⟩ : syracuseStep 2738657 = 2053993) B2053993
theorem B4213255 : Blo 738327 4213255 := bstep (se 1 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 4213255 = 6319883) B6319883
theorem B739867 : Blo 738327 739867 := bstep (se 1 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 739867 = 1109801) B1109801
theorem B739871 : Blo 738327 739871 := bstep (se 1 (by rfl) ⟨554903, by rfl⟩ : syracuseStep 739871 = 1109807) B1109807
theorem B9128659 : Blo 738327 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B740187 : Blo 738327 740187 := bstep (se 1 (by rfl) ⟨555140, by rfl⟩ : syracuseStep 740187 = 1110281) B1110281
theorem B740255 : Blo 738327 740255 := bstep (se 1 (by rfl) ⟨555191, by rfl⟩ : syracuseStep 740255 = 1110383) B1110383
theorem B740399 : Blo 738327 740399 := bstep (se 1 (by rfl) ⟨555299, by rfl⟩ : syracuseStep 740399 = 1110599) B1110599
theorem B740423 : Blo 738327 740423 := bstep (se 1 (by rfl) ⟨555317, by rfl⟩ : syracuseStep 740423 = 1110635) B1110635
theorem B740575 : Blo 738327 740575 := bstep (se 1 (by rfl) ⟨555431, by rfl⟩ : syracuseStep 740575 = 1110863) B1110863
theorem B1002719 : Blo 738327 1002719 := bstep (se 1 (by rfl) ⟨752039, by rfl⟩ : syracuseStep 1002719 = 1504079) B1504079
theorem B5328251 : Blo 738327 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B740839 : Blo 738327 740839 := bstep (se 1 (by rfl) ⟨555629, by rfl⟩ : syracuseStep 740839 = 1111259) B1111259
theorem B1330679 : Blo 738327 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B740955 : Blo 738327 740955 := bstep (se 1 (by rfl) ⟨555716, by rfl⟩ : syracuseStep 740955 = 1111433) B1111433
theorem B3559069 : Blo 738327 3559069 := bstep (se 3 (by rfl) ⟨667325, by rfl⟩ : syracuseStep 3559069 = 1334651) B1334651
theorem B4214531 : Blo 738327 4214531 := bstep (se 1 (by rfl) ⟨3160898, by rfl⟩ : syracuseStep 4214531 = 6321797) B6321797
theorem B1691431 : Blo 738327 1691431 := bstep (se 1 (by rfl) ⟨1268573, by rfl⟩ : syracuseStep 1691431 = 2537147) B2537147
theorem B741191 : Blo 738327 741191 := bstep (se 1 (by rfl) ⟨555893, by rfl⟩ : syracuseStep 741191 = 1111787) B1111787
theorem B7982995 : Blo 738327 7982995 := bstep (se 1 (by rfl) ⟨5987246, by rfl⟩ : syracuseStep 7982995 = 11974493) B11974493
theorem B741343 : Blo 738327 741343 := bstep (se 1 (by rfl) ⟨556007, by rfl⟩ : syracuseStep 741343 = 1112015) B1112015
theorem B741607 : Blo 738327 741607 := bstep (se 1 (by rfl) ⟨556205, by rfl⟩ : syracuseStep 741607 = 1112411) B1112411
theorem B22794533 : Blo 738327 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B741759 : Blo 738327 741759 := bstep (se 1 (by rfl) ⟨556319, by rfl⟩ : syracuseStep 741759 = 1112639) B1112639
theorem B2675111 : Blo 738327 2675111 := bstep (se 1 (by rfl) ⟨2006333, by rfl⟩ : syracuseStep 2675111 = 4012667) B4012667
theorem B741839 : Blo 738327 741839 := bstep (se 1 (by rfl) ⟨556379, by rfl⟩ : syracuseStep 741839 = 1112759) B1112759
theorem B741991 : Blo 738327 741991 := bstep (se 1 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 741991 = 1112987) B1112987
theorem B4510505 : Blo 738327 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B2806589 : Blo 738327 2806589 := bstep (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) B1052471
theorem B742255 : Blo 738327 742255 := bstep (se 1 (by rfl) ⟨556691, by rfl⟩ : syracuseStep 742255 = 1113383) B1113383
theorem B742311 : Blo 738327 742311 := bstep (se 1 (by rfl) ⟨556733, by rfl⟩ : syracuseStep 742311 = 1113467) B1113467
theorem B939215 : Blo 738327 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B3757265 : Blo 738327 3757265 := bstep (se 2 (by rfl) ⟨1408974, by rfl⟩ : syracuseStep 3757265 = 2817949) B2817949
theorem B19518907 : Blo 738327 19518907 := bstep (se 1 (by rfl) ⟨14639180, by rfl⟩ : syracuseStep 19518907 = 29278361) B29278361
theorem B7296983 : Blo 738327 7296983 := bstep (se 1 (by rfl) ⟨5472737, by rfl⟩ : syracuseStep 7296983 = 10945475) B10945475
theorem B18241631 : Blo 738327 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B10279111 : Blo 738327 10279111 := bstep (se 1 (by rfl) ⟨7709333, by rfl⟩ : syracuseStep 10279111 = 15418667) B15418667
theorem B4217129 : Blo 738327 4217129 := bstep (se 2 (by rfl) ⟨1581423, by rfl⟩ : syracuseStep 4217129 = 3162847) B3162847
theorem B3168553 : Blo 738327 3168553 := bstep (se 2 (by rfl) ⟨1188207, by rfl⟩ : syracuseStep 3168553 = 2376415) B2376415
theorem B9492947 : Blo 738327 9492947 := bstep (se 1 (by rfl) ⟨7119710, by rfl⟩ : syracuseStep 9492947 = 14239421) B14239421
theorem B1333865 : Blo 738327 1333865 := bstep (se 2 (by rfl) ⟨500199, by rfl⟩ : syracuseStep 1333865 = 1000399) B1000399
theorem B4873085 : Blo 738327 4873085 := bstep (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) B1827407
theorem B1661903 : Blo 738327 1661903 := bstep (se 1 (by rfl) ⟨1246427, by rfl⟩ : syracuseStep 1661903 = 2492855) B2492855
theorem B1661921 : Blo 738327 1661921 := bstep (se 2 (by rfl) ⟨623220, by rfl⟩ : syracuseStep 1661921 = 1246441) B1246441
theorem B1661993 : Blo 738327 1661993 := bstep (se 2 (by rfl) ⟨623247, by rfl⟩ : syracuseStep 1661993 = 1246495) B1246495
theorem B7691321 : Blo 738327 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B3169631 : Blo 738327 3169631 := bstep (se 1 (by rfl) ⟨2377223, by rfl⟩ : syracuseStep 3169631 = 4754447) B4754447
theorem B2809991 : Blo 738327 2809991 := bstep (se 1 (by rfl) ⟨2107493, by rfl⟩ : syracuseStep 2809991 = 4214987) B4214987
theorem B6742187 : Blo 738327 6742187 := bstep (se 1 (by rfl) ⟨5056640, by rfl⟩ : syracuseStep 6742187 = 10113281) B10113281
theorem B15196673 : Blo 738327 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B2810477 : Blo 738327 2810477 := bstep (se 3 (by rfl) ⟨526964, by rfl⟩ : syracuseStep 2810477 = 1053929) B1053929
theorem B9495407 : Blo 738327 9495407 := bstep (se 1 (by rfl) ⟨7121555, by rfl⟩ : syracuseStep 9495407 = 14243111) B14243111
theorem B8414117 : Blo 738327 8414117 := bstep (se 4 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 8414117 = 1577647) B1577647
theorem B1663955 : Blo 738327 1663955 := bstep (se 1 (by rfl) ⟨1247966, by rfl⟩ : syracuseStep 1663955 = 2495933) B2495933
theorem B1139707 : Blo 738327 1139707 := bstep (se 1 (by rfl) ⟨854780, by rfl⟩ : syracuseStep 1139707 = 1709561) B1709561
theorem B1664207 : Blo 738327 1664207 := bstep (se 1 (by rfl) ⟨1248155, by rfl⟩ : syracuseStep 1664207 = 2496311) B2496311
theorem B2024875 : Blo 738327 2024875 := bstep (se 1 (by rfl) ⟨1518656, by rfl⟩ : syracuseStep 2024875 = 3037313) B3037313
theorem B1664531 : Blo 738327 1664531 := bstep (se 1 (by rfl) ⟨1248398, by rfl⟩ : syracuseStep 1664531 = 2496797) B2496797
theorem B1107527 : Blo 738327 1107527 := bstep (se 1 (by rfl) ⟨830645, by rfl⟩ : syracuseStep 1107527 = 1661291) B1661291
theorem B31975033 : Blo 738327 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B1107623 : Blo 738327 1107623 := bstep (se 1 (by rfl) ⟨830717, by rfl⟩ : syracuseStep 1107623 = 1661435) B1661435
theorem B1402535 : Blo 738327 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B1107707 : Blo 738327 1107707 := bstep (se 1 (by rfl) ⟨830780, by rfl⟩ : syracuseStep 1107707 = 1661561) B1661561
theorem B1107743 : Blo 738327 1107743 := bstep (se 1 (by rfl) ⟨830807, by rfl⟩ : syracuseStep 1107743 = 1661615) B1661615
theorem B1107791 : Blo 738327 1107791 := bstep (se 1 (by rfl) ⟨830843, by rfl⟩ : syracuseStep 1107791 = 1661687) B1661687
theorem B1107911 : Blo 738327 1107911 := bstep (se 1 (by rfl) ⟨830933, by rfl⟩ : syracuseStep 1107911 = 1661867) B1661867
theorem B1665215 : Blo 738327 1665215 := bstep (se 1 (by rfl) ⟨1248911, by rfl⟩ : syracuseStep 1665215 = 2497823) B2497823
theorem B1108265 : Blo 738327 1108265 := bstep (se 2 (by rfl) ⟨415599, by rfl⟩ : syracuseStep 1108265 = 831199) B831199
theorem B1108271 : Blo 738327 1108271 := bstep (se 1 (by rfl) ⟨831203, by rfl⟩ : syracuseStep 1108271 = 1662407) B1662407
theorem B6416891 : Blo 738327 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B1108511 : Blo 738327 1108511 := bstep (se 1 (by rfl) ⟨831383, by rfl⟩ : syracuseStep 1108511 = 1662767) B1662767
theorem B4221503 : Blo 738327 4221503 := bstep (se 1 (by rfl) ⟨3166127, by rfl⟩ : syracuseStep 4221503 = 6332255) B6332255
theorem B4745911 : Blo 738327 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B3795767 : Blo 738327 3795767 := bstep (se 1 (by rfl) ⟨2846825, by rfl⟩ : syracuseStep 3795767 = 5693651) B5693651
theorem B1108895 : Blo 738327 1108895 := bstep (se 1 (by rfl) ⟨831671, by rfl⟩ : syracuseStep 1108895 = 1663343) B1663343
theorem B1108943 : Blo 738327 1108943 := bstep (se 1 (by rfl) ⟨831707, by rfl⟩ : syracuseStep 1108943 = 1663415) B1663415
theorem B2812907 : Blo 738327 2812907 := bstep (se 1 (by rfl) ⟨2109680, by rfl⟩ : syracuseStep 2812907 = 4219361) B4219361
theorem B1109033 : Blo 738327 1109033 := bstep (se 2 (by rfl) ⟨415887, by rfl⟩ : syracuseStep 1109033 = 831775) B831775
theorem B1109039 : Blo 738327 1109039 := bstep (se 1 (by rfl) ⟨831779, by rfl⟩ : syracuseStep 1109039 = 1663559) B1663559
theorem B1109063 : Blo 738327 1109063 := bstep (se 1 (by rfl) ⟨831797, by rfl⟩ : syracuseStep 1109063 = 1663595) B1663595
theorem B1666169 : Blo 738327 1666169 := bstep (se 2 (by rfl) ⟨624813, by rfl⟩ : syracuseStep 1666169 = 1249627) B1249627
theorem B1109327 : Blo 738327 1109327 := bstep (se 1 (by rfl) ⟨831995, by rfl⟩ : syracuseStep 1109327 = 1663991) B1663991
theorem B1109417 : Blo 738327 1109417 := bstep (se 2 (by rfl) ⟨416031, by rfl⟩ : syracuseStep 1109417 = 832063) B832063
theorem B1109567 : Blo 738327 1109567 := bstep (se 1 (by rfl) ⟨832175, by rfl⟩ : syracuseStep 1109567 = 1664351) B1664351
theorem B1404479 : Blo 738327 1404479 := bstep (se 1 (by rfl) ⟨1053359, by rfl⟩ : syracuseStep 1404479 = 2106719) B2106719
theorem B1666835 : Blo 738327 1666835 := bstep (se 1 (by rfl) ⟨1250126, by rfl⟩ : syracuseStep 1666835 = 2500253) B2500253
theorem B1109831 : Blo 738327 1109831 := bstep (se 1 (by rfl) ⟨832373, by rfl⟩ : syracuseStep 1109831 = 1664747) B1664747
theorem B1109915 : Blo 738327 1109915 := bstep (se 1 (by rfl) ⟨832436, by rfl⟩ : syracuseStep 1109915 = 1664873) B1664873
theorem B1667195 : Blo 738327 1667195 := bstep (se 1 (by rfl) ⟨1250396, by rfl⟩ : syracuseStep 1667195 = 2500793) B2500793
theorem B1667465 : Blo 738327 1667465 := bstep (se 2 (by rfl) ⟨625299, by rfl⟩ : syracuseStep 1667465 = 1250599) B1250599
theorem B1110479 : Blo 738327 1110479 := bstep (se 1 (by rfl) ⟨832859, by rfl⟩ : syracuseStep 1110479 = 1665719) B1665719
theorem B4223461 : Blo 738327 4223461 := bstep (se 4 (by rfl) ⟨395949, by rfl⟩ : syracuseStep 4223461 = 791899) B791899
theorem B1110521 : Blo 738327 1110521 := bstep (se 2 (by rfl) ⟨416445, by rfl⟩ : syracuseStep 1110521 = 832891) B832891
theorem B5337683 : Blo 738327 5337683 := bstep (se 1 (by rfl) ⟨4003262, by rfl⟩ : syracuseStep 5337683 = 8006525) B8006525
theorem B2814547 : Blo 738327 2814547 := bstep (se 1 (by rfl) ⟨2110910, by rfl⟩ : syracuseStep 2814547 = 4221821) B4221821
theorem B1110623 : Blo 738327 1110623 := bstep (se 1 (by rfl) ⟨832967, by rfl⟩ : syracuseStep 1110623 = 1665935) B1665935
theorem B4223735 : Blo 738327 4223735 := bstep (se 1 (by rfl) ⟨3167801, by rfl⟩ : syracuseStep 4223735 = 6335603) B6335603
theorem B8024993 : Blo 738327 8024993 := bstep (se 2 (by rfl) ⟨3009372, by rfl⟩ : syracuseStep 8024993 = 6018745) B6018745
theorem B1111103 : Blo 738327 1111103 := bstep (se 1 (by rfl) ⟨833327, by rfl⟩ : syracuseStep 1111103 = 1666655) B1666655
theorem B1111145 : Blo 738327 1111145 := bstep (se 2 (by rfl) ⟨416679, by rfl⟩ : syracuseStep 1111145 = 833359) B833359
theorem B1668203 : Blo 738327 1668203 := bstep (se 1 (by rfl) ⟨1251152, by rfl⟩ : syracuseStep 1668203 = 2502305) B2502305
theorem B1111247 : Blo 738327 1111247 := bstep (se 1 (by rfl) ⟨833435, by rfl⟩ : syracuseStep 1111247 = 1666871) B1666871
theorem B1111451 : Blo 738327 1111451 := bstep (se 1 (by rfl) ⟨833588, by rfl⟩ : syracuseStep 1111451 = 1667177) B1667177
theorem B1111673 : Blo 738327 1111673 := bstep (se 2 (by rfl) ⟨416877, by rfl⟩ : syracuseStep 1111673 = 833755) B833755
theorem B1668779 : Blo 738327 1668779 := bstep (se 1 (by rfl) ⟨1251584, by rfl⟩ : syracuseStep 1668779 = 2503169) B2503169
theorem B1111775 : Blo 738327 1111775 := bstep (se 1 (by rfl) ⟨833831, by rfl⟩ : syracuseStep 1111775 = 1667663) B1667663
theorem B2193209 : Blo 738327 2193209 := bstep (se 2 (by rfl) ⟨822453, by rfl⟩ : syracuseStep 2193209 = 1644907) B1644907
theorem B1111871 : Blo 738327 1111871 := bstep (se 1 (by rfl) ⟨833903, by rfl⟩ : syracuseStep 1111871 = 1667807) B1667807
theorem B1800073 : Blo 738327 1800073 := bstep (se 2 (by rfl) ⟨675027, by rfl⟩ : syracuseStep 1800073 = 1350055) B1350055
theorem B1112039 : Blo 738327 1112039 := bstep (se 1 (by rfl) ⟨834029, by rfl⟩ : syracuseStep 1112039 = 1668059) B1668059
theorem B1669103 : Blo 738327 1669103 := bstep (se 1 (by rfl) ⟨1251827, by rfl⟩ : syracuseStep 1669103 = 2503655) B2503655
theorem B1112057 : Blo 738327 1112057 := bstep (se 2 (by rfl) ⟨417021, by rfl⟩ : syracuseStep 1112057 = 834043) B834043
theorem B1112159 : Blo 738327 1112159 := bstep (se 1 (by rfl) ⟨834119, by rfl⟩ : syracuseStep 1112159 = 1668239) B1668239
theorem B1112219 : Blo 738327 1112219 := bstep (se 1 (by rfl) ⟨834164, by rfl⟩ : syracuseStep 1112219 = 1668329) B1668329
theorem B1112255 : Blo 738327 1112255 := bstep (se 1 (by rfl) ⟨834191, by rfl⟩ : syracuseStep 1112255 = 1668383) B1668383
theorem B1669319 : Blo 738327 1669319 := bstep (se 1 (by rfl) ⟨1251989, by rfl⟩ : syracuseStep 1669319 = 2503979) B2503979
theorem B1112297 : Blo 738327 1112297 := bstep (se 2 (by rfl) ⟨417111, by rfl⟩ : syracuseStep 1112297 = 834223) B834223
theorem B1669499 : Blo 738327 1669499 := bstep (se 1 (by rfl) ⟨1252124, by rfl⟩ : syracuseStep 1669499 = 2504249) B2504249
theorem B1112603 : Blo 738327 1112603 := bstep (se 1 (by rfl) ⟨834452, by rfl⟩ : syracuseStep 1112603 = 1668905) B1668905
theorem B1112681 : Blo 738327 1112681 := bstep (se 2 (by rfl) ⟨417255, by rfl⟩ : syracuseStep 1112681 = 834511) B834511
theorem B5634683 : Blo 738327 5634683 := bstep (se 1 (by rfl) ⟨4226012, by rfl⟩ : syracuseStep 5634683 = 8452025) B8452025
theorem B1669769 : Blo 738327 1669769 := bstep (se 2 (by rfl) ⟨626163, by rfl⟩ : syracuseStep 1669769 = 1252327) B1252327
theorem B19528613 : Blo 738327 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B1113209 : Blo 738327 1113209 := bstep (se 2 (by rfl) ⟨417453, by rfl⟩ : syracuseStep 1113209 = 834907) B834907
theorem B1113311 : Blo 738327 1113311 := bstep (se 1 (by rfl) ⟨834983, by rfl⟩ : syracuseStep 1113311 = 1669967) B1669967
theorem B1113353 : Blo 738327 1113353 := bstep (se 2 (by rfl) ⟨417507, by rfl⟩ : syracuseStep 1113353 = 835015) B835015
theorem B1408367 : Blo 738327 1408367 := bstep (se 1 (by rfl) ⟨1056275, by rfl⟩ : syracuseStep 1408367 = 2112551) B2112551
theorem B1113455 : Blo 738327 1113455 := bstep (se 1 (by rfl) ⟨835091, by rfl⟩ : syracuseStep 1113455 = 1670183) B1670183
theorem B1408603 : Blo 738327 1408603 := bstep (se 1 (by rfl) ⟨1056452, by rfl⟩ : syracuseStep 1408603 = 2112905) B2112905
theorem B4226651 : Blo 738327 4226651 := bstep (se 1 (by rfl) ⟨3169988, by rfl⟩ : syracuseStep 4226651 = 6339977) B6339977
theorem B4226903 : Blo 738327 4226903 := bstep (se 1 (by rfl) ⟨3170177, by rfl⟩ : syracuseStep 4226903 = 6340355) B6340355
theorem B1246151 : Blo 738327 1246151 := bstep (se 1 (by rfl) ⟨934613, by rfl⟩ : syracuseStep 1246151 = 1869227) B1869227
theorem B1247015 : Blo 738327 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B42633377 : Blo 738327 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B2492639 : Blo 738327 2492639 := bstep (se 1 (by rfl) ⟨1869479, by rfl⟩ : syracuseStep 2492639 = 3738959) B3738959
theorem B854299 : Blo 738327 854299 := bstep (se 1 (by rfl) ⟨640724, by rfl⟩ : syracuseStep 854299 = 1281449) B1281449
theorem B887119 : Blo 738327 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B1248041 : Blo 738327 1248041 := bstep (se 2 (by rfl) ⟨468015, by rfl⟩ : syracuseStep 1248041 = 936031) B936031
theorem B1248169 : Blo 738327 1248169 := bstep (se 2 (by rfl) ⟨468063, by rfl⟩ : syracuseStep 1248169 = 936127) B936127
theorem B1248311 : Blo 738327 1248311 := bstep (se 1 (by rfl) ⟨936233, by rfl⟩ : syracuseStep 1248311 = 1872467) B1872467
theorem B2493503 : Blo 738327 2493503 := bstep (se 1 (by rfl) ⟨1870127, by rfl⟩ : syracuseStep 2493503 = 3740255) B3740255
theorem B1871059 : Blo 738327 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B6327881 : Blo 738327 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B1248871 : Blo 738327 1248871 := bstep (se 1 (by rfl) ⟨936653, by rfl⟩ : syracuseStep 1248871 = 1873307) B1873307
theorem B54857411 : Blo 738327 54857411 := bstep (se 1 (by rfl) ⟨41143058, by rfl⟩ : syracuseStep 54857411 = 82286117) B82286117
theorem B12161087 : Blo 738327 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B1052767 : Blo 738327 1052767 := bstep (se 1 (by rfl) ⟨789575, by rfl⟩ : syracuseStep 1052767 = 1579151) B1579151
theorem B1052779 : Blo 738327 1052779 := bstep (se 1 (by rfl) ⟨789584, by rfl⟩ : syracuseStep 1052779 = 1579169) B1579169
theorem B6328631 : Blo 738327 6328631 := bstep (se 1 (by rfl) ⟨4746473, by rfl⟩ : syracuseStep 6328631 = 9492947) B9492947
theorem B3740093 : Blo 738327 3740093 := bstep (se 3 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 3740093 = 1402535) B1402535
theorem B3248723 : Blo 738327 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B1577819 : Blo 738327 1577819 := bstep (se 1 (by rfl) ⟨1183364, by rfl⟩ : syracuseStep 1577819 = 2366729) B2366729
theorem B791455 : Blo 738327 791455 := bstep (se 1 (by rfl) ⟨593591, by rfl⟩ : syracuseStep 791455 = 1187183) B1187183
theorem B1873327 : Blo 738327 1873327 := bstep (se 1 (by rfl) ⟨1404995, by rfl⟩ : syracuseStep 1873327 = 2809991) B2809991
theorem B4494791 : Blo 738327 4494791 := bstep (se 1 (by rfl) ⟨3371093, by rfl⟩ : syracuseStep 4494791 = 6742187) B6742187
theorem B6395441 : Blo 738327 6395441 := bstep (se 2 (by rfl) ⟨2398290, by rfl⟩ : syracuseStep 6395441 = 4796581) B4796581
theorem B10131115 : Blo 738327 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B1873651 : Blo 738327 1873651 := bstep (se 1 (by rfl) ⟨1405238, by rfl⟩ : syracuseStep 1873651 = 2810477) B2810477
theorem B1185607 : Blo 738327 1185607 := bstep (se 1 (by rfl) ⟨889205, by rfl⟩ : syracuseStep 1185607 = 1778411) B1778411
theorem B6330271 : Blo 738327 6330271 := bstep (se 1 (by rfl) ⟨4747703, by rfl⟩ : syracuseStep 6330271 = 9495407) B9495407
theorem B5609411 : Blo 738327 5609411 := bstep (se 1 (by rfl) ⟨4207058, by rfl⟩ : syracuseStep 5609411 = 8414117) B8414117
theorem B14260333 : Blo 738327 14260333 := bstep (se 3 (by rfl) ⟨2673812, by rfl⟩ : syracuseStep 14260333 = 5347625) B5347625
theorem B27400355 : Blo 738327 27400355 := bstep (se 1 (by rfl) ⟨20550266, by rfl⟩ : syracuseStep 27400355 = 41100533) B41100533
theorem B2497337 : Blo 738327 2497337 := bstep (se 2 (by rfl) ⟨936501, by rfl⟩ : syracuseStep 2497337 = 1873003) B1873003
theorem B1252219 : Blo 738327 1252219 := bstep (se 1 (by rfl) ⟨939164, by rfl⟩ : syracuseStep 1252219 = 1878329) B1878329
theorem B2530511 : Blo 738327 2530511 := bstep (se 1 (by rfl) ⟨1897883, by rfl⟩ : syracuseStep 2530511 = 3795767) B3795767
theorem B26025209 : Blo 738327 26025209 := bstep (se 2 (by rfl) ⟨9759453, by rfl⟩ : syracuseStep 26025209 = 19518907) B19518907
theorem B1875271 : Blo 738327 1875271 := bstep (se 1 (by rfl) ⟨1406453, by rfl⟩ : syracuseStep 1875271 = 2812907) B2812907
theorem B3154049 : Blo 738327 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B13705481 : Blo 738327 13705481 := bstep (se 2 (by rfl) ⟨5139555, by rfl⟩ : syracuseStep 13705481 = 10279111) B10279111
theorem B2499065 : Blo 738327 2499065 := bstep (se 2 (by rfl) ⟨937149, by rfl⟩ : syracuseStep 2499065 = 1874299) B1874299
theorem B5349995 : Blo 738327 5349995 := bstep (se 1 (by rfl) ⟨4012496, by rfl⟩ : syracuseStep 5349995 = 8024993) B8024993
theorem B2499335 : Blo 738327 2499335 := bstep (se 1 (by rfl) ⟨1874501, by rfl⟩ : syracuseStep 2499335 = 3749003) B3749003
theorem B1582355 : Blo 738327 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B3745277 : Blo 738327 3745277 := bstep (se 3 (by rfl) ⟨702239, by rfl⟩ : syracuseStep 3745277 = 1404479) B1404479
theorem B9020965 : Blo 738327 9020965 := bstep (se 4 (by rfl) ⟨845715, by rfl⟩ : syracuseStep 9020965 = 1691431) B1691431
theorem B2500415 : Blo 738327 2500415 := bstep (se 1 (by rfl) ⟨1875311, by rfl⟩ : syracuseStep 2500415 = 3750623) B3750623
theorem B1583039 : Blo 738327 1583039 := bstep (se 1 (by rfl) ⟨1187279, by rfl⟩ : syracuseStep 1583039 = 2374559) B2374559
theorem B13019075 : Blo 738327 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B1583201 : Blo 738327 1583201 := bstep (se 2 (by rfl) ⟨593700, by rfl⟩ : syracuseStep 1583201 = 1187401) B1187401
theorem B1878137 : Blo 738327 1878137 := bstep (se 2 (by rfl) ⟨704301, by rfl⟩ : syracuseStep 1878137 = 1408603) B1408603
theorem B3746087 : Blo 738327 3746087 := bstep (se 1 (by rfl) ⟨2809565, by rfl⟩ : syracuseStep 3746087 = 5619131) B5619131
theorem B2107721 : Blo 738327 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B8006215 : Blo 738327 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B27405047 : Blo 738327 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B1780487 : Blo 738327 1780487 := bstep (se 1 (by rfl) ⟨1335365, by rfl⟩ : syracuseStep 1780487 = 2670731) B2670731
theorem B5778383 : Blo 738327 5778383 := bstep (se 1 (by rfl) ⟨4333787, by rfl⟩ : syracuseStep 5778383 = 8667575) B8667575
theorem B2501927 : Blo 738327 2501927 := bstep (se 1 (by rfl) ⟨1876445, by rfl⟩ : syracuseStep 2501927 = 3752891) B3752891
theorem B3091751 : Blo 738327 3091751 := bstep (se 1 (by rfl) ⟨2318813, by rfl⟩ : syracuseStep 3091751 = 4637627) B4637627
theorem B7122329 : Blo 738327 7122329 := bstep (se 2 (by rfl) ⟨2670873, by rfl⟩ : syracuseStep 7122329 = 5341747) B5341747
theorem B830875 : Blo 738327 830875 := bstep (se 1 (by rfl) ⟨623156, by rfl⟩ : syracuseStep 830875 = 1246313) B1246313
theorem B2370971 : Blo 738327 2370971 := bstep (se 1 (by rfl) ⟨1778228, by rfl⟩ : syracuseStep 2370971 = 3556457) B3556457
theorem B23997883 : Blo 738327 23997883 := bstep (se 1 (by rfl) ⟨17998412, by rfl⟩ : syracuseStep 23997883 = 35996825) B35996825
theorem B4730687 : Blo 738327 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B1519609 : Blo 738327 1519609 := bstep (se 2 (by rfl) ⟨569853, by rfl⟩ : syracuseStep 1519609 = 1139707) B1139707
theorem B831847 : Blo 738327 831847 := bstep (se 1 (by rfl) ⟨623885, by rfl⟩ : syracuseStep 831847 = 1247771) B1247771
theorem B2699833 : Blo 738327 2699833 := bstep (se 2 (by rfl) ⟨1012437, by rfl⟩ : syracuseStep 2699833 = 2024875) B2024875
theorem B12202649 : Blo 738327 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B3552167 : Blo 738327 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B832495 : Blo 738327 832495 := bstep (se 1 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 832495 = 1248743) B1248743
theorem B6009851 : Blo 738327 6009851 := bstep (se 1 (by rfl) ⟨4507388, by rfl⟩ : syracuseStep 6009851 = 9014777) B9014777
theorem B832999 : Blo 738327 832999 := bstep (se 1 (by rfl) ⟨624749, by rfl⟩ : syracuseStep 832999 = 1249499) B1249499
theorem B833179 : Blo 738327 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B2537257 : Blo 738327 2537257 := bstep (se 2 (by rfl) ⟨951471, by rfl⟩ : syracuseStep 2537257 = 1902943) B1902943
theorem B2504573 : Blo 738327 2504573 := bstep (se 3 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 2504573 = 939215) B939215
theorem B5617673 : Blo 738327 5617673 := bstep (se 2 (by rfl) ⟨2106627, by rfl⟩ : syracuseStep 5617673 = 4213255) B4213255
theorem B3553321 : Blo 738327 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B4503691 : Blo 738327 4503691 := bstep (se 1 (by rfl) ⟨3377768, by rfl⟩ : syracuseStep 4503691 = 6755537) B6755537
theorem B2504843 : Blo 738327 2504843 := bstep (se 1 (by rfl) ⟨1878632, by rfl⟩ : syracuseStep 2504843 = 3757265) B3757265
theorem B16234775 : Blo 738327 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B12171545 : Blo 738327 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B6764957 : Blo 738327 6764957 := bstep (se 3 (by rfl) ⟨1268429, by rfl⟩ : syracuseStep 6764957 = 2536859) B2536859
theorem B4864655 : Blo 738327 4864655 := bstep (se 1 (by rfl) ⟨3648491, by rfl⟩ : syracuseStep 4864655 = 7296983) B7296983
theorem B6339293 : Blo 738327 6339293 := bstep (se 3 (by rfl) ⟨1188617, by rfl⟩ : syracuseStep 6339293 = 2377235) B2377235
theorem B5127547 : Blo 738327 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B2113087 : Blo 738327 2113087 := bstep (se 1 (by rfl) ⟨1584815, by rfl⟩ : syracuseStep 2113087 = 3169631) B3169631
theorem B3752729 : Blo 738327 3752729 := bstep (se 2 (by rfl) ⟨1407273, by rfl⟩ : syracuseStep 3752729 = 2814547) B2814547
theorem B738351 : Blo 738327 738351 := bstep (se 1 (by rfl) ⟨553763, by rfl⟩ : syracuseStep 738351 = 1107527) B1107527
theorem B738415 : Blo 738327 738415 := bstep (se 1 (by rfl) ⟨553811, by rfl⟩ : syracuseStep 738415 = 1107623) B1107623
theorem B738471 : Blo 738327 738471 := bstep (se 1 (by rfl) ⟨553853, by rfl⟩ : syracuseStep 738471 = 1107707) B1107707
theorem B738495 : Blo 738327 738495 := bstep (se 1 (by rfl) ⟨553871, by rfl⟩ : syracuseStep 738495 = 1107743) B1107743
theorem B738527 : Blo 738327 738527 := bstep (se 1 (by rfl) ⟨553895, by rfl⟩ : syracuseStep 738527 = 1107791) B1107791
theorem B7128323 : Blo 738327 7128323 := bstep (se 1 (by rfl) ⟨5346242, by rfl⟩ : syracuseStep 7128323 = 10692485) B10692485
theorem B738607 : Blo 738327 738607 := bstep (se 1 (by rfl) ⟨553955, by rfl⟩ : syracuseStep 738607 = 1107911) B1107911
theorem B738843 : Blo 738327 738843 := bstep (se 1 (by rfl) ⟨554132, by rfl⟩ : syracuseStep 738843 = 1108265) B1108265
theorem B738847 : Blo 738327 738847 := bstep (se 1 (by rfl) ⟨554135, by rfl⟩ : syracuseStep 738847 = 1108271) B1108271
theorem B3556973 : Blo 738327 3556973 := bstep (se 3 (by rfl) ⟨666932, by rfl⟩ : syracuseStep 3556973 = 1333865) B1333865
theorem B3163769 : Blo 738327 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B4277927 : Blo 738327 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B739007 : Blo 738327 739007 := bstep (se 1 (by rfl) ⟨554255, by rfl⟩ : syracuseStep 739007 = 1108511) B1108511
theorem B36095705 : Blo 738327 36095705 := bstep (se 2 (by rfl) ⟨13535889, by rfl⟩ : syracuseStep 36095705 = 27071779) B27071779
theorem B55428907 : Blo 738327 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B739263 : Blo 738327 739263 := bstep (se 1 (by rfl) ⟨554447, by rfl⟩ : syracuseStep 739263 = 1108895) B1108895
theorem B739295 : Blo 738327 739295 := bstep (se 1 (by rfl) ⟨554471, by rfl⟩ : syracuseStep 739295 = 1108943) B1108943
theorem B739355 : Blo 738327 739355 := bstep (se 1 (by rfl) ⟨554516, by rfl⟩ : syracuseStep 739355 = 1109033) B1109033
theorem B739359 : Blo 738327 739359 := bstep (se 1 (by rfl) ⟨554519, by rfl⟩ : syracuseStep 739359 = 1109039) B1109039
theorem B739375 : Blo 738327 739375 := bstep (se 1 (by rfl) ⟨554531, by rfl⟩ : syracuseStep 739375 = 1109063) B1109063
theorem B739551 : Blo 738327 739551 := bstep (se 1 (by rfl) ⟨554663, by rfl⟩ : syracuseStep 739551 = 1109327) B1109327
theorem B739611 : Blo 738327 739611 := bstep (se 1 (by rfl) ⟨554708, by rfl⟩ : syracuseStep 739611 = 1109417) B1109417
theorem B739711 : Blo 738327 739711 := bstep (se 1 (by rfl) ⟨554783, by rfl⟩ : syracuseStep 739711 = 1109567) B1109567
theorem B2804129 : Blo 738327 2804129 := bstep (se 2 (by rfl) ⟨1051548, by rfl⟩ : syracuseStep 2804129 = 2103097) B2103097
theorem B739887 : Blo 738327 739887 := bstep (se 1 (by rfl) ⟨554915, by rfl⟩ : syracuseStep 739887 = 1109831) B1109831
theorem B2804327 : Blo 738327 2804327 := bstep (se 1 (by rfl) ⟨2103245, by rfl⟩ : syracuseStep 2804327 = 4206491) B4206491
theorem B739943 : Blo 738327 739943 := bstep (se 1 (by rfl) ⟨554957, by rfl⟩ : syracuseStep 739943 = 1109915) B1109915
theorem B4213529 : Blo 738327 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B740319 : Blo 738327 740319 := bstep (se 1 (by rfl) ⟨555239, by rfl⟩ : syracuseStep 740319 = 1110479) B1110479
theorem B740347 : Blo 738327 740347 := bstep (se 1 (by rfl) ⟨555260, by rfl⟩ : syracuseStep 740347 = 1110521) B1110521
theorem B2247689 : Blo 738327 2247689 := bstep (se 2 (by rfl) ⟨842883, by rfl⟩ : syracuseStep 2247689 = 1685767) B1685767
theorem B3558455 : Blo 738327 3558455 := bstep (se 1 (by rfl) ⟨2668841, by rfl⟩ : syracuseStep 3558455 = 5337683) B5337683
theorem B740415 : Blo 738327 740415 := bstep (se 1 (by rfl) ⟨555311, by rfl⟩ : syracuseStep 740415 = 1110623) B1110623
theorem B2673917 : Blo 738327 2673917 := bstep (se 3 (by rfl) ⟨501359, by rfl⟩ : syracuseStep 2673917 = 1002719) B1002719
theorem B2805101 : Blo 738327 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B740735 : Blo 738327 740735 := bstep (se 1 (by rfl) ⟨555551, by rfl⟩ : syracuseStep 740735 = 1111103) B1111103
theorem B740763 : Blo 738327 740763 := bstep (se 1 (by rfl) ⟨555572, by rfl⟩ : syracuseStep 740763 = 1111145) B1111145
theorem B740831 : Blo 738327 740831 := bstep (se 1 (by rfl) ⟨555623, by rfl⟩ : syracuseStep 740831 = 1111247) B1111247
theorem B740967 : Blo 738327 740967 := bstep (se 1 (by rfl) ⟨555725, by rfl⟩ : syracuseStep 740967 = 1111451) B1111451
theorem B3755645 : Blo 738327 3755645 := bstep (se 3 (by rfl) ⟨704183, by rfl⟩ : syracuseStep 3755645 = 1408367) B1408367
theorem B741115 : Blo 738327 741115 := bstep (se 1 (by rfl) ⟨555836, by rfl⟩ : syracuseStep 741115 = 1111673) B1111673
theorem B741183 : Blo 738327 741183 := bstep (se 1 (by rfl) ⟨555887, by rfl⟩ : syracuseStep 741183 = 1111775) B1111775
theorem B1462139 : Blo 738327 1462139 := bstep (se 1 (by rfl) ⟨1096604, by rfl⟩ : syracuseStep 1462139 = 2193209) B2193209
theorem B741247 : Blo 738327 741247 := bstep (se 1 (by rfl) ⟨555935, by rfl⟩ : syracuseStep 741247 = 1111871) B1111871
theorem B11980781 : Blo 738327 11980781 := bstep (se 3 (by rfl) ⟨2246396, by rfl⟩ : syracuseStep 11980781 = 4492793) B4492793
theorem B741359 : Blo 738327 741359 := bstep (se 1 (by rfl) ⟨556019, by rfl⟩ : syracuseStep 741359 = 1112039) B1112039
theorem B741371 : Blo 738327 741371 := bstep (se 1 (by rfl) ⟨556028, by rfl⟩ : syracuseStep 741371 = 1112057) B1112057
theorem B2805799 : Blo 738327 2805799 := bstep (se 1 (by rfl) ⟨2104349, by rfl⟩ : syracuseStep 2805799 = 4208699) B4208699
theorem B741439 : Blo 738327 741439 := bstep (se 1 (by rfl) ⟨556079, by rfl⟩ : syracuseStep 741439 = 1112159) B1112159
theorem B741479 : Blo 738327 741479 := bstep (se 1 (by rfl) ⟨556109, by rfl⟩ : syracuseStep 741479 = 1112219) B1112219
theorem B741503 : Blo 738327 741503 := bstep (se 1 (by rfl) ⟨556127, by rfl⟩ : syracuseStep 741503 = 1112255) B1112255
theorem B741531 : Blo 738327 741531 := bstep (se 1 (by rfl) ⟨556148, by rfl⟩ : syracuseStep 741531 = 1112297) B1112297
theorem B12636485 : Blo 738327 12636485 := bstep (se 4 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 12636485 = 2369341) B2369341
theorem B741735 : Blo 738327 741735 := bstep (se 1 (by rfl) ⟨556301, by rfl⟩ : syracuseStep 741735 = 1112603) B1112603
theorem B741787 : Blo 738327 741787 := bstep (se 1 (by rfl) ⟨556340, by rfl⟩ : syracuseStep 741787 = 1112681) B1112681
theorem B3756455 : Blo 738327 3756455 := bstep (se 1 (by rfl) ⟨2817341, by rfl⟩ : syracuseStep 3756455 = 5634683) B5634683
theorem B742139 : Blo 738327 742139 := bstep (se 1 (by rfl) ⟨556604, by rfl⟩ : syracuseStep 742139 = 1113209) B1113209
theorem B742207 : Blo 738327 742207 := bstep (se 1 (by rfl) ⟨556655, by rfl⟩ : syracuseStep 742207 = 1113311) B1113311
theorem B742235 : Blo 738327 742235 := bstep (se 1 (by rfl) ⟨556676, by rfl⟩ : syracuseStep 742235 = 1113353) B1113353
theorem B742303 : Blo 738327 742303 := bstep (se 1 (by rfl) ⟨556727, by rfl⟩ : syracuseStep 742303 = 1113455) B1113455
theorem B2806771 : Blo 738327 2806771 := bstep (se 1 (by rfl) ⟨2105078, by rfl⟩ : syracuseStep 2806771 = 4210157) B4210157
theorem B42751475 : Blo 738327 42751475 := bstep (se 1 (by rfl) ⟨32063606, by rfl⟩ : syracuseStep 42751475 = 64127213) B64127213
theorem B2807531 : Blo 738327 2807531 := bstep (se 1 (by rfl) ⟨2105648, by rfl⟩ : syracuseStep 2807531 = 4211297) B4211297
theorem B7198541 : Blo 738327 7198541 := bstep (se 3 (by rfl) ⟨1349726, by rfl⟩ : syracuseStep 7198541 = 2699453) B2699453
theorem B1497079 : Blo 738327 1497079 := bstep (se 1 (by rfl) ⟨1122809, by rfl⟩ : syracuseStep 1497079 = 2245619) B2245619
theorem B1661345 : Blo 738327 1661345 := bstep (se 2 (by rfl) ⟨623004, by rfl⟩ : syracuseStep 1661345 = 1246009) B1246009
theorem B7133629 : Blo 738327 7133629 := bstep (se 3 (by rfl) ⟨1337555, by rfl⟩ : syracuseStep 7133629 = 2675111) B2675111
theorem B1661417 : Blo 738327 1661417 := bstep (se 2 (by rfl) ⟨623031, by rfl⟩ : syracuseStep 1661417 = 1246063) B1246063
theorem B3169783 : Blo 738327 3169783 := bstep (se 1 (by rfl) ⟨2377337, by rfl⟩ : syracuseStep 3169783 = 4754675) B4754675
theorem B2809687 : Blo 738327 2809687 := bstep (se 1 (by rfl) ⟨2107265, by rfl⟩ : syracuseStep 2809687 = 4214531) B4214531
theorem B1662875 : Blo 738327 1662875 := bstep (se 1 (by rfl) ⟨1247156, by rfl⟩ : syracuseStep 1662875 = 2494313) B2494313
theorem B15196355 : Blo 738327 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B1663289 : Blo 738327 1663289 := bstep (se 2 (by rfl) ⟨623733, by rfl⟩ : syracuseStep 1663289 = 1247467) B1247467
theorem B3007003 : Blo 738327 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B4743809 : Blo 738327 4743809 := bstep (se 2 (by rfl) ⟨1778928, by rfl⟩ : syracuseStep 4743809 = 3557857) B3557857
theorem B1663775 : Blo 738327 1663775 := bstep (se 1 (by rfl) ⟨1247831, by rfl⟩ : syracuseStep 1663775 = 2495663) B2495663
theorem B3564971 : Blo 738327 3564971 := bstep (se 1 (by rfl) ⟨2673728, by rfl⟩ : syracuseStep 3564971 = 5347457) B5347457
theorem B2811419 : Blo 738327 2811419 := bstep (se 1 (by rfl) ⟨2108564, by rfl⟩ : syracuseStep 2811419 = 4217129) B4217129
theorem B1664585 : Blo 738327 1664585 := bstep (se 2 (by rfl) ⟨624219, by rfl⟩ : syracuseStep 1664585 = 1248439) B1248439
theorem B1402687 : Blo 738327 1402687 := bstep (se 1 (by rfl) ⟨1052015, by rfl⟩ : syracuseStep 1402687 = 2104031) B2104031
theorem B1107935 : Blo 738327 1107935 := bstep (se 1 (by rfl) ⟨830951, by rfl⟩ : syracuseStep 1107935 = 1661903) B1661903
theorem B1107947 : Blo 738327 1107947 := bstep (se 1 (by rfl) ⟨830960, by rfl⟩ : syracuseStep 1107947 = 1661921) B1661921
theorem B1665017 : Blo 738327 1665017 := bstep (se 2 (by rfl) ⟨624381, by rfl⟩ : syracuseStep 1665017 = 1248763) B1248763
theorem B1107995 : Blo 738327 1107995 := bstep (se 1 (by rfl) ⟨830996, by rfl⟩ : syracuseStep 1107995 = 1661993) B1661993
theorem B1665071 : Blo 738327 1665071 := bstep (se 1 (by rfl) ⟨1248803, by rfl⟩ : syracuseStep 1665071 = 2497607) B2497607
theorem B1665107 : Blo 738327 1665107 := bstep (se 1 (by rfl) ⟨1248830, by rfl⟩ : syracuseStep 1665107 = 2497661) B2497661
theorem B5400695 : Blo 738327 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B4221071 : Blo 738327 4221071 := bstep (se 1 (by rfl) ⟨3165803, by rfl⟩ : syracuseStep 4221071 = 6331607) B6331607
theorem B4745425 : Blo 738327 4745425 := bstep (se 2 (by rfl) ⟨1779534, by rfl⟩ : syracuseStep 4745425 = 3559069) B3559069
theorem B1665287 : Blo 738327 1665287 := bstep (se 1 (by rfl) ⟨1248965, by rfl⟩ : syracuseStep 1665287 = 2497931) B2497931
theorem B1108361 : Blo 738327 1108361 := bstep (se 2 (by rfl) ⟨415635, by rfl⟩ : syracuseStep 1108361 = 831271) B831271
theorem B10643993 : Blo 738327 10643993 := bstep (se 2 (by rfl) ⟨3991497, by rfl⟩ : syracuseStep 10643993 = 7982995) B7982995
theorem B1665593 : Blo 738327 1665593 := bstep (se 2 (by rfl) ⟨624597, by rfl⟩ : syracuseStep 1665593 = 1249195) B1249195
theorem B1666313 : Blo 738327 1666313 := bstep (se 2 (by rfl) ⟨624867, by rfl⟩ : syracuseStep 1666313 = 1249735) B1249735
theorem B5631281 : Blo 738327 5631281 := bstep (se 2 (by rfl) ⟨2111730, by rfl⟩ : syracuseStep 5631281 = 4223461) B4223461
theorem B1109303 : Blo 738327 1109303 := bstep (se 1 (by rfl) ⟨831977, by rfl⟩ : syracuseStep 1109303 = 1663955) B1663955
theorem B1109471 : Blo 738327 1109471 := bstep (se 1 (by rfl) ⟨832103, by rfl⟩ : syracuseStep 1109471 = 1664207) B1664207
theorem B1109687 : Blo 738327 1109687 := bstep (se 1 (by rfl) ⟨832265, by rfl⟩ : syracuseStep 1109687 = 1664531) B1664531
theorem B1109897 : Blo 738327 1109897 := bstep (se 2 (by rfl) ⟨416211, by rfl⟩ : syracuseStep 1109897 = 832423) B832423
theorem B7303085 : Blo 738327 7303085 := bstep (se 3 (by rfl) ⟨1369328, by rfl⟩ : syracuseStep 7303085 = 2738657) B2738657
theorem B1110143 : Blo 738327 1110143 := bstep (se 1 (by rfl) ⟨832607, by rfl⟩ : syracuseStep 1110143 = 1665215) B1665215
theorem B1667303 : Blo 738327 1667303 := bstep (se 1 (by rfl) ⟨1250477, by rfl⟩ : syracuseStep 1667303 = 2500955) B2500955
theorem B2814335 : Blo 738327 2814335 := bstep (se 1 (by rfl) ⟨2110751, by rfl⟩ : syracuseStep 2814335 = 4221503) B4221503
theorem B1667483 : Blo 738327 1667483 := bstep (se 1 (by rfl) ⟨1250612, by rfl⟩ : syracuseStep 1667483 = 2501225) B2501225
theorem B1602283 : Blo 738327 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1110779 : Blo 738327 1110779 := bstep (se 1 (by rfl) ⟨833084, by rfl⟩ : syracuseStep 1110779 = 1666169) B1666169
theorem B9466703 : Blo 738327 9466703 := bstep (se 1 (by rfl) ⟨7100027, by rfl⟩ : syracuseStep 9466703 = 14200055) B14200055
theorem B1405907 : Blo 738327 1405907 := bstep (se 1 (by rfl) ⟨1054430, by rfl⟩ : syracuseStep 1405907 = 2108861) B2108861
theorem B1668167 : Blo 738327 1668167 := bstep (se 1 (by rfl) ⟨1251125, by rfl⟩ : syracuseStep 1668167 = 2502251) B2502251
theorem B1406135 : Blo 738327 1406135 := bstep (se 1 (by rfl) ⟨1054601, by rfl⟩ : syracuseStep 1406135 = 2109203) B2109203
theorem B1111223 : Blo 738327 1111223 := bstep (se 1 (by rfl) ⟨833417, by rfl⟩ : syracuseStep 1111223 = 1666835) B1666835
theorem B1668347 : Blo 738327 1668347 := bstep (se 1 (by rfl) ⟨1251260, by rfl⟩ : syracuseStep 1668347 = 2502521) B2502521
theorem B7107871 : Blo 738327 7107871 := bstep (se 1 (by rfl) ⟨5330903, by rfl⟩ : syracuseStep 7107871 = 10661807) B10661807
theorem B5338399 : Blo 738327 5338399 := bstep (se 1 (by rfl) ⟨4003799, by rfl⟩ : syracuseStep 5338399 = 8007599) B8007599
theorem B1111463 : Blo 738327 1111463 := bstep (se 1 (by rfl) ⟨833597, by rfl⟩ : syracuseStep 1111463 = 1667195) B1667195
theorem B1668563 : Blo 738327 1668563 := bstep (se 1 (by rfl) ⟨1251422, by rfl⟩ : syracuseStep 1668563 = 2502845) B2502845
theorem B947803 : Blo 738327 947803 := bstep (se 1 (by rfl) ⟨710852, by rfl⟩ : syracuseStep 947803 = 1421705) B1421705
theorem B1111643 : Blo 738327 1111643 := bstep (se 1 (by rfl) ⟨833732, by rfl⟩ : syracuseStep 1111643 = 1667465) B1667465
theorem B1406575 : Blo 738327 1406575 := bstep (se 1 (by rfl) ⟨1054931, by rfl⟩ : syracuseStep 1406575 = 2109863) B2109863
theorem B1668833 : Blo 738327 1668833 := bstep (se 2 (by rfl) ⟨625812, by rfl⟩ : syracuseStep 1668833 = 1251625) B1251625
theorem B4224737 : Blo 738327 4224737 := bstep (se 2 (by rfl) ⟨1584276, by rfl⟩ : syracuseStep 4224737 = 3168553) B3168553
theorem B2815823 : Blo 738327 2815823 := bstep (se 1 (by rfl) ⟨2111867, by rfl⟩ : syracuseStep 2815823 = 4223735) B4223735
theorem B1112105 : Blo 738327 1112105 := bstep (se 2 (by rfl) ⟨417039, by rfl⟩ : syracuseStep 1112105 = 834079) B834079
theorem B1112135 : Blo 738327 1112135 := bstep (se 1 (by rfl) ⟨834101, by rfl⟩ : syracuseStep 1112135 = 1668203) B1668203
theorem B1669355 : Blo 738327 1669355 := bstep (se 1 (by rfl) ⟨1252016, by rfl⟩ : syracuseStep 1669355 = 2504033) B2504033
theorem B1112519 : Blo 738327 1112519 := bstep (se 1 (by rfl) ⟨834389, by rfl⟩ : syracuseStep 1112519 = 1668779) B1668779
theorem B1407593 : Blo 738327 1407593 := bstep (se 2 (by rfl) ⟨527847, by rfl⟩ : syracuseStep 1407593 = 1055695) B1055695
theorem B1407631 : Blo 738327 1407631 := bstep (se 1 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 1407631 = 2111447) B2111447
theorem B1112735 : Blo 738327 1112735 := bstep (se 1 (by rfl) ⟨834551, by rfl⟩ : syracuseStep 1112735 = 1669103) B1669103
theorem B1112879 : Blo 738327 1112879 := bstep (se 1 (by rfl) ⟨834659, by rfl⟩ : syracuseStep 1112879 = 1669319) B1669319
theorem B1112999 : Blo 738327 1112999 := bstep (se 1 (by rfl) ⟨834749, by rfl⟩ : syracuseStep 1112999 = 1669499) B1669499
theorem B1113179 : Blo 738327 1113179 := bstep (se 1 (by rfl) ⟨834884, by rfl⟩ : syracuseStep 1113179 = 1669769) B1669769
theorem B9600389 : Blo 738327 9600389 := bstep (se 4 (by rfl) ⟨900036, by rfl⟩ : syracuseStep 9600389 = 1800073) B1800073
theorem B949711 : Blo 738327 949711 := bstep (se 1 (by rfl) ⟨712283, by rfl⟩ : syracuseStep 949711 = 1424567) B1424567
theorem B2817767 : Blo 738327 2817767 := bstep (se 1 (by rfl) ⟨2113325, by rfl⟩ : syracuseStep 2817767 = 4226651) B4226651
theorem B2817935 : Blo 738327 2817935 := bstep (se 1 (by rfl) ⟨2113451, by rfl⟩ : syracuseStep 2817935 = 4226903) B4226903
theorem B24019685 : Blo 738327 24019685 := bstep (se 4 (by rfl) ⟨2251845, by rfl⟩ : syracuseStep 24019685 = 4503691) B4503691
theorem B4752215 : Blo 738327 4752215 := bstep (se 1 (by rfl) ⟨3564161, by rfl⟩ : syracuseStep 4752215 = 7128323) B7128323
theorem B2851951 : Blo 738327 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B1869419 : Blo 738327 1869419 := bstep (se 1 (by rfl) ⟨1402064, by rfl⟩ : syracuseStep 1869419 = 2804129) B2804129
theorem B1869551 : Blo 738327 1869551 := bstep (se 1 (by rfl) ⟨1402163, by rfl⟩ : syracuseStep 1869551 = 2804327) B2804327
theorem B12027953 : Blo 738327 12027953 := bstep (se 2 (by rfl) ⟨4510482, by rfl⟩ : syracuseStep 12027953 = 9020965) B9020965
theorem B1870067 : Blo 738327 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B1870249 : Blo 738327 1870249 := bstep (se 2 (by rfl) ⟨701343, by rfl⟩ : syracuseStep 1870249 = 1402687) B1402687
theorem B36571607 : Blo 738327 36571607 := bstep (se 1 (by rfl) ⟨27428705, by rfl⟩ : syracuseStep 36571607 = 54857411) B54857411
theorem B8424323 : Blo 738327 8424323 := bstep (se 1 (by rfl) ⟨6318242, by rfl⟩ : syracuseStep 8424323 = 12636485) B12636485
theorem B6327233 : Blo 738327 6327233 := bstep (se 2 (by rfl) ⟨2372712, by rfl⟩ : syracuseStep 6327233 = 4745425) B4745425
theorem B2493395 : Blo 738327 2493395 := bstep (se 1 (by rfl) ⟨1870046, by rfl⟩ : syracuseStep 2493395 = 3740093) B3740093
theorem B2165815 : Blo 738327 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B1051879 : Blo 738327 1051879 := bstep (se 1 (by rfl) ⟨788909, by rfl⟩ : syracuseStep 1051879 = 1577819) B1577819
theorem B1871687 : Blo 738327 1871687 := bstep (se 1 (by rfl) ⟨1403765, by rfl⟩ : syracuseStep 1871687 = 2807531) B2807531
theorem B3739607 : Blo 738327 3739607 := bstep (se 1 (by rfl) ⟨2804705, by rfl⟩ : syracuseStep 3739607 = 5609411) B5609411
theorem B2494745 : Blo 738327 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B3741065 : Blo 738327 3741065 := bstep (se 2 (by rfl) ⟨1402899, by rfl⟩ : syracuseStep 3741065 = 2805799) B2805799
theorem B2102699 : Blo 738327 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B10130903 : Blo 738327 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B2136377 : Blo 738327 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B2496851 : Blo 738327 2496851 := bstep (se 1 (by rfl) ⟨1872638, by rfl⟩ : syracuseStep 2496851 = 3745277) B3745277
theorem B1874279 : Blo 738327 1874279 := bstep (se 1 (by rfl) ⟨1405709, by rfl⟩ : syracuseStep 1874279 = 2811419) B2811419
theorem B1055273 : Blo 738327 1055273 := bstep (se 2 (by rfl) ⟨395727, by rfl⟩ : syracuseStep 1055273 = 791455) B791455
theorem B1055359 : Blo 738327 1055359 := bstep (se 1 (by rfl) ⟨791519, by rfl⟩ : syracuseStep 1055359 = 1583039) B1583039
theorem B3742361 : Blo 738327 3742361 := bstep (se 2 (by rfl) ⟨1403385, by rfl⟩ : syracuseStep 3742361 = 2806771) B2806771
theorem B1055467 : Blo 738327 1055467 := bstep (se 1 (by rfl) ⟨791600, by rfl⟩ : syracuseStep 1055467 = 1583201) B1583201
theorem B1252091 : Blo 738327 1252091 := bstep (se 1 (by rfl) ⟨939068, by rfl⟩ : syracuseStep 1252091 = 1878137) B1878137
theorem B2497391 : Blo 738327 2497391 := bstep (se 1 (by rfl) ⟨1873043, by rfl⟩ : syracuseStep 2497391 = 3746087) B3746087
theorem B9477161 : Blo 738327 9477161 := bstep (se 2 (by rfl) ⟨3553935, by rfl⟩ : syracuseStep 9477161 = 7107871) B7107871
theorem B7117865 : Blo 738327 7117865 := bstep (se 2 (by rfl) ⟨2669199, by rfl⟩ : syracuseStep 7117865 = 5338399) B5338399
theorem B1186991 : Blo 738327 1186991 := bstep (se 1 (by rfl) ⟨890243, by rfl⟩ : syracuseStep 1186991 = 1780487) B1780487
theorem B2497769 : Blo 738327 2497769 := bstep (se 2 (by rfl) ⟨936663, by rfl⟩ : syracuseStep 2497769 = 1873327) B1873327
theorem B1875433 : Blo 738327 1875433 := bstep (se 2 (by rfl) ⟨703287, by rfl⟩ : syracuseStep 1875433 = 1406575) B1406575
theorem B13508153 : Blo 738327 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B1580647 : Blo 738327 1580647 := bstep (se 1 (by rfl) ⟨1185485, by rfl⟩ : syracuseStep 1580647 = 2370971) B2370971
theorem B2498201 : Blo 738327 2498201 := bstep (se 2 (by rfl) ⟨936825, by rfl⟩ : syracuseStep 2498201 = 1873651) B1873651
theorem B3383009 : Blo 738327 3383009 := bstep (se 2 (by rfl) ⟨1268628, by rfl⟩ : syracuseStep 3383009 = 2537257) B2537257
theorem B1580809 : Blo 738327 1580809 := bstep (se 2 (by rfl) ⟨592803, by rfl⟩ : syracuseStep 1580809 = 1185607) B1185607
theorem B3153791 : Blo 738327 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B19013777 : Blo 738327 19013777 := bstep (se 2 (by rfl) ⟨7130166, by rfl⟩ : syracuseStep 19013777 = 14260333) B14260333
theorem B1876223 : Blo 738327 1876223 := bstep (se 1 (by rfl) ⟨1407167, by rfl⟩ : syracuseStep 1876223 = 2814335) B2814335
theorem B8135099 : Blo 738327 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B9511505 : Blo 738327 9511505 := bstep (se 2 (by rfl) ⟨3566814, by rfl⟩ : syracuseStep 9511505 = 7133629) B7133629
theorem B2368111 : Blo 738327 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B4006567 : Blo 738327 4006567 := bstep (se 1 (by rfl) ⟨3004925, by rfl⟩ : syracuseStep 4006567 = 6009851) B6009851
theorem B1876841 : Blo 738327 1876841 := bstep (se 2 (by rfl) ⟨703815, by rfl⟩ : syracuseStep 1876841 = 1407631) B1407631
theorem B1877215 : Blo 738327 1877215 := bstep (se 1 (by rfl) ⟨1407911, by rfl⟩ : syracuseStep 1877215 = 2815823) B2815823
theorem B3745115 : Blo 738327 3745115 := bstep (se 1 (by rfl) ⟨2808836, by rfl⟩ : syracuseStep 3745115 = 5617673) B5617673
theorem B10823183 : Blo 738327 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B2500361 : Blo 738327 2500361 := bstep (se 2 (by rfl) ⟨937635, by rfl⟩ : syracuseStep 2500361 = 1875271) B1875271
theorem B77899573 : Blo 738327 77899573 := bstep (se 5 (by rfl) ⟨3651542, by rfl⟩ : syracuseStep 77899573 = 7303085) B7303085
theorem B6400259 : Blo 738327 6400259 := bstep (se 1 (by rfl) ⟨4800194, by rfl⟩ : syracuseStep 6400259 = 9600389) B9600389
theorem B3746249 : Blo 738327 3746249 := bstep (se 2 (by rfl) ⟨1404843, by rfl⟩ : syracuseStep 3746249 = 2809687) B2809687
theorem B1878511 : Blo 738327 1878511 := bstep (se 1 (by rfl) ⟨1408883, by rfl⟩ : syracuseStep 1878511 = 2817767) B2817767
theorem B1878623 : Blo 738327 1878623 := bstep (se 1 (by rfl) ⟨1408967, by rfl⟩ : syracuseStep 1878623 = 2817935) B2817935
theorem B5614757 : Blo 738327 5614757 := bstep (se 4 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 5614757 = 1052767) B1052767
theorem B2501819 : Blo 738327 2501819 := bstep (se 1 (by rfl) ⟨1876364, by rfl⟩ : syracuseStep 2501819 = 3752729) B3752729
theorem B830767 : Blo 738327 830767 := bstep (se 1 (by rfl) ⟨623075, by rfl⟩ : syracuseStep 830767 = 1246151) B1246151
theorem B36547949 : Blo 738327 36547949 := bstep (se 3 (by rfl) ⟨6852740, by rfl⟩ : syracuseStep 36547949 = 13705481) B13705481
theorem B4009337 : Blo 738327 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B2109179 : Blo 738327 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B24063803 : Blo 738327 24063803 := bstep (se 1 (by rfl) ⟨18047852, by rfl⟩ : syracuseStep 24063803 = 36095705) B36095705
theorem B831343 : Blo 738327 831343 := bstep (se 1 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 831343 = 1247015) B1247015
theorem B28422251 : Blo 738327 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B4731301 : Blo 738327 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B832027 : Blo 738327 832027 := bstep (se 1 (by rfl) ⟨624020, by rfl⟩ : syracuseStep 832027 = 1248041) B1248041
theorem B832207 : Blo 738327 832207 := bstep (se 1 (by rfl) ⟨624155, by rfl⟩ : syracuseStep 832207 = 1248311) B1248311
theorem B2372303 : Blo 738327 2372303 := bstep (se 1 (by rfl) ⟨1779227, by rfl⟩ : syracuseStep 2372303 = 3558455) B3558455
theorem B1782611 : Blo 738327 1782611 := bstep (se 1 (by rfl) ⟨1336958, by rfl⟩ : syracuseStep 1782611 = 2673917) B2673917
theorem B73905209 : Blo 738327 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B2503763 : Blo 738327 2503763 := bstep (se 1 (by rfl) ⟨1877822, by rfl⟩ : syracuseStep 2503763 = 3755645) B3755645
theorem B8107391 : Blo 738327 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B2504303 : Blo 738327 2504303 := bstep (se 1 (by rfl) ⟨1878227, by rfl⟩ : syracuseStep 2504303 = 3756455) B3756455
theorem B2996527 : Blo 738327 2996527 := bstep (se 1 (by rfl) ⟨2247395, by rfl⟩ : syracuseStep 2996527 = 4494791) B4494791
theorem B4799027 : Blo 738327 4799027 := bstep (se 1 (by rfl) ⟨3599270, by rfl⟩ : syracuseStep 4799027 = 7198541) B7198541
theorem B18266903 : Blo 738327 18266903 := bstep (se 1 (by rfl) ⟨13700177, by rfl⟩ : syracuseStep 18266903 = 27400355) B27400355
theorem B17054509 : Blo 738327 17054509 := bstep (se 3 (by rfl) ⟨3197720, by rfl⟩ : syracuseStep 17054509 = 6395441) B6395441
theorem B9485261 : Blo 738327 9485261 := bstep (se 3 (by rfl) ⟨1778486, by rfl⟩ : syracuseStep 9485261 = 3556973) B3556973
theorem B31997177 : Blo 738327 31997177 := bstep (se 2 (by rfl) ⟨11998941, by rfl⟩ : syracuseStep 31997177 = 23997883) B23997883
theorem B1687007 : Blo 738327 1687007 := bstep (se 1 (by rfl) ⟨1265255, by rfl⟩ : syracuseStep 1687007 = 2530511) B2530511
theorem B17350139 : Blo 738327 17350139 := bstep (se 1 (by rfl) ⟨13012604, by rfl⟩ : syracuseStep 17350139 = 26025209) B26025209
theorem B3162539 : Blo 738327 3162539 := bstep (se 1 (by rfl) ⟨2371904, by rfl⟩ : syracuseStep 3162539 = 4743809) B4743809
theorem B5620589 : Blo 738327 5620589 := bstep (se 3 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 5620589 = 2107721) B2107721
theorem B2376647 : Blo 738327 2376647 := bstep (se 1 (by rfl) ⟨1782485, by rfl⟩ : syracuseStep 2376647 = 3564971) B3564971
theorem B738623 : Blo 738327 738623 := bstep (se 1 (by rfl) ⟨553967, by rfl⟩ : syracuseStep 738623 = 1107935) B1107935
theorem B738631 : Blo 738327 738631 := bstep (se 1 (by rfl) ⟨553973, by rfl⟩ : syracuseStep 738631 = 1107947) B1107947
theorem B738663 : Blo 738327 738663 := bstep (se 1 (by rfl) ⟨553997, by rfl⟩ : syracuseStep 738663 = 1107995) B1107995
theorem B738907 : Blo 738327 738907 := bstep (se 1 (by rfl) ⟨554180, by rfl⟩ : syracuseStep 738907 = 1108361) B1108361
theorem B7095995 : Blo 738327 7095995 := bstep (se 1 (by rfl) ⟨5321996, by rfl⟩ : syracuseStep 7095995 = 10643993) B10643993
theorem B18270031 : Blo 738327 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B1263737 : Blo 738327 1263737 := bstep (se 2 (by rfl) ⟨473901, by rfl⟩ : syracuseStep 1263737 = 947803) B947803
theorem B3754187 : Blo 738327 3754187 := bstep (se 1 (by rfl) ⟨2815640, by rfl⟩ : syracuseStep 3754187 = 5631281) B5631281
theorem B739535 : Blo 738327 739535 := bstep (se 1 (by rfl) ⟨554651, by rfl⟩ : syracuseStep 739535 = 1109303) B1109303
theorem B739647 : Blo 738327 739647 := bstep (se 1 (by rfl) ⟨554735, by rfl⟩ : syracuseStep 739647 = 1109471) B1109471
theorem B739791 : Blo 738327 739791 := bstep (se 1 (by rfl) ⟨554843, by rfl⟩ : syracuseStep 739791 = 1109687) B1109687
theorem B8440361 : Blo 738327 8440361 := bstep (se 2 (by rfl) ⟨3165135, by rfl⟩ : syracuseStep 8440361 = 6330271) B6330271
theorem B739931 : Blo 738327 739931 := bstep (se 1 (by rfl) ⟨554948, by rfl⟩ : syracuseStep 739931 = 1109897) B1109897
theorem B4737761 : Blo 738327 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B740095 : Blo 738327 740095 := bstep (se 1 (by rfl) ⟨555071, by rfl⟩ : syracuseStep 740095 = 1110143) B1110143
theorem B740519 : Blo 738327 740519 := bstep (se 1 (by rfl) ⟨555389, by rfl⟩ : syracuseStep 740519 = 1110779) B1110779
theorem B6311135 : Blo 738327 6311135 := bstep (se 1 (by rfl) ⟨4733351, by rfl⟩ : syracuseStep 6311135 = 9466703) B9466703
theorem B937271 : Blo 738327 937271 := bstep (se 1 (by rfl) ⟨702953, by rfl⟩ : syracuseStep 937271 = 1405907) B1405907
theorem B937423 : Blo 738327 937423 := bstep (se 1 (by rfl) ⟨703067, by rfl⟩ : syracuseStep 937423 = 1406135) B1406135
theorem B740815 : Blo 738327 740815 := bstep (se 1 (by rfl) ⟨555611, by rfl⟩ : syracuseStep 740815 = 1111223) B1111223
theorem B740975 : Blo 738327 740975 := bstep (se 1 (by rfl) ⟨555731, by rfl⟩ : syracuseStep 740975 = 1111463) B1111463
theorem B741095 : Blo 738327 741095 := bstep (se 1 (by rfl) ⟨555821, by rfl⟩ : syracuseStep 741095 = 1111643) B1111643
theorem B741403 : Blo 738327 741403 := bstep (se 1 (by rfl) ⟨556052, by rfl⟩ : syracuseStep 741403 = 1112105) B1112105
theorem B741423 : Blo 738327 741423 := bstep (se 1 (by rfl) ⟨556067, by rfl⟩ : syracuseStep 741423 = 1112135) B1112135
theorem B8114363 : Blo 738327 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B4509971 : Blo 738327 4509971 := bstep (se 1 (by rfl) ⟨3382478, by rfl⟩ : syracuseStep 4509971 = 6764957) B6764957
theorem B741679 : Blo 738327 741679 := bstep (se 1 (by rfl) ⟨556259, by rfl⟩ : syracuseStep 741679 = 1112519) B1112519
theorem B938395 : Blo 738327 938395 := bstep (se 1 (by rfl) ⟨703796, by rfl⟩ : syracuseStep 938395 = 1407593) B1407593
theorem B741823 : Blo 738327 741823 := bstep (se 1 (by rfl) ⟨556367, by rfl⟩ : syracuseStep 741823 = 1112735) B1112735
theorem B6836729 : Blo 738327 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B741919 : Blo 738327 741919 := bstep (se 1 (by rfl) ⟨556439, by rfl⟩ : syracuseStep 741919 = 1112879) B1112879
theorem B1266281 : Blo 738327 1266281 := bstep (se 2 (by rfl) ⟨474855, by rfl⟩ : syracuseStep 1266281 = 949711) B949711
theorem B741999 : Blo 738327 741999 := bstep (se 1 (by rfl) ⟨556499, by rfl⟩ : syracuseStep 741999 = 1112999) B1112999
theorem B742119 : Blo 738327 742119 := bstep (se 1 (by rfl) ⟨556589, by rfl⟩ : syracuseStep 742119 = 1113179) B1113179
theorem B1661759 : Blo 738327 1661759 := bstep (se 1 (by rfl) ⟨1246319, by rfl⟩ : syracuseStep 1661759 = 2492639) B2492639
theorem B2809019 : Blo 738327 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B1662335 : Blo 738327 1662335 := bstep (se 1 (by rfl) ⟨1246751, by rfl⟩ : syracuseStep 1662335 = 2493503) B2493503
theorem B4218587 : Blo 738327 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B974759 : Blo 738327 974759 := bstep (se 1 (by rfl) ⟨731069, by rfl⟩ : syracuseStep 974759 = 1462139) B1462139
theorem B7987187 : Blo 738327 7987187 := bstep (se 1 (by rfl) ⟨5990390, by rfl⟩ : syracuseStep 7987187 = 11980781) B11980781
theorem B4219087 : Blo 738327 4219087 := bstep (se 1 (by rfl) ⟨3164315, by rfl⟩ : syracuseStep 4219087 = 6328631) B6328631
theorem B1139065 : Blo 738327 1139065 := bstep (se 2 (by rfl) ⟨427149, by rfl⟩ : syracuseStep 1139065 = 854299) B854299
theorem B4219613 : Blo 738327 4219613 := bstep (se 3 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 4219613 = 1582355) B1582355
theorem B10674953 : Blo 738327 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B28500983 : Blo 738327 28500983 := bstep (se 1 (by rfl) ⟨21375737, by rfl⟩ : syracuseStep 28500983 = 42751475) B42751475
theorem B1664225 : Blo 738327 1664225 := bstep (se 2 (by rfl) ⟨624084, by rfl⟩ : syracuseStep 1664225 = 1248169) B1248169
theorem B1107563 : Blo 738327 1107563 := bstep (se 1 (by rfl) ⟨830672, by rfl⟩ : syracuseStep 1107563 = 1661345) B1661345
theorem B1107611 : Blo 738327 1107611 := bstep (se 1 (by rfl) ⟨830708, by rfl⟩ : syracuseStep 1107611 = 1661417) B1661417
theorem B1107833 : Blo 738327 1107833 := bstep (se 2 (by rfl) ⟨415437, by rfl⟩ : syracuseStep 1107833 = 830875) B830875
theorem B1664891 : Blo 738327 1664891 := bstep (se 1 (by rfl) ⟨1248668, by rfl⟩ : syracuseStep 1664891 = 2497337) B2497337
theorem B1665161 : Blo 738327 1665161 := bstep (se 2 (by rfl) ⟨624435, by rfl⟩ : syracuseStep 1665161 = 1248871) B1248871
theorem B1108583 : Blo 738327 1108583 := bstep (se 1 (by rfl) ⟨831437, by rfl⟩ : syracuseStep 1108583 = 1662875) B1662875
theorem B2026145 : Blo 738327 2026145 := bstep (se 2 (by rfl) ⟨759804, by rfl⟩ : syracuseStep 2026145 = 1519609) B1519609
theorem B1403705 : Blo 738327 1403705 := bstep (se 2 (by rfl) ⟨526389, by rfl⟩ : syracuseStep 1403705 = 1052779) B1052779
theorem B1108859 : Blo 738327 1108859 := bstep (se 1 (by rfl) ⟨831644, by rfl⟩ : syracuseStep 1108859 = 1663289) B1663289
theorem B1666043 : Blo 738327 1666043 := bstep (se 1 (by rfl) ⟨1249532, by rfl⟩ : syracuseStep 1666043 = 2499065) B2499065
theorem B3566663 : Blo 738327 3566663 := bstep (se 1 (by rfl) ⟨2674997, by rfl⟩ : syracuseStep 3566663 = 5349995) B5349995
theorem B1109129 : Blo 738327 1109129 := bstep (se 2 (by rfl) ⟨415923, by rfl⟩ : syracuseStep 1109129 = 831847) B831847
theorem B1666223 : Blo 738327 1666223 := bstep (se 1 (by rfl) ⟨1249667, by rfl⟩ : syracuseStep 1666223 = 2499335) B2499335
theorem B1109183 : Blo 738327 1109183 := bstep (se 1 (by rfl) ⟨831887, by rfl⟩ : syracuseStep 1109183 = 1663775) B1663775
theorem B3599777 : Blo 738327 3599777 := bstep (se 2 (by rfl) ⟨1349916, by rfl⟩ : syracuseStep 3599777 = 2699833) B2699833
theorem B1109723 : Blo 738327 1109723 := bstep (se 1 (by rfl) ⟨832292, by rfl⟩ : syracuseStep 1109723 = 1664585) B1664585
theorem B1666943 : Blo 738327 1666943 := bstep (se 1 (by rfl) ⟨1250207, by rfl⟩ : syracuseStep 1666943 = 2500415) B2500415
theorem B8679383 : Blo 738327 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B1109993 : Blo 738327 1109993 := bstep (se 2 (by rfl) ⟨416247, by rfl⟩ : syracuseStep 1109993 = 832495) B832495
theorem B1110011 : Blo 738327 1110011 := bstep (se 1 (by rfl) ⟨832508, by rfl⟩ : syracuseStep 1110011 = 1665017) B1665017
theorem B1110047 : Blo 738327 1110047 := bstep (se 1 (by rfl) ⟨832535, by rfl⟩ : syracuseStep 1110047 = 1665071) B1665071
theorem B1110071 : Blo 738327 1110071 := bstep (se 1 (by rfl) ⟨832553, by rfl⟩ : syracuseStep 1110071 = 1665107) B1665107
theorem B3600463 : Blo 738327 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B2814047 : Blo 738327 2814047 := bstep (se 1 (by rfl) ⟨2110535, by rfl⟩ : syracuseStep 2814047 = 4221071) B4221071
theorem B1110191 : Blo 738327 1110191 := bstep (se 1 (by rfl) ⟨832643, by rfl⟩ : syracuseStep 1110191 = 1665287) B1665287
theorem B1110395 : Blo 738327 1110395 := bstep (se 1 (by rfl) ⟨832796, by rfl⟩ : syracuseStep 1110395 = 1665593) B1665593
theorem B12972413 : Blo 738327 12972413 := bstep (se 3 (by rfl) ⟨2432327, by rfl⟩ : syracuseStep 12972413 = 4864655) B4864655
theorem B1110665 : Blo 738327 1110665 := bstep (se 2 (by rfl) ⟨416499, by rfl⟩ : syracuseStep 1110665 = 832999) B832999
theorem B1110875 : Blo 738327 1110875 := bstep (se 1 (by rfl) ⟨833156, by rfl⟩ : syracuseStep 1110875 = 1666313) B1666313
theorem B1667951 : Blo 738327 1667951 := bstep (se 1 (by rfl) ⟨1250963, by rfl⟩ : syracuseStep 1667951 = 2501927) B2501927
theorem B2061167 : Blo 738327 2061167 := bstep (se 1 (by rfl) ⟨1545875, by rfl⟩ : syracuseStep 2061167 = 3091751) B3091751
theorem B1110905 : Blo 738327 1110905 := bstep (se 2 (by rfl) ⟨416589, by rfl⟩ : syracuseStep 1110905 = 833179) B833179
theorem B4748219 : Blo 738327 4748219 := bstep (se 1 (by rfl) ⟨3561164, by rfl⟩ : syracuseStep 4748219 = 7122329) B7122329
theorem B1996105 : Blo 738327 1996105 := bstep (se 2 (by rfl) ⟨748539, by rfl⟩ : syracuseStep 1996105 = 1497079) B1497079
theorem B5993837 : Blo 738327 5993837 := bstep (se 3 (by rfl) ⟨1123844, by rfl⟩ : syracuseStep 5993837 = 2247689) B2247689
theorem B1111535 : Blo 738327 1111535 := bstep (se 1 (by rfl) ⟨833651, by rfl⟩ : syracuseStep 1111535 = 1667303) B1667303
theorem B1111655 : Blo 738327 1111655 := bstep (se 1 (by rfl) ⟨833741, by rfl⟩ : syracuseStep 1111655 = 1667483) B1667483
theorem B1112111 : Blo 738327 1112111 := bstep (se 1 (by rfl) ⟨834083, by rfl⟩ : syracuseStep 1112111 = 1668167) B1668167
theorem B1112231 : Blo 738327 1112231 := bstep (se 1 (by rfl) ⟨834173, by rfl⟩ : syracuseStep 1112231 = 1668347) B1668347
theorem B1112375 : Blo 738327 1112375 := bstep (se 1 (by rfl) ⟨834281, by rfl⟩ : syracuseStep 1112375 = 1668563) B1668563
theorem B1112555 : Blo 738327 1112555 := bstep (se 1 (by rfl) ⟨834416, by rfl⟩ : syracuseStep 1112555 = 1668833) B1668833
theorem B2816491 : Blo 738327 2816491 := bstep (se 1 (by rfl) ⟨2112368, by rfl⟩ : syracuseStep 2816491 = 4224737) B4224737
theorem B1669625 : Blo 738327 1669625 := bstep (se 2 (by rfl) ⟨626109, by rfl⟩ : syracuseStep 1669625 = 1252219) B1252219
theorem B1669715 : Blo 738327 1669715 := bstep (se 1 (by rfl) ⟨1252286, by rfl⟩ : syracuseStep 1669715 = 2504573) B2504573
theorem B1669895 : Blo 738327 1669895 := bstep (se 1 (by rfl) ⟨1252421, by rfl⟩ : syracuseStep 1669895 = 2504843) B2504843
theorem B1112903 : Blo 738327 1112903 := bstep (se 1 (by rfl) ⟨834677, by rfl⟩ : syracuseStep 1112903 = 1669355) B1669355
theorem B4226195 : Blo 738327 4226195 := bstep (se 1 (by rfl) ⟨3169646, by rfl⟩ : syracuseStep 4226195 = 6339293) B6339293
theorem B4226377 : Blo 738327 4226377 := bstep (se 2 (by rfl) ⟨1584891, by rfl⟩ : syracuseStep 4226377 = 3169783) B3169783
theorem B2817449 : Blo 738327 2817449 := bstep (se 2 (by rfl) ⟨1056543, by rfl⟩ : syracuseStep 2817449 = 2113087) B2113087
theorem B61636085 : Blo 738327 61636085 := bstep (se 5 (by rfl) ⟨2889191, by rfl⟩ : syracuseStep 61636085 = 5778383) B5778383
theorem B1246279 : Blo 738327 1246279 := bstep (se 1 (by rfl) ⟨934709, by rfl⟩ : syracuseStep 1246279 = 1869419) B1869419
theorem B1246367 : Blo 738327 1246367 := bstep (se 1 (by rfl) ⟨934775, by rfl⟩ : syracuseStep 1246367 = 1869551) B1869551
theorem B3802601 : Blo 738327 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B1246711 : Blo 738327 1246711 := bstep (se 1 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 1246711 = 1870067) B1870067
theorem B24381071 : Blo 738327 24381071 := bstep (se 1 (by rfl) ⟨18285803, by rfl⟩ : syracuseStep 24381071 = 36571607) B36571607
theorem B1247791 : Blo 738327 1247791 := bstep (se 1 (by rfl) ⟨935843, by rfl⟩ : syracuseStep 1247791 = 1871687) B1871687
theorem B2493071 : Blo 738327 2493071 := bstep (se 1 (by rfl) ⟨1869803, by rfl⟩ : syracuseStep 2493071 = 3739607) B3739607
theorem B5409575 : Blo 738327 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B2493665 : Blo 738327 2493665 := bstep (se 2 (by rfl) ⟨935124, by rfl⟩ : syracuseStep 2493665 = 1870249) B1870249
theorem B21368357 : Blo 738327 21368357 := bstep (se 4 (by rfl) ⟨2003283, by rfl⟩ : syracuseStep 21368357 = 4006567) B4006567
theorem B2494043 : Blo 738327 2494043 := bstep (se 1 (by rfl) ⟨1870532, by rfl⟩ : syracuseStep 2494043 = 3741065) B3741065
theorem B6753935 : Blo 738327 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B2887753 : Blo 738327 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B1249519 : Blo 738327 1249519 := bstep (se 1 (by rfl) ⟨937139, by rfl⟩ : syracuseStep 1249519 = 1874279) B1874279
theorem B2494907 : Blo 738327 2494907 := bstep (se 1 (by rfl) ⟨1871180, by rfl⟩ : syracuseStep 2494907 = 3742361) B3742361
theorem B1249897 : Blo 738327 1249897 := bstep (se 2 (by rfl) ⟨468711, by rfl⟩ : syracuseStep 1249897 = 937423) B937423
theorem B791327 : Blo 738327 791327 := bstep (se 1 (by rfl) ⟨593495, by rfl⟩ : syracuseStep 791327 = 1186991) B1186991
theorem B1872679 : Blo 738327 1872679 := bstep (se 1 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 1872679 = 2809019) B2809019
theorem B2102527 : Blo 738327 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B1250815 : Blo 738327 1250815 := bstep (se 1 (by rfl) ⟨938111, by rfl⟩ : syracuseStep 1250815 = 1876223) B1876223
theorem B7116635 : Blo 738327 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B1251193 : Blo 738327 1251193 := bstep (se 2 (by rfl) ⟨469197, by rfl⟩ : syracuseStep 1251193 = 938395) B938395
theorem B1251227 : Blo 738327 1251227 := bstep (se 1 (by rfl) ⟨938420, by rfl⟩ : syracuseStep 1251227 = 1876841) B1876841
theorem B2496743 : Blo 738327 2496743 := bstep (se 1 (by rfl) ⟨1872557, by rfl⟩ : syracuseStep 2496743 = 3745115) B3745115
theorem B7215455 : Blo 738327 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B4266839 : Blo 738327 4266839 := bstep (se 1 (by rfl) ⟨3200129, by rfl⟩ : syracuseStep 4266839 = 6400259) B6400259
theorem B2497499 : Blo 738327 2497499 := bstep (se 1 (by rfl) ⟨1873124, by rfl⟩ : syracuseStep 2497499 = 3746249) B3746249
theorem B1252415 : Blo 738327 1252415 := bstep (se 1 (by rfl) ⟨939311, by rfl⟩ : syracuseStep 1252415 = 1878623) B1878623
theorem B2661473 : Blo 738327 2661473 := bstep (se 2 (by rfl) ⟨998052, by rfl⟩ : syracuseStep 2661473 = 1996105) B1996105
theorem B1350763 : Blo 738327 1350763 := bstep (se 1 (by rfl) ⟨1013072, by rfl⟩ : syracuseStep 1350763 = 2026145) B2026145
theorem B3743171 : Blo 738327 3743171 := bstep (se 1 (by rfl) ⟨2807378, by rfl⟩ : syracuseStep 3743171 = 5614757) B5614757
theorem B2399851 : Blo 738327 2399851 := bstep (se 1 (by rfl) ⟨1799888, by rfl⟩ : syracuseStep 2399851 = 3599777) B3599777
theorem B1876031 : Blo 738327 1876031 := bstep (se 1 (by rfl) ⟨1407023, by rfl⟩ : syracuseStep 1876031 = 2814047) B2814047
theorem B18948167 : Blo 738327 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B1581535 : Blo 738327 1581535 := bstep (se 1 (by rfl) ⟨1186151, by rfl⟩ : syracuseStep 1581535 = 2372303) B2372303
theorem B1188407 : Blo 738327 1188407 := bstep (se 1 (by rfl) ⟨891305, by rfl⟩ : syracuseStep 1188407 = 1782611) B1782611
theorem B2499389 : Blo 738327 2499389 := bstep (se 3 (by rfl) ⟨468635, by rfl⟩ : syracuseStep 2499389 = 937271) B937271
theorem B10397429 : Blo 738327 10397429 := bstep (se 5 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 10397429 = 974759) B974759
theorem B2500577 : Blo 738327 2500577 := bstep (se 2 (by rfl) ⟨937716, by rfl⟩ : syracuseStep 2500577 = 1875433) B1875433
theorem B2107529 : Blo 738327 2107529 := bstep (se 2 (by rfl) ⟨790323, by rfl⟩ : syracuseStep 2107529 = 1580647) B1580647
theorem B1878299 : Blo 738327 1878299 := bstep (se 1 (by rfl) ⟨1408724, by rfl⟩ : syracuseStep 1878299 = 2817449) B2817449
theorem B1124671 : Blo 738327 1124671 := bstep (se 1 (by rfl) ⟨843503, by rfl⟩ : syracuseStep 1124671 = 1687007) B1687007
theorem B2107745 : Blo 738327 2107745 := bstep (se 2 (by rfl) ⟨790404, by rfl⟩ : syracuseStep 2107745 = 1580809) B1580809
theorem B2108359 : Blo 738327 2108359 := bstep (se 1 (by rfl) ⟨1581269, by rfl⟩ : syracuseStep 2108359 = 3162539) B3162539
theorem B3747059 : Blo 738327 3747059 := bstep (se 1 (by rfl) ⟨2810294, by rfl⟩ : syracuseStep 3747059 = 5620589) B5620589
theorem B1584431 : Blo 738327 1584431 := bstep (se 1 (by rfl) ⟨1188323, by rfl⟩ : syracuseStep 1584431 = 2376647) B2376647
theorem B3157481 : Blo 738327 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B4730663 : Blo 738327 4730663 := bstep (se 1 (by rfl) ⟨3547997, by rfl⟩ : syracuseStep 4730663 = 7095995) B7095995
theorem B18231277 : Blo 738327 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B2502791 : Blo 738327 2502791 := bstep (se 1 (by rfl) ⟨1877093, by rfl⟩ : syracuseStep 2502791 = 3754187) B3754187
theorem B2502953 : Blo 738327 2502953 := bstep (se 2 (by rfl) ⟨938607, by rfl⟩ : syracuseStep 2502953 = 1877215) B1877215
theorem B3158507 : Blo 738327 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B5616215 : Blo 738327 5616215 := bstep (se 1 (by rfl) ⟨4212161, by rfl⟩ : syracuseStep 5616215 = 8424323) B8424323
theorem B6075013 : Blo 738327 6075013 := bstep (se 4 (by rfl) ⟨569532, by rfl⟩ : syracuseStep 6075013 = 1139065) B1139065
theorem B4207423 : Blo 738327 4207423 := bstep (se 1 (by rfl) ⟨3155567, by rfl⟩ : syracuseStep 4207423 = 6311135) B6311135
theorem B24360041 : Blo 738327 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B2504681 : Blo 738327 2504681 := bstep (se 2 (by rfl) ⟨939255, by rfl⟩ : syracuseStep 2504681 = 1878511) B1878511
theorem B1424251 : Blo 738327 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B834727 : Blo 738327 834727 := bstep (se 1 (by rfl) ⟨626045, by rfl⟩ : syracuseStep 834727 = 1252091) B1252091
theorem B5324791 : Blo 738327 5324791 := bstep (se 1 (by rfl) ⟨3993593, by rfl⟩ : syracuseStep 5324791 = 7987187) B7987187
theorem B4800617 : Blo 738327 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B5423399 : Blo 738327 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B6341003 : Blo 738327 6341003 := bstep (se 1 (by rfl) ⟨4755752, by rfl⟩ : syracuseStep 6341003 = 9511505) B9511505
theorem B6308401 : Blo 738327 6308401 := bstep (se 2 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 6308401 = 4731301) B4731301
theorem B738375 : Blo 738327 738375 := bstep (se 1 (by rfl) ⟨553781, by rfl⟩ : syracuseStep 738375 = 1107563) B1107563
theorem B738407 : Blo 738327 738407 := bstep (se 1 (by rfl) ⟨553805, by rfl⟩ : syracuseStep 738407 = 1107611) B1107611
theorem B738555 : Blo 738327 738555 := bstep (se 1 (by rfl) ⟨553916, by rfl⟩ : syracuseStep 738555 = 1107833) B1107833
theorem B739055 : Blo 738327 739055 := bstep (se 1 (by rfl) ⟨554291, by rfl⟩ : syracuseStep 739055 = 1108583) B1108583
theorem B935803 : Blo 738327 935803 := bstep (se 1 (by rfl) ⟨701852, by rfl⟩ : syracuseStep 935803 = 1403705) B1403705
theorem B739239 : Blo 738327 739239 := bstep (se 1 (by rfl) ⟨554429, by rfl⟩ : syracuseStep 739239 = 1108859) B1108859
theorem B2377775 : Blo 738327 2377775 := bstep (se 1 (by rfl) ⟨1783331, by rfl⟩ : syracuseStep 2377775 = 3566663) B3566663
theorem B739419 : Blo 738327 739419 := bstep (se 1 (by rfl) ⟨554564, by rfl⟩ : syracuseStep 739419 = 1109129) B1109129
theorem B739455 : Blo 738327 739455 := bstep (se 1 (by rfl) ⟨554591, by rfl⟩ : syracuseStep 739455 = 1109183) B1109183
theorem B24365299 : Blo 738327 24365299 := bstep (se 1 (by rfl) ⟨18273974, by rfl⟩ : syracuseStep 24365299 = 36547949) B36547949
theorem B2672891 : Blo 738327 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B739815 : Blo 738327 739815 := bstep (se 1 (by rfl) ⟨554861, by rfl⟩ : syracuseStep 739815 = 1109723) B1109723
theorem B16042535 : Blo 738327 16042535 := bstep (se 1 (by rfl) ⟨12031901, by rfl⟩ : syracuseStep 16042535 = 24063803) B24063803
theorem B5786255 : Blo 738327 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B739995 : Blo 738327 739995 := bstep (se 1 (by rfl) ⟨554996, by rfl⟩ : syracuseStep 739995 = 1109993) B1109993
theorem B740007 : Blo 738327 740007 := bstep (se 1 (by rfl) ⟨555005, by rfl⟩ : syracuseStep 740007 = 1110011) B1110011
theorem B740031 : Blo 738327 740031 := bstep (se 1 (by rfl) ⟨555023, by rfl⟩ : syracuseStep 740031 = 1110047) B1110047
theorem B740047 : Blo 738327 740047 := bstep (se 1 (by rfl) ⟨555035, by rfl⟩ : syracuseStep 740047 = 1110071) B1110071
theorem B740127 : Blo 738327 740127 := bstep (se 1 (by rfl) ⟨555095, by rfl⟩ : syracuseStep 740127 = 1110191) B1110191
theorem B740263 : Blo 738327 740263 := bstep (se 1 (by rfl) ⟨555197, by rfl⟩ : syracuseStep 740263 = 1110395) B1110395
theorem B740443 : Blo 738327 740443 := bstep (se 1 (by rfl) ⟨555332, by rfl⟩ : syracuseStep 740443 = 1110665) B1110665
theorem B740583 : Blo 738327 740583 := bstep (se 1 (by rfl) ⟨555437, by rfl⟩ : syracuseStep 740583 = 1110875) B1110875
theorem B740603 : Blo 738327 740603 := bstep (se 1 (by rfl) ⟨555452, by rfl⟩ : syracuseStep 740603 = 1110905) B1110905
theorem B3165479 : Blo 738327 3165479 := bstep (se 1 (by rfl) ⟨2374109, by rfl⟩ : syracuseStep 3165479 = 4748219) B4748219
theorem B3755321 : Blo 738327 3755321 := bstep (se 2 (by rfl) ⟨1408245, by rfl⟩ : syracuseStep 3755321 = 2816491) B2816491
theorem B49270139 : Blo 738327 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B741023 : Blo 738327 741023 := bstep (se 1 (by rfl) ⟨555767, by rfl⟩ : syracuseStep 741023 = 1111535) B1111535
theorem B741103 : Blo 738327 741103 := bstep (se 1 (by rfl) ⟨555827, by rfl⟩ : syracuseStep 741103 = 1111655) B1111655
theorem B741407 : Blo 738327 741407 := bstep (se 1 (by rfl) ⟨556055, by rfl⟩ : syracuseStep 741407 = 1112111) B1112111
theorem B741487 : Blo 738327 741487 := bstep (se 1 (by rfl) ⟨556115, by rfl⟩ : syracuseStep 741487 = 1112231) B1112231
theorem B741583 : Blo 738327 741583 := bstep (se 1 (by rfl) ⟨556187, by rfl⟩ : syracuseStep 741583 = 1112375) B1112375
theorem B741703 : Blo 738327 741703 := bstep (se 1 (by rfl) ⟨556277, by rfl⟩ : syracuseStep 741703 = 1112555) B1112555
theorem B3199351 : Blo 738327 3199351 := bstep (se 1 (by rfl) ⟨2399513, by rfl⟩ : syracuseStep 3199351 = 4799027) B4799027
theorem B12177935 : Blo 738327 12177935 := bstep (se 1 (by rfl) ⟨9133451, by rfl⟩ : syracuseStep 12177935 = 18266903) B18266903
theorem B741935 : Blo 738327 741935 := bstep (se 1 (by rfl) ⟨556451, by rfl⟩ : syracuseStep 741935 = 1112903) B1112903
theorem B5624477 : Blo 738327 5624477 := bstep (se 3 (by rfl) ⟨1054589, by rfl⟩ : syracuseStep 5624477 = 2109179) B2109179
theorem B5625449 : Blo 738327 5625449 := bstep (se 2 (by rfl) ⟨2109543, by rfl⟩ : syracuseStep 5625449 = 4219087) B4219087
theorem B16013123 : Blo 738327 16013123 := bstep (se 1 (by rfl) ⟨12009842, by rfl⟩ : syracuseStep 16013123 = 24019685) B24019685
theorem B3168143 : Blo 738327 3168143 := bstep (se 1 (by rfl) ⟨2376107, by rfl⟩ : syracuseStep 3168143 = 4752215) B4752215
theorem B34593101 : Blo 738327 34593101 := bstep (se 3 (by rfl) ⟨6486206, by rfl⟩ : syracuseStep 34593101 = 12972413) B12972413
theorem B8018635 : Blo 738327 8018635 := bstep (se 1 (by rfl) ⟨6013976, by rfl⟩ : syracuseStep 8018635 = 12027953) B12027953
theorem B842491 : Blo 738327 842491 := bstep (se 1 (by rfl) ⟨631868, by rfl⟩ : syracuseStep 842491 = 1263737) B1263737
theorem B5626907 : Blo 738327 5626907 := bstep (se 1 (by rfl) ⟨4220180, by rfl⟩ : syracuseStep 5626907 = 8440361) B8440361
theorem B4218155 : Blo 738327 4218155 := bstep (se 1 (by rfl) ⟨3163616, by rfl⟩ : syracuseStep 4218155 = 6327233) B6327233
theorem B1662263 : Blo 738327 1662263 := bstep (se 1 (by rfl) ⟨1246697, by rfl⟩ : syracuseStep 1662263 = 2493395) B2493395
theorem B5496445 : Blo 738327 5496445 := bstep (se 3 (by rfl) ⟨1030583, by rfl⟩ : syracuseStep 5496445 = 2061167) B2061167
theorem B3006647 : Blo 738327 3006647 := bstep (se 1 (by rfl) ⟨2254985, by rfl⟩ : syracuseStep 3006647 = 4509971) B4509971
theorem B1663163 : Blo 738327 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B844187 : Blo 738327 844187 := bstep (se 1 (by rfl) ⟨633140, by rfl⟩ : syracuseStep 844187 = 1266281) B1266281
theorem B1401799 : Blo 738327 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B1664567 : Blo 738327 1664567 := bstep (se 1 (by rfl) ⟨1248425, by rfl⟩ : syracuseStep 1664567 = 2496851) B2496851
theorem B1402505 : Blo 738327 1402505 := bstep (se 2 (by rfl) ⟨525939, by rfl⟩ : syracuseStep 1402505 = 1051879) B1051879
theorem B1107689 : Blo 738327 1107689 := bstep (se 2 (by rfl) ⟨415383, by rfl⟩ : syracuseStep 1107689 = 830767) B830767
theorem B1107839 : Blo 738327 1107839 := bstep (se 1 (by rfl) ⟨830879, by rfl⟩ : syracuseStep 1107839 = 1661759) B1661759
theorem B1664927 : Blo 738327 1664927 := bstep (se 1 (by rfl) ⟨1248695, by rfl⟩ : syracuseStep 1664927 = 2497391) B2497391
theorem B6318107 : Blo 738327 6318107 := bstep (se 1 (by rfl) ⟨4738580, by rfl⟩ : syracuseStep 6318107 = 9477161) B9477161
theorem B4745243 : Blo 738327 4745243 := bstep (se 1 (by rfl) ⟨3558932, by rfl⟩ : syracuseStep 4745243 = 7117865) B7117865
theorem B1665179 : Blo 738327 1665179 := bstep (se 1 (by rfl) ⟨1248884, by rfl⟩ : syracuseStep 1665179 = 2497769) B2497769
theorem B1108223 : Blo 738327 1108223 := bstep (se 1 (by rfl) ⟨831167, by rfl⟩ : syracuseStep 1108223 = 1662335) B1662335
theorem B9005435 : Blo 738327 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B1665467 : Blo 738327 1665467 := bstep (se 1 (by rfl) ⟨1249100, by rfl⟩ : syracuseStep 1665467 = 2498201) B2498201
theorem B2812391 : Blo 738327 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B1108457 : Blo 738327 1108457 := bstep (se 2 (by rfl) ⟨415671, by rfl⟩ : syracuseStep 1108457 = 831343) B831343
theorem B2255339 : Blo 738327 2255339 := bstep (se 1 (by rfl) ⟨1691504, by rfl⟩ : syracuseStep 2255339 = 3383009) B3383009
theorem B12675851 : Blo 738327 12675851 := bstep (se 1 (by rfl) ⟨9506888, by rfl⟩ : syracuseStep 12675851 = 19013777) B19013777
theorem B2813075 : Blo 738327 2813075 := bstep (se 1 (by rfl) ⟨2109806, by rfl⟩ : syracuseStep 2813075 = 4219613) B4219613
theorem B19000655 : Blo 738327 19000655 := bstep (se 1 (by rfl) ⟨14250491, by rfl⟩ : syracuseStep 19000655 = 28500983) B28500983
theorem B1109369 : Blo 738327 1109369 := bstep (se 2 (by rfl) ⟨416013, by rfl⟩ : syracuseStep 1109369 = 832027) B832027
theorem B1109483 : Blo 738327 1109483 := bstep (se 1 (by rfl) ⟨832112, by rfl⟩ : syracuseStep 1109483 = 1664225) B1664225
theorem B1109609 : Blo 738327 1109609 := bstep (se 2 (by rfl) ⟨416103, by rfl⟩ : syracuseStep 1109609 = 832207) B832207
theorem B1666907 : Blo 738327 1666907 := bstep (se 1 (by rfl) ⟨1250180, by rfl⟩ : syracuseStep 1666907 = 2500361) B2500361
theorem B1109927 : Blo 738327 1109927 := bstep (se 1 (by rfl) ⟨832445, by rfl⟩ : syracuseStep 1109927 = 1664891) B1664891
theorem B1110107 : Blo 738327 1110107 := bstep (se 1 (by rfl) ⟨832580, by rfl⟩ : syracuseStep 1110107 = 1665161) B1665161
theorem B2814061 : Blo 738327 2814061 := bstep (se 3 (by rfl) ⟨527636, by rfl⟩ : syracuseStep 2814061 = 1055273) B1055273
theorem B1110695 : Blo 738327 1110695 := bstep (se 1 (by rfl) ⟨833021, by rfl⟩ : syracuseStep 1110695 = 1666043) B1666043
theorem B1110815 : Blo 738327 1110815 := bstep (se 1 (by rfl) ⟨833111, by rfl⟩ : syracuseStep 1110815 = 1666223) B1666223
theorem B1667879 : Blo 738327 1667879 := bstep (se 1 (by rfl) ⟨1250909, by rfl⟩ : syracuseStep 1667879 = 2501819) B2501819
theorem B1111295 : Blo 738327 1111295 := bstep (se 1 (by rfl) ⟨833471, by rfl⟩ : syracuseStep 1111295 = 1666943) B1666943
theorem B3995369 : Blo 738327 3995369 := bstep (se 2 (by rfl) ⟨1498263, by rfl⟩ : syracuseStep 3995369 = 2996527) B2996527
theorem B1111967 : Blo 738327 1111967 := bstep (se 1 (by rfl) ⟨833975, by rfl⟩ : syracuseStep 1111967 = 1667951) B1667951
theorem B1669175 : Blo 738327 1669175 := bstep (se 1 (by rfl) ⟨1251881, by rfl⟩ : syracuseStep 1669175 = 2503763) B2503763
theorem B1407145 : Blo 738327 1407145 := bstep (se 2 (by rfl) ⟨527679, by rfl⟩ : syracuseStep 1407145 = 1055359) B1055359
theorem B3995891 : Blo 738327 3995891 := bstep (se 1 (by rfl) ⟨2996918, by rfl⟩ : syracuseStep 3995891 = 5993837) B5993837
theorem B5404927 : Blo 738327 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B1407289 : Blo 738327 1407289 := bstep (se 2 (by rfl) ⟨527733, by rfl⟩ : syracuseStep 1407289 = 1055467) B1055467
theorem B22739345 : Blo 738327 22739345 := bstep (se 2 (by rfl) ⟨8527254, by rfl⟩ : syracuseStep 22739345 = 17054509) B17054509
theorem B1669535 : Blo 738327 1669535 := bstep (se 1 (by rfl) ⟨1252151, by rfl⟩ : syracuseStep 1669535 = 2504303) B2504303
theorem B415464389 : Blo 738327 415464389 := bstep (se 4 (by rfl) ⟨38949786, by rfl⟩ : syracuseStep 415464389 = 77899573) B77899573
theorem B1113083 : Blo 738327 1113083 := bstep (se 1 (by rfl) ⟨834812, by rfl⟩ : syracuseStep 1113083 = 1669625) B1669625
theorem B1113143 : Blo 738327 1113143 := bstep (se 1 (by rfl) ⟨834857, by rfl⟩ : syracuseStep 1113143 = 1669715) B1669715
theorem B5635169 : Blo 738327 5635169 := bstep (se 2 (by rfl) ⟨2113188, by rfl⟩ : syracuseStep 5635169 = 4226377) B4226377
theorem B1113263 : Blo 738327 1113263 := bstep (se 1 (by rfl) ⟨834947, by rfl⟩ : syracuseStep 1113263 = 1669895) B1669895
theorem B6323507 : Blo 738327 6323507 := bstep (se 1 (by rfl) ⟨4742630, by rfl⟩ : syracuseStep 6323507 = 9485261) B9485261
theorem B2817463 : Blo 738327 2817463 := bstep (se 1 (by rfl) ⟨2113097, by rfl⟩ : syracuseStep 2817463 = 4226195) B4226195
theorem B21331451 : Blo 738327 21331451 := bstep (se 1 (by rfl) ⟨15998588, by rfl⟩ : syracuseStep 21331451 = 31997177) B31997177
theorem B41090723 : Blo 738327 41090723 := bstep (se 1 (by rfl) ⟨30818042, by rfl⟩ : syracuseStep 41090723 = 61636085) B61636085
theorem B11566759 : Blo 738327 11566759 := bstep (se 1 (by rfl) ⟨8675069, by rfl⟩ : syracuseStep 11566759 = 17350139) B17350139
theorem B4227335 : Blo 738327 4227335 := bstep (se 1 (by rfl) ⟨3170501, by rfl⟩ : syracuseStep 4227335 = 6341003) B6341003
theorem B16254047 : Blo 738327 16254047 := bstep (se 1 (by rfl) ⟨12190535, by rfl⟩ : syracuseStep 16254047 = 24381071) B24381071
theorem B1869065 : Blo 738327 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B3606383 : Blo 738327 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B1247737 : Blo 738327 1247737 := bstep (se 2 (by rfl) ⟨467901, by rfl⟩ : syracuseStep 1247737 = 935803) B935803
theorem B1774315 : Blo 738327 1774315 := bstep (se 1 (by rfl) ⟨1330736, by rfl⟩ : syracuseStep 1774315 = 2661473) B2661473
theorem B2495447 : Blo 738327 2495447 := bstep (se 1 (by rfl) ⟨1871585, by rfl⟩ : syracuseStep 2495447 = 3743171) B3743171
theorem B1250687 : Blo 738327 1250687 := bstep (se 1 (by rfl) ⟨938015, by rfl⟩ : syracuseStep 1250687 = 1876031) B1876031
theorem B12653981 : Blo 738327 12653981 := bstep (se 3 (by rfl) ⟨2372621, by rfl⟩ : syracuseStep 12653981 = 4745243) B4745243
theorem B2004431 : Blo 738327 2004431 := bstep (se 1 (by rfl) ⟨1503323, by rfl⟩ : syracuseStep 2004431 = 3006647) B3006647
theorem B792271 : Blo 738327 792271 := bstep (se 1 (by rfl) ⟨594203, by rfl⟩ : syracuseStep 792271 = 1188407) B1188407
theorem B4265801 : Blo 738327 4265801 := bstep (se 2 (by rfl) ⟨1599675, by rfl⟩ : syracuseStep 4265801 = 3199351) B3199351
theorem B8100017 : Blo 738327 8100017 := bstep (se 2 (by rfl) ⟨3037506, by rfl⟩ : syracuseStep 8100017 = 6075013) B6075013
theorem B2496905 : Blo 738327 2496905 := bstep (se 2 (by rfl) ⟨936339, by rfl⟩ : syracuseStep 2496905 = 1872679) B1872679
theorem B5609897 : Blo 738327 5609897 := bstep (se 2 (by rfl) ⟨2103711, by rfl⟩ : syracuseStep 5609897 = 4207423) B4207423
theorem B1252199 : Blo 738327 1252199 := bstep (se 1 (by rfl) ⟨939149, by rfl⟩ : syracuseStep 1252199 = 1878299) B1878299
theorem B6003623 : Blo 738327 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B1874927 : Blo 738327 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B1875383 : Blo 738327 1875383 := bstep (se 1 (by rfl) ⟨1406537, by rfl⟩ : syracuseStep 1875383 = 2813075) B2813075
theorem B2498039 : Blo 738327 2498039 := bstep (se 1 (by rfl) ⟨1873529, by rfl⟩ : syracuseStep 2498039 = 3747059) B3747059
theorem B1056287 : Blo 738327 1056287 := bstep (se 1 (by rfl) ⟨792215, by rfl⟩ : syracuseStep 1056287 = 1584431) B1584431
theorem B3153775 : Blo 738327 3153775 := bstep (se 1 (by rfl) ⟨2365331, by rfl⟩ : syracuseStep 3153775 = 4730663) B4730663
theorem B1876193 : Blo 738327 1876193 := bstep (se 2 (by rfl) ⟨703572, by rfl⟩ : syracuseStep 1876193 = 1407145) B1407145
theorem B2105671 : Blo 738327 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B3744143 : Blo 738327 3744143 := bstep (se 1 (by rfl) ⟨2808107, by rfl⟩ : syracuseStep 3744143 = 5616215) B5616215
theorem B1876385 : Blo 738327 1876385 := bstep (se 2 (by rfl) ⟨703644, by rfl⟩ : syracuseStep 1876385 = 1407289) B1407289
theorem B10691513 : Blo 738327 10691513 := bstep (se 2 (by rfl) ⟨4009317, by rfl⟩ : syracuseStep 10691513 = 8018635) B8018635
theorem B1123321 : Blo 738327 1123321 := bstep (se 2 (by rfl) ⟨421245, by rfl⟩ : syracuseStep 1123321 = 842491) B842491
theorem B2663579 : Blo 738327 2663579 := bstep (se 1 (by rfl) ⟨1997684, by rfl⟩ : syracuseStep 2663579 = 3995369) B3995369
theorem B2663927 : Blo 738327 2663927 := bstep (se 1 (by rfl) ⟨1997945, by rfl⟩ : syracuseStep 2663927 = 3995891) B3995891
theorem B3615599 : Blo 738327 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B2108713 : Blo 738327 2108713 := bstep (se 2 (by rfl) ⟨790767, by rfl⟩ : syracuseStep 2108713 = 1581535) B1581535
theorem B830911 : Blo 738327 830911 := bstep (se 1 (by rfl) ⟨623183, by rfl⟩ : syracuseStep 830911 = 1246367) B1246367
theorem B2535067 : Blo 738327 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B1585183 : Blo 738327 1585183 := bstep (se 1 (by rfl) ⟨1188887, by rfl⟩ : syracuseStep 1585183 = 2377775) B2377775
theorem B1781927 : Blo 738327 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B10695023 : Blo 738327 10695023 := bstep (se 1 (by rfl) ⟨8021267, by rfl⟩ : syracuseStep 10695023 = 16042535) B16042535
theorem B2110205 : Blo 738327 2110205 := bstep (se 3 (by rfl) ⟨395663, by rfl⟩ : syracuseStep 2110205 = 791327) B791327
theorem B2110319 : Blo 738327 2110319 := bstep (se 1 (by rfl) ⟨1582739, by rfl⟩ : syracuseStep 2110319 = 3165479) B3165479
theorem B2503547 : Blo 738327 2503547 := bstep (se 1 (by rfl) ⟨1877660, by rfl⟩ : syracuseStep 2503547 = 3755321) B3755321
theorem B32846759 : Blo 738327 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B4502623 : Blo 738327 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B32487065 : Blo 738327 32487065 := bstep (se 2 (by rfl) ⟨12182649, by rfl⟩ : syracuseStep 32487065 = 24365299) B24365299
theorem B3749651 : Blo 738327 3749651 := bstep (se 1 (by rfl) ⟨2812238, by rfl⟩ : syracuseStep 3749651 = 5624477) B5624477
theorem B3750299 : Blo 738327 3750299 := bstep (se 1 (by rfl) ⟨2812724, by rfl⟩ : syracuseStep 3750299 = 5625449) B5625449
theorem B2112095 : Blo 738327 2112095 := bstep (se 1 (by rfl) ⟨1584071, by rfl⟩ : syracuseStep 2112095 = 3168143) B3168143
theorem B834151 : Blo 738327 834151 := bstep (se 1 (by rfl) ⟨625613, by rfl⟩ : syracuseStep 834151 = 1251227) B1251227
theorem B3751271 : Blo 738327 3751271 := bstep (se 1 (by rfl) ⟨2813453, by rfl⟩ : syracuseStep 3751271 = 5626907) B5626907
theorem B834943 : Blo 738327 834943 := bstep (se 1 (by rfl) ⟨626207, by rfl⟩ : syracuseStep 834943 = 1252415) B1252415
theorem B12632111 : Blo 738327 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B3850337 : Blo 738327 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B3752081 : Blo 738327 3752081 := bstep (se 2 (by rfl) ⟨1407030, by rfl⟩ : syracuseStep 3752081 = 2814061) B2814061
theorem B935003 : Blo 738327 935003 := bstep (se 1 (by rfl) ⟨701252, by rfl⟩ : syracuseStep 935003 = 1402505) B1402505
theorem B738459 : Blo 738327 738459 := bstep (se 1 (by rfl) ⟨553844, by rfl⟩ : syracuseStep 738459 = 1107689) B1107689
theorem B6931619 : Blo 738327 6931619 := bstep (se 1 (by rfl) ⟨5198714, by rfl⟩ : syracuseStep 6931619 = 10397429) B10397429
theorem B738559 : Blo 738327 738559 := bstep (se 1 (by rfl) ⟨553919, by rfl⟩ : syracuseStep 738559 = 1107839) B1107839
theorem B4212071 : Blo 738327 4212071 := bstep (se 1 (by rfl) ⟨3159053, by rfl⟩ : syracuseStep 4212071 = 6318107) B6318107
theorem B738815 : Blo 738327 738815 := bstep (se 1 (by rfl) ⟨554111, by rfl⟩ : syracuseStep 738815 = 1108223) B1108223
theorem B738971 : Blo 738327 738971 := bstep (se 1 (by rfl) ⟨554228, by rfl⟩ : syracuseStep 738971 = 1108457) B1108457
theorem B2803369 : Blo 738327 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B12667103 : Blo 738327 12667103 := bstep (se 1 (by rfl) ⟨9500327, by rfl⟩ : syracuseStep 12667103 = 19000655) B19000655
theorem B739579 : Blo 738327 739579 := bstep (se 1 (by rfl) ⟨554684, by rfl⟩ : syracuseStep 739579 = 1109369) B1109369
theorem B739655 : Blo 738327 739655 := bstep (se 1 (by rfl) ⟨554741, by rfl⟩ : syracuseStep 739655 = 1109483) B1109483
theorem B739739 : Blo 738327 739739 := bstep (se 1 (by rfl) ⟨554804, by rfl⟩ : syracuseStep 739739 = 1109609) B1109609
theorem B739951 : Blo 738327 739951 := bstep (se 1 (by rfl) ⟨554963, by rfl⟩ : syracuseStep 739951 = 1109927) B1109927
theorem B740071 : Blo 738327 740071 := bstep (se 1 (by rfl) ⟨555053, by rfl⟩ : syracuseStep 740071 = 1110107) B1110107
theorem B740463 : Blo 738327 740463 := bstep (se 1 (by rfl) ⟨555347, by rfl⟩ : syracuseStep 740463 = 1110695) B1110695
theorem B740543 : Blo 738327 740543 := bstep (se 1 (by rfl) ⟨555407, by rfl⟩ : syracuseStep 740543 = 1110815) B1110815
theorem B12799205 : Blo 738327 12799205 := bstep (se 4 (by rfl) ⟨1199925, by rfl⟩ : syracuseStep 12799205 = 2399851) B2399851
theorem B16240027 : Blo 738327 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B740863 : Blo 738327 740863 := bstep (se 1 (by rfl) ⟨555647, by rfl⟩ : syracuseStep 740863 = 1111295) B1111295
theorem B741311 : Blo 738327 741311 := bstep (se 1 (by rfl) ⟨555983, by rfl⟩ : syracuseStep 741311 = 1111967) B1111967
theorem B15159563 : Blo 738327 15159563 := bstep (se 1 (by rfl) ⟨11369672, by rfl⟩ : syracuseStep 15159563 = 22739345) B22739345
theorem B3756617 : Blo 738327 3756617 := bstep (se 2 (by rfl) ⟨1408731, by rfl⟩ : syracuseStep 3756617 = 2817463) B2817463
theorem B276976259 : Blo 738327 276976259 := bstep (se 1 (by rfl) ⟨207732194, by rfl⟩ : syracuseStep 276976259 = 415464389) B415464389
theorem B742055 : Blo 738327 742055 := bstep (se 1 (by rfl) ⟨556541, by rfl⟩ : syracuseStep 742055 = 1113083) B1113083
theorem B742095 : Blo 738327 742095 := bstep (se 1 (by rfl) ⟨556571, by rfl⟩ : syracuseStep 742095 = 1113143) B1113143
theorem B3756779 : Blo 738327 3756779 := bstep (se 1 (by rfl) ⟨2817584, by rfl⟩ : syracuseStep 3756779 = 5635169) B5635169
theorem B742175 : Blo 738327 742175 := bstep (se 1 (by rfl) ⟨556631, by rfl⟩ : syracuseStep 742175 = 1113263) B1113263
theorem B7328593 : Blo 738327 7328593 := bstep (se 2 (by rfl) ⟨2748222, by rfl⟩ : syracuseStep 7328593 = 5496445) B5496445
theorem B4215671 : Blo 738327 4215671 := bstep (se 1 (by rfl) ⟨3161753, by rfl⟩ : syracuseStep 4215671 = 6323507) B6323507
theorem B15422345 : Blo 738327 15422345 := bstep (se 2 (by rfl) ⟨5783379, by rfl⟩ : syracuseStep 15422345 = 11566759) B11566759
theorem B7099721 : Blo 738327 7099721 := bstep (se 2 (by rfl) ⟨2662395, by rfl⟩ : syracuseStep 7099721 = 5324791) B5324791
theorem B3200411 : Blo 738327 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B8411201 : Blo 738327 8411201 := bstep (se 2 (by rfl) ⟨3154200, by rfl⟩ : syracuseStep 8411201 = 6308401) B6308401
theorem B2251165 : Blo 738327 2251165 := bstep (se 3 (by rfl) ⟨422093, by rfl⟩ : syracuseStep 2251165 = 844187) B844187
theorem B1661705 : Blo 738327 1661705 := bstep (se 2 (by rfl) ⟨623139, by rfl⟩ : syracuseStep 1661705 = 1246279) B1246279
theorem B1662047 : Blo 738327 1662047 := bstep (se 1 (by rfl) ⟨1246535, by rfl⟩ : syracuseStep 1662047 = 2493071) B2493071
theorem B3857503 : Blo 738327 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B1662281 : Blo 738327 1662281 := bstep (se 2 (by rfl) ⟨623355, by rfl⟩ : syracuseStep 1662281 = 1246711) B1246711
theorem B1662443 : Blo 738327 1662443 := bstep (se 1 (by rfl) ⟨1246832, by rfl⟩ : syracuseStep 1662443 = 2493665) B2493665
theorem B14245571 : Blo 738327 14245571 := bstep (se 1 (by rfl) ⟨10684178, by rfl⟩ : syracuseStep 14245571 = 21368357) B21368357
theorem B1662695 : Blo 738327 1662695 := bstep (se 1 (by rfl) ⟨1247021, by rfl⟩ : syracuseStep 1662695 = 2494043) B2494043
theorem B1663271 : Blo 738327 1663271 := bstep (se 1 (by rfl) ⟨1247453, by rfl⟩ : syracuseStep 1663271 = 2494907) B2494907
theorem B8118623 : Blo 738327 8118623 := bstep (se 1 (by rfl) ⟨6088967, by rfl⟩ : syracuseStep 8118623 = 12177935) B12177935
theorem B1499561 : Blo 738327 1499561 := bstep (se 2 (by rfl) ⟨562335, by rfl⟩ : syracuseStep 1499561 = 1124671) B1124671
theorem B1663721 : Blo 738327 1663721 := bstep (se 2 (by rfl) ⟨623895, by rfl⟩ : syracuseStep 1663721 = 1247791) B1247791
theorem B10675415 : Blo 738327 10675415 := bstep (se 1 (by rfl) ⟨8006561, by rfl⟩ : syracuseStep 10675415 = 16013123) B16013123
theorem B4744423 : Blo 738327 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B2811145 : Blo 738327 2811145 := bstep (se 2 (by rfl) ⟨1054179, by rfl⟩ : syracuseStep 2811145 = 2108359) B2108359
theorem B1664495 : Blo 738327 1664495 := bstep (se 1 (by rfl) ⟨1248371, by rfl⟩ : syracuseStep 1664495 = 2496743) B2496743
theorem B23062067 : Blo 738327 23062067 := bstep (se 1 (by rfl) ⟨17296550, by rfl⟩ : syracuseStep 23062067 = 34593101) B34593101
theorem B4810303 : Blo 738327 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B2844559 : Blo 738327 2844559 := bstep (se 1 (by rfl) ⟨2133419, by rfl⟩ : syracuseStep 2844559 = 4266839) B4266839
theorem B1664999 : Blo 738327 1664999 := bstep (se 1 (by rfl) ⟨1248749, by rfl⟩ : syracuseStep 1664999 = 2497499) B2497499
theorem B2812103 : Blo 738327 2812103 := bstep (se 1 (by rfl) ⟨2109077, by rfl⟩ : syracuseStep 2812103 = 4218155) B4218155
theorem B1108175 : Blo 738327 1108175 := bstep (se 1 (by rfl) ⟨831131, by rfl⟩ : syracuseStep 1108175 = 1662263) B1662263
theorem B24308369 : Blo 738327 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B1108775 : Blo 738327 1108775 := bstep (se 1 (by rfl) ⟨831581, by rfl⟩ : syracuseStep 1108775 = 1663163) B1663163
theorem B1666025 : Blo 738327 1666025 := bstep (se 2 (by rfl) ⟨624759, by rfl⟩ : syracuseStep 1666025 = 1249519) B1249519
theorem B1666259 : Blo 738327 1666259 := bstep (se 1 (by rfl) ⟨1249694, by rfl⟩ : syracuseStep 1666259 = 2499389) B2499389
theorem B7204069 : Blo 738327 7204069 := bstep (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) B1350763
theorem B1666529 : Blo 738327 1666529 := bstep (se 2 (by rfl) ⟨624948, by rfl⟩ : syracuseStep 1666529 = 1249897) B1249897
theorem B1109711 : Blo 738327 1109711 := bstep (se 1 (by rfl) ⟨832283, by rfl⟩ : syracuseStep 1109711 = 1664567) B1664567
theorem B1109951 : Blo 738327 1109951 := bstep (se 1 (by rfl) ⟨832463, by rfl⟩ : syracuseStep 1109951 = 1664927) B1664927
theorem B1667051 : Blo 738327 1667051 := bstep (se 1 (by rfl) ⟨1250288, by rfl⟩ : syracuseStep 1667051 = 2500577) B2500577
theorem B1405019 : Blo 738327 1405019 := bstep (se 1 (by rfl) ⟨1053764, by rfl⟩ : syracuseStep 1405019 = 2107529) B2107529
theorem B1110119 : Blo 738327 1110119 := bstep (se 1 (by rfl) ⟨832589, by rfl⟩ : syracuseStep 1110119 = 1665179) B1665179
theorem B1405163 : Blo 738327 1405163 := bstep (se 1 (by rfl) ⟨1053872, by rfl⟩ : syracuseStep 1405163 = 2107745) B2107745
theorem B1110311 : Blo 738327 1110311 := bstep (se 1 (by rfl) ⟨832733, by rfl⟩ : syracuseStep 1110311 = 1665467) B1665467
theorem B1503559 : Blo 738327 1503559 := bstep (se 1 (by rfl) ⟨1127669, by rfl⟩ : syracuseStep 1503559 = 2255339) B2255339
theorem B8450567 : Blo 738327 8450567 := bstep (se 1 (by rfl) ⟨6337925, by rfl⟩ : syracuseStep 8450567 = 12675851) B12675851
theorem B1667753 : Blo 738327 1667753 := bstep (se 2 (by rfl) ⟨625407, by rfl⟩ : syracuseStep 1667753 = 1250815) B1250815
theorem B1668257 : Blo 738327 1668257 := bstep (se 2 (by rfl) ⟨625596, by rfl⟩ : syracuseStep 1668257 = 1251193) B1251193
theorem B1111271 : Blo 738327 1111271 := bstep (se 1 (by rfl) ⟨833453, by rfl⟩ : syracuseStep 1111271 = 1666907) B1666907
theorem B1668527 : Blo 738327 1668527 := bstep (se 1 (by rfl) ⟨1251395, by rfl⟩ : syracuseStep 1668527 = 2502791) B2502791
theorem B1668635 : Blo 738327 1668635 := bstep (se 1 (by rfl) ⟨1251476, by rfl⟩ : syracuseStep 1668635 = 2502953) B2502953
theorem B7206569 : Blo 738327 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B1111919 : Blo 738327 1111919 := bstep (se 1 (by rfl) ⟨833939, by rfl⟩ : syracuseStep 1111919 = 1667879) B1667879
theorem B1899001 : Blo 738327 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B8419949 : Blo 738327 8419949 := bstep (se 3 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 8419949 = 3157481) B3157481
theorem B1669787 : Blo 738327 1669787 := bstep (se 1 (by rfl) ⟨1252340, by rfl⟩ : syracuseStep 1669787 = 2504681) B2504681
theorem B1112783 : Blo 738327 1112783 := bstep (se 1 (by rfl) ⟨834587, by rfl⟩ : syracuseStep 1112783 = 1669175) B1669175
theorem B1112969 : Blo 738327 1112969 := bstep (se 2 (by rfl) ⟨417363, by rfl⟩ : syracuseStep 1112969 = 834727) B834727
theorem B1113023 : Blo 738327 1113023 := bstep (se 1 (by rfl) ⟨834767, by rfl⟩ : syracuseStep 1113023 = 1669535) B1669535
theorem B14220967 : Blo 738327 14220967 := bstep (se 1 (by rfl) ⟨10665725, by rfl⟩ : syracuseStep 14220967 = 21331451) B21331451
theorem B27393815 : Blo 738327 27393815 := bstep (se 1 (by rfl) ⟨20545361, by rfl⟩ : syracuseStep 27393815 = 41090723) B41090723
theorem B8421407 : Blo 738327 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B2818223 : Blo 738327 2818223 := bstep (se 1 (by rfl) ⟨2113667, by rfl⟩ : syracuseStep 2818223 = 4227335) B4227335
theorem B4621079 : Blo 738327 4621079 := bstep (se 1 (by rfl) ⟨3465809, by rfl⟩ : syracuseStep 4621079 = 6931619) B6931619
theorem B1246043 : Blo 738327 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B6325897 : Blo 738327 6325897 := bstep (se 2 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 6325897 = 4744423) B4744423
theorem B3737825 : Blo 738327 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B2493341 : Blo 738327 2493341 := bstep (se 3 (by rfl) ⟨467501, by rfl⟩ : syracuseStep 2493341 = 935003) B935003
theorem B184650839 : Blo 738327 184650839 := bstep (se 1 (by rfl) ⟨138488129, by rfl⟩ : syracuseStep 184650839 = 276976259) B276976259
theorem B2133607 : Blo 738327 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B5345149 : Blo 738327 5345149 := bstep (se 3 (by rfl) ⟨1002215, by rfl⟩ : syracuseStep 5345149 = 2004431) B2004431
theorem B5607467 : Blo 738327 5607467 := bstep (se 1 (by rfl) ⟨4205600, by rfl⟩ : syracuseStep 5607467 = 8411201) B8411201
theorem B3739931 : Blo 738327 3739931 := bstep (se 1 (by rfl) ⟨2804948, by rfl⟩ : syracuseStep 3739931 = 5609897) B5609897
theorem B9605425 : Blo 738327 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B4002415 : Blo 738327 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B1249951 : Blo 738327 1249951 := bstep (se 1 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 1249951 = 1874927) B1874927
theorem B3380089 : Blo 738327 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B1250255 : Blo 738327 1250255 := bstep (se 1 (by rfl) ⟨937691, by rfl⟩ : syracuseStep 1250255 = 1875383) B1875383
theorem B1250795 : Blo 738327 1250795 := bstep (se 1 (by rfl) ⟨938096, by rfl⟩ : syracuseStep 1250795 = 1876193) B1876193
theorem B5412415 : Blo 738327 5412415 := bstep (se 1 (by rfl) ⟨4059311, by rfl⟩ : syracuseStep 5412415 = 8118623) B8118623
theorem B2496095 : Blo 738327 2496095 := bstep (se 1 (by rfl) ⟨1872071, by rfl⟩ : syracuseStep 2496095 = 3744143) B3744143
theorem B1250923 : Blo 738327 1250923 := bstep (se 1 (by rfl) ⟨938192, by rfl⟩ : syracuseStep 1250923 = 1876385) B1876385
theorem B2004745 : Blo 738327 2004745 := bstep (se 2 (by rfl) ⟨751779, by rfl⟩ : syracuseStep 2004745 = 1503559) B1503559
theorem B1775719 : Blo 738327 1775719 := bstep (se 1 (by rfl) ⟨1331789, by rfl⟩ : syracuseStep 1775719 = 2663579) B2663579
theorem B7116943 : Blo 738327 7116943 := bstep (se 1 (by rfl) ⟨5337707, by rfl⟩ : syracuseStep 7116943 = 10675415) B10675415
theorem B1775951 : Blo 738327 1775951 := bstep (se 1 (by rfl) ⟨1331963, by rfl⟩ : syracuseStep 1775951 = 2663927) B2663927
theorem B15374711 : Blo 738327 15374711 := bstep (se 1 (by rfl) ⟨11531033, by rfl⟩ : syracuseStep 15374711 = 23062067) B23062067
theorem B9771457 : Blo 738327 9771457 := bstep (se 2 (by rfl) ⟨3664296, by rfl⟩ : syracuseStep 9771457 = 7328593) B7328593
theorem B6003497 : Blo 738327 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B1874735 : Blo 738327 1874735 := bstep (se 1 (by rfl) ⟨1406051, by rfl⟩ : syracuseStep 1874735 = 2812103) B2812103
theorem B1187951 : Blo 738327 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B21897839 : Blo 738327 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B2532001 : Blo 738327 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B2499767 : Blo 738327 2499767 := bstep (se 1 (by rfl) ⟨1874825, by rfl⟩ : syracuseStep 2499767 = 3749651) B3749651
theorem B2500199 : Blo 738327 2500199 := bstep (se 1 (by rfl) ⟨1875149, by rfl⟩ : syracuseStep 2500199 = 3750299) B3750299
theorem B5613299 : Blo 738327 5613299 := bstep (se 1 (by rfl) ⟨4209974, by rfl⟩ : syracuseStep 5613299 = 8419949) B8419949
theorem B2500847 : Blo 738327 2500847 := bstep (se 1 (by rfl) ⟨1875635, by rfl⟩ : syracuseStep 2500847 = 3751271) B3751271
theorem B4205033 : Blo 738327 4205033 := bstep (se 2 (by rfl) ⟨1576887, by rfl⟩ : syracuseStep 4205033 = 3153775) B3153775
theorem B18262543 : Blo 738327 18262543 := bstep (se 1 (by rfl) ⟨13696907, by rfl⟩ : syracuseStep 18262543 = 27393815) B27393815
theorem B2566891 : Blo 738327 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B2501387 : Blo 738327 2501387 := bstep (se 1 (by rfl) ⟨1876040, by rfl⟩ : syracuseStep 2501387 = 3752081) B3752081
theorem B2404255 : Blo 738327 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B3748193 : Blo 738327 3748193 := bstep (se 2 (by rfl) ⟨1405572, by rfl⟩ : syracuseStep 3748193 = 2811145) B2811145
theorem B8532803 : Blo 738327 8532803 := bstep (se 1 (by rfl) ⟨6399602, by rfl⟩ : syracuseStep 8532803 = 12799205) B12799205
theorem B10106375 : Blo 738327 10106375 := bstep (se 1 (by rfl) ⟨7579781, by rfl⟩ : syracuseStep 10106375 = 15159563) B15159563
theorem B2504411 : Blo 738327 2504411 := bstep (se 1 (by rfl) ⟨1878308, by rfl⟩ : syracuseStep 2504411 = 3756617) B3756617
theorem B2504519 : Blo 738327 2504519 := bstep (se 1 (by rfl) ⟨1878389, by rfl⟩ : syracuseStep 2504519 = 3756779) B3756779
theorem B4733147 : Blo 738327 4733147 := bstep (se 1 (by rfl) ⟨3549860, by rfl⟩ : syracuseStep 4733147 = 7099721) B7099721
theorem B833791 : Blo 738327 833791 := bstep (se 1 (by rfl) ⟨625343, by rfl⟩ : syracuseStep 833791 = 1250687) B1250687
theorem B8435987 : Blo 738327 8435987 := bstep (se 1 (by rfl) ⟨6326990, by rfl⟩ : syracuseStep 8435987 = 12653981) B12653981
theorem B834799 : Blo 738327 834799 := bstep (se 1 (by rfl) ⟨626099, by rfl⟩ : syracuseStep 834799 = 1252199) B1252199
theorem B2113577 : Blo 738327 2113577 := bstep (se 2 (by rfl) ⟨792591, by rfl⟩ : syracuseStep 2113577 = 1585183) B1585183
theorem B999707 : Blo 738327 999707 := bstep (se 1 (by rfl) ⟨749780, by rfl⟩ : syracuseStep 999707 = 1499561) B1499561
theorem B7127675 : Blo 738327 7127675 := bstep (se 1 (by rfl) ⟨5345756, by rfl⟩ : syracuseStep 7127675 = 10691513) B10691513
theorem B738783 : Blo 738327 738783 := bstep (se 1 (by rfl) ⟨554087, by rfl⟩ : syracuseStep 738783 = 1108175) B1108175
theorem B16205579 : Blo 738327 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B739183 : Blo 738327 739183 := bstep (se 1 (by rfl) ⟨554387, by rfl⟩ : syracuseStep 739183 = 1108775) B1108775
theorem B2410399 : Blo 738327 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B739807 : Blo 738327 739807 := bstep (se 1 (by rfl) ⟨554855, by rfl⟩ : syracuseStep 739807 = 1109711) B1109711
theorem B739967 : Blo 738327 739967 := bstep (se 1 (by rfl) ⟨554975, by rfl⟩ : syracuseStep 739967 = 1109951) B1109951
theorem B936679 : Blo 738327 936679 := bstep (se 1 (by rfl) ⟨702509, by rfl⟩ : syracuseStep 936679 = 1405019) B1405019
theorem B740079 : Blo 738327 740079 := bstep (se 1 (by rfl) ⟨555059, by rfl⟩ : syracuseStep 740079 = 1110119) B1110119
theorem B936775 : Blo 738327 936775 := bstep (se 1 (by rfl) ⟨702581, by rfl⟩ : syracuseStep 936775 = 1405163) B1405163
theorem B740207 : Blo 738327 740207 := bstep (se 1 (by rfl) ⟨555155, by rfl⟩ : syracuseStep 740207 = 1110311) B1110311
theorem B7130015 : Blo 738327 7130015 := bstep (se 1 (by rfl) ⟨5347511, by rfl⟩ : syracuseStep 7130015 = 10695023) B10695023
theorem B3001553 : Blo 738327 3001553 := bstep (se 2 (by rfl) ⟨1125582, by rfl⟩ : syracuseStep 3001553 = 2251165) B2251165
theorem B740847 : Blo 738327 740847 := bstep (se 1 (by rfl) ⟨555635, by rfl⟩ : syracuseStep 740847 = 1111271) B1111271
theorem B4804379 : Blo 738327 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B741279 : Blo 738327 741279 := bstep (se 1 (by rfl) ⟨555959, by rfl⟩ : syracuseStep 741279 = 1111919) B1111919
theorem B741855 : Blo 738327 741855 := bstep (se 1 (by rfl) ⟨556391, by rfl⟩ : syracuseStep 741855 = 1112783) B1112783
theorem B741979 : Blo 738327 741979 := bstep (se 1 (by rfl) ⟨556484, by rfl⟩ : syracuseStep 741979 = 1112969) B1112969
theorem B742015 : Blo 738327 742015 := bstep (se 1 (by rfl) ⟨556511, by rfl⟩ : syracuseStep 742015 = 1113023) B1113023
theorem B18961289 : Blo 738327 18961289 := bstep (se 2 (by rfl) ⟨7110483, by rfl⟩ : syracuseStep 18961289 = 14220967) B14220967
theorem B2807561 : Blo 738327 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B10836031 : Blo 738327 10836031 := bstep (se 1 (by rfl) ⟨8127023, by rfl⟩ : syracuseStep 10836031 = 16254047) B16254047
theorem B2808047 : Blo 738327 2808047 := bstep (se 1 (by rfl) ⟨2106035, by rfl⟩ : syracuseStep 2808047 = 4212071) B4212071
theorem B1497761 : Blo 738327 1497761 := bstep (se 2 (by rfl) ⟨561660, by rfl⟩ : syracuseStep 1497761 = 1123321) B1123321
theorem B8444735 : Blo 738327 8444735 := bstep (se 1 (by rfl) ⟨6333551, by rfl⟩ : syracuseStep 8444735 = 12667103) B12667103
theorem B6413737 : Blo 738327 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B3792745 : Blo 738327 3792745 := bstep (se 2 (by rfl) ⟨1422279, by rfl⟩ : syracuseStep 3792745 = 2844559) B2844559
theorem B2810447 : Blo 738327 2810447 := bstep (se 1 (by rfl) ⟨2107835, by rfl⟩ : syracuseStep 2810447 = 4215671) B4215671
theorem B10281563 : Blo 738327 10281563 := bstep (se 1 (by rfl) ⟨7711172, by rfl⟩ : syracuseStep 10281563 = 15422345) B15422345
theorem B1663631 : Blo 738327 1663631 := bstep (se 1 (by rfl) ⟨1247723, by rfl⟩ : syracuseStep 1663631 = 2495447) B2495447
theorem B1663649 : Blo 738327 1663649 := bstep (se 2 (by rfl) ⟨623868, by rfl⟩ : syracuseStep 1663649 = 1247737) B1247737
theorem B2843867 : Blo 738327 2843867 := bstep (se 1 (by rfl) ⟨2132900, by rfl⟩ : syracuseStep 2843867 = 4265801) B4265801
theorem B9463013 : Blo 738327 9463013 := bstep (se 4 (by rfl) ⟨887157, by rfl⟩ : syracuseStep 9463013 = 1774315) B1774315
theorem B5400011 : Blo 738327 5400011 := bstep (se 1 (by rfl) ⟨4050008, by rfl⟩ : syracuseStep 5400011 = 8100017) B8100017
theorem B1664603 : Blo 738327 1664603 := bstep (se 1 (by rfl) ⟨1248452, by rfl⟩ : syracuseStep 1664603 = 2496905) B2496905
theorem B2811617 : Blo 738327 2811617 := bstep (se 2 (by rfl) ⟨1054356, by rfl⟩ : syracuseStep 2811617 = 2108713) B2108713
theorem B1107803 : Blo 738327 1107803 := bstep (se 1 (by rfl) ⟨830852, by rfl⟩ : syracuseStep 1107803 = 1661705) B1661705
theorem B21653369 : Blo 738327 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B1107881 : Blo 738327 1107881 := bstep (se 2 (by rfl) ⟨415455, by rfl⟩ : syracuseStep 1107881 = 830911) B830911
theorem B1108031 : Blo 738327 1108031 := bstep (se 1 (by rfl) ⟨831023, by rfl⟩ : syracuseStep 1108031 = 1662047) B1662047
theorem B1108187 : Blo 738327 1108187 := bstep (se 1 (by rfl) ⟨831140, by rfl⟩ : syracuseStep 1108187 = 1662281) B1662281
theorem B1108295 : Blo 738327 1108295 := bstep (se 1 (by rfl) ⟨831221, by rfl⟩ : syracuseStep 1108295 = 1662443) B1662443
theorem B1665359 : Blo 738327 1665359 := bstep (se 1 (by rfl) ⟨1249019, by rfl⟩ : syracuseStep 1665359 = 2498039) B2498039
theorem B9497047 : Blo 738327 9497047 := bstep (se 1 (by rfl) ⟨7122785, by rfl⟩ : syracuseStep 9497047 = 14245571) B14245571
theorem B1108463 : Blo 738327 1108463 := bstep (se 1 (by rfl) ⟨831347, by rfl⟩ : syracuseStep 1108463 = 1662695) B1662695
theorem B1108847 : Blo 738327 1108847 := bstep (se 1 (by rfl) ⟨831635, by rfl⟩ : syracuseStep 1108847 = 1663271) B1663271
theorem B1109147 : Blo 738327 1109147 := bstep (se 1 (by rfl) ⟨831860, by rfl⟩ : syracuseStep 1109147 = 1663721) B1663721
theorem B1109663 : Blo 738327 1109663 := bstep (se 1 (by rfl) ⟨832247, by rfl⟩ : syracuseStep 1109663 = 1664495) B1664495
theorem B1109999 : Blo 738327 1109999 := bstep (se 1 (by rfl) ⟨832499, by rfl⟩ : syracuseStep 1109999 = 1664999) B1664999
theorem B5632253 : Blo 738327 5632253 := bstep (se 3 (by rfl) ⟨1056047, by rfl⟩ : syracuseStep 5632253 = 2112095) B2112095
theorem B1110683 : Blo 738327 1110683 := bstep (se 1 (by rfl) ⟨833012, by rfl⟩ : syracuseStep 1110683 = 1666025) B1666025
theorem B1110839 : Blo 738327 1110839 := bstep (se 1 (by rfl) ⟨833129, by rfl⟩ : syracuseStep 1110839 = 1666259) B1666259
theorem B1111019 : Blo 738327 1111019 := bstep (se 1 (by rfl) ⟨833264, by rfl⟩ : syracuseStep 1111019 = 1666529) B1666529
theorem B1111367 : Blo 738327 1111367 := bstep (se 1 (by rfl) ⟨833525, by rfl⟩ : syracuseStep 1111367 = 1667051) B1667051
theorem B5633711 : Blo 738327 5633711 := bstep (se 1 (by rfl) ⟨4225283, by rfl⟩ : syracuseStep 5633711 = 8450567) B8450567
theorem B1111835 : Blo 738327 1111835 := bstep (se 1 (by rfl) ⟨833876, by rfl⟩ : syracuseStep 1111835 = 1667753) B1667753
theorem B1406803 : Blo 738327 1406803 := bstep (se 1 (by rfl) ⟨1055102, by rfl⟩ : syracuseStep 1406803 = 2110205) B2110205
theorem B1406879 : Blo 738327 1406879 := bstep (se 1 (by rfl) ⟨1055159, by rfl⟩ : syracuseStep 1406879 = 2110319) B2110319
theorem B1669031 : Blo 738327 1669031 := bstep (se 1 (by rfl) ⟨1251773, by rfl⟩ : syracuseStep 1669031 = 2503547) B2503547
theorem B1112171 : Blo 738327 1112171 := bstep (se 1 (by rfl) ⟨834128, by rfl⟩ : syracuseStep 1112171 = 1668257) B1668257
theorem B1112201 : Blo 738327 1112201 := bstep (se 2 (by rfl) ⟨417075, by rfl⟩ : syracuseStep 1112201 = 834151) B834151
theorem B1112351 : Blo 738327 1112351 := bstep (se 1 (by rfl) ⟨834263, by rfl⟩ : syracuseStep 1112351 = 1668527) B1668527
theorem B1112423 : Blo 738327 1112423 := bstep (se 1 (by rfl) ⟨834317, by rfl⟩ : syracuseStep 1112423 = 1668635) B1668635
theorem B4225445 : Blo 738327 4225445 := bstep (se 4 (by rfl) ⟨396135, by rfl⟩ : syracuseStep 4225445 = 792271) B792271
theorem B21658043 : Blo 738327 21658043 := bstep (se 1 (by rfl) ⟨16243532, by rfl⟩ : syracuseStep 21658043 = 32487065) B32487065
theorem B2816765 : Blo 738327 2816765 := bstep (se 3 (by rfl) ⟨528143, by rfl⟩ : syracuseStep 2816765 = 1056287) B1056287
theorem B5143337 : Blo 738327 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B1113191 : Blo 738327 1113191 := bstep (se 1 (by rfl) ⟨834893, by rfl⟩ : syracuseStep 1113191 = 1669787) B1669787
theorem B1113257 : Blo 738327 1113257 := bstep (se 2 (by rfl) ⟨417471, by rfl⟩ : syracuseStep 1113257 = 834943) B834943
theorem B1409051 : Blo 738327 1409051 := bstep (se 1 (by rfl) ⟨1056788, by rfl⟩ : syracuseStep 1409051 = 2113577) B2113577
theorem B4751783 : Blo 738327 4751783 := bstep (se 1 (by rfl) ⟨3563837, by rfl⟩ : syracuseStep 4751783 = 7127675) B7127675
theorem B3080719 : Blo 738327 3080719 := bstep (se 1 (by rfl) ⟨2310539, by rfl⟩ : syracuseStep 3080719 = 4621079) B4621079
theorem B3376001 : Blo 738327 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B2491883 : Blo 738327 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B4753343 : Blo 738327 4753343 := bstep (se 1 (by rfl) ⟨3565007, by rfl⟩ : syracuseStep 4753343 = 7130015) B7130015
theorem B2001035 : Blo 738327 2001035 := bstep (se 1 (by rfl) ⟨1500776, by rfl⟩ : syracuseStep 2001035 = 3001553) B3001553
theorem B3213865 : Blo 738327 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B3738311 : Blo 738327 3738311 := bstep (se 1 (by rfl) ⟨2803733, by rfl⟩ : syracuseStep 3738311 = 5607467) B5607467
theorem B2493287 : Blo 738327 2493287 := bstep (se 1 (by rfl) ⟨1869965, by rfl⟩ : syracuseStep 2493287 = 3739931) B3739931
theorem B24350057 : Blo 738327 24350057 := bstep (se 2 (by rfl) ⟨9131271, by rfl⟩ : syracuseStep 24350057 = 18262543) B18262543
theorem B1248905 : Blo 738327 1248905 := bstep (se 2 (by rfl) ⟨468339, by rfl⟩ : syracuseStep 1248905 = 936679) B936679
theorem B1249033 : Blo 738327 1249033 := bstep (se 2 (by rfl) ⟨468387, by rfl⟩ : syracuseStep 1249033 = 936775) B936775
theorem B1871707 : Blo 738327 1871707 := bstep (se 1 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 1871707 = 2807561) B2807561
theorem B1872031 : Blo 738327 1872031 := bstep (se 1 (by rfl) ⟨1404023, by rfl⟩ : syracuseStep 1872031 = 2808047) B2808047
theorem B1183967 : Blo 738327 1183967 := bstep (se 1 (by rfl) ⟨887975, by rfl⟩ : syracuseStep 1183967 = 1775951) B1775951
theorem B4002331 : Blo 738327 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B1249823 : Blo 738327 1249823 := bstep (se 1 (by rfl) ⟨937367, by rfl⟩ : syracuseStep 1249823 = 1874735) B1874735
theorem B1873631 : Blo 738327 1873631 := bstep (se 1 (by rfl) ⟨1405223, by rfl⟩ : syracuseStep 1873631 = 2810447) B2810447
theorem B6854375 : Blo 738327 6854375 := bstep (se 1 (by rfl) ⟨5140781, by rfl⟩ : syracuseStep 6854375 = 10281563) B10281563
theorem B40999229 : Blo 738327 40999229 := bstep (se 3 (by rfl) ⟨7687355, by rfl⟩ : syracuseStep 40999229 = 15374711) B15374711
theorem B1874411 : Blo 738327 1874411 := bstep (se 1 (by rfl) ⟨1405808, by rfl⟩ : syracuseStep 1874411 = 2811617) B2811617
theorem B3742199 : Blo 738327 3742199 := bstep (se 1 (by rfl) ⟨2806649, by rfl⟩ : syracuseStep 3742199 = 5613299) B5613299
theorem B7216553 : Blo 738327 7216553 := bstep (se 2 (by rfl) ⟨2706207, by rfl⟩ : syracuseStep 7216553 = 5412415) B5412415
theorem B1875737 : Blo 738327 1875737 := bstep (se 2 (by rfl) ⟨703401, by rfl⟩ : syracuseStep 1875737 = 1406803) B1406803
theorem B2367625 : Blo 738327 2367625 := bstep (se 2 (by rfl) ⟨887859, by rfl⟩ : syracuseStep 2367625 = 1775719) B1775719
theorem B2498795 : Blo 738327 2498795 := bstep (se 1 (by rfl) ⟨1874096, by rfl⟩ : syracuseStep 2498795 = 3748193) B3748193
theorem B3155431 : Blo 738327 3155431 := bstep (se 1 (by rfl) ⟨2366573, by rfl⟩ : syracuseStep 3155431 = 4733147) B4733147
theorem B1877843 : Blo 738327 1877843 := bstep (se 1 (by rfl) ⟨1408382, by rfl⟩ : syracuseStep 1877843 = 2816765) B2816765
theorem B20227973 : Blo 738327 20227973 := bstep (se 4 (by rfl) ⟨1896372, by rfl⟩ : syracuseStep 20227973 = 3792745) B3792745
theorem B5614271 : Blo 738327 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B1878815 : Blo 738327 1878815 := bstep (se 1 (by rfl) ⟨1409111, by rfl⟩ : syracuseStep 1878815 = 2818223) B2818223
theorem B830695 : Blo 738327 830695 := bstep (se 1 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 830695 = 1246043) B1246043
theorem B2665885 : Blo 738327 2665885 := bstep (se 3 (by rfl) ⟨499853, by rfl⟩ : syracuseStep 2665885 = 999707) B999707
theorem B22754141 : Blo 738327 22754141 := bstep (se 3 (by rfl) ⟨4266401, by rfl⟩ : syracuseStep 22754141 = 8532803) B8532803
theorem B8434529 : Blo 738327 8434529 := bstep (se 2 (by rfl) ⟨3162948, by rfl⟩ : syracuseStep 8434529 = 6325897) B6325897
theorem B7583645 : Blo 738327 7583645 := bstep (se 3 (by rfl) ⟨1421933, by rfl⟩ : syracuseStep 7583645 = 2843867) B2843867
theorem B21346213 : Blo 738327 21346213 := bstep (se 4 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 21346213 = 4002415) B4002415
theorem B12662729 : Blo 738327 12662729 := bstep (se 2 (by rfl) ⟨4748523, by rfl⟩ : syracuseStep 12662729 = 9497047) B9497047
theorem B833503 : Blo 738327 833503 := bstep (se 1 (by rfl) ⟨625127, by rfl⟩ : syracuseStep 833503 = 1250255) B1250255
theorem B3422521 : Blo 738327 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B833863 : Blo 738327 833863 := bstep (se 1 (by rfl) ⟨625397, by rfl⟩ : syracuseStep 833863 = 1250795) B1250795
theorem B26950333 : Blo 738327 26950333 := bstep (se 3 (by rfl) ⟨5053187, by rfl⟩ : syracuseStep 26950333 = 10106375) B10106375
theorem B998507 : Blo 738327 998507 := bstep (se 1 (by rfl) ⟨748880, by rfl⟩ : syracuseStep 998507 = 1497761) B1497761
theorem B7126865 : Blo 738327 7126865 := bstep (se 2 (by rfl) ⟨2672574, by rfl⟩ : syracuseStep 7126865 = 5345149) B5345149
theorem B14598559 : Blo 738327 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B6308675 : Blo 738327 6308675 := bstep (se 1 (by rfl) ⟨4731506, by rfl⟩ : syracuseStep 6308675 = 9463013) B9463013
theorem B4506785 : Blo 738327 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B738535 : Blo 738327 738535 := bstep (se 1 (by rfl) ⟨553901, by rfl⟩ : syracuseStep 738535 = 1107803) B1107803
theorem B14435579 : Blo 738327 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B738587 : Blo 738327 738587 := bstep (se 1 (by rfl) ⟨553940, by rfl⟩ : syracuseStep 738587 = 1107881) B1107881
theorem B738687 : Blo 738327 738687 := bstep (se 1 (by rfl) ⟨554015, by rfl⟩ : syracuseStep 738687 = 1108031) B1108031
theorem B738791 : Blo 738327 738791 := bstep (se 1 (by rfl) ⟨554093, by rfl⟩ : syracuseStep 738791 = 1108187) B1108187
theorem B738863 : Blo 738327 738863 := bstep (se 1 (by rfl) ⟨554147, by rfl⟩ : syracuseStep 738863 = 1108295) B1108295
theorem B2803355 : Blo 738327 2803355 := bstep (se 1 (by rfl) ⟨2102516, by rfl⟩ : syracuseStep 2803355 = 4205033) B4205033
theorem B738975 : Blo 738327 738975 := bstep (se 1 (by rfl) ⟨554231, by rfl⟩ : syracuseStep 738975 = 1108463) B1108463
theorem B739231 : Blo 738327 739231 := bstep (se 1 (by rfl) ⟨554423, by rfl⟩ : syracuseStep 739231 = 1108847) B1108847
theorem B739431 : Blo 738327 739431 := bstep (se 1 (by rfl) ⟨554573, by rfl⟩ : syracuseStep 739431 = 1109147) B1109147
theorem B2672993 : Blo 738327 2672993 := bstep (se 2 (by rfl) ⟨1002372, by rfl⟩ : syracuseStep 2672993 = 2004745) B2004745
theorem B739775 : Blo 738327 739775 := bstep (se 1 (by rfl) ⟨554831, by rfl⟩ : syracuseStep 739775 = 1109663) B1109663
theorem B739999 : Blo 738327 739999 := bstep (se 1 (by rfl) ⟨554999, by rfl⟩ : syracuseStep 739999 = 1109999) B1109999
theorem B3754835 : Blo 738327 3754835 := bstep (se 1 (by rfl) ⟨2816126, by rfl⟩ : syracuseStep 3754835 = 5632253) B5632253
theorem B9489257 : Blo 738327 9489257 := bstep (se 2 (by rfl) ⟨3558471, by rfl⟩ : syracuseStep 9489257 = 7116943) B7116943
theorem B740455 : Blo 738327 740455 := bstep (se 1 (by rfl) ⟨555341, by rfl⟩ : syracuseStep 740455 = 1110683) B1110683
theorem B740559 : Blo 738327 740559 := bstep (se 1 (by rfl) ⟨555419, by rfl⟩ : syracuseStep 740559 = 1110839) B1110839
theorem B13028609 : Blo 738327 13028609 := bstep (se 2 (by rfl) ⟨4885728, by rfl⟩ : syracuseStep 13028609 = 9771457) B9771457
theorem B740679 : Blo 738327 740679 := bstep (se 1 (by rfl) ⟨555509, by rfl⟩ : syracuseStep 740679 = 1111019) B1111019
theorem B740911 : Blo 738327 740911 := bstep (se 1 (by rfl) ⟨555683, by rfl⟩ : syracuseStep 740911 = 1111367) B1111367
theorem B3755807 : Blo 738327 3755807 := bstep (se 1 (by rfl) ⟨2816855, by rfl⟩ : syracuseStep 3755807 = 5633711) B5633711
theorem B741223 : Blo 738327 741223 := bstep (se 1 (by rfl) ⟨555917, by rfl⟩ : syracuseStep 741223 = 1111835) B1111835
theorem B937919 : Blo 738327 937919 := bstep (se 1 (by rfl) ⟨703439, by rfl⟩ : syracuseStep 937919 = 1406879) B1406879
theorem B741447 : Blo 738327 741447 := bstep (se 1 (by rfl) ⟨556085, by rfl⟩ : syracuseStep 741447 = 1112171) B1112171
theorem B741467 : Blo 738327 741467 := bstep (se 1 (by rfl) ⟨556100, by rfl⟩ : syracuseStep 741467 = 1112201) B1112201
theorem B5623991 : Blo 738327 5623991 := bstep (se 1 (by rfl) ⟨4217993, by rfl⟩ : syracuseStep 5623991 = 8435987) B8435987
theorem B741567 : Blo 738327 741567 := bstep (se 1 (by rfl) ⟨556175, by rfl⟩ : syracuseStep 741567 = 1112351) B1112351
theorem B741615 : Blo 738327 741615 := bstep (se 1 (by rfl) ⟨556211, by rfl⟩ : syracuseStep 741615 = 1112423) B1112423
theorem B14438695 : Blo 738327 14438695 := bstep (se 1 (by rfl) ⟨10829021, by rfl⟩ : syracuseStep 14438695 = 21658043) B21658043
theorem B3428891 : Blo 738327 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B742127 : Blo 738327 742127 := bstep (se 1 (by rfl) ⟨556595, by rfl⟩ : syracuseStep 742127 = 1113191) B1113191
theorem B742171 : Blo 738327 742171 := bstep (se 1 (by rfl) ⟨556628, by rfl⟩ : syracuseStep 742171 = 1113257) B1113257
theorem B12671477 : Blo 738327 12671477 := bstep (se 5 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 12671477 = 1187951) B1187951
theorem B10803719 : Blo 738327 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B1662227 : Blo 738327 1662227 := bstep (se 1 (by rfl) ⟨1246670, by rfl⟩ : syracuseStep 1662227 = 2493341) B2493341
theorem B123100559 : Blo 738327 123100559 := bstep (se 1 (by rfl) ⟨92325419, by rfl⟩ : syracuseStep 123100559 = 184650839) B184650839
theorem B3202919 : Blo 738327 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B12640859 : Blo 738327 12640859 := bstep (se 1 (by rfl) ⟨9480644, by rfl⟩ : syracuseStep 12640859 = 18961289) B18961289
theorem B1664063 : Blo 738327 1664063 := bstep (se 1 (by rfl) ⟨1248047, by rfl⟩ : syracuseStep 1664063 = 2496095) B2496095
theorem B5629823 : Blo 738327 5629823 := bstep (se 1 (by rfl) ⟨4222367, by rfl⟩ : syracuseStep 5629823 = 8444735) B8444735
theorem B2844809 : Blo 738327 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B3205673 : Blo 738327 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B12807233 : Blo 738327 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B1109087 : Blo 738327 1109087 := bstep (se 1 (by rfl) ⟨831815, by rfl⟩ : syracuseStep 1109087 = 1663631) B1663631
theorem B1109099 : Blo 738327 1109099 := bstep (se 1 (by rfl) ⟨831824, by rfl⟩ : syracuseStep 1109099 = 1663649) B1663649
theorem B1666511 : Blo 738327 1666511 := bstep (se 1 (by rfl) ⟨1249883, by rfl⟩ : syracuseStep 1666511 = 2499767) B2499767
theorem B1666601 : Blo 738327 1666601 := bstep (se 2 (by rfl) ⟨624975, by rfl⟩ : syracuseStep 1666601 = 1249951) B1249951
theorem B3600007 : Blo 738327 3600007 := bstep (se 1 (by rfl) ⟨2700005, by rfl⟩ : syracuseStep 3600007 = 5400011) B5400011
theorem B1109735 : Blo 738327 1109735 := bstep (se 1 (by rfl) ⟨832301, by rfl⟩ : syracuseStep 1109735 = 1664603) B1664603
theorem B1666799 : Blo 738327 1666799 := bstep (se 1 (by rfl) ⟨1250099, by rfl⟩ : syracuseStep 1666799 = 2500199) B2500199
theorem B1667231 : Blo 738327 1667231 := bstep (se 1 (by rfl) ⟨1250423, by rfl⟩ : syracuseStep 1667231 = 2500847) B2500847
theorem B1110239 : Blo 738327 1110239 := bstep (se 1 (by rfl) ⟨832679, by rfl⟩ : syracuseStep 1110239 = 1665359) B1665359
theorem B1667591 : Blo 738327 1667591 := bstep (se 1 (by rfl) ⟨1250693, by rfl⟩ : syracuseStep 1667591 = 2501387) B2501387
theorem B1667897 : Blo 738327 1667897 := bstep (se 2 (by rfl) ⟨625461, by rfl⟩ : syracuseStep 1667897 = 1250923) B1250923
theorem B14448041 : Blo 738327 14448041 := bstep (se 2 (by rfl) ⟨5418015, by rfl⟩ : syracuseStep 14448041 = 10836031) B10836031
theorem B1111721 : Blo 738327 1111721 := bstep (se 2 (by rfl) ⟨416895, by rfl⟩ : syracuseStep 1111721 = 833791) B833791
theorem B1669607 : Blo 738327 1669607 := bstep (se 1 (by rfl) ⟨1252205, by rfl⟩ : syracuseStep 1669607 = 2504411) B2504411
theorem B1669679 : Blo 738327 1669679 := bstep (se 1 (by rfl) ⟨1252259, by rfl⟩ : syracuseStep 1669679 = 2504519) B2504519
theorem B1112687 : Blo 738327 1112687 := bstep (se 1 (by rfl) ⟨834515, by rfl⟩ : syracuseStep 1112687 = 1669031) B1669031
theorem B2816963 : Blo 738327 2816963 := bstep (se 1 (by rfl) ⟨2112722, by rfl⟩ : syracuseStep 2816963 = 4225445) B4225445
theorem B1113065 : Blo 738327 1113065 := bstep (se 2 (by rfl) ⟨417399, by rfl⟩ : syracuseStep 1113065 = 834799) B834799
theorem B8551649 : Blo 738327 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B19464745 : Blo 738327 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B1868903 : Blo 738327 1868903 := bstep (se 1 (by rfl) ⟨1401677, by rfl⟩ : syracuseStep 1868903 = 2803355) B2803355
theorem B2492207 : Blo 738327 2492207 := bstep (se 1 (by rfl) ⟨1869155, by rfl⟩ : syracuseStep 2492207 = 3738311) B3738311
theorem B6326171 : Blo 738327 6326171 := bstep (se 1 (by rfl) ⟨4744628, by rfl⟩ : syracuseStep 6326171 = 9489257) B9489257
theorem B8685739 : Blo 738327 8685739 := bstep (se 1 (by rfl) ⟨6514304, by rfl⟩ : syracuseStep 8685739 = 13028609) B13028609
theorem B789311 : Blo 738327 789311 := bstep (se 1 (by rfl) ⟨591983, by rfl⟩ : syracuseStep 789311 = 1183967) B1183967
theorem B1249087 : Blo 738327 1249087 := bstep (se 1 (by rfl) ⟨936815, by rfl⟩ : syracuseStep 1249087 = 1873631) B1873631
theorem B27332819 : Blo 738327 27332819 := bstep (se 1 (by rfl) ⟨20499614, by rfl⟩ : syracuseStep 27332819 = 40999229) B40999229
theorem B1249607 : Blo 738327 1249607 := bstep (se 1 (by rfl) ⟨937205, by rfl⟩ : syracuseStep 1249607 = 1874411) B1874411
theorem B2494799 : Blo 738327 2494799 := bstep (se 1 (by rfl) ⟨1871099, by rfl⟩ : syracuseStep 2494799 = 3742199) B3742199
theorem B53941261 : Blo 738327 53941261 := bstep (se 3 (by rfl) ⟨10113986, by rfl⟩ : syracuseStep 53941261 = 20227973) B20227973
theorem B20223053 : Blo 738327 20223053 := bstep (se 3 (by rfl) ⟨3791822, by rfl⟩ : syracuseStep 20223053 = 7583645) B7583645
theorem B2495609 : Blo 738327 2495609 := bstep (se 2 (by rfl) ⟨935853, by rfl⟩ : syracuseStep 2495609 = 1871707) B1871707
theorem B1250491 : Blo 738327 1250491 := bstep (se 1 (by rfl) ⟨937868, by rfl⟩ : syracuseStep 1250491 = 1875737) B1875737
theorem B2135279 : Blo 738327 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B2496041 : Blo 738327 2496041 := bstep (se 2 (by rfl) ⟨936015, by rfl⟩ : syracuseStep 2496041 = 1872031) B1872031
theorem B8427239 : Blo 738327 8427239 := bstep (se 1 (by rfl) ⟨6320429, by rfl⟩ : syracuseStep 8427239 = 12640859) B12640859
theorem B1251895 : Blo 738327 1251895 := bstep (se 1 (by rfl) ⟨938921, by rfl⟩ : syracuseStep 1251895 = 1877843) B1877843
theorem B28809917 : Blo 738327 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B2137115 : Blo 738327 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B3742847 : Blo 738327 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B1252543 : Blo 738327 1252543 := bstep (se 1 (by rfl) ⟨939407, by rfl⟩ : syracuseStep 1252543 = 1878815) B1878815
theorem B2662685 : Blo 738327 2662685 := bstep (se 3 (by rfl) ⟨499253, by rfl⟩ : syracuseStep 2662685 = 998507) B998507
theorem B4563361 : Blo 738327 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B1877975 : Blo 738327 1877975 := bstep (se 1 (by rfl) ⟨1408481, by rfl⟩ : syracuseStep 1877975 = 2816963) B2816963
theorem B2501117 : Blo 738327 2501117 := bstep (se 3 (by rfl) ⟨468959, by rfl⟩ : syracuseStep 2501117 = 937919) B937919
theorem B3156833 : Blo 738327 3156833 := bstep (se 2 (by rfl) ⟨1183812, by rfl⟩ : syracuseStep 3156833 = 2367625) B2367625
theorem B4205783 : Blo 738327 4205783 := bstep (se 1 (by rfl) ⟨3154337, by rfl⟩ : syracuseStep 4205783 = 6308675) B6308675
theorem B1781995 : Blo 738327 1781995 := bstep (se 1 (by rfl) ⟨1336496, by rfl⟩ : syracuseStep 1781995 = 2672993) B2672993
theorem B2503223 : Blo 738327 2503223 := bstep (se 1 (by rfl) ⟨1877417, by rfl⟩ : syracuseStep 2503223 = 3754835) B3754835
theorem B4207241 : Blo 738327 4207241 := bstep (se 2 (by rfl) ⟨1577715, by rfl⟩ : syracuseStep 4207241 = 3155431) B3155431
theorem B16233371 : Blo 738327 16233371 := bstep (se 1 (by rfl) ⟨12175028, by rfl⟩ : syracuseStep 16233371 = 24350057) B24350057
theorem B832603 : Blo 738327 832603 := bstep (se 1 (by rfl) ⟨624452, by rfl⟩ : syracuseStep 832603 = 1248905) B1248905
theorem B2503871 : Blo 738327 2503871 := bstep (se 1 (by rfl) ⟨1877903, by rfl⟩ : syracuseStep 2503871 = 3755807) B3755807
theorem B16430501 : Blo 738327 16430501 := bstep (se 4 (by rfl) ⟨1540359, by rfl⟩ : syracuseStep 16430501 = 3080719) B3080719
theorem B3749327 : Blo 738327 3749327 := bstep (se 1 (by rfl) ⟨2811995, by rfl⟩ : syracuseStep 3749327 = 5623991) B5623991
theorem B833215 : Blo 738327 833215 := bstep (se 1 (by rfl) ⟨624911, by rfl⟩ : syracuseStep 833215 = 1249823) B1249823
theorem B4569583 : Blo 738327 4569583 := bstep (se 1 (by rfl) ⟨3427187, by rfl⟩ : syracuseStep 4569583 = 6854375) B6854375
theorem B3554513 : Blo 738327 3554513 := bstep (se 2 (by rfl) ⟨1332942, by rfl⟩ : syracuseStep 3554513 = 2665885) B2665885
theorem B82067039 : Blo 738327 82067039 := bstep (se 1 (by rfl) ⟨61550279, by rfl⟩ : syracuseStep 82067039 = 123100559) B123100559
theorem B19251593 : Blo 738327 19251593 := bstep (se 2 (by rfl) ⟨7219347, by rfl⟩ : syracuseStep 19251593 = 14438695) B14438695
theorem B3753215 : Blo 738327 3753215 := bstep (se 1 (by rfl) ⟨2814911, by rfl⟩ : syracuseStep 3753215 = 5629823) B5629823
theorem B8538155 : Blo 738327 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B739391 : Blo 738327 739391 := bstep (se 1 (by rfl) ⟨554543, by rfl⟩ : syracuseStep 739391 = 1109087) B1109087
theorem B739399 : Blo 738327 739399 := bstep (se 1 (by rfl) ⟨554549, by rfl⟩ : syracuseStep 739399 = 1109099) B1109099
theorem B739823 : Blo 738327 739823 := bstep (se 1 (by rfl) ⟨554867, by rfl⟩ : syracuseStep 739823 = 1109735) B1109735
theorem B28461617 : Blo 738327 28461617 := bstep (se 2 (by rfl) ⟨10673106, by rfl⟩ : syracuseStep 28461617 = 21346213) B21346213
theorem B740159 : Blo 738327 740159 := bstep (se 1 (by rfl) ⟨555119, by rfl⟩ : syracuseStep 740159 = 1110239) B1110239
theorem B5623019 : Blo 738327 5623019 := bstep (se 1 (by rfl) ⟨4217264, by rfl⟩ : syracuseStep 5623019 = 8434529) B8434529
theorem B35933777 : Blo 738327 35933777 := bstep (se 2 (by rfl) ⟨13475166, by rfl⟩ : syracuseStep 35933777 = 26950333) B26950333
theorem B741147 : Blo 738327 741147 := bstep (se 1 (by rfl) ⟨555860, by rfl⟩ : syracuseStep 741147 = 1111721) B1111721
theorem B8441819 : Blo 738327 8441819 := bstep (se 1 (by rfl) ⟨6331364, by rfl⟩ : syracuseStep 8441819 = 12662729) B12662729
theorem B741791 : Blo 738327 741791 := bstep (se 1 (by rfl) ⟨556343, by rfl⟩ : syracuseStep 741791 = 1112687) B1112687
theorem B742043 : Blo 738327 742043 := bstep (se 1 (by rfl) ⟨556532, by rfl⟩ : syracuseStep 742043 = 1113065) B1113065
theorem B939367 : Blo 738327 939367 := bstep (se 1 (by rfl) ⟨704525, by rfl⟩ : syracuseStep 939367 = 1409051) B1409051
theorem B3167855 : Blo 738327 3167855 := bstep (se 1 (by rfl) ⟨2375891, by rfl⟩ : syracuseStep 3167855 = 4751783) B4751783
theorem B2250667 : Blo 738327 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B3004523 : Blo 738327 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B9623719 : Blo 738327 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B1661255 : Blo 738327 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B3168895 : Blo 738327 3168895 := bstep (se 1 (by rfl) ⟨2376671, by rfl⟩ : syracuseStep 3168895 = 4753343) B4753343
theorem B1662191 : Blo 738327 1662191 := bstep (se 1 (by rfl) ⟨1246643, by rfl⟩ : syracuseStep 1662191 = 2493287) B2493287
theorem B76800149 : Blo 738327 76800149 := bstep (se 6 (by rfl) ⟨1800003, by rfl⟩ : syracuseStep 76800149 = 3600007) B3600007
theorem B2285927 : Blo 738327 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B4285153 : Blo 738327 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B1107593 : Blo 738327 1107593 := bstep (se 2 (by rfl) ⟨415347, by rfl⟩ : syracuseStep 1107593 = 830695) B830695
theorem B8447651 : Blo 738327 8447651 := bstep (se 1 (by rfl) ⟨6335738, by rfl⟩ : syracuseStep 8447651 = 12671477) B12671477
theorem B1108151 : Blo 738327 1108151 := bstep (se 1 (by rfl) ⟨831113, by rfl⟩ : syracuseStep 1108151 = 1662227) B1662227
theorem B4811035 : Blo 738327 4811035 := bstep (se 1 (by rfl) ⟨3608276, by rfl⟩ : syracuseStep 4811035 = 7216553) B7216553
theorem B1665377 : Blo 738327 1665377 := bstep (se 2 (by rfl) ⟨624516, by rfl⟩ : syracuseStep 1665377 = 1249033) B1249033
theorem B1665863 : Blo 738327 1665863 := bstep (se 1 (by rfl) ⟨1249397, by rfl⟩ : syracuseStep 1665863 = 2498795) B2498795
theorem B5336093 : Blo 738327 5336093 := bstep (se 3 (by rfl) ⟨1000517, by rfl⟩ : syracuseStep 5336093 = 2001035) B2001035
theorem B5336441 : Blo 738327 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B1109375 : Blo 738327 1109375 := bstep (se 1 (by rfl) ⟨832031, by rfl⟩ : syracuseStep 1109375 = 1664063) B1664063
theorem B1896539 : Blo 738327 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B1111007 : Blo 738327 1111007 := bstep (se 1 (by rfl) ⟨833255, by rfl⟩ : syracuseStep 1111007 = 1666511) B1666511
theorem B1111067 : Blo 738327 1111067 := bstep (se 1 (by rfl) ⟨833300, by rfl⟩ : syracuseStep 1111067 = 1666601) B1666601
theorem B1111199 : Blo 738327 1111199 := bstep (se 1 (by rfl) ⟨833399, by rfl⟩ : syracuseStep 1111199 = 1666799) B1666799
theorem B1111337 : Blo 738327 1111337 := bstep (se 2 (by rfl) ⟨416751, by rfl⟩ : syracuseStep 1111337 = 833503) B833503
theorem B1111487 : Blo 738327 1111487 := bstep (se 1 (by rfl) ⟨833615, by rfl⟩ : syracuseStep 1111487 = 1667231) B1667231
theorem B1111727 : Blo 738327 1111727 := bstep (se 1 (by rfl) ⟨833795, by rfl⟩ : syracuseStep 1111727 = 1667591) B1667591
theorem B1111817 : Blo 738327 1111817 := bstep (se 2 (by rfl) ⟨416931, by rfl⟩ : syracuseStep 1111817 = 833863) B833863
theorem B1111931 : Blo 738327 1111931 := bstep (se 1 (by rfl) ⟨833948, by rfl⟩ : syracuseStep 1111931 = 1667897) B1667897
theorem B15169427 : Blo 738327 15169427 := bstep (se 1 (by rfl) ⟨11377070, by rfl⟩ : syracuseStep 15169427 = 22754141) B22754141
theorem B9632027 : Blo 738327 9632027 := bstep (se 1 (by rfl) ⟨7224020, by rfl⟩ : syracuseStep 9632027 = 14448041) B14448041
theorem B1113071 : Blo 738327 1113071 := bstep (se 1 (by rfl) ⟨834803, by rfl⟩ : syracuseStep 1113071 = 1669607) B1669607
theorem B1113119 : Blo 738327 1113119 := bstep (se 1 (by rfl) ⟨834839, by rfl⟩ : syracuseStep 1113119 = 1669679) B1669679
theorem B5701099 : Blo 738327 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B4751243 : Blo 738327 4751243 := bstep (se 1 (by rfl) ⟨3563432, by rfl⟩ : syracuseStep 4751243 = 7126865) B7126865
theorem B25952993 : Blo 738327 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B1245935 : Blo 738327 1245935 := bstep (se 1 (by rfl) ⟨934451, by rfl⟩ : syracuseStep 1245935 = 1868903) B1868903
theorem B18974411 : Blo 738327 18974411 := bstep (se 1 (by rfl) ⟨14230808, by rfl⟩ : syracuseStep 18974411 = 28461617) B28461617
theorem B23955851 : Blo 738327 23955851 := bstep (se 1 (by rfl) ⟨17966888, by rfl⟩ : syracuseStep 23955851 = 35933777) B35933777
theorem B18221879 : Blo 738327 18221879 := bstep (se 1 (by rfl) ⟨13666409, by rfl⟩ : syracuseStep 18221879 = 27332819) B27332819
theorem B2003015 : Blo 738327 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B19206611 : Blo 738327 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B2495231 : Blo 738327 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B1775123 : Blo 738327 1775123 := bstep (se 1 (by rfl) ⟨1331342, by rfl⟩ : syracuseStep 1775123 = 2662685) B2662685
theorem B1251983 : Blo 738327 1251983 := bstep (se 1 (by rfl) ⟨938987, by rfl⟩ : syracuseStep 1251983 = 1877975) B1877975
theorem B1252489 : Blo 738327 1252489 := bstep (se 2 (by rfl) ⟨469683, by rfl⟩ : syracuseStep 1252489 = 939367) B939367
theorem B2104555 : Blo 738327 2104555 := bstep (se 1 (by rfl) ⟨1578416, by rfl⟩ : syracuseStep 2104555 = 3156833) B3156833
theorem B2104829 : Blo 738327 2104829 := bstep (se 3 (by rfl) ⟨394655, by rfl⟩ : syracuseStep 2104829 = 789311) B789311
theorem B10822247 : Blo 738327 10822247 := bstep (se 1 (by rfl) ⟨8116685, by rfl⟩ : syracuseStep 10822247 = 16233371) B16233371
theorem B10953667 : Blo 738327 10953667 := bstep (se 1 (by rfl) ⟨8215250, by rfl⟩ : syracuseStep 10953667 = 16430501) B16430501
theorem B2499551 : Blo 738327 2499551 := bstep (se 1 (by rfl) ⟨1874663, by rfl⟩ : syracuseStep 2499551 = 3749327) B3749327
theorem B2369675 : Blo 738327 2369675 := bstep (se 1 (by rfl) ⟨1777256, by rfl⟩ : syracuseStep 2369675 = 3554513) B3554513
theorem B2502143 : Blo 738327 2502143 := bstep (se 1 (by rfl) ⟨1876607, by rfl⟩ : syracuseStep 2502143 = 3753215) B3753215
theorem B20229749 : Blo 738327 20229749 := bstep (se 5 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 20229749 = 1896539) B1896539
theorem B5713537 : Blo 738327 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B3748679 : Blo 738327 3748679 := bstep (se 1 (by rfl) ⟨2811509, by rfl⟩ : syracuseStep 3748679 = 5623019) B5623019
theorem B833071 : Blo 738327 833071 := bstep (se 1 (by rfl) ⟨624803, by rfl⟩ : syracuseStep 833071 = 1249607) B1249607
theorem B11580985 : Blo 738327 11580985 := bstep (se 2 (by rfl) ⟨4342869, by rfl⟩ : syracuseStep 11580985 = 8685739) B8685739
theorem B13482035 : Blo 738327 13482035 := bstep (se 1 (by rfl) ⟨10111526, by rfl⟩ : syracuseStep 13482035 = 20223053) B20223053
theorem B2111903 : Blo 738327 2111903 := bstep (se 1 (by rfl) ⟨1583927, by rfl⟩ : syracuseStep 2111903 = 3167855) B3167855
theorem B5618159 : Blo 738327 5618159 := bstep (se 1 (by rfl) ⟨4213619, by rfl⟩ : syracuseStep 5618159 = 8427239) B8427239
theorem B51200099 : Blo 738327 51200099 := bstep (se 1 (by rfl) ⟨38400074, by rfl⟩ : syracuseStep 51200099 = 76800149) B76800149
theorem B1523951 : Blo 738327 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B2375993 : Blo 738327 2375993 := bstep (se 2 (by rfl) ⟨890997, by rfl⟩ : syracuseStep 2375993 = 1781995) B1781995
theorem B738395 : Blo 738327 738395 := bstep (se 1 (by rfl) ⟨553796, by rfl⟩ : syracuseStep 738395 = 1107593) B1107593
theorem B738767 : Blo 738327 738767 := bstep (se 1 (by rfl) ⟨554075, by rfl⟩ : syracuseStep 738767 = 1108151) B1108151
theorem B3557395 : Blo 738327 3557395 := bstep (se 1 (by rfl) ⟨2668046, by rfl⟩ : syracuseStep 3557395 = 5336093) B5336093
theorem B2803855 : Blo 738327 2803855 := bstep (se 1 (by rfl) ⟨2102891, by rfl⟩ : syracuseStep 2803855 = 4205783) B4205783
theorem B3557627 : Blo 738327 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B739583 : Blo 738327 739583 := bstep (se 1 (by rfl) ⟨554687, by rfl⟩ : syracuseStep 739583 = 1109375) B1109375
theorem B3000889 : Blo 738327 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B12831625 : Blo 738327 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B2804827 : Blo 738327 2804827 := bstep (se 1 (by rfl) ⟨2103620, by rfl⟩ : syracuseStep 2804827 = 4207241) B4207241
theorem B740671 : Blo 738327 740671 := bstep (se 1 (by rfl) ⟨555503, by rfl⟩ : syracuseStep 740671 = 1111007) B1111007
theorem B740711 : Blo 738327 740711 := bstep (se 1 (by rfl) ⟨555533, by rfl⟩ : syracuseStep 740711 = 1111067) B1111067
theorem B740799 : Blo 738327 740799 := bstep (se 1 (by rfl) ⟨555599, by rfl⟩ : syracuseStep 740799 = 1111199) B1111199
theorem B740891 : Blo 738327 740891 := bstep (se 1 (by rfl) ⟨555668, by rfl⟩ : syracuseStep 740891 = 1111337) B1111337
theorem B740991 : Blo 738327 740991 := bstep (se 1 (by rfl) ⟨555743, by rfl⟩ : syracuseStep 740991 = 1111487) B1111487
theorem B741151 : Blo 738327 741151 := bstep (se 1 (by rfl) ⟨555863, by rfl⟩ : syracuseStep 741151 = 1111727) B1111727
theorem B741211 : Blo 738327 741211 := bstep (se 1 (by rfl) ⟨555908, by rfl⟩ : syracuseStep 741211 = 1111817) B1111817
theorem B741287 : Blo 738327 741287 := bstep (se 1 (by rfl) ⟨555965, by rfl⟩ : syracuseStep 741287 = 1111931) B1111931
theorem B10112951 : Blo 738327 10112951 := bstep (se 1 (by rfl) ⟨7584713, by rfl⟩ : syracuseStep 10112951 = 15169427) B15169427
theorem B742047 : Blo 738327 742047 := bstep (se 1 (by rfl) ⟨556535, by rfl⟩ : syracuseStep 742047 = 1113071) B1113071
theorem B742079 : Blo 738327 742079 := bstep (se 1 (by rfl) ⟨556559, by rfl⟩ : syracuseStep 742079 = 1113119) B1113119
theorem B54711359 : Blo 738327 54711359 := bstep (se 1 (by rfl) ⟨41033519, by rfl⟩ : syracuseStep 54711359 = 82067039) B82067039
theorem B3167495 : Blo 738327 3167495 := bstep (se 1 (by rfl) ⟨2375621, by rfl⟩ : syracuseStep 3167495 = 4751243) B4751243
theorem B12834395 : Blo 738327 12834395 := bstep (se 1 (by rfl) ⟨9625796, by rfl⟩ : syracuseStep 12834395 = 19251593) B19251593
theorem B1661471 : Blo 738327 1661471 := bstep (se 1 (by rfl) ⟨1246103, by rfl⟩ : syracuseStep 1661471 = 2492207) B2492207
theorem B4217447 : Blo 738327 4217447 := bstep (se 1 (by rfl) ⟨3163085, by rfl⟩ : syracuseStep 4217447 = 6326171) B6326171
theorem B5692103 : Blo 738327 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B24337925 : Blo 738327 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B5627879 : Blo 738327 5627879 := bstep (se 1 (by rfl) ⟨4220909, by rfl⟩ : syracuseStep 5627879 = 8441819) B8441819
theorem B1663199 : Blo 738327 1663199 := bstep (se 1 (by rfl) ⟨1247399, by rfl⟩ : syracuseStep 1663199 = 2494799) B2494799
theorem B6414713 : Blo 738327 6414713 := bstep (se 2 (by rfl) ⟨2405517, by rfl⟩ : syracuseStep 6414713 = 4811035) B4811035
theorem B5694077 : Blo 738327 5694077 := bstep (se 3 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 5694077 = 2135279) B2135279
theorem B1663739 : Blo 738327 1663739 := bstep (se 1 (by rfl) ⟨1247804, by rfl⟩ : syracuseStep 1663739 = 2495609) B2495609
theorem B1664027 : Blo 738327 1664027 := bstep (se 1 (by rfl) ⟨1248020, by rfl⟩ : syracuseStep 1664027 = 2496041) B2496041
theorem B1107503 : Blo 738327 1107503 := bstep (se 1 (by rfl) ⟨830627, by rfl⟩ : syracuseStep 1107503 = 1661255) B1661255
theorem B1108127 : Blo 738327 1108127 := bstep (se 1 (by rfl) ⟨831095, by rfl⟩ : syracuseStep 1108127 = 1662191) B1662191
theorem B1665449 : Blo 738327 1665449 := bstep (se 2 (by rfl) ⟨624543, by rfl⟩ : syracuseStep 1665449 = 1249087) B1249087
theorem B5631767 : Blo 738327 5631767 := bstep (se 1 (by rfl) ⟨4223825, by rfl⟩ : syracuseStep 5631767 = 8447651) B8447651
theorem B71921681 : Blo 738327 71921681 := bstep (se 2 (by rfl) ⟨26970630, by rfl⟩ : syracuseStep 71921681 = 53941261) B53941261
theorem B1110137 : Blo 738327 1110137 := bstep (se 2 (by rfl) ⟨416301, by rfl⟩ : syracuseStep 1110137 = 832603) B832603
theorem B1110251 : Blo 738327 1110251 := bstep (se 1 (by rfl) ⟨832688, by rfl⟩ : syracuseStep 1110251 = 1665377) B1665377
theorem B1667321 : Blo 738327 1667321 := bstep (se 2 (by rfl) ⟨625245, by rfl⟩ : syracuseStep 1667321 = 1250491) B1250491
theorem B1667411 : Blo 738327 1667411 := bstep (se 1 (by rfl) ⟨1250558, by rfl⟩ : syracuseStep 1667411 = 2501117) B2501117
theorem B1110575 : Blo 738327 1110575 := bstep (se 1 (by rfl) ⟨832931, by rfl⟩ : syracuseStep 1110575 = 1665863) B1665863
theorem B1110953 : Blo 738327 1110953 := bstep (se 2 (by rfl) ⟨416607, by rfl⟩ : syracuseStep 1110953 = 833215) B833215
theorem B5698973 : Blo 738327 5698973 := bstep (se 3 (by rfl) ⟨1068557, by rfl⟩ : syracuseStep 5698973 = 2137115) B2137115
theorem B1668815 : Blo 738327 1668815 := bstep (se 1 (by rfl) ⟨1251611, by rfl⟩ : syracuseStep 1668815 = 2503223) B2503223
theorem B6092777 : Blo 738327 6092777 := bstep (se 2 (by rfl) ⟨2284791, by rfl⟩ : syracuseStep 6092777 = 4569583) B4569583
theorem B1669193 : Blo 738327 1669193 := bstep (se 2 (by rfl) ⟨625947, by rfl⟩ : syracuseStep 1669193 = 1251895) B1251895
theorem B1669247 : Blo 738327 1669247 := bstep (se 1 (by rfl) ⟨1251935, by rfl⟩ : syracuseStep 1669247 = 2503871) B2503871
theorem B4225193 : Blo 738327 4225193 := bstep (se 2 (by rfl) ⟨1584447, by rfl⟩ : syracuseStep 4225193 = 3168895) B3168895
theorem B6421351 : Blo 738327 6421351 := bstep (se 1 (by rfl) ⟨4816013, by rfl⟩ : syracuseStep 6421351 = 9632027) B9632027
theorem B1670057 : Blo 738327 1670057 := bstep (se 2 (by rfl) ⟨626271, by rfl⟩ : syracuseStep 1670057 = 1252543) B1252543
theorem B7601465 : Blo 738327 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B1015967 : Blo 738327 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B5341373 : Blo 738327 5341373 := bstep (se 3 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 5341373 = 2003015) B2003015
theorem B17301995 : Blo 738327 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B12649607 : Blo 738327 12649607 := bstep (se 1 (by rfl) ⟨9487205, by rfl⟩ : syracuseStep 12649607 = 18974411) B18974411
theorem B3738473 : Blo 738327 3738473 := bstep (se 2 (by rfl) ⟨1401927, by rfl⟩ : syracuseStep 3738473 = 2803855) B2803855
theorem B36474239 : Blo 738327 36474239 := bstep (se 1 (by rfl) ⟨27355679, by rfl⟩ : syracuseStep 36474239 = 54711359) B54711359
theorem B4001185 : Blo 738327 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B1183415 : Blo 738327 1183415 := bstep (se 1 (by rfl) ⟨887561, by rfl⟩ : syracuseStep 1183415 = 1775123) B1775123
theorem B8556263 : Blo 738327 8556263 := bstep (se 1 (by rfl) ⟨6417197, by rfl⟩ : syracuseStep 8556263 = 12834395) B12834395
theorem B17108833 : Blo 738327 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B3739769 : Blo 738327 3739769 := bstep (se 2 (by rfl) ⟨1402413, by rfl⟩ : syracuseStep 3739769 = 2804827) B2804827
theorem B16225283 : Blo 738327 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B7214831 : Blo 738327 7214831 := bstep (se 1 (by rfl) ⟨5411123, by rfl⟩ : syracuseStep 7214831 = 10822247) B10822247
theorem B15441313 : Blo 738327 15441313 := bstep (se 2 (by rfl) ⟨5790492, by rfl⟩ : syracuseStep 15441313 = 11580985) B11580985
theorem B47947787 : Blo 738327 47947787 := bstep (se 1 (by rfl) ⟨35960840, by rfl⟩ : syracuseStep 47947787 = 71921681) B71921681
theorem B2499119 : Blo 738327 2499119 := bstep (se 1 (by rfl) ⟨1874339, by rfl⟩ : syracuseStep 2499119 = 3748679) B3748679
theorem B8561801 : Blo 738327 8561801 := bstep (se 2 (by rfl) ⟨3210675, by rfl⟩ : syracuseStep 8561801 = 6421351) B6421351
theorem B8988023 : Blo 738327 8988023 := bstep (se 1 (by rfl) ⟨6741017, by rfl⟩ : syracuseStep 8988023 = 13482035) B13482035
theorem B3745439 : Blo 738327 3745439 := bstep (se 1 (by rfl) ⟨2809079, by rfl⟩ : syracuseStep 3745439 = 5618159) B5618159
theorem B830623 : Blo 738327 830623 := bstep (se 1 (by rfl) ⟨622967, by rfl⟩ : syracuseStep 830623 = 1245935) B1245935
theorem B6335981 : Blo 738327 6335981 := bstep (se 3 (by rfl) ⟨1187996, by rfl⟩ : syracuseStep 6335981 = 2375993) B2375993
theorem B2371751 : Blo 738327 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B15970567 : Blo 738327 15970567 := bstep (se 1 (by rfl) ⟨11977925, by rfl⟩ : syracuseStep 15970567 = 23955851) B23955851
theorem B15184205 : Blo 738327 15184205 := bstep (se 3 (by rfl) ⟨2847038, by rfl⟩ : syracuseStep 15184205 = 5694077) B5694077
theorem B2111663 : Blo 738327 2111663 := bstep (se 1 (by rfl) ⟨1583747, by rfl⟩ : syracuseStep 2111663 = 3167495) B3167495
theorem B834655 : Blo 738327 834655 := bstep (se 1 (by rfl) ⟨625991, by rfl⟩ : syracuseStep 834655 = 1251983) B1251983
theorem B7618049 : Blo 738327 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B3751919 : Blo 738327 3751919 := bstep (se 1 (by rfl) ⟨2813939, by rfl⟩ : syracuseStep 3751919 = 5627879) B5627879
theorem B4276475 : Blo 738327 4276475 := bstep (se 1 (by rfl) ⟨3207356, by rfl⟩ : syracuseStep 4276475 = 6414713) B6414713
theorem B738335 : Blo 738327 738335 := bstep (se 1 (by rfl) ⟨553751, by rfl⟩ : syracuseStep 738335 = 1107503) B1107503
theorem B738751 : Blo 738327 738751 := bstep (se 1 (by rfl) ⟨554063, by rfl⟩ : syracuseStep 738751 = 1108127) B1108127
theorem B13486499 : Blo 738327 13486499 := bstep (se 1 (by rfl) ⟨10114874, by rfl⟩ : syracuseStep 13486499 = 20229749) B20229749
theorem B3754511 : Blo 738327 3754511 := bstep (se 1 (by rfl) ⟨2815883, by rfl⟩ : syracuseStep 3754511 = 5631767) B5631767
theorem B740091 : Blo 738327 740091 := bstep (se 1 (by rfl) ⟨555068, by rfl⟩ : syracuseStep 740091 = 1110137) B1110137
theorem B740167 : Blo 738327 740167 := bstep (se 1 (by rfl) ⟨555125, by rfl⟩ : syracuseStep 740167 = 1110251) B1110251
theorem B740383 : Blo 738327 740383 := bstep (se 1 (by rfl) ⟨555287, by rfl⟩ : syracuseStep 740383 = 1110575) B1110575
theorem B740635 : Blo 738327 740635 := bstep (se 1 (by rfl) ⟨555476, by rfl⟩ : syracuseStep 740635 = 1110953) B1110953
theorem B20270573 : Blo 738327 20270573 := bstep (se 3 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 20270573 = 7601465) B7601465
theorem B2806073 : Blo 738327 2806073 := bstep (se 2 (by rfl) ⟨1052277, by rfl⟩ : syracuseStep 2806073 = 2104555) B2104555
theorem B34133399 : Blo 738327 34133399 := bstep (se 1 (by rfl) ⟨25600049, by rfl⟩ : syracuseStep 34133399 = 51200099) B51200099
theorem B14604889 : Blo 738327 14604889 := bstep (se 2 (by rfl) ⟨5476833, by rfl⟩ : syracuseStep 14604889 = 10953667) B10953667
theorem B6741967 : Blo 738327 6741967 := bstep (se 1 (by rfl) ⟨5056475, by rfl⟩ : syracuseStep 6741967 = 10112951) B10112951
theorem B4743193 : Blo 738327 4743193 := bstep (se 2 (by rfl) ⟨1778697, by rfl⟩ : syracuseStep 4743193 = 3557395) B3557395
theorem B12804407 : Blo 738327 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B1663487 : Blo 738327 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B1107647 : Blo 738327 1107647 := bstep (se 1 (by rfl) ⟨830735, by rfl⟩ : syracuseStep 1107647 = 1661471) B1661471
theorem B2811631 : Blo 738327 2811631 := bstep (se 1 (by rfl) ⟨2108723, by rfl⟩ : syracuseStep 2811631 = 4217447) B4217447
theorem B3794735 : Blo 738327 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B1403219 : Blo 738327 1403219 := bstep (se 1 (by rfl) ⟨1052414, by rfl⟩ : syracuseStep 1403219 = 2104829) B2104829
theorem B16247405 : Blo 738327 16247405 := bstep (se 3 (by rfl) ⟨3046388, by rfl⟩ : syracuseStep 16247405 = 6092777) B6092777
theorem B1108799 : Blo 738327 1108799 := bstep (se 1 (by rfl) ⟨831599, by rfl⟩ : syracuseStep 1108799 = 1663199) B1663199
theorem B6319133 : Blo 738327 6319133 := bstep (se 3 (by rfl) ⟨1184837, by rfl⟩ : syracuseStep 6319133 = 2369675) B2369675
theorem B1109159 : Blo 738327 1109159 := bstep (se 1 (by rfl) ⟨831869, by rfl⟩ : syracuseStep 1109159 = 1663739) B1663739
theorem B1666367 : Blo 738327 1666367 := bstep (se 1 (by rfl) ⟨1249775, by rfl⟩ : syracuseStep 1666367 = 2499551) B2499551
theorem B1109351 : Blo 738327 1109351 := bstep (se 1 (by rfl) ⟨832013, by rfl⟩ : syracuseStep 1109351 = 1664027) B1664027
theorem B1110299 : Blo 738327 1110299 := bstep (se 1 (by rfl) ⟨832724, by rfl⟩ : syracuseStep 1110299 = 1665449) B1665449
theorem B1110761 : Blo 738327 1110761 := bstep (se 2 (by rfl) ⟨416535, by rfl⟩ : syracuseStep 1110761 = 833071) B833071
theorem B48591677 : Blo 738327 48591677 := bstep (se 3 (by rfl) ⟨9110939, by rfl⟩ : syracuseStep 48591677 = 18221879) B18221879
theorem B1668095 : Blo 738327 1668095 := bstep (se 1 (by rfl) ⟨1251071, by rfl⟩ : syracuseStep 1668095 = 2502143) B2502143
theorem B1111547 : Blo 738327 1111547 := bstep (se 1 (by rfl) ⟨833660, by rfl⟩ : syracuseStep 1111547 = 1667321) B1667321
theorem B1111607 : Blo 738327 1111607 := bstep (se 1 (by rfl) ⟨833705, by rfl⟩ : syracuseStep 1111607 = 1667411) B1667411
theorem B3799315 : Blo 738327 3799315 := bstep (se 1 (by rfl) ⟨2849486, by rfl⟩ : syracuseStep 3799315 = 5698973) B5698973
theorem B1112543 : Blo 738327 1112543 := bstep (se 1 (by rfl) ⟨834407, by rfl⟩ : syracuseStep 1112543 = 1668815) B1668815
theorem B1112795 : Blo 738327 1112795 := bstep (se 1 (by rfl) ⟨834596, by rfl⟩ : syracuseStep 1112795 = 1669193) B1669193
theorem B1112831 : Blo 738327 1112831 := bstep (se 1 (by rfl) ⟨834623, by rfl⟩ : syracuseStep 1112831 = 1669247) B1669247
theorem B2816795 : Blo 738327 2816795 := bstep (se 1 (by rfl) ⟨2112596, by rfl⟩ : syracuseStep 2816795 = 4225193) B4225193
theorem B1669985 : Blo 738327 1669985 := bstep (se 2 (by rfl) ⟨626244, by rfl⟩ : syracuseStep 1669985 = 1252489) B1252489
theorem B1407935 : Blo 738327 1407935 := bstep (se 1 (by rfl) ⟨1055951, by rfl⟩ : syracuseStep 1407935 = 2111903) B2111903
theorem B1113371 : Blo 738327 1113371 := bstep (se 1 (by rfl) ⟨835028, by rfl⟩ : syracuseStep 1113371 = 1670057) B1670057
theorem B6324257 : Blo 738327 6324257 := bstep (se 2 (by rfl) ⟨2371596, by rfl⟩ : syracuseStep 6324257 = 4743193) B4743193
theorem B2850983 : Blo 738327 2850983 := bstep (se 1 (by rfl) ⟨2138237, by rfl⟩ : syracuseStep 2850983 = 4276475) B4276475
theorem B11534663 : Blo 738327 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B2492315 : Blo 738327 2492315 := bstep (se 1 (by rfl) ⟨1869236, by rfl⟩ : syracuseStep 2492315 = 3738473) B3738473
theorem B24316159 : Blo 738327 24316159 := bstep (se 1 (by rfl) ⟨18237119, by rfl⟩ : syracuseStep 24316159 = 36474239) B36474239
theorem B5704175 : Blo 738327 5704175 := bstep (se 1 (by rfl) ⟨4278131, by rfl⟩ : syracuseStep 5704175 = 8556263) B8556263
theorem B2493179 : Blo 738327 2493179 := bstep (se 1 (by rfl) ⟨1869884, by rfl⟩ : syracuseStep 2493179 = 3739769) B3739769
theorem B1870715 : Blo 738327 1870715 := bstep (se 1 (by rfl) ⟨1403036, by rfl⟩ : syracuseStep 1870715 = 2806073) B2806073
theorem B22811777 : Blo 738327 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B2496959 : Blo 738327 2496959 := bstep (se 1 (by rfl) ⟨1872719, by rfl⟩ : syracuseStep 2496959 = 3745439) B3745439
theorem B1581167 : Blo 738327 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B19473185 : Blo 738327 19473185 := bstep (se 2 (by rfl) ⟨7302444, by rfl⟩ : syracuseStep 19473185 = 14604889) B14604889
theorem B3155773 : Blo 738327 3155773 := bstep (se 3 (by rfl) ⟨591707, by rfl⟩ : syracuseStep 3155773 = 1183415) B1183415
theorem B1877863 : Blo 738327 1877863 := bstep (se 1 (by rfl) ⟨1408397, by rfl⟩ : syracuseStep 1877863 = 2816795) B2816795
theorem B20588417 : Blo 738327 20588417 := bstep (se 2 (by rfl) ⟨7720656, by rfl⟩ : syracuseStep 20588417 = 15441313) B15441313
theorem B8989289 : Blo 738327 8989289 := bstep (se 2 (by rfl) ⟨3370983, by rfl⟩ : syracuseStep 8989289 = 6741967) B6741967
theorem B2501279 : Blo 738327 2501279 := bstep (se 1 (by rfl) ⟨1875959, by rfl⟩ : syracuseStep 2501279 = 3751919) B3751919
theorem B8433071 : Blo 738327 8433071 := bstep (se 1 (by rfl) ⟨6324803, by rfl⟩ : syracuseStep 8433071 = 12649607) B12649607
theorem B8990999 : Blo 738327 8990999 := bstep (se 1 (by rfl) ⟨6743249, by rfl⟩ : syracuseStep 8990999 = 13486499) B13486499
theorem B2503007 : Blo 738327 2503007 := bstep (se 1 (by rfl) ⟨1877255, by rfl⟩ : syracuseStep 2503007 = 3754511) B3754511
theorem B129577805 : Blo 738327 129577805 := bstep (se 3 (by rfl) ⟨24295838, by rfl⟩ : syracuseStep 129577805 = 48591677) B48591677
theorem B3748841 : Blo 738327 3748841 := bstep (se 2 (by rfl) ⟨1405815, by rfl⟩ : syracuseStep 3748841 = 2811631) B2811631
theorem B13513715 : Blo 738327 13513715 := bstep (se 1 (by rfl) ⟨10135286, by rfl⟩ : syracuseStep 13513715 = 20270573) B20270573
theorem B43267421 : Blo 738327 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B22755599 : Blo 738327 22755599 := bstep (se 1 (by rfl) ⟨17066699, by rfl⟩ : syracuseStep 22755599 = 34133399) B34133399
theorem B31965191 : Blo 738327 31965191 := bstep (se 1 (by rfl) ⟨23973893, by rfl⟩ : syracuseStep 31965191 = 47947787) B47947787
theorem B8536271 : Blo 738327 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B738431 : Blo 738327 738431 := bstep (se 1 (by rfl) ⟨553823, by rfl⟩ : syracuseStep 738431 = 1107647) B1107647
theorem B935479 : Blo 738327 935479 := bstep (se 1 (by rfl) ⟨701609, by rfl⟩ : syracuseStep 935479 = 1403219) B1403219
theorem B10831603 : Blo 738327 10831603 := bstep (se 1 (by rfl) ⟨8123702, by rfl⟩ : syracuseStep 10831603 = 16247405) B16247405
theorem B739199 : Blo 738327 739199 := bstep (se 1 (by rfl) ⟨554399, by rfl⟩ : syracuseStep 739199 = 1108799) B1108799
theorem B4212755 : Blo 738327 4212755 := bstep (se 1 (by rfl) ⟨3159566, by rfl⟩ : syracuseStep 4212755 = 6319133) B6319133
theorem B739439 : Blo 738327 739439 := bstep (se 1 (by rfl) ⟨554579, by rfl⟩ : syracuseStep 739439 = 1109159) B1109159
theorem B739567 : Blo 738327 739567 := bstep (se 1 (by rfl) ⟨554675, by rfl⟩ : syracuseStep 739567 = 1109351) B1109351
theorem B740199 : Blo 738327 740199 := bstep (se 1 (by rfl) ⟨555149, by rfl⟩ : syracuseStep 740199 = 1110299) B1110299
theorem B5065753 : Blo 738327 5065753 := bstep (se 2 (by rfl) ⟨1899657, by rfl⟩ : syracuseStep 5065753 = 3799315) B3799315
theorem B740507 : Blo 738327 740507 := bstep (se 1 (by rfl) ⟨555380, by rfl⟩ : syracuseStep 740507 = 1110761) B1110761
theorem B741031 : Blo 738327 741031 := bstep (se 1 (by rfl) ⟨555773, by rfl⟩ : syracuseStep 741031 = 1111547) B1111547
theorem B741071 : Blo 738327 741071 := bstep (se 1 (by rfl) ⟨555803, by rfl⟩ : syracuseStep 741071 = 1111607) B1111607
theorem B741695 : Blo 738327 741695 := bstep (se 1 (by rfl) ⟨556271, by rfl⟩ : syracuseStep 741695 = 1112543) B1112543
theorem B741863 : Blo 738327 741863 := bstep (se 1 (by rfl) ⟨556397, by rfl⟩ : syracuseStep 741863 = 1112795) B1112795
theorem B741887 : Blo 738327 741887 := bstep (se 1 (by rfl) ⟨556415, by rfl⟩ : syracuseStep 741887 = 1112831) B1112831
theorem B938623 : Blo 738327 938623 := bstep (se 1 (by rfl) ⟨703967, by rfl⟩ : syracuseStep 938623 = 1407935) B1407935
theorem B742247 : Blo 738327 742247 := bstep (se 1 (by rfl) ⟨556685, by rfl⟩ : syracuseStep 742247 = 1113371) B1113371
theorem B3560915 : Blo 738327 3560915 := bstep (se 1 (by rfl) ⟨2670686, by rfl⟩ : syracuseStep 3560915 = 5341373) B5341373
theorem B2709245 : Blo 738327 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B22831469 : Blo 738327 22831469 := bstep (se 3 (by rfl) ⟨4280900, by rfl⟩ : syracuseStep 22831469 = 8561801) B8561801
theorem B4809887 : Blo 738327 4809887 := bstep (se 1 (by rfl) ⟨3607415, by rfl⟩ : syracuseStep 4809887 = 7214831) B7214831
theorem B1107497 : Blo 738327 1107497 := bstep (se 2 (by rfl) ⟨415311, by rfl⟩ : syracuseStep 1107497 = 830623) B830623
theorem B5334913 : Blo 738327 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B10119293 : Blo 738327 10119293 := bstep (se 3 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 10119293 = 3794735) B3794735
theorem B1108991 : Blo 738327 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B21294089 : Blo 738327 21294089 := bstep (se 2 (by rfl) ⟨7985283, by rfl⟩ : syracuseStep 21294089 = 15970567) B15970567
theorem B1666079 : Blo 738327 1666079 := bstep (se 1 (by rfl) ⟨1249559, by rfl⟩ : syracuseStep 1666079 = 2499119) B2499119
theorem B5992015 : Blo 738327 5992015 := bstep (se 1 (by rfl) ⟨4494011, by rfl⟩ : syracuseStep 5992015 = 8988023) B8988023
theorem B1110911 : Blo 738327 1110911 := bstep (se 1 (by rfl) ⟨833183, by rfl⟩ : syracuseStep 1110911 = 1666367) B1666367
theorem B4223987 : Blo 738327 4223987 := bstep (se 1 (by rfl) ⟨3167990, by rfl⟩ : syracuseStep 4223987 = 6335981) B6335981
theorem B10122803 : Blo 738327 10122803 := bstep (se 1 (by rfl) ⟨7592102, by rfl⟩ : syracuseStep 10122803 = 15184205) B15184205
theorem B1112063 : Blo 738327 1112063 := bstep (se 1 (by rfl) ⟨834047, by rfl⟩ : syracuseStep 1112063 = 1668095) B1668095
theorem B1407775 : Blo 738327 1407775 := bstep (se 1 (by rfl) ⟨1055831, by rfl⟩ : syracuseStep 1407775 = 2111663) B2111663
theorem B1112873 : Blo 738327 1112873 := bstep (se 2 (by rfl) ⟨417327, by rfl⟩ : syracuseStep 1112873 = 834655) B834655
theorem B1113323 : Blo 738327 1113323 := bstep (se 1 (by rfl) ⟨834992, by rfl⟩ : syracuseStep 1113323 = 1669985) B1669985
theorem B5078699 : Blo 738327 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B1900655 : Blo 738327 1900655 := bstep (se 1 (by rfl) ⟨1425491, by rfl⟩ : syracuseStep 1900655 = 2850983) B2850983
theorem B3802783 : Blo 738327 3802783 := bstep (se 1 (by rfl) ⟨2852087, by rfl⟩ : syracuseStep 3802783 = 5704175) B5704175
theorem B1247143 : Blo 738327 1247143 := bstep (se 1 (by rfl) ⟨935357, by rfl⟩ : syracuseStep 1247143 = 1870715) B1870715
theorem B1247305 : Blo 738327 1247305 := bstep (se 2 (by rfl) ⟨467739, by rfl⟩ : syracuseStep 1247305 = 935479) B935479
theorem B7113217 : Blo 738327 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B15207851 : Blo 738327 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B6754337 : Blo 738327 6754337 := bstep (se 2 (by rfl) ⟨2532876, by rfl⟩ : syracuseStep 6754337 = 5065753) B5065753
theorem B12982123 : Blo 738327 12982123 := bstep (se 1 (by rfl) ⟨9736592, by rfl⟩ : syracuseStep 12982123 = 19473185) B19473185
theorem B1251497 : Blo 738327 1251497 := bstep (se 2 (by rfl) ⟨469311, by rfl⟩ : syracuseStep 1251497 = 938623) B938623
theorem B14196059 : Blo 738327 14196059 := bstep (se 1 (by rfl) ⟨10647044, by rfl⟩ : syracuseStep 14196059 = 21294089) B21294089
theorem B86385203 : Blo 738327 86385203 := bstep (se 1 (by rfl) ⟨64788902, by rfl⟩ : syracuseStep 86385203 = 129577805) B129577805
theorem B2499227 : Blo 738327 2499227 := bstep (se 1 (by rfl) ⟨1874420, by rfl⟩ : syracuseStep 2499227 = 3748841) B3748841
theorem B28844947 : Blo 738327 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B1877033 : Blo 738327 1877033 := bstep (se 2 (by rfl) ⟨703887, by rfl⟩ : syracuseStep 1877033 = 1407775) B1407775
theorem B3385799 : Blo 738327 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B21310127 : Blo 738327 21310127 := bstep (se 1 (by rfl) ⟨15982595, by rfl⟩ : syracuseStep 21310127 = 31965191) B31965191
theorem B4207697 : Blo 738327 4207697 := bstep (se 2 (by rfl) ⟨1577886, by rfl⟩ : syracuseStep 4207697 = 3155773) B3155773
theorem B2503817 : Blo 738327 2503817 := bstep (se 2 (by rfl) ⟨938931, by rfl⟩ : syracuseStep 2503817 = 1877863) B1877863
theorem B32421545 : Blo 738327 32421545 := bstep (se 2 (by rfl) ⟨12158079, by rfl⟩ : syracuseStep 32421545 = 24316159) B24316159
theorem B2373943 : Blo 738327 2373943 := bstep (se 1 (by rfl) ⟨1780457, by rfl⟩ : syracuseStep 2373943 = 3560915) B3560915
theorem B7224653 : Blo 738327 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B15220979 : Blo 738327 15220979 := bstep (se 1 (by rfl) ⟨11415734, by rfl⟩ : syracuseStep 15220979 = 22831469) B22831469
theorem B738331 : Blo 738327 738331 := bstep (se 1 (by rfl) ⟨553748, by rfl⟩ : syracuseStep 738331 = 1107497) B1107497
theorem B739327 : Blo 738327 739327 := bstep (se 1 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 739327 = 1108991) B1108991
theorem B5622047 : Blo 738327 5622047 := bstep (se 1 (by rfl) ⟨4216535, by rfl⟩ : syracuseStep 5622047 = 8433071) B8433071
theorem B740607 : Blo 738327 740607 := bstep (se 1 (by rfl) ⟨555455, by rfl⟩ : syracuseStep 740607 = 1110911) B1110911
theorem B741375 : Blo 738327 741375 := bstep (se 1 (by rfl) ⟨556031, by rfl⟩ : syracuseStep 741375 = 1112063) B1112063
theorem B741915 : Blo 738327 741915 := bstep (se 1 (by rfl) ⟨556436, by rfl⟩ : syracuseStep 741915 = 1112873) B1112873
theorem B742215 : Blo 738327 742215 := bstep (se 1 (by rfl) ⟨556661, by rfl⟩ : syracuseStep 742215 = 1113323) B1113323
theorem B4216171 : Blo 738327 4216171 := bstep (se 1 (by rfl) ⟨3162128, by rfl⟩ : syracuseStep 4216171 = 6324257) B6324257
theorem B7689775 : Blo 738327 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B4216445 : Blo 738327 4216445 := bstep (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) B1581167
theorem B1661543 : Blo 738327 1661543 := bstep (se 1 (by rfl) ⟨1246157, by rfl⟩ : syracuseStep 1661543 = 2492315) B2492315
theorem B2808503 : Blo 738327 2808503 := bstep (se 1 (by rfl) ⟨2106377, by rfl⟩ : syracuseStep 2808503 = 4212755) B4212755
theorem B1662119 : Blo 738327 1662119 := bstep (se 1 (by rfl) ⟨1246589, by rfl⟩ : syracuseStep 1662119 = 2493179) B2493179
theorem B91053557 : Blo 738327 91053557 := bstep (se 5 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 91053557 = 8536271) B8536271
theorem B14442137 : Blo 738327 14442137 := bstep (se 2 (by rfl) ⟨5415801, by rfl⟩ : syracuseStep 14442137 = 10831603) B10831603
theorem B1664639 : Blo 738327 1664639 := bstep (se 1 (by rfl) ⟨1248479, by rfl⟩ : syracuseStep 1664639 = 2496959) B2496959
theorem B7989353 : Blo 738327 7989353 := bstep (se 2 (by rfl) ⟨2996007, by rfl⟩ : syracuseStep 7989353 = 5992015) B5992015
theorem B3206591 : Blo 738327 3206591 := bstep (se 1 (by rfl) ⟨2404943, by rfl⟩ : syracuseStep 3206591 = 4809887) B4809887
theorem B13725611 : Blo 738327 13725611 := bstep (se 1 (by rfl) ⟨10294208, by rfl⟩ : syracuseStep 13725611 = 20588417) B20588417
theorem B6746195 : Blo 738327 6746195 := bstep (se 1 (by rfl) ⟨5059646, by rfl⟩ : syracuseStep 6746195 = 10119293) B10119293
theorem B5992859 : Blo 738327 5992859 := bstep (se 1 (by rfl) ⟨4494644, by rfl⟩ : syracuseStep 5992859 = 8989289) B8989289
theorem B1667519 : Blo 738327 1667519 := bstep (se 1 (by rfl) ⟨1250639, by rfl⟩ : syracuseStep 1667519 = 2501279) B2501279
theorem B1110719 : Blo 738327 1110719 := bstep (se 1 (by rfl) ⟨833039, by rfl⟩ : syracuseStep 1110719 = 1666079) B1666079
theorem B5993999 : Blo 738327 5993999 := bstep (se 1 (by rfl) ⟨4495499, by rfl⟩ : syracuseStep 5993999 = 8990999) B8990999
theorem B1668671 : Blo 738327 1668671 := bstep (se 1 (by rfl) ⟨1251503, by rfl⟩ : syracuseStep 1668671 = 2503007) B2503007
theorem B9009143 : Blo 738327 9009143 := bstep (se 1 (by rfl) ⟨6756857, by rfl⟩ : syracuseStep 9009143 = 13513715) B13513715
theorem B2815991 : Blo 738327 2815991 := bstep (se 1 (by rfl) ⟨2111993, by rfl⟩ : syracuseStep 2815991 = 4223987) B4223987
theorem B6748535 : Blo 738327 6748535 := bstep (se 1 (by rfl) ⟨5061401, by rfl⟩ : syracuseStep 6748535 = 10122803) B10122803
theorem B15170399 : Blo 738327 15170399 := bstep (se 1 (by rfl) ⟨11377799, by rfl⟩ : syracuseStep 15170399 = 22755599) B22755599
theorem B1872335 : Blo 738327 1872335 := bstep (se 1 (by rfl) ⟨1404251, by rfl⟩ : syracuseStep 1872335 = 2808503) B2808503
theorem B1251355 : Blo 738327 1251355 := bstep (se 1 (by rfl) ⟨938516, by rfl⟩ : syracuseStep 1251355 = 1877033) B1877033
theorem B2137727 : Blo 738327 2137727 := bstep (se 1 (by rfl) ⟨1603295, by rfl⟩ : syracuseStep 2137727 = 3206591) B3206591
theorem B17309497 : Blo 738327 17309497 := bstep (se 2 (by rfl) ⟨6491061, by rfl⟩ : syracuseStep 17309497 = 12982123) B12982123
theorem B9150407 : Blo 738327 9150407 := bstep (se 1 (by rfl) ⟨6862805, by rfl⟩ : syracuseStep 9150407 = 13725611) B13725611
theorem B4497463 : Blo 738327 4497463 := bstep (se 1 (by rfl) ⟨3373097, by rfl⟩ : syracuseStep 4497463 = 6746195) B6746195
theorem B6006095 : Blo 738327 6006095 := bstep (se 1 (by rfl) ⟨4504571, by rfl⟩ : syracuseStep 6006095 = 9009143) B9009143
theorem B1877327 : Blo 738327 1877327 := bstep (se 1 (by rfl) ⟨1407995, by rfl⟩ : syracuseStep 1877327 = 2815991) B2815991
theorem B4499023 : Blo 738327 4499023 := bstep (se 1 (by rfl) ⟨3374267, by rfl⟩ : syracuseStep 4499023 = 6748535) B6748535
theorem B3748031 : Blo 738327 3748031 := bstep (se 1 (by rfl) ⟨2811023, by rfl⟩ : syracuseStep 3748031 = 5622047) B5622047
theorem B10138567 : Blo 738327 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B4502891 : Blo 738327 4502891 := bstep (se 1 (by rfl) ⟨3377168, by rfl⟩ : syracuseStep 4502891 = 6754337) B6754337
theorem B9484289 : Blo 738327 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B834331 : Blo 738327 834331 := bstep (se 1 (by rfl) ⟨625748, by rfl⟩ : syracuseStep 834331 = 1251497) B1251497
theorem B60702371 : Blo 738327 60702371 := bstep (se 1 (by rfl) ⟨45526778, by rfl⟩ : syracuseStep 60702371 = 91053557) B91053557
theorem B57590135 : Blo 738327 57590135 := bstep (se 1 (by rfl) ⟨43192601, by rfl⟩ : syracuseStep 57590135 = 86385203) B86385203
theorem B5326235 : Blo 738327 5326235 := bstep (se 1 (by rfl) ⟨3994676, by rfl⟩ : syracuseStep 5326235 = 7989353) B7989353
theorem B14206751 : Blo 738327 14206751 := bstep (se 1 (by rfl) ⟨10655063, by rfl⟩ : syracuseStep 14206751 = 21310127) B21310127
theorem B5621561 : Blo 738327 5621561 := bstep (se 2 (by rfl) ⟨2108085, by rfl⟩ : syracuseStep 5621561 = 4216171) B4216171
theorem B3165257 : Blo 738327 3165257 := bstep (se 2 (by rfl) ⟨1186971, by rfl⟩ : syracuseStep 3165257 = 2373943) B2373943
theorem B740479 : Blo 738327 740479 := bstep (se 1 (by rfl) ⟨555359, by rfl⟩ : syracuseStep 740479 = 1110719) B1110719
theorem B2805131 : Blo 738327 2805131 := bstep (se 1 (by rfl) ⟨2103848, by rfl⟩ : syracuseStep 2805131 = 4207697) B4207697
theorem B21614363 : Blo 738327 21614363 := bstep (se 1 (by rfl) ⟨16210772, by rfl⟩ : syracuseStep 21614363 = 32421545) B32421545
theorem B10113599 : Blo 738327 10113599 := bstep (se 1 (by rfl) ⟨7585199, by rfl⟩ : syracuseStep 10113599 = 15170399) B15170399
theorem B1267103 : Blo 738327 1267103 := bstep (se 1 (by rfl) ⟨950327, by rfl⟩ : syracuseStep 1267103 = 1900655) B1900655
theorem B10147319 : Blo 738327 10147319 := bstep (se 1 (by rfl) ⟨7610489, by rfl⟩ : syracuseStep 10147319 = 15220979) B15220979
theorem B38459929 : Blo 738327 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B5070377 : Blo 738327 5070377 := bstep (se 2 (by rfl) ⟨1901391, by rfl⟩ : syracuseStep 5070377 = 3802783) B3802783
theorem B1662857 : Blo 738327 1662857 := bstep (se 2 (by rfl) ⟨623571, by rfl⟩ : syracuseStep 1662857 = 1247143) B1247143
theorem B1663073 : Blo 738327 1663073 := bstep (se 2 (by rfl) ⟨623652, by rfl⟩ : syracuseStep 1663073 = 1247305) B1247305
theorem B2810963 : Blo 738327 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B1107695 : Blo 738327 1107695 := bstep (se 1 (by rfl) ⟨830771, by rfl⟩ : syracuseStep 1107695 = 1661543) B1661543
theorem B1108079 : Blo 738327 1108079 := bstep (se 1 (by rfl) ⟨831059, by rfl⟩ : syracuseStep 1108079 = 1662119) B1662119
theorem B9464039 : Blo 738327 9464039 := bstep (se 1 (by rfl) ⟨7098029, by rfl⟩ : syracuseStep 9464039 = 14196059) B14196059
theorem B9628091 : Blo 738327 9628091 := bstep (se 1 (by rfl) ⟨7221068, by rfl⟩ : syracuseStep 9628091 = 14442137) B14442137
theorem B1666151 : Blo 738327 1666151 := bstep (se 1 (by rfl) ⟨1249613, by rfl⟩ : syracuseStep 1666151 = 2499227) B2499227
theorem B1109759 : Blo 738327 1109759 := bstep (se 1 (by rfl) ⟨832319, by rfl⟩ : syracuseStep 1109759 = 1664639) B1664639
theorem B2257199 : Blo 738327 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B10253033 : Blo 738327 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B3995239 : Blo 738327 3995239 := bstep (se 1 (by rfl) ⟨2996429, by rfl⟩ : syracuseStep 3995239 = 5992859) B5992859
theorem B1111679 : Blo 738327 1111679 := bstep (se 1 (by rfl) ⟨833759, by rfl⟩ : syracuseStep 1111679 = 1667519) B1667519
theorem B1669211 : Blo 738327 1669211 := bstep (se 1 (by rfl) ⟨1251908, by rfl⟩ : syracuseStep 1669211 = 2503817) B2503817
theorem B3995999 : Blo 738327 3995999 := bstep (se 1 (by rfl) ⟨2996999, by rfl⟩ : syracuseStep 3995999 = 5993999) B5993999
theorem B1112447 : Blo 738327 1112447 := bstep (se 1 (by rfl) ⟨834335, by rfl⟩ : syracuseStep 1112447 = 1668671) B1668671
theorem B4816435 : Blo 738327 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B23986469 : Blo 738327 23986469 := bstep (se 4 (by rfl) ⟨2248731, by rfl⟩ : syracuseStep 23986469 = 4497463) B4497463
theorem B9471167 : Blo 738327 9471167 := bstep (se 1 (by rfl) ⟨7103375, by rfl⟩ : syracuseStep 9471167 = 14206751) B14206751
theorem B26969597 : Blo 738327 26969597 := bstep (se 3 (by rfl) ⟨5056799, by rfl⟩ : syracuseStep 26969597 = 10113599) B10113599
theorem B5998697 : Blo 738327 5998697 := bstep (se 2 (by rfl) ⟨2249511, by rfl⟩ : syracuseStep 5998697 = 4499023) B4499023
theorem B1870087 : Blo 738327 1870087 := bstep (se 1 (by rfl) ⟨1402565, by rfl⟩ : syracuseStep 1870087 = 2805131) B2805131
theorem B1248223 : Blo 738327 1248223 := bstep (se 1 (by rfl) ⟨936167, by rfl⟩ : syracuseStep 1248223 = 1872335) B1872335
theorem B6100271 : Blo 738327 6100271 := bstep (se 1 (by rfl) ⟨4575203, by rfl⟩ : syracuseStep 6100271 = 9150407) B9150407
theorem B1873975 : Blo 738327 1873975 := bstep (se 1 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 1873975 = 2810963) B2810963
theorem B4004063 : Blo 738327 4004063 := bstep (se 1 (by rfl) ⟨3003047, by rfl⟩ : syracuseStep 4004063 = 6006095) B6006095
theorem B1251551 : Blo 738327 1251551 := bstep (se 1 (by rfl) ⟨938663, by rfl⟩ : syracuseStep 1251551 = 1877327) B1877327
theorem B2498687 : Blo 738327 2498687 := bstep (se 1 (by rfl) ⟨1874015, by rfl⟩ : syracuseStep 2498687 = 3748031) B3748031
theorem B2663999 : Blo 738327 2663999 := bstep (se 1 (by rfl) ⟨1997999, by rfl⟩ : syracuseStep 2663999 = 3995999) B3995999
theorem B23079329 : Blo 738327 23079329 := bstep (se 2 (by rfl) ⟨8654748, by rfl⟩ : syracuseStep 23079329 = 17309497) B17309497
theorem B3550823 : Blo 738327 3550823 := bstep (se 1 (by rfl) ⟨2663117, by rfl⟩ : syracuseStep 3550823 = 5326235) B5326235
theorem B3747707 : Blo 738327 3747707 := bstep (se 1 (by rfl) ⟨2810780, by rfl⟩ : syracuseStep 3747707 = 5621561) B5621561
theorem B2110171 : Blo 738327 2110171 := bstep (se 1 (by rfl) ⟨1582628, by rfl⟩ : syracuseStep 2110171 = 3165257) B3165257
theorem B12007709 : Blo 738327 12007709 := bstep (se 3 (by rfl) ⟨2251445, by rfl⟩ : syracuseStep 12007709 = 4502891) B4502891
theorem B6764879 : Blo 738327 6764879 := bstep (se 1 (by rfl) ⟨5073659, by rfl⟩ : syracuseStep 6764879 = 10147319) B10147319
theorem B1425151 : Blo 738327 1425151 := bstep (se 1 (by rfl) ⟨1068863, by rfl⟩ : syracuseStep 1425151 = 2137727) B2137727
theorem B738463 : Blo 738327 738463 := bstep (se 1 (by rfl) ⟨553847, by rfl⟩ : syracuseStep 738463 = 1107695) B1107695
theorem B13518089 : Blo 738327 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B738719 : Blo 738327 738719 := bstep (se 1 (by rfl) ⟨554039, by rfl⟩ : syracuseStep 738719 = 1108079) B1108079
theorem B6309359 : Blo 738327 6309359 := bstep (se 1 (by rfl) ⟨4732019, by rfl⟩ : syracuseStep 6309359 = 9464039) B9464039
theorem B5326985 : Blo 738327 5326985 := bstep (se 2 (by rfl) ⟨1997619, by rfl⟩ : syracuseStep 5326985 = 3995239) B3995239
theorem B739839 : Blo 738327 739839 := bstep (se 1 (by rfl) ⟨554879, by rfl⟩ : syracuseStep 739839 = 1109759) B1109759
theorem B6835355 : Blo 738327 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B741119 : Blo 738327 741119 := bstep (se 1 (by rfl) ⟨555839, by rfl⟩ : syracuseStep 741119 = 1111679) B1111679
theorem B13521005 : Blo 738327 13521005 := bstep (se 3 (by rfl) ⟨2535188, by rfl⟩ : syracuseStep 13521005 = 5070377) B5070377
theorem B741631 : Blo 738327 741631 := bstep (se 1 (by rfl) ⟨556223, by rfl⟩ : syracuseStep 741631 = 1112447) B1112447
theorem B38393423 : Blo 738327 38393423 := bstep (se 1 (by rfl) ⟨28795067, by rfl⟩ : syracuseStep 38393423 = 57590135) B57590135
theorem B14409575 : Blo 738327 14409575 := bstep (se 1 (by rfl) ⟨10807181, by rfl⟩ : syracuseStep 14409575 = 21614363) B21614363
theorem B844735 : Blo 738327 844735 := bstep (se 1 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 844735 = 1267103) B1267103
theorem B1108571 : Blo 738327 1108571 := bstep (se 1 (by rfl) ⟨831428, by rfl⟩ : syracuseStep 1108571 = 1662857) B1662857
theorem B1108715 : Blo 738327 1108715 := bstep (se 1 (by rfl) ⟨831536, by rfl⟩ : syracuseStep 1108715 = 1663073) B1663073
theorem B6418727 : Blo 738327 6418727 := bstep (se 1 (by rfl) ⟨4814045, by rfl⟩ : syracuseStep 6418727 = 9628091) B9628091
theorem B1110767 : Blo 738327 1110767 := bstep (se 1 (by rfl) ⟨833075, by rfl⟩ : syracuseStep 1110767 = 1666151) B1666151
theorem B1668473 : Blo 738327 1668473 := bstep (se 2 (by rfl) ⟨625677, by rfl⟩ : syracuseStep 1668473 = 1251355) B1251355
theorem B1504799 : Blo 738327 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B51279905 : Blo 738327 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B1112441 : Blo 738327 1112441 := bstep (se 2 (by rfl) ⟨417165, by rfl⟩ : syracuseStep 1112441 = 834331) B834331
theorem B6322859 : Blo 738327 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B1112807 : Blo 738327 1112807 := bstep (se 1 (by rfl) ⟨834605, by rfl⟩ : syracuseStep 1112807 = 1669211) B1669211
theorem B6421913 : Blo 738327 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B40468247 : Blo 738327 40468247 := bstep (se 1 (by rfl) ⟨30351185, by rfl⟩ : syracuseStep 40468247 = 60702371) B60702371
theorem B15990979 : Blo 738327 15990979 := bstep (se 1 (by rfl) ⟨11993234, by rfl⟩ : syracuseStep 15990979 = 23986469) B23986469
theorem B9012059 : Blo 738327 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B3999131 : Blo 738327 3999131 := bstep (se 1 (by rfl) ⟨2999348, by rfl⟩ : syracuseStep 3999131 = 5998697) B5998697
theorem B4556903 : Blo 738327 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B9014003 : Blo 738327 9014003 := bstep (se 1 (by rfl) ⟨6760502, by rfl⟩ : syracuseStep 9014003 = 13521005) B13521005
theorem B2493449 : Blo 738327 2493449 := bstep (se 2 (by rfl) ⟨935043, by rfl⟩ : syracuseStep 2493449 = 1870087) B1870087
theorem B4066847 : Blo 738327 4066847 := bstep (se 1 (by rfl) ⟨3050135, by rfl⟩ : syracuseStep 4066847 = 6100271) B6100271
theorem B25595615 : Blo 738327 25595615 := bstep (se 1 (by rfl) ⟨19196711, by rfl⟩ : syracuseStep 25595615 = 38393423) B38393423
theorem B9606383 : Blo 738327 9606383 := bstep (se 1 (by rfl) ⟨7204787, by rfl⟩ : syracuseStep 9606383 = 14409575) B14409575
theorem B136746413 : Blo 738327 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B1775999 : Blo 738327 1775999 := bstep (se 1 (by rfl) ⟨1331999, by rfl⟩ : syracuseStep 1775999 = 2663999) B2663999
theorem B2367215 : Blo 738327 2367215 := bstep (se 1 (by rfl) ⟨1775411, by rfl⟩ : syracuseStep 2367215 = 3550823) B3550823
theorem B2498471 : Blo 738327 2498471 := bstep (se 1 (by rfl) ⟨1873853, by rfl⟩ : syracuseStep 2498471 = 3747707) B3747707
theorem B2498633 : Blo 738327 2498633 := bstep (se 2 (by rfl) ⟨936987, by rfl⟩ : syracuseStep 2498633 = 1873975) B1873975
theorem B8005139 : Blo 738327 8005139 := bstep (se 1 (by rfl) ⟨6003854, by rfl⟩ : syracuseStep 8005139 = 12007709) B12007709
theorem B26978831 : Blo 738327 26978831 := bstep (se 1 (by rfl) ⟨20234123, by rfl⟩ : syracuseStep 26978831 = 40468247) B40468247
theorem B4206239 : Blo 738327 4206239 := bstep (se 1 (by rfl) ⟨3154679, by rfl⟩ : syracuseStep 4206239 = 6309359) B6309359
theorem B1126313 : Blo 738327 1126313 := bstep (se 2 (by rfl) ⟨422367, by rfl⟩ : syracuseStep 1126313 = 844735) B844735
theorem B3551323 : Blo 738327 3551323 := bstep (se 1 (by rfl) ⟨2663492, by rfl⟩ : syracuseStep 3551323 = 5326985) B5326985
theorem B2669375 : Blo 738327 2669375 := bstep (se 1 (by rfl) ⟨2002031, by rfl⟩ : syracuseStep 2669375 = 4004063) B4004063
theorem B834367 : Blo 738327 834367 := bstep (se 1 (by rfl) ⟨625775, by rfl⟩ : syracuseStep 834367 = 1251551) B1251551
theorem B15386219 : Blo 738327 15386219 := bstep (se 1 (by rfl) ⟨11539664, by rfl⟩ : syracuseStep 15386219 = 23079329) B23079329
theorem B739047 : Blo 738327 739047 := bstep (se 1 (by rfl) ⟨554285, by rfl⟩ : syracuseStep 739047 = 1108571) B1108571
theorem B739143 : Blo 738327 739143 := bstep (se 1 (by rfl) ⟨554357, by rfl⟩ : syracuseStep 739143 = 1108715) B1108715
theorem B4279151 : Blo 738327 4279151 := bstep (se 1 (by rfl) ⟨3209363, by rfl⟩ : syracuseStep 4279151 = 6418727) B6418727
theorem B740511 : Blo 738327 740511 := bstep (se 1 (by rfl) ⟨555383, by rfl⟩ : syracuseStep 740511 = 1110767) B1110767
theorem B1003199 : Blo 738327 1003199 := bstep (se 1 (by rfl) ⟨752399, by rfl⟩ : syracuseStep 1003199 = 1504799) B1504799
theorem B4509919 : Blo 738327 4509919 := bstep (se 1 (by rfl) ⟨3382439, by rfl⟩ : syracuseStep 4509919 = 6764879) B6764879
theorem B741627 : Blo 738327 741627 := bstep (se 1 (by rfl) ⟨556220, by rfl⟩ : syracuseStep 741627 = 1112441) B1112441
theorem B4215239 : Blo 738327 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B741871 : Blo 738327 741871 := bstep (se 1 (by rfl) ⟨556403, by rfl⟩ : syracuseStep 741871 = 1112807) B1112807
theorem B4281275 : Blo 738327 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B6314111 : Blo 738327 6314111 := bstep (se 1 (by rfl) ⟨4735583, by rfl⟩ : syracuseStep 6314111 = 9471167) B9471167
theorem B17979731 : Blo 738327 17979731 := bstep (se 1 (by rfl) ⟨13484798, by rfl⟩ : syracuseStep 17979731 = 26969597) B26969597
theorem B1664297 : Blo 738327 1664297 := bstep (se 2 (by rfl) ⟨624111, by rfl⟩ : syracuseStep 1664297 = 1248223) B1248223
theorem B1665791 : Blo 738327 1665791 := bstep (se 1 (by rfl) ⟨1249343, by rfl⟩ : syracuseStep 1665791 = 2498687) B2498687
theorem B2813561 : Blo 738327 2813561 := bstep (se 2 (by rfl) ⟨1055085, by rfl⟩ : syracuseStep 2813561 = 2110171) B2110171
theorem B1112315 : Blo 738327 1112315 := bstep (se 1 (by rfl) ⟨834236, by rfl⟩ : syracuseStep 1112315 = 1668473) B1668473
theorem B1900201 : Blo 738327 1900201 := bstep (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) B1425151
theorem B10257479 : Blo 738327 10257479 := bstep (se 1 (by rfl) ⟨7693109, by rfl⟩ : syracuseStep 10257479 = 15386219) B15386219
theorem B2852767 : Blo 738327 2852767 := bstep (se 1 (by rfl) ⟨2139575, by rfl⟩ : syracuseStep 2852767 = 4279151) B4279151
theorem B91164275 : Blo 738327 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B1183999 : Blo 738327 1183999 := bstep (se 1 (by rfl) ⟨887999, by rfl⟩ : syracuseStep 1183999 = 1775999) B1775999
theorem B1578143 : Blo 738327 1578143 := bstep (se 1 (by rfl) ⟨1183607, by rfl⟩ : syracuseStep 1578143 = 2367215) B2367215
theorem B1875707 : Blo 738327 1875707 := bstep (se 1 (by rfl) ⟨1406780, by rfl⟩ : syracuseStep 1875707 = 2813561) B2813561
theorem B1779583 : Blo 738327 1779583 := bstep (se 1 (by rfl) ⟨1334687, by rfl⟩ : syracuseStep 1779583 = 2669375) B2669375
theorem B2533601 : Blo 738327 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B6008039 : Blo 738327 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B2666087 : Blo 738327 2666087 := bstep (se 1 (by rfl) ⟨1999565, by rfl⟩ : syracuseStep 2666087 = 3999131) B3999131
theorem B48606965 : Blo 738327 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B6009335 : Blo 738327 6009335 := bstep (se 1 (by rfl) ⟨4507001, by rfl⟩ : syracuseStep 6009335 = 9014003) B9014003
theorem B11416733 : Blo 738327 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B6404255 : Blo 738327 6404255 := bstep (se 1 (by rfl) ⟨4803191, by rfl⟩ : syracuseStep 6404255 = 9606383) B9606383
theorem B4209407 : Blo 738327 4209407 := bstep (se 1 (by rfl) ⟨3157055, by rfl⟩ : syracuseStep 4209407 = 6314111) B6314111
theorem B4735097 : Blo 738327 4735097 := bstep (se 2 (by rfl) ⟨1775661, by rfl⟩ : syracuseStep 4735097 = 3551323) B3551323
theorem B6013225 : Blo 738327 6013225 := bstep (se 2 (by rfl) ⟨2254959, by rfl⟩ : syracuseStep 6013225 = 4509919) B4509919
theorem B2804159 : Blo 738327 2804159 := bstep (se 1 (by rfl) ⟨2103119, by rfl⟩ : syracuseStep 2804159 = 4206239) B4206239
theorem B741543 : Blo 738327 741543 := bstep (se 1 (by rfl) ⟨556157, by rfl⟩ : syracuseStep 741543 = 1112315) B1112315
theorem B2675197 : Blo 738327 2675197 := bstep (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) B1003199
theorem B21321305 : Blo 738327 21321305 := bstep (se 2 (by rfl) ⟨7995489, by rfl⟩ : syracuseStep 21321305 = 15990979) B15990979
theorem B1662299 : Blo 738327 1662299 := bstep (se 1 (by rfl) ⟨1246724, by rfl⟩ : syracuseStep 1662299 = 2493449) B2493449
theorem B2711231 : Blo 738327 2711231 := bstep (se 1 (by rfl) ⟨2033423, by rfl⟩ : syracuseStep 2711231 = 4066847) B4066847
theorem B2810159 : Blo 738327 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B11986487 : Blo 738327 11986487 := bstep (se 1 (by rfl) ⟨8989865, by rfl⟩ : syracuseStep 11986487 = 17979731) B17979731
theorem B1665647 : Blo 738327 1665647 := bstep (se 1 (by rfl) ⟨1249235, by rfl⟩ : syracuseStep 1665647 = 2498471) B2498471
theorem B1665755 : Blo 738327 1665755 := bstep (se 1 (by rfl) ⟨1249316, by rfl⟩ : syracuseStep 1665755 = 2498633) B2498633
theorem B1109531 : Blo 738327 1109531 := bstep (se 1 (by rfl) ⟨832148, by rfl⟩ : syracuseStep 1109531 = 1664297) B1664297
theorem B5336759 : Blo 738327 5336759 := bstep (se 1 (by rfl) ⟨4002569, by rfl⟩ : syracuseStep 5336759 = 8005139) B8005139
theorem B17985887 : Blo 738327 17985887 := bstep (se 1 (by rfl) ⟨13489415, by rfl⟩ : syracuseStep 17985887 = 26978831) B26978831
theorem B1110527 : Blo 738327 1110527 := bstep (se 1 (by rfl) ⟨832895, by rfl⟩ : syracuseStep 1110527 = 1665791) B1665791
theorem B750875 : Blo 738327 750875 := bstep (se 1 (by rfl) ⟨563156, by rfl⟩ : syracuseStep 750875 = 1126313) B1126313
theorem B1112489 : Blo 738327 1112489 := bstep (se 2 (by rfl) ⟨417183, by rfl⟩ : syracuseStep 1112489 = 834367) B834367
theorem B68254973 : Blo 738327 68254973 := bstep (se 3 (by rfl) ⟨12797807, by rfl⟩ : syracuseStep 68254973 = 25595615) B25595615
theorem B1869439 : Blo 738327 1869439 := bstep (se 1 (by rfl) ⟨1402079, by rfl⟩ : syracuseStep 1869439 = 2804159) B2804159
theorem B3803689 : Blo 738327 3803689 := bstep (se 2 (by rfl) ⟨1426383, by rfl⟩ : syracuseStep 3803689 = 2852767) B2852767
theorem B2002333 : Blo 738327 2002333 := bstep (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) B750875
theorem B1807487 : Blo 738327 1807487 := bstep (se 1 (by rfl) ⟨1355615, by rfl⟩ : syracuseStep 1807487 = 2711231) B2711231
theorem B1250471 : Blo 738327 1250471 := bstep (se 1 (by rfl) ⟨937853, by rfl⟩ : syracuseStep 1250471 = 1875707) B1875707
theorem B1873439 : Blo 738327 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B1578665 : Blo 738327 1578665 := bstep (se 2 (by rfl) ⟨591999, by rfl⟩ : syracuseStep 1578665 = 1183999) B1183999
theorem B4005359 : Blo 738327 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B1777391 : Blo 738327 1777391 := bstep (se 1 (by rfl) ⟨1333043, by rfl⟩ : syracuseStep 1777391 = 2666087) B2666087
theorem B4006223 : Blo 738327 4006223 := bstep (se 1 (by rfl) ⟨3004667, by rfl⟩ : syracuseStep 4006223 = 6009335) B6009335
theorem B7611155 : Blo 738327 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B4269503 : Blo 738327 4269503 := bstep (se 1 (by rfl) ⟨3202127, by rfl⟩ : syracuseStep 4269503 = 6404255) B6404255
theorem B3156731 : Blo 738327 3156731 := bstep (se 1 (by rfl) ⟨2367548, by rfl⟩ : syracuseStep 3156731 = 4735097) B4735097
theorem B2372777 : Blo 738327 2372777 := bstep (se 2 (by rfl) ⟨889791, by rfl⟩ : syracuseStep 2372777 = 1779583) B1779583
theorem B4208381 : Blo 738327 4208381 := bstep (se 3 (by rfl) ⟨789071, by rfl⟩ : syracuseStep 4208381 = 1578143) B1578143
theorem B1689067 : Blo 738327 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B739687 : Blo 738327 739687 := bstep (se 1 (by rfl) ⟨554765, by rfl⟩ : syracuseStep 739687 = 1109531) B1109531
theorem B3557839 : Blo 738327 3557839 := bstep (se 1 (by rfl) ⟨2668379, by rfl⟩ : syracuseStep 3557839 = 5336759) B5336759
theorem B740351 : Blo 738327 740351 := bstep (se 1 (by rfl) ⟨555263, by rfl⟩ : syracuseStep 740351 = 1110527) B1110527
theorem B741659 : Blo 738327 741659 := bstep (se 1 (by rfl) ⟨556244, by rfl⟩ : syracuseStep 741659 = 1112489) B1112489
theorem B2806271 : Blo 738327 2806271 := bstep (se 1 (by rfl) ⟨2104703, by rfl⟩ : syracuseStep 2806271 = 4209407) B4209407
theorem B45503315 : Blo 738327 45503315 := bstep (se 1 (by rfl) ⟨34127486, by rfl⟩ : syracuseStep 45503315 = 68254973) B68254973
theorem B8017633 : Blo 738327 8017633 := bstep (se 2 (by rfl) ⟨3006612, by rfl⟩ : syracuseStep 8017633 = 6013225) B6013225
theorem B6838319 : Blo 738327 6838319 := bstep (se 1 (by rfl) ⟨5128739, by rfl⟩ : syracuseStep 6838319 = 10257479) B10257479
theorem B60776183 : Blo 738327 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B14214203 : Blo 738327 14214203 := bstep (se 1 (by rfl) ⟨10660652, by rfl⟩ : syracuseStep 14214203 = 21321305) B21321305
theorem B1108199 : Blo 738327 1108199 := bstep (se 1 (by rfl) ⟨831149, by rfl⟩ : syracuseStep 1108199 = 1662299) B1662299
theorem B3566929 : Blo 738327 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B7990991 : Blo 738327 7990991 := bstep (se 1 (by rfl) ⟨5993243, by rfl⟩ : syracuseStep 7990991 = 11986487) B11986487
theorem B1110431 : Blo 738327 1110431 := bstep (se 1 (by rfl) ⟨832823, by rfl⟩ : syracuseStep 1110431 = 1665647) B1665647
theorem B1110503 : Blo 738327 1110503 := bstep (se 1 (by rfl) ⟨832877, by rfl⟩ : syracuseStep 1110503 = 1665755) B1665755
theorem B32404643 : Blo 738327 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B11990591 : Blo 738327 11990591 := bstep (se 1 (by rfl) ⟨8992943, by rfl⟩ : syracuseStep 11990591 = 17985887) B17985887
theorem B2492585 : Blo 738327 2492585 := bstep (se 2 (by rfl) ⟨934719, by rfl⟩ : syracuseStep 2492585 = 1869439) B1869439
theorem B1870847 : Blo 738327 1870847 := bstep (se 1 (by rfl) ⟨1403135, by rfl⟩ : syracuseStep 1870847 = 2806271) B2806271
theorem B1248959 : Blo 738327 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B1052443 : Blo 738327 1052443 := bstep (se 1 (by rfl) ⟨789332, by rfl⟩ : syracuseStep 1052443 = 1578665) B1578665
theorem B4558879 : Blo 738327 4558879 := bstep (se 1 (by rfl) ⟨3419159, by rfl⟩ : syracuseStep 4558879 = 6838319) B6838319
theorem B4755905 : Blo 738327 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B1184927 : Blo 738327 1184927 := bstep (se 1 (by rfl) ⟨888695, by rfl⟩ : syracuseStep 1184927 = 1777391) B1777391
theorem B9476135 : Blo 738327 9476135 := bstep (se 1 (by rfl) ⟨7107101, by rfl⟩ : syracuseStep 9476135 = 14214203) B14214203
theorem B2104487 : Blo 738327 2104487 := bstep (se 1 (by rfl) ⟨1578365, by rfl⟩ : syracuseStep 2104487 = 3156731) B3156731
theorem B10690177 : Blo 738327 10690177 := bstep (se 2 (by rfl) ⟨4008816, by rfl⟩ : syracuseStep 10690177 = 8017633) B8017633
theorem B21603095 : Blo 738327 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B1581851 : Blo 738327 1581851 := bstep (se 1 (by rfl) ⟨1186388, by rfl⟩ : syracuseStep 1581851 = 2372777) B2372777
theorem B833647 : Blo 738327 833647 := bstep (se 1 (by rfl) ⟨625235, by rfl⟩ : syracuseStep 833647 = 1250471) B1250471
theorem B2669777 : Blo 738327 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B2670239 : Blo 738327 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B40517455 : Blo 738327 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B2670815 : Blo 738327 2670815 := bstep (se 1 (by rfl) ⟨2003111, by rfl⟩ : syracuseStep 2670815 = 4006223) B4006223
theorem B738799 : Blo 738327 738799 := bstep (se 1 (by rfl) ⟨554099, by rfl⟩ : syracuseStep 738799 = 1108199) B1108199
theorem B5327327 : Blo 738327 5327327 := bstep (se 1 (by rfl) ⟨3995495, by rfl⟩ : syracuseStep 5327327 = 7990991) B7990991
theorem B740287 : Blo 738327 740287 := bstep (se 1 (by rfl) ⟨555215, by rfl⟩ : syracuseStep 740287 = 1110431) B1110431
theorem B740335 : Blo 738327 740335 := bstep (se 1 (by rfl) ⟨555251, by rfl⟩ : syracuseStep 740335 = 1110503) B1110503
theorem B2805587 : Blo 738327 2805587 := bstep (se 1 (by rfl) ⟨2104190, by rfl⟩ : syracuseStep 2805587 = 4208381) B4208381
theorem B2252089 : Blo 738327 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B30335543 : Blo 738327 30335543 := bstep (se 1 (by rfl) ⟨22751657, by rfl⟩ : syracuseStep 30335543 = 45503315) B45503315
theorem B4743785 : Blo 738327 4743785 := bstep (se 2 (by rfl) ⟨1778919, by rfl⟩ : syracuseStep 4743785 = 3557839) B3557839
theorem B5071585 : Blo 738327 5071585 := bstep (se 2 (by rfl) ⟨1901844, by rfl⟩ : syracuseStep 5071585 = 3803689) B3803689
theorem B1204991 : Blo 738327 1204991 := bstep (se 1 (by rfl) ⟨903743, by rfl⟩ : syracuseStep 1204991 = 1807487) B1807487
theorem B5074103 : Blo 738327 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B2846335 : Blo 738327 2846335 := bstep (se 1 (by rfl) ⟨2134751, by rfl⟩ : syracuseStep 2846335 = 4269503) B4269503
theorem B7993727 : Blo 738327 7993727 := bstep (se 1 (by rfl) ⟨5995295, by rfl⟩ : syracuseStep 7993727 = 11990591) B11990591
theorem B1247231 : Blo 738327 1247231 := bstep (se 1 (by rfl) ⟨935423, by rfl⟩ : syracuseStep 1247231 = 1870847) B1870847
theorem B1870391 : Blo 738327 1870391 := bstep (se 1 (by rfl) ⟨1402793, by rfl⟩ : syracuseStep 1870391 = 2805587) B2805587
theorem B20223695 : Blo 738327 20223695 := bstep (se 1 (by rfl) ⟨15167771, by rfl⟩ : syracuseStep 20223695 = 30335543) B30335543
theorem B1054567 : Blo 738327 1054567 := bstep (se 1 (by rfl) ⟨790925, by rfl⟩ : syracuseStep 1054567 = 1581851) B1581851
theorem B3382735 : Blo 738327 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B1779851 : Blo 738327 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B1780159 : Blo 738327 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B1780543 : Blo 738327 1780543 := bstep (se 1 (by rfl) ⟨1335407, by rfl⟩ : syracuseStep 1780543 = 2670815) B2670815
theorem B6762113 : Blo 738327 6762113 := bstep (se 2 (by rfl) ⟨2535792, by rfl⟩ : syracuseStep 6762113 = 5071585) B5071585
theorem B832639 : Blo 738327 832639 := bstep (se 1 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 832639 = 1248959) B1248959
theorem B3159805 : Blo 738327 3159805 := bstep (se 3 (by rfl) ⟨592463, by rfl⟩ : syracuseStep 3159805 = 1184927) B1184927
theorem B6078505 : Blo 738327 6078505 := bstep (se 2 (by rfl) ⟨2279439, by rfl⟩ : syracuseStep 6078505 = 4558879) B4558879
theorem B3162523 : Blo 738327 3162523 := bstep (se 1 (by rfl) ⟨2371892, by rfl⟩ : syracuseStep 3162523 = 4743785) B4743785
theorem B803327 : Blo 738327 803327 := bstep (se 1 (by rfl) ⟨602495, by rfl⟩ : syracuseStep 803327 = 1204991) B1204991
theorem B14402063 : Blo 738327 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B14206205 : Blo 738327 14206205 := bstep (se 3 (by rfl) ⟨2663663, by rfl⟩ : syracuseStep 14206205 = 5327327) B5327327
theorem B12011141 : Blo 738327 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B5329151 : Blo 738327 5329151 := bstep (se 1 (by rfl) ⟨3996863, by rfl⟩ : syracuseStep 5329151 = 7993727) B7993727
theorem B54023273 : Blo 738327 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B1661723 : Blo 738327 1661723 := bstep (se 1 (by rfl) ⟨1246292, by rfl⟩ : syracuseStep 1661723 = 2492585) B2492585
theorem B3170603 : Blo 738327 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B6317423 : Blo 738327 6317423 := bstep (se 1 (by rfl) ⟨4738067, by rfl⟩ : syracuseStep 6317423 = 9476135) B9476135
theorem B1402991 : Blo 738327 1402991 := bstep (se 1 (by rfl) ⟨1052243, by rfl⟩ : syracuseStep 1402991 = 2104487) B2104487
theorem B3795113 : Blo 738327 3795113 := bstep (se 2 (by rfl) ⟨1423167, by rfl⟩ : syracuseStep 3795113 = 2846335) B2846335
theorem B1403257 : Blo 738327 1403257 := bstep (se 2 (by rfl) ⟨526221, by rfl⟩ : syracuseStep 1403257 = 1052443) B1052443
theorem B1111529 : Blo 738327 1111529 := bstep (se 2 (by rfl) ⟨416823, by rfl⟩ : syracuseStep 1111529 = 833647) B833647
theorem B14253569 : Blo 738327 14253569 := bstep (se 2 (by rfl) ⟨5345088, by rfl⟩ : syracuseStep 14253569 = 10690177) B10690177
theorem B9601375 : Blo 738327 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B8454941 : Blo 738327 8454941 := bstep (se 3 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 8454941 = 3170603) B3170603
theorem B9470803 : Blo 738327 9470803 := bstep (se 1 (by rfl) ⟨7103102, by rfl⟩ : syracuseStep 9470803 = 14206205) B14206205
theorem B1246927 : Blo 738327 1246927 := bstep (se 1 (by rfl) ⟨935195, by rfl⟩ : syracuseStep 1246927 = 1870391) B1870391
theorem B1871009 : Blo 738327 1871009 := bstep (se 2 (by rfl) ⟨701628, by rfl⟩ : syracuseStep 1871009 = 1403257) B1403257
theorem B36015515 : Blo 738327 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B2530075 : Blo 738327 2530075 := bstep (se 1 (by rfl) ⟨1897556, by rfl⟩ : syracuseStep 2530075 = 3795113) B3795113
theorem B8104673 : Blo 738327 8104673 := bstep (se 2 (by rfl) ⟨3039252, by rfl⟩ : syracuseStep 8104673 = 6078505) B6078505
theorem B8007427 : Blo 738327 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B831487 : Blo 738327 831487 := bstep (se 1 (by rfl) ⟨623615, by rfl⟩ : syracuseStep 831487 = 1247231) B1247231
theorem B3552767 : Blo 738327 3552767 := bstep (se 1 (by rfl) ⟨2664575, by rfl⟩ : syracuseStep 3552767 = 5329151) B5329151
theorem B2373545 : Blo 738327 2373545 := bstep (se 2 (by rfl) ⟨890079, by rfl⟩ : syracuseStep 2373545 = 1780159) B1780159
theorem B2374057 : Blo 738327 2374057 := bstep (se 2 (by rfl) ⟨890271, by rfl⟩ : syracuseStep 2374057 = 1780543) B1780543
theorem B13482463 : Blo 738327 13482463 := bstep (se 1 (by rfl) ⟨10111847, by rfl⟩ : syracuseStep 13482463 = 20223695) B20223695
theorem B8568821 : Blo 738327 8568821 := bstep (se 5 (by rfl) ⟨401663, by rfl⟩ : syracuseStep 8568821 = 803327) B803327
theorem B4211615 : Blo 738327 4211615 := bstep (se 1 (by rfl) ⟨3158711, by rfl⟩ : syracuseStep 4211615 = 6317423) B6317423
theorem B935327 : Blo 738327 935327 := bstep (se 1 (by rfl) ⟨701495, by rfl⟩ : syracuseStep 935327 = 1402991) B1402991
theorem B4213073 : Blo 738327 4213073 := bstep (se 2 (by rfl) ⟨1579902, by rfl⟩ : syracuseStep 4213073 = 3159805) B3159805
theorem B4508075 : Blo 738327 4508075 := bstep (se 1 (by rfl) ⟨3381056, by rfl⟩ : syracuseStep 4508075 = 6762113) B6762113
theorem B741019 : Blo 738327 741019 := bstep (se 1 (by rfl) ⟨555764, by rfl⟩ : syracuseStep 741019 = 1111529) B1111529
theorem B4510313 : Blo 738327 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B4216697 : Blo 738327 4216697 := bstep (se 2 (by rfl) ⟨1581261, by rfl⟩ : syracuseStep 4216697 = 3162523) B3162523
theorem B1107815 : Blo 738327 1107815 := bstep (se 1 (by rfl) ⟨830861, by rfl⟩ : syracuseStep 1107815 = 1661723) B1661723
theorem B4746269 : Blo 738327 4746269 := bstep (se 3 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 4746269 = 1779851) B1779851
theorem B1110185 : Blo 738327 1110185 := bstep (se 2 (by rfl) ⟨416319, by rfl⟩ : syracuseStep 1110185 = 832639) B832639
theorem B1406089 : Blo 738327 1406089 := bstep (se 2 (by rfl) ⟨527283, by rfl⟩ : syracuseStep 1406089 = 1054567) B1054567
theorem B9502379 : Blo 738327 9502379 := bstep (se 1 (by rfl) ⟨7126784, by rfl⟩ : syracuseStep 9502379 = 14253569) B14253569
theorem B5636627 : Blo 738327 5636627 := bstep (se 1 (by rfl) ⟨4227470, by rfl⟩ : syracuseStep 5636627 = 8454941) B8454941
theorem B1247339 : Blo 738327 1247339 := bstep (se 1 (by rfl) ⟨935504, by rfl⟩ : syracuseStep 1247339 = 1871009) B1871009
theorem B2494205 : Blo 738327 2494205 := bstep (se 3 (by rfl) ⟨467663, by rfl⟩ : syracuseStep 2494205 = 935327) B935327
theorem B1874785 : Blo 738327 1874785 := bstep (se 2 (by rfl) ⟨703044, by rfl⟩ : syracuseStep 1874785 = 1406089) B1406089
theorem B2368511 : Blo 738327 2368511 := bstep (se 1 (by rfl) ⟨1776383, by rfl⟩ : syracuseStep 2368511 = 3552767) B3552767
theorem B1582363 : Blo 738327 1582363 := bstep (se 1 (by rfl) ⟨1186772, by rfl⟩ : syracuseStep 1582363 = 2373545) B2373545
theorem B6334919 : Blo 738327 6334919 := bstep (se 1 (by rfl) ⟨4751189, by rfl⟩ : syracuseStep 6334919 = 9502379) B9502379
theorem B5712547 : Blo 738327 5712547 := bstep (se 1 (by rfl) ⟨4284410, by rfl⟩ : syracuseStep 5712547 = 8568821) B8568821
theorem B12627737 : Blo 738327 12627737 := bstep (se 2 (by rfl) ⟨4735401, by rfl⟩ : syracuseStep 12627737 = 9470803) B9470803
theorem B738543 : Blo 738327 738543 := bstep (se 1 (by rfl) ⟨553907, by rfl⟩ : syracuseStep 738543 = 1107815) B1107815
theorem B3164179 : Blo 738327 3164179 := bstep (se 1 (by rfl) ⟨2373134, by rfl⟩ : syracuseStep 3164179 = 4746269) B4746269
theorem B740123 : Blo 738327 740123 := bstep (se 1 (by rfl) ⟨555092, by rfl⟩ : syracuseStep 740123 = 1110185) B1110185
theorem B3165409 : Blo 738327 3165409 := bstep (se 2 (by rfl) ⟨1187028, by rfl⟩ : syracuseStep 3165409 = 2374057) B2374057
theorem B17976617 : Blo 738327 17976617 := bstep (se 2 (by rfl) ⟨6741231, by rfl⟩ : syracuseStep 17976617 = 13482463) B13482463
theorem B12801833 : Blo 738327 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B2807743 : Blo 738327 2807743 := bstep (se 1 (by rfl) ⟨2105807, by rfl⟩ : syracuseStep 2807743 = 4211615) B4211615
theorem B2808715 : Blo 738327 2808715 := bstep (se 1 (by rfl) ⟨2106536, by rfl⟩ : syracuseStep 2808715 = 4213073) B4213073
theorem B3005383 : Blo 738327 3005383 := bstep (se 1 (by rfl) ⟨2254037, by rfl⟩ : syracuseStep 3005383 = 4508075) B4508075
theorem B24010343 : Blo 738327 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B1662569 : Blo 738327 1662569 := bstep (se 2 (by rfl) ⟨623463, by rfl⟩ : syracuseStep 1662569 = 1246927) B1246927
theorem B3006875 : Blo 738327 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B2811131 : Blo 738327 2811131 := bstep (se 1 (by rfl) ⟨2108348, by rfl⟩ : syracuseStep 2811131 = 4216697) B4216697
theorem B10676569 : Blo 738327 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B1108649 : Blo 738327 1108649 := bstep (se 2 (by rfl) ⟨415743, by rfl⟩ : syracuseStep 1108649 = 831487) B831487
theorem B5403115 : Blo 738327 5403115 := bstep (se 1 (by rfl) ⟨4052336, by rfl⟩ : syracuseStep 5403115 = 8104673) B8104673
theorem B3373433 : Blo 738327 3373433 := bstep (se 2 (by rfl) ⟨1265037, by rfl⟩ : syracuseStep 3373433 = 2530075) B2530075
theorem B2004583 : Blo 738327 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B1579007 : Blo 738327 1579007 := bstep (se 1 (by rfl) ⟨1184255, by rfl⟩ : syracuseStep 1579007 = 2368511) B2368511
theorem B1874087 : Blo 738327 1874087 := bstep (se 1 (by rfl) ⟨1405565, by rfl⟩ : syracuseStep 1874087 = 2811131) B2811131
theorem B3743657 : Blo 738327 3743657 := bstep (se 2 (by rfl) ⟨1403871, by rfl⟩ : syracuseStep 3743657 = 2807743) B2807743
theorem B2499713 : Blo 738327 2499713 := bstep (se 2 (by rfl) ⟨937392, by rfl⟩ : syracuseStep 2499713 = 1874785) B1874785
theorem B3744953 : Blo 738327 3744953 := bstep (se 2 (by rfl) ⟨1404357, by rfl⟩ : syracuseStep 3744953 = 2808715) B2808715
theorem B4007177 : Blo 738327 4007177 := bstep (se 2 (by rfl) ⟨1502691, by rfl⟩ : syracuseStep 4007177 = 3005383) B3005383
theorem B831559 : Blo 738327 831559 := bstep (se 1 (by rfl) ⟨623669, by rfl⟩ : syracuseStep 831559 = 1247339) B1247339
theorem B2109817 : Blo 738327 2109817 := bstep (se 2 (by rfl) ⟨791181, by rfl⟩ : syracuseStep 2109817 = 1582363) B1582363
theorem B14235425 : Blo 738327 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B7616729 : Blo 738327 7616729 := bstep (se 2 (by rfl) ⟨2856273, by rfl⟩ : syracuseStep 7616729 = 5712547) B5712547
theorem B8534555 : Blo 738327 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B16006895 : Blo 738327 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B739099 : Blo 738327 739099 := bstep (se 1 (by rfl) ⟨554324, by rfl⟩ : syracuseStep 739099 = 1108649) B1108649
theorem B2248955 : Blo 738327 2248955 := bstep (se 1 (by rfl) ⟨1686716, by rfl⟩ : syracuseStep 2248955 = 3373433) B3373433
theorem B3757751 : Blo 738327 3757751 := bstep (se 1 (by rfl) ⟨2818313, by rfl⟩ : syracuseStep 3757751 = 5636627) B5636627
theorem B11984411 : Blo 738327 11984411 := bstep (se 1 (by rfl) ⟨8988308, by rfl⟩ : syracuseStep 11984411 = 17976617) B17976617
theorem B1662803 : Blo 738327 1662803 := bstep (se 1 (by rfl) ⟨1247102, by rfl⟩ : syracuseStep 1662803 = 2494205) B2494205
theorem B4218905 : Blo 738327 4218905 := bstep (se 2 (by rfl) ⟨1582089, by rfl⟩ : syracuseStep 4218905 = 3164179) B3164179
theorem B4220545 : Blo 738327 4220545 := bstep (se 2 (by rfl) ⟨1582704, by rfl⟩ : syracuseStep 4220545 = 3165409) B3165409
theorem B1108379 : Blo 738327 1108379 := bstep (se 1 (by rfl) ⟨831284, by rfl⟩ : syracuseStep 1108379 = 1662569) B1662569
theorem B7204153 : Blo 738327 7204153 := bstep (se 2 (by rfl) ⟨2701557, by rfl⟩ : syracuseStep 7204153 = 5403115) B5403115
theorem B4223279 : Blo 738327 4223279 := bstep (se 1 (by rfl) ⟨3167459, by rfl⟩ : syracuseStep 4223279 = 6334919) B6334919
theorem B8418491 : Blo 738327 8418491 := bstep (se 1 (by rfl) ⟨6313868, by rfl⟩ : syracuseStep 8418491 = 12627737) B12627737
theorem B1052671 : Blo 738327 1052671 := bstep (se 1 (by rfl) ⟨789503, by rfl⟩ : syracuseStep 1052671 = 1579007) B1579007
theorem B1249391 : Blo 738327 1249391 := bstep (se 1 (by rfl) ⟨937043, by rfl⟩ : syracuseStep 1249391 = 1874087) B1874087
theorem B9605537 : Blo 738327 9605537 := bstep (se 2 (by rfl) ⟨3602076, by rfl⟩ : syracuseStep 9605537 = 7204153) B7204153
theorem B2495771 : Blo 738327 2495771 := bstep (se 1 (by rfl) ⟨1871828, by rfl⟩ : syracuseStep 2495771 = 3743657) B3743657
theorem B2496635 : Blo 738327 2496635 := bstep (se 1 (by rfl) ⟨1872476, by rfl⟩ : syracuseStep 2496635 = 3744953) B3744953
theorem B5612327 : Blo 738327 5612327 := bstep (se 1 (by rfl) ⟨4209245, by rfl⟩ : syracuseStep 5612327 = 8418491) B8418491
theorem B2505167 : Blo 738327 2505167 := bstep (se 1 (by rfl) ⟨1878875, by rfl⟩ : syracuseStep 2505167 = 3757751) B3757751
theorem B2671451 : Blo 738327 2671451 := bstep (se 1 (by rfl) ⟨2003588, by rfl⟩ : syracuseStep 2671451 = 4007177) B4007177
theorem B738919 : Blo 738327 738919 := bstep (se 1 (by rfl) ⟨554189, by rfl⟩ : syracuseStep 738919 = 1108379) B1108379
theorem B2672777 : Blo 738327 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B9490283 : Blo 738327 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B5689703 : Blo 738327 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B10671263 : Blo 738327 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B5627393 : Blo 738327 5627393 := bstep (se 2 (by rfl) ⟨2110272, by rfl⟩ : syracuseStep 5627393 = 4220545) B4220545
theorem B1499303 : Blo 738327 1499303 := bstep (se 1 (by rfl) ⟨1124477, by rfl⟩ : syracuseStep 1499303 = 2248955) B2248955
theorem B7989607 : Blo 738327 7989607 := bstep (se 1 (by rfl) ⟨5992205, by rfl⟩ : syracuseStep 7989607 = 11984411) B11984411
theorem B1108535 : Blo 738327 1108535 := bstep (se 1 (by rfl) ⟨831401, by rfl⟩ : syracuseStep 1108535 = 1662803) B1662803
theorem B2812603 : Blo 738327 2812603 := bstep (se 1 (by rfl) ⟨2109452, by rfl⟩ : syracuseStep 2812603 = 4218905) B4218905
theorem B1108745 : Blo 738327 1108745 := bstep (se 2 (by rfl) ⟨415779, by rfl⟩ : syracuseStep 1108745 = 831559) B831559
theorem B2813089 : Blo 738327 2813089 := bstep (se 2 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 2813089 = 2109817) B2109817
theorem B1666475 : Blo 738327 1666475 := bstep (se 1 (by rfl) ⟨1249856, by rfl⟩ : syracuseStep 1666475 = 2499713) B2499713
theorem B2815519 : Blo 738327 2815519 := bstep (se 1 (by rfl) ⟨2111639, by rfl⟩ : syracuseStep 2815519 = 4223279) B4223279
theorem B5077819 : Blo 738327 5077819 := bstep (se 1 (by rfl) ⟨3808364, by rfl⟩ : syracuseStep 5077819 = 7616729) B7616729
theorem B15172541 : Blo 738327 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B6326855 : Blo 738327 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B10652809 : Blo 738327 10652809 := bstep (se 2 (by rfl) ⟨3994803, by rfl⟩ : syracuseStep 10652809 = 7989607) B7989607
theorem B7114175 : Blo 738327 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B3741551 : Blo 738327 3741551 := bstep (se 1 (by rfl) ⟨2806163, by rfl⟩ : syracuseStep 3741551 = 5612327) B5612327
theorem B1780967 : Blo 738327 1780967 := bstep (se 1 (by rfl) ⟨1335725, by rfl⟩ : syracuseStep 1780967 = 2671451) B2671451
theorem B1781851 : Blo 738327 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B832927 : Blo 738327 832927 := bstep (se 1 (by rfl) ⟨624695, by rfl⟩ : syracuseStep 832927 = 1249391) B1249391
theorem B6403691 : Blo 738327 6403691 := bstep (se 1 (by rfl) ⟨4802768, by rfl⟩ : syracuseStep 6403691 = 9605537) B9605537
theorem B3750137 : Blo 738327 3750137 := bstep (se 2 (by rfl) ⟨1406301, by rfl⟩ : syracuseStep 3750137 = 2812603) B2812603
theorem B3750785 : Blo 738327 3750785 := bstep (se 2 (by rfl) ⟨1406544, by rfl⟩ : syracuseStep 3750785 = 2813089) B2813089
theorem B3751595 : Blo 738327 3751595 := bstep (se 1 (by rfl) ⟨2813696, by rfl⟩ : syracuseStep 3751595 = 5627393) B5627393
theorem B999535 : Blo 738327 999535 := bstep (se 1 (by rfl) ⟨749651, by rfl⟩ : syracuseStep 999535 = 1499303) B1499303
theorem B739023 : Blo 738327 739023 := bstep (se 1 (by rfl) ⟨554267, by rfl⟩ : syracuseStep 739023 = 1108535) B1108535
theorem B739163 : Blo 738327 739163 := bstep (se 1 (by rfl) ⟨554372, by rfl⟩ : syracuseStep 739163 = 1108745) B1108745
theorem B3754025 : Blo 738327 3754025 := bstep (se 2 (by rfl) ⟨1407759, by rfl⟩ : syracuseStep 3754025 = 2815519) B2815519
theorem B6770425 : Blo 738327 6770425 := bstep (se 2 (by rfl) ⟨2538909, by rfl⟩ : syracuseStep 6770425 = 5077819) B5077819
theorem B1663847 : Blo 738327 1663847 := bstep (se 1 (by rfl) ⟨1247885, by rfl⟩ : syracuseStep 1663847 = 2495771) B2495771
theorem B1664423 : Blo 738327 1664423 := bstep (se 1 (by rfl) ⟨1248317, by rfl⟩ : syracuseStep 1664423 = 2496635) B2496635
theorem B1403561 : Blo 738327 1403561 := bstep (se 2 (by rfl) ⟨526335, by rfl⟩ : syracuseStep 1403561 = 1052671) B1052671
theorem B1110983 : Blo 738327 1110983 := bstep (se 1 (by rfl) ⟨833237, by rfl⟩ : syracuseStep 1110983 = 1666475) B1666475
theorem B1670111 : Blo 738327 1670111 := bstep (se 1 (by rfl) ⟨1252583, by rfl⟩ : syracuseStep 1670111 = 2505167) B2505167
theorem B2494367 : Blo 738327 2494367 := bstep (se 1 (by rfl) ⟨1870775, by rfl⟩ : syracuseStep 2494367 = 3741551) B3741551
theorem B1187311 : Blo 738327 1187311 := bstep (se 1 (by rfl) ⟨890483, by rfl⟩ : syracuseStep 1187311 = 1780967) B1780967
theorem B4269127 : Blo 738327 4269127 := bstep (se 1 (by rfl) ⟨3201845, by rfl⟩ : syracuseStep 4269127 = 6403691) B6403691
theorem B2500091 : Blo 738327 2500091 := bstep (se 1 (by rfl) ⟨1875068, by rfl⟩ : syracuseStep 2500091 = 3750137) B3750137
theorem B2500523 : Blo 738327 2500523 := bstep (se 1 (by rfl) ⟨1875392, by rfl⟩ : syracuseStep 2500523 = 3750785) B3750785
theorem B2501063 : Blo 738327 2501063 := bstep (se 1 (by rfl) ⟨1875797, by rfl⟩ : syracuseStep 2501063 = 3751595) B3751595
theorem B2502683 : Blo 738327 2502683 := bstep (se 1 (by rfl) ⟨1877012, by rfl⟩ : syracuseStep 2502683 = 3754025) B3754025
theorem B14203745 : Blo 738327 14203745 := bstep (se 2 (by rfl) ⟨5326404, by rfl⟩ : syracuseStep 14203745 = 10652809) B10652809
theorem B9027233 : Blo 738327 9027233 := bstep (se 2 (by rfl) ⟨3385212, by rfl⟩ : syracuseStep 9027233 = 6770425) B6770425
theorem B2375801 : Blo 738327 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B935707 : Blo 738327 935707 := bstep (se 1 (by rfl) ⟨701780, by rfl⟩ : syracuseStep 935707 = 1403561) B1403561
theorem B740655 : Blo 738327 740655 := bstep (se 1 (by rfl) ⟨555491, by rfl⟩ : syracuseStep 740655 = 1110983) B1110983
theorem B1332713 : Blo 738327 1332713 := bstep (se 2 (by rfl) ⟨499767, by rfl⟩ : syracuseStep 1332713 = 999535) B999535
theorem B10115027 : Blo 738327 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B4217903 : Blo 738327 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B4742783 : Blo 738327 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B1109231 : Blo 738327 1109231 := bstep (se 1 (by rfl) ⟨831923, by rfl⟩ : syracuseStep 1109231 = 1663847) B1663847
theorem B1109615 : Blo 738327 1109615 := bstep (se 1 (by rfl) ⟨832211, by rfl⟩ : syracuseStep 1109615 = 1664423) B1664423
theorem B1110569 : Blo 738327 1110569 := bstep (se 2 (by rfl) ⟨416463, by rfl⟩ : syracuseStep 1110569 = 832927) B832927
theorem B1113407 : Blo 738327 1113407 := bstep (se 1 (by rfl) ⟨835055, by rfl⟩ : syracuseStep 1113407 = 1670111) B1670111
theorem B1247609 : Blo 738327 1247609 := bstep (se 2 (by rfl) ⟨467853, by rfl⟩ : syracuseStep 1247609 = 935707) B935707
theorem B888475 : Blo 738327 888475 := bstep (se 1 (by rfl) ⟨666356, by rfl⟩ : syracuseStep 888475 = 1332713) B1332713
theorem B1583081 : Blo 738327 1583081 := bstep (se 2 (by rfl) ⟨593655, by rfl⟩ : syracuseStep 1583081 = 1187311) B1187311
theorem B1583867 : Blo 738327 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B3161855 : Blo 738327 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B739487 : Blo 738327 739487 := bstep (se 1 (by rfl) ⟨554615, by rfl⟩ : syracuseStep 739487 = 1109231) B1109231
theorem B739743 : Blo 738327 739743 := bstep (se 1 (by rfl) ⟨554807, by rfl⟩ : syracuseStep 739743 = 1109615) B1109615
theorem B740379 : Blo 738327 740379 := bstep (se 1 (by rfl) ⟨555284, by rfl⟩ : syracuseStep 740379 = 1110569) B1110569
theorem B742271 : Blo 738327 742271 := bstep (se 1 (by rfl) ⟨556703, by rfl⟩ : syracuseStep 742271 = 1113407) B1113407
theorem B6018155 : Blo 738327 6018155 := bstep (se 1 (by rfl) ⟨4513616, by rfl⟩ : syracuseStep 6018155 = 9027233) B9027233
theorem B5692169 : Blo 738327 5692169 := bstep (se 2 (by rfl) ⟨2134563, by rfl⟩ : syracuseStep 5692169 = 4269127) B4269127
theorem B1662911 : Blo 738327 1662911 := bstep (se 1 (by rfl) ⟨1247183, by rfl⟩ : syracuseStep 1662911 = 2494367) B2494367
theorem B6743351 : Blo 738327 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B2811935 : Blo 738327 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B1666727 : Blo 738327 1666727 := bstep (se 1 (by rfl) ⟨1250045, by rfl⟩ : syracuseStep 1666727 = 2500091) B2500091
theorem B1667015 : Blo 738327 1667015 := bstep (se 1 (by rfl) ⟨1250261, by rfl⟩ : syracuseStep 1667015 = 2500523) B2500523
theorem B1667375 : Blo 738327 1667375 := bstep (se 1 (by rfl) ⟨1250531, by rfl⟩ : syracuseStep 1667375 = 2501063) B2501063
theorem B1668455 : Blo 738327 1668455 := bstep (se 1 (by rfl) ⟨1251341, by rfl⟩ : syracuseStep 1668455 = 2502683) B2502683
theorem B9469163 : Blo 738327 9469163 := bstep (se 1 (by rfl) ⟨7101872, by rfl⟩ : syracuseStep 9469163 = 14203745) B14203745
theorem B1184633 : Blo 738327 1184633 := bstep (se 2 (by rfl) ⟨444237, by rfl⟩ : syracuseStep 1184633 = 888475) B888475
theorem B4495567 : Blo 738327 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B1055387 : Blo 738327 1055387 := bstep (se 1 (by rfl) ⟨791540, by rfl⟩ : syracuseStep 1055387 = 1583081) B1583081
theorem B1874623 : Blo 738327 1874623 := bstep (se 1 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 1874623 = 2811935) B2811935
theorem B1055911 : Blo 738327 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B8431613 : Blo 738327 8431613 := bstep (se 3 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 8431613 = 3161855) B3161855
theorem B831739 : Blo 738327 831739 := bstep (se 1 (by rfl) ⟨623804, by rfl⟩ : syracuseStep 831739 = 1247609) B1247609
theorem B4012103 : Blo 738327 4012103 := bstep (se 1 (by rfl) ⟨3009077, by rfl⟩ : syracuseStep 4012103 = 6018155) B6018155
theorem B6312775 : Blo 738327 6312775 := bstep (se 1 (by rfl) ⟨4734581, by rfl⟩ : syracuseStep 6312775 = 9469163) B9469163
theorem B3794779 : Blo 738327 3794779 := bstep (se 1 (by rfl) ⟨2846084, by rfl⟩ : syracuseStep 3794779 = 5692169) B5692169
theorem B1108607 : Blo 738327 1108607 := bstep (se 1 (by rfl) ⟨831455, by rfl⟩ : syracuseStep 1108607 = 1662911) B1662911
theorem B1111151 : Blo 738327 1111151 := bstep (se 1 (by rfl) ⟨833363, by rfl⟩ : syracuseStep 1111151 = 1666727) B1666727
theorem B1111343 : Blo 738327 1111343 := bstep (se 1 (by rfl) ⟨833507, by rfl⟩ : syracuseStep 1111343 = 1667015) B1667015
theorem B1111583 : Blo 738327 1111583 := bstep (se 1 (by rfl) ⟨833687, by rfl⟩ : syracuseStep 1111583 = 1667375) B1667375
theorem B1112303 : Blo 738327 1112303 := bstep (se 1 (by rfl) ⟨834227, by rfl⟩ : syracuseStep 1112303 = 1668455) B1668455
theorem B789755 : Blo 738327 789755 := bstep (se 1 (by rfl) ⟨592316, by rfl⟩ : syracuseStep 789755 = 1184633) B1184633
theorem B2499497 : Blo 738327 2499497 := bstep (se 2 (by rfl) ⟨937311, by rfl⟩ : syracuseStep 2499497 = 1874623) B1874623
theorem B5059705 : Blo 738327 5059705 := bstep (se 2 (by rfl) ⟨1897389, by rfl⟩ : syracuseStep 5059705 = 3794779) B3794779
theorem B10698941 : Blo 738327 10698941 := bstep (se 3 (by rfl) ⟨2006051, by rfl⟩ : syracuseStep 10698941 = 4012103) B4012103
theorem B5621075 : Blo 738327 5621075 := bstep (se 1 (by rfl) ⟨4215806, by rfl⟩ : syracuseStep 5621075 = 8431613) B8431613
theorem B739071 : Blo 738327 739071 := bstep (se 1 (by rfl) ⟨554303, by rfl⟩ : syracuseStep 739071 = 1108607) B1108607
theorem B740767 : Blo 738327 740767 := bstep (se 1 (by rfl) ⟨555575, by rfl⟩ : syracuseStep 740767 = 1111151) B1111151
theorem B740895 : Blo 738327 740895 := bstep (se 1 (by rfl) ⟨555671, by rfl⟩ : syracuseStep 740895 = 1111343) B1111343
theorem B741055 : Blo 738327 741055 := bstep (se 1 (by rfl) ⟨555791, by rfl⟩ : syracuseStep 741055 = 1111583) B1111583
theorem B741535 : Blo 738327 741535 := bstep (se 1 (by rfl) ⟨556151, by rfl⟩ : syracuseStep 741535 = 1112303) B1112303
theorem B1108985 : Blo 738327 1108985 := bstep (se 2 (by rfl) ⟨415869, by rfl⟩ : syracuseStep 1108985 = 831739) B831739
theorem B8417033 : Blo 738327 8417033 := bstep (se 2 (by rfl) ⟨3156387, by rfl⟩ : syracuseStep 8417033 = 6312775) B6312775
theorem B2814365 : Blo 738327 2814365 := bstep (se 3 (by rfl) ⟨527693, by rfl⟩ : syracuseStep 2814365 = 1055387) B1055387
theorem B5994089 : Blo 738327 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B1407881 : Blo 738327 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B5611355 : Blo 738327 5611355 := bstep (se 1 (by rfl) ⟨4208516, by rfl⟩ : syracuseStep 5611355 = 8417033) B8417033
theorem B1876243 : Blo 738327 1876243 := bstep (se 1 (by rfl) ⟨1407182, by rfl⟩ : syracuseStep 1876243 = 2814365) B2814365
theorem B2106013 : Blo 738327 2106013 := bstep (se 3 (by rfl) ⟨394877, by rfl⟩ : syracuseStep 2106013 = 789755) B789755
theorem B3747383 : Blo 738327 3747383 := bstep (se 1 (by rfl) ⟨2810537, by rfl⟩ : syracuseStep 3747383 = 5621075) B5621075
theorem B739323 : Blo 738327 739323 := bstep (se 1 (by rfl) ⟨554492, by rfl⟩ : syracuseStep 739323 = 1108985) B1108985
theorem B3754349 : Blo 738327 3754349 := bstep (se 3 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 3754349 = 1407881) B1407881
theorem B7132627 : Blo 738327 7132627 := bstep (se 1 (by rfl) ⟨5349470, by rfl⟩ : syracuseStep 7132627 = 10698941) B10698941
theorem B1666331 : Blo 738327 1666331 := bstep (se 1 (by rfl) ⟨1249748, by rfl⟩ : syracuseStep 1666331 = 2499497) B2499497
theorem B6746273 : Blo 738327 6746273 := bstep (se 2 (by rfl) ⟨2529852, by rfl⟩ : syracuseStep 6746273 = 5059705) B5059705
theorem B3996059 : Blo 738327 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B3740903 : Blo 738327 3740903 := bstep (se 1 (by rfl) ⟨2805677, by rfl⟩ : syracuseStep 3740903 = 5611355) B5611355
theorem B10656157 : Blo 738327 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B9510169 : Blo 738327 9510169 := bstep (se 2 (by rfl) ⟨3566313, by rfl⟩ : syracuseStep 9510169 = 7132627) B7132627
theorem B2498255 : Blo 738327 2498255 := bstep (se 1 (by rfl) ⟨1873691, by rfl⟩ : syracuseStep 2498255 = 3747383) B3747383
theorem B4497515 : Blo 738327 4497515 := bstep (se 1 (by rfl) ⟨3373136, by rfl⟩ : syracuseStep 4497515 = 6746273) B6746273
theorem B2501657 : Blo 738327 2501657 := bstep (se 2 (by rfl) ⟨938121, by rfl⟩ : syracuseStep 2501657 = 1876243) B1876243
theorem B2502899 : Blo 738327 2502899 := bstep (se 1 (by rfl) ⟨1877174, by rfl⟩ : syracuseStep 2502899 = 3754349) B3754349
theorem B2808017 : Blo 738327 2808017 := bstep (se 2 (by rfl) ⟨1053006, by rfl⟩ : syracuseStep 2808017 = 2106013) B2106013
theorem B1110887 : Blo 738327 1110887 := bstep (se 1 (by rfl) ⟨833165, by rfl⟩ : syracuseStep 1110887 = 1666331) B1666331
theorem B2493935 : Blo 738327 2493935 := bstep (se 1 (by rfl) ⟨1870451, by rfl⟩ : syracuseStep 2493935 = 3740903) B3740903
theorem B1872011 : Blo 738327 1872011 := bstep (se 1 (by rfl) ⟨1404008, by rfl⟩ : syracuseStep 1872011 = 2808017) B2808017
theorem B2998343 : Blo 738327 2998343 := bstep (se 1 (by rfl) ⟨2248757, by rfl⟩ : syracuseStep 2998343 = 4497515) B4497515
theorem B14208209 : Blo 738327 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B740591 : Blo 738327 740591 := bstep (se 1 (by rfl) ⟨555443, by rfl⟩ : syracuseStep 740591 = 1110887) B1110887
theorem B1665503 : Blo 738327 1665503 := bstep (se 1 (by rfl) ⟨1249127, by rfl⟩ : syracuseStep 1665503 = 2498255) B2498255
theorem B1667771 : Blo 738327 1667771 := bstep (se 1 (by rfl) ⟨1250828, by rfl⟩ : syracuseStep 1667771 = 2501657) B2501657
theorem B1668599 : Blo 738327 1668599 := bstep (se 1 (by rfl) ⟨1251449, by rfl⟩ : syracuseStep 1668599 = 2502899) B2502899
theorem B12680225 : Blo 738327 12680225 := bstep (se 2 (by rfl) ⟨4755084, by rfl⟩ : syracuseStep 12680225 = 9510169) B9510169
theorem B7995581 : Blo 738327 7995581 := bstep (se 3 (by rfl) ⟨1499171, by rfl⟩ : syracuseStep 7995581 = 2998343) B2998343
theorem B9472139 : Blo 738327 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B1248007 : Blo 738327 1248007 := bstep (se 1 (by rfl) ⟨936005, by rfl⟩ : syracuseStep 1248007 = 1872011) B1872011
theorem B1662623 : Blo 738327 1662623 := bstep (se 1 (by rfl) ⟨1246967, by rfl⟩ : syracuseStep 1662623 = 2493935) B2493935
theorem B1110335 : Blo 738327 1110335 := bstep (se 1 (by rfl) ⟨832751, by rfl⟩ : syracuseStep 1110335 = 1665503) B1665503
theorem B1111847 : Blo 738327 1111847 := bstep (se 1 (by rfl) ⟨833885, by rfl⟩ : syracuseStep 1111847 = 1667771) B1667771
theorem B1112399 : Blo 738327 1112399 := bstep (se 1 (by rfl) ⟨834299, by rfl⟩ : syracuseStep 1112399 = 1668599) B1668599
theorem B8453483 : Blo 738327 8453483 := bstep (se 1 (by rfl) ⟨6340112, by rfl⟩ : syracuseStep 8453483 = 12680225) B12680225
theorem B740223 : Blo 738327 740223 := bstep (se 1 (by rfl) ⟨555167, by rfl⟩ : syracuseStep 740223 = 1110335) B1110335
theorem B741231 : Blo 738327 741231 := bstep (se 1 (by rfl) ⟨555923, by rfl⟩ : syracuseStep 741231 = 1111847) B1111847
theorem B741599 : Blo 738327 741599 := bstep (se 1 (by rfl) ⟨556199, by rfl⟩ : syracuseStep 741599 = 1112399) B1112399
theorem B5330387 : Blo 738327 5330387 := bstep (se 1 (by rfl) ⟨3997790, by rfl⟩ : syracuseStep 5330387 = 7995581) B7995581
theorem B6314759 : Blo 738327 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B1664009 : Blo 738327 1664009 := bstep (se 2 (by rfl) ⟨624003, by rfl⟩ : syracuseStep 1664009 = 1248007) B1248007
theorem B1108415 : Blo 738327 1108415 := bstep (se 1 (by rfl) ⟨831311, by rfl⟩ : syracuseStep 1108415 = 1662623) B1662623
theorem B5635655 : Blo 738327 5635655 := bstep (se 1 (by rfl) ⟨4226741, by rfl⟩ : syracuseStep 5635655 = 8453483) B8453483
theorem B3553591 : Blo 738327 3553591 := bstep (se 1 (by rfl) ⟨2665193, by rfl⟩ : syracuseStep 3553591 = 5330387) B5330387
theorem B4209839 : Blo 738327 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B738943 : Blo 738327 738943 := bstep (se 1 (by rfl) ⟨554207, by rfl⟩ : syracuseStep 738943 = 1108415) B1108415
theorem B3757103 : Blo 738327 3757103 := bstep (se 1 (by rfl) ⟨2817827, by rfl⟩ : syracuseStep 3757103 = 5635655) B5635655
theorem B1109339 : Blo 738327 1109339 := bstep (se 1 (by rfl) ⟨832004, by rfl⟩ : syracuseStep 1109339 = 1664009) B1664009
theorem B2504735 : Blo 738327 2504735 := bstep (se 1 (by rfl) ⟨1878551, by rfl⟩ : syracuseStep 2504735 = 3757103) B3757103
theorem B739559 : Blo 738327 739559 := bstep (se 1 (by rfl) ⟨554669, by rfl⟩ : syracuseStep 739559 = 1109339) B1109339
theorem B4738121 : Blo 738327 4738121 := bstep (se 2 (by rfl) ⟨1776795, by rfl⟩ : syracuseStep 4738121 = 3553591) B3553591
theorem B2806559 : Blo 738327 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B1871039 : Blo 738327 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B3158747 : Blo 738327 3158747 := bstep (se 1 (by rfl) ⟨2369060, by rfl⟩ : syracuseStep 3158747 = 4738121) B4738121
theorem B1669823 : Blo 738327 1669823 := bstep (se 1 (by rfl) ⟨1252367, by rfl⟩ : syracuseStep 1669823 = 2504735) B2504735
theorem B1247359 : Blo 738327 1247359 := bstep (se 1 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 1247359 = 1871039) B1871039
theorem B2105831 : Blo 738327 2105831 := bstep (se 1 (by rfl) ⟨1579373, by rfl⟩ : syracuseStep 2105831 = 3158747) B3158747
theorem B1113215 : Blo 738327 1113215 := bstep (se 1 (by rfl) ⟨834911, by rfl⟩ : syracuseStep 1113215 = 1669823) B1669823
theorem B742143 : Blo 738327 742143 := bstep (se 1 (by rfl) ⟨556607, by rfl⟩ : syracuseStep 742143 = 1113215) B1113215
theorem B1663145 : Blo 738327 1663145 := bstep (se 2 (by rfl) ⟨623679, by rfl⟩ : syracuseStep 1663145 = 1247359) B1247359
theorem B1403887 : Blo 738327 1403887 := bstep (se 1 (by rfl) ⟨1052915, by rfl⟩ : syracuseStep 1403887 = 2105831) B2105831
theorem B1871849 : Blo 738327 1871849 := bstep (se 2 (by rfl) ⟨701943, by rfl⟩ : syracuseStep 1871849 = 1403887) B1403887
theorem B1108763 : Blo 738327 1108763 := bstep (se 1 (by rfl) ⟨831572, by rfl⟩ : syracuseStep 1108763 = 1663145) B1663145
theorem B1247899 : Blo 738327 1247899 := bstep (se 1 (by rfl) ⟨935924, by rfl⟩ : syracuseStep 1247899 = 1871849) B1871849
theorem B739175 : Blo 738327 739175 := bstep (se 1 (by rfl) ⟨554381, by rfl⟩ : syracuseStep 739175 = 1108763) B1108763
theorem B1663865 : Blo 738327 1663865 := bstep (se 2 (by rfl) ⟨623949, by rfl⟩ : syracuseStep 1663865 = 1247899) B1247899
theorem B1109243 : Blo 738327 1109243 := bstep (se 1 (by rfl) ⟨831932, by rfl⟩ : syracuseStep 1109243 = 1663865) B1663865
theorem B739495 : Blo 738327 739495 := bstep (se 1 (by rfl) ⟨554621, by rfl⟩ : syracuseStep 739495 = 1109243) B1109243

theorem C0 (j : ℕ) (h1 : 184581 ≤ j) (h2 : j ≤ 185280) : Blo 738327 (4 * j + 3) := by
  interval_cases j
  · exact B738327
  · exact B738331
  · exact B738335
  · exact B738339
  · exact B738343
  · exact B738347
  · exact B738351
  · exact B738355
  · exact B738359
  · exact B738363
  · exact B738367
  · exact B738371
  · exact B738375
  · exact B738379
  · exact B738383
  · exact B738387
  · exact B738391
  · exact B738395
  · exact B738399
  · exact B738403
  · exact B738407
  · exact B738411
  · exact B738415
  · exact B738419
  · exact B738423
  · exact B738427
  · exact B738431
  · exact B738435
  · exact B738439
  · exact B738443
  · exact B738447
  · exact B738451
  · exact B738455
  · exact B738459
  · exact B738463
  · exact B738467
  · exact B738471
  · exact B738475
  · exact B738479
  · exact B738483
  · exact B738487
  · exact B738491
  · exact B738495
  · exact B738499
  · exact B738503
  · exact B738507
  · exact B738511
  · exact B738515
  · exact B738519
  · exact B738523
  · exact B738527
  · exact B738531
  · exact B738535
  · exact B738539
  · exact B738543
  · exact B738547
  · exact B738551
  · exact B738555
  · exact B738559
  · exact B738563
  · exact B738567
  · exact B738571
  · exact B738575
  · exact B738579
  · exact B738583
  · exact B738587
  · exact B738591
  · exact B738595
  · exact B738599
  · exact B738603
  · exact B738607
  · exact B738611
  · exact B738615
  · exact B738619
  · exact B738623
  · exact B738627
  · exact B738631
  · exact B738635
  · exact B738639
  · exact B738643
  · exact B738647
  · exact B738651
  · exact B738655
  · exact B738659
  · exact B738663
  · exact B738667
  · exact B738671
  · exact B738675
  · exact B738679
  · exact B738683
  · exact B738687
  · exact B738691
  · exact B738695
  · exact B738699
  · exact B738703
  · exact B738707
  · exact B738711
  · exact B738715
  · exact B738719
  · exact B738723
  · exact B738727
  · exact B738731
  · exact B738735
  · exact B738739
  · exact B738743
  · exact B738747
  · exact B738751
  · exact B738755
  · exact B738759
  · exact B738763
  · exact B738767
  · exact B738771
  · exact B738775
  · exact B738779
  · exact B738783
  · exact B738787
  · exact B738791
  · exact B738795
  · exact B738799
  · exact B738803
  · exact B738807
  · exact B738811
  · exact B738815
  · exact B738819
  · exact B738823
  · exact B738827
  · exact B738831
  · exact B738835
  · exact B738839
  · exact B738843
  · exact B738847
  · exact B738851
  · exact B738855
  · exact B738859
  · exact B738863
  · exact B738867
  · exact B738871
  · exact B738875
  · exact B738879
  · exact B738883
  · exact B738887
  · exact B738891
  · exact B738895
  · exact B738899
  · exact B738903
  · exact B738907
  · exact B738911
  · exact B738915
  · exact B738919
  · exact B738923
  · exact B738927
  · exact B738931
  · exact B738935
  · exact B738939
  · exact B738943
  · exact B738947
  · exact B738951
  · exact B738955
  · exact B738959
  · exact B738963
  · exact B738967
  · exact B738971
  · exact B738975
  · exact B738979
  · exact B738983
  · exact B738987
  · exact B738991
  · exact B738995
  · exact B738999
  · exact B739003
  · exact B739007
  · exact B739011
  · exact B739015
  · exact B739019
  · exact B739023
  · exact B739027
  · exact B739031
  · exact B739035
  · exact B739039
  · exact B739043
  · exact B739047
  · exact B739051
  · exact B739055
  · exact B739059
  · exact B739063
  · exact B739067
  · exact B739071
  · exact B739075
  · exact B739079
  · exact B739083
  · exact B739087
  · exact B739091
  · exact B739095
  · exact B739099
  · exact B739103
  · exact B739107
  · exact B739111
  · exact B739115
  · exact B739119
  · exact B739123
  · exact B739127
  · exact B739131
  · exact B739135
  · exact B739139
  · exact B739143
  · exact B739147
  · exact B739151
  · exact B739155
  · exact B739159
  · exact B739163
  · exact B739167
  · exact B739171
  · exact B739175
  · exact B739179
  · exact B739183
  · exact B739187
  · exact B739191
  · exact B739195
  · exact B739199
  · exact B739203
  · exact B739207
  · exact B739211
  · exact B739215
  · exact B739219
  · exact B739223
  · exact B739227
  · exact B739231
  · exact B739235
  · exact B739239
  · exact B739243
  · exact B739247
  · exact B739251
  · exact B739255
  · exact B739259
  · exact B739263
  · exact B739267
  · exact B739271
  · exact B739275
  · exact B739279
  · exact B739283
  · exact B739287
  · exact B739291
  · exact B739295
  · exact B739299
  · exact B739303
  · exact B739307
  · exact B739311
  · exact B739315
  · exact B739319
  · exact B739323
  · exact B739327
  · exact B739331
  · exact B739335
  · exact B739339
  · exact B739343
  · exact B739347
  · exact B739351
  · exact B739355
  · exact B739359
  · exact B739363
  · exact B739367
  · exact B739371
  · exact B739375
  · exact B739379
  · exact B739383
  · exact B739387
  · exact B739391
  · exact B739395
  · exact B739399
  · exact B739403
  · exact B739407
  · exact B739411
  · exact B739415
  · exact B739419
  · exact B739423
  · exact B739427
  · exact B739431
  · exact B739435
  · exact B739439
  · exact B739443
  · exact B739447
  · exact B739451
  · exact B739455
  · exact B739459
  · exact B739463
  · exact B739467
  · exact B739471
  · exact B739475
  · exact B739479
  · exact B739483
  · exact B739487
  · exact B739491
  · exact B739495
  · exact B739499
  · exact B739503
  · exact B739507
  · exact B739511
  · exact B739515
  · exact B739519
  · exact B739523
  · exact B739527
  · exact B739531
  · exact B739535
  · exact B739539
  · exact B739543
  · exact B739547
  · exact B739551
  · exact B739555
  · exact B739559
  · exact B739563
  · exact B739567
  · exact B739571
  · exact B739575
  · exact B739579
  · exact B739583
  · exact B739587
  · exact B739591
  · exact B739595
  · exact B739599
  · exact B739603
  · exact B739607
  · exact B739611
  · exact B739615
  · exact B739619
  · exact B739623
  · exact B739627
  · exact B739631
  · exact B739635
  · exact B739639
  · exact B739643
  · exact B739647
  · exact B739651
  · exact B739655
  · exact B739659
  · exact B739663
  · exact B739667
  · exact B739671
  · exact B739675
  · exact B739679
  · exact B739683
  · exact B739687
  · exact B739691
  · exact B739695
  · exact B739699
  · exact B739703
  · exact B739707
  · exact B739711
  · exact B739715
  · exact B739719
  · exact B739723
  · exact B739727
  · exact B739731
  · exact B739735
  · exact B739739
  · exact B739743
  · exact B739747
  · exact B739751
  · exact B739755
  · exact B739759
  · exact B739763
  · exact B739767
  · exact B739771
  · exact B739775
  · exact B739779
  · exact B739783
  · exact B739787
  · exact B739791
  · exact B739795
  · exact B739799
  · exact B739803
  · exact B739807
  · exact B739811
  · exact B739815
  · exact B739819
  · exact B739823
  · exact B739827
  · exact B739831
  · exact B739835
  · exact B739839
  · exact B739843
  · exact B739847
  · exact B739851
  · exact B739855
  · exact B739859
  · exact B739863
  · exact B739867
  · exact B739871
  · exact B739875
  · exact B739879
  · exact B739883
  · exact B739887
  · exact B739891
  · exact B739895
  · exact B739899
  · exact B739903
  · exact B739907
  · exact B739911
  · exact B739915
  · exact B739919
  · exact B739923
  · exact B739927
  · exact B739931
  · exact B739935
  · exact B739939
  · exact B739943
  · exact B739947
  · exact B739951
  · exact B739955
  · exact B739959
  · exact B739963
  · exact B739967
  · exact B739971
  · exact B739975
  · exact B739979
  · exact B739983
  · exact B739987
  · exact B739991
  · exact B739995
  · exact B739999
  · exact B740003
  · exact B740007
  · exact B740011
  · exact B740015
  · exact B740019
  · exact B740023
  · exact B740027
  · exact B740031
  · exact B740035
  · exact B740039
  · exact B740043
  · exact B740047
  · exact B740051
  · exact B740055
  · exact B740059
  · exact B740063
  · exact B740067
  · exact B740071
  · exact B740075
  · exact B740079
  · exact B740083
  · exact B740087
  · exact B740091
  · exact B740095
  · exact B740099
  · exact B740103
  · exact B740107
  · exact B740111
  · exact B740115
  · exact B740119
  · exact B740123
  · exact B740127
  · exact B740131
  · exact B740135
  · exact B740139
  · exact B740143
  · exact B740147
  · exact B740151
  · exact B740155
  · exact B740159
  · exact B740163
  · exact B740167
  · exact B740171
  · exact B740175
  · exact B740179
  · exact B740183
  · exact B740187
  · exact B740191
  · exact B740195
  · exact B740199
  · exact B740203
  · exact B740207
  · exact B740211
  · exact B740215
  · exact B740219
  · exact B740223
  · exact B740227
  · exact B740231
  · exact B740235
  · exact B740239
  · exact B740243
  · exact B740247
  · exact B740251
  · exact B740255
  · exact B740259
  · exact B740263
  · exact B740267
  · exact B740271
  · exact B740275
  · exact B740279
  · exact B740283
  · exact B740287
  · exact B740291
  · exact B740295
  · exact B740299
  · exact B740303
  · exact B740307
  · exact B740311
  · exact B740315
  · exact B740319
  · exact B740323
  · exact B740327
  · exact B740331
  · exact B740335
  · exact B740339
  · exact B740343
  · exact B740347
  · exact B740351
  · exact B740355
  · exact B740359
  · exact B740363
  · exact B740367
  · exact B740371
  · exact B740375
  · exact B740379
  · exact B740383
  · exact B740387
  · exact B740391
  · exact B740395
  · exact B740399
  · exact B740403
  · exact B740407
  · exact B740411
  · exact B740415
  · exact B740419
  · exact B740423
  · exact B740427
  · exact B740431
  · exact B740435
  · exact B740439
  · exact B740443
  · exact B740447
  · exact B740451
  · exact B740455
  · exact B740459
  · exact B740463
  · exact B740467
  · exact B740471
  · exact B740475
  · exact B740479
  · exact B740483
  · exact B740487
  · exact B740491
  · exact B740495
  · exact B740499
  · exact B740503
  · exact B740507
  · exact B740511
  · exact B740515
  · exact B740519
  · exact B740523
  · exact B740527
  · exact B740531
  · exact B740535
  · exact B740539
  · exact B740543
  · exact B740547
  · exact B740551
  · exact B740555
  · exact B740559
  · exact B740563
  · exact B740567
  · exact B740571
  · exact B740575
  · exact B740579
  · exact B740583
  · exact B740587
  · exact B740591
  · exact B740595
  · exact B740599
  · exact B740603
  · exact B740607
  · exact B740611
  · exact B740615
  · exact B740619
  · exact B740623
  · exact B740627
  · exact B740631
  · exact B740635
  · exact B740639
  · exact B740643
  · exact B740647
  · exact B740651
  · exact B740655
  · exact B740659
  · exact B740663
  · exact B740667
  · exact B740671
  · exact B740675
  · exact B740679
  · exact B740683
  · exact B740687
  · exact B740691
  · exact B740695
  · exact B740699
  · exact B740703
  · exact B740707
  · exact B740711
  · exact B740715
  · exact B740719
  · exact B740723
  · exact B740727
  · exact B740731
  · exact B740735
  · exact B740739
  · exact B740743
  · exact B740747
  · exact B740751
  · exact B740755
  · exact B740759
  · exact B740763
  · exact B740767
  · exact B740771
  · exact B740775
  · exact B740779
  · exact B740783
  · exact B740787
  · exact B740791
  · exact B740795
  · exact B740799
  · exact B740803
  · exact B740807
  · exact B740811
  · exact B740815
  · exact B740819
  · exact B740823
  · exact B740827
  · exact B740831
  · exact B740835
  · exact B740839
  · exact B740843
  · exact B740847
  · exact B740851
  · exact B740855
  · exact B740859
  · exact B740863
  · exact B740867
  · exact B740871
  · exact B740875
  · exact B740879
  · exact B740883
  · exact B740887
  · exact B740891
  · exact B740895
  · exact B740899
  · exact B740903
  · exact B740907
  · exact B740911
  · exact B740915
  · exact B740919
  · exact B740923
  · exact B740927
  · exact B740931
  · exact B740935
  · exact B740939
  · exact B740943
  · exact B740947
  · exact B740951
  · exact B740955
  · exact B740959
  · exact B740963
  · exact B740967
  · exact B740971
  · exact B740975
  · exact B740979
  · exact B740983
  · exact B740987
  · exact B740991
  · exact B740995
  · exact B740999
  · exact B741003
  · exact B741007
  · exact B741011
  · exact B741015
  · exact B741019
  · exact B741023
  · exact B741027
  · exact B741031
  · exact B741035
  · exact B741039
  · exact B741043
  · exact B741047
  · exact B741051
  · exact B741055
  · exact B741059
  · exact B741063
  · exact B741067
  · exact B741071
  · exact B741075
  · exact B741079
  · exact B741083
  · exact B741087
  · exact B741091
  · exact B741095
  · exact B741099
  · exact B741103
  · exact B741107
  · exact B741111
  · exact B741115
  · exact B741119
  · exact B741123

theorem C1 (j : ℕ) (h1 : 185281 ≤ j) (h2 : j ≤ 185581) : Blo 738327 (4 * j + 3) := by
  interval_cases j
  · exact B741127
  · exact B741131
  · exact B741135
  · exact B741139
  · exact B741143
  · exact B741147
  · exact B741151
  · exact B741155
  · exact B741159
  · exact B741163
  · exact B741167
  · exact B741171
  · exact B741175
  · exact B741179
  · exact B741183
  · exact B741187
  · exact B741191
  · exact B741195
  · exact B741199
  · exact B741203
  · exact B741207
  · exact B741211
  · exact B741215
  · exact B741219
  · exact B741223
  · exact B741227
  · exact B741231
  · exact B741235
  · exact B741239
  · exact B741243
  · exact B741247
  · exact B741251
  · exact B741255
  · exact B741259
  · exact B741263
  · exact B741267
  · exact B741271
  · exact B741275
  · exact B741279
  · exact B741283
  · exact B741287
  · exact B741291
  · exact B741295
  · exact B741299
  · exact B741303
  · exact B741307
  · exact B741311
  · exact B741315
  · exact B741319
  · exact B741323
  · exact B741327
  · exact B741331
  · exact B741335
  · exact B741339
  · exact B741343
  · exact B741347
  · exact B741351
  · exact B741355
  · exact B741359
  · exact B741363
  · exact B741367
  · exact B741371
  · exact B741375
  · exact B741379
  · exact B741383
  · exact B741387
  · exact B741391
  · exact B741395
  · exact B741399
  · exact B741403
  · exact B741407
  · exact B741411
  · exact B741415
  · exact B741419
  · exact B741423
  · exact B741427
  · exact B741431
  · exact B741435
  · exact B741439
  · exact B741443
  · exact B741447
  · exact B741451
  · exact B741455
  · exact B741459
  · exact B741463
  · exact B741467
  · exact B741471
  · exact B741475
  · exact B741479
  · exact B741483
  · exact B741487
  · exact B741491
  · exact B741495
  · exact B741499
  · exact B741503
  · exact B741507
  · exact B741511
  · exact B741515
  · exact B741519
  · exact B741523
  · exact B741527
  · exact B741531
  · exact B741535
  · exact B741539
  · exact B741543
  · exact B741547
  · exact B741551
  · exact B741555
  · exact B741559
  · exact B741563
  · exact B741567
  · exact B741571
  · exact B741575
  · exact B741579
  · exact B741583
  · exact B741587
  · exact B741591
  · exact B741595
  · exact B741599
  · exact B741603
  · exact B741607
  · exact B741611
  · exact B741615
  · exact B741619
  · exact B741623
  · exact B741627
  · exact B741631
  · exact B741635
  · exact B741639
  · exact B741643
  · exact B741647
  · exact B741651
  · exact B741655
  · exact B741659
  · exact B741663
  · exact B741667
  · exact B741671
  · exact B741675
  · exact B741679
  · exact B741683
  · exact B741687
  · exact B741691
  · exact B741695
  · exact B741699
  · exact B741703
  · exact B741707
  · exact B741711
  · exact B741715
  · exact B741719
  · exact B741723
  · exact B741727
  · exact B741731
  · exact B741735
  · exact B741739
  · exact B741743
  · exact B741747
  · exact B741751
  · exact B741755
  · exact B741759
  · exact B741763
  · exact B741767
  · exact B741771
  · exact B741775
  · exact B741779
  · exact B741783
  · exact B741787
  · exact B741791
  · exact B741795
  · exact B741799
  · exact B741803
  · exact B741807
  · exact B741811
  · exact B741815
  · exact B741819
  · exact B741823
  · exact B741827
  · exact B741831
  · exact B741835
  · exact B741839
  · exact B741843
  · exact B741847
  · exact B741851
  · exact B741855
  · exact B741859
  · exact B741863
  · exact B741867
  · exact B741871
  · exact B741875
  · exact B741879
  · exact B741883
  · exact B741887
  · exact B741891
  · exact B741895
  · exact B741899
  · exact B741903
  · exact B741907
  · exact B741911
  · exact B741915
  · exact B741919
  · exact B741923
  · exact B741927
  · exact B741931
  · exact B741935
  · exact B741939
  · exact B741943
  · exact B741947
  · exact B741951
  · exact B741955
  · exact B741959
  · exact B741963
  · exact B741967
  · exact B741971
  · exact B741975
  · exact B741979
  · exact B741983
  · exact B741987
  · exact B741991
  · exact B741995
  · exact B741999
  · exact B742003
  · exact B742007
  · exact B742011
  · exact B742015
  · exact B742019
  · exact B742023
  · exact B742027
  · exact B742031
  · exact B742035
  · exact B742039
  · exact B742043
  · exact B742047
  · exact B742051
  · exact B742055
  · exact B742059
  · exact B742063
  · exact B742067
  · exact B742071
  · exact B742075
  · exact B742079
  · exact B742083
  · exact B742087
  · exact B742091
  · exact B742095
  · exact B742099
  · exact B742103
  · exact B742107
  · exact B742111
  · exact B742115
  · exact B742119
  · exact B742123
  · exact B742127
  · exact B742131
  · exact B742135
  · exact B742139
  · exact B742143
  · exact B742147
  · exact B742151
  · exact B742155
  · exact B742159
  · exact B742163
  · exact B742167
  · exact B742171
  · exact B742175
  · exact B742179
  · exact B742183
  · exact B742187
  · exact B742191
  · exact B742195
  · exact B742199
  · exact B742203
  · exact B742207
  · exact B742211
  · exact B742215
  · exact B742219
  · exact B742223
  · exact B742227
  · exact B742231
  · exact B742235
  · exact B742239
  · exact B742243
  · exact B742247
  · exact B742251
  · exact B742255
  · exact B742259
  · exact B742263
  · exact B742267
  · exact B742271
  · exact B742275
  · exact B742279
  · exact B742283
  · exact B742287
  · exact B742291
  · exact B742295
  · exact B742299
  · exact B742303
  · exact B742307
  · exact B742311
  · exact B742315
  · exact B742319
  · exact B742323
  · exact B742327

theorem solution (m : ℕ) (hlo : 738327 ≤ m) (hhi : m ≤ 742327) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 184581 ≤ j := by omega
    have hj2 : j ≤ 185581 := by omega
    have hb : Blo 738327 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 185281 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
