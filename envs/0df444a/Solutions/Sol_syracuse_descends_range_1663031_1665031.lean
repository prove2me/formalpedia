-- Prove2me | solution 1 for syracuse_descends_range_1663031_1665031
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:19:34.354344+00:00
-- url     : https://prove2.me/submissions/f804b7aa-a559-4441-b54f-9623d143a223

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


theorem B3743765 : Blo 1663031 3743765 := bbase (se 6 (by rfl) ⟨87744, by rfl⟩ : syracuseStep 3743765 = 175489) (by norm_num)
theorem B1998901 : Blo 1663031 1998901 := bbase (se 5 (by rfl) ⟨93698, by rfl⟩ : syracuseStep 1998901 = 187397) (by norm_num)
theorem B3743837 : Blo 1663031 3743837 := bbase (se 3 (by rfl) ⟨701969, by rfl⟩ : syracuseStep 3743837 = 1403939) (by norm_num)
theorem B7110757 : Blo 1663031 7110757 := bbase (se 4 (by rfl) ⟨666633, by rfl⟩ : syracuseStep 7110757 = 1333267) (by norm_num)
theorem B2105453 : Blo 1663031 2105453 := bbase (se 3 (by rfl) ⟨394772, by rfl⟩ : syracuseStep 2105453 = 789545) (by norm_num)
theorem B4210805 : Blo 1663031 4210805 := bbase (se 5 (by rfl) ⟨197381, by rfl⟩ : syracuseStep 4210805 = 394763) (by norm_num)
theorem B12640373 : Blo 1663031 12640373 := bbase (se 5 (by rfl) ⟨592517, by rfl⟩ : syracuseStep 12640373 = 1185035) (by norm_num)
theorem B2105509 : Blo 1663031 2105509 := bbase (se 4 (by rfl) ⟨197391, by rfl⟩ : syracuseStep 2105509 = 394783) (by norm_num)
theorem B3743909 : Blo 1663031 3743909 := bbase (se 4 (by rfl) ⟨350991, by rfl⟩ : syracuseStep 3743909 = 701983) (by norm_num)
theorem B7594181 : Blo 1663031 7594181 := bbase (se 4 (by rfl) ⟨711954, by rfl⟩ : syracuseStep 7594181 = 1423909) (by norm_num)
theorem B3743981 : Blo 1663031 3743981 := bbase (se 3 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 3743981 = 1403993) (by norm_num)
theorem B2105605 : Blo 1663031 2105605 := bbase (se 4 (by rfl) ⟨197400, by rfl⟩ : syracuseStep 2105605 = 394801) (by norm_num)
theorem B3744053 : Blo 1663031 3744053 := bbase (se 5 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 3744053 = 351005) (by norm_num)
theorem B1777997 : Blo 1663031 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B3744125 : Blo 1663031 3744125 := bbase (se 3 (by rfl) ⟨702023, by rfl⟩ : syracuseStep 3744125 = 1404047) (by norm_num)
theorem B2105777 : Blo 1663031 2105777 := bbase (se 2 (by rfl) ⟨789666, by rfl⟩ : syracuseStep 2105777 = 1579333) (by norm_num)
theorem B3744197 : Blo 1663031 3744197 := bbase (se 4 (by rfl) ⟨351018, by rfl⟩ : syracuseStep 3744197 = 702037) (by norm_num)
theorem B4211149 : Blo 1663031 4211149 := bbase (se 3 (by rfl) ⟨789590, by rfl⟩ : syracuseStep 4211149 = 1579181) (by norm_num)
theorem B8102357 : Blo 1663031 8102357 := bbase (se 7 (by rfl) ⟨94949, by rfl⟩ : syracuseStep 8102357 = 189899) (by norm_num)
theorem B2105833 : Blo 1663031 2105833 := bbase (se 2 (by rfl) ⟨789687, by rfl⟩ : syracuseStep 2105833 = 1579375) (by norm_num)
theorem B8421893 : Blo 1663031 8421893 := bbase (se 4 (by rfl) ⟨789552, by rfl⟩ : syracuseStep 8421893 = 1579105) (by norm_num)
theorem B3744269 : Blo 1663031 3744269 := bbase (se 3 (by rfl) ⟨702050, by rfl⟩ : syracuseStep 3744269 = 1404101) (by norm_num)
theorem B12632597 : Blo 1663031 12632597 := bbase (se 6 (by rfl) ⟨296076, by rfl⟩ : syracuseStep 12632597 = 592153) (by norm_num)
theorem B2998813 : Blo 1663031 2998813 := bbase (se 3 (by rfl) ⟨562277, by rfl⟩ : syracuseStep 2998813 = 1124555) (by norm_num)
theorem B4211261 : Blo 1663031 4211261 := bbase (se 3 (by rfl) ⟨789611, by rfl⟩ : syracuseStep 4211261 = 1579223) (by norm_num)
theorem B2105929 : Blo 1663031 2105929 := bbase (se 2 (by rfl) ⟨789723, by rfl⟩ : syracuseStep 2105929 = 1579447) (by norm_num)
theorem B3998285 : Blo 1663031 3998285 := bbase (se 3 (by rfl) ⟨749678, by rfl⟩ : syracuseStep 3998285 = 1499357) (by norm_num)
theorem B3744341 : Blo 1663031 3744341 := bbase (se 8 (by rfl) ⟨21939, by rfl⟩ : syracuseStep 3744341 = 43879) (by norm_num)
theorem B3744413 : Blo 1663031 3744413 := bbase (se 3 (by rfl) ⟨702077, by rfl⟩ : syracuseStep 3744413 = 1404155) (by norm_num)
theorem B4268749 : Blo 1663031 4268749 := bbase (se 3 (by rfl) ⟨800390, by rfl⟩ : syracuseStep 4268749 = 1600781) (by norm_num)
theorem B3744485 : Blo 1663031 3744485 := bbase (se 4 (by rfl) ⟨351045, by rfl⟩ : syracuseStep 3744485 = 702091) (by norm_num)
theorem B2106101 : Blo 1663031 2106101 := bbase (se 5 (by rfl) ⟨98723, by rfl⟩ : syracuseStep 2106101 = 197447) (by norm_num)
theorem B4211453 : Blo 1663031 4211453 := bbase (se 3 (by rfl) ⟨789647, by rfl⟩ : syracuseStep 4211453 = 1579295) (by norm_num)
theorem B1999613 : Blo 1663031 1999613 := bbase (se 3 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 1999613 = 749855) (by norm_num)
theorem B2106157 : Blo 1663031 2106157 := bbase (se 3 (by rfl) ⟨394904, by rfl⟩ : syracuseStep 2106157 = 789809) (by norm_num)
theorem B3744557 : Blo 1663031 3744557 := bbase (se 3 (by rfl) ⟨702104, by rfl⟩ : syracuseStep 3744557 = 1404209) (by norm_num)
theorem B5333813 : Blo 1663031 5333813 := bbase (se 5 (by rfl) ⟨250022, by rfl⟩ : syracuseStep 5333813 = 500045) (by norm_num)
theorem B3744629 : Blo 1663031 3744629 := bbase (se 5 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 3744629 = 351059) (by norm_num)
theorem B2106253 : Blo 1663031 2106253 := bbase (se 3 (by rfl) ⟨394922, by rfl⟩ : syracuseStep 2106253 = 789845) (by norm_num)
theorem B3744701 : Blo 1663031 3744701 := bbase (se 3 (by rfl) ⟨702131, by rfl⟩ : syracuseStep 3744701 = 1404263) (by norm_num)
theorem B2368453 : Blo 1663031 2368453 := bbase (se 4 (by rfl) ⟨222042, by rfl⟩ : syracuseStep 2368453 = 444085) (by norm_num)
theorem B11994101 : Blo 1663031 11994101 := bbase (se 5 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 11994101 = 1124447) (by norm_num)
theorem B3998717 : Blo 1663031 3998717 := bbase (se 3 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 3998717 = 1499519) (by norm_num)
theorem B3744773 : Blo 1663031 3744773 := bbase (se 4 (by rfl) ⟨351072, by rfl⟩ : syracuseStep 3744773 = 702145) (by norm_num)
theorem B2106425 : Blo 1663031 2106425 := bbase (se 2 (by rfl) ⟨789909, by rfl⟩ : syracuseStep 2106425 = 1579819) (by norm_num)
theorem B3744845 : Blo 1663031 3744845 := bbase (se 3 (by rfl) ⟨702158, by rfl⟩ : syracuseStep 3744845 = 1404317) (by norm_num)
theorem B1999949 : Blo 1663031 1999949 := bbase (se 3 (by rfl) ⟨374990, by rfl⟩ : syracuseStep 1999949 = 749981) (by norm_num)
theorem B4211797 : Blo 1663031 4211797 := bbase (se 8 (by rfl) ⟨24678, by rfl⟩ : syracuseStep 4211797 = 49357) (by norm_num)
theorem B2106481 : Blo 1663031 2106481 := bbase (se 2 (by rfl) ⟨789930, by rfl⟩ : syracuseStep 2106481 = 1579861) (by norm_num)
theorem B3744917 : Blo 1663031 3744917 := bbase (se 6 (by rfl) ⟨87771, by rfl⟩ : syracuseStep 3744917 = 175543) (by norm_num)
theorem B2999477 : Blo 1663031 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B2000065 : Blo 1663031 2000065 := bbase (se 2 (by rfl) ⟨750024, by rfl⟩ : syracuseStep 2000065 = 1500049) (by norm_num)
theorem B4211909 : Blo 1663031 4211909 := bbase (se 4 (by rfl) ⟨394866, by rfl⟩ : syracuseStep 4211909 = 789733) (by norm_num)
theorem B2106577 : Blo 1663031 2106577 := bbase (se 2 (by rfl) ⟨789966, by rfl⟩ : syracuseStep 2106577 = 1579933) (by norm_num)
theorem B2000089 : Blo 1663031 2000089 := bbase (se 2 (by rfl) ⟨750033, by rfl⟩ : syracuseStep 2000089 = 1500067) (by norm_num)
theorem B3744989 : Blo 1663031 3744989 := bbase (se 3 (by rfl) ⟨702185, by rfl⟩ : syracuseStep 3744989 = 1404371) (by norm_num)
theorem B4736245 : Blo 1663031 4736245 := bbase (se 5 (by rfl) ⟨222011, by rfl⟩ : syracuseStep 4736245 = 444023) (by norm_num)
theorem B3745061 : Blo 1663031 3745061 := bbase (se 4 (by rfl) ⟨351099, by rfl⟩ : syracuseStep 3745061 = 702199) (by norm_num)
theorem B3745133 : Blo 1663031 3745133 := bbase (se 3 (by rfl) ⟨702212, by rfl⟩ : syracuseStep 3745133 = 1404425) (by norm_num)
theorem B2106749 : Blo 1663031 2106749 := bbase (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) (by norm_num)
theorem B4212101 : Blo 1663031 4212101 := bbase (se 4 (by rfl) ⟨394884, by rfl⟩ : syracuseStep 4212101 = 789769) (by norm_num)
theorem B2999693 : Blo 1663031 2999693 := bbase (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) (by norm_num)
theorem B3745205 : Blo 1663031 3745205 := bbase (se 5 (by rfl) ⟨175556, by rfl⟩ : syracuseStep 3745205 = 351113) (by norm_num)
theorem B2106805 : Blo 1663031 2106805 := bbase (se 5 (by rfl) ⟨98756, by rfl⟩ : syracuseStep 2106805 = 197513) (by norm_num)
theorem B2663869 : Blo 1663031 2663869 := bbase (se 3 (by rfl) ⟨499475, by rfl⟩ : syracuseStep 2663869 = 998951) (by norm_num)
theorem B5613029 : Blo 1663031 5613029 := bbase (se 4 (by rfl) ⟨526221, by rfl⟩ : syracuseStep 5613029 = 1052443) (by norm_num)
theorem B2663933 : Blo 1663031 2663933 := bbase (se 3 (by rfl) ⟨499487, by rfl⟩ : syracuseStep 2663933 = 998975) (by norm_num)
theorem B3745277 : Blo 1663031 3745277 := bbase (se 3 (by rfl) ⟨702239, by rfl⟩ : syracuseStep 3745277 = 1404479) (by norm_num)
theorem B2369045 : Blo 1663031 2369045 := bbase (se 6 (by rfl) ⟨55524, by rfl⟩ : syracuseStep 2369045 = 111049) (by norm_num)
theorem B2106901 : Blo 1663031 2106901 := bbase (se 6 (by rfl) ⟨49380, by rfl⟩ : syracuseStep 2106901 = 98761) (by norm_num)
theorem B6317621 : Blo 1663031 6317621 := bbase (se 5 (by rfl) ⟨296138, by rfl⟩ : syracuseStep 6317621 = 592277) (by norm_num)
theorem B3745349 : Blo 1663031 3745349 := bbase (se 4 (by rfl) ⟨351126, by rfl⟩ : syracuseStep 3745349 = 702253) (by norm_num)
theorem B7300709 : Blo 1663031 7300709 := bbase (se 4 (by rfl) ⟨684441, by rfl⟩ : syracuseStep 7300709 = 1368883) (by norm_num)
theorem B2369125 : Blo 1663031 2369125 := bbase (se 4 (by rfl) ⟨222105, by rfl⟩ : syracuseStep 2369125 = 444211) (by norm_num)
theorem B3745421 : Blo 1663031 3745421 := bbase (se 3 (by rfl) ⟨702266, by rfl⟩ : syracuseStep 3745421 = 1404533) (by norm_num)
theorem B31999637 : Blo 1663031 31999637 := bbase (se 6 (by rfl) ⟨749991, by rfl⟩ : syracuseStep 31999637 = 1499983) (by norm_num)
theorem B2107073 : Blo 1663031 2107073 := bbase (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) (by norm_num)
theorem B3745493 : Blo 1663031 3745493 := bbase (se 7 (by rfl) ⟨43892, by rfl⟩ : syracuseStep 3745493 = 87785) (by norm_num)
theorem B2369245 : Blo 1663031 2369245 := bbase (se 3 (by rfl) ⟨444233, by rfl⟩ : syracuseStep 2369245 = 888467) (by norm_num)
theorem B4212445 : Blo 1663031 4212445 := bbase (se 3 (by rfl) ⟨789833, by rfl⟩ : syracuseStep 4212445 = 1579667) (by norm_num)
theorem B2926309 : Blo 1663031 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B2107129 : Blo 1663031 2107129 := bbase (se 2 (by rfl) ⟨790173, by rfl⟩ : syracuseStep 2107129 = 1580347) (by norm_num)
theorem B8423189 : Blo 1663031 8423189 := bbase (se 6 (by rfl) ⟨197418, by rfl⟩ : syracuseStep 8423189 = 394837) (by norm_num)
theorem B3745565 : Blo 1663031 3745565 := bbase (se 3 (by rfl) ⟨702293, by rfl⟩ : syracuseStep 3745565 = 1404587) (by norm_num)
theorem B2369341 : Blo 1663031 2369341 := bbase (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) (by norm_num)
theorem B4212557 : Blo 1663031 4212557 := bbase (se 3 (by rfl) ⟨789854, by rfl⟩ : syracuseStep 4212557 = 1579709) (by norm_num)
theorem B6317909 : Blo 1663031 6317909 := bbase (se 9 (by rfl) ⟨18509, by rfl⟩ : syracuseStep 6317909 = 37019) (by norm_num)
theorem B2107225 : Blo 1663031 2107225 := bbase (se 2 (by rfl) ⟨790209, by rfl⟩ : syracuseStep 2107225 = 1580419) (by norm_num)
theorem B3745637 : Blo 1663031 3745637 := bbase (se 4 (by rfl) ⟨351153, by rfl⟩ : syracuseStep 3745637 = 702307) (by norm_num)
theorem B3000197 : Blo 1663031 3000197 := bbase (se 4 (by rfl) ⟨281268, by rfl⟩ : syracuseStep 3000197 = 562537) (by norm_num)
theorem B5613461 : Blo 1663031 5613461 := bbase (se 6 (by rfl) ⟨131565, by rfl⟩ : syracuseStep 5613461 = 263131) (by norm_num)
theorem B3745709 : Blo 1663031 3745709 := bbase (se 3 (by rfl) ⟨702320, by rfl⟩ : syracuseStep 3745709 = 1404641) (by norm_num)
theorem B5998549 : Blo 1663031 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B3745781 : Blo 1663031 3745781 := bbase (se 5 (by rfl) ⟨175583, by rfl⟩ : syracuseStep 3745781 = 351167) (by norm_num)
theorem B4212749 : Blo 1663031 4212749 := bbase (se 3 (by rfl) ⟨789890, by rfl⟩ : syracuseStep 4212749 = 1579781) (by norm_num)
theorem B4499509 : Blo 1663031 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B3745853 : Blo 1663031 3745853 := bbase (se 3 (by rfl) ⟨702347, by rfl⟩ : syracuseStep 3745853 = 1404695) (by norm_num)
theorem B3745925 : Blo 1663031 3745925 := bbase (se 4 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 3745925 = 702361) (by norm_num)
theorem B3999917 : Blo 1663031 3999917 := bbase (se 3 (by rfl) ⟨749984, by rfl⟩ : syracuseStep 3999917 = 1499969) (by norm_num)
theorem B3745997 : Blo 1663031 3745997 := bbase (se 3 (by rfl) ⟨702374, by rfl⟩ : syracuseStep 3745997 = 1404749) (by norm_num)
theorem B3746069 : Blo 1663031 3746069 := bbase (se 6 (by rfl) ⟨87798, by rfl⟩ : syracuseStep 3746069 = 175597) (by norm_num)
theorem B2369837 : Blo 1663031 2369837 := bbase (se 3 (by rfl) ⟨444344, by rfl⟩ : syracuseStep 2369837 = 888689) (by norm_num)
theorem B5613893 : Blo 1663031 5613893 := bbase (se 4 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 5613893 = 1052605) (by norm_num)
theorem B14223701 : Blo 1663031 14223701 := bbase (se 10 (by rfl) ⟨20835, by rfl⟩ : syracuseStep 14223701 = 41671) (by norm_num)
theorem B3746141 : Blo 1663031 3746141 := bbase (se 3 (by rfl) ⟨702401, by rfl⟩ : syracuseStep 3746141 = 1404803) (by norm_num)
theorem B4213093 : Blo 1663031 4213093 := bbase (se 4 (by rfl) ⟨394977, by rfl⟩ : syracuseStep 4213093 = 789955) (by norm_num)
theorem B3746213 : Blo 1663031 3746213 := bbase (se 4 (by rfl) ⟨351207, by rfl⟩ : syracuseStep 3746213 = 702415) (by norm_num)
theorem B4213205 : Blo 1663031 4213205 := bbase (se 7 (by rfl) ⟨49373, by rfl⟩ : syracuseStep 4213205 = 98747) (by norm_num)
theorem B3746285 : Blo 1663031 3746285 := bbase (se 3 (by rfl) ⟨702428, by rfl⟩ : syracuseStep 3746285 = 1404857) (by norm_num)
theorem B4213397 : Blo 1663031 4213397 := bbase (se 6 (by rfl) ⟨98751, by rfl⟩ : syracuseStep 4213397 = 197503) (by norm_num)
theorem B11389621 : Blo 1663031 11389621 := bbase (se 5 (by rfl) ⟨533888, by rfl⟩ : syracuseStep 11389621 = 1067777) (by norm_num)
theorem B4270781 : Blo 1663031 4270781 := bbase (se 3 (by rfl) ⟨800771, by rfl⟩ : syracuseStep 4270781 = 1601543) (by norm_num)
theorem B5614325 : Blo 1663031 5614325 := bbase (se 5 (by rfl) ⟨263171, by rfl⟩ : syracuseStep 5614325 = 526343) (by norm_num)
theorem B2665253 : Blo 1663031 2665253 := bbase (se 4 (by rfl) ⟨249867, by rfl⟩ : syracuseStep 2665253 = 499735) (by norm_num)
theorem B2370389 : Blo 1663031 2370389 := bbase (se 9 (by rfl) ⟨6944, by rfl⟩ : syracuseStep 2370389 = 13889) (by norm_num)
theorem B5327765 : Blo 1663031 5327765 := bbase (se 6 (by rfl) ⟨124869, by rfl⟩ : syracuseStep 5327765 = 249739) (by norm_num)
theorem B2665381 : Blo 1663031 2665381 := bbase (se 4 (by rfl) ⟨249879, by rfl⟩ : syracuseStep 2665381 = 499759) (by norm_num)
theorem B4213741 : Blo 1663031 4213741 := bbase (se 3 (by rfl) ⟨790076, by rfl⟩ : syracuseStep 4213741 = 1580153) (by norm_num)
theorem B6319093 : Blo 1663031 6319093 := bbase (se 5 (by rfl) ⟨296207, by rfl⟩ : syracuseStep 6319093 = 592415) (by norm_num)
theorem B8424485 : Blo 1663031 8424485 := bbase (se 4 (by rfl) ⟨789795, by rfl⟩ : syracuseStep 8424485 = 1579591) (by norm_num)
theorem B1870933 : Blo 1663031 1870933 := bbase (se 8 (by rfl) ⟨10962, by rfl⟩ : syracuseStep 1870933 = 21925) (by norm_num)
theorem B4213853 : Blo 1663031 4213853 := bbase (se 3 (by rfl) ⟨790097, by rfl⟩ : syracuseStep 4213853 = 1580195) (by norm_num)
theorem B7588981 : Blo 1663031 7588981 := bbase (se 5 (by rfl) ⟨355733, by rfl⟩ : syracuseStep 7588981 = 711467) (by norm_num)
theorem B1870969 : Blo 1663031 1870969 := bbase (se 2 (by rfl) ⟨701613, by rfl⟩ : syracuseStep 1870969 = 1403227) (by norm_num)
theorem B1871005 : Blo 1663031 1871005 := bbase (se 3 (by rfl) ⟨350813, by rfl⟩ : syracuseStep 1871005 = 701627) (by norm_num)
theorem B6745253 : Blo 1663031 6745253 := bbase (se 4 (by rfl) ⟨632367, by rfl⟩ : syracuseStep 6745253 = 1264735) (by norm_num)
theorem B5614757 : Blo 1663031 5614757 := bbase (se 4 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 5614757 = 1052767) (by norm_num)
theorem B1871041 : Blo 1663031 1871041 := bbase (se 2 (by rfl) ⟨701640, by rfl⟩ : syracuseStep 1871041 = 1403281) (by norm_num)
theorem B1871077 : Blo 1663031 1871077 := bbase (se 4 (by rfl) ⟨175413, by rfl⟩ : syracuseStep 1871077 = 350827) (by norm_num)
theorem B7204069 : Blo 1663031 7204069 := bbase (se 4 (by rfl) ⟨675381, by rfl⟩ : syracuseStep 7204069 = 1350763) (by norm_num)
theorem B1871113 : Blo 1663031 1871113 := bbase (se 2 (by rfl) ⟨701667, by rfl⟩ : syracuseStep 1871113 = 1403335) (by norm_num)
theorem B4214045 : Blo 1663031 4214045 := bbase (se 3 (by rfl) ⟨790133, by rfl⟩ : syracuseStep 4214045 = 1580267) (by norm_num)
theorem B4164901 : Blo 1663031 4164901 := bbase (se 4 (by rfl) ⟨390459, by rfl⟩ : syracuseStep 4164901 = 780919) (by norm_num)
theorem B6319397 : Blo 1663031 6319397 := bbase (se 4 (by rfl) ⟨592443, by rfl⟩ : syracuseStep 6319397 = 1184887) (by norm_num)
theorem B1871149 : Blo 1663031 1871149 := bbase (se 3 (by rfl) ⟨350840, by rfl⟩ : syracuseStep 1871149 = 701681) (by norm_num)
theorem B2247997 : Blo 1663031 2247997 := bbase (se 3 (by rfl) ⟨421499, by rfl⟩ : syracuseStep 2247997 = 842999) (by norm_num)
theorem B1871185 : Blo 1663031 1871185 := bbase (se 2 (by rfl) ⟨701694, by rfl⟩ : syracuseStep 1871185 = 1403389) (by norm_num)
theorem B1871221 : Blo 1663031 1871221 := bbase (se 5 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 1871221 = 175427) (by norm_num)
theorem B1871257 : Blo 1663031 1871257 := bbase (se 2 (by rfl) ⟨701721, by rfl⟩ : syracuseStep 1871257 = 1403443) (by norm_num)
theorem B1871293 : Blo 1663031 1871293 := bbase (se 3 (by rfl) ⟨350867, by rfl⟩ : syracuseStep 1871293 = 701735) (by norm_num)
theorem B4050389 : Blo 1663031 4050389 := bbase (se 7 (by rfl) ⟨47465, by rfl⟩ : syracuseStep 4050389 = 94931) (by norm_num)
theorem B1871329 : Blo 1663031 1871329 := bbase (se 2 (by rfl) ⟨701748, by rfl⟩ : syracuseStep 1871329 = 1403497) (by norm_num)
theorem B1871365 : Blo 1663031 1871365 := bbase (se 4 (by rfl) ⟨175440, by rfl⟩ : syracuseStep 1871365 = 350881) (by norm_num)
theorem B1871401 : Blo 1663031 1871401 := bbase (se 2 (by rfl) ⟨701775, by rfl⟩ : syracuseStep 1871401 = 1403551) (by norm_num)
theorem B1871437 : Blo 1663031 1871437 := bbase (se 3 (by rfl) ⟨350894, by rfl⟩ : syracuseStep 1871437 = 701789) (by norm_num)
theorem B5615189 : Blo 1663031 5615189 := bbase (se 8 (by rfl) ⟨32901, by rfl⟩ : syracuseStep 5615189 = 65803) (by norm_num)
theorem B1871473 : Blo 1663031 1871473 := bbase (se 2 (by rfl) ⟨701802, by rfl⟩ : syracuseStep 1871473 = 1403605) (by norm_num)
theorem B4214389 : Blo 1663031 4214389 := bbase (se 5 (by rfl) ⟨197549, by rfl⟩ : syracuseStep 4214389 = 395099) (by norm_num)
theorem B1871509 : Blo 1663031 1871509 := bbase (se 6 (by rfl) ⟨43863, by rfl⟩ : syracuseStep 1871509 = 87727) (by norm_num)
theorem B1871545 : Blo 1663031 1871545 := bbase (se 2 (by rfl) ⟨701829, by rfl⟩ : syracuseStep 1871545 = 1403659) (by norm_num)
theorem B2666189 : Blo 1663031 2666189 := bbase (se 3 (by rfl) ⟨499910, by rfl⟩ : syracuseStep 2666189 = 999821) (by norm_num)
theorem B3157717 : Blo 1663031 3157717 := bbase (se 7 (by rfl) ⟨37004, by rfl⟩ : syracuseStep 3157717 = 74009) (by norm_num)
theorem B1871581 : Blo 1663031 1871581 := bbase (se 3 (by rfl) ⟨350921, by rfl⟩ : syracuseStep 1871581 = 701843) (by norm_num)
theorem B4214501 : Blo 1663031 4214501 := bbase (se 4 (by rfl) ⟨395109, by rfl⟩ : syracuseStep 4214501 = 790219) (by norm_num)
theorem B1871617 : Blo 1663031 1871617 := bbase (se 2 (by rfl) ⟨701856, by rfl⟩ : syracuseStep 1871617 = 1403713) (by norm_num)
theorem B1871653 : Blo 1663031 1871653 := bbase (se 4 (by rfl) ⟨175467, by rfl⟩ : syracuseStep 1871653 = 350935) (by norm_num)
theorem B1871689 : Blo 1663031 1871689 := bbase (se 2 (by rfl) ⟨701883, by rfl⟩ : syracuseStep 1871689 = 1403767) (by norm_num)
theorem B3157861 : Blo 1663031 3157861 := bbase (se 4 (by rfl) ⟨296049, by rfl⟩ : syracuseStep 3157861 = 592099) (by norm_num)
theorem B1871725 : Blo 1663031 1871725 := bbase (se 3 (by rfl) ⟨350948, by rfl⟩ : syracuseStep 1871725 = 701897) (by norm_num)
theorem B1871761 : Blo 1663031 1871761 := bbase (se 2 (by rfl) ⟨701910, by rfl⟩ : syracuseStep 1871761 = 1403821) (by norm_num)
theorem B7106453 : Blo 1663031 7106453 := bbase (se 6 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 7106453 = 333115) (by norm_num)
theorem B1871797 : Blo 1663031 1871797 := bbase (se 5 (by rfl) ⟨87740, by rfl⟩ : syracuseStep 1871797 = 175481) (by norm_num)
theorem B64876501 : Blo 1663031 64876501 := bbase (se 7 (by rfl) ⟨760271, by rfl⟩ : syracuseStep 64876501 = 1520543) (by norm_num)
theorem B1871833 : Blo 1663031 1871833 := bbase (se 2 (by rfl) ⟨701937, by rfl⟩ : syracuseStep 1871833 = 1403875) (by norm_num)
theorem B2666477 : Blo 1663031 2666477 := bbase (se 3 (by rfl) ⟨499964, by rfl⟩ : syracuseStep 2666477 = 999929) (by norm_num)
theorem B1871869 : Blo 1663031 1871869 := bbase (se 3 (by rfl) ⟨350975, by rfl⟩ : syracuseStep 1871869 = 701951) (by norm_num)
theorem B3600389 : Blo 1663031 3600389 := bbase (se 4 (by rfl) ⟨337536, by rfl⟩ : syracuseStep 3600389 = 675073) (by norm_num)
theorem B3158021 : Blo 1663031 3158021 := bbase (se 4 (by rfl) ⟨296064, by rfl⟩ : syracuseStep 3158021 = 592129) (by norm_num)
theorem B5615621 : Blo 1663031 5615621 := bbase (se 4 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 5615621 = 1052929) (by norm_num)
theorem B2248717 : Blo 1663031 2248717 := bbase (se 3 (by rfl) ⟨421634, by rfl⟩ : syracuseStep 2248717 = 843269) (by norm_num)
theorem B4739093 : Blo 1663031 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B2846749 : Blo 1663031 2846749 := bbase (se 3 (by rfl) ⟨533765, by rfl⟩ : syracuseStep 2846749 = 1067531) (by norm_num)
theorem B1871905 : Blo 1663031 1871905 := bbase (se 2 (by rfl) ⟨701964, by rfl⟩ : syracuseStep 1871905 = 1403929) (by norm_num)
theorem B1871941 : Blo 1663031 1871941 := bbase (se 4 (by rfl) ⟨175494, by rfl⟩ : syracuseStep 1871941 = 350989) (by norm_num)
theorem B2494565 : Blo 1663031 2494565 := bbase (se 4 (by rfl) ⟨233865, by rfl⟩ : syracuseStep 2494565 = 467731) (by norm_num)
theorem B1871977 : Blo 1663031 1871977 := bbase (se 2 (by rfl) ⟨701991, by rfl⟩ : syracuseStep 1871977 = 1403983) (by norm_num)
theorem B1896565 : Blo 1663031 1896565 := bbase (se 5 (by rfl) ⟨88901, by rfl⟩ : syracuseStep 1896565 = 177803) (by norm_num)
theorem B2494589 : Blo 1663031 2494589 := bbase (se 3 (by rfl) ⟨467735, by rfl⟩ : syracuseStep 2494589 = 935471) (by norm_num)
theorem B1872013 : Blo 1663031 1872013 := bbase (se 3 (by rfl) ⟨351002, by rfl⟩ : syracuseStep 1872013 = 702005) (by norm_num)
theorem B2494613 : Blo 1663031 2494613 := bbase (se 6 (by rfl) ⟨58467, by rfl⟩ : syracuseStep 2494613 = 116935) (by norm_num)
theorem B3158165 : Blo 1663031 3158165 := bbase (se 6 (by rfl) ⟨74019, by rfl⟩ : syracuseStep 3158165 = 148039) (by norm_num)
theorem B2494637 : Blo 1663031 2494637 := bbase (se 3 (by rfl) ⟨467744, by rfl⟩ : syracuseStep 2494637 = 935489) (by norm_num)
theorem B1872049 : Blo 1663031 1872049 := bbase (se 2 (by rfl) ⟨702018, by rfl⟩ : syracuseStep 1872049 = 1404037) (by norm_num)
theorem B1896629 : Blo 1663031 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B2494661 : Blo 1663031 2494661 := bbase (se 4 (by rfl) ⟨233874, by rfl⟩ : syracuseStep 2494661 = 467749) (by norm_num)
theorem B1896661 : Blo 1663031 1896661 := bbase (se 7 (by rfl) ⟨22226, by rfl⟩ : syracuseStep 1896661 = 44453) (by norm_num)
theorem B1872085 : Blo 1663031 1872085 := bbase (se 7 (by rfl) ⟨21938, by rfl⟩ : syracuseStep 1872085 = 43877) (by norm_num)
theorem B2494685 : Blo 1663031 2494685 := bbase (se 3 (by rfl) ⟨467753, by rfl⟩ : syracuseStep 2494685 = 935507) (by norm_num)
theorem B2494709 : Blo 1663031 2494709 := bbase (se 5 (by rfl) ⟨116939, by rfl⟩ : syracuseStep 2494709 = 233879) (by norm_num)
theorem B1872121 : Blo 1663031 1872121 := bbase (se 2 (by rfl) ⟨702045, by rfl⟩ : syracuseStep 1872121 = 1404091) (by norm_num)
theorem B2494733 : Blo 1663031 2494733 := bbase (se 3 (by rfl) ⟨467762, by rfl⟩ : syracuseStep 2494733 = 935525) (by norm_num)
theorem B1872157 : Blo 1663031 1872157 := bbase (se 3 (by rfl) ⟨351029, by rfl⟩ : syracuseStep 1872157 = 702059) (by norm_num)
theorem B2494757 : Blo 1663031 2494757 := bbase (se 4 (by rfl) ⟨233883, by rfl⟩ : syracuseStep 2494757 = 467767) (by norm_num)
theorem B8425781 : Blo 1663031 8425781 := bbase (se 5 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 8425781 = 789917) (by norm_num)
theorem B2494781 : Blo 1663031 2494781 := bbase (se 3 (by rfl) ⟨467771, by rfl⟩ : syracuseStep 2494781 = 935543) (by norm_num)
theorem B1872193 : Blo 1663031 1872193 := bbase (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) (by norm_num)
theorem B2494805 : Blo 1663031 2494805 := bbase (se 10 (by rfl) ⟨3654, by rfl⟩ : syracuseStep 2494805 = 7309) (by norm_num)
theorem B1872229 : Blo 1663031 1872229 := bbase (se 4 (by rfl) ⟨175521, by rfl⟩ : syracuseStep 1872229 = 351043) (by norm_num)
theorem B2494829 : Blo 1663031 2494829 := bbase (se 3 (by rfl) ⟨467780, by rfl⟩ : syracuseStep 2494829 = 935561) (by norm_num)
theorem B2494853 : Blo 1663031 2494853 := bbase (se 4 (by rfl) ⟨233892, by rfl⟩ : syracuseStep 2494853 = 467785) (by norm_num)
theorem B1872265 : Blo 1663031 1872265 := bbase (se 2 (by rfl) ⟨702099, by rfl⟩ : syracuseStep 1872265 = 1404199) (by norm_num)
theorem B2666893 : Blo 1663031 2666893 := bbase (se 3 (by rfl) ⟨500042, by rfl⟩ : syracuseStep 2666893 = 1000085) (by norm_num)
theorem B10662293 : Blo 1663031 10662293 := bbase (se 6 (by rfl) ⟨249897, by rfl⟩ : syracuseStep 10662293 = 499795) (by norm_num)
theorem B2494877 : Blo 1663031 2494877 := bbase (se 3 (by rfl) ⟨467789, by rfl⟩ : syracuseStep 2494877 = 935579) (by norm_num)
theorem B3420581 : Blo 1663031 3420581 := bbase (se 4 (by rfl) ⟨320679, by rfl⟩ : syracuseStep 3420581 = 641359) (by norm_num)
theorem B1872301 : Blo 1663031 1872301 := bbase (se 3 (by rfl) ⟨351056, by rfl⟩ : syracuseStep 1872301 = 702113) (by norm_num)
theorem B2494901 : Blo 1663031 2494901 := bbase (se 5 (by rfl) ⟨116948, by rfl⟩ : syracuseStep 2494901 = 233897) (by norm_num)
theorem B3158453 : Blo 1663031 3158453 := bbase (se 5 (by rfl) ⟨148052, by rfl⟩ : syracuseStep 3158453 = 296105) (by norm_num)
theorem B5616053 : Blo 1663031 5616053 := bbase (se 5 (by rfl) ⟨263252, by rfl⟩ : syracuseStep 5616053 = 526505) (by norm_num)
theorem B2249149 : Blo 1663031 2249149 := bbase (se 3 (by rfl) ⟨421715, by rfl⟩ : syracuseStep 2249149 = 843431) (by norm_num)
theorem B2494925 : Blo 1663031 2494925 := bbase (se 3 (by rfl) ⟨467798, by rfl⟩ : syracuseStep 2494925 = 935597) (by norm_num)
theorem B1872337 : Blo 1663031 1872337 := bbase (se 2 (by rfl) ⟨702126, by rfl⟩ : syracuseStep 1872337 = 1404253) (by norm_num)
theorem B2494949 : Blo 1663031 2494949 := bbase (se 4 (by rfl) ⟨233901, by rfl⟩ : syracuseStep 2494949 = 467803) (by norm_num)
theorem B1872373 : Blo 1663031 1872373 := bbase (se 5 (by rfl) ⟨87767, by rfl⟩ : syracuseStep 1872373 = 175535) (by norm_num)
theorem B9482741 : Blo 1663031 9482741 := bbase (se 5 (by rfl) ⟨444503, by rfl⟩ : syracuseStep 9482741 = 889007) (by norm_num)
theorem B2494973 : Blo 1663031 2494973 := bbase (se 3 (by rfl) ⟨467807, by rfl⟩ : syracuseStep 2494973 = 935615) (by norm_num)
theorem B2494997 : Blo 1663031 2494997 := bbase (se 6 (by rfl) ⟨58476, by rfl⟩ : syracuseStep 2494997 = 116953) (by norm_num)
theorem B1872409 : Blo 1663031 1872409 := bbase (se 2 (by rfl) ⟨702153, by rfl⟩ : syracuseStep 1872409 = 1404307) (by norm_num)
theorem B2495021 : Blo 1663031 2495021 := bbase (se 3 (by rfl) ⟨467816, by rfl⟩ : syracuseStep 2495021 = 935633) (by norm_num)
theorem B1872445 : Blo 1663031 1872445 := bbase (se 3 (by rfl) ⟨351083, by rfl⟩ : syracuseStep 1872445 = 702167) (by norm_num)
theorem B2495045 : Blo 1663031 2495045 := bbase (se 4 (by rfl) ⟨233910, by rfl⟩ : syracuseStep 2495045 = 467821) (by norm_num)
theorem B3158605 : Blo 1663031 3158605 := bbase (se 3 (by rfl) ⟨592238, by rfl⟩ : syracuseStep 3158605 = 1184477) (by norm_num)
theorem B2495069 : Blo 1663031 2495069 := bbase (se 3 (by rfl) ⟨467825, by rfl⟩ : syracuseStep 2495069 = 935651) (by norm_num)
theorem B1872481 : Blo 1663031 1872481 := bbase (se 2 (by rfl) ⟨702180, by rfl⟩ : syracuseStep 1872481 = 1404361) (by norm_num)
theorem B2806373 : Blo 1663031 2806373 := bbase (se 4 (by rfl) ⟨263097, by rfl⟩ : syracuseStep 2806373 = 526195) (by norm_num)
theorem B2495093 : Blo 1663031 2495093 := bbase (se 5 (by rfl) ⟨116957, by rfl⟩ : syracuseStep 2495093 = 233915) (by norm_num)
theorem B9474677 : Blo 1663031 9474677 := bbase (se 5 (by rfl) ⟨444125, by rfl⟩ : syracuseStep 9474677 = 888251) (by norm_num)
theorem B1872517 : Blo 1663031 1872517 := bbase (se 4 (by rfl) ⟨175548, by rfl⟩ : syracuseStep 1872517 = 351097) (by norm_num)
theorem B2495117 : Blo 1663031 2495117 := bbase (se 3 (by rfl) ⟨467834, by rfl⟩ : syracuseStep 2495117 = 935669) (by norm_num)
theorem B2495141 : Blo 1663031 2495141 := bbase (se 4 (by rfl) ⟨233919, by rfl⟩ : syracuseStep 2495141 = 467839) (by norm_num)
theorem B2249381 : Blo 1663031 2249381 := bbase (se 4 (by rfl) ⟨210879, by rfl⟩ : syracuseStep 2249381 = 421759) (by norm_num)
theorem B1872553 : Blo 1663031 1872553 := bbase (se 2 (by rfl) ⟨702207, by rfl⟩ : syracuseStep 1872553 = 1404415) (by norm_num)
theorem B2495165 : Blo 1663031 2495165 := bbase (se 3 (by rfl) ⟨467843, by rfl⟩ : syracuseStep 2495165 = 935687) (by norm_num)
theorem B1872589 : Blo 1663031 1872589 := bbase (se 3 (by rfl) ⟨351110, by rfl⟩ : syracuseStep 1872589 = 702221) (by norm_num)
theorem B2495189 : Blo 1663031 2495189 := bbase (se 7 (by rfl) ⟨29240, by rfl⟩ : syracuseStep 2495189 = 58481) (by norm_num)
theorem B2806501 : Blo 1663031 2806501 := bbase (se 4 (by rfl) ⟨263109, by rfl⟩ : syracuseStep 2806501 = 526219) (by norm_num)
theorem B2495213 : Blo 1663031 2495213 := bbase (se 3 (by rfl) ⟨467852, by rfl⟩ : syracuseStep 2495213 = 935705) (by norm_num)
theorem B1872625 : Blo 1663031 1872625 := bbase (se 2 (by rfl) ⟨702234, by rfl⟩ : syracuseStep 1872625 = 1404469) (by norm_num)
theorem B2495237 : Blo 1663031 2495237 := bbase (se 4 (by rfl) ⟨233928, by rfl⟩ : syracuseStep 2495237 = 467857) (by norm_num)
theorem B5329685 : Blo 1663031 5329685 := bbase (se 6 (by rfl) ⟨124914, by rfl⟩ : syracuseStep 5329685 = 249829) (by norm_num)
theorem B1872661 : Blo 1663031 1872661 := bbase (se 6 (by rfl) ⟨43890, by rfl⟩ : syracuseStep 1872661 = 87781) (by norm_num)
theorem B2495261 : Blo 1663031 2495261 := bbase (se 3 (by rfl) ⟨467861, by rfl⟩ : syracuseStep 2495261 = 935723) (by norm_num)
theorem B1897249 : Blo 1663031 1897249 := bbase (se 2 (by rfl) ⟨711468, by rfl⟩ : syracuseStep 1897249 = 1422937) (by norm_num)
theorem B2495285 : Blo 1663031 2495285 := bbase (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) (by norm_num)
theorem B1872697 : Blo 1663031 1872697 := bbase (se 2 (by rfl) ⟨702261, by rfl⟩ : syracuseStep 1872697 = 1404523) (by norm_num)
theorem B2806589 : Blo 1663031 2806589 := bbase (se 3 (by rfl) ⟨526235, by rfl⟩ : syracuseStep 2806589 = 1052471) (by norm_num)
theorem B2495309 : Blo 1663031 2495309 := bbase (se 3 (by rfl) ⟨467870, by rfl⟩ : syracuseStep 2495309 = 935741) (by norm_num)
theorem B1872733 : Blo 1663031 1872733 := bbase (se 3 (by rfl) ⟨351137, by rfl⟩ : syracuseStep 1872733 = 702275) (by norm_num)
theorem B2495333 : Blo 1663031 2495333 := bbase (se 4 (by rfl) ⟨233937, by rfl⟩ : syracuseStep 2495333 = 467875) (by norm_num)
theorem B5616485 : Blo 1663031 5616485 := bbase (se 4 (by rfl) ⟨526545, by rfl⟩ : syracuseStep 5616485 = 1053091) (by norm_num)
theorem B2495357 : Blo 1663031 2495357 := bbase (se 3 (by rfl) ⟨467879, by rfl⟩ : syracuseStep 2495357 = 935759) (by norm_num)
theorem B3158909 : Blo 1663031 3158909 := bbase (se 3 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 3158909 = 1184591) (by norm_num)
theorem B1872769 : Blo 1663031 1872769 := bbase (se 2 (by rfl) ⟨702288, by rfl⟩ : syracuseStep 1872769 = 1404577) (by norm_num)
theorem B3552133 : Blo 1663031 3552133 := bbase (se 4 (by rfl) ⟨333012, by rfl⟩ : syracuseStep 3552133 = 666025) (by norm_num)
theorem B2495381 : Blo 1663031 2495381 := bbase (se 6 (by rfl) ⟨58485, by rfl⟩ : syracuseStep 2495381 = 116971) (by norm_num)
theorem B1872805 : Blo 1663031 1872805 := bbase (se 4 (by rfl) ⟨175575, by rfl⟩ : syracuseStep 1872805 = 351151) (by norm_num)
theorem B2495405 : Blo 1663031 2495405 := bbase (se 3 (by rfl) ⟨467888, by rfl⟩ : syracuseStep 2495405 = 935777) (by norm_num)
theorem B2806717 : Blo 1663031 2806717 := bbase (se 3 (by rfl) ⟨526259, by rfl⟩ : syracuseStep 2806717 = 1052519) (by norm_num)
theorem B2495429 : Blo 1663031 2495429 := bbase (se 4 (by rfl) ⟨233946, by rfl⟩ : syracuseStep 2495429 = 467893) (by norm_num)
theorem B1872841 : Blo 1663031 1872841 := bbase (se 2 (by rfl) ⟨702315, by rfl⟩ : syracuseStep 1872841 = 1404631) (by norm_num)
theorem B2495453 : Blo 1663031 2495453 := bbase (se 3 (by rfl) ⟨467897, by rfl⟩ : syracuseStep 2495453 = 935795) (by norm_num)
theorem B1872877 : Blo 1663031 1872877 := bbase (se 3 (by rfl) ⟨351164, by rfl⟩ : syracuseStep 1872877 = 702329) (by norm_num)
theorem B2495477 : Blo 1663031 2495477 := bbase (se 5 (by rfl) ⟨116975, by rfl⟩ : syracuseStep 2495477 = 233951) (by norm_num)
theorem B2135041 : Blo 1663031 2135041 := bbase (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) (by norm_num)
theorem B2495501 : Blo 1663031 2495501 := bbase (se 3 (by rfl) ⟨467906, by rfl⟩ : syracuseStep 2495501 = 935813) (by norm_num)
theorem B1872913 : Blo 1663031 1872913 := bbase (se 2 (by rfl) ⟨702342, by rfl⟩ : syracuseStep 1872913 = 1404685) (by norm_num)
theorem B2806805 : Blo 1663031 2806805 := bbase (se 6 (by rfl) ⟨65784, by rfl⟩ : syracuseStep 2806805 = 131569) (by norm_num)
theorem B2495525 : Blo 1663031 2495525 := bbase (se 4 (by rfl) ⟨233955, by rfl⟩ : syracuseStep 2495525 = 467911) (by norm_num)
theorem B1872949 : Blo 1663031 1872949 := bbase (se 5 (by rfl) ⟨87794, by rfl⟩ : syracuseStep 1872949 = 175589) (by norm_num)
theorem B2495549 : Blo 1663031 2495549 := bbase (se 3 (by rfl) ⟨467915, by rfl⟩ : syracuseStep 2495549 = 935831) (by norm_num)
theorem B2495573 : Blo 1663031 2495573 := bbase (se 8 (by rfl) ⟨14622, by rfl⟩ : syracuseStep 2495573 = 29245) (by norm_num)
theorem B6403157 : Blo 1663031 6403157 := bbase (se 8 (by rfl) ⟨37518, by rfl⟩ : syracuseStep 6403157 = 75037) (by norm_num)
theorem B1872985 : Blo 1663031 1872985 := bbase (se 2 (by rfl) ⟨702369, by rfl⟩ : syracuseStep 1872985 = 1404739) (by norm_num)
theorem B1897573 : Blo 1663031 1897573 := bbase (se 4 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 1897573 = 355795) (by norm_num)
theorem B2495597 : Blo 1663031 2495597 := bbase (se 3 (by rfl) ⟨467924, by rfl⟩ : syracuseStep 2495597 = 935849) (by norm_num)
theorem B2249845 : Blo 1663031 2249845 := bbase (se 5 (by rfl) ⟨105461, by rfl⟩ : syracuseStep 2249845 = 210923) (by norm_num)
theorem B1873021 : Blo 1663031 1873021 := bbase (se 3 (by rfl) ⟨351191, by rfl⟩ : syracuseStep 1873021 = 702383) (by norm_num)
theorem B2495621 : Blo 1663031 2495621 := bbase (se 4 (by rfl) ⟨233964, by rfl⟩ : syracuseStep 2495621 = 467929) (by norm_num)
theorem B2806933 : Blo 1663031 2806933 := bbase (se 6 (by rfl) ⟨65787, by rfl⟩ : syracuseStep 2806933 = 131575) (by norm_num)
theorem B2495645 : Blo 1663031 2495645 := bbase (se 3 (by rfl) ⟨467933, by rfl⟩ : syracuseStep 2495645 = 935867) (by norm_num)
theorem B1873057 : Blo 1663031 1873057 := bbase (se 2 (by rfl) ⟨702396, by rfl⟩ : syracuseStep 1873057 = 1404793) (by norm_num)
theorem B5690533 : Blo 1663031 5690533 := bbase (se 4 (by rfl) ⟨533487, by rfl⟩ : syracuseStep 5690533 = 1066975) (by norm_num)
theorem B2495669 : Blo 1663031 2495669 := bbase (se 5 (by rfl) ⟨116984, by rfl⟩ : syracuseStep 2495669 = 233969) (by norm_num)
theorem B4740277 : Blo 1663031 4740277 := bbase (se 5 (by rfl) ⟨222200, by rfl⟩ : syracuseStep 4740277 = 444401) (by norm_num)
theorem B1873093 : Blo 1663031 1873093 := bbase (se 4 (by rfl) ⟨175602, by rfl⟩ : syracuseStep 1873093 = 351205) (by norm_num)
theorem B2495693 : Blo 1663031 2495693 := bbase (se 3 (by rfl) ⟨467942, by rfl⟩ : syracuseStep 2495693 = 935885) (by norm_num)
theorem B8541397 : Blo 1663031 8541397 := bbase (se 7 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 8541397 = 200189) (by norm_num)
theorem B2495717 : Blo 1663031 2495717 := bbase (se 4 (by rfl) ⟨233973, by rfl⟩ : syracuseStep 2495717 = 467947) (by norm_num)
theorem B1873129 : Blo 1663031 1873129 := bbase (se 2 (by rfl) ⟨702423, by rfl⟩ : syracuseStep 1873129 = 1404847) (by norm_num)
theorem B2807021 : Blo 1663031 2807021 := bbase (se 3 (by rfl) ⟨526316, by rfl⟩ : syracuseStep 2807021 = 1052633) (by norm_num)
theorem B2495741 : Blo 1663031 2495741 := bbase (se 3 (by rfl) ⟨467951, by rfl⟩ : syracuseStep 2495741 = 935903) (by norm_num)
theorem B2495765 : Blo 1663031 2495765 := bbase (se 6 (by rfl) ⟨58494, by rfl⟩ : syracuseStep 2495765 = 116989) (by norm_num)
theorem B5616917 : Blo 1663031 5616917 := bbase (se 6 (by rfl) ⟨131646, by rfl⟩ : syracuseStep 5616917 = 263293) (by norm_num)
theorem B2495789 : Blo 1663031 2495789 := bbase (se 3 (by rfl) ⟨467960, by rfl⟩ : syracuseStep 2495789 = 935921) (by norm_num)
theorem B2495813 : Blo 1663031 2495813 := bbase (se 4 (by rfl) ⟨233982, by rfl⟩ : syracuseStep 2495813 = 467965) (by norm_num)
theorem B6747461 : Blo 1663031 6747461 := bbase (se 4 (by rfl) ⟨632574, by rfl⟩ : syracuseStep 6747461 = 1265149) (by norm_num)
theorem B9606485 : Blo 1663031 9606485 := bbase (se 14 (by rfl) ⟨879, by rfl⟩ : syracuseStep 9606485 = 1759) (by norm_num)
theorem B4740437 : Blo 1663031 4740437 := bbase (se 16 (by rfl) ⟨108, by rfl⟩ : syracuseStep 4740437 = 217) (by norm_num)
theorem B2495837 : Blo 1663031 2495837 := bbase (se 3 (by rfl) ⟨467969, by rfl⟩ : syracuseStep 2495837 = 935939) (by norm_num)
theorem B6321509 : Blo 1663031 6321509 := bbase (se 4 (by rfl) ⟨592641, by rfl⟩ : syracuseStep 6321509 = 1185283) (by norm_num)
theorem B2807149 : Blo 1663031 2807149 := bbase (se 3 (by rfl) ⟨526340, by rfl⟩ : syracuseStep 2807149 = 1052681) (by norm_num)
theorem B2495861 : Blo 1663031 2495861 := bbase (se 5 (by rfl) ⟨116993, by rfl⟩ : syracuseStep 2495861 = 233987) (by norm_num)
theorem B2495885 : Blo 1663031 2495885 := bbase (se 3 (by rfl) ⟨467978, by rfl⟩ : syracuseStep 2495885 = 935957) (by norm_num)
theorem B2495909 : Blo 1663031 2495909 := bbase (se 4 (by rfl) ⟨233991, by rfl⟩ : syracuseStep 2495909 = 467983) (by norm_num)
theorem B2495933 : Blo 1663031 2495933 := bbase (se 3 (by rfl) ⟨467987, by rfl⟩ : syracuseStep 2495933 = 935975) (by norm_num)
theorem B2807237 : Blo 1663031 2807237 := bbase (se 4 (by rfl) ⟨263178, by rfl⟩ : syracuseStep 2807237 = 526357) (by norm_num)
theorem B2495957 : Blo 1663031 2495957 := bbase (se 7 (by rfl) ⟨29249, by rfl⟩ : syracuseStep 2495957 = 58499) (by norm_num)
theorem B2528741 : Blo 1663031 2528741 := bbase (se 4 (by rfl) ⟨237069, by rfl⟩ : syracuseStep 2528741 = 474139) (by norm_num)
theorem B2495981 : Blo 1663031 2495981 := bbase (se 3 (by rfl) ⟨467996, by rfl⟩ : syracuseStep 2495981 = 935993) (by norm_num)
theorem B2496005 : Blo 1663031 2496005 := bbase (se 4 (by rfl) ⟨234000, by rfl⟩ : syracuseStep 2496005 = 468001) (by norm_num)
theorem B15996437 : Blo 1663031 15996437 := bbase (se 6 (by rfl) ⟨374916, by rfl⟩ : syracuseStep 15996437 = 749833) (by norm_num)
theorem B2496029 : Blo 1663031 2496029 := bbase (se 3 (by rfl) ⟨468005, by rfl⟩ : syracuseStep 2496029 = 936011) (by norm_num)
theorem B2496053 : Blo 1663031 2496053 := bbase (se 5 (by rfl) ⟨117002, by rfl⟩ : syracuseStep 2496053 = 234005) (by norm_num)
theorem B1922617 : Blo 1663031 1922617 := bbase (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) (by norm_num)
theorem B2807365 : Blo 1663031 2807365 := bbase (se 4 (by rfl) ⟨263190, by rfl⟩ : syracuseStep 2807365 = 526381) (by norm_num)
theorem B8427077 : Blo 1663031 8427077 := bbase (se 4 (by rfl) ⟨790038, by rfl⟩ : syracuseStep 8427077 = 1580077) (by norm_num)
theorem B4740677 : Blo 1663031 4740677 := bbase (se 4 (by rfl) ⟨444438, by rfl⟩ : syracuseStep 4740677 = 888877) (by norm_num)
theorem B2496077 : Blo 1663031 2496077 := bbase (se 3 (by rfl) ⟨468014, by rfl⟩ : syracuseStep 2496077 = 936029) (by norm_num)
theorem B2496101 : Blo 1663031 2496101 := bbase (se 4 (by rfl) ⟨234009, by rfl⟩ : syracuseStep 2496101 = 468019) (by norm_num)
theorem B8001125 : Blo 1663031 8001125 := bbase (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) (by norm_num)
theorem B3159661 : Blo 1663031 3159661 := bbase (se 3 (by rfl) ⟨592436, by rfl⟩ : syracuseStep 3159661 = 1184873) (by norm_num)
theorem B2496125 : Blo 1663031 2496125 := bbase (se 3 (by rfl) ⟨468023, by rfl⟩ : syracuseStep 2496125 = 936047) (by norm_num)
theorem B7108229 : Blo 1663031 7108229 := bbase (se 4 (by rfl) ⟨666396, by rfl⟩ : syracuseStep 7108229 = 1332793) (by norm_num)
theorem B6321797 : Blo 1663031 6321797 := bbase (se 4 (by rfl) ⟨592668, by rfl⟩ : syracuseStep 6321797 = 1185337) (by norm_num)
theorem B2496149 : Blo 1663031 2496149 := bbase (se 6 (by rfl) ⟨58503, by rfl⟩ : syracuseStep 2496149 = 117007) (by norm_num)
theorem B2807453 : Blo 1663031 2807453 := bbase (se 3 (by rfl) ⟨526397, by rfl⟩ : syracuseStep 2807453 = 1052795) (by norm_num)
theorem B2496173 : Blo 1663031 2496173 := bbase (se 3 (by rfl) ⟨468032, by rfl⟩ : syracuseStep 2496173 = 936065) (by norm_num)
theorem B2496197 : Blo 1663031 2496197 := bbase (se 4 (by rfl) ⟨234018, by rfl⟩ : syracuseStep 2496197 = 468037) (by norm_num)
theorem B5617349 : Blo 1663031 5617349 := bbase (se 4 (by rfl) ⟨526626, by rfl⟩ : syracuseStep 5617349 = 1053253) (by norm_num)
theorem B2496221 : Blo 1663031 2496221 := bbase (se 3 (by rfl) ⟨468041, by rfl⟩ : syracuseStep 2496221 = 936083) (by norm_num)
theorem B2496245 : Blo 1663031 2496245 := bbase (se 5 (by rfl) ⟨117011, by rfl⟩ : syracuseStep 2496245 = 234023) (by norm_num)
theorem B3553021 : Blo 1663031 3553021 := bbase (se 3 (by rfl) ⟨666191, by rfl⟩ : syracuseStep 3553021 = 1332383) (by norm_num)
theorem B3159805 : Blo 1663031 3159805 := bbase (se 3 (by rfl) ⟨592463, by rfl⟩ : syracuseStep 3159805 = 1184927) (by norm_num)
theorem B4740869 : Blo 1663031 4740869 := bbase (se 4 (by rfl) ⟨444456, by rfl⟩ : syracuseStep 4740869 = 888913) (by norm_num)
theorem B2496269 : Blo 1663031 2496269 := bbase (se 3 (by rfl) ⟨468050, by rfl⟩ : syracuseStep 2496269 = 936101) (by norm_num)
theorem B2807581 : Blo 1663031 2807581 := bbase (se 3 (by rfl) ⟨526421, by rfl⟩ : syracuseStep 2807581 = 1052843) (by norm_num)
theorem B2496293 : Blo 1663031 2496293 := bbase (se 4 (by rfl) ⟨234027, by rfl⟩ : syracuseStep 2496293 = 468055) (by norm_num)
theorem B2496317 : Blo 1663031 2496317 := bbase (se 3 (by rfl) ⟨468059, by rfl⟩ : syracuseStep 2496317 = 936119) (by norm_num)
theorem B2496341 : Blo 1663031 2496341 := bbase (se 9 (by rfl) ⟨7313, by rfl⟩ : syracuseStep 2496341 = 14627) (by norm_num)
theorem B2496365 : Blo 1663031 2496365 := bbase (se 3 (by rfl) ⟨468068, by rfl⟩ : syracuseStep 2496365 = 936137) (by norm_num)
theorem B3553141 : Blo 1663031 3553141 := bbase (se 5 (by rfl) ⟨166553, by rfl⟩ : syracuseStep 3553141 = 333107) (by norm_num)
theorem B2807669 : Blo 1663031 2807669 := bbase (se 5 (by rfl) ⟨131609, by rfl⟩ : syracuseStep 2807669 = 263219) (by norm_num)
theorem B7108469 : Blo 1663031 7108469 := bbase (se 5 (by rfl) ⟨333209, by rfl⟩ : syracuseStep 7108469 = 666419) (by norm_num)
theorem B2496389 : Blo 1663031 2496389 := bbase (se 4 (by rfl) ⟨234036, by rfl⟩ : syracuseStep 2496389 = 468073) (by norm_num)
theorem B2496413 : Blo 1663031 2496413 := bbase (se 3 (by rfl) ⟨468077, by rfl⟩ : syracuseStep 2496413 = 936155) (by norm_num)
theorem B3159965 : Blo 1663031 3159965 := bbase (se 3 (by rfl) ⟨592493, by rfl⟩ : syracuseStep 3159965 = 1184987) (by norm_num)
theorem B2496437 : Blo 1663031 2496437 := bbase (se 5 (by rfl) ⟨117020, by rfl⟩ : syracuseStep 2496437 = 234041) (by norm_num)
theorem B2701253 : Blo 1663031 2701253 := bbase (se 4 (by rfl) ⟨253242, by rfl⟩ : syracuseStep 2701253 = 506485) (by norm_num)
theorem B2496461 : Blo 1663031 2496461 := bbase (se 3 (by rfl) ⟨468086, by rfl⟩ : syracuseStep 2496461 = 936173) (by norm_num)
theorem B22763477 : Blo 1663031 22763477 := bbase (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) (by norm_num)
theorem B8419301 : Blo 1663031 8419301 := bbase (se 4 (by rfl) ⟨789309, by rfl⟩ : syracuseStep 8419301 = 1578619) (by norm_num)
theorem B2496485 : Blo 1663031 2496485 := bbase (se 4 (by rfl) ⟨234045, by rfl⟩ : syracuseStep 2496485 = 468091) (by norm_num)
theorem B2807797 : Blo 1663031 2807797 := bbase (se 5 (by rfl) ⟨131615, by rfl⟩ : syracuseStep 2807797 = 263231) (by norm_num)
theorem B2496509 : Blo 1663031 2496509 := bbase (se 3 (by rfl) ⟨468095, by rfl⟩ : syracuseStep 2496509 = 936191) (by norm_num)
theorem B2496533 : Blo 1663031 2496533 := bbase (se 6 (by rfl) ⟨58512, by rfl⟩ : syracuseStep 2496533 = 117025) (by norm_num)
theorem B2496557 : Blo 1663031 2496557 := bbase (se 3 (by rfl) ⟨468104, by rfl⟩ : syracuseStep 2496557 = 936209) (by norm_num)
theorem B3160109 : Blo 1663031 3160109 := bbase (se 3 (by rfl) ⟨592520, by rfl⟩ : syracuseStep 3160109 = 1185041) (by norm_num)
theorem B2529349 : Blo 1663031 2529349 := bbase (se 4 (by rfl) ⟨237126, by rfl⟩ : syracuseStep 2529349 = 474253) (by norm_num)
theorem B2496581 : Blo 1663031 2496581 := bbase (se 4 (by rfl) ⟨234054, by rfl⟩ : syracuseStep 2496581 = 468109) (by norm_num)
theorem B2807885 : Blo 1663031 2807885 := bbase (se 3 (by rfl) ⟨526478, by rfl⟩ : syracuseStep 2807885 = 1052957) (by norm_num)
theorem B8992853 : Blo 1663031 8992853 := bbase (se 8 (by rfl) ⟨52692, by rfl⟩ : syracuseStep 8992853 = 105385) (by norm_num)
theorem B2496605 : Blo 1663031 2496605 := bbase (se 3 (by rfl) ⟨468113, by rfl⟩ : syracuseStep 2496605 = 936227) (by norm_num)
theorem B3553397 : Blo 1663031 3553397 := bbase (se 5 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 3553397 = 333131) (by norm_num)
theorem B2496629 : Blo 1663031 2496629 := bbase (se 5 (by rfl) ⟨117029, by rfl⟩ : syracuseStep 2496629 = 234059) (by norm_num)
theorem B5617781 : Blo 1663031 5617781 := bbase (se 5 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 5617781 = 526667) (by norm_num)
theorem B3741821 : Blo 1663031 3741821 := bbase (se 3 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 3741821 = 1403183) (by norm_num)
theorem B2496653 : Blo 1663031 2496653 := bbase (se 3 (by rfl) ⟨468122, by rfl⟩ : syracuseStep 2496653 = 936245) (by norm_num)
theorem B5331109 : Blo 1663031 5331109 := bbase (se 4 (by rfl) ⟨499791, by rfl⟩ : syracuseStep 5331109 = 999583) (by norm_num)
theorem B2496677 : Blo 1663031 2496677 := bbase (se 4 (by rfl) ⟨234063, by rfl⟩ : syracuseStep 2496677 = 468127) (by norm_num)
theorem B2496701 : Blo 1663031 2496701 := bbase (se 3 (by rfl) ⟨468131, by rfl⟩ : syracuseStep 2496701 = 936263) (by norm_num)
theorem B3741893 : Blo 1663031 3741893 := bbase (se 4 (by rfl) ⟨350802, by rfl⟩ : syracuseStep 3741893 = 701605) (by norm_num)
theorem B2808013 : Blo 1663031 2808013 := bbase (se 3 (by rfl) ⟨526502, by rfl⟩ : syracuseStep 2808013 = 1053005) (by norm_num)
theorem B2496725 : Blo 1663031 2496725 := bbase (se 7 (by rfl) ⟨29258, by rfl⟩ : syracuseStep 2496725 = 58517) (by norm_num)
theorem B2496749 : Blo 1663031 2496749 := bbase (se 3 (by rfl) ⟨468140, by rfl⟩ : syracuseStep 2496749 = 936281) (by norm_num)
theorem B2496773 : Blo 1663031 2496773 := bbase (se 4 (by rfl) ⟨234072, by rfl⟩ : syracuseStep 2496773 = 468145) (by norm_num)
theorem B3741965 : Blo 1663031 3741965 := bbase (se 3 (by rfl) ⟨701618, by rfl⟩ : syracuseStep 3741965 = 1403237) (by norm_num)
theorem B5994773 : Blo 1663031 5994773 := bbase (se 6 (by rfl) ⟨140502, by rfl⟩ : syracuseStep 5994773 = 281005) (by norm_num)
theorem B2496797 : Blo 1663031 2496797 := bbase (se 3 (by rfl) ⟨468149, by rfl⟩ : syracuseStep 2496797 = 936299) (by norm_num)
theorem B2808101 : Blo 1663031 2808101 := bbase (se 4 (by rfl) ⟨263259, by rfl⟩ : syracuseStep 2808101 = 526519) (by norm_num)
theorem B3995957 : Blo 1663031 3995957 := bbase (se 5 (by rfl) ⟨187310, by rfl⟩ : syracuseStep 3995957 = 374621) (by norm_num)
theorem B2496821 : Blo 1663031 2496821 := bbase (se 5 (by rfl) ⟨117038, by rfl⟩ : syracuseStep 2496821 = 234077) (by norm_num)
theorem B2496845 : Blo 1663031 2496845 := bbase (se 3 (by rfl) ⟨468158, by rfl⟩ : syracuseStep 2496845 = 936317) (by norm_num)
theorem B3160397 : Blo 1663031 3160397 := bbase (se 3 (by rfl) ⟨592574, by rfl⟩ : syracuseStep 3160397 = 1185149) (by norm_num)
theorem B3742037 : Blo 1663031 3742037 := bbase (se 10 (by rfl) ⟨5481, by rfl⟩ : syracuseStep 3742037 = 10963) (by norm_num)
theorem B2701669 : Blo 1663031 2701669 := bbase (se 4 (by rfl) ⟨253281, by rfl⟩ : syracuseStep 2701669 = 506563) (by norm_num)
theorem B2496869 : Blo 1663031 2496869 := bbase (se 4 (by rfl) ⟨234081, by rfl⟩ : syracuseStep 2496869 = 468163) (by norm_num)
theorem B2496893 : Blo 1663031 2496893 := bbase (se 3 (by rfl) ⟨468167, by rfl⟩ : syracuseStep 2496893 = 936335) (by norm_num)
theorem B2496917 : Blo 1663031 2496917 := bbase (se 6 (by rfl) ⟨58521, by rfl⟩ : syracuseStep 2496917 = 117043) (by norm_num)
theorem B3742109 : Blo 1663031 3742109 := bbase (se 3 (by rfl) ⟨701645, by rfl⟩ : syracuseStep 3742109 = 1403291) (by norm_num)
theorem B2808229 : Blo 1663031 2808229 := bbase (se 4 (by rfl) ⟨263271, by rfl⟩ : syracuseStep 2808229 = 526543) (by norm_num)
theorem B2496941 : Blo 1663031 2496941 := bbase (se 3 (by rfl) ⟨468176, by rfl⟩ : syracuseStep 2496941 = 936353) (by norm_num)
theorem B1776049 : Blo 1663031 1776049 := bbase (se 2 (by rfl) ⟨666018, by rfl⟩ : syracuseStep 1776049 = 1332037) (by norm_num)
theorem B1685953 : Blo 1663031 1685953 := bbase (se 2 (by rfl) ⟨632232, by rfl⟩ : syracuseStep 1685953 = 1264465) (by norm_num)
theorem B2496965 : Blo 1663031 2496965 := bbase (se 4 (by rfl) ⟨234090, by rfl⟩ : syracuseStep 2496965 = 468181) (by norm_num)
theorem B1710533 : Blo 1663031 1710533 := bbase (se 4 (by rfl) ⟨160362, by rfl⟩ : syracuseStep 1710533 = 320725) (by norm_num)
theorem B63969749 : Blo 1663031 63969749 := bbase (se 7 (by rfl) ⟨749645, by rfl⟩ : syracuseStep 63969749 = 1499291) (by norm_num)
theorem B2496989 : Blo 1663031 2496989 := bbase (se 3 (by rfl) ⟨468185, by rfl⟩ : syracuseStep 2496989 = 936371) (by norm_num)
theorem B3742181 : Blo 1663031 3742181 := bbase (se 4 (by rfl) ⟨350829, by rfl⟩ : syracuseStep 3742181 = 701659) (by norm_num)
theorem B3160549 : Blo 1663031 3160549 := bbase (se 4 (by rfl) ⟨296301, by rfl⟩ : syracuseStep 3160549 = 592603) (by norm_num)
theorem B2497013 : Blo 1663031 2497013 := bbase (se 5 (by rfl) ⟨117047, by rfl⟩ : syracuseStep 2497013 = 234095) (by norm_num)
theorem B2808317 : Blo 1663031 2808317 := bbase (se 3 (by rfl) ⟨526559, by rfl⟩ : syracuseStep 2808317 = 1053119) (by norm_num)
theorem B2497037 : Blo 1663031 2497037 := bbase (se 3 (by rfl) ⟨468194, by rfl⟩ : syracuseStep 2497037 = 936389) (by norm_num)
theorem B3602981 : Blo 1663031 3602981 := bbase (se 4 (by rfl) ⟨337779, by rfl⟩ : syracuseStep 3602981 = 675559) (by norm_num)
theorem B5618213 : Blo 1663031 5618213 := bbase (se 4 (by rfl) ⟨526707, by rfl⟩ : syracuseStep 5618213 = 1053415) (by norm_num)
theorem B2497061 : Blo 1663031 2497061 := bbase (se 4 (by rfl) ⟨234099, by rfl⟩ : syracuseStep 2497061 = 468199) (by norm_num)
theorem B1776169 : Blo 1663031 1776169 := bbase (se 2 (by rfl) ⟨666063, by rfl⟩ : syracuseStep 1776169 = 1332127) (by norm_num)
theorem B3742253 : Blo 1663031 3742253 := bbase (se 3 (by rfl) ⟨701672, by rfl⟩ : syracuseStep 3742253 = 1403345) (by norm_num)
theorem B2497085 : Blo 1663031 2497085 := bbase (se 3 (by rfl) ⟨468203, by rfl⟩ : syracuseStep 2497085 = 936407) (by norm_num)
theorem B2497109 : Blo 1663031 2497109 := bbase (se 8 (by rfl) ⟨14631, by rfl⟩ : syracuseStep 2497109 = 29263) (by norm_num)
theorem B1800797 : Blo 1663031 1800797 := bbase (se 3 (by rfl) ⟨337649, by rfl⟩ : syracuseStep 1800797 = 675299) (by norm_num)
theorem B5331557 : Blo 1663031 5331557 := bbase (se 4 (by rfl) ⟨499833, by rfl⟩ : syracuseStep 5331557 = 999667) (by norm_num)
theorem B2497133 : Blo 1663031 2497133 := bbase (se 3 (by rfl) ⟨468212, by rfl⟩ : syracuseStep 2497133 = 936425) (by norm_num)
theorem B3742325 : Blo 1663031 3742325 := bbase (se 5 (by rfl) ⟨175421, by rfl⟩ : syracuseStep 3742325 = 350843) (by norm_num)
theorem B2808445 : Blo 1663031 2808445 := bbase (se 3 (by rfl) ⟨526583, by rfl⟩ : syracuseStep 2808445 = 1053167) (by norm_num)
theorem B2497157 : Blo 1663031 2497157 := bbase (se 4 (by rfl) ⟨234108, by rfl⟩ : syracuseStep 2497157 = 468217) (by norm_num)
theorem B18946709 : Blo 1663031 18946709 := bbase (se 6 (by rfl) ⟨444063, by rfl⟩ : syracuseStep 18946709 = 888127) (by norm_num)
theorem B2497181 : Blo 1663031 2497181 := bbase (se 3 (by rfl) ⟨468221, by rfl⟩ : syracuseStep 2497181 = 936443) (by norm_num)
theorem B2497205 : Blo 1663031 2497205 := bbase (se 5 (by rfl) ⟨117056, by rfl⟩ : syracuseStep 2497205 = 234113) (by norm_num)
theorem B3742397 : Blo 1663031 3742397 := bbase (se 3 (by rfl) ⟨701699, by rfl⟩ : syracuseStep 3742397 = 1403399) (by norm_num)
theorem B5995205 : Blo 1663031 5995205 := bbase (se 4 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 5995205 = 1124101) (by norm_num)
theorem B2497229 : Blo 1663031 2497229 := bbase (se 3 (by rfl) ⟨468230, by rfl⟩ : syracuseStep 2497229 = 936461) (by norm_num)
theorem B2808533 : Blo 1663031 2808533 := bbase (se 7 (by rfl) ⟨32912, by rfl⟩ : syracuseStep 2808533 = 65825) (by norm_num)
theorem B2497253 : Blo 1663031 2497253 := bbase (se 4 (by rfl) ⟨234117, by rfl⟩ : syracuseStep 2497253 = 468235) (by norm_num)
theorem B2497277 : Blo 1663031 2497277 := bbase (se 3 (by rfl) ⟨468239, by rfl⟩ : syracuseStep 2497277 = 936479) (by norm_num)
theorem B3742469 : Blo 1663031 3742469 := bbase (se 4 (by rfl) ⟨350856, by rfl⟩ : syracuseStep 3742469 = 701713) (by norm_num)
theorem B2497301 : Blo 1663031 2497301 := bbase (se 6 (by rfl) ⟨58530, by rfl⟩ : syracuseStep 2497301 = 117061) (by norm_num)
theorem B3160853 : Blo 1663031 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B1776421 : Blo 1663031 1776421 := bbase (se 4 (by rfl) ⟨166539, by rfl⟩ : syracuseStep 1776421 = 333079) (by norm_num)
theorem B1776425 : Blo 1663031 1776425 := bbase (se 2 (by rfl) ⟨666159, by rfl⟩ : syracuseStep 1776425 = 1332319) (by norm_num)
theorem B2497325 : Blo 1663031 2497325 := bbase (se 3 (by rfl) ⟨468248, by rfl⟩ : syracuseStep 2497325 = 936497) (by norm_num)
theorem B2497349 : Blo 1663031 2497349 := bbase (se 4 (by rfl) ⟨234126, by rfl⟩ : syracuseStep 2497349 = 468253) (by norm_num)
theorem B3742541 : Blo 1663031 3742541 := bbase (se 3 (by rfl) ⟨701726, by rfl⟩ : syracuseStep 3742541 = 1403453) (by norm_num)
theorem B2808661 : Blo 1663031 2808661 := bbase (se 9 (by rfl) ⟨8228, by rfl⟩ : syracuseStep 2808661 = 16457) (by norm_num)
theorem B8428373 : Blo 1663031 8428373 := bbase (se 9 (by rfl) ⟨24692, by rfl⟩ : syracuseStep 8428373 = 49385) (by norm_num)
theorem B2497373 : Blo 1663031 2497373 := bbase (se 3 (by rfl) ⟨468257, by rfl⟩ : syracuseStep 2497373 = 936515) (by norm_num)
theorem B2497397 : Blo 1663031 2497397 := bbase (se 5 (by rfl) ⟨117065, by rfl⟩ : syracuseStep 2497397 = 234131) (by norm_num)
theorem B2497421 : Blo 1663031 2497421 := bbase (se 3 (by rfl) ⟨468266, by rfl⟩ : syracuseStep 2497421 = 936533) (by norm_num)
theorem B3742613 : Blo 1663031 3742613 := bbase (se 6 (by rfl) ⟨87717, by rfl⟩ : syracuseStep 3742613 = 175435) (by norm_num)
theorem B2497445 : Blo 1663031 2497445 := bbase (se 4 (by rfl) ⟨234135, by rfl⟩ : syracuseStep 2497445 = 468271) (by norm_num)
theorem B2808749 : Blo 1663031 2808749 := bbase (se 3 (by rfl) ⟨526640, by rfl⟩ : syracuseStep 2808749 = 1053281) (by norm_num)
theorem B2497469 : Blo 1663031 2497469 := bbase (se 3 (by rfl) ⟨468275, by rfl⟩ : syracuseStep 2497469 = 936551) (by norm_num)
theorem B9608149 : Blo 1663031 9608149 := bbase (se 7 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 9608149 = 225191) (by norm_num)
theorem B5618645 : Blo 1663031 5618645 := bbase (se 7 (by rfl) ⟨65843, by rfl⟩ : syracuseStep 5618645 = 131687) (by norm_num)
theorem B2497493 : Blo 1663031 2497493 := bbase (se 7 (by rfl) ⟨29267, by rfl⟩ : syracuseStep 2497493 = 58535) (by norm_num)
theorem B3742685 : Blo 1663031 3742685 := bbase (se 3 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 3742685 = 1403507) (by norm_num)
theorem B3554285 : Blo 1663031 3554285 := bbase (se 3 (by rfl) ⟨666428, by rfl⟩ : syracuseStep 3554285 = 1332857) (by norm_num)
theorem B2497517 : Blo 1663031 2497517 := bbase (se 3 (by rfl) ⟨468284, by rfl⟩ : syracuseStep 2497517 = 936569) (by norm_num)
theorem B2497541 : Blo 1663031 2497541 := bbase (se 4 (by rfl) ⟨234144, by rfl⟩ : syracuseStep 2497541 = 468289) (by norm_num)
theorem B3742757 : Blo 1663031 3742757 := bbase (se 4 (by rfl) ⟨350883, by rfl⟩ : syracuseStep 3742757 = 701767) (by norm_num)
theorem B2808877 : Blo 1663031 2808877 := bbase (se 3 (by rfl) ⟨526664, by rfl⟩ : syracuseStep 2808877 = 1053329) (by norm_num)
theorem B3742829 : Blo 1663031 3742829 := bbase (se 3 (by rfl) ⟨701780, by rfl⟩ : syracuseStep 3742829 = 1403561) (by norm_num)
theorem B2808965 : Blo 1663031 2808965 := bbase (se 4 (by rfl) ⟨263340, by rfl⟩ : syracuseStep 2808965 = 526681) (by norm_num)
theorem B3742901 : Blo 1663031 3742901 := bbase (se 5 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 3742901 = 350897) (by norm_num)
theorem B1998013 : Blo 1663031 1998013 := bbase (se 3 (by rfl) ⟨374627, by rfl⟩ : syracuseStep 1998013 = 749255) (by norm_num)
theorem B4209853 : Blo 1663031 4209853 := bbase (se 3 (by rfl) ⟨789347, by rfl⟩ : syracuseStep 4209853 = 1578695) (by norm_num)
theorem B6315205 : Blo 1663031 6315205 := bbase (se 4 (by rfl) ⟨592050, by rfl⟩ : syracuseStep 6315205 = 1184101) (by norm_num)
theorem B3554525 : Blo 1663031 3554525 := bbase (se 3 (by rfl) ⟨666473, by rfl⟩ : syracuseStep 3554525 = 1332947) (by norm_num)
theorem B8420597 : Blo 1663031 8420597 := bbase (se 5 (by rfl) ⟨394715, by rfl⟩ : syracuseStep 8420597 = 789431) (by norm_num)
theorem B3742973 : Blo 1663031 3742973 := bbase (se 3 (by rfl) ⟨701807, by rfl⟩ : syracuseStep 3742973 = 1403615) (by norm_num)
theorem B2809093 : Blo 1663031 2809093 := bbase (se 4 (by rfl) ⟨263352, by rfl⟩ : syracuseStep 2809093 = 526705) (by norm_num)
theorem B1998113 : Blo 1663031 1998113 := bbase (se 2 (by rfl) ⟨749292, by rfl⟩ : syracuseStep 1998113 = 1498585) (by norm_num)
theorem B4209965 : Blo 1663031 4209965 := bbase (se 3 (by rfl) ⟨789368, by rfl⟩ : syracuseStep 4209965 = 1578737) (by norm_num)
theorem B3743045 : Blo 1663031 3743045 := bbase (se 4 (by rfl) ⟨350910, by rfl⟩ : syracuseStep 3743045 = 701821) (by norm_num)
theorem B1776989 : Blo 1663031 1776989 := bbase (se 3 (by rfl) ⟨333185, by rfl⟩ : syracuseStep 1776989 = 666371) (by norm_num)
theorem B2809181 : Blo 1663031 2809181 := bbase (se 3 (by rfl) ⟨526721, by rfl⟩ : syracuseStep 2809181 = 1053443) (by norm_num)
theorem B4496741 : Blo 1663031 4496741 := bbase (se 4 (by rfl) ⟨421569, by rfl⟩ : syracuseStep 4496741 = 843139) (by norm_num)
theorem B5619077 : Blo 1663031 5619077 := bbase (se 4 (by rfl) ⟨526788, by rfl⟩ : syracuseStep 5619077 = 1053577) (by norm_num)
theorem B3743117 : Blo 1663031 3743117 := bbase (se 3 (by rfl) ⟨701834, by rfl⟩ : syracuseStep 3743117 = 1403669) (by norm_num)
theorem B3743189 : Blo 1663031 3743189 := bbase (se 7 (by rfl) ⟨43865, by rfl⟩ : syracuseStep 3743189 = 87731) (by norm_num)
theorem B2809309 : Blo 1663031 2809309 := bbase (se 3 (by rfl) ⟨526745, by rfl⟩ : syracuseStep 2809309 = 1053491) (by norm_num)
theorem B2104805 : Blo 1663031 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B4210157 : Blo 1663031 4210157 := bbase (se 3 (by rfl) ⟨789404, by rfl⟩ : syracuseStep 4210157 = 1578809) (by norm_num)
theorem B6315509 : Blo 1663031 6315509 := bbase (se 5 (by rfl) ⟨296039, by rfl⟩ : syracuseStep 6315509 = 592079) (by norm_num)
theorem B1777177 : Blo 1663031 1777177 := bbase (se 2 (by rfl) ⟨666441, by rfl⟩ : syracuseStep 1777177 = 1332883) (by norm_num)
theorem B2104861 : Blo 1663031 2104861 := bbase (se 3 (by rfl) ⟨394661, by rfl⟩ : syracuseStep 2104861 = 789323) (by norm_num)
theorem B3743261 : Blo 1663031 3743261 := bbase (se 3 (by rfl) ⟨701861, by rfl⟩ : syracuseStep 3743261 = 1403723) (by norm_num)
theorem B2809397 : Blo 1663031 2809397 := bbase (se 5 (by rfl) ⟨131690, by rfl⟩ : syracuseStep 2809397 = 263381) (by norm_num)
theorem B4619845 : Blo 1663031 4619845 := bbase (se 4 (by rfl) ⟨433110, by rfl⟩ : syracuseStep 4619845 = 866221) (by norm_num)
theorem B3743333 : Blo 1663031 3743333 := bbase (se 4 (by rfl) ⟨350937, by rfl⟩ : syracuseStep 3743333 = 701875) (by norm_num)
theorem B2104957 : Blo 1663031 2104957 := bbase (se 3 (by rfl) ⟨394679, by rfl⟩ : syracuseStep 2104957 = 789359) (by norm_num)
theorem B3743405 : Blo 1663031 3743405 := bbase (se 3 (by rfl) ⟨701888, by rfl⟩ : syracuseStep 3743405 = 1403777) (by norm_num)
theorem B9608885 : Blo 1663031 9608885 := bbase (se 5 (by rfl) ⟨450416, by rfl⟩ : syracuseStep 9608885 = 900833) (by norm_num)
theorem B2809525 : Blo 1663031 2809525 := bbase (se 5 (by rfl) ⟨131696, by rfl⟩ : syracuseStep 2809525 = 263393) (by norm_num)
theorem B3555029 : Blo 1663031 3555029 := bbase (se 7 (by rfl) ⟨41660, by rfl⟩ : syracuseStep 3555029 = 83321) (by norm_num)
theorem B3555037 : Blo 1663031 3555037 := bbase (se 3 (by rfl) ⟨666569, by rfl⟩ : syracuseStep 3555037 = 1333139) (by norm_num)
theorem B3743477 : Blo 1663031 3743477 := bbase (se 5 (by rfl) ⟨175475, by rfl⟩ : syracuseStep 3743477 = 350951) (by norm_num)
theorem B7995125 : Blo 1663031 7995125 := bbase (se 5 (by rfl) ⟨374771, by rfl⟩ : syracuseStep 7995125 = 749543) (by norm_num)
theorem B2809613 : Blo 1663031 2809613 := bbase (se 3 (by rfl) ⟨526802, by rfl⟩ : syracuseStep 2809613 = 1053605) (by norm_num)
theorem B2105129 : Blo 1663031 2105129 := bbase (se 2 (by rfl) ⟨789423, by rfl⟩ : syracuseStep 2105129 = 1578847) (by norm_num)
theorem B3743549 : Blo 1663031 3743549 := bbase (se 3 (by rfl) ⟨701915, by rfl⟩ : syracuseStep 3743549 = 1403831) (by norm_num)
theorem B4210501 : Blo 1663031 4210501 := bbase (se 4 (by rfl) ⟨394734, by rfl⟩ : syracuseStep 4210501 = 789469) (by norm_num)
theorem B28417877 : Blo 1663031 28417877 := bbase (se 9 (by rfl) ⟨83255, by rfl⟩ : syracuseStep 28417877 = 166511) (by norm_num)
theorem B2105185 : Blo 1663031 2105185 := bbase (se 2 (by rfl) ⟨789444, by rfl⟩ : syracuseStep 2105185 = 1578889) (by norm_num)
theorem B3743621 : Blo 1663031 3743621 := bbase (se 4 (by rfl) ⟨350964, by rfl⟩ : syracuseStep 3743621 = 701929) (by norm_num)
theorem B1687433 : Blo 1663031 1687433 := bbase (se 2 (by rfl) ⟨632787, by rfl⟩ : syracuseStep 1687433 = 1265575) (by norm_num)
theorem B2809741 : Blo 1663031 2809741 := bbase (se 3 (by rfl) ⟨526826, by rfl⟩ : syracuseStep 2809741 = 1053653) (by norm_num)
theorem B4210613 : Blo 1663031 4210613 := bbase (se 5 (by rfl) ⟨197372, by rfl⟩ : syracuseStep 4210613 = 394745) (by norm_num)
theorem B2105281 : Blo 1663031 2105281 := bbase (se 2 (by rfl) ⟨789480, by rfl⟩ : syracuseStep 2105281 = 1578961) (by norm_num)
theorem B3743693 : Blo 1663031 3743693 := bbase (se 3 (by rfl) ⟨701942, by rfl⟩ : syracuseStep 3743693 = 1403885) (by norm_num)
theorem B2998237 : Blo 1663031 2998237 := bbase (se 3 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 2998237 = 1124339) (by norm_num)
theorem B3997669 : Blo 1663031 3997669 := bbase (se 4 (by rfl) ⟨374781, by rfl⟩ : syracuseStep 3997669 = 749563) (by norm_num)
theorem B2105347 : Blo 1663031 2105347 := bstep (se 1 (by rfl) ⟨1579010, by rfl⟩ : syracuseStep 2105347 = 3158021) B3158021
theorem B3743747 : Blo 1663031 3743747 := bstep (se 1 (by rfl) ⟨2807810, by rfl⟩ : syracuseStep 3743747 = 5615621) B5615621
theorem B9601037 : Blo 1663031 9601037 := bstep (se 3 (by rfl) ⟨1800194, by rfl⟩ : syracuseStep 9601037 = 3600389) B3600389
theorem B2998289 : Blo 1663031 2998289 := bstep (se 2 (by rfl) ⟨1124358, by rfl⟩ : syracuseStep 2998289 = 2248717) B2248717
theorem B45547541 : Blo 1663031 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B1663043 : Blo 1663031 1663043 := bstep (se 1 (by rfl) ⟨1247282, by rfl⟩ : syracuseStep 1663043 = 2494565) B2494565
theorem B1663059 : Blo 1663031 1663059 := bstep (se 1 (by rfl) ⟨1247294, by rfl⟩ : syracuseStep 1663059 = 2494589) B2494589
theorem B1663075 : Blo 1663031 1663075 := bstep (se 1 (by rfl) ⟨1247306, by rfl⟩ : syracuseStep 1663075 = 2494613) B2494613
theorem B2105443 : Blo 1663031 2105443 := bstep (se 1 (by rfl) ⟨1579082, by rfl⟩ : syracuseStep 2105443 = 3158165) B3158165
theorem B1663091 : Blo 1663031 1663091 := bstep (se 1 (by rfl) ⟨1247318, by rfl⟩ : syracuseStep 1663091 = 2494637) B2494637
theorem B1663107 : Blo 1663031 1663107 := bstep (se 1 (by rfl) ⟨1247330, by rfl⟩ : syracuseStep 1663107 = 2494661) B2494661
theorem B5062787 : Blo 1663031 5062787 := bstep (se 1 (by rfl) ⟨3797090, by rfl⟩ : syracuseStep 5062787 = 7594181) B7594181
theorem B1663123 : Blo 1663031 1663123 := bstep (se 1 (by rfl) ⟨1247342, by rfl⟩ : syracuseStep 1663123 = 2494685) B2494685
theorem B1663139 : Blo 1663031 1663139 := bstep (se 1 (by rfl) ⟨1247354, by rfl⟩ : syracuseStep 1663139 = 2494709) B2494709
theorem B1663155 : Blo 1663031 1663155 := bstep (se 1 (by rfl) ⟨1247366, by rfl⟩ : syracuseStep 1663155 = 2494733) B2494733
theorem B1663171 : Blo 1663031 1663171 := bstep (se 1 (by rfl) ⟨1247378, by rfl⟩ : syracuseStep 1663171 = 2494757) B2494757
theorem B5333197 : Blo 1663031 5333197 := bstep (se 3 (by rfl) ⟨999974, by rfl⟩ : syracuseStep 5333197 = 1999949) B1999949
theorem B1663187 : Blo 1663031 1663187 := bstep (se 1 (by rfl) ⟨1247390, by rfl⟩ : syracuseStep 1663187 = 2494781) B2494781
theorem B72982741 : Blo 1663031 72982741 := bstep (se 7 (by rfl) ⟨855266, by rfl⟩ : syracuseStep 72982741 = 1710533) B1710533
theorem B1663203 : Blo 1663031 1663203 := bstep (se 1 (by rfl) ⟨1247402, by rfl⟩ : syracuseStep 1663203 = 2494805) B2494805
theorem B1663219 : Blo 1663031 1663219 := bstep (se 1 (by rfl) ⟨1247414, by rfl⟩ : syracuseStep 1663219 = 2494829) B2494829
theorem B1663235 : Blo 1663031 1663235 := bstep (se 1 (by rfl) ⟨1247426, by rfl⟩ : syracuseStep 1663235 = 2494853) B2494853
theorem B3744017 : Blo 1663031 3744017 := bstep (se 2 (by rfl) ⟨1404006, by rfl⟩ : syracuseStep 3744017 = 2808013) B2808013
theorem B1663251 : Blo 1663031 1663251 := bstep (se 1 (by rfl) ⟨1247438, by rfl⟩ : syracuseStep 1663251 = 2494877) B2494877
theorem B1663267 : Blo 1663031 1663267 := bstep (se 1 (by rfl) ⟨1247450, by rfl⟩ : syracuseStep 1663267 = 2494901) B2494901
theorem B3744035 : Blo 1663031 3744035 := bstep (se 1 (by rfl) ⟨2808026, by rfl⟩ : syracuseStep 3744035 = 5616053) B5616053
theorem B1663283 : Blo 1663031 1663283 := bstep (se 1 (by rfl) ⟨1247462, by rfl⟩ : syracuseStep 1663283 = 2494925) B2494925
theorem B1663299 : Blo 1663031 1663299 := bstep (se 1 (by rfl) ⟨1247474, by rfl⟩ : syracuseStep 1663299 = 2494949) B2494949
theorem B1663315 : Blo 1663031 1663315 := bstep (se 1 (by rfl) ⟨1247486, by rfl⟩ : syracuseStep 1663315 = 2494973) B2494973
theorem B1663331 : Blo 1663031 1663331 := bstep (se 1 (by rfl) ⟨1247498, by rfl⟩ : syracuseStep 1663331 = 2494997) B2494997
theorem B8421731 : Blo 1663031 8421731 := bstep (se 1 (by rfl) ⟨6316298, by rfl⟩ : syracuseStep 8421731 = 12632597) B12632597
theorem B1663347 : Blo 1663031 1663347 := bstep (se 1 (by rfl) ⟨1247510, by rfl⟩ : syracuseStep 1663347 = 2495021) B2495021
theorem B1663363 : Blo 1663031 1663363 := bstep (se 1 (by rfl) ⟨1247522, by rfl⟩ : syracuseStep 1663363 = 2495045) B2495045
theorem B1663379 : Blo 1663031 1663379 := bstep (se 1 (by rfl) ⟨1247534, by rfl⟩ : syracuseStep 1663379 = 2495069) B2495069
theorem B1663395 : Blo 1663031 1663395 := bstep (se 1 (by rfl) ⟨1247546, by rfl⟩ : syracuseStep 1663395 = 2495093) B2495093
theorem B6316451 : Blo 1663031 6316451 := bstep (se 1 (by rfl) ⟨4737338, by rfl⟩ : syracuseStep 6316451 = 9474677) B9474677
theorem B1663411 : Blo 1663031 1663411 := bstep (se 1 (by rfl) ⟨1247558, by rfl⟩ : syracuseStep 1663411 = 2495117) B2495117
theorem B1663427 : Blo 1663031 1663427 := bstep (se 1 (by rfl) ⟨1247570, by rfl⟩ : syracuseStep 1663427 = 2495141) B2495141
theorem B1663443 : Blo 1663031 1663443 := bstep (se 1 (by rfl) ⟨1247582, by rfl⟩ : syracuseStep 1663443 = 2495165) B2495165
theorem B1663459 : Blo 1663031 1663459 := bstep (se 1 (by rfl) ⟨1247594, by rfl⟩ : syracuseStep 1663459 = 2495189) B2495189
theorem B1663475 : Blo 1663031 1663475 := bstep (se 1 (by rfl) ⟨1247606, by rfl⟩ : syracuseStep 1663475 = 2495213) B2495213
theorem B1663491 : Blo 1663031 1663491 := bstep (se 1 (by rfl) ⟨1247618, by rfl⟩ : syracuseStep 1663491 = 2495237) B2495237
theorem B3555857 : Blo 1663031 3555857 := bstep (se 2 (by rfl) ⟨1333446, by rfl⟩ : syracuseStep 3555857 = 2666893) B2666893
theorem B1663507 : Blo 1663031 1663507 := bstep (se 1 (by rfl) ⟨1247630, by rfl⟩ : syracuseStep 1663507 = 2495261) B2495261
theorem B1663523 : Blo 1663031 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B3555875 : Blo 1663031 3555875 := bstep (se 1 (by rfl) ⟨2666906, by rfl⟩ : syracuseStep 3555875 = 5333813) B5333813
theorem B3744305 : Blo 1663031 3744305 := bstep (se 2 (by rfl) ⟨1404114, by rfl⟩ : syracuseStep 3744305 = 2808229) B2808229
theorem B1663539 : Blo 1663031 1663539 := bstep (se 1 (by rfl) ⟨1247654, by rfl⟩ : syracuseStep 1663539 = 2495309) B2495309
theorem B1663555 : Blo 1663031 1663555 := bstep (se 1 (by rfl) ⟨1247666, by rfl⟩ : syracuseStep 1663555 = 2495333) B2495333
theorem B3744323 : Blo 1663031 3744323 := bstep (se 1 (by rfl) ⟨2808242, by rfl⟩ : syracuseStep 3744323 = 5616485) B5616485
theorem B2998865 : Blo 1663031 2998865 := bstep (se 2 (by rfl) ⟨1124574, by rfl⟩ : syracuseStep 2998865 = 2249149) B2249149
theorem B1663571 : Blo 1663031 1663571 := bstep (se 1 (by rfl) ⟨1247678, by rfl⟩ : syracuseStep 1663571 = 2495357) B2495357
theorem B2105939 : Blo 1663031 2105939 := bstep (se 1 (by rfl) ⟨1579454, by rfl⟩ : syracuseStep 2105939 = 3158909) B3158909
theorem B1663587 : Blo 1663031 1663587 := bstep (se 1 (by rfl) ⟨1247690, by rfl⟩ : syracuseStep 1663587 = 2495381) B2495381
theorem B1663603 : Blo 1663031 1663603 := bstep (se 1 (by rfl) ⟨1247702, by rfl⟩ : syracuseStep 1663603 = 2495405) B2495405
theorem B1663619 : Blo 1663031 1663619 := bstep (se 1 (by rfl) ⟨1247714, by rfl⟩ : syracuseStep 1663619 = 2495429) B2495429
theorem B1663635 : Blo 1663031 1663635 := bstep (se 1 (by rfl) ⟨1247726, by rfl⟩ : syracuseStep 1663635 = 2495453) B2495453
theorem B1663651 : Blo 1663031 1663651 := bstep (se 1 (by rfl) ⟨1247738, by rfl⟩ : syracuseStep 1663651 = 2495477) B2495477
theorem B7996067 : Blo 1663031 7996067 := bstep (se 1 (by rfl) ⟨5997050, by rfl⟩ : syracuseStep 7996067 = 11994101) B11994101
theorem B1663667 : Blo 1663031 1663667 := bstep (se 1 (by rfl) ⟨1247750, by rfl⟩ : syracuseStep 1663667 = 2495501) B2495501
theorem B1663683 : Blo 1663031 1663683 := bstep (se 1 (by rfl) ⟨1247762, by rfl⟩ : syracuseStep 1663683 = 2495525) B2495525
theorem B3998417 : Blo 1663031 3998417 := bstep (se 2 (by rfl) ⟨1499406, by rfl⟩ : syracuseStep 3998417 = 2998813) B2998813
theorem B1663699 : Blo 1663031 1663699 := bstep (se 1 (by rfl) ⟨1247774, by rfl⟩ : syracuseStep 1663699 = 2495549) B2495549
theorem B2368225 : Blo 1663031 2368225 := bstep (se 2 (by rfl) ⟨888084, by rfl⟩ : syracuseStep 2368225 = 1776169) B1776169
theorem B1663715 : Blo 1663031 1663715 := bstep (se 1 (by rfl) ⟨1247786, by rfl⟩ : syracuseStep 1663715 = 2495573) B2495573
theorem B4268771 : Blo 1663031 4268771 := bstep (se 1 (by rfl) ⟨3201578, by rfl⟩ : syracuseStep 4268771 = 6403157) B6403157
theorem B1663731 : Blo 1663031 1663731 := bstep (se 1 (by rfl) ⟨1247798, by rfl⟩ : syracuseStep 1663731 = 2495597) B2495597
theorem B1663747 : Blo 1663031 1663747 := bstep (se 1 (by rfl) ⟨1247810, by rfl⟩ : syracuseStep 1663747 = 2495621) B2495621
theorem B4211473 : Blo 1663031 4211473 := bstep (se 2 (by rfl) ⟨1579302, by rfl⟩ : syracuseStep 4211473 = 3158605) B3158605
theorem B1663763 : Blo 1663031 1663763 := bstep (se 1 (by rfl) ⟨1247822, by rfl⟩ : syracuseStep 1663763 = 2495645) B2495645
theorem B1663779 : Blo 1663031 1663779 := bstep (se 1 (by rfl) ⟨1247834, by rfl⟩ : syracuseStep 1663779 = 2495669) B2495669
theorem B1999651 : Blo 1663031 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B1663795 : Blo 1663031 1663795 := bstep (se 1 (by rfl) ⟨1247846, by rfl⟩ : syracuseStep 1663795 = 2495693) B2495693
theorem B1663811 : Blo 1663031 1663811 := bstep (se 1 (by rfl) ⟨1247858, by rfl⟩ : syracuseStep 1663811 = 2495717) B2495717
theorem B3744593 : Blo 1663031 3744593 := bstep (se 2 (by rfl) ⟨1404222, by rfl⟩ : syracuseStep 3744593 = 2808445) B2808445
theorem B1663827 : Blo 1663031 1663827 := bstep (se 1 (by rfl) ⟨1247870, by rfl⟩ : syracuseStep 1663827 = 2495741) B2495741
theorem B1663843 : Blo 1663031 1663843 := bstep (se 1 (by rfl) ⟨1247882, by rfl⟩ : syracuseStep 1663843 = 2495765) B2495765
theorem B3744611 : Blo 1663031 3744611 := bstep (se 1 (by rfl) ⟨2808458, by rfl⟩ : syracuseStep 3744611 = 5616917) B5616917
theorem B1663859 : Blo 1663031 1663859 := bstep (se 1 (by rfl) ⟨1247894, by rfl⟩ : syracuseStep 1663859 = 2495789) B2495789
theorem B1663875 : Blo 1663031 1663875 := bstep (se 1 (by rfl) ⟨1247906, by rfl⟩ : syracuseStep 1663875 = 2495813) B2495813
theorem B4498307 : Blo 1663031 4498307 := bstep (se 1 (by rfl) ⟨3373730, by rfl⟩ : syracuseStep 4498307 = 6747461) B6747461
theorem B25617293 : Blo 1663031 25617293 := bstep (se 3 (by rfl) ⟨4803242, by rfl⟩ : syracuseStep 25617293 = 9606485) B9606485
theorem B1663891 : Blo 1663031 1663891 := bstep (se 1 (by rfl) ⟨1247918, by rfl⟩ : syracuseStep 1663891 = 2495837) B2495837
theorem B1663907 : Blo 1663031 1663907 := bstep (se 1 (by rfl) ⟨1247930, by rfl⟩ : syracuseStep 1663907 = 2495861) B2495861
theorem B1663923 : Blo 1663031 1663923 := bstep (se 1 (by rfl) ⟨1247942, by rfl⟩ : syracuseStep 1663923 = 2495885) B2495885
theorem B1663939 : Blo 1663031 1663939 := bstep (se 1 (by rfl) ⟨1247954, by rfl⟩ : syracuseStep 1663939 = 2495909) B2495909
theorem B1663955 : Blo 1663031 1663955 := bstep (se 1 (by rfl) ⟨1247966, by rfl⟩ : syracuseStep 1663955 = 2495933) B2495933
theorem B1663971 : Blo 1663031 1663971 := bstep (se 1 (by rfl) ⟨1247978, by rfl⟩ : syracuseStep 1663971 = 2495957) B2495957
theorem B1663987 : Blo 1663031 1663987 := bstep (se 1 (by rfl) ⟨1247990, by rfl⟩ : syracuseStep 1663987 = 2495981) B2495981
theorem B1664003 : Blo 1663031 1664003 := bstep (se 1 (by rfl) ⟨1248002, by rfl⟩ : syracuseStep 1664003 = 2496005) B2496005
theorem B1664019 : Blo 1663031 1664019 := bstep (se 1 (by rfl) ⟨1248014, by rfl⟩ : syracuseStep 1664019 = 2496029) B2496029
theorem B4211747 : Blo 1663031 4211747 := bstep (se 1 (by rfl) ⟨3158810, by rfl⟩ : syracuseStep 4211747 = 6317621) B6317621
theorem B1664035 : Blo 1663031 1664035 := bstep (se 1 (by rfl) ⟨1248026, by rfl⟩ : syracuseStep 1664035 = 2496053) B2496053
theorem B1664051 : Blo 1663031 1664051 := bstep (se 1 (by rfl) ⟨1248038, by rfl⟩ : syracuseStep 1664051 = 2496077) B2496077
theorem B4867139 : Blo 1663031 4867139 := bstep (se 1 (by rfl) ⟨3650354, by rfl⟩ : syracuseStep 4867139 = 7300709) B7300709
theorem B1664067 : Blo 1663031 1664067 := bstep (se 1 (by rfl) ⟨1248050, by rfl⟩ : syracuseStep 1664067 = 2496101) B2496101
theorem B5334083 : Blo 1663031 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B1664083 : Blo 1663031 1664083 := bstep (se 1 (by rfl) ⟨1248062, by rfl⟩ : syracuseStep 1664083 = 2496125) B2496125
theorem B1664099 : Blo 1663031 1664099 := bstep (se 1 (by rfl) ⟨1248074, by rfl⟩ : syracuseStep 1664099 = 2496149) B2496149
theorem B21333091 : Blo 1663031 21333091 := bstep (se 1 (by rfl) ⟨15999818, by rfl⟩ : syracuseStep 21333091 = 31999637) B31999637
theorem B3744881 : Blo 1663031 3744881 := bstep (se 2 (by rfl) ⟨1404330, by rfl⟩ : syracuseStep 3744881 = 2808661) B2808661
theorem B1664115 : Blo 1663031 1664115 := bstep (se 1 (by rfl) ⟨1248086, by rfl⟩ : syracuseStep 1664115 = 2496173) B2496173
theorem B1664131 : Blo 1663031 1664131 := bstep (se 1 (by rfl) ⟨1248098, by rfl⟩ : syracuseStep 1664131 = 2496197) B2496197
theorem B3744899 : Blo 1663031 3744899 := bstep (se 1 (by rfl) ⟨2808674, by rfl⟩ : syracuseStep 3744899 = 5617349) B5617349
theorem B8422541 : Blo 1663031 8422541 := bstep (se 3 (by rfl) ⟨1579226, by rfl⟩ : syracuseStep 8422541 = 3158453) B3158453
theorem B1664147 : Blo 1663031 1664147 := bstep (se 1 (by rfl) ⟨1248110, by rfl⟩ : syracuseStep 1664147 = 2496221) B2496221
theorem B1664163 : Blo 1663031 1664163 := bstep (se 1 (by rfl) ⟨1248122, by rfl⟩ : syracuseStep 1664163 = 2496245) B2496245
theorem B4736177 : Blo 1663031 4736177 := bstep (se 2 (by rfl) ⟨1776066, by rfl⟩ : syracuseStep 4736177 = 3552133) B3552133
theorem B1664179 : Blo 1663031 1664179 := bstep (se 1 (by rfl) ⟨1248134, by rfl⟩ : syracuseStep 1664179 = 2496269) B2496269
theorem B1664195 : Blo 1663031 1664195 := bstep (se 1 (by rfl) ⟨1248146, by rfl⟩ : syracuseStep 1664195 = 2496293) B2496293
theorem B1664211 : Blo 1663031 1664211 := bstep (se 1 (by rfl) ⟨1248158, by rfl⟩ : syracuseStep 1664211 = 2496317) B2496317
theorem B4211939 : Blo 1663031 4211939 := bstep (se 1 (by rfl) ⟨3158954, by rfl⟩ : syracuseStep 4211939 = 6317909) B6317909
theorem B1664227 : Blo 1663031 1664227 := bstep (se 1 (by rfl) ⟨1248170, by rfl⟩ : syracuseStep 1664227 = 2496341) B2496341
theorem B1664243 : Blo 1663031 1664243 := bstep (se 1 (by rfl) ⟨1248182, by rfl⟩ : syracuseStep 1664243 = 2496365) B2496365
theorem B1664259 : Blo 1663031 1664259 := bstep (se 1 (by rfl) ⟨1248194, by rfl⟩ : syracuseStep 1664259 = 2496389) B2496389
theorem B5612813 : Blo 1663031 5612813 := bstep (se 3 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 5612813 = 2104805) B2104805
theorem B1664275 : Blo 1663031 1664275 := bstep (se 1 (by rfl) ⟨1248206, by rfl⟩ : syracuseStep 1664275 = 2496413) B2496413
theorem B2106643 : Blo 1663031 2106643 := bstep (se 1 (by rfl) ⟨1579982, by rfl⟩ : syracuseStep 2106643 = 3159965) B3159965
theorem B1664291 : Blo 1663031 1664291 := bstep (se 1 (by rfl) ⟨1248218, by rfl⟩ : syracuseStep 1664291 = 2496437) B2496437
theorem B1664307 : Blo 1663031 1664307 := bstep (se 1 (by rfl) ⟨1248230, by rfl⟩ : syracuseStep 1664307 = 2496461) B2496461
theorem B5612867 : Blo 1663031 5612867 := bstep (se 1 (by rfl) ⟨4209650, by rfl⟩ : syracuseStep 5612867 = 8419301) B8419301
theorem B1664323 : Blo 1663031 1664323 := bstep (se 1 (by rfl) ⟨1248242, by rfl⟩ : syracuseStep 1664323 = 2496485) B2496485
theorem B7103821 : Blo 1663031 7103821 := bstep (se 3 (by rfl) ⟨1331966, by rfl⟩ : syracuseStep 7103821 = 2663933) B2663933
theorem B1664339 : Blo 1663031 1664339 := bstep (se 1 (by rfl) ⟨1248254, by rfl⟩ : syracuseStep 1664339 = 2496509) B2496509
theorem B1664355 : Blo 1663031 1664355 := bstep (se 1 (by rfl) ⟨1248266, by rfl⟩ : syracuseStep 1664355 = 2496533) B2496533
theorem B1664371 : Blo 1663031 1664371 := bstep (se 1 (by rfl) ⟨1248278, by rfl⟩ : syracuseStep 1664371 = 2496557) B2496557
theorem B2106739 : Blo 1663031 2106739 := bstep (se 1 (by rfl) ⟨1580054, by rfl⟩ : syracuseStep 2106739 = 3160109) B3160109
theorem B1664387 : Blo 1663031 1664387 := bstep (se 1 (by rfl) ⟨1248290, by rfl⟩ : syracuseStep 1664387 = 2496581) B2496581
theorem B6317453 : Blo 1663031 6317453 := bstep (se 3 (by rfl) ⟨1184522, by rfl⟩ : syracuseStep 6317453 = 2369045) B2369045
theorem B3745169 : Blo 1663031 3745169 := bstep (se 2 (by rfl) ⟨1404438, by rfl⟩ : syracuseStep 3745169 = 2808877) B2808877
theorem B1664403 : Blo 1663031 1664403 := bstep (se 1 (by rfl) ⟨1248302, by rfl⟩ : syracuseStep 1664403 = 2496605) B2496605
theorem B2368931 : Blo 1663031 2368931 := bstep (se 1 (by rfl) ⟨1776698, by rfl⟩ : syracuseStep 2368931 = 3553397) B3553397
theorem B1664419 : Blo 1663031 1664419 := bstep (se 1 (by rfl) ⟨1248314, by rfl⟩ : syracuseStep 1664419 = 2496629) B2496629
theorem B3745187 : Blo 1663031 3745187 := bstep (se 1 (by rfl) ⟨2808890, by rfl⟩ : syracuseStep 3745187 = 5617781) B5617781
theorem B1664435 : Blo 1663031 1664435 := bstep (se 1 (by rfl) ⟨1248326, by rfl⟩ : syracuseStep 1664435 = 2496653) B2496653
theorem B1664451 : Blo 1663031 1664451 := bstep (se 1 (by rfl) ⟨1248338, by rfl⟩ : syracuseStep 1664451 = 2496677) B2496677
theorem B1664467 : Blo 1663031 1664467 := bstep (se 1 (by rfl) ⟨1248350, by rfl⟩ : syracuseStep 1664467 = 2496701) B2496701
theorem B1664483 : Blo 1663031 1664483 := bstep (se 1 (by rfl) ⟨1248362, by rfl⟩ : syracuseStep 1664483 = 2496725) B2496725
theorem B10118641 : Blo 1663031 10118641 := bstep (se 2 (by rfl) ⟨3794490, by rfl⟩ : syracuseStep 10118641 = 7588981) B7588981
theorem B1664499 : Blo 1663031 1664499 := bstep (se 1 (by rfl) ⟨1248374, by rfl⟩ : syracuseStep 1664499 = 2496749) B2496749
theorem B1664515 : Blo 1663031 1664515 := bstep (se 1 (by rfl) ⟨1248386, by rfl⟩ : syracuseStep 1664515 = 2496773) B2496773
theorem B1664531 : Blo 1663031 1664531 := bstep (se 1 (by rfl) ⟨1248398, by rfl⟩ : syracuseStep 1664531 = 2496797) B2496797
theorem B2663971 : Blo 1663031 2663971 := bstep (se 1 (by rfl) ⟨1997978, by rfl⟩ : syracuseStep 2663971 = 3995957) B3995957
theorem B1664547 : Blo 1663031 1664547 := bstep (se 1 (by rfl) ⟨1248410, by rfl⟩ : syracuseStep 1664547 = 2496821) B2496821
theorem B7587377 : Blo 1663031 7587377 := bstep (se 2 (by rfl) ⟨2845266, by rfl⟩ : syracuseStep 7587377 = 5690533) B5690533
theorem B1664563 : Blo 1663031 1664563 := bstep (se 1 (by rfl) ⟨1248422, by rfl⟩ : syracuseStep 1664563 = 2496845) B2496845
theorem B1664579 : Blo 1663031 1664579 := bstep (se 1 (by rfl) ⟨1248434, by rfl⟩ : syracuseStep 1664579 = 2496869) B2496869
theorem B4802125 : Blo 1663031 4802125 := bstep (se 3 (by rfl) ⟨900398, by rfl⟩ : syracuseStep 4802125 = 1800797) B1800797
theorem B2664017 : Blo 1663031 2664017 := bstep (se 2 (by rfl) ⟨999006, by rfl⟩ : syracuseStep 2664017 = 1998013) B1998013
theorem B5613137 : Blo 1663031 5613137 := bstep (se 2 (by rfl) ⟨2104926, by rfl⟩ : syracuseStep 5613137 = 4209853) B4209853
theorem B1664595 : Blo 1663031 1664595 := bstep (se 1 (by rfl) ⟨1248446, by rfl⟩ : syracuseStep 1664595 = 2496893) B2496893
theorem B1664611 : Blo 1663031 1664611 := bstep (se 1 (by rfl) ⟨1248458, by rfl⟩ : syracuseStep 1664611 = 2496917) B2496917
theorem B11388529 : Blo 1663031 11388529 := bstep (se 2 (by rfl) ⟨4270698, by rfl⟩ : syracuseStep 11388529 = 8541397) B8541397
theorem B1664627 : Blo 1663031 1664627 := bstep (se 1 (by rfl) ⟨1248470, by rfl⟩ : syracuseStep 1664627 = 2496941) B2496941
theorem B1664643 : Blo 1663031 1664643 := bstep (se 1 (by rfl) ⟨1248482, by rfl⟩ : syracuseStep 1664643 = 2496965) B2496965
theorem B1664659 : Blo 1663031 1664659 := bstep (se 1 (by rfl) ⟨1248494, by rfl⟩ : syracuseStep 1664659 = 2496989) B2496989
theorem B1664675 : Blo 1663031 1664675 := bstep (se 1 (by rfl) ⟨1248506, by rfl⟩ : syracuseStep 1664675 = 2497013) B2497013
theorem B3745457 : Blo 1663031 3745457 := bstep (se 2 (by rfl) ⟨1404546, by rfl⟩ : syracuseStep 3745457 = 2809093) B2809093
theorem B1664691 : Blo 1663031 1664691 := bstep (se 1 (by rfl) ⟨1248518, by rfl⟩ : syracuseStep 1664691 = 2497037) B2497037
theorem B2401987 : Blo 1663031 2401987 := bstep (se 1 (by rfl) ⟨1801490, by rfl⟩ : syracuseStep 2401987 = 3602981) B3602981
theorem B3745475 : Blo 1663031 3745475 := bstep (se 1 (by rfl) ⟨2809106, by rfl⟩ : syracuseStep 3745475 = 5618213) B5618213
theorem B1664707 : Blo 1663031 1664707 := bstep (se 1 (by rfl) ⟨1248530, by rfl⟩ : syracuseStep 1664707 = 2497061) B2497061
theorem B1664723 : Blo 1663031 1664723 := bstep (se 1 (by rfl) ⟨1248542, by rfl⟩ : syracuseStep 1664723 = 2497085) B2497085
theorem B1664739 : Blo 1663031 1664739 := bstep (se 1 (by rfl) ⟨1248554, by rfl⟩ : syracuseStep 1664739 = 2497109) B2497109
theorem B1664755 : Blo 1663031 1664755 := bstep (se 1 (by rfl) ⟨1248566, by rfl⟩ : syracuseStep 1664755 = 2497133) B2497133
theorem B1664771 : Blo 1663031 1664771 := bstep (se 1 (by rfl) ⟨1248578, by rfl⟩ : syracuseStep 1664771 = 2497157) B2497157
theorem B5998349 : Blo 1663031 5998349 := bstep (se 3 (by rfl) ⟨1124690, by rfl⟩ : syracuseStep 5998349 = 2249381) B2249381
theorem B1664787 : Blo 1663031 1664787 := bstep (se 1 (by rfl) ⟨1248590, by rfl⟩ : syracuseStep 1664787 = 2497181) B2497181
theorem B1664803 : Blo 1663031 1664803 := bstep (se 1 (by rfl) ⟨1248602, by rfl⟩ : syracuseStep 1664803 = 2497205) B2497205
theorem B1664819 : Blo 1663031 1664819 := bstep (se 1 (by rfl) ⟨1248614, by rfl⟩ : syracuseStep 1664819 = 2497229) B2497229
theorem B1664835 : Blo 1663031 1664835 := bstep (se 1 (by rfl) ⟨1248626, by rfl⟩ : syracuseStep 1664835 = 2497253) B2497253
theorem B1664851 : Blo 1663031 1664851 := bstep (se 1 (by rfl) ⟨1248638, by rfl⟩ : syracuseStep 1664851 = 2497277) B2497277
theorem B1664867 : Blo 1663031 1664867 := bstep (se 1 (by rfl) ⟨1248650, by rfl⟩ : syracuseStep 1664867 = 2497301) B2497301
theorem B2107235 : Blo 1663031 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B1664883 : Blo 1663031 1664883 := bstep (se 1 (by rfl) ⟨1248662, by rfl⟩ : syracuseStep 1664883 = 2497325) B2497325
theorem B1664899 : Blo 1663031 1664899 := bstep (se 1 (by rfl) ⟨1248674, by rfl⟩ : syracuseStep 1664899 = 2497349) B2497349
theorem B9480077 : Blo 1663031 9480077 := bstep (se 3 (by rfl) ⟨1777514, by rfl⟩ : syracuseStep 9480077 = 3555029) B3555029
theorem B1664915 : Blo 1663031 1664915 := bstep (se 1 (by rfl) ⟨1248686, by rfl⟩ : syracuseStep 1664915 = 2497373) B2497373
theorem B1664931 : Blo 1663031 1664931 := bstep (se 1 (by rfl) ⟨1248698, by rfl⟩ : syracuseStep 1664931 = 2497397) B2497397
theorem B1664947 : Blo 1663031 1664947 := bstep (se 1 (by rfl) ⟨1248710, by rfl⟩ : syracuseStep 1664947 = 2497421) B2497421
theorem B1664963 : Blo 1663031 1664963 := bstep (se 1 (by rfl) ⟨1248722, by rfl⟩ : syracuseStep 1664963 = 2497445) B2497445
theorem B3745745 : Blo 1663031 3745745 := bstep (se 2 (by rfl) ⟨1404654, by rfl⟩ : syracuseStep 3745745 = 2809309) B2809309
theorem B1664979 : Blo 1663031 1664979 := bstep (se 1 (by rfl) ⟨1248734, by rfl⟩ : syracuseStep 1664979 = 2497469) B2497469
theorem B3745763 : Blo 1663031 3745763 := bstep (se 1 (by rfl) ⟨2809322, by rfl⟩ : syracuseStep 3745763 = 5618645) B5618645
theorem B1664995 : Blo 1663031 1664995 := bstep (se 1 (by rfl) ⟨1248746, by rfl⟩ : syracuseStep 1664995 = 2497493) B2497493
theorem B1665011 : Blo 1663031 1665011 := bstep (se 1 (by rfl) ⟨1248758, by rfl⟩ : syracuseStep 1665011 = 2497517) B2497517
theorem B1665027 : Blo 1663031 1665027 := bstep (se 1 (by rfl) ⟨1248770, by rfl⟩ : syracuseStep 1665027 = 2497541) B2497541
theorem B12642317 : Blo 1663031 12642317 := bstep (se 3 (by rfl) ⟨2370434, by rfl⟩ : syracuseStep 12642317 = 4740869) B4740869
theorem B2369569 : Blo 1663031 2369569 := bstep (se 2 (by rfl) ⟨888588, by rfl⟩ : syracuseStep 2369569 = 1777177) B1777177
theorem B5613677 : Blo 1663031 5613677 := bstep (se 3 (by rfl) ⟨1052564, by rfl⟩ : syracuseStep 5613677 = 2105129) B2105129
theorem B4737133 : Blo 1663031 4737133 := bstep (se 3 (by rfl) ⟨888212, by rfl⟩ : syracuseStep 4737133 = 1776425) B1776425
theorem B4212881 : Blo 1663031 4212881 := bstep (se 2 (by rfl) ⟨1579830, by rfl⟩ : syracuseStep 4212881 = 3159661) B3159661
theorem B2369683 : Blo 1663031 2369683 := bstep (se 1 (by rfl) ⟨1777262, by rfl⟩ : syracuseStep 2369683 = 3554525) B3554525
theorem B5613731 : Blo 1663031 5613731 := bstep (se 1 (by rfl) ⟨4210298, by rfl⟩ : syracuseStep 5613731 = 8420597) B8420597
theorem B4212931 : Blo 1663031 4212931 := bstep (se 1 (by rfl) ⟨3159698, by rfl⟩ : syracuseStep 4212931 = 6319397) B6319397
theorem B3746033 : Blo 1663031 3746033 := bstep (se 2 (by rfl) ⟨1404762, by rfl⟩ : syracuseStep 3746033 = 2809525) B2809525
theorem B3746051 : Blo 1663031 3746051 := bstep (se 1 (by rfl) ⟨2809538, by rfl⟩ : syracuseStep 3746051 = 5619077) B5619077
theorem B9472261 : Blo 1663031 9472261 := bstep (se 4 (by rfl) ⟨888024, by rfl⟩ : syracuseStep 9472261 = 1776049) B1776049
theorem B3901745 : Blo 1663031 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B4737361 : Blo 1663031 4737361 := bstep (se 2 (by rfl) ⟨1776510, by rfl⟩ : syracuseStep 4737361 = 3553021) B3553021
theorem B4213073 : Blo 1663031 4213073 := bstep (se 2 (by rfl) ⟨1579902, by rfl⟩ : syracuseStep 4213073 = 3159805) B3159805
theorem B4499821 : Blo 1663031 4499821 := bstep (se 3 (by rfl) ⟨843716, by rfl⟩ : syracuseStep 4499821 = 1687433) B1687433
theorem B5614001 : Blo 1663031 5614001 := bstep (se 2 (by rfl) ⟨2105250, by rfl⟩ : syracuseStep 5614001 = 4210501) B4210501
theorem B51243461 : Blo 1663031 51243461 := bstep (se 4 (by rfl) ⟨4804074, by rfl⟩ : syracuseStep 51243461 = 9608149) B9608149
theorem B4737521 : Blo 1663031 4737521 := bstep (se 2 (by rfl) ⟨1776570, by rfl⟩ : syracuseStep 4737521 = 3553141) B3553141
theorem B3746321 : Blo 1663031 3746321 := bstep (se 2 (by rfl) ⟨1404870, by rfl⟩ : syracuseStep 3746321 = 2809741) B2809741
theorem B4737635 : Blo 1663031 4737635 := bstep (se 1 (by rfl) ⟨3553226, by rfl⟩ : syracuseStep 4737635 = 7106453) B7106453
theorem B7998065 : Blo 1663031 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B86502001 : Blo 1663031 86502001 := bstep (se 2 (by rfl) ⟨32438250, by rfl⟩ : syracuseStep 86502001 = 64876501) B64876501
theorem B3795665 : Blo 1663031 3795665 := bstep (se 2 (by rfl) ⟨1423374, by rfl⟩ : syracuseStep 3795665 = 2846749) B2846749
theorem B5999345 : Blo 1663031 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B9481009 : Blo 1663031 9481009 := bstep (se 2 (by rfl) ⟨3555378, by rfl⟩ : syracuseStep 9481009 = 7110757) B7110757
theorem B10660805 : Blo 1663031 10660805 := bstep (se 4 (by rfl) ⟨999450, by rfl⟩ : syracuseStep 10660805 = 1998901) B1998901
theorem B5614541 : Blo 1663031 5614541 := bstep (se 3 (by rfl) ⟨1052726, by rfl⟩ : syracuseStep 5614541 = 2105453) B2105453
theorem B5401571 : Blo 1663031 5401571 := bstep (se 1 (by rfl) ⟨4051178, by rfl⟩ : syracuseStep 5401571 = 8102357) B8102357
theorem B5614595 : Blo 1663031 5614595 := bstep (se 1 (by rfl) ⟨4210946, by rfl⟩ : syracuseStep 5614595 = 8421893) B8421893
theorem B2665523 : Blo 1663031 2665523 := bstep (se 1 (by rfl) ⟨1999142, by rfl⟩ : syracuseStep 2665523 = 3998285) B3998285
theorem B1870915 : Blo 1663031 1870915 := bstep (se 1 (by rfl) ⟨1403186, by rfl⟩ : syracuseStep 1870915 = 2806373) B2806373
theorem B5057677 : Blo 1663031 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B1871059 : Blo 1663031 1871059 := bstep (se 1 (by rfl) ⟨1403294, by rfl⟩ : syracuseStep 1871059 = 2806589) B2806589
theorem B5614865 : Blo 1663031 5614865 := bstep (se 2 (by rfl) ⟨2105574, by rfl⟩ : syracuseStep 5614865 = 4211149) B4211149
theorem B4214065 : Blo 1663031 4214065 := bstep (se 2 (by rfl) ⟨1580274, by rfl⟩ : syracuseStep 4214065 = 3160549) B3160549
theorem B2665811 : Blo 1663031 2665811 := bstep (se 1 (by rfl) ⟨1999358, by rfl⟩ : syracuseStep 2665811 = 3998717) B3998717
theorem B1871203 : Blo 1663031 1871203 := bstep (se 1 (by rfl) ⟨1403402, by rfl⟩ : syracuseStep 1871203 = 2806805) B2806805
theorem B6319565 : Blo 1663031 6319565 := bstep (se 3 (by rfl) ⟨1184918, by rfl⟩ : syracuseStep 6319565 = 2369837) B2369837
theorem B1871347 : Blo 1663031 1871347 := bstep (se 1 (by rfl) ⟨1403510, by rfl⟩ : syracuseStep 1871347 = 2807021) B2807021
theorem B4214339 : Blo 1663031 4214339 := bstep (se 1 (by rfl) ⟨3160754, by rfl⟩ : syracuseStep 4214339 = 6321509) B6321509
theorem B4738637 : Blo 1663031 4738637 := bstep (se 3 (by rfl) ⟨888494, by rfl⟩ : syracuseStep 4738637 = 1776989) B1776989
theorem B1871491 : Blo 1663031 1871491 := bstep (se 1 (by rfl) ⟨1403618, by rfl⟩ : syracuseStep 1871491 = 2807237) B2807237
theorem B7999181 : Blo 1663031 7999181 := bstep (se 3 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 7999181 = 2999693) B2999693
theorem B4738819 : Blo 1663031 4738819 := bstep (se 1 (by rfl) ⟨3554114, by rfl⟩ : syracuseStep 4738819 = 7108229) B7108229
theorem B4214531 : Blo 1663031 4214531 := bstep (se 1 (by rfl) ⟨3160898, by rfl⟩ : syracuseStep 4214531 = 6321797) B6321797
theorem B1871635 : Blo 1663031 1871635 := bstep (se 1 (by rfl) ⟨1403726, by rfl⟩ : syracuseStep 1871635 = 2807453) B2807453
theorem B5615405 : Blo 1663031 5615405 := bstep (se 3 (by rfl) ⟨1052888, by rfl⟩ : syracuseStep 5615405 = 2105777) B2105777
theorem B5615459 : Blo 1663031 5615459 := bstep (se 1 (by rfl) ⟨4211594, by rfl⟩ : syracuseStep 5615459 = 8423189) B8423189
theorem B10801037 : Blo 1663031 10801037 := bstep (se 3 (by rfl) ⟨2025194, by rfl⟩ : syracuseStep 10801037 = 4050389) B4050389
theorem B1871779 : Blo 1663031 1871779 := bstep (se 1 (by rfl) ⟨1403834, by rfl⟩ : syracuseStep 1871779 = 2807669) B2807669
theorem B4738979 : Blo 1663031 4738979 := bstep (se 1 (by rfl) ⟨3554234, by rfl⟩ : syracuseStep 4738979 = 7108469) B7108469
theorem B3157937 : Blo 1663031 3157937 := bstep (se 2 (by rfl) ⟨1184226, by rfl⟩ : syracuseStep 3157937 = 2368453) B2368453
theorem B8425457 : Blo 1663031 8425457 := bstep (se 2 (by rfl) ⟨3159546, by rfl⟩ : syracuseStep 8425457 = 6319093) B6319093
theorem B1871923 : Blo 1663031 1871923 := bstep (se 1 (by rfl) ⟨1403942, by rfl⟩ : syracuseStep 1871923 = 2807885) B2807885
theorem B2494547 : Blo 1663031 2494547 := bstep (se 1 (by rfl) ⟨1870910, by rfl⟩ : syracuseStep 2494547 = 3741821) B3741821
theorem B2494577 : Blo 1663031 2494577 := bstep (se 2 (by rfl) ⟨935466, by rfl⟩ : syracuseStep 2494577 = 1870933) B1870933
theorem B5615729 : Blo 1663031 5615729 := bstep (se 2 (by rfl) ⟨2105898, by rfl⟩ : syracuseStep 5615729 = 4211797) B4211797
theorem B2666611 : Blo 1663031 2666611 := bstep (se 1 (by rfl) ⟨1999958, by rfl⟩ : syracuseStep 2666611 = 3999917) B3999917
theorem B2494595 : Blo 1663031 2494595 := bstep (se 1 (by rfl) ⟨1870946, by rfl⟩ : syracuseStep 2494595 = 3741893) B3741893
theorem B2494625 : Blo 1663031 2494625 := bstep (se 2 (by rfl) ⟨935484, by rfl⟩ : syracuseStep 2494625 = 1870969) B1870969
theorem B2494643 : Blo 1663031 2494643 := bstep (se 1 (by rfl) ⟨1870982, by rfl⟩ : syracuseStep 2494643 = 3741965) B3741965
theorem B1872067 : Blo 1663031 1872067 := bstep (se 1 (by rfl) ⟨1404050, by rfl⟩ : syracuseStep 1872067 = 2808101) B2808101
theorem B9474245 : Blo 1663031 9474245 := bstep (se 4 (by rfl) ⟨888210, by rfl⟩ : syracuseStep 9474245 = 1776421) B1776421
theorem B22212805 : Blo 1663031 22212805 := bstep (se 4 (by rfl) ⟨2082450, by rfl⟩ : syracuseStep 22212805 = 4164901) B4164901
theorem B2494673 : Blo 1663031 2494673 := bstep (se 2 (by rfl) ⟨935502, by rfl⟩ : syracuseStep 2494673 = 1871005) B1871005
theorem B2494691 : Blo 1663031 2494691 := bstep (se 1 (by rfl) ⟨1871018, by rfl⟩ : syracuseStep 2494691 = 3742037) B3742037
theorem B9482467 : Blo 1663031 9482467 := bstep (se 1 (by rfl) ⟨7111850, by rfl⟩ : syracuseStep 9482467 = 14223701) B14223701
theorem B6320369 : Blo 1663031 6320369 := bstep (se 2 (by rfl) ⟨2370138, by rfl⟩ : syracuseStep 6320369 = 4740277) B4740277
theorem B2494721 : Blo 1663031 2494721 := bstep (se 2 (by rfl) ⟨935520, by rfl⟩ : syracuseStep 2494721 = 1871041) B1871041
theorem B2666753 : Blo 1663031 2666753 := bstep (se 2 (by rfl) ⟨1000032, by rfl⟩ : syracuseStep 2666753 = 2000065) B2000065
theorem B2494739 : Blo 1663031 2494739 := bstep (se 1 (by rfl) ⟨1871054, by rfl⟩ : syracuseStep 2494739 = 3742109) B3742109
theorem B2666785 : Blo 1663031 2666785 := bstep (se 2 (by rfl) ⟨1000044, by rfl⟩ : syracuseStep 2666785 = 2000089) B2000089
theorem B2494769 : Blo 1663031 2494769 := bstep (se 2 (by rfl) ⟨935538, by rfl⟩ : syracuseStep 2494769 = 1871077) B1871077
theorem B9605425 : Blo 1663031 9605425 := bstep (se 2 (by rfl) ⟨3602034, by rfl⟩ : syracuseStep 9605425 = 7204069) B7204069
theorem B2494787 : Blo 1663031 2494787 := bstep (se 1 (by rfl) ⟨1871090, by rfl⟩ : syracuseStep 2494787 = 3742181) B3742181
theorem B12636485 : Blo 1663031 12636485 := bstep (se 4 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 12636485 = 2369341) B2369341
theorem B1872211 : Blo 1663031 1872211 := bstep (se 1 (by rfl) ⟨1404158, by rfl⟩ : syracuseStep 1872211 = 2808317) B2808317
theorem B2494817 : Blo 1663031 2494817 := bstep (se 2 (by rfl) ⟨935556, by rfl⟩ : syracuseStep 2494817 = 1871113) B1871113
theorem B2494835 : Blo 1663031 2494835 := bstep (se 1 (by rfl) ⟨1871126, by rfl⟩ : syracuseStep 2494835 = 3742253) B3742253
theorem B2494865 : Blo 1663031 2494865 := bstep (se 2 (by rfl) ⟨935574, by rfl⟩ : syracuseStep 2494865 = 1871149) B1871149
theorem B2494883 : Blo 1663031 2494883 := bstep (se 1 (by rfl) ⟨1871162, by rfl⟩ : syracuseStep 2494883 = 3742325) B3742325
theorem B2494913 : Blo 1663031 2494913 := bstep (se 2 (by rfl) ⟨935592, by rfl⟩ : syracuseStep 2494913 = 1871185) B1871185
theorem B2494931 : Blo 1663031 2494931 := bstep (se 1 (by rfl) ⟨1871198, by rfl⟩ : syracuseStep 2494931 = 3742397) B3742397
theorem B2847187 : Blo 1663031 2847187 := bstep (se 1 (by rfl) ⟨2135390, by rfl⟩ : syracuseStep 2847187 = 4270781) B4270781
theorem B1872355 : Blo 1663031 1872355 := bstep (se 1 (by rfl) ⟨1404266, by rfl⟩ : syracuseStep 1872355 = 2808533) B2808533
theorem B2494961 : Blo 1663031 2494961 := bstep (se 2 (by rfl) ⟨935610, by rfl⟩ : syracuseStep 2494961 = 1871221) B1871221
theorem B2494979 : Blo 1663031 2494979 := bstep (se 1 (by rfl) ⟨1871234, by rfl⟩ : syracuseStep 2494979 = 3742469) B3742469
theorem B2495009 : Blo 1663031 2495009 := bstep (se 2 (by rfl) ⟨935628, by rfl⟩ : syracuseStep 2495009 = 1871257) B1871257
theorem B2495027 : Blo 1663031 2495027 := bstep (se 1 (by rfl) ⟨1871270, by rfl⟩ : syracuseStep 2495027 = 3742541) B3742541
theorem B3551825 : Blo 1663031 3551825 := bstep (se 2 (by rfl) ⟨1331934, by rfl⟩ : syracuseStep 3551825 = 2663869) B2663869
theorem B2495057 : Blo 1663031 2495057 := bstep (se 2 (by rfl) ⟨935646, by rfl⟩ : syracuseStep 2495057 = 1871293) B1871293
theorem B3551843 : Blo 1663031 3551843 := bstep (se 1 (by rfl) ⟨2663882, by rfl⟩ : syracuseStep 3551843 = 5327765) B5327765
theorem B2495075 : Blo 1663031 2495075 := bstep (se 1 (by rfl) ⟨1871306, by rfl⟩ : syracuseStep 2495075 = 3742613) B3742613
theorem B1872499 : Blo 1663031 1872499 := bstep (se 1 (by rfl) ⟨1404374, by rfl⟩ : syracuseStep 1872499 = 2808749) B2808749
theorem B2495105 : Blo 1663031 2495105 := bstep (se 2 (by rfl) ⟨935664, by rfl⟩ : syracuseStep 2495105 = 1871329) B1871329
theorem B21320333 : Blo 1663031 21320333 := bstep (se 3 (by rfl) ⟨3997562, by rfl⟩ : syracuseStep 21320333 = 7995125) B7995125
theorem B5616269 : Blo 1663031 5616269 := bstep (se 3 (by rfl) ⟨1053050, by rfl⟩ : syracuseStep 5616269 = 2106101) B2106101
theorem B2495123 : Blo 1663031 2495123 := bstep (se 1 (by rfl) ⟨1871342, by rfl⟩ : syracuseStep 2495123 = 3742685) B3742685
theorem B2495153 : Blo 1663031 2495153 := bstep (se 2 (by rfl) ⟨935682, by rfl⟩ : syracuseStep 2495153 = 1871365) B1871365
theorem B2495171 : Blo 1663031 2495171 := bstep (se 1 (by rfl) ⟨1871378, by rfl⟩ : syracuseStep 2495171 = 3742757) B3742757
theorem B5616323 : Blo 1663031 5616323 := bstep (se 1 (by rfl) ⟨4212242, by rfl⟩ : syracuseStep 5616323 = 8424485) B8424485
theorem B2806481 : Blo 1663031 2806481 := bstep (se 2 (by rfl) ⟨1052430, by rfl⟩ : syracuseStep 2806481 = 2104861) B2104861
theorem B2495201 : Blo 1663031 2495201 := bstep (se 2 (by rfl) ⟨935700, by rfl⟩ : syracuseStep 2495201 = 1871401) B1871401
theorem B2495219 : Blo 1663031 2495219 := bstep (se 1 (by rfl) ⟨1871414, by rfl⟩ : syracuseStep 2495219 = 3742829) B3742829
theorem B1872643 : Blo 1663031 1872643 := bstep (se 1 (by rfl) ⟨1404482, by rfl⟩ : syracuseStep 1872643 = 2808965) B2808965
theorem B2495249 : Blo 1663031 2495249 := bstep (se 2 (by rfl) ⟨935718, by rfl⟩ : syracuseStep 2495249 = 1871437) B1871437
theorem B2495267 : Blo 1663031 2495267 := bstep (se 1 (by rfl) ⟨1871450, by rfl⟩ : syracuseStep 2495267 = 3742901) B3742901
theorem B3158833 : Blo 1663031 3158833 := bstep (se 2 (by rfl) ⟨1184562, by rfl⟩ : syracuseStep 3158833 = 2369125) B2369125
theorem B2495297 : Blo 1663031 2495297 := bstep (se 2 (by rfl) ⟨935736, by rfl⟩ : syracuseStep 2495297 = 1871473) B1871473
theorem B2806609 : Blo 1663031 2806609 := bstep (se 2 (by rfl) ⟨1052478, by rfl⟩ : syracuseStep 2806609 = 2104957) B2104957
theorem B2495315 : Blo 1663031 2495315 := bstep (se 1 (by rfl) ⟨1871486, by rfl⟩ : syracuseStep 2495315 = 3742973) B3742973
theorem B2495345 : Blo 1663031 2495345 := bstep (se 2 (by rfl) ⟨935754, by rfl⟩ : syracuseStep 2495345 = 1871509) B1871509
theorem B2806643 : Blo 1663031 2806643 := bstep (se 1 (by rfl) ⟨2104982, by rfl⟩ : syracuseStep 2806643 = 4209965) B4209965
theorem B2495363 : Blo 1663031 2495363 := bstep (se 1 (by rfl) ⟨1871522, by rfl⟩ : syracuseStep 2495363 = 3743045) B3743045
theorem B6321037 : Blo 1663031 6321037 := bstep (se 3 (by rfl) ⟨1185194, by rfl⟩ : syracuseStep 6321037 = 2370389) B2370389
theorem B1872787 : Blo 1663031 1872787 := bstep (se 1 (by rfl) ⟨1404590, by rfl⟩ : syracuseStep 1872787 = 2809181) B2809181
theorem B2495393 : Blo 1663031 2495393 := bstep (se 2 (by rfl) ⟨935772, by rfl⟩ : syracuseStep 2495393 = 1871545) B1871545
theorem B2495411 : Blo 1663031 2495411 := bstep (se 1 (by rfl) ⟨1871558, by rfl⟩ : syracuseStep 2495411 = 3743117) B3743117
theorem B2495441 : Blo 1663031 2495441 := bstep (se 2 (by rfl) ⟨935790, by rfl⟩ : syracuseStep 2495441 = 1871581) B1871581
theorem B3158993 : Blo 1663031 3158993 := bstep (se 2 (by rfl) ⟨1184622, by rfl⟩ : syracuseStep 3158993 = 2369245) B2369245
theorem B5616593 : Blo 1663031 5616593 := bstep (se 2 (by rfl) ⟨2106222, by rfl⟩ : syracuseStep 5616593 = 4212445) B4212445
theorem B4740049 : Blo 1663031 4740049 := bstep (se 2 (by rfl) ⟨1777518, by rfl⟩ : syracuseStep 4740049 = 3555037) B3555037
theorem B2495459 : Blo 1663031 2495459 := bstep (se 1 (by rfl) ⟨1871594, by rfl⟩ : syracuseStep 2495459 = 3743189) B3743189
theorem B2806771 : Blo 1663031 2806771 := bstep (se 1 (by rfl) ⟨2105078, by rfl⟩ : syracuseStep 2806771 = 4210157) B4210157
theorem B2495489 : Blo 1663031 2495489 := bstep (se 2 (by rfl) ⟨935808, by rfl⟩ : syracuseStep 2495489 = 1871617) B1871617
theorem B8991749 : Blo 1663031 8991749 := bstep (se 4 (by rfl) ⟨842976, by rfl⟩ : syracuseStep 8991749 = 1685953) B1685953
theorem B8000525 : Blo 1663031 8000525 := bstep (se 3 (by rfl) ⟨1500098, by rfl⟩ : syracuseStep 8000525 = 3000197) B3000197
theorem B2495507 : Blo 1663031 2495507 := bstep (se 1 (by rfl) ⟨1871630, by rfl⟩ : syracuseStep 2495507 = 3743261) B3743261
theorem B1872931 : Blo 1663031 1872931 := bstep (se 1 (by rfl) ⟨1404698, by rfl⟩ : syracuseStep 1872931 = 2809397) B2809397
theorem B2495537 : Blo 1663031 2495537 := bstep (se 2 (by rfl) ⟨935826, by rfl⟩ : syracuseStep 2495537 = 1871653) B1871653
theorem B2495555 : Blo 1663031 2495555 := bstep (se 1 (by rfl) ⟨1871666, by rfl⟩ : syracuseStep 2495555 = 3743333) B3743333
theorem B2495585 : Blo 1663031 2495585 := bstep (se 2 (by rfl) ⟨935844, by rfl⟩ : syracuseStep 2495585 = 1871689) B1871689
theorem B2495603 : Blo 1663031 2495603 := bstep (se 1 (by rfl) ⟨1871702, by rfl⟩ : syracuseStep 2495603 = 3743405) B3743405
theorem B2806913 : Blo 1663031 2806913 := bstep (se 2 (by rfl) ⟨1052592, by rfl⟩ : syracuseStep 2806913 = 2105185) B2105185
theorem B2495633 : Blo 1663031 2495633 := bstep (se 2 (by rfl) ⟨935862, by rfl⟩ : syracuseStep 2495633 = 1871725) B1871725
theorem B2495651 : Blo 1663031 2495651 := bstep (se 1 (by rfl) ⟨1871738, by rfl⟩ : syracuseStep 2495651 = 3743477) B3743477
theorem B1873075 : Blo 1663031 1873075 := bstep (se 1 (by rfl) ⟨1404806, by rfl⟩ : syracuseStep 1873075 = 2809613) B2809613
theorem B2495681 : Blo 1663031 2495681 := bstep (se 2 (by rfl) ⟨935880, by rfl⟩ : syracuseStep 2495681 = 1871761) B1871761
theorem B2495699 : Blo 1663031 2495699 := bstep (se 1 (by rfl) ⟨1871774, by rfl⟩ : syracuseStep 2495699 = 3743549) B3743549
theorem B18945251 : Blo 1663031 18945251 := bstep (se 1 (by rfl) ⟨14208938, by rfl⟩ : syracuseStep 18945251 = 28417877) B28417877
theorem B2495729 : Blo 1663031 2495729 := bstep (se 2 (by rfl) ⟨935898, by rfl⟩ : syracuseStep 2495729 = 1871797) B1871797
theorem B2807041 : Blo 1663031 2807041 := bstep (se 2 (by rfl) ⟨1052640, by rfl⟩ : syracuseStep 2807041 = 2105281) B2105281
theorem B2495747 : Blo 1663031 2495747 := bstep (se 1 (by rfl) ⟨1871810, by rfl⟩ : syracuseStep 2495747 = 3743621) B3743621
theorem B2495777 : Blo 1663031 2495777 := bstep (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) B1871833
theorem B2807075 : Blo 1663031 2807075 := bstep (se 1 (by rfl) ⟨2105306, by rfl⟩ : syracuseStep 2807075 = 4210613) B4210613
theorem B5330225 : Blo 1663031 5330225 := bstep (se 2 (by rfl) ⟨1998834, by rfl⟩ : syracuseStep 5330225 = 3997669) B3997669
theorem B2495795 : Blo 1663031 2495795 := bstep (se 1 (by rfl) ⟨1871846, by rfl⟩ : syracuseStep 2495795 = 3743693) B3743693
theorem B2495825 : Blo 1663031 2495825 := bstep (se 2 (by rfl) ⟨935934, by rfl⟩ : syracuseStep 2495825 = 1871869) B1871869
theorem B2495843 : Blo 1663031 2495843 := bstep (se 1 (by rfl) ⟨1871882, by rfl⟩ : syracuseStep 2495843 = 3743765) B3743765
theorem B3159395 : Blo 1663031 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B2495873 : Blo 1663031 2495873 := bstep (se 2 (by rfl) ⟨935952, by rfl⟩ : syracuseStep 2495873 = 1871905) B1871905
theorem B2495891 : Blo 1663031 2495891 := bstep (se 1 (by rfl) ⟨1871918, by rfl⟩ : syracuseStep 2495891 = 3743837) B3743837
theorem B2807203 : Blo 1663031 2807203 := bstep (se 1 (by rfl) ⟨2105402, by rfl⟩ : syracuseStep 2807203 = 4210805) B4210805
theorem B8426915 : Blo 1663031 8426915 := bstep (se 1 (by rfl) ⟨6320186, by rfl⟩ : syracuseStep 8426915 = 12640373) B12640373
theorem B2495921 : Blo 1663031 2495921 := bstep (se 2 (by rfl) ⟨935970, by rfl⟩ : syracuseStep 2495921 = 1871941) B1871941
theorem B2495939 : Blo 1663031 2495939 := bstep (se 1 (by rfl) ⟨1871954, by rfl⟩ : syracuseStep 2495939 = 3743909) B3743909
theorem B2495969 : Blo 1663031 2495969 := bstep (se 2 (by rfl) ⟨935988, by rfl⟩ : syracuseStep 2495969 = 1871977) B1871977
theorem B5617133 : Blo 1663031 5617133 := bstep (se 3 (by rfl) ⟨1053212, by rfl⟩ : syracuseStep 5617133 = 2106425) B2106425
theorem B2528753 : Blo 1663031 2528753 := bstep (se 2 (by rfl) ⟨948282, by rfl⟩ : syracuseStep 2528753 = 1896565) B1896565
theorem B2495987 : Blo 1663031 2495987 := bstep (se 1 (by rfl) ⟨1871990, by rfl⟩ : syracuseStep 2495987 = 3743981) B3743981
theorem B2496017 : Blo 1663031 2496017 := bstep (se 2 (by rfl) ⟨936006, by rfl⟩ : syracuseStep 2496017 = 1872013) B1872013
theorem B2496035 : Blo 1663031 2496035 := bstep (se 1 (by rfl) ⟨1872026, by rfl⟩ : syracuseStep 2496035 = 3744053) B3744053
theorem B5617187 : Blo 1663031 5617187 := bstep (se 1 (by rfl) ⟨4212890, by rfl⟩ : syracuseStep 5617187 = 8425781) B8425781
theorem B2807345 : Blo 1663031 2807345 := bstep (se 2 (by rfl) ⟨1052754, by rfl⟩ : syracuseStep 2807345 = 2105509) B2105509
theorem B7108145 : Blo 1663031 7108145 := bstep (se 2 (by rfl) ⟨2665554, by rfl⟩ : syracuseStep 7108145 = 5331109) B5331109
theorem B2496065 : Blo 1663031 2496065 := bstep (se 2 (by rfl) ⟨936024, by rfl⟩ : syracuseStep 2496065 = 1872049) B1872049
theorem B2496083 : Blo 1663031 2496083 := bstep (se 1 (by rfl) ⟨1872062, by rfl⟩ : syracuseStep 2496083 = 3744125) B3744125
theorem B7108195 : Blo 1663031 7108195 := bstep (se 1 (by rfl) ⟨5331146, by rfl⟩ : syracuseStep 7108195 = 10662293) B10662293
theorem B2496113 : Blo 1663031 2496113 := bstep (se 2 (by rfl) ⟨936042, by rfl⟩ : syracuseStep 2496113 = 1872085) B1872085
theorem B2496131 : Blo 1663031 2496131 := bstep (se 1 (by rfl) ⟨1872098, by rfl⟩ : syracuseStep 2496131 = 3744197) B3744197
theorem B2496161 : Blo 1663031 2496161 := bstep (se 2 (by rfl) ⟨936060, by rfl⟩ : syracuseStep 2496161 = 1872121) B1872121
theorem B6321827 : Blo 1663031 6321827 := bstep (se 1 (by rfl) ⟨4741370, by rfl⟩ : syracuseStep 6321827 = 9482741) B9482741
theorem B2807473 : Blo 1663031 2807473 := bstep (se 2 (by rfl) ⟨1052802, by rfl⟩ : syracuseStep 2807473 = 2105605) B2105605
theorem B2496179 : Blo 1663031 2496179 := bstep (se 1 (by rfl) ⟨1872134, by rfl⟩ : syracuseStep 2496179 = 3744269) B3744269
theorem B21313205 : Blo 1663031 21313205 := bstep (se 5 (by rfl) ⟨999056, by rfl⟩ : syracuseStep 21313205 = 1998113) B1998113
theorem B13489861 : Blo 1663031 13489861 := bstep (se 4 (by rfl) ⟨1264674, by rfl⟩ : syracuseStep 13489861 = 2529349) B2529349
theorem B2496209 : Blo 1663031 2496209 := bstep (se 2 (by rfl) ⟨936078, by rfl⟩ : syracuseStep 2496209 = 1872157) B1872157
theorem B2807507 : Blo 1663031 2807507 := bstep (se 1 (by rfl) ⟨2105630, by rfl⟩ : syracuseStep 2807507 = 4211261) B4211261
theorem B2496227 : Blo 1663031 2496227 := bstep (se 1 (by rfl) ⟨1872170, by rfl⟩ : syracuseStep 2496227 = 3744341) B3744341
theorem B2496257 : Blo 1663031 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B17987341 : Blo 1663031 17987341 := bstep (se 3 (by rfl) ⟨3372626, by rfl⟩ : syracuseStep 17987341 = 6745253) B6745253
theorem B2496275 : Blo 1663031 2496275 := bstep (se 1 (by rfl) ⟨1872206, by rfl⟩ : syracuseStep 2496275 = 3744413) B3744413
theorem B3602225 : Blo 1663031 3602225 := bstep (se 2 (by rfl) ⟨1350834, by rfl⟩ : syracuseStep 3602225 = 2701669) B2701669
theorem B2496305 : Blo 1663031 2496305 := bstep (se 2 (by rfl) ⟨936114, by rfl⟩ : syracuseStep 2496305 = 1872229) B1872229
theorem B5617457 : Blo 1663031 5617457 := bstep (se 2 (by rfl) ⟨2106546, by rfl⟩ : syracuseStep 5617457 = 4213093) B4213093
theorem B2496323 : Blo 1663031 2496323 := bstep (se 1 (by rfl) ⟨1872242, by rfl⟩ : syracuseStep 2496323 = 3744485) B3744485
theorem B2807635 : Blo 1663031 2807635 := bstep (se 1 (by rfl) ⟨2105726, by rfl⟩ : syracuseStep 2807635 = 4211453) B4211453
theorem B2496353 : Blo 1663031 2496353 := bstep (se 2 (by rfl) ⟨936132, by rfl⟩ : syracuseStep 2496353 = 1872265) B1872265
theorem B2496371 : Blo 1663031 2496371 := bstep (se 1 (by rfl) ⟨1872278, by rfl⟩ : syracuseStep 2496371 = 3744557) B3744557
theorem B2496401 : Blo 1663031 2496401 := bstep (se 2 (by rfl) ⟨936150, by rfl⟩ : syracuseStep 2496401 = 1872301) B1872301
theorem B2496419 : Blo 1663031 2496419 := bstep (se 1 (by rfl) ⟨1872314, by rfl⟩ : syracuseStep 2496419 = 3744629) B3744629
theorem B2496449 : Blo 1663031 2496449 := bstep (se 2 (by rfl) ⟨936168, by rfl⟩ : syracuseStep 2496449 = 1872337) B1872337
theorem B11999173 : Blo 1663031 11999173 := bstep (se 4 (by rfl) ⟨1124922, by rfl⟩ : syracuseStep 11999173 = 2249845) B2249845
theorem B2496467 : Blo 1663031 2496467 := bstep (se 1 (by rfl) ⟨1872350, by rfl⟩ : syracuseStep 2496467 = 3744701) B3744701
theorem B2807777 : Blo 1663031 2807777 := bstep (se 2 (by rfl) ⟨1052916, by rfl⟩ : syracuseStep 2807777 = 2105833) B2105833
theorem B2496497 : Blo 1663031 2496497 := bstep (se 2 (by rfl) ⟨936186, by rfl⟩ : syracuseStep 2496497 = 1872373) B1872373
theorem B2496515 : Blo 1663031 2496515 := bstep (se 1 (by rfl) ⟨1872386, by rfl⟩ : syracuseStep 2496515 = 3744773) B3744773
theorem B2496545 : Blo 1663031 2496545 := bstep (se 2 (by rfl) ⟨936204, by rfl⟩ : syracuseStep 2496545 = 1872409) B1872409
theorem B2496563 : Blo 1663031 2496563 := bstep (se 1 (by rfl) ⟨1872422, by rfl⟩ : syracuseStep 2496563 = 3744845) B3744845
theorem B2496593 : Blo 1663031 2496593 := bstep (se 2 (by rfl) ⟨936222, by rfl⟩ : syracuseStep 2496593 = 1872445) B1872445
theorem B2807905 : Blo 1663031 2807905 := bstep (se 2 (by rfl) ⟨1052964, by rfl⟩ : syracuseStep 2807905 = 2105929) B2105929
theorem B2496611 : Blo 1663031 2496611 := bstep (se 1 (by rfl) ⟨1872458, by rfl⟩ : syracuseStep 2496611 = 3744917) B3744917
theorem B2496641 : Blo 1663031 2496641 := bstep (se 2 (by rfl) ⟨936240, by rfl⟩ : syracuseStep 2496641 = 1872481) B1872481
theorem B2807939 : Blo 1663031 2807939 := bstep (se 1 (by rfl) ⟨2105954, by rfl⟩ : syracuseStep 2807939 = 4211909) B4211909
theorem B2496659 : Blo 1663031 2496659 := bstep (se 1 (by rfl) ⟨1872494, by rfl⟩ : syracuseStep 2496659 = 3744989) B3744989
theorem B2496689 : Blo 1663031 2496689 := bstep (se 2 (by rfl) ⟨936258, by rfl⟩ : syracuseStep 2496689 = 1872517) B1872517
theorem B2496707 : Blo 1663031 2496707 := bstep (se 1 (by rfl) ⟨1872530, by rfl⟩ : syracuseStep 2496707 = 3745061) B3745061
theorem B8427725 : Blo 1663031 8427725 := bstep (se 3 (by rfl) ⟨1580198, by rfl⟩ : syracuseStep 8427725 = 3160397) B3160397
theorem B4741325 : Blo 1663031 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B2496737 : Blo 1663031 2496737 := bstep (se 2 (by rfl) ⟨936276, by rfl⟩ : syracuseStep 2496737 = 1872553) B1872553
theorem B3160291 : Blo 1663031 3160291 := bstep (se 1 (by rfl) ⟨2370218, by rfl⟩ : syracuseStep 3160291 = 4740437) B4740437
theorem B15186161 : Blo 1663031 15186161 := bstep (se 2 (by rfl) ⟨5694810, by rfl⟩ : syracuseStep 15186161 = 11389621) B11389621
theorem B2496755 : Blo 1663031 2496755 := bstep (se 1 (by rfl) ⟨1872566, by rfl⟩ : syracuseStep 2496755 = 3745133) B3745133
theorem B2808067 : Blo 1663031 2808067 := bstep (se 1 (by rfl) ⟨2106050, by rfl⟩ : syracuseStep 2808067 = 4212101) B4212101
theorem B5691665 : Blo 1663031 5691665 := bstep (se 2 (by rfl) ⟨2134374, by rfl⟩ : syracuseStep 5691665 = 4268749) B4268749
theorem B2496785 : Blo 1663031 2496785 := bstep (se 2 (by rfl) ⟨936294, by rfl⟩ : syracuseStep 2496785 = 1872589) B1872589
theorem B2496803 : Blo 1663031 2496803 := bstep (se 1 (by rfl) ⟨1872602, by rfl⟩ : syracuseStep 2496803 = 3745205) B3745205
theorem B3742001 : Blo 1663031 3742001 := bstep (se 2 (by rfl) ⟨1403250, by rfl⟩ : syracuseStep 3742001 = 2806501) B2806501
theorem B2496833 : Blo 1663031 2496833 := bstep (se 2 (by rfl) ⟨936312, by rfl⟩ : syracuseStep 2496833 = 1872625) B1872625
theorem B3742019 : Blo 1663031 3742019 := bstep (se 1 (by rfl) ⟨2806514, by rfl⟩ : syracuseStep 3742019 = 5613029) B5613029
theorem B1685827 : Blo 1663031 1685827 := bstep (se 1 (by rfl) ⟨1264370, by rfl⟩ : syracuseStep 1685827 = 2528741) B2528741
theorem B5617997 : Blo 1663031 5617997 := bstep (se 3 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 5617997 = 2106749) B2106749
theorem B2496851 : Blo 1663031 2496851 := bstep (se 1 (by rfl) ⟨1872638, by rfl⟩ : syracuseStep 2496851 = 3745277) B3745277
theorem B10664291 : Blo 1663031 10664291 := bstep (se 1 (by rfl) ⟨7998218, by rfl⟩ : syracuseStep 10664291 = 15996437) B15996437
theorem B2496881 : Blo 1663031 2496881 := bstep (se 2 (by rfl) ⟨936330, by rfl⟩ : syracuseStep 2496881 = 1872661) B1872661
theorem B2529665 : Blo 1663031 2529665 := bstep (se 2 (by rfl) ⟨948624, by rfl⟩ : syracuseStep 2529665 = 1897249) B1897249
theorem B2496899 : Blo 1663031 2496899 := bstep (se 1 (by rfl) ⟨1872674, by rfl⟩ : syracuseStep 2496899 = 3745349) B3745349
theorem B5618051 : Blo 1663031 5618051 := bstep (se 1 (by rfl) ⟨4213538, by rfl⟩ : syracuseStep 5618051 = 8427077) B8427077
theorem B3160451 : Blo 1663031 3160451 := bstep (se 1 (by rfl) ⟨2370338, by rfl⟩ : syracuseStep 3160451 = 4740677) B4740677
theorem B2808209 : Blo 1663031 2808209 := bstep (se 2 (by rfl) ⟨1053078, by rfl⟩ : syracuseStep 2808209 = 2106157) B2106157
theorem B2496929 : Blo 1663031 2496929 := bstep (se 2 (by rfl) ⟨936348, by rfl⟩ : syracuseStep 2496929 = 1872697) B1872697
theorem B2496947 : Blo 1663031 2496947 := bstep (se 1 (by rfl) ⟨1872710, by rfl⟩ : syracuseStep 2496947 = 3745421) B3745421
theorem B10115525 : Blo 1663031 10115525 := bstep (se 4 (by rfl) ⟨948330, by rfl⟩ : syracuseStep 10115525 = 1896661) B1896661
theorem B2496977 : Blo 1663031 2496977 := bstep (se 2 (by rfl) ⟨936366, by rfl⟩ : syracuseStep 2496977 = 1872733) B1872733
theorem B2496995 : Blo 1663031 2496995 := bstep (se 1 (by rfl) ⟨1872746, by rfl⟩ : syracuseStep 2496995 = 3745493) B3745493
theorem B2497025 : Blo 1663031 2497025 := bstep (se 2 (by rfl) ⟨936384, by rfl⟩ : syracuseStep 2497025 = 1872769) B1872769
theorem B2808337 : Blo 1663031 2808337 := bstep (se 2 (by rfl) ⟨1053126, by rfl⟩ : syracuseStep 2808337 = 2106253) B2106253
theorem B2497043 : Blo 1663031 2497043 := bstep (se 1 (by rfl) ⟨1872782, by rfl⟩ : syracuseStep 2497043 = 3745565) B3745565
theorem B3553841 : Blo 1663031 3553841 := bstep (se 2 (by rfl) ⟨1332690, by rfl⟩ : syracuseStep 3553841 = 2665381) B2665381
theorem B2808371 : Blo 1663031 2808371 := bstep (se 1 (by rfl) ⟨2106278, by rfl⟩ : syracuseStep 2808371 = 4212557) B4212557
theorem B2497073 : Blo 1663031 2497073 := bstep (se 2 (by rfl) ⟨936402, by rfl⟩ : syracuseStep 2497073 = 1872805) B1872805
theorem B2497091 : Blo 1663031 2497091 := bstep (se 1 (by rfl) ⟨1872818, by rfl⟩ : syracuseStep 2497091 = 3745637) B3745637
theorem B3742289 : Blo 1663031 3742289 := bstep (se 2 (by rfl) ⟨1403358, by rfl⟩ : syracuseStep 3742289 = 2806717) B2806717
theorem B2497121 : Blo 1663031 2497121 := bstep (se 2 (by rfl) ⟨936420, by rfl⟩ : syracuseStep 2497121 = 1872841) B1872841
theorem B3742307 : Blo 1663031 3742307 := bstep (se 1 (by rfl) ⟨2806730, by rfl⟩ : syracuseStep 3742307 = 5613461) B5613461
theorem B2497139 : Blo 1663031 2497139 := bstep (se 1 (by rfl) ⟨1872854, by rfl⟩ : syracuseStep 2497139 = 3745709) B3745709
theorem B1800835 : Blo 1663031 1800835 := bstep (se 1 (by rfl) ⟨1350626, by rfl⟩ : syracuseStep 1800835 = 2701253) B2701253
theorem B5618321 : Blo 1663031 5618321 := bstep (se 2 (by rfl) ⟨2106870, by rfl⟩ : syracuseStep 5618321 = 4213741) B4213741
theorem B2497169 : Blo 1663031 2497169 := bstep (se 2 (by rfl) ⟨936438, by rfl⟩ : syracuseStep 2497169 = 1872877) B1872877
theorem B2497187 : Blo 1663031 2497187 := bstep (se 1 (by rfl) ⟨1872890, by rfl⟩ : syracuseStep 2497187 = 3745781) B3745781
theorem B2808499 : Blo 1663031 2808499 := bstep (se 1 (by rfl) ⟨2106374, by rfl⟩ : syracuseStep 2808499 = 4212749) B4212749
theorem B2497217 : Blo 1663031 2497217 := bstep (se 2 (by rfl) ⟨936456, by rfl⟩ : syracuseStep 2497217 = 1872913) B1872913
theorem B2497235 : Blo 1663031 2497235 := bstep (se 1 (by rfl) ⟨1872926, by rfl⟩ : syracuseStep 2497235 = 3745853) B3745853
theorem B5995235 : Blo 1663031 5995235 := bstep (se 1 (by rfl) ⟨4496426, by rfl⟩ : syracuseStep 5995235 = 8992853) B8992853
theorem B2497265 : Blo 1663031 2497265 := bstep (se 2 (by rfl) ⟨936474, by rfl⟩ : syracuseStep 2497265 = 1872949) B1872949
theorem B2497283 : Blo 1663031 2497283 := bstep (se 1 (by rfl) ⟨1872962, by rfl⟩ : syracuseStep 2497283 = 3745925) B3745925
theorem B2497313 : Blo 1663031 2497313 := bstep (se 2 (by rfl) ⟨936492, by rfl⟩ : syracuseStep 2497313 = 1872985) B1872985
theorem B2530097 : Blo 1663031 2530097 := bstep (se 2 (by rfl) ⟨948786, by rfl⟩ : syracuseStep 2530097 = 1897573) B1897573
theorem B2497331 : Blo 1663031 2497331 := bstep (se 1 (by rfl) ⟨1872998, by rfl⟩ : syracuseStep 2497331 = 3745997) B3745997
theorem B2808641 : Blo 1663031 2808641 := bstep (se 2 (by rfl) ⟨1053240, by rfl⟩ : syracuseStep 2808641 = 2106481) B2106481
theorem B2497361 : Blo 1663031 2497361 := bstep (se 2 (by rfl) ⟨936510, by rfl⟩ : syracuseStep 2497361 = 1873021) B1873021
theorem B3996515 : Blo 1663031 3996515 := bstep (se 1 (by rfl) ⟨2997386, by rfl⟩ : syracuseStep 3996515 = 5994773) B5994773
theorem B2497379 : Blo 1663031 2497379 := bstep (se 1 (by rfl) ⟨1873034, by rfl⟩ : syracuseStep 2497379 = 3746069) B3746069
theorem B3742577 : Blo 1663031 3742577 := bstep (se 2 (by rfl) ⟨1403466, by rfl⟩ : syracuseStep 3742577 = 2806933) B2806933
theorem B2497409 : Blo 1663031 2497409 := bstep (se 2 (by rfl) ⟨936528, by rfl⟩ : syracuseStep 2497409 = 1873057) B1873057
theorem B3742595 : Blo 1663031 3742595 := bstep (se 1 (by rfl) ⟨2806946, by rfl⟩ : syracuseStep 3742595 = 5613893) B5613893
theorem B2497427 : Blo 1663031 2497427 := bstep (se 1 (by rfl) ⟨1873070, by rfl⟩ : syracuseStep 2497427 = 3746141) B3746141
theorem B8420273 : Blo 1663031 8420273 := bstep (se 2 (by rfl) ⟨3157602, by rfl⟩ : syracuseStep 8420273 = 6315205) B6315205
theorem B2497457 : Blo 1663031 2497457 := bstep (se 2 (by rfl) ⟨936546, by rfl⟩ : syracuseStep 2497457 = 1873093) B1873093
theorem B2808769 : Blo 1663031 2808769 := bstep (se 2 (by rfl) ⟨1053288, by rfl⟩ : syracuseStep 2808769 = 2106577) B2106577
theorem B2497475 : Blo 1663031 2497475 := bstep (se 1 (by rfl) ⟨1873106, by rfl⟩ : syracuseStep 2497475 = 3746213) B3746213
theorem B2497505 : Blo 1663031 2497505 := bstep (se 2 (by rfl) ⟨936564, by rfl⟩ : syracuseStep 2497505 = 1873129) B1873129
theorem B42646499 : Blo 1663031 42646499 := bstep (se 1 (by rfl) ⟨31984874, by rfl⟩ : syracuseStep 42646499 = 63969749) B63969749
theorem B2808803 : Blo 1663031 2808803 := bstep (se 1 (by rfl) ⟨2106602, by rfl⟩ : syracuseStep 2808803 = 4213205) B4213205
theorem B6314993 : Blo 1663031 6314993 := bstep (se 2 (by rfl) ⟨2368122, by rfl⟩ : syracuseStep 6314993 = 4736245) B4736245
theorem B2497523 : Blo 1663031 2497523 := bstep (se 1 (by rfl) ⟨1873142, by rfl⟩ : syracuseStep 2497523 = 3746285) B3746285
theorem B36486197 : Blo 1663031 36486197 := bstep (se 5 (by rfl) ⟨1710290, by rfl⟩ : syracuseStep 36486197 = 3420581) B3420581
theorem B3554371 : Blo 1663031 3554371 := bstep (se 1 (by rfl) ⟨2665778, by rfl⟩ : syracuseStep 3554371 = 5331557) B5331557
theorem B2997329 : Blo 1663031 2997329 := bstep (se 2 (by rfl) ⟨1123998, by rfl⟩ : syracuseStep 2997329 = 2247997) B2247997
theorem B12631139 : Blo 1663031 12631139 := bstep (se 1 (by rfl) ⟨9473354, by rfl⟩ : syracuseStep 12631139 = 18946709) B18946709
theorem B2808931 : Blo 1663031 2808931 := bstep (se 1 (by rfl) ⟨2106698, by rfl⟩ : syracuseStep 2808931 = 4213397) B4213397
theorem B3996803 : Blo 1663031 3996803 := bstep (se 1 (by rfl) ⟨2997602, by rfl⟩ : syracuseStep 3996803 = 5995205) B5995205
theorem B3742865 : Blo 1663031 3742865 := bstep (se 2 (by rfl) ⟨1403574, by rfl⟩ : syracuseStep 3742865 = 2807149) B2807149
theorem B3742883 : Blo 1663031 3742883 := bstep (se 1 (by rfl) ⟨2807162, by rfl⟩ : syracuseStep 3742883 = 5614325) B5614325
theorem B5618861 : Blo 1663031 5618861 := bstep (se 3 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 5618861 = 2107073) B2107073
theorem B1776835 : Blo 1663031 1776835 := bstep (se 1 (by rfl) ⟨1332626, by rfl⟩ : syracuseStep 1776835 = 2665253) B2665253
theorem B5618915 : Blo 1663031 5618915 := bstep (se 1 (by rfl) ⟨4214186, by rfl⟩ : syracuseStep 5618915 = 8428373) B8428373
theorem B2809073 : Blo 1663031 2809073 := bstep (se 2 (by rfl) ⟨1053402, by rfl⟩ : syracuseStep 2809073 = 2106805) B2106805
theorem B5332301 : Blo 1663031 5332301 := bstep (se 3 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 5332301 = 1999613) B1999613
theorem B2809201 : Blo 1663031 2809201 := bstep (se 2 (by rfl) ⟨1053450, by rfl⟩ : syracuseStep 2809201 = 2106901) B2106901
theorem B14212493 : Blo 1663031 14212493 := bstep (se 3 (by rfl) ⟨2664842, by rfl⟩ : syracuseStep 14212493 = 5329685) B5329685
theorem B2809235 : Blo 1663031 2809235 := bstep (se 1 (by rfl) ⟨2106926, by rfl⟩ : syracuseStep 2809235 = 4213853) B4213853
theorem B2563489 : Blo 1663031 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B6159793 : Blo 1663031 6159793 := bstep (se 2 (by rfl) ⟨2309922, by rfl⟩ : syracuseStep 6159793 = 4619845) B4619845
theorem B3743153 : Blo 1663031 3743153 := bstep (se 2 (by rfl) ⟨1403682, by rfl⟩ : syracuseStep 3743153 = 2807365) B2807365
theorem B3743171 : Blo 1663031 3743171 := bstep (se 1 (by rfl) ⟨2807378, by rfl⟩ : syracuseStep 3743171 = 5614757) B5614757
theorem B5619185 : Blo 1663031 5619185 := bstep (se 2 (by rfl) ⟨2107194, by rfl⟩ : syracuseStep 5619185 = 4214389) B4214389
theorem B2809363 : Blo 1663031 2809363 := bstep (se 1 (by rfl) ⟨2107022, by rfl⟩ : syracuseStep 2809363 = 4214045) B4214045
theorem B2997827 : Blo 1663031 2997827 := bstep (se 1 (by rfl) ⟨2248370, by rfl⟩ : syracuseStep 2997827 = 4496741) B4496741
theorem B4210289 : Blo 1663031 4210289 := bstep (se 2 (by rfl) ⟨1578858, by rfl⟩ : syracuseStep 4210289 = 3157717) B3157717
theorem B2809505 : Blo 1663031 2809505 := bstep (se 2 (by rfl) ⟨1053564, by rfl⟩ : syracuseStep 2809505 = 2107129) B2107129
theorem B4210339 : Blo 1663031 4210339 := bstep (se 1 (by rfl) ⟨3157754, by rfl⟩ : syracuseStep 4210339 = 6315509) B6315509
theorem B3743441 : Blo 1663031 3743441 := bstep (se 2 (by rfl) ⟨1403790, by rfl⟩ : syracuseStep 3743441 = 2807581) B2807581
theorem B3743459 : Blo 1663031 3743459 := bstep (se 1 (by rfl) ⟨2807594, by rfl⟩ : syracuseStep 3743459 = 5615189) B5615189
theorem B2809633 : Blo 1663031 2809633 := bstep (se 2 (by rfl) ⟨1053612, by rfl⟩ : syracuseStep 2809633 = 2107225) B2107225
theorem B6405923 : Blo 1663031 6405923 := bstep (se 1 (by rfl) ⟨4804442, by rfl⟩ : syracuseStep 6405923 = 9608885) B9608885
theorem B4210481 : Blo 1663031 4210481 := bstep (se 2 (by rfl) ⟨1578930, by rfl⟩ : syracuseStep 4210481 = 3157861) B3157861
theorem B1777459 : Blo 1663031 1777459 := bstep (se 1 (by rfl) ⟨1333094, by rfl⟩ : syracuseStep 1777459 = 2666189) B2666189
theorem B2809667 : Blo 1663031 2809667 := bstep (se 1 (by rfl) ⟨2107250, by rfl⟩ : syracuseStep 2809667 = 4214501) B4214501
theorem B60702605 : Blo 1663031 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B9478093 : Blo 1663031 9478093 := bstep (se 3 (by rfl) ⟨1777142, by rfl⟩ : syracuseStep 9478093 = 3554285) B3554285
theorem B7110605 : Blo 1663031 7110605 := bstep (se 3 (by rfl) ⟨1333238, by rfl⟩ : syracuseStep 7110605 = 2666477) B2666477
theorem B3997649 : Blo 1663031 3997649 := bstep (se 2 (by rfl) ⟨1499118, by rfl⟩ : syracuseStep 3997649 = 2998237) B2998237
theorem B3743729 : Blo 1663031 3743729 := bstep (se 2 (by rfl) ⟨1403898, by rfl⟩ : syracuseStep 3743729 = 2807797) B2807797
theorem B1998859 : Blo 1663031 1998859 := bstep (se 1 (by rfl) ⟨1499144, by rfl⟩ : syracuseStep 1998859 = 2998289) B2998289
theorem B1663031 : Blo 1663031 1663031 := bstep (se 1 (by rfl) ⟨1247273, by rfl⟩ : syracuseStep 1663031 = 2494547) B2494547
theorem B1663051 : Blo 1663031 1663051 := bstep (se 1 (by rfl) ⟨1247288, by rfl⟩ : syracuseStep 1663051 = 2494577) B2494577
theorem B3743819 : Blo 1663031 3743819 := bstep (se 1 (by rfl) ⟨2807864, by rfl⟩ : syracuseStep 3743819 = 5615729) B5615729
theorem B1663063 : Blo 1663031 1663063 := bstep (se 1 (by rfl) ⟨1247297, by rfl⟩ : syracuseStep 1663063 = 2494595) B2494595
theorem B3375191 : Blo 1663031 3375191 := bstep (se 1 (by rfl) ⟨2531393, by rfl⟩ : syracuseStep 3375191 = 5062787) B5062787
theorem B1663083 : Blo 1663031 1663083 := bstep (se 1 (by rfl) ⟨1247312, by rfl⟩ : syracuseStep 1663083 = 2494625) B2494625
theorem B1663095 : Blo 1663031 1663095 := bstep (se 1 (by rfl) ⟨1247321, by rfl⟩ : syracuseStep 1663095 = 2494643) B2494643
theorem B3743873 : Blo 1663031 3743873 := bstep (se 2 (by rfl) ⟨1403952, by rfl⟩ : syracuseStep 3743873 = 2807905) B2807905
theorem B6316163 : Blo 1663031 6316163 := bstep (se 1 (by rfl) ⟨4737122, by rfl⟩ : syracuseStep 6316163 = 9474245) B9474245
theorem B1663115 : Blo 1663031 1663115 := bstep (se 1 (by rfl) ⟨1247336, by rfl⟩ : syracuseStep 1663115 = 2494673) B2494673
theorem B6316177 : Blo 1663031 6316177 := bstep (se 2 (by rfl) ⟨2368566, by rfl⟩ : syracuseStep 6316177 = 4737133) B4737133
theorem B1663127 : Blo 1663031 1663127 := bstep (se 1 (by rfl) ⟨1247345, by rfl⟩ : syracuseStep 1663127 = 2494691) B2494691
theorem B1663147 : Blo 1663031 1663147 := bstep (se 1 (by rfl) ⟨1247360, by rfl⟩ : syracuseStep 1663147 = 2494721) B2494721
theorem B1777835 : Blo 1663031 1777835 := bstep (se 1 (by rfl) ⟨1333376, by rfl⟩ : syracuseStep 1777835 = 2666753) B2666753
theorem B1663159 : Blo 1663031 1663159 := bstep (se 1 (by rfl) ⟨1247369, by rfl⟩ : syracuseStep 1663159 = 2494739) B2494739
theorem B1663179 : Blo 1663031 1663179 := bstep (se 1 (by rfl) ⟨1247384, by rfl⟩ : syracuseStep 1663179 = 2494769) B2494769
theorem B1663191 : Blo 1663031 1663191 := bstep (se 1 (by rfl) ⟨1247393, by rfl⟩ : syracuseStep 1663191 = 2494787) B2494787
theorem B1663211 : Blo 1663031 1663211 := bstep (se 1 (by rfl) ⟨1247408, by rfl⟩ : syracuseStep 1663211 = 2494817) B2494817
theorem B1663223 : Blo 1663031 1663223 := bstep (se 1 (by rfl) ⟨1247417, by rfl⟩ : syracuseStep 1663223 = 2494835) B2494835
theorem B1663243 : Blo 1663031 1663243 := bstep (se 1 (by rfl) ⟨1247432, by rfl⟩ : syracuseStep 1663243 = 2494865) B2494865
theorem B7110929 : Blo 1663031 7110929 := bstep (se 2 (by rfl) ⟨2666598, by rfl⟩ : syracuseStep 7110929 = 5333197) B5333197
theorem B1663255 : Blo 1663031 1663255 := bstep (se 1 (by rfl) ⟨1247441, by rfl⟩ : syracuseStep 1663255 = 2494883) B2494883
theorem B4210967 : Blo 1663031 4210967 := bstep (se 1 (by rfl) ⟨3158225, by rfl⟩ : syracuseStep 4210967 = 6316451) B6316451
theorem B1663275 : Blo 1663031 1663275 := bstep (se 1 (by rfl) ⟨1247456, by rfl⟩ : syracuseStep 1663275 = 2494913) B2494913
theorem B1663287 : Blo 1663031 1663287 := bstep (se 1 (by rfl) ⟨1247465, by rfl⟩ : syracuseStep 1663287 = 2494931) B2494931
theorem B1663307 : Blo 1663031 1663307 := bstep (se 1 (by rfl) ⟨1247480, by rfl⟩ : syracuseStep 1663307 = 2494961) B2494961
theorem B1663319 : Blo 1663031 1663319 := bstep (se 1 (by rfl) ⟨1247489, by rfl⟩ : syracuseStep 1663319 = 2494979) B2494979
theorem B3744089 : Blo 1663031 3744089 := bstep (se 2 (by rfl) ⟨1404033, by rfl⟩ : syracuseStep 3744089 = 2808067) B2808067
theorem B10658141 : Blo 1663031 10658141 := bstep (se 3 (by rfl) ⟨1998401, by rfl⟩ : syracuseStep 10658141 = 3996803) B3996803
theorem B1663339 : Blo 1663031 1663339 := bstep (se 1 (by rfl) ⟨1247504, by rfl⟩ : syracuseStep 1663339 = 2495009) B2495009
theorem B1663351 : Blo 1663031 1663351 := bstep (se 1 (by rfl) ⟨1247513, by rfl⟩ : syracuseStep 1663351 = 2495027) B2495027
theorem B3555713 : Blo 1663031 3555713 := bstep (se 2 (by rfl) ⟨1333392, by rfl⟩ : syracuseStep 3555713 = 2666785) B2666785
theorem B2367883 : Blo 1663031 2367883 := bstep (se 1 (by rfl) ⟨1775912, by rfl⟩ : syracuseStep 2367883 = 3551825) B3551825
theorem B1663371 : Blo 1663031 1663371 := bstep (se 1 (by rfl) ⟨1247528, by rfl⟩ : syracuseStep 1663371 = 2495057) B2495057
theorem B1999243 : Blo 1663031 1999243 := bstep (se 1 (by rfl) ⟨1499432, by rfl⟩ : syracuseStep 1999243 = 2998865) B2998865
theorem B2367895 : Blo 1663031 2367895 := bstep (se 1 (by rfl) ⟨1775921, by rfl⟩ : syracuseStep 2367895 = 3551843) B3551843
theorem B1663383 : Blo 1663031 1663383 := bstep (se 1 (by rfl) ⟨1247537, by rfl⟩ : syracuseStep 1663383 = 2495075) B2495075
theorem B1663403 : Blo 1663031 1663403 := bstep (se 1 (by rfl) ⟨1247552, by rfl⟩ : syracuseStep 1663403 = 2495105) B2495105
theorem B14213555 : Blo 1663031 14213555 := bstep (se 1 (by rfl) ⟨10660166, by rfl⟩ : syracuseStep 14213555 = 21320333) B21320333
theorem B3744179 : Blo 1663031 3744179 := bstep (se 1 (by rfl) ⟨2808134, by rfl⟩ : syracuseStep 3744179 = 5616269) B5616269
theorem B1663415 : Blo 1663031 1663415 := bstep (se 1 (by rfl) ⟨1247561, by rfl⟩ : syracuseStep 1663415 = 2495123) B2495123
theorem B6316481 : Blo 1663031 6316481 := bstep (se 2 (by rfl) ⟨2368680, by rfl⟩ : syracuseStep 6316481 = 4737361) B4737361
theorem B1663435 : Blo 1663031 1663435 := bstep (se 1 (by rfl) ⟨1247576, by rfl⟩ : syracuseStep 1663435 = 2495153) B2495153
theorem B1663447 : Blo 1663031 1663447 := bstep (se 1 (by rfl) ⟨1247585, by rfl⟩ : syracuseStep 1663447 = 2495171) B2495171
theorem B3744215 : Blo 1663031 3744215 := bstep (se 1 (by rfl) ⟨2808161, by rfl⟩ : syracuseStep 3744215 = 5616323) B5616323
theorem B1663467 : Blo 1663031 1663467 := bstep (se 1 (by rfl) ⟨1247600, by rfl⟩ : syracuseStep 1663467 = 2495201) B2495201
theorem B1663479 : Blo 1663031 1663479 := bstep (se 1 (by rfl) ⟨1247609, by rfl⟩ : syracuseStep 1663479 = 2495219) B2495219
theorem B1663499 : Blo 1663031 1663499 := bstep (se 1 (by rfl) ⟨1247624, by rfl⟩ : syracuseStep 1663499 = 2495249) B2495249
theorem B1663511 : Blo 1663031 1663511 := bstep (se 1 (by rfl) ⟨1247633, by rfl⟩ : syracuseStep 1663511 = 2495267) B2495267
theorem B1663531 : Blo 1663031 1663531 := bstep (se 1 (by rfl) ⟨1247648, by rfl⟩ : syracuseStep 1663531 = 2495297) B2495297
theorem B1663543 : Blo 1663031 1663543 := bstep (se 1 (by rfl) ⟨1247657, by rfl⟩ : syracuseStep 1663543 = 2495315) B2495315
theorem B1663563 : Blo 1663031 1663563 := bstep (se 1 (by rfl) ⟨1247672, by rfl⟩ : syracuseStep 1663563 = 2495345) B2495345
theorem B1663575 : Blo 1663031 1663575 := bstep (se 1 (by rfl) ⟨1247681, by rfl⟩ : syracuseStep 1663575 = 2495363) B2495363
theorem B2998871 : Blo 1663031 2998871 := bstep (se 1 (by rfl) ⟨2249153, by rfl⟩ : syracuseStep 2998871 = 4498307) B4498307
theorem B14221925 : Blo 1663031 14221925 := bstep (se 4 (by rfl) ⟨1333305, by rfl⟩ : syracuseStep 14221925 = 2666611) B2666611
theorem B1663595 : Blo 1663031 1663595 := bstep (se 1 (by rfl) ⟨1247696, by rfl⟩ : syracuseStep 1663595 = 2495393) B2495393
theorem B1663607 : Blo 1663031 1663607 := bstep (se 1 (by rfl) ⟨1247705, by rfl⟩ : syracuseStep 1663607 = 2495411) B2495411
theorem B1663627 : Blo 1663031 1663627 := bstep (se 1 (by rfl) ⟨1247720, by rfl⟩ : syracuseStep 1663627 = 2495441) B2495441
theorem B2105995 : Blo 1663031 2105995 := bstep (se 1 (by rfl) ⟨1579496, by rfl⟩ : syracuseStep 2105995 = 3158993) B3158993
theorem B3744395 : Blo 1663031 3744395 := bstep (se 1 (by rfl) ⟨2808296, by rfl⟩ : syracuseStep 3744395 = 5616593) B5616593
theorem B1663639 : Blo 1663031 1663639 := bstep (se 1 (by rfl) ⟨1247729, by rfl⟩ : syracuseStep 1663639 = 2495459) B2495459
theorem B1663659 : Blo 1663031 1663659 := bstep (se 1 (by rfl) ⟨1247744, by rfl⟩ : syracuseStep 1663659 = 2495489) B2495489
theorem B5333683 : Blo 1663031 5333683 := bstep (se 1 (by rfl) ⟨4000262, by rfl⟩ : syracuseStep 5333683 = 8000525) B8000525
theorem B1663671 : Blo 1663031 1663671 := bstep (se 1 (by rfl) ⟨1247753, by rfl⟩ : syracuseStep 1663671 = 2495507) B2495507
theorem B3744449 : Blo 1663031 3744449 := bstep (se 2 (by rfl) ⟨1404168, by rfl⟩ : syracuseStep 3744449 = 2808337) B2808337
theorem B1663691 : Blo 1663031 1663691 := bstep (se 1 (by rfl) ⟨1247768, by rfl⟩ : syracuseStep 1663691 = 2495537) B2495537
theorem B1663703 : Blo 1663031 1663703 := bstep (se 1 (by rfl) ⟨1247777, by rfl⟩ : syracuseStep 1663703 = 2495555) B2495555
theorem B3556055 : Blo 1663031 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B1663723 : Blo 1663031 1663723 := bstep (se 1 (by rfl) ⟨1247792, by rfl⟩ : syracuseStep 1663723 = 2495585) B2495585
theorem B1663735 : Blo 1663031 1663735 := bstep (se 1 (by rfl) ⟨1247801, by rfl⟩ : syracuseStep 1663735 = 2495603) B2495603
theorem B1663755 : Blo 1663031 1663755 := bstep (se 1 (by rfl) ⟨1247816, by rfl⟩ : syracuseStep 1663755 = 2495633) B2495633
theorem B1663767 : Blo 1663031 1663767 := bstep (se 1 (by rfl) ⟨1247825, by rfl⟩ : syracuseStep 1663767 = 2495651) B2495651
theorem B1663787 : Blo 1663031 1663787 := bstep (se 1 (by rfl) ⟨1247840, by rfl⟩ : syracuseStep 1663787 = 2495681) B2495681
theorem B1663799 : Blo 1663031 1663799 := bstep (se 1 (by rfl) ⟨1247849, by rfl⟩ : syracuseStep 1663799 = 2495699) B2495699
theorem B115336001 : Blo 1663031 115336001 := bstep (se 2 (by rfl) ⟨43251000, by rfl⟩ : syracuseStep 115336001 = 86502001) B86502001
theorem B1663819 : Blo 1663031 1663819 := bstep (se 1 (by rfl) ⟨1247864, by rfl⟩ : syracuseStep 1663819 = 2495729) B2495729
theorem B1663831 : Blo 1663031 1663831 := bstep (se 1 (by rfl) ⟨1247873, by rfl⟩ : syracuseStep 1663831 = 2495747) B2495747
theorem B1663851 : Blo 1663031 1663851 := bstep (se 1 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 1663851 = 2495777) B2495777
theorem B1663863 : Blo 1663031 1663863 := bstep (se 1 (by rfl) ⟨1247897, by rfl⟩ : syracuseStep 1663863 = 2495795) B2495795
theorem B1663883 : Blo 1663031 1663883 := bstep (se 1 (by rfl) ⟨1247912, by rfl⟩ : syracuseStep 1663883 = 2495825) B2495825
theorem B1663895 : Blo 1663031 1663895 := bstep (se 1 (by rfl) ⟨1247921, by rfl⟩ : syracuseStep 1663895 = 2495843) B2495843
theorem B2106263 : Blo 1663031 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B3744665 : Blo 1663031 3744665 := bstep (se 2 (by rfl) ⟨1404249, by rfl⟩ : syracuseStep 3744665 = 2808499) B2808499
theorem B1663915 : Blo 1663031 1663915 := bstep (se 1 (by rfl) ⟨1247936, by rfl⟩ : syracuseStep 1663915 = 2495873) B2495873
theorem B4211635 : Blo 1663031 4211635 := bstep (se 1 (by rfl) ⟨3158726, by rfl⟩ : syracuseStep 4211635 = 6317453) B6317453
theorem B1663927 : Blo 1663031 1663927 := bstep (se 1 (by rfl) ⟨1247945, by rfl⟩ : syracuseStep 1663927 = 2495891) B2495891
theorem B1663947 : Blo 1663031 1663947 := bstep (se 1 (by rfl) ⟨1247960, by rfl⟩ : syracuseStep 1663947 = 2495921) B2495921
theorem B1663959 : Blo 1663031 1663959 := bstep (se 1 (by rfl) ⟨1247969, by rfl⟩ : syracuseStep 1663959 = 2495939) B2495939
theorem B1663979 : Blo 1663031 1663979 := bstep (se 1 (by rfl) ⟨1247984, by rfl⟩ : syracuseStep 1663979 = 2495969) B2495969
theorem B3744755 : Blo 1663031 3744755 := bstep (se 1 (by rfl) ⟨2808566, by rfl⟩ : syracuseStep 3744755 = 5617133) B5617133
theorem B1663991 : Blo 1663031 1663991 := bstep (se 1 (by rfl) ⟨1247993, by rfl⟩ : syracuseStep 1663991 = 2495987) B2495987
theorem B1664011 : Blo 1663031 1664011 := bstep (se 1 (by rfl) ⟨1248008, by rfl⟩ : syracuseStep 1664011 = 2496017) B2496017
theorem B1664023 : Blo 1663031 1664023 := bstep (se 1 (by rfl) ⟨1248017, by rfl⟩ : syracuseStep 1664023 = 2496035) B2496035
theorem B3744791 : Blo 1663031 3744791 := bstep (se 1 (by rfl) ⟨2808593, by rfl⟩ : syracuseStep 3744791 = 5617187) B5617187
theorem B1664043 : Blo 1663031 1664043 := bstep (se 1 (by rfl) ⟨1248032, by rfl⟩ : syracuseStep 1664043 = 2496065) B2496065
theorem B1664055 : Blo 1663031 1664055 := bstep (se 1 (by rfl) ⟨1248041, by rfl⟩ : syracuseStep 1664055 = 2496083) B2496083
theorem B4211777 : Blo 1663031 4211777 := bstep (se 2 (by rfl) ⟨1579416, by rfl⟩ : syracuseStep 4211777 = 3158833) B3158833
theorem B12641345 : Blo 1663031 12641345 := bstep (se 2 (by rfl) ⟨4740504, by rfl⟩ : syracuseStep 12641345 = 9481009) B9481009
theorem B1664075 : Blo 1663031 1664075 := bstep (se 1 (by rfl) ⟨1248056, by rfl⟩ : syracuseStep 1664075 = 2496113) B2496113
theorem B1664087 : Blo 1663031 1664087 := bstep (se 1 (by rfl) ⟨1248065, by rfl⟩ : syracuseStep 1664087 = 2496131) B2496131
theorem B6317149 : Blo 1663031 6317149 := bstep (se 3 (by rfl) ⟨1184465, by rfl⟩ : syracuseStep 6317149 = 2368931) B2368931
theorem B1664107 : Blo 1663031 1664107 := bstep (se 1 (by rfl) ⟨1248080, by rfl⟩ : syracuseStep 1664107 = 2496161) B2496161
theorem B1664119 : Blo 1663031 1664119 := bstep (se 1 (by rfl) ⟨1248089, by rfl⟩ : syracuseStep 1664119 = 2496179) B2496179
theorem B1664139 : Blo 1663031 1664139 := bstep (se 1 (by rfl) ⟨1248104, by rfl⟩ : syracuseStep 1664139 = 2496209) B2496209
theorem B1664151 : Blo 1663031 1664151 := bstep (se 1 (by rfl) ⟨1248113, by rfl⟩ : syracuseStep 1664151 = 2496227) B2496227
theorem B1664171 : Blo 1663031 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B3998899 : Blo 1663031 3998899 := bstep (se 1 (by rfl) ⟨2999174, by rfl⟩ : syracuseStep 3998899 = 5998349) B5998349
theorem B1664183 : Blo 1663031 1664183 := bstep (se 1 (by rfl) ⟨1248137, by rfl⟩ : syracuseStep 1664183 = 2496275) B2496275
theorem B2401483 : Blo 1663031 2401483 := bstep (se 1 (by rfl) ⟨1801112, by rfl⟩ : syracuseStep 2401483 = 3602225) B3602225
theorem B1664203 : Blo 1663031 1664203 := bstep (se 1 (by rfl) ⟨1248152, by rfl⟩ : syracuseStep 1664203 = 2496305) B2496305
theorem B3744971 : Blo 1663031 3744971 := bstep (se 1 (by rfl) ⟨2808728, by rfl⟩ : syracuseStep 3744971 = 5617457) B5617457
theorem B1664215 : Blo 1663031 1664215 := bstep (se 1 (by rfl) ⟨1248161, by rfl⟩ : syracuseStep 1664215 = 2496323) B2496323
theorem B1664235 : Blo 1663031 1664235 := bstep (se 1 (by rfl) ⟨1248176, by rfl⟩ : syracuseStep 1664235 = 2496353) B2496353
theorem B1664247 : Blo 1663031 1664247 := bstep (se 1 (by rfl) ⟨1248185, by rfl⟩ : syracuseStep 1664247 = 2496371) B2496371
theorem B3745025 : Blo 1663031 3745025 := bstep (se 2 (by rfl) ⟨1404384, by rfl⟩ : syracuseStep 3745025 = 2808769) B2808769
theorem B1664267 : Blo 1663031 1664267 := bstep (se 1 (by rfl) ⟨1248200, by rfl⟩ : syracuseStep 1664267 = 2496401) B2496401
theorem B1664279 : Blo 1663031 1664279 := bstep (se 1 (by rfl) ⟨1248209, by rfl⟩ : syracuseStep 1664279 = 2496419) B2496419
theorem B1664299 : Blo 1663031 1664299 := bstep (se 1 (by rfl) ⟨1248224, by rfl⟩ : syracuseStep 1664299 = 2496449) B2496449
theorem B6743341 : Blo 1663031 6743341 := bstep (se 3 (by rfl) ⟨1264376, by rfl⟩ : syracuseStep 6743341 = 2528753) B2528753
theorem B1664311 : Blo 1663031 1664311 := bstep (se 1 (by rfl) ⟨1248233, by rfl⟩ : syracuseStep 1664311 = 2496467) B2496467
theorem B1664331 : Blo 1663031 1664331 := bstep (se 1 (by rfl) ⟨1248248, by rfl⟩ : syracuseStep 1664331 = 2496497) B2496497
theorem B1664343 : Blo 1663031 1664343 := bstep (se 1 (by rfl) ⟨1248257, by rfl⟩ : syracuseStep 1664343 = 2496515) B2496515
theorem B1664363 : Blo 1663031 1664363 := bstep (se 1 (by rfl) ⟨1248272, by rfl⟩ : syracuseStep 1664363 = 2496545) B2496545
theorem B1664375 : Blo 1663031 1664375 := bstep (se 1 (by rfl) ⟨1248281, by rfl⟩ : syracuseStep 1664375 = 2496563) B2496563
theorem B1664395 : Blo 1663031 1664395 := bstep (se 1 (by rfl) ⟨1248296, by rfl⟩ : syracuseStep 1664395 = 2496593) B2496593
theorem B1664407 : Blo 1663031 1664407 := bstep (se 1 (by rfl) ⟨1248305, by rfl⟩ : syracuseStep 1664407 = 2496611) B2496611
theorem B1664427 : Blo 1663031 1664427 := bstep (se 1 (by rfl) ⟨1248320, by rfl⟩ : syracuseStep 1664427 = 2496641) B2496641
theorem B1664439 : Blo 1663031 1664439 := bstep (se 1 (by rfl) ⟨1248329, by rfl⟩ : syracuseStep 1664439 = 2496659) B2496659
theorem B1664459 : Blo 1663031 1664459 := bstep (se 1 (by rfl) ⟨1248344, by rfl⟩ : syracuseStep 1664459 = 2496689) B2496689
theorem B1664471 : Blo 1663031 1664471 := bstep (se 1 (by rfl) ⟨1248353, by rfl⟩ : syracuseStep 1664471 = 2496707) B2496707
theorem B3745241 : Blo 1663031 3745241 := bstep (se 2 (by rfl) ⟨1404465, by rfl⟩ : syracuseStep 3745241 = 2808931) B2808931
theorem B28444121 : Blo 1663031 28444121 := bstep (se 2 (by rfl) ⟨10666545, by rfl⟩ : syracuseStep 28444121 = 21333091) B21333091
theorem B1664491 : Blo 1663031 1664491 := bstep (se 1 (by rfl) ⟨1248368, by rfl⟩ : syracuseStep 1664491 = 2496737) B2496737
theorem B1664503 : Blo 1663031 1664503 := bstep (se 1 (by rfl) ⟨1248377, by rfl⟩ : syracuseStep 1664503 = 2496755) B2496755
theorem B1664523 : Blo 1663031 1664523 := bstep (se 1 (by rfl) ⟨1248392, by rfl⟩ : syracuseStep 1664523 = 2496785) B2496785
theorem B6743569 : Blo 1663031 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1664535 : Blo 1663031 1664535 := bstep (se 1 (by rfl) ⟨1248401, by rfl⟩ : syracuseStep 1664535 = 2496803) B2496803
theorem B1664555 : Blo 1663031 1664555 := bstep (se 1 (by rfl) ⟨1248416, by rfl⟩ : syracuseStep 1664555 = 2496833) B2496833
theorem B3745331 : Blo 1663031 3745331 := bstep (se 1 (by rfl) ⟨2808998, by rfl⟩ : syracuseStep 3745331 = 5617997) B5617997
theorem B1664567 : Blo 1663031 1664567 := bstep (se 1 (by rfl) ⟨1248425, by rfl⟩ : syracuseStep 1664567 = 2496851) B2496851
theorem B1664587 : Blo 1663031 1664587 := bstep (se 1 (by rfl) ⟨1248440, by rfl⟩ : syracuseStep 1664587 = 2496881) B2496881
theorem B1664599 : Blo 1663031 1664599 := bstep (se 1 (by rfl) ⟨1248449, by rfl⟩ : syracuseStep 1664599 = 2496899) B2496899
theorem B3745367 : Blo 1663031 3745367 := bstep (se 1 (by rfl) ⟨2809025, by rfl⟩ : syracuseStep 3745367 = 5618051) B5618051
theorem B2106967 : Blo 1663031 2106967 := bstep (se 1 (by rfl) ⟨1580225, by rfl⟩ : syracuseStep 2106967 = 3160451) B3160451
theorem B1664619 : Blo 1663031 1664619 := bstep (se 1 (by rfl) ⟨1248464, by rfl⟩ : syracuseStep 1664619 = 2496929) B2496929
theorem B1664631 : Blo 1663031 1664631 := bstep (se 1 (by rfl) ⟨1248473, by rfl⟩ : syracuseStep 1664631 = 2496947) B2496947
theorem B6743683 : Blo 1663031 6743683 := bstep (se 1 (by rfl) ⟨5057762, by rfl⟩ : syracuseStep 6743683 = 10115525) B10115525
theorem B34162307 : Blo 1663031 34162307 := bstep (se 1 (by rfl) ⟨25621730, by rfl⟩ : syracuseStep 34162307 = 51243461) B51243461
theorem B1664651 : Blo 1663031 1664651 := bstep (se 1 (by rfl) ⟨1248488, by rfl⟩ : syracuseStep 1664651 = 2496977) B2496977
theorem B1664663 : Blo 1663031 1664663 := bstep (se 1 (by rfl) ⟨1248497, by rfl⟩ : syracuseStep 1664663 = 2496995) B2496995
theorem B1664683 : Blo 1663031 1664683 := bstep (se 1 (by rfl) ⟨1248512, by rfl⟩ : syracuseStep 1664683 = 2497025) B2497025
theorem B1664695 : Blo 1663031 1664695 := bstep (se 1 (by rfl) ⟨1248521, by rfl⟩ : syracuseStep 1664695 = 2497043) B2497043
theorem B1664715 : Blo 1663031 1664715 := bstep (se 1 (by rfl) ⟨1248536, by rfl⟩ : syracuseStep 1664715 = 2497073) B2497073
theorem B1664727 : Blo 1663031 1664727 := bstep (se 1 (by rfl) ⟨1248545, by rfl⟩ : syracuseStep 1664727 = 2497091) B2497091
theorem B1664747 : Blo 1663031 1664747 := bstep (se 1 (by rfl) ⟨1248560, by rfl⟩ : syracuseStep 1664747 = 2497121) B2497121
theorem B1664759 : Blo 1663031 1664759 := bstep (se 1 (by rfl) ⟨1248569, by rfl⟩ : syracuseStep 1664759 = 2497139) B2497139
theorem B3745547 : Blo 1663031 3745547 := bstep (se 1 (by rfl) ⟨2809160, by rfl⟩ : syracuseStep 3745547 = 5618321) B5618321
theorem B1664779 : Blo 1663031 1664779 := bstep (se 1 (by rfl) ⟨1248584, by rfl⟩ : syracuseStep 1664779 = 2497169) B2497169
theorem B9471761 : Blo 1663031 9471761 := bstep (se 2 (by rfl) ⟨3551910, by rfl⟩ : syracuseStep 9471761 = 7103821) B7103821
theorem B1664791 : Blo 1663031 1664791 := bstep (se 1 (by rfl) ⟨1248593, by rfl⟩ : syracuseStep 1664791 = 2497187) B2497187
theorem B1664811 : Blo 1663031 1664811 := bstep (se 1 (by rfl) ⟨1248608, by rfl⟩ : syracuseStep 1664811 = 2497217) B2497217
theorem B1664823 : Blo 1663031 1664823 := bstep (se 1 (by rfl) ⟨1248617, by rfl⟩ : syracuseStep 1664823 = 2497235) B2497235
theorem B3745601 : Blo 1663031 3745601 := bstep (se 2 (by rfl) ⟨1404600, by rfl⟩ : syracuseStep 3745601 = 2809201) B2809201
theorem B3999563 : Blo 1663031 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B1664843 : Blo 1663031 1664843 := bstep (se 1 (by rfl) ⟨1248632, by rfl⟩ : syracuseStep 1664843 = 2497265) B2497265
theorem B1664855 : Blo 1663031 1664855 := bstep (se 1 (by rfl) ⟨1248641, by rfl⟩ : syracuseStep 1664855 = 2497283) B2497283
theorem B1664875 : Blo 1663031 1664875 := bstep (se 1 (by rfl) ⟨1248656, by rfl⟩ : syracuseStep 1664875 = 2497313) B2497313
theorem B1664887 : Blo 1663031 1664887 := bstep (se 1 (by rfl) ⟨1248665, by rfl⟩ : syracuseStep 1664887 = 2497331) B2497331
theorem B3417985 : Blo 1663031 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B1664907 : Blo 1663031 1664907 := bstep (se 1 (by rfl) ⟨1248680, by rfl⟩ : syracuseStep 1664907 = 2497361) B2497361
theorem B2664343 : Blo 1663031 2664343 := bstep (se 1 (by rfl) ⟨1998257, by rfl⟩ : syracuseStep 2664343 = 3996515) B3996515
theorem B1664919 : Blo 1663031 1664919 := bstep (se 1 (by rfl) ⟨1248689, by rfl⟩ : syracuseStep 1664919 = 2497379) B2497379
theorem B1664939 : Blo 1663031 1664939 := bstep (se 1 (by rfl) ⟨1248704, by rfl⟩ : syracuseStep 1664939 = 2497409) B2497409
theorem B1664951 : Blo 1663031 1664951 := bstep (se 1 (by rfl) ⟨1248713, by rfl⟩ : syracuseStep 1664951 = 2497427) B2497427
theorem B5613515 : Blo 1663031 5613515 := bstep (se 1 (by rfl) ⟨4210136, by rfl⟩ : syracuseStep 5613515 = 8420273) B8420273
theorem B1664971 : Blo 1663031 1664971 := bstep (se 1 (by rfl) ⟨1248728, by rfl⟩ : syracuseStep 1664971 = 2497457) B2497457
theorem B1664983 : Blo 1663031 1664983 := bstep (se 1 (by rfl) ⟨1248737, by rfl⟩ : syracuseStep 1664983 = 2497475) B2497475
theorem B1665003 : Blo 1663031 1665003 := bstep (se 1 (by rfl) ⟨1248752, by rfl⟩ : syracuseStep 1665003 = 2497505) B2497505
theorem B1665015 : Blo 1663031 1665015 := bstep (se 1 (by rfl) ⟨1248761, by rfl⟩ : syracuseStep 1665015 = 2497523) B2497523
theorem B3745817 : Blo 1663031 3745817 := bstep (se 2 (by rfl) ⟨1404681, by rfl⟩ : syracuseStep 3745817 = 2809363) B2809363
theorem B24324131 : Blo 1663031 24324131 := bstep (se 1 (by rfl) ⟨18243098, by rfl⟩ : syracuseStep 24324131 = 36486197) B36486197
theorem B17082461 : Blo 1663031 17082461 := bstep (se 3 (by rfl) ⟨3202961, by rfl⟩ : syracuseStep 17082461 = 6405923) B6405923
theorem B3745907 : Blo 1663031 3745907 := bstep (se 1 (by rfl) ⟨2809430, by rfl⟩ : syracuseStep 3745907 = 5618861) B5618861
theorem B3745943 : Blo 1663031 3745943 := bstep (se 1 (by rfl) ⟨2809457, by rfl⟩ : syracuseStep 3745943 = 5618915) B5618915
theorem B5613785 : Blo 1663031 5613785 := bstep (se 2 (by rfl) ⟨2105169, by rfl⟩ : syracuseStep 5613785 = 4210339) B4210339
theorem B4213043 : Blo 1663031 4213043 := bstep (se 1 (by rfl) ⟨3159782, by rfl⟩ : syracuseStep 4213043 = 6319565) B6319565
theorem B3746123 : Blo 1663031 3746123 := bstep (se 1 (by rfl) ⟨2809592, by rfl⟩ : syracuseStep 3746123 = 5619185) B5619185
theorem B6318425 : Blo 1663031 6318425 := bstep (se 2 (by rfl) ⟨2369409, by rfl⟩ : syracuseStep 6318425 = 4738819) B4738819
theorem B57616757 : Blo 1663031 57616757 := bstep (se 5 (by rfl) ⟨2700785, by rfl⟩ : syracuseStep 57616757 = 5401571) B5401571
theorem B3746177 : Blo 1663031 3746177 := bstep (se 2 (by rfl) ⟨1404816, by rfl⟩ : syracuseStep 3746177 = 2809633) B2809633
theorem B2369945 : Blo 1663031 2369945 := bstep (se 2 (by rfl) ⟨888729, by rfl⟩ : syracuseStep 2369945 = 1777459) B1777459
theorem B2665099 : Blo 1663031 2665099 := bstep (se 1 (by rfl) ⟨1998824, by rfl⟩ : syracuseStep 2665099 = 3997649) B3997649
theorem B6400691 : Blo 1663031 6400691 := bstep (se 1 (by rfl) ⟨4800518, by rfl⟩ : syracuseStep 6400691 = 9601037) B9601037
theorem B4213579 : Blo 1663031 4213579 := bstep (se 1 (by rfl) ⟨3160184, by rfl⟩ : syracuseStep 4213579 = 6320369) B6320369
theorem B12979037 : Blo 1663031 12979037 := bstep (se 3 (by rfl) ⟨2433569, by rfl⟩ : syracuseStep 12979037 = 4867139) B4867139
theorem B14207845 : Blo 1663031 14207845 := bstep (se 4 (by rfl) ⟨1331985, by rfl⟩ : syracuseStep 14207845 = 2663971) B2663971
theorem B8424323 : Blo 1663031 8424323 := bstep (se 1 (by rfl) ⟨6318242, by rfl⟩ : syracuseStep 8424323 = 12636485) B12636485
theorem B5614487 : Blo 1663031 5614487 := bstep (se 1 (by rfl) ⟨4210865, by rfl⟩ : syracuseStep 5614487 = 8421731) B8421731
theorem B29617073 : Blo 1663031 29617073 := bstep (se 2 (by rfl) ⟨11106402, by rfl⟩ : syracuseStep 29617073 = 22212805) B22212805
theorem B4213721 : Blo 1663031 4213721 := bstep (se 2 (by rfl) ⟨1580145, by rfl⟩ : syracuseStep 4213721 = 3160291) B3160291
theorem B12643289 : Blo 1663031 12643289 := bstep (se 2 (by rfl) ⟨4741233, by rfl⟩ : syracuseStep 12643289 = 9482467) B9482467
theorem B2370583 : Blo 1663031 2370583 := bstep (se 1 (by rfl) ⟨1777937, by rfl⟩ : syracuseStep 2370583 = 3555875) B3555875
theorem B12807233 : Blo 1663031 12807233 := bstep (se 2 (by rfl) ⟨4802712, by rfl⟩ : syracuseStep 12807233 = 9605425) B9605425
theorem B2247769 : Blo 1663031 2247769 := bstep (se 2 (by rfl) ⟨842913, by rfl⟩ : syracuseStep 2247769 = 1685827) B1685827
theorem B1870987 : Blo 1663031 1870987 := bstep (se 1 (by rfl) ⟨1403240, by rfl⟩ : syracuseStep 1870987 = 2806481) B2806481
theorem B5999761 : Blo 1663031 5999761 := bstep (se 2 (by rfl) ⟨2249910, by rfl⟩ : syracuseStep 5999761 = 4499821) B4499821
theorem B2845847 : Blo 1663031 2845847 := bstep (se 1 (by rfl) ⟨2134385, by rfl⟩ : syracuseStep 2845847 = 4268771) B4268771
theorem B26987701 : Blo 1663031 26987701 := bstep (se 5 (by rfl) ⟨1265048, by rfl⟩ : syracuseStep 26987701 = 2530097) B2530097
theorem B1871095 : Blo 1663031 1871095 := bstep (se 1 (by rfl) ⟨1403321, by rfl⟩ : syracuseStep 1871095 = 2806643) B2806643
theorem B60738821 : Blo 1663031 60738821 := bstep (se 4 (by rfl) ⟨5694264, by rfl⟩ : syracuseStep 60738821 = 11388529) B11388529
theorem B3796249 : Blo 1663031 3796249 := bstep (se 2 (by rfl) ⟨1423593, by rfl⟩ : syracuseStep 3796249 = 2847187) B2847187
theorem B40496429 : Blo 1663031 40496429 := bstep (se 3 (by rfl) ⟨7593080, by rfl⟩ : syracuseStep 40496429 = 15186161) B15186161
theorem B1871275 : Blo 1663031 1871275 := bstep (se 1 (by rfl) ⟨1403456, by rfl⟩ : syracuseStep 1871275 = 2806913) B2806913
theorem B5615027 : Blo 1663031 5615027 := bstep (se 1 (by rfl) ⟨4211270, by rfl⟩ : syracuseStep 5615027 = 8422541) B8422541
theorem B3157451 : Blo 1663031 3157451 := bstep (se 1 (by rfl) ⟨2368088, by rfl⟩ : syracuseStep 3157451 = 4736177) B4736177
theorem B1871383 : Blo 1663031 1871383 := bstep (se 1 (by rfl) ⟨1403537, by rfl⟩ : syracuseStep 1871383 = 2807075) B2807075
theorem B3157633 : Blo 1663031 3157633 := bstep (se 2 (by rfl) ⟨1184112, by rfl⟩ : syracuseStep 3157633 = 2368225) B2368225
theorem B5615297 : Blo 1663031 5615297 := bstep (se 2 (by rfl) ⟨2105736, by rfl⟩ : syracuseStep 5615297 = 4211473) B4211473
theorem B5058251 : Blo 1663031 5058251 := bstep (se 1 (by rfl) ⟨3793688, by rfl⟩ : syracuseStep 5058251 = 7587377) B7587377
theorem B1871563 : Blo 1663031 1871563 := bstep (se 1 (by rfl) ⟨1403672, by rfl⟩ : syracuseStep 1871563 = 2807345) B2807345
theorem B4738763 : Blo 1663031 4738763 := bstep (se 1 (by rfl) ⟨3554072, by rfl⟩ : syracuseStep 4738763 = 7108145) B7108145
theorem B2666201 : Blo 1663031 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B4214551 : Blo 1663031 4214551 := bstep (se 1 (by rfl) ⟨3160913, by rfl⟩ : syracuseStep 4214551 = 6321827) B6321827
theorem B14208803 : Blo 1663031 14208803 := bstep (se 1 (by rfl) ⟨10656602, by rfl⟩ : syracuseStep 14208803 = 21313205) B21313205
theorem B1871671 : Blo 1663031 1871671 := bstep (se 1 (by rfl) ⟨1403753, by rfl⟩ : syracuseStep 1871671 = 2807507) B2807507
theorem B6320051 : Blo 1663031 6320051 := bstep (se 1 (by rfl) ⟨4740038, by rfl⟩ : syracuseStep 6320051 = 9480077) B9480077
theorem B6320065 : Blo 1663031 6320065 := bstep (se 2 (by rfl) ⟨2370024, by rfl⟩ : syracuseStep 6320065 = 4740049) B4740049
theorem B1871851 : Blo 1663031 1871851 := bstep (se 1 (by rfl) ⟨1403888, by rfl⟩ : syracuseStep 1871851 = 2807777) B2807777
theorem B9482285 : Blo 1663031 9482285 := bstep (se 3 (by rfl) ⟨1777928, by rfl⟩ : syracuseStep 9482285 = 3555857) B3555857
theorem B1871959 : Blo 1663031 1871959 := bstep (se 1 (by rfl) ⟨1403969, by rfl⟩ : syracuseStep 1871959 = 2807939) B2807939
theorem B2494553 : Blo 1663031 2494553 := bstep (se 2 (by rfl) ⟨935457, by rfl⟩ : syracuseStep 2494553 = 1870915) B1870915
theorem B4739161 : Blo 1663031 4739161 := bstep (se 2 (by rfl) ⟨1777185, by rfl⟩ : syracuseStep 4739161 = 3554371) B3554371
theorem B2494667 : Blo 1663031 2494667 := bstep (se 1 (by rfl) ⟨1871000, by rfl⟩ : syracuseStep 2494667 = 3742001) B3742001
theorem B2601163 : Blo 1663031 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B2494679 : Blo 1663031 2494679 := bstep (se 1 (by rfl) ⟨1871009, by rfl⟩ : syracuseStep 2494679 = 3742019) B3742019
theorem B5615837 : Blo 1663031 5615837 := bstep (se 3 (by rfl) ⟨1052969, by rfl⟩ : syracuseStep 5615837 = 2105939) B2105939
theorem B1872139 : Blo 1663031 1872139 := bstep (se 1 (by rfl) ⟨1404104, by rfl⟩ : syracuseStep 1872139 = 2808209) B2808209
theorem B2494745 : Blo 1663031 2494745 := bstep (se 2 (by rfl) ⟨935529, by rfl⟩ : syracuseStep 2494745 = 1871059) B1871059
theorem B3158347 : Blo 1663031 3158347 := bstep (se 1 (by rfl) ⟨2368760, by rfl⟩ : syracuseStep 3158347 = 4737521) B4737521
theorem B1872247 : Blo 1663031 1872247 := bstep (se 1 (by rfl) ⟨1404185, by rfl⟩ : syracuseStep 1872247 = 2808371) B2808371
theorem B2494859 : Blo 1663031 2494859 := bstep (se 1 (by rfl) ⟨1871144, by rfl⟩ : syracuseStep 2494859 = 3742289) B3742289
theorem B3158423 : Blo 1663031 3158423 := bstep (se 1 (by rfl) ⟨2368817, by rfl⟩ : syracuseStep 3158423 = 4737635) B4737635
theorem B2494871 : Blo 1663031 2494871 := bstep (se 1 (by rfl) ⟨1871153, by rfl⟩ : syracuseStep 2494871 = 3742307) B3742307
theorem B2494937 : Blo 1663031 2494937 := bstep (se 2 (by rfl) ⟨935601, by rfl⟩ : syracuseStep 2494937 = 1871203) B1871203
theorem B1872427 : Blo 1663031 1872427 := bstep (se 1 (by rfl) ⟨1404320, by rfl⟩ : syracuseStep 1872427 = 2808641) B2808641
theorem B10662445 : Blo 1663031 10662445 := bstep (se 3 (by rfl) ⟨1999208, by rfl⟩ : syracuseStep 10662445 = 3998417) B3998417
theorem B10121773 : Blo 1663031 10121773 := bstep (se 3 (by rfl) ⟨1897832, by rfl⟩ : syracuseStep 10121773 = 3795665) B3795665
theorem B8213057 : Blo 1663031 8213057 := bstep (se 2 (by rfl) ⟨3079896, by rfl⟩ : syracuseStep 8213057 = 6159793) B6159793
theorem B2495051 : Blo 1663031 2495051 := bstep (se 1 (by rfl) ⟨1871288, by rfl⟩ : syracuseStep 2495051 = 3742577) B3742577
theorem B2495063 : Blo 1663031 2495063 := bstep (se 1 (by rfl) ⟨1871297, by rfl⟩ : syracuseStep 2495063 = 3742595) B3742595
theorem B7107203 : Blo 1663031 7107203 := bstep (se 1 (by rfl) ⟨5330402, by rfl⟩ : syracuseStep 7107203 = 10660805) B10660805
theorem B28430999 : Blo 1663031 28430999 := bstep (se 1 (by rfl) ⟨21323249, by rfl⟩ : syracuseStep 28430999 = 42646499) B42646499
theorem B1872535 : Blo 1663031 1872535 := bstep (se 1 (by rfl) ⟨1404401, by rfl⟩ : syracuseStep 1872535 = 2808803) B2808803
theorem B2495129 : Blo 1663031 2495129 := bstep (se 2 (by rfl) ⟨935673, by rfl⟩ : syracuseStep 2495129 = 1871347) B1871347
theorem B2495243 : Blo 1663031 2495243 := bstep (se 1 (by rfl) ⟨1871432, by rfl⟩ : syracuseStep 2495243 = 3742865) B3742865
theorem B6402833 : Blo 1663031 6402833 := bstep (se 2 (by rfl) ⟨2401062, by rfl⟩ : syracuseStep 6402833 = 4802125) B4802125
theorem B2495255 : Blo 1663031 2495255 := bstep (se 1 (by rfl) ⟨1871441, by rfl⟩ : syracuseStep 2495255 = 3742883) B3742883
theorem B1872715 : Blo 1663031 1872715 := bstep (se 1 (by rfl) ⟨1404536, by rfl⟩ : syracuseStep 1872715 = 2809073) B2809073
theorem B2495321 : Blo 1663031 2495321 := bstep (se 2 (by rfl) ⟨935745, by rfl⟩ : syracuseStep 2495321 = 1871491) B1871491
theorem B17986481 : Blo 1663031 17986481 := bstep (se 2 (by rfl) ⟨6744930, by rfl⟩ : syracuseStep 17986481 = 13489861) B13489861
theorem B9474995 : Blo 1663031 9474995 := bstep (se 1 (by rfl) ⟨7106246, by rfl⟩ : syracuseStep 9474995 = 14212493) B14212493
theorem B1872823 : Blo 1663031 1872823 := bstep (se 1 (by rfl) ⟨1404617, by rfl⟩ : syracuseStep 1872823 = 2809235) B2809235
theorem B2495435 : Blo 1663031 2495435 := bstep (se 1 (by rfl) ⟨1871576, by rfl⟩ : syracuseStep 2495435 = 3743153) B3743153
theorem B2495447 : Blo 1663031 2495447 := bstep (se 1 (by rfl) ⟨1871585, by rfl⟩ : syracuseStep 2495447 = 3743171) B3743171
theorem B23983121 : Blo 1663031 23983121 := bstep (se 2 (by rfl) ⟨8993670, by rfl⟩ : syracuseStep 23983121 = 17987341) B17987341
theorem B2495513 : Blo 1663031 2495513 := bstep (se 2 (by rfl) ⟨935817, by rfl⟩ : syracuseStep 2495513 = 1871635) B1871635
theorem B3159091 : Blo 1663031 3159091 := bstep (se 1 (by rfl) ⟨2369318, by rfl⟩ : syracuseStep 3159091 = 4738637) B4738637
theorem B2806859 : Blo 1663031 2806859 := bstep (se 1 (by rfl) ⟨2105144, by rfl⟩ : syracuseStep 2806859 = 4210289) B4210289
theorem B1873003 : Blo 1663031 1873003 := bstep (se 1 (by rfl) ⟨1404752, by rfl⟩ : syracuseStep 1873003 = 2809505) B2809505
theorem B2495627 : Blo 1663031 2495627 := bstep (se 1 (by rfl) ⟨1871720, by rfl⟩ : syracuseStep 2495627 = 3743441) B3743441
theorem B2495639 : Blo 1663031 2495639 := bstep (se 1 (by rfl) ⟨1871729, by rfl⟩ : syracuseStep 2495639 = 3743459) B3743459
theorem B2806987 : Blo 1663031 2806987 := bstep (se 1 (by rfl) ⟨2105240, by rfl⟩ : syracuseStep 2806987 = 4210481) B4210481
theorem B1873111 : Blo 1663031 1873111 := bstep (se 1 (by rfl) ⟨1404833, by rfl⟩ : syracuseStep 1873111 = 2809667) B2809667
theorem B2495705 : Blo 1663031 2495705 := bstep (se 2 (by rfl) ⟨935889, by rfl⟩ : syracuseStep 2495705 = 1871779) B1871779
theorem B12637457 : Blo 1663031 12637457 := bstep (se 2 (by rfl) ⟨4739046, by rfl⟩ : syracuseStep 12637457 = 9478093) B9478093
theorem B3159319 : Blo 1663031 3159319 := bstep (se 1 (by rfl) ⟨2369489, by rfl⟩ : syracuseStep 3159319 = 4738979) B4738979
theorem B4740403 : Blo 1663031 4740403 := bstep (se 1 (by rfl) ⟨3555302, by rfl⟩ : syracuseStep 4740403 = 7110605) B7110605
theorem B2495819 : Blo 1663031 2495819 := bstep (se 1 (by rfl) ⟨1871864, by rfl⟩ : syracuseStep 2495819 = 3743729) B3743729
theorem B5616971 : Blo 1663031 5616971 := bstep (se 1 (by rfl) ⟨4212728, by rfl⟩ : syracuseStep 5616971 = 8425457) B8425457
theorem B2495831 : Blo 1663031 2495831 := bstep (se 1 (by rfl) ⟨1871873, by rfl⟩ : syracuseStep 2495831 = 3743747) B3743747
theorem B2807129 : Blo 1663031 2807129 := bstep (se 2 (by rfl) ⟨1052673, by rfl⟩ : syracuseStep 2807129 = 2105347) B2105347
theorem B30365027 : Blo 1663031 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B3159425 : Blo 1663031 3159425 := bstep (se 2 (by rfl) ⟨1184784, by rfl⟩ : syracuseStep 3159425 = 2369569) B2369569
theorem B38417813 : Blo 1663031 38417813 := bstep (se 6 (by rfl) ⟨900417, by rfl⟩ : syracuseStep 38417813 = 1800835) B1800835
theorem B2495897 : Blo 1663031 2495897 := bstep (se 2 (by rfl) ⟨935961, by rfl⟩ : syracuseStep 2495897 = 1871923) B1871923
theorem B2807257 : Blo 1663031 2807257 := bstep (se 2 (by rfl) ⟨1052721, by rfl⟩ : syracuseStep 2807257 = 2105443) B2105443
theorem B2496011 : Blo 1663031 2496011 := bstep (se 1 (by rfl) ⟨1872008, by rfl⟩ : syracuseStep 2496011 = 3744017) B3744017
theorem B2496023 : Blo 1663031 2496023 := bstep (se 1 (by rfl) ⟨1872017, by rfl⟩ : syracuseStep 2496023 = 3744035) B3744035
theorem B3159577 : Blo 1663031 3159577 := bstep (se 2 (by rfl) ⟨1184841, by rfl⟩ : syracuseStep 3159577 = 2369683) B2369683
theorem B7992877 : Blo 1663031 7992877 := bstep (se 3 (by rfl) ⟨1498664, by rfl⟩ : syracuseStep 7992877 = 2997329) B2997329
theorem B2496089 : Blo 1663031 2496089 := bstep (se 2 (by rfl) ⟨936033, by rfl⟩ : syracuseStep 2496089 = 1872067) B1872067
theorem B5617241 : Blo 1663031 5617241 := bstep (se 2 (by rfl) ⟨2106465, by rfl⟩ : syracuseStep 5617241 = 4212931) B4212931
theorem B97310321 : Blo 1663031 97310321 := bstep (se 2 (by rfl) ⟨36491370, by rfl⟩ : syracuseStep 97310321 = 72982741) B72982741
theorem B12629681 : Blo 1663031 12629681 := bstep (se 2 (by rfl) ⟨4736130, by rfl⟩ : syracuseStep 12629681 = 9472261) B9472261
theorem B2496203 : Blo 1663031 2496203 := bstep (se 1 (by rfl) ⟨1872152, by rfl⟩ : syracuseStep 2496203 = 3744305) B3744305
theorem B2496215 : Blo 1663031 2496215 := bstep (se 1 (by rfl) ⟨1872161, by rfl⟩ : syracuseStep 2496215 = 3744323) B3744323
theorem B5330711 : Blo 1663031 5330711 := bstep (se 1 (by rfl) ⟨3998033, by rfl⟩ : syracuseStep 5330711 = 7996067) B7996067
theorem B2496281 : Blo 1663031 2496281 := bstep (se 2 (by rfl) ⟨936105, by rfl⟩ : syracuseStep 2496281 = 1872211) B1872211
theorem B2496395 : Blo 1663031 2496395 := bstep (se 1 (by rfl) ⟨1872296, by rfl⟩ : syracuseStep 2496395 = 3744593) B3744593
theorem B2496407 : Blo 1663031 2496407 := bstep (se 1 (by rfl) ⟨1872305, by rfl⟩ : syracuseStep 2496407 = 3744611) B3744611
theorem B17078195 : Blo 1663031 17078195 := bstep (se 1 (by rfl) ⟨12808646, by rfl⟩ : syracuseStep 17078195 = 25617293) B25617293
theorem B2496473 : Blo 1663031 2496473 := bstep (se 2 (by rfl) ⟨936177, by rfl⟩ : syracuseStep 2496473 = 1872355) B1872355
theorem B5994499 : Blo 1663031 5994499 := bstep (se 1 (by rfl) ⟨4495874, by rfl⟩ : syracuseStep 5994499 = 8991749) B8991749
theorem B2807831 : Blo 1663031 2807831 := bstep (se 1 (by rfl) ⟨2105873, by rfl⟩ : syracuseStep 2807831 = 4211747) B4211747
theorem B15177773 : Blo 1663031 15177773 := bstep (se 3 (by rfl) ⟨2845832, by rfl⟩ : syracuseStep 15177773 = 5691665) B5691665
theorem B2496587 : Blo 1663031 2496587 := bstep (se 1 (by rfl) ⟨1872440, by rfl⟩ : syracuseStep 2496587 = 3744881) B3744881
theorem B2496599 : Blo 1663031 2496599 := bstep (se 1 (by rfl) ⟨1872449, by rfl⟩ : syracuseStep 2496599 = 3744899) B3744899
theorem B12630167 : Blo 1663031 12630167 := bstep (se 1 (by rfl) ⟨9472625, by rfl⟩ : syracuseStep 12630167 = 18945251) B18945251
theorem B2807959 : Blo 1663031 2807959 := bstep (se 1 (by rfl) ⟨2105969, by rfl⟩ : syracuseStep 2807959 = 4211939) B4211939
theorem B2496665 : Blo 1663031 2496665 := bstep (se 2 (by rfl) ⟨936249, by rfl⟩ : syracuseStep 2496665 = 1872499) B1872499
theorem B3741875 : Blo 1663031 3741875 := bstep (se 1 (by rfl) ⟨2806406, by rfl⟩ : syracuseStep 3741875 = 5612813) B5612813
theorem B3553483 : Blo 1663031 3553483 := bstep (se 1 (by rfl) ⟨2665112, by rfl⟩ : syracuseStep 3553483 = 5330225) B5330225
theorem B3741911 : Blo 1663031 3741911 := bstep (se 1 (by rfl) ⟨2806433, by rfl⟩ : syracuseStep 3741911 = 5612867) B5612867
theorem B7108829 : Blo 1663031 7108829 := bstep (se 3 (by rfl) ⟨1332905, by rfl⟩ : syracuseStep 7108829 = 2665811) B2665811
theorem B2496779 : Blo 1663031 2496779 := bstep (se 1 (by rfl) ⟨1872584, by rfl⟩ : syracuseStep 2496779 = 3745169) B3745169
theorem B2496791 : Blo 1663031 2496791 := bstep (se 1 (by rfl) ⟨1872593, by rfl⟩ : syracuseStep 2496791 = 3745187) B3745187
theorem B5617943 : Blo 1663031 5617943 := bstep (se 1 (by rfl) ⟨4213457, by rfl⟩ : syracuseStep 5617943 = 8426915) B8426915
theorem B2496857 : Blo 1663031 2496857 := bstep (se 2 (by rfl) ⟨936321, by rfl⟩ : syracuseStep 2496857 = 1872643) B1872643
theorem B9476453 : Blo 1663031 9476453 := bstep (se 4 (by rfl) ⟨888417, by rfl⟩ : syracuseStep 9476453 = 1776835) B1776835
theorem B1776011 : Blo 1663031 1776011 := bstep (se 1 (by rfl) ⟨1332008, by rfl⟩ : syracuseStep 1776011 = 2664017) B2664017
theorem B3742091 : Blo 1663031 3742091 := bstep (se 1 (by rfl) ⟨2806568, by rfl⟩ : syracuseStep 3742091 = 5613137) B5613137
theorem B3742145 : Blo 1663031 3742145 := bstep (se 2 (by rfl) ⟨1403304, by rfl⟩ : syracuseStep 3742145 = 2806609) B2806609
theorem B2496971 : Blo 1663031 2496971 := bstep (se 1 (by rfl) ⟨1872728, by rfl⟩ : syracuseStep 2496971 = 3745457) B3745457
theorem B2496983 : Blo 1663031 2496983 := bstep (se 1 (by rfl) ⟨1872737, by rfl⟩ : syracuseStep 2496983 = 3745475) B3745475
theorem B8428049 : Blo 1663031 8428049 := bstep (se 2 (by rfl) ⟨3160518, by rfl⟩ : syracuseStep 8428049 = 6321037) B6321037
theorem B2497049 : Blo 1663031 2497049 := bstep (se 2 (by rfl) ⟨936393, by rfl⟩ : syracuseStep 2497049 = 1872787) B1872787
theorem B2497163 : Blo 1663031 2497163 := bstep (se 1 (by rfl) ⟨1872872, by rfl⟩ : syracuseStep 2497163 = 3745745) B3745745
theorem B2497175 : Blo 1663031 2497175 := bstep (se 1 (by rfl) ⟨1872881, by rfl⟩ : syracuseStep 2497175 = 3745763) B3745763
theorem B3742361 : Blo 1663031 3742361 := bstep (se 2 (by rfl) ⟨1403385, by rfl⟩ : syracuseStep 3742361 = 2806771) B2806771
theorem B8428211 : Blo 1663031 8428211 := bstep (se 1 (by rfl) ⟨6321158, by rfl⟩ : syracuseStep 8428211 = 12642317) B12642317
theorem B2497241 : Blo 1663031 2497241 := bstep (se 2 (by rfl) ⟨936465, by rfl⟩ : syracuseStep 2497241 = 1872931) B1872931
theorem B3742451 : Blo 1663031 3742451 := bstep (se 1 (by rfl) ⟨2806838, by rfl⟩ : syracuseStep 3742451 = 5613677) B5613677
theorem B2808587 : Blo 1663031 2808587 := bstep (se 1 (by rfl) ⟨2106440, by rfl⟩ : syracuseStep 2808587 = 4212881) B4212881
theorem B3742487 : Blo 1663031 3742487 := bstep (se 1 (by rfl) ⟨2806865, by rfl⟩ : syracuseStep 3742487 = 5613731) B5613731
theorem B9476909 : Blo 1663031 9476909 := bstep (se 3 (by rfl) ⟨1776920, by rfl⟩ : syracuseStep 9476909 = 3553841) B3553841
theorem B5618483 : Blo 1663031 5618483 := bstep (se 1 (by rfl) ⟨4213862, by rfl⟩ : syracuseStep 5618483 = 8427725) B8427725
theorem B3160883 : Blo 1663031 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B2497355 : Blo 1663031 2497355 := bstep (se 1 (by rfl) ⟨1873016, by rfl⟩ : syracuseStep 2497355 = 3746033) B3746033
theorem B2497367 : Blo 1663031 2497367 := bstep (se 1 (by rfl) ⟨1873025, by rfl⟩ : syracuseStep 2497367 = 3746051) B3746051
theorem B2808715 : Blo 1663031 2808715 := bstep (se 1 (by rfl) ⟨2106536, by rfl⟩ : syracuseStep 2808715 = 4213073) B4213073
theorem B7109527 : Blo 1663031 7109527 := bstep (se 1 (by rfl) ⟨5332145, by rfl⟩ : syracuseStep 7109527 = 10664291) B10664291
theorem B2497433 : Blo 1663031 2497433 := bstep (se 2 (by rfl) ⟨936537, by rfl⟩ : syracuseStep 2497433 = 1873075) B1873075
theorem B1686443 : Blo 1663031 1686443 := bstep (se 1 (by rfl) ⟨1264832, by rfl⟩ : syracuseStep 1686443 = 2529665) B2529665
theorem B3742667 : Blo 1663031 3742667 := bstep (se 1 (by rfl) ⟨2807000, by rfl⟩ : syracuseStep 3742667 = 5614001) B5614001
theorem B3742721 : Blo 1663031 3742721 := bstep (se 2 (by rfl) ⟨1403520, by rfl⟩ : syracuseStep 3742721 = 2807041) B2807041
theorem B2497547 : Blo 1663031 2497547 := bstep (se 1 (by rfl) ⟨1873160, by rfl⟩ : syracuseStep 2497547 = 3746321) B3746321
theorem B2808857 : Blo 1663031 2808857 := bstep (se 2 (by rfl) ⟨1053321, by rfl⟩ : syracuseStep 2808857 = 2106643) B2106643
theorem B5618753 : Blo 1663031 5618753 := bstep (se 2 (by rfl) ⟨2107032, by rfl⟩ : syracuseStep 5618753 = 4214065) B4214065
theorem B5332043 : Blo 1663031 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B3996823 : Blo 1663031 3996823 := bstep (se 1 (by rfl) ⟨2997617, by rfl⟩ : syracuseStep 3996823 = 5995235) B5995235
theorem B2808985 : Blo 1663031 2808985 := bstep (se 2 (by rfl) ⟨1053369, by rfl⟩ : syracuseStep 2808985 = 2106739) B2106739
theorem B3742937 : Blo 1663031 3742937 := bstep (se 2 (by rfl) ⟨1403601, by rfl⟩ : syracuseStep 3742937 = 2807203) B2807203
theorem B3743027 : Blo 1663031 3743027 := bstep (se 1 (by rfl) ⟨2807270, by rfl⟩ : syracuseStep 3743027 = 5614541) B5614541
theorem B13491521 : Blo 1663031 13491521 := bstep (se 2 (by rfl) ⟨5059320, by rfl⟩ : syracuseStep 13491521 = 10118641) B10118641
theorem B4209995 : Blo 1663031 4209995 := bstep (se 1 (by rfl) ⟨3157496, by rfl⟩ : syracuseStep 4209995 = 6314993) B6314993
theorem B3743063 : Blo 1663031 3743063 := bstep (se 1 (by rfl) ⟨2807297, by rfl⟩ : syracuseStep 3743063 = 5614595) B5614595
theorem B1777015 : Blo 1663031 1777015 := bstep (se 1 (by rfl) ⟨1332761, by rfl⟩ : syracuseStep 1777015 = 2665523) B2665523
theorem B8420759 : Blo 1663031 8420759 := bstep (se 1 (by rfl) ⟨6315569, by rfl⟩ : syracuseStep 8420759 = 12631139) B12631139
theorem B9477593 : Blo 1663031 9477593 := bstep (se 2 (by rfl) ⟨3554097, by rfl⟩ : syracuseStep 9477593 = 7108195) B7108195
theorem B3743243 : Blo 1663031 3743243 := bstep (se 1 (by rfl) ⟨2807432, by rfl⟩ : syracuseStep 3743243 = 5614865) B5614865
theorem B3554867 : Blo 1663031 3554867 := bstep (se 1 (by rfl) ⟨2666150, by rfl⟩ : syracuseStep 3554867 = 5332301) B5332301
theorem B3743297 : Blo 1663031 3743297 := bstep (se 2 (by rfl) ⟨1403736, by rfl⟩ : syracuseStep 3743297 = 2807473) B2807473
theorem B3202649 : Blo 1663031 3202649 := bstep (se 2 (by rfl) ⟨1200993, by rfl⟩ : syracuseStep 3202649 = 2401987) B2401987
theorem B5619293 : Blo 1663031 5619293 := bstep (se 3 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 5619293 = 2107235) B2107235
theorem B28802765 : Blo 1663031 28802765 := bstep (se 3 (by rfl) ⟨5400518, by rfl⟩ : syracuseStep 28802765 = 10801037) B10801037
theorem B1998551 : Blo 1663031 1998551 := bstep (se 1 (by rfl) ⟨1498913, by rfl⟩ : syracuseStep 1998551 = 2997827) B2997827
theorem B2809559 : Blo 1663031 2809559 := bstep (se 1 (by rfl) ⟨2107169, by rfl⟩ : syracuseStep 2809559 = 4214339) B4214339
theorem B3743513 : Blo 1663031 3743513 := bstep (se 2 (by rfl) ⟨1403817, by rfl⟩ : syracuseStep 3743513 = 2807635) B2807635
theorem B5332787 : Blo 1663031 5332787 := bstep (se 1 (by rfl) ⟨3999590, by rfl⟩ : syracuseStep 5332787 = 7999181) B7999181
theorem B2809687 : Blo 1663031 2809687 := bstep (se 1 (by rfl) ⟨2107265, by rfl⟩ : syracuseStep 2809687 = 4214531) B4214531
theorem B3743603 : Blo 1663031 3743603 := bstep (se 1 (by rfl) ⟨2807702, by rfl⟩ : syracuseStep 3743603 = 5615405) B5615405
theorem B3743639 : Blo 1663031 3743639 := bstep (se 1 (by rfl) ⟨2807729, by rfl⟩ : syracuseStep 3743639 = 5615459) B5615459
theorem B15998897 : Blo 1663031 15998897 := bstep (se 2 (by rfl) ⟨5999586, by rfl⟩ : syracuseStep 15998897 = 11999173) B11999173
theorem B40468403 : Blo 1663031 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B2105291 : Blo 1663031 2105291 := bstep (se 1 (by rfl) ⟨1578968, by rfl⟩ : syracuseStep 2105291 = 3157937) B3157937
theorem B1663035 : Blo 1663031 1663035 := bstep (se 1 (by rfl) ⟨1247276, by rfl⟩ : syracuseStep 1663035 = 2494553) B2494553
theorem B4210775 : Blo 1663031 4210775 := bstep (se 1 (by rfl) ⟨3158081, by rfl⟩ : syracuseStep 4210775 = 6316163) B6316163
theorem B1663111 : Blo 1663031 1663111 := bstep (se 1 (by rfl) ⟨1247333, by rfl⟩ : syracuseStep 1663111 = 2494667) B2494667
theorem B1663119 : Blo 1663031 1663119 := bstep (se 1 (by rfl) ⟨1247339, by rfl⟩ : syracuseStep 1663119 = 2494679) B2494679
theorem B3743891 : Blo 1663031 3743891 := bstep (se 1 (by rfl) ⟨2807918, by rfl⟩ : syracuseStep 3743891 = 5615837) B5615837
theorem B1663163 : Blo 1663031 1663163 := bstep (se 1 (by rfl) ⟨1247372, by rfl⟩ : syracuseStep 1663163 = 2494745) B2494745
theorem B8421569 : Blo 1663031 8421569 := bstep (se 2 (by rfl) ⟨3158088, by rfl⟩ : syracuseStep 8421569 = 6316177) B6316177
theorem B3743945 : Blo 1663031 3743945 := bstep (se 2 (by rfl) ⟨1403979, by rfl⟩ : syracuseStep 3743945 = 2807959) B2807959
theorem B1663239 : Blo 1663031 1663239 := bstep (se 1 (by rfl) ⟨1247429, by rfl⟩ : syracuseStep 1663239 = 2494859) B2494859
theorem B1663247 : Blo 1663031 1663247 := bstep (se 1 (by rfl) ⟨1247435, by rfl⟩ : syracuseStep 1663247 = 2494871) B2494871
theorem B2105615 : Blo 1663031 2105615 := bstep (se 1 (by rfl) ⟨1579211, by rfl⟩ : syracuseStep 2105615 = 3158423) B3158423
theorem B4210987 : Blo 1663031 4210987 := bstep (se 1 (by rfl) ⟨3158240, by rfl⟩ : syracuseStep 4210987 = 6316481) B6316481
theorem B1663291 : Blo 1663031 1663291 := bstep (se 1 (by rfl) ⟨1247468, by rfl⟩ : syracuseStep 1663291 = 2494937) B2494937
theorem B1663367 : Blo 1663031 1663367 := bstep (se 1 (by rfl) ⟨1247525, by rfl⟩ : syracuseStep 1663367 = 2495051) B2495051
theorem B1663375 : Blo 1663031 1663375 := bstep (se 1 (by rfl) ⟨1247531, by rfl⟩ : syracuseStep 1663375 = 2495063) B2495063
theorem B1999247 : Blo 1663031 1999247 := bstep (se 1 (by rfl) ⟨1499435, by rfl⟩ : syracuseStep 1999247 = 2998871) B2998871
theorem B4211129 : Blo 1663031 4211129 := bstep (se 2 (by rfl) ⟨1579173, by rfl⟩ : syracuseStep 4211129 = 3158347) B3158347
theorem B1663419 : Blo 1663031 1663419 := bstep (se 1 (by rfl) ⟨1247564, by rfl⟩ : syracuseStep 1663419 = 2495129) B2495129
theorem B1663495 : Blo 1663031 1663495 := bstep (se 1 (by rfl) ⟨1247621, by rfl⟩ : syracuseStep 1663495 = 2495243) B2495243
theorem B4268555 : Blo 1663031 4268555 := bstep (se 1 (by rfl) ⟨3201416, by rfl⟩ : syracuseStep 4268555 = 6402833) B6402833
theorem B1663503 : Blo 1663031 1663503 := bstep (se 1 (by rfl) ⟨1247627, by rfl⟩ : syracuseStep 1663503 = 2495255) B2495255
theorem B76890667 : Blo 1663031 76890667 := bstep (se 1 (by rfl) ⟨57668000, by rfl⟩ : syracuseStep 76890667 = 115336001) B115336001
theorem B1663547 : Blo 1663031 1663547 := bstep (se 1 (by rfl) ⟨1247660, by rfl⟩ : syracuseStep 1663547 = 2495321) B2495321
theorem B6316663 : Blo 1663031 6316663 := bstep (se 1 (by rfl) ⟨4737497, by rfl⟩ : syracuseStep 6316663 = 9474995) B9474995
theorem B1663623 : Blo 1663031 1663623 := bstep (se 1 (by rfl) ⟨1247717, by rfl⟩ : syracuseStep 1663623 = 2495435) B2495435
theorem B1663631 : Blo 1663031 1663631 := bstep (se 1 (by rfl) ⟨1247723, by rfl⟩ : syracuseStep 1663631 = 2495447) B2495447
theorem B1663675 : Blo 1663031 1663675 := bstep (se 1 (by rfl) ⟨1247756, by rfl⟩ : syracuseStep 1663675 = 2495513) B2495513
theorem B1663751 : Blo 1663031 1663751 := bstep (se 1 (by rfl) ⟨1247813, by rfl⟩ : syracuseStep 1663751 = 2495627) B2495627
theorem B1663759 : Blo 1663031 1663759 := bstep (se 1 (by rfl) ⟨1247819, by rfl⟩ : syracuseStep 1663759 = 2495639) B2495639
theorem B1663803 : Blo 1663031 1663803 := bstep (se 1 (by rfl) ⟨1247852, by rfl⟩ : syracuseStep 1663803 = 2495705) B2495705
theorem B1663879 : Blo 1663031 1663879 := bstep (se 1 (by rfl) ⟨1247909, by rfl⟩ : syracuseStep 1663879 = 2495819) B2495819
theorem B3744647 : Blo 1663031 3744647 := bstep (se 1 (by rfl) ⟨2808485, by rfl⟩ : syracuseStep 3744647 = 5616971) B5616971
theorem B1663887 : Blo 1663031 1663887 := bstep (se 1 (by rfl) ⟨1247915, by rfl⟩ : syracuseStep 1663887 = 2495831) B2495831
theorem B20243351 : Blo 1663031 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B7111577 : Blo 1663031 7111577 := bstep (se 2 (by rfl) ⟨2666841, by rfl⟩ : syracuseStep 7111577 = 5333683) B5333683
theorem B1663931 : Blo 1663031 1663931 := bstep (se 1 (by rfl) ⟨1247948, by rfl⟩ : syracuseStep 1663931 = 2495897) B2495897
theorem B1664007 : Blo 1663031 1664007 := bstep (se 1 (by rfl) ⟨1248005, by rfl⟩ : syracuseStep 1664007 = 2496011) B2496011
theorem B1664015 : Blo 1663031 1664015 := bstep (se 1 (by rfl) ⟨1248011, by rfl⟩ : syracuseStep 1664015 = 2496023) B2496023
theorem B4736029 : Blo 1663031 4736029 := bstep (se 3 (by rfl) ⟨888005, by rfl⟩ : syracuseStep 4736029 = 1776011) B1776011
theorem B1664059 : Blo 1663031 1664059 := bstep (se 1 (by rfl) ⟨1248044, by rfl⟩ : syracuseStep 1664059 = 2496089) B2496089
theorem B3744827 : Blo 1663031 3744827 := bstep (se 1 (by rfl) ⟨2808620, by rfl⟩ : syracuseStep 3744827 = 5617241) B5617241
theorem B64873547 : Blo 1663031 64873547 := bstep (se 1 (by rfl) ⟨48655160, by rfl⟩ : syracuseStep 64873547 = 97310321) B97310321
theorem B22774871 : Blo 1663031 22774871 := bstep (se 1 (by rfl) ⟨17081153, by rfl⟩ : syracuseStep 22774871 = 34162307) B34162307
theorem B1664135 : Blo 1663031 1664135 := bstep (se 1 (by rfl) ⟨1248101, by rfl⟩ : syracuseStep 1664135 = 2496203) B2496203
theorem B1664143 : Blo 1663031 1664143 := bstep (se 1 (by rfl) ⟨1248107, by rfl⟩ : syracuseStep 1664143 = 2496215) B2496215
theorem B3744953 : Blo 1663031 3744953 := bstep (se 2 (by rfl) ⟨1404357, by rfl⟩ : syracuseStep 3744953 = 2808715) B2808715
theorem B1664187 : Blo 1663031 1664187 := bstep (se 1 (by rfl) ⟨1248140, by rfl⟩ : syracuseStep 1664187 = 2496281) B2496281
theorem B9479369 : Blo 1663031 9479369 := bstep (se 2 (by rfl) ⟨3554763, by rfl⟩ : syracuseStep 9479369 = 7109527) B7109527
theorem B1664263 : Blo 1663031 1664263 := bstep (se 1 (by rfl) ⟨1248197, by rfl⟩ : syracuseStep 1664263 = 2496395) B2496395
theorem B1664271 : Blo 1663031 1664271 := bstep (se 1 (by rfl) ⟨1248203, by rfl⟩ : syracuseStep 1664271 = 2496407) B2496407
theorem B1664315 : Blo 1663031 1664315 := bstep (se 1 (by rfl) ⟨1248236, by rfl⟩ : syracuseStep 1664315 = 2496473) B2496473
theorem B10118515 : Blo 1663031 10118515 := bstep (se 1 (by rfl) ⟨7588886, by rfl⟩ : syracuseStep 10118515 = 15177773) B15177773
theorem B1664391 : Blo 1663031 1664391 := bstep (se 1 (by rfl) ⟨1248293, by rfl⟩ : syracuseStep 1664391 = 2496587) B2496587
theorem B1664399 : Blo 1663031 1664399 := bstep (se 1 (by rfl) ⟨1248299, by rfl⟩ : syracuseStep 1664399 = 2496599) B2496599
theorem B4212121 : Blo 1663031 4212121 := bstep (se 2 (by rfl) ⟨1579545, by rfl⟩ : syracuseStep 4212121 = 3159091) B3159091
theorem B1664443 : Blo 1663031 1664443 := bstep (se 1 (by rfl) ⟨1248332, by rfl⟩ : syracuseStep 1664443 = 2496665) B2496665
theorem B8422865 : Blo 1663031 8422865 := bstep (se 2 (by rfl) ⟨3158574, by rfl⟩ : syracuseStep 8422865 = 6317149) B6317149
theorem B1664519 : Blo 1663031 1664519 := bstep (se 1 (by rfl) ⟨1248389, by rfl⟩ : syracuseStep 1664519 = 2496779) B2496779
theorem B1664527 : Blo 1663031 1664527 := bstep (se 1 (by rfl) ⟨1248395, by rfl⟩ : syracuseStep 1664527 = 2496791) B2496791
theorem B3745295 : Blo 1663031 3745295 := bstep (se 1 (by rfl) ⟨2808971, by rfl⟩ : syracuseStep 3745295 = 5617943) B5617943
theorem B3745313 : Blo 1663031 3745313 := bstep (se 2 (by rfl) ⟨1404492, by rfl⟩ : syracuseStep 3745313 = 2808985) B2808985
theorem B4212283 : Blo 1663031 4212283 := bstep (se 1 (by rfl) ⟨3159212, by rfl⟩ : syracuseStep 4212283 = 6318425) B6318425
theorem B1664571 : Blo 1663031 1664571 := bstep (se 1 (by rfl) ⟨1248428, by rfl⟩ : syracuseStep 1664571 = 2496857) B2496857
theorem B6317635 : Blo 1663031 6317635 := bstep (se 1 (by rfl) ⟨4738226, by rfl⟩ : syracuseStep 6317635 = 9476453) B9476453
theorem B35964485 : Blo 1663031 35964485 := bstep (se 4 (by rfl) ⟨3371670, by rfl⟩ : syracuseStep 35964485 = 6743341) B6743341
theorem B1664647 : Blo 1663031 1664647 := bstep (se 1 (by rfl) ⟨1248485, by rfl⟩ : syracuseStep 1664647 = 2496971) B2496971
theorem B1664655 : Blo 1663031 1664655 := bstep (se 1 (by rfl) ⟨1248491, by rfl⟩ : syracuseStep 1664655 = 2496983) B2496983
theorem B1664699 : Blo 1663031 1664699 := bstep (se 1 (by rfl) ⟨1248524, by rfl⟩ : syracuseStep 1664699 = 2497049) B2497049
theorem B4212425 : Blo 1663031 4212425 := bstep (se 2 (by rfl) ⟨1579659, by rfl⟩ : syracuseStep 4212425 = 3159319) B3159319
theorem B1664775 : Blo 1663031 1664775 := bstep (se 1 (by rfl) ⟨1248581, by rfl⟩ : syracuseStep 1664775 = 2497163) B2497163
theorem B1664783 : Blo 1663031 1664783 := bstep (se 1 (by rfl) ⟨1248587, by rfl⟩ : syracuseStep 1664783 = 2497175) B2497175
theorem B1664827 : Blo 1663031 1664827 := bstep (se 1 (by rfl) ⟨1248620, by rfl⟩ : syracuseStep 1664827 = 2497241) B2497241
theorem B2369353 : Blo 1663031 2369353 := bstep (se 2 (by rfl) ⟨888507, by rfl⟩ : syracuseStep 2369353 = 1777015) B1777015
theorem B6317939 : Blo 1663031 6317939 := bstep (se 1 (by rfl) ⟨4738454, by rfl⟩ : syracuseStep 6317939 = 9476909) B9476909
theorem B3745655 : Blo 1663031 3745655 := bstep (se 1 (by rfl) ⟨2809241, by rfl⟩ : syracuseStep 3745655 = 5618483) B5618483
theorem B1664903 : Blo 1663031 1664903 := bstep (se 1 (by rfl) ⟨1248677, by rfl⟩ : syracuseStep 1664903 = 2497355) B2497355
theorem B1664911 : Blo 1663031 1664911 := bstep (se 1 (by rfl) ⟨1248683, by rfl⟩ : syracuseStep 1664911 = 2497367) B2497367
theorem B8652691 : Blo 1663031 8652691 := bstep (se 1 (by rfl) ⟨6489518, by rfl⟩ : syracuseStep 8652691 = 12979037) B12979037
theorem B1664955 : Blo 1663031 1664955 := bstep (se 1 (by rfl) ⟨1248716, by rfl⟩ : syracuseStep 1664955 = 2497433) B2497433
theorem B19744715 : Blo 1663031 19744715 := bstep (se 1 (by rfl) ⟨14808536, by rfl⟩ : syracuseStep 19744715 = 29617073) B29617073
theorem B1665031 : Blo 1663031 1665031 := bstep (se 1 (by rfl) ⟨1248773, by rfl⟩ : syracuseStep 1665031 = 2497547) B2497547
theorem B4212769 : Blo 1663031 4212769 := bstep (se 2 (by rfl) ⟨1579788, by rfl⟩ : syracuseStep 4212769 = 3159577) B3159577
theorem B8538155 : Blo 1663031 8538155 := bstep (se 1 (by rfl) ⟨6403616, by rfl⟩ : syracuseStep 8538155 = 12807233) B12807233
theorem B3745835 : Blo 1663031 3745835 := bstep (se 1 (by rfl) ⟨2809376, by rfl⟩ : syracuseStep 3745835 = 5618753) B5618753
theorem B5613839 : Blo 1663031 5613839 := bstep (se 1 (by rfl) ⟨4210379, by rfl⟩ : syracuseStep 5613839 = 8420759) B8420759
theorem B6318395 : Blo 1663031 6318395 := bstep (se 1 (by rfl) ⟨4738796, by rfl⟩ : syracuseStep 6318395 = 9477593) B9477593
theorem B2369911 : Blo 1663031 2369911 := bstep (se 1 (by rfl) ⟨1777433, by rfl⟩ : syracuseStep 2369911 = 3554867) B3554867
theorem B3746195 : Blo 1663031 3746195 := bstep (se 1 (by rfl) ⟨2809646, by rfl⟩ : syracuseStep 3746195 = 5619293) B5619293
theorem B3746249 : Blo 1663031 3746249 := bstep (se 2 (by rfl) ⟨1404843, by rfl⟩ : syracuseStep 3746249 = 2809687) B2809687
theorem B4557313 : Blo 1663031 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B9472535 : Blo 1663031 9472535 := bstep (se 1 (by rfl) ⟨7104401, by rfl⟩ : syracuseStep 9472535 = 14208803) B14208803
theorem B5614109 : Blo 1663031 5614109 := bstep (se 3 (by rfl) ⟨1052645, by rfl⟩ : syracuseStep 5614109 = 2105291) B2105291
theorem B26978935 : Blo 1663031 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B4213367 : Blo 1663031 4213367 := bstep (se 1 (by rfl) ⟨3160025, by rfl⟩ : syracuseStep 4213367 = 6320051) B6320051
theorem B2665145 : Blo 1663031 2665145 := bstep (se 2 (by rfl) ⟨999429, by rfl⟩ : syracuseStep 2665145 = 1998859) B1998859
theorem B6318881 : Blo 1663031 6318881 := bstep (se 2 (by rfl) ⟨2369580, by rfl⟩ : syracuseStep 6318881 = 4739161) B4739161
theorem B7105427 : Blo 1663031 7105427 := bstep (se 1 (by rfl) ⟨5329070, by rfl⟩ : syracuseStep 7105427 = 10658141) B10658141
theorem B2370475 : Blo 1663031 2370475 := bstep (se 1 (by rfl) ⟨1777856, by rfl⟩ : syracuseStep 2370475 = 3555713) B3555713
theorem B4737977 : Blo 1663031 4737977 := bstep (se 2 (by rfl) ⟨1776741, by rfl⟩ : syracuseStep 4737977 = 3553483) B3553483
theorem B5475371 : Blo 1663031 5475371 := bstep (se 1 (by rfl) ⟨4106528, by rfl⟩ : syracuseStep 5475371 = 8213057) B8213057
theorem B9481283 : Blo 1663031 9481283 := bstep (se 1 (by rfl) ⟨7110962, by rfl⟩ : syracuseStep 9481283 = 14221925) B14221925
theorem B11988101 : Blo 1663031 11988101 := bstep (se 4 (by rfl) ⟨1123884, by rfl⟩ : syracuseStep 11988101 = 2247769) B2247769
theorem B2370703 : Blo 1663031 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B2665657 : Blo 1663031 2665657 := bstep (se 2 (by rfl) ⟨999621, by rfl⟩ : syracuseStep 2665657 = 1999243) B1999243
theorem B3157193 : Blo 1663031 3157193 := bstep (se 2 (by rfl) ⟨1183947, by rfl⟩ : syracuseStep 3157193 = 2367895) B2367895
theorem B1871239 : Blo 1663031 1871239 := bstep (se 1 (by rfl) ⟨1403429, by rfl⟩ : syracuseStep 1871239 = 2806859) B2806859
theorem B14216593 : Blo 1663031 14216593 := bstep (se 2 (by rfl) ⟨5331222, by rfl⟩ : syracuseStep 14216593 = 10662445) B10662445
theorem B13495697 : Blo 1663031 13495697 := bstep (se 2 (by rfl) ⟨5060886, by rfl⟩ : syracuseStep 13495697 = 10121773) B10121773
theorem B8424971 : Blo 1663031 8424971 := bstep (se 1 (by rfl) ⟨6318728, by rfl⟩ : syracuseStep 8424971 = 12637457) B12637457
theorem B1871419 : Blo 1663031 1871419 := bstep (se 1 (by rfl) ⟨1403564, by rfl⟩ : syracuseStep 1871419 = 2807129) B2807129
theorem B25611875 : Blo 1663031 25611875 := bstep (se 1 (by rfl) ⟨19208906, by rfl⟩ : syracuseStep 25611875 = 38417813) B38417813
theorem B8425133 : Blo 1663031 8425133 := bstep (se 3 (by rfl) ⟨1579712, by rfl⟩ : syracuseStep 8425133 = 3159425) B3159425
theorem B13872869 : Blo 1663031 13872869 := bstep (se 4 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 13872869 = 2601163) B2601163
theorem B6319853 : Blo 1663031 6319853 := bstep (se 3 (by rfl) ⟨1184972, by rfl⟩ : syracuseStep 6319853 = 2369945) B2369945
theorem B18943793 : Blo 1663031 18943793 := bstep (se 2 (by rfl) ⟨7103922, by rfl⟩ : syracuseStep 18943793 = 14207845) B14207845
theorem B2666375 : Blo 1663031 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B5615513 : Blo 1663031 5615513 := bstep (se 2 (by rfl) ⟨2105817, by rfl⟩ : syracuseStep 5615513 = 4211635) B4211635
theorem B1871887 : Blo 1663031 1871887 := bstep (se 1 (by rfl) ⟨1403915, by rfl⟩ : syracuseStep 1871887 = 2807831) B2807831
theorem B16216087 : Blo 1663031 16216087 := bstep (se 1 (by rfl) ⟨12162065, by rfl⟩ : syracuseStep 16216087 = 24324131) B24324131
theorem B2494583 : Blo 1663031 2494583 := bstep (se 1 (by rfl) ⟨1870937, by rfl⟩ : syracuseStep 2494583 = 3741875) B3741875
theorem B2494607 : Blo 1663031 2494607 := bstep (se 1 (by rfl) ⟨1870955, by rfl⟩ : syracuseStep 2494607 = 3741911) B3741911
theorem B4739219 : Blo 1663031 4739219 := bstep (se 1 (by rfl) ⟨3554414, by rfl⟩ : syracuseStep 4739219 = 7108829) B7108829
theorem B2494649 : Blo 1663031 2494649 := bstep (se 2 (by rfl) ⟨935493, by rfl⟩ : syracuseStep 2494649 = 1870987) B1870987
theorem B7999681 : Blo 1663031 7999681 := bstep (se 2 (by rfl) ⟨2999880, by rfl⟩ : syracuseStep 7999681 = 5999761) B5999761
theorem B5329097 : Blo 1663031 5329097 := bstep (se 2 (by rfl) ⟨1998411, by rfl⟩ : syracuseStep 5329097 = 3996823) B3996823
theorem B35983601 : Blo 1663031 35983601 := bstep (se 2 (by rfl) ⟨13493850, by rfl⟩ : syracuseStep 35983601 = 26987701) B26987701
theorem B2494727 : Blo 1663031 2494727 := bstep (se 1 (by rfl) ⟨1871045, by rfl⟩ : syracuseStep 2494727 = 3742091) B3742091
theorem B2494763 : Blo 1663031 2494763 := bstep (se 1 (by rfl) ⟨1871072, by rfl⟩ : syracuseStep 2494763 = 3742145) B3742145
theorem B2494793 : Blo 1663031 2494793 := bstep (se 2 (by rfl) ⟨935547, by rfl⟩ : syracuseStep 2494793 = 1871095) B1871095
theorem B18952541 : Blo 1663031 18952541 := bstep (se 3 (by rfl) ⟨3553601, by rfl⟩ : syracuseStep 18952541 = 7107203) B7107203
theorem B6320537 : Blo 1663031 6320537 := bstep (se 2 (by rfl) ⟨2370201, by rfl⟩ : syracuseStep 6320537 = 4740403) B4740403
theorem B2494907 : Blo 1663031 2494907 := bstep (se 1 (by rfl) ⟨1871180, by rfl⟩ : syracuseStep 2494907 = 3742361) B3742361
theorem B2494967 : Blo 1663031 2494967 := bstep (se 1 (by rfl) ⟨1871225, by rfl⟩ : syracuseStep 2494967 = 3742451) B3742451
theorem B1872391 : Blo 1663031 1872391 := bstep (se 1 (by rfl) ⟨1404293, by rfl⟩ : syracuseStep 1872391 = 2808587) B2808587
theorem B2494991 : Blo 1663031 2494991 := bstep (se 1 (by rfl) ⟨1871243, by rfl⟩ : syracuseStep 2494991 = 3742487) B3742487
theorem B2495033 : Blo 1663031 2495033 := bstep (se 2 (by rfl) ⟨935637, by rfl⟩ : syracuseStep 2495033 = 1871275) B1871275
theorem B5329469 : Blo 1663031 5329469 := bstep (se 3 (by rfl) ⟨999275, by rfl⟩ : syracuseStep 5329469 = 1998551) B1998551
theorem B5616215 : Blo 1663031 5616215 := bstep (se 1 (by rfl) ⟨4212161, by rfl⟩ : syracuseStep 5616215 = 8424323) B8424323
theorem B2495111 : Blo 1663031 2495111 := bstep (se 1 (by rfl) ⟨1871333, by rfl⟩ : syracuseStep 2495111 = 3742667) B3742667
theorem B2495147 : Blo 1663031 2495147 := bstep (se 1 (by rfl) ⟨1871360, by rfl⟩ : syracuseStep 2495147 = 3742721) B3742721
theorem B1872571 : Blo 1663031 1872571 := bstep (se 1 (by rfl) ⟨1404428, by rfl⟩ : syracuseStep 1872571 = 2808857) B2808857
theorem B8991425 : Blo 1663031 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B2495177 : Blo 1663031 2495177 := bstep (se 2 (by rfl) ⟨935691, by rfl⟩ : syracuseStep 2495177 = 1871383) B1871383
theorem B12628709 : Blo 1663031 12628709 := bstep (se 4 (by rfl) ⟨1183941, by rfl⟩ : syracuseStep 12628709 = 2367883) B2367883
theorem B1897231 : Blo 1663031 1897231 := bstep (se 1 (by rfl) ⟨1422923, by rfl⟩ : syracuseStep 1897231 = 2845847) B2845847
theorem B14209829 : Blo 1663031 14209829 := bstep (se 4 (by rfl) ⟨1332171, by rfl⟩ : syracuseStep 14209829 = 2664343) B2664343
theorem B2495291 : Blo 1663031 2495291 := bstep (se 1 (by rfl) ⟨1871468, by rfl⟩ : syracuseStep 2495291 = 3742937) B3742937
theorem B8991577 : Blo 1663031 8991577 := bstep (se 2 (by rfl) ⟨3371841, by rfl⟩ : syracuseStep 8991577 = 6743683) B6743683
theorem B26997619 : Blo 1663031 26997619 := bstep (se 1 (by rfl) ⟨20248214, by rfl⟩ : syracuseStep 26997619 = 40496429) B40496429
theorem B2495351 : Blo 1663031 2495351 := bstep (se 1 (by rfl) ⟨1871513, by rfl⟩ : syracuseStep 2495351 = 3743027) B3743027
theorem B2806663 : Blo 1663031 2806663 := bstep (se 1 (by rfl) ⟨2104997, by rfl⟩ : syracuseStep 2806663 = 4209995) B4209995
theorem B2495375 : Blo 1663031 2495375 := bstep (se 1 (by rfl) ⟨1871531, by rfl⟩ : syracuseStep 2495375 = 3743063) B3743063
theorem B2495417 : Blo 1663031 2495417 := bstep (se 2 (by rfl) ⟨935781, by rfl⟩ : syracuseStep 2495417 = 1871563) B1871563
theorem B2495495 : Blo 1663031 2495495 := bstep (se 1 (by rfl) ⟨1871621, by rfl⟩ : syracuseStep 2495495 = 3743243) B3743243
theorem B2495531 : Blo 1663031 2495531 := bstep (se 1 (by rfl) ⟨1871648, by rfl⟩ : syracuseStep 2495531 = 3743297) B3743297
theorem B2135099 : Blo 1663031 2135099 := bstep (se 1 (by rfl) ⟨1601324, by rfl⟩ : syracuseStep 2135099 = 3202649) B3202649
theorem B5616701 : Blo 1663031 5616701 := bstep (se 3 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 5616701 = 2106263) B2106263
theorem B2495561 : Blo 1663031 2495561 := bstep (se 2 (by rfl) ⟨935835, by rfl⟩ : syracuseStep 2495561 = 1871671) B1871671
theorem B3372167 : Blo 1663031 3372167 := bstep (se 1 (by rfl) ⟨2529125, by rfl⟩ : syracuseStep 3372167 = 5058251) B5058251
theorem B3159175 : Blo 1663031 3159175 := bstep (se 1 (by rfl) ⟨2369381, by rfl⟩ : syracuseStep 3159175 = 4738763) B4738763
theorem B1873039 : Blo 1663031 1873039 := bstep (se 1 (by rfl) ⟨1404779, by rfl⟩ : syracuseStep 1873039 = 2809559) B2809559
theorem B2495675 : Blo 1663031 2495675 := bstep (se 1 (by rfl) ⟨1871756, by rfl⟩ : syracuseStep 2495675 = 3743513) B3743513
theorem B2495735 : Blo 1663031 2495735 := bstep (se 1 (by rfl) ⟨1871801, by rfl⟩ : syracuseStep 2495735 = 3743603) B3743603
theorem B8426753 : Blo 1663031 8426753 := bstep (se 2 (by rfl) ⟨3160032, by rfl⟩ : syracuseStep 8426753 = 6320065) B6320065
theorem B2495759 : Blo 1663031 2495759 := bstep (se 1 (by rfl) ⟨1871819, by rfl⟩ : syracuseStep 2495759 = 3743639) B3743639
theorem B2495801 : Blo 1663031 2495801 := bstep (se 2 (by rfl) ⟨935925, by rfl⟩ : syracuseStep 2495801 = 1871851) B1871851
theorem B7992665 : Blo 1663031 7992665 := bstep (se 2 (by rfl) ⟨2997249, by rfl⟩ : syracuseStep 7992665 = 5994499) B5994499
theorem B6321523 : Blo 1663031 6321523 := bstep (se 1 (by rfl) ⟨4741142, by rfl⟩ : syracuseStep 6321523 = 9482285) B9482285
theorem B2495879 : Blo 1663031 2495879 := bstep (se 1 (by rfl) ⟨1871909, by rfl⟩ : syracuseStep 2495879 = 3743819) B3743819
theorem B2250127 : Blo 1663031 2250127 := bstep (se 1 (by rfl) ⟨1687595, by rfl⟩ : syracuseStep 2250127 = 3375191) B3375191
theorem B2495915 : Blo 1663031 2495915 := bstep (se 1 (by rfl) ⟨1871936, by rfl⟩ : syracuseStep 2495915 = 3743873) B3743873
theorem B2495945 : Blo 1663031 2495945 := bstep (se 2 (by rfl) ⟨935979, by rfl⟩ : syracuseStep 2495945 = 1871959) B1871959
theorem B4740619 : Blo 1663031 4740619 := bstep (se 1 (by rfl) ⟨3555464, by rfl⟩ : syracuseStep 4740619 = 7110929) B7110929
theorem B2807311 : Blo 1663031 2807311 := bstep (se 1 (by rfl) ⟨2105483, by rfl⟩ : syracuseStep 2807311 = 4210967) B4210967
theorem B2496059 : Blo 1663031 2496059 := bstep (se 1 (by rfl) ⟨1872044, by rfl⟩ : syracuseStep 2496059 = 3744089) B3744089
theorem B45553229 : Blo 1663031 45553229 := bstep (se 3 (by rfl) ⟨8541230, by rfl⟩ : syracuseStep 45553229 = 17082461) B17082461
theorem B9475703 : Blo 1663031 9475703 := bstep (se 1 (by rfl) ⟨7106777, by rfl⟩ : syracuseStep 9475703 = 14213555) B14213555
theorem B2496119 : Blo 1663031 2496119 := bstep (se 1 (by rfl) ⟨1872089, by rfl⟩ : syracuseStep 2496119 = 3744179) B3744179
theorem B2496143 : Blo 1663031 2496143 := bstep (se 1 (by rfl) ⟨1872107, by rfl⟩ : syracuseStep 2496143 = 3744215) B3744215
theorem B2496185 : Blo 1663031 2496185 := bstep (se 2 (by rfl) ⟨936069, by rfl⟩ : syracuseStep 2496185 = 1872139) B1872139
theorem B2496263 : Blo 1663031 2496263 := bstep (se 1 (by rfl) ⟨1872197, by rfl⟩ : syracuseStep 2496263 = 3744395) B3744395
theorem B18953999 : Blo 1663031 18953999 := bstep (se 1 (by rfl) ⟨14215499, by rfl⟩ : syracuseStep 18953999 = 28430999) B28430999
theorem B4740893 : Blo 1663031 4740893 := bstep (se 3 (by rfl) ⟨888917, by rfl⟩ : syracuseStep 4740893 = 1777835) B1777835
theorem B2496299 : Blo 1663031 2496299 := bstep (se 1 (by rfl) ⟨1872224, by rfl⟩ : syracuseStep 2496299 = 3744449) B3744449
theorem B2496329 : Blo 1663031 2496329 := bstep (se 2 (by rfl) ⟨936123, by rfl⟩ : syracuseStep 2496329 = 1872247) B1872247
theorem B2496443 : Blo 1663031 2496443 := bstep (se 1 (by rfl) ⟨1872332, by rfl⟩ : syracuseStep 2496443 = 3744665) B3744665
theorem B11990987 : Blo 1663031 11990987 := bstep (se 1 (by rfl) ⟨8993240, by rfl⟩ : syracuseStep 11990987 = 17986481) B17986481
theorem B2496503 : Blo 1663031 2496503 := bstep (se 1 (by rfl) ⟨1872377, by rfl⟩ : syracuseStep 2496503 = 3744755) B3744755
theorem B15988747 : Blo 1663031 15988747 := bstep (se 1 (by rfl) ⟨11991560, by rfl⟩ : syracuseStep 15988747 = 23983121) B23983121
theorem B2496527 : Blo 1663031 2496527 := bstep (se 1 (by rfl) ⟨1872395, by rfl⟩ : syracuseStep 2496527 = 3744791) B3744791
theorem B2807851 : Blo 1663031 2807851 := bstep (se 1 (by rfl) ⟨2105888, by rfl⟩ : syracuseStep 2807851 = 4211777) B4211777
theorem B8427563 : Blo 1663031 8427563 := bstep (se 1 (by rfl) ⟨6320672, by rfl⟩ : syracuseStep 8427563 = 12641345) B12641345
theorem B2496569 : Blo 1663031 2496569 := bstep (se 2 (by rfl) ⟨936213, by rfl⟩ : syracuseStep 2496569 = 1872427) B1872427
theorem B2496647 : Blo 1663031 2496647 := bstep (se 1 (by rfl) ⟨1872485, by rfl⟩ : syracuseStep 2496647 = 3744971) B3744971
theorem B2496683 : Blo 1663031 2496683 := bstep (se 1 (by rfl) ⟨1872512, by rfl⟩ : syracuseStep 2496683 = 3745025) B3745025
theorem B3553465 : Blo 1663031 3553465 := bstep (se 2 (by rfl) ⟨1332549, by rfl⟩ : syracuseStep 3553465 = 2665099) B2665099
theorem B2807993 : Blo 1663031 2807993 := bstep (se 2 (by rfl) ⟨1052997, by rfl⟩ : syracuseStep 2807993 = 2105995) B2105995
theorem B2496713 : Blo 1663031 2496713 := bstep (se 2 (by rfl) ⟨936267, by rfl⟩ : syracuseStep 2496713 = 1872535) B1872535
theorem B2496827 : Blo 1663031 2496827 := bstep (se 1 (by rfl) ⟨1872620, by rfl⟩ : syracuseStep 2496827 = 3745241) B3745241
theorem B18962747 : Blo 1663031 18962747 := bstep (se 1 (by rfl) ⟨14222060, by rfl⟩ : syracuseStep 18962747 = 28444121) B28444121
theorem B2496887 : Blo 1663031 2496887 := bstep (se 1 (by rfl) ⟨1872665, by rfl⟩ : syracuseStep 2496887 = 3745331) B3745331
theorem B2496911 : Blo 1663031 2496911 := bstep (se 1 (by rfl) ⟨1872683, by rfl⟩ : syracuseStep 2496911 = 3745367) B3745367
theorem B5618105 : Blo 1663031 5618105 := bstep (se 2 (by rfl) ⟨2106789, by rfl⟩ : syracuseStep 5618105 = 4213579) B4213579
theorem B2496953 : Blo 1663031 2496953 := bstep (se 2 (by rfl) ⟨936357, by rfl⟩ : syracuseStep 2496953 = 1872715) B1872715
theorem B8419787 : Blo 1663031 8419787 := bstep (se 1 (by rfl) ⟨6314840, by rfl⟩ : syracuseStep 8419787 = 12629681) B12629681
theorem B2497031 : Blo 1663031 2497031 := bstep (se 1 (by rfl) ⟨1872773, by rfl⟩ : syracuseStep 2497031 = 3745547) B3745547
theorem B6314507 : Blo 1663031 6314507 := bstep (se 1 (by rfl) ⟨4735880, by rfl⟩ : syracuseStep 6314507 = 9471761) B9471761
theorem B3553807 : Blo 1663031 3553807 := bstep (se 1 (by rfl) ⟨2665355, by rfl⟩ : syracuseStep 3553807 = 5330711) B5330711
theorem B2497067 : Blo 1663031 2497067 := bstep (se 1 (by rfl) ⟨1872800, by rfl⟩ : syracuseStep 2497067 = 3745601) B3745601
theorem B2497097 : Blo 1663031 2497097 := bstep (se 2 (by rfl) ⟨936411, by rfl⟩ : syracuseStep 2497097 = 1872823) B1872823
theorem B11385463 : Blo 1663031 11385463 := bstep (se 1 (by rfl) ⟨8539097, by rfl⟩ : syracuseStep 11385463 = 17078195) B17078195
theorem B3742343 : Blo 1663031 3742343 := bstep (se 1 (by rfl) ⟨2806757, by rfl⟩ : syracuseStep 3742343 = 5613515) B5613515
theorem B2497211 : Blo 1663031 2497211 := bstep (se 1 (by rfl) ⟨1872908, by rfl⟩ : syracuseStep 2497211 = 3745817) B3745817
theorem B3160777 : Blo 1663031 3160777 := bstep (se 2 (by rfl) ⟨1185291, by rfl⟩ : syracuseStep 3160777 = 2370583) B2370583
theorem B2497271 : Blo 1663031 2497271 := bstep (se 1 (by rfl) ⟨1872953, by rfl⟩ : syracuseStep 2497271 = 3745907) B3745907
theorem B8420111 : Blo 1663031 8420111 := bstep (se 1 (by rfl) ⟨6315083, by rfl⟩ : syracuseStep 8420111 = 12630167) B12630167
theorem B2497295 : Blo 1663031 2497295 := bstep (se 1 (by rfl) ⟨1872971, by rfl⟩ : syracuseStep 2497295 = 3745943) B3745943
theorem B2497337 : Blo 1663031 2497337 := bstep (se 2 (by rfl) ⟨936501, by rfl⟩ : syracuseStep 2497337 = 1873003) B1873003
theorem B3742523 : Blo 1663031 3742523 := bstep (se 1 (by rfl) ⟨2806892, by rfl⟩ : syracuseStep 3742523 = 5613785) B5613785
theorem B2808695 : Blo 1663031 2808695 := bstep (se 1 (by rfl) ⟨2106521, by rfl⟩ : syracuseStep 2808695 = 4213043) B4213043
theorem B2497415 : Blo 1663031 2497415 := bstep (se 1 (by rfl) ⟨1873061, by rfl⟩ : syracuseStep 2497415 = 3746123) B3746123
theorem B5331865 : Blo 1663031 5331865 := bstep (se 2 (by rfl) ⟨1999449, by rfl⟩ : syracuseStep 5331865 = 3998899) B3998899
theorem B38411171 : Blo 1663031 38411171 := bstep (se 1 (by rfl) ⟨28808378, by rfl⟩ : syracuseStep 38411171 = 57616757) B57616757
theorem B2497451 : Blo 1663031 2497451 := bstep (se 1 (by rfl) ⟨1873088, by rfl⟩ : syracuseStep 2497451 = 3746177) B3746177
theorem B3742649 : Blo 1663031 3742649 := bstep (se 2 (by rfl) ⟨1403493, by rfl⟩ : syracuseStep 3742649 = 2806987) B2806987
theorem B3201977 : Blo 1663031 3201977 := bstep (se 2 (by rfl) ⟨1200741, by rfl⟩ : syracuseStep 3201977 = 2401483) B2401483
theorem B2497481 : Blo 1663031 2497481 := bstep (se 2 (by rfl) ⟨936555, by rfl⟩ : syracuseStep 2497481 = 1873111) B1873111
theorem B5618699 : Blo 1663031 5618699 := bstep (se 1 (by rfl) ⟨4214024, by rfl⟩ : syracuseStep 5618699 = 8428049) B8428049
theorem B5061665 : Blo 1663031 5061665 := bstep (se 2 (by rfl) ⟨1898124, by rfl⟩ : syracuseStep 5061665 = 3796249) B3796249
theorem B17988725 : Blo 1663031 17988725 := bstep (se 5 (by rfl) ⟨843221, by rfl⟩ : syracuseStep 17988725 = 1686443) B1686443
theorem B4267127 : Blo 1663031 4267127 := bstep (se 1 (by rfl) ⟨3200345, by rfl⟩ : syracuseStep 4267127 = 6400691) B6400691
theorem B5618807 : Blo 1663031 5618807 := bstep (se 1 (by rfl) ⟨4214105, by rfl⟩ : syracuseStep 5618807 = 8428211) B8428211
theorem B7109869 : Blo 1663031 7109869 := bstep (se 3 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 7109869 = 2666201) B2666201
theorem B3742991 : Blo 1663031 3742991 := bstep (se 1 (by rfl) ⟨2807243, by rfl⟩ : syracuseStep 3742991 = 5614487) B5614487
theorem B3743009 : Blo 1663031 3743009 := bstep (se 2 (by rfl) ⟨1403628, by rfl⟩ : syracuseStep 3743009 = 2807257) B2807257
theorem B2809147 : Blo 1663031 2809147 := bstep (se 1 (by rfl) ⟨2106860, by rfl⟩ : syracuseStep 2809147 = 4213721) B4213721
theorem B8428859 : Blo 1663031 8428859 := bstep (se 1 (by rfl) ⟨6321644, by rfl⟩ : syracuseStep 8428859 = 12643289) B12643289
theorem B3554695 : Blo 1663031 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B10657169 : Blo 1663031 10657169 := bstep (se 2 (by rfl) ⟨3996438, by rfl⟩ : syracuseStep 10657169 = 7992877) B7992877
theorem B2809289 : Blo 1663031 2809289 := bstep (se 2 (by rfl) ⟨1053483, by rfl⟩ : syracuseStep 2809289 = 2106967) B2106967
theorem B8429021 : Blo 1663031 8429021 := bstep (se 3 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 8429021 = 3160883) B3160883
theorem B4210177 : Blo 1663031 4210177 := bstep (se 2 (by rfl) ⟨1578816, by rfl⟩ : syracuseStep 4210177 = 3157633) B3157633
theorem B40492547 : Blo 1663031 40492547 := bstep (se 1 (by rfl) ⟨30369410, by rfl⟩ : syracuseStep 40492547 = 60738821) B60738821
theorem B8994347 : Blo 1663031 8994347 := bstep (se 1 (by rfl) ⟨6745760, by rfl⟩ : syracuseStep 8994347 = 13491521) B13491521
theorem B3743351 : Blo 1663031 3743351 := bstep (se 1 (by rfl) ⟨2807513, by rfl⟩ : syracuseStep 3743351 = 5615027) B5615027
theorem B2104967 : Blo 1663031 2104967 := bstep (se 1 (by rfl) ⟨1578725, by rfl⟩ : syracuseStep 2104967 = 3157451) B3157451
theorem B5619401 : Blo 1663031 5619401 := bstep (se 2 (by rfl) ⟨2107275, by rfl⟩ : syracuseStep 5619401 = 4214551) B4214551
theorem B3743531 : Blo 1663031 3743531 := bstep (se 1 (by rfl) ⟨2807648, by rfl⟩ : syracuseStep 3743531 = 5615297) B5615297
theorem B19201843 : Blo 1663031 19201843 := bstep (se 1 (by rfl) ⟨14401382, by rfl⟩ : syracuseStep 19201843 = 28802765) B28802765
theorem B3555191 : Blo 1663031 3555191 := bstep (se 1 (by rfl) ⟨2666393, by rfl⟩ : syracuseStep 3555191 = 5332787) B5332787
theorem B10665931 : Blo 1663031 10665931 := bstep (se 1 (by rfl) ⟨7999448, by rfl⟩ : syracuseStep 10665931 = 15998897) B15998897
theorem B3743801 : Blo 1663031 3743801 := bstep (se 2 (by rfl) ⟨1403925, by rfl⟩ : syracuseStep 3743801 = 2807851) B2807851
theorem B1663055 : Blo 1663031 1663055 := bstep (se 1 (by rfl) ⟨1247291, by rfl⟩ : syracuseStep 1663055 = 2494583) B2494583
theorem B1663071 : Blo 1663031 1663071 := bstep (se 1 (by rfl) ⟨1247303, by rfl⟩ : syracuseStep 1663071 = 2494607) B2494607
theorem B1663099 : Blo 1663031 1663099 := bstep (se 1 (by rfl) ⟨1247324, by rfl⟩ : syracuseStep 1663099 = 2494649) B2494649
theorem B5693597 : Blo 1663031 5693597 := bstep (se 3 (by rfl) ⟨1067549, by rfl⟩ : syracuseStep 5693597 = 2135099) B2135099
theorem B1663151 : Blo 1663031 1663151 := bstep (se 1 (by rfl) ⟨1247363, by rfl⟩ : syracuseStep 1663151 = 2494727) B2494727
theorem B1663175 : Blo 1663031 1663175 := bstep (se 1 (by rfl) ⟨1247381, by rfl⟩ : syracuseStep 1663175 = 2494763) B2494763
theorem B1663195 : Blo 1663031 1663195 := bstep (se 1 (by rfl) ⟨1247396, by rfl⟩ : syracuseStep 1663195 = 2494793) B2494793
theorem B10666241 : Blo 1663031 10666241 := bstep (se 2 (by rfl) ⟨3999840, by rfl⟩ : syracuseStep 10666241 = 7999681) B7999681
theorem B1663271 : Blo 1663031 1663271 := bstep (se 1 (by rfl) ⟨1247453, by rfl⟩ : syracuseStep 1663271 = 2494907) B2494907
theorem B11379005 : Blo 1663031 11379005 := bstep (se 3 (by rfl) ⟨2133563, by rfl⟩ : syracuseStep 11379005 = 4267127) B4267127
theorem B1663311 : Blo 1663031 1663311 := bstep (se 1 (by rfl) ⟨1247483, by rfl⟩ : syracuseStep 1663311 = 2494967) B2494967
theorem B1663327 : Blo 1663031 1663327 := bstep (se 1 (by rfl) ⟨1247495, by rfl⟩ : syracuseStep 1663327 = 2494991) B2494991
theorem B1663355 : Blo 1663031 1663355 := bstep (se 1 (by rfl) ⟨1247516, by rfl⟩ : syracuseStep 1663355 = 2495033) B2495033
theorem B3744143 : Blo 1663031 3744143 := bstep (se 1 (by rfl) ⟨2808107, by rfl⟩ : syracuseStep 3744143 = 5616215) B5616215
theorem B1663407 : Blo 1663031 1663407 := bstep (se 1 (by rfl) ⟨1247555, by rfl⟩ : syracuseStep 1663407 = 2495111) B2495111
theorem B1663431 : Blo 1663031 1663431 := bstep (se 1 (by rfl) ⟨1247573, by rfl⟩ : syracuseStep 1663431 = 2495147) B2495147
theorem B1663451 : Blo 1663031 1663451 := bstep (se 1 (by rfl) ⟨1247588, by rfl⟩ : syracuseStep 1663451 = 2495177) B2495177
theorem B1663527 : Blo 1663031 1663527 := bstep (se 1 (by rfl) ⟨1247645, by rfl⟩ : syracuseStep 1663527 = 2495291) B2495291
theorem B1663567 : Blo 1663031 1663567 := bstep (se 1 (by rfl) ⟨1247675, by rfl⟩ : syracuseStep 1663567 = 2495351) B2495351
theorem B1663583 : Blo 1663031 1663583 := bstep (se 1 (by rfl) ⟨1247687, by rfl⟩ : syracuseStep 1663583 = 2495375) B2495375
theorem B1663611 : Blo 1663031 1663611 := bstep (se 1 (by rfl) ⟨1247708, by rfl⟩ : syracuseStep 1663611 = 2495417) B2495417
theorem B1663663 : Blo 1663031 1663663 := bstep (se 1 (by rfl) ⟨1247747, by rfl⟩ : syracuseStep 1663663 = 2495495) B2495495
theorem B1663687 : Blo 1663031 1663687 := bstep (se 1 (by rfl) ⟨1247765, by rfl⟩ : syracuseStep 1663687 = 2495531) B2495531
theorem B3744467 : Blo 1663031 3744467 := bstep (se 1 (by rfl) ⟨2808350, by rfl⟩ : syracuseStep 3744467 = 5616701) B5616701
theorem B1663707 : Blo 1663031 1663707 := bstep (se 1 (by rfl) ⟨1247780, by rfl⟩ : syracuseStep 1663707 = 2495561) B2495561
theorem B1663783 : Blo 1663031 1663783 := bstep (se 1 (by rfl) ⟨1247837, by rfl⟩ : syracuseStep 1663783 = 2495675) B2495675
theorem B35971913 : Blo 1663031 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B8422217 : Blo 1663031 8422217 := bstep (se 2 (by rfl) ⟨3158331, by rfl⟩ : syracuseStep 8422217 = 6316663) B6316663
theorem B15180617 : Blo 1663031 15180617 := bstep (se 2 (by rfl) ⟨5692731, by rfl⟩ : syracuseStep 15180617 = 11385463) B11385463
theorem B1663823 : Blo 1663031 1663823 := bstep (se 1 (by rfl) ⟨1247867, by rfl⟩ : syracuseStep 1663823 = 2495735) B2495735
theorem B1663839 : Blo 1663031 1663839 := bstep (se 1 (by rfl) ⟨1247879, by rfl⟩ : syracuseStep 1663839 = 2495759) B2495759
theorem B1663867 : Blo 1663031 1663867 := bstep (se 1 (by rfl) ⟨1247900, by rfl⟩ : syracuseStep 1663867 = 2495801) B2495801
theorem B1663919 : Blo 1663031 1663919 := bstep (se 1 (by rfl) ⟨1247939, by rfl⟩ : syracuseStep 1663919 = 2495879) B2495879
theorem B1663943 : Blo 1663031 1663943 := bstep (se 1 (by rfl) ⟨1247957, by rfl⟩ : syracuseStep 1663943 = 2495915) B2495915
theorem B1663963 : Blo 1663031 1663963 := bstep (se 1 (by rfl) ⟨1247972, by rfl⟩ : syracuseStep 1663963 = 2495945) B2495945
theorem B1664039 : Blo 1663031 1664039 := bstep (se 1 (by rfl) ⟨1248029, by rfl⟩ : syracuseStep 1664039 = 2496059) B2496059
theorem B30368819 : Blo 1663031 30368819 := bstep (se 1 (by rfl) ⟨22776614, by rfl⟩ : syracuseStep 30368819 = 45553229) B45553229
theorem B6317135 : Blo 1663031 6317135 := bstep (se 1 (by rfl) ⟨4737851, by rfl⟩ : syracuseStep 6317135 = 9475703) B9475703
theorem B1664079 : Blo 1663031 1664079 := bstep (se 1 (by rfl) ⟨1248059, by rfl⟩ : syracuseStep 1664079 = 2496119) B2496119
theorem B1664095 : Blo 1663031 1664095 := bstep (se 1 (by rfl) ⟨1248071, by rfl⟩ : syracuseStep 1664095 = 2496143) B2496143
theorem B1664123 : Blo 1663031 1664123 := bstep (se 1 (by rfl) ⟨1248092, by rfl⟩ : syracuseStep 1664123 = 2496185) B2496185
theorem B35996825 : Blo 1663031 35996825 := bstep (se 2 (by rfl) ⟨13498809, by rfl⟩ : syracuseStep 35996825 = 26997619) B26997619
theorem B1664175 : Blo 1663031 1664175 := bstep (se 1 (by rfl) ⟨1248131, by rfl⟩ : syracuseStep 1664175 = 2496263) B2496263
theorem B1664199 : Blo 1663031 1664199 := bstep (se 1 (by rfl) ⟨1248149, by rfl⟩ : syracuseStep 1664199 = 2496299) B2496299
theorem B1664219 : Blo 1663031 1664219 := bstep (se 1 (by rfl) ⟨1248164, by rfl⟩ : syracuseStep 1664219 = 2496329) B2496329
theorem B4211959 : Blo 1663031 4211959 := bstep (se 1 (by rfl) ⟨3158969, by rfl⟩ : syracuseStep 4211959 = 6317939) B6317939
theorem B1664295 : Blo 1663031 1664295 := bstep (se 1 (by rfl) ⟨1248221, by rfl⟩ : syracuseStep 1664295 = 2496443) B2496443
theorem B1664335 : Blo 1663031 1664335 := bstep (se 1 (by rfl) ⟨1248251, by rfl⟩ : syracuseStep 1664335 = 2496503) B2496503
theorem B1664351 : Blo 1663031 1664351 := bstep (se 1 (by rfl) ⟨1248263, by rfl⟩ : syracuseStep 1664351 = 2496527) B2496527
theorem B1664379 : Blo 1663031 1664379 := bstep (se 1 (by rfl) ⟨1248284, by rfl⟩ : syracuseStep 1664379 = 2496569) B2496569
theorem B1664431 : Blo 1663031 1664431 := bstep (se 1 (by rfl) ⟨1248323, by rfl⟩ : syracuseStep 1664431 = 2496647) B2496647
theorem B1664455 : Blo 1663031 1664455 := bstep (se 1 (by rfl) ⟨1248341, by rfl⟩ : syracuseStep 1664455 = 2496683) B2496683
theorem B1664475 : Blo 1663031 1664475 := bstep (se 1 (by rfl) ⟨1248356, by rfl⟩ : syracuseStep 1664475 = 2496713) B2496713
theorem B21325301 : Blo 1663031 21325301 := bstep (se 5 (by rfl) ⟨999623, by rfl⟩ : syracuseStep 21325301 = 1999247) B1999247
theorem B4212233 : Blo 1663031 4212233 := bstep (se 2 (by rfl) ⟨1579587, by rfl⟩ : syracuseStep 4212233 = 3159175) B3159175
theorem B4212263 : Blo 1663031 4212263 := bstep (se 1 (by rfl) ⟨3159197, by rfl⟩ : syracuseStep 4212263 = 6318395) B6318395
theorem B1664551 : Blo 1663031 1664551 := bstep (se 1 (by rfl) ⟨1248413, by rfl⟩ : syracuseStep 1664551 = 2496827) B2496827
theorem B12641831 : Blo 1663031 12641831 := bstep (se 1 (by rfl) ⟨9481373, by rfl⟩ : syracuseStep 12641831 = 18962747) B18962747
theorem B1664591 : Blo 1663031 1664591 := bstep (se 1 (by rfl) ⟨1248443, by rfl⟩ : syracuseStep 1664591 = 2496887) B2496887
theorem B1664607 : Blo 1663031 1664607 := bstep (se 1 (by rfl) ⟨1248455, by rfl⟩ : syracuseStep 1664607 = 2496911) B2496911
theorem B102409829 : Blo 1663031 102409829 := bstep (se 4 (by rfl) ⟨9600921, by rfl⟩ : syracuseStep 102409829 = 19201843) B19201843
theorem B3745403 : Blo 1663031 3745403 := bstep (se 1 (by rfl) ⟨2809052, by rfl⟩ : syracuseStep 3745403 = 5618105) B5618105
theorem B1664635 : Blo 1663031 1664635 := bstep (se 1 (by rfl) ⟨1248476, by rfl⟩ : syracuseStep 1664635 = 2496953) B2496953
theorem B5613191 : Blo 1663031 5613191 := bstep (se 1 (by rfl) ⟨4209893, by rfl⟩ : syracuseStep 5613191 = 8419787) B8419787
theorem B9479825 : Blo 1663031 9479825 := bstep (se 2 (by rfl) ⟨3554934, by rfl⟩ : syracuseStep 9479825 = 7109869) B7109869
theorem B1664687 : Blo 1663031 1664687 := bstep (se 1 (by rfl) ⟨1248515, by rfl⟩ : syracuseStep 1664687 = 2497031) B2497031
theorem B5613245 : Blo 1663031 5613245 := bstep (se 3 (by rfl) ⟨1052483, by rfl⟩ : syracuseStep 5613245 = 2104967) B2104967
theorem B1664711 : Blo 1663031 1664711 := bstep (se 1 (by rfl) ⟨1248533, by rfl⟩ : syracuseStep 1664711 = 2497067) B2497067
theorem B1664731 : Blo 1663031 1664731 := bstep (se 1 (by rfl) ⟨1248548, by rfl⟩ : syracuseStep 1664731 = 2497097) B2497097
theorem B3745529 : Blo 1663031 3745529 := bstep (se 2 (by rfl) ⟨1404573, by rfl⟩ : syracuseStep 3745529 = 2809147) B2809147
theorem B1664807 : Blo 1663031 1664807 := bstep (se 1 (by rfl) ⟨1248605, by rfl⟩ : syracuseStep 1664807 = 2497211) B2497211
theorem B1664847 : Blo 1663031 1664847 := bstep (se 1 (by rfl) ⟨1248635, by rfl⟩ : syracuseStep 1664847 = 2497271) B2497271
theorem B5613407 : Blo 1663031 5613407 := bstep (se 1 (by rfl) ⟨4210055, by rfl⟩ : syracuseStep 5613407 = 8420111) B8420111
theorem B1664863 : Blo 1663031 1664863 := bstep (se 1 (by rfl) ⟨1248647, by rfl⟩ : syracuseStep 1664863 = 2497295) B2497295
theorem B3000169 : Blo 1663031 3000169 := bstep (se 2 (by rfl) ⟨1125063, by rfl⟩ : syracuseStep 3000169 = 2250127) B2250127
theorem B4212587 : Blo 1663031 4212587 := bstep (se 1 (by rfl) ⟨3159440, by rfl⟩ : syracuseStep 4212587 = 6318881) B6318881
theorem B1664891 : Blo 1663031 1664891 := bstep (se 1 (by rfl) ⟨1248668, by rfl⟩ : syracuseStep 1664891 = 2497337) B2497337
theorem B1664943 : Blo 1663031 1664943 := bstep (se 1 (by rfl) ⟨1248707, by rfl⟩ : syracuseStep 1664943 = 2497415) B2497415
theorem B4736951 : Blo 1663031 4736951 := bstep (se 1 (by rfl) ⟨3552713, by rfl⟩ : syracuseStep 4736951 = 7105427) B7105427
theorem B1664967 : Blo 1663031 1664967 := bstep (se 1 (by rfl) ⟨1248725, by rfl⟩ : syracuseStep 1664967 = 2497451) B2497451
theorem B1664987 : Blo 1663031 1664987 := bstep (se 1 (by rfl) ⟨1248740, by rfl⟩ : syracuseStep 1664987 = 2497481) B2497481
theorem B5613569 : Blo 1663031 5613569 := bstep (se 2 (by rfl) ⟨2105088, by rfl⟩ : syracuseStep 5613569 = 4210177) B4210177
theorem B3745799 : Blo 1663031 3745799 := bstep (se 1 (by rfl) ⟨2809349, by rfl⟩ : syracuseStep 3745799 = 5618699) B5618699
theorem B18958373 : Blo 1663031 18958373 := bstep (se 4 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 18958373 = 3554695) B3554695
theorem B3745871 : Blo 1663031 3745871 := bstep (se 1 (by rfl) ⟨2809403, by rfl⟩ : syracuseStep 3745871 = 5618807) B5618807
theorem B8423513 : Blo 1663031 8423513 := bstep (se 2 (by rfl) ⟨3158817, by rfl⟩ : syracuseStep 8423513 = 6317635) B6317635
theorem B7104779 : Blo 1663031 7104779 := bstep (se 1 (by rfl) ⟨5328584, by rfl⟩ : syracuseStep 7104779 = 10657169) B10657169
theorem B8997131 : Blo 1663031 8997131 := bstep (se 1 (by rfl) ⟨6747848, by rfl⟩ : syracuseStep 8997131 = 13495697) B13495697
theorem B9480509 : Blo 1663031 9480509 := bstep (se 3 (by rfl) ⟨1777595, by rfl⟩ : syracuseStep 9480509 = 3555191) B3555191
theorem B26995031 : Blo 1663031 26995031 := bstep (se 1 (by rfl) ⟨20246273, by rfl⟩ : syracuseStep 26995031 = 40492547) B40492547
theorem B17074583 : Blo 1663031 17074583 := bstep (se 1 (by rfl) ⟨12805937, by rfl⟩ : syracuseStep 17074583 = 25611875) B25611875
theorem B3746267 : Blo 1663031 3746267 := bstep (se 1 (by rfl) ⟨2809700, by rfl⟩ : syracuseStep 3746267 = 5619401) B5619401
theorem B8538605 : Blo 1663031 8538605 := bstep (se 3 (by rfl) ⟨1600988, by rfl⟩ : syracuseStep 8538605 = 3201977) B3201977
theorem B4213235 : Blo 1663031 4213235 := bstep (se 1 (by rfl) ⟨3159926, by rfl⟩ : syracuseStep 4213235 = 6319853) B6319853
theorem B11536921 : Blo 1663031 11536921 := bstep (se 2 (by rfl) ⟨4326345, by rfl⟩ : syracuseStep 11536921 = 8652691) B8652691
theorem B21318329 : Blo 1663031 21318329 := bstep (se 2 (by rfl) ⟨7994373, by rfl⟩ : syracuseStep 21318329 = 15988747) B15988747
theorem B21621449 : Blo 1663031 21621449 := bstep (se 2 (by rfl) ⟨8108043, by rfl⟩ : syracuseStep 21621449 = 16216087) B16216087
theorem B14600989 : Blo 1663031 14600989 := bstep (se 3 (by rfl) ⟨2737685, by rfl⟩ : syracuseStep 14600989 = 5475371) B5475371
theorem B5614379 : Blo 1663031 5614379 := bstep (se 1 (by rfl) ⟨4210784, by rfl⟩ : syracuseStep 5614379 = 8421569) B8421569
theorem B23989067 : Blo 1663031 23989067 := bstep (se 1 (by rfl) ⟨17991800, by rfl⟩ : syracuseStep 23989067 = 35983601) B35983601
theorem B12635027 : Blo 1663031 12635027 := bstep (se 1 (by rfl) ⟨9476270, by rfl⟩ : syracuseStep 12635027 = 18952541) B18952541
theorem B4737953 : Blo 1663031 4737953 := bstep (se 2 (by rfl) ⟨1776732, by rfl⟩ : syracuseStep 4737953 = 3553465) B3553465
theorem B4213691 : Blo 1663031 4213691 := bstep (se 1 (by rfl) ⟨3160268, by rfl⟩ : syracuseStep 4213691 = 6320537) B6320537
theorem B2845703 : Blo 1663031 2845703 := bstep (se 1 (by rfl) ⟨2134277, by rfl⟩ : syracuseStep 2845703 = 4268555) B4268555
theorem B31968269 : Blo 1663031 31968269 := bstep (se 3 (by rfl) ⟨5994050, by rfl⟩ : syracuseStep 31968269 = 11988101) B11988101
theorem B5614649 : Blo 1663031 5614649 := bstep (se 2 (by rfl) ⟨2105493, by rfl⟩ : syracuseStep 5614649 = 4210987) B4210987
theorem B9473219 : Blo 1663031 9473219 := bstep (se 1 (by rfl) ⟨7104914, by rfl⟩ : syracuseStep 9473219 = 14209829) B14209829
theorem B13495567 : Blo 1663031 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B4738409 : Blo 1663031 4738409 := bstep (se 2 (by rfl) ⟨1776903, by rfl⟩ : syracuseStep 4738409 = 3553807) B3553807
theorem B5614973 : Blo 1663031 5614973 := bstep (se 3 (by rfl) ⟨1052807, by rfl⟩ : syracuseStep 5614973 = 2105615) B2105615
theorem B43249031 : Blo 1663031 43249031 := bstep (se 1 (by rfl) ⟨32436773, by rfl⟩ : syracuseStep 43249031 = 64873547) B64873547
theorem B15183247 : Blo 1663031 15183247 := bstep (se 1 (by rfl) ⟨11387435, by rfl⟩ : syracuseStep 15183247 = 22774871) B22774871
theorem B2248111 : Blo 1663031 2248111 := bstep (se 1 (by rfl) ⟨1686083, by rfl⟩ : syracuseStep 2248111 = 3372167) B3372167
theorem B6319579 : Blo 1663031 6319579 := bstep (se 1 (by rfl) ⟨4739684, by rfl⟩ : syracuseStep 6319579 = 9479369) B9479369
theorem B5328443 : Blo 1663031 5328443 := bstep (se 1 (by rfl) ⟨3996332, by rfl⟩ : syracuseStep 5328443 = 7992665) B7992665
theorem B4214369 : Blo 1663031 4214369 := bstep (se 2 (by rfl) ⟨1580388, by rfl⟩ : syracuseStep 4214369 = 3160777) B3160777
theorem B5615243 : Blo 1663031 5615243 := bstep (se 1 (by rfl) ⟨4211432, by rfl⟩ : syracuseStep 5615243 = 8422865) B8422865
theorem B11988769 : Blo 1663031 11988769 := bstep (se 2 (by rfl) ⟨4495788, by rfl⟩ : syracuseStep 11988769 = 8991577) B8991577
theorem B12635999 : Blo 1663031 12635999 := bstep (se 1 (by rfl) ⟨9476999, by rfl⟩ : syracuseStep 12635999 = 18953999) B18953999
theorem B1871995 : Blo 1663031 1871995 := bstep (se 1 (by rfl) ⟨1403996, by rfl⟩ : syracuseStep 1871995 = 2807993) B2807993
theorem B2494895 : Blo 1663031 2494895 := bstep (se 1 (by rfl) ⟨1871171, by rfl⟩ : syracuseStep 2494895 = 3742343) B3742343
theorem B2494985 : Blo 1663031 2494985 := bstep (se 2 (by rfl) ⟨935619, by rfl⟩ : syracuseStep 2494985 = 1871239) B1871239
theorem B5616161 : Blo 1663031 5616161 := bstep (se 2 (by rfl) ⟨2106060, by rfl⟩ : syracuseStep 5616161 = 4212121) B4212121
theorem B2495015 : Blo 1663031 2495015 := bstep (se 1 (by rfl) ⟨1871261, by rfl⟩ : syracuseStep 2495015 = 3742523) B3742523
theorem B1872463 : Blo 1663031 1872463 := bstep (se 1 (by rfl) ⟨1404347, by rfl⟩ : syracuseStep 1872463 = 2808695) B2808695
theorem B2495099 : Blo 1663031 2495099 := bstep (se 1 (by rfl) ⟨1871324, by rfl⟩ : syracuseStep 2495099 = 3742649) B3742649
theorem B3158651 : Blo 1663031 3158651 := bstep (se 1 (by rfl) ⟨2368988, by rfl⟩ : syracuseStep 3158651 = 4737977) B4737977
theorem B6320825 : Blo 1663031 6320825 := bstep (se 2 (by rfl) ⟨2370309, by rfl⟩ : syracuseStep 6320825 = 4740619) B4740619
theorem B6320855 : Blo 1663031 6320855 := bstep (se 1 (by rfl) ⟨4740641, by rfl⟩ : syracuseStep 6320855 = 9481283) B9481283
theorem B2495225 : Blo 1663031 2495225 := bstep (se 2 (by rfl) ⟨935709, by rfl⟩ : syracuseStep 2495225 = 1871419) B1871419
theorem B5616377 : Blo 1663031 5616377 := bstep (se 2 (by rfl) ⟨2106141, by rfl⟩ : syracuseStep 5616377 = 4212283) B4212283
theorem B2495327 : Blo 1663031 2495327 := bstep (se 1 (by rfl) ⟨1871495, by rfl⟩ : syracuseStep 2495327 = 3742991) B3742991
theorem B2495339 : Blo 1663031 2495339 := bstep (se 1 (by rfl) ⟨1871504, by rfl⟩ : syracuseStep 2495339 = 3743009) B3743009
theorem B1872859 : Blo 1663031 1872859 := bstep (se 1 (by rfl) ⟨1404644, by rfl⟩ : syracuseStep 1872859 = 2809289) B2809289
theorem B5616647 : Blo 1663031 5616647 := bstep (se 1 (by rfl) ⟨4212485, by rfl⟩ : syracuseStep 5616647 = 8424971) B8424971
theorem B2495567 : Blo 1663031 2495567 := bstep (se 1 (by rfl) ⟨1871675, by rfl⟩ : syracuseStep 2495567 = 3743351) B3743351
theorem B3159137 : Blo 1663031 3159137 := bstep (se 2 (by rfl) ⟨1184676, by rfl⟩ : syracuseStep 3159137 = 2369353) B2369353
theorem B5616755 : Blo 1663031 5616755 := bstep (se 1 (by rfl) ⟨4212566, by rfl⟩ : syracuseStep 5616755 = 8425133) B8425133
theorem B2495687 : Blo 1663031 2495687 := bstep (se 1 (by rfl) ⟨1871765, by rfl⟩ : syracuseStep 2495687 = 3743531) B3743531
theorem B12629195 : Blo 1663031 12629195 := bstep (se 1 (by rfl) ⟨9471896, by rfl⟩ : syracuseStep 12629195 = 18943793) B18943793
theorem B2495849 : Blo 1663031 2495849 := bstep (se 2 (by rfl) ⟨935943, by rfl⟩ : syracuseStep 2495849 = 1871887) B1871887
theorem B5617025 : Blo 1663031 5617025 := bstep (se 2 (by rfl) ⟨2106384, by rfl⟩ : syracuseStep 5617025 = 4212769) B4212769
theorem B2807183 : Blo 1663031 2807183 := bstep (se 1 (by rfl) ⟨2105387, by rfl⟩ : syracuseStep 2807183 = 4210775) B4210775
theorem B2495927 : Blo 1663031 2495927 := bstep (se 1 (by rfl) ⟨1871945, by rfl⟩ : syracuseStep 2495927 = 3743891) B3743891
theorem B3159479 : Blo 1663031 3159479 := bstep (se 1 (by rfl) ⟨2369609, by rfl⟩ : syracuseStep 3159479 = 4739219) B4739219
theorem B3552731 : Blo 1663031 3552731 := bstep (se 1 (by rfl) ⟨2664548, by rfl⟩ : syracuseStep 3552731 = 5329097) B5329097
theorem B2495963 : Blo 1663031 2495963 := bstep (se 1 (by rfl) ⟨1871972, by rfl⟩ : syracuseStep 2495963 = 3743945) B3743945
theorem B2807419 : Blo 1663031 2807419 := bstep (se 1 (by rfl) ⟨2105564, by rfl⟩ : syracuseStep 2807419 = 4211129) B4211129
theorem B3552979 : Blo 1663031 3552979 := bstep (se 1 (by rfl) ⟨2664734, by rfl⟩ : syracuseStep 3552979 = 5329469) B5329469
theorem B5994283 : Blo 1663031 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B8419139 : Blo 1663031 8419139 := bstep (se 1 (by rfl) ⟨6314354, by rfl⟩ : syracuseStep 8419139 = 12628709) B12628709
theorem B3159881 : Blo 1663031 3159881 := bstep (se 2 (by rfl) ⟨1184955, by rfl⟩ : syracuseStep 3159881 = 2369911) B2369911
theorem B2496431 : Blo 1663031 2496431 := bstep (se 1 (by rfl) ⟨1872323, by rfl⟩ : syracuseStep 2496431 = 3744647) B3744647
theorem B6076417 : Blo 1663031 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B2496521 : Blo 1663031 2496521 := bstep (se 2 (by rfl) ⟨936195, by rfl⟩ : syracuseStep 2496521 = 1872391) B1872391
theorem B2496551 : Blo 1663031 2496551 := bstep (se 1 (by rfl) ⟨1872413, by rfl⟩ : syracuseStep 2496551 = 3744827) B3744827
theorem B102520889 : Blo 1663031 102520889 := bstep (se 2 (by rfl) ⟨38445333, by rfl⟩ : syracuseStep 102520889 = 76890667) B76890667
theorem B2496635 : Blo 1663031 2496635 := bstep (se 1 (by rfl) ⟨1872476, by rfl⟩ : syracuseStep 2496635 = 3744953) B3744953
theorem B5617835 : Blo 1663031 5617835 := bstep (se 1 (by rfl) ⟨4213376, by rfl⟩ : syracuseStep 5617835 = 8426753) B8426753
theorem B2496761 : Blo 1663031 2496761 := bstep (se 2 (by rfl) ⟨936285, by rfl⟩ : syracuseStep 2496761 = 1872571) B1872571
theorem B2496863 : Blo 1663031 2496863 := bstep (se 1 (by rfl) ⟨1872647, by rfl⟩ : syracuseStep 2496863 = 3745295) B3745295
theorem B2529641 : Blo 1663031 2529641 := bstep (se 2 (by rfl) ⟨948615, by rfl⟩ : syracuseStep 2529641 = 1897231) B1897231
theorem B2496875 : Blo 1663031 2496875 := bstep (se 1 (by rfl) ⟨1872656, by rfl⟩ : syracuseStep 2496875 = 3745313) B3745313
theorem B23976323 : Blo 1663031 23976323 := bstep (se 1 (by rfl) ⟨17982242, by rfl⟩ : syracuseStep 23976323 = 35964485) B35964485
theorem B2808283 : Blo 1663031 2808283 := bstep (se 1 (by rfl) ⟨2106212, by rfl⟩ : syracuseStep 2808283 = 4212425) B4212425
theorem B3742217 : Blo 1663031 3742217 := bstep (se 2 (by rfl) ⟨1403331, by rfl⟩ : syracuseStep 3742217 = 2806663) B2806663
theorem B3160595 : Blo 1663031 3160595 := bstep (se 1 (by rfl) ⟨2370446, by rfl⟩ : syracuseStep 3160595 = 4740893) B4740893
theorem B7109153 : Blo 1663031 7109153 := bstep (se 2 (by rfl) ⟨2665932, by rfl⟩ : syracuseStep 7109153 = 5331865) B5331865
theorem B3160633 : Blo 1663031 3160633 := bstep (se 2 (by rfl) ⟨1185237, by rfl⟩ : syracuseStep 3160633 = 2370475) B2370475
theorem B2497103 : Blo 1663031 2497103 := bstep (se 1 (by rfl) ⟨1872827, by rfl⟩ : syracuseStep 2497103 = 3745655) B3745655
theorem B7993991 : Blo 1663031 7993991 := bstep (se 1 (by rfl) ⟨5995493, by rfl⟩ : syracuseStep 7993991 = 11990987) B11990987
theorem B13163143 : Blo 1663031 13163143 := bstep (se 1 (by rfl) ⟨9872357, by rfl⟩ : syracuseStep 13163143 = 19744715) B19744715
theorem B5692103 : Blo 1663031 5692103 := bstep (se 1 (by rfl) ⟨4269077, by rfl⟩ : syracuseStep 5692103 = 8538155) B8538155
theorem B5618375 : Blo 1663031 5618375 := bstep (se 1 (by rfl) ⟨4213781, by rfl⟩ : syracuseStep 5618375 = 8427563) B8427563
theorem B2497223 : Blo 1663031 2497223 := bstep (se 1 (by rfl) ⟨1872917, by rfl⟩ : syracuseStep 2497223 = 3745835) B3745835
theorem B6314705 : Blo 1663031 6314705 := bstep (se 2 (by rfl) ⟨2368014, by rfl⟩ : syracuseStep 6314705 = 4736029) B4736029
theorem B3742559 : Blo 1663031 3742559 := bstep (se 1 (by rfl) ⟨2806919, by rfl⟩ : syracuseStep 3742559 = 5613839) B5613839
theorem B2497385 : Blo 1663031 2497385 := bstep (se 2 (by rfl) ⟨936519, by rfl⟩ : syracuseStep 2497385 = 1873039) B1873039
theorem B3160937 : Blo 1663031 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B3554209 : Blo 1663031 3554209 := bstep (se 2 (by rfl) ⟨1332828, by rfl⟩ : syracuseStep 3554209 = 2665657) B2665657
theorem B2497463 : Blo 1663031 2497463 := bstep (se 1 (by rfl) ⟨1873097, by rfl⟩ : syracuseStep 2497463 = 3746195) B3746195
theorem B2497499 : Blo 1663031 2497499 := bstep (se 1 (by rfl) ⟨1873124, by rfl⟩ : syracuseStep 2497499 = 3746249) B3746249
theorem B4209671 : Blo 1663031 4209671 := bstep (se 1 (by rfl) ⟨3157253, by rfl⟩ : syracuseStep 4209671 = 6314507) B6314507
theorem B6315023 : Blo 1663031 6315023 := bstep (se 1 (by rfl) ⟨4736267, by rfl⟩ : syracuseStep 6315023 = 9472535) B9472535
theorem B3742739 : Blo 1663031 3742739 := bstep (se 1 (by rfl) ⟨2807054, by rfl⟩ : syracuseStep 3742739 = 5614109) B5614109
theorem B2808911 : Blo 1663031 2808911 := bstep (se 1 (by rfl) ⟨2106683, by rfl⟩ : syracuseStep 2808911 = 4213367) B4213367
theorem B1776763 : Blo 1663031 1776763 := bstep (se 1 (by rfl) ⟨1332572, by rfl⟩ : syracuseStep 1776763 = 2665145) B2665145
theorem B13491353 : Blo 1663031 13491353 := bstep (se 2 (by rfl) ⟨5059257, by rfl⟩ : syracuseStep 13491353 = 10118515) B10118515
theorem B8428697 : Blo 1663031 8428697 := bstep (se 2 (by rfl) ⟨3160761, by rfl⟩ : syracuseStep 8428697 = 6321523) B6321523
theorem B18955457 : Blo 1663031 18955457 := bstep (se 2 (by rfl) ⟨7108296, by rfl⟩ : syracuseStep 18955457 = 14216593) B14216593
theorem B25607447 : Blo 1663031 25607447 := bstep (se 1 (by rfl) ⟨19205585, by rfl⟩ : syracuseStep 25607447 = 38411171) B38411171
theorem B3743081 : Blo 1663031 3743081 := bstep (se 2 (by rfl) ⟨1403655, by rfl⟩ : syracuseStep 3743081 = 2807311) B2807311
theorem B3374443 : Blo 1663031 3374443 := bstep (se 1 (by rfl) ⟨2530832, by rfl⟩ : syracuseStep 3374443 = 5061665) B5061665
theorem B11992483 : Blo 1663031 11992483 := bstep (se 1 (by rfl) ⟨8994362, by rfl⟩ : syracuseStep 11992483 = 17988725) B17988725
theorem B2104795 : Blo 1663031 2104795 := bstep (se 1 (by rfl) ⟨1578596, by rfl⟩ : syracuseStep 2104795 = 3157193) B3157193
theorem B5619239 : Blo 1663031 5619239 := bstep (se 1 (by rfl) ⟨4214429, by rfl⟩ : syracuseStep 5619239 = 8428859) B8428859
theorem B5619347 : Blo 1663031 5619347 := bstep (se 1 (by rfl) ⟨4214510, by rfl⟩ : syracuseStep 5619347 = 8429021) B8429021
theorem B5996231 : Blo 1663031 5996231 := bstep (se 1 (by rfl) ⟨4497173, by rfl⟩ : syracuseStep 5996231 = 8994347) B8994347
theorem B18964205 : Blo 1663031 18964205 := bstep (se 3 (by rfl) ⟨3555788, by rfl⟩ : syracuseStep 18964205 = 7111577) B7111577
theorem B9248579 : Blo 1663031 9248579 := bstep (se 1 (by rfl) ⟨6936434, by rfl⟩ : syracuseStep 9248579 = 13872869) B13872869
theorem B1777583 : Blo 1663031 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B14221241 : Blo 1663031 14221241 := bstep (se 2 (by rfl) ⟨5332965, by rfl⟩ : syracuseStep 14221241 = 10665931) B10665931
theorem B3743675 : Blo 1663031 3743675 := bstep (se 1 (by rfl) ⟨2807756, by rfl⟩ : syracuseStep 3743675 = 5615513) B5615513
theorem B8101889 : Blo 1663031 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B7110827 : Blo 1663031 7110827 := bstep (se 1 (by rfl) ⟨5333120, by rfl⟩ : syracuseStep 7110827 = 10666241) B10666241
theorem B7586003 : Blo 1663031 7586003 := bstep (se 1 (by rfl) ⟨5689502, by rfl⟩ : syracuseStep 7586003 = 11379005) B11379005
theorem B1663263 : Blo 1663031 1663263 := bstep (se 1 (by rfl) ⟨1247447, by rfl⟩ : syracuseStep 1663263 = 2494895) B2494895
theorem B1663323 : Blo 1663031 1663323 := bstep (se 1 (by rfl) ⟨1247492, by rfl⟩ : syracuseStep 1663323 = 2494985) B2494985
theorem B3744107 : Blo 1663031 3744107 := bstep (se 1 (by rfl) ⟨2808080, by rfl⟩ : syracuseStep 3744107 = 5616161) B5616161
theorem B1663343 : Blo 1663031 1663343 := bstep (se 1 (by rfl) ⟨1247507, by rfl⟩ : syracuseStep 1663343 = 2495015) B2495015
theorem B1663399 : Blo 1663031 1663399 := bstep (se 1 (by rfl) ⟨1247549, by rfl⟩ : syracuseStep 1663399 = 2495099) B2495099
theorem B2105767 : Blo 1663031 2105767 := bstep (se 1 (by rfl) ⟨1579325, by rfl⟩ : syracuseStep 2105767 = 3158651) B3158651
theorem B1663483 : Blo 1663031 1663483 := bstep (se 1 (by rfl) ⟨1247612, by rfl⟩ : syracuseStep 1663483 = 2495225) B2495225
theorem B3744251 : Blo 1663031 3744251 := bstep (se 1 (by rfl) ⟨2808188, by rfl⟩ : syracuseStep 3744251 = 5616377) B5616377
theorem B1663551 : Blo 1663031 1663551 := bstep (se 1 (by rfl) ⟨1247663, by rfl⟩ : syracuseStep 1663551 = 2495327) B2495327
theorem B1663559 : Blo 1663031 1663559 := bstep (se 1 (by rfl) ⟨1247669, by rfl⟩ : syracuseStep 1663559 = 2495339) B2495339
theorem B3744377 : Blo 1663031 3744377 := bstep (se 2 (by rfl) ⟨1404141, by rfl⟩ : syracuseStep 3744377 = 2808283) B2808283
theorem B3744431 : Blo 1663031 3744431 := bstep (se 1 (by rfl) ⟨2808323, by rfl⟩ : syracuseStep 3744431 = 5616647) B5616647
theorem B4211423 : Blo 1663031 4211423 := bstep (se 1 (by rfl) ⟨3158567, by rfl⟩ : syracuseStep 4211423 = 6317135) B6317135
theorem B1663711 : Blo 1663031 1663711 := bstep (se 1 (by rfl) ⟨1247783, by rfl⟩ : syracuseStep 1663711 = 2495567) B2495567
theorem B2106091 : Blo 1663031 2106091 := bstep (se 1 (by rfl) ⟨1579568, by rfl⟩ : syracuseStep 2106091 = 3159137) B3159137
theorem B3744503 : Blo 1663031 3744503 := bstep (se 1 (by rfl) ⟨2808377, by rfl⟩ : syracuseStep 3744503 = 5616755) B5616755
theorem B1663791 : Blo 1663031 1663791 := bstep (se 1 (by rfl) ⟨1247843, by rfl⟩ : syracuseStep 1663791 = 2495687) B2495687
theorem B1663899 : Blo 1663031 1663899 := bstep (se 1 (by rfl) ⟨1247924, by rfl⟩ : syracuseStep 1663899 = 2495849) B2495849
theorem B3744683 : Blo 1663031 3744683 := bstep (se 1 (by rfl) ⟨2808512, by rfl⟩ : syracuseStep 3744683 = 5617025) B5617025
theorem B1663951 : Blo 1663031 1663951 := bstep (se 1 (by rfl) ⟨1247963, by rfl⟩ : syracuseStep 1663951 = 2495927) B2495927
theorem B2106319 : Blo 1663031 2106319 := bstep (se 1 (by rfl) ⟨1579739, by rfl⟩ : syracuseStep 2106319 = 3159479) B3159479
theorem B2368487 : Blo 1663031 2368487 := bstep (se 1 (by rfl) ⟨1776365, by rfl⟩ : syracuseStep 2368487 = 3552731) B3552731
theorem B1663975 : Blo 1663031 1663975 := bstep (se 1 (by rfl) ⟨1247981, by rfl⟩ : syracuseStep 1663975 = 2495963) B2495963
theorem B68273219 : Blo 1663031 68273219 := bstep (se 1 (by rfl) ⟨51204914, by rfl⟩ : syracuseStep 68273219 = 102409829) B102409829
theorem B5612759 : Blo 1663031 5612759 := bstep (se 1 (by rfl) ⟨4209569, by rfl⟩ : syracuseStep 5612759 = 8419139) B8419139
theorem B2106587 : Blo 1663031 2106587 := bstep (se 1 (by rfl) ⟨1579940, by rfl⟩ : syracuseStep 2106587 = 3159881) B3159881
theorem B1664287 : Blo 1663031 1664287 := bstep (se 1 (by rfl) ⟨1248215, by rfl⟩ : syracuseStep 1664287 = 2496431) B2496431
theorem B1664347 : Blo 1663031 1664347 := bstep (se 1 (by rfl) ⟨1248260, by rfl⟩ : syracuseStep 1664347 = 2496521) B2496521
theorem B1664367 : Blo 1663031 1664367 := bstep (se 1 (by rfl) ⟨1248275, by rfl⟩ : syracuseStep 1664367 = 2496551) B2496551
theorem B68347259 : Blo 1663031 68347259 := bstep (se 1 (by rfl) ⟨51260444, by rfl⟩ : syracuseStep 68347259 = 102520889) B102520889
theorem B1664423 : Blo 1663031 1664423 := bstep (se 1 (by rfl) ⟨1248317, by rfl⟩ : syracuseStep 1664423 = 2496635) B2496635
theorem B3745223 : Blo 1663031 3745223 := bstep (se 1 (by rfl) ⟨2808917, by rfl⟩ : syracuseStep 3745223 = 5617835) B5617835
theorem B2369017 : Blo 1663031 2369017 := bstep (se 2 (by rfl) ⟨888381, by rfl⟩ : syracuseStep 2369017 = 1776763) B1776763
theorem B1664507 : Blo 1663031 1664507 := bstep (se 1 (by rfl) ⟨1248380, by rfl⟩ : syracuseStep 1664507 = 2496761) B2496761
theorem B4736519 : Blo 1663031 4736519 := bstep (se 1 (by rfl) ⟨3552389, by rfl⟩ : syracuseStep 4736519 = 7104779) B7104779
theorem B5998087 : Blo 1663031 5998087 := bstep (se 1 (by rfl) ⟨4498565, by rfl⟩ : syracuseStep 5998087 = 8997131) B8997131
theorem B1664575 : Blo 1663031 1664575 := bstep (se 1 (by rfl) ⟨1248431, by rfl⟩ : syracuseStep 1664575 = 2496863) B2496863
theorem B1664583 : Blo 1663031 1664583 := bstep (se 1 (by rfl) ⟨1248437, by rfl⟩ : syracuseStep 1664583 = 2496875) B2496875
theorem B15984215 : Blo 1663031 15984215 := bstep (se 1 (by rfl) ⟨11988161, by rfl⟩ : syracuseStep 15984215 = 23976323) B23976323
theorem B2107063 : Blo 1663031 2107063 := bstep (se 1 (by rfl) ⟨1580297, by rfl⟩ : syracuseStep 2107063 = 3160595) B3160595
theorem B1664735 : Blo 1663031 1664735 := bstep (se 1 (by rfl) ⟨1248551, by rfl⟩ : syracuseStep 1664735 = 2497103) B2497103
theorem B3794735 : Blo 1663031 3794735 := bstep (se 1 (by rfl) ⟨2846051, by rfl⟩ : syracuseStep 3794735 = 5692103) B5692103
theorem B3745583 : Blo 1663031 3745583 := bstep (se 1 (by rfl) ⟨2809187, by rfl⟩ : syracuseStep 3745583 = 5618375) B5618375
theorem B1664815 : Blo 1663031 1664815 := bstep (se 1 (by rfl) ⟨1248611, by rfl⟩ : syracuseStep 1664815 = 2497223) B2497223
theorem B20244329 : Blo 1663031 20244329 := bstep (se 2 (by rfl) ⟨7591623, by rfl⟩ : syracuseStep 20244329 = 15183247) B15183247
theorem B57657197 : Blo 1663031 57657197 := bstep (se 3 (by rfl) ⟨10810724, by rfl⟩ : syracuseStep 57657197 = 21621449) B21621449
theorem B15992711 : Blo 1663031 15992711 := bstep (se 1 (by rfl) ⟨11994533, by rfl⟩ : syracuseStep 15992711 = 23989067) B23989067
theorem B1664923 : Blo 1663031 1664923 := bstep (se 1 (by rfl) ⟨1248692, by rfl⟩ : syracuseStep 1664923 = 2497385) B2497385
theorem B2107291 : Blo 1663031 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B8423351 : Blo 1663031 8423351 := bstep (se 1 (by rfl) ⟨6317513, by rfl⟩ : syracuseStep 8423351 = 12635027) B12635027
theorem B1664975 : Blo 1663031 1664975 := bstep (se 1 (by rfl) ⟨1248731, by rfl⟩ : syracuseStep 1664975 = 2497463) B2497463
theorem B1664999 : Blo 1663031 1664999 := bstep (se 1 (by rfl) ⟨1248749, by rfl⟩ : syracuseStep 1664999 = 2497499) B2497499
theorem B4737305 : Blo 1663031 4737305 := bstep (se 2 (by rfl) ⟨1776489, by rfl⟩ : syracuseStep 4737305 = 3552979) B3552979
theorem B3746159 : Blo 1663031 3746159 := bstep (se 1 (by rfl) ⟨2809619, by rfl⟩ : syracuseStep 3746159 = 5619239) B5619239
theorem B15985025 : Blo 1663031 15985025 := bstep (se 2 (by rfl) ⟨5994384, by rfl⟩ : syracuseStep 15985025 = 11988769) B11988769
theorem B12634541 : Blo 1663031 12634541 := bstep (se 3 (by rfl) ⟨2368976, by rfl⟩ : syracuseStep 12634541 = 4737953) B4737953
theorem B3746231 : Blo 1663031 3746231 := bstep (se 1 (by rfl) ⟨2809673, by rfl⟩ : syracuseStep 3746231 = 5619347) B5619347
theorem B4000225 : Blo 1663031 4000225 := bstep (se 2 (by rfl) ⟨1500084, by rfl⟩ : syracuseStep 4000225 = 3000169) B3000169
theorem B12642803 : Blo 1663031 12642803 := bstep (se 1 (by rfl) ⟨9482102, by rfl⟩ : syracuseStep 12642803 = 18964205) B18964205
theorem B8423999 : Blo 1663031 8423999 := bstep (se 1 (by rfl) ⟨6317999, by rfl⟩ : syracuseStep 8423999 = 12635999) B12635999
theorem B9480827 : Blo 1663031 9480827 := bstep (se 1 (by rfl) ⟨7110620, by rfl⟩ : syracuseStep 9480827 = 14221241) B14221241
theorem B7588541 : Blo 1663031 7588541 := bstep (se 3 (by rfl) ⟨1422851, by rfl⟩ : syracuseStep 7588541 = 2845703) B2845703
theorem B3795731 : Blo 1663031 3795731 := bstep (se 1 (by rfl) ⟨2846798, by rfl⟩ : syracuseStep 3795731 = 5693597) B5693597
theorem B4213883 : Blo 1663031 4213883 := bstep (se 1 (by rfl) ⟨3160412, by rfl⟩ : syracuseStep 4213883 = 6320825) B6320825
theorem B4213903 : Blo 1663031 4213903 := bstep (se 1 (by rfl) ⟨3160427, by rfl⟩ : syracuseStep 4213903 = 6320855) B6320855
theorem B23981275 : Blo 1663031 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B5614811 : Blo 1663031 5614811 := bstep (se 1 (by rfl) ⟨4211108, by rfl⟩ : syracuseStep 5614811 = 8422217) B8422217
theorem B10120411 : Blo 1663031 10120411 := bstep (se 1 (by rfl) ⟨7590308, by rfl⟩ : syracuseStep 10120411 = 15180617) B15180617
theorem B20245879 : Blo 1663031 20245879 := bstep (se 1 (by rfl) ⟨15184409, by rfl⟩ : syracuseStep 20245879 = 30368819) B30368819
theorem B4214177 : Blo 1663031 4214177 := bstep (se 2 (by rfl) ⟨1580316, by rfl⟩ : syracuseStep 4214177 = 3160633) B3160633
theorem B23997883 : Blo 1663031 23997883 := bstep (se 1 (by rfl) ⟨17998412, by rfl⟩ : syracuseStep 23997883 = 35996825) B35996825
theorem B17550857 : Blo 1663031 17550857 := bstep (se 2 (by rfl) ⟨6581571, by rfl⟩ : syracuseStep 17550857 = 13163143) B13163143
theorem B1871455 : Blo 1663031 1871455 := bstep (se 1 (by rfl) ⟨1403591, by rfl⟩ : syracuseStep 1871455 = 2807183) B2807183
theorem B14216867 : Blo 1663031 14216867 := bstep (se 1 (by rfl) ⟨10662650, by rfl⟩ : syracuseStep 14216867 = 21325301) B21325301
theorem B6319883 : Blo 1663031 6319883 := bstep (se 1 (by rfl) ⟨4739912, by rfl⟩ : syracuseStep 6319883 = 9479825) B9479825
theorem B4738945 : Blo 1663031 4738945 := bstep (se 2 (by rfl) ⟨1777104, by rfl⟩ : syracuseStep 4738945 = 3554209) B3554209
theorem B3157967 : Blo 1663031 3157967 := bstep (se 1 (by rfl) ⟨2368475, by rfl⟩ : syracuseStep 3157967 = 4736951) B4736951
theorem B5615675 : Blo 1663031 5615675 := bstep (se 1 (by rfl) ⟨4211756, by rfl⟩ : syracuseStep 5615675 = 8423513) B8423513
theorem B14209181 : Blo 1663031 14209181 := bstep (se 3 (by rfl) ⟨2664221, by rfl⟩ : syracuseStep 14209181 = 5328443) B5328443
theorem B6320339 : Blo 1663031 6320339 := bstep (se 1 (by rfl) ⟨4740254, by rfl⟩ : syracuseStep 6320339 = 9480509) B9480509
theorem B11383055 : Blo 1663031 11383055 := bstep (se 1 (by rfl) ⟨8537291, by rfl⟩ : syracuseStep 11383055 = 17074583) B17074583
theorem B5615945 : Blo 1663031 5615945 := bstep (se 2 (by rfl) ⟨2105979, by rfl⟩ : syracuseStep 5615945 = 4211959) B4211959
theorem B2494811 : Blo 1663031 2494811 := bstep (se 1 (by rfl) ⟨1871108, by rfl⟩ : syracuseStep 2494811 = 3742217) B3742217
theorem B17994089 : Blo 1663031 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B4739435 : Blo 1663031 4739435 := bstep (se 1 (by rfl) ⟨3554576, by rfl⟩ : syracuseStep 4739435 = 7109153) B7109153
theorem B5329327 : Blo 1663031 5329327 := bstep (se 1 (by rfl) ⟨3996995, by rfl⟩ : syracuseStep 5329327 = 7993991) B7993991
theorem B2495039 : Blo 1663031 2495039 := bstep (se 1 (by rfl) ⟨1871279, by rfl⟩ : syracuseStep 2495039 = 3742559) B3742559
theorem B2806393 : Blo 1663031 2806393 := bstep (se 2 (by rfl) ⟨1052397, by rfl⟩ : syracuseStep 2806393 = 2104795) B2104795
theorem B8426105 : Blo 1663031 8426105 := bstep (se 2 (by rfl) ⟨3159789, by rfl⟩ : syracuseStep 8426105 = 6319579) B6319579
theorem B2806447 : Blo 1663031 2806447 := bstep (se 1 (by rfl) ⟨2104835, by rfl⟩ : syracuseStep 2806447 = 4209671) B4209671
theorem B21312179 : Blo 1663031 21312179 := bstep (se 1 (by rfl) ⟨15984134, by rfl⟩ : syracuseStep 21312179 = 31968269) B31968269
theorem B2495159 : Blo 1663031 2495159 := bstep (se 1 (by rfl) ⟨1871369, by rfl⟩ : syracuseStep 2495159 = 3742739) B3742739
theorem B1872607 : Blo 1663031 1872607 := bstep (se 1 (by rfl) ⟨1404455, by rfl⟩ : syracuseStep 1872607 = 2808911) B2808911
theorem B12636971 : Blo 1663031 12636971 := bstep (se 1 (by rfl) ⟨9477728, by rfl⟩ : syracuseStep 12636971 = 18955457) B18955457
theorem B2495387 : Blo 1663031 2495387 := bstep (se 1 (by rfl) ⟨1871540, by rfl⟩ : syracuseStep 2495387 = 3743081) B3743081
theorem B3158939 : Blo 1663031 3158939 := bstep (se 1 (by rfl) ⟨2369204, by rfl⟩ : syracuseStep 3158939 = 4738409) B4738409
theorem B28832687 : Blo 1663031 28832687 := bstep (se 1 (by rfl) ⟨21624515, by rfl⟩ : syracuseStep 28832687 = 43249031) B43249031
theorem B7992377 : Blo 1663031 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B4740221 : Blo 1663031 4740221 := bstep (se 3 (by rfl) ⟨888791, by rfl⟩ : syracuseStep 4740221 = 1777583) B1777583
theorem B6165719 : Blo 1663031 6165719 := bstep (se 1 (by rfl) ⟨4624289, by rfl⟩ : syracuseStep 6165719 = 9248579) B9248579
theorem B2495783 : Blo 1663031 2495783 := bstep (se 1 (by rfl) ⟨1871837, by rfl⟩ : syracuseStep 2495783 = 3743675) B3743675
theorem B2495867 : Blo 1663031 2495867 := bstep (se 1 (by rfl) ⟨1871900, by rfl⟩ : syracuseStep 2495867 = 3743801) B3743801
theorem B2495993 : Blo 1663031 2495993 := bstep (se 2 (by rfl) ⟨935997, by rfl⟩ : syracuseStep 2495993 = 1871995) B1871995
theorem B2496095 : Blo 1663031 2496095 := bstep (se 1 (by rfl) ⟨1872071, by rfl⟩ : syracuseStep 2496095 = 3744143) B3744143
theorem B2496311 : Blo 1663031 2496311 := bstep (se 1 (by rfl) ⟨1872233, by rfl⟩ : syracuseStep 2496311 = 3744467) B3744467
theorem B15382561 : Blo 1663031 15382561 := bstep (se 2 (by rfl) ⟨5768460, by rfl⟩ : syracuseStep 15382561 = 11536921) B11536921
theorem B2496617 : Blo 1663031 2496617 := bstep (se 2 (by rfl) ⟨936231, by rfl⟩ : syracuseStep 2496617 = 1872463) B1872463
theorem B8419463 : Blo 1663031 8419463 := bstep (se 1 (by rfl) ⟨6314597, by rfl⟩ : syracuseStep 8419463 = 12629195) B12629195
theorem B2808155 : Blo 1663031 2808155 := bstep (se 1 (by rfl) ⟨2106116, by rfl⟩ : syracuseStep 2808155 = 4212233) B4212233
theorem B2808175 : Blo 1663031 2808175 := bstep (se 1 (by rfl) ⟨2106131, by rfl⟩ : syracuseStep 2808175 = 4212263) B4212263
theorem B8427887 : Blo 1663031 8427887 := bstep (se 1 (by rfl) ⟨6320915, by rfl⟩ : syracuseStep 8427887 = 12641831) B12641831
theorem B2496935 : Blo 1663031 2496935 := bstep (se 1 (by rfl) ⟨1872701, by rfl⟩ : syracuseStep 2496935 = 3745403) B3745403
theorem B3742127 : Blo 1663031 3742127 := bstep (se 1 (by rfl) ⟨2806595, by rfl⟩ : syracuseStep 3742127 = 5613191) B5613191
theorem B3742163 : Blo 1663031 3742163 := bstep (se 1 (by rfl) ⟨2806622, by rfl⟩ : syracuseStep 3742163 = 5613245) B5613245
theorem B2497019 : Blo 1663031 2497019 := bstep (se 1 (by rfl) ⟨1872764, by rfl⟩ : syracuseStep 2497019 = 3745529) B3745529
theorem B3742271 : Blo 1663031 3742271 := bstep (se 1 (by rfl) ⟨2806703, by rfl⟩ : syracuseStep 3742271 = 5613407) B5613407
theorem B2808391 : Blo 1663031 2808391 := bstep (se 1 (by rfl) ⟨2106293, by rfl⟩ : syracuseStep 2808391 = 4212587) B4212587
theorem B2497145 : Blo 1663031 2497145 := bstep (se 2 (by rfl) ⟨936429, by rfl⟩ : syracuseStep 2497145 = 1872859) B1872859
theorem B3742379 : Blo 1663031 3742379 := bstep (se 1 (by rfl) ⟨2806784, by rfl⟩ : syracuseStep 3742379 = 5613569) B5613569
theorem B2497199 : Blo 1663031 2497199 := bstep (se 1 (by rfl) ⟨1872899, by rfl⟩ : syracuseStep 2497199 = 3745799) B3745799
theorem B12638915 : Blo 1663031 12638915 := bstep (se 1 (by rfl) ⟨9479186, by rfl⟩ : syracuseStep 12638915 = 18958373) B18958373
theorem B2497247 : Blo 1663031 2497247 := bstep (se 1 (by rfl) ⟨1872935, by rfl⟩ : syracuseStep 2497247 = 3745871) B3745871
theorem B77871941 : Blo 1663031 77871941 := bstep (se 4 (by rfl) ⟨7300494, by rfl⟩ : syracuseStep 77871941 = 14600989) B14600989
theorem B17996687 : Blo 1663031 17996687 := bstep (se 1 (by rfl) ⟨13497515, by rfl⟩ : syracuseStep 17996687 = 26995031) B26995031
theorem B1686427 : Blo 1663031 1686427 := bstep (se 1 (by rfl) ⟨1264820, by rfl⟩ : syracuseStep 1686427 = 2529641) B2529641
theorem B2497511 : Blo 1663031 2497511 := bstep (se 1 (by rfl) ⟨1873133, by rfl⟩ : syracuseStep 2497511 = 3746267) B3746267
theorem B5692403 : Blo 1663031 5692403 := bstep (se 1 (by rfl) ⟨4269302, by rfl⟩ : syracuseStep 5692403 = 8538605) B8538605
theorem B2808823 : Blo 1663031 2808823 := bstep (se 1 (by rfl) ⟨2106617, by rfl⟩ : syracuseStep 2808823 = 4213235) B4213235
theorem B14212219 : Blo 1663031 14212219 := bstep (se 1 (by rfl) ⟨10659164, by rfl⟩ : syracuseStep 14212219 = 21318329) B21318329
theorem B4209803 : Blo 1663031 4209803 := bstep (se 1 (by rfl) ⟨3157352, by rfl⟩ : syracuseStep 4209803 = 6314705) B6314705
theorem B3742919 : Blo 1663031 3742919 := bstep (se 1 (by rfl) ⟨2807189, by rfl⟩ : syracuseStep 3742919 = 5614379) B5614379
theorem B15989977 : Blo 1663031 15989977 := bstep (se 2 (by rfl) ⟨5996241, by rfl⟩ : syracuseStep 15989977 = 11992483) B11992483
theorem B17997029 : Blo 1663031 17997029 := bstep (se 4 (by rfl) ⟨1687221, by rfl⟩ : syracuseStep 17997029 = 3374443) B3374443
theorem B2997481 : Blo 1663031 2997481 := bstep (se 2 (by rfl) ⟨1124055, by rfl⟩ : syracuseStep 2997481 = 2248111) B2248111
theorem B2809127 : Blo 1663031 2809127 := bstep (se 1 (by rfl) ⟨2106845, by rfl⟩ : syracuseStep 2809127 = 4213691) B4213691
theorem B4210015 : Blo 1663031 4210015 := bstep (se 1 (by rfl) ⟨3157511, by rfl⟩ : syracuseStep 4210015 = 6315023) B6315023
theorem B3743099 : Blo 1663031 3743099 := bstep (se 1 (by rfl) ⟨2807324, by rfl⟩ : syracuseStep 3743099 = 5614649) B5614649
theorem B8994235 : Blo 1663031 8994235 := bstep (se 1 (by rfl) ⟨6745676, by rfl⟩ : syracuseStep 8994235 = 13491353) B13491353
theorem B5619131 : Blo 1663031 5619131 := bstep (se 1 (by rfl) ⟨4214348, by rfl⟩ : syracuseStep 5619131 = 8428697) B8428697
theorem B6315479 : Blo 1663031 6315479 := bstep (se 1 (by rfl) ⟨4736609, by rfl⟩ : syracuseStep 6315479 = 9473219) B9473219
theorem B3743225 : Blo 1663031 3743225 := bstep (se 2 (by rfl) ⟨1403709, by rfl⟩ : syracuseStep 3743225 = 2807419) B2807419
theorem B17071631 : Blo 1663031 17071631 := bstep (se 1 (by rfl) ⟨12803723, by rfl⟩ : syracuseStep 17071631 = 25607447) B25607447
theorem B3743315 : Blo 1663031 3743315 := bstep (se 1 (by rfl) ⟨2807486, by rfl⟩ : syracuseStep 3743315 = 5614973) B5614973
theorem B2809579 : Blo 1663031 2809579 := bstep (se 1 (by rfl) ⟨2107184, by rfl⟩ : syracuseStep 2809579 = 4214369) B4214369
theorem B3743495 : Blo 1663031 3743495 := bstep (se 1 (by rfl) ⟨2807621, by rfl⟩ : syracuseStep 3743495 = 5615243) B5615243
theorem B3997487 : Blo 1663031 3997487 := bstep (se 1 (by rfl) ⟨2998115, by rfl⟩ : syracuseStep 3997487 = 5996231) B5996231
theorem B3743783 : Blo 1663031 3743783 := bstep (se 1 (by rfl) ⟨2807837, by rfl⟩ : syracuseStep 3743783 = 5615675) B5615675
theorem B3743963 : Blo 1663031 3743963 := bstep (se 1 (by rfl) ⟨2807972, by rfl⟩ : syracuseStep 3743963 = 5615945) B5615945
theorem B1663207 : Blo 1663031 1663207 := bstep (se 1 (by rfl) ⟨1247405, by rfl⟩ : syracuseStep 1663207 = 2494811) B2494811
theorem B1663359 : Blo 1663031 1663359 := bstep (se 1 (by rfl) ⟨1247519, by rfl⟩ : syracuseStep 1663359 = 2495039) B2495039
theorem B1663439 : Blo 1663031 1663439 := bstep (se 1 (by rfl) ⟨1247579, by rfl⟩ : syracuseStep 1663439 = 2495159) B2495159
theorem B3744233 : Blo 1663031 3744233 := bstep (se 2 (by rfl) ⟨1404087, by rfl⟩ : syracuseStep 3744233 = 2808175) B2808175
theorem B1663591 : Blo 1663031 1663591 := bstep (se 1 (by rfl) ⟨1247693, by rfl⟩ : syracuseStep 1663591 = 2495387) B2495387
theorem B5333633 : Blo 1663031 5333633 := bstep (se 2 (by rfl) ⟨2000112, by rfl⟩ : syracuseStep 5333633 = 4000225) B4000225
theorem B45515479 : Blo 1663031 45515479 := bstep (se 1 (by rfl) ⟨34136609, by rfl⟩ : syracuseStep 45515479 = 68273219) B68273219
theorem B3744521 : Blo 1663031 3744521 := bstep (se 2 (by rfl) ⟨1404195, by rfl⟩ : syracuseStep 3744521 = 2808391) B2808391
theorem B1663855 : Blo 1663031 1663855 := bstep (se 1 (by rfl) ⟨1247891, by rfl⟩ : syracuseStep 1663855 = 2495783) B2495783
theorem B1663911 : Blo 1663031 1663911 := bstep (se 1 (by rfl) ⟨1247933, by rfl⟩ : syracuseStep 1663911 = 2495867) B2495867
theorem B45564839 : Blo 1663031 45564839 := bstep (se 1 (by rfl) ⟨34173629, by rfl⟩ : syracuseStep 45564839 = 68347259) B68347259
theorem B1663995 : Blo 1663031 1663995 := bstep (se 1 (by rfl) ⟨1247996, by rfl⟩ : syracuseStep 1663995 = 2495993) B2495993
theorem B1664063 : Blo 1663031 1664063 := bstep (se 1 (by rfl) ⟨1248047, by rfl⟩ : syracuseStep 1664063 = 2496095) B2496095
theorem B1664207 : Blo 1663031 1664207 := bstep (se 1 (by rfl) ⟨1248155, by rfl⟩ : syracuseStep 1664207 = 2496311) B2496311
theorem B3745097 : Blo 1663031 3745097 := bstep (se 2 (by rfl) ⟨1404411, by rfl⟩ : syracuseStep 3745097 = 2808823) B2808823
theorem B1664411 : Blo 1663031 1664411 := bstep (se 1 (by rfl) ⟨1248308, by rfl⟩ : syracuseStep 1664411 = 2496617) B2496617
theorem B5612975 : Blo 1663031 5612975 := bstep (se 1 (by rfl) ⟨4209731, by rfl⟩ : syracuseStep 5612975 = 8419463) B8419463
theorem B18949625 : Blo 1663031 18949625 := bstep (se 2 (by rfl) ⟨7106109, by rfl⟩ : syracuseStep 18949625 = 14212219) B14212219
theorem B1664623 : Blo 1663031 1664623 := bstep (se 1 (by rfl) ⟨1248467, by rfl⟩ : syracuseStep 1664623 = 2496935) B2496935
theorem B8423027 : Blo 1663031 8423027 := bstep (se 1 (by rfl) ⟨6317270, by rfl⟩ : syracuseStep 8423027 = 12634541) B12634541
theorem B31975033 : Blo 1663031 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B13493881 : Blo 1663031 13493881 := bstep (se 2 (by rfl) ⟨5060205, by rfl⟩ : syracuseStep 13493881 = 10120411) B10120411
theorem B1664679 : Blo 1663031 1664679 := bstep (se 1 (by rfl) ⟨1248509, by rfl⟩ : syracuseStep 1664679 = 2497019) B2497019
theorem B1664763 : Blo 1663031 1664763 := bstep (se 1 (by rfl) ⟨1248572, by rfl⟩ : syracuseStep 1664763 = 2497145) B2497145
theorem B1664799 : Blo 1663031 1664799 := bstep (se 1 (by rfl) ⟨1248599, by rfl⟩ : syracuseStep 1664799 = 2497199) B2497199
theorem B5613353 : Blo 1663031 5613353 := bstep (se 2 (by rfl) ⟨2105007, by rfl⟩ : syracuseStep 5613353 = 4210015) B4210015
theorem B1664831 : Blo 1663031 1664831 := bstep (se 1 (by rfl) ⟨1248623, by rfl⟩ : syracuseStep 1664831 = 2497247) B2497247
theorem B51914627 : Blo 1663031 51914627 := bstep (se 1 (by rfl) ⟨38935970, by rfl⟩ : syracuseStep 51914627 = 77871941) B77871941
theorem B1665007 : Blo 1663031 1665007 := bstep (se 1 (by rfl) ⟨1248755, by rfl⟩ : syracuseStep 1665007 = 2497511) B2497511
theorem B3794935 : Blo 1663031 3794935 := bstep (se 1 (by rfl) ⟨2846201, by rfl⟩ : syracuseStep 3794935 = 5692403) B5692403
theorem B7997449 : Blo 1663031 7997449 := bstep (se 2 (by rfl) ⟨2999043, by rfl⟩ : syracuseStep 7997449 = 5998087) B5998087
theorem B10119293 : Blo 1663031 10119293 := bstep (se 3 (by rfl) ⟨1897367, by rfl⟩ : syracuseStep 10119293 = 3794735) B3794735
theorem B3746087 : Blo 1663031 3746087 := bstep (se 1 (by rfl) ⟨2809565, by rfl⟩ : syracuseStep 3746087 = 5619131) B5619131
theorem B3746105 : Blo 1663031 3746105 := bstep (se 2 (by rfl) ⟨1404789, by rfl⟩ : syracuseStep 3746105 = 2809579) B2809579
theorem B11700571 : Blo 1663031 11700571 := bstep (se 1 (by rfl) ⟨8775428, by rfl⟩ : syracuseStep 11700571 = 17550857) B17550857
theorem B11381087 : Blo 1663031 11381087 := bstep (se 1 (by rfl) ⟨8535815, by rfl⟩ : syracuseStep 11381087 = 17071631) B17071631
theorem B8423837 : Blo 1663031 8423837 := bstep (se 3 (by rfl) ⟨1579469, by rfl⟩ : syracuseStep 8423837 = 3158939) B3158939
theorem B6318593 : Blo 1663031 6318593 := bstep (se 2 (by rfl) ⟨2369472, by rfl⟩ : syracuseStep 6318593 = 4738945) B4738945
theorem B4213255 : Blo 1663031 4213255 := bstep (se 1 (by rfl) ⟨3159941, by rfl⟩ : syracuseStep 4213255 = 6319883) B6319883
theorem B2664991 : Blo 1663031 2664991 := bstep (se 1 (by rfl) ⟨1998743, by rfl⟩ : syracuseStep 2664991 = 3997487) B3997487
theorem B5401259 : Blo 1663031 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B9472787 : Blo 1663031 9472787 := bstep (se 1 (by rfl) ⟨7104590, by rfl⟩ : syracuseStep 9472787 = 14209181) B14209181
theorem B5057335 : Blo 1663031 5057335 := bstep (se 1 (by rfl) ⟨3793001, by rfl⟩ : syracuseStep 5057335 = 7586003) B7586003
theorem B4213559 : Blo 1663031 4213559 := bstep (se 1 (by rfl) ⟨3160169, by rfl⟩ : syracuseStep 4213559 = 6320339) B6320339
theorem B7588703 : Blo 1663031 7588703 := bstep (se 1 (by rfl) ⟨5691527, by rfl⟩ : syracuseStep 7588703 = 11383055) B11383055
theorem B14208119 : Blo 1663031 14208119 := bstep (se 1 (by rfl) ⟨10656089, by rfl⟩ : syracuseStep 14208119 = 21312179) B21312179
theorem B8424647 : Blo 1663031 8424647 := bstep (se 1 (by rfl) ⟨6318485, by rfl⟩ : syracuseStep 8424647 = 12636971) B12636971
theorem B7105769 : Blo 1663031 7105769 := bstep (se 2 (by rfl) ⟨2664663, by rfl⟩ : syracuseStep 7105769 = 5329327) B5329327
theorem B19221791 : Blo 1663031 19221791 := bstep (se 1 (by rfl) ⟨14416343, by rfl⟩ : syracuseStep 19221791 = 28832687) B28832687
theorem B5328251 : Blo 1663031 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B47984237 : Blo 1663031 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B3157679 : Blo 1663031 3157679 := bstep (se 1 (by rfl) ⟨2368259, by rfl⟩ : syracuseStep 3157679 = 4736519) B4736519
theorem B13496219 : Blo 1663031 13496219 := bstep (se 1 (by rfl) ⟨10122164, by rfl⟩ : syracuseStep 13496219 = 20244329) B20244329
theorem B10661807 : Blo 1663031 10661807 := bstep (se 1 (by rfl) ⟨7996355, by rfl⟩ : syracuseStep 10661807 = 15992711) B15992711
theorem B5615567 : Blo 1663031 5615567 := bstep (se 1 (by rfl) ⟨4211675, by rfl⟩ : syracuseStep 5615567 = 8423351) B8423351
theorem B3158203 : Blo 1663031 3158203 := bstep (se 1 (by rfl) ⟨2368652, by rfl⟩ : syracuseStep 3158203 = 4737305) B4737305
theorem B1872103 : Blo 1663031 1872103 := bstep (se 1 (by rfl) ⟨1404077, by rfl⟩ : syracuseStep 1872103 = 2808155) B2808155
theorem B2494751 : Blo 1663031 2494751 := bstep (se 1 (by rfl) ⟨1871063, by rfl⟩ : syracuseStep 2494751 = 3742127) B3742127
theorem B21319969 : Blo 1663031 21319969 := bstep (se 2 (by rfl) ⟨7994988, by rfl⟩ : syracuseStep 21319969 = 15989977) B15989977
theorem B2494775 : Blo 1663031 2494775 := bstep (se 1 (by rfl) ⟨1871081, by rfl⟩ : syracuseStep 2494775 = 3742163) B3742163
theorem B2494847 : Blo 1663031 2494847 := bstep (se 1 (by rfl) ⟨1871135, by rfl⟩ : syracuseStep 2494847 = 3742271) B3742271
theorem B5615999 : Blo 1663031 5615999 := bstep (se 1 (by rfl) ⟨4211999, by rfl⟩ : syracuseStep 5615999 = 8423999) B8423999
theorem B6320551 : Blo 1663031 6320551 := bstep (se 1 (by rfl) ⟨4740413, by rfl⟩ : syracuseStep 6320551 = 9480827) B9480827
theorem B2494919 : Blo 1663031 2494919 := bstep (se 1 (by rfl) ⟨1871189, by rfl⟩ : syracuseStep 2494919 = 3742379) B3742379
theorem B5059027 : Blo 1663031 5059027 := bstep (se 1 (by rfl) ⟨3794270, by rfl⟩ : syracuseStep 5059027 = 7588541) B7588541
theorem B8425943 : Blo 1663031 8425943 := bstep (se 1 (by rfl) ⟨6319457, by rfl⟩ : syracuseStep 8425943 = 12638915) B12638915
theorem B11997791 : Blo 1663031 11997791 := bstep (se 1 (by rfl) ⟨8998343, by rfl⟩ : syracuseStep 11997791 = 17996687) B17996687
theorem B3158689 : Blo 1663031 3158689 := bstep (se 2 (by rfl) ⟨1184508, by rfl⟩ : syracuseStep 3158689 = 2369017) B2369017
theorem B2806535 : Blo 1663031 2806535 := bstep (se 1 (by rfl) ⟨2104901, by rfl⟩ : syracuseStep 2806535 = 4209803) B4209803
theorem B2495273 : Blo 1663031 2495273 := bstep (se 2 (by rfl) ⟨935727, by rfl⟩ : syracuseStep 2495273 = 1871455) B1871455
theorem B2495279 : Blo 1663031 2495279 := bstep (se 1 (by rfl) ⟨1871459, by rfl⟩ : syracuseStep 2495279 = 3742919) B3742919
theorem B11998019 : Blo 1663031 11998019 := bstep (se 1 (by rfl) ⟨8998514, by rfl⟩ : syracuseStep 11998019 = 17997029) B17997029
theorem B1872751 : Blo 1663031 1872751 := bstep (se 1 (by rfl) ⟨1404563, by rfl⟩ : syracuseStep 1872751 = 2809127) B2809127
theorem B2495399 : Blo 1663031 2495399 := bstep (se 1 (by rfl) ⟨1871549, by rfl⟩ : syracuseStep 2495399 = 3743099) B3743099
theorem B153752525 : Blo 1663031 153752525 := bstep (se 3 (by rfl) ⟨28828598, by rfl⟩ : syracuseStep 153752525 = 57657197) B57657197
theorem B2495483 : Blo 1663031 2495483 := bstep (se 1 (by rfl) ⟨1871612, by rfl⟩ : syracuseStep 2495483 = 3743225) B3743225
theorem B2495543 : Blo 1663031 2495543 := bstep (se 1 (by rfl) ⟨1871657, by rfl⟩ : syracuseStep 2495543 = 3743315) B3743315
theorem B2495663 : Blo 1663031 2495663 := bstep (se 1 (by rfl) ⟨1871747, by rfl⟩ : syracuseStep 2495663 = 3743495) B3743495
theorem B20510081 : Blo 1663031 20510081 := bstep (se 2 (by rfl) ⟨7691280, by rfl⟩ : syracuseStep 20510081 = 15382561) B15382561
theorem B4740551 : Blo 1663031 4740551 := bstep (se 1 (by rfl) ⟨3555413, by rfl⟩ : syracuseStep 4740551 = 7110827) B7110827
theorem B2496071 : Blo 1663031 2496071 := bstep (se 1 (by rfl) ⟨1872053, by rfl⟩ : syracuseStep 2496071 = 3744107) B3744107
theorem B3159623 : Blo 1663031 3159623 := bstep (se 1 (by rfl) ⟨2369717, by rfl⟩ : syracuseStep 3159623 = 4739435) B4739435
theorem B2496167 : Blo 1663031 2496167 := bstep (se 1 (by rfl) ⟨1872125, by rfl⟩ : syracuseStep 2496167 = 3744251) B3744251
theorem B2496251 : Blo 1663031 2496251 := bstep (se 1 (by rfl) ⟨1872188, by rfl⟩ : syracuseStep 2496251 = 3744377) B3744377
theorem B5617403 : Blo 1663031 5617403 := bstep (se 1 (by rfl) ⟨4213052, by rfl⟩ : syracuseStep 5617403 = 8426105) B8426105
theorem B2496287 : Blo 1663031 2496287 := bstep (se 1 (by rfl) ⟨1872215, by rfl⟩ : syracuseStep 2496287 = 3744431) B3744431
theorem B2807615 : Blo 1663031 2807615 := bstep (se 1 (by rfl) ⟨2105711, by rfl⟩ : syracuseStep 2807615 = 4211423) B4211423
theorem B2496335 : Blo 1663031 2496335 := bstep (se 1 (by rfl) ⟨1872251, by rfl⟩ : syracuseStep 2496335 = 3744503) B3744503
theorem B2807689 : Blo 1663031 2807689 := bstep (se 2 (by rfl) ⟨1052883, by rfl⟩ : syracuseStep 2807689 = 2105767) B2105767
theorem B5617565 : Blo 1663031 5617565 := bstep (se 3 (by rfl) ⟨1053293, by rfl⟩ : syracuseStep 5617565 = 2106587) B2106587
theorem B2496455 : Blo 1663031 2496455 := bstep (se 1 (by rfl) ⟨1872341, by rfl⟩ : syracuseStep 2496455 = 3744683) B3744683
theorem B3160147 : Blo 1663031 3160147 := bstep (se 1 (by rfl) ⟨2370110, by rfl⟩ : syracuseStep 3160147 = 4740221) B4740221
theorem B3741839 : Blo 1663031 3741839 := bstep (se 1 (by rfl) ⟨2806379, by rfl⟩ : syracuseStep 3741839 = 5612759) B5612759
theorem B4110479 : Blo 1663031 4110479 := bstep (se 1 (by rfl) ⟨3082859, by rfl⟩ : syracuseStep 4110479 = 6165719) B6165719
theorem B3741857 : Blo 1663031 3741857 := bstep (se 2 (by rfl) ⟨1403196, by rfl⟩ : syracuseStep 3741857 = 2806393) B2806393
theorem B3741929 : Blo 1663031 3741929 := bstep (se 2 (by rfl) ⟨1403223, by rfl⟩ : syracuseStep 3741929 = 2806447) B2806447
theorem B2496809 : Blo 1663031 2496809 := bstep (se 2 (by rfl) ⟨936303, by rfl⟩ : syracuseStep 2496809 = 1872607) B1872607
theorem B2496815 : Blo 1663031 2496815 := bstep (se 1 (by rfl) ⟨1872611, by rfl⟩ : syracuseStep 2496815 = 3745223) B3745223
theorem B2808121 : Blo 1663031 2808121 := bstep (se 2 (by rfl) ⟨1053045, by rfl⟩ : syracuseStep 2808121 = 2106091) B2106091
theorem B10656143 : Blo 1663031 10656143 := bstep (se 1 (by rfl) ⟨7992107, by rfl⟩ : syracuseStep 10656143 = 15984215) B15984215
theorem B2497055 : Blo 1663031 2497055 := bstep (se 1 (by rfl) ⟨1872791, by rfl⟩ : syracuseStep 2497055 = 3745583) B3745583
theorem B2808425 : Blo 1663031 2808425 := bstep (se 2 (by rfl) ⟨1053159, by rfl⟩ : syracuseStep 2808425 = 2106319) B2106319
theorem B5618537 : Blo 1663031 5618537 := bstep (se 2 (by rfl) ⟨2106951, by rfl⟩ : syracuseStep 5618537 = 4213903) B4213903
theorem B5618591 : Blo 1663031 5618591 := bstep (se 1 (by rfl) ⟨4213943, by rfl⟩ : syracuseStep 5618591 = 8427887) B8427887
theorem B2497439 : Blo 1663031 2497439 := bstep (se 1 (by rfl) ⟨1873079, by rfl⟩ : syracuseStep 2497439 = 3746159) B3746159
theorem B10656683 : Blo 1663031 10656683 := bstep (se 1 (by rfl) ⟨7992512, by rfl⟩ : syracuseStep 10656683 = 15985025) B15985025
theorem B2497487 : Blo 1663031 2497487 := bstep (se 1 (by rfl) ⟨1873115, by rfl⟩ : syracuseStep 2497487 = 3746231) B3746231
theorem B3996641 : Blo 1663031 3996641 := bstep (se 2 (by rfl) ⟨1498740, by rfl⟩ : syracuseStep 3996641 = 2997481) B2997481
theorem B8428535 : Blo 1663031 8428535 := bstep (se 1 (by rfl) ⟨6321401, by rfl⟩ : syracuseStep 8428535 = 12642803) B12642803
theorem B2530487 : Blo 1663031 2530487 := bstep (se 1 (by rfl) ⟨1897865, by rfl⟩ : syracuseStep 2530487 = 3795731) B3795731
theorem B11992313 : Blo 1663031 11992313 := bstep (se 2 (by rfl) ⟨4497117, by rfl⟩ : syracuseStep 11992313 = 8994235) B8994235
theorem B31997177 : Blo 1663031 31997177 := bstep (se 2 (by rfl) ⟨11998941, by rfl⟩ : syracuseStep 31997177 = 23997883) B23997883
theorem B107978021 : Blo 1663031 107978021 := bstep (se 4 (by rfl) ⟨10122939, by rfl⟩ : syracuseStep 107978021 = 20245879) B20245879
theorem B2809255 : Blo 1663031 2809255 := bstep (se 1 (by rfl) ⟨2106941, by rfl⟩ : syracuseStep 2809255 = 4213883) B4213883
theorem B8994277 : Blo 1663031 8994277 := bstep (se 4 (by rfl) ⟨843213, by rfl⟩ : syracuseStep 8994277 = 1686427) B1686427
theorem B3743207 : Blo 1663031 3743207 := bstep (se 1 (by rfl) ⟨2807405, by rfl⟩ : syracuseStep 3743207 = 5614811) B5614811
theorem B2809417 : Blo 1663031 2809417 := bstep (se 2 (by rfl) ⟨1053531, by rfl⟩ : syracuseStep 2809417 = 2107063) B2107063
theorem B2809451 : Blo 1663031 2809451 := bstep (se 1 (by rfl) ⟨2107088, by rfl⟩ : syracuseStep 2809451 = 4214177) B4214177
theorem B4210319 : Blo 1663031 4210319 := bstep (se 1 (by rfl) ⟨3157739, by rfl⟩ : syracuseStep 4210319 = 6315479) B6315479
theorem B9477911 : Blo 1663031 9477911 := bstep (se 1 (by rfl) ⟨7108433, by rfl⟩ : syracuseStep 9477911 = 14216867) B14216867
theorem B2809721 : Blo 1663031 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B8421245 : Blo 1663031 8421245 := bstep (se 3 (by rfl) ⟨1578983, by rfl⟩ : syracuseStep 8421245 = 3157967) B3157967
theorem B6315965 : Blo 1663031 6315965 := bstep (se 3 (by rfl) ⟨1184243, by rfl⟩ : syracuseStep 6315965 = 2368487) B2368487
theorem B1663167 : Blo 1663031 1663167 := bstep (se 1 (by rfl) ⟨1247375, by rfl⟩ : syracuseStep 1663167 = 2494751) B2494751
theorem B1663183 : Blo 1663031 1663183 := bstep (se 1 (by rfl) ⟨1247387, by rfl⟩ : syracuseStep 1663183 = 2494775) B2494775
theorem B4210937 : Blo 1663031 4210937 := bstep (se 2 (by rfl) ⟨1579101, by rfl⟩ : syracuseStep 4210937 = 3158203) B3158203
theorem B1663231 : Blo 1663031 1663231 := bstep (se 1 (by rfl) ⟨1247423, by rfl⟩ : syracuseStep 1663231 = 2494847) B2494847
theorem B3743999 : Blo 1663031 3743999 := bstep (se 1 (by rfl) ⟨2807999, by rfl⟩ : syracuseStep 3743999 = 5615999) B5615999
theorem B1663279 : Blo 1663031 1663279 := bstep (se 1 (by rfl) ⟨1247459, by rfl⟩ : syracuseStep 1663279 = 2494919) B2494919
theorem B28426625 : Blo 1663031 28426625 := bstep (se 2 (by rfl) ⟨10659984, by rfl⟩ : syracuseStep 28426625 = 21319969) B21319969
theorem B3744161 : Blo 1663031 3744161 := bstep (se 2 (by rfl) ⟨1404060, by rfl⟩ : syracuseStep 3744161 = 2808121) B2808121
theorem B3555755 : Blo 1663031 3555755 := bstep (se 1 (by rfl) ⟨2666816, by rfl⟩ : syracuseStep 3555755 = 5333633) B5333633
theorem B1663515 : Blo 1663031 1663515 := bstep (se 1 (by rfl) ⟨1247636, by rfl⟩ : syracuseStep 1663515 = 2495273) B2495273
theorem B1663519 : Blo 1663031 1663519 := bstep (se 1 (by rfl) ⟨1247639, by rfl⟩ : syracuseStep 1663519 = 2495279) B2495279
theorem B1663599 : Blo 1663031 1663599 := bstep (se 1 (by rfl) ⟨1247699, by rfl⟩ : syracuseStep 1663599 = 2495399) B2495399
theorem B30376559 : Blo 1663031 30376559 := bstep (se 1 (by rfl) ⟨22782419, by rfl⟩ : syracuseStep 30376559 = 45564839) B45564839
theorem B1663655 : Blo 1663031 1663655 := bstep (se 1 (by rfl) ⟨1247741, by rfl⟩ : syracuseStep 1663655 = 2495483) B2495483
theorem B1663695 : Blo 1663031 1663695 := bstep (se 1 (by rfl) ⟨1247771, by rfl⟩ : syracuseStep 1663695 = 2495543) B2495543
theorem B51258109 : Blo 1663031 51258109 := bstep (se 3 (by rfl) ⟨9610895, by rfl⟩ : syracuseStep 51258109 = 19221791) B19221791
theorem B1663775 : Blo 1663031 1663775 := bstep (se 1 (by rfl) ⟨1247831, by rfl⟩ : syracuseStep 1663775 = 2495663) B2495663
theorem B4211585 : Blo 1663031 4211585 := bstep (se 2 (by rfl) ⟨1579344, by rfl⟩ : syracuseStep 4211585 = 3158689) B3158689
theorem B13673387 : Blo 1663031 13673387 := bstep (se 1 (by rfl) ⟨10255040, by rfl⟩ : syracuseStep 13673387 = 20510081) B20510081
theorem B60687305 : Blo 1663031 60687305 := bstep (se 2 (by rfl) ⟨22757739, by rfl⟩ : syracuseStep 60687305 = 45515479) B45515479
theorem B12633083 : Blo 1663031 12633083 := bstep (se 1 (by rfl) ⟨9474812, by rfl⟩ : syracuseStep 12633083 = 18949625) B18949625
theorem B1664047 : Blo 1663031 1664047 := bstep (se 1 (by rfl) ⟨1248035, by rfl⟩ : syracuseStep 1664047 = 2496071) B2496071
theorem B2106415 : Blo 1663031 2106415 := bstep (se 1 (by rfl) ⟨1579811, by rfl⟩ : syracuseStep 2106415 = 3159623) B3159623
theorem B1664111 : Blo 1663031 1664111 := bstep (se 1 (by rfl) ⟨1248083, by rfl⟩ : syracuseStep 1664111 = 2496167) B2496167
theorem B1664167 : Blo 1663031 1664167 := bstep (se 1 (by rfl) ⟨1248125, by rfl⟩ : syracuseStep 1664167 = 2496251) B2496251
theorem B3744935 : Blo 1663031 3744935 := bstep (se 1 (by rfl) ⟨2808701, by rfl⟩ : syracuseStep 3744935 = 5617403) B5617403
theorem B1664191 : Blo 1663031 1664191 := bstep (se 1 (by rfl) ⟨1248143, by rfl⟩ : syracuseStep 1664191 = 2496287) B2496287
theorem B1664223 : Blo 1663031 1664223 := bstep (se 1 (by rfl) ⟨1248167, by rfl⟩ : syracuseStep 1664223 = 2496335) B2496335
theorem B3745043 : Blo 1663031 3745043 := bstep (se 1 (by rfl) ⟨2808782, by rfl⟩ : syracuseStep 3745043 = 5617565) B5617565
theorem B1664303 : Blo 1663031 1664303 := bstep (se 1 (by rfl) ⟨1248227, by rfl⟩ : syracuseStep 1664303 = 2496455) B2496455
theorem B1664539 : Blo 1663031 1664539 := bstep (se 1 (by rfl) ⟨1248404, by rfl⟩ : syracuseStep 1664539 = 2496809) B2496809
theorem B1664543 : Blo 1663031 1664543 := bstep (se 1 (by rfl) ⟨1248407, by rfl⟩ : syracuseStep 1664543 = 2496815) B2496815
theorem B7587391 : Blo 1663031 7587391 := bstep (se 1 (by rfl) ⟨5690543, by rfl⟩ : syracuseStep 7587391 = 11381087) B11381087
theorem B7104095 : Blo 1663031 7104095 := bstep (se 1 (by rfl) ⟨5328071, by rfl⟩ : syracuseStep 7104095 = 10656143) B10656143
theorem B4212395 : Blo 1663031 4212395 := bstep (se 1 (by rfl) ⟨3159296, by rfl⟩ : syracuseStep 4212395 = 6318593) B6318593
theorem B1664703 : Blo 1663031 1664703 := bstep (se 1 (by rfl) ⟨1248527, by rfl⟩ : syracuseStep 1664703 = 2497055) B2497055
theorem B3745673 : Blo 1663031 3745673 := bstep (se 2 (by rfl) ⟨1404627, by rfl⟩ : syracuseStep 3745673 = 2809255) B2809255
theorem B3745691 : Blo 1663031 3745691 := bstep (se 1 (by rfl) ⟨2809268, by rfl⟩ : syracuseStep 3745691 = 5618537) B5618537
theorem B3745727 : Blo 1663031 3745727 := bstep (se 1 (by rfl) ⟨2809295, by rfl⟩ : syracuseStep 3745727 = 5618591) B5618591
theorem B1664959 : Blo 1663031 1664959 := bstep (se 1 (by rfl) ⟨1248719, by rfl⟩ : syracuseStep 1664959 = 2497439) B2497439
theorem B7104455 : Blo 1663031 7104455 := bstep (se 1 (by rfl) ⟨5328341, by rfl⟩ : syracuseStep 7104455 = 10656683) B10656683
theorem B1664991 : Blo 1663031 1664991 := bstep (se 1 (by rfl) ⟨1248743, by rfl⟩ : syracuseStep 1664991 = 2497487) B2497487
theorem B2664427 : Blo 1663031 2664427 := bstep (se 1 (by rfl) ⟨1998320, by rfl⟩ : syracuseStep 2664427 = 3996641) B3996641
theorem B9472079 : Blo 1663031 9472079 := bstep (se 1 (by rfl) ⟨7104059, by rfl⟩ : syracuseStep 9472079 = 14208119) B14208119
theorem B3745889 : Blo 1663031 3745889 := bstep (se 2 (by rfl) ⟨1404708, by rfl⟩ : syracuseStep 3745889 = 2809417) B2809417
theorem B4737179 : Blo 1663031 4737179 := bstep (se 1 (by rfl) ⟨3552884, by rfl⟩ : syracuseStep 4737179 = 7105769) B7105769
theorem B42633377 : Blo 1663031 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B17991841 : Blo 1663031 17991841 := bstep (se 2 (by rfl) ⟨6746940, by rfl⟩ : syracuseStep 17991841 = 13493881) B13493881
theorem B71985347 : Blo 1663031 71985347 := bstep (se 1 (by rfl) ⟨53989010, by rfl⟩ : syracuseStep 71985347 = 107978021) B107978021
theorem B6318607 : Blo 1663031 6318607 := bstep (se 1 (by rfl) ⟨4738955, by rfl⟩ : syracuseStep 6318607 = 9477911) B9477911
theorem B5614163 : Blo 1663031 5614163 := bstep (se 1 (by rfl) ⟨4210622, by rfl⟩ : syracuseStep 5614163 = 8421245) B8421245
theorem B8997479 : Blo 1663031 8997479 := bstep (se 1 (by rfl) ⟨6748109, by rfl⟩ : syracuseStep 8997479 = 13496219) B13496219
theorem B4213529 : Blo 1663031 4213529 := bstep (se 2 (by rfl) ⟨1580073, by rfl⟩ : syracuseStep 4213529 = 3160147) B3160147
theorem B7998527 : Blo 1663031 7998527 := bstep (se 1 (by rfl) ⟨5998895, by rfl⟩ : syracuseStep 7998527 = 11997791) B11997791
theorem B15600761 : Blo 1663031 15600761 := bstep (se 2 (by rfl) ⟨5850285, by rfl⟩ : syracuseStep 15600761 = 11700571) B11700571
theorem B1871023 : Blo 1663031 1871023 := bstep (se 1 (by rfl) ⟨1403267, by rfl⟩ : syracuseStep 1871023 = 2806535) B2806535
theorem B7998679 : Blo 1663031 7998679 := bstep (se 1 (by rfl) ⟨5999009, by rfl⟩ : syracuseStep 7998679 = 11998019) B11998019
theorem B6745369 : Blo 1663031 6745369 := bstep (se 2 (by rfl) ⟨2529513, by rfl⟩ : syracuseStep 6745369 = 5059027) B5059027
theorem B102501683 : Blo 1663031 102501683 := bstep (se 1 (by rfl) ⟨76876262, by rfl⟩ : syracuseStep 102501683 = 153752525) B153752525
theorem B5615351 : Blo 1663031 5615351 := bstep (se 1 (by rfl) ⟨4211513, by rfl⟩ : syracuseStep 5615351 = 8423027) B8423027
theorem B1871743 : Blo 1663031 1871743 := bstep (se 1 (by rfl) ⟨1403807, by rfl⟩ : syracuseStep 1871743 = 2807615) B2807615
theorem B6746195 : Blo 1663031 6746195 := bstep (se 1 (by rfl) ⟨5059646, by rfl⟩ : syracuseStep 6746195 = 10119293) B10119293
theorem B2494559 : Blo 1663031 2494559 := bstep (se 1 (by rfl) ⟨1870919, by rfl⟩ : syracuseStep 2494559 = 3741839) B3741839
theorem B2740319 : Blo 1663031 2740319 := bstep (se 1 (by rfl) ⟨2055239, by rfl⟩ : syracuseStep 2740319 = 4110479) B4110479
theorem B2494571 : Blo 1663031 2494571 := bstep (se 1 (by rfl) ⟨1870928, by rfl⟩ : syracuseStep 2494571 = 3741857) B3741857
theorem B2494619 : Blo 1663031 2494619 := bstep (se 1 (by rfl) ⟨1870964, by rfl⟩ : syracuseStep 2494619 = 3741929) B3741929
theorem B5615891 : Blo 1663031 5615891 := bstep (se 1 (by rfl) ⟨4211918, by rfl⟩ : syracuseStep 5615891 = 8423837) B8423837
theorem B26972453 : Blo 1663031 26972453 := bstep (se 4 (by rfl) ⟨2528667, by rfl⟩ : syracuseStep 26972453 = 5057335) B5057335
theorem B1872283 : Blo 1663031 1872283 := bstep (se 1 (by rfl) ⟨1404212, by rfl⟩ : syracuseStep 1872283 = 2808425) B2808425
theorem B3600839 : Blo 1663031 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B5059135 : Blo 1663031 5059135 := bstep (se 1 (by rfl) ⟨3794351, by rfl⟩ : syracuseStep 5059135 = 7588703) B7588703
theorem B5616431 : Blo 1663031 5616431 := bstep (se 1 (by rfl) ⟨4212323, by rfl⟩ : syracuseStep 5616431 = 8424647) B8424647
theorem B3552167 : Blo 1663031 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B2495471 : Blo 1663031 2495471 := bstep (se 1 (by rfl) ⟨1871603, by rfl⟩ : syracuseStep 2495471 = 3743207) B3743207
theorem B1872967 : Blo 1663031 1872967 := bstep (se 1 (by rfl) ⟨1404725, by rfl⟩ : syracuseStep 1872967 = 2809451) B2809451
theorem B2806879 : Blo 1663031 2806879 := bstep (se 1 (by rfl) ⟨2105159, by rfl⟩ : syracuseStep 2806879 = 4210319) B4210319
theorem B1873147 : Blo 1663031 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B7107871 : Blo 1663031 7107871 := bstep (se 1 (by rfl) ⟨5330903, by rfl⟩ : syracuseStep 7107871 = 10661807) B10661807
theorem B5059913 : Blo 1663031 5059913 := bstep (se 2 (by rfl) ⟨1897467, by rfl⟩ : syracuseStep 5059913 = 3794935) B3794935
theorem B10663265 : Blo 1663031 10663265 := bstep (se 2 (by rfl) ⟨3998724, by rfl⟩ : syracuseStep 10663265 = 7997449) B7997449
theorem B2495855 : Blo 1663031 2495855 := bstep (se 1 (by rfl) ⟨1871891, by rfl⟩ : syracuseStep 2495855 = 3743783) B3743783
theorem B2495975 : Blo 1663031 2495975 := bstep (se 1 (by rfl) ⟨1871981, by rfl⟩ : syracuseStep 2495975 = 3743963) B3743963
theorem B2496137 : Blo 1663031 2496137 := bstep (se 2 (by rfl) ⟨936051, by rfl⟩ : syracuseStep 2496137 = 1872103) B1872103
theorem B5617295 : Blo 1663031 5617295 := bstep (se 1 (by rfl) ⟨4212971, by rfl⟩ : syracuseStep 5617295 = 8425943) B8425943
theorem B2496155 : Blo 1663031 2496155 := bstep (se 1 (by rfl) ⟨1872116, by rfl⟩ : syracuseStep 2496155 = 3744233) B3744233
theorem B2496347 : Blo 1663031 2496347 := bstep (se 1 (by rfl) ⟨1872260, by rfl⟩ : syracuseStep 2496347 = 3744521) B3744521
theorem B8427401 : Blo 1663031 8427401 := bstep (se 2 (by rfl) ⟨3160275, by rfl⟩ : syracuseStep 8427401 = 6320551) B6320551
theorem B5617673 : Blo 1663031 5617673 := bstep (se 2 (by rfl) ⟨2106627, by rfl⟩ : syracuseStep 5617673 = 4213255) B4213255
theorem B3553321 : Blo 1663031 3553321 := bstep (se 2 (by rfl) ⟨1332495, by rfl⟩ : syracuseStep 3553321 = 2664991) B2664991
theorem B2496731 : Blo 1663031 2496731 := bstep (se 1 (by rfl) ⟨1872548, by rfl⟩ : syracuseStep 2496731 = 3745097) B3745097
theorem B3741983 : Blo 1663031 3741983 := bstep (se 1 (by rfl) ⟨2806487, by rfl⟩ : syracuseStep 3741983 = 5612975) B5612975
theorem B3160367 : Blo 1663031 3160367 := bstep (se 1 (by rfl) ⟨2370275, by rfl⟩ : syracuseStep 3160367 = 4740551) B4740551
theorem B2497001 : Blo 1663031 2497001 := bstep (se 2 (by rfl) ⟨936375, by rfl⟩ : syracuseStep 2497001 = 1872751) B1872751
theorem B3742235 : Blo 1663031 3742235 := bstep (se 1 (by rfl) ⟨2806676, by rfl⟩ : syracuseStep 3742235 = 5613353) B5613353
theorem B34609751 : Blo 1663031 34609751 := bstep (se 1 (by rfl) ⟨25957313, by rfl⟩ : syracuseStep 34609751 = 51914627) B51914627
theorem B2497391 : Blo 1663031 2497391 := bstep (se 1 (by rfl) ⟨1873043, by rfl⟩ : syracuseStep 2497391 = 3746087) B3746087
theorem B2497403 : Blo 1663031 2497403 := bstep (se 1 (by rfl) ⟨1873052, by rfl⟩ : syracuseStep 2497403 = 3746105) B3746105
theorem B6315191 : Blo 1663031 6315191 := bstep (se 1 (by rfl) ⟨4736393, by rfl⟩ : syracuseStep 6315191 = 9472787) B9472787
theorem B2809039 : Blo 1663031 2809039 := bstep (se 1 (by rfl) ⟨2106779, by rfl⟩ : syracuseStep 2809039 = 4213559) B4213559
theorem B11992369 : Blo 1663031 11992369 := bstep (se 2 (by rfl) ⟨4497138, by rfl⟩ : syracuseStep 11992369 = 8994277) B8994277
theorem B5619023 : Blo 1663031 5619023 := bstep (se 1 (by rfl) ⟨4214267, by rfl⟩ : syracuseStep 5619023 = 8428535) B8428535
theorem B1686991 : Blo 1663031 1686991 := bstep (se 1 (by rfl) ⟨1265243, by rfl⟩ : syracuseStep 1686991 = 2530487) B2530487
theorem B7994875 : Blo 1663031 7994875 := bstep (se 1 (by rfl) ⟨5996156, by rfl⟩ : syracuseStep 7994875 = 11992313) B11992313
theorem B21331451 : Blo 1663031 21331451 := bstep (se 1 (by rfl) ⟨15998588, by rfl⟩ : syracuseStep 21331451 = 31997177) B31997177
theorem B31989491 : Blo 1663031 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B2105119 : Blo 1663031 2105119 := bstep (se 1 (by rfl) ⟨1578839, by rfl⟩ : syracuseStep 2105119 = 3157679) B3157679
theorem B3743585 : Blo 1663031 3743585 := bstep (se 2 (by rfl) ⟨1403844, by rfl⟩ : syracuseStep 3743585 = 2807689) B2807689
theorem B4210643 : Blo 1663031 4210643 := bstep (se 1 (by rfl) ⟨3157982, by rfl⟩ : syracuseStep 4210643 = 6315965) B6315965
theorem B3743711 : Blo 1663031 3743711 := bstep (se 1 (by rfl) ⟨2807783, by rfl⟩ : syracuseStep 3743711 = 5615567) B5615567
theorem B4497463 : Blo 1663031 4497463 := bstep (se 1 (by rfl) ⟨3373097, by rfl⟩ : syracuseStep 4497463 = 6746195) B6746195
theorem B1663039 : Blo 1663031 1663039 := bstep (se 1 (by rfl) ⟨1247279, by rfl⟩ : syracuseStep 1663039 = 2494559) B2494559
theorem B1826879 : Blo 1663031 1826879 := bstep (se 1 (by rfl) ⟨1370159, by rfl⟩ : syracuseStep 1826879 = 2740319) B2740319
theorem B1663047 : Blo 1663031 1663047 := bstep (se 1 (by rfl) ⟨1247285, by rfl⟩ : syracuseStep 1663047 = 2494571) B2494571
theorem B1663079 : Blo 1663031 1663079 := bstep (se 1 (by rfl) ⟨1247309, by rfl⟩ : syracuseStep 1663079 = 2494619) B2494619
theorem B3743927 : Blo 1663031 3743927 := bstep (se 1 (by rfl) ⟨2807945, by rfl⟩ : syracuseStep 3743927 = 5615891) B5615891
theorem B17981635 : Blo 1663031 17981635 := bstep (se 1 (by rfl) ⟨13486226, by rfl⟩ : syracuseStep 17981635 = 26972453) B26972453
theorem B2400559 : Blo 1663031 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B3744287 : Blo 1663031 3744287 := bstep (se 1 (by rfl) ⟨2808215, by rfl⟩ : syracuseStep 3744287 = 5616431) B5616431
theorem B2368111 : Blo 1663031 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B1663647 : Blo 1663031 1663647 := bstep (se 1 (by rfl) ⟨1247735, by rfl⟩ : syracuseStep 1663647 = 2495471) B2495471
theorem B8422055 : Blo 1663031 8422055 := bstep (se 1 (by rfl) ⟨6316541, by rfl⟩ : syracuseStep 8422055 = 12633083) B12633083
theorem B1663903 : Blo 1663031 1663903 := bstep (se 1 (by rfl) ⟨1247927, by rfl⟩ : syracuseStep 1663903 = 2495855) B2495855
theorem B28435373 : Blo 1663031 28435373 := bstep (se 3 (by rfl) ⟨5331632, by rfl⟩ : syracuseStep 28435373 = 10663265) B10663265
theorem B1663983 : Blo 1663031 1663983 := bstep (se 1 (by rfl) ⟨1247987, by rfl⟩ : syracuseStep 1663983 = 2495975) B2495975
theorem B4736063 : Blo 1663031 4736063 := bstep (se 1 (by rfl) ⟨3552047, by rfl⟩ : syracuseStep 4736063 = 7104095) B7104095
theorem B1664091 : Blo 1663031 1664091 := bstep (se 1 (by rfl) ⟨1248068, by rfl⟩ : syracuseStep 1664091 = 2496137) B2496137
theorem B3744863 : Blo 1663031 3744863 := bstep (se 1 (by rfl) ⟨2808647, by rfl⟩ : syracuseStep 3744863 = 5617295) B5617295
theorem B1664103 : Blo 1663031 1664103 := bstep (se 1 (by rfl) ⟨1248077, by rfl⟩ : syracuseStep 1664103 = 2496155) B2496155
theorem B1664231 : Blo 1663031 1664231 := bstep (se 1 (by rfl) ⟨1248173, by rfl⟩ : syracuseStep 1664231 = 2496347) B2496347
theorem B4736303 : Blo 1663031 4736303 := bstep (se 1 (by rfl) ⟨3552227, by rfl⟩ : syracuseStep 4736303 = 7104455) B7104455
theorem B3745115 : Blo 1663031 3745115 := bstep (se 1 (by rfl) ⟨2808836, by rfl⟩ : syracuseStep 3745115 = 5617673) B5617673
theorem B47990231 : Blo 1663031 47990231 := bstep (se 1 (by rfl) ⟨35992673, by rfl⟩ : syracuseStep 47990231 = 71985347) B71985347
theorem B1664487 : Blo 1663031 1664487 := bstep (se 1 (by rfl) ⟨1248365, by rfl⟩ : syracuseStep 1664487 = 2496731) B2496731
theorem B2106911 : Blo 1663031 2106911 := bstep (se 1 (by rfl) ⟨1580183, by rfl⟩ : syracuseStep 2106911 = 3160367) B3160367
theorem B3745385 : Blo 1663031 3745385 := bstep (se 2 (by rfl) ⟨1404519, by rfl⟩ : syracuseStep 3745385 = 2809039) B2809039
theorem B81004157 : Blo 1663031 81004157 := bstep (se 3 (by rfl) ⟨15188279, by rfl⟩ : syracuseStep 81004157 = 30376559) B30376559
theorem B1664667 : Blo 1663031 1664667 := bstep (se 1 (by rfl) ⟨1248500, by rfl⟩ : syracuseStep 1664667 = 2497001) B2497001
theorem B5998319 : Blo 1663031 5998319 := bstep (se 1 (by rfl) ⟨4498739, by rfl⟩ : syracuseStep 5998319 = 8997479) B8997479
theorem B1664927 : Blo 1663031 1664927 := bstep (se 1 (by rfl) ⟨1248695, by rfl⟩ : syracuseStep 1664927 = 2497391) B2497391
theorem B1664935 : Blo 1663031 1664935 := bstep (se 1 (by rfl) ⟨1248701, by rfl⟩ : syracuseStep 1664935 = 2497403) B2497403
theorem B10659833 : Blo 1663031 10659833 := bstep (se 2 (by rfl) ⟨3997437, by rfl⟩ : syracuseStep 10659833 = 7994875) B7994875
theorem B3746015 : Blo 1663031 3746015 := bstep (se 1 (by rfl) ⟨2809511, by rfl⟩ : syracuseStep 3746015 = 5619023) B5619023
theorem B21326327 : Blo 1663031 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B4737761 : Blo 1663031 4737761 := bstep (se 2 (by rfl) ⟨1776660, by rfl⟩ : syracuseStep 4737761 = 3553321) B3553321
theorem B23989121 : Blo 1663031 23989121 := bstep (se 2 (by rfl) ⟨8995920, by rfl⟩ : syracuseStep 23989121 = 17991841) B17991841
theorem B18951083 : Blo 1663031 18951083 := bstep (se 1 (by rfl) ⟨14213312, by rfl⟩ : syracuseStep 18951083 = 28426625) B28426625
theorem B2370503 : Blo 1663031 2370503 := bstep (se 1 (by rfl) ⟨1777877, by rfl⟩ : syracuseStep 2370503 = 3555755) B3555755
theorem B8424809 : Blo 1663031 8424809 := bstep (se 2 (by rfl) ⟨3159303, by rfl⟩ : syracuseStep 8424809 = 6318607) B6318607
theorem B6745513 : Blo 1663031 6745513 := bstep (se 2 (by rfl) ⟨2529567, by rfl⟩ : syracuseStep 6745513 = 5059135) B5059135
theorem B53972405 : Blo 1663031 53972405 := bstep (se 5 (by rfl) ⟨2529956, by rfl⟩ : syracuseStep 53972405 = 5059913) B5059913
theorem B42659621 : Blo 1663031 42659621 := bstep (se 4 (by rfl) ⟨3999339, by rfl⟩ : syracuseStep 42659621 = 7998679) B7998679
theorem B3158119 : Blo 1663031 3158119 := bstep (se 1 (by rfl) ⟨2368589, by rfl⟩ : syracuseStep 3158119 = 4737179) B4737179
theorem B28422251 : Blo 1663031 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B2494655 : Blo 1663031 2494655 := bstep (se 1 (by rfl) ⟨1870991, by rfl⟩ : syracuseStep 2494655 = 3741983) B3741983
theorem B2494697 : Blo 1663031 2494697 := bstep (se 2 (by rfl) ⟨935511, by rfl⟩ : syracuseStep 2494697 = 1871023) B1871023
theorem B2494823 : Blo 1663031 2494823 := bstep (se 1 (by rfl) ⟨1871117, by rfl⟩ : syracuseStep 2494823 = 3742235) B3742235
theorem B23073167 : Blo 1663031 23073167 := bstep (se 1 (by rfl) ⟨17304875, by rfl⟩ : syracuseStep 23073167 = 34609751) B34609751
theorem B2249321 : Blo 1663031 2249321 := bstep (se 2 (by rfl) ⟨843495, by rfl⟩ : syracuseStep 2249321 = 1686991) B1686991
theorem B10400507 : Blo 1663031 10400507 := bstep (se 1 (by rfl) ⟨7800380, by rfl⟩ : syracuseStep 10400507 = 15600761) B15600761
theorem B68334455 : Blo 1663031 68334455 := bstep (se 1 (by rfl) ⟨51250841, by rfl⟩ : syracuseStep 68334455 = 102501683) B102501683
theorem B2806825 : Blo 1663031 2806825 := bstep (se 2 (by rfl) ⟨1052559, by rfl⟩ : syracuseStep 2806825 = 2105119) B2105119
theorem B2495657 : Blo 1663031 2495657 := bstep (se 2 (by rfl) ⟨935871, by rfl⟩ : syracuseStep 2495657 = 1871743) B1871743
theorem B2495723 : Blo 1663031 2495723 := bstep (se 1 (by rfl) ⟨1871792, by rfl⟩ : syracuseStep 2495723 = 3743585) B3743585
theorem B2807095 : Blo 1663031 2807095 := bstep (se 1 (by rfl) ⟨2105321, by rfl⟩ : syracuseStep 2807095 = 4210643) B4210643
theorem B3552569 : Blo 1663031 3552569 := bstep (se 2 (by rfl) ⟨1332213, by rfl⟩ : syracuseStep 3552569 = 2664427) B2664427
theorem B2495807 : Blo 1663031 2495807 := bstep (se 1 (by rfl) ⟨1871855, by rfl⟩ : syracuseStep 2495807 = 3743711) B3743711
theorem B2807291 : Blo 1663031 2807291 := bstep (se 1 (by rfl) ⟨2105468, by rfl⟩ : syracuseStep 2807291 = 4210937) B4210937
theorem B2495999 : Blo 1663031 2495999 := bstep (se 1 (by rfl) ⟨1871999, by rfl⟩ : syracuseStep 2495999 = 3743999) B3743999
theorem B2496107 : Blo 1663031 2496107 := bstep (se 1 (by rfl) ⟨1872080, by rfl⟩ : syracuseStep 2496107 = 3744161) B3744161
theorem B2496377 : Blo 1663031 2496377 := bstep (se 2 (by rfl) ⟨936141, by rfl⟩ : syracuseStep 2496377 = 1872283) B1872283
theorem B2807723 : Blo 1663031 2807723 := bstep (se 1 (by rfl) ⟨2105792, by rfl⟩ : syracuseStep 2807723 = 4211585) B4211585
theorem B9115591 : Blo 1663031 9115591 := bstep (se 1 (by rfl) ⟨6836693, by rfl⟩ : syracuseStep 9115591 = 13673387) B13673387
theorem B40458203 : Blo 1663031 40458203 := bstep (se 1 (by rfl) ⟨30343652, by rfl⟩ : syracuseStep 40458203 = 60687305) B60687305
theorem B2496623 : Blo 1663031 2496623 := bstep (se 1 (by rfl) ⟨1872467, by rfl⟩ : syracuseStep 2496623 = 3744935) B3744935
theorem B2496695 : Blo 1663031 2496695 := bstep (se 1 (by rfl) ⟨1872521, by rfl⟩ : syracuseStep 2496695 = 3745043) B3745043
theorem B68344145 : Blo 1663031 68344145 := bstep (se 2 (by rfl) ⟨25629054, by rfl⟩ : syracuseStep 68344145 = 51258109) B51258109
theorem B2808263 : Blo 1663031 2808263 := bstep (se 1 (by rfl) ⟨2106197, by rfl⟩ : syracuseStep 2808263 = 4212395) B4212395
theorem B5618267 : Blo 1663031 5618267 := bstep (se 1 (by rfl) ⟨4213700, by rfl⟩ : syracuseStep 5618267 = 8427401) B8427401
theorem B2497115 : Blo 1663031 2497115 := bstep (se 1 (by rfl) ⟨1872836, by rfl⟩ : syracuseStep 2497115 = 3745673) B3745673
theorem B2497127 : Blo 1663031 2497127 := bstep (se 1 (by rfl) ⟨1872845, by rfl⟩ : syracuseStep 2497127 = 3745691) B3745691
theorem B2497151 : Blo 1663031 2497151 := bstep (se 1 (by rfl) ⟨1872863, by rfl⟩ : syracuseStep 2497151 = 3745727) B3745727
theorem B6314719 : Blo 1663031 6314719 := bstep (se 1 (by rfl) ⟨4736039, by rfl⟩ : syracuseStep 6314719 = 9472079) B9472079
theorem B2808553 : Blo 1663031 2808553 := bstep (se 2 (by rfl) ⟨1053207, by rfl⟩ : syracuseStep 2808553 = 2106415) B2106415
theorem B2497259 : Blo 1663031 2497259 := bstep (se 1 (by rfl) ⟨1872944, by rfl⟩ : syracuseStep 2497259 = 3745889) B3745889
theorem B2497289 : Blo 1663031 2497289 := bstep (se 2 (by rfl) ⟨936483, by rfl⟩ : syracuseStep 2497289 = 1872967) B1872967
theorem B3742505 : Blo 1663031 3742505 := bstep (se 2 (by rfl) ⟨1403439, by rfl⟩ : syracuseStep 3742505 = 2806879) B2806879
theorem B2497529 : Blo 1663031 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B8993825 : Blo 1663031 8993825 := bstep (se 2 (by rfl) ⟨3372684, by rfl⟩ : syracuseStep 8993825 = 6745369) B6745369
theorem B9477161 : Blo 1663031 9477161 := bstep (se 2 (by rfl) ⟨3553935, by rfl⟩ : syracuseStep 9477161 = 7107871) B7107871
theorem B3742775 : Blo 1663031 3742775 := bstep (se 1 (by rfl) ⟨2807081, by rfl⟩ : syracuseStep 3742775 = 5614163) B5614163
theorem B15989825 : Blo 1663031 15989825 := bstep (se 2 (by rfl) ⟨5996184, by rfl⟩ : syracuseStep 15989825 = 11992369) B11992369
theorem B2809019 : Blo 1663031 2809019 := bstep (se 1 (by rfl) ⟨2106764, by rfl⟩ : syracuseStep 2809019 = 4213529) B4213529
theorem B5332351 : Blo 1663031 5332351 := bstep (se 1 (by rfl) ⟨3999263, by rfl⟩ : syracuseStep 5332351 = 7998527) B7998527
theorem B10116521 : Blo 1663031 10116521 := bstep (se 2 (by rfl) ⟨3793695, by rfl⟩ : syracuseStep 10116521 = 7587391) B7587391
theorem B4210127 : Blo 1663031 4210127 := bstep (se 1 (by rfl) ⟨3157595, by rfl⟩ : syracuseStep 4210127 = 6315191) B6315191
theorem B14220967 : Blo 1663031 14220967 := bstep (se 1 (by rfl) ⟨10665725, by rfl⟩ : syracuseStep 14220967 = 21331451) B21331451
theorem B3743567 : Blo 1663031 3743567 := bstep (se 1 (by rfl) ⟨2807675, by rfl⟩ : syracuseStep 3743567 = 5615351) B5615351
theorem B18948167 : Blo 1663031 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B1663103 : Blo 1663031 1663103 := bstep (se 1 (by rfl) ⟨1247327, by rfl⟩ : syracuseStep 1663103 = 2494655) B2494655
theorem B4210825 : Blo 1663031 4210825 := bstep (se 2 (by rfl) ⟨1579059, by rfl⟩ : syracuseStep 4210825 = 3158119) B3158119
theorem B1663131 : Blo 1663031 1663131 := bstep (se 1 (by rfl) ⟨1247348, by rfl⟩ : syracuseStep 1663131 = 2494697) B2494697
theorem B1663215 : Blo 1663031 1663215 := bstep (se 1 (by rfl) ⟨1247411, by rfl⟩ : syracuseStep 1663215 = 2494823) B2494823
theorem B23986469 : Blo 1663031 23986469 := bstep (se 4 (by rfl) ⟨2248731, by rfl⟩ : syracuseStep 23986469 = 4497463) B4497463
theorem B18956915 : Blo 1663031 18956915 := bstep (se 1 (by rfl) ⟨14217686, by rfl⟩ : syracuseStep 18956915 = 28435373) B28435373
theorem B1663771 : Blo 1663031 1663771 := bstep (se 1 (by rfl) ⟨1247828, by rfl⟩ : syracuseStep 1663771 = 2495657) B2495657
theorem B1663815 : Blo 1663031 1663815 := bstep (se 1 (by rfl) ⟨1247861, by rfl⟩ : syracuseStep 1663815 = 2495723) B2495723
theorem B2368379 : Blo 1663031 2368379 := bstep (se 1 (by rfl) ⟨1776284, by rfl⟩ : syracuseStep 2368379 = 3552569) B3552569
theorem B1663871 : Blo 1663031 1663871 := bstep (se 1 (by rfl) ⟨1247903, by rfl⟩ : syracuseStep 1663871 = 2495807) B2495807
theorem B3744737 : Blo 1663031 3744737 := bstep (se 2 (by rfl) ⟨1404276, by rfl⟩ : syracuseStep 3744737 = 2808553) B2808553
theorem B1663999 : Blo 1663031 1663999 := bstep (se 1 (by rfl) ⟨1247999, by rfl⟩ : syracuseStep 1663999 = 2495999) B2495999
theorem B1664071 : Blo 1663031 1664071 := bstep (se 1 (by rfl) ⟨1248053, by rfl⟩ : syracuseStep 1664071 = 2496107) B2496107
theorem B54002771 : Blo 1663031 54002771 := bstep (se 1 (by rfl) ⟨40502078, by rfl⟩ : syracuseStep 54002771 = 81004157) B81004157
theorem B3998879 : Blo 1663031 3998879 := bstep (se 1 (by rfl) ⟨2999159, by rfl⟩ : syracuseStep 3998879 = 5998319) B5998319
theorem B1664251 : Blo 1663031 1664251 := bstep (se 1 (by rfl) ⟨1248188, by rfl⟩ : syracuseStep 1664251 = 2496377) B2496377
theorem B1664415 : Blo 1663031 1664415 := bstep (se 1 (by rfl) ⟨1248311, by rfl⟩ : syracuseStep 1664415 = 2496623) B2496623
theorem B1664463 : Blo 1663031 1664463 := bstep (se 1 (by rfl) ⟨1248347, by rfl⟩ : syracuseStep 1664463 = 2496695) B2496695
theorem B3745511 : Blo 1663031 3745511 := bstep (se 1 (by rfl) ⟨2809133, by rfl⟩ : syracuseStep 3745511 = 5618267) B5618267
theorem B1664743 : Blo 1663031 1664743 := bstep (se 1 (by rfl) ⟨1248557, by rfl⟩ : syracuseStep 1664743 = 2497115) B2497115
theorem B1664751 : Blo 1663031 1664751 := bstep (se 1 (by rfl) ⟨1248563, by rfl⟩ : syracuseStep 1664751 = 2497127) B2497127
theorem B1664767 : Blo 1663031 1664767 := bstep (se 1 (by rfl) ⟨1248575, by rfl⟩ : syracuseStep 1664767 = 2497151) B2497151
theorem B1664839 : Blo 1663031 1664839 := bstep (se 1 (by rfl) ⟨1248629, by rfl⟩ : syracuseStep 1664839 = 2497259) B2497259
theorem B1664859 : Blo 1663031 1664859 := bstep (se 1 (by rfl) ⟨1248644, by rfl⟩ : syracuseStep 1664859 = 2497289) B2497289
theorem B15992747 : Blo 1663031 15992747 := bstep (se 1 (by rfl) ⟨11994560, by rfl⟩ : syracuseStep 15992747 = 23989121) B23989121
theorem B12634055 : Blo 1663031 12634055 := bstep (se 1 (by rfl) ⟨9475541, by rfl⟩ : syracuseStep 12634055 = 18951083) B18951083
theorem B1665019 : Blo 1663031 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B6318107 : Blo 1663031 6318107 := bstep (se 1 (by rfl) ⟨4738580, by rfl⟩ : syracuseStep 6318107 = 9477161) B9477161
theorem B10659883 : Blo 1663031 10659883 := bstep (se 1 (by rfl) ⟨7994912, by rfl⟩ : syracuseStep 10659883 = 15989825) B15989825
theorem B6744347 : Blo 1663031 6744347 := bstep (se 1 (by rfl) ⟨5058260, by rfl⟩ : syracuseStep 6744347 = 10116521) B10116521
theorem B35981603 : Blo 1663031 35981603 := bstep (se 1 (by rfl) ⟨26986202, by rfl⟩ : syracuseStep 35981603 = 53972405) B53972405
theorem B182225213 : Blo 1663031 182225213 := bstep (se 3 (by rfl) ⟨34167227, by rfl⟩ : syracuseStep 182225213 = 68334455) B68334455
theorem B5614703 : Blo 1663031 5614703 := bstep (se 1 (by rfl) ⟨4211027, by rfl⟩ : syracuseStep 5614703 = 8422055) B8422055
theorem B6933671 : Blo 1663031 6933671 := bstep (se 1 (by rfl) ⟨5200253, by rfl⟩ : syracuseStep 6933671 = 10400507) B10400507
theorem B3157375 : Blo 1663031 3157375 := bstep (se 1 (by rfl) ⟨2368031, by rfl⟩ : syracuseStep 3157375 = 4736063) B4736063
theorem B3157481 : Blo 1663031 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B3157535 : Blo 1663031 3157535 := bstep (se 1 (by rfl) ⟨2368151, by rfl⟩ : syracuseStep 3157535 = 4736303) B4736303
theorem B31993487 : Blo 1663031 31993487 := bstep (se 1 (by rfl) ⟨23995115, by rfl⟩ : syracuseStep 31993487 = 47990231) B47990231
theorem B1871527 : Blo 1663031 1871527 := bstep (se 1 (by rfl) ⟨1403645, by rfl⟩ : syracuseStep 1871527 = 2807291) B2807291
theorem B1871815 : Blo 1663031 1871815 := bstep (se 1 (by rfl) ⟨1403861, by rfl⟩ : syracuseStep 1871815 = 2807723) B2807723
theorem B26972135 : Blo 1663031 26972135 := bstep (se 1 (by rfl) ⟨20229101, by rfl⟩ : syracuseStep 26972135 = 40458203) B40458203
theorem B7106555 : Blo 1663031 7106555 := bstep (se 1 (by rfl) ⟨5329916, by rfl⟩ : syracuseStep 7106555 = 10659833) B10659833
theorem B1872175 : Blo 1663031 1872175 := bstep (se 1 (by rfl) ⟨1404131, by rfl⟩ : syracuseStep 1872175 = 2808263) B2808263
theorem B14217551 : Blo 1663031 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B3158507 : Blo 1663031 3158507 := bstep (se 1 (by rfl) ⟨2368880, by rfl⟩ : syracuseStep 3158507 = 4737761) B4737761
theorem B2495003 : Blo 1663031 2495003 := bstep (se 1 (by rfl) ⟨1871252, by rfl⟩ : syracuseStep 2495003 = 3742505) B3742505
theorem B2495183 : Blo 1663031 2495183 := bstep (se 1 (by rfl) ⟨1871387, by rfl⟩ : syracuseStep 2495183 = 3742775) B3742775
theorem B1872679 : Blo 1663031 1872679 := bstep (se 1 (by rfl) ⟨1404509, by rfl⟩ : syracuseStep 1872679 = 2809019) B2809019
theorem B18961289 : Blo 1663031 18961289 := bstep (se 2 (by rfl) ⟨7110483, by rfl⟩ : syracuseStep 18961289 = 14220967) B14220967
theorem B5616539 : Blo 1663031 5616539 := bstep (se 1 (by rfl) ⟨4212404, by rfl⟩ : syracuseStep 5616539 = 8424809) B8424809
theorem B2806751 : Blo 1663031 2806751 := bstep (se 1 (by rfl) ⟨2105063, by rfl⟩ : syracuseStep 2806751 = 4210127) B4210127
theorem B6321341 : Blo 1663031 6321341 := bstep (se 3 (by rfl) ⟨1185251, by rfl⟩ : syracuseStep 6321341 = 2370503) B2370503
theorem B28439747 : Blo 1663031 28439747 := bstep (se 1 (by rfl) ⟨21329810, by rfl⟩ : syracuseStep 28439747 = 42659621) B42659621
theorem B2495711 : Blo 1663031 2495711 := bstep (se 1 (by rfl) ⟨1871783, by rfl⟩ : syracuseStep 2495711 = 3743567) B3743567
theorem B12154121 : Blo 1663031 12154121 := bstep (se 2 (by rfl) ⟨4557795, by rfl⟩ : syracuseStep 12154121 = 9115591) B9115591
theorem B2495951 : Blo 1663031 2495951 := bstep (se 1 (by rfl) ⟨1871963, by rfl⟩ : syracuseStep 2495951 = 3743927) B3743927
theorem B4871677 : Blo 1663031 4871677 := bstep (se 3 (by rfl) ⟨913439, by rfl⟩ : syracuseStep 4871677 = 1826879) B1826879
theorem B23975513 : Blo 1663031 23975513 := bstep (se 2 (by rfl) ⟨8990817, by rfl⟩ : syracuseStep 23975513 = 17981635) B17981635
theorem B15382111 : Blo 1663031 15382111 := bstep (se 1 (by rfl) ⟨11536583, by rfl⟩ : syracuseStep 15382111 = 23073167) B23073167
theorem B2496191 : Blo 1663031 2496191 := bstep (se 1 (by rfl) ⟨1872143, by rfl⟩ : syracuseStep 2496191 = 3744287) B3744287
theorem B2496575 : Blo 1663031 2496575 := bstep (se 1 (by rfl) ⟨1872431, by rfl⟩ : syracuseStep 2496575 = 3744863) B3744863
theorem B2496743 : Blo 1663031 2496743 := bstep (se 1 (by rfl) ⟨1872557, by rfl⟩ : syracuseStep 2496743 = 3745115) B3745115
theorem B8419625 : Blo 1663031 8419625 := bstep (se 2 (by rfl) ⟨3157359, by rfl⟩ : syracuseStep 8419625 = 6314719) B6314719
theorem B2496923 : Blo 1663031 2496923 := bstep (se 1 (by rfl) ⟨1872692, by rfl⟩ : syracuseStep 2496923 = 3745385) B3745385
theorem B23992757 : Blo 1663031 23992757 := bstep (se 5 (by rfl) ⟨1124660, by rfl⟩ : syracuseStep 23992757 = 2249321) B2249321
theorem B3742433 : Blo 1663031 3742433 := bstep (se 2 (by rfl) ⟨1403412, by rfl⟩ : syracuseStep 3742433 = 2806825) B2806825
theorem B5618429 : Blo 1663031 5618429 := bstep (se 3 (by rfl) ⟨1053455, by rfl⟩ : syracuseStep 5618429 = 2106911) B2106911
theorem B2497343 : Blo 1663031 2497343 := bstep (se 1 (by rfl) ⟨1873007, by rfl⟩ : syracuseStep 2497343 = 3746015) B3746015
theorem B45562763 : Blo 1663031 45562763 := bstep (se 1 (by rfl) ⟨34172072, by rfl⟩ : syracuseStep 45562763 = 68344145) B68344145
theorem B12802981 : Blo 1663031 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B3742793 : Blo 1663031 3742793 := bstep (se 2 (by rfl) ⟨1403547, by rfl⟩ : syracuseStep 3742793 = 2807095) B2807095
theorem B7109801 : Blo 1663031 7109801 := bstep (se 2 (by rfl) ⟨2666175, by rfl⟩ : syracuseStep 7109801 = 5332351) B5332351
theorem B8994017 : Blo 1663031 8994017 := bstep (se 2 (by rfl) ⟨3372756, by rfl⟩ : syracuseStep 8994017 = 6745513) B6745513
theorem B5995883 : Blo 1663031 5995883 := bstep (se 1 (by rfl) ⟨4496912, by rfl⟩ : syracuseStep 5995883 = 8993825) B8993825
theorem B12632111 : Blo 1663031 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B14213177 : Blo 1663031 14213177 := bstep (se 2 (by rfl) ⟨5329941, by rfl⟩ : syracuseStep 14213177 = 10659883) B10659883
theorem B15990979 : Blo 1663031 15990979 := bstep (se 1 (by rfl) ⟨11993234, by rfl⟩ : syracuseStep 15990979 = 23986469) B23986469
theorem B9478367 : Blo 1663031 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B2105671 : Blo 1663031 2105671 := bstep (se 1 (by rfl) ⟨1579253, by rfl⟩ : syracuseStep 2105671 = 3158507) B3158507
theorem B1663335 : Blo 1663031 1663335 := bstep (se 1 (by rfl) ⟨1247501, by rfl⟩ : syracuseStep 1663335 = 2495003) B2495003
theorem B1663455 : Blo 1663031 1663455 := bstep (se 1 (by rfl) ⟨1247591, by rfl⟩ : syracuseStep 1663455 = 2495183) B2495183
theorem B12640859 : Blo 1663031 12640859 := bstep (se 1 (by rfl) ⟨9480644, by rfl⟩ : syracuseStep 12640859 = 18961289) B18961289
theorem B3744359 : Blo 1663031 3744359 := bstep (se 1 (by rfl) ⟨2808269, by rfl⟩ : syracuseStep 3744359 = 5616539) B5616539
theorem B1663807 : Blo 1663031 1663807 := bstep (se 1 (by rfl) ⟨1247855, by rfl⟩ : syracuseStep 1663807 = 2495711) B2495711
theorem B8102747 : Blo 1663031 8102747 := bstep (se 1 (by rfl) ⟨6077060, by rfl⟩ : syracuseStep 8102747 = 12154121) B12154121
theorem B1663967 : Blo 1663031 1663967 := bstep (se 1 (by rfl) ⟨1247975, by rfl⟩ : syracuseStep 1663967 = 2495951) B2495951
theorem B15983675 : Blo 1663031 15983675 := bstep (se 1 (by rfl) ⟨11987756, by rfl⟩ : syracuseStep 15983675 = 23975513) B23975513
theorem B1664127 : Blo 1663031 1664127 := bstep (se 1 (by rfl) ⟨1248095, by rfl⟩ : syracuseStep 1664127 = 2496191) B2496191
theorem B8422703 : Blo 1663031 8422703 := bstep (se 1 (by rfl) ⟨6317027, by rfl⟩ : syracuseStep 8422703 = 12634055) B12634055
theorem B4212071 : Blo 1663031 4212071 := bstep (se 1 (by rfl) ⟨3159053, by rfl⟩ : syracuseStep 4212071 = 6318107) B6318107
theorem B1664383 : Blo 1663031 1664383 := bstep (se 1 (by rfl) ⟨1248287, by rfl⟩ : syracuseStep 1664383 = 2496575) B2496575
theorem B1664495 : Blo 1663031 1664495 := bstep (se 1 (by rfl) ⟨1248371, by rfl⟩ : syracuseStep 1664495 = 2496743) B2496743
theorem B23987735 : Blo 1663031 23987735 := bstep (se 1 (by rfl) ⟨17990801, by rfl⟩ : syracuseStep 23987735 = 35981603) B35981603
theorem B5613083 : Blo 1663031 5613083 := bstep (se 1 (by rfl) ⟨4209812, by rfl⟩ : syracuseStep 5613083 = 8419625) B8419625
theorem B1664615 : Blo 1663031 1664615 := bstep (se 1 (by rfl) ⟨1248461, by rfl⟩ : syracuseStep 1664615 = 2496923) B2496923
theorem B3745619 : Blo 1663031 3745619 := bstep (se 1 (by rfl) ⟨2809214, by rfl⟩ : syracuseStep 3745619 = 5618429) B5618429
theorem B1664895 : Blo 1663031 1664895 := bstep (se 1 (by rfl) ⟨1248671, by rfl⟩ : syracuseStep 1664895 = 2497343) B2497343
theorem B4622447 : Blo 1663031 4622447 := bstep (se 1 (by rfl) ⟨3466835, by rfl⟩ : syracuseStep 4622447 = 6933671) B6933671
theorem B4737703 : Blo 1663031 4737703 := bstep (se 1 (by rfl) ⟨3553277, by rfl⟩ : syracuseStep 4737703 = 7106555) B7106555
theorem B5614433 : Blo 1663031 5614433 := bstep (se 2 (by rfl) ⟨2105412, by rfl⟩ : syracuseStep 5614433 = 4210825) B4210825
theorem B1871167 : Blo 1663031 1871167 := bstep (se 1 (by rfl) ⟨1403375, by rfl⟩ : syracuseStep 1871167 = 2806751) B2806751
theorem B2665919 : Blo 1663031 2665919 := bstep (se 1 (by rfl) ⟨1999439, by rfl⟩ : syracuseStep 2665919 = 3998879) B3998879
theorem B4214227 : Blo 1663031 4214227 := bstep (se 1 (by rfl) ⟨3160670, by rfl⟩ : syracuseStep 4214227 = 6321341) B6321341
theorem B18959831 : Blo 1663031 18959831 := bstep (se 1 (by rfl) ⟨14219873, by rfl⟩ : syracuseStep 18959831 = 28439747) B28439747
theorem B10661831 : Blo 1663031 10661831 := bstep (se 1 (by rfl) ⟨7996373, by rfl⟩ : syracuseStep 10661831 = 15992747) B15992747
theorem B121483475 : Blo 1663031 121483475 := bstep (se 1 (by rfl) ⟨91112606, by rfl⟩ : syracuseStep 121483475 = 182225213) B182225213
theorem B15995171 : Blo 1663031 15995171 := bstep (se 1 (by rfl) ⟨11996378, by rfl⟩ : syracuseStep 15995171 = 23992757) B23992757
theorem B2494955 : Blo 1663031 2494955 := bstep (se 1 (by rfl) ⟨1871216, by rfl⟩ : syracuseStep 2494955 = 3742433) B3742433
theorem B2495195 : Blo 1663031 2495195 := bstep (se 1 (by rfl) ⟨1871396, by rfl⟩ : syracuseStep 2495195 = 3742793) B3742793
theorem B4739867 : Blo 1663031 4739867 := bstep (se 1 (by rfl) ⟨3554900, by rfl⟩ : syracuseStep 4739867 = 7109801) B7109801
theorem B20509481 : Blo 1663031 20509481 := bstep (se 2 (by rfl) ⟨7691055, by rfl⟩ : syracuseStep 20509481 = 15382111) B15382111
theorem B2495369 : Blo 1663031 2495369 := bstep (se 2 (by rfl) ⟨935763, by rfl⟩ : syracuseStep 2495369 = 1871527) B1871527
theorem B21328991 : Blo 1663031 21328991 := bstep (se 1 (by rfl) ⟨15996743, by rfl⟩ : syracuseStep 21328991 = 31993487) B31993487
theorem B2495753 : Blo 1663031 2495753 := bstep (se 2 (by rfl) ⟨935907, by rfl⟩ : syracuseStep 2495753 = 1871815) B1871815
theorem B2496233 : Blo 1663031 2496233 := bstep (se 2 (by rfl) ⟨936087, by rfl⟩ : syracuseStep 2496233 = 1872175) B1872175
theorem B12637943 : Blo 1663031 12637943 := bstep (se 1 (by rfl) ⟨9478457, by rfl⟩ : syracuseStep 12637943 = 18956915) B18956915
theorem B23984045 : Blo 1663031 23984045 := bstep (se 3 (by rfl) ⟨4497008, by rfl⟩ : syracuseStep 23984045 = 8994017) B8994017
theorem B2496491 : Blo 1663031 2496491 := bstep (se 1 (by rfl) ⟨1872368, by rfl⟩ : syracuseStep 2496491 = 3744737) B3744737
theorem B36001847 : Blo 1663031 36001847 := bstep (se 1 (by rfl) ⟨27001385, by rfl⟩ : syracuseStep 36001847 = 54002771) B54002771
theorem B15989021 : Blo 1663031 15989021 := bstep (se 3 (by rfl) ⟨2997941, by rfl⟩ : syracuseStep 15989021 = 5995883) B5995883
theorem B2496905 : Blo 1663031 2496905 := bstep (se 2 (by rfl) ⟨936339, by rfl⟩ : syracuseStep 2496905 = 1872679) B1872679
theorem B2497007 : Blo 1663031 2497007 := bstep (se 1 (by rfl) ⟨1872755, by rfl⟩ : syracuseStep 2497007 = 3745511) B3745511
theorem B17070641 : Blo 1663031 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B8419949 : Blo 1663031 8419949 := bstep (se 3 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 8419949 = 3157481) B3157481
theorem B4496231 : Blo 1663031 4496231 := bstep (se 1 (by rfl) ⟨3372173, by rfl⟩ : syracuseStep 4496231 = 6744347) B6744347
theorem B4209833 : Blo 1663031 4209833 := bstep (se 2 (by rfl) ⟨1578687, by rfl⟩ : syracuseStep 4209833 = 3157375) B3157375
theorem B30375175 : Blo 1663031 30375175 := bstep (se 1 (by rfl) ⟨22781381, by rfl⟩ : syracuseStep 30375175 = 45562763) B45562763
theorem B6495569 : Blo 1663031 6495569 := bstep (se 2 (by rfl) ⟨2435838, by rfl⟩ : syracuseStep 6495569 = 4871677) B4871677
theorem B3743135 : Blo 1663031 3743135 := bstep (se 1 (by rfl) ⟨2807351, by rfl⟩ : syracuseStep 3743135 = 5614703) B5614703
theorem B6315677 : Blo 1663031 6315677 := bstep (se 3 (by rfl) ⟨1184189, by rfl⟩ : syracuseStep 6315677 = 2368379) B2368379
theorem B2105023 : Blo 1663031 2105023 := bstep (se 1 (by rfl) ⟨1578767, by rfl⟩ : syracuseStep 2105023 = 3157535) B3157535
theorem B17981423 : Blo 1663031 17981423 := bstep (se 1 (by rfl) ⟨13486067, by rfl⟩ : syracuseStep 17981423 = 26972135) B26972135
theorem B8421407 : Blo 1663031 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B1663303 : Blo 1663031 1663303 := bstep (se 1 (by rfl) ⟨1247477, by rfl⟩ : syracuseStep 1663303 = 2494955) B2494955
theorem B1663463 : Blo 1663031 1663463 := bstep (se 1 (by rfl) ⟨1247597, by rfl⟩ : syracuseStep 1663463 = 2495195) B2495195
theorem B1663579 : Blo 1663031 1663579 := bstep (se 1 (by rfl) ⟨1247684, by rfl⟩ : syracuseStep 1663579 = 2495369) B2495369
theorem B1663835 : Blo 1663031 1663835 := bstep (se 1 (by rfl) ⟨1247876, by rfl⟩ : syracuseStep 1663835 = 2495753) B2495753
theorem B6316937 : Blo 1663031 6316937 := bstep (se 2 (by rfl) ⟨2368851, by rfl⟩ : syracuseStep 6316937 = 4737703) B4737703
theorem B15991823 : Blo 1663031 15991823 := bstep (se 1 (by rfl) ⟨11993867, by rfl⟩ : syracuseStep 15991823 = 23987735) B23987735
theorem B1664155 : Blo 1663031 1664155 := bstep (se 1 (by rfl) ⟨1248116, by rfl⟩ : syracuseStep 1664155 = 2496233) B2496233
theorem B1664327 : Blo 1663031 1664327 := bstep (se 1 (by rfl) ⟨1248245, by rfl⟩ : syracuseStep 1664327 = 2496491) B2496491
theorem B10659347 : Blo 1663031 10659347 := bstep (se 1 (by rfl) ⟨7994510, by rfl⟩ : syracuseStep 10659347 = 15989021) B15989021
theorem B1664603 : Blo 1663031 1664603 := bstep (se 1 (by rfl) ⟨1248452, by rfl⟩ : syracuseStep 1664603 = 2496905) B2496905
theorem B1664671 : Blo 1663031 1664671 := bstep (se 1 (by rfl) ⟨1248503, by rfl⟩ : syracuseStep 1664671 = 2497007) B2497007
theorem B11380427 : Blo 1663031 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B5613299 : Blo 1663031 5613299 := bstep (se 1 (by rfl) ⟨4209974, by rfl⟩ : syracuseStep 5613299 = 8419949) B8419949
theorem B54691949 : Blo 1663031 54691949 := bstep (se 3 (by rfl) ⟨10254740, by rfl⟩ : syracuseStep 54691949 = 20509481) B20509481
theorem B11987615 : Blo 1663031 11987615 := bstep (se 1 (by rfl) ⟨8990711, by rfl⟩ : syracuseStep 11987615 = 17981423) B17981423
theorem B80988983 : Blo 1663031 80988983 := bstep (se 1 (by rfl) ⟨60741737, by rfl⟩ : syracuseStep 80988983 = 121483475) B121483475
theorem B6318911 : Blo 1663031 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B5401831 : Blo 1663031 5401831 := bstep (se 1 (by rfl) ⟨4051373, by rfl⟩ : syracuseStep 5401831 = 8102747) B8102747
theorem B5615135 : Blo 1663031 5615135 := bstep (se 1 (by rfl) ⟨4211351, by rfl⟩ : syracuseStep 5615135 = 8422703) B8422703
theorem B8425295 : Blo 1663031 8425295 := bstep (se 1 (by rfl) ⟨6318971, by rfl⟩ : syracuseStep 8425295 = 12637943) B12637943
theorem B2494889 : Blo 1663031 2494889 := bstep (se 2 (by rfl) ⟨935583, by rfl⟩ : syracuseStep 2494889 = 1871167) B1871167
theorem B2806555 : Blo 1663031 2806555 := bstep (se 1 (by rfl) ⟨2104916, by rfl⟩ : syracuseStep 2806555 = 4209833) B4209833
theorem B4330379 : Blo 1663031 4330379 := bstep (se 1 (by rfl) ⟨3247784, by rfl⟩ : syracuseStep 4330379 = 6495569) B6495569
theorem B2806697 : Blo 1663031 2806697 := bstep (se 2 (by rfl) ⟨1052511, by rfl⟩ : syracuseStep 2806697 = 2105023) B2105023
theorem B2495423 : Blo 1663031 2495423 := bstep (se 1 (by rfl) ⟨1871567, by rfl⟩ : syracuseStep 2495423 = 3743135) B3743135
theorem B7107887 : Blo 1663031 7107887 := bstep (se 1 (by rfl) ⟨5330915, by rfl⟩ : syracuseStep 7107887 = 10661831) B10661831
theorem B9475451 : Blo 1663031 9475451 := bstep (se 1 (by rfl) ⟨7106588, by rfl⟩ : syracuseStep 9475451 = 14213177) B14213177
theorem B10663447 : Blo 1663031 10663447 := bstep (se 1 (by rfl) ⟨7997585, by rfl⟩ : syracuseStep 10663447 = 15995171) B15995171
theorem B21321305 : Blo 1663031 21321305 := bstep (se 2 (by rfl) ⟨7995489, by rfl⟩ : syracuseStep 21321305 = 15990979) B15990979
theorem B12326525 : Blo 1663031 12326525 := bstep (se 3 (by rfl) ⟨2311223, by rfl⟩ : syracuseStep 12326525 = 4622447) B4622447
theorem B8427239 : Blo 1663031 8427239 := bstep (se 1 (by rfl) ⟨6320429, by rfl⟩ : syracuseStep 8427239 = 12640859) B12640859
theorem B2496239 : Blo 1663031 2496239 := bstep (se 1 (by rfl) ⟨1872179, by rfl⟩ : syracuseStep 2496239 = 3744359) B3744359
theorem B2807561 : Blo 1663031 2807561 := bstep (se 2 (by rfl) ⟨1052835, by rfl⟩ : syracuseStep 2807561 = 2105671) B2105671
theorem B3159911 : Blo 1663031 3159911 := bstep (se 1 (by rfl) ⟨2369933, by rfl⟩ : syracuseStep 3159911 = 4739867) B4739867
theorem B10655783 : Blo 1663031 10655783 := bstep (se 1 (by rfl) ⟨7991837, by rfl⟩ : syracuseStep 10655783 = 15983675) B15983675
theorem B14219327 : Blo 1663031 14219327 := bstep (se 1 (by rfl) ⟨10664495, by rfl⟩ : syracuseStep 14219327 = 21328991) B21328991
theorem B2808047 : Blo 1663031 2808047 := bstep (se 1 (by rfl) ⟨2106035, by rfl⟩ : syracuseStep 2808047 = 4212071) B4212071
theorem B3742055 : Blo 1663031 3742055 := bstep (se 1 (by rfl) ⟨2806541, by rfl⟩ : syracuseStep 3742055 = 5613083) B5613083
theorem B7109117 : Blo 1663031 7109117 := bstep (se 3 (by rfl) ⟨1332959, by rfl⟩ : syracuseStep 7109117 = 2665919) B2665919
theorem B2497079 : Blo 1663031 2497079 := bstep (se 1 (by rfl) ⟨1872809, by rfl⟩ : syracuseStep 2497079 = 3745619) B3745619
theorem B15989363 : Blo 1663031 15989363 := bstep (se 1 (by rfl) ⟨11992022, by rfl⟩ : syracuseStep 15989363 = 23984045) B23984045
theorem B24001231 : Blo 1663031 24001231 := bstep (se 1 (by rfl) ⟨18000923, by rfl⟩ : syracuseStep 24001231 = 36001847) B36001847
theorem B40500233 : Blo 1663031 40500233 := bstep (se 2 (by rfl) ⟨15187587, by rfl⟩ : syracuseStep 40500233 = 30375175) B30375175
theorem B3742955 : Blo 1663031 3742955 := bstep (se 1 (by rfl) ⟨2807216, by rfl⟩ : syracuseStep 3742955 = 5614433) B5614433
theorem B2997487 : Blo 1663031 2997487 := bstep (se 1 (by rfl) ⟨2248115, by rfl⟩ : syracuseStep 2997487 = 4496231) B4496231
theorem B5618969 : Blo 1663031 5618969 := bstep (se 2 (by rfl) ⟨2107113, by rfl⟩ : syracuseStep 5618969 = 4214227) B4214227
theorem B12639887 : Blo 1663031 12639887 := bstep (se 1 (by rfl) ⟨9479915, by rfl⟩ : syracuseStep 12639887 = 18959831) B18959831
theorem B4210451 : Blo 1663031 4210451 := bstep (se 1 (by rfl) ⟨3157838, by rfl⟩ : syracuseStep 4210451 = 6315677) B6315677
theorem B1663259 : Blo 1663031 1663259 := bstep (se 1 (by rfl) ⟨1247444, by rfl⟩ : syracuseStep 1663259 = 2494889) B2494889
theorem B4211291 : Blo 1663031 4211291 := bstep (se 1 (by rfl) ⟨3158468, by rfl⟩ : syracuseStep 4211291 = 6316937) B6316937
theorem B1663615 : Blo 1663031 1663615 := bstep (se 1 (by rfl) ⟨1247711, by rfl⟩ : syracuseStep 1663615 = 2495423) B2495423
theorem B6316967 : Blo 1663031 6316967 := bstep (se 1 (by rfl) ⟨4737725, by rfl⟩ : syracuseStep 6316967 = 9475451) B9475451
theorem B14214203 : Blo 1663031 14214203 := bstep (se 1 (by rfl) ⟨10660652, by rfl⟩ : syracuseStep 14214203 = 21321305) B21321305
theorem B8217683 : Blo 1663031 8217683 := bstep (se 1 (by rfl) ⟨6163262, by rfl⟩ : syracuseStep 8217683 = 12326525) B12326525
theorem B7586951 : Blo 1663031 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B1664159 : Blo 1663031 1664159 := bstep (se 1 (by rfl) ⟨1248119, by rfl⟩ : syracuseStep 1664159 = 2496239) B2496239
theorem B7103855 : Blo 1663031 7103855 := bstep (se 1 (by rfl) ⟨5327891, by rfl⟩ : syracuseStep 7103855 = 10655783) B10655783
theorem B9479551 : Blo 1663031 9479551 := bstep (se 1 (by rfl) ⟨7109663, by rfl⟩ : syracuseStep 9479551 = 14219327) B14219327
theorem B7202441 : Blo 1663031 7202441 := bstep (se 2 (by rfl) ⟨2700915, by rfl⟩ : syracuseStep 7202441 = 5401831) B5401831
theorem B1664719 : Blo 1663031 1664719 := bstep (se 1 (by rfl) ⟨1248539, by rfl⟩ : syracuseStep 1664719 = 2497079) B2497079
theorem B10659575 : Blo 1663031 10659575 := bstep (se 1 (by rfl) ⟨7994681, by rfl⟩ : syracuseStep 10659575 = 15989363) B15989363
theorem B4212607 : Blo 1663031 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B3745979 : Blo 1663031 3745979 := bstep (se 1 (by rfl) ⟨2809484, by rfl⟩ : syracuseStep 3745979 = 5618969) B5618969
theorem B5614271 : Blo 1663031 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B1871131 : Blo 1663031 1871131 := bstep (se 1 (by rfl) ⟨1403348, by rfl⟩ : syracuseStep 1871131 = 2806697) B2806697
theorem B10661215 : Blo 1663031 10661215 := bstep (se 1 (by rfl) ⟨7995911, by rfl⟩ : syracuseStep 10661215 = 15991823) B15991823
theorem B4738591 : Blo 1663031 4738591 := bstep (se 1 (by rfl) ⟨3553943, by rfl⟩ : syracuseStep 4738591 = 7107887) B7107887
theorem B32001641 : Blo 1663031 32001641 := bstep (se 2 (by rfl) ⟨12000615, by rfl⟩ : syracuseStep 32001641 = 24001231) B24001231
theorem B7106231 : Blo 1663031 7106231 := bstep (se 1 (by rfl) ⟨5329673, by rfl⟩ : syracuseStep 7106231 = 10659347) B10659347
theorem B1871707 : Blo 1663031 1871707 := bstep (se 1 (by rfl) ⟨1403780, by rfl⟩ : syracuseStep 1871707 = 2807561) B2807561
theorem B1872031 : Blo 1663031 1872031 := bstep (se 1 (by rfl) ⟨1404023, by rfl⟩ : syracuseStep 1872031 = 2808047) B2808047
theorem B2494703 : Blo 1663031 2494703 := bstep (se 1 (by rfl) ⟨1871027, by rfl⟩ : syracuseStep 2494703 = 3742055) B3742055
theorem B4739411 : Blo 1663031 4739411 := bstep (se 1 (by rfl) ⟨3554558, by rfl⟩ : syracuseStep 4739411 = 7109117) B7109117
theorem B7991743 : Blo 1663031 7991743 := bstep (se 1 (by rfl) ⟨5993807, by rfl⟩ : syracuseStep 7991743 = 11987615) B11987615
theorem B14217929 : Blo 1663031 14217929 := bstep (se 2 (by rfl) ⟨5331723, by rfl⟩ : syracuseStep 14217929 = 10663447) B10663447
theorem B2495303 : Blo 1663031 2495303 := bstep (se 1 (by rfl) ⟨1871477, by rfl⟩ : syracuseStep 2495303 = 3742955) B3742955
theorem B8426429 : Blo 1663031 8426429 := bstep (se 3 (by rfl) ⟨1579955, by rfl⟩ : syracuseStep 8426429 = 3159911) B3159911
theorem B11547677 : Blo 1663031 11547677 := bstep (se 3 (by rfl) ⟨2165189, by rfl⟩ : syracuseStep 11547677 = 4330379) B4330379
theorem B8426591 : Blo 1663031 8426591 := bstep (se 1 (by rfl) ⟨6319943, by rfl⟩ : syracuseStep 8426591 = 12639887) B12639887
theorem B2806967 : Blo 1663031 2806967 := bstep (se 1 (by rfl) ⟨2105225, by rfl⟩ : syracuseStep 2806967 = 4210451) B4210451
theorem B5616863 : Blo 1663031 5616863 := bstep (se 1 (by rfl) ⟨4212647, by rfl⟩ : syracuseStep 5616863 = 8425295) B8425295
theorem B3742073 : Blo 1663031 3742073 := bstep (se 2 (by rfl) ⟨1403277, by rfl⟩ : syracuseStep 3742073 = 2806555) B2806555
theorem B5618159 : Blo 1663031 5618159 := bstep (se 1 (by rfl) ⟨4213619, by rfl⟩ : syracuseStep 5618159 = 8427239) B8427239
theorem B3742199 : Blo 1663031 3742199 := bstep (se 1 (by rfl) ⟨2806649, by rfl⟩ : syracuseStep 3742199 = 5613299) B5613299
theorem B36461299 : Blo 1663031 36461299 := bstep (se 1 (by rfl) ⟨27345974, by rfl⟩ : syracuseStep 36461299 = 54691949) B54691949
theorem B3996649 : Blo 1663031 3996649 := bstep (se 2 (by rfl) ⟨1498743, by rfl⟩ : syracuseStep 3996649 = 2997487) B2997487
theorem B53992655 : Blo 1663031 53992655 := bstep (se 1 (by rfl) ⟨40494491, by rfl⟩ : syracuseStep 53992655 = 80988983) B80988983
theorem B27000155 : Blo 1663031 27000155 := bstep (se 1 (by rfl) ⟨20250116, by rfl⟩ : syracuseStep 27000155 = 40500233) B40500233
theorem B3743423 : Blo 1663031 3743423 := bstep (se 1 (by rfl) ⟨2807567, by rfl⟩ : syracuseStep 3743423 = 5615135) B5615135
theorem B1663135 : Blo 1663031 1663135 := bstep (se 1 (by rfl) ⟨1247351, by rfl⟩ : syracuseStep 1663135 = 2494703) B2494703
theorem B9478619 : Blo 1663031 9478619 := bstep (se 1 (by rfl) ⟨7108964, by rfl⟩ : syracuseStep 9478619 = 14217929) B14217929
theorem B1663535 : Blo 1663031 1663535 := bstep (se 1 (by rfl) ⟨1247651, by rfl⟩ : syracuseStep 1663535 = 2495303) B2495303
theorem B4211311 : Blo 1663031 4211311 := bstep (se 1 (by rfl) ⟨3158483, by rfl⟩ : syracuseStep 4211311 = 6316967) B6316967
theorem B3744575 : Blo 1663031 3744575 := bstep (se 1 (by rfl) ⟨2808431, by rfl⟩ : syracuseStep 3744575 = 5616863) B5616863
theorem B72000413 : Blo 1663031 72000413 := bstep (se 3 (by rfl) ⟨13500077, by rfl⟩ : syracuseStep 72000413 = 27000155) B27000155
theorem B4735903 : Blo 1663031 4735903 := bstep (se 1 (by rfl) ⟨3551927, by rfl⟩ : syracuseStep 4735903 = 7103855) B7103855
theorem B4801627 : Blo 1663031 4801627 := bstep (se 1 (by rfl) ⟨3601220, by rfl⟩ : syracuseStep 4801627 = 7202441) B7202441
theorem B3745439 : Blo 1663031 3745439 := bstep (se 1 (by rfl) ⟨2809079, by rfl⟩ : syracuseStep 3745439 = 5618159) B5618159
theorem B14214953 : Blo 1663031 14214953 := bstep (se 2 (by rfl) ⟨5330607, by rfl⟩ : syracuseStep 14214953 = 10661215) B10661215
theorem B6318121 : Blo 1663031 6318121 := bstep (se 2 (by rfl) ⟨2369295, by rfl⟩ : syracuseStep 6318121 = 4738591) B4738591
theorem B21334427 : Blo 1663031 21334427 := bstep (se 1 (by rfl) ⟨16000820, by rfl⟩ : syracuseStep 21334427 = 32001641) B32001641
theorem B4737487 : Blo 1663031 4737487 := bstep (se 1 (by rfl) ⟨3553115, by rfl⟩ : syracuseStep 4737487 = 7106231) B7106231
theorem B1871311 : Blo 1663031 1871311 := bstep (se 1 (by rfl) ⟨1403483, by rfl⟩ : syracuseStep 1871311 = 2806967) B2806967
theorem B48615065 : Blo 1663031 48615065 := bstep (se 2 (by rfl) ⟨18230649, by rfl⟩ : syracuseStep 48615065 = 36461299) B36461299
theorem B7106383 : Blo 1663031 7106383 := bstep (se 1 (by rfl) ⟨5329787, by rfl⟩ : syracuseStep 7106383 = 10659575) B10659575
theorem B5328865 : Blo 1663031 5328865 := bstep (se 2 (by rfl) ⟨1998324, by rfl⟩ : syracuseStep 5328865 = 3996649) B3996649
theorem B2494715 : Blo 1663031 2494715 := bstep (se 1 (by rfl) ⟨1871036, by rfl⟩ : syracuseStep 2494715 = 3742073) B3742073
theorem B2494799 : Blo 1663031 2494799 := bstep (se 1 (by rfl) ⟨1871099, by rfl⟩ : syracuseStep 2494799 = 3742199) B3742199
theorem B2494841 : Blo 1663031 2494841 := bstep (se 2 (by rfl) ⟨935565, by rfl⟩ : syracuseStep 2494841 = 1871131) B1871131
theorem B2495609 : Blo 1663031 2495609 := bstep (se 2 (by rfl) ⟨935853, by rfl⟩ : syracuseStep 2495609 = 1871707) B1871707
theorem B2495615 : Blo 1663031 2495615 := bstep (se 1 (by rfl) ⟨1871711, by rfl⟩ : syracuseStep 2495615 = 3743423) B3743423
theorem B5616809 : Blo 1663031 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B2496041 : Blo 1663031 2496041 := bstep (se 2 (by rfl) ⟨936015, by rfl⟩ : syracuseStep 2496041 = 1872031) B1872031
theorem B20231869 : Blo 1663031 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B2807527 : Blo 1663031 2807527 := bstep (se 1 (by rfl) ⟨2105645, by rfl⟩ : syracuseStep 2807527 = 4211291) B4211291
theorem B10655657 : Blo 1663031 10655657 := bstep (se 2 (by rfl) ⟨3995871, by rfl⟩ : syracuseStep 10655657 = 7991743) B7991743
theorem B5617619 : Blo 1663031 5617619 := bstep (se 1 (by rfl) ⟨4213214, by rfl⟩ : syracuseStep 5617619 = 8426429) B8426429
theorem B7698451 : Blo 1663031 7698451 := bstep (se 1 (by rfl) ⟨5773838, by rfl⟩ : syracuseStep 7698451 = 11547677) B11547677
theorem B9476135 : Blo 1663031 9476135 := bstep (se 1 (by rfl) ⟨7107101, by rfl⟩ : syracuseStep 9476135 = 14214203) B14214203
theorem B5478455 : Blo 1663031 5478455 := bstep (se 1 (by rfl) ⟨4108841, by rfl⟩ : syracuseStep 5478455 = 8217683) B8217683
theorem B5617727 : Blo 1663031 5617727 := bstep (se 1 (by rfl) ⟨4213295, by rfl⟩ : syracuseStep 5617727 = 8426591) B8426591
theorem B12638429 : Blo 1663031 12638429 := bstep (se 3 (by rfl) ⟨2369705, by rfl⟩ : syracuseStep 12638429 = 4739411) B4739411
theorem B2497319 : Blo 1663031 2497319 := bstep (se 1 (by rfl) ⟨1872989, by rfl⟩ : syracuseStep 2497319 = 3745979) B3745979
theorem B3742847 : Blo 1663031 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B12639401 : Blo 1663031 12639401 := bstep (se 2 (by rfl) ⟨4739775, by rfl⟩ : syracuseStep 12639401 = 9479551) B9479551
theorem B35995103 : Blo 1663031 35995103 := bstep (se 1 (by rfl) ⟨26996327, by rfl⟩ : syracuseStep 35995103 = 53992655) B53992655
theorem B10264601 : Blo 1663031 10264601 := bstep (se 2 (by rfl) ⟨3849225, by rfl⟩ : syracuseStep 10264601 = 7698451) B7698451
theorem B1663143 : Blo 1663031 1663143 := bstep (se 1 (by rfl) ⟨1247357, by rfl⟩ : syracuseStep 1663143 = 2494715) B2494715
theorem B1663199 : Blo 1663031 1663199 := bstep (se 1 (by rfl) ⟨1247399, by rfl⟩ : syracuseStep 1663199 = 2494799) B2494799
theorem B1663227 : Blo 1663031 1663227 := bstep (se 1 (by rfl) ⟨1247420, by rfl⟩ : syracuseStep 1663227 = 2494841) B2494841
theorem B6316649 : Blo 1663031 6316649 := bstep (se 2 (by rfl) ⟨2368743, by rfl⟩ : syracuseStep 6316649 = 4737487) B4737487
theorem B1663739 : Blo 1663031 1663739 := bstep (se 1 (by rfl) ⟨1247804, by rfl⟩ : syracuseStep 1663739 = 2495609) B2495609
theorem B1663743 : Blo 1663031 1663743 := bstep (se 1 (by rfl) ⟨1247807, by rfl⟩ : syracuseStep 1663743 = 2495615) B2495615
theorem B3744539 : Blo 1663031 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B1664027 : Blo 1663031 1664027 := bstep (se 1 (by rfl) ⟨1248020, by rfl⟩ : syracuseStep 1664027 = 2496041) B2496041
theorem B7103771 : Blo 1663031 7103771 := bstep (se 1 (by rfl) ⟨5327828, by rfl⟩ : syracuseStep 7103771 = 10655657) B10655657
theorem B3745079 : Blo 1663031 3745079 := bstep (se 1 (by rfl) ⟨2808809, by rfl⟩ : syracuseStep 3745079 = 5617619) B5617619
theorem B6317423 : Blo 1663031 6317423 := bstep (se 1 (by rfl) ⟨4738067, by rfl⟩ : syracuseStep 6317423 = 9476135) B9476135
theorem B3745151 : Blo 1663031 3745151 := bstep (se 1 (by rfl) ⟨2808863, by rfl⟩ : syracuseStep 3745151 = 5617727) B5617727
theorem B14222951 : Blo 1663031 14222951 := bstep (se 1 (by rfl) ⟨10667213, by rfl⟩ : syracuseStep 14222951 = 21334427) B21334427
theorem B1664879 : Blo 1663031 1664879 := bstep (se 1 (by rfl) ⟨1248659, by rfl⟩ : syracuseStep 1664879 = 2497319) B2497319
theorem B23996735 : Blo 1663031 23996735 := bstep (se 1 (by rfl) ⟨17997551, by rfl⟩ : syracuseStep 23996735 = 35995103) B35995103
theorem B32410043 : Blo 1663031 32410043 := bstep (se 1 (by rfl) ⟨24307532, by rfl⟩ : syracuseStep 32410043 = 48615065) B48615065
theorem B7105153 : Blo 1663031 7105153 := bstep (se 2 (by rfl) ⟨2664432, by rfl⟩ : syracuseStep 7105153 = 5328865) B5328865
theorem B8424161 : Blo 1663031 8424161 := bstep (se 2 (by rfl) ⟨3159060, by rfl⟩ : syracuseStep 8424161 = 6318121) B6318121
theorem B6319079 : Blo 1663031 6319079 := bstep (se 1 (by rfl) ⟨4739309, by rfl⟩ : syracuseStep 6319079 = 9478619) B9478619
theorem B48000275 : Blo 1663031 48000275 := bstep (se 1 (by rfl) ⟨36000206, by rfl⟩ : syracuseStep 48000275 = 72000413) B72000413
theorem B5615081 : Blo 1663031 5615081 := bstep (se 2 (by rfl) ⟨2105655, by rfl⟩ : syracuseStep 5615081 = 4211311) B4211311
theorem B6402169 : Blo 1663031 6402169 := bstep (se 2 (by rfl) ⟨2400813, by rfl⟩ : syracuseStep 6402169 = 4801627) B4801627
theorem B8425619 : Blo 1663031 8425619 := bstep (se 1 (by rfl) ⟨6319214, by rfl⟩ : syracuseStep 8425619 = 12638429) B12638429
theorem B2495081 : Blo 1663031 2495081 := bstep (se 2 (by rfl) ⟨935655, by rfl⟩ : syracuseStep 2495081 = 1871311) B1871311
theorem B2495231 : Blo 1663031 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B8426267 : Blo 1663031 8426267 := bstep (se 1 (by rfl) ⟨6319700, by rfl⟩ : syracuseStep 8426267 = 12639401) B12639401
theorem B9475177 : Blo 1663031 9475177 := bstep (se 2 (by rfl) ⟨3553191, by rfl⟩ : syracuseStep 9475177 = 7106383) B7106383
theorem B2496383 : Blo 1663031 2496383 := bstep (se 1 (by rfl) ⟨1872287, by rfl⟩ : syracuseStep 2496383 = 3744575) B3744575
theorem B2496959 : Blo 1663031 2496959 := bstep (se 1 (by rfl) ⟨1872719, by rfl⟩ : syracuseStep 2496959 = 3745439) B3745439
theorem B9476635 : Blo 1663031 9476635 := bstep (se 1 (by rfl) ⟨7107476, by rfl⟩ : syracuseStep 9476635 = 14214953) B14214953
theorem B6314537 : Blo 1663031 6314537 := bstep (se 2 (by rfl) ⟨2367951, by rfl⟩ : syracuseStep 6314537 = 4735903) B4735903
theorem B3652303 : Blo 1663031 3652303 := bstep (se 1 (by rfl) ⟨2739227, by rfl⟩ : syracuseStep 3652303 = 5478455) B5478455
theorem B26975825 : Blo 1663031 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B3743369 : Blo 1663031 3743369 := bstep (se 2 (by rfl) ⟨1403763, by rfl⟩ : syracuseStep 3743369 = 2807527) B2807527
theorem B1663387 : Blo 1663031 1663387 := bstep (se 1 (by rfl) ⟨1247540, by rfl⟩ : syracuseStep 1663387 = 2495081) B2495081
theorem B4211099 : Blo 1663031 4211099 := bstep (se 1 (by rfl) ⟨3158324, by rfl⟩ : syracuseStep 4211099 = 6316649) B6316649
theorem B1663487 : Blo 1663031 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B34144901 : Blo 1663031 34144901 := bstep (se 4 (by rfl) ⟨3201084, by rfl⟩ : syracuseStep 34144901 = 6402169) B6402169
theorem B4735847 : Blo 1663031 4735847 := bstep (se 1 (by rfl) ⟨3551885, by rfl⟩ : syracuseStep 4735847 = 7103771) B7103771
theorem B4211615 : Blo 1663031 4211615 := bstep (se 1 (by rfl) ⟨3158711, by rfl⟩ : syracuseStep 4211615 = 6317423) B6317423
theorem B1664255 : Blo 1663031 1664255 := bstep (se 1 (by rfl) ⟨1248191, by rfl⟩ : syracuseStep 1664255 = 2496383) B2496383
theorem B12633569 : Blo 1663031 12633569 := bstep (se 2 (by rfl) ⟨4737588, by rfl⟩ : syracuseStep 12633569 = 9475177) B9475177
theorem B1664639 : Blo 1663031 1664639 := bstep (se 1 (by rfl) ⟨1248479, by rfl⟩ : syracuseStep 1664639 = 2496959) B2496959
theorem B4212719 : Blo 1663031 4212719 := bstep (se 1 (by rfl) ⟨3159539, by rfl⟩ : syracuseStep 4212719 = 6319079) B6319079
theorem B32000183 : Blo 1663031 32000183 := bstep (se 1 (by rfl) ⟨24000137, by rfl⟩ : syracuseStep 32000183 = 48000275) B48000275
theorem B17983883 : Blo 1663031 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B6843067 : Blo 1663031 6843067 := bstep (se 1 (by rfl) ⟨5132300, by rfl⟩ : syracuseStep 6843067 = 10264601) B10264601
theorem B12635513 : Blo 1663031 12635513 := bstep (se 2 (by rfl) ⟨4738317, by rfl⟩ : syracuseStep 12635513 = 9476635) B9476635
theorem B9473537 : Blo 1663031 9473537 := bstep (se 2 (by rfl) ⟨3552576, by rfl⟩ : syracuseStep 9473537 = 7105153) B7105153
theorem B4869737 : Blo 1663031 4869737 := bstep (se 2 (by rfl) ⟨1826151, by rfl⟩ : syracuseStep 4869737 = 3652303) B3652303
theorem B9481967 : Blo 1663031 9481967 := bstep (se 1 (by rfl) ⟨7111475, by rfl⟩ : syracuseStep 9481967 = 14222951) B14222951
theorem B21606695 : Blo 1663031 21606695 := bstep (se 1 (by rfl) ⟨16205021, by rfl⟩ : syracuseStep 21606695 = 32410043) B32410043
theorem B5616107 : Blo 1663031 5616107 := bstep (se 1 (by rfl) ⟨4212080, by rfl⟩ : syracuseStep 5616107 = 8424161) B8424161
theorem B2495579 : Blo 1663031 2495579 := bstep (se 1 (by rfl) ⟨1871684, by rfl⟩ : syracuseStep 2495579 = 3743369) B3743369
theorem B5617079 : Blo 1663031 5617079 := bstep (se 1 (by rfl) ⟨4212809, by rfl⟩ : syracuseStep 5617079 = 8425619) B8425619
theorem B2496359 : Blo 1663031 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B5617511 : Blo 1663031 5617511 := bstep (se 1 (by rfl) ⟨4213133, by rfl⟩ : syracuseStep 5617511 = 8426267) B8426267
theorem B2496719 : Blo 1663031 2496719 := bstep (se 1 (by rfl) ⟨1872539, by rfl⟩ : syracuseStep 2496719 = 3745079) B3745079
theorem B2496767 : Blo 1663031 2496767 := bstep (se 1 (by rfl) ⟨1872575, by rfl⟩ : syracuseStep 2496767 = 3745151) B3745151
theorem B15997823 : Blo 1663031 15997823 := bstep (se 1 (by rfl) ⟨11998367, by rfl⟩ : syracuseStep 15997823 = 23996735) B23996735
theorem B4209691 : Blo 1663031 4209691 := bstep (se 1 (by rfl) ⟨3157268, by rfl⟩ : syracuseStep 4209691 = 6314537) B6314537
theorem B3743387 : Blo 1663031 3743387 := bstep (se 1 (by rfl) ⟨2807540, by rfl⟩ : syracuseStep 3743387 = 5615081) B5615081
theorem B3744071 : Blo 1663031 3744071 := bstep (se 1 (by rfl) ⟨2808053, by rfl⟩ : syracuseStep 3744071 = 5616107) B5616107
theorem B1663719 : Blo 1663031 1663719 := bstep (se 1 (by rfl) ⟨1247789, by rfl⟩ : syracuseStep 1663719 = 2495579) B2495579
theorem B3744719 : Blo 1663031 3744719 := bstep (se 1 (by rfl) ⟨2808539, by rfl⟩ : syracuseStep 3744719 = 5617079) B5617079
theorem B8422379 : Blo 1663031 8422379 := bstep (se 1 (by rfl) ⟨6316784, by rfl⟩ : syracuseStep 8422379 = 12633569) B12633569
theorem B1664239 : Blo 1663031 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B3745007 : Blo 1663031 3745007 := bstep (se 1 (by rfl) ⟨2808755, by rfl⟩ : syracuseStep 3745007 = 5617511) B5617511
theorem B5612921 : Blo 1663031 5612921 := bstep (se 2 (by rfl) ⟨2104845, by rfl⟩ : syracuseStep 5612921 = 4209691) B4209691
theorem B21333455 : Blo 1663031 21333455 := bstep (se 1 (by rfl) ⟨16000091, by rfl⟩ : syracuseStep 21333455 = 32000183) B32000183
theorem B1664479 : Blo 1663031 1664479 := bstep (se 1 (by rfl) ⟨1248359, by rfl⟩ : syracuseStep 1664479 = 2496719) B2496719
theorem B1664511 : Blo 1663031 1664511 := bstep (se 1 (by rfl) ⟨1248383, by rfl⟩ : syracuseStep 1664511 = 2496767) B2496767
theorem B8423675 : Blo 1663031 8423675 := bstep (se 1 (by rfl) ⟨6317756, by rfl⟩ : syracuseStep 8423675 = 12635513) B12635513
theorem B3246491 : Blo 1663031 3246491 := bstep (se 1 (by rfl) ⟨2434868, by rfl⟩ : syracuseStep 3246491 = 4869737) B4869737
theorem B14404463 : Blo 1663031 14404463 := bstep (se 1 (by rfl) ⟨10803347, by rfl⟩ : syracuseStep 14404463 = 21606695) B21606695
theorem B3157231 : Blo 1663031 3157231 := bstep (se 1 (by rfl) ⟨2367923, by rfl⟩ : syracuseStep 3157231 = 4735847) B4735847
theorem B145985429 : Blo 1663031 145985429 := bstep (se 6 (by rfl) ⟨3421533, by rfl⟩ : syracuseStep 145985429 = 6843067) B6843067
theorem B11989255 : Blo 1663031 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B2495591 : Blo 1663031 2495591 := bstep (se 1 (by rfl) ⟨1871693, by rfl⟩ : syracuseStep 2495591 = 3743387) B3743387
theorem B6321311 : Blo 1663031 6321311 := bstep (se 1 (by rfl) ⟨4740983, by rfl⟩ : syracuseStep 6321311 = 9481967) B9481967
theorem B2807399 : Blo 1663031 2807399 := bstep (se 1 (by rfl) ⟨2105549, by rfl⟩ : syracuseStep 2807399 = 4211099) B4211099
theorem B22763267 : Blo 1663031 22763267 := bstep (se 1 (by rfl) ⟨17072450, by rfl⟩ : syracuseStep 22763267 = 34144901) B34144901
theorem B2807743 : Blo 1663031 2807743 := bstep (se 1 (by rfl) ⟨2105807, by rfl⟩ : syracuseStep 2807743 = 4211615) B4211615
theorem B2808479 : Blo 1663031 2808479 := bstep (se 1 (by rfl) ⟨2106359, by rfl⟩ : syracuseStep 2808479 = 4212719) B4212719
theorem B10665215 : Blo 1663031 10665215 := bstep (se 1 (by rfl) ⟨7998911, by rfl⟩ : syracuseStep 10665215 = 15997823) B15997823
theorem B6315691 : Blo 1663031 6315691 := bstep (se 1 (by rfl) ⟨4736768, by rfl⟩ : syracuseStep 6315691 = 9473537) B9473537
theorem B1663727 : Blo 1663031 1663727 := bstep (se 1 (by rfl) ⟨1247795, by rfl⟩ : syracuseStep 1663727 = 2495591) B2495591
theorem B14222303 : Blo 1663031 14222303 := bstep (se 1 (by rfl) ⟨10666727, by rfl⟩ : syracuseStep 14222303 = 21333455) B21333455
theorem B2164327 : Blo 1663031 2164327 := bstep (se 1 (by rfl) ⟨1623245, by rfl⟩ : syracuseStep 2164327 = 3246491) B3246491
theorem B9602975 : Blo 1663031 9602975 := bstep (se 1 (by rfl) ⟨7202231, by rfl⟩ : syracuseStep 9602975 = 14404463) B14404463
theorem B97323619 : Blo 1663031 97323619 := bstep (se 1 (by rfl) ⟨72992714, by rfl⟩ : syracuseStep 97323619 = 145985429) B145985429
theorem B15985673 : Blo 1663031 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B5614919 : Blo 1663031 5614919 := bstep (se 1 (by rfl) ⟨4211189, by rfl⟩ : syracuseStep 5614919 = 8422379) B8422379
theorem B4214207 : Blo 1663031 4214207 := bstep (se 1 (by rfl) ⟨3160655, by rfl⟩ : syracuseStep 4214207 = 6321311) B6321311
theorem B1871599 : Blo 1663031 1871599 := bstep (se 1 (by rfl) ⟨1403699, by rfl⟩ : syracuseStep 1871599 = 2807399) B2807399
theorem B15175511 : Blo 1663031 15175511 := bstep (se 1 (by rfl) ⟨11381633, by rfl⟩ : syracuseStep 15175511 = 22763267) B22763267
theorem B5615783 : Blo 1663031 5615783 := bstep (se 1 (by rfl) ⟨4211837, by rfl⟩ : syracuseStep 5615783 = 8423675) B8423675
theorem B1872319 : Blo 1663031 1872319 := bstep (se 1 (by rfl) ⟨1404239, by rfl⟩ : syracuseStep 1872319 = 2808479) B2808479
theorem B2496047 : Blo 1663031 2496047 := bstep (se 1 (by rfl) ⟨1872035, by rfl⟩ : syracuseStep 2496047 = 3744071) B3744071
theorem B2496479 : Blo 1663031 2496479 := bstep (se 1 (by rfl) ⟨1872359, by rfl⟩ : syracuseStep 2496479 = 3744719) B3744719
theorem B2496671 : Blo 1663031 2496671 := bstep (se 1 (by rfl) ⟨1872503, by rfl⟩ : syracuseStep 2496671 = 3745007) B3745007
theorem B3741947 : Blo 1663031 3741947 := bstep (se 1 (by rfl) ⟨2806460, by rfl⟩ : syracuseStep 3741947 = 5612921) B5612921
theorem B4209641 : Blo 1663031 4209641 := bstep (se 2 (by rfl) ⟨1578615, by rfl⟩ : syracuseStep 4209641 = 3157231) B3157231
theorem B7110143 : Blo 1663031 7110143 := bstep (se 1 (by rfl) ⟨5332607, by rfl⟩ : syracuseStep 7110143 = 10665215) B10665215
theorem B8420921 : Blo 1663031 8420921 := bstep (se 2 (by rfl) ⟨3157845, by rfl⟩ : syracuseStep 8420921 = 6315691) B6315691
theorem B3743657 : Blo 1663031 3743657 := bstep (se 2 (by rfl) ⟨1403871, by rfl⟩ : syracuseStep 3743657 = 2807743) B2807743
theorem B3743855 : Blo 1663031 3743855 := bstep (se 1 (by rfl) ⟨2807891, by rfl⟩ : syracuseStep 3743855 = 5615783) B5615783
theorem B11543077 : Blo 1663031 11543077 := bstep (se 4 (by rfl) ⟨1082163, by rfl⟩ : syracuseStep 11543077 = 2164327) B2164327
theorem B1664031 : Blo 1663031 1664031 := bstep (se 1 (by rfl) ⟨1248023, by rfl⟩ : syracuseStep 1664031 = 2496047) B2496047
theorem B1664319 : Blo 1663031 1664319 := bstep (se 1 (by rfl) ⟨1248239, by rfl⟩ : syracuseStep 1664319 = 2496479) B2496479
theorem B1664447 : Blo 1663031 1664447 := bstep (se 1 (by rfl) ⟨1248335, by rfl⟩ : syracuseStep 1664447 = 2496671) B2496671
theorem B5613947 : Blo 1663031 5613947 := bstep (se 1 (by rfl) ⟨4210460, by rfl⟩ : syracuseStep 5613947 = 8420921) B8420921
theorem B9481535 : Blo 1663031 9481535 := bstep (se 1 (by rfl) ⟨7111151, by rfl⟩ : syracuseStep 9481535 = 14222303) B14222303
theorem B129764825 : Blo 1663031 129764825 := bstep (se 2 (by rfl) ⟨48661809, by rfl⟩ : syracuseStep 129764825 = 97323619) B97323619
theorem B2494631 : Blo 1663031 2494631 := bstep (se 1 (by rfl) ⟨1870973, by rfl⟩ : syracuseStep 2494631 = 3741947) B3741947
theorem B2806427 : Blo 1663031 2806427 := bstep (se 1 (by rfl) ⟨2104820, by rfl⟩ : syracuseStep 2806427 = 4209641) B4209641
theorem B2495465 : Blo 1663031 2495465 := bstep (se 2 (by rfl) ⟨935799, by rfl⟩ : syracuseStep 2495465 = 1871599) B1871599
theorem B4740095 : Blo 1663031 4740095 := bstep (se 1 (by rfl) ⟨3555071, by rfl⟩ : syracuseStep 4740095 = 7110143) B7110143
theorem B2495771 : Blo 1663031 2495771 := bstep (se 1 (by rfl) ⟨1871828, by rfl⟩ : syracuseStep 2495771 = 3743657) B3743657
theorem B2496425 : Blo 1663031 2496425 := bstep (se 2 (by rfl) ⟨936159, by rfl⟩ : syracuseStep 2496425 = 1872319) B1872319
theorem B10657115 : Blo 1663031 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B3743279 : Blo 1663031 3743279 := bstep (se 1 (by rfl) ⟨2807459, by rfl⟩ : syracuseStep 3743279 = 5614919) B5614919
theorem B2809471 : Blo 1663031 2809471 := bstep (se 1 (by rfl) ⟨2107103, by rfl⟩ : syracuseStep 2809471 = 4214207) B4214207
theorem B25607933 : Blo 1663031 25607933 := bstep (se 3 (by rfl) ⟨4801487, by rfl⟩ : syracuseStep 25607933 = 9602975) B9602975
theorem B10117007 : Blo 1663031 10117007 := bstep (se 1 (by rfl) ⟨7587755, by rfl⟩ : syracuseStep 10117007 = 15175511) B15175511
theorem B1663087 : Blo 1663031 1663087 := bstep (se 1 (by rfl) ⟨1247315, by rfl⟩ : syracuseStep 1663087 = 2494631) B2494631
theorem B1663643 : Blo 1663031 1663643 := bstep (se 1 (by rfl) ⟨1247732, by rfl⟩ : syracuseStep 1663643 = 2495465) B2495465
theorem B1663847 : Blo 1663031 1663847 := bstep (se 1 (by rfl) ⟨1247885, by rfl⟩ : syracuseStep 1663847 = 2495771) B2495771
theorem B1664283 : Blo 1663031 1664283 := bstep (se 1 (by rfl) ⟨1248212, by rfl⟩ : syracuseStep 1664283 = 2496425) B2496425
theorem B3745961 : Blo 1663031 3745961 := bstep (se 2 (by rfl) ⟨1404735, by rfl⟩ : syracuseStep 3745961 = 2809471) B2809471
theorem B7104743 : Blo 1663031 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B86509883 : Blo 1663031 86509883 := bstep (se 1 (by rfl) ⟨64882412, by rfl⟩ : syracuseStep 86509883 = 129764825) B129764825
theorem B6744671 : Blo 1663031 6744671 := bstep (se 1 (by rfl) ⟨5058503, by rfl⟩ : syracuseStep 6744671 = 10117007) B10117007
theorem B1870951 : Blo 1663031 1870951 := bstep (se 1 (by rfl) ⟨1403213, by rfl⟩ : syracuseStep 1870951 = 2806427) B2806427
theorem B6321023 : Blo 1663031 6321023 := bstep (se 1 (by rfl) ⟨4740767, by rfl⟩ : syracuseStep 6321023 = 9481535) B9481535
theorem B2495519 : Blo 1663031 2495519 := bstep (se 1 (by rfl) ⟨1871639, by rfl⟩ : syracuseStep 2495519 = 3743279) B3743279
theorem B2495903 : Blo 1663031 2495903 := bstep (se 1 (by rfl) ⟨1871927, by rfl⟩ : syracuseStep 2495903 = 3743855) B3743855
theorem B3160063 : Blo 1663031 3160063 := bstep (se 1 (by rfl) ⟨2370047, by rfl⟩ : syracuseStep 3160063 = 4740095) B4740095
theorem B15390769 : Blo 1663031 15390769 := bstep (se 2 (by rfl) ⟨5771538, by rfl⟩ : syracuseStep 15390769 = 11543077) B11543077
theorem B3742631 : Blo 1663031 3742631 := bstep (se 1 (by rfl) ⟨2806973, by rfl⟩ : syracuseStep 3742631 = 5613947) B5613947
theorem B17071955 : Blo 1663031 17071955 := bstep (se 1 (by rfl) ⟨12803966, by rfl⟩ : syracuseStep 17071955 = 25607933) B25607933
theorem B20521025 : Blo 1663031 20521025 := bstep (se 2 (by rfl) ⟨7695384, by rfl⟩ : syracuseStep 20521025 = 15390769) B15390769
theorem B1663679 : Blo 1663031 1663679 := bstep (se 1 (by rfl) ⟨1247759, by rfl⟩ : syracuseStep 1663679 = 2495519) B2495519
theorem B1663935 : Blo 1663031 1663935 := bstep (se 1 (by rfl) ⟨1247951, by rfl⟩ : syracuseStep 1663935 = 2495903) B2495903
theorem B4736495 : Blo 1663031 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B57673255 : Blo 1663031 57673255 := bstep (se 1 (by rfl) ⟨43254941, by rfl⟩ : syracuseStep 57673255 = 86509883) B86509883
theorem B11381303 : Blo 1663031 11381303 := bstep (se 1 (by rfl) ⟨8535977, by rfl⟩ : syracuseStep 11381303 = 17071955) B17071955
theorem B4213417 : Blo 1663031 4213417 := bstep (se 2 (by rfl) ⟨1580031, by rfl⟩ : syracuseStep 4213417 = 3160063) B3160063
theorem B4214015 : Blo 1663031 4214015 := bstep (se 1 (by rfl) ⟨3160511, by rfl⟩ : syracuseStep 4214015 = 6321023) B6321023
theorem B2494601 : Blo 1663031 2494601 := bstep (se 2 (by rfl) ⟨935475, by rfl⟩ : syracuseStep 2494601 = 1870951) B1870951
theorem B2495087 : Blo 1663031 2495087 := bstep (se 1 (by rfl) ⟨1871315, by rfl⟩ : syracuseStep 2495087 = 3742631) B3742631
theorem B2497307 : Blo 1663031 2497307 := bstep (se 1 (by rfl) ⟨1872980, by rfl⟩ : syracuseStep 2497307 = 3745961) B3745961
theorem B4496447 : Blo 1663031 4496447 := bstep (se 1 (by rfl) ⟨3372335, by rfl⟩ : syracuseStep 4496447 = 6744671) B6744671
theorem B13680683 : Blo 1663031 13680683 := bstep (se 1 (by rfl) ⟨10260512, by rfl⟩ : syracuseStep 13680683 = 20521025) B20521025
theorem B1663067 : Blo 1663031 1663067 := bstep (se 1 (by rfl) ⟨1247300, by rfl⟩ : syracuseStep 1663067 = 2494601) B2494601
theorem B1663391 : Blo 1663031 1663391 := bstep (se 1 (by rfl) ⟨1247543, by rfl⟩ : syracuseStep 1663391 = 2495087) B2495087
theorem B7587535 : Blo 1663031 7587535 := bstep (se 1 (by rfl) ⟨5690651, by rfl⟩ : syracuseStep 7587535 = 11381303) B11381303
theorem B1664871 : Blo 1663031 1664871 := bstep (se 1 (by rfl) ⟨1248653, by rfl⟩ : syracuseStep 1664871 = 2497307) B2497307
theorem B5617889 : Blo 1663031 5617889 := bstep (se 2 (by rfl) ⟨2106708, by rfl⟩ : syracuseStep 5617889 = 4213417) B4213417
theorem B12630653 : Blo 1663031 12630653 := bstep (se 3 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 12630653 = 4736495) B4736495
theorem B2997631 : Blo 1663031 2997631 := bstep (se 1 (by rfl) ⟨2248223, by rfl⟩ : syracuseStep 2997631 = 4496447) B4496447
theorem B76897673 : Blo 1663031 76897673 := bstep (se 2 (by rfl) ⟨28836627, by rfl⟩ : syracuseStep 76897673 = 57673255) B57673255
theorem B2809343 : Blo 1663031 2809343 := bstep (se 1 (by rfl) ⟨2107007, by rfl⟩ : syracuseStep 2809343 = 4214015) B4214015
theorem B3745259 : Blo 1663031 3745259 := bstep (se 1 (by rfl) ⟨2808944, by rfl⟩ : syracuseStep 3745259 = 5617889) B5617889
theorem B9120455 : Blo 1663031 9120455 := bstep (se 1 (by rfl) ⟨6840341, by rfl⟩ : syracuseStep 9120455 = 13680683) B13680683
theorem B15987365 : Blo 1663031 15987365 := bstep (se 4 (by rfl) ⟨1498815, by rfl⟩ : syracuseStep 15987365 = 2997631) B2997631
theorem B1872895 : Blo 1663031 1872895 := bstep (se 1 (by rfl) ⟨1404671, by rfl⟩ : syracuseStep 1872895 = 2809343) B2809343
theorem B8420435 : Blo 1663031 8420435 := bstep (se 1 (by rfl) ⟨6315326, by rfl⟩ : syracuseStep 8420435 = 12630653) B12630653
theorem B51265115 : Blo 1663031 51265115 := bstep (se 1 (by rfl) ⟨38448836, by rfl⟩ : syracuseStep 51265115 = 76897673) B76897673
theorem B10116713 : Blo 1663031 10116713 := bstep (se 2 (by rfl) ⟨3793767, by rfl⟩ : syracuseStep 10116713 = 7587535) B7587535
theorem B10658243 : Blo 1663031 10658243 := bstep (se 1 (by rfl) ⟨7993682, by rfl⟩ : syracuseStep 10658243 = 15987365) B15987365
theorem B6080303 : Blo 1663031 6080303 := bstep (se 1 (by rfl) ⟨4560227, by rfl⟩ : syracuseStep 6080303 = 9120455) B9120455
theorem B5613623 : Blo 1663031 5613623 := bstep (se 1 (by rfl) ⟨4210217, by rfl⟩ : syracuseStep 5613623 = 8420435) B8420435
theorem B6744475 : Blo 1663031 6744475 := bstep (se 1 (by rfl) ⟨5058356, by rfl⟩ : syracuseStep 6744475 = 10116713) B10116713
theorem B2496839 : Blo 1663031 2496839 := bstep (se 1 (by rfl) ⟨1872629, by rfl⟩ : syracuseStep 2496839 = 3745259) B3745259
theorem B2497193 : Blo 1663031 2497193 := bstep (se 2 (by rfl) ⟨936447, by rfl⟩ : syracuseStep 2497193 = 1872895) B1872895
theorem B34176743 : Blo 1663031 34176743 := bstep (se 1 (by rfl) ⟨25632557, by rfl⟩ : syracuseStep 34176743 = 51265115) B51265115
theorem B1664559 : Blo 1663031 1664559 := bstep (se 1 (by rfl) ⟨1248419, by rfl⟩ : syracuseStep 1664559 = 2496839) B2496839
theorem B1664795 : Blo 1663031 1664795 := bstep (se 1 (by rfl) ⟨1248596, by rfl⟩ : syracuseStep 1664795 = 2497193) B2497193
theorem B16214141 : Blo 1663031 16214141 := bstep (se 3 (by rfl) ⟨3040151, by rfl⟩ : syracuseStep 16214141 = 6080303) B6080303
theorem B22784495 : Blo 1663031 22784495 := bstep (se 1 (by rfl) ⟨17088371, by rfl⟩ : syracuseStep 22784495 = 34176743) B34176743
theorem B7105495 : Blo 1663031 7105495 := bstep (se 1 (by rfl) ⟨5329121, by rfl⟩ : syracuseStep 7105495 = 10658243) B10658243
theorem B8992633 : Blo 1663031 8992633 := bstep (se 2 (by rfl) ⟨3372237, by rfl⟩ : syracuseStep 8992633 = 6744475) B6744475
theorem B3742415 : Blo 1663031 3742415 := bstep (se 1 (by rfl) ⟨2806811, by rfl⟩ : syracuseStep 3742415 = 5613623) B5613623
theorem B43237709 : Blo 1663031 43237709 := bstep (se 3 (by rfl) ⟨8107070, by rfl⟩ : syracuseStep 43237709 = 16214141) B16214141
theorem B243034613 : Blo 1663031 243034613 := bstep (se 5 (by rfl) ⟨11392247, by rfl⟩ : syracuseStep 243034613 = 22784495) B22784495
theorem B9473993 : Blo 1663031 9473993 := bstep (se 2 (by rfl) ⟨3552747, by rfl⟩ : syracuseStep 9473993 = 7105495) B7105495
theorem B2494943 : Blo 1663031 2494943 := bstep (se 1 (by rfl) ⟨1871207, by rfl⟩ : syracuseStep 2494943 = 3742415) B3742415
theorem B11990177 : Blo 1663031 11990177 := bstep (se 2 (by rfl) ⟨4496316, by rfl⟩ : syracuseStep 11990177 = 8992633) B8992633
theorem B1663295 : Blo 1663031 1663295 := bstep (se 1 (by rfl) ⟨1247471, by rfl⟩ : syracuseStep 1663295 = 2494943) B2494943
theorem B162023075 : Blo 1663031 162023075 := bstep (se 1 (by rfl) ⟨121517306, by rfl⟩ : syracuseStep 162023075 = 243034613) B243034613
theorem B28825139 : Blo 1663031 28825139 := bstep (se 1 (by rfl) ⟨21618854, by rfl⟩ : syracuseStep 28825139 = 43237709) B43237709
theorem B7993451 : Blo 1663031 7993451 := bstep (se 1 (by rfl) ⟨5995088, by rfl⟩ : syracuseStep 7993451 = 11990177) B11990177
theorem B6315995 : Blo 1663031 6315995 := bstep (se 1 (by rfl) ⟨4736996, by rfl⟩ : syracuseStep 6315995 = 9473993) B9473993
theorem B21315869 : Blo 1663031 21315869 := bstep (se 3 (by rfl) ⟨3996725, by rfl⟩ : syracuseStep 21315869 = 7993451) B7993451
theorem B108015383 : Blo 1663031 108015383 := bstep (se 1 (by rfl) ⟨81011537, by rfl⟩ : syracuseStep 108015383 = 162023075) B162023075
theorem B19216759 : Blo 1663031 19216759 := bstep (se 1 (by rfl) ⟨14412569, by rfl⟩ : syracuseStep 19216759 = 28825139) B28825139
theorem B4210663 : Blo 1663031 4210663 := bstep (se 1 (by rfl) ⟨3157997, by rfl⟩ : syracuseStep 4210663 = 6315995) B6315995
theorem B72010255 : Blo 1663031 72010255 := bstep (se 1 (by rfl) ⟨54007691, by rfl⟩ : syracuseStep 72010255 = 108015383) B108015383
theorem B5614217 : Blo 1663031 5614217 := bstep (se 2 (by rfl) ⟨2105331, by rfl⟩ : syracuseStep 5614217 = 4210663) B4210663
theorem B14210579 : Blo 1663031 14210579 := bstep (se 1 (by rfl) ⟨10657934, by rfl⟩ : syracuseStep 14210579 = 21315869) B21315869
theorem B25622345 : Blo 1663031 25622345 := bstep (se 2 (by rfl) ⟨9608379, by rfl⟩ : syracuseStep 25622345 = 19216759) B19216759
theorem B96013673 : Blo 1663031 96013673 := bstep (se 2 (by rfl) ⟨36005127, by rfl⟩ : syracuseStep 96013673 = 72010255) B72010255
theorem B9473719 : Blo 1663031 9473719 := bstep (se 1 (by rfl) ⟨7105289, by rfl⟩ : syracuseStep 9473719 = 14210579) B14210579
theorem B68326253 : Blo 1663031 68326253 := bstep (se 3 (by rfl) ⟨12811172, by rfl⟩ : syracuseStep 68326253 = 25622345) B25622345
theorem B3742811 : Blo 1663031 3742811 := bstep (se 1 (by rfl) ⟨2807108, by rfl⟩ : syracuseStep 3742811 = 5614217) B5614217
theorem B45550835 : Blo 1663031 45550835 := bstep (se 1 (by rfl) ⟨34163126, by rfl⟩ : syracuseStep 45550835 = 68326253) B68326253
theorem B2495207 : Blo 1663031 2495207 := bstep (se 1 (by rfl) ⟨1871405, by rfl⟩ : syracuseStep 2495207 = 3742811) B3742811
theorem B64009115 : Blo 1663031 64009115 := bstep (se 1 (by rfl) ⟨48006836, by rfl⟩ : syracuseStep 64009115 = 96013673) B96013673
theorem B12631625 : Blo 1663031 12631625 := bstep (se 2 (by rfl) ⟨4736859, by rfl⟩ : syracuseStep 12631625 = 9473719) B9473719
theorem B1663471 : Blo 1663031 1663471 := bstep (se 1 (by rfl) ⟨1247603, by rfl⟩ : syracuseStep 1663471 = 2495207) B2495207
theorem B42672743 : Blo 1663031 42672743 := bstep (se 1 (by rfl) ⟨32004557, by rfl⟩ : syracuseStep 42672743 = 64009115) B64009115
theorem B30367223 : Blo 1663031 30367223 := bstep (se 1 (by rfl) ⟨22775417, by rfl⟩ : syracuseStep 30367223 = 45550835) B45550835
theorem B8421083 : Blo 1663031 8421083 := bstep (se 1 (by rfl) ⟨6315812, by rfl⟩ : syracuseStep 8421083 = 12631625) B12631625
theorem B20244815 : Blo 1663031 20244815 := bstep (se 1 (by rfl) ⟨15183611, by rfl⟩ : syracuseStep 20244815 = 30367223) B30367223
theorem B5614055 : Blo 1663031 5614055 := bstep (se 1 (by rfl) ⟨4210541, by rfl⟩ : syracuseStep 5614055 = 8421083) B8421083
theorem B28448495 : Blo 1663031 28448495 := bstep (se 1 (by rfl) ⟨21336371, by rfl⟩ : syracuseStep 28448495 = 42672743) B42672743
theorem B18965663 : Blo 1663031 18965663 := bstep (se 1 (by rfl) ⟨14224247, by rfl⟩ : syracuseStep 18965663 = 28448495) B28448495
theorem B13496543 : Blo 1663031 13496543 := bstep (se 1 (by rfl) ⟨10122407, by rfl⟩ : syracuseStep 13496543 = 20244815) B20244815
theorem B3742703 : Blo 1663031 3742703 := bstep (se 1 (by rfl) ⟨2807027, by rfl⟩ : syracuseStep 3742703 = 5614055) B5614055
theorem B8997695 : Blo 1663031 8997695 := bstep (se 1 (by rfl) ⟨6748271, by rfl⟩ : syracuseStep 8997695 = 13496543) B13496543
theorem B12643775 : Blo 1663031 12643775 := bstep (se 1 (by rfl) ⟨9482831, by rfl⟩ : syracuseStep 12643775 = 18965663) B18965663
theorem B2495135 : Blo 1663031 2495135 := bstep (se 1 (by rfl) ⟨1871351, by rfl⟩ : syracuseStep 2495135 = 3742703) B3742703
theorem B1663423 : Blo 1663031 1663423 := bstep (se 1 (by rfl) ⟨1247567, by rfl⟩ : syracuseStep 1663423 = 2495135) B2495135
theorem B5998463 : Blo 1663031 5998463 := bstep (se 1 (by rfl) ⟨4498847, by rfl⟩ : syracuseStep 5998463 = 8997695) B8997695
theorem B8429183 : Blo 1663031 8429183 := bstep (se 1 (by rfl) ⟨6321887, by rfl⟩ : syracuseStep 8429183 = 12643775) B12643775
theorem B3998975 : Blo 1663031 3998975 := bstep (se 1 (by rfl) ⟨2999231, by rfl⟩ : syracuseStep 3998975 = 5998463) B5998463
theorem B5619455 : Blo 1663031 5619455 := bstep (se 1 (by rfl) ⟨4214591, by rfl⟩ : syracuseStep 5619455 = 8429183) B8429183
theorem B3746303 : Blo 1663031 3746303 := bstep (se 1 (by rfl) ⟨2809727, by rfl⟩ : syracuseStep 3746303 = 5619455) B5619455
theorem B10663933 : Blo 1663031 10663933 := bstep (se 3 (by rfl) ⟨1999487, by rfl⟩ : syracuseStep 10663933 = 3998975) B3998975
theorem B14218577 : Blo 1663031 14218577 := bstep (se 2 (by rfl) ⟨5331966, by rfl⟩ : syracuseStep 14218577 = 10663933) B10663933
theorem B2497535 : Blo 1663031 2497535 := bstep (se 1 (by rfl) ⟨1873151, by rfl⟩ : syracuseStep 2497535 = 3746303) B3746303
theorem B9479051 : Blo 1663031 9479051 := bstep (se 1 (by rfl) ⟨7109288, by rfl⟩ : syracuseStep 9479051 = 14218577) B14218577
theorem B1665023 : Blo 1663031 1665023 := bstep (se 1 (by rfl) ⟨1248767, by rfl⟩ : syracuseStep 1665023 = 2497535) B2497535
theorem B6319367 : Blo 1663031 6319367 := bstep (se 1 (by rfl) ⟨4739525, by rfl⟩ : syracuseStep 6319367 = 9479051) B9479051
theorem B4212911 : Blo 1663031 4212911 := bstep (se 1 (by rfl) ⟨3159683, by rfl⟩ : syracuseStep 4212911 = 6319367) B6319367
theorem B2808607 : Blo 1663031 2808607 := bstep (se 1 (by rfl) ⟨2106455, by rfl⟩ : syracuseStep 2808607 = 4212911) B4212911
theorem B3744809 : Blo 1663031 3744809 := bstep (se 2 (by rfl) ⟨1404303, by rfl⟩ : syracuseStep 3744809 = 2808607) B2808607
theorem B2496539 : Blo 1663031 2496539 := bstep (se 1 (by rfl) ⟨1872404, by rfl⟩ : syracuseStep 2496539 = 3744809) B3744809
theorem B1664359 : Blo 1663031 1664359 := bstep (se 1 (by rfl) ⟨1248269, by rfl⟩ : syracuseStep 1664359 = 2496539) B2496539

theorem C0 (j : ℕ) (h1 : 415757 ≤ j) (h2 : j ≤ 416257) : Blo 1663031 (4 * j + 3) := by
  interval_cases j
  · exact B1663031
  · exact B1663035
  · exact B1663039
  · exact B1663043
  · exact B1663047
  · exact B1663051
  · exact B1663055
  · exact B1663059
  · exact B1663063
  · exact B1663067
  · exact B1663071
  · exact B1663075
  · exact B1663079
  · exact B1663083
  · exact B1663087
  · exact B1663091
  · exact B1663095
  · exact B1663099
  · exact B1663103
  · exact B1663107
  · exact B1663111
  · exact B1663115
  · exact B1663119
  · exact B1663123
  · exact B1663127
  · exact B1663131
  · exact B1663135
  · exact B1663139
  · exact B1663143
  · exact B1663147
  · exact B1663151
  · exact B1663155
  · exact B1663159
  · exact B1663163
  · exact B1663167
  · exact B1663171
  · exact B1663175
  · exact B1663179
  · exact B1663183
  · exact B1663187
  · exact B1663191
  · exact B1663195
  · exact B1663199
  · exact B1663203
  · exact B1663207
  · exact B1663211
  · exact B1663215
  · exact B1663219
  · exact B1663223
  · exact B1663227
  · exact B1663231
  · exact B1663235
  · exact B1663239
  · exact B1663243
  · exact B1663247
  · exact B1663251
  · exact B1663255
  · exact B1663259
  · exact B1663263
  · exact B1663267
  · exact B1663271
  · exact B1663275
  · exact B1663279
  · exact B1663283
  · exact B1663287
  · exact B1663291
  · exact B1663295
  · exact B1663299
  · exact B1663303
  · exact B1663307
  · exact B1663311
  · exact B1663315
  · exact B1663319
  · exact B1663323
  · exact B1663327
  · exact B1663331
  · exact B1663335
  · exact B1663339
  · exact B1663343
  · exact B1663347
  · exact B1663351
  · exact B1663355
  · exact B1663359
  · exact B1663363
  · exact B1663367
  · exact B1663371
  · exact B1663375
  · exact B1663379
  · exact B1663383
  · exact B1663387
  · exact B1663391
  · exact B1663395
  · exact B1663399
  · exact B1663403
  · exact B1663407
  · exact B1663411
  · exact B1663415
  · exact B1663419
  · exact B1663423
  · exact B1663427
  · exact B1663431
  · exact B1663435
  · exact B1663439
  · exact B1663443
  · exact B1663447
  · exact B1663451
  · exact B1663455
  · exact B1663459
  · exact B1663463
  · exact B1663467
  · exact B1663471
  · exact B1663475
  · exact B1663479
  · exact B1663483
  · exact B1663487
  · exact B1663491
  · exact B1663495
  · exact B1663499
  · exact B1663503
  · exact B1663507
  · exact B1663511
  · exact B1663515
  · exact B1663519
  · exact B1663523
  · exact B1663527
  · exact B1663531
  · exact B1663535
  · exact B1663539
  · exact B1663543
  · exact B1663547
  · exact B1663551
  · exact B1663555
  · exact B1663559
  · exact B1663563
  · exact B1663567
  · exact B1663571
  · exact B1663575
  · exact B1663579
  · exact B1663583
  · exact B1663587
  · exact B1663591
  · exact B1663595
  · exact B1663599
  · exact B1663603
  · exact B1663607
  · exact B1663611
  · exact B1663615
  · exact B1663619
  · exact B1663623
  · exact B1663627
  · exact B1663631
  · exact B1663635
  · exact B1663639
  · exact B1663643
  · exact B1663647
  · exact B1663651
  · exact B1663655
  · exact B1663659
  · exact B1663663
  · exact B1663667
  · exact B1663671
  · exact B1663675
  · exact B1663679
  · exact B1663683
  · exact B1663687
  · exact B1663691
  · exact B1663695
  · exact B1663699
  · exact B1663703
  · exact B1663707
  · exact B1663711
  · exact B1663715
  · exact B1663719
  · exact B1663723
  · exact B1663727
  · exact B1663731
  · exact B1663735
  · exact B1663739
  · exact B1663743
  · exact B1663747
  · exact B1663751
  · exact B1663755
  · exact B1663759
  · exact B1663763
  · exact B1663767
  · exact B1663771
  · exact B1663775
  · exact B1663779
  · exact B1663783
  · exact B1663787
  · exact B1663791
  · exact B1663795
  · exact B1663799
  · exact B1663803
  · exact B1663807
  · exact B1663811
  · exact B1663815
  · exact B1663819
  · exact B1663823
  · exact B1663827
  · exact B1663831
  · exact B1663835
  · exact B1663839
  · exact B1663843
  · exact B1663847
  · exact B1663851
  · exact B1663855
  · exact B1663859
  · exact B1663863
  · exact B1663867
  · exact B1663871
  · exact B1663875
  · exact B1663879
  · exact B1663883
  · exact B1663887
  · exact B1663891
  · exact B1663895
  · exact B1663899
  · exact B1663903
  · exact B1663907
  · exact B1663911
  · exact B1663915
  · exact B1663919
  · exact B1663923
  · exact B1663927
  · exact B1663931
  · exact B1663935
  · exact B1663939
  · exact B1663943
  · exact B1663947
  · exact B1663951
  · exact B1663955
  · exact B1663959
  · exact B1663963
  · exact B1663967
  · exact B1663971
  · exact B1663975
  · exact B1663979
  · exact B1663983
  · exact B1663987
  · exact B1663991
  · exact B1663995
  · exact B1663999
  · exact B1664003
  · exact B1664007
  · exact B1664011
  · exact B1664015
  · exact B1664019
  · exact B1664023
  · exact B1664027
  · exact B1664031
  · exact B1664035
  · exact B1664039
  · exact B1664043
  · exact B1664047
  · exact B1664051
  · exact B1664055
  · exact B1664059
  · exact B1664063
  · exact B1664067
  · exact B1664071
  · exact B1664075
  · exact B1664079
  · exact B1664083
  · exact B1664087
  · exact B1664091
  · exact B1664095
  · exact B1664099
  · exact B1664103
  · exact B1664107
  · exact B1664111
  · exact B1664115
  · exact B1664119
  · exact B1664123
  · exact B1664127
  · exact B1664131
  · exact B1664135
  · exact B1664139
  · exact B1664143
  · exact B1664147
  · exact B1664151
  · exact B1664155
  · exact B1664159
  · exact B1664163
  · exact B1664167
  · exact B1664171
  · exact B1664175
  · exact B1664179
  · exact B1664183
  · exact B1664187
  · exact B1664191
  · exact B1664195
  · exact B1664199
  · exact B1664203
  · exact B1664207
  · exact B1664211
  · exact B1664215
  · exact B1664219
  · exact B1664223
  · exact B1664227
  · exact B1664231
  · exact B1664235
  · exact B1664239
  · exact B1664243
  · exact B1664247
  · exact B1664251
  · exact B1664255
  · exact B1664259
  · exact B1664263
  · exact B1664267
  · exact B1664271
  · exact B1664275
  · exact B1664279
  · exact B1664283
  · exact B1664287
  · exact B1664291
  · exact B1664295
  · exact B1664299
  · exact B1664303
  · exact B1664307
  · exact B1664311
  · exact B1664315
  · exact B1664319
  · exact B1664323
  · exact B1664327
  · exact B1664331
  · exact B1664335
  · exact B1664339
  · exact B1664343
  · exact B1664347
  · exact B1664351
  · exact B1664355
  · exact B1664359
  · exact B1664363
  · exact B1664367
  · exact B1664371
  · exact B1664375
  · exact B1664379
  · exact B1664383
  · exact B1664387
  · exact B1664391
  · exact B1664395
  · exact B1664399
  · exact B1664403
  · exact B1664407
  · exact B1664411
  · exact B1664415
  · exact B1664419
  · exact B1664423
  · exact B1664427
  · exact B1664431
  · exact B1664435
  · exact B1664439
  · exact B1664443
  · exact B1664447
  · exact B1664451
  · exact B1664455
  · exact B1664459
  · exact B1664463
  · exact B1664467
  · exact B1664471
  · exact B1664475
  · exact B1664479
  · exact B1664483
  · exact B1664487
  · exact B1664491
  · exact B1664495
  · exact B1664499
  · exact B1664503
  · exact B1664507
  · exact B1664511
  · exact B1664515
  · exact B1664519
  · exact B1664523
  · exact B1664527
  · exact B1664531
  · exact B1664535
  · exact B1664539
  · exact B1664543
  · exact B1664547
  · exact B1664551
  · exact B1664555
  · exact B1664559
  · exact B1664563
  · exact B1664567
  · exact B1664571
  · exact B1664575
  · exact B1664579
  · exact B1664583
  · exact B1664587
  · exact B1664591
  · exact B1664595
  · exact B1664599
  · exact B1664603
  · exact B1664607
  · exact B1664611
  · exact B1664615
  · exact B1664619
  · exact B1664623
  · exact B1664627
  · exact B1664631
  · exact B1664635
  · exact B1664639
  · exact B1664643
  · exact B1664647
  · exact B1664651
  · exact B1664655
  · exact B1664659
  · exact B1664663
  · exact B1664667
  · exact B1664671
  · exact B1664675
  · exact B1664679
  · exact B1664683
  · exact B1664687
  · exact B1664691
  · exact B1664695
  · exact B1664699
  · exact B1664703
  · exact B1664707
  · exact B1664711
  · exact B1664715
  · exact B1664719
  · exact B1664723
  · exact B1664727
  · exact B1664731
  · exact B1664735
  · exact B1664739
  · exact B1664743
  · exact B1664747
  · exact B1664751
  · exact B1664755
  · exact B1664759
  · exact B1664763
  · exact B1664767
  · exact B1664771
  · exact B1664775
  · exact B1664779
  · exact B1664783
  · exact B1664787
  · exact B1664791
  · exact B1664795
  · exact B1664799
  · exact B1664803
  · exact B1664807
  · exact B1664811
  · exact B1664815
  · exact B1664819
  · exact B1664823
  · exact B1664827
  · exact B1664831
  · exact B1664835
  · exact B1664839
  · exact B1664843
  · exact B1664847
  · exact B1664851
  · exact B1664855
  · exact B1664859
  · exact B1664863
  · exact B1664867
  · exact B1664871
  · exact B1664875
  · exact B1664879
  · exact B1664883
  · exact B1664887
  · exact B1664891
  · exact B1664895
  · exact B1664899
  · exact B1664903
  · exact B1664907
  · exact B1664911
  · exact B1664915
  · exact B1664919
  · exact B1664923
  · exact B1664927
  · exact B1664931
  · exact B1664935
  · exact B1664939
  · exact B1664943
  · exact B1664947
  · exact B1664951
  · exact B1664955
  · exact B1664959
  · exact B1664963
  · exact B1664967
  · exact B1664971
  · exact B1664975
  · exact B1664979
  · exact B1664983
  · exact B1664987
  · exact B1664991
  · exact B1664995
  · exact B1664999
  · exact B1665003
  · exact B1665007
  · exact B1665011
  · exact B1665015
  · exact B1665019
  · exact B1665023
  · exact B1665027
  · exact B1665031

theorem solution (m : ℕ) (hlo : 1663031 ≤ m) (hhi : m ≤ 1665031) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 415757 ≤ j := by omega
    have hj2 : j ≤ 416257 := by omega
    have hb : Blo 1663031 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
