-- Prove2me | solution 1 for syracuse_descends_range_1040609_1044609
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:24.162505+00:00
-- url     : https://prove2.me/submissions/c9afdbac-e126-4c10-9480-c01dff92acfe

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


theorem B1114273 : Blo 1040609 1114273 := bbase (se 2 (by rfl) ⟨417852, by rfl⟩ : syracuseStep 1114273 = 835705) (by norm_num)
theorem B1114345 : Blo 1040609 1114345 := bbase (se 2 (by rfl) ⟨417879, by rfl⟩ : syracuseStep 1114345 = 835759) (by norm_num)
theorem B2818309 : Blo 1040609 2818309 := bbase (se 4 (by rfl) ⟨264216, by rfl⟩ : syracuseStep 2818309 = 528433) (by norm_num)
theorem B2228485 : Blo 1040609 2228485 := bbase (se 4 (by rfl) ⟨208920, by rfl⟩ : syracuseStep 2228485 = 417841) (by norm_num)
theorem B3965381 : Blo 1040609 3965381 := bbase (se 4 (by rfl) ⟨371754, by rfl⟩ : syracuseStep 3965381 = 743509) (by norm_num)
theorem B1409501 : Blo 1040609 1409501 := bbase (se 3 (by rfl) ⟨264281, by rfl⟩ : syracuseStep 1409501 = 528563) (by norm_num)
theorem B1671749 : Blo 1040609 1671749 := bbase (se 4 (by rfl) ⟨156726, by rfl⟩ : syracuseStep 1671749 = 313453) (by norm_num)
theorem B1114717 : Blo 1040609 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B3572437 : Blo 1040609 3572437 := bbase (se 7 (by rfl) ⟨41864, by rfl⟩ : syracuseStep 3572437 = 83729) (by norm_num)
theorem B3965669 : Blo 1040609 3965669 := bbase (se 4 (by rfl) ⟨371781, by rfl⟩ : syracuseStep 3965669 = 743563) (by norm_num)
theorem B1671941 : Blo 1040609 1671941 := bbase (se 4 (by rfl) ⟨156744, by rfl⟩ : syracuseStep 1671941 = 313489) (by norm_num)
theorem B3801941 : Blo 1040609 3801941 := bbase (se 9 (by rfl) ⟨11138, by rfl⟩ : syracuseStep 3801941 = 22277) (by norm_num)
theorem B15008597 : Blo 1040609 15008597 := bbase (se 9 (by rfl) ⟨43970, by rfl⟩ : syracuseStep 15008597 = 87941) (by norm_num)
theorem B5276501 : Blo 1040609 5276501 := bbase (se 9 (by rfl) ⟨15458, by rfl⟩ : syracuseStep 5276501 = 30917) (by norm_num)
theorem B3343189 : Blo 1040609 3343189 := bbase (se 9 (by rfl) ⟨9794, by rfl⟩ : syracuseStep 3343189 = 19589) (by norm_num)
theorem B1115093 : Blo 1040609 1115093 := bbase (se 7 (by rfl) ⟨13067, by rfl⟩ : syracuseStep 1115093 = 26135) (by norm_num)
theorem B1115165 : Blo 1040609 1115165 := bbase (se 3 (by rfl) ⟨209093, by rfl⟩ : syracuseStep 1115165 = 418187) (by norm_num)
theorem B3343445 : Blo 1040609 3343445 := bbase (se 8 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 3343445 = 39181) (by norm_num)
theorem B2229373 : Blo 1040609 2229373 := bbase (se 3 (by rfl) ⟨418007, by rfl⟩ : syracuseStep 2229373 = 836015) (by norm_num)
theorem B1115353 : Blo 1040609 1115353 := bbase (se 2 (by rfl) ⟨418257, by rfl⟩ : syracuseStep 1115353 = 836515) (by norm_num)
theorem B4818197 : Blo 1040609 4818197 := bbase (se 6 (by rfl) ⟨112926, by rfl⟩ : syracuseStep 4818197 = 225853) (by norm_num)
theorem B5014997 : Blo 1040609 5014997 := bbase (se 7 (by rfl) ⟨58769, by rfl⟩ : syracuseStep 5014997 = 117539) (by norm_num)
theorem B2229869 : Blo 1040609 2229869 := bbase (se 3 (by rfl) ⟨418100, by rfl⟩ : syracuseStep 2229869 = 836201) (by norm_num)
theorem B2819909 : Blo 1040609 2819909 := bbase (se 4 (by rfl) ⟨264366, by rfl⟩ : syracuseStep 2819909 = 528733) (by norm_num)
theorem B1411165 : Blo 1040609 1411165 := bbase (se 3 (by rfl) ⟨264593, by rfl⟩ : syracuseStep 1411165 = 529187) (by norm_num)
theorem B5277797 : Blo 1040609 5277797 := bbase (se 4 (by rfl) ⟨494793, by rfl⟩ : syracuseStep 5277797 = 989587) (by norm_num)
theorem B2230733 : Blo 1040609 2230733 := bbase (se 3 (by rfl) ⟨418262, by rfl⟩ : syracuseStep 2230733 = 836525) (by norm_num)
theorem B1804853 : Blo 1040609 1804853 := bbase (se 5 (by rfl) ⟨84602, by rfl⟩ : syracuseStep 1804853 = 169205) (by norm_num)
theorem B2230877 : Blo 1040609 2230877 := bbase (se 3 (by rfl) ⟨418289, by rfl⟩ : syracuseStep 2230877 = 836579) (by norm_num)
theorem B4459157 : Blo 1040609 4459157 := bbase (se 6 (by rfl) ⟨104511, by rfl⟩ : syracuseStep 4459157 = 209023) (by norm_num)
theorem B5016629 : Blo 1040609 5016629 := bbase (se 5 (by rfl) ⟨235154, by rfl⟩ : syracuseStep 5016629 = 470309) (by norm_num)
theorem B2821205 : Blo 1040609 2821205 := bbase (se 8 (by rfl) ⟨16530, by rfl⟩ : syracuseStep 2821205 = 33061) (by norm_num)
theorem B9506069 : Blo 1040609 9506069 := bbase (se 6 (by rfl) ⟨222798, by rfl⟩ : syracuseStep 9506069 = 445597) (by norm_num)
theorem B5279093 : Blo 1040609 5279093 := bbase (se 5 (by rfl) ⟨247457, by rfl⟩ : syracuseStep 5279093 = 494915) (by norm_num)
theorem B2035109 : Blo 1040609 2035109 := bbase (se 4 (by rfl) ⟨190791, by rfl⟩ : syracuseStep 2035109 = 381583) (by norm_num)
theorem B4754933 : Blo 1040609 4754933 := bbase (se 5 (by rfl) ⟨222887, by rfl⟩ : syracuseStep 4754933 = 445775) (by norm_num)
theorem B3346213 : Blo 1040609 3346213 := bbase (se 4 (by rfl) ⟨313707, by rfl⟩ : syracuseStep 3346213 = 627415) (by norm_num)
theorem B5639989 : Blo 1040609 5639989 := bbase (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) (by norm_num)
theorem B1806229 : Blo 1040609 1806229 := bbase (se 6 (by rfl) ⟨42333, by rfl⟩ : syracuseStep 1806229 = 84667) (by norm_num)
theorem B4460933 : Blo 1040609 4460933 := bbase (se 4 (by rfl) ⟨418212, by rfl⟩ : syracuseStep 4460933 = 836425) (by norm_num)
theorem B1905061 : Blo 1040609 1905061 := bbase (se 4 (by rfl) ⟨178599, by rfl⟩ : syracuseStep 1905061 = 357199) (by norm_num)
theorem B5345909 : Blo 1040609 5345909 := bbase (se 5 (by rfl) ⟨250589, by rfl⟩ : syracuseStep 5345909 = 501179) (by norm_num)
theorem B5280389 : Blo 1040609 5280389 := bbase (se 4 (by rfl) ⟨495036, by rfl⟩ : syracuseStep 5280389 = 990073) (by norm_num)
theorem B5083829 : Blo 1040609 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B1250597 : Blo 1040609 1250597 := bbase (se 4 (by rfl) ⟨117243, by rfl⟩ : syracuseStep 1250597 = 234487) (by norm_num)
theorem B4461925 : Blo 1040609 4461925 := bbase (se 4 (by rfl) ⟨418305, by rfl⟩ : syracuseStep 4461925 = 836611) (by norm_num)
theorem B5641589 : Blo 1040609 5641589 := bbase (se 5 (by rfl) ⟨264449, by rfl⟩ : syracuseStep 5641589 = 528899) (by norm_num)
theorem B1250905 : Blo 1040609 1250905 := bbase (se 2 (by rfl) ⟨469089, by rfl⟩ : syracuseStep 1250905 = 938179) (by norm_num)
theorem B5936885 : Blo 1040609 5936885 := bbase (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) (by norm_num)
theorem B3512213 : Blo 1040609 3512213 := bbase (se 6 (by rfl) ⟨82317, by rfl⟩ : syracuseStep 3512213 = 164635) (by norm_num)
theorem B5281685 : Blo 1040609 5281685 := bbase (se 6 (by rfl) ⟨123789, by rfl⟩ : syracuseStep 5281685 = 247579) (by norm_num)
theorem B1087417 : Blo 1040609 1087417 := bbase (se 2 (by rfl) ⟨407781, by rfl⟩ : syracuseStep 1087417 = 815563) (by norm_num)
theorem B1251289 : Blo 1040609 1251289 := bbase (se 2 (by rfl) ⟨469233, by rfl⟩ : syracuseStep 1251289 = 938467) (by norm_num)
theorem B1251293 : Blo 1040609 1251293 := bbase (se 3 (by rfl) ⟨234617, by rfl⟩ : syracuseStep 1251293 = 469235) (by norm_num)
theorem B12687637 : Blo 1040609 12687637 := bbase (se 6 (by rfl) ⟨297366, by rfl⟩ : syracuseStep 12687637 = 594733) (by norm_num)
theorem B1317161 : Blo 1040609 1317161 := bbase (se 2 (by rfl) ⟨493935, by rfl⟩ : syracuseStep 1317161 = 987871) (by norm_num)
theorem B3512645 : Blo 1040609 3512645 := bbase (se 4 (by rfl) ⟨329310, by rfl⟩ : syracuseStep 3512645 = 658621) (by norm_num)
theorem B1317217 : Blo 1040609 1317217 := bbase (se 2 (by rfl) ⟨493956, by rfl⟩ : syracuseStep 1317217 = 987913) (by norm_num)
theorem B1251697 : Blo 1040609 1251697 := bbase (se 2 (by rfl) ⟨469386, by rfl⟩ : syracuseStep 1251697 = 938773) (by norm_num)
theorem B1317313 : Blo 1040609 1317313 := bbase (se 2 (by rfl) ⟨493992, by rfl⟩ : syracuseStep 1317313 = 987985) (by norm_num)
theorem B1055333 : Blo 1040609 1055333 := bbase (se 4 (by rfl) ⟨98937, by rfl⟩ : syracuseStep 1055333 = 197875) (by norm_num)
theorem B1317485 : Blo 1040609 1317485 := bbase (se 3 (by rfl) ⟨247028, by rfl⟩ : syracuseStep 1317485 = 494057) (by norm_num)
theorem B1055341 : Blo 1040609 1055341 := bbase (se 3 (by rfl) ⟨197876, by rfl⟩ : syracuseStep 1055341 = 395753) (by norm_num)
theorem B1317541 : Blo 1040609 1317541 := bbase (se 4 (by rfl) ⟨123519, by rfl⟩ : syracuseStep 1317541 = 247039) (by norm_num)
theorem B3513077 : Blo 1040609 3513077 := bbase (se 5 (by rfl) ⟨164675, by rfl⟩ : syracuseStep 3513077 = 329351) (by norm_num)
theorem B1317637 : Blo 1040609 1317637 := bbase (se 4 (by rfl) ⟨123528, by rfl⟩ : syracuseStep 1317637 = 247057) (by norm_num)
theorem B5938069 : Blo 1040609 5938069 := bbase (se 6 (by rfl) ⟨139173, by rfl⟩ : syracuseStep 5938069 = 278347) (by norm_num)
theorem B1317809 : Blo 1040609 1317809 := bbase (se 2 (by rfl) ⟨494178, by rfl⟩ : syracuseStep 1317809 = 988357) (by norm_num)
theorem B1317865 : Blo 1040609 1317865 := bbase (se 2 (by rfl) ⟨494199, by rfl⟩ : syracuseStep 1317865 = 988399) (by norm_num)
theorem B1317961 : Blo 1040609 1317961 := bbase (se 2 (by rfl) ⟨494235, by rfl⟩ : syracuseStep 1317961 = 988471) (by norm_num)
theorem B1055873 : Blo 1040609 1055873 := bbase (se 2 (by rfl) ⟨395952, by rfl⟩ : syracuseStep 1055873 = 791905) (by norm_num)
theorem B3513509 : Blo 1040609 3513509 := bbase (se 4 (by rfl) ⟨329391, by rfl⟩ : syracuseStep 3513509 = 658783) (by norm_num)
theorem B5282981 : Blo 1040609 5282981 := bbase (se 4 (by rfl) ⟨495279, by rfl⟩ : syracuseStep 5282981 = 990559) (by norm_num)
theorem B2170037 : Blo 1040609 2170037 := bbase (se 5 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 2170037 = 203441) (by norm_num)
theorem B1318133 : Blo 1040609 1318133 := bbase (se 5 (by rfl) ⟨61787, by rfl⟩ : syracuseStep 1318133 = 123575) (by norm_num)
theorem B1481989 : Blo 1040609 1481989 := bbase (se 4 (by rfl) ⟨138936, by rfl⟩ : syracuseStep 1481989 = 277873) (by norm_num)
theorem B1318189 : Blo 1040609 1318189 := bbase (se 3 (by rfl) ⟨247160, by rfl⟩ : syracuseStep 1318189 = 494321) (by norm_num)
theorem B1318285 : Blo 1040609 1318285 := bbase (se 3 (by rfl) ⟨247178, by rfl⟩ : syracuseStep 1318285 = 494357) (by norm_num)
theorem B1056265 : Blo 1040609 1056265 := bbase (se 2 (by rfl) ⟨396099, by rfl⟩ : syracuseStep 1056265 = 792199) (by norm_num)
theorem B7904789 : Blo 1040609 7904789 := bbase (se 6 (by rfl) ⟨185268, by rfl⟩ : syracuseStep 7904789 = 370537) (by norm_num)
theorem B1318457 : Blo 1040609 1318457 := bbase (se 2 (by rfl) ⟨494421, by rfl⟩ : syracuseStep 1318457 = 988843) (by norm_num)
theorem B3513941 : Blo 1040609 3513941 := bbase (se 8 (by rfl) ⟨20589, by rfl⟩ : syracuseStep 3513941 = 41179) (by norm_num)
theorem B1318513 : Blo 1040609 1318513 := bbase (se 2 (by rfl) ⟨494442, by rfl⟩ : syracuseStep 1318513 = 988885) (by norm_num)
theorem B1318609 : Blo 1040609 1318609 := bbase (se 2 (by rfl) ⟨494478, by rfl⟩ : syracuseStep 1318609 = 988957) (by norm_num)
theorem B1253081 : Blo 1040609 1253081 := bbase (se 2 (by rfl) ⟨469905, by rfl⟩ : syracuseStep 1253081 = 939811) (by norm_num)
theorem B1187569 : Blo 1040609 1187569 := bbase (se 2 (by rfl) ⟨445338, by rfl⟩ : syracuseStep 1187569 = 890677) (by norm_num)
theorem B32481109 : Blo 1040609 32481109 := bbase (se 9 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 32481109 = 190319) (by norm_num)
theorem B1482581 : Blo 1040609 1482581 := bbase (se 9 (by rfl) ⟨4343, by rfl⟩ : syracuseStep 1482581 = 8687) (by norm_num)
theorem B1318781 : Blo 1040609 1318781 := bbase (se 3 (by rfl) ⟨247271, by rfl⟩ : syracuseStep 1318781 = 494543) (by norm_num)
theorem B1482661 : Blo 1040609 1482661 := bbase (se 4 (by rfl) ⟨138999, by rfl⟩ : syracuseStep 1482661 = 277999) (by norm_num)
theorem B1318837 : Blo 1040609 1318837 := bbase (se 5 (by rfl) ⟨61820, by rfl⟩ : syracuseStep 1318837 = 123641) (by norm_num)
theorem B1253341 : Blo 1040609 1253341 := bbase (se 3 (by rfl) ⟨235001, by rfl⟩ : syracuseStep 1253341 = 470003) (by norm_num)
theorem B3514373 : Blo 1040609 3514373 := bbase (se 4 (by rfl) ⟨329472, by rfl⟩ : syracuseStep 3514373 = 658945) (by norm_num)
theorem B1253389 : Blo 1040609 1253389 := bbase (se 3 (by rfl) ⟨235010, by rfl⟩ : syracuseStep 1253389 = 470021) (by norm_num)
theorem B1318933 : Blo 1040609 1318933 := bbase (se 6 (by rfl) ⟨30912, by rfl⟩ : syracuseStep 1318933 = 61825) (by norm_num)
theorem B1482781 : Blo 1040609 1482781 := bbase (se 3 (by rfl) ⟨278021, by rfl⟩ : syracuseStep 1482781 = 556043) (by norm_num)
theorem B1187893 : Blo 1040609 1187893 := bbase (se 5 (by rfl) ⟨55682, by rfl⟩ : syracuseStep 1187893 = 111365) (by norm_num)
theorem B1482877 : Blo 1040609 1482877 := bbase (se 3 (by rfl) ⟨278039, by rfl⟩ : syracuseStep 1482877 = 556079) (by norm_num)
theorem B1319105 : Blo 1040609 1319105 := bbase (se 2 (by rfl) ⟨494664, by rfl⟩ : syracuseStep 1319105 = 989329) (by norm_num)
theorem B3612869 : Blo 1040609 3612869 := bbase (se 4 (by rfl) ⟨338706, by rfl⟩ : syracuseStep 3612869 = 677413) (by norm_num)
theorem B10035413 : Blo 1040609 10035413 := bbase (se 7 (by rfl) ⟨117602, by rfl⟩ : syracuseStep 10035413 = 235205) (by norm_num)
theorem B1319161 : Blo 1040609 1319161 := bbase (se 2 (by rfl) ⟨494685, by rfl⟩ : syracuseStep 1319161 = 989371) (by norm_num)
theorem B33497429 : Blo 1040609 33497429 := bbase (se 10 (by rfl) ⟨49068, by rfl⟩ : syracuseStep 33497429 = 98137) (by norm_num)
theorem B1319257 : Blo 1040609 1319257 := bbase (se 2 (by rfl) ⟨494721, by rfl⟩ : syracuseStep 1319257 = 989443) (by norm_num)
theorem B3514805 : Blo 1040609 3514805 := bbase (se 5 (by rfl) ⟨164756, by rfl⟩ : syracuseStep 3514805 = 329513) (by norm_num)
theorem B5284277 : Blo 1040609 5284277 := bbase (se 5 (by rfl) ⟨247700, by rfl⟩ : syracuseStep 5284277 = 495401) (by norm_num)
theorem B1876421 : Blo 1040609 1876421 := bbase (se 4 (by rfl) ⟨175914, by rfl⟩ : syracuseStep 1876421 = 351829) (by norm_num)
theorem B1319429 : Blo 1040609 1319429 := bbase (se 4 (by rfl) ⟨123696, by rfl⟩ : syracuseStep 1319429 = 247393) (by norm_num)
theorem B1319485 : Blo 1040609 1319485 := bbase (se 3 (by rfl) ⟨247403, by rfl⟩ : syracuseStep 1319485 = 494807) (by norm_num)
theorem B1188445 : Blo 1040609 1188445 := bbase (se 3 (by rfl) ⟨222833, by rfl⟩ : syracuseStep 1188445 = 445667) (by norm_num)
theorem B1057385 : Blo 1040609 1057385 := bbase (se 2 (by rfl) ⟨396519, by rfl⟩ : syracuseStep 1057385 = 793039) (by norm_num)
theorem B1483373 : Blo 1040609 1483373 := bbase (se 3 (by rfl) ⟨278132, by rfl⟩ : syracuseStep 1483373 = 556265) (by norm_num)
theorem B1057433 : Blo 1040609 1057433 := bbase (se 2 (by rfl) ⟨396537, by rfl⟩ : syracuseStep 1057433 = 793075) (by norm_num)
theorem B1319581 : Blo 1040609 1319581 := bbase (se 3 (by rfl) ⟨247421, by rfl⟩ : syracuseStep 1319581 = 494843) (by norm_num)
theorem B1254061 : Blo 1040609 1254061 := bbase (se 3 (by rfl) ⟨235136, by rfl⟩ : syracuseStep 1254061 = 470273) (by norm_num)
theorem B1319753 : Blo 1040609 1319753 := bbase (se 2 (by rfl) ⟨494907, by rfl⟩ : syracuseStep 1319753 = 989815) (by norm_num)
theorem B5940053 : Blo 1040609 5940053 := bbase (se 9 (by rfl) ⟨17402, by rfl⟩ : syracuseStep 5940053 = 34805) (by norm_num)
theorem B3515237 : Blo 1040609 3515237 := bbase (se 4 (by rfl) ⟨329553, by rfl⟩ : syracuseStep 3515237 = 659107) (by norm_num)
theorem B1319809 : Blo 1040609 1319809 := bbase (se 2 (by rfl) ⟨494928, by rfl⟩ : syracuseStep 1319809 = 989857) (by norm_num)
theorem B1319905 : Blo 1040609 1319905 := bbase (se 2 (by rfl) ⟨494964, by rfl⟩ : syracuseStep 1319905 = 989929) (by norm_num)
theorem B1320077 : Blo 1040609 1320077 := bbase (se 3 (by rfl) ⟨247514, by rfl⟩ : syracuseStep 1320077 = 495029) (by norm_num)
theorem B1483925 : Blo 1040609 1483925 := bbase (se 6 (by rfl) ⟨34779, by rfl⟩ : syracuseStep 1483925 = 69559) (by norm_num)
theorem B1320133 : Blo 1040609 1320133 := bbase (se 4 (by rfl) ⟨123762, by rfl⟩ : syracuseStep 1320133 = 247525) (by norm_num)
theorem B1582301 : Blo 1040609 1582301 := bbase (se 3 (by rfl) ⟨296681, by rfl⟩ : syracuseStep 1582301 = 593363) (by norm_num)
theorem B10003733 : Blo 1040609 10003733 := bbase (se 6 (by rfl) ⟨234462, by rfl⟩ : syracuseStep 10003733 = 468925) (by norm_num)
theorem B3515669 : Blo 1040609 3515669 := bbase (se 6 (by rfl) ⟨82398, by rfl⟩ : syracuseStep 3515669 = 164797) (by norm_num)
theorem B1320229 : Blo 1040609 1320229 := bbase (se 4 (by rfl) ⟨123771, by rfl⟩ : syracuseStep 1320229 = 247543) (by norm_num)
theorem B1320401 : Blo 1040609 1320401 := bbase (se 2 (by rfl) ⟨495150, by rfl⟩ : syracuseStep 1320401 = 990301) (by norm_num)
theorem B1975765 : Blo 1040609 1975765 := bbase (se 7 (by rfl) ⟨23153, by rfl⟩ : syracuseStep 1975765 = 46307) (by norm_num)
theorem B1320457 : Blo 1040609 1320457 := bbase (se 2 (by rfl) ⟨495171, by rfl⟩ : syracuseStep 1320457 = 990343) (by norm_num)
theorem B1975909 : Blo 1040609 1975909 := bbase (se 4 (by rfl) ⟨185241, by rfl⟩ : syracuseStep 1975909 = 370483) (by norm_num)
theorem B1320553 : Blo 1040609 1320553 := bbase (se 2 (by rfl) ⟨495207, by rfl⟩ : syracuseStep 1320553 = 990415) (by norm_num)
theorem B1189513 : Blo 1040609 1189513 := bbase (se 2 (by rfl) ⟨446067, by rfl⟩ : syracuseStep 1189513 = 892135) (by norm_num)
theorem B3516101 : Blo 1040609 3516101 := bbase (se 4 (by rfl) ⟨329634, by rfl⟩ : syracuseStep 3516101 = 659269) (by norm_num)
theorem B5285573 : Blo 1040609 5285573 := bbase (se 4 (by rfl) ⟨495522, by rfl⟩ : syracuseStep 5285573 = 991045) (by norm_num)
theorem B1189585 : Blo 1040609 1189585 := bbase (se 2 (by rfl) ⟨446094, by rfl⟩ : syracuseStep 1189585 = 892189) (by norm_num)
theorem B1976069 : Blo 1040609 1976069 := bbase (se 4 (by rfl) ⟨185256, by rfl⟩ : syracuseStep 1976069 = 370513) (by norm_num)
theorem B1320725 : Blo 1040609 1320725 := bbase (se 6 (by rfl) ⟨30954, by rfl⟩ : syracuseStep 1320725 = 61909) (by norm_num)
theorem B1320781 : Blo 1040609 1320781 := bbase (se 3 (by rfl) ⟨247646, by rfl⟩ : syracuseStep 1320781 = 495293) (by norm_num)
theorem B1484677 : Blo 1040609 1484677 := bbase (se 4 (by rfl) ⟨139188, by rfl⟩ : syracuseStep 1484677 = 278377) (by norm_num)
theorem B1976213 : Blo 1040609 1976213 := bbase (se 6 (by rfl) ⟨46317, by rfl⟩ : syracuseStep 1976213 = 92635) (by norm_num)
theorem B1320877 : Blo 1040609 1320877 := bbase (se 3 (by rfl) ⟨247664, by rfl⟩ : syracuseStep 1320877 = 495329) (by norm_num)
theorem B1189937 : Blo 1040609 1189937 := bbase (se 2 (by rfl) ⟨446226, by rfl⟩ : syracuseStep 1189937 = 892453) (by norm_num)
theorem B1321049 : Blo 1040609 1321049 := bbase (se 2 (by rfl) ⟨495393, by rfl⟩ : syracuseStep 1321049 = 990787) (by norm_num)
theorem B3516533 : Blo 1040609 3516533 := bbase (se 5 (by rfl) ⟨164837, by rfl⟩ : syracuseStep 3516533 = 329675) (by norm_num)
theorem B2500733 : Blo 1040609 2500733 := bbase (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) (by norm_num)
theorem B2500741 : Blo 1040609 2500741 := bbase (se 4 (by rfl) ⟨234444, by rfl⟩ : syracuseStep 2500741 = 468889) (by norm_num)
theorem B1321105 : Blo 1040609 1321105 := bbase (se 2 (by rfl) ⟨495414, by rfl⟩ : syracuseStep 1321105 = 990829) (by norm_num)
theorem B1976501 : Blo 1040609 1976501 := bbase (se 5 (by rfl) ⟨92648, by rfl⟩ : syracuseStep 1976501 = 185297) (by norm_num)
theorem B1321201 : Blo 1040609 1321201 := bbase (se 2 (by rfl) ⟨495450, by rfl⟩ : syracuseStep 1321201 = 990901) (by norm_num)
theorem B1780013 : Blo 1040609 1780013 := bbase (se 3 (by rfl) ⟨333752, by rfl⟩ : syracuseStep 1780013 = 667505) (by norm_num)
theorem B1976653 : Blo 1040609 1976653 := bbase (se 3 (by rfl) ⟨370622, by rfl⟩ : syracuseStep 1976653 = 741245) (by norm_num)
theorem B1321373 : Blo 1040609 1321373 := bbase (se 3 (by rfl) ⟨247757, by rfl⟩ : syracuseStep 1321373 = 495515) (by norm_num)
theorem B1321429 : Blo 1040609 1321429 := bbase (se 7 (by rfl) ⟨15485, by rfl⟩ : syracuseStep 1321429 = 30971) (by norm_num)
theorem B3516965 : Blo 1040609 3516965 := bbase (se 4 (by rfl) ⟨329715, by rfl⟩ : syracuseStep 3516965 = 659431) (by norm_num)
theorem B1321525 : Blo 1040609 1321525 := bbase (se 5 (by rfl) ⟨61946, by rfl⟩ : syracuseStep 1321525 = 123893) (by norm_num)
theorem B1976957 : Blo 1040609 1976957 := bbase (se 3 (by rfl) ⟨370679, by rfl⟩ : syracuseStep 1976957 = 741359) (by norm_num)
theorem B1485469 : Blo 1040609 1485469 := bbase (se 3 (by rfl) ⟨278525, by rfl⟩ : syracuseStep 1485469 = 557051) (by norm_num)
theorem B1288921 : Blo 1040609 1288921 := bbase (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) (by norm_num)
theorem B1321697 : Blo 1040609 1321697 := bbase (se 2 (by rfl) ⟨495636, by rfl⟩ : syracuseStep 1321697 = 991273) (by norm_num)
theorem B1321753 : Blo 1040609 1321753 := bbase (se 2 (by rfl) ⟨495657, by rfl⟩ : syracuseStep 1321753 = 991315) (by norm_num)
theorem B2009933 : Blo 1040609 2009933 := bbase (se 3 (by rfl) ⟨376862, by rfl⟩ : syracuseStep 2009933 = 753725) (by norm_num)
theorem B1321849 : Blo 1040609 1321849 := bbase (se 2 (by rfl) ⟨495693, by rfl⟩ : syracuseStep 1321849 = 991387) (by norm_num)
theorem B8924053 : Blo 1040609 8924053 := bbase (se 6 (by rfl) ⟨209157, by rfl⟩ : syracuseStep 8924053 = 418315) (by norm_num)
theorem B3517397 : Blo 1040609 3517397 := bbase (se 7 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 3517397 = 82439) (by norm_num)
theorem B5286869 : Blo 1040609 5286869 := bbase (se 7 (by rfl) ⟨61955, by rfl⟩ : syracuseStep 5286869 = 123911) (by norm_num)
theorem B1485805 : Blo 1040609 1485805 := bbase (se 3 (by rfl) ⟨278588, by rfl⟩ : syracuseStep 1485805 = 557177) (by norm_num)
theorem B5942261 : Blo 1040609 5942261 := bbase (se 5 (by rfl) ⟨278543, by rfl⟩ : syracuseStep 5942261 = 557087) (by norm_num)
theorem B1190909 : Blo 1040609 1190909 := bbase (se 3 (by rfl) ⟨223295, by rfl⟩ : syracuseStep 1190909 = 446591) (by norm_num)
theorem B1322021 : Blo 1040609 1322021 := bbase (se 4 (by rfl) ⟨123939, by rfl⟩ : syracuseStep 1322021 = 247879) (by norm_num)
theorem B1322077 : Blo 1040609 1322077 := bbase (se 3 (by rfl) ⟨247889, by rfl⟩ : syracuseStep 1322077 = 495779) (by norm_num)
theorem B2501741 : Blo 1040609 2501741 := bbase (se 3 (by rfl) ⟨469076, by rfl⟩ : syracuseStep 2501741 = 938153) (by norm_num)
theorem B1486021 : Blo 1040609 1486021 := bbase (se 4 (by rfl) ⟨139314, by rfl⟩ : syracuseStep 1486021 = 278629) (by norm_num)
theorem B1977709 : Blo 1040609 1977709 := bbase (se 3 (by rfl) ⟨370820, by rfl⟩ : syracuseStep 1977709 = 741641) (by norm_num)
theorem B3517829 : Blo 1040609 3517829 := bbase (se 4 (by rfl) ⟨329796, by rfl⟩ : syracuseStep 3517829 = 659593) (by norm_num)
theorem B9514421 : Blo 1040609 9514421 := bbase (se 5 (by rfl) ⟨445988, by rfl⟩ : syracuseStep 9514421 = 891977) (by norm_num)
theorem B1977853 : Blo 1040609 1977853 := bbase (se 3 (by rfl) ⟨370847, by rfl⟩ : syracuseStep 1977853 = 741695) (by norm_num)
theorem B1486397 : Blo 1040609 1486397 := bbase (se 3 (by rfl) ⟨278699, by rfl⟩ : syracuseStep 1486397 = 557399) (by norm_num)
theorem B1978013 : Blo 1040609 1978013 := bbase (se 3 (by rfl) ⟨370877, by rfl⟩ : syracuseStep 1978013 = 741755) (by norm_num)
theorem B1978157 : Blo 1040609 1978157 := bbase (se 3 (by rfl) ⟨370904, by rfl⟩ : syracuseStep 1978157 = 741809) (by norm_num)
theorem B3518261 : Blo 1040609 3518261 := bbase (se 5 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 3518261 = 329837) (by norm_num)
theorem B2502509 : Blo 1040609 2502509 := bbase (se 3 (by rfl) ⟨469220, by rfl⟩ : syracuseStep 2502509 = 938441) (by norm_num)
theorem B1978445 : Blo 1040609 1978445 := bbase (se 3 (by rfl) ⟨370958, by rfl⟩ : syracuseStep 1978445 = 741917) (by norm_num)
theorem B1978597 : Blo 1040609 1978597 := bbase (se 4 (by rfl) ⟨185493, by rfl⟩ : syracuseStep 1978597 = 370987) (by norm_num)
theorem B3518693 : Blo 1040609 3518693 := bbase (se 4 (by rfl) ⟨329877, by rfl⟩ : syracuseStep 3518693 = 659755) (by norm_num)
theorem B5288165 : Blo 1040609 5288165 := bbase (se 4 (by rfl) ⟨495765, by rfl⟩ : syracuseStep 5288165 = 991531) (by norm_num)
theorem B1585469 : Blo 1040609 1585469 := bbase (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) (by norm_num)
theorem B1880509 : Blo 1040609 1880509 := bbase (se 3 (by rfl) ⟨352595, by rfl⟩ : syracuseStep 1880509 = 705191) (by norm_num)
theorem B1782229 : Blo 1040609 1782229 := bbase (se 7 (by rfl) ⟨20885, by rfl⟩ : syracuseStep 1782229 = 41771) (by norm_num)
theorem B2634221 : Blo 1040609 2634221 := bbase (se 3 (by rfl) ⟨493916, by rfl⟩ : syracuseStep 2634221 = 987833) (by norm_num)
theorem B1978901 : Blo 1040609 1978901 := bbase (se 6 (by rfl) ⟨46380, by rfl⟩ : syracuseStep 1978901 = 92761) (by norm_num)
theorem B3519125 : Blo 1040609 3519125 := bbase (se 6 (by rfl) ⟨82479, by rfl⟩ : syracuseStep 3519125 = 164959) (by norm_num)
theorem B2634565 : Blo 1040609 2634565 := bbase (se 4 (by rfl) ⟨246990, by rfl⟩ : syracuseStep 2634565 = 493981) (by norm_num)
theorem B2634677 : Blo 1040609 2634677 := bbase (se 5 (by rfl) ⟨123500, by rfl⟩ : syracuseStep 2634677 = 247001) (by norm_num)
theorem B9286613 : Blo 1040609 9286613 := bbase (se 7 (by rfl) ⟨108827, by rfl⟩ : syracuseStep 9286613 = 217655) (by norm_num)
theorem B1782845 : Blo 1040609 1782845 := bbase (se 3 (by rfl) ⟨334283, by rfl⟩ : syracuseStep 1782845 = 668567) (by norm_num)
theorem B1881149 : Blo 1040609 1881149 := bbase (se 3 (by rfl) ⟨352715, by rfl⟩ : syracuseStep 1881149 = 705431) (by norm_num)
theorem B3519557 : Blo 1040609 3519557 := bbase (se 4 (by rfl) ⟨329958, by rfl⟩ : syracuseStep 3519557 = 659917) (by norm_num)
theorem B2634869 : Blo 1040609 2634869 := bbase (se 5 (by rfl) ⟨123509, by rfl⟩ : syracuseStep 2634869 = 247019) (by norm_num)
theorem B1979653 : Blo 1040609 1979653 := bbase (se 4 (by rfl) ⟨185592, by rfl⟩ : syracuseStep 1979653 = 371185) (by norm_num)
theorem B1979797 : Blo 1040609 1979797 := bbase (se 6 (by rfl) ⟨46401, by rfl⟩ : syracuseStep 1979797 = 92803) (by norm_num)
theorem B2635213 : Blo 1040609 2635213 := bbase (se 3 (by rfl) ⟨494102, by rfl⟩ : syracuseStep 2635213 = 988205) (by norm_num)
theorem B2110925 : Blo 1040609 2110925 := bbase (se 3 (by rfl) ⟨395798, by rfl⟩ : syracuseStep 2110925 = 791597) (by norm_num)
theorem B3519989 : Blo 1040609 3519989 := bbase (se 5 (by rfl) ⟨164999, by rfl⟩ : syracuseStep 3519989 = 329999) (by norm_num)
theorem B1979957 : Blo 1040609 1979957 := bbase (se 5 (by rfl) ⟨92810, by rfl⟩ : syracuseStep 1979957 = 185621) (by norm_num)
theorem B2635325 : Blo 1040609 2635325 := bbase (se 3 (by rfl) ⟨494123, by rfl⟩ : syracuseStep 2635325 = 988247) (by norm_num)
theorem B2504317 : Blo 1040609 2504317 := bbase (se 3 (by rfl) ⟨469559, by rfl⟩ : syracuseStep 2504317 = 939119) (by norm_num)
theorem B10303157 : Blo 1040609 10303157 := bbase (se 5 (by rfl) ⟨482960, by rfl⟩ : syracuseStep 10303157 = 965921) (by norm_num)
theorem B1128125 : Blo 1040609 1128125 := bbase (se 3 (by rfl) ⟨211523, by rfl⟩ : syracuseStep 1128125 = 423047) (by norm_num)
theorem B1980101 : Blo 1040609 1980101 := bbase (se 4 (by rfl) ⟨185634, by rfl⟩ : syracuseStep 1980101 = 371269) (by norm_num)
theorem B1586893 : Blo 1040609 1586893 := bbase (se 3 (by rfl) ⟨297542, by rfl⟩ : syracuseStep 1586893 = 595085) (by norm_num)
theorem B2635517 : Blo 1040609 2635517 := bbase (se 3 (by rfl) ⟨494159, by rfl⟩ : syracuseStep 2635517 = 988319) (by norm_num)
theorem B1881893 : Blo 1040609 1881893 := bbase (se 4 (by rfl) ⟨176427, by rfl⟩ : syracuseStep 1881893 = 352855) (by norm_num)
theorem B1718101 : Blo 1040609 1718101 := bbase (se 9 (by rfl) ⟨5033, by rfl⟩ : syracuseStep 1718101 = 10067) (by norm_num)
theorem B2963317 : Blo 1040609 2963317 := bbase (se 5 (by rfl) ⟨138905, by rfl⟩ : syracuseStep 2963317 = 277811) (by norm_num)
theorem B3520421 : Blo 1040609 3520421 := bbase (se 4 (by rfl) ⟨330039, by rfl⟩ : syracuseStep 3520421 = 660079) (by norm_num)
theorem B1980389 : Blo 1040609 1980389 := bbase (se 4 (by rfl) ⟨185661, by rfl⟩ : syracuseStep 1980389 = 371323) (by norm_num)
theorem B1128493 : Blo 1040609 1128493 := bbase (se 3 (by rfl) ⟨211592, by rfl⟩ : syracuseStep 1128493 = 423185) (by norm_num)
theorem B2635861 : Blo 1040609 2635861 := bbase (se 8 (by rfl) ⟨15444, by rfl⟩ : syracuseStep 2635861 = 30889) (by norm_num)
theorem B1587317 : Blo 1040609 1587317 := bbase (se 5 (by rfl) ⟨74405, by rfl⟩ : syracuseStep 1587317 = 148811) (by norm_num)
theorem B1980541 : Blo 1040609 1980541 := bbase (se 3 (by rfl) ⟨371351, by rfl⟩ : syracuseStep 1980541 = 742703) (by norm_num)
theorem B2504837 : Blo 1040609 2504837 := bbase (se 4 (by rfl) ⟨234828, by rfl⟩ : syracuseStep 2504837 = 469657) (by norm_num)
theorem B2635973 : Blo 1040609 2635973 := bbase (se 4 (by rfl) ⟨247122, by rfl⟩ : syracuseStep 2635973 = 494245) (by norm_num)
theorem B3520853 : Blo 1040609 3520853 := bbase (se 10 (by rfl) ⟨5157, by rfl⟩ : syracuseStep 3520853 = 10315) (by norm_num)
theorem B2636165 : Blo 1040609 2636165 := bbase (se 4 (by rfl) ⟨247140, by rfl⟩ : syracuseStep 2636165 = 494281) (by norm_num)
theorem B1980845 : Blo 1040609 1980845 := bbase (se 3 (by rfl) ⟨371408, by rfl⟩ : syracuseStep 1980845 = 742817) (by norm_num)
theorem B2505221 : Blo 1040609 2505221 := bbase (se 4 (by rfl) ⟨234864, by rfl⟩ : syracuseStep 2505221 = 469729) (by norm_num)
theorem B2341421 : Blo 1040609 2341421 := bbase (se 3 (by rfl) ⟨439016, by rfl⟩ : syracuseStep 2341421 = 878033) (by norm_num)
theorem B1587757 : Blo 1040609 1587757 := bbase (se 3 (by rfl) ⟨297704, by rfl⟩ : syracuseStep 1587757 = 595409) (by norm_num)
theorem B2505269 : Blo 1040609 2505269 := bbase (se 5 (by rfl) ⟨117434, by rfl⟩ : syracuseStep 2505269 = 234869) (by norm_num)
theorem B2505277 : Blo 1040609 2505277 := bbase (se 3 (by rfl) ⟨469739, by rfl⟩ : syracuseStep 2505277 = 939479) (by norm_num)
theorem B2112077 : Blo 1040609 2112077 := bbase (se 3 (by rfl) ⟨396014, by rfl⟩ : syracuseStep 2112077 = 792029) (by norm_num)
theorem B1784413 : Blo 1040609 1784413 := bbase (se 3 (by rfl) ⟨334577, by rfl⟩ : syracuseStep 1784413 = 669155) (by norm_num)
theorem B2341493 : Blo 1040609 2341493 := bbase (se 5 (by rfl) ⟨109757, by rfl⟩ : syracuseStep 2341493 = 219515) (by norm_num)
theorem B2374261 : Blo 1040609 2374261 := bbase (se 5 (by rfl) ⟨111293, by rfl⟩ : syracuseStep 2374261 = 222587) (by norm_num)
theorem B2341565 : Blo 1040609 2341565 := bbase (se 3 (by rfl) ⟨439043, by rfl⟩ : syracuseStep 2341565 = 878087) (by norm_num)
theorem B2636509 : Blo 1040609 2636509 := bbase (se 3 (by rfl) ⟨494345, by rfl⟩ : syracuseStep 2636509 = 988691) (by norm_num)
theorem B2341637 : Blo 1040609 2341637 := bbase (se 4 (by rfl) ⟨219528, by rfl⟩ : syracuseStep 2341637 = 439057) (by norm_num)
theorem B3521285 : Blo 1040609 3521285 := bbase (se 4 (by rfl) ⟨330120, by rfl⟩ : syracuseStep 3521285 = 660241) (by norm_num)
theorem B2341709 : Blo 1040609 2341709 := bbase (se 3 (by rfl) ⟨439070, by rfl⟩ : syracuseStep 2341709 = 878141) (by norm_num)
theorem B2636621 : Blo 1040609 2636621 := bbase (se 3 (by rfl) ⟨494366, by rfl⟩ : syracuseStep 2636621 = 988733) (by norm_num)
theorem B7519061 : Blo 1040609 7519061 := bbase (se 9 (by rfl) ⟨22028, by rfl⟩ : syracuseStep 7519061 = 44057) (by norm_num)
theorem B2341781 : Blo 1040609 2341781 := bbase (se 6 (by rfl) ⟨54885, by rfl⟩ : syracuseStep 2341781 = 109771) (by norm_num)
theorem B2341853 : Blo 1040609 2341853 := bbase (se 3 (by rfl) ⟨439097, by rfl⟩ : syracuseStep 2341853 = 878195) (by norm_num)
theorem B2636813 : Blo 1040609 2636813 := bbase (se 3 (by rfl) ⟨494402, by rfl⟩ : syracuseStep 2636813 = 988805) (by norm_num)
theorem B2341925 : Blo 1040609 2341925 := bbase (se 4 (by rfl) ⟨219555, by rfl⟩ : syracuseStep 2341925 = 439111) (by norm_num)
theorem B2341997 : Blo 1040609 2341997 := bbase (se 3 (by rfl) ⟨439124, by rfl⟩ : syracuseStep 2341997 = 878249) (by norm_num)
theorem B7912565 : Blo 1040609 7912565 := bbase (se 5 (by rfl) ⟨370901, by rfl⟩ : syracuseStep 7912565 = 741803) (by norm_num)
theorem B1981597 : Blo 1040609 1981597 := bbase (se 3 (by rfl) ⟨371549, by rfl⟩ : syracuseStep 1981597 = 743099) (by norm_num)
theorem B2342069 : Blo 1040609 2342069 := bbase (se 5 (by rfl) ⟨109784, by rfl⟩ : syracuseStep 2342069 = 219569) (by norm_num)
theorem B3521717 : Blo 1040609 3521717 := bbase (se 5 (by rfl) ⟨165080, by rfl⟩ : syracuseStep 3521717 = 330161) (by norm_num)
theorem B2342141 : Blo 1040609 2342141 := bbase (se 3 (by rfl) ⟨439151, by rfl⟩ : syracuseStep 2342141 = 878303) (by norm_num)
theorem B1981741 : Blo 1040609 1981741 := bbase (se 3 (by rfl) ⟨371576, by rfl⟩ : syracuseStep 1981741 = 743153) (by norm_num)
theorem B2342213 : Blo 1040609 2342213 := bbase (se 4 (by rfl) ⟨219582, by rfl⟩ : syracuseStep 2342213 = 439165) (by norm_num)
theorem B2637157 : Blo 1040609 2637157 := bbase (se 4 (by rfl) ⟨247233, by rfl⟩ : syracuseStep 2637157 = 494467) (by norm_num)
theorem B2342285 : Blo 1040609 2342285 := bbase (se 3 (by rfl) ⟨439178, by rfl⟩ : syracuseStep 2342285 = 878357) (by norm_num)
theorem B1981901 : Blo 1040609 1981901 := bbase (se 3 (by rfl) ⟨371606, by rfl⟩ : syracuseStep 1981901 = 743213) (by norm_num)
theorem B2342357 : Blo 1040609 2342357 := bbase (se 7 (by rfl) ⟨27449, by rfl⟩ : syracuseStep 2342357 = 54899) (by norm_num)
theorem B2637269 : Blo 1040609 2637269 := bbase (se 7 (by rfl) ⟨30905, by rfl⟩ : syracuseStep 2637269 = 61811) (by norm_num)
theorem B2342429 : Blo 1040609 2342429 := bbase (se 3 (by rfl) ⟨439205, by rfl⟩ : syracuseStep 2342429 = 878411) (by norm_num)
theorem B2506277 : Blo 1040609 2506277 := bbase (se 4 (by rfl) ⟨234963, by rfl⟩ : syracuseStep 2506277 = 469927) (by norm_num)
theorem B1982045 : Blo 1040609 1982045 := bbase (se 3 (by rfl) ⟨371633, by rfl⟩ : syracuseStep 1982045 = 743267) (by norm_num)
theorem B2342501 : Blo 1040609 2342501 := bbase (se 4 (by rfl) ⟨219609, by rfl⟩ : syracuseStep 2342501 = 439219) (by norm_num)
theorem B3522149 : Blo 1040609 3522149 := bbase (se 4 (by rfl) ⟨330201, by rfl⟩ : syracuseStep 3522149 = 660403) (by norm_num)
theorem B2637461 : Blo 1040609 2637461 := bbase (se 6 (by rfl) ⟨61815, by rfl⟩ : syracuseStep 2637461 = 123631) (by norm_num)
theorem B2342573 : Blo 1040609 2342573 := bbase (se 3 (by rfl) ⟨439232, by rfl⟩ : syracuseStep 2342573 = 878465) (by norm_num)
theorem B2506469 : Blo 1040609 2506469 := bbase (se 4 (by rfl) ⟨234981, by rfl⟩ : syracuseStep 2506469 = 469963) (by norm_num)
theorem B2342645 : Blo 1040609 2342645 := bbase (se 5 (by rfl) ⟨109811, by rfl⟩ : syracuseStep 2342645 = 219623) (by norm_num)
theorem B2342717 : Blo 1040609 2342717 := bbase (se 3 (by rfl) ⟨439259, by rfl⟩ : syracuseStep 2342717 = 878519) (by norm_num)
theorem B1982333 : Blo 1040609 1982333 := bbase (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) (by norm_num)
theorem B2342789 : Blo 1040609 2342789 := bbase (se 4 (by rfl) ⟨219636, by rfl⟩ : syracuseStep 2342789 = 439273) (by norm_num)
theorem B2342861 : Blo 1040609 2342861 := bbase (se 3 (by rfl) ⟨439286, by rfl⟩ : syracuseStep 2342861 = 878573) (by norm_num)
theorem B2637805 : Blo 1040609 2637805 := bbase (se 3 (by rfl) ⟨494588, by rfl⟩ : syracuseStep 2637805 = 989177) (by norm_num)
theorem B2342933 : Blo 1040609 2342933 := bbase (se 6 (by rfl) ⟨54912, by rfl⟩ : syracuseStep 2342933 = 109825) (by norm_num)
theorem B3522581 : Blo 1040609 3522581 := bbase (se 6 (by rfl) ⟨82560, by rfl⟩ : syracuseStep 3522581 = 165121) (by norm_num)
theorem B1982485 : Blo 1040609 1982485 := bbase (se 6 (by rfl) ⟨46464, by rfl⟩ : syracuseStep 1982485 = 92929) (by norm_num)
theorem B1785925 : Blo 1040609 1785925 := bbase (se 4 (by rfl) ⟨167430, by rfl⟩ : syracuseStep 1785925 = 334861) (by norm_num)
theorem B3752021 : Blo 1040609 3752021 := bbase (se 8 (by rfl) ⟨21984, by rfl⟩ : syracuseStep 3752021 = 43969) (by norm_num)
theorem B2343005 : Blo 1040609 2343005 := bbase (se 3 (by rfl) ⟨439313, by rfl⟩ : syracuseStep 2343005 = 878627) (by norm_num)
theorem B2637917 : Blo 1040609 2637917 := bbase (se 3 (by rfl) ⟨494609, by rfl⟩ : syracuseStep 2637917 = 989219) (by norm_num)
theorem B2343077 : Blo 1040609 2343077 := bbase (se 4 (by rfl) ⟨219663, by rfl⟩ : syracuseStep 2343077 = 439327) (by norm_num)
theorem B2343149 : Blo 1040609 2343149 := bbase (se 3 (by rfl) ⟨439340, by rfl⟩ : syracuseStep 2343149 = 878681) (by norm_num)
theorem B2638109 : Blo 1040609 2638109 := bbase (se 3 (by rfl) ⟨494645, by rfl⟩ : syracuseStep 2638109 = 989291) (by norm_num)
theorem B2343221 : Blo 1040609 2343221 := bbase (se 5 (by rfl) ⟨109838, by rfl⟩ : syracuseStep 2343221 = 219677) (by norm_num)
theorem B1982789 : Blo 1040609 1982789 := bbase (se 4 (by rfl) ⟨185886, by rfl⟩ : syracuseStep 1982789 = 371773) (by norm_num)
theorem B2343293 : Blo 1040609 2343293 := bbase (se 3 (by rfl) ⟨439367, by rfl⟩ : syracuseStep 2343293 = 878735) (by norm_num)
theorem B2408837 : Blo 1040609 2408837 := bbase (se 4 (by rfl) ⟨225828, by rfl⟩ : syracuseStep 2408837 = 451657) (by norm_num)
theorem B2343365 : Blo 1040609 2343365 := bbase (se 4 (by rfl) ⟨219690, by rfl⟩ : syracuseStep 2343365 = 439381) (by norm_num)
theorem B3523013 : Blo 1040609 3523013 := bbase (se 4 (by rfl) ⟨330282, by rfl⟩ : syracuseStep 3523013 = 660565) (by norm_num)
theorem B2343437 : Blo 1040609 2343437 := bbase (se 3 (by rfl) ⟨439394, by rfl⟩ : syracuseStep 2343437 = 878789) (by norm_num)
theorem B1786445 : Blo 1040609 1786445 := bbase (se 3 (by rfl) ⟨334958, by rfl⟩ : syracuseStep 1786445 = 669917) (by norm_num)
theorem B2343509 : Blo 1040609 2343509 := bbase (se 8 (by rfl) ⟨13731, by rfl⟩ : syracuseStep 2343509 = 27463) (by norm_num)
theorem B2638453 : Blo 1040609 2638453 := bbase (se 5 (by rfl) ⟨123677, by rfl⟩ : syracuseStep 2638453 = 247355) (by norm_num)
theorem B2966165 : Blo 1040609 2966165 := bbase (se 6 (by rfl) ⟨69519, by rfl⟩ : syracuseStep 2966165 = 139039) (by norm_num)
theorem B2343581 : Blo 1040609 2343581 := bbase (se 3 (by rfl) ⟨439421, by rfl⟩ : syracuseStep 2343581 = 878843) (by norm_num)
theorem B2343653 : Blo 1040609 2343653 := bbase (se 4 (by rfl) ⟨219717, by rfl⟩ : syracuseStep 2343653 = 439435) (by norm_num)
theorem B2638565 : Blo 1040609 2638565 := bbase (se 4 (by rfl) ⟨247365, by rfl⟩ : syracuseStep 2638565 = 494731) (by norm_num)
theorem B2671373 : Blo 1040609 2671373 := bbase (se 3 (by rfl) ⟨500882, by rfl⟩ : syracuseStep 2671373 = 1001765) (by norm_num)
theorem B2343725 : Blo 1040609 2343725 := bbase (se 3 (by rfl) ⟨439448, by rfl⟩ : syracuseStep 2343725 = 878897) (by norm_num)
theorem B2343797 : Blo 1040609 2343797 := bbase (se 5 (by rfl) ⟨109865, by rfl⟩ : syracuseStep 2343797 = 219731) (by norm_num)
theorem B3523445 : Blo 1040609 3523445 := bbase (se 5 (by rfl) ⟨165161, by rfl⟩ : syracuseStep 3523445 = 330323) (by norm_num)
theorem B2638757 : Blo 1040609 2638757 := bbase (se 4 (by rfl) ⟨247383, by rfl⟩ : syracuseStep 2638757 = 494767) (by norm_num)
theorem B2343869 : Blo 1040609 2343869 := bbase (se 3 (by rfl) ⟨439475, by rfl⟩ : syracuseStep 2343869 = 878951) (by norm_num)
theorem B2343941 : Blo 1040609 2343941 := bbase (se 4 (by rfl) ⟨219744, by rfl⟩ : syracuseStep 2343941 = 439489) (by norm_num)
theorem B2344013 : Blo 1040609 2344013 := bbase (se 3 (by rfl) ⟨439502, by rfl⟩ : syracuseStep 2344013 = 879005) (by norm_num)
theorem B2344085 : Blo 1040609 2344085 := bbase (se 6 (by rfl) ⟨54939, by rfl⟩ : syracuseStep 2344085 = 109879) (by norm_num)
theorem B2344157 : Blo 1040609 2344157 := bbase (se 3 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 2344157 = 879059) (by norm_num)
theorem B2639101 : Blo 1040609 2639101 := bbase (se 3 (by rfl) ⟨494831, by rfl⟩ : syracuseStep 2639101 = 989663) (by norm_num)
theorem B2344229 : Blo 1040609 2344229 := bbase (se 4 (by rfl) ⟨219771, by rfl⟩ : syracuseStep 2344229 = 439543) (by norm_num)
theorem B3523877 : Blo 1040609 3523877 := bbase (se 4 (by rfl) ⟨330363, by rfl⟩ : syracuseStep 3523877 = 660727) (by norm_num)
theorem B2671949 : Blo 1040609 2671949 := bbase (se 3 (by rfl) ⟨500990, by rfl⟩ : syracuseStep 2671949 = 1001981) (by norm_num)
theorem B2344301 : Blo 1040609 2344301 := bbase (se 3 (by rfl) ⟨439556, by rfl⟩ : syracuseStep 2344301 = 879113) (by norm_num)
theorem B2639213 : Blo 1040609 2639213 := bbase (se 3 (by rfl) ⟨494852, by rfl⟩ : syracuseStep 2639213 = 989705) (by norm_num)
theorem B2344373 : Blo 1040609 2344373 := bbase (se 5 (by rfl) ⟨109892, by rfl⟩ : syracuseStep 2344373 = 219785) (by norm_num)
theorem B2344445 : Blo 1040609 2344445 := bbase (se 3 (by rfl) ⟨439583, by rfl⟩ : syracuseStep 2344445 = 879167) (by norm_num)
theorem B2115077 : Blo 1040609 2115077 := bbase (se 4 (by rfl) ⟨198288, by rfl⟩ : syracuseStep 2115077 = 396577) (by norm_num)
theorem B2639405 : Blo 1040609 2639405 := bbase (se 3 (by rfl) ⟨494888, by rfl⟩ : syracuseStep 2639405 = 989777) (by norm_num)
theorem B2344517 : Blo 1040609 2344517 := bbase (se 4 (by rfl) ⟨219798, by rfl⟩ : syracuseStep 2344517 = 439597) (by norm_num)
theorem B2508421 : Blo 1040609 2508421 := bbase (se 4 (by rfl) ⟨235164, by rfl⟩ : syracuseStep 2508421 = 470329) (by norm_num)
theorem B2344589 : Blo 1040609 2344589 := bbase (se 3 (by rfl) ⟨439610, by rfl⟩ : syracuseStep 2344589 = 879221) (by norm_num)
theorem B2344661 : Blo 1040609 2344661 := bbase (se 7 (by rfl) ⟨27476, by rfl⟩ : syracuseStep 2344661 = 54953) (by norm_num)
theorem B3524309 : Blo 1040609 3524309 := bbase (se 7 (by rfl) ⟨41300, by rfl⟩ : syracuseStep 3524309 = 82601) (by norm_num)
theorem B2344733 : Blo 1040609 2344733 := bbase (se 3 (by rfl) ⟨439637, by rfl⟩ : syracuseStep 2344733 = 879275) (by norm_num)
theorem B2967349 : Blo 1040609 2967349 := bbase (se 5 (by rfl) ⟨139094, by rfl⟩ : syracuseStep 2967349 = 278189) (by norm_num)
theorem B2344805 : Blo 1040609 2344805 := bbase (se 4 (by rfl) ⟨219825, by rfl⟩ : syracuseStep 2344805 = 439651) (by norm_num)
theorem B2639749 : Blo 1040609 2639749 := bbase (se 4 (by rfl) ⟨247476, by rfl⟩ : syracuseStep 2639749 = 494953) (by norm_num)
theorem B2344877 : Blo 1040609 2344877 := bbase (se 3 (by rfl) ⟨439664, by rfl⟩ : syracuseStep 2344877 = 879329) (by norm_num)
theorem B2967509 : Blo 1040609 2967509 := bbase (se 7 (by rfl) ⟨34775, by rfl⟩ : syracuseStep 2967509 = 69551) (by norm_num)
theorem B2344949 : Blo 1040609 2344949 := bbase (se 5 (by rfl) ⟨109919, by rfl⟩ : syracuseStep 2344949 = 219839) (by norm_num)
theorem B2639861 : Blo 1040609 2639861 := bbase (se 5 (by rfl) ⟨123743, by rfl⟩ : syracuseStep 2639861 = 247487) (by norm_num)
theorem B2672645 : Blo 1040609 2672645 := bbase (se 4 (by rfl) ⟨250560, by rfl⟩ : syracuseStep 2672645 = 501121) (by norm_num)
theorem B2377765 : Blo 1040609 2377765 := bbase (se 4 (by rfl) ⟨222915, by rfl⟩ : syracuseStep 2377765 = 445831) (by norm_num)
theorem B2345021 : Blo 1040609 2345021 := bbase (se 3 (by rfl) ⟨439691, by rfl⟩ : syracuseStep 2345021 = 879383) (by norm_num)
theorem B2115709 : Blo 1040609 2115709 := bbase (se 3 (by rfl) ⟨396695, by rfl⟩ : syracuseStep 2115709 = 793391) (by norm_num)
theorem B2345093 : Blo 1040609 2345093 := bbase (se 4 (by rfl) ⟨219852, by rfl⟩ : syracuseStep 2345093 = 439705) (by norm_num)
theorem B3524741 : Blo 1040609 3524741 := bbase (se 4 (by rfl) ⟨330444, by rfl⟩ : syracuseStep 3524741 = 660889) (by norm_num)
theorem B2640053 : Blo 1040609 2640053 := bbase (se 5 (by rfl) ⟨123752, by rfl⟩ : syracuseStep 2640053 = 247505) (by norm_num)
theorem B2967749 : Blo 1040609 2967749 := bbase (se 4 (by rfl) ⟨278226, by rfl⟩ : syracuseStep 2967749 = 556453) (by norm_num)
theorem B2345165 : Blo 1040609 2345165 := bbase (se 3 (by rfl) ⟨439718, by rfl⟩ : syracuseStep 2345165 = 879437) (by norm_num)
theorem B2345237 : Blo 1040609 2345237 := bbase (se 6 (by rfl) ⟨54966, by rfl⟩ : syracuseStep 2345237 = 109933) (by norm_num)
theorem B2345309 : Blo 1040609 2345309 := bbase (se 3 (by rfl) ⟨439745, by rfl⟩ : syracuseStep 2345309 = 879491) (by norm_num)
theorem B2967941 : Blo 1040609 2967941 := bbase (se 4 (by rfl) ⟨278244, by rfl⟩ : syracuseStep 2967941 = 556489) (by norm_num)
theorem B2345381 : Blo 1040609 2345381 := bbase (se 4 (by rfl) ⟨219879, by rfl⟩ : syracuseStep 2345381 = 439759) (by norm_num)
theorem B2345453 : Blo 1040609 2345453 := bbase (se 3 (by rfl) ⟨439772, by rfl⟩ : syracuseStep 2345453 = 879545) (by norm_num)
theorem B2411021 : Blo 1040609 2411021 := bbase (se 3 (by rfl) ⟨452066, by rfl⟩ : syracuseStep 2411021 = 904133) (by norm_num)
theorem B2640397 : Blo 1040609 2640397 := bbase (se 3 (by rfl) ⟨495074, by rfl⟩ : syracuseStep 2640397 = 990149) (by norm_num)
theorem B2345525 : Blo 1040609 2345525 := bbase (se 5 (by rfl) ⟨109946, by rfl⟩ : syracuseStep 2345525 = 219893) (by norm_num)
theorem B3525173 : Blo 1040609 3525173 := bbase (se 5 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 3525173 = 330485) (by norm_num)
theorem B2509373 : Blo 1040609 2509373 := bbase (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) (by norm_num)
theorem B5360197 : Blo 1040609 5360197 := bbase (se 4 (by rfl) ⟨502518, by rfl⟩ : syracuseStep 5360197 = 1005037) (by norm_num)
theorem B2509429 : Blo 1040609 2509429 := bbase (se 5 (by rfl) ⟨117629, by rfl⟩ : syracuseStep 2509429 = 235259) (by norm_num)
theorem B2345597 : Blo 1040609 2345597 := bbase (se 3 (by rfl) ⟨439799, by rfl⟩ : syracuseStep 2345597 = 879599) (by norm_num)
theorem B2640509 : Blo 1040609 2640509 := bbase (se 3 (by rfl) ⟨495095, by rfl⟩ : syracuseStep 2640509 = 990191) (by norm_num)
theorem B3951301 : Blo 1040609 3951301 := bbase (se 4 (by rfl) ⟨370434, by rfl⟩ : syracuseStep 3951301 = 740869) (by norm_num)
theorem B2345669 : Blo 1040609 2345669 := bbase (se 4 (by rfl) ⟨219906, by rfl⟩ : syracuseStep 2345669 = 439813) (by norm_num)
theorem B2345741 : Blo 1040609 2345741 := bbase (se 3 (by rfl) ⟨439826, by rfl⟩ : syracuseStep 2345741 = 879653) (by norm_num)
theorem B2640701 : Blo 1040609 2640701 := bbase (se 3 (by rfl) ⟨495131, by rfl⟩ : syracuseStep 2640701 = 990263) (by norm_num)
theorem B2345813 : Blo 1040609 2345813 := bbase (se 9 (by rfl) ⟨6872, by rfl⟩ : syracuseStep 2345813 = 13745) (by norm_num)
theorem B7523189 : Blo 1040609 7523189 := bbase (se 5 (by rfl) ⟨352649, by rfl⟩ : syracuseStep 7523189 = 705299) (by norm_num)
theorem B2345885 : Blo 1040609 2345885 := bbase (se 3 (by rfl) ⟨439853, by rfl⟩ : syracuseStep 2345885 = 879707) (by norm_num)
theorem B1756093 : Blo 1040609 1756093 := bbase (se 3 (by rfl) ⟨329267, by rfl⟩ : syracuseStep 1756093 = 658535) (by norm_num)
theorem B2345957 : Blo 1040609 2345957 := bbase (se 4 (by rfl) ⟨219933, by rfl⟩ : syracuseStep 2345957 = 439867) (by norm_num)
theorem B2509805 : Blo 1040609 2509805 := bbase (se 3 (by rfl) ⟨470588, by rfl⟩ : syracuseStep 2509805 = 941177) (by norm_num)
theorem B3951605 : Blo 1040609 3951605 := bbase (se 5 (by rfl) ⟨185231, by rfl⟩ : syracuseStep 3951605 = 370463) (by norm_num)
theorem B1756181 : Blo 1040609 1756181 := bbase (se 6 (by rfl) ⟨41160, by rfl⟩ : syracuseStep 1756181 = 82321) (by norm_num)
theorem B2346029 : Blo 1040609 2346029 := bbase (se 3 (by rfl) ⟨439880, by rfl⟩ : syracuseStep 2346029 = 879761) (by norm_num)
theorem B2346101 : Blo 1040609 2346101 := bbase (se 5 (by rfl) ⟨109973, by rfl⟩ : syracuseStep 2346101 = 219947) (by norm_num)
theorem B1756309 : Blo 1040609 1756309 := bbase (se 6 (by rfl) ⟨41163, by rfl⟩ : syracuseStep 1756309 = 82327) (by norm_num)
theorem B2641045 : Blo 1040609 2641045 := bbase (se 6 (by rfl) ⟨61899, by rfl⟩ : syracuseStep 2641045 = 123799) (by norm_num)
theorem B2346173 : Blo 1040609 2346173 := bbase (se 3 (by rfl) ⟨439907, by rfl⟩ : syracuseStep 2346173 = 879815) (by norm_num)
theorem B2116813 : Blo 1040609 2116813 := bbase (se 3 (by rfl) ⟨396902, by rfl⟩ : syracuseStep 2116813 = 793805) (by norm_num)
theorem B1756397 : Blo 1040609 1756397 := bbase (se 3 (by rfl) ⟨329324, by rfl⟩ : syracuseStep 1756397 = 658649) (by norm_num)
theorem B2346245 : Blo 1040609 2346245 := bbase (se 4 (by rfl) ⟨219960, by rfl⟩ : syracuseStep 2346245 = 439921) (by norm_num)
theorem B2641157 : Blo 1040609 2641157 := bbase (se 4 (by rfl) ⟨247608, by rfl⟩ : syracuseStep 2641157 = 495217) (by norm_num)
theorem B2346317 : Blo 1040609 2346317 := bbase (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) (by norm_num)
theorem B9522517 : Blo 1040609 9522517 := bbase (se 11 (by rfl) ⟨6974, by rfl⟩ : syracuseStep 9522517 = 13949) (by norm_num)
theorem B2968933 : Blo 1040609 2968933 := bbase (se 4 (by rfl) ⟨278337, by rfl⟩ : syracuseStep 2968933 = 556675) (by norm_num)
theorem B1756525 : Blo 1040609 1756525 := bbase (se 3 (by rfl) ⟨329348, by rfl⟩ : syracuseStep 1756525 = 658697) (by norm_num)
theorem B2346389 : Blo 1040609 2346389 := bbase (se 6 (by rfl) ⟨54993, by rfl⟩ : syracuseStep 2346389 = 109987) (by norm_num)
theorem B1756613 : Blo 1040609 1756613 := bbase (se 4 (by rfl) ⟨164682, by rfl⟩ : syracuseStep 1756613 = 329365) (by norm_num)
theorem B2641349 : Blo 1040609 2641349 := bbase (se 4 (by rfl) ⟨247626, by rfl⟩ : syracuseStep 2641349 = 495253) (by norm_num)
theorem B2346461 : Blo 1040609 2346461 := bbase (se 3 (by rfl) ⟨439961, by rfl⟩ : syracuseStep 2346461 = 879923) (by norm_num)
theorem B4509173 : Blo 1040609 4509173 := bbase (se 5 (by rfl) ⟨211367, by rfl⟩ : syracuseStep 4509173 = 422735) (by norm_num)
theorem B2346533 : Blo 1040609 2346533 := bbase (se 4 (by rfl) ⟨219987, by rfl⟩ : syracuseStep 2346533 = 439975) (by norm_num)
theorem B1756741 : Blo 1040609 1756741 := bbase (se 4 (by rfl) ⟨164694, by rfl⟩ : syracuseStep 1756741 = 329389) (by norm_num)
theorem B17780309 : Blo 1040609 17780309 := bbase (se 8 (by rfl) ⟨104181, by rfl⟩ : syracuseStep 17780309 = 208363) (by norm_num)
theorem B2346605 : Blo 1040609 2346605 := bbase (se 3 (by rfl) ⟨439988, by rfl⟩ : syracuseStep 2346605 = 879977) (by norm_num)
theorem B1756829 : Blo 1040609 1756829 := bbase (se 3 (by rfl) ⟨329405, by rfl⟩ : syracuseStep 1756829 = 658811) (by norm_num)
theorem B2346677 : Blo 1040609 2346677 := bbase (se 5 (by rfl) ⟨110000, by rfl⟩ : syracuseStep 2346677 = 220001) (by norm_num)
theorem B2346749 : Blo 1040609 2346749 := bbase (se 3 (by rfl) ⟨440015, by rfl⟩ : syracuseStep 2346749 = 880031) (by norm_num)
theorem B1756957 : Blo 1040609 1756957 := bbase (se 3 (by rfl) ⟨329429, by rfl⟩ : syracuseStep 1756957 = 658859) (by norm_num)
theorem B2641693 : Blo 1040609 2641693 := bbase (se 3 (by rfl) ⟨495317, by rfl⟩ : syracuseStep 2641693 = 990635) (by norm_num)
theorem B2346821 : Blo 1040609 2346821 := bbase (se 4 (by rfl) ⟨220014, by rfl⟩ : syracuseStep 2346821 = 440029) (by norm_num)
theorem B5001061 : Blo 1040609 5001061 := bbase (se 4 (by rfl) ⟨468849, by rfl⟩ : syracuseStep 5001061 = 937699) (by norm_num)
theorem B1757045 : Blo 1040609 1757045 := bbase (se 5 (by rfl) ⟨82361, by rfl⟩ : syracuseStep 1757045 = 164723) (by norm_num)
theorem B2346893 : Blo 1040609 2346893 := bbase (se 3 (by rfl) ⟨440042, by rfl⟩ : syracuseStep 2346893 = 880085) (by norm_num)
theorem B2641805 : Blo 1040609 2641805 := bbase (se 3 (by rfl) ⟨495338, by rfl⟩ : syracuseStep 2641805 = 990677) (by norm_num)
theorem B4018085 : Blo 1040609 4018085 := bbase (se 4 (by rfl) ⟨376695, by rfl⟩ : syracuseStep 4018085 = 753391) (by norm_num)
theorem B6770645 : Blo 1040609 6770645 := bbase (se 7 (by rfl) ⟨79343, by rfl⟩ : syracuseStep 6770645 = 158687) (by norm_num)
theorem B2346965 : Blo 1040609 2346965 := bbase (se 7 (by rfl) ⟨27503, by rfl⟩ : syracuseStep 2346965 = 55007) (by norm_num)
theorem B1757173 : Blo 1040609 1757173 := bbase (se 5 (by rfl) ⟨82367, by rfl⟩ : syracuseStep 1757173 = 164735) (by norm_num)
theorem B2379773 : Blo 1040609 2379773 := bbase (se 3 (by rfl) ⟨446207, by rfl⟩ : syracuseStep 2379773 = 892415) (by norm_num)
theorem B2347037 : Blo 1040609 2347037 := bbase (se 3 (by rfl) ⟨440069, by rfl⟩ : syracuseStep 2347037 = 880139) (by norm_num)
theorem B1757261 : Blo 1040609 1757261 := bbase (se 3 (by rfl) ⟨329486, by rfl⟩ : syracuseStep 1757261 = 658973) (by norm_num)
theorem B2641997 : Blo 1040609 2641997 := bbase (se 3 (by rfl) ⟨495374, by rfl⟩ : syracuseStep 2641997 = 990749) (by norm_num)
theorem B2347109 : Blo 1040609 2347109 := bbase (se 4 (by rfl) ⟨220041, by rfl⟩ : syracuseStep 2347109 = 440083) (by norm_num)
theorem B2347181 : Blo 1040609 2347181 := bbase (se 3 (by rfl) ⟨440096, by rfl⟩ : syracuseStep 2347181 = 880193) (by norm_num)
theorem B1757389 : Blo 1040609 1757389 := bbase (se 3 (by rfl) ⟨329510, by rfl⟩ : syracuseStep 1757389 = 659021) (by norm_num)
theorem B2347253 : Blo 1040609 2347253 := bbase (se 5 (by rfl) ⟨110027, by rfl⟩ : syracuseStep 2347253 = 220055) (by norm_num)
theorem B1757477 : Blo 1040609 1757477 := bbase (se 4 (by rfl) ⟨164763, by rfl⟩ : syracuseStep 1757477 = 329527) (by norm_num)
theorem B2347325 : Blo 1040609 2347325 := bbase (se 3 (by rfl) ⟨440123, by rfl⟩ : syracuseStep 2347325 = 880247) (by norm_num)
theorem B1560917 : Blo 1040609 1560917 := bbase (se 10 (by rfl) ⟨2286, by rfl⟩ : syracuseStep 1560917 = 4573) (by norm_num)
theorem B1560941 : Blo 1040609 1560941 := bbase (se 3 (by rfl) ⟨292676, by rfl⟩ : syracuseStep 1560941 = 585353) (by norm_num)
theorem B2675069 : Blo 1040609 2675069 := bbase (se 3 (by rfl) ⟨501575, by rfl⟩ : syracuseStep 2675069 = 1003151) (by norm_num)
theorem B1560965 : Blo 1040609 1560965 := bbase (se 4 (by rfl) ⟨146340, by rfl⟩ : syracuseStep 1560965 = 292681) (by norm_num)
theorem B2347397 : Blo 1040609 2347397 := bbase (se 4 (by rfl) ⟨220068, by rfl⟩ : syracuseStep 2347397 = 440137) (by norm_num)
theorem B1560989 : Blo 1040609 1560989 := bbase (se 3 (by rfl) ⟨292685, by rfl⟩ : syracuseStep 1560989 = 585371) (by norm_num)
theorem B1757605 : Blo 1040609 1757605 := bbase (se 4 (by rfl) ⟨164775, by rfl⟩ : syracuseStep 1757605 = 329551) (by norm_num)
theorem B2642341 : Blo 1040609 2642341 := bbase (se 4 (by rfl) ⟨247719, by rfl⟩ : syracuseStep 2642341 = 495439) (by norm_num)
theorem B1561013 : Blo 1040609 1561013 := bbase (se 5 (by rfl) ⟨73172, by rfl⟩ : syracuseStep 1561013 = 146345) (by norm_num)
theorem B2970037 : Blo 1040609 2970037 := bbase (se 5 (by rfl) ⟨139220, by rfl⟩ : syracuseStep 2970037 = 278441) (by norm_num)
theorem B1561037 : Blo 1040609 1561037 := bbase (se 3 (by rfl) ⟨292694, by rfl⟩ : syracuseStep 1561037 = 585389) (by norm_num)
theorem B2347469 : Blo 1040609 2347469 := bbase (se 3 (by rfl) ⟨440150, by rfl⟩ : syracuseStep 2347469 = 880301) (by norm_num)
theorem B1561061 : Blo 1040609 1561061 := bbase (se 4 (by rfl) ⟨146349, by rfl⟩ : syracuseStep 1561061 = 292699) (by norm_num)
theorem B1561085 : Blo 1040609 1561085 := bbase (se 3 (by rfl) ⟨292703, by rfl⟩ : syracuseStep 1561085 = 585407) (by norm_num)
theorem B1757693 : Blo 1040609 1757693 := bbase (se 3 (by rfl) ⟨329567, by rfl⟩ : syracuseStep 1757693 = 659135) (by norm_num)
theorem B1561109 : Blo 1040609 1561109 := bbase (se 6 (by rfl) ⟨36588, by rfl⟩ : syracuseStep 1561109 = 73177) (by norm_num)
theorem B2347541 : Blo 1040609 2347541 := bbase (se 6 (by rfl) ⟨55020, by rfl⟩ : syracuseStep 2347541 = 110041) (by norm_num)
theorem B2642453 : Blo 1040609 2642453 := bbase (se 6 (by rfl) ⟨61932, by rfl⟩ : syracuseStep 2642453 = 123865) (by norm_num)
theorem B1561133 : Blo 1040609 1561133 := bbase (se 3 (by rfl) ⟨292712, by rfl⟩ : syracuseStep 1561133 = 585425) (by norm_num)
theorem B1561157 : Blo 1040609 1561157 := bbase (se 4 (by rfl) ⟨146358, by rfl⟩ : syracuseStep 1561157 = 292717) (by norm_num)
theorem B1561181 : Blo 1040609 1561181 := bbase (se 3 (by rfl) ⟨292721, by rfl⟩ : syracuseStep 1561181 = 585443) (by norm_num)
theorem B2347613 : Blo 1040609 2347613 := bbase (se 3 (by rfl) ⟨440177, by rfl⟩ : syracuseStep 2347613 = 880355) (by norm_num)
theorem B1561205 : Blo 1040609 1561205 := bbase (se 5 (by rfl) ⟨73181, by rfl⟩ : syracuseStep 1561205 = 146363) (by norm_num)
theorem B1757821 : Blo 1040609 1757821 := bbase (se 3 (by rfl) ⟨329591, by rfl⟩ : syracuseStep 1757821 = 659183) (by norm_num)
theorem B1561229 : Blo 1040609 1561229 := bbase (se 3 (by rfl) ⟨292730, by rfl⟩ : syracuseStep 1561229 = 585461) (by norm_num)
theorem B1561253 : Blo 1040609 1561253 := bbase (se 4 (by rfl) ⟨146367, by rfl⟩ : syracuseStep 1561253 = 292735) (by norm_num)
theorem B2347685 : Blo 1040609 2347685 := bbase (se 4 (by rfl) ⟨220095, by rfl⟩ : syracuseStep 2347685 = 440191) (by norm_num)
theorem B1561277 : Blo 1040609 1561277 := bbase (se 3 (by rfl) ⟨292739, by rfl⟩ : syracuseStep 1561277 = 585479) (by norm_num)
theorem B1561301 : Blo 1040609 1561301 := bbase (se 7 (by rfl) ⟨18296, by rfl⟩ : syracuseStep 1561301 = 36593) (by norm_num)
theorem B1757909 : Blo 1040609 1757909 := bbase (se 7 (by rfl) ⟨20600, by rfl⟩ : syracuseStep 1757909 = 41201) (by norm_num)
theorem B2642645 : Blo 1040609 2642645 := bbase (se 7 (by rfl) ⟨30968, by rfl⟩ : syracuseStep 2642645 = 61937) (by norm_num)
theorem B1430245 : Blo 1040609 1430245 := bbase (se 4 (by rfl) ⟨134085, by rfl⟩ : syracuseStep 1430245 = 268171) (by norm_num)
theorem B1561325 : Blo 1040609 1561325 := bbase (se 3 (by rfl) ⟨292748, by rfl⟩ : syracuseStep 1561325 = 585497) (by norm_num)
theorem B2347757 : Blo 1040609 2347757 := bbase (se 3 (by rfl) ⟨440204, by rfl⟩ : syracuseStep 2347757 = 880409) (by norm_num)
theorem B1561349 : Blo 1040609 1561349 := bbase (se 4 (by rfl) ⟨146376, by rfl⟩ : syracuseStep 1561349 = 292753) (by norm_num)
theorem B1561373 : Blo 1040609 1561373 := bbase (se 3 (by rfl) ⟨292757, by rfl⟩ : syracuseStep 1561373 = 585515) (by norm_num)
theorem B2675501 : Blo 1040609 2675501 := bbase (se 3 (by rfl) ⟨501656, by rfl⟩ : syracuseStep 2675501 = 1003313) (by norm_num)
theorem B1561397 : Blo 1040609 1561397 := bbase (se 5 (by rfl) ⟨73190, by rfl⟩ : syracuseStep 1561397 = 146381) (by norm_num)
theorem B6673205 : Blo 1040609 6673205 := bbase (se 5 (by rfl) ⟨312806, by rfl⟩ : syracuseStep 6673205 = 625613) (by norm_num)
theorem B2347829 : Blo 1040609 2347829 := bbase (se 5 (by rfl) ⟨110054, by rfl⟩ : syracuseStep 2347829 = 220109) (by norm_num)
theorem B1561421 : Blo 1040609 1561421 := bbase (se 3 (by rfl) ⟨292766, by rfl⟩ : syracuseStep 1561421 = 585533) (by norm_num)
theorem B1758037 : Blo 1040609 1758037 := bbase (se 9 (by rfl) ⟨5150, by rfl⟩ : syracuseStep 1758037 = 10301) (by norm_num)
theorem B1561445 : Blo 1040609 1561445 := bbase (se 4 (by rfl) ⟨146385, by rfl⟩ : syracuseStep 1561445 = 292771) (by norm_num)
theorem B4576117 : Blo 1040609 4576117 := bbase (se 5 (by rfl) ⟨214505, by rfl⟩ : syracuseStep 4576117 = 429011) (by norm_num)
theorem B1561469 : Blo 1040609 1561469 := bbase (se 3 (by rfl) ⟨292775, by rfl⟩ : syracuseStep 1561469 = 585551) (by norm_num)
theorem B2675581 : Blo 1040609 2675581 := bbase (se 3 (by rfl) ⟨501671, by rfl⟩ : syracuseStep 2675581 = 1003343) (by norm_num)
theorem B2347901 : Blo 1040609 2347901 := bbase (se 3 (by rfl) ⟨440231, by rfl⟩ : syracuseStep 2347901 = 880463) (by norm_num)
theorem B1561493 : Blo 1040609 1561493 := bbase (se 6 (by rfl) ⟨36597, by rfl⟩ : syracuseStep 1561493 = 73195) (by norm_num)
theorem B1561517 : Blo 1040609 1561517 := bbase (se 3 (by rfl) ⟨292784, by rfl⟩ : syracuseStep 1561517 = 585569) (by norm_num)
theorem B1758125 : Blo 1040609 1758125 := bbase (se 3 (by rfl) ⟨329648, by rfl⟩ : syracuseStep 1758125 = 659297) (by norm_num)
theorem B1561541 : Blo 1040609 1561541 := bbase (se 4 (by rfl) ⟨146394, by rfl⟩ : syracuseStep 1561541 = 292789) (by norm_num)
theorem B2347973 : Blo 1040609 2347973 := bbase (se 4 (by rfl) ⟨220122, by rfl⟩ : syracuseStep 2347973 = 440245) (by norm_num)
theorem B1561565 : Blo 1040609 1561565 := bbase (se 3 (by rfl) ⟨292793, by rfl⟩ : syracuseStep 1561565 = 585587) (by norm_num)
theorem B2118637 : Blo 1040609 2118637 := bbase (se 3 (by rfl) ⟨397244, by rfl⟩ : syracuseStep 2118637 = 794489) (by norm_num)
theorem B1561589 : Blo 1040609 1561589 := bbase (se 5 (by rfl) ⟨73199, by rfl⟩ : syracuseStep 1561589 = 146399) (by norm_num)
theorem B2675717 : Blo 1040609 2675717 := bbase (se 4 (by rfl) ⟨250848, by rfl⟩ : syracuseStep 2675717 = 501697) (by norm_num)
theorem B1561613 : Blo 1040609 1561613 := bbase (se 3 (by rfl) ⟨292802, by rfl⟩ : syracuseStep 1561613 = 585605) (by norm_num)
theorem B2348045 : Blo 1040609 2348045 := bbase (se 3 (by rfl) ⟨440258, by rfl⟩ : syracuseStep 2348045 = 880517) (by norm_num)
theorem B1561637 : Blo 1040609 1561637 := bbase (se 4 (by rfl) ⟨146403, by rfl⟩ : syracuseStep 1561637 = 292807) (by norm_num)
theorem B1758253 : Blo 1040609 1758253 := bbase (se 3 (by rfl) ⟨329672, by rfl⟩ : syracuseStep 1758253 = 659345) (by norm_num)
theorem B2642989 : Blo 1040609 2642989 := bbase (se 3 (by rfl) ⟨495560, by rfl⟩ : syracuseStep 2642989 = 991121) (by norm_num)
theorem B3953717 : Blo 1040609 3953717 := bbase (se 5 (by rfl) ⟨185330, by rfl⟩ : syracuseStep 3953717 = 370661) (by norm_num)
theorem B1561661 : Blo 1040609 1561661 := bbase (se 3 (by rfl) ⟨292811, by rfl⟩ : syracuseStep 1561661 = 585623) (by norm_num)
theorem B1561685 : Blo 1040609 1561685 := bbase (se 8 (by rfl) ⟨9150, by rfl⟩ : syracuseStep 1561685 = 18301) (by norm_num)
theorem B2348117 : Blo 1040609 2348117 := bbase (se 8 (by rfl) ⟨13758, by rfl⟩ : syracuseStep 2348117 = 27517) (by norm_num)
theorem B1561709 : Blo 1040609 1561709 := bbase (se 3 (by rfl) ⟨292820, by rfl⟩ : syracuseStep 1561709 = 585641) (by norm_num)
theorem B1561733 : Blo 1040609 1561733 := bbase (se 4 (by rfl) ⟨146412, by rfl⟩ : syracuseStep 1561733 = 292825) (by norm_num)
theorem B1758341 : Blo 1040609 1758341 := bbase (se 4 (by rfl) ⟨164844, by rfl⟩ : syracuseStep 1758341 = 329689) (by norm_num)
theorem B1561757 : Blo 1040609 1561757 := bbase (se 3 (by rfl) ⟨292829, by rfl⟩ : syracuseStep 1561757 = 585659) (by norm_num)
theorem B2348189 : Blo 1040609 2348189 := bbase (se 3 (by rfl) ⟨440285, by rfl⟩ : syracuseStep 2348189 = 880571) (by norm_num)
theorem B2643101 : Blo 1040609 2643101 := bbase (se 3 (by rfl) ⟨495581, by rfl⟩ : syracuseStep 2643101 = 991163) (by norm_num)
theorem B1561781 : Blo 1040609 1561781 := bbase (se 5 (by rfl) ⟨73208, by rfl⟩ : syracuseStep 1561781 = 146417) (by norm_num)
theorem B1561805 : Blo 1040609 1561805 := bbase (se 3 (by rfl) ⟨292838, by rfl⟩ : syracuseStep 1561805 = 585677) (by norm_num)
theorem B33871061 : Blo 1040609 33871061 := bbase (se 7 (by rfl) ⟨396926, by rfl⟩ : syracuseStep 33871061 = 793853) (by norm_num)
theorem B1561829 : Blo 1040609 1561829 := bbase (se 4 (by rfl) ⟨146421, by rfl⟩ : syracuseStep 1561829 = 292843) (by norm_num)
theorem B2348261 : Blo 1040609 2348261 := bbase (se 4 (by rfl) ⟨220149, by rfl⟩ : syracuseStep 2348261 = 440299) (by norm_num)
theorem B1561853 : Blo 1040609 1561853 := bbase (se 3 (by rfl) ⟨292847, by rfl⟩ : syracuseStep 1561853 = 585695) (by norm_num)
theorem B1758469 : Blo 1040609 1758469 := bbase (se 4 (by rfl) ⟨164856, by rfl⟩ : syracuseStep 1758469 = 329713) (by norm_num)
theorem B1561877 : Blo 1040609 1561877 := bbase (se 6 (by rfl) ⟨36606, by rfl⟩ : syracuseStep 1561877 = 73213) (by norm_num)
theorem B1561901 : Blo 1040609 1561901 := bbase (se 3 (by rfl) ⟨292856, by rfl⟩ : syracuseStep 1561901 = 585713) (by norm_num)
theorem B2348333 : Blo 1040609 2348333 := bbase (se 3 (by rfl) ⟨440312, by rfl⟩ : syracuseStep 2348333 = 880625) (by norm_num)
theorem B1561925 : Blo 1040609 1561925 := bbase (se 4 (by rfl) ⟨146430, by rfl⟩ : syracuseStep 1561925 = 292861) (by norm_num)
theorem B3954005 : Blo 1040609 3954005 := bbase (se 16 (by rfl) ⟨90, by rfl⟩ : syracuseStep 3954005 = 181) (by norm_num)
theorem B1561949 : Blo 1040609 1561949 := bbase (se 3 (by rfl) ⟨292865, by rfl⟩ : syracuseStep 1561949 = 585731) (by norm_num)
theorem B1758557 : Blo 1040609 1758557 := bbase (se 3 (by rfl) ⟨329729, by rfl⟩ : syracuseStep 1758557 = 659459) (by norm_num)
theorem B2643293 : Blo 1040609 2643293 := bbase (se 3 (by rfl) ⟨495617, by rfl⟩ : syracuseStep 2643293 = 991235) (by norm_num)
theorem B1561973 : Blo 1040609 1561973 := bbase (se 5 (by rfl) ⟨73217, by rfl⟩ : syracuseStep 1561973 = 146435) (by norm_num)
theorem B2348405 : Blo 1040609 2348405 := bbase (se 5 (by rfl) ⟨110081, by rfl⟩ : syracuseStep 2348405 = 220163) (by norm_num)
theorem B1561997 : Blo 1040609 1561997 := bbase (se 3 (by rfl) ⟨292874, by rfl⟩ : syracuseStep 1561997 = 585749) (by norm_num)
theorem B1562021 : Blo 1040609 1562021 := bbase (se 4 (by rfl) ⟨146439, by rfl⟩ : syracuseStep 1562021 = 292879) (by norm_num)
theorem B1562045 : Blo 1040609 1562045 := bbase (se 3 (by rfl) ⟨292883, by rfl⟩ : syracuseStep 1562045 = 585767) (by norm_num)
theorem B2348477 : Blo 1040609 2348477 := bbase (se 3 (by rfl) ⟨440339, by rfl⟩ : syracuseStep 2348477 = 880679) (by norm_num)
theorem B1562069 : Blo 1040609 1562069 := bbase (se 7 (by rfl) ⟨18305, by rfl⟩ : syracuseStep 1562069 = 36611) (by norm_num)
theorem B1758685 : Blo 1040609 1758685 := bbase (se 3 (by rfl) ⟨329753, by rfl⟩ : syracuseStep 1758685 = 659507) (by norm_num)
theorem B1562093 : Blo 1040609 1562093 := bbase (se 3 (by rfl) ⟨292892, by rfl⟩ : syracuseStep 1562093 = 585785) (by norm_num)
theorem B1562117 : Blo 1040609 1562117 := bbase (se 4 (by rfl) ⟨146448, by rfl⟩ : syracuseStep 1562117 = 292897) (by norm_num)
theorem B2348549 : Blo 1040609 2348549 := bbase (se 4 (by rfl) ⟨220176, by rfl⟩ : syracuseStep 2348549 = 440353) (by norm_num)
theorem B1562141 : Blo 1040609 1562141 := bbase (se 3 (by rfl) ⟨292901, by rfl⟩ : syracuseStep 1562141 = 585803) (by norm_num)
theorem B1562165 : Blo 1040609 1562165 := bbase (se 5 (by rfl) ⟨73226, by rfl⟩ : syracuseStep 1562165 = 146453) (by norm_num)
theorem B1758773 : Blo 1040609 1758773 := bbase (se 5 (by rfl) ⟨82442, by rfl⟩ : syracuseStep 1758773 = 164885) (by norm_num)
theorem B1562189 : Blo 1040609 1562189 := bbase (se 3 (by rfl) ⟨292910, by rfl⟩ : syracuseStep 1562189 = 585821) (by norm_num)
theorem B2348621 : Blo 1040609 2348621 := bbase (se 3 (by rfl) ⟨440366, by rfl⟩ : syracuseStep 2348621 = 880733) (by norm_num)
theorem B1562213 : Blo 1040609 1562213 := bbase (se 4 (by rfl) ⟨146457, by rfl⟩ : syracuseStep 1562213 = 292915) (by norm_num)
theorem B1562237 : Blo 1040609 1562237 := bbase (se 3 (by rfl) ⟨292919, by rfl⟩ : syracuseStep 1562237 = 585839) (by norm_num)
theorem B1562261 : Blo 1040609 1562261 := bbase (se 6 (by rfl) ⟨36615, by rfl⟩ : syracuseStep 1562261 = 73231) (by norm_num)
theorem B2348693 : Blo 1040609 2348693 := bbase (se 6 (by rfl) ⟨55047, by rfl⟩ : syracuseStep 2348693 = 110095) (by norm_num)
theorem B1562285 : Blo 1040609 1562285 := bbase (se 3 (by rfl) ⟨292928, by rfl⟩ : syracuseStep 1562285 = 585857) (by norm_num)
theorem B1758901 : Blo 1040609 1758901 := bbase (se 5 (by rfl) ⟨82448, by rfl⟩ : syracuseStep 1758901 = 164897) (by norm_num)
theorem B2643637 : Blo 1040609 2643637 := bbase (se 5 (by rfl) ⟨123920, by rfl⟩ : syracuseStep 2643637 = 247841) (by norm_num)
theorem B1562309 : Blo 1040609 1562309 := bbase (se 4 (by rfl) ⟨146466, by rfl⟩ : syracuseStep 1562309 = 292933) (by norm_num)
theorem B2381525 : Blo 1040609 2381525 := bbase (se 7 (by rfl) ⟨27908, by rfl⟩ : syracuseStep 2381525 = 55817) (by norm_num)
theorem B1562333 : Blo 1040609 1562333 := bbase (se 3 (by rfl) ⟨292937, by rfl⟩ : syracuseStep 1562333 = 585875) (by norm_num)
theorem B2348765 : Blo 1040609 2348765 := bbase (se 3 (by rfl) ⟨440393, by rfl⟩ : syracuseStep 2348765 = 880787) (by norm_num)
theorem B1562357 : Blo 1040609 1562357 := bbase (se 5 (by rfl) ⟨73235, by rfl⟩ : syracuseStep 1562357 = 146471) (by norm_num)
theorem B1562381 : Blo 1040609 1562381 := bbase (se 3 (by rfl) ⟨292946, by rfl⟩ : syracuseStep 1562381 = 585893) (by norm_num)
theorem B1758989 : Blo 1040609 1758989 := bbase (se 3 (by rfl) ⟨329810, by rfl⟩ : syracuseStep 1758989 = 659621) (by norm_num)
theorem B12048149 : Blo 1040609 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B1562405 : Blo 1040609 1562405 := bbase (se 4 (by rfl) ⟨146475, by rfl⟩ : syracuseStep 1562405 = 292951) (by norm_num)
theorem B2348837 : Blo 1040609 2348837 := bbase (se 4 (by rfl) ⟨220203, by rfl⟩ : syracuseStep 2348837 = 440407) (by norm_num)
theorem B2643749 : Blo 1040609 2643749 := bbase (se 4 (by rfl) ⟨247851, by rfl⟩ : syracuseStep 2643749 = 495703) (by norm_num)
theorem B1562429 : Blo 1040609 1562429 := bbase (se 3 (by rfl) ⟨292955, by rfl⟩ : syracuseStep 1562429 = 585911) (by norm_num)
theorem B1562453 : Blo 1040609 1562453 := bbase (se 9 (by rfl) ⟨4577, by rfl⟩ : syracuseStep 1562453 = 9155) (by norm_num)
theorem B1562477 : Blo 1040609 1562477 := bbase (se 3 (by rfl) ⟨292964, by rfl⟩ : syracuseStep 1562477 = 585929) (by norm_num)
theorem B2348909 : Blo 1040609 2348909 := bbase (se 3 (by rfl) ⟨440420, by rfl⟩ : syracuseStep 2348909 = 880841) (by norm_num)
theorem B1562501 : Blo 1040609 1562501 := bbase (se 4 (by rfl) ⟨146484, by rfl⟩ : syracuseStep 1562501 = 292969) (by norm_num)
theorem B1759117 : Blo 1040609 1759117 := bbase (se 3 (by rfl) ⟨329834, by rfl⟩ : syracuseStep 1759117 = 659669) (by norm_num)
theorem B2971541 : Blo 1040609 2971541 := bbase (se 6 (by rfl) ⟨69645, by rfl⟩ : syracuseStep 2971541 = 139291) (by norm_num)
theorem B1562525 : Blo 1040609 1562525 := bbase (se 3 (by rfl) ⟨292973, by rfl⟩ : syracuseStep 1562525 = 585947) (by norm_num)
theorem B1562549 : Blo 1040609 1562549 := bbase (se 5 (by rfl) ⟨73244, by rfl⟩ : syracuseStep 1562549 = 146489) (by norm_num)
theorem B2348981 : Blo 1040609 2348981 := bbase (se 5 (by rfl) ⟨110108, by rfl⟩ : syracuseStep 2348981 = 220217) (by norm_num)
theorem B1562573 : Blo 1040609 1562573 := bbase (se 3 (by rfl) ⟨292982, by rfl⟩ : syracuseStep 1562573 = 585965) (by norm_num)
theorem B22566869 : Blo 1040609 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2676701 : Blo 1040609 2676701 := bbase (se 3 (by rfl) ⟨501881, by rfl⟩ : syracuseStep 2676701 = 1003763) (by norm_num)
theorem B1562597 : Blo 1040609 1562597 := bbase (se 4 (by rfl) ⟨146493, by rfl⟩ : syracuseStep 1562597 = 292987) (by norm_num)
theorem B1759205 : Blo 1040609 1759205 := bbase (se 4 (by rfl) ⟨164925, by rfl⟩ : syracuseStep 1759205 = 329851) (by norm_num)
theorem B2381797 : Blo 1040609 2381797 := bbase (se 4 (by rfl) ⟨223293, by rfl⟩ : syracuseStep 2381797 = 446587) (by norm_num)
theorem B2643941 : Blo 1040609 2643941 := bbase (se 4 (by rfl) ⟨247869, by rfl⟩ : syracuseStep 2643941 = 495739) (by norm_num)
theorem B1562621 : Blo 1040609 1562621 := bbase (se 3 (by rfl) ⟨292991, by rfl⟩ : syracuseStep 1562621 = 585983) (by norm_num)
theorem B2349053 : Blo 1040609 2349053 := bbase (se 3 (by rfl) ⟨440447, by rfl⟩ : syracuseStep 2349053 = 880895) (by norm_num)
theorem B1562645 : Blo 1040609 1562645 := bbase (se 6 (by rfl) ⟨36624, by rfl⟩ : syracuseStep 1562645 = 73249) (by norm_num)
theorem B1562669 : Blo 1040609 1562669 := bbase (se 3 (by rfl) ⟨293000, by rfl⟩ : syracuseStep 1562669 = 586001) (by norm_num)
theorem B1562693 : Blo 1040609 1562693 := bbase (se 4 (by rfl) ⟨146502, by rfl⟩ : syracuseStep 1562693 = 293005) (by norm_num)
theorem B2349125 : Blo 1040609 2349125 := bbase (se 4 (by rfl) ⟨220230, by rfl⟩ : syracuseStep 2349125 = 440461) (by norm_num)
theorem B1562717 : Blo 1040609 1562717 := bbase (se 3 (by rfl) ⟨293009, by rfl⟩ : syracuseStep 1562717 = 586019) (by norm_num)
theorem B1759333 : Blo 1040609 1759333 := bbase (se 4 (by rfl) ⟨164937, by rfl⟩ : syracuseStep 1759333 = 329875) (by norm_num)
theorem B1562741 : Blo 1040609 1562741 := bbase (se 5 (by rfl) ⟨73253, by rfl⟩ : syracuseStep 1562741 = 146507) (by norm_num)
theorem B1562765 : Blo 1040609 1562765 := bbase (se 3 (by rfl) ⟨293018, by rfl⟩ : syracuseStep 1562765 = 586037) (by norm_num)
theorem B2349197 : Blo 1040609 2349197 := bbase (se 3 (by rfl) ⟨440474, by rfl⟩ : syracuseStep 2349197 = 880949) (by norm_num)
theorem B1562789 : Blo 1040609 1562789 := bbase (se 4 (by rfl) ⟨146511, by rfl⟩ : syracuseStep 1562789 = 293023) (by norm_num)
theorem B1562813 : Blo 1040609 1562813 := bbase (se 3 (by rfl) ⟨293027, by rfl⟩ : syracuseStep 1562813 = 586055) (by norm_num)
theorem B1759421 : Blo 1040609 1759421 := bbase (se 3 (by rfl) ⟨329891, by rfl⟩ : syracuseStep 1759421 = 659783) (by norm_num)
theorem B1562837 : Blo 1040609 1562837 := bbase (se 7 (by rfl) ⟨18314, by rfl⟩ : syracuseStep 1562837 = 36629) (by norm_num)
theorem B2349269 : Blo 1040609 2349269 := bbase (se 7 (by rfl) ⟨27530, by rfl⟩ : syracuseStep 2349269 = 55061) (by norm_num)
theorem B1562861 : Blo 1040609 1562861 := bbase (se 3 (by rfl) ⟨293036, by rfl⟩ : syracuseStep 1562861 = 586073) (by norm_num)
theorem B1562885 : Blo 1040609 1562885 := bbase (se 4 (by rfl) ⟨146520, by rfl⟩ : syracuseStep 1562885 = 293041) (by norm_num)
theorem B1562909 : Blo 1040609 1562909 := bbase (se 3 (by rfl) ⟨293045, by rfl⟩ : syracuseStep 1562909 = 586091) (by norm_num)
theorem B2349341 : Blo 1040609 2349341 := bbase (se 3 (by rfl) ⟨440501, by rfl⟩ : syracuseStep 2349341 = 881003) (by norm_num)
theorem B1562933 : Blo 1040609 1562933 := bbase (se 5 (by rfl) ⟨73262, by rfl⟩ : syracuseStep 1562933 = 146525) (by norm_num)
theorem B1759549 : Blo 1040609 1759549 := bbase (se 3 (by rfl) ⟨329915, by rfl⟩ : syracuseStep 1759549 = 659831) (by norm_num)
theorem B1562957 : Blo 1040609 1562957 := bbase (se 3 (by rfl) ⟨293054, by rfl⟩ : syracuseStep 1562957 = 586109) (by norm_num)
theorem B1562981 : Blo 1040609 1562981 := bbase (se 4 (by rfl) ⟨146529, by rfl⟩ : syracuseStep 1562981 = 293059) (by norm_num)
theorem B2349413 : Blo 1040609 2349413 := bbase (se 4 (by rfl) ⟨220257, by rfl⟩ : syracuseStep 2349413 = 440515) (by norm_num)
theorem B1563005 : Blo 1040609 1563005 := bbase (se 3 (by rfl) ⟨293063, by rfl⟩ : syracuseStep 1563005 = 586127) (by norm_num)
theorem B1563029 : Blo 1040609 1563029 := bbase (se 6 (by rfl) ⟨36633, by rfl⟩ : syracuseStep 1563029 = 73267) (by norm_num)
theorem B1759637 : Blo 1040609 1759637 := bbase (se 6 (by rfl) ⟨41241, by rfl⟩ : syracuseStep 1759637 = 82483) (by norm_num)
theorem B1563053 : Blo 1040609 1563053 := bbase (se 3 (by rfl) ⟨293072, by rfl⟩ : syracuseStep 1563053 = 586145) (by norm_num)
theorem B2349485 : Blo 1040609 2349485 := bbase (se 3 (by rfl) ⟨440528, by rfl⟩ : syracuseStep 2349485 = 881057) (by norm_num)
theorem B1563077 : Blo 1040609 1563077 := bbase (se 4 (by rfl) ⟨146538, by rfl⟩ : syracuseStep 1563077 = 293077) (by norm_num)
theorem B1563101 : Blo 1040609 1563101 := bbase (se 3 (by rfl) ⟨293081, by rfl⟩ : syracuseStep 1563101 = 586163) (by norm_num)
theorem B3955189 : Blo 1040609 3955189 := bbase (se 5 (by rfl) ⟨185399, by rfl⟩ : syracuseStep 3955189 = 370799) (by norm_num)
theorem B1563125 : Blo 1040609 1563125 := bbase (se 5 (by rfl) ⟨73271, by rfl⟩ : syracuseStep 1563125 = 146543) (by norm_num)
theorem B2349557 : Blo 1040609 2349557 := bbase (se 5 (by rfl) ⟨110135, by rfl⟩ : syracuseStep 2349557 = 220271) (by norm_num)
theorem B1563149 : Blo 1040609 1563149 := bbase (se 3 (by rfl) ⟨293090, by rfl⟩ : syracuseStep 1563149 = 586181) (by norm_num)
theorem B4512277 : Blo 1040609 4512277 := bbase (se 6 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 4512277 = 211513) (by norm_num)
theorem B1759765 : Blo 1040609 1759765 := bbase (se 6 (by rfl) ⟨41244, by rfl⟩ : syracuseStep 1759765 = 82489) (by norm_num)
theorem B1563173 : Blo 1040609 1563173 := bbase (se 4 (by rfl) ⟨146547, by rfl⟩ : syracuseStep 1563173 = 293095) (by norm_num)
theorem B1563197 : Blo 1040609 1563197 := bbase (se 3 (by rfl) ⟨293099, by rfl⟩ : syracuseStep 1563197 = 586199) (by norm_num)
theorem B2349629 : Blo 1040609 2349629 := bbase (se 3 (by rfl) ⟨440555, by rfl⟩ : syracuseStep 2349629 = 881111) (by norm_num)
theorem B1563221 : Blo 1040609 1563221 := bbase (se 8 (by rfl) ⟨9159, by rfl⟩ : syracuseStep 1563221 = 18319) (by norm_num)
theorem B1563245 : Blo 1040609 1563245 := bbase (se 3 (by rfl) ⟨293108, by rfl⟩ : syracuseStep 1563245 = 586217) (by norm_num)
theorem B1759853 : Blo 1040609 1759853 := bbase (se 3 (by rfl) ⟨329972, by rfl⟩ : syracuseStep 1759853 = 659945) (by norm_num)
theorem B1563269 : Blo 1040609 1563269 := bbase (se 4 (by rfl) ⟨146556, by rfl⟩ : syracuseStep 1563269 = 293113) (by norm_num)
theorem B2349701 : Blo 1040609 2349701 := bbase (se 4 (by rfl) ⟨220284, by rfl⟩ : syracuseStep 2349701 = 440569) (by norm_num)
theorem B1563293 : Blo 1040609 1563293 := bbase (se 3 (by rfl) ⟨293117, by rfl⟩ : syracuseStep 1563293 = 586235) (by norm_num)
theorem B1563317 : Blo 1040609 1563317 := bbase (se 5 (by rfl) ⟨73280, by rfl⟩ : syracuseStep 1563317 = 146561) (by norm_num)
theorem B1563341 : Blo 1040609 1563341 := bbase (se 3 (by rfl) ⟨293126, by rfl⟩ : syracuseStep 1563341 = 586253) (by norm_num)
theorem B2349773 : Blo 1040609 2349773 := bbase (se 3 (by rfl) ⟨440582, by rfl⟩ : syracuseStep 2349773 = 881165) (by norm_num)
theorem B7920341 : Blo 1040609 7920341 := bbase (se 7 (by rfl) ⟨92816, by rfl⟩ : syracuseStep 7920341 = 185633) (by norm_num)
theorem B1563365 : Blo 1040609 1563365 := bbase (se 4 (by rfl) ⟨146565, by rfl⟩ : syracuseStep 1563365 = 293131) (by norm_num)
theorem B1759981 : Blo 1040609 1759981 := bbase (se 3 (by rfl) ⟨329996, by rfl⟩ : syracuseStep 1759981 = 659993) (by norm_num)
theorem B1563389 : Blo 1040609 1563389 := bbase (se 3 (by rfl) ⟨293135, by rfl⟩ : syracuseStep 1563389 = 586271) (by norm_num)
theorem B1563413 : Blo 1040609 1563413 := bbase (se 6 (by rfl) ⟨36642, by rfl⟩ : syracuseStep 1563413 = 73285) (by norm_num)
theorem B2349845 : Blo 1040609 2349845 := bbase (se 6 (by rfl) ⟨55074, by rfl⟩ : syracuseStep 2349845 = 110149) (by norm_num)
theorem B3955493 : Blo 1040609 3955493 := bbase (se 4 (by rfl) ⟨370827, by rfl⟩ : syracuseStep 3955493 = 741655) (by norm_num)
theorem B1563437 : Blo 1040609 1563437 := bbase (se 3 (by rfl) ⟨293144, by rfl⟩ : syracuseStep 1563437 = 586289) (by norm_num)
theorem B1563461 : Blo 1040609 1563461 := bbase (se 4 (by rfl) ⟨146574, by rfl⟩ : syracuseStep 1563461 = 293149) (by norm_num)
theorem B1760069 : Blo 1040609 1760069 := bbase (se 4 (by rfl) ⟨165006, by rfl⟩ : syracuseStep 1760069 = 330013) (by norm_num)
theorem B4447061 : Blo 1040609 4447061 := bbase (se 9 (by rfl) ⟨13028, by rfl⟩ : syracuseStep 4447061 = 26057) (by norm_num)
theorem B1563485 : Blo 1040609 1563485 := bbase (se 3 (by rfl) ⟨293153, by rfl⟩ : syracuseStep 1563485 = 586307) (by norm_num)
theorem B2349917 : Blo 1040609 2349917 := bbase (se 3 (by rfl) ⟨440609, by rfl⟩ : syracuseStep 2349917 = 881219) (by norm_num)
theorem B1563509 : Blo 1040609 1563509 := bbase (se 5 (by rfl) ⟨73289, by rfl⟩ : syracuseStep 1563509 = 146579) (by norm_num)
theorem B1563533 : Blo 1040609 1563533 := bbase (se 3 (by rfl) ⟨293162, by rfl⟩ : syracuseStep 1563533 = 586325) (by norm_num)
theorem B1563557 : Blo 1040609 1563557 := bbase (se 4 (by rfl) ⟨146583, by rfl⟩ : syracuseStep 1563557 = 293167) (by norm_num)
theorem B2349989 : Blo 1040609 2349989 := bbase (se 4 (by rfl) ⟨220311, by rfl⟩ : syracuseStep 2349989 = 440623) (by norm_num)
theorem B1563581 : Blo 1040609 1563581 := bbase (se 3 (by rfl) ⟨293171, by rfl⟩ : syracuseStep 1563581 = 586343) (by norm_num)
theorem B1760197 : Blo 1040609 1760197 := bbase (se 4 (by rfl) ⟨165018, by rfl⟩ : syracuseStep 1760197 = 330037) (by norm_num)
theorem B1563605 : Blo 1040609 1563605 := bbase (se 7 (by rfl) ⟨18323, by rfl⟩ : syracuseStep 1563605 = 36647) (by norm_num)
theorem B1563629 : Blo 1040609 1563629 := bbase (se 3 (by rfl) ⟨293180, by rfl⟩ : syracuseStep 1563629 = 586361) (by norm_num)
theorem B2350061 : Blo 1040609 2350061 := bbase (se 3 (by rfl) ⟨440636, by rfl⟩ : syracuseStep 2350061 = 881273) (by norm_num)
theorem B1563653 : Blo 1040609 1563653 := bbase (se 4 (by rfl) ⟨146592, by rfl⟩ : syracuseStep 1563653 = 293185) (by norm_num)
theorem B1563677 : Blo 1040609 1563677 := bbase (se 3 (by rfl) ⟨293189, by rfl⟩ : syracuseStep 1563677 = 586379) (by norm_num)
theorem B1760285 : Blo 1040609 1760285 := bbase (se 3 (by rfl) ⟨330053, by rfl⟩ : syracuseStep 1760285 = 660107) (by norm_num)
theorem B1563701 : Blo 1040609 1563701 := bbase (se 5 (by rfl) ⟨73298, by rfl⟩ : syracuseStep 1563701 = 146597) (by norm_num)
theorem B2350133 : Blo 1040609 2350133 := bbase (se 5 (by rfl) ⟨110162, by rfl⟩ : syracuseStep 2350133 = 220325) (by norm_num)
theorem B3759173 : Blo 1040609 3759173 := bbase (se 4 (by rfl) ⟨352422, by rfl⟩ : syracuseStep 3759173 = 704845) (by norm_num)
theorem B1563725 : Blo 1040609 1563725 := bbase (se 3 (by rfl) ⟨293198, by rfl⟩ : syracuseStep 1563725 = 586397) (by norm_num)
theorem B1563749 : Blo 1040609 1563749 := bbase (se 4 (by rfl) ⟨146601, by rfl⟩ : syracuseStep 1563749 = 293203) (by norm_num)
theorem B1563773 : Blo 1040609 1563773 := bbase (se 3 (by rfl) ⟨293207, by rfl⟩ : syracuseStep 1563773 = 586415) (by norm_num)
theorem B2350205 : Blo 1040609 2350205 := bbase (se 3 (by rfl) ⟨440663, by rfl⟩ : syracuseStep 2350205 = 881327) (by norm_num)
theorem B1563797 : Blo 1040609 1563797 := bbase (se 6 (by rfl) ⟨36651, by rfl⟩ : syracuseStep 1563797 = 73303) (by norm_num)
theorem B1760413 : Blo 1040609 1760413 := bbase (se 3 (by rfl) ⟨330077, by rfl⟩ : syracuseStep 1760413 = 660155) (by norm_num)
theorem B1563821 : Blo 1040609 1563821 := bbase (se 3 (by rfl) ⟨293216, by rfl⟩ : syracuseStep 1563821 = 586433) (by norm_num)
theorem B1563845 : Blo 1040609 1563845 := bbase (se 4 (by rfl) ⟨146610, by rfl⟩ : syracuseStep 1563845 = 293221) (by norm_num)
theorem B2350277 : Blo 1040609 2350277 := bbase (se 4 (by rfl) ⟨220338, by rfl⟩ : syracuseStep 2350277 = 440677) (by norm_num)
theorem B1563869 : Blo 1040609 1563869 := bbase (se 3 (by rfl) ⟨293225, by rfl⟩ : syracuseStep 1563869 = 586451) (by norm_num)
theorem B1563893 : Blo 1040609 1563893 := bbase (se 5 (by rfl) ⟨73307, by rfl⟩ : syracuseStep 1563893 = 146615) (by norm_num)
theorem B1760501 : Blo 1040609 1760501 := bbase (se 5 (by rfl) ⟨82523, by rfl⟩ : syracuseStep 1760501 = 165047) (by norm_num)
theorem B1170697 : Blo 1040609 1170697 := bbase (se 2 (by rfl) ⟨439011, by rfl⟩ : syracuseStep 1170697 = 878023) (by norm_num)
theorem B1563917 : Blo 1040609 1563917 := bbase (se 3 (by rfl) ⟨293234, by rfl⟩ : syracuseStep 1563917 = 586469) (by norm_num)
theorem B2350349 : Blo 1040609 2350349 := bbase (se 3 (by rfl) ⟨440690, by rfl⟩ : syracuseStep 2350349 = 881381) (by norm_num)
theorem B1563941 : Blo 1040609 1563941 := bbase (se 4 (by rfl) ⟨146619, by rfl⟩ : syracuseStep 1563941 = 293239) (by norm_num)
theorem B1170733 : Blo 1040609 1170733 := bbase (se 3 (by rfl) ⟨219512, by rfl⟩ : syracuseStep 1170733 = 439025) (by norm_num)
theorem B1269049 : Blo 1040609 1269049 := bbase (se 2 (by rfl) ⟨475893, by rfl⟩ : syracuseStep 1269049 = 951787) (by norm_num)
theorem B1563965 : Blo 1040609 1563965 := bbase (se 3 (by rfl) ⟨293243, by rfl⟩ : syracuseStep 1563965 = 586487) (by norm_num)
theorem B1170769 : Blo 1040609 1170769 := bbase (se 2 (by rfl) ⟨439038, by rfl⟩ : syracuseStep 1170769 = 878077) (by norm_num)
theorem B1563989 : Blo 1040609 1563989 := bbase (se 11 (by rfl) ⟨1145, by rfl⟩ : syracuseStep 1563989 = 2291) (by norm_num)
theorem B1564013 : Blo 1040609 1564013 := bbase (se 3 (by rfl) ⟨293252, by rfl⟩ : syracuseStep 1564013 = 586505) (by norm_num)
theorem B1170805 : Blo 1040609 1170805 := bbase (se 5 (by rfl) ⟨54881, by rfl⟩ : syracuseStep 1170805 = 109763) (by norm_num)
theorem B1760629 : Blo 1040609 1760629 := bbase (se 5 (by rfl) ⟨82529, by rfl⟩ : syracuseStep 1760629 = 165059) (by norm_num)
theorem B1564037 : Blo 1040609 1564037 := bbase (se 4 (by rfl) ⟨146628, by rfl⟩ : syracuseStep 1564037 = 293257) (by norm_num)
theorem B1170841 : Blo 1040609 1170841 := bbase (se 2 (by rfl) ⟨439065, by rfl⟩ : syracuseStep 1170841 = 878131) (by norm_num)
theorem B1564061 : Blo 1040609 1564061 := bbase (se 3 (by rfl) ⟨293261, by rfl⟩ : syracuseStep 1564061 = 586523) (by norm_num)
theorem B1564085 : Blo 1040609 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B1170877 : Blo 1040609 1170877 := bbase (se 3 (by rfl) ⟨219539, by rfl⟩ : syracuseStep 1170877 = 439079) (by norm_num)
theorem B2973125 : Blo 1040609 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B1760717 : Blo 1040609 1760717 := bbase (se 3 (by rfl) ⟨330134, by rfl⟩ : syracuseStep 1760717 = 660269) (by norm_num)
theorem B1564109 : Blo 1040609 1564109 := bbase (se 3 (by rfl) ⟨293270, by rfl⟩ : syracuseStep 1564109 = 586541) (by norm_num)
theorem B1170913 : Blo 1040609 1170913 := bbase (se 2 (by rfl) ⟨439092, by rfl⟩ : syracuseStep 1170913 = 878185) (by norm_num)
theorem B1564133 : Blo 1040609 1564133 := bbase (se 4 (by rfl) ⟨146637, by rfl⟩ : syracuseStep 1564133 = 293275) (by norm_num)
theorem B1203697 : Blo 1040609 1203697 := bbase (se 2 (by rfl) ⟨451386, by rfl⟩ : syracuseStep 1203697 = 902773) (by norm_num)
theorem B1564157 : Blo 1040609 1564157 := bbase (se 3 (by rfl) ⟨293279, by rfl⟩ : syracuseStep 1564157 = 586559) (by norm_num)
theorem B1170949 : Blo 1040609 1170949 := bbase (se 4 (by rfl) ⟨109776, by rfl⟩ : syracuseStep 1170949 = 219553) (by norm_num)
theorem B1564181 : Blo 1040609 1564181 := bbase (se 6 (by rfl) ⟨36660, by rfl⟩ : syracuseStep 1564181 = 73321) (by norm_num)
theorem B1170985 : Blo 1040609 1170985 := bbase (se 2 (by rfl) ⟨439119, by rfl⟩ : syracuseStep 1170985 = 878239) (by norm_num)
theorem B1564205 : Blo 1040609 1564205 := bbase (se 3 (by rfl) ⟨293288, by rfl⟩ : syracuseStep 1564205 = 586577) (by norm_num)
theorem B1564229 : Blo 1040609 1564229 := bbase (se 4 (by rfl) ⟨146646, by rfl⟩ : syracuseStep 1564229 = 293293) (by norm_num)
theorem B1171021 : Blo 1040609 1171021 := bbase (se 3 (by rfl) ⟨219566, by rfl⟩ : syracuseStep 1171021 = 439133) (by norm_num)
theorem B1760845 : Blo 1040609 1760845 := bbase (se 3 (by rfl) ⟨330158, by rfl⟩ : syracuseStep 1760845 = 660317) (by norm_num)
theorem B1564253 : Blo 1040609 1564253 := bbase (se 3 (by rfl) ⟨293297, by rfl⟩ : syracuseStep 1564253 = 586595) (by norm_num)
theorem B1171057 : Blo 1040609 1171057 := bbase (se 2 (by rfl) ⟨439146, by rfl⟩ : syracuseStep 1171057 = 878293) (by norm_num)
theorem B1564277 : Blo 1040609 1564277 := bbase (se 5 (by rfl) ⟨73325, by rfl⟩ : syracuseStep 1564277 = 146651) (by norm_num)
theorem B1564301 : Blo 1040609 1564301 := bbase (se 3 (by rfl) ⟨293306, by rfl⟩ : syracuseStep 1564301 = 586613) (by norm_num)
theorem B1171093 : Blo 1040609 1171093 := bbase (se 6 (by rfl) ⟨27447, by rfl⟩ : syracuseStep 1171093 = 54895) (by norm_num)
theorem B1564325 : Blo 1040609 1564325 := bbase (se 4 (by rfl) ⟨146655, by rfl⟩ : syracuseStep 1564325 = 293311) (by norm_num)
theorem B1760933 : Blo 1040609 1760933 := bbase (se 4 (by rfl) ⟨165087, by rfl⟩ : syracuseStep 1760933 = 330175) (by norm_num)
theorem B1171129 : Blo 1040609 1171129 := bbase (se 2 (by rfl) ⟨439173, by rfl⟩ : syracuseStep 1171129 = 878347) (by norm_num)
theorem B1564349 : Blo 1040609 1564349 := bbase (se 3 (by rfl) ⟨293315, by rfl⟩ : syracuseStep 1564349 = 586631) (by norm_num)
theorem B1564373 : Blo 1040609 1564373 := bbase (se 7 (by rfl) ⟨18332, by rfl⟩ : syracuseStep 1564373 = 36665) (by norm_num)
theorem B1171165 : Blo 1040609 1171165 := bbase (se 3 (by rfl) ⟨219593, by rfl⟩ : syracuseStep 1171165 = 439187) (by norm_num)
theorem B1564397 : Blo 1040609 1564397 := bbase (se 3 (by rfl) ⟨293324, by rfl⟩ : syracuseStep 1564397 = 586649) (by norm_num)
theorem B1171201 : Blo 1040609 1171201 := bbase (se 2 (by rfl) ⟨439200, by rfl⟩ : syracuseStep 1171201 = 878401) (by norm_num)
theorem B1564421 : Blo 1040609 1564421 := bbase (se 4 (by rfl) ⟨146664, by rfl⟩ : syracuseStep 1564421 = 293329) (by norm_num)
theorem B1564445 : Blo 1040609 1564445 := bbase (se 3 (by rfl) ⟨293333, by rfl⟩ : syracuseStep 1564445 = 586667) (by norm_num)
theorem B1171237 : Blo 1040609 1171237 := bbase (se 4 (by rfl) ⟨109803, by rfl⟩ : syracuseStep 1171237 = 219607) (by norm_num)
theorem B1761061 : Blo 1040609 1761061 := bbase (se 4 (by rfl) ⟨165099, by rfl⟩ : syracuseStep 1761061 = 330199) (by norm_num)
theorem B1269545 : Blo 1040609 1269545 := bbase (se 2 (by rfl) ⟨476079, by rfl⟩ : syracuseStep 1269545 = 952159) (by norm_num)
theorem B1564469 : Blo 1040609 1564469 := bbase (se 5 (by rfl) ⟨73334, by rfl⟩ : syracuseStep 1564469 = 146669) (by norm_num)
theorem B1171273 : Blo 1040609 1171273 := bbase (se 2 (by rfl) ⟨439227, by rfl⟩ : syracuseStep 1171273 = 878455) (by norm_num)
theorem B1564493 : Blo 1040609 1564493 := bbase (se 3 (by rfl) ⟨293342, by rfl⟩ : syracuseStep 1564493 = 586685) (by norm_num)
theorem B1564517 : Blo 1040609 1564517 := bbase (se 4 (by rfl) ⟨146673, by rfl⟩ : syracuseStep 1564517 = 293347) (by norm_num)
theorem B1171309 : Blo 1040609 1171309 := bbase (se 3 (by rfl) ⟨219620, by rfl⟩ : syracuseStep 1171309 = 439241) (by norm_num)
theorem B1564541 : Blo 1040609 1564541 := bbase (se 3 (by rfl) ⟨293351, by rfl⟩ : syracuseStep 1564541 = 586703) (by norm_num)
theorem B1761149 : Blo 1040609 1761149 := bbase (se 3 (by rfl) ⟨330215, by rfl⟩ : syracuseStep 1761149 = 660431) (by norm_num)
theorem B1171345 : Blo 1040609 1171345 := bbase (se 2 (by rfl) ⟨439254, by rfl⟩ : syracuseStep 1171345 = 878509) (by norm_num)
theorem B1564565 : Blo 1040609 1564565 := bbase (se 6 (by rfl) ⟨36669, by rfl⟩ : syracuseStep 1564565 = 73339) (by norm_num)
theorem B1564589 : Blo 1040609 1564589 := bbase (se 3 (by rfl) ⟨293360, by rfl⟩ : syracuseStep 1564589 = 586721) (by norm_num)
theorem B1171381 : Blo 1040609 1171381 := bbase (se 5 (by rfl) ⟨54908, by rfl⟩ : syracuseStep 1171381 = 109817) (by norm_num)
theorem B3170245 : Blo 1040609 3170245 := bbase (se 4 (by rfl) ⟨297210, by rfl⟩ : syracuseStep 3170245 = 594421) (by norm_num)
theorem B1564613 : Blo 1040609 1564613 := bbase (se 4 (by rfl) ⟨146682, by rfl⟩ : syracuseStep 1564613 = 293365) (by norm_num)
theorem B1171417 : Blo 1040609 1171417 := bbase (se 2 (by rfl) ⟨439281, by rfl⟩ : syracuseStep 1171417 = 878563) (by norm_num)
theorem B1564637 : Blo 1040609 1564637 := bbase (se 3 (by rfl) ⟨293369, by rfl⟩ : syracuseStep 1564637 = 586739) (by norm_num)
theorem B1564661 : Blo 1040609 1564661 := bbase (se 5 (by rfl) ⟨73343, by rfl⟩ : syracuseStep 1564661 = 146687) (by norm_num)
theorem B1761277 : Blo 1040609 1761277 := bbase (se 3 (by rfl) ⟨330239, by rfl⟩ : syracuseStep 1761277 = 660479) (by norm_num)
theorem B1171453 : Blo 1040609 1171453 := bbase (se 3 (by rfl) ⟨219647, by rfl⟩ : syracuseStep 1171453 = 439295) (by norm_num)
theorem B1564685 : Blo 1040609 1564685 := bbase (se 3 (by rfl) ⟨293378, by rfl⟩ : syracuseStep 1564685 = 586757) (by norm_num)
theorem B1171489 : Blo 1040609 1171489 := bbase (se 2 (by rfl) ⟨439308, by rfl⟩ : syracuseStep 1171489 = 878617) (by norm_num)
theorem B1564709 : Blo 1040609 1564709 := bbase (se 4 (by rfl) ⟨146691, by rfl⟩ : syracuseStep 1564709 = 293383) (by norm_num)
theorem B1564733 : Blo 1040609 1564733 := bbase (se 3 (by rfl) ⟨293387, by rfl⟩ : syracuseStep 1564733 = 586775) (by norm_num)
theorem B1171525 : Blo 1040609 1171525 := bbase (se 4 (by rfl) ⟨109830, by rfl⟩ : syracuseStep 1171525 = 219661) (by norm_num)
theorem B1564757 : Blo 1040609 1564757 := bbase (se 8 (by rfl) ⟨9168, by rfl⟩ : syracuseStep 1564757 = 18337) (by norm_num)
theorem B1761365 : Blo 1040609 1761365 := bbase (se 8 (by rfl) ⟨10320, by rfl⟩ : syracuseStep 1761365 = 20641) (by norm_num)
theorem B2973797 : Blo 1040609 2973797 := bbase (se 4 (by rfl) ⟨278793, by rfl⟩ : syracuseStep 2973797 = 557587) (by norm_num)
theorem B1171561 : Blo 1040609 1171561 := bbase (se 2 (by rfl) ⟨439335, by rfl⟩ : syracuseStep 1171561 = 878671) (by norm_num)
theorem B1564781 : Blo 1040609 1564781 := bbase (se 3 (by rfl) ⟨293396, by rfl⟩ : syracuseStep 1564781 = 586793) (by norm_num)
theorem B1564805 : Blo 1040609 1564805 := bbase (se 4 (by rfl) ⟨146700, by rfl⟩ : syracuseStep 1564805 = 293401) (by norm_num)
theorem B1171597 : Blo 1040609 1171597 := bbase (se 3 (by rfl) ⟨219674, by rfl⟩ : syracuseStep 1171597 = 439349) (by norm_num)
theorem B1564829 : Blo 1040609 1564829 := bbase (se 3 (by rfl) ⟨293405, by rfl⟩ : syracuseStep 1564829 = 586811) (by norm_num)
theorem B1171633 : Blo 1040609 1171633 := bbase (se 2 (by rfl) ⟨439362, by rfl⟩ : syracuseStep 1171633 = 878725) (by norm_num)
theorem B1564853 : Blo 1040609 1564853 := bbase (se 5 (by rfl) ⟨73352, by rfl⟩ : syracuseStep 1564853 = 146705) (by norm_num)
theorem B1564877 : Blo 1040609 1564877 := bbase (se 3 (by rfl) ⟨293414, by rfl⟩ : syracuseStep 1564877 = 586829) (by norm_num)
theorem B1171669 : Blo 1040609 1171669 := bbase (se 7 (by rfl) ⟨13730, by rfl⟩ : syracuseStep 1171669 = 27461) (by norm_num)
theorem B8904917 : Blo 1040609 8904917 := bbase (se 7 (by rfl) ⟨104354, by rfl⟩ : syracuseStep 8904917 = 208709) (by norm_num)
theorem B1761493 : Blo 1040609 1761493 := bbase (se 7 (by rfl) ⟨20642, by rfl⟩ : syracuseStep 1761493 = 41285) (by norm_num)
theorem B1564901 : Blo 1040609 1564901 := bbase (se 4 (by rfl) ⟨146709, by rfl⟩ : syracuseStep 1564901 = 293419) (by norm_num)
theorem B1171705 : Blo 1040609 1171705 := bbase (se 2 (by rfl) ⟨439389, by rfl⟩ : syracuseStep 1171705 = 878779) (by norm_num)
theorem B1564925 : Blo 1040609 1564925 := bbase (se 3 (by rfl) ⟨293423, by rfl⟩ : syracuseStep 1564925 = 586847) (by norm_num)
theorem B1564949 : Blo 1040609 1564949 := bbase (se 6 (by rfl) ⟨36678, by rfl⟩ : syracuseStep 1564949 = 73357) (by norm_num)
theorem B1171741 : Blo 1040609 1171741 := bbase (se 3 (by rfl) ⟨219701, by rfl⟩ : syracuseStep 1171741 = 439403) (by norm_num)
theorem B1564973 : Blo 1040609 1564973 := bbase (se 3 (by rfl) ⟨293432, by rfl⟩ : syracuseStep 1564973 = 586865) (by norm_num)
theorem B1761581 : Blo 1040609 1761581 := bbase (se 3 (by rfl) ⟨330296, by rfl⟩ : syracuseStep 1761581 = 660593) (by norm_num)
theorem B1171777 : Blo 1040609 1171777 := bbase (se 2 (by rfl) ⟨439416, by rfl⟩ : syracuseStep 1171777 = 878833) (by norm_num)
theorem B1564997 : Blo 1040609 1564997 := bbase (se 4 (by rfl) ⟨146718, by rfl⟩ : syracuseStep 1564997 = 293437) (by norm_num)
theorem B3760453 : Blo 1040609 3760453 := bbase (se 4 (by rfl) ⟨352542, by rfl⟩ : syracuseStep 3760453 = 705085) (by norm_num)
theorem B1565021 : Blo 1040609 1565021 := bbase (se 3 (by rfl) ⟨293441, by rfl⟩ : syracuseStep 1565021 = 586883) (by norm_num)
theorem B1171813 : Blo 1040609 1171813 := bbase (se 4 (by rfl) ⟨109857, by rfl⟩ : syracuseStep 1171813 = 219715) (by norm_num)
theorem B1565045 : Blo 1040609 1565045 := bbase (se 5 (by rfl) ⟨73361, by rfl⟩ : syracuseStep 1565045 = 146723) (by norm_num)
theorem B1171849 : Blo 1040609 1171849 := bbase (se 2 (by rfl) ⟨439443, by rfl⟩ : syracuseStep 1171849 = 878887) (by norm_num)
theorem B1565069 : Blo 1040609 1565069 := bbase (se 3 (by rfl) ⟨293450, by rfl⟩ : syracuseStep 1565069 = 586901) (by norm_num)
theorem B1565093 : Blo 1040609 1565093 := bbase (se 4 (by rfl) ⟨146727, by rfl⟩ : syracuseStep 1565093 = 293455) (by norm_num)
theorem B1171885 : Blo 1040609 1171885 := bbase (se 3 (by rfl) ⟨219728, by rfl⟩ : syracuseStep 1171885 = 439457) (by norm_num)
theorem B1761709 : Blo 1040609 1761709 := bbase (se 3 (by rfl) ⟨330320, by rfl⟩ : syracuseStep 1761709 = 660641) (by norm_num)
theorem B1565117 : Blo 1040609 1565117 := bbase (se 3 (by rfl) ⟨293459, by rfl⟩ : syracuseStep 1565117 = 586919) (by norm_num)
theorem B1171921 : Blo 1040609 1171921 := bbase (se 2 (by rfl) ⟨439470, by rfl⟩ : syracuseStep 1171921 = 878941) (by norm_num)
theorem B1565141 : Blo 1040609 1565141 := bbase (se 7 (by rfl) ⟨18341, by rfl⟩ : syracuseStep 1565141 = 36683) (by norm_num)
theorem B1335781 : Blo 1040609 1335781 := bbase (se 4 (by rfl) ⟨125229, by rfl⟩ : syracuseStep 1335781 = 250459) (by norm_num)
theorem B1565165 : Blo 1040609 1565165 := bbase (se 3 (by rfl) ⟨293468, by rfl⟩ : syracuseStep 1565165 = 586937) (by norm_num)
theorem B1171957 : Blo 1040609 1171957 := bbase (se 5 (by rfl) ⟨54935, by rfl⟩ : syracuseStep 1171957 = 109871) (by norm_num)
theorem B1565189 : Blo 1040609 1565189 := bbase (se 4 (by rfl) ⟨146736, by rfl⟩ : syracuseStep 1565189 = 293473) (by norm_num)
theorem B1761797 : Blo 1040609 1761797 := bbase (se 4 (by rfl) ⟨165168, by rfl⟩ : syracuseStep 1761797 = 330337) (by norm_num)
theorem B2974229 : Blo 1040609 2974229 := bbase (se 6 (by rfl) ⟨69708, by rfl⟩ : syracuseStep 2974229 = 139417) (by norm_num)
theorem B1171993 : Blo 1040609 1171993 := bbase (se 2 (by rfl) ⟨439497, by rfl⟩ : syracuseStep 1171993 = 878995) (by norm_num)
theorem B1565213 : Blo 1040609 1565213 := bbase (se 3 (by rfl) ⟨293477, by rfl⟩ : syracuseStep 1565213 = 586955) (by norm_num)
theorem B2253349 : Blo 1040609 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B1565237 : Blo 1040609 1565237 := bbase (se 5 (by rfl) ⟨73370, by rfl⟩ : syracuseStep 1565237 = 146741) (by norm_num)
theorem B1172029 : Blo 1040609 1172029 := bbase (se 3 (by rfl) ⟨219755, by rfl⟩ : syracuseStep 1172029 = 439511) (by norm_num)
theorem B4448837 : Blo 1040609 4448837 := bbase (se 4 (by rfl) ⟨417078, by rfl⟩ : syracuseStep 4448837 = 834157) (by norm_num)
theorem B1565261 : Blo 1040609 1565261 := bbase (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) (by norm_num)
theorem B1172065 : Blo 1040609 1172065 := bbase (se 2 (by rfl) ⟨439524, by rfl⟩ : syracuseStep 1172065 = 879049) (by norm_num)
theorem B1565285 : Blo 1040609 1565285 := bbase (se 4 (by rfl) ⟨146745, by rfl⟩ : syracuseStep 1565285 = 293491) (by norm_num)
theorem B1565309 : Blo 1040609 1565309 := bbase (se 3 (by rfl) ⟨293495, by rfl⟩ : syracuseStep 1565309 = 586991) (by norm_num)
theorem B1172101 : Blo 1040609 1172101 := bbase (se 4 (by rfl) ⟨109884, by rfl⟩ : syracuseStep 1172101 = 219769) (by norm_num)
theorem B1761925 : Blo 1040609 1761925 := bbase (se 4 (by rfl) ⟨165180, by rfl⟩ : syracuseStep 1761925 = 330361) (by norm_num)
theorem B1565333 : Blo 1040609 1565333 := bbase (se 6 (by rfl) ⟨36687, by rfl⟩ : syracuseStep 1565333 = 73375) (by norm_num)
theorem B1172137 : Blo 1040609 1172137 := bbase (se 2 (by rfl) ⟨439551, by rfl⟩ : syracuseStep 1172137 = 879103) (by norm_num)
theorem B1565357 : Blo 1040609 1565357 := bbase (se 3 (by rfl) ⟨293504, by rfl⟩ : syracuseStep 1565357 = 587009) (by norm_num)
theorem B1565381 : Blo 1040609 1565381 := bbase (se 4 (by rfl) ⟨146754, by rfl⟩ : syracuseStep 1565381 = 293509) (by norm_num)
theorem B1172173 : Blo 1040609 1172173 := bbase (se 3 (by rfl) ⟨219782, by rfl⟩ : syracuseStep 1172173 = 439565) (by norm_num)
theorem B1565405 : Blo 1040609 1565405 := bbase (se 3 (by rfl) ⟨293513, by rfl⟩ : syracuseStep 1565405 = 587027) (by norm_num)
theorem B1762013 : Blo 1040609 1762013 := bbase (se 3 (by rfl) ⟨330377, by rfl⟩ : syracuseStep 1762013 = 660755) (by norm_num)
theorem B1172209 : Blo 1040609 1172209 := bbase (se 2 (by rfl) ⟨439578, by rfl⟩ : syracuseStep 1172209 = 879157) (by norm_num)
theorem B1565429 : Blo 1040609 1565429 := bbase (se 5 (by rfl) ⟨73379, by rfl⟩ : syracuseStep 1565429 = 146759) (by norm_num)
theorem B2286341 : Blo 1040609 2286341 := bbase (se 4 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 2286341 = 428689) (by norm_num)
theorem B1565453 : Blo 1040609 1565453 := bbase (se 3 (by rfl) ⟨293522, by rfl⟩ : syracuseStep 1565453 = 587045) (by norm_num)
theorem B1172245 : Blo 1040609 1172245 := bbase (se 6 (by rfl) ⟨27474, by rfl⟩ : syracuseStep 1172245 = 54949) (by norm_num)
theorem B1565477 : Blo 1040609 1565477 := bbase (se 4 (by rfl) ⟨146763, by rfl⟩ : syracuseStep 1565477 = 293527) (by norm_num)
theorem B1336109 : Blo 1040609 1336109 := bbase (se 3 (by rfl) ⟨250520, by rfl⟩ : syracuseStep 1336109 = 501041) (by norm_num)
theorem B4449077 : Blo 1040609 4449077 := bbase (se 5 (by rfl) ⟨208550, by rfl⟩ : syracuseStep 4449077 = 417101) (by norm_num)
theorem B1172281 : Blo 1040609 1172281 := bbase (se 2 (by rfl) ⟨439605, by rfl⟩ : syracuseStep 1172281 = 879211) (by norm_num)
theorem B1565501 : Blo 1040609 1565501 := bbase (se 3 (by rfl) ⟨293531, by rfl⟩ : syracuseStep 1565501 = 587063) (by norm_num)
theorem B1565525 : Blo 1040609 1565525 := bbase (se 9 (by rfl) ⟨4586, by rfl⟩ : syracuseStep 1565525 = 9173) (by norm_num)
theorem B1172317 : Blo 1040609 1172317 := bbase (se 3 (by rfl) ⟨219809, by rfl⟩ : syracuseStep 1172317 = 439619) (by norm_num)
theorem B1762141 : Blo 1040609 1762141 := bbase (se 3 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 1762141 = 660803) (by norm_num)
theorem B3957605 : Blo 1040609 3957605 := bbase (se 4 (by rfl) ⟨371025, by rfl⟩ : syracuseStep 3957605 = 742051) (by norm_num)
theorem B1565549 : Blo 1040609 1565549 := bbase (se 3 (by rfl) ⟨293540, by rfl⟩ : syracuseStep 1565549 = 587081) (by norm_num)
theorem B1172353 : Blo 1040609 1172353 := bbase (se 2 (by rfl) ⟨439632, by rfl⟩ : syracuseStep 1172353 = 879265) (by norm_num)
theorem B1565573 : Blo 1040609 1565573 := bbase (se 4 (by rfl) ⟨146772, by rfl⟩ : syracuseStep 1565573 = 293545) (by norm_num)
theorem B1565597 : Blo 1040609 1565597 := bbase (se 3 (by rfl) ⟨293549, by rfl⟩ : syracuseStep 1565597 = 587099) (by norm_num)
theorem B1172389 : Blo 1040609 1172389 := bbase (se 4 (by rfl) ⟨109911, by rfl⟩ : syracuseStep 1172389 = 219823) (by norm_num)
theorem B1565621 : Blo 1040609 1565621 := bbase (se 5 (by rfl) ⟨73388, by rfl⟩ : syracuseStep 1565621 = 146777) (by norm_num)
theorem B1762229 : Blo 1040609 1762229 := bbase (se 5 (by rfl) ⟨82604, by rfl⟩ : syracuseStep 1762229 = 165209) (by norm_num)
theorem B1172425 : Blo 1040609 1172425 := bbase (se 2 (by rfl) ⟨439659, by rfl⟩ : syracuseStep 1172425 = 879319) (by norm_num)
theorem B1565645 : Blo 1040609 1565645 := bbase (se 3 (by rfl) ⟨293558, by rfl⟩ : syracuseStep 1565645 = 587117) (by norm_num)
theorem B3335141 : Blo 1040609 3335141 := bbase (se 4 (by rfl) ⟨312669, by rfl⟩ : syracuseStep 3335141 = 625339) (by norm_num)
theorem B1565669 : Blo 1040609 1565669 := bbase (se 4 (by rfl) ⟨146781, by rfl⟩ : syracuseStep 1565669 = 293563) (by norm_num)
theorem B1172461 : Blo 1040609 1172461 := bbase (se 3 (by rfl) ⟨219836, by rfl⟩ : syracuseStep 1172461 = 439673) (by norm_num)
theorem B1565693 : Blo 1040609 1565693 := bbase (se 3 (by rfl) ⟨293567, by rfl⟩ : syracuseStep 1565693 = 587135) (by norm_num)
theorem B1172497 : Blo 1040609 1172497 := bbase (se 2 (by rfl) ⟨439686, by rfl⟩ : syracuseStep 1172497 = 879373) (by norm_num)
theorem B1565717 : Blo 1040609 1565717 := bbase (se 6 (by rfl) ⟨36696, by rfl⟩ : syracuseStep 1565717 = 73393) (by norm_num)
theorem B1565741 : Blo 1040609 1565741 := bbase (se 3 (by rfl) ⟨293576, by rfl⟩ : syracuseStep 1565741 = 587153) (by norm_num)
theorem B1172533 : Blo 1040609 1172533 := bbase (se 5 (by rfl) ⟨54962, by rfl⟩ : syracuseStep 1172533 = 109925) (by norm_num)
theorem B1762357 : Blo 1040609 1762357 := bbase (se 5 (by rfl) ⟨82610, by rfl⟩ : syracuseStep 1762357 = 165221) (by norm_num)
theorem B1565765 : Blo 1040609 1565765 := bbase (se 4 (by rfl) ⟨146790, by rfl⟩ : syracuseStep 1565765 = 293581) (by norm_num)
theorem B7529557 : Blo 1040609 7529557 := bbase (se 8 (by rfl) ⟨44118, by rfl⟩ : syracuseStep 7529557 = 88237) (by norm_num)
theorem B1172569 : Blo 1040609 1172569 := bbase (se 2 (by rfl) ⟨439713, by rfl⟩ : syracuseStep 1172569 = 879427) (by norm_num)
theorem B1565789 : Blo 1040609 1565789 := bbase (se 3 (by rfl) ⟨293585, by rfl⟩ : syracuseStep 1565789 = 587171) (by norm_num)
theorem B1565813 : Blo 1040609 1565813 := bbase (se 5 (by rfl) ⟨73397, by rfl⟩ : syracuseStep 1565813 = 146795) (by norm_num)
theorem B1172605 : Blo 1040609 1172605 := bbase (se 3 (by rfl) ⟨219863, by rfl⟩ : syracuseStep 1172605 = 439727) (by norm_num)
theorem B3957893 : Blo 1040609 3957893 := bbase (se 4 (by rfl) ⟨371052, by rfl⟩ : syracuseStep 3957893 = 742105) (by norm_num)
theorem B1565837 : Blo 1040609 1565837 := bbase (se 3 (by rfl) ⟨293594, by rfl⟩ : syracuseStep 1565837 = 587189) (by norm_num)
theorem B1762445 : Blo 1040609 1762445 := bbase (se 3 (by rfl) ⟨330458, by rfl⟩ : syracuseStep 1762445 = 660917) (by norm_num)
theorem B11854997 : Blo 1040609 11854997 := bbase (se 6 (by rfl) ⟨277851, by rfl⟩ : syracuseStep 11854997 = 555703) (by norm_num)
theorem B1172641 : Blo 1040609 1172641 := bbase (se 2 (by rfl) ⟨439740, by rfl⟩ : syracuseStep 1172641 = 879481) (by norm_num)
theorem B1565861 : Blo 1040609 1565861 := bbase (se 4 (by rfl) ⟨146799, by rfl⟩ : syracuseStep 1565861 = 293599) (by norm_num)
theorem B1565885 : Blo 1040609 1565885 := bbase (se 3 (by rfl) ⟨293603, by rfl⟩ : syracuseStep 1565885 = 587207) (by norm_num)
theorem B1172677 : Blo 1040609 1172677 := bbase (se 4 (by rfl) ⟨109938, by rfl⟩ : syracuseStep 1172677 = 219877) (by norm_num)
theorem B1565909 : Blo 1040609 1565909 := bbase (se 7 (by rfl) ⟨18350, by rfl⟩ : syracuseStep 1565909 = 36701) (by norm_num)
theorem B1172713 : Blo 1040609 1172713 := bbase (se 2 (by rfl) ⟨439767, by rfl⟩ : syracuseStep 1172713 = 879535) (by norm_num)
theorem B1565933 : Blo 1040609 1565933 := bbase (se 3 (by rfl) ⟨293612, by rfl⟩ : syracuseStep 1565933 = 587225) (by norm_num)
theorem B5268725 : Blo 1040609 5268725 := bbase (se 5 (by rfl) ⟨246971, by rfl⟩ : syracuseStep 5268725 = 493943) (by norm_num)
theorem B1565957 : Blo 1040609 1565957 := bbase (se 4 (by rfl) ⟨146808, by rfl⟩ : syracuseStep 1565957 = 293617) (by norm_num)
theorem B1172749 : Blo 1040609 1172749 := bbase (se 3 (by rfl) ⟨219890, by rfl⟩ : syracuseStep 1172749 = 439781) (by norm_num)
theorem B1762573 : Blo 1040609 1762573 := bbase (se 3 (by rfl) ⟨330482, by rfl⟩ : syracuseStep 1762573 = 660965) (by norm_num)
theorem B1565981 : Blo 1040609 1565981 := bbase (se 3 (by rfl) ⟨293621, by rfl⟩ : syracuseStep 1565981 = 587243) (by norm_num)
theorem B1172785 : Blo 1040609 1172785 := bbase (se 2 (by rfl) ⟨439794, by rfl⟩ : syracuseStep 1172785 = 879589) (by norm_num)
theorem B1566005 : Blo 1040609 1566005 := bbase (se 5 (by rfl) ⟨73406, by rfl⟩ : syracuseStep 1566005 = 146813) (by norm_num)
theorem B1566029 : Blo 1040609 1566029 := bbase (se 3 (by rfl) ⟨293630, by rfl⟩ : syracuseStep 1566029 = 587261) (by norm_num)
theorem B1172821 : Blo 1040609 1172821 := bbase (se 12 (by rfl) ⟨429, by rfl⟩ : syracuseStep 1172821 = 859) (by norm_num)
theorem B1566053 : Blo 1040609 1566053 := bbase (se 4 (by rfl) ⟨146817, by rfl⟩ : syracuseStep 1566053 = 293635) (by norm_num)
theorem B1762661 : Blo 1040609 1762661 := bbase (se 4 (by rfl) ⟨165249, by rfl⟩ : syracuseStep 1762661 = 330499) (by norm_num)
theorem B1172857 : Blo 1040609 1172857 := bbase (se 2 (by rfl) ⟨439821, by rfl⟩ : syracuseStep 1172857 = 879643) (by norm_num)
theorem B1566077 : Blo 1040609 1566077 := bbase (se 3 (by rfl) ⟨293639, by rfl⟩ : syracuseStep 1566077 = 587279) (by norm_num)
theorem B1566101 : Blo 1040609 1566101 := bbase (se 6 (by rfl) ⟨36705, by rfl⟩ : syracuseStep 1566101 = 73411) (by norm_num)
theorem B1172893 : Blo 1040609 1172893 := bbase (se 3 (by rfl) ⟨219917, by rfl⟩ : syracuseStep 1172893 = 439835) (by norm_num)
theorem B1566125 : Blo 1040609 1566125 := bbase (se 3 (by rfl) ⟨293648, by rfl⟩ : syracuseStep 1566125 = 587297) (by norm_num)
theorem B1172929 : Blo 1040609 1172929 := bbase (se 2 (by rfl) ⟨439848, by rfl⟩ : syracuseStep 1172929 = 879697) (by norm_num)
theorem B1566149 : Blo 1040609 1566149 := bbase (se 4 (by rfl) ⟨146826, by rfl⟩ : syracuseStep 1566149 = 293653) (by norm_num)
theorem B1566173 : Blo 1040609 1566173 := bbase (se 3 (by rfl) ⟨293657, by rfl⟩ : syracuseStep 1566173 = 587315) (by norm_num)
theorem B4220389 : Blo 1040609 4220389 := bbase (se 4 (by rfl) ⟨395661, by rfl⟩ : syracuseStep 4220389 = 791323) (by norm_num)
theorem B1172965 : Blo 1040609 1172965 := bbase (se 4 (by rfl) ⟨109965, by rfl⟩ : syracuseStep 1172965 = 219931) (by norm_num)
theorem B1566197 : Blo 1040609 1566197 := bbase (se 5 (by rfl) ⟨73415, by rfl⟩ : syracuseStep 1566197 = 146831) (by norm_num)
theorem B1173001 : Blo 1040609 1173001 := bbase (se 2 (by rfl) ⟨439875, by rfl⟩ : syracuseStep 1173001 = 879751) (by norm_num)
theorem B1566221 : Blo 1040609 1566221 := bbase (se 3 (by rfl) ⟨293666, by rfl⟩ : syracuseStep 1566221 = 587333) (by norm_num)
theorem B1566245 : Blo 1040609 1566245 := bbase (se 4 (by rfl) ⟨146835, by rfl⟩ : syracuseStep 1566245 = 293671) (by norm_num)
theorem B1173037 : Blo 1040609 1173037 := bbase (se 3 (by rfl) ⟨219944, by rfl⟩ : syracuseStep 1173037 = 439889) (by norm_num)
theorem B1566269 : Blo 1040609 1566269 := bbase (se 3 (by rfl) ⟨293675, by rfl⟩ : syracuseStep 1566269 = 587351) (by norm_num)
theorem B1173073 : Blo 1040609 1173073 := bbase (se 2 (by rfl) ⟨439902, by rfl⟩ : syracuseStep 1173073 = 879805) (by norm_num)
theorem B1566293 : Blo 1040609 1566293 := bbase (se 8 (by rfl) ⟨9177, by rfl⟩ : syracuseStep 1566293 = 18355) (by norm_num)
theorem B1566317 : Blo 1040609 1566317 := bbase (se 3 (by rfl) ⟨293684, by rfl⟩ : syracuseStep 1566317 = 587369) (by norm_num)
theorem B1173109 : Blo 1040609 1173109 := bbase (se 5 (by rfl) ⟨54989, by rfl⟩ : syracuseStep 1173109 = 109979) (by norm_num)
theorem B1566341 : Blo 1040609 1566341 := bbase (se 4 (by rfl) ⟨146844, by rfl⟩ : syracuseStep 1566341 = 293689) (by norm_num)
theorem B1336981 : Blo 1040609 1336981 := bbase (se 6 (by rfl) ⟨31335, by rfl⟩ : syracuseStep 1336981 = 62671) (by norm_num)
theorem B1173145 : Blo 1040609 1173145 := bbase (se 2 (by rfl) ⟨439929, by rfl⟩ : syracuseStep 1173145 = 879859) (by norm_num)
theorem B1566365 : Blo 1040609 1566365 := bbase (se 3 (by rfl) ⟨293693, by rfl⟩ : syracuseStep 1566365 = 587387) (by norm_num)
theorem B1566389 : Blo 1040609 1566389 := bbase (se 5 (by rfl) ⟨73424, by rfl⟩ : syracuseStep 1566389 = 146849) (by norm_num)
theorem B1173181 : Blo 1040609 1173181 := bbase (se 3 (by rfl) ⟨219971, by rfl⟩ : syracuseStep 1173181 = 439943) (by norm_num)
theorem B1566413 : Blo 1040609 1566413 := bbase (se 3 (by rfl) ⟨293702, by rfl⟩ : syracuseStep 1566413 = 587405) (by norm_num)
theorem B1173217 : Blo 1040609 1173217 := bbase (se 2 (by rfl) ⟨439956, by rfl⟩ : syracuseStep 1173217 = 879913) (by norm_num)
theorem B1566437 : Blo 1040609 1566437 := bbase (se 4 (by rfl) ⟨146853, by rfl⟩ : syracuseStep 1566437 = 293707) (by norm_num)
theorem B1566461 : Blo 1040609 1566461 := bbase (se 3 (by rfl) ⟨293711, by rfl⟩ : syracuseStep 1566461 = 587423) (by norm_num)
theorem B1173253 : Blo 1040609 1173253 := bbase (se 4 (by rfl) ⟨109992, by rfl⟩ : syracuseStep 1173253 = 219985) (by norm_num)
theorem B1566485 : Blo 1040609 1566485 := bbase (se 6 (by rfl) ⟨36714, by rfl⟩ : syracuseStep 1566485 = 73429) (by norm_num)
theorem B1173289 : Blo 1040609 1173289 := bbase (se 2 (by rfl) ⟨439983, by rfl⟩ : syracuseStep 1173289 = 879967) (by norm_num)
theorem B1566509 : Blo 1040609 1566509 := bbase (se 3 (by rfl) ⟨293720, by rfl⟩ : syracuseStep 1566509 = 587441) (by norm_num)
theorem B1566533 : Blo 1040609 1566533 := bbase (se 4 (by rfl) ⟨146862, by rfl⟩ : syracuseStep 1566533 = 293725) (by norm_num)
theorem B1173325 : Blo 1040609 1173325 := bbase (se 3 (by rfl) ⟨219998, by rfl⟩ : syracuseStep 1173325 = 439997) (by norm_num)
theorem B1566557 : Blo 1040609 1566557 := bbase (se 3 (by rfl) ⟨293729, by rfl⟩ : syracuseStep 1566557 = 587459) (by norm_num)
theorem B1173361 : Blo 1040609 1173361 := bbase (se 2 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 1173361 = 880021) (by norm_num)
theorem B1566581 : Blo 1040609 1566581 := bbase (se 5 (by rfl) ⟨73433, by rfl⟩ : syracuseStep 1566581 = 146867) (by norm_num)
theorem B1566605 : Blo 1040609 1566605 := bbase (se 3 (by rfl) ⟨293738, by rfl⟩ : syracuseStep 1566605 = 587477) (by norm_num)
theorem B1173397 : Blo 1040609 1173397 := bbase (se 6 (by rfl) ⟨27501, by rfl⟩ : syracuseStep 1173397 = 55003) (by norm_num)
theorem B1566629 : Blo 1040609 1566629 := bbase (se 4 (by rfl) ⟨146871, by rfl⟩ : syracuseStep 1566629 = 293743) (by norm_num)
theorem B1173433 : Blo 1040609 1173433 := bbase (se 2 (by rfl) ⟨440037, by rfl⟩ : syracuseStep 1173433 = 880075) (by norm_num)
theorem B1566653 : Blo 1040609 1566653 := bbase (se 3 (by rfl) ⟨293747, by rfl⟩ : syracuseStep 1566653 = 587495) (by norm_num)
theorem B1566677 : Blo 1040609 1566677 := bbase (se 7 (by rfl) ⟨18359, by rfl⟩ : syracuseStep 1566677 = 36719) (by norm_num)
theorem B1173469 : Blo 1040609 1173469 := bbase (se 3 (by rfl) ⟨220025, by rfl⟩ : syracuseStep 1173469 = 440051) (by norm_num)
theorem B1566701 : Blo 1040609 1566701 := bbase (se 3 (by rfl) ⟨293756, by rfl⟩ : syracuseStep 1566701 = 587513) (by norm_num)
theorem B1173505 : Blo 1040609 1173505 := bbase (se 2 (by rfl) ⟨440064, by rfl⟩ : syracuseStep 1173505 = 880129) (by norm_num)
theorem B5007365 : Blo 1040609 5007365 := bbase (se 4 (by rfl) ⟨469440, by rfl⟩ : syracuseStep 5007365 = 938881) (by norm_num)
theorem B1566725 : Blo 1040609 1566725 := bbase (se 4 (by rfl) ⟨146880, by rfl⟩ : syracuseStep 1566725 = 293761) (by norm_num)
theorem B1566749 : Blo 1040609 1566749 := bbase (se 3 (by rfl) ⟨293765, by rfl⟩ : syracuseStep 1566749 = 587531) (by norm_num)
theorem B1173541 : Blo 1040609 1173541 := bbase (se 4 (by rfl) ⟨110019, by rfl⟩ : syracuseStep 1173541 = 220039) (by norm_num)
theorem B1566773 : Blo 1040609 1566773 := bbase (se 5 (by rfl) ⟨73442, by rfl⟩ : syracuseStep 1566773 = 146885) (by norm_num)
theorem B1173577 : Blo 1040609 1173577 := bbase (se 2 (by rfl) ⟨440091, by rfl⟩ : syracuseStep 1173577 = 880183) (by norm_num)
theorem B1566797 : Blo 1040609 1566797 := bbase (se 3 (by rfl) ⟨293774, by rfl⟩ : syracuseStep 1566797 = 587549) (by norm_num)
theorem B1566821 : Blo 1040609 1566821 := bbase (se 4 (by rfl) ⟨146889, by rfl⟩ : syracuseStep 1566821 = 293779) (by norm_num)
theorem B1173613 : Blo 1040609 1173613 := bbase (se 3 (by rfl) ⟨220052, by rfl⟩ : syracuseStep 1173613 = 440105) (by norm_num)
theorem B1566845 : Blo 1040609 1566845 := bbase (se 3 (by rfl) ⟨293783, by rfl⟩ : syracuseStep 1566845 = 587567) (by norm_num)
theorem B1173649 : Blo 1040609 1173649 := bbase (se 2 (by rfl) ⟨440118, by rfl⟩ : syracuseStep 1173649 = 880237) (by norm_num)
theorem B1566869 : Blo 1040609 1566869 := bbase (se 6 (by rfl) ⟨36723, by rfl⟩ : syracuseStep 1566869 = 73447) (by norm_num)
theorem B1566893 : Blo 1040609 1566893 := bbase (se 3 (by rfl) ⟨293792, by rfl⟩ : syracuseStep 1566893 = 587585) (by norm_num)
theorem B1173685 : Blo 1040609 1173685 := bbase (se 5 (by rfl) ⟨55016, by rfl⟩ : syracuseStep 1173685 = 110033) (by norm_num)
theorem B1173721 : Blo 1040609 1173721 := bbase (se 2 (by rfl) ⟨440145, by rfl⟩ : syracuseStep 1173721 = 880291) (by norm_num)
theorem B1173757 : Blo 1040609 1173757 := bbase (se 3 (by rfl) ⟨220079, by rfl⟩ : syracuseStep 1173757 = 440159) (by norm_num)
theorem B1173793 : Blo 1040609 1173793 := bbase (se 2 (by rfl) ⟨440172, by rfl⟩ : syracuseStep 1173793 = 880345) (by norm_num)
theorem B3959077 : Blo 1040609 3959077 := bbase (se 4 (by rfl) ⟨371163, by rfl⟩ : syracuseStep 3959077 = 742327) (by norm_num)
theorem B1173829 : Blo 1040609 1173829 := bbase (se 4 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 1173829 = 220093) (by norm_num)
theorem B1173865 : Blo 1040609 1173865 := bbase (se 2 (by rfl) ⟨440199, by rfl⟩ : syracuseStep 1173865 = 880399) (by norm_num)
theorem B3336565 : Blo 1040609 3336565 := bbase (se 5 (by rfl) ⟨156401, by rfl⟩ : syracuseStep 3336565 = 312803) (by norm_num)
theorem B1173901 : Blo 1040609 1173901 := bbase (se 3 (by rfl) ⟨220106, by rfl⟩ : syracuseStep 1173901 = 440213) (by norm_num)
theorem B1173937 : Blo 1040609 1173937 := bbase (se 2 (by rfl) ⟨440226, by rfl⟩ : syracuseStep 1173937 = 880453) (by norm_num)
theorem B1173973 : Blo 1040609 1173973 := bbase (se 7 (by rfl) ⟨13757, by rfl⟩ : syracuseStep 1173973 = 27515) (by norm_num)
theorem B1174009 : Blo 1040609 1174009 := bbase (se 2 (by rfl) ⟨440253, by rfl⟩ : syracuseStep 1174009 = 880507) (by norm_num)
theorem B5270021 : Blo 1040609 5270021 := bbase (se 4 (by rfl) ⟨494064, by rfl⟩ : syracuseStep 5270021 = 988129) (by norm_num)
theorem B1174045 : Blo 1040609 1174045 := bbase (se 3 (by rfl) ⟨220133, by rfl⟩ : syracuseStep 1174045 = 440267) (by norm_num)
theorem B1174081 : Blo 1040609 1174081 := bbase (se 2 (by rfl) ⟨440280, by rfl⟩ : syracuseStep 1174081 = 880561) (by norm_num)
theorem B3959381 : Blo 1040609 3959381 := bbase (se 8 (by rfl) ⟨23199, by rfl⟩ : syracuseStep 3959381 = 46399) (by norm_num)
theorem B1174117 : Blo 1040609 1174117 := bbase (se 4 (by rfl) ⟨110073, by rfl⟩ : syracuseStep 1174117 = 220147) (by norm_num)
theorem B1174153 : Blo 1040609 1174153 := bbase (se 2 (by rfl) ⟨440307, by rfl⟩ : syracuseStep 1174153 = 880615) (by norm_num)
theorem B1174189 : Blo 1040609 1174189 := bbase (se 3 (by rfl) ⟨220160, by rfl⟩ : syracuseStep 1174189 = 440321) (by norm_num)
theorem B1174225 : Blo 1040609 1174225 := bbase (se 2 (by rfl) ⟨440334, by rfl⟩ : syracuseStep 1174225 = 880669) (by norm_num)
theorem B1174261 : Blo 1040609 1174261 := bbase (se 5 (by rfl) ⟨55043, by rfl⟩ : syracuseStep 1174261 = 110087) (by norm_num)
theorem B1174297 : Blo 1040609 1174297 := bbase (se 2 (by rfl) ⟨440361, by rfl⟩ : syracuseStep 1174297 = 880723) (by norm_num)
theorem B3337013 : Blo 1040609 3337013 := bbase (se 5 (by rfl) ⟨156422, by rfl⟩ : syracuseStep 3337013 = 312845) (by norm_num)
theorem B1174333 : Blo 1040609 1174333 := bbase (se 3 (by rfl) ⟨220187, by rfl⟩ : syracuseStep 1174333 = 440375) (by norm_num)
theorem B1174369 : Blo 1040609 1174369 := bbase (se 2 (by rfl) ⟨440388, by rfl⟩ : syracuseStep 1174369 = 880777) (by norm_num)
theorem B1174405 : Blo 1040609 1174405 := bbase (se 4 (by rfl) ⟨110100, by rfl⟩ : syracuseStep 1174405 = 220201) (by norm_num)
theorem B3763093 : Blo 1040609 3763093 := bbase (se 6 (by rfl) ⟨88197, by rfl⟩ : syracuseStep 3763093 = 176395) (by norm_num)
theorem B1174441 : Blo 1040609 1174441 := bbase (se 2 (by rfl) ⟨440415, by rfl⟩ : syracuseStep 1174441 = 880831) (by norm_num)
theorem B1174477 : Blo 1040609 1174477 := bbase (se 3 (by rfl) ⟨220214, by rfl⟩ : syracuseStep 1174477 = 440429) (by norm_num)
theorem B1174513 : Blo 1040609 1174513 := bbase (se 2 (by rfl) ⟨440442, by rfl⟩ : syracuseStep 1174513 = 880885) (by norm_num)
theorem B1174549 : Blo 1040609 1174549 := bbase (se 6 (by rfl) ⟨27528, by rfl⟩ : syracuseStep 1174549 = 55057) (by norm_num)
theorem B4451365 : Blo 1040609 4451365 := bbase (se 4 (by rfl) ⟨417315, by rfl⟩ : syracuseStep 4451365 = 834631) (by norm_num)
theorem B1174585 : Blo 1040609 1174585 := bbase (se 2 (by rfl) ⟨440469, by rfl⟩ : syracuseStep 1174585 = 880939) (by norm_num)
theorem B1174621 : Blo 1040609 1174621 := bbase (se 3 (by rfl) ⟨220241, by rfl⟩ : syracuseStep 1174621 = 440483) (by norm_num)
theorem B8907893 : Blo 1040609 8907893 := bbase (se 5 (by rfl) ⟨417557, by rfl⟩ : syracuseStep 8907893 = 835115) (by norm_num)
theorem B1174657 : Blo 1040609 1174657 := bbase (se 2 (by rfl) ⟨440496, by rfl⟩ : syracuseStep 1174657 = 880993) (by norm_num)
theorem B1174693 : Blo 1040609 1174693 := bbase (se 4 (by rfl) ⟨110127, by rfl⟩ : syracuseStep 1174693 = 220255) (by norm_num)
theorem B1174729 : Blo 1040609 1174729 := bbase (se 2 (by rfl) ⟨440523, by rfl⟩ : syracuseStep 1174729 = 881047) (by norm_num)
theorem B2223325 : Blo 1040609 2223325 := bbase (se 3 (by rfl) ⟨416873, by rfl⟩ : syracuseStep 2223325 = 833747) (by norm_num)
theorem B1174765 : Blo 1040609 1174765 := bbase (se 3 (by rfl) ⟨220268, by rfl⟩ : syracuseStep 1174765 = 440537) (by norm_num)
theorem B1174801 : Blo 1040609 1174801 := bbase (se 2 (by rfl) ⟨440550, by rfl⟩ : syracuseStep 1174801 = 881101) (by norm_num)
theorem B1174837 : Blo 1040609 1174837 := bbase (se 5 (by rfl) ⟨55070, by rfl⟩ : syracuseStep 1174837 = 110141) (by norm_num)
theorem B5008709 : Blo 1040609 5008709 := bbase (se 4 (by rfl) ⟨469566, by rfl⟩ : syracuseStep 5008709 = 939133) (by norm_num)
theorem B2223445 : Blo 1040609 2223445 := bbase (se 11 (by rfl) ⟨1628, by rfl⟩ : syracuseStep 2223445 = 3257) (by norm_num)
theorem B1174873 : Blo 1040609 1174873 := bbase (se 2 (by rfl) ⟨440577, by rfl⟩ : syracuseStep 1174873 = 881155) (by norm_num)
theorem B1174909 : Blo 1040609 1174909 := bbase (se 3 (by rfl) ⟨220295, by rfl⟩ : syracuseStep 1174909 = 440591) (by norm_num)
theorem B1174945 : Blo 1040609 1174945 := bbase (se 2 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 1174945 = 881209) (by norm_num)
theorem B1174981 : Blo 1040609 1174981 := bbase (se 4 (by rfl) ⟨110154, by rfl⟩ : syracuseStep 1174981 = 220309) (by norm_num)
theorem B1175017 : Blo 1040609 1175017 := bbase (se 2 (by rfl) ⟨440631, by rfl⟩ : syracuseStep 1175017 = 881263) (by norm_num)
theorem B1175053 : Blo 1040609 1175053 := bbase (se 3 (by rfl) ⟨220322, by rfl⟩ : syracuseStep 1175053 = 440645) (by norm_num)
theorem B1175089 : Blo 1040609 1175089 := bbase (se 2 (by rfl) ⟨440658, by rfl⟩ : syracuseStep 1175089 = 881317) (by norm_num)
theorem B2223701 : Blo 1040609 2223701 := bbase (se 8 (by rfl) ⟨13029, by rfl⟩ : syracuseStep 2223701 = 26059) (by norm_num)
theorem B1175125 : Blo 1040609 1175125 := bbase (se 8 (by rfl) ⟨6885, by rfl⟩ : syracuseStep 1175125 = 13771) (by norm_num)
theorem B3174005 : Blo 1040609 3174005 := bbase (se 5 (by rfl) ⟨148781, by rfl⟩ : syracuseStep 3174005 = 297563) (by norm_num)
theorem B1175161 : Blo 1040609 1175161 := bbase (se 2 (by rfl) ⟨440685, by rfl⟩ : syracuseStep 1175161 = 881371) (by norm_num)
theorem B5271317 : Blo 1040609 5271317 := bbase (se 6 (by rfl) ⟨123546, by rfl⟩ : syracuseStep 5271317 = 247093) (by norm_num)
theorem B1339517 : Blo 1040609 1339517 := bbase (se 3 (by rfl) ⟨251159, by rfl⟩ : syracuseStep 1339517 = 502319) (by norm_num)
theorem B2814277 : Blo 1040609 2814277 := bbase (se 4 (by rfl) ⟨263838, by rfl⟩ : syracuseStep 2814277 = 527677) (by norm_num)
theorem B3764549 : Blo 1040609 3764549 := bbase (se 4 (by rfl) ⟨352926, by rfl⟩ : syracuseStep 3764549 = 705853) (by norm_num)
theorem B2224589 : Blo 1040609 2224589 := bbase (se 3 (by rfl) ⟨417110, by rfl⟩ : syracuseStep 2224589 = 834221) (by norm_num)
theorem B4452853 : Blo 1040609 4452853 := bbase (se 5 (by rfl) ⟨208727, by rfl⟩ : syracuseStep 4452853 = 417455) (by norm_num)
theorem B4452869 : Blo 1040609 4452869 := bbase (se 4 (by rfl) ⟨417456, by rfl⟩ : syracuseStep 4452869 = 834913) (by norm_num)
theorem B1339993 : Blo 1040609 1339993 := bbase (se 2 (by rfl) ⟨502497, by rfl⟩ : syracuseStep 1339993 = 1004995) (by norm_num)
theorem B3961493 : Blo 1040609 3961493 := bbase (se 6 (by rfl) ⟨92847, by rfl⟩ : syracuseStep 3961493 = 185695) (by norm_num)
theorem B2224829 : Blo 1040609 2224829 := bbase (se 3 (by rfl) ⟨417155, by rfl⟩ : syracuseStep 2224829 = 834311) (by norm_num)
theorem B5010133 : Blo 1040609 5010133 := bbase (se 7 (by rfl) ⟨58712, by rfl⟩ : syracuseStep 5010133 = 117425) (by norm_num)
theorem B2257645 : Blo 1040609 2257645 := bbase (se 3 (by rfl) ⟨423308, by rfl⟩ : syracuseStep 2257645 = 846617) (by norm_num)
theorem B4223765 : Blo 1040609 4223765 := bbase (se 6 (by rfl) ⟨98994, by rfl⟩ : syracuseStep 4223765 = 197989) (by norm_num)
theorem B1667981 : Blo 1040609 1667981 := bbase (se 3 (by rfl) ⟨312746, by rfl⟩ : syracuseStep 1667981 = 625493) (by norm_num)
theorem B3961781 : Blo 1040609 3961781 := bbase (se 5 (by rfl) ⟨185708, by rfl⟩ : syracuseStep 3961781 = 371417) (by norm_num)
theorem B1504261 : Blo 1040609 1504261 := bbase (se 4 (by rfl) ⟨141024, by rfl⟩ : syracuseStep 1504261 = 282049) (by norm_num)
theorem B3339269 : Blo 1040609 3339269 := bbase (se 4 (by rfl) ⟨313056, by rfl⟩ : syracuseStep 3339269 = 626113) (by norm_num)
theorem B1668109 : Blo 1040609 1668109 := bbase (se 3 (by rfl) ⟨312770, by rfl⟩ : syracuseStep 1668109 = 625541) (by norm_num)
theorem B5272613 : Blo 1040609 5272613 := bbase (se 4 (by rfl) ⟨494307, by rfl⟩ : syracuseStep 5272613 = 988615) (by norm_num)
theorem B2225333 : Blo 1040609 2225333 := bbase (se 5 (by rfl) ⟨104312, by rfl⟩ : syracuseStep 2225333 = 208625) (by norm_num)
theorem B2225341 : Blo 1040609 2225341 := bbase (se 3 (by rfl) ⟨417251, by rfl⟩ : syracuseStep 2225341 = 834503) (by norm_num)
theorem B7501045 : Blo 1040609 7501045 := bbase (se 5 (by rfl) ⟨351611, by rfl⟩ : syracuseStep 7501045 = 703223) (by norm_num)
theorem B1111321 : Blo 1040609 1111321 := bbase (se 2 (by rfl) ⟨416745, by rfl⟩ : syracuseStep 1111321 = 833491) (by norm_num)
theorem B1111573 : Blo 1040609 1111573 := bbase (se 6 (by rfl) ⟨26052, by rfl⟩ : syracuseStep 1111573 = 52105) (by norm_num)
theorem B1111577 : Blo 1040609 1111577 := bbase (se 2 (by rfl) ⟨416841, by rfl⟩ : syracuseStep 1111577 = 833683) (by norm_num)
theorem B2815669 : Blo 1040609 2815669 := bbase (se 5 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 2815669 = 263969) (by norm_num)
theorem B1406765 : Blo 1040609 1406765 := bbase (se 3 (by rfl) ⟨263768, by rfl⟩ : syracuseStep 1406765 = 527537) (by norm_num)
theorem B1668917 : Blo 1040609 1668917 := bbase (se 5 (by rfl) ⟨78230, by rfl⟩ : syracuseStep 1668917 = 156461) (by norm_num)
theorem B5928821 : Blo 1040609 5928821 := bbase (se 5 (by rfl) ⟨277913, by rfl⟩ : syracuseStep 5928821 = 555827) (by norm_num)
theorem B1112141 : Blo 1040609 1112141 := bbase (se 3 (by rfl) ⟨208526, by rfl⟩ : syracuseStep 1112141 = 417053) (by norm_num)
theorem B1669205 : Blo 1040609 1669205 := bbase (se 8 (by rfl) ⟨9780, by rfl⟩ : syracuseStep 1669205 = 19561) (by norm_num)
theorem B3962965 : Blo 1040609 3962965 := bbase (se 8 (by rfl) ⟨23220, by rfl⟩ : syracuseStep 3962965 = 46441) (by norm_num)
theorem B1407181 : Blo 1040609 1407181 := bbase (se 3 (by rfl) ⟨263846, by rfl⟩ : syracuseStep 1407181 = 527693) (by norm_num)
theorem B3012869 : Blo 1040609 3012869 := bbase (se 4 (by rfl) ⟨282456, by rfl⟩ : syracuseStep 3012869 = 564913) (by norm_num)
theorem B1112329 : Blo 1040609 1112329 := bbase (se 2 (by rfl) ⟨417123, by rfl⟩ : syracuseStep 1112329 = 834247) (by norm_num)
theorem B2226469 : Blo 1040609 2226469 := bbase (se 4 (by rfl) ⟨208731, by rfl⟩ : syracuseStep 2226469 = 417463) (by norm_num)
theorem B5273909 : Blo 1040609 5273909 := bbase (se 5 (by rfl) ⟨247214, by rfl⟩ : syracuseStep 5273909 = 494429) (by norm_num)
theorem B7928117 : Blo 1040609 7928117 := bbase (se 5 (by rfl) ⟨371630, by rfl⟩ : syracuseStep 7928117 = 743261) (by norm_num)
theorem B3963269 : Blo 1040609 3963269 := bbase (se 4 (by rfl) ⟨371556, by rfl⟩ : syracuseStep 3963269 = 743113) (by norm_num)
theorem B1669621 : Blo 1040609 1669621 := bbase (se 5 (by rfl) ⟨78263, by rfl⟩ : syracuseStep 1669621 = 156527) (by norm_num)
theorem B7502453 : Blo 1040609 7502453 := bbase (se 5 (by rfl) ⟨351677, by rfl⟩ : syracuseStep 7502453 = 703355) (by norm_num)
theorem B2226845 : Blo 1040609 2226845 := bbase (se 3 (by rfl) ⟨417533, by rfl⟩ : syracuseStep 2226845 = 835067) (by norm_num)
theorem B4455125 : Blo 1040609 4455125 := bbase (se 7 (by rfl) ⟨52208, by rfl⟩ : syracuseStep 4455125 = 104417) (by norm_num)
theorem B1932005 : Blo 1040609 1932005 := bbase (se 4 (by rfl) ⟨181125, by rfl⟩ : syracuseStep 1932005 = 362251) (by norm_num)
theorem B6683381 : Blo 1040609 6683381 := bbase (se 5 (by rfl) ⟨313283, by rfl⟩ : syracuseStep 6683381 = 626567) (by norm_num)
theorem B4225877 : Blo 1040609 4225877 := bbase (se 9 (by rfl) ⟨12380, by rfl⟩ : syracuseStep 4225877 = 24761) (by norm_num)
theorem B1932317 : Blo 1040609 1932317 := bbase (se 3 (by rfl) ⟨362309, by rfl⟩ : syracuseStep 1932317 = 724619) (by norm_num)
theorem B1113149 : Blo 1040609 1113149 := bbase (se 3 (by rfl) ⟨208715, by rfl⟩ : syracuseStep 1113149 = 417431) (by norm_num)
theorem B1408117 : Blo 1040609 1408117 := bbase (se 5 (by rfl) ⟨66005, by rfl⟩ : syracuseStep 1408117 = 132011) (by norm_num)
theorem B1670557 : Blo 1040609 1670557 := bbase (se 3 (by rfl) ⟨313229, by rfl⟩ : syracuseStep 1670557 = 626459) (by norm_num)
theorem B1113593 : Blo 1040609 1113593 := bbase (se 2 (by rfl) ⟨417597, by rfl⟩ : syracuseStep 1113593 = 835195) (by norm_num)
theorem B5275205 : Blo 1040609 5275205 := bbase (se 4 (by rfl) ⟨494550, by rfl⟩ : syracuseStep 5275205 = 989101) (by norm_num)
theorem B3047141 : Blo 1040609 3047141 := bbase (se 4 (by rfl) ⟨285669, by rfl⟩ : syracuseStep 3047141 = 571339) (by norm_num)
theorem B1113841 : Blo 1040609 1113841 := bbase (se 2 (by rfl) ⟨417690, by rfl⟩ : syracuseStep 1113841 = 835381) (by norm_num)
theorem B1671185 : Blo 1040609 1671185 := bstep (se 2 (by rfl) ⟨626694, by rfl⟩ : syracuseStep 1671185 = 1253389) B1253389
theorem B28508213 : Blo 1040609 28508213 := bstep (se 5 (by rfl) ⟨1336322, by rfl⟩ : syracuseStep 28508213 = 2672645) B2672645
theorem B5275853 : Blo 1040609 5275853 := bstep (se 3 (by rfl) ⟨989222, by rfl⟩ : syracuseStep 5275853 = 1978445) B1978445
theorem B20611381 : Blo 1040609 20611381 := bstep (se 5 (by rfl) ⟨966158, by rfl⟩ : syracuseStep 20611381 = 1932317) B1932317
theorem B3572045 : Blo 1040609 3572045 := bstep (se 3 (by rfl) ⟨669758, by rfl⟩ : syracuseStep 3572045 = 1339517) B1339517
theorem B1114499 : Blo 1040609 1114499 := bstep (se 1 (by rfl) ⟨835874, by rfl⟩ : syracuseStep 1114499 = 1671749) B1671749
theorem B5013937 : Blo 1040609 5013937 := bstep (se 2 (by rfl) ⟨1880226, by rfl⟩ : syracuseStep 5013937 = 3760453) B3760453
theorem B2228963 : Blo 1040609 2228963 := bstep (se 1 (by rfl) ⟨1671722, by rfl⟩ : syracuseStep 2228963 = 3343445) B3343445
theorem B3212131 : Blo 1040609 3212131 := bstep (se 1 (by rfl) ⟨2409098, by rfl⟩ : syracuseStep 3212131 = 4818197) B4818197
theorem B3343331 : Blo 1040609 3343331 := bstep (se 1 (by rfl) ⟨2507498, by rfl⟩ : syracuseStep 3343331 = 5014997) B5014997
theorem B6423565 : Blo 1040609 6423565 := bstep (se 3 (by rfl) ⟨1204418, by rfl⟩ : syracuseStep 6423565 = 2408837) B2408837
theorem B11895821 : Blo 1040609 11895821 := bstep (se 3 (by rfl) ⟨2230466, by rfl⟩ : syracuseStep 11895821 = 4460933) B4460933
theorem B4457585 : Blo 1040609 4457585 := bstep (se 2 (by rfl) ⟨1671594, by rfl⟩ : syracuseStep 4457585 = 3343189) B3343189
theorem B5932237 : Blo 1040609 5932237 := bstep (se 3 (by rfl) ⟨1112294, by rfl⟩ : syracuseStep 5932237 = 2224589) B2224589
theorem B2819693 : Blo 1040609 2819693 := bstep (se 3 (by rfl) ⟨528692, by rfl⟩ : syracuseStep 2819693 = 1057385) B1057385
theorem B1607347 : Blo 1040609 1607347 := bstep (se 1 (by rfl) ⟨1205510, by rfl⟩ : syracuseStep 1607347 = 2411021) B2411021
theorem B1672915 : Blo 1040609 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B2819821 : Blo 1040609 2819821 := bstep (se 3 (by rfl) ⟨528716, by rfl⟩ : syracuseStep 2819821 = 1057433) B1057433
theorem B5015459 : Blo 1040609 5015459 := bstep (se 1 (by rfl) ⟨3761594, by rfl⟩ : syracuseStep 5015459 = 7523189) B7523189
theorem B4458509 : Blo 1040609 4458509 := bstep (se 3 (by rfl) ⟨835970, by rfl⟩ : syracuseStep 4458509 = 1671941) B1671941
theorem B3344419 : Blo 1040609 3344419 := bstep (se 1 (by rfl) ⟨2508314, by rfl⟩ : syracuseStep 3344419 = 5016629) B5016629
theorem B3344561 : Blo 1040609 3344561 := bstep (se 2 (by rfl) ⟨1254210, by rfl⟩ : syracuseStep 3344561 = 2508421) B2508421
theorem B5278769 : Blo 1040609 5278769 := bstep (se 2 (by rfl) ⟨1979538, by rfl⟩ : syracuseStep 5278769 = 3959077) B3959077
theorem B7146629 : Blo 1040609 7146629 := bstep (se 4 (by rfl) ⟨669996, by rfl⟩ : syracuseStep 7146629 = 1339993) B1339993
theorem B5934221 : Blo 1040609 5934221 := bstep (se 3 (by rfl) ⟨1112666, by rfl⟩ : syracuseStep 5934221 = 2225333) B2225333
theorem B7146929 : Blo 1040609 7146929 := bstep (se 2 (by rfl) ⟨2680098, by rfl⟩ : syracuseStep 7146929 = 5360197) B5360197
theorem B22580707 : Blo 1040609 22580707 := bstep (se 1 (by rfl) ⟨16935530, by rfl⟩ : syracuseStep 22580707 = 33871061) B33871061
theorem B3345905 : Blo 1040609 3345905 := bstep (se 2 (by rfl) ⟨1254714, by rfl⟩ : syracuseStep 3345905 = 2509429) B2509429
theorem B357305909 : Blo 1040609 357305909 := bstep (se 5 (by rfl) ⟨16748714, by rfl⟩ : syracuseStep 357305909 = 33497429) B33497429
theorem B6688325 : Blo 1040609 6688325 := bstep (se 4 (by rfl) ⟨627030, by rfl⟩ : syracuseStep 6688325 = 1254061) B1254061
theorem B15044237 : Blo 1040609 15044237 := bstep (se 3 (by rfl) ⟨2820794, by rfl⟩ : syracuseStep 15044237 = 5641589) B5641589
theorem B5017457 : Blo 1040609 5017457 := bstep (se 2 (by rfl) ⟨1881546, by rfl⟩ : syracuseStep 5017457 = 3763093) B3763093
theorem B11898737 : Blo 1040609 11898737 := bstep (se 2 (by rfl) ⟨4462026, by rfl⟩ : syracuseStep 11898737 = 8924053) B8924053
theorem B15044579 : Blo 1040609 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B5640205 : Blo 1040609 5640205 := bstep (se 3 (by rfl) ⟨1057538, by rfl⟩ : syracuseStep 5640205 = 2115077) B2115077
theorem B5935153 : Blo 1040609 5935153 := bstep (se 2 (by rfl) ⟨2225682, by rfl⟩ : syracuseStep 5935153 = 4451365) B4451365
theorem B2822417 : Blo 1040609 2822417 := bstep (se 2 (by rfl) ⟨1058406, by rfl⟩ : syracuseStep 2822417 = 2116813) B2116813
theorem B5280227 : Blo 1040609 5280227 := bstep (se 1 (by rfl) ⟨3960170, by rfl⟩ : syracuseStep 5280227 = 7920341) B7920341
theorem B5018381 : Blo 1040609 5018381 := bstep (se 3 (by rfl) ⟨940946, by rfl⟩ : syracuseStep 5018381 = 1881893) B1881893
theorem B4461617 : Blo 1040609 4461617 := bstep (se 2 (by rfl) ⟨1673106, by rfl⟩ : syracuseStep 4461617 = 3346213) B3346213
theorem B5281037 : Blo 1040609 5281037 := bstep (se 3 (by rfl) ⟨990194, by rfl⟩ : syracuseStep 5281037 = 1980389) B1980389
theorem B5936611 : Blo 1040609 5936611 := bstep (se 1 (by rfl) ⟨4452458, by rfl⟩ : syracuseStep 5936611 = 8904917) B8904917
theorem B6690275 : Blo 1040609 6690275 := bstep (se 1 (by rfl) ⟨5017706, by rfl⟩ : syracuseStep 6690275 = 10035413) B10035413
theorem B1250947 : Blo 1040609 1250947 := bstep (se 1 (by rfl) ⟨938210, by rfl⟩ : syracuseStep 1250947 = 1876421) B1876421
theorem B4232845 : Blo 1040609 4232845 := bstep (se 3 (by rfl) ⟨793658, by rfl⟩ : syracuseStep 4232845 = 1587317) B1587317
theorem B5937137 : Blo 1040609 5937137 := bstep (se 2 (by rfl) ⟨2226426, by rfl⟩ : syracuseStep 5937137 = 4452853) B4452853
theorem B8034317 : Blo 1040609 8034317 := bstep (se 3 (by rfl) ⟨1506434, by rfl⟩ : syracuseStep 8034317 = 3012869) B3012869
theorem B7903331 : Blo 1040609 7903331 := bstep (se 1 (by rfl) ⟨5927498, by rfl⟩ : syracuseStep 7903331 = 11854997) B11854997
theorem B3512429 : Blo 1040609 3512429 := bstep (se 3 (by rfl) ⟨658580, by rfl⟩ : syracuseStep 3512429 = 1317161) B1317161
theorem B1054867 : Blo 1040609 1054867 := bstep (se 1 (by rfl) ⟨791150, by rfl⟩ : syracuseStep 1054867 = 1582301) B1582301
theorem B3512483 : Blo 1040609 3512483 := bstep (se 1 (by rfl) ⟨2634362, by rfl⟩ : syracuseStep 3512483 = 5268725) B5268725
theorem B1906993 : Blo 1040609 1906993 := bstep (se 2 (by rfl) ⟨715122, by rfl⟩ : syracuseStep 1906993 = 1430245) B1430245
theorem B3512753 : Blo 1040609 3512753 := bstep (se 2 (by rfl) ⟨1317282, by rfl⟩ : syracuseStep 3512753 = 2634565) B2634565
theorem B6101489 : Blo 1040609 6101489 := bstep (se 2 (by rfl) ⟨2288058, by rfl⟩ : syracuseStep 6101489 = 4576117) B4576117
theorem B1317379 : Blo 1040609 1317379 := bstep (se 1 (by rfl) ⟨988034, by rfl⟩ : syracuseStep 1317379 = 1976069) B1976069
theorem B1317475 : Blo 1040609 1317475 := bstep (se 1 (by rfl) ⟨988106, by rfl⟩ : syracuseStep 1317475 = 1976213) B1976213
theorem B2824849 : Blo 1040609 2824849 := bstep (se 2 (by rfl) ⟨1059318, by rfl⟩ : syracuseStep 2824849 = 2118637) B2118637
theorem B2005681 : Blo 1040609 2005681 := bstep (se 2 (by rfl) ⟨752130, by rfl⟩ : syracuseStep 2005681 = 1504261) B1504261
theorem B3513293 : Blo 1040609 3513293 := bstep (se 3 (by rfl) ⟨658742, by rfl⟩ : syracuseStep 3513293 = 1317485) B1317485
theorem B10001393 : Blo 1040609 10001393 := bstep (se 2 (by rfl) ⟨3750522, by rfl⟩ : syracuseStep 10001393 = 7501045) B7501045
theorem B3513347 : Blo 1040609 3513347 := bstep (se 1 (by rfl) ⟨2635010, by rfl⟩ : syracuseStep 3513347 = 5270021) B5270021
theorem B1481761 : Blo 1040609 1481761 := bstep (se 2 (by rfl) ⟨555660, by rfl⟩ : syracuseStep 1481761 = 1111321) B1111321
theorem B1317971 : Blo 1040609 1317971 := bstep (se 1 (by rfl) ⟨988478, by rfl⟩ : syracuseStep 1317971 = 1976957) B1976957
theorem B3513617 : Blo 1040609 3513617 := bstep (se 2 (by rfl) ⟨1317606, by rfl⟩ : syracuseStep 3513617 = 2635213) B2635213
theorem B5938595 : Blo 1040609 5938595 := bstep (se 1 (by rfl) ⟨4453946, by rfl⟩ : syracuseStep 5938595 = 8907893) B8907893
theorem B1482467 : Blo 1040609 1482467 := bstep (se 1 (by rfl) ⟨1111850, by rfl⟩ : syracuseStep 1482467 = 2223701) B2223701
theorem B1318675 : Blo 1040609 1318675 := bstep (se 1 (by rfl) ⟨989006, by rfl⟩ : syracuseStep 1318675 = 1978013) B1978013
theorem B3514157 : Blo 1040609 3514157 := bstep (se 3 (by rfl) ⟨658904, by rfl⟩ : syracuseStep 3514157 = 1317809) B1317809
theorem B3514211 : Blo 1040609 3514211 := bstep (se 1 (by rfl) ⟨2635658, by rfl⟩ : syracuseStep 3514211 = 5271317) B5271317
theorem B1318771 : Blo 1040609 1318771 := bstep (se 1 (by rfl) ⟨989078, by rfl⟩ : syracuseStep 1318771 = 1978157) B1978157
theorem B6692813 : Blo 1040609 6692813 := bstep (se 3 (by rfl) ⟨1254902, by rfl⟩ : syracuseStep 6692813 = 2509805) B2509805
theorem B3514481 : Blo 1040609 3514481 := bstep (se 2 (by rfl) ⟨1317930, by rfl⟩ : syracuseStep 3514481 = 2635861) B2635861
theorem B5283953 : Blo 1040609 5283953 := bstep (se 2 (by rfl) ⟨1981482, by rfl⟩ : syracuseStep 5283953 = 3962965) B3962965
theorem B1056979 : Blo 1040609 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B1876241 : Blo 1040609 1876241 := bstep (se 2 (by rfl) ⟨703590, by rfl⟩ : syracuseStep 1876241 = 1407181) B1407181
theorem B1483105 : Blo 1040609 1483105 := bstep (se 2 (by rfl) ⟨556164, by rfl⟩ : syracuseStep 1483105 = 1112329) B1112329
theorem B1319267 : Blo 1040609 1319267 := bstep (se 1 (by rfl) ⟨989450, by rfl⟩ : syracuseStep 1319267 = 1978901) B1978901
theorem B16916849 : Blo 1040609 16916849 := bstep (se 2 (by rfl) ⟨6343818, by rfl⟩ : syracuseStep 16916849 = 12687637) B12687637
theorem B13541813 : Blo 1040609 13541813 := bstep (se 5 (by rfl) ⟨634772, by rfl⟩ : syracuseStep 13541813 = 1269545) B1269545
theorem B1483219 : Blo 1040609 1483219 := bstep (se 1 (by rfl) ⟨1112414, by rfl⟩ : syracuseStep 1483219 = 2224829) B2224829
theorem B3515021 : Blo 1040609 3515021 := bstep (se 3 (by rfl) ⟨659066, by rfl⟩ : syracuseStep 3515021 = 1318133) B1318133
theorem B3515075 : Blo 1040609 3515075 := bstep (se 1 (by rfl) ⟨2636306, by rfl⟩ : syracuseStep 3515075 = 5272613) B5272613
theorem B1188563 : Blo 1040609 1188563 := bstep (se 1 (by rfl) ⟨891422, by rfl⟩ : syracuseStep 1188563 = 1782845) B1782845
theorem B21439285 : Blo 1040609 21439285 := bstep (se 5 (by rfl) ⟨1004966, by rfl⟩ : syracuseStep 21439285 = 2009933) B2009933
theorem B3515345 : Blo 1040609 3515345 := bstep (se 2 (by rfl) ⟨1318254, by rfl⟩ : syracuseStep 3515345 = 2636509) B2636509
theorem B1319971 : Blo 1040609 1319971 := bstep (se 1 (by rfl) ⟨989978, by rfl⟩ : syracuseStep 1319971 = 1979957) B1979957
theorem B1320067 : Blo 1040609 1320067 := bstep (se 1 (by rfl) ⟨990050, by rfl⟩ : syracuseStep 1320067 = 1980101) B1980101
theorem B5940485 : Blo 1040609 5940485 := bstep (se 4 (by rfl) ⟨556920, by rfl⟩ : syracuseStep 5940485 = 1113841) B1113841
theorem B3515885 : Blo 1040609 3515885 := bstep (se 3 (by rfl) ⟨659228, by rfl⟩ : syracuseStep 3515885 = 1318457) B1318457
theorem B1877489 : Blo 1040609 1877489 := bstep (se 2 (by rfl) ⟨704058, by rfl⟩ : syracuseStep 1877489 = 1408117) B1408117
theorem B3515939 : Blo 1040609 3515939 := bstep (se 1 (by rfl) ⟨2636954, by rfl⟩ : syracuseStep 3515939 = 5273909) B5273909
theorem B5285411 : Blo 1040609 5285411 := bstep (se 1 (by rfl) ⟨3964058, by rfl⟩ : syracuseStep 5285411 = 7928117) B7928117
theorem B1320563 : Blo 1040609 1320563 := bstep (se 1 (by rfl) ⟨990422, by rfl⟩ : syracuseStep 1320563 = 1980845) B1980845
theorem B1975985 : Blo 1040609 1975985 := bstep (se 2 (by rfl) ⟨740994, by rfl⟩ : syracuseStep 1975985 = 1481989) B1481989
theorem B1484563 : Blo 1040609 1484563 := bstep (se 1 (by rfl) ⟨1113422, by rfl⟩ : syracuseStep 1484563 = 2226845) B2226845
theorem B3516209 : Blo 1040609 3516209 := bstep (se 2 (by rfl) ⟨1318578, by rfl⟩ : syracuseStep 3516209 = 2637157) B2637157
theorem B1288003 : Blo 1040609 1288003 := bstep (se 1 (by rfl) ⟨966002, by rfl⟩ : syracuseStep 1288003 = 1932005) B1932005
theorem B1321267 : Blo 1040609 1321267 := bstep (se 1 (by rfl) ⟨990950, by rfl⟩ : syracuseStep 1321267 = 1981901) B1981901
theorem B13347125 : Blo 1040609 13347125 := bstep (se 5 (by rfl) ⟨625646, by rfl⟩ : syracuseStep 13347125 = 1251293) B1251293
theorem B1583425 : Blo 1040609 1583425 := bstep (se 2 (by rfl) ⟨593784, by rfl⟩ : syracuseStep 1583425 = 1187569) B1187569
theorem B3516749 : Blo 1040609 3516749 := bstep (se 3 (by rfl) ⟨659390, by rfl⟩ : syracuseStep 3516749 = 1318781) B1318781
theorem B5286221 : Blo 1040609 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B3516803 : Blo 1040609 3516803 := bstep (se 1 (by rfl) ⟨2637602, by rfl⟩ : syracuseStep 3516803 = 5275205) B5275205
theorem B1321363 : Blo 1040609 1321363 := bstep (se 1 (by rfl) ⟨991022, by rfl⟩ : syracuseStep 1321363 = 1982045) B1982045
theorem B1976881 : Blo 1040609 1976881 := bstep (se 2 (by rfl) ⟨741330, by rfl⟩ : syracuseStep 1976881 = 1482661) B1482661
theorem B3517073 : Blo 1040609 3517073 := bstep (se 2 (by rfl) ⟨1318902, by rfl⟩ : syracuseStep 3517073 = 2637805) B2637805
theorem B1977041 : Blo 1040609 1977041 := bstep (se 2 (by rfl) ⟨741390, by rfl⟩ : syracuseStep 1977041 = 1482781) B1482781
theorem B1583857 : Blo 1040609 1583857 := bstep (se 2 (by rfl) ⟨593946, by rfl⟩ : syracuseStep 1583857 = 1187893) B1187893
theorem B1485697 : Blo 1040609 1485697 := bstep (se 2 (by rfl) ⟨557136, by rfl⟩ : syracuseStep 1485697 = 1114273) B1114273
theorem B1321859 : Blo 1040609 1321859 := bstep (se 1 (by rfl) ⟨991394, by rfl⟩ : syracuseStep 1321859 = 1982789) B1982789
theorem B10005389 : Blo 1040609 10005389 := bstep (se 3 (by rfl) ⟨1876010, by rfl⟩ : syracuseStep 10005389 = 3752021) B3752021
theorem B1485793 : Blo 1040609 1485793 := bstep (se 2 (by rfl) ⟨557172, by rfl⟩ : syracuseStep 1485793 = 1114345) B1114345
theorem B1190963 : Blo 1040609 1190963 := bstep (se 1 (by rfl) ⟨893222, by rfl⟩ : syracuseStep 1190963 = 1786445) B1786445
theorem B1977443 : Blo 1040609 1977443 := bstep (se 1 (by rfl) ⟨1483082, by rfl⟩ : syracuseStep 1977443 = 2966165) B2966165
theorem B3517613 : Blo 1040609 3517613 := bstep (se 3 (by rfl) ⟨659552, by rfl⟩ : syracuseStep 3517613 = 1319105) B1319105
theorem B1780915 : Blo 1040609 1780915 := bstep (se 1 (by rfl) ⟨1335686, by rfl⟩ : syracuseStep 1780915 = 2671373) B2671373
theorem B2534627 : Blo 1040609 2534627 := bstep (se 1 (by rfl) ⟨1900970, by rfl⟩ : syracuseStep 2534627 = 3801941) B3801941
theorem B10005731 : Blo 1040609 10005731 := bstep (se 1 (by rfl) ⟨7504298, by rfl⟩ : syracuseStep 10005731 = 15008597) B15008597
theorem B3517667 : Blo 1040609 3517667 := bstep (se 1 (by rfl) ⟨2638250, by rfl⟩ : syracuseStep 3517667 = 5276501) B5276501
theorem B1781041 : Blo 1040609 1781041 := bstep (se 2 (by rfl) ⟨667890, by rfl⟩ : syracuseStep 1781041 = 1335781) B1335781
theorem B20065589 : Blo 1040609 20065589 := bstep (se 5 (by rfl) ⟨940574, by rfl⟩ : syracuseStep 20065589 = 1881149) B1881149
theorem B7908677 : Blo 1040609 7908677 := bstep (se 4 (by rfl) ⟨741438, by rfl⟩ : syracuseStep 7908677 = 1482877) B1482877
theorem B11283781 : Blo 1040609 11283781 := bstep (se 4 (by rfl) ⟨1057854, by rfl⟩ : syracuseStep 11283781 = 2115709) B2115709
theorem B1584593 : Blo 1040609 1584593 := bstep (se 2 (by rfl) ⟨594222, by rfl⟩ : syracuseStep 1584593 = 1188445) B1188445
theorem B1486289 : Blo 1040609 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B3517937 : Blo 1040609 3517937 := bstep (se 2 (by rfl) ⟨1319226, by rfl⟩ : syracuseStep 3517937 = 2638453) B2638453
theorem B1781299 : Blo 1040609 1781299 := bstep (se 1 (by rfl) ⟨1335974, by rfl⟩ : syracuseStep 1781299 = 2671949) B2671949
theorem B4763249 : Blo 1040609 4763249 := bstep (se 2 (by rfl) ⟨1786218, by rfl⟩ : syracuseStep 4763249 = 3572437) B3572437
theorem B1879939 : Blo 1040609 1879939 := bstep (se 1 (by rfl) ⟨1409954, by rfl⟩ : syracuseStep 1879939 = 2819909) B2819909
theorem B1978339 : Blo 1040609 1978339 := bstep (se 1 (by rfl) ⟨1483754, by rfl⟩ : syracuseStep 1978339 = 2967509) B2967509
theorem B3518477 : Blo 1040609 3518477 := bstep (se 3 (by rfl) ⟨659714, by rfl⟩ : syracuseStep 3518477 = 1319429) B1319429
theorem B3518531 : Blo 1040609 3518531 := bstep (se 1 (by rfl) ⟨2638898, by rfl⟩ : syracuseStep 3518531 = 5277797) B5277797
theorem B10039409 : Blo 1040609 10039409 := bstep (se 2 (by rfl) ⟨3764778, by rfl⟩ : syracuseStep 10039409 = 7529557) B7529557
theorem B1978499 : Blo 1040609 1978499 := bstep (se 1 (by rfl) ⟨1483874, by rfl⟩ : syracuseStep 1978499 = 2967749) B2967749
theorem B1487155 : Blo 1040609 1487155 := bstep (se 1 (by rfl) ⟨1115366, by rfl⟩ : syracuseStep 1487155 = 2230733) B2230733
theorem B3518801 : Blo 1040609 3518801 := bstep (se 2 (by rfl) ⟨1319550, by rfl⟩ : syracuseStep 3518801 = 2639101) B2639101
theorem B1487251 : Blo 1040609 1487251 := bstep (se 1 (by rfl) ⟨1115438, by rfl⟩ : syracuseStep 1487251 = 2230877) B2230877
theorem B2634353 : Blo 1040609 2634353 := bstep (se 2 (by rfl) ⟨987882, by rfl⟩ : syracuseStep 2634353 = 1975765) B1975765
theorem B2634403 : Blo 1040609 2634403 := bstep (se 1 (by rfl) ⟨1975802, by rfl⟩ : syracuseStep 2634403 = 3951605) B3951605
theorem B1880803 : Blo 1040609 1880803 := bstep (se 1 (by rfl) ⟨1410602, by rfl⟩ : syracuseStep 1880803 = 2821205) B2821205
theorem B2634545 : Blo 1040609 2634545 := bstep (se 2 (by rfl) ⟨987954, by rfl⟩ : syracuseStep 2634545 = 1975909) B1975909
theorem B1586017 : Blo 1040609 1586017 := bstep (se 2 (by rfl) ⟨594756, by rfl⟩ : syracuseStep 1586017 = 1189513) B1189513
theorem B6337379 : Blo 1040609 6337379 := bstep (se 1 (by rfl) ⟨4753034, by rfl⟩ : syracuseStep 6337379 = 9506069) B9506069
theorem B3519341 : Blo 1040609 3519341 := bstep (se 3 (by rfl) ⟨659876, by rfl⟩ : syracuseStep 3519341 = 1319753) B1319753
theorem B1782641 : Blo 1040609 1782641 := bstep (se 2 (by rfl) ⟨668490, by rfl⟩ : syracuseStep 1782641 = 1336981) B1336981
theorem B3519395 : Blo 1040609 3519395 := bstep (se 1 (by rfl) ⟨2639546, by rfl⟩ : syracuseStep 3519395 = 5279093) B5279093
theorem B1979569 : Blo 1040609 1979569 := bstep (se 2 (by rfl) ⟨742338, by rfl⟩ : syracuseStep 1979569 = 1484677) B1484677
theorem B3519665 : Blo 1040609 3519665 := bstep (se 2 (by rfl) ⟨1319874, by rfl⟩ : syracuseStep 3519665 = 2639749) B2639749
theorem B8893709 : Blo 1040609 8893709 := bstep (se 3 (by rfl) ⟨1667570, by rfl⟩ : syracuseStep 8893709 = 3335141) B3335141
theorem B1586515 : Blo 1040609 1586515 := bstep (se 1 (by rfl) ⟨1189886, by rfl⟩ : syracuseStep 1586515 = 2379773) B2379773
theorem B1881553 : Blo 1040609 1881553 := bstep (se 2 (by rfl) ⟨705582, by rfl⟩ : syracuseStep 1881553 = 1411165) B1411165
theorem B1783379 : Blo 1040609 1783379 := bstep (se 1 (by rfl) ⟨1337534, by rfl⟩ : syracuseStep 1783379 = 2675069) B2675069
theorem B3520205 : Blo 1040609 3520205 := bstep (se 3 (by rfl) ⟨660038, by rfl⟩ : syracuseStep 3520205 = 1320077) B1320077
theorem B3520259 : Blo 1040609 3520259 := bstep (se 1 (by rfl) ⟨2640194, by rfl⟩ : syracuseStep 3520259 = 5280389) B5280389
theorem B2635537 : Blo 1040609 2635537 := bstep (se 2 (by rfl) ⟨988326, by rfl⟩ : syracuseStep 2635537 = 1976653) B1976653
theorem B3389219 : Blo 1040609 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B1783667 : Blo 1040609 1783667 := bstep (se 1 (by rfl) ⟨1337750, by rfl⟩ : syracuseStep 1783667 = 2675501) B2675501
theorem B12662725 : Blo 1040609 12662725 := bstep (se 4 (by rfl) ⟨1187130, by rfl⟩ : syracuseStep 12662725 = 2374261) B2374261
theorem B1783811 : Blo 1040609 1783811 := bstep (se 1 (by rfl) ⟨1337858, by rfl⟩ : syracuseStep 1783811 = 2675717) B2675717
theorem B3520529 : Blo 1040609 3520529 := bstep (se 2 (by rfl) ⟨1320198, by rfl⟩ : syracuseStep 3520529 = 2640397) B2640397
theorem B2635811 : Blo 1040609 2635811 := bstep (se 1 (by rfl) ⟨1976858, by rfl⟩ : syracuseStep 2635811 = 3953717) B3953717
theorem B1980625 : Blo 1040609 1980625 := bstep (se 2 (by rfl) ⟨742734, by rfl⟩ : syracuseStep 1980625 = 1485469) B1485469
theorem B2636003 : Blo 1040609 2636003 := bstep (se 1 (by rfl) ⟨1977002, by rfl⟩ : syracuseStep 2636003 = 3954005) B3954005
theorem B1718561 : Blo 1040609 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1587683 : Blo 1040609 1587683 := bstep (se 1 (by rfl) ⟨1190762, by rfl⟩ : syracuseStep 1587683 = 2381525) B2381525
theorem B3521069 : Blo 1040609 3521069 := bstep (se 3 (by rfl) ⟨660200, by rfl⟩ : syracuseStep 3521069 = 1320401) B1320401
theorem B2341457 : Blo 1040609 2341457 := bstep (se 2 (by rfl) ⟨878046, by rfl⟩ : syracuseStep 2341457 = 1756093) B1756093
theorem B2341475 : Blo 1040609 2341475 := bstep (se 1 (by rfl) ⟨1756106, by rfl⟩ : syracuseStep 2341475 = 3512213) B3512213
theorem B3521123 : Blo 1040609 3521123 := bstep (se 1 (by rfl) ⟨2640842, by rfl⟩ : syracuseStep 3521123 = 5281685) B5281685
theorem B1981027 : Blo 1040609 1981027 := bstep (se 1 (by rfl) ⟨1485770, by rfl⟩ : syracuseStep 1981027 = 2971541) B2971541
theorem B1981073 : Blo 1040609 1981073 := bstep (se 2 (by rfl) ⟨742902, by rfl⟩ : syracuseStep 1981073 = 1485805) B1485805
theorem B1784467 : Blo 1040609 1784467 := bstep (se 1 (by rfl) ⟨1338350, by rfl⟩ : syracuseStep 1784467 = 2676701) B2676701
theorem B2964205 : Blo 1040609 2964205 := bstep (se 3 (by rfl) ⟨555788, by rfl⟩ : syracuseStep 2964205 = 1111577) B1111577
theorem B2341745 : Blo 1040609 2341745 := bstep (se 2 (by rfl) ⟨878154, by rfl⟩ : syracuseStep 2341745 = 1756309) B1756309
theorem B3521393 : Blo 1040609 3521393 := bstep (se 2 (by rfl) ⟨1320522, by rfl⟩ : syracuseStep 3521393 = 2641045) B2641045
theorem B2341763 : Blo 1040609 2341763 := bstep (se 1 (by rfl) ⟨1756322, by rfl⟩ : syracuseStep 2341763 = 3512645) B3512645
theorem B1981361 : Blo 1040609 1981361 := bstep (se 2 (by rfl) ⟨743010, by rfl⟩ : syracuseStep 1981361 = 1486021) B1486021
theorem B5946317 : Blo 1040609 5946317 := bstep (se 3 (by rfl) ⟨1114934, by rfl⟩ : syracuseStep 5946317 = 2229869) B2229869
theorem B2964433 : Blo 1040609 2964433 := bstep (se 2 (by rfl) ⟨1111662, by rfl⟩ : syracuseStep 2964433 = 2223325) B2223325
theorem B2964593 : Blo 1040609 2964593 := bstep (se 2 (by rfl) ⟨1111722, by rfl⟩ : syracuseStep 2964593 = 2223445) B2223445
theorem B12696689 : Blo 1040609 12696689 := bstep (se 2 (by rfl) ⟨4761258, by rfl⟩ : syracuseStep 12696689 = 9522517) B9522517
theorem B27475085 : Blo 1040609 27475085 := bstep (se 3 (by rfl) ⟨5151578, by rfl⟩ : syracuseStep 27475085 = 10303157) B10303157
theorem B2342033 : Blo 1040609 2342033 := bstep (se 2 (by rfl) ⟨878262, by rfl⟩ : syracuseStep 2342033 = 1756525) B1756525
theorem B2636945 : Blo 1040609 2636945 := bstep (se 2 (by rfl) ⟨988854, by rfl⟩ : syracuseStep 2636945 = 1977709) B1977709
theorem B2342051 : Blo 1040609 2342051 := bstep (se 1 (by rfl) ⟨1756538, by rfl⟩ : syracuseStep 2342051 = 3513077) B3513077
theorem B2636995 : Blo 1040609 2636995 := bstep (se 1 (by rfl) ⟨1977746, by rfl⟩ : syracuseStep 2636995 = 3955493) B3955493
theorem B2964707 : Blo 1040609 2964707 := bstep (se 1 (by rfl) ⟨2223530, by rfl⟩ : syracuseStep 2964707 = 4447061) B4447061
theorem B14269765 : Blo 1040609 14269765 := bstep (se 4 (by rfl) ⟨1337790, by rfl⟩ : syracuseStep 14269765 = 2675581) B2675581
theorem B2637137 : Blo 1040609 2637137 := bstep (se 2 (by rfl) ⟨988926, by rfl⟩ : syracuseStep 2637137 = 1977853) B1977853
theorem B2506115 : Blo 1040609 2506115 := bstep (se 1 (by rfl) ⟨1879586, by rfl⟩ : syracuseStep 2506115 = 3759173) B3759173
theorem B32128397 : Blo 1040609 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B3521933 : Blo 1040609 3521933 := bstep (se 3 (by rfl) ⟨660362, by rfl⟩ : syracuseStep 3521933 = 1320725) B1320725
theorem B2342321 : Blo 1040609 2342321 := bstep (se 2 (by rfl) ⟨878370, by rfl⟩ : syracuseStep 2342321 = 1756741) B1756741
theorem B2342339 : Blo 1040609 2342339 := bstep (se 1 (by rfl) ⟨1756754, by rfl⟩ : syracuseStep 2342339 = 3513509) B3513509
theorem B3521987 : Blo 1040609 3521987 := bstep (se 1 (by rfl) ⟨2641490, by rfl⟩ : syracuseStep 3521987 = 5282981) B5282981
theorem B3751373 : Blo 1040609 3751373 := bstep (se 3 (by rfl) ⟨703382, by rfl⟩ : syracuseStep 3751373 = 1406765) B1406765
theorem B1982083 : Blo 1040609 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B2342609 : Blo 1040609 2342609 := bstep (se 2 (by rfl) ⟨878478, by rfl⟩ : syracuseStep 2342609 = 1756957) B1756957
theorem B3522257 : Blo 1040609 3522257 := bstep (se 2 (by rfl) ⟨1320846, by rfl⟩ : syracuseStep 3522257 = 2641693) B2641693
theorem B2342627 : Blo 1040609 2342627 := bstep (se 1 (by rfl) ⟨1756970, by rfl⟩ : syracuseStep 2342627 = 3513941) B3513941
theorem B7519985 : Blo 1040609 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B6668081 : Blo 1040609 6668081 := bstep (se 2 (by rfl) ⟨2500530, by rfl⟩ : syracuseStep 6668081 = 5001061) B5001061
theorem B2408305 : Blo 1040609 2408305 := bstep (se 2 (by rfl) ⟨903114, by rfl⟩ : syracuseStep 2408305 = 1806229) B1806229
theorem B11878325 : Blo 1040609 11878325 := bstep (se 5 (by rfl) ⟨556796, by rfl⟩ : syracuseStep 11878325 = 1113593) B1113593
theorem B2342897 : Blo 1040609 2342897 := bstep (se 2 (by rfl) ⟨878586, by rfl⟩ : syracuseStep 2342897 = 1757173) B1757173
theorem B2342915 : Blo 1040609 2342915 := bstep (se 1 (by rfl) ⟨1757186, by rfl⟩ : syracuseStep 2342915 = 3514373) B3514373
theorem B1982531 : Blo 1040609 1982531 := bstep (se 1 (by rfl) ⟨1486898, by rfl⟩ : syracuseStep 1982531 = 2973797) B2973797
theorem B2408579 : Blo 1040609 2408579 := bstep (se 1 (by rfl) ⟨1806434, by rfl⟩ : syracuseStep 2408579 = 3612869) B3612869
theorem B2965709 : Blo 1040609 2965709 := bstep (se 3 (by rfl) ⟨556070, by rfl⟩ : syracuseStep 2965709 = 1112141) B1112141
theorem B3522797 : Blo 1040609 3522797 := bstep (se 3 (by rfl) ⟨660524, by rfl⟩ : syracuseStep 3522797 = 1321049) B1321049
theorem B2343185 : Blo 1040609 2343185 := bstep (se 2 (by rfl) ⟨878694, by rfl⟩ : syracuseStep 2343185 = 1757389) B1757389
theorem B2343203 : Blo 1040609 2343203 := bstep (se 1 (by rfl) ⟨1757402, by rfl⟩ : syracuseStep 2343203 = 3514805) B3514805
theorem B3522851 : Blo 1040609 3522851 := bstep (se 1 (by rfl) ⟨2642138, by rfl⟩ : syracuseStep 3522851 = 5284277) B5284277
theorem B2638129 : Blo 1040609 2638129 := bstep (se 2 (by rfl) ⟨989298, by rfl⟩ : syracuseStep 2638129 = 1978597) B1978597
theorem B1982819 : Blo 1040609 1982819 := bstep (se 1 (by rfl) ⟨1487114, by rfl⟩ : syracuseStep 1982819 = 2974229) B2974229
theorem B2965891 : Blo 1040609 2965891 := bstep (se 1 (by rfl) ⟨2224418, by rfl⟩ : syracuseStep 2965891 = 4448837) B4448837
theorem B3752369 : Blo 1040609 3752369 := bstep (se 2 (by rfl) ⟨1407138, by rfl⟩ : syracuseStep 3752369 = 2814277) B2814277
theorem B1524227 : Blo 1040609 1524227 := bstep (se 1 (by rfl) ⟨1143170, by rfl⟩ : syracuseStep 1524227 = 2286341) B2286341
theorem B2966051 : Blo 1040609 2966051 := bstep (se 1 (by rfl) ⟨2224538, by rfl⟩ : syracuseStep 2966051 = 4449077) B4449077
theorem B2343473 : Blo 1040609 2343473 := bstep (se 2 (by rfl) ⟨878802, by rfl⟩ : syracuseStep 2343473 = 1757605) B1757605
theorem B2540081 : Blo 1040609 2540081 := bstep (se 2 (by rfl) ⟨952530, by rfl⟩ : syracuseStep 2540081 = 1905061) B1905061
theorem B3523121 : Blo 1040609 3523121 := bstep (se 2 (by rfl) ⟨1321170, by rfl⟩ : syracuseStep 3523121 = 2642341) B2642341
theorem B2343491 : Blo 1040609 2343491 := bstep (se 1 (by rfl) ⟨1757618, by rfl⟩ : syracuseStep 2343491 = 3515237) B3515237
theorem B2638403 : Blo 1040609 2638403 := bstep (se 1 (by rfl) ⟨1978802, by rfl⟩ : syracuseStep 2638403 = 3957605) B3957605
theorem B2507345 : Blo 1040609 2507345 := bstep (se 2 (by rfl) ⟨940254, by rfl⟩ : syracuseStep 2507345 = 1880509) B1880509
theorem B2376305 : Blo 1040609 2376305 := bstep (se 2 (by rfl) ⟨891114, by rfl⟩ : syracuseStep 2376305 = 1782229) B1782229
theorem B2638595 : Blo 1040609 2638595 := bstep (se 1 (by rfl) ⟨1978946, by rfl⟩ : syracuseStep 2638595 = 3957893) B3957893
theorem B2343761 : Blo 1040609 2343761 := bstep (se 2 (by rfl) ⟨878910, by rfl⟩ : syracuseStep 2343761 = 1757821) B1757821
theorem B6669155 : Blo 1040609 6669155 := bstep (se 1 (by rfl) ⟨5001866, by rfl⟩ : syracuseStep 6669155 = 10003733) B10003733
theorem B2343779 : Blo 1040609 2343779 := bstep (se 1 (by rfl) ⟨1757834, by rfl⟩ : syracuseStep 2343779 = 3515669) B3515669
theorem B7914509 : Blo 1040609 7914509 := bstep (se 3 (by rfl) ⟨1483970, by rfl⟩ : syracuseStep 7914509 = 2967941) B2967941
theorem B3523661 : Blo 1040609 3523661 := bstep (se 3 (by rfl) ⟨660686, by rfl⟩ : syracuseStep 3523661 = 1321373) B1321373
theorem B2344049 : Blo 1040609 2344049 := bstep (se 2 (by rfl) ⟨879018, by rfl⟩ : syracuseStep 2344049 = 1758037) B1758037
theorem B2344067 : Blo 1040609 2344067 := bstep (se 1 (by rfl) ⟨1758050, by rfl⟩ : syracuseStep 2344067 = 3516101) B3516101
theorem B3523715 : Blo 1040609 3523715 := bstep (se 1 (by rfl) ⟨2642786, by rfl⟩ : syracuseStep 3523715 = 5285573) B5285573
theorem B5948549 : Blo 1040609 5948549 := bstep (se 4 (by rfl) ⟨557676, by rfl⟩ : syracuseStep 5948549 = 1115353) B1115353
theorem B2344337 : Blo 1040609 2344337 := bstep (se 2 (by rfl) ⟨879126, by rfl⟩ : syracuseStep 2344337 = 1758253) B1758253
theorem B3523985 : Blo 1040609 3523985 := bstep (se 2 (by rfl) ⟨1321494, by rfl⟩ : syracuseStep 3523985 = 2642989) B2642989
theorem B2344355 : Blo 1040609 2344355 := bstep (se 1 (by rfl) ⟨1758266, by rfl⟩ : syracuseStep 2344355 = 3516533) B3516533
theorem B2967121 : Blo 1040609 2967121 := bstep (se 2 (by rfl) ⟨1112670, by rfl⟩ : syracuseStep 2967121 = 2225341) B2225341
theorem B2344625 : Blo 1040609 2344625 := bstep (se 2 (by rfl) ⟨879234, by rfl⟩ : syracuseStep 2344625 = 1758469) B1758469
theorem B2639537 : Blo 1040609 2639537 := bstep (se 2 (by rfl) ⟨989826, by rfl⟩ : syracuseStep 2639537 = 1979653) B1979653
theorem B2344643 : Blo 1040609 2344643 := bstep (se 1 (by rfl) ⟨1758482, by rfl⟩ : syracuseStep 2344643 = 3516965) B3516965
theorem B2639587 : Blo 1040609 2639587 := bstep (se 1 (by rfl) ⟨1979690, by rfl⟩ : syracuseStep 2639587 = 3959381) B3959381
theorem B5949233 : Blo 1040609 5949233 := bstep (se 2 (by rfl) ⟨2230962, by rfl⟩ : syracuseStep 5949233 = 4461925) B4461925
theorem B2639729 : Blo 1040609 2639729 := bstep (se 2 (by rfl) ⟨989898, by rfl⟩ : syracuseStep 2639729 = 1979797) B1979797
theorem B3524525 : Blo 1040609 3524525 := bstep (se 3 (by rfl) ⟨660848, by rfl⟩ : syracuseStep 3524525 = 1321697) B1321697
theorem B2344913 : Blo 1040609 2344913 := bstep (se 2 (by rfl) ⟨879342, by rfl⟩ : syracuseStep 2344913 = 1758685) B1758685
theorem B2344931 : Blo 1040609 2344931 := bstep (se 1 (by rfl) ⟨1758698, by rfl⟩ : syracuseStep 2344931 = 3517397) B3517397
theorem B3524579 : Blo 1040609 3524579 := bstep (se 1 (by rfl) ⟨2643434, by rfl⟩ : syracuseStep 3524579 = 5286869) B5286869
theorem B3754225 : Blo 1040609 3754225 := bstep (se 2 (by rfl) ⟨1407834, by rfl⟩ : syracuseStep 3754225 = 2815669) B2815669
theorem B2345201 : Blo 1040609 2345201 := bstep (se 2 (by rfl) ⟨879450, by rfl⟩ : syracuseStep 2345201 = 1758901) B1758901
theorem B3524849 : Blo 1040609 3524849 := bstep (se 2 (by rfl) ⟨1321818, by rfl⟩ : syracuseStep 3524849 = 2643637) B2643637
theorem B2345219 : Blo 1040609 2345219 := bstep (se 1 (by rfl) ⟨1758914, by rfl⟩ : syracuseStep 2345219 = 3517829) B3517829
theorem B2115857 : Blo 1040609 2115857 := bstep (se 2 (by rfl) ⟨793446, by rfl⟩ : syracuseStep 2115857 = 1586893) B1586893
theorem B6342947 : Blo 1040609 6342947 := bstep (se 1 (by rfl) ⟨4757210, by rfl⟩ : syracuseStep 6342947 = 9514421) B9514421
theorem B2116003 : Blo 1040609 2116003 := bstep (se 1 (by rfl) ⟨1587002, by rfl⟩ : syracuseStep 2116003 = 3174005) B3174005
theorem B3951089 : Blo 1040609 3951089 := bstep (se 2 (by rfl) ⟨1481658, by rfl⟩ : syracuseStep 3951089 = 2963317) B2963317
theorem B2345489 : Blo 1040609 2345489 := bstep (se 2 (by rfl) ⟨879558, by rfl⟩ : syracuseStep 2345489 = 1759117) B1759117
theorem B2345507 : Blo 1040609 2345507 := bstep (se 1 (by rfl) ⟨1759130, by rfl⟩ : syracuseStep 2345507 = 3518261) B3518261
theorem B3525389 : Blo 1040609 3525389 := bstep (se 3 (by rfl) ⟨661010, by rfl⟩ : syracuseStep 3525389 = 1322021) B1322021
theorem B2345777 : Blo 1040609 2345777 := bstep (se 2 (by rfl) ⟨879666, by rfl⟩ : syracuseStep 2345777 = 1759333) B1759333
theorem B2345795 : Blo 1040609 2345795 := bstep (se 1 (by rfl) ⟨1759346, by rfl⟩ : syracuseStep 2345795 = 3518693) B3518693
theorem B3525443 : Blo 1040609 3525443 := bstep (se 1 (by rfl) ⟨2644082, by rfl⟩ : syracuseStep 3525443 = 5288165) B5288165
theorem B2968397 : Blo 1040609 2968397 := bstep (se 3 (by rfl) ⟨556574, by rfl⟩ : syracuseStep 2968397 = 1113149) B1113149
theorem B2640721 : Blo 1040609 2640721 := bstep (se 2 (by rfl) ⟨990270, by rfl⟩ : syracuseStep 2640721 = 1980541) B1980541
theorem B2509699 : Blo 1040609 2509699 := bstep (se 1 (by rfl) ⟨1882274, by rfl⟩ : syracuseStep 2509699 = 3764549) B3764549
theorem B1756147 : Blo 1040609 1756147 := bstep (se 1 (by rfl) ⟨1317110, by rfl⟩ : syracuseStep 1756147 = 2634221) B2634221
theorem B2968579 : Blo 1040609 2968579 := bstep (se 1 (by rfl) ⟨2226434, by rfl⟩ : syracuseStep 2968579 = 4452869) B4452869
theorem B2968625 : Blo 1040609 2968625 := bstep (se 2 (by rfl) ⟨1113234, by rfl⟩ : syracuseStep 2968625 = 2226469) B2226469
theorem B2346065 : Blo 1040609 2346065 := bstep (se 2 (by rfl) ⟨879774, by rfl⟩ : syracuseStep 2346065 = 1759549) B1759549
theorem B2346083 : Blo 1040609 2346083 := bstep (se 1 (by rfl) ⟨1759562, by rfl⟩ : syracuseStep 2346083 = 3519125) B3519125
theorem B2640995 : Blo 1040609 2640995 := bstep (se 1 (by rfl) ⟨1980746, by rfl⟩ : syracuseStep 2640995 = 3961493) B3961493
theorem B1756289 : Blo 1040609 1756289 := bstep (se 2 (by rfl) ⟨658608, by rfl⟩ : syracuseStep 1756289 = 1317217) B1317217
theorem B5786765 : Blo 1040609 5786765 := bstep (se 3 (by rfl) ⟨1085018, by rfl⟩ : syracuseStep 5786765 = 2170037) B2170037
theorem B1756417 : Blo 1040609 1756417 := bstep (se 2 (by rfl) ⟨658656, by rfl⟩ : syracuseStep 1756417 = 1317313) B1317313
theorem B1756451 : Blo 1040609 1756451 := bstep (se 1 (by rfl) ⟨1317338, by rfl⟩ : syracuseStep 1756451 = 2634677) B2634677
theorem B2641187 : Blo 1040609 2641187 := bstep (se 1 (by rfl) ⟨1980890, by rfl⟩ : syracuseStep 2641187 = 3961781) B3961781
theorem B6016369 : Blo 1040609 6016369 := bstep (se 2 (by rfl) ⟨2256138, by rfl⟩ : syracuseStep 6016369 = 4512277) B4512277
theorem B2346353 : Blo 1040609 2346353 := bstep (se 2 (by rfl) ⟨879882, by rfl⟩ : syracuseStep 2346353 = 1759765) B1759765
theorem B2346371 : Blo 1040609 2346371 := bstep (se 1 (by rfl) ⟨1759778, by rfl⟩ : syracuseStep 2346371 = 3519557) B3519557
theorem B2117009 : Blo 1040609 2117009 := bstep (se 2 (by rfl) ⟨793878, by rfl⟩ : syracuseStep 2117009 = 1587757) B1587757
theorem B1756579 : Blo 1040609 1756579 := bstep (se 1 (by rfl) ⟨1317434, by rfl⟩ : syracuseStep 1756579 = 2634869) B2634869
theorem B2379217 : Blo 1040609 2379217 := bstep (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) B1784413
theorem B1756721 : Blo 1040609 1756721 := bstep (se 2 (by rfl) ⟨658770, by rfl⟩ : syracuseStep 1756721 = 1317541) B1317541
theorem B2346641 : Blo 1040609 2346641 := bstep (se 2 (by rfl) ⟨879990, by rfl⟩ : syracuseStep 2346641 = 1759981) B1759981
theorem B2346659 : Blo 1040609 2346659 := bstep (se 1 (by rfl) ⟨1759994, by rfl⟩ : syracuseStep 2346659 = 3519989) B3519989
theorem B1756849 : Blo 1040609 1756849 := bstep (se 2 (by rfl) ⟨658818, by rfl⟩ : syracuseStep 1756849 = 1317637) B1317637
theorem B1756883 : Blo 1040609 1756883 := bstep (se 1 (by rfl) ⟨1317662, by rfl⟩ : syracuseStep 1756883 = 2635325) B2635325
theorem B6344453 : Blo 1040609 6344453 := bstep (se 4 (by rfl) ⟨594792, by rfl⟩ : syracuseStep 6344453 = 1189585) B1189585
theorem B5426957 : Blo 1040609 5426957 := bstep (se 3 (by rfl) ⟨1017554, by rfl⟩ : syracuseStep 5426957 = 2035109) B2035109
theorem B1757011 : Blo 1040609 1757011 := bstep (se 1 (by rfl) ⟨1317758, by rfl⟩ : syracuseStep 1757011 = 2635517) B2635517
theorem B7917425 : Blo 1040609 7917425 := bstep (se 2 (by rfl) ⟨2969034, by rfl⟩ : syracuseStep 7917425 = 5938069) B5938069
theorem B3952547 : Blo 1040609 3952547 := bstep (se 1 (by rfl) ⟨2964410, by rfl⟩ : syracuseStep 3952547 = 5928821) B5928821
theorem B2346929 : Blo 1040609 2346929 := bstep (se 2 (by rfl) ⟨880098, by rfl⟩ : syracuseStep 2346929 = 1760197) B1760197
theorem B2346947 : Blo 1040609 2346947 := bstep (se 1 (by rfl) ⟨1760210, by rfl⟩ : syracuseStep 2346947 = 3520421) B3520421
theorem B1757153 : Blo 1040609 1757153 := bstep (se 2 (by rfl) ⟨658932, by rfl⟩ : syracuseStep 1757153 = 1317865) B1317865
theorem B1757281 : Blo 1040609 1757281 := bstep (se 2 (by rfl) ⟨658980, by rfl⟩ : syracuseStep 1757281 = 1317961) B1317961
theorem B1757315 : Blo 1040609 1757315 := bstep (se 1 (by rfl) ⟨1317986, by rfl⟩ : syracuseStep 1757315 = 2635973) B2635973
theorem B2347217 : Blo 1040609 2347217 := bstep (se 2 (by rfl) ⟨880206, by rfl⟩ : syracuseStep 2347217 = 1760413) B1760413
theorem B2642129 : Blo 1040609 2642129 := bstep (se 2 (by rfl) ⟨990798, by rfl⟩ : syracuseStep 2642129 = 1981597) B1981597
theorem B2347235 : Blo 1040609 2347235 := bstep (se 1 (by rfl) ⟨1760426, by rfl⟩ : syracuseStep 2347235 = 3520853) B3520853
theorem B1757443 : Blo 1040609 1757443 := bstep (se 1 (by rfl) ⟨1318082, by rfl⟩ : syracuseStep 1757443 = 2636165) B2636165
theorem B2642179 : Blo 1040609 2642179 := bstep (se 1 (by rfl) ⟨1981634, by rfl⟩ : syracuseStep 2642179 = 3963269) B3963269
theorem B1560929 : Blo 1040609 1560929 := bstep (se 2 (by rfl) ⟨585348, by rfl⟩ : syracuseStep 1560929 = 1170697) B1170697
theorem B1560947 : Blo 1040609 1560947 := bstep (se 1 (by rfl) ⟨1170710, by rfl⟩ : syracuseStep 1560947 = 2341421) B2341421
theorem B1560977 : Blo 1040609 1560977 := bstep (se 2 (by rfl) ⟨585366, by rfl⟩ : syracuseStep 1560977 = 1170733) B1170733
theorem B1757585 : Blo 1040609 1757585 := bstep (se 2 (by rfl) ⟨659094, by rfl⟩ : syracuseStep 1757585 = 1318189) B1318189
theorem B2642321 : Blo 1040609 2642321 := bstep (se 2 (by rfl) ⟨990870, by rfl⟩ : syracuseStep 2642321 = 1981741) B1981741
theorem B1692065 : Blo 1040609 1692065 := bstep (se 2 (by rfl) ⟨634524, by rfl⟩ : syracuseStep 1692065 = 1269049) B1269049
theorem B1560995 : Blo 1040609 1560995 := bstep (se 1 (by rfl) ⟨1170746, by rfl⟩ : syracuseStep 1560995 = 2341493) B2341493
theorem B5001635 : Blo 1040609 5001635 := bstep (se 1 (by rfl) ⟨3751226, by rfl⟩ : syracuseStep 5001635 = 7502453) B7502453
theorem B1561025 : Blo 1040609 1561025 := bstep (se 2 (by rfl) ⟨585384, by rfl⟩ : syracuseStep 1561025 = 1170769) B1170769
theorem B1561043 : Blo 1040609 1561043 := bstep (se 1 (by rfl) ⟨1170782, by rfl⟩ : syracuseStep 1561043 = 2341565) B2341565
theorem B2970083 : Blo 1040609 2970083 := bstep (se 1 (by rfl) ⟨2227562, by rfl⟩ : syracuseStep 2970083 = 4455125) B4455125
theorem B1561073 : Blo 1040609 1561073 := bstep (se 2 (by rfl) ⟨585402, by rfl⟩ : syracuseStep 1561073 = 1170805) B1170805
theorem B2347505 : Blo 1040609 2347505 := bstep (se 2 (by rfl) ⟨880314, by rfl⟩ : syracuseStep 2347505 = 1760629) B1760629
theorem B1561091 : Blo 1040609 1561091 := bstep (se 1 (by rfl) ⟨1170818, by rfl⟩ : syracuseStep 1561091 = 2341637) B2341637
theorem B2347523 : Blo 1040609 2347523 := bstep (se 1 (by rfl) ⟨1760642, by rfl⟩ : syracuseStep 2347523 = 3521285) B3521285
theorem B1757713 : Blo 1040609 1757713 := bstep (se 2 (by rfl) ⟨659142, by rfl⟩ : syracuseStep 1757713 = 1318285) B1318285
theorem B1561121 : Blo 1040609 1561121 := bstep (se 2 (by rfl) ⟨585420, by rfl⟩ : syracuseStep 1561121 = 1170841) B1170841
theorem B1561139 : Blo 1040609 1561139 := bstep (se 1 (by rfl) ⟨1170854, by rfl⟩ : syracuseStep 1561139 = 2341709) B2341709
theorem B1757747 : Blo 1040609 1757747 := bstep (se 1 (by rfl) ⟨1318310, by rfl⟩ : syracuseStep 1757747 = 2636621) B2636621
theorem B1561169 : Blo 1040609 1561169 := bstep (se 2 (by rfl) ⟨585438, by rfl⟩ : syracuseStep 1561169 = 1170877) B1170877
theorem B1561187 : Blo 1040609 1561187 := bstep (se 1 (by rfl) ⟨1170890, by rfl⟩ : syracuseStep 1561187 = 2341781) B2341781
theorem B1561217 : Blo 1040609 1561217 := bstep (se 2 (by rfl) ⟨585456, by rfl⟩ : syracuseStep 1561217 = 1170913) B1170913
theorem B1561235 : Blo 1040609 1561235 := bstep (se 1 (by rfl) ⟨1170926, by rfl⟩ : syracuseStep 1561235 = 2341853) B2341853
theorem B1561265 : Blo 1040609 1561265 := bstep (se 2 (by rfl) ⟨585474, by rfl⟩ : syracuseStep 1561265 = 1170949) B1170949
theorem B1757875 : Blo 1040609 1757875 := bstep (se 1 (by rfl) ⟨1318406, by rfl⟩ : syracuseStep 1757875 = 2636813) B2636813
theorem B1561283 : Blo 1040609 1561283 := bstep (se 1 (by rfl) ⟨1170962, by rfl⟩ : syracuseStep 1561283 = 2341925) B2341925
theorem B1561313 : Blo 1040609 1561313 := bstep (se 2 (by rfl) ⟨585492, by rfl⟩ : syracuseStep 1561313 = 1170985) B1170985
theorem B1561331 : Blo 1040609 1561331 := bstep (se 1 (by rfl) ⟨1170998, by rfl⟩ : syracuseStep 1561331 = 2341997) B2341997
theorem B1561361 : Blo 1040609 1561361 := bstep (se 2 (by rfl) ⟨585510, by rfl⟩ : syracuseStep 1561361 = 1171021) B1171021
theorem B2347793 : Blo 1040609 2347793 := bstep (se 2 (by rfl) ⟨880422, by rfl⟩ : syracuseStep 2347793 = 1760845) B1760845
theorem B1561379 : Blo 1040609 1561379 := bstep (se 1 (by rfl) ⟨1171034, by rfl⟩ : syracuseStep 1561379 = 2342069) B2342069
theorem B2347811 : Blo 1040609 2347811 := bstep (se 1 (by rfl) ⟨1760858, by rfl⟩ : syracuseStep 2347811 = 3521717) B3521717
theorem B1561409 : Blo 1040609 1561409 := bstep (se 2 (by rfl) ⟨585528, by rfl⟩ : syracuseStep 1561409 = 1171057) B1171057
theorem B1758017 : Blo 1040609 1758017 := bstep (se 2 (by rfl) ⟨659256, by rfl⟩ : syracuseStep 1758017 = 1318513) B1318513
theorem B1561427 : Blo 1040609 1561427 := bstep (se 1 (by rfl) ⟨1171070, by rfl⟩ : syracuseStep 1561427 = 2342141) B2342141
theorem B1561457 : Blo 1040609 1561457 := bstep (se 2 (by rfl) ⟨585546, by rfl⟩ : syracuseStep 1561457 = 1171093) B1171093
theorem B1561475 : Blo 1040609 1561475 := bstep (se 1 (by rfl) ⟨1171106, by rfl⟩ : syracuseStep 1561475 = 2342213) B2342213
theorem B3953549 : Blo 1040609 3953549 := bstep (se 3 (by rfl) ⟨741290, by rfl⟩ : syracuseStep 3953549 = 1482581) B1482581
theorem B1561505 : Blo 1040609 1561505 := bstep (se 2 (by rfl) ⟨585564, by rfl⟩ : syracuseStep 1561505 = 1171129) B1171129
theorem B1561523 : Blo 1040609 1561523 := bstep (se 1 (by rfl) ⟨1171142, by rfl⟩ : syracuseStep 1561523 = 2342285) B2342285
theorem B1758145 : Blo 1040609 1758145 := bstep (se 2 (by rfl) ⟨659304, by rfl⟩ : syracuseStep 1758145 = 1318609) B1318609
theorem B6673357 : Blo 1040609 6673357 := bstep (se 3 (by rfl) ⟨1251254, by rfl⟩ : syracuseStep 6673357 = 2502509) B2502509
theorem B1561553 : Blo 1040609 1561553 := bstep (se 2 (by rfl) ⟨585582, by rfl⟩ : syracuseStep 1561553 = 1171165) B1171165
theorem B1561571 : Blo 1040609 1561571 := bstep (se 1 (by rfl) ⟨1171178, by rfl⟩ : syracuseStep 1561571 = 2342357) B2342357
theorem B1758179 : Blo 1040609 1758179 := bstep (se 1 (by rfl) ⟨1318634, by rfl⟩ : syracuseStep 1758179 = 2637269) B2637269
theorem B1561601 : Blo 1040609 1561601 := bstep (se 2 (by rfl) ⟨585600, by rfl⟩ : syracuseStep 1561601 = 1171201) B1171201
theorem B1561619 : Blo 1040609 1561619 := bstep (se 1 (by rfl) ⟨1171214, by rfl⟩ : syracuseStep 1561619 = 2342429) B2342429
theorem B1561649 : Blo 1040609 1561649 := bstep (se 2 (by rfl) ⟨585618, by rfl⟩ : syracuseStep 1561649 = 1171237) B1171237
theorem B2348081 : Blo 1040609 2348081 := bstep (se 2 (by rfl) ⟨880530, by rfl⟩ : syracuseStep 2348081 = 1761061) B1761061
theorem B1561667 : Blo 1040609 1561667 := bstep (se 1 (by rfl) ⟨1171250, by rfl⟩ : syracuseStep 1561667 = 2342501) B2342501
theorem B2348099 : Blo 1040609 2348099 := bstep (se 1 (by rfl) ⟨1761074, by rfl⟩ : syracuseStep 2348099 = 3522149) B3522149
theorem B1561697 : Blo 1040609 1561697 := bstep (se 2 (by rfl) ⟨585636, by rfl⟩ : syracuseStep 1561697 = 1171273) B1171273
theorem B1758307 : Blo 1040609 1758307 := bstep (se 1 (by rfl) ⟨1318730, by rfl⟩ : syracuseStep 1758307 = 2637461) B2637461
theorem B43308145 : Blo 1040609 43308145 := bstep (se 2 (by rfl) ⟨16240554, by rfl⟩ : syracuseStep 43308145 = 32481109) B32481109
theorem B1561715 : Blo 1040609 1561715 := bstep (se 1 (by rfl) ⟨1171286, by rfl⟩ : syracuseStep 1561715 = 2342573) B2342573
theorem B1561745 : Blo 1040609 1561745 := bstep (se 2 (by rfl) ⟨585654, by rfl⟩ : syracuseStep 1561745 = 1171309) B1171309
theorem B1561763 : Blo 1040609 1561763 := bstep (se 1 (by rfl) ⟨1171322, by rfl⟩ : syracuseStep 1561763 = 2342645) B2342645
theorem B1561793 : Blo 1040609 1561793 := bstep (se 2 (by rfl) ⟨585672, by rfl⟩ : syracuseStep 1561793 = 1171345) B1171345
theorem B1561811 : Blo 1040609 1561811 := bstep (se 1 (by rfl) ⟨1171358, by rfl⟩ : syracuseStep 1561811 = 2342717) B2342717
theorem B1561841 : Blo 1040609 1561841 := bstep (se 2 (by rfl) ⟨585690, by rfl⟩ : syracuseStep 1561841 = 1171381) B1171381
theorem B1758449 : Blo 1040609 1758449 := bstep (se 2 (by rfl) ⟨659418, by rfl⟩ : syracuseStep 1758449 = 1318837) B1318837
theorem B1561859 : Blo 1040609 1561859 := bstep (se 1 (by rfl) ⟨1171394, by rfl⟩ : syracuseStep 1561859 = 2342789) B2342789
theorem B1561889 : Blo 1040609 1561889 := bstep (se 2 (by rfl) ⟨585708, by rfl⟩ : syracuseStep 1561889 = 1171417) B1171417
theorem B1561907 : Blo 1040609 1561907 := bstep (se 1 (by rfl) ⟨1171430, by rfl⟩ : syracuseStep 1561907 = 2342861) B2342861
theorem B1561937 : Blo 1040609 1561937 := bstep (se 2 (by rfl) ⟨585726, by rfl⟩ : syracuseStep 1561937 = 1171453) B1171453
theorem B2348369 : Blo 1040609 2348369 := bstep (se 2 (by rfl) ⟨880638, by rfl⟩ : syracuseStep 2348369 = 1761277) B1761277
theorem B1561955 : Blo 1040609 1561955 := bstep (se 1 (by rfl) ⟨1171466, by rfl⟩ : syracuseStep 1561955 = 2342933) B2342933
theorem B2348387 : Blo 1040609 2348387 := bstep (se 1 (by rfl) ⟨1761290, by rfl⟩ : syracuseStep 2348387 = 3522581) B3522581
theorem B1758577 : Blo 1040609 1758577 := bstep (se 2 (by rfl) ⟨659466, by rfl⟩ : syracuseStep 1758577 = 1318933) B1318933
theorem B2643313 : Blo 1040609 2643313 := bstep (se 2 (by rfl) ⟨991242, by rfl⟩ : syracuseStep 2643313 = 1982485) B1982485
theorem B1561985 : Blo 1040609 1561985 := bstep (se 2 (by rfl) ⟨585744, by rfl⟩ : syracuseStep 1561985 = 1171489) B1171489
theorem B1562003 : Blo 1040609 1562003 := bstep (se 1 (by rfl) ⟨1171502, by rfl⟩ : syracuseStep 1562003 = 2343005) B2343005
theorem B1758611 : Blo 1040609 1758611 := bstep (se 1 (by rfl) ⟨1318958, by rfl⟩ : syracuseStep 1758611 = 2637917) B2637917
theorem B1562033 : Blo 1040609 1562033 := bstep (se 2 (by rfl) ⟨585762, by rfl⟩ : syracuseStep 1562033 = 1171525) B1171525
theorem B2381233 : Blo 1040609 2381233 := bstep (se 2 (by rfl) ⟨892962, by rfl⟩ : syracuseStep 2381233 = 1785925) B1785925
theorem B1562051 : Blo 1040609 1562051 := bstep (se 1 (by rfl) ⟨1171538, by rfl⟩ : syracuseStep 1562051 = 2343077) B2343077
theorem B1562081 : Blo 1040609 1562081 := bstep (se 2 (by rfl) ⟨585780, by rfl⟩ : syracuseStep 1562081 = 1171561) B1171561
theorem B1562099 : Blo 1040609 1562099 := bstep (se 1 (by rfl) ⟨1171574, by rfl⟩ : syracuseStep 1562099 = 2343149) B2343149
theorem B1562129 : Blo 1040609 1562129 := bstep (se 2 (by rfl) ⟨585798, by rfl⟩ : syracuseStep 1562129 = 1171597) B1171597
theorem B1758739 : Blo 1040609 1758739 := bstep (se 1 (by rfl) ⟨1319054, by rfl⟩ : syracuseStep 1758739 = 2638109) B2638109
theorem B22533653 : Blo 1040609 22533653 := bstep (se 6 (by rfl) ⟨528132, by rfl⟩ : syracuseStep 22533653 = 1056265) B1056265
theorem B1562147 : Blo 1040609 1562147 := bstep (se 1 (by rfl) ⟨1171610, by rfl⟩ : syracuseStep 1562147 = 2343221) B2343221
theorem B1562177 : Blo 1040609 1562177 := bstep (se 2 (by rfl) ⟨585816, by rfl⟩ : syracuseStep 1562177 = 1171633) B1171633
theorem B1562195 : Blo 1040609 1562195 := bstep (se 1 (by rfl) ⟨1171646, by rfl⟩ : syracuseStep 1562195 = 2343293) B2343293
theorem B1562225 : Blo 1040609 1562225 := bstep (se 2 (by rfl) ⟨585834, by rfl⟩ : syracuseStep 1562225 = 1171669) B1171669
theorem B2348657 : Blo 1040609 2348657 := bstep (se 2 (by rfl) ⟨880746, by rfl⟩ : syracuseStep 2348657 = 1761493) B1761493
theorem B1562243 : Blo 1040609 1562243 := bstep (se 1 (by rfl) ⟨1171682, by rfl⟩ : syracuseStep 1562243 = 2343365) B2343365
theorem B2348675 : Blo 1040609 2348675 := bstep (se 1 (by rfl) ⟨1761506, by rfl⟩ : syracuseStep 2348675 = 3523013) B3523013
theorem B2643587 : Blo 1040609 2643587 := bstep (se 1 (by rfl) ⟨1982690, by rfl⟩ : syracuseStep 2643587 = 3965381) B3965381
theorem B1562273 : Blo 1040609 1562273 := bstep (se 2 (by rfl) ⟨585852, by rfl⟩ : syracuseStep 1562273 = 1171705) B1171705
theorem B1758881 : Blo 1040609 1758881 := bstep (se 2 (by rfl) ⟨659580, by rfl⟩ : syracuseStep 1758881 = 1319161) B1319161
theorem B3757745 : Blo 1040609 3757745 := bstep (se 2 (by rfl) ⟨1409154, by rfl⟩ : syracuseStep 3757745 = 2818309) B2818309
theorem B2971313 : Blo 1040609 2971313 := bstep (se 2 (by rfl) ⟨1114242, by rfl⟩ : syracuseStep 2971313 = 2228485) B2228485
theorem B1562291 : Blo 1040609 1562291 := bstep (se 1 (by rfl) ⟨1171718, by rfl⟩ : syracuseStep 1562291 = 2343437) B2343437
theorem B1562321 : Blo 1040609 1562321 := bstep (se 2 (by rfl) ⟨585870, by rfl⟩ : syracuseStep 1562321 = 1171741) B1171741
theorem B1562339 : Blo 1040609 1562339 := bstep (se 1 (by rfl) ⟨1171754, by rfl⟩ : syracuseStep 1562339 = 2343509) B2343509
theorem B1562369 : Blo 1040609 1562369 := bstep (se 2 (by rfl) ⟨585888, by rfl⟩ : syracuseStep 1562369 = 1171777) B1171777
theorem B1562387 : Blo 1040609 1562387 := bstep (se 1 (by rfl) ⟨1171790, by rfl⟩ : syracuseStep 1562387 = 2343581) B2343581
theorem B1759009 : Blo 1040609 1759009 := bstep (se 2 (by rfl) ⟨659628, by rfl⟩ : syracuseStep 1759009 = 1319257) B1319257
theorem B1562417 : Blo 1040609 1562417 := bstep (se 2 (by rfl) ⟨585906, by rfl⟩ : syracuseStep 1562417 = 1171813) B1171813
theorem B1562435 : Blo 1040609 1562435 := bstep (se 1 (by rfl) ⟨1171826, by rfl⟩ : syracuseStep 1562435 = 2343653) B2343653
theorem B1759043 : Blo 1040609 1759043 := bstep (se 1 (by rfl) ⟨1319282, by rfl⟩ : syracuseStep 1759043 = 2638565) B2638565
theorem B2643779 : Blo 1040609 2643779 := bstep (se 1 (by rfl) ⟨1982834, by rfl⟩ : syracuseStep 2643779 = 3965669) B3965669
theorem B1562465 : Blo 1040609 1562465 := bstep (se 2 (by rfl) ⟨585924, by rfl⟩ : syracuseStep 1562465 = 1171849) B1171849
theorem B1562483 : Blo 1040609 1562483 := bstep (se 1 (by rfl) ⟨1171862, by rfl⟩ : syracuseStep 1562483 = 2343725) B2343725
theorem B1562513 : Blo 1040609 1562513 := bstep (se 2 (by rfl) ⟨585942, by rfl⟩ : syracuseStep 1562513 = 1171885) B1171885
theorem B2348945 : Blo 1040609 2348945 := bstep (se 2 (by rfl) ⟨880854, by rfl⟩ : syracuseStep 2348945 = 1761709) B1761709
theorem B1562531 : Blo 1040609 1562531 := bstep (se 1 (by rfl) ⟨1171898, by rfl⟩ : syracuseStep 1562531 = 2343797) B2343797
theorem B2348963 : Blo 1040609 2348963 := bstep (se 1 (by rfl) ⟨1761722, by rfl⟩ : syracuseStep 2348963 = 3523445) B3523445
theorem B1562561 : Blo 1040609 1562561 := bstep (se 2 (by rfl) ⟨585960, by rfl⟩ : syracuseStep 1562561 = 1171921) B1171921
theorem B1759171 : Blo 1040609 1759171 := bstep (se 1 (by rfl) ⟨1319378, by rfl⟩ : syracuseStep 1759171 = 2638757) B2638757
theorem B1562579 : Blo 1040609 1562579 := bstep (se 1 (by rfl) ⟨1171934, by rfl⟩ : syracuseStep 1562579 = 2343869) B2343869
theorem B1562609 : Blo 1040609 1562609 := bstep (se 2 (by rfl) ⟨585978, by rfl⟩ : syracuseStep 1562609 = 1171957) B1171957
theorem B1562627 : Blo 1040609 1562627 := bstep (se 1 (by rfl) ⟨1171970, by rfl⟩ : syracuseStep 1562627 = 2343941) B2343941
theorem B1562657 : Blo 1040609 1562657 := bstep (se 2 (by rfl) ⟨585996, by rfl⟩ : syracuseStep 1562657 = 1171993) B1171993
theorem B3004465 : Blo 1040609 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1562675 : Blo 1040609 1562675 := bstep (se 1 (by rfl) ⟨1172006, by rfl⟩ : syracuseStep 1562675 = 2344013) B2344013
theorem B1562705 : Blo 1040609 1562705 := bstep (se 2 (by rfl) ⟨586014, by rfl⟩ : syracuseStep 1562705 = 1172029) B1172029
theorem B1759313 : Blo 1040609 1759313 := bstep (se 2 (by rfl) ⟨659742, by rfl⟩ : syracuseStep 1759313 = 1319485) B1319485
theorem B1562723 : Blo 1040609 1562723 := bstep (se 1 (by rfl) ⟨1172042, by rfl⟩ : syracuseStep 1562723 = 2344085) B2344085
theorem B1562753 : Blo 1040609 1562753 := bstep (se 2 (by rfl) ⟨586032, by rfl⟩ : syracuseStep 1562753 = 1172065) B1172065
theorem B1562771 : Blo 1040609 1562771 := bstep (se 1 (by rfl) ⟨1172078, by rfl⟩ : syracuseStep 1562771 = 2344157) B2344157
theorem B1562801 : Blo 1040609 1562801 := bstep (se 2 (by rfl) ⟨586050, by rfl⟩ : syracuseStep 1562801 = 1172101) B1172101
theorem B2349233 : Blo 1040609 2349233 := bstep (se 2 (by rfl) ⟨880962, by rfl⟩ : syracuseStep 2349233 = 1761925) B1761925
theorem B1562819 : Blo 1040609 1562819 := bstep (se 1 (by rfl) ⟨1172114, by rfl⟩ : syracuseStep 1562819 = 2344229) B2344229
theorem B2349251 : Blo 1040609 2349251 := bstep (se 1 (by rfl) ⟨1761938, by rfl⟩ : syracuseStep 2349251 = 3523877) B3523877
theorem B1759441 : Blo 1040609 1759441 := bstep (se 2 (by rfl) ⟨659790, by rfl⟩ : syracuseStep 1759441 = 1319581) B1319581
theorem B1562849 : Blo 1040609 1562849 := bstep (se 2 (by rfl) ⟨586068, by rfl⟩ : syracuseStep 1562849 = 1172137) B1172137
theorem B1562867 : Blo 1040609 1562867 := bstep (se 1 (by rfl) ⟨1172150, by rfl⟩ : syracuseStep 1562867 = 2344301) B2344301
theorem B1759475 : Blo 1040609 1759475 := bstep (se 1 (by rfl) ⟨1319606, by rfl⟩ : syracuseStep 1759475 = 2639213) B2639213
theorem B1562897 : Blo 1040609 1562897 := bstep (se 2 (by rfl) ⟨586086, by rfl⟩ : syracuseStep 1562897 = 1172173) B1172173
theorem B1562915 : Blo 1040609 1562915 := bstep (se 1 (by rfl) ⟨1172186, by rfl⟩ : syracuseStep 1562915 = 2344373) B2344373
theorem B1562945 : Blo 1040609 1562945 := bstep (se 2 (by rfl) ⟨586104, by rfl⟩ : syracuseStep 1562945 = 1172209) B1172209
theorem B1562963 : Blo 1040609 1562963 := bstep (se 1 (by rfl) ⟨1172222, by rfl⟩ : syracuseStep 1562963 = 2344445) B2344445
theorem B1562993 : Blo 1040609 1562993 := bstep (se 2 (by rfl) ⟨586122, by rfl⟩ : syracuseStep 1562993 = 1172245) B1172245
theorem B1759603 : Blo 1040609 1759603 := bstep (se 1 (by rfl) ⟨1319702, by rfl⟩ : syracuseStep 1759603 = 2639405) B2639405
theorem B1563011 : Blo 1040609 1563011 := bstep (se 1 (by rfl) ⟨1172258, by rfl⟩ : syracuseStep 1563011 = 2344517) B2344517
theorem B1563041 : Blo 1040609 1563041 := bstep (se 2 (by rfl) ⟨586140, by rfl⟩ : syracuseStep 1563041 = 1172281) B1172281
theorem B1563059 : Blo 1040609 1563059 := bstep (se 1 (by rfl) ⟨1172294, by rfl⟩ : syracuseStep 1563059 = 2344589) B2344589
theorem B1563089 : Blo 1040609 1563089 := bstep (se 2 (by rfl) ⟨586158, by rfl⟩ : syracuseStep 1563089 = 1172317) B1172317
theorem B2349521 : Blo 1040609 2349521 := bstep (se 2 (by rfl) ⟨881070, by rfl⟩ : syracuseStep 2349521 = 1762141) B1762141
theorem B1563107 : Blo 1040609 1563107 := bstep (se 1 (by rfl) ⟨1172330, by rfl⟩ : syracuseStep 1563107 = 2344661) B2344661
theorem B2349539 : Blo 1040609 2349539 := bstep (se 1 (by rfl) ⟨1762154, by rfl⟩ : syracuseStep 2349539 = 3524309) B3524309
theorem B1563137 : Blo 1040609 1563137 := bstep (se 2 (by rfl) ⟨586176, by rfl⟩ : syracuseStep 1563137 = 1172353) B1172353
theorem B1759745 : Blo 1040609 1759745 := bstep (se 2 (by rfl) ⟨659904, by rfl⟩ : syracuseStep 1759745 = 1319809) B1319809
theorem B1563155 : Blo 1040609 1563155 := bstep (se 1 (by rfl) ⟨1172366, by rfl⟩ : syracuseStep 1563155 = 2344733) B2344733
theorem B1563185 : Blo 1040609 1563185 := bstep (se 2 (by rfl) ⟨586194, by rfl⟩ : syracuseStep 1563185 = 1172389) B1172389
theorem B1563203 : Blo 1040609 1563203 := bstep (se 1 (by rfl) ⟨1172402, by rfl⟩ : syracuseStep 1563203 = 2344805) B2344805
theorem B3758669 : Blo 1040609 3758669 := bstep (se 3 (by rfl) ⟨704750, by rfl⟩ : syracuseStep 3758669 = 1409501) B1409501
theorem B1563233 : Blo 1040609 1563233 := bstep (se 2 (by rfl) ⟨586212, by rfl⟩ : syracuseStep 1563233 = 1172425) B1172425
theorem B1563251 : Blo 1040609 1563251 := bstep (se 1 (by rfl) ⟨1172438, by rfl⟩ : syracuseStep 1563251 = 2344877) B2344877
theorem B1759873 : Blo 1040609 1759873 := bstep (se 2 (by rfl) ⟨659952, by rfl⟩ : syracuseStep 1759873 = 1319905) B1319905
theorem B1563281 : Blo 1040609 1563281 := bstep (se 2 (by rfl) ⟨586230, by rfl⟩ : syracuseStep 1563281 = 1172461) B1172461
theorem B1563299 : Blo 1040609 1563299 := bstep (se 1 (by rfl) ⟨1172474, by rfl⟩ : syracuseStep 1563299 = 2344949) B2344949
theorem B1759907 : Blo 1040609 1759907 := bstep (se 1 (by rfl) ⟨1319930, by rfl⟩ : syracuseStep 1759907 = 2639861) B2639861
theorem B1563329 : Blo 1040609 1563329 := bstep (se 2 (by rfl) ⟨586248, by rfl⟩ : syracuseStep 1563329 = 1172497) B1172497
theorem B1563347 : Blo 1040609 1563347 := bstep (se 1 (by rfl) ⟨1172510, by rfl⟩ : syracuseStep 1563347 = 2345021) B2345021
theorem B1563377 : Blo 1040609 1563377 := bstep (se 2 (by rfl) ⟨586266, by rfl⟩ : syracuseStep 1563377 = 1172533) B1172533
theorem B2349809 : Blo 1040609 2349809 := bstep (se 2 (by rfl) ⟨881178, by rfl⟩ : syracuseStep 2349809 = 1762357) B1762357
theorem B1563395 : Blo 1040609 1563395 := bstep (se 1 (by rfl) ⟨1172546, by rfl⟩ : syracuseStep 1563395 = 2345093) B2345093
theorem B2349827 : Blo 1040609 2349827 := bstep (se 1 (by rfl) ⟨1762370, by rfl⟩ : syracuseStep 2349827 = 3524741) B3524741
theorem B1563425 : Blo 1040609 1563425 := bstep (se 2 (by rfl) ⟨586284, by rfl⟩ : syracuseStep 1563425 = 1172569) B1172569
theorem B1760035 : Blo 1040609 1760035 := bstep (se 1 (by rfl) ⟨1320026, by rfl⟩ : syracuseStep 1760035 = 2640053) B2640053
theorem B1563443 : Blo 1040609 1563443 := bstep (se 1 (by rfl) ⟨1172582, by rfl⟩ : syracuseStep 1563443 = 2345165) B2345165
theorem B1563473 : Blo 1040609 1563473 := bstep (se 2 (by rfl) ⟨586302, by rfl⟩ : syracuseStep 1563473 = 1172605) B1172605
theorem B1563491 : Blo 1040609 1563491 := bstep (se 1 (by rfl) ⟨1172618, by rfl⟩ : syracuseStep 1563491 = 2345237) B2345237
theorem B1563521 : Blo 1040609 1563521 := bstep (se 2 (by rfl) ⟨586320, by rfl⟩ : syracuseStep 1563521 = 1172641) B1172641
theorem B1563539 : Blo 1040609 1563539 := bstep (se 1 (by rfl) ⟨1172654, by rfl⟩ : syracuseStep 1563539 = 2345309) B2345309
theorem B1563569 : Blo 1040609 1563569 := bstep (se 2 (by rfl) ⟨586338, by rfl⟩ : syracuseStep 1563569 = 1172677) B1172677
theorem B1760177 : Blo 1040609 1760177 := bstep (se 2 (by rfl) ⟨660066, by rfl⟩ : syracuseStep 1760177 = 1320133) B1320133
theorem B1563587 : Blo 1040609 1563587 := bstep (se 1 (by rfl) ⟨1172690, by rfl⟩ : syracuseStep 1563587 = 2345381) B2345381
theorem B3955661 : Blo 1040609 3955661 := bstep (se 3 (by rfl) ⟨741686, by rfl⟩ : syracuseStep 3955661 = 1483373) B1483373
theorem B1563617 : Blo 1040609 1563617 := bstep (se 2 (by rfl) ⟨586356, by rfl⟩ : syracuseStep 1563617 = 1172713) B1172713
theorem B1563635 : Blo 1040609 1563635 := bstep (se 1 (by rfl) ⟨1172726, by rfl⟩ : syracuseStep 1563635 = 2345453) B2345453
theorem B1563665 : Blo 1040609 1563665 := bstep (se 2 (by rfl) ⟨586374, by rfl⟩ : syracuseStep 1563665 = 1172749) B1172749
theorem B2350097 : Blo 1040609 2350097 := bstep (se 2 (by rfl) ⟨881286, by rfl⟩ : syracuseStep 2350097 = 1762573) B1762573
theorem B1563683 : Blo 1040609 1563683 := bstep (se 1 (by rfl) ⟨1172762, by rfl⟩ : syracuseStep 1563683 = 2345525) B2345525
theorem B2350115 : Blo 1040609 2350115 := bstep (se 1 (by rfl) ⟨1762586, by rfl⟩ : syracuseStep 2350115 = 3525173) B3525173
theorem B1760305 : Blo 1040609 1760305 := bstep (se 2 (by rfl) ⟨660114, by rfl⟩ : syracuseStep 1760305 = 1320229) B1320229
theorem B1563713 : Blo 1040609 1563713 := bstep (se 2 (by rfl) ⟨586392, by rfl⟩ : syracuseStep 1563713 = 1172785) B1172785
theorem B1563731 : Blo 1040609 1563731 := bstep (se 1 (by rfl) ⟨1172798, by rfl⟩ : syracuseStep 1563731 = 2345597) B2345597
theorem B1760339 : Blo 1040609 1760339 := bstep (se 1 (by rfl) ⟨1320254, by rfl⟩ : syracuseStep 1760339 = 2640509) B2640509
theorem B2972771 : Blo 1040609 2972771 := bstep (se 1 (by rfl) ⟨2229578, by rfl⟩ : syracuseStep 2972771 = 4459157) B4459157
theorem B1563761 : Blo 1040609 1563761 := bstep (se 2 (by rfl) ⟨586410, by rfl⟩ : syracuseStep 1563761 = 1172821) B1172821
theorem B1563779 : Blo 1040609 1563779 := bstep (se 1 (by rfl) ⟨1172834, by rfl⟩ : syracuseStep 1563779 = 2345669) B2345669
theorem B1563809 : Blo 1040609 1563809 := bstep (se 2 (by rfl) ⟨586428, by rfl⟩ : syracuseStep 1563809 = 1172857) B1172857
theorem B1563827 : Blo 1040609 1563827 := bstep (se 1 (by rfl) ⟨1172870, by rfl⟩ : syracuseStep 1563827 = 2345741) B2345741
theorem B1563857 : Blo 1040609 1563857 := bstep (se 2 (by rfl) ⟨586446, by rfl⟩ : syracuseStep 1563857 = 1172893) B1172893
theorem B1760467 : Blo 1040609 1760467 := bstep (se 1 (by rfl) ⟨1320350, by rfl⟩ : syracuseStep 1760467 = 2640701) B2640701
theorem B1563875 : Blo 1040609 1563875 := bstep (se 1 (by rfl) ⟨1172906, by rfl⟩ : syracuseStep 1563875 = 2345813) B2345813
theorem B1563905 : Blo 1040609 1563905 := bstep (se 2 (by rfl) ⟨586464, by rfl⟩ : syracuseStep 1563905 = 1172929) B1172929
theorem B1563923 : Blo 1040609 1563923 := bstep (se 1 (by rfl) ⟨1172942, by rfl⟩ : syracuseStep 1563923 = 2345885) B2345885
theorem B1563953 : Blo 1040609 1563953 := bstep (se 2 (by rfl) ⟨586482, by rfl⟩ : syracuseStep 1563953 = 1172965) B1172965
theorem B1563971 : Blo 1040609 1563971 := bstep (se 1 (by rfl) ⟨1172978, by rfl⟩ : syracuseStep 1563971 = 2345957) B2345957
theorem B1564001 : Blo 1040609 1564001 := bstep (se 2 (by rfl) ⟨586500, by rfl⟩ : syracuseStep 1564001 = 1173001) B1173001
theorem B1760609 : Blo 1040609 1760609 := bstep (se 2 (by rfl) ⟨660228, by rfl⟩ : syracuseStep 1760609 = 1320457) B1320457
theorem B1170787 : Blo 1040609 1170787 := bstep (se 1 (by rfl) ⟨878090, by rfl⟩ : syracuseStep 1170787 = 1756181) B1756181
theorem B1564019 : Blo 1040609 1564019 := bstep (se 1 (by rfl) ⟨1173014, by rfl⟩ : syracuseStep 1564019 = 2346029) B2346029
theorem B1564049 : Blo 1040609 1564049 := bstep (se 2 (by rfl) ⟨586518, by rfl⟩ : syracuseStep 1564049 = 1173037) B1173037
theorem B1564067 : Blo 1040609 1564067 := bstep (se 1 (by rfl) ⟨1173050, by rfl⟩ : syracuseStep 1564067 = 2346101) B2346101
theorem B1564097 : Blo 1040609 1564097 := bstep (se 2 (by rfl) ⟨586536, by rfl⟩ : syracuseStep 1564097 = 1173073) B1173073
theorem B3562957 : Blo 1040609 3562957 := bstep (se 3 (by rfl) ⟨668054, by rfl⟩ : syracuseStep 3562957 = 1336109) B1336109
theorem B1564115 : Blo 1040609 1564115 := bstep (se 1 (by rfl) ⟨1173086, by rfl⟩ : syracuseStep 1564115 = 2346173) B2346173
theorem B1760737 : Blo 1040609 1760737 := bstep (se 2 (by rfl) ⟨660276, by rfl⟩ : syracuseStep 1760737 = 1320553) B1320553
theorem B1564145 : Blo 1040609 1564145 := bstep (se 2 (by rfl) ⟨586554, by rfl⟩ : syracuseStep 1564145 = 1173109) B1173109
theorem B1170931 : Blo 1040609 1170931 := bstep (se 1 (by rfl) ⟨878198, by rfl⟩ : syracuseStep 1170931 = 1756397) B1756397
theorem B1564163 : Blo 1040609 1564163 := bstep (se 1 (by rfl) ⟨1173122, by rfl⟩ : syracuseStep 1564163 = 2346245) B2346245
theorem B1760771 : Blo 1040609 1760771 := bstep (se 1 (by rfl) ⟨1320578, by rfl⟩ : syracuseStep 1760771 = 2641157) B2641157
theorem B1564193 : Blo 1040609 1564193 := bstep (se 2 (by rfl) ⟨586572, by rfl⟩ : syracuseStep 1564193 = 1173145) B1173145
theorem B1564211 : Blo 1040609 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B1564241 : Blo 1040609 1564241 := bstep (se 2 (by rfl) ⟨586590, by rfl⟩ : syracuseStep 1564241 = 1173181) B1173181
theorem B1564259 : Blo 1040609 1564259 := bstep (se 1 (by rfl) ⟨1173194, by rfl⟩ : syracuseStep 1564259 = 2346389) B2346389
theorem B1564289 : Blo 1040609 1564289 := bstep (se 2 (by rfl) ⟨586608, by rfl⟩ : syracuseStep 1564289 = 1173217) B1173217
theorem B1171075 : Blo 1040609 1171075 := bstep (se 1 (by rfl) ⟨878306, by rfl⟩ : syracuseStep 1171075 = 1756613) B1756613
theorem B1760899 : Blo 1040609 1760899 := bstep (se 1 (by rfl) ⟨1320674, by rfl⟩ : syracuseStep 1760899 = 2641349) B2641349
theorem B1564307 : Blo 1040609 1564307 := bstep (se 1 (by rfl) ⟨1173230, by rfl⟩ : syracuseStep 1564307 = 2346461) B2346461
theorem B3006115 : Blo 1040609 3006115 := bstep (se 1 (by rfl) ⟨2254586, by rfl⟩ : syracuseStep 3006115 = 4509173) B4509173
theorem B3169955 : Blo 1040609 3169955 := bstep (se 1 (by rfl) ⟨2377466, by rfl⟩ : syracuseStep 3169955 = 4754933) B4754933
theorem B1564337 : Blo 1040609 1564337 := bstep (se 2 (by rfl) ⟨586626, by rfl⟩ : syracuseStep 1564337 = 1173253) B1173253
theorem B1564355 : Blo 1040609 1564355 := bstep (se 1 (by rfl) ⟨1173266, by rfl⟩ : syracuseStep 1564355 = 2346533) B2346533
theorem B1564385 : Blo 1040609 1564385 := bstep (se 2 (by rfl) ⟨586644, by rfl⟩ : syracuseStep 1564385 = 1173289) B1173289
theorem B11853539 : Blo 1040609 11853539 := bstep (se 1 (by rfl) ⟨8890154, by rfl⟩ : syracuseStep 11853539 = 17780309) B17780309
theorem B3956465 : Blo 1040609 3956465 := bstep (se 2 (by rfl) ⟨1483674, by rfl⟩ : syracuseStep 3956465 = 2967349) B2967349
theorem B1564403 : Blo 1040609 1564403 := bstep (se 1 (by rfl) ⟨1173302, by rfl⟩ : syracuseStep 1564403 = 2346605) B2346605
theorem B1564433 : Blo 1040609 1564433 := bstep (se 2 (by rfl) ⟨586662, by rfl⟩ : syracuseStep 1564433 = 1173325) B1173325
theorem B1761041 : Blo 1040609 1761041 := bstep (se 2 (by rfl) ⟨660390, by rfl⟩ : syracuseStep 1761041 = 1320781) B1320781
theorem B1171219 : Blo 1040609 1171219 := bstep (se 1 (by rfl) ⟨878414, by rfl⟩ : syracuseStep 1171219 = 1756829) B1756829
theorem B1564451 : Blo 1040609 1564451 := bstep (se 1 (by rfl) ⟨1173338, by rfl⟩ : syracuseStep 1564451 = 2346677) B2346677
theorem B1564481 : Blo 1040609 1564481 := bstep (se 2 (by rfl) ⟨586680, by rfl⟩ : syracuseStep 1564481 = 1173361) B1173361
theorem B1564499 : Blo 1040609 1564499 := bstep (se 1 (by rfl) ⟨1173374, by rfl⟩ : syracuseStep 1564499 = 2346749) B2346749
theorem B1564529 : Blo 1040609 1564529 := bstep (se 2 (by rfl) ⟨586698, by rfl⟩ : syracuseStep 1564529 = 1173397) B1173397
theorem B1564547 : Blo 1040609 1564547 := bstep (se 1 (by rfl) ⟨1173410, by rfl⟩ : syracuseStep 1564547 = 2346821) B2346821
theorem B2973581 : Blo 1040609 2973581 := bstep (se 3 (by rfl) ⟨557546, by rfl⟩ : syracuseStep 2973581 = 1115093) B1115093
theorem B1761169 : Blo 1040609 1761169 := bstep (se 2 (by rfl) ⟨660438, by rfl⟩ : syracuseStep 1761169 = 1320877) B1320877
theorem B1564577 : Blo 1040609 1564577 := bstep (se 2 (by rfl) ⟨586716, by rfl⟩ : syracuseStep 1564577 = 1173433) B1173433
theorem B1171363 : Blo 1040609 1171363 := bstep (se 1 (by rfl) ⟨878522, by rfl⟩ : syracuseStep 1171363 = 1757045) B1757045
theorem B1564595 : Blo 1040609 1564595 := bstep (se 1 (by rfl) ⟨1173446, by rfl⟩ : syracuseStep 1564595 = 2346893) B2346893
theorem B1761203 : Blo 1040609 1761203 := bstep (se 1 (by rfl) ⟨1320902, by rfl⟩ : syracuseStep 1761203 = 2641805) B2641805
theorem B2678723 : Blo 1040609 2678723 := bstep (se 1 (by rfl) ⟨2009042, by rfl⟩ : syracuseStep 2678723 = 4018085) B4018085
theorem B1564625 : Blo 1040609 1564625 := bstep (se 2 (by rfl) ⟨586734, by rfl⟩ : syracuseStep 1564625 = 1173469) B1173469
theorem B4513763 : Blo 1040609 4513763 := bstep (se 1 (by rfl) ⟨3385322, by rfl⟩ : syracuseStep 4513763 = 6770645) B6770645
theorem B1564643 : Blo 1040609 1564643 := bstep (se 1 (by rfl) ⟨1173482, by rfl⟩ : syracuseStep 1564643 = 2346965) B2346965
theorem B1564673 : Blo 1040609 1564673 := bstep (se 2 (by rfl) ⟨586752, by rfl⟩ : syracuseStep 1564673 = 1173505) B1173505
theorem B1564691 : Blo 1040609 1564691 := bstep (se 1 (by rfl) ⟨1173518, by rfl⟩ : syracuseStep 1564691 = 2347037) B2347037
theorem B3170353 : Blo 1040609 3170353 := bstep (se 2 (by rfl) ⟨1188882, by rfl⟩ : syracuseStep 3170353 = 2377765) B2377765
theorem B1564721 : Blo 1040609 1564721 := bstep (se 2 (by rfl) ⟨586770, by rfl⟩ : syracuseStep 1564721 = 1173541) B1173541
theorem B1171507 : Blo 1040609 1171507 := bstep (se 1 (by rfl) ⟨878630, by rfl⟩ : syracuseStep 1171507 = 1757261) B1757261
theorem B1761331 : Blo 1040609 1761331 := bstep (se 1 (by rfl) ⟨1320998, by rfl⟩ : syracuseStep 1761331 = 2641997) B2641997
theorem B1564739 : Blo 1040609 1564739 := bstep (se 1 (by rfl) ⟨1173554, by rfl⟩ : syracuseStep 1564739 = 2347109) B2347109
theorem B2973773 : Blo 1040609 2973773 := bstep (se 3 (by rfl) ⟨557582, by rfl⟩ : syracuseStep 2973773 = 1115165) B1115165
theorem B1564769 : Blo 1040609 1564769 := bstep (se 2 (by rfl) ⟨586788, by rfl⟩ : syracuseStep 1564769 = 1173577) B1173577
theorem B1564787 : Blo 1040609 1564787 := bstep (se 1 (by rfl) ⟨1173590, by rfl⟩ : syracuseStep 1564787 = 2347181) B2347181
theorem B1564817 : Blo 1040609 1564817 := bstep (se 2 (by rfl) ⟨586806, by rfl⟩ : syracuseStep 1564817 = 1173613) B1173613
theorem B1564835 : Blo 1040609 1564835 := bstep (se 1 (by rfl) ⟨1173626, by rfl⟩ : syracuseStep 1564835 = 2347253) B2347253
theorem B3334321 : Blo 1040609 3334321 := bstep (se 2 (by rfl) ⟨1250370, by rfl⟩ : syracuseStep 3334321 = 2500741) B2500741
theorem B1564865 : Blo 1040609 1564865 := bstep (se 2 (by rfl) ⟨586824, by rfl⟩ : syracuseStep 1564865 = 1173649) B1173649
theorem B1761473 : Blo 1040609 1761473 := bstep (se 2 (by rfl) ⟨660552, by rfl⟩ : syracuseStep 1761473 = 1321105) B1321105
theorem B1171651 : Blo 1040609 1171651 := bstep (se 1 (by rfl) ⟨878738, by rfl⟩ : syracuseStep 1171651 = 1757477) B1757477
theorem B1564883 : Blo 1040609 1564883 := bstep (se 1 (by rfl) ⟨1173662, by rfl⟩ : syracuseStep 1564883 = 2347325) B2347325
theorem B1040611 : Blo 1040609 1040611 := bstep (se 1 (by rfl) ⟨780458, by rfl⟩ : syracuseStep 1040611 = 1560917) B1560917
theorem B1564913 : Blo 1040609 1564913 := bstep (se 2 (by rfl) ⟨586842, by rfl⟩ : syracuseStep 1564913 = 1173685) B1173685
theorem B1040627 : Blo 1040609 1040627 := bstep (se 1 (by rfl) ⟨780470, by rfl⟩ : syracuseStep 1040627 = 1560941) B1560941
theorem B1040643 : Blo 1040609 1040643 := bstep (se 1 (by rfl) ⟨780482, by rfl⟩ : syracuseStep 1040643 = 1560965) B1560965
theorem B1564931 : Blo 1040609 1564931 := bstep (se 1 (by rfl) ⟨1173698, by rfl⟩ : syracuseStep 1564931 = 2347397) B2347397
theorem B1040659 : Blo 1040609 1040659 := bstep (se 1 (by rfl) ⟨780494, by rfl⟩ : syracuseStep 1040659 = 1560989) B1560989
theorem B1564961 : Blo 1040609 1564961 := bstep (se 2 (by rfl) ⟨586860, by rfl⟩ : syracuseStep 1564961 = 1173721) B1173721
theorem B1040675 : Blo 1040609 1040675 := bstep (se 1 (by rfl) ⟨780506, by rfl⟩ : syracuseStep 1040675 = 1561013) B1561013
theorem B1040691 : Blo 1040609 1040691 := bstep (se 1 (by rfl) ⟨780518, by rfl⟩ : syracuseStep 1040691 = 1561037) B1561037
theorem B1564979 : Blo 1040609 1564979 := bstep (se 1 (by rfl) ⟨1173734, by rfl⟩ : syracuseStep 1564979 = 2347469) B2347469
theorem B1040707 : Blo 1040609 1040707 := bstep (se 1 (by rfl) ⟨780530, by rfl⟩ : syracuseStep 1040707 = 1561061) B1561061
theorem B1761601 : Blo 1040609 1761601 := bstep (se 2 (by rfl) ⟨660600, by rfl⟩ : syracuseStep 1761601 = 1321201) B1321201
theorem B1565009 : Blo 1040609 1565009 := bstep (se 2 (by rfl) ⟨586878, by rfl⟩ : syracuseStep 1565009 = 1173757) B1173757
theorem B1040723 : Blo 1040609 1040723 := bstep (se 1 (by rfl) ⟨780542, by rfl⟩ : syracuseStep 1040723 = 1561085) B1561085
theorem B1171795 : Blo 1040609 1171795 := bstep (se 1 (by rfl) ⟨878846, by rfl⟩ : syracuseStep 1171795 = 1757693) B1757693
theorem B1040739 : Blo 1040609 1040739 := bstep (se 1 (by rfl) ⟨780554, by rfl⟩ : syracuseStep 1040739 = 1561109) B1561109
theorem B1565027 : Blo 1040609 1565027 := bstep (se 1 (by rfl) ⟨1173770, by rfl⟩ : syracuseStep 1565027 = 2347541) B2347541
theorem B1761635 : Blo 1040609 1761635 := bstep (se 1 (by rfl) ⟨1321226, by rfl⟩ : syracuseStep 1761635 = 2642453) B2642453
theorem B1040755 : Blo 1040609 1040755 := bstep (se 1 (by rfl) ⟨780566, by rfl⟩ : syracuseStep 1040755 = 1561133) B1561133
theorem B1565057 : Blo 1040609 1565057 := bstep (se 2 (by rfl) ⟨586896, by rfl⟩ : syracuseStep 1565057 = 1173793) B1173793
theorem B1040771 : Blo 1040609 1040771 := bstep (se 1 (by rfl) ⟨780578, by rfl⟩ : syracuseStep 1040771 = 1561157) B1561157
theorem B3957133 : Blo 1040609 3957133 := bstep (se 3 (by rfl) ⟨741962, by rfl⟩ : syracuseStep 3957133 = 1483925) B1483925
theorem B1040787 : Blo 1040609 1040787 := bstep (se 1 (by rfl) ⟨780590, by rfl⟩ : syracuseStep 1040787 = 1561181) B1561181
theorem B1565075 : Blo 1040609 1565075 := bstep (se 1 (by rfl) ⟨1173806, by rfl⟩ : syracuseStep 1565075 = 2347613) B2347613
theorem B1040803 : Blo 1040609 1040803 := bstep (se 1 (by rfl) ⟨780602, by rfl⟩ : syracuseStep 1040803 = 1561205) B1561205
theorem B3563939 : Blo 1040609 3563939 := bstep (se 1 (by rfl) ⟨2672954, by rfl⟩ : syracuseStep 3563939 = 5345909) B5345909
theorem B1565105 : Blo 1040609 1565105 := bstep (se 2 (by rfl) ⟨586914, by rfl⟩ : syracuseStep 1565105 = 1173829) B1173829
theorem B1040819 : Blo 1040609 1040819 := bstep (se 1 (by rfl) ⟨780614, by rfl⟩ : syracuseStep 1040819 = 1561229) B1561229
theorem B1040835 : Blo 1040609 1040835 := bstep (se 1 (by rfl) ⟨780626, by rfl⟩ : syracuseStep 1040835 = 1561253) B1561253
theorem B1565123 : Blo 1040609 1565123 := bstep (se 1 (by rfl) ⟨1173842, by rfl⟩ : syracuseStep 1565123 = 2347685) B2347685
theorem B1040851 : Blo 1040609 1040851 := bstep (se 1 (by rfl) ⟨780638, by rfl⟩ : syracuseStep 1040851 = 1561277) B1561277
theorem B1565153 : Blo 1040609 1565153 := bstep (se 2 (by rfl) ⟨586932, by rfl⟩ : syracuseStep 1565153 = 1173865) B1173865
theorem B1040867 : Blo 1040609 1040867 := bstep (se 1 (by rfl) ⟨780650, by rfl⟩ : syracuseStep 1040867 = 1561301) B1561301
theorem B1171939 : Blo 1040609 1171939 := bstep (se 1 (by rfl) ⟨878954, by rfl⟩ : syracuseStep 1171939 = 1757909) B1757909
theorem B1761763 : Blo 1040609 1761763 := bstep (se 1 (by rfl) ⟨1321322, by rfl⟩ : syracuseStep 1761763 = 2642645) B2642645
theorem B4448753 : Blo 1040609 4448753 := bstep (se 2 (by rfl) ⟨1668282, by rfl⟩ : syracuseStep 4448753 = 3336565) B3336565
theorem B1040883 : Blo 1040609 1040883 := bstep (se 1 (by rfl) ⟨780662, by rfl⟩ : syracuseStep 1040883 = 1561325) B1561325
theorem B1565171 : Blo 1040609 1565171 := bstep (se 1 (by rfl) ⟨1173878, by rfl⟩ : syracuseStep 1565171 = 2347757) B2347757
theorem B1040899 : Blo 1040609 1040899 := bstep (se 1 (by rfl) ⟨780674, by rfl⟩ : syracuseStep 1040899 = 1561349) B1561349
theorem B1565201 : Blo 1040609 1565201 := bstep (se 2 (by rfl) ⟨586950, by rfl⟩ : syracuseStep 1565201 = 1173901) B1173901
theorem B1040915 : Blo 1040609 1040915 := bstep (se 1 (by rfl) ⟨780686, by rfl⟩ : syracuseStep 1040915 = 1561373) B1561373
theorem B1040931 : Blo 1040609 1040931 := bstep (se 1 (by rfl) ⟨780698, by rfl⟩ : syracuseStep 1040931 = 1561397) B1561397
theorem B4448803 : Blo 1040609 4448803 := bstep (se 1 (by rfl) ⟨3336602, by rfl⟩ : syracuseStep 4448803 = 6673205) B6673205
theorem B1565219 : Blo 1040609 1565219 := bstep (se 1 (by rfl) ⟨1173914, by rfl⟩ : syracuseStep 1565219 = 2347829) B2347829
theorem B1040947 : Blo 1040609 1040947 := bstep (se 1 (by rfl) ⟨780710, by rfl⟩ : syracuseStep 1040947 = 1561421) B1561421
theorem B1565249 : Blo 1040609 1565249 := bstep (se 2 (by rfl) ⟨586968, by rfl⟩ : syracuseStep 1565249 = 1173937) B1173937
theorem B1040963 : Blo 1040609 1040963 := bstep (se 1 (by rfl) ⟨780722, by rfl⟩ : syracuseStep 1040963 = 1561445) B1561445
theorem B1040979 : Blo 1040609 1040979 := bstep (se 1 (by rfl) ⟨780734, by rfl⟩ : syracuseStep 1040979 = 1561469) B1561469
theorem B1565267 : Blo 1040609 1565267 := bstep (se 1 (by rfl) ⟨1173950, by rfl⟩ : syracuseStep 1565267 = 2347901) B2347901
theorem B1040995 : Blo 1040609 1040995 := bstep (se 1 (by rfl) ⟨780746, by rfl⟩ : syracuseStep 1040995 = 1561493) B1561493
theorem B1565297 : Blo 1040609 1565297 := bstep (se 2 (by rfl) ⟨586986, by rfl⟩ : syracuseStep 1565297 = 1173973) B1173973
theorem B1761905 : Blo 1040609 1761905 := bstep (se 2 (by rfl) ⟨660714, by rfl⟩ : syracuseStep 1761905 = 1321429) B1321429
theorem B1041011 : Blo 1040609 1041011 := bstep (se 1 (by rfl) ⟨780758, by rfl⟩ : syracuseStep 1041011 = 1561517) B1561517
theorem B1172083 : Blo 1040609 1172083 := bstep (se 1 (by rfl) ⟨879062, by rfl⟩ : syracuseStep 1172083 = 1758125) B1758125
theorem B1041027 : Blo 1040609 1041027 := bstep (se 1 (by rfl) ⟨780770, by rfl⟩ : syracuseStep 1041027 = 1561541) B1561541
theorem B1565315 : Blo 1040609 1565315 := bstep (se 1 (by rfl) ⟨1173986, by rfl⟩ : syracuseStep 1565315 = 2347973) B2347973
theorem B1041043 : Blo 1040609 1041043 := bstep (se 1 (by rfl) ⟨780782, by rfl⟩ : syracuseStep 1041043 = 1561565) B1561565
theorem B1565345 : Blo 1040609 1565345 := bstep (se 2 (by rfl) ⟨587004, by rfl⟩ : syracuseStep 1565345 = 1174009) B1174009
theorem B1041059 : Blo 1040609 1041059 := bstep (se 1 (by rfl) ⟨780794, by rfl⟩ : syracuseStep 1041059 = 1561589) B1561589
theorem B1041075 : Blo 1040609 1041075 := bstep (se 1 (by rfl) ⟨780806, by rfl⟩ : syracuseStep 1041075 = 1561613) B1561613
theorem B1565363 : Blo 1040609 1565363 := bstep (se 1 (by rfl) ⟨1174022, by rfl⟩ : syracuseStep 1565363 = 2348045) B2348045
theorem B1041091 : Blo 1040609 1041091 := bstep (se 1 (by rfl) ⟨780818, by rfl⟩ : syracuseStep 1041091 = 1561637) B1561637
theorem B1565393 : Blo 1040609 1565393 := bstep (se 2 (by rfl) ⟨587022, by rfl⟩ : syracuseStep 1565393 = 1174045) B1174045
theorem B1041107 : Blo 1040609 1041107 := bstep (se 1 (by rfl) ⟨780830, by rfl⟩ : syracuseStep 1041107 = 1561661) B1561661
theorem B1041123 : Blo 1040609 1041123 := bstep (se 1 (by rfl) ⟨780842, by rfl⟩ : syracuseStep 1041123 = 1561685) B1561685
theorem B1565411 : Blo 1040609 1565411 := bstep (se 1 (by rfl) ⟨1174058, by rfl⟩ : syracuseStep 1565411 = 2348117) B2348117
theorem B1762033 : Blo 1040609 1762033 := bstep (se 2 (by rfl) ⟨660762, by rfl⟩ : syracuseStep 1762033 = 1321525) B1321525
theorem B1041139 : Blo 1040609 1041139 := bstep (se 1 (by rfl) ⟨780854, by rfl⟩ : syracuseStep 1041139 = 1561709) B1561709
theorem B1565441 : Blo 1040609 1565441 := bstep (se 2 (by rfl) ⟨587040, by rfl⟩ : syracuseStep 1565441 = 1174081) B1174081
theorem B1041155 : Blo 1040609 1041155 := bstep (se 1 (by rfl) ⟨780866, by rfl⟩ : syracuseStep 1041155 = 1561733) B1561733
theorem B1172227 : Blo 1040609 1172227 := bstep (se 1 (by rfl) ⟨879170, by rfl⟩ : syracuseStep 1172227 = 1758341) B1758341
theorem B3334925 : Blo 1040609 3334925 := bstep (se 3 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 3334925 = 1250597) B1250597
theorem B1041171 : Blo 1040609 1041171 := bstep (se 1 (by rfl) ⟨780878, by rfl⟩ : syracuseStep 1041171 = 1561757) B1561757
theorem B1565459 : Blo 1040609 1565459 := bstep (se 1 (by rfl) ⟨1174094, by rfl⟩ : syracuseStep 1565459 = 2348189) B2348189
theorem B1762067 : Blo 1040609 1762067 := bstep (se 1 (by rfl) ⟨1321550, by rfl⟩ : syracuseStep 1762067 = 2643101) B2643101
theorem B1041187 : Blo 1040609 1041187 := bstep (se 1 (by rfl) ⟨780890, by rfl⟩ : syracuseStep 1041187 = 1561781) B1561781
theorem B1565489 : Blo 1040609 1565489 := bstep (se 2 (by rfl) ⟨587058, by rfl⟩ : syracuseStep 1565489 = 1174117) B1174117
theorem B1041203 : Blo 1040609 1041203 := bstep (se 1 (by rfl) ⟨780902, by rfl⟩ : syracuseStep 1041203 = 1561805) B1561805
theorem B1041219 : Blo 1040609 1041219 := bstep (se 1 (by rfl) ⟨780914, by rfl⟩ : syracuseStep 1041219 = 1561829) B1561829
theorem B1565507 : Blo 1040609 1565507 := bstep (se 1 (by rfl) ⟨1174130, by rfl⟩ : syracuseStep 1565507 = 2348261) B2348261
theorem B1041235 : Blo 1040609 1041235 := bstep (se 1 (by rfl) ⟨780926, by rfl⟩ : syracuseStep 1041235 = 1561853) B1561853
theorem B1565537 : Blo 1040609 1565537 := bstep (se 2 (by rfl) ⟨587076, by rfl⟩ : syracuseStep 1565537 = 1174153) B1174153
theorem B1041251 : Blo 1040609 1041251 := bstep (se 1 (by rfl) ⟨780938, by rfl⟩ : syracuseStep 1041251 = 1561877) B1561877
theorem B1041267 : Blo 1040609 1041267 := bstep (se 1 (by rfl) ⟨780950, by rfl⟩ : syracuseStep 1041267 = 1561901) B1561901
theorem B1565555 : Blo 1040609 1565555 := bstep (se 1 (by rfl) ⟨1174166, by rfl⟩ : syracuseStep 1565555 = 2348333) B2348333
theorem B1041283 : Blo 1040609 1041283 := bstep (se 1 (by rfl) ⟨780962, by rfl⟩ : syracuseStep 1041283 = 1561925) B1561925
theorem B1565585 : Blo 1040609 1565585 := bstep (se 2 (by rfl) ⟨587094, by rfl⟩ : syracuseStep 1565585 = 1174189) B1174189
theorem B1041299 : Blo 1040609 1041299 := bstep (se 1 (by rfl) ⟨780974, by rfl⟩ : syracuseStep 1041299 = 1561949) B1561949
theorem B1172371 : Blo 1040609 1172371 := bstep (se 1 (by rfl) ⟨879278, by rfl⟩ : syracuseStep 1172371 = 1758557) B1758557
theorem B1762195 : Blo 1040609 1762195 := bstep (se 1 (by rfl) ⟨1321646, by rfl⟩ : syracuseStep 1762195 = 2643293) B2643293
theorem B1041315 : Blo 1040609 1041315 := bstep (se 1 (by rfl) ⟨780986, by rfl⟩ : syracuseStep 1041315 = 1561973) B1561973
theorem B1565603 : Blo 1040609 1565603 := bstep (se 1 (by rfl) ⟨1174202, by rfl⟩ : syracuseStep 1565603 = 2348405) B2348405
theorem B5268401 : Blo 1040609 5268401 := bstep (se 2 (by rfl) ⟨1975650, by rfl⟩ : syracuseStep 5268401 = 3951301) B3951301
theorem B1041331 : Blo 1040609 1041331 := bstep (se 1 (by rfl) ⟨780998, by rfl⟩ : syracuseStep 1041331 = 1561997) B1561997
theorem B1565633 : Blo 1040609 1565633 := bstep (se 2 (by rfl) ⟨587112, by rfl⟩ : syracuseStep 1565633 = 1174225) B1174225
theorem B1041347 : Blo 1040609 1041347 := bstep (se 1 (by rfl) ⟨781010, by rfl⟩ : syracuseStep 1041347 = 1562021) B1562021
theorem B1041363 : Blo 1040609 1041363 := bstep (se 1 (by rfl) ⟨781022, by rfl⟩ : syracuseStep 1041363 = 1562045) B1562045
theorem B1565651 : Blo 1040609 1565651 := bstep (se 1 (by rfl) ⟨1174238, by rfl⟩ : syracuseStep 1565651 = 2348477) B2348477
theorem B1041379 : Blo 1040609 1041379 := bstep (se 1 (by rfl) ⟨781034, by rfl⟩ : syracuseStep 1041379 = 1562069) B1562069
theorem B1565681 : Blo 1040609 1565681 := bstep (se 2 (by rfl) ⟨587130, by rfl⟩ : syracuseStep 1565681 = 1174261) B1174261
theorem B1041395 : Blo 1040609 1041395 := bstep (se 1 (by rfl) ⟨781046, by rfl⟩ : syracuseStep 1041395 = 1562093) B1562093
theorem B1041411 : Blo 1040609 1041411 := bstep (se 1 (by rfl) ⟨781058, by rfl⟩ : syracuseStep 1041411 = 1562117) B1562117
theorem B1565699 : Blo 1040609 1565699 := bstep (se 1 (by rfl) ⟨1174274, by rfl⟩ : syracuseStep 1565699 = 2348549) B2348549
theorem B1041427 : Blo 1040609 1041427 := bstep (se 1 (by rfl) ⟨781070, by rfl⟩ : syracuseStep 1041427 = 1562141) B1562141
theorem B1565729 : Blo 1040609 1565729 := bstep (se 2 (by rfl) ⟨587148, by rfl⟩ : syracuseStep 1565729 = 1174297) B1174297
theorem B1762337 : Blo 1040609 1762337 := bstep (se 2 (by rfl) ⟨660876, by rfl⟩ : syracuseStep 1762337 = 1321753) B1321753
theorem B1041443 : Blo 1040609 1041443 := bstep (se 1 (by rfl) ⟨781082, by rfl⟩ : syracuseStep 1041443 = 1562165) B1562165
theorem B1172515 : Blo 1040609 1172515 := bstep (se 1 (by rfl) ⟨879386, by rfl⟩ : syracuseStep 1172515 = 1758773) B1758773
theorem B1041459 : Blo 1040609 1041459 := bstep (se 1 (by rfl) ⟨781094, by rfl⟩ : syracuseStep 1041459 = 1562189) B1562189
theorem B1565747 : Blo 1040609 1565747 := bstep (se 1 (by rfl) ⟨1174310, by rfl⟩ : syracuseStep 1565747 = 2348621) B2348621
theorem B1041475 : Blo 1040609 1041475 := bstep (se 1 (by rfl) ⟨781106, by rfl⟩ : syracuseStep 1041475 = 1562213) B1562213
theorem B1565777 : Blo 1040609 1565777 := bstep (se 2 (by rfl) ⟨587166, by rfl⟩ : syracuseStep 1565777 = 1174333) B1174333
theorem B1041491 : Blo 1040609 1041491 := bstep (se 1 (by rfl) ⟨781118, by rfl⟩ : syracuseStep 1041491 = 1562237) B1562237
theorem B1041507 : Blo 1040609 1041507 := bstep (se 1 (by rfl) ⟨781130, by rfl⟩ : syracuseStep 1041507 = 1562261) B1562261
theorem B1565795 : Blo 1040609 1565795 := bstep (se 1 (by rfl) ⟨1174346, by rfl⟩ : syracuseStep 1565795 = 2348693) B2348693
theorem B1041523 : Blo 1040609 1041523 := bstep (se 1 (by rfl) ⟨781142, by rfl⟩ : syracuseStep 1041523 = 1562285) B1562285
theorem B1565825 : Blo 1040609 1565825 := bstep (se 2 (by rfl) ⟨587184, by rfl⟩ : syracuseStep 1565825 = 1174369) B1174369
theorem B1041539 : Blo 1040609 1041539 := bstep (se 1 (by rfl) ⟨781154, by rfl⟩ : syracuseStep 1041539 = 1562309) B1562309
theorem B1041555 : Blo 1040609 1041555 := bstep (se 1 (by rfl) ⟨781166, by rfl⟩ : syracuseStep 1041555 = 1562333) B1562333
theorem B1565843 : Blo 1040609 1565843 := bstep (se 1 (by rfl) ⟨1174382, by rfl⟩ : syracuseStep 1565843 = 2348765) B2348765
theorem B1762465 : Blo 1040609 1762465 := bstep (se 2 (by rfl) ⟨660924, by rfl⟩ : syracuseStep 1762465 = 1321849) B1321849
theorem B1041571 : Blo 1040609 1041571 := bstep (se 1 (by rfl) ⟨781178, by rfl⟩ : syracuseStep 1041571 = 1562357) B1562357
theorem B3957923 : Blo 1040609 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B1565873 : Blo 1040609 1565873 := bstep (se 2 (by rfl) ⟨587202, by rfl⟩ : syracuseStep 1565873 = 1174405) B1174405
theorem B1041587 : Blo 1040609 1041587 := bstep (se 1 (by rfl) ⟨781190, by rfl⟩ : syracuseStep 1041587 = 1562381) B1562381
theorem B1172659 : Blo 1040609 1172659 := bstep (se 1 (by rfl) ⟨879494, by rfl⟩ : syracuseStep 1172659 = 1758989) B1758989
theorem B1041603 : Blo 1040609 1041603 := bstep (se 1 (by rfl) ⟨781202, by rfl⟩ : syracuseStep 1041603 = 1562405) B1562405
theorem B1565891 : Blo 1040609 1565891 := bstep (se 1 (by rfl) ⟨1174418, by rfl⟩ : syracuseStep 1565891 = 2348837) B2348837
theorem B1762499 : Blo 1040609 1762499 := bstep (se 1 (by rfl) ⟨1321874, by rfl⟩ : syracuseStep 1762499 = 2643749) B2643749
theorem B5629133 : Blo 1040609 5629133 := bstep (se 3 (by rfl) ⟨1055462, by rfl⟩ : syracuseStep 5629133 = 2110925) B2110925
theorem B1041619 : Blo 1040609 1041619 := bstep (se 1 (by rfl) ⟨781214, by rfl⟩ : syracuseStep 1041619 = 1562429) B1562429
theorem B1565921 : Blo 1040609 1565921 := bstep (se 2 (by rfl) ⟨587220, by rfl⟩ : syracuseStep 1565921 = 1174441) B1174441
theorem B1041635 : Blo 1040609 1041635 := bstep (se 1 (by rfl) ⟨781226, by rfl⟩ : syracuseStep 1041635 = 1562453) B1562453
theorem B1041651 : Blo 1040609 1041651 := bstep (se 1 (by rfl) ⟨781238, by rfl⟩ : syracuseStep 1041651 = 1562477) B1562477
theorem B1565939 : Blo 1040609 1565939 := bstep (se 1 (by rfl) ⟨1174454, by rfl⟩ : syracuseStep 1565939 = 2348909) B2348909
theorem B1041667 : Blo 1040609 1041667 := bstep (se 1 (by rfl) ⟨781250, by rfl⟩ : syracuseStep 1041667 = 1562501) B1562501
theorem B1565969 : Blo 1040609 1565969 := bstep (se 2 (by rfl) ⟨587238, by rfl⟩ : syracuseStep 1565969 = 1174477) B1174477
theorem B1041683 : Blo 1040609 1041683 := bstep (se 1 (by rfl) ⟨781262, by rfl⟩ : syracuseStep 1041683 = 1562525) B1562525
theorem B1041699 : Blo 1040609 1041699 := bstep (se 1 (by rfl) ⟨781274, by rfl⟩ : syracuseStep 1041699 = 1562549) B1562549
theorem B1565987 : Blo 1040609 1565987 := bstep (se 1 (by rfl) ⟨1174490, by rfl⟩ : syracuseStep 1565987 = 2348981) B2348981
theorem B1041715 : Blo 1040609 1041715 := bstep (se 1 (by rfl) ⟨781286, by rfl⟩ : syracuseStep 1041715 = 1562573) B1562573
theorem B1566017 : Blo 1040609 1566017 := bstep (se 2 (by rfl) ⟨587256, by rfl⟩ : syracuseStep 1566017 = 1174513) B1174513
theorem B1041731 : Blo 1040609 1041731 := bstep (se 1 (by rfl) ⟨781298, by rfl⟩ : syracuseStep 1041731 = 1562597) B1562597
theorem B1172803 : Blo 1040609 1172803 := bstep (se 1 (by rfl) ⟨879602, by rfl⟩ : syracuseStep 1172803 = 1759205) B1759205
theorem B1762627 : Blo 1040609 1762627 := bstep (se 1 (by rfl) ⟨1321970, by rfl⟩ : syracuseStep 1762627 = 2643941) B2643941
theorem B1041747 : Blo 1040609 1041747 := bstep (se 1 (by rfl) ⟨781310, by rfl⟩ : syracuseStep 1041747 = 1562621) B1562621
theorem B1566035 : Blo 1040609 1566035 := bstep (se 1 (by rfl) ⟨1174526, by rfl⟩ : syracuseStep 1566035 = 2349053) B2349053
theorem B1041763 : Blo 1040609 1041763 := bstep (se 1 (by rfl) ⟨781322, by rfl⟩ : syracuseStep 1041763 = 1562645) B1562645
theorem B1566065 : Blo 1040609 1566065 := bstep (se 2 (by rfl) ⟨587274, by rfl⟩ : syracuseStep 1566065 = 1174549) B1174549
theorem B1041779 : Blo 1040609 1041779 := bstep (se 1 (by rfl) ⟨781334, by rfl⟩ : syracuseStep 1041779 = 1562669) B1562669
theorem B1041795 : Blo 1040609 1041795 := bstep (se 1 (by rfl) ⟨781346, by rfl⟩ : syracuseStep 1041795 = 1562693) B1562693
theorem B1566083 : Blo 1040609 1566083 := bstep (se 1 (by rfl) ⟨1174562, by rfl⟩ : syracuseStep 1566083 = 2349125) B2349125
theorem B1041811 : Blo 1040609 1041811 := bstep (se 1 (by rfl) ⟨781358, by rfl⟩ : syracuseStep 1041811 = 1562717) B1562717
theorem B1566113 : Blo 1040609 1566113 := bstep (se 2 (by rfl) ⟨587292, by rfl⟩ : syracuseStep 1566113 = 1174585) B1174585
theorem B1041827 : Blo 1040609 1041827 := bstep (se 1 (by rfl) ⟨781370, by rfl⟩ : syracuseStep 1041827 = 1562741) B1562741
theorem B1041843 : Blo 1040609 1041843 := bstep (se 1 (by rfl) ⟨781382, by rfl⟩ : syracuseStep 1041843 = 1562765) B1562765
theorem B1566131 : Blo 1040609 1566131 := bstep (se 1 (by rfl) ⟨1174598, by rfl⟩ : syracuseStep 1566131 = 2349197) B2349197
theorem B1041859 : Blo 1040609 1041859 := bstep (se 1 (by rfl) ⟨781394, by rfl⟩ : syracuseStep 1041859 = 1562789) B1562789
theorem B1566161 : Blo 1040609 1566161 := bstep (se 2 (by rfl) ⟨587310, by rfl⟩ : syracuseStep 1566161 = 1174621) B1174621
theorem B1762769 : Blo 1040609 1762769 := bstep (se 2 (by rfl) ⟨661038, by rfl⟩ : syracuseStep 1762769 = 1322077) B1322077
theorem B1041875 : Blo 1040609 1041875 := bstep (se 1 (by rfl) ⟨781406, by rfl⟩ : syracuseStep 1041875 = 1562813) B1562813
theorem B1172947 : Blo 1040609 1172947 := bstep (se 1 (by rfl) ⟨879710, by rfl⟩ : syracuseStep 1172947 = 1759421) B1759421
theorem B1041891 : Blo 1040609 1041891 := bstep (se 1 (by rfl) ⟨781418, by rfl⟩ : syracuseStep 1041891 = 1562837) B1562837
theorem B1566179 : Blo 1040609 1566179 := bstep (se 1 (by rfl) ⟨1174634, by rfl⟩ : syracuseStep 1566179 = 2349269) B2349269
theorem B1041907 : Blo 1040609 1041907 := bstep (se 1 (by rfl) ⟨781430, by rfl⟩ : syracuseStep 1041907 = 1562861) B1562861
theorem B1566209 : Blo 1040609 1566209 := bstep (se 2 (by rfl) ⟨587328, by rfl⟩ : syracuseStep 1566209 = 1174657) B1174657
theorem B1041923 : Blo 1040609 1041923 := bstep (se 1 (by rfl) ⟨781442, by rfl⟩ : syracuseStep 1041923 = 1562885) B1562885
theorem B1041939 : Blo 1040609 1041939 := bstep (se 1 (by rfl) ⟨781454, by rfl⟩ : syracuseStep 1041939 = 1562909) B1562909
theorem B1566227 : Blo 1040609 1566227 := bstep (se 1 (by rfl) ⟨1174670, by rfl⟩ : syracuseStep 1566227 = 2349341) B2349341
theorem B1041955 : Blo 1040609 1041955 := bstep (se 1 (by rfl) ⟨781466, by rfl⟩ : syracuseStep 1041955 = 1562933) B1562933
theorem B1566257 : Blo 1040609 1566257 := bstep (se 2 (by rfl) ⟨587346, by rfl⟩ : syracuseStep 1566257 = 1174693) B1174693
theorem B1041971 : Blo 1040609 1041971 := bstep (se 1 (by rfl) ⟨781478, by rfl⟩ : syracuseStep 1041971 = 1562957) B1562957
theorem B1041987 : Blo 1040609 1041987 := bstep (se 1 (by rfl) ⟨781490, by rfl⟩ : syracuseStep 1041987 = 1562981) B1562981
theorem B1566275 : Blo 1040609 1566275 := bstep (se 1 (by rfl) ⟨1174706, by rfl⟩ : syracuseStep 1566275 = 2349413) B2349413
theorem B1042003 : Blo 1040609 1042003 := bstep (se 1 (by rfl) ⟨781502, by rfl⟩ : syracuseStep 1042003 = 1563005) B1563005
theorem B1566305 : Blo 1040609 1566305 := bstep (se 2 (by rfl) ⟨587364, by rfl⟩ : syracuseStep 1566305 = 1174729) B1174729
theorem B1042019 : Blo 1040609 1042019 := bstep (se 1 (by rfl) ⟨781514, by rfl⟩ : syracuseStep 1042019 = 1563029) B1563029
theorem B1173091 : Blo 1040609 1173091 := bstep (se 1 (by rfl) ⟨879818, by rfl⟩ : syracuseStep 1173091 = 1759637) B1759637
theorem B1042035 : Blo 1040609 1042035 := bstep (se 1 (by rfl) ⟨781526, by rfl⟩ : syracuseStep 1042035 = 1563053) B1563053
theorem B1566323 : Blo 1040609 1566323 := bstep (se 1 (by rfl) ⟨1174742, by rfl⟩ : syracuseStep 1566323 = 2349485) B2349485
theorem B1042051 : Blo 1040609 1042051 := bstep (se 1 (by rfl) ⟨781538, by rfl⟩ : syracuseStep 1042051 = 1563077) B1563077
theorem B1566353 : Blo 1040609 1566353 := bstep (se 2 (by rfl) ⟨587382, by rfl⟩ : syracuseStep 1566353 = 1174765) B1174765
theorem B1042067 : Blo 1040609 1042067 := bstep (se 1 (by rfl) ⟨781550, by rfl⟩ : syracuseStep 1042067 = 1563101) B1563101
theorem B1042083 : Blo 1040609 1042083 := bstep (se 1 (by rfl) ⟨781562, by rfl⟩ : syracuseStep 1042083 = 1563125) B1563125
theorem B1566371 : Blo 1040609 1566371 := bstep (se 1 (by rfl) ⟨1174778, by rfl⟩ : syracuseStep 1566371 = 2349557) B2349557
theorem B1042099 : Blo 1040609 1042099 := bstep (se 1 (by rfl) ⟨781574, by rfl⟩ : syracuseStep 1042099 = 1563149) B1563149
theorem B1566401 : Blo 1040609 1566401 := bstep (se 2 (by rfl) ⟨587400, by rfl⟩ : syracuseStep 1566401 = 1174801) B1174801
theorem B1042115 : Blo 1040609 1042115 := bstep (se 1 (by rfl) ⟨781586, by rfl⟩ : syracuseStep 1042115 = 1563173) B1563173
theorem B1042131 : Blo 1040609 1042131 := bstep (se 1 (by rfl) ⟨781598, by rfl⟩ : syracuseStep 1042131 = 1563197) B1563197
theorem B1566419 : Blo 1040609 1566419 := bstep (se 1 (by rfl) ⟨1174814, by rfl⟩ : syracuseStep 1566419 = 2349629) B2349629
theorem B1042147 : Blo 1040609 1042147 := bstep (se 1 (by rfl) ⟨781610, by rfl⟩ : syracuseStep 1042147 = 1563221) B1563221
theorem B1566449 : Blo 1040609 1566449 := bstep (se 2 (by rfl) ⟨587418, by rfl⟩ : syracuseStep 1566449 = 1174837) B1174837
theorem B1042163 : Blo 1040609 1042163 := bstep (se 1 (by rfl) ⟨781622, by rfl⟩ : syracuseStep 1042163 = 1563245) B1563245
theorem B1173235 : Blo 1040609 1173235 := bstep (se 1 (by rfl) ⟨879926, by rfl⟩ : syracuseStep 1173235 = 1759853) B1759853
theorem B1042179 : Blo 1040609 1042179 := bstep (se 1 (by rfl) ⟨781634, by rfl⟩ : syracuseStep 1042179 = 1563269) B1563269
theorem B1566467 : Blo 1040609 1566467 := bstep (se 1 (by rfl) ⟨1174850, by rfl⟩ : syracuseStep 1566467 = 2349701) B2349701
theorem B1042195 : Blo 1040609 1042195 := bstep (se 1 (by rfl) ⟨781646, by rfl⟩ : syracuseStep 1042195 = 1563293) B1563293
theorem B1566497 : Blo 1040609 1566497 := bstep (se 2 (by rfl) ⟨587436, by rfl⟩ : syracuseStep 1566497 = 1174873) B1174873
theorem B1042211 : Blo 1040609 1042211 := bstep (se 1 (by rfl) ⟨781658, by rfl⟩ : syracuseStep 1042211 = 1563317) B1563317
theorem B3958577 : Blo 1040609 3958577 := bstep (se 2 (by rfl) ⟨1484466, by rfl⟩ : syracuseStep 3958577 = 2968933) B2968933
theorem B1042227 : Blo 1040609 1042227 := bstep (se 1 (by rfl) ⟨781670, by rfl⟩ : syracuseStep 1042227 = 1563341) B1563341
theorem B1566515 : Blo 1040609 1566515 := bstep (se 1 (by rfl) ⟨1174886, by rfl⟩ : syracuseStep 1566515 = 2349773) B2349773
theorem B1042243 : Blo 1040609 1042243 := bstep (se 1 (by rfl) ⟨781682, by rfl⟩ : syracuseStep 1042243 = 1563365) B1563365
theorem B3008333 : Blo 1040609 3008333 := bstep (se 3 (by rfl) ⟨564062, by rfl⟩ : syracuseStep 3008333 = 1128125) B1128125
theorem B1566545 : Blo 1040609 1566545 := bstep (se 2 (by rfl) ⟨587454, by rfl⟩ : syracuseStep 1566545 = 1174909) B1174909
theorem B1042259 : Blo 1040609 1042259 := bstep (se 1 (by rfl) ⟨781694, by rfl⟩ : syracuseStep 1042259 = 1563389) B1563389
theorem B1042275 : Blo 1040609 1042275 := bstep (se 1 (by rfl) ⟨781706, by rfl⟩ : syracuseStep 1042275 = 1563413) B1563413
theorem B1566563 : Blo 1040609 1566563 := bstep (se 1 (by rfl) ⟨1174922, by rfl⟩ : syracuseStep 1566563 = 2349845) B2349845
theorem B1042291 : Blo 1040609 1042291 := bstep (se 1 (by rfl) ⟨781718, by rfl⟩ : syracuseStep 1042291 = 1563437) B1563437
theorem B1566593 : Blo 1040609 1566593 := bstep (se 2 (by rfl) ⟨587472, by rfl⟩ : syracuseStep 1566593 = 1174945) B1174945
theorem B1042307 : Blo 1040609 1042307 := bstep (se 1 (by rfl) ⟨781730, by rfl⟩ : syracuseStep 1042307 = 1563461) B1563461
theorem B1173379 : Blo 1040609 1173379 := bstep (se 1 (by rfl) ⟨880034, by rfl⟩ : syracuseStep 1173379 = 1760069) B1760069
theorem B1042323 : Blo 1040609 1042323 := bstep (se 1 (by rfl) ⟨781742, by rfl⟩ : syracuseStep 1042323 = 1563485) B1563485
theorem B1566611 : Blo 1040609 1566611 := bstep (se 1 (by rfl) ⟨1174958, by rfl⟩ : syracuseStep 1566611 = 2349917) B2349917
theorem B1042339 : Blo 1040609 1042339 := bstep (se 1 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 1042339 = 1563509) B1563509
theorem B1566641 : Blo 1040609 1566641 := bstep (se 2 (by rfl) ⟨587490, by rfl⟩ : syracuseStep 1566641 = 1174981) B1174981
theorem B1042355 : Blo 1040609 1042355 := bstep (se 1 (by rfl) ⟨781766, by rfl⟩ : syracuseStep 1042355 = 1563533) B1563533
theorem B1042371 : Blo 1040609 1042371 := bstep (se 1 (by rfl) ⟨781778, by rfl⟩ : syracuseStep 1042371 = 1563557) B1563557
theorem B1566659 : Blo 1040609 1566659 := bstep (se 1 (by rfl) ⟨1174994, by rfl⟩ : syracuseStep 1566659 = 2349989) B2349989
theorem B1042387 : Blo 1040609 1042387 := bstep (se 1 (by rfl) ⟨781790, by rfl⟩ : syracuseStep 1042387 = 1563581) B1563581
theorem B1566689 : Blo 1040609 1566689 := bstep (se 2 (by rfl) ⟨587508, by rfl⟩ : syracuseStep 1566689 = 1175017) B1175017
theorem B1042403 : Blo 1040609 1042403 := bstep (se 1 (by rfl) ⟨781802, by rfl⟩ : syracuseStep 1042403 = 1563605) B1563605
theorem B1042419 : Blo 1040609 1042419 := bstep (se 1 (by rfl) ⟨781814, by rfl⟩ : syracuseStep 1042419 = 1563629) B1563629
theorem B1566707 : Blo 1040609 1566707 := bstep (se 1 (by rfl) ⟨1175030, by rfl⟩ : syracuseStep 1566707 = 2350061) B2350061
theorem B1042435 : Blo 1040609 1042435 := bstep (se 1 (by rfl) ⟨781826, by rfl⟩ : syracuseStep 1042435 = 1563653) B1563653
theorem B1566737 : Blo 1040609 1566737 := bstep (se 2 (by rfl) ⟨587526, by rfl⟩ : syracuseStep 1566737 = 1175053) B1175053
theorem B1042451 : Blo 1040609 1042451 := bstep (se 1 (by rfl) ⟨781838, by rfl⟩ : syracuseStep 1042451 = 1563677) B1563677
theorem B1173523 : Blo 1040609 1173523 := bstep (se 1 (by rfl) ⟨880142, by rfl⟩ : syracuseStep 1173523 = 1760285) B1760285
theorem B1042467 : Blo 1040609 1042467 := bstep (se 1 (by rfl) ⟨781850, by rfl⟩ : syracuseStep 1042467 = 1563701) B1563701
theorem B1566755 : Blo 1040609 1566755 := bstep (se 1 (by rfl) ⟨1175066, by rfl⟩ : syracuseStep 1566755 = 2350133) B2350133
theorem B1042483 : Blo 1040609 1042483 := bstep (se 1 (by rfl) ⟨781862, by rfl⟩ : syracuseStep 1042483 = 1563725) B1563725
theorem B1566785 : Blo 1040609 1566785 := bstep (se 2 (by rfl) ⟨587544, by rfl⟩ : syracuseStep 1566785 = 1175089) B1175089
theorem B1042499 : Blo 1040609 1042499 := bstep (se 1 (by rfl) ⟨781874, by rfl⟩ : syracuseStep 1042499 = 1563749) B1563749
theorem B1042515 : Blo 1040609 1042515 := bstep (se 1 (by rfl) ⟨781886, by rfl⟩ : syracuseStep 1042515 = 1563773) B1563773
theorem B1566803 : Blo 1040609 1566803 := bstep (se 1 (by rfl) ⟨1175102, by rfl⟩ : syracuseStep 1566803 = 2350205) B2350205
theorem B1042531 : Blo 1040609 1042531 := bstep (se 1 (by rfl) ⟨781898, by rfl⟩ : syracuseStep 1042531 = 1563797) B1563797
theorem B1566833 : Blo 1040609 1566833 := bstep (se 2 (by rfl) ⟨587562, by rfl⟩ : syracuseStep 1566833 = 1175125) B1175125
theorem B1042547 : Blo 1040609 1042547 := bstep (se 1 (by rfl) ⟨781910, by rfl⟩ : syracuseStep 1042547 = 1563821) B1563821
theorem B1042563 : Blo 1040609 1042563 := bstep (se 1 (by rfl) ⟨781922, by rfl⟩ : syracuseStep 1042563 = 1563845) B1563845
theorem B1566851 : Blo 1040609 1566851 := bstep (se 1 (by rfl) ⟨1175138, by rfl⟩ : syracuseStep 1566851 = 2350277) B2350277
theorem B1042579 : Blo 1040609 1042579 := bstep (se 1 (by rfl) ⟨781934, by rfl⟩ : syracuseStep 1042579 = 1563869) B1563869
theorem B1566881 : Blo 1040609 1566881 := bstep (se 2 (by rfl) ⟨587580, by rfl⟩ : syracuseStep 1566881 = 1175161) B1175161
theorem B1042595 : Blo 1040609 1042595 := bstep (se 1 (by rfl) ⟨781946, by rfl⟩ : syracuseStep 1042595 = 1563893) B1563893
theorem B1173667 : Blo 1040609 1173667 := bstep (se 1 (by rfl) ⟨880250, by rfl⟩ : syracuseStep 1173667 = 1760501) B1760501
theorem B1042611 : Blo 1040609 1042611 := bstep (se 1 (by rfl) ⟨781958, by rfl⟩ : syracuseStep 1042611 = 1563917) B1563917
theorem B1566899 : Blo 1040609 1566899 := bstep (se 1 (by rfl) ⟨1175174, by rfl⟩ : syracuseStep 1566899 = 2350349) B2350349
theorem B1042627 : Blo 1040609 1042627 := bstep (se 1 (by rfl) ⟨781970, by rfl⟩ : syracuseStep 1042627 = 1563941) B1563941
theorem B1042643 : Blo 1040609 1042643 := bstep (se 1 (by rfl) ⟨781982, by rfl⟩ : syracuseStep 1042643 = 1563965) B1563965
theorem B1042659 : Blo 1040609 1042659 := bstep (se 1 (by rfl) ⟨781994, by rfl⟩ : syracuseStep 1042659 = 1563989) B1563989
theorem B1042675 : Blo 1040609 1042675 := bstep (se 1 (by rfl) ⟨782006, by rfl⟩ : syracuseStep 1042675 = 1564013) B1564013
theorem B1042691 : Blo 1040609 1042691 := bstep (se 1 (by rfl) ⟨782018, by rfl⟩ : syracuseStep 1042691 = 1564037) B1564037
theorem B1042707 : Blo 1040609 1042707 := bstep (se 1 (by rfl) ⟨782030, by rfl⟩ : syracuseStep 1042707 = 1564061) B1564061
theorem B1042723 : Blo 1040609 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B1042739 : Blo 1040609 1042739 := bstep (se 1 (by rfl) ⟨782054, by rfl⟩ : syracuseStep 1042739 = 1564109) B1564109
theorem B1173811 : Blo 1040609 1173811 := bstep (se 1 (by rfl) ⟨880358, by rfl⟩ : syracuseStep 1173811 = 1760717) B1760717
theorem B1042755 : Blo 1040609 1042755 := bstep (se 1 (by rfl) ⟨782066, by rfl⟩ : syracuseStep 1042755 = 1564133) B1564133
theorem B1042771 : Blo 1040609 1042771 := bstep (se 1 (by rfl) ⟨782078, by rfl⟩ : syracuseStep 1042771 = 1564157) B1564157
theorem B5269859 : Blo 1040609 5269859 := bstep (se 1 (by rfl) ⟨3952394, by rfl⟩ : syracuseStep 5269859 = 7904789) B7904789
theorem B1042787 : Blo 1040609 1042787 := bstep (se 1 (by rfl) ⟨782090, by rfl⟩ : syracuseStep 1042787 = 1564181) B1564181
theorem B1042803 : Blo 1040609 1042803 := bstep (se 1 (by rfl) ⟨782102, by rfl⟩ : syracuseStep 1042803 = 1564205) B1564205
theorem B1042819 : Blo 1040609 1042819 := bstep (se 1 (by rfl) ⟨782114, by rfl⟩ : syracuseStep 1042819 = 1564229) B1564229
theorem B1042835 : Blo 1040609 1042835 := bstep (se 1 (by rfl) ⟨782126, by rfl⟩ : syracuseStep 1042835 = 1564253) B1564253
theorem B1042851 : Blo 1040609 1042851 := bstep (se 1 (by rfl) ⟨782138, by rfl⟩ : syracuseStep 1042851 = 1564277) B1564277
theorem B1042867 : Blo 1040609 1042867 := bstep (se 1 (by rfl) ⟨782150, by rfl⟩ : syracuseStep 1042867 = 1564301) B1564301
theorem B1042883 : Blo 1040609 1042883 := bstep (se 1 (by rfl) ⟨782162, by rfl⟩ : syracuseStep 1042883 = 1564325) B1564325
theorem B1173955 : Blo 1040609 1173955 := bstep (se 1 (by rfl) ⟨880466, by rfl⟩ : syracuseStep 1173955 = 1760933) B1760933
theorem B1042899 : Blo 1040609 1042899 := bstep (se 1 (by rfl) ⟨782174, by rfl⟩ : syracuseStep 1042899 = 1564349) B1564349
theorem B1042915 : Blo 1040609 1042915 := bstep (se 1 (by rfl) ⟨782186, by rfl⟩ : syracuseStep 1042915 = 1564373) B1564373
theorem B1042931 : Blo 1040609 1042931 := bstep (se 1 (by rfl) ⟨782198, by rfl⟩ : syracuseStep 1042931 = 1564397) B1564397
theorem B1042947 : Blo 1040609 1042947 := bstep (se 1 (by rfl) ⟨782210, by rfl⟩ : syracuseStep 1042947 = 1564421) B1564421
theorem B1042963 : Blo 1040609 1042963 := bstep (se 1 (by rfl) ⟨782222, by rfl⟩ : syracuseStep 1042963 = 1564445) B1564445
theorem B1042979 : Blo 1040609 1042979 := bstep (se 1 (by rfl) ⟨782234, by rfl⟩ : syracuseStep 1042979 = 1564469) B1564469
theorem B1042995 : Blo 1040609 1042995 := bstep (se 1 (by rfl) ⟨782246, by rfl⟩ : syracuseStep 1042995 = 1564493) B1564493
theorem B1043011 : Blo 1040609 1043011 := bstep (se 1 (by rfl) ⟨782258, by rfl⟩ : syracuseStep 1043011 = 1564517) B1564517
theorem B1043027 : Blo 1040609 1043027 := bstep (se 1 (by rfl) ⟨782270, by rfl⟩ : syracuseStep 1043027 = 1564541) B1564541
theorem B1174099 : Blo 1040609 1174099 := bstep (se 1 (by rfl) ⟨880574, by rfl⟩ : syracuseStep 1174099 = 1761149) B1761149
theorem B1043043 : Blo 1040609 1043043 := bstep (se 1 (by rfl) ⟨782282, by rfl⟩ : syracuseStep 1043043 = 1564565) B1564565
theorem B1043059 : Blo 1040609 1043059 := bstep (se 1 (by rfl) ⟨782294, by rfl⟩ : syracuseStep 1043059 = 1564589) B1564589
theorem B1043075 : Blo 1040609 1043075 := bstep (se 1 (by rfl) ⟨782306, by rfl⟩ : syracuseStep 1043075 = 1564613) B1564613
theorem B1043091 : Blo 1040609 1043091 := bstep (se 1 (by rfl) ⟨782318, by rfl⟩ : syracuseStep 1043091 = 1564637) B1564637
theorem B1043107 : Blo 1040609 1043107 := bstep (se 1 (by rfl) ⟨782330, by rfl⟩ : syracuseStep 1043107 = 1564661) B1564661
theorem B1043123 : Blo 1040609 1043123 := bstep (se 1 (by rfl) ⟨782342, by rfl⟩ : syracuseStep 1043123 = 1564685) B1564685
theorem B1043139 : Blo 1040609 1043139 := bstep (se 1 (by rfl) ⟨782354, by rfl⟩ : syracuseStep 1043139 = 1564709) B1564709
theorem B1043155 : Blo 1040609 1043155 := bstep (se 1 (by rfl) ⟨782366, by rfl⟩ : syracuseStep 1043155 = 1564733) B1564733
theorem B1043171 : Blo 1040609 1043171 := bstep (se 1 (by rfl) ⟨782378, by rfl⟩ : syracuseStep 1043171 = 1564757) B1564757
theorem B1174243 : Blo 1040609 1174243 := bstep (se 1 (by rfl) ⟨880682, by rfl⟩ : syracuseStep 1174243 = 1761365) B1761365
theorem B1043187 : Blo 1040609 1043187 := bstep (se 1 (by rfl) ⟨782390, by rfl⟩ : syracuseStep 1043187 = 1564781) B1564781
theorem B1043203 : Blo 1040609 1043203 := bstep (se 1 (by rfl) ⟨782402, by rfl⟩ : syracuseStep 1043203 = 1564805) B1564805
theorem B1043219 : Blo 1040609 1043219 := bstep (se 1 (by rfl) ⟨782414, by rfl⟩ : syracuseStep 1043219 = 1564829) B1564829
theorem B1043235 : Blo 1040609 1043235 := bstep (se 1 (by rfl) ⟨782426, by rfl⟩ : syracuseStep 1043235 = 1564853) B1564853
theorem B3173165 : Blo 1040609 3173165 := bstep (se 3 (by rfl) ⟨594968, by rfl⟩ : syracuseStep 3173165 = 1189937) B1189937
theorem B1043251 : Blo 1040609 1043251 := bstep (se 1 (by rfl) ⟨782438, by rfl⟩ : syracuseStep 1043251 = 1564877) B1564877
theorem B1043267 : Blo 1040609 1043267 := bstep (se 1 (by rfl) ⟨782450, by rfl⟩ : syracuseStep 1043267 = 1564901) B1564901
theorem B1043283 : Blo 1040609 1043283 := bstep (se 1 (by rfl) ⟨782462, by rfl⟩ : syracuseStep 1043283 = 1564925) B1564925
theorem B1043299 : Blo 1040609 1043299 := bstep (se 1 (by rfl) ⟨782474, by rfl⟩ : syracuseStep 1043299 = 1564949) B1564949
theorem B1043315 : Blo 1040609 1043315 := bstep (se 1 (by rfl) ⟨782486, by rfl⟩ : syracuseStep 1043315 = 1564973) B1564973
theorem B1174387 : Blo 1040609 1174387 := bstep (se 1 (by rfl) ⟨880790, by rfl⟩ : syracuseStep 1174387 = 1761581) B1761581
theorem B1043331 : Blo 1040609 1043331 := bstep (se 1 (by rfl) ⟨782498, by rfl⟩ : syracuseStep 1043331 = 1564997) B1564997
theorem B4451213 : Blo 1040609 4451213 := bstep (se 3 (by rfl) ⟨834602, by rfl⟩ : syracuseStep 4451213 = 1669205) B1669205
theorem B1043347 : Blo 1040609 1043347 := bstep (se 1 (by rfl) ⟨782510, by rfl⟩ : syracuseStep 1043347 = 1565021) B1565021
theorem B1043363 : Blo 1040609 1043363 := bstep (se 1 (by rfl) ⟨782522, by rfl⟩ : syracuseStep 1043363 = 1565045) B1565045
theorem B1043379 : Blo 1040609 1043379 := bstep (se 1 (by rfl) ⟨782534, by rfl⟩ : syracuseStep 1043379 = 1565069) B1565069
theorem B1043395 : Blo 1040609 1043395 := bstep (se 1 (by rfl) ⟨782546, by rfl⟩ : syracuseStep 1043395 = 1565093) B1565093
theorem B1043411 : Blo 1040609 1043411 := bstep (se 1 (by rfl) ⟨782558, by rfl⟩ : syracuseStep 1043411 = 1565117) B1565117
theorem B1043427 : Blo 1040609 1043427 := bstep (se 1 (by rfl) ⟨782570, by rfl⟩ : syracuseStep 1043427 = 1565141) B1565141
theorem B1043443 : Blo 1040609 1043443 := bstep (se 1 (by rfl) ⟨782582, by rfl⟩ : syracuseStep 1043443 = 1565165) B1565165
theorem B1043459 : Blo 1040609 1043459 := bstep (se 1 (by rfl) ⟨782594, by rfl⟩ : syracuseStep 1043459 = 1565189) B1565189
theorem B1174531 : Blo 1040609 1174531 := bstep (se 1 (by rfl) ⟨880898, by rfl⟩ : syracuseStep 1174531 = 1761797) B1761797
theorem B1043475 : Blo 1040609 1043475 := bstep (se 1 (by rfl) ⟨782606, by rfl⟩ : syracuseStep 1043475 = 1565213) B1565213
theorem B1043491 : Blo 1040609 1043491 := bstep (se 1 (by rfl) ⟨782618, by rfl⟩ : syracuseStep 1043491 = 1565237) B1565237
theorem B1043507 : Blo 1040609 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B1043523 : Blo 1040609 1043523 := bstep (se 1 (by rfl) ⟨782642, by rfl⟩ : syracuseStep 1043523 = 1565285) B1565285
theorem B1043539 : Blo 1040609 1043539 := bstep (se 1 (by rfl) ⟨782654, by rfl⟩ : syracuseStep 1043539 = 1565309) B1565309
theorem B1043555 : Blo 1040609 1043555 := bstep (se 1 (by rfl) ⟨782666, by rfl⟩ : syracuseStep 1043555 = 1565333) B1565333
theorem B1043571 : Blo 1040609 1043571 := bstep (se 1 (by rfl) ⟨782678, by rfl⟩ : syracuseStep 1043571 = 1565357) B1565357
theorem B1043587 : Blo 1040609 1043587 := bstep (se 1 (by rfl) ⟨782690, by rfl⟩ : syracuseStep 1043587 = 1565381) B1565381
theorem B5270669 : Blo 1040609 5270669 := bstep (se 3 (by rfl) ⟨988250, by rfl⟩ : syracuseStep 5270669 = 1976501) B1976501
theorem B1043603 : Blo 1040609 1043603 := bstep (se 1 (by rfl) ⟨782702, by rfl⟩ : syracuseStep 1043603 = 1565405) B1565405
theorem B1174675 : Blo 1040609 1174675 := bstep (se 1 (by rfl) ⟨881006, by rfl⟩ : syracuseStep 1174675 = 1762013) B1762013
theorem B1043619 : Blo 1040609 1043619 := bstep (se 1 (by rfl) ⟨782714, by rfl⟩ : syracuseStep 1043619 = 1565429) B1565429
theorem B1043635 : Blo 1040609 1043635 := bstep (se 1 (by rfl) ⟨782726, by rfl⟩ : syracuseStep 1043635 = 1565453) B1565453
theorem B1043651 : Blo 1040609 1043651 := bstep (se 1 (by rfl) ⟨782738, by rfl⟩ : syracuseStep 1043651 = 1565477) B1565477
theorem B1043667 : Blo 1040609 1043667 := bstep (se 1 (by rfl) ⟨782750, by rfl⟩ : syracuseStep 1043667 = 1565501) B1565501
theorem B3960035 : Blo 1040609 3960035 := bstep (se 1 (by rfl) ⟨2970026, by rfl⟩ : syracuseStep 3960035 = 5940053) B5940053
theorem B1043683 : Blo 1040609 1043683 := bstep (se 1 (by rfl) ⟨782762, by rfl⟩ : syracuseStep 1043683 = 1565525) B1565525
theorem B3960049 : Blo 1040609 3960049 := bstep (se 2 (by rfl) ⟨1485018, by rfl⟩ : syracuseStep 3960049 = 2970037) B2970037
theorem B1043699 : Blo 1040609 1043699 := bstep (se 1 (by rfl) ⟨782774, by rfl⟩ : syracuseStep 1043699 = 1565549) B1565549
theorem B1043715 : Blo 1040609 1043715 := bstep (se 1 (by rfl) ⟨782786, by rfl⟩ : syracuseStep 1043715 = 1565573) B1565573
theorem B1043731 : Blo 1040609 1043731 := bstep (se 1 (by rfl) ⟨782798, by rfl⟩ : syracuseStep 1043731 = 1565597) B1565597
theorem B1043747 : Blo 1040609 1043747 := bstep (se 1 (by rfl) ⟨782810, by rfl⟩ : syracuseStep 1043747 = 1565621) B1565621
theorem B1174819 : Blo 1040609 1174819 := bstep (se 1 (by rfl) ⟨881114, by rfl⟩ : syracuseStep 1174819 = 1762229) B1762229
theorem B1043763 : Blo 1040609 1043763 := bstep (se 1 (by rfl) ⟨782822, by rfl⟩ : syracuseStep 1043763 = 1565645) B1565645
theorem B1043779 : Blo 1040609 1043779 := bstep (se 1 (by rfl) ⟨782834, by rfl⟩ : syracuseStep 1043779 = 1565669) B1565669
theorem B11889989 : Blo 1040609 11889989 := bstep (se 4 (by rfl) ⟨1114686, by rfl⟩ : syracuseStep 11889989 = 2229373) B2229373
theorem B1043795 : Blo 1040609 1043795 := bstep (se 1 (by rfl) ⟨782846, by rfl⟩ : syracuseStep 1043795 = 1565693) B1565693
theorem B1043811 : Blo 1040609 1043811 := bstep (se 1 (by rfl) ⟨782858, by rfl⟩ : syracuseStep 1043811 = 1565717) B1565717
theorem B1043827 : Blo 1040609 1043827 := bstep (se 1 (by rfl) ⟨782870, by rfl⟩ : syracuseStep 1043827 = 1565741) B1565741
theorem B1043843 : Blo 1040609 1043843 := bstep (se 1 (by rfl) ⟨782882, by rfl⟩ : syracuseStep 1043843 = 1565765) B1565765
theorem B1043859 : Blo 1040609 1043859 := bstep (se 1 (by rfl) ⟨782894, by rfl⟩ : syracuseStep 1043859 = 1565789) B1565789
theorem B1043875 : Blo 1040609 1043875 := bstep (se 1 (by rfl) ⟨782906, by rfl⟩ : syracuseStep 1043875 = 1565813) B1565813
theorem B1043891 : Blo 1040609 1043891 := bstep (se 1 (by rfl) ⟨782918, by rfl⟩ : syracuseStep 1043891 = 1565837) B1565837
theorem B1174963 : Blo 1040609 1174963 := bstep (se 1 (by rfl) ⟨881222, by rfl⟩ : syracuseStep 1174963 = 1762445) B1762445
theorem B1043907 : Blo 1040609 1043907 := bstep (se 1 (by rfl) ⟨782930, by rfl⟩ : syracuseStep 1043907 = 1565861) B1565861
theorem B4746701 : Blo 1040609 4746701 := bstep (se 3 (by rfl) ⟨890006, by rfl⟩ : syracuseStep 4746701 = 1780013) B1780013
theorem B1043923 : Blo 1040609 1043923 := bstep (se 1 (by rfl) ⟨782942, by rfl⟩ : syracuseStep 1043923 = 1565885) B1565885
theorem B1043939 : Blo 1040609 1043939 := bstep (se 1 (by rfl) ⟨782954, by rfl⟩ : syracuseStep 1043939 = 1565909) B1565909
theorem B1043955 : Blo 1040609 1043955 := bstep (se 1 (by rfl) ⟨782966, by rfl⟩ : syracuseStep 1043955 = 1565933) B1565933
theorem B1043971 : Blo 1040609 1043971 := bstep (se 1 (by rfl) ⟨782978, by rfl⟩ : syracuseStep 1043971 = 1565957) B1565957
theorem B1043987 : Blo 1040609 1043987 := bstep (se 1 (by rfl) ⟨782990, by rfl⟩ : syracuseStep 1043987 = 1565981) B1565981
theorem B1044003 : Blo 1040609 1044003 := bstep (se 1 (by rfl) ⟨783002, by rfl⟩ : syracuseStep 1044003 = 1566005) B1566005
theorem B1044019 : Blo 1040609 1044019 := bstep (se 1 (by rfl) ⟨783014, by rfl⟩ : syracuseStep 1044019 = 1566029) B1566029
theorem B1044035 : Blo 1040609 1044035 := bstep (se 1 (by rfl) ⟨783026, by rfl⟩ : syracuseStep 1044035 = 1566053) B1566053
theorem B1175107 : Blo 1040609 1175107 := bstep (se 1 (by rfl) ⟨881330, by rfl⟩ : syracuseStep 1175107 = 1762661) B1762661
theorem B1044051 : Blo 1040609 1044051 := bstep (se 1 (by rfl) ⟨783038, by rfl⟩ : syracuseStep 1044051 = 1566077) B1566077
theorem B1044067 : Blo 1040609 1044067 := bstep (se 1 (by rfl) ⟨783050, by rfl⟩ : syracuseStep 1044067 = 1566101) B1566101
theorem B6680177 : Blo 1040609 6680177 := bstep (se 2 (by rfl) ⟨2505066, by rfl⟩ : syracuseStep 6680177 = 5010133) B5010133
theorem B1044083 : Blo 1040609 1044083 := bstep (se 1 (by rfl) ⟨783062, by rfl⟩ : syracuseStep 1044083 = 1566125) B1566125
theorem B1044099 : Blo 1040609 1044099 := bstep (se 1 (by rfl) ⟨783074, by rfl⟩ : syracuseStep 1044099 = 1566149) B1566149
theorem B3010193 : Blo 1040609 3010193 := bstep (se 2 (by rfl) ⟨1128822, by rfl⟩ : syracuseStep 3010193 = 2257645) B2257645
theorem B1044115 : Blo 1040609 1044115 := bstep (se 1 (by rfl) ⟨783086, by rfl⟩ : syracuseStep 1044115 = 1566173) B1566173
theorem B1044131 : Blo 1040609 1044131 := bstep (se 1 (by rfl) ⟨783098, by rfl⟩ : syracuseStep 1044131 = 1566197) B1566197
theorem B1044147 : Blo 1040609 1044147 := bstep (se 1 (by rfl) ⟨783110, by rfl⟩ : syracuseStep 1044147 = 1566221) B1566221
theorem B1044163 : Blo 1040609 1044163 := bstep (se 1 (by rfl) ⟨783122, by rfl⟩ : syracuseStep 1044163 = 1566245) B1566245
theorem B1044179 : Blo 1040609 1044179 := bstep (se 1 (by rfl) ⟨783134, by rfl⟩ : syracuseStep 1044179 = 1566269) B1566269
theorem B1044195 : Blo 1040609 1044195 := bstep (se 1 (by rfl) ⟨783146, by rfl⟩ : syracuseStep 1044195 = 1566293) B1566293
theorem B1044211 : Blo 1040609 1044211 := bstep (se 1 (by rfl) ⟨783158, by rfl⟩ : syracuseStep 1044211 = 1566317) B1566317
theorem B1044227 : Blo 1040609 1044227 := bstep (se 1 (by rfl) ⟨783170, by rfl⟩ : syracuseStep 1044227 = 1566341) B1566341
theorem B1044243 : Blo 1040609 1044243 := bstep (se 1 (by rfl) ⟨783182, by rfl⟩ : syracuseStep 1044243 = 1566365) B1566365
theorem B1044259 : Blo 1040609 1044259 := bstep (se 1 (by rfl) ⟨783194, by rfl⟩ : syracuseStep 1044259 = 1566389) B1566389
theorem B1044275 : Blo 1040609 1044275 := bstep (se 1 (by rfl) ⟨783206, by rfl⟩ : syracuseStep 1044275 = 1566413) B1566413
theorem B1044291 : Blo 1040609 1044291 := bstep (se 1 (by rfl) ⟨783218, by rfl⟩ : syracuseStep 1044291 = 1566437) B1566437
theorem B1044307 : Blo 1040609 1044307 := bstep (se 1 (by rfl) ⟨783230, by rfl⟩ : syracuseStep 1044307 = 1566461) B1566461
theorem B1044323 : Blo 1040609 1044323 := bstep (se 1 (by rfl) ⟨783242, by rfl⟩ : syracuseStep 1044323 = 1566485) B1566485
theorem B1044339 : Blo 1040609 1044339 := bstep (se 1 (by rfl) ⟨783254, by rfl⟩ : syracuseStep 1044339 = 1566509) B1566509
theorem B1044355 : Blo 1040609 1044355 := bstep (se 1 (by rfl) ⟨783266, by rfl⟩ : syracuseStep 1044355 = 1566533) B1566533
theorem B1044371 : Blo 1040609 1044371 := bstep (se 1 (by rfl) ⟨783278, by rfl⟩ : syracuseStep 1044371 = 1566557) B1566557
theorem B1044387 : Blo 1040609 1044387 := bstep (se 1 (by rfl) ⟨783290, by rfl⟩ : syracuseStep 1044387 = 1566581) B1566581
theorem B1044403 : Blo 1040609 1044403 := bstep (se 1 (by rfl) ⟨783302, by rfl⟩ : syracuseStep 1044403 = 1566605) B1566605
theorem B1044419 : Blo 1040609 1044419 := bstep (se 1 (by rfl) ⟨783314, by rfl⟩ : syracuseStep 1044419 = 1566629) B1566629
theorem B1044435 : Blo 1040609 1044435 := bstep (se 1 (by rfl) ⟨783326, by rfl⟩ : syracuseStep 1044435 = 1566653) B1566653
theorem B1044451 : Blo 1040609 1044451 := bstep (se 1 (by rfl) ⟨783338, by rfl⟩ : syracuseStep 1044451 = 1566677) B1566677
theorem B1044467 : Blo 1040609 1044467 := bstep (se 1 (by rfl) ⟨783350, by rfl⟩ : syracuseStep 1044467 = 1566701) B1566701
theorem B3338243 : Blo 1040609 3338243 := bstep (se 1 (by rfl) ⟨2503682, by rfl⟩ : syracuseStep 3338243 = 5007365) B5007365
theorem B1044483 : Blo 1040609 1044483 := bstep (se 1 (by rfl) ⟨783362, by rfl⟩ : syracuseStep 1044483 = 1566725) B1566725
theorem B2224145 : Blo 1040609 2224145 := bstep (se 2 (by rfl) ⟨834054, by rfl⟩ : syracuseStep 2224145 = 1668109) B1668109
theorem B1044499 : Blo 1040609 1044499 := bstep (se 1 (by rfl) ⟨783374, by rfl⟩ : syracuseStep 1044499 = 1566749) B1566749
theorem B1044515 : Blo 1040609 1044515 := bstep (se 1 (by rfl) ⟨783386, by rfl⟩ : syracuseStep 1044515 = 1566773) B1566773
theorem B1044531 : Blo 1040609 1044531 := bstep (se 1 (by rfl) ⟨783398, by rfl⟩ : syracuseStep 1044531 = 1566797) B1566797
theorem B1044547 : Blo 1040609 1044547 := bstep (se 1 (by rfl) ⟨783410, by rfl⟩ : syracuseStep 1044547 = 1566821) B1566821
theorem B1667155 : Blo 1040609 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B1044563 : Blo 1040609 1044563 := bstep (se 1 (by rfl) ⟨783422, by rfl⟩ : syracuseStep 1044563 = 1566845) B1566845
theorem B1044579 : Blo 1040609 1044579 := bstep (se 1 (by rfl) ⟨783434, by rfl⟩ : syracuseStep 1044579 = 1566869) B1566869
theorem B1044595 : Blo 1040609 1044595 := bstep (se 1 (by rfl) ⟨783446, by rfl⟩ : syracuseStep 1044595 = 1566893) B1566893
theorem B4812941 : Blo 1040609 4812941 := bstep (se 3 (by rfl) ⟨902426, by rfl⟩ : syracuseStep 4812941 = 1804853) B1804853
theorem B6680717 : Blo 1040609 6680717 := bstep (se 3 (by rfl) ⟨1252634, by rfl⟩ : syracuseStep 6680717 = 2505269) B2505269
theorem B2814221 : Blo 1040609 2814221 := bstep (se 3 (by rfl) ⟨527666, by rfl⟩ : syracuseStep 2814221 = 1055333) B1055333
theorem B2224675 : Blo 1040609 2224675 := bstep (se 1 (by rfl) ⟨1668506, by rfl⟩ : syracuseStep 2224675 = 3337013) B3337013
theorem B3961507 : Blo 1040609 3961507 := bstep (se 1 (by rfl) ⟨2971130, by rfl⟩ : syracuseStep 3961507 = 5942261) B5942261
theorem B1667827 : Blo 1040609 1667827 := bstep (se 1 (by rfl) ⟨1250870, by rfl⟩ : syracuseStep 1667827 = 2501741) B2501741
theorem B1667873 : Blo 1040609 1667873 := bstep (se 2 (by rfl) ⟨625452, by rfl⟩ : syracuseStep 1667873 = 1250905) B1250905
theorem B3339089 : Blo 1040609 3339089 := bstep (se 2 (by rfl) ⟨1252158, by rfl⟩ : syracuseStep 3339089 = 2504317) B2504317
theorem B3339139 : Blo 1040609 3339139 := bstep (se 1 (by rfl) ⟨2504354, by rfl⟩ : syracuseStep 3339139 = 5008709) B5008709
theorem B2290801 : Blo 1040609 2290801 := bstep (se 2 (by rfl) ⟨859050, by rfl⟩ : syracuseStep 2290801 = 1718101) B1718101
theorem B22508741 : Blo 1040609 22508741 := bstep (se 4 (by rfl) ⟨2110194, by rfl⟩ : syracuseStep 22508741 = 4220389) B4220389
theorem B6419717 : Blo 1040609 6419717 := bstep (se 4 (by rfl) ⟨601848, by rfl⟩ : syracuseStep 6419717 = 1203697) B1203697
theorem B1668385 : Blo 1040609 1668385 := bstep (se 2 (by rfl) ⟨625644, by rfl⟩ : syracuseStep 1668385 = 1251289) B1251289
theorem B3175729 : Blo 1040609 3175729 := bstep (se 2 (by rfl) ⟨1190898, by rfl⟩ : syracuseStep 3175729 = 2381797) B2381797
theorem B3175757 : Blo 1040609 3175757 := bstep (se 3 (by rfl) ⟨595454, by rfl⟩ : syracuseStep 3175757 = 1190909) B1190909
theorem B1504657 : Blo 1040609 1504657 := bstep (se 2 (by rfl) ⟨564246, by rfl⟩ : syracuseStep 1504657 = 1128493) B1128493
theorem B5928389 : Blo 1040609 5928389 := bstep (se 4 (by rfl) ⟨555786, by rfl⟩ : syracuseStep 5928389 = 1111573) B1111573
theorem B2815661 : Blo 1040609 2815661 := bstep (se 3 (by rfl) ⟨527936, by rfl⟩ : syracuseStep 2815661 = 1055873) B1055873
theorem B1668929 : Blo 1040609 1668929 := bstep (se 2 (by rfl) ⟨625848, by rfl⟩ : syracuseStep 1668929 = 1251697) B1251697
theorem B2815843 : Blo 1040609 2815843 := bstep (se 1 (by rfl) ⟨2111882, by rfl⟩ : syracuseStep 2815843 = 4223765) B4223765
theorem B1111987 : Blo 1040609 1111987 := bstep (se 1 (by rfl) ⟨833990, by rfl⟩ : syracuseStep 1111987 = 1667981) B1667981
theorem B6191075 : Blo 1040609 6191075 := bstep (se 1 (by rfl) ⟨4643306, by rfl⟩ : syracuseStep 6191075 = 9286613) B9286613
theorem B5273585 : Blo 1040609 5273585 := bstep (se 2 (by rfl) ⟨1977594, by rfl⟩ : syracuseStep 5273585 = 3955189) B3955189
theorem B2226161 : Blo 1040609 2226161 := bstep (se 2 (by rfl) ⟨834810, by rfl⟩ : syracuseStep 2226161 = 1669621) B1669621
theorem B2226179 : Blo 1040609 2226179 := bstep (se 1 (by rfl) ⟨1669634, by rfl⟩ : syracuseStep 2226179 = 3339269) B3339269
theorem B3340369 : Blo 1040609 3340369 := bstep (se 2 (by rfl) ⟨1252638, by rfl⟩ : syracuseStep 3340369 = 2505277) B2505277
theorem B1407121 : Blo 1040609 1407121 := bstep (se 2 (by rfl) ⟨527670, by rfl⟩ : syracuseStep 1407121 = 1055341) B1055341
theorem B1112611 : Blo 1040609 1112611 := bstep (se 1 (by rfl) ⟨834458, by rfl⟩ : syracuseStep 1112611 = 1668917) B1668917
theorem B1669891 : Blo 1040609 1669891 := bstep (se 1 (by rfl) ⟨1252418, by rfl⟩ : syracuseStep 1669891 = 2504837) B2504837
theorem B3963725 : Blo 1040609 3963725 := bstep (se 3 (by rfl) ⟨743198, by rfl⟩ : syracuseStep 3963725 = 1486397) B1486397
theorem B1670147 : Blo 1040609 1670147 := bstep (se 1 (by rfl) ⟨1252610, by rfl⟩ : syracuseStep 1670147 = 2505221) B2505221
theorem B1408051 : Blo 1040609 1408051 := bstep (se 1 (by rfl) ⟨1056038, by rfl⟩ : syracuseStep 1408051 = 2112077) B2112077
theorem B4455587 : Blo 1040609 4455587 := bstep (se 1 (by rfl) ⟨3341690, by rfl⟩ : syracuseStep 4455587 = 6683381) B6683381
theorem B2227409 : Blo 1040609 2227409 := bstep (se 2 (by rfl) ⟨835278, by rfl⟩ : syracuseStep 2227409 = 1670557) B1670557
theorem B2817251 : Blo 1040609 2817251 := bstep (se 1 (by rfl) ⟨2112938, by rfl⟩ : syracuseStep 2817251 = 4225877) B4225877
theorem B5012707 : Blo 1040609 5012707 := bstep (se 1 (by rfl) ⟨3759530, by rfl⟩ : syracuseStep 5012707 = 7519061) B7519061
theorem B3341549 : Blo 1040609 3341549 := bstep (se 3 (by rfl) ⟨626540, by rfl⟩ : syracuseStep 3341549 = 1253081) B1253081
theorem B6683917 : Blo 1040609 6683917 := bstep (se 3 (by rfl) ⟨1253234, by rfl⟩ : syracuseStep 6683917 = 2506469) B2506469
theorem B5275043 : Blo 1040609 5275043 := bstep (se 1 (by rfl) ⟨3956282, by rfl⟩ : syracuseStep 5275043 = 7912565) B7912565
theorem B5799557 : Blo 1040609 5799557 := bstep (se 4 (by rfl) ⟨543708, by rfl⟩ : syracuseStep 5799557 = 1087417) B1087417
theorem B1670851 : Blo 1040609 1670851 := bstep (se 1 (by rfl) ⟨1253138, by rfl⟩ : syracuseStep 1670851 = 2506277) B2506277
theorem B2031427 : Blo 1040609 2031427 := bstep (se 1 (by rfl) ⟨1523570, by rfl⟩ : syracuseStep 2031427 = 3047141) B3047141
theorem B4226993 : Blo 1040609 4226993 := bstep (se 2 (by rfl) ⟨1585122, by rfl⟩ : syracuseStep 4226993 = 3170245) B3170245
theorem B1671121 : Blo 1040609 1671121 := bstep (se 2 (by rfl) ⟨626670, by rfl⟩ : syracuseStep 1671121 = 1253341) B1253341
theorem B1114123 : Blo 1040609 1114123 := bstep (se 1 (by rfl) ⟨835592, by rfl⟩ : syracuseStep 1114123 = 1671185) B1671185
theorem B19005475 : Blo 1040609 19005475 := bstep (se 1 (by rfl) ⟨14254106, by rfl⟩ : syracuseStep 19005475 = 28508213) B28508213
theorem B5931053 : Blo 1040609 5931053 := bstep (se 3 (by rfl) ⟨1112072, by rfl⟩ : syracuseStep 5931053 = 2224145) B2224145
theorem B4227137 : Blo 1040609 4227137 := bstep (se 2 (by rfl) ⟨1585176, by rfl⟩ : syracuseStep 4227137 = 3170353) B3170353
theorem B1605719 : Blo 1040609 1605719 := bstep (se 1 (by rfl) ⟨1204289, by rfl⟩ : syracuseStep 1605719 = 2408579) B2408579
theorem B7930061 : Blo 1040609 7930061 := bstep (se 3 (by rfl) ⟨1486886, by rfl⟩ : syracuseStep 7930061 = 2973773) B2973773
theorem B137036053 : Blo 1040609 137036053 := bstep (se 6 (by rfl) ⟨3211782, by rfl⟩ : syracuseStep 137036053 = 6423565) B6423565
theorem B1671563 : Blo 1040609 1671563 := bstep (se 1 (by rfl) ⟨1253672, by rfl⟩ : syracuseStep 1671563 = 2507345) B2507345
theorem B5276177 : Blo 1040609 5276177 := bstep (se 2 (by rfl) ⟨1978566, by rfl⟩ : syracuseStep 5276177 = 3957133) B3957133
theorem B6685249 : Blo 1040609 6685249 := bstep (se 2 (by rfl) ⟨2506968, by rfl⟩ : syracuseStep 6685249 = 5013937) B5013937
theorem B2228887 : Blo 1040609 2228887 := bstep (se 1 (by rfl) ⟨1671665, by rfl⟩ : syracuseStep 2228887 = 3343331) B3343331
theorem B5276339 : Blo 1040609 5276339 := bstep (se 1 (by rfl) ⟨3957254, by rfl⟩ : syracuseStep 5276339 = 7914509) B7914509
theorem B7930547 : Blo 1040609 7930547 := bstep (se 1 (by rfl) ⟨5947910, by rfl⟩ : syracuseStep 7930547 = 11895821) B11895821
theorem B7504589 : Blo 1040609 7504589 := bstep (se 3 (by rfl) ⟨1407110, by rfl⟩ : syracuseStep 7504589 = 2814221) B2814221
theorem B5931737 : Blo 1040609 5931737 := bstep (se 2 (by rfl) ⟨2224401, by rfl⟩ : syracuseStep 5931737 = 4448803) B4448803
theorem B3965699 : Blo 1040609 3965699 := bstep (se 1 (by rfl) ⟨2974274, by rfl⟩ : syracuseStep 3965699 = 5948549) B5948549
theorem B7504645 : Blo 1040609 7504645 := bstep (se 4 (by rfl) ⟨703560, by rfl⟩ : syracuseStep 7504645 = 1407121) B1407121
theorem B13337693 : Blo 1040609 13337693 := bstep (se 3 (by rfl) ⟨2500817, by rfl⟩ : syracuseStep 13337693 = 5001635) B5001635
theorem B9503837 : Blo 1040609 9503837 := bstep (se 3 (by rfl) ⟨1781969, by rfl⟩ : syracuseStep 9503837 = 3563939) B3563939
theorem B5637221 : Blo 1040609 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B3966155 : Blo 1040609 3966155 := bstep (se 1 (by rfl) ⟨2974616, by rfl⟩ : syracuseStep 3966155 = 5949233) B5949233
theorem B3343639 : Blo 1040609 3343639 := bstep (se 1 (by rfl) ⟨2507729, by rfl⟩ : syracuseStep 3343639 = 5015459) B5015459
theorem B2229707 : Blo 1040609 2229707 := bstep (se 1 (by rfl) ⟨1672280, by rfl⟩ : syracuseStep 2229707 = 3344561) B3344561
theorem B1410571 : Blo 1040609 1410571 := bstep (se 1 (by rfl) ⟨1057928, by rfl⟩ : syracuseStep 1410571 = 2115857) B2115857
theorem B4228631 : Blo 1040609 4228631 := bstep (se 1 (by rfl) ⟨3171473, by rfl⟩ : syracuseStep 4228631 = 6342947) B6342947
theorem B7932005 : Blo 1040609 7932005 := bstep (se 4 (by rfl) ⟨743625, by rfl⟩ : syracuseStep 7932005 = 1487251) B1487251
theorem B1411339 : Blo 1040609 1411339 := bstep (se 1 (by rfl) ⟨1058504, by rfl⟩ : syracuseStep 1411339 = 2117009) B2117009
theorem B2230553 : Blo 1040609 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B4458883 : Blo 1040609 4458883 := bstep (se 1 (by rfl) ⟨3344162, by rfl⟩ : syracuseStep 4458883 = 6688325) B6688325
theorem B10029491 : Blo 1040609 10029491 := bstep (se 1 (by rfl) ⟨7522118, by rfl⟩ : syracuseStep 10029491 = 15044237) B15044237
theorem B5278283 : Blo 1040609 5278283 := bstep (se 1 (by rfl) ⟨3958712, by rfl⟩ : syracuseStep 5278283 = 7917425) B7917425
theorem B3344971 : Blo 1040609 3344971 := bstep (se 1 (by rfl) ⟨2508728, by rfl⟩ : syracuseStep 3344971 = 5017457) B5017457
theorem B7932491 : Blo 1040609 7932491 := bstep (se 1 (by rfl) ⟨5949368, by rfl⟩ : syracuseStep 7932491 = 11898737) B11898737
theorem B10029719 : Blo 1040609 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B4459225 : Blo 1040609 4459225 := bstep (se 2 (by rfl) ⟨1672209, by rfl⟩ : syracuseStep 4459225 = 3344419) B3344419
theorem B3345587 : Blo 1040609 3345587 := bstep (se 1 (by rfl) ⟨2509190, by rfl⟩ : syracuseStep 3345587 = 5018381) B5018381
theorem B15011021 : Blo 1040609 15011021 := bstep (se 3 (by rfl) ⟨2814566, by rfl⟩ : syracuseStep 15011021 = 5629133) B5629133
theorem B2821337 : Blo 1040609 2821337 := bstep (se 2 (by rfl) ⟨1058001, by rfl⟩ : syracuseStep 2821337 = 2116003) B2116003
theorem B4460183 : Blo 1040609 4460183 := bstep (se 1 (by rfl) ⟨3345137, by rfl⟩ : syracuseStep 4460183 = 6690275) B6690275
theorem B3346265 : Blo 1040609 3346265 := bstep (se 2 (by rfl) ⟨1254849, by rfl⟩ : syracuseStep 3346265 = 2509699) B2509699
theorem B10030949 : Blo 1040609 10030949 := bstep (se 4 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 10030949 = 1880803) B1880803
theorem B5280065 : Blo 1040609 5280065 := bstep (se 2 (by rfl) ⟨1980024, by rfl⟩ : syracuseStep 5280065 = 3960049) B3960049
theorem B4067659 : Blo 1040609 4067659 := bstep (se 1 (by rfl) ⟨3050744, by rfl⟩ : syracuseStep 4067659 = 6101489) B6101489
theorem B15045041 : Blo 1040609 15045041 := bstep (se 2 (by rfl) ⟨5641890, by rfl⟩ : syracuseStep 15045041 = 11283781) B11283781
theorem B4756445 : Blo 1040609 4756445 := bstep (se 3 (by rfl) ⟨891833, by rfl⟩ : syracuseStep 4756445 = 1783667) B1783667
theorem B7902359 : Blo 1040609 7902359 := bstep (se 1 (by rfl) ⟨5926769, by rfl⟩ : syracuseStep 7902359 = 11853539) B11853539
theorem B5936429 : Blo 1040609 5936429 := bstep (se 3 (by rfl) ⟨1113080, by rfl⟩ : syracuseStep 5936429 = 2226161) B2226161
theorem B4461875 : Blo 1040609 4461875 := bstep (se 1 (by rfl) ⟨3346406, by rfl⟩ : syracuseStep 4461875 = 6692813) B6692813
theorem B16258421 : Blo 1040609 16258421 := bstep (se 5 (by rfl) ⟨762113, by rfl⟩ : syracuseStep 16258421 = 1524227) B1524227
theorem B11277899 : Blo 1040609 11277899 := bstep (se 1 (by rfl) ⟨8458424, by rfl⟩ : syracuseStep 11277899 = 16916849) B16916849
theorem B3512267 : Blo 1040609 3512267 := bstep (se 1 (by rfl) ⟨2634200, by rfl⟩ : syracuseStep 3512267 = 5268401) B5268401
theorem B3512537 : Blo 1040609 3512537 := bstep (se 2 (by rfl) ⟨1317201, by rfl⟩ : syracuseStep 3512537 = 2634403) B2634403
theorem B5282009 : Blo 1040609 5282009 := bstep (se 2 (by rfl) ⟨1980753, by rfl⟩ : syracuseStep 5282009 = 3961507) B3961507
theorem B1251659 : Blo 1040609 1251659 := bstep (se 1 (by rfl) ⟨938744, by rfl⟩ : syracuseStep 1251659 = 1877489) B1877489
theorem B1317323 : Blo 1040609 1317323 := bstep (se 1 (by rfl) ⟨987992, by rfl⟩ : syracuseStep 1317323 = 1975985) B1975985
theorem B2005555 : Blo 1040609 2005555 := bstep (se 1 (by rfl) ⟨1504166, by rfl⟩ : syracuseStep 2005555 = 3008333) B3008333
theorem B57744193 : Blo 1040609 57744193 := bstep (se 2 (by rfl) ⟨21654072, by rfl⟩ : syracuseStep 57744193 = 43308145) B43308145
theorem B3054401 : Blo 1040609 3054401 := bstep (se 2 (by rfl) ⟨1145400, by rfl⟩ : syracuseStep 3054401 = 2290801) B2290801
theorem B3513239 : Blo 1040609 3513239 := bstep (se 1 (by rfl) ⟨2634929, by rfl⟩ : syracuseStep 3513239 = 5269859) B5269859
theorem B1318027 : Blo 1040609 1318027 := bstep (se 1 (by rfl) ⟨988520, by rfl⟩ : syracuseStep 1318027 = 1977041) B1977041
theorem B2006209 : Blo 1040609 2006209 := bstep (se 2 (by rfl) ⟨752328, by rfl⟩ : syracuseStep 2006209 = 1504657) B1504657
theorem B1318295 : Blo 1040609 1318295 := bstep (se 1 (by rfl) ⟨988721, by rfl⟩ : syracuseStep 1318295 = 1977443) B1977443
theorem B3513779 : Blo 1040609 3513779 := bstep (se 1 (by rfl) ⟨2635334, by rfl⟩ : syracuseStep 3513779 = 5270669) B5270669
theorem B5643793 : Blo 1040609 5643793 := bstep (se 2 (by rfl) ⟨2116422, by rfl⟩ : syracuseStep 5643793 = 4232845) B4232845
theorem B13377059 : Blo 1040609 13377059 := bstep (se 1 (by rfl) ⟨10032794, by rfl⟩ : syracuseStep 13377059 = 20065589) B20065589
theorem B1056395 : Blo 1040609 1056395 := bstep (se 1 (by rfl) ⟨792296, by rfl⟩ : syracuseStep 1056395 = 1584593) B1584593
theorem B3514049 : Blo 1040609 3514049 := bstep (se 2 (by rfl) ⟨1317768, by rfl⟩ : syracuseStep 3514049 = 2635537) B2635537
theorem B2006795 : Blo 1040609 2006795 := bstep (se 1 (by rfl) ⟨1505096, by rfl⟩ : syracuseStep 2006795 = 3010193) B3010193
theorem B5283629 : Blo 1040609 5283629 := bstep (se 3 (by rfl) ⟨990680, by rfl⟩ : syracuseStep 5283629 = 1981361) B1981361
theorem B16883633 : Blo 1040609 16883633 := bstep (se 2 (by rfl) ⟨6331362, by rfl⟩ : syracuseStep 16883633 = 12662725) B12662725
theorem B4005953 : Blo 1040609 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B6692939 : Blo 1040609 6692939 := bstep (se 1 (by rfl) ⟨5019704, by rfl⟩ : syracuseStep 6692939 = 10039409) B10039409
theorem B1318999 : Blo 1040609 1318999 := bstep (se 1 (by rfl) ⟨989249, by rfl⟩ : syracuseStep 1318999 = 1978499) B1978499
theorem B3514589 : Blo 1040609 3514589 := bstep (se 3 (by rfl) ⟨658985, by rfl⟩ : syracuseStep 3514589 = 1317971) B1317971
theorem B33857837 : Blo 1040609 33857837 := bstep (se 3 (by rfl) ⟨6348344, by rfl⟩ : syracuseStep 33857837 = 12696689) B12696689
theorem B1188427 : Blo 1040609 1188427 := bstep (se 1 (by rfl) ⟨891320, by rfl⟩ : syracuseStep 1188427 = 1782641) B1782641
theorem B1483481 : Blo 1040609 1483481 := bstep (se 2 (by rfl) ⟨556305, by rfl⟩ : syracuseStep 1483481 = 1112611) B1112611
theorem B16032613 : Blo 1040609 16032613 := bstep (se 4 (by rfl) ⟨1503057, by rfl⟩ : syracuseStep 16032613 = 3006115) B3006115
theorem B1188919 : Blo 1040609 1188919 := bstep (se 1 (by rfl) ⟨891689, by rfl⟩ : syracuseStep 1188919 = 1783379) B1783379
theorem B1877107 : Blo 1040609 1877107 := bstep (se 1 (by rfl) ⟨1407830, by rfl⟩ : syracuseStep 1877107 = 2815661) B2815661
theorem B8922413 : Blo 1040609 8922413 := bstep (se 3 (by rfl) ⟨1672952, by rfl⟩ : syracuseStep 8922413 = 3345905) B3345905
theorem B3515723 : Blo 1040609 3515723 := bstep (se 1 (by rfl) ⟨2636792, by rfl⟩ : syracuseStep 3515723 = 5273585) B5273585
theorem B1484119 : Blo 1040609 1484119 := bstep (se 1 (by rfl) ⟨1113089, by rfl⟩ : syracuseStep 1484119 = 2226179) B2226179
theorem B1189207 : Blo 1040609 1189207 := bstep (se 1 (by rfl) ⟨891905, by rfl⟩ : syracuseStep 1189207 = 1783811) B1783811
theorem B1975681 : Blo 1040609 1975681 := bstep (se 2 (by rfl) ⟨740880, by rfl⟩ : syracuseStep 1975681 = 1481761) B1481761
theorem B1877401 : Blo 1040609 1877401 := bstep (se 2 (by rfl) ⟨704025, by rfl⟩ : syracuseStep 1877401 = 1408051) B1408051
theorem B3515993 : Blo 1040609 3515993 := bstep (se 2 (by rfl) ⟨1318497, by rfl⟩ : syracuseStep 3515993 = 2636995) B2636995
theorem B1058455 : Blo 1040609 1058455 := bstep (se 1 (by rfl) ⟨793841, by rfl⟩ : syracuseStep 1058455 = 1587683) B1587683
theorem B1320715 : Blo 1040609 1320715 := bstep (se 1 (by rfl) ⟨990536, by rfl⟩ : syracuseStep 1320715 = 1981073) B1981073
theorem B16918541 : Blo 1040609 16918541 := bstep (se 3 (by rfl) ⟨3172226, by rfl⟩ : syracuseStep 16918541 = 6344453) B6344453
theorem B1976395 : Blo 1040609 1976395 := bstep (se 1 (by rfl) ⟨1482296, by rfl⟩ : syracuseStep 1976395 = 2964593) B2964593
theorem B1484939 : Blo 1040609 1484939 := bstep (se 1 (by rfl) ⟨1113704, by rfl⟩ : syracuseStep 1484939 = 2227409) B2227409
theorem B1976471 : Blo 1040609 1976471 := bstep (se 1 (by rfl) ⟨1482353, by rfl⟩ : syracuseStep 1976471 = 2964707) B2964707
theorem B1878167 : Blo 1040609 1878167 := bstep (se 1 (by rfl) ⟨1408625, by rfl⟩ : syracuseStep 1878167 = 2817251) B2817251
theorem B3516695 : Blo 1040609 3516695 := bstep (se 1 (by rfl) ⟨2637521, by rfl⟩ : syracuseStep 3516695 = 5275043) B5275043
theorem B2500915 : Blo 1040609 2500915 := bstep (se 1 (by rfl) ⟨1875686, by rfl⟩ : syracuseStep 2500915 = 3751373) B3751373
theorem B12036701 : Blo 1040609 12036701 := bstep (se 3 (by rfl) ⟨2256881, by rfl⟩ : syracuseStep 12036701 = 4513763) B4513763
theorem B1321687 : Blo 1040609 1321687 := bstep (se 1 (by rfl) ⟨991265, by rfl⟩ : syracuseStep 1321687 = 1982531) B1982531
theorem B1977139 : Blo 1040609 1977139 := bstep (se 1 (by rfl) ⟨1482854, by rfl⟩ : syracuseStep 1977139 = 2965709) B2965709
theorem B3517235 : Blo 1040609 3517235 := bstep (se 1 (by rfl) ⟨2637926, by rfl⟩ : syracuseStep 3517235 = 5275853) B5275853
theorem B2501579 : Blo 1040609 2501579 := bstep (se 1 (by rfl) ⟨1876184, by rfl⟩ : syracuseStep 2501579 = 3752369) B3752369
theorem B1977367 : Blo 1040609 1977367 := bstep (se 1 (by rfl) ⟨1483025, by rfl⟩ : syracuseStep 1977367 = 2966051) B2966051
theorem B3517505 : Blo 1040609 3517505 := bstep (se 2 (by rfl) ⟨1319064, by rfl⟩ : syracuseStep 3517505 = 2638129) B2638129
theorem B1584203 : Blo 1040609 1584203 := bstep (se 1 (by rfl) ⟨1188152, by rfl⟩ : syracuseStep 1584203 = 2376305) B2376305
theorem B1977473 : Blo 1040609 1977473 := bstep (se 2 (by rfl) ⟨741552, by rfl⟩ : syracuseStep 1977473 = 1483105) B1483105
theorem B1977625 : Blo 1040609 1977625 := bstep (se 2 (by rfl) ⟨741609, by rfl⟩ : syracuseStep 1977625 = 1483219) B1483219
theorem B3518045 : Blo 1040609 3518045 := bstep (se 3 (by rfl) ⟨659633, by rfl⟩ : syracuseStep 3518045 = 1319267) B1319267
theorem B5287517 : Blo 1040609 5287517 := bstep (se 3 (by rfl) ⟨991409, by rfl⟩ : syracuseStep 5287517 = 1982819) B1982819
theorem B1879795 : Blo 1040609 1879795 := bstep (se 1 (by rfl) ⟨1409846, by rfl⟩ : syracuseStep 1879795 = 2819693) B2819693
theorem B10170629 : Blo 1040609 10170629 := bstep (se 4 (by rfl) ⟨953496, by rfl⟩ : syracuseStep 10170629 = 1906993) B1906993
theorem B7909649 : Blo 1040609 7909649 := bstep (se 2 (by rfl) ⟨2966118, by rfl⟩ : syracuseStep 7909649 = 5932237) B5932237
theorem B2634059 : Blo 1040609 2634059 := bstep (se 1 (by rfl) ⟨1975544, by rfl⟩ : syracuseStep 2634059 = 3951089) B3951089
theorem B1978931 : Blo 1040609 1978931 := bstep (se 1 (by rfl) ⟨1484198, by rfl⟩ : syracuseStep 1978931 = 2968397) B2968397
theorem B5943901 : Blo 1040609 5943901 := bstep (se 3 (by rfl) ⟨1114481, by rfl⟩ : syracuseStep 5943901 = 2228963) B2228963
theorem B1979083 : Blo 1040609 1979083 := bstep (se 1 (by rfl) ⟨1484312, by rfl⟩ : syracuseStep 1979083 = 2968625) B2968625
theorem B3519179 : Blo 1040609 3519179 := bstep (se 1 (by rfl) ⟨2639384, by rfl⟩ : syracuseStep 3519179 = 5278769) B5278769
theorem B4764419 : Blo 1040609 4764419 := bstep (se 1 (by rfl) ⟨3573314, by rfl⟩ : syracuseStep 4764419 = 7146629) B7146629
theorem B4764619 : Blo 1040609 4764619 := bstep (se 1 (by rfl) ⟨3573464, by rfl⟩ : syracuseStep 4764619 = 7146929) B7146929
theorem B3519449 : Blo 1040609 3519449 := bstep (se 2 (by rfl) ⟨1319793, by rfl⟩ : syracuseStep 3519449 = 2639587) B2639587
theorem B1979417 : Blo 1040609 1979417 := bstep (se 2 (by rfl) ⟨742281, by rfl⟩ : syracuseStep 1979417 = 1484563) B1484563
theorem B1717337 : Blo 1040609 1717337 := bstep (se 2 (by rfl) ⟨644001, by rfl⟩ : syracuseStep 1717337 = 1288003) B1288003
theorem B2635031 : Blo 1040609 2635031 := bstep (se 1 (by rfl) ⟨1976273, by rfl⟩ : syracuseStep 2635031 = 3952547) B3952547
theorem B1881611 : Blo 1040609 1881611 := bstep (se 1 (by rfl) ⟨1411208, by rfl⟩ : syracuseStep 1881611 = 2822417) B2822417
theorem B1128043 : Blo 1040609 1128043 := bstep (se 1 (by rfl) ⟨846032, by rfl⟩ : syracuseStep 1128043 = 1692065) B1692065
theorem B1980055 : Blo 1040609 1980055 := bstep (se 1 (by rfl) ⟨1485041, by rfl⟩ : syracuseStep 1980055 = 2970083) B2970083
theorem B3520151 : Blo 1040609 3520151 := bstep (se 1 (by rfl) ⟨2640113, by rfl⟩ : syracuseStep 3520151 = 5280227) B5280227
theorem B2111233 : Blo 1040609 2111233 := bstep (se 2 (by rfl) ⟨791712, by rfl⟩ : syracuseStep 2111233 = 1583425) B1583425
theorem B2635699 : Blo 1040609 2635699 := bstep (se 1 (by rfl) ⟨1976774, by rfl⟩ : syracuseStep 2635699 = 3953549) B3953549
theorem B2635841 : Blo 1040609 2635841 := bstep (se 2 (by rfl) ⟨988440, by rfl⟩ : syracuseStep 2635841 = 1976881) B1976881
theorem B3520691 : Blo 1040609 3520691 := bstep (se 1 (by rfl) ⟨2640518, by rfl⟩ : syracuseStep 3520691 = 5281037) B5281037
theorem B15022435 : Blo 1040609 15022435 := bstep (se 1 (by rfl) ⟨11266826, by rfl⟩ : syracuseStep 15022435 = 22533653) B22533653
theorem B3520961 : Blo 1040609 3520961 := bstep (se 2 (by rfl) ⟨1320360, by rfl⟩ : syracuseStep 3520961 = 2640721) B2640721
theorem B2505163 : Blo 1040609 2505163 := bstep (se 1 (by rfl) ⟨1878872, by rfl⟩ : syracuseStep 2505163 = 3757745) B3757745
theorem B1980875 : Blo 1040609 1980875 := bstep (se 1 (by rfl) ⟨1485656, by rfl⟩ : syracuseStep 1980875 = 2971313) B2971313
theorem B1980929 : Blo 1040609 1980929 := bstep (se 2 (by rfl) ⟨742848, by rfl⟩ : syracuseStep 1980929 = 1485697) B1485697
theorem B2341529 : Blo 1040609 2341529 := bstep (se 2 (by rfl) ⟨878073, by rfl⟩ : syracuseStep 2341529 = 1756147) B1756147
theorem B5356211 : Blo 1040609 5356211 := bstep (se 1 (by rfl) ⟨4017158, by rfl⟩ : syracuseStep 5356211 = 8034317) B8034317
theorem B2341619 : Blo 1040609 2341619 := bstep (se 1 (by rfl) ⟨1756214, by rfl⟩ : syracuseStep 2341619 = 3512429) B3512429
theorem B2341655 : Blo 1040609 2341655 := bstep (se 1 (by rfl) ⟨1756241, by rfl⟩ : syracuseStep 2341655 = 3512483) B3512483
theorem B2374553 : Blo 1040609 2374553 := bstep (se 2 (by rfl) ⟨890457, by rfl⟩ : syracuseStep 2374553 = 1780915) B1780915
theorem B114342853 : Blo 1040609 114342853 := bstep (se 4 (by rfl) ⟨10719642, by rfl⟩ : syracuseStep 114342853 = 21439285) B21439285
theorem B2341835 : Blo 1040609 2341835 := bstep (se 1 (by rfl) ⟨1756376, by rfl⟩ : syracuseStep 2341835 = 3512753) B3512753
theorem B3521501 : Blo 1040609 3521501 := bstep (se 3 (by rfl) ⟨660281, by rfl⟩ : syracuseStep 3521501 = 1320563) B1320563
theorem B2341889 : Blo 1040609 2341889 := bstep (se 2 (by rfl) ⟨878208, by rfl⟩ : syracuseStep 2341889 = 1756417) B1756417
theorem B2505779 : Blo 1040609 2505779 := bstep (se 1 (by rfl) ⟨1879334, by rfl⟩ : syracuseStep 2505779 = 3758669) B3758669
theorem B2374721 : Blo 1040609 2374721 := bstep (se 2 (by rfl) ⟨890520, by rfl⟩ : syracuseStep 2374721 = 1781041) B1781041
theorem B2342105 : Blo 1040609 2342105 := bstep (se 2 (by rfl) ⟨878289, by rfl⟩ : syracuseStep 2342105 = 1756579) B1756579
theorem B2342195 : Blo 1040609 2342195 := bstep (se 1 (by rfl) ⟨1756646, by rfl⟩ : syracuseStep 2342195 = 3513293) B3513293
theorem B2637107 : Blo 1040609 2637107 := bstep (se 1 (by rfl) ⟨1977830, by rfl⟩ : syracuseStep 2637107 = 3955661) B3955661
theorem B6667595 : Blo 1040609 6667595 := bstep (se 1 (by rfl) ⟨5000696, by rfl⟩ : syracuseStep 6667595 = 10001393) B10001393
theorem B2342231 : Blo 1040609 2342231 := bstep (se 1 (by rfl) ⟨1756673, by rfl⟩ : syracuseStep 2342231 = 3513347) B3513347
theorem B1981847 : Blo 1040609 1981847 := bstep (se 1 (by rfl) ⟨1486385, by rfl⟩ : syracuseStep 1981847 = 2972771) B2972771
theorem B2375065 : Blo 1040609 2375065 := bstep (se 2 (by rfl) ⟨890649, by rfl⟩ : syracuseStep 2375065 = 1781299) B1781299
theorem B2342411 : Blo 1040609 2342411 := bstep (se 1 (by rfl) ⟨1756808, by rfl⟩ : syracuseStep 2342411 = 3513617) B3513617
theorem B2342465 : Blo 1040609 2342465 := bstep (se 2 (by rfl) ⟨878424, by rfl⟩ : syracuseStep 2342465 = 1756849) B1756849
theorem B2113303 : Blo 1040609 2113303 := bstep (se 1 (by rfl) ⟨1584977, by rfl⟩ : syracuseStep 2113303 = 3169955) B3169955
theorem B2342681 : Blo 1040609 2342681 := bstep (se 2 (by rfl) ⟨878505, by rfl⟩ : syracuseStep 2342681 = 1757011) B1757011
theorem B2637643 : Blo 1040609 2637643 := bstep (se 1 (by rfl) ⟨1978232, by rfl⟩ : syracuseStep 2637643 = 3956465) B3956465
theorem B2506585 : Blo 1040609 2506585 := bstep (se 2 (by rfl) ⟨939969, by rfl⟩ : syracuseStep 2506585 = 1879939) B1879939
theorem B2342771 : Blo 1040609 2342771 := bstep (se 1 (by rfl) ⟨1757078, by rfl⟩ : syracuseStep 2342771 = 3514157) B3514157
theorem B2342807 : Blo 1040609 2342807 := bstep (se 1 (by rfl) ⟨1757105, by rfl⟩ : syracuseStep 2342807 = 3514211) B3514211
theorem B1982387 : Blo 1040609 1982387 := bstep (se 1 (by rfl) ⟨1486790, by rfl⟩ : syracuseStep 1982387 = 2973581) B2973581
theorem B1785815 : Blo 1040609 1785815 := bstep (se 1 (by rfl) ⟨1339361, by rfl⟩ : syracuseStep 1785815 = 2678723) B2678723
theorem B2637785 : Blo 1040609 2637785 := bstep (se 2 (by rfl) ⟨989169, by rfl⟩ : syracuseStep 2637785 = 1978339) B1978339
theorem B7520273 : Blo 1040609 7520273 := bstep (se 2 (by rfl) ⟨2820102, by rfl⟩ : syracuseStep 7520273 = 5640205) B5640205
theorem B7913537 : Blo 1040609 7913537 := bstep (se 2 (by rfl) ⟨2967576, by rfl⟩ : syracuseStep 7913537 = 5935153) B5935153
theorem B2342987 : Blo 1040609 2342987 := bstep (se 1 (by rfl) ⟨1757240, by rfl⟩ : syracuseStep 2342987 = 3514481) B3514481
theorem B3522635 : Blo 1040609 3522635 := bstep (se 1 (by rfl) ⟨2641976, by rfl⟩ : syracuseStep 3522635 = 5283953) B5283953
theorem B2343041 : Blo 1040609 2343041 := bstep (se 2 (by rfl) ⟨878640, by rfl⟩ : syracuseStep 2343041 = 1757281) B1757281
theorem B9027875 : Blo 1040609 9027875 := bstep (se 1 (by rfl) ⟨6770906, by rfl⟩ : syracuseStep 9027875 = 13541813) B13541813
theorem B2965835 : Blo 1040609 2965835 := bstep (se 1 (by rfl) ⟨2224376, by rfl⟩ : syracuseStep 2965835 = 4448753) B4448753
theorem B2343257 : Blo 1040609 2343257 := bstep (se 2 (by rfl) ⟨878721, by rfl⟩ : syracuseStep 2343257 = 1757443) B1757443
theorem B3522905 : Blo 1040609 3522905 := bstep (se 2 (by rfl) ⟨1321089, by rfl⟩ : syracuseStep 3522905 = 2642179) B2642179
theorem B1982873 : Blo 1040609 1982873 := bstep (se 2 (by rfl) ⟨743577, by rfl⟩ : syracuseStep 1982873 = 1487155) B1487155
theorem B2343347 : Blo 1040609 2343347 := bstep (se 1 (by rfl) ⟨1757510, by rfl⟩ : syracuseStep 2343347 = 3515021) B3515021
theorem B2343383 : Blo 1040609 2343383 := bstep (se 1 (by rfl) ⟨1757537, by rfl⟩ : syracuseStep 2343383 = 3515075) B3515075
theorem B3811263029 : Blo 1040609 3811263029 := bstep (se 5 (by rfl) ⟨178652954, by rfl⟩ : syracuseStep 3811263029 = 357305909) B357305909
theorem B2343563 : Blo 1040609 2343563 := bstep (se 1 (by rfl) ⟨1757672, by rfl⟩ : syracuseStep 2343563 = 3515345) B3515345
theorem B2343617 : Blo 1040609 2343617 := bstep (se 2 (by rfl) ⟨878856, by rfl⟩ : syracuseStep 2343617 = 1757713) B1757713
theorem B2966233 : Blo 1040609 2966233 := bstep (se 2 (by rfl) ⟨1112337, by rfl⟩ : syracuseStep 2966233 = 2224675) B2224675
theorem B2638615 : Blo 1040609 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B2343833 : Blo 1040609 2343833 := bstep (se 2 (by rfl) ⟨878937, by rfl⟩ : syracuseStep 2343833 = 1757875) B1757875
theorem B2343923 : Blo 1040609 2343923 := bstep (se 1 (by rfl) ⟨1757942, by rfl⟩ : syracuseStep 2343923 = 3515885) B3515885
theorem B67748885 : Blo 1040609 67748885 := bstep (se 6 (by rfl) ⟨1587864, by rfl⟩ : syracuseStep 67748885 = 3175729) B3175729
theorem B2343959 : Blo 1040609 2343959 := bstep (se 1 (by rfl) ⟨1757969, by rfl⟩ : syracuseStep 2343959 = 3515939) B3515939
theorem B3523607 : Blo 1040609 3523607 := bstep (se 1 (by rfl) ⟨2642705, by rfl⟩ : syracuseStep 3523607 = 5285411) B5285411
theorem B2114689 : Blo 1040609 2114689 := bstep (se 2 (by rfl) ⟨793008, by rfl⟩ : syracuseStep 2114689 = 1586017) B1586017
theorem B2344139 : Blo 1040609 2344139 := bstep (se 1 (by rfl) ⟨1758104, by rfl⟩ : syracuseStep 2344139 = 3516209) B3516209
theorem B2639051 : Blo 1040609 2639051 := bstep (se 1 (by rfl) ⟨1979288, by rfl⟩ : syracuseStep 2639051 = 3958577) B3958577
theorem B2344193 : Blo 1040609 2344193 := bstep (se 2 (by rfl) ⟨879072, by rfl⟩ : syracuseStep 2344193 = 1758145) B1758145
theorem B8897809 : Blo 1040609 8897809 := bstep (se 2 (by rfl) ⟨3336678, by rfl⟩ : syracuseStep 8897809 = 6673357) B6673357
theorem B2344409 : Blo 1040609 2344409 := bstep (se 2 (by rfl) ⟨879153, by rfl⟩ : syracuseStep 2344409 = 1758307) B1758307
theorem B8898083 : Blo 1040609 8898083 := bstep (se 1 (by rfl) ⟨6673562, by rfl⟩ : syracuseStep 8898083 = 13347125) B13347125
theorem B2344499 : Blo 1040609 2344499 := bstep (se 1 (by rfl) ⟨1758374, by rfl⟩ : syracuseStep 2344499 = 3516749) B3516749
theorem B3524147 : Blo 1040609 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B2639425 : Blo 1040609 2639425 := bstep (se 2 (by rfl) ⟨989784, by rfl⟩ : syracuseStep 2639425 = 1979569) B1979569
theorem B2344535 : Blo 1040609 2344535 := bstep (se 1 (by rfl) ⟨1758401, by rfl⟩ : syracuseStep 2344535 = 3516803) B3516803
theorem B2344715 : Blo 1040609 2344715 := bstep (se 1 (by rfl) ⟨1758536, by rfl⟩ : syracuseStep 2344715 = 3517073) B3517073
theorem B2115353 : Blo 1040609 2115353 := bstep (se 2 (by rfl) ⟨793257, by rfl⟩ : syracuseStep 2115353 = 1586515) B1586515
theorem B2344769 : Blo 1040609 2344769 := bstep (se 2 (by rfl) ⟨879288, by rfl⟩ : syracuseStep 2344769 = 1758577) B1758577
theorem B3524417 : Blo 1040609 3524417 := bstep (se 2 (by rfl) ⟨1321656, by rfl⟩ : syracuseStep 3524417 = 2643313) B2643313
theorem B2115443 : Blo 1040609 2115443 := bstep (se 1 (by rfl) ⟨1586582, by rfl⟩ : syracuseStep 2115443 = 3173165) B3173165
theorem B6670259 : Blo 1040609 6670259 := bstep (se 1 (by rfl) ⟨5002694, by rfl⟩ : syracuseStep 6670259 = 10005389) B10005389
theorem B2967475 : Blo 1040609 2967475 := bstep (se 1 (by rfl) ⟨2225606, by rfl⟩ : syracuseStep 2967475 = 4451213) B4451213
theorem B2508737 : Blo 1040609 2508737 := bstep (se 2 (by rfl) ⟨940776, by rfl⟩ : syracuseStep 2508737 = 1881553) B1881553
theorem B7915481 : Blo 1040609 7915481 := bstep (se 2 (by rfl) ⟨2968305, by rfl⟩ : syracuseStep 7915481 = 5936611) B5936611
theorem B2344985 : Blo 1040609 2344985 := bstep (se 2 (by rfl) ⟨879369, by rfl⟩ : syracuseStep 2344985 = 1758739) B1758739
theorem B2345075 : Blo 1040609 2345075 := bstep (se 1 (by rfl) ⟨1758806, by rfl⟩ : syracuseStep 2345075 = 3517613) B3517613
theorem B1689751 : Blo 1040609 1689751 := bstep (se 1 (by rfl) ⟨1267313, by rfl⟩ : syracuseStep 1689751 = 2534627) B2534627
theorem B6670487 : Blo 1040609 6670487 := bstep (se 1 (by rfl) ⟨5002865, by rfl⟩ : syracuseStep 6670487 = 10005731) B10005731
theorem B2345111 : Blo 1040609 2345111 := bstep (se 1 (by rfl) ⟨1758833, by rfl⟩ : syracuseStep 2345111 = 3517667) B3517667
theorem B2640023 : Blo 1040609 2640023 := bstep (se 1 (by rfl) ⟨1980017, by rfl⟩ : syracuseStep 2640023 = 3960035) B3960035
theorem B3164467 : Blo 1040609 3164467 := bstep (se 1 (by rfl) ⟨2373350, by rfl⟩ : syracuseStep 3164467 = 4746701) B4746701
theorem B2345291 : Blo 1040609 2345291 := bstep (se 1 (by rfl) ⟨1758968, by rfl⟩ : syracuseStep 2345291 = 3517937) B3517937
theorem B3524957 : Blo 1040609 3524957 := bstep (se 3 (by rfl) ⟨660929, by rfl⟩ : syracuseStep 3524957 = 1321859) B1321859
theorem B2345345 : Blo 1040609 2345345 := bstep (se 2 (by rfl) ⟨879504, by rfl⟩ : syracuseStep 2345345 = 1759009) B1759009
theorem B3754457 : Blo 1040609 3754457 := bstep (se 2 (by rfl) ⟨1407921, by rfl⟩ : syracuseStep 3754457 = 2815843) B2815843
theorem B2345561 : Blo 1040609 2345561 := bstep (se 2 (by rfl) ⟨879585, by rfl⟩ : syracuseStep 2345561 = 1759171) B1759171
theorem B2345651 : Blo 1040609 2345651 := bstep (se 1 (by rfl) ⟨1759238, by rfl⟩ : syracuseStep 2345651 = 3518477) B3518477
theorem B2345687 : Blo 1040609 2345687 := bstep (se 1 (by rfl) ⟨1759265, by rfl⟩ : syracuseStep 2345687 = 3518531) B3518531
theorem B2345867 : Blo 1040609 2345867 := bstep (se 1 (by rfl) ⟨1759400, by rfl⟩ : syracuseStep 2345867 = 3518801) B3518801
theorem B2345921 : Blo 1040609 2345921 := bstep (se 2 (by rfl) ⟨879720, by rfl⟩ : syracuseStep 2345921 = 1759441) B1759441
theorem B2640833 : Blo 1040609 2640833 := bstep (se 2 (by rfl) ⟨990312, by rfl⟩ : syracuseStep 2640833 = 1980625) B1980625
theorem B1756235 : Blo 1040609 1756235 := bstep (se 1 (by rfl) ⟨1317176, by rfl⟩ : syracuseStep 1756235 = 2634353) B2634353
theorem B2346137 : Blo 1040609 2346137 := bstep (se 2 (by rfl) ⟨879801, by rfl⟩ : syracuseStep 2346137 = 1759603) B1759603
theorem B1756363 : Blo 1040609 1756363 := bstep (se 1 (by rfl) ⟨1317272, by rfl⟩ : syracuseStep 1756363 = 2634545) B2634545
theorem B2346227 : Blo 1040609 2346227 := bstep (se 1 (by rfl) ⟨1759670, by rfl⟩ : syracuseStep 2346227 = 3519341) B3519341
theorem B2346263 : Blo 1040609 2346263 := bstep (se 1 (by rfl) ⟨1759697, by rfl⟩ : syracuseStep 2346263 = 3519395) B3519395
theorem B1756505 : Blo 1040609 1756505 := bstep (se 2 (by rfl) ⟨658689, by rfl⟩ : syracuseStep 1756505 = 1317379) B1317379
theorem B6671717 : Blo 1040609 6671717 := bstep (se 4 (by rfl) ⟨625473, by rfl⟩ : syracuseStep 6671717 = 1250947) B1250947
theorem B2346443 : Blo 1040609 2346443 := bstep (se 1 (by rfl) ⟨1759832, by rfl⟩ : syracuseStep 2346443 = 3519665) B3519665
theorem B1756633 : Blo 1040609 1756633 := bstep (se 2 (by rfl) ⟨658737, by rfl⟩ : syracuseStep 1756633 = 1317475) B1317475
theorem B2641369 : Blo 1040609 2641369 := bstep (se 2 (by rfl) ⟨990513, by rfl⟩ : syracuseStep 2641369 = 1981027) B1981027
theorem B2346497 : Blo 1040609 2346497 := bstep (se 2 (by rfl) ⟨879936, by rfl⟩ : syracuseStep 2346497 = 1759873) B1759873
theorem B4279811 : Blo 1040609 4279811 := bstep (se 1 (by rfl) ⟨3209858, by rfl⟩ : syracuseStep 4279811 = 6419717) B6419717
theorem B2379289 : Blo 1040609 2379289 := bstep (se 2 (by rfl) ⟨892233, by rfl⟩ : syracuseStep 2379289 = 1784467) B1784467
theorem B2117171 : Blo 1040609 2117171 := bstep (se 1 (by rfl) ⟨1587878, by rfl⟩ : syracuseStep 2117171 = 3175757) B3175757
theorem B2674241 : Blo 1040609 2674241 := bstep (se 2 (by rfl) ⟨1002840, by rfl⟩ : syracuseStep 2674241 = 2005681) B2005681
theorem B8572517 : Blo 1040609 8572517 := bstep (se 4 (by rfl) ⟨803673, by rfl⟩ : syracuseStep 8572517 = 1607347) B1607347
theorem B3952259 : Blo 1040609 3952259 := bstep (se 1 (by rfl) ⟨2964194, by rfl⟩ : syracuseStep 3952259 = 5928389) B5928389
theorem B3952273 : Blo 1040609 3952273 := bstep (se 2 (by rfl) ⟨1482102, by rfl⟩ : syracuseStep 3952273 = 2964205) B2964205
theorem B2346713 : Blo 1040609 2346713 := bstep (se 2 (by rfl) ⟨880017, by rfl⟩ : syracuseStep 2346713 = 1760035) B1760035
theorem B2346803 : Blo 1040609 2346803 := bstep (se 1 (by rfl) ⟨1760102, by rfl⟩ : syracuseStep 2346803 = 3520205) B3520205
theorem B2346839 : Blo 1040609 2346839 := bstep (se 1 (by rfl) ⟨1760129, by rfl⟩ : syracuseStep 2346839 = 3520259) B3520259
theorem B3952577 : Blo 1040609 3952577 := bstep (se 2 (by rfl) ⟨1482216, by rfl⟩ : syracuseStep 3952577 = 2964433) B2964433
theorem B2347019 : Blo 1040609 2347019 := bstep (se 1 (by rfl) ⟨1760264, by rfl⟩ : syracuseStep 2347019 = 3520529) B3520529
theorem B1757207 : Blo 1040609 1757207 := bstep (se 1 (by rfl) ⟨1317905, by rfl⟩ : syracuseStep 1757207 = 2635811) B2635811
theorem B2347073 : Blo 1040609 2347073 := bstep (se 2 (by rfl) ⟨880152, by rfl⟩ : syracuseStep 2347073 = 1760305) B1760305
theorem B1757335 : Blo 1040609 1757335 := bstep (se 1 (by rfl) ⟨1318001, by rfl⟩ : syracuseStep 1757335 = 2636003) B2636003
theorem B2347289 : Blo 1040609 2347289 := bstep (se 2 (by rfl) ⟨880233, by rfl⟩ : syracuseStep 2347289 = 1760467) B1760467
theorem B2347379 : Blo 1040609 2347379 := bstep (se 1 (by rfl) ⟨1760534, by rfl⟩ : syracuseStep 2347379 = 3521069) B3521069
theorem B1560971 : Blo 1040609 1560971 := bstep (se 1 (by rfl) ⟨1170728, by rfl⟩ : syracuseStep 1560971 = 2341457) B2341457
theorem B1560983 : Blo 1040609 1560983 := bstep (se 1 (by rfl) ⟨1170737, by rfl⟩ : syracuseStep 1560983 = 2341475) B2341475
theorem B2347415 : Blo 1040609 2347415 := bstep (se 1 (by rfl) ⟨1760561, by rfl⟩ : syracuseStep 2347415 = 3521123) B3521123
theorem B19026353 : Blo 1040609 19026353 := bstep (se 2 (by rfl) ⟨7134882, by rfl⟩ : syracuseStep 19026353 = 14269765) B14269765
theorem B1561049 : Blo 1040609 1561049 := bstep (se 2 (by rfl) ⟨585393, by rfl⟩ : syracuseStep 1561049 = 1170787) B1170787
theorem B2642483 : Blo 1040609 2642483 := bstep (se 1 (by rfl) ⟨1981862, by rfl⟩ : syracuseStep 2642483 = 3963725) B3963725
theorem B1561163 : Blo 1040609 1561163 := bstep (se 1 (by rfl) ⟨1170872, by rfl⟩ : syracuseStep 1561163 = 2341745) B2341745
theorem B2347595 : Blo 1040609 2347595 := bstep (se 1 (by rfl) ⟨1760696, by rfl⟩ : syracuseStep 2347595 = 3521393) B3521393
theorem B1561175 : Blo 1040609 1561175 := bstep (se 1 (by rfl) ⟨1170881, by rfl⟩ : syracuseStep 1561175 = 2341763) B2341763
theorem B3953245 : Blo 1040609 3953245 := bstep (se 3 (by rfl) ⟨741233, by rfl⟩ : syracuseStep 3953245 = 1482467) B1482467
theorem B2347649 : Blo 1040609 2347649 := bstep (se 2 (by rfl) ⟨880368, by rfl⟩ : syracuseStep 2347649 = 1760737) B1760737
theorem B1561241 : Blo 1040609 1561241 := bstep (se 2 (by rfl) ⟨585465, by rfl⟩ : syracuseStep 1561241 = 1170931) B1170931
theorem B14471885 : Blo 1040609 14471885 := bstep (se 3 (by rfl) ⟨2713478, by rfl⟩ : syracuseStep 14471885 = 5426957) B5426957
theorem B1561355 : Blo 1040609 1561355 := bstep (se 1 (by rfl) ⟨1171016, by rfl⟩ : syracuseStep 1561355 = 2342033) B2342033
theorem B1757963 : Blo 1040609 1757963 := bstep (se 1 (by rfl) ⟨1318472, by rfl⟩ : syracuseStep 1757963 = 2636945) B2636945
theorem B1561367 : Blo 1040609 1561367 := bstep (se 1 (by rfl) ⟨1171025, by rfl⟩ : syracuseStep 1561367 = 2342051) B2342051
theorem B2970391 : Blo 1040609 2970391 := bstep (se 1 (by rfl) ⟨2227793, by rfl⟩ : syracuseStep 2970391 = 4455587) B4455587
theorem B1561433 : Blo 1040609 1561433 := bstep (se 2 (by rfl) ⟨585537, by rfl⟩ : syracuseStep 1561433 = 1171075) B1171075
theorem B2347865 : Blo 1040609 2347865 := bstep (se 2 (by rfl) ⟨880449, by rfl⟩ : syracuseStep 2347865 = 1760899) B1760899
theorem B2642777 : Blo 1040609 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B1758091 : Blo 1040609 1758091 := bstep (se 1 (by rfl) ⟨1318568, by rfl⟩ : syracuseStep 1758091 = 2637137) B2637137
theorem B21418931 : Blo 1040609 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B2347955 : Blo 1040609 2347955 := bstep (se 1 (by rfl) ⟨1760966, by rfl⟩ : syracuseStep 2347955 = 3521933) B3521933
theorem B1561547 : Blo 1040609 1561547 := bstep (se 1 (by rfl) ⟨1171160, by rfl⟩ : syracuseStep 1561547 = 2342321) B2342321
theorem B1561559 : Blo 1040609 1561559 := bstep (se 1 (by rfl) ⟨1171169, by rfl⟩ : syracuseStep 1561559 = 2342339) B2342339
theorem B2347991 : Blo 1040609 2347991 := bstep (se 1 (by rfl) ⟨1760993, by rfl⟩ : syracuseStep 2347991 = 3521987) B3521987
theorem B1561625 : Blo 1040609 1561625 := bstep (se 2 (by rfl) ⟨585609, by rfl⟩ : syracuseStep 1561625 = 1171219) B1171219
theorem B1758233 : Blo 1040609 1758233 := bstep (se 2 (by rfl) ⟨659337, by rfl⟩ : syracuseStep 1758233 = 1318675) B1318675
theorem B2708569 : Blo 1040609 2708569 := bstep (se 2 (by rfl) ⟨1015713, by rfl⟩ : syracuseStep 2708569 = 2031427) B2031427
theorem B1561739 : Blo 1040609 1561739 := bstep (se 1 (by rfl) ⟨1171304, by rfl⟩ : syracuseStep 1561739 = 2342609) B2342609
theorem B2348171 : Blo 1040609 2348171 := bstep (se 1 (by rfl) ⟨1761128, by rfl⟩ : syracuseStep 2348171 = 3522257) B3522257
theorem B1561751 : Blo 1040609 1561751 := bstep (se 1 (by rfl) ⟨1171313, by rfl⟩ : syracuseStep 1561751 = 2342627) B2342627
theorem B1758361 : Blo 1040609 1758361 := bstep (se 2 (by rfl) ⟨659385, by rfl⟩ : syracuseStep 1758361 = 1318771) B1318771
theorem B2348225 : Blo 1040609 2348225 := bstep (se 2 (by rfl) ⟨880584, by rfl⟩ : syracuseStep 2348225 = 1761169) B1761169
theorem B4445387 : Blo 1040609 4445387 := bstep (se 1 (by rfl) ⟨3334040, by rfl⟩ : syracuseStep 4445387 = 6668081) B6668081
theorem B1561817 : Blo 1040609 1561817 := bstep (se 2 (by rfl) ⟨585681, by rfl⟩ : syracuseStep 1561817 = 1171363) B1171363
theorem B7918883 : Blo 1040609 7918883 := bstep (se 1 (by rfl) ⟨5939162, by rfl⟩ : syracuseStep 7918883 = 11878325) B11878325
theorem B1561931 : Blo 1040609 1561931 := bstep (se 1 (by rfl) ⟨1171448, by rfl⟩ : syracuseStep 1561931 = 2342897) B2342897
theorem B1561943 : Blo 1040609 1561943 := bstep (se 1 (by rfl) ⟨1171457, by rfl⟩ : syracuseStep 1561943 = 2342915) B2342915
theorem B1562009 : Blo 1040609 1562009 := bstep (se 2 (by rfl) ⟨585753, by rfl⟩ : syracuseStep 1562009 = 1171507) B1171507
theorem B2348441 : Blo 1040609 2348441 := bstep (se 2 (by rfl) ⟨880665, by rfl⟩ : syracuseStep 2348441 = 1761331) B1761331
theorem B2348531 : Blo 1040609 2348531 := bstep (se 1 (by rfl) ⟨1761398, by rfl⟩ : syracuseStep 2348531 = 3522797) B3522797
theorem B1562123 : Blo 1040609 1562123 := bstep (se 1 (by rfl) ⟨1171592, by rfl⟩ : syracuseStep 1562123 = 2343185) B2343185
theorem B1562135 : Blo 1040609 1562135 := bstep (se 1 (by rfl) ⟨1171601, by rfl⟩ : syracuseStep 1562135 = 2343203) B2343203
theorem B2348567 : Blo 1040609 2348567 := bstep (se 1 (by rfl) ⟨1761425, by rfl⟩ : syracuseStep 2348567 = 3522851) B3522851
theorem B2381363 : Blo 1040609 2381363 := bstep (se 1 (by rfl) ⟨1786022, by rfl⟩ : syracuseStep 2381363 = 3572045) B3572045
theorem B4445761 : Blo 1040609 4445761 := bstep (se 2 (by rfl) ⟨1667160, by rfl⟩ : syracuseStep 4445761 = 3334321) B3334321
theorem B1562201 : Blo 1040609 1562201 := bstep (se 2 (by rfl) ⟨585825, by rfl⟩ : syracuseStep 1562201 = 1171651) B1171651
theorem B1562315 : Blo 1040609 1562315 := bstep (se 1 (by rfl) ⟨1171736, by rfl⟩ : syracuseStep 1562315 = 2343473) B2343473
theorem B2348747 : Blo 1040609 2348747 := bstep (se 1 (by rfl) ⟨1761560, by rfl⟩ : syracuseStep 2348747 = 3523121) B3523121
theorem B1562327 : Blo 1040609 1562327 := bstep (se 1 (by rfl) ⟨1171745, by rfl⟩ : syracuseStep 1562327 = 2343491) B2343491
theorem B1758935 : Blo 1040609 1758935 := bstep (se 1 (by rfl) ⟨1319201, by rfl⟩ : syracuseStep 1758935 = 2638403) B2638403
theorem B27481841 : Blo 1040609 27481841 := bstep (se 2 (by rfl) ⟨10305690, by rfl⟩ : syracuseStep 27481841 = 20611381) B20611381
theorem B2348801 : Blo 1040609 2348801 := bstep (se 2 (by rfl) ⟨880800, by rfl⟩ : syracuseStep 2348801 = 1761601) B1761601
theorem B17815301 : Blo 1040609 17815301 := bstep (se 4 (by rfl) ⟨1670184, by rfl⟩ : syracuseStep 17815301 = 3340369) B3340369
theorem B1562393 : Blo 1040609 1562393 := bstep (se 2 (by rfl) ⟨585897, by rfl⟩ : syracuseStep 1562393 = 1171795) B1171795
theorem B1759063 : Blo 1040609 1759063 := bstep (se 1 (by rfl) ⟨1319297, by rfl⟩ : syracuseStep 1759063 = 2638595) B2638595
theorem B3954521 : Blo 1040609 3954521 := bstep (se 2 (by rfl) ⟨1482945, by rfl⟩ : syracuseStep 3954521 = 2965891) B2965891
theorem B1562507 : Blo 1040609 1562507 := bstep (se 1 (by rfl) ⟨1171880, by rfl⟩ : syracuseStep 1562507 = 2343761) B2343761
theorem B4446103 : Blo 1040609 4446103 := bstep (se 1 (by rfl) ⟨3334577, by rfl⟩ : syracuseStep 4446103 = 6669155) B6669155
theorem B1562519 : Blo 1040609 1562519 := bstep (se 1 (by rfl) ⟨1171889, by rfl⟩ : syracuseStep 1562519 = 2343779) B2343779
theorem B1562585 : Blo 1040609 1562585 := bstep (se 2 (by rfl) ⟨585969, by rfl⟩ : syracuseStep 1562585 = 1171939) B1171939
theorem B2349017 : Blo 1040609 2349017 := bstep (se 2 (by rfl) ⟨880881, by rfl⟩ : syracuseStep 2349017 = 1761763) B1761763
theorem B5003309 : Blo 1040609 5003309 := bstep (se 3 (by rfl) ⟨938120, by rfl⟩ : syracuseStep 5003309 = 1876241) B1876241
theorem B2349107 : Blo 1040609 2349107 := bstep (se 1 (by rfl) ⟨1761830, by rfl⟩ : syracuseStep 2349107 = 3523661) B3523661
theorem B1562699 : Blo 1040609 1562699 := bstep (se 1 (by rfl) ⟨1172024, by rfl⟩ : syracuseStep 1562699 = 2344049) B2344049
theorem B2971723 : Blo 1040609 2971723 := bstep (se 1 (by rfl) ⟨2228792, by rfl⟩ : syracuseStep 2971723 = 4457585) B4457585
theorem B1562711 : Blo 1040609 1562711 := bstep (se 1 (by rfl) ⟨1172033, by rfl⟩ : syracuseStep 1562711 = 2344067) B2344067
theorem B2349143 : Blo 1040609 2349143 := bstep (se 1 (by rfl) ⟨1761857, by rfl⟩ : syracuseStep 2349143 = 3523715) B3523715
theorem B1562777 : Blo 1040609 1562777 := bstep (se 2 (by rfl) ⟨586041, by rfl⟩ : syracuseStep 1562777 = 1172083) B1172083
theorem B1562891 : Blo 1040609 1562891 := bstep (se 1 (by rfl) ⟨1172168, by rfl⟩ : syracuseStep 1562891 = 2344337) B2344337
theorem B2349323 : Blo 1040609 2349323 := bstep (se 1 (by rfl) ⟨1761992, by rfl⟩ : syracuseStep 2349323 = 3523985) B3523985
theorem B1562903 : Blo 1040609 1562903 := bstep (se 1 (by rfl) ⟨1172177, by rfl⟩ : syracuseStep 1562903 = 2344355) B2344355
theorem B2349377 : Blo 1040609 2349377 := bstep (se 2 (by rfl) ⟨881016, by rfl⟩ : syracuseStep 2349377 = 1762033) B1762033
theorem B1562969 : Blo 1040609 1562969 := bstep (se 2 (by rfl) ⟨586113, by rfl⟩ : syracuseStep 1562969 = 1172227) B1172227
theorem B2971997 : Blo 1040609 2971997 := bstep (se 3 (by rfl) ⟨557249, by rfl⟩ : syracuseStep 2971997 = 1114499) B1114499
theorem B1563083 : Blo 1040609 1563083 := bstep (se 1 (by rfl) ⟨1172312, by rfl⟩ : syracuseStep 1563083 = 2344625) B2344625
theorem B1759691 : Blo 1040609 1759691 := bstep (se 1 (by rfl) ⟨1319768, by rfl⟩ : syracuseStep 1759691 = 2639537) B2639537
theorem B1563095 : Blo 1040609 1563095 := bstep (se 1 (by rfl) ⟨1172321, by rfl⟩ : syracuseStep 1563095 = 2344643) B2344643
theorem B4282841 : Blo 1040609 4282841 := bstep (se 2 (by rfl) ⟨1606065, by rfl⟩ : syracuseStep 4282841 = 3212131) B3212131
theorem B1563161 : Blo 1040609 1563161 := bstep (se 2 (by rfl) ⟨586185, by rfl⟩ : syracuseStep 1563161 = 1172371) B1172371
theorem B2349593 : Blo 1040609 2349593 := bstep (se 2 (by rfl) ⟨881097, by rfl⟩ : syracuseStep 2349593 = 1762195) B1762195
theorem B1759819 : Blo 1040609 1759819 := bstep (se 1 (by rfl) ⟨1319864, by rfl⟩ : syracuseStep 1759819 = 2639729) B2639729
theorem B2349683 : Blo 1040609 2349683 := bstep (se 1 (by rfl) ⟨1762262, by rfl⟩ : syracuseStep 2349683 = 3524525) B3524525
theorem B1563275 : Blo 1040609 1563275 := bstep (se 1 (by rfl) ⟨1172456, by rfl⟩ : syracuseStep 1563275 = 2344913) B2344913
theorem B1563287 : Blo 1040609 1563287 := bstep (se 1 (by rfl) ⟨1172465, by rfl⟩ : syracuseStep 1563287 = 2344931) B2344931
theorem B2349719 : Blo 1040609 2349719 := bstep (se 1 (by rfl) ⟨1762289, by rfl⟩ : syracuseStep 2349719 = 3524579) B3524579
theorem B2972339 : Blo 1040609 2972339 := bstep (se 1 (by rfl) ⟨2229254, by rfl⟩ : syracuseStep 2972339 = 4458509) B4458509
theorem B1563353 : Blo 1040609 1563353 := bstep (se 2 (by rfl) ⟨586257, by rfl⟩ : syracuseStep 1563353 = 1172515) B1172515
theorem B1759961 : Blo 1040609 1759961 := bstep (se 2 (by rfl) ⟨659985, by rfl⟩ : syracuseStep 1759961 = 1319971) B1319971
theorem B6773549 : Blo 1040609 6773549 := bstep (se 3 (by rfl) ⟨1270040, by rfl⟩ : syracuseStep 6773549 = 2540081) B2540081
theorem B1563467 : Blo 1040609 1563467 := bstep (se 1 (by rfl) ⟨1172600, by rfl⟩ : syracuseStep 1563467 = 2345201) B2345201
theorem B2349899 : Blo 1040609 2349899 := bstep (se 1 (by rfl) ⟨1762424, by rfl⟩ : syracuseStep 2349899 = 3524849) B3524849
theorem B1563479 : Blo 1040609 1563479 := bstep (se 1 (by rfl) ⟨1172609, by rfl⟩ : syracuseStep 1563479 = 2345219) B2345219
theorem B1760089 : Blo 1040609 1760089 := bstep (se 2 (by rfl) ⟨660033, by rfl⟩ : syracuseStep 1760089 = 1320067) B1320067
theorem B2349953 : Blo 1040609 2349953 := bstep (se 2 (by rfl) ⟨881232, by rfl⟩ : syracuseStep 2349953 = 1762465) B1762465
theorem B1563545 : Blo 1040609 1563545 := bstep (se 2 (by rfl) ⟨586329, by rfl⟩ : syracuseStep 1563545 = 1172659) B1172659
theorem B1563659 : Blo 1040609 1563659 := bstep (se 1 (by rfl) ⟨1172744, by rfl⟩ : syracuseStep 1563659 = 2345489) B2345489
theorem B1563671 : Blo 1040609 1563671 := bstep (se 1 (by rfl) ⟨1172753, by rfl⟩ : syracuseStep 1563671 = 2345507) B2345507
theorem B1563737 : Blo 1040609 1563737 := bstep (se 2 (by rfl) ⟨586401, by rfl⟩ : syracuseStep 1563737 = 1172803) B1172803
theorem B2350169 : Blo 1040609 2350169 := bstep (se 2 (by rfl) ⟨881313, by rfl⟩ : syracuseStep 2350169 = 1762627) B1762627
theorem B2350259 : Blo 1040609 2350259 := bstep (se 1 (by rfl) ⟨1762694, by rfl⟩ : syracuseStep 2350259 = 3525389) B3525389
theorem B1563851 : Blo 1040609 1563851 := bstep (se 1 (by rfl) ⟨1172888, by rfl⟩ : syracuseStep 1563851 = 2345777) B2345777
theorem B1563863 : Blo 1040609 1563863 := bstep (se 1 (by rfl) ⟨1172897, by rfl⟩ : syracuseStep 1563863 = 2345795) B2345795
theorem B2350295 : Blo 1040609 2350295 := bstep (se 1 (by rfl) ⟨1762721, by rfl⟩ : syracuseStep 2350295 = 3525443) B3525443
theorem B1563929 : Blo 1040609 1563929 := bstep (se 2 (by rfl) ⟨586473, by rfl⟩ : syracuseStep 1563929 = 1172947) B1172947
theorem B1564043 : Blo 1040609 1564043 := bstep (se 1 (by rfl) ⟨1173032, by rfl⟩ : syracuseStep 1564043 = 2346065) B2346065
theorem B1564055 : Blo 1040609 1564055 := bstep (se 1 (by rfl) ⟨1173041, by rfl⟩ : syracuseStep 1564055 = 2346083) B2346083
theorem B1760663 : Blo 1040609 1760663 := bstep (se 1 (by rfl) ⟨1320497, by rfl⟩ : syracuseStep 1760663 = 2640995) B2640995
theorem B1170859 : Blo 1040609 1170859 := bstep (se 1 (by rfl) ⟨878144, by rfl⟩ : syracuseStep 1170859 = 1756289) B1756289
theorem B3857843 : Blo 1040609 3857843 := bstep (se 1 (by rfl) ⟨2893382, by rfl⟩ : syracuseStep 3857843 = 5786765) B5786765
theorem B3956147 : Blo 1040609 3956147 := bstep (se 1 (by rfl) ⟨2967110, by rfl⟩ : syracuseStep 3956147 = 5934221) B5934221
theorem B3956161 : Blo 1040609 3956161 := bstep (se 2 (by rfl) ⟨1483560, by rfl⟩ : syracuseStep 3956161 = 2967121) B2967121
theorem B1564121 : Blo 1040609 1564121 := bstep (se 2 (by rfl) ⟨586545, by rfl⟩ : syracuseStep 1564121 = 1173091) B1173091
theorem B1170967 : Blo 1040609 1170967 := bstep (se 1 (by rfl) ⟨878225, by rfl⟩ : syracuseStep 1170967 = 1756451) B1756451
theorem B1760791 : Blo 1040609 1760791 := bstep (se 1 (by rfl) ⟨1320593, by rfl⟩ : syracuseStep 1760791 = 2641187) B2641187
theorem B1564235 : Blo 1040609 1564235 := bstep (se 1 (by rfl) ⟨1173176, by rfl⟩ : syracuseStep 1564235 = 2346353) B2346353
theorem B1564247 : Blo 1040609 1564247 := bstep (se 1 (by rfl) ⟨1173185, by rfl⟩ : syracuseStep 1564247 = 2346371) B2346371
theorem B3759761 : Blo 1040609 3759761 := bstep (se 2 (by rfl) ⟨1409910, by rfl⟩ : syracuseStep 3759761 = 2819821) B2819821
theorem B1564313 : Blo 1040609 1564313 := bstep (se 2 (by rfl) ⟨586617, by rfl⟩ : syracuseStep 1564313 = 1173235) B1173235
theorem B1171147 : Blo 1040609 1171147 := bstep (se 1 (by rfl) ⟨878360, by rfl⟩ : syracuseStep 1171147 = 1756721) B1756721
theorem B1564427 : Blo 1040609 1564427 := bstep (se 1 (by rfl) ⟨1173320, by rfl⟩ : syracuseStep 1564427 = 2346641) B2346641
theorem B1564439 : Blo 1040609 1564439 := bstep (se 1 (by rfl) ⟨1173329, by rfl⟩ : syracuseStep 1564439 = 2346659) B2346659
theorem B1171255 : Blo 1040609 1171255 := bstep (se 1 (by rfl) ⟨878441, by rfl⟩ : syracuseStep 1171255 = 1756883) B1756883
theorem B1564505 : Blo 1040609 1564505 := bstep (se 2 (by rfl) ⟨586689, by rfl⟩ : syracuseStep 1564505 = 1173379) B1173379
theorem B1564619 : Blo 1040609 1564619 := bstep (se 1 (by rfl) ⟨1173464, by rfl⟩ : syracuseStep 1564619 = 2346929) B2346929
theorem B1564631 : Blo 1040609 1564631 := bstep (se 1 (by rfl) ⟨1173473, by rfl⟩ : syracuseStep 1564631 = 2346947) B2346947
theorem B1171435 : Blo 1040609 1171435 := bstep (se 1 (by rfl) ⟨878576, by rfl⟩ : syracuseStep 1171435 = 1757153) B1757153
theorem B1564697 : Blo 1040609 1564697 := bstep (se 2 (by rfl) ⟨586761, by rfl⟩ : syracuseStep 1564697 = 1173523) B1173523
theorem B1171543 : Blo 1040609 1171543 := bstep (se 1 (by rfl) ⟨878657, by rfl⟩ : syracuseStep 1171543 = 1757315) B1757315
theorem B1564811 : Blo 1040609 1564811 := bstep (se 1 (by rfl) ⟨1173608, by rfl⟩ : syracuseStep 1564811 = 2347217) B2347217
theorem B1761419 : Blo 1040609 1761419 := bstep (se 1 (by rfl) ⟨1321064, by rfl⟩ : syracuseStep 1761419 = 2642129) B2642129
theorem B1564823 : Blo 1040609 1564823 := bstep (se 1 (by rfl) ⟨1173617, by rfl⟩ : syracuseStep 1564823 = 2347235) B2347235
theorem B1564889 : Blo 1040609 1564889 := bstep (se 2 (by rfl) ⟨586833, by rfl⟩ : syracuseStep 1564889 = 1173667) B1173667
theorem B1040619 : Blo 1040609 1040619 := bstep (se 1 (by rfl) ⟨780464, by rfl⟩ : syracuseStep 1040619 = 1560929) B1560929
theorem B1040631 : Blo 1040609 1040631 := bstep (se 1 (by rfl) ⟨780473, by rfl⟩ : syracuseStep 1040631 = 1560947) B1560947
theorem B1040651 : Blo 1040609 1040651 := bstep (se 1 (by rfl) ⟨780488, by rfl⟩ : syracuseStep 1040651 = 1560977) B1560977
theorem B1171723 : Blo 1040609 1171723 := bstep (se 1 (by rfl) ⟨878792, by rfl⟩ : syracuseStep 1171723 = 1757585) B1757585
theorem B1761547 : Blo 1040609 1761547 := bstep (se 1 (by rfl) ⟨1321160, by rfl⟩ : syracuseStep 1761547 = 2642321) B2642321
theorem B1040663 : Blo 1040609 1040663 := bstep (se 1 (by rfl) ⟨780497, by rfl⟩ : syracuseStep 1040663 = 1560995) B1560995
theorem B1040683 : Blo 1040609 1040683 := bstep (se 1 (by rfl) ⟨780512, by rfl⟩ : syracuseStep 1040683 = 1561025) B1561025
theorem B1040695 : Blo 1040609 1040695 := bstep (se 1 (by rfl) ⟨780521, by rfl⟩ : syracuseStep 1040695 = 1561043) B1561043
theorem B5005633 : Blo 1040609 5005633 := bstep (se 2 (by rfl) ⟨1877112, by rfl⟩ : syracuseStep 5005633 = 3754225) B3754225
theorem B1040715 : Blo 1040609 1040715 := bstep (se 1 (by rfl) ⟨780536, by rfl⟩ : syracuseStep 1040715 = 1561073) B1561073
theorem B1565003 : Blo 1040609 1565003 := bstep (se 1 (by rfl) ⟨1173752, by rfl⟩ : syracuseStep 1565003 = 2347505) B2347505
theorem B1040727 : Blo 1040609 1040727 := bstep (se 1 (by rfl) ⟨780545, by rfl⟩ : syracuseStep 1040727 = 1561091) B1561091
theorem B1565015 : Blo 1040609 1565015 := bstep (se 1 (by rfl) ⟨1173761, by rfl⟩ : syracuseStep 1565015 = 2347523) B2347523
theorem B1040747 : Blo 1040609 1040747 := bstep (se 1 (by rfl) ⟨780560, by rfl⟩ : syracuseStep 1040747 = 1561121) B1561121
theorem B1040759 : Blo 1040609 1040759 := bstep (se 1 (by rfl) ⟨780569, by rfl⟩ : syracuseStep 1040759 = 1561139) B1561139
theorem B1171831 : Blo 1040609 1171831 := bstep (se 1 (by rfl) ⟨878873, by rfl⟩ : syracuseStep 1171831 = 1757747) B1757747
theorem B1040779 : Blo 1040609 1040779 := bstep (se 1 (by rfl) ⟨780584, by rfl⟩ : syracuseStep 1040779 = 1561169) B1561169
theorem B1040791 : Blo 1040609 1040791 := bstep (se 1 (by rfl) ⟨780593, by rfl⟩ : syracuseStep 1040791 = 1561187) B1561187
theorem B1565081 : Blo 1040609 1565081 := bstep (se 2 (by rfl) ⟨586905, by rfl⟩ : syracuseStep 1565081 = 1173811) B1173811
theorem B1761689 : Blo 1040609 1761689 := bstep (se 2 (by rfl) ⟨660633, by rfl⟩ : syracuseStep 1761689 = 1321267) B1321267
theorem B1040811 : Blo 1040609 1040811 := bstep (se 1 (by rfl) ⟨780608, by rfl⟩ : syracuseStep 1040811 = 1561217) B1561217
theorem B1040823 : Blo 1040609 1040823 := bstep (se 1 (by rfl) ⟨780617, by rfl⟩ : syracuseStep 1040823 = 1561235) B1561235
theorem B1040843 : Blo 1040609 1040843 := bstep (se 1 (by rfl) ⟨780632, by rfl⟩ : syracuseStep 1040843 = 1561265) B1561265
theorem B1040855 : Blo 1040609 1040855 := bstep (se 1 (by rfl) ⟨780641, by rfl⟩ : syracuseStep 1040855 = 1561283) B1561283
theorem B1040875 : Blo 1040609 1040875 := bstep (se 1 (by rfl) ⟨780656, by rfl⟩ : syracuseStep 1040875 = 1561313) B1561313
theorem B1040887 : Blo 1040609 1040887 := bstep (se 1 (by rfl) ⟨780665, by rfl⟩ : syracuseStep 1040887 = 1561331) B1561331
theorem B1040907 : Blo 1040609 1040907 := bstep (se 1 (by rfl) ⟨780680, by rfl⟩ : syracuseStep 1040907 = 1561361) B1561361
theorem B1565195 : Blo 1040609 1565195 := bstep (se 1 (by rfl) ⟨1173896, by rfl⟩ : syracuseStep 1565195 = 2347793) B2347793
theorem B1040919 : Blo 1040609 1040919 := bstep (se 1 (by rfl) ⟨780689, by rfl⟩ : syracuseStep 1040919 = 1561379) B1561379
theorem B1565207 : Blo 1040609 1565207 := bstep (se 1 (by rfl) ⟨1173905, by rfl⟩ : syracuseStep 1565207 = 2347811) B2347811
theorem B1761817 : Blo 1040609 1761817 := bstep (se 2 (by rfl) ⟨660681, by rfl⟩ : syracuseStep 1761817 = 1321363) B1321363
theorem B1040939 : Blo 1040609 1040939 := bstep (se 1 (by rfl) ⟨780704, by rfl⟩ : syracuseStep 1040939 = 1561409) B1561409
theorem B1172011 : Blo 1040609 1172011 := bstep (se 1 (by rfl) ⟨879008, by rfl⟩ : syracuseStep 1172011 = 1758017) B1758017
theorem B1040951 : Blo 1040609 1040951 := bstep (se 1 (by rfl) ⟨780713, by rfl⟩ : syracuseStep 1040951 = 1561427) B1561427
theorem B1040971 : Blo 1040609 1040971 := bstep (se 1 (by rfl) ⟨780728, by rfl⟩ : syracuseStep 1040971 = 1561457) B1561457
theorem B1040983 : Blo 1040609 1040983 := bstep (se 1 (by rfl) ⟨780737, by rfl⟩ : syracuseStep 1040983 = 1561475) B1561475
theorem B1565273 : Blo 1040609 1565273 := bstep (se 2 (by rfl) ⟨586977, by rfl⟩ : syracuseStep 1565273 = 1173955) B1173955
theorem B1041003 : Blo 1040609 1041003 := bstep (se 1 (by rfl) ⟨780752, by rfl⟩ : syracuseStep 1041003 = 1561505) B1561505
theorem B1041015 : Blo 1040609 1041015 := bstep (se 1 (by rfl) ⟨780761, by rfl⟩ : syracuseStep 1041015 = 1561523) B1561523
theorem B1041035 : Blo 1040609 1041035 := bstep (se 1 (by rfl) ⟨780776, by rfl⟩ : syracuseStep 1041035 = 1561553) B1561553
theorem B1041047 : Blo 1040609 1041047 := bstep (se 1 (by rfl) ⟨780785, by rfl⟩ : syracuseStep 1041047 = 1561571) B1561571
theorem B1172119 : Blo 1040609 1172119 := bstep (se 1 (by rfl) ⟨879089, by rfl⟩ : syracuseStep 1172119 = 1758179) B1758179
theorem B1041067 : Blo 1040609 1041067 := bstep (se 1 (by rfl) ⟨780800, by rfl⟩ : syracuseStep 1041067 = 1561601) B1561601
theorem B1041079 : Blo 1040609 1041079 := bstep (se 1 (by rfl) ⟨780809, by rfl⟩ : syracuseStep 1041079 = 1561619) B1561619
theorem B1041099 : Blo 1040609 1041099 := bstep (se 1 (by rfl) ⟨780824, by rfl⟩ : syracuseStep 1041099 = 1561649) B1561649
theorem B1565387 : Blo 1040609 1565387 := bstep (se 1 (by rfl) ⟨1174040, by rfl⟩ : syracuseStep 1565387 = 2348081) B2348081
theorem B2974411 : Blo 1040609 2974411 := bstep (se 1 (by rfl) ⟨2230808, by rfl⟩ : syracuseStep 2974411 = 4461617) B4461617
theorem B1041111 : Blo 1040609 1041111 := bstep (se 1 (by rfl) ⟨780833, by rfl⟩ : syracuseStep 1041111 = 1561667) B1561667
theorem B1565399 : Blo 1040609 1565399 := bstep (se 1 (by rfl) ⟨1174049, by rfl⟩ : syracuseStep 1565399 = 2348099) B2348099
theorem B1041131 : Blo 1040609 1041131 := bstep (se 1 (by rfl) ⟨780848, by rfl⟩ : syracuseStep 1041131 = 1561697) B1561697
theorem B1041143 : Blo 1040609 1041143 := bstep (se 1 (by rfl) ⟨780857, by rfl⟩ : syracuseStep 1041143 = 1561715) B1561715
theorem B15065861 : Blo 1040609 15065861 := bstep (se 4 (by rfl) ⟨1412424, by rfl⟩ : syracuseStep 15065861 = 2824849) B2824849
theorem B1041163 : Blo 1040609 1041163 := bstep (se 1 (by rfl) ⟨780872, by rfl⟩ : syracuseStep 1041163 = 1561745) B1561745
theorem B1041175 : Blo 1040609 1041175 := bstep (se 1 (by rfl) ⟨780881, by rfl⟩ : syracuseStep 1041175 = 1561763) B1561763
theorem B1565465 : Blo 1040609 1565465 := bstep (se 2 (by rfl) ⟨587049, by rfl⟩ : syracuseStep 1565465 = 1174099) B1174099
theorem B1041195 : Blo 1040609 1041195 := bstep (se 1 (by rfl) ⟨780896, by rfl⟩ : syracuseStep 1041195 = 1561793) B1561793
theorem B1041207 : Blo 1040609 1041207 := bstep (se 1 (by rfl) ⟨780905, by rfl⟩ : syracuseStep 1041207 = 1561811) B1561811
theorem B1041227 : Blo 1040609 1041227 := bstep (se 1 (by rfl) ⟨780920, by rfl⟩ : syracuseStep 1041227 = 1561841) B1561841
theorem B1172299 : Blo 1040609 1172299 := bstep (se 1 (by rfl) ⟨879224, by rfl⟩ : syracuseStep 1172299 = 1758449) B1758449
theorem B1041239 : Blo 1040609 1041239 := bstep (se 1 (by rfl) ⟨780929, by rfl⟩ : syracuseStep 1041239 = 1561859) B1561859
theorem B1041259 : Blo 1040609 1041259 := bstep (se 1 (by rfl) ⟨780944, by rfl⟩ : syracuseStep 1041259 = 1561889) B1561889
theorem B1041271 : Blo 1040609 1041271 := bstep (se 1 (by rfl) ⟨780953, by rfl⟩ : syracuseStep 1041271 = 1561907) B1561907
theorem B1041291 : Blo 1040609 1041291 := bstep (se 1 (by rfl) ⟨780968, by rfl⟩ : syracuseStep 1041291 = 1561937) B1561937
theorem B1565579 : Blo 1040609 1565579 := bstep (se 1 (by rfl) ⟨1174184, by rfl⟩ : syracuseStep 1565579 = 2348369) B2348369
theorem B1041303 : Blo 1040609 1041303 := bstep (se 1 (by rfl) ⟨780977, by rfl⟩ : syracuseStep 1041303 = 1561955) B1561955
theorem B1565591 : Blo 1040609 1565591 := bstep (se 1 (by rfl) ⟨1174193, by rfl⟩ : syracuseStep 1565591 = 2348387) B2348387
theorem B1041323 : Blo 1040609 1041323 := bstep (se 1 (by rfl) ⟨780992, by rfl⟩ : syracuseStep 1041323 = 1561985) B1561985
theorem B1041335 : Blo 1040609 1041335 := bstep (se 1 (by rfl) ⟨781001, by rfl⟩ : syracuseStep 1041335 = 1562003) B1562003
theorem B1172407 : Blo 1040609 1172407 := bstep (se 1 (by rfl) ⟨879305, by rfl⟩ : syracuseStep 1172407 = 1758611) B1758611
theorem B1041355 : Blo 1040609 1041355 := bstep (se 1 (by rfl) ⟨781016, by rfl⟩ : syracuseStep 1041355 = 1562033) B1562033
theorem B1041367 : Blo 1040609 1041367 := bstep (se 1 (by rfl) ⟨781025, by rfl⟩ : syracuseStep 1041367 = 1562051) B1562051
theorem B1565657 : Blo 1040609 1565657 := bstep (se 2 (by rfl) ⟨587121, by rfl⟩ : syracuseStep 1565657 = 1174243) B1174243
theorem B1041387 : Blo 1040609 1041387 := bstep (se 1 (by rfl) ⟨781040, by rfl⟩ : syracuseStep 1041387 = 1562081) B1562081
theorem B1041399 : Blo 1040609 1041399 := bstep (se 1 (by rfl) ⟨781049, by rfl⟩ : syracuseStep 1041399 = 1562099) B1562099
theorem B1041419 : Blo 1040609 1041419 := bstep (se 1 (by rfl) ⟨781064, by rfl⟩ : syracuseStep 1041419 = 1562129) B1562129
theorem B1041431 : Blo 1040609 1041431 := bstep (se 1 (by rfl) ⟨781073, by rfl⟩ : syracuseStep 1041431 = 1562147) B1562147
theorem B1041451 : Blo 1040609 1041451 := bstep (se 1 (by rfl) ⟨781088, by rfl⟩ : syracuseStep 1041451 = 1562177) B1562177
theorem B1041463 : Blo 1040609 1041463 := bstep (se 1 (by rfl) ⟨781097, by rfl⟩ : syracuseStep 1041463 = 1562195) B1562195
theorem B1041483 : Blo 1040609 1041483 := bstep (se 1 (by rfl) ⟨781112, by rfl⟩ : syracuseStep 1041483 = 1562225) B1562225
theorem B1565771 : Blo 1040609 1565771 := bstep (se 1 (by rfl) ⟨1174328, by rfl⟩ : syracuseStep 1565771 = 2348657) B2348657
theorem B1041495 : Blo 1040609 1041495 := bstep (se 1 (by rfl) ⟨781121, by rfl⟩ : syracuseStep 1041495 = 1562243) B1562243
theorem B1565783 : Blo 1040609 1565783 := bstep (se 1 (by rfl) ⟨1174337, by rfl⟩ : syracuseStep 1565783 = 2348675) B2348675
theorem B1762391 : Blo 1040609 1762391 := bstep (se 1 (by rfl) ⟨1321793, by rfl⟩ : syracuseStep 1762391 = 2643587) B2643587
theorem B1041515 : Blo 1040609 1041515 := bstep (se 1 (by rfl) ⟨781136, by rfl⟩ : syracuseStep 1041515 = 1562273) B1562273
theorem B1172587 : Blo 1040609 1172587 := bstep (se 1 (by rfl) ⟨879440, by rfl⟩ : syracuseStep 1172587 = 1758881) B1758881
theorem B1041527 : Blo 1040609 1041527 := bstep (se 1 (by rfl) ⟨781145, by rfl⟩ : syracuseStep 1041527 = 1562291) B1562291
theorem B1041547 : Blo 1040609 1041547 := bstep (se 1 (by rfl) ⟨781160, by rfl⟩ : syracuseStep 1041547 = 1562321) B1562321
theorem B1041559 : Blo 1040609 1041559 := bstep (se 1 (by rfl) ⟨781169, by rfl⟩ : syracuseStep 1041559 = 1562339) B1562339
theorem B1565849 : Blo 1040609 1565849 := bstep (se 2 (by rfl) ⟨587193, by rfl⟩ : syracuseStep 1565849 = 1174387) B1174387
theorem B1041579 : Blo 1040609 1041579 := bstep (se 1 (by rfl) ⟨781184, by rfl⟩ : syracuseStep 1041579 = 1562369) B1562369
theorem B1041591 : Blo 1040609 1041591 := bstep (se 1 (by rfl) ⟨781193, by rfl⟩ : syracuseStep 1041591 = 1562387) B1562387
theorem B1041611 : Blo 1040609 1041611 := bstep (se 1 (by rfl) ⟨781208, by rfl⟩ : syracuseStep 1041611 = 1562417) B1562417
theorem B1041623 : Blo 1040609 1041623 := bstep (se 1 (by rfl) ⟨781217, by rfl⟩ : syracuseStep 1041623 = 1562435) B1562435
theorem B1172695 : Blo 1040609 1172695 := bstep (se 1 (by rfl) ⟨879521, by rfl⟩ : syracuseStep 1172695 = 1759043) B1759043
theorem B1762519 : Blo 1040609 1762519 := bstep (se 1 (by rfl) ⟨1321889, by rfl⟩ : syracuseStep 1762519 = 2643779) B2643779
theorem B1041643 : Blo 1040609 1041643 := bstep (se 1 (by rfl) ⟨781232, by rfl⟩ : syracuseStep 1041643 = 1562465) B1562465
theorem B1041655 : Blo 1040609 1041655 := bstep (se 1 (by rfl) ⟨781241, by rfl⟩ : syracuseStep 1041655 = 1562483) B1562483
theorem B8447237 : Blo 1040609 8447237 := bstep (se 4 (by rfl) ⟨791928, by rfl⟩ : syracuseStep 8447237 = 1583857) B1583857
theorem B1041675 : Blo 1040609 1041675 := bstep (se 1 (by rfl) ⟨781256, by rfl⟩ : syracuseStep 1041675 = 1562513) B1562513
theorem B1565963 : Blo 1040609 1565963 := bstep (se 1 (by rfl) ⟨1174472, by rfl⟩ : syracuseStep 1565963 = 2348945) B2348945
theorem B1041687 : Blo 1040609 1041687 := bstep (se 1 (by rfl) ⟨781265, by rfl⟩ : syracuseStep 1041687 = 1562531) B1562531
theorem B1565975 : Blo 1040609 1565975 := bstep (se 1 (by rfl) ⟨1174481, by rfl⟩ : syracuseStep 1565975 = 2348963) B2348963
theorem B1041707 : Blo 1040609 1041707 := bstep (se 1 (by rfl) ⟨781280, by rfl⟩ : syracuseStep 1041707 = 1562561) B1562561
theorem B1041719 : Blo 1040609 1041719 := bstep (se 1 (by rfl) ⟨781289, by rfl⟩ : syracuseStep 1041719 = 1562579) B1562579
theorem B1041739 : Blo 1040609 1041739 := bstep (se 1 (by rfl) ⟨781304, by rfl⟩ : syracuseStep 1041739 = 1562609) B1562609
theorem B3958091 : Blo 1040609 3958091 := bstep (se 1 (by rfl) ⟨2968568, by rfl⟩ : syracuseStep 3958091 = 5937137) B5937137
theorem B1041751 : Blo 1040609 1041751 := bstep (se 1 (by rfl) ⟨781313, by rfl⟩ : syracuseStep 1041751 = 1562627) B1562627
theorem B3958105 : Blo 1040609 3958105 := bstep (se 2 (by rfl) ⟨1484289, by rfl⟩ : syracuseStep 3958105 = 2968579) B2968579
theorem B1566041 : Blo 1040609 1566041 := bstep (se 2 (by rfl) ⟨587265, by rfl⟩ : syracuseStep 1566041 = 1174531) B1174531
theorem B1041771 : Blo 1040609 1041771 := bstep (se 1 (by rfl) ⟨781328, by rfl⟩ : syracuseStep 1041771 = 1562657) B1562657
theorem B1041783 : Blo 1040609 1041783 := bstep (se 1 (by rfl) ⟨781337, by rfl⟩ : syracuseStep 1041783 = 1562675) B1562675
theorem B1041803 : Blo 1040609 1041803 := bstep (se 1 (by rfl) ⟨781352, by rfl⟩ : syracuseStep 1041803 = 1562705) B1562705
theorem B1172875 : Blo 1040609 1172875 := bstep (se 1 (by rfl) ⟨879656, by rfl⟩ : syracuseStep 1172875 = 1759313) B1759313
theorem B5268887 : Blo 1040609 5268887 := bstep (se 1 (by rfl) ⟨3951665, by rfl⟩ : syracuseStep 5268887 = 7903331) B7903331
theorem B1041815 : Blo 1040609 1041815 := bstep (se 1 (by rfl) ⟨781361, by rfl⟩ : syracuseStep 1041815 = 1562723) B1562723
theorem B1041835 : Blo 1040609 1041835 := bstep (se 1 (by rfl) ⟨781376, by rfl⟩ : syracuseStep 1041835 = 1562753) B1562753
theorem B1041847 : Blo 1040609 1041847 := bstep (se 1 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 1041847 = 1562771) B1562771
theorem B1041867 : Blo 1040609 1041867 := bstep (se 1 (by rfl) ⟨781400, by rfl⟩ : syracuseStep 1041867 = 1562801) B1562801
theorem B1566155 : Blo 1040609 1566155 := bstep (se 1 (by rfl) ⟨1174616, by rfl⟩ : syracuseStep 1566155 = 2349233) B2349233
theorem B1041879 : Blo 1040609 1041879 := bstep (se 1 (by rfl) ⟨781409, by rfl⟩ : syracuseStep 1041879 = 1562819) B1562819
theorem B1566167 : Blo 1040609 1566167 := bstep (se 1 (by rfl) ⟨1174625, by rfl⟩ : syracuseStep 1566167 = 2349251) B2349251
theorem B1041899 : Blo 1040609 1041899 := bstep (se 1 (by rfl) ⟨781424, by rfl⟩ : syracuseStep 1041899 = 1562849) B1562849
theorem B1041911 : Blo 1040609 1041911 := bstep (se 1 (by rfl) ⟨781433, by rfl⟩ : syracuseStep 1041911 = 1562867) B1562867
theorem B1172983 : Blo 1040609 1172983 := bstep (se 1 (by rfl) ⟨879737, by rfl⟩ : syracuseStep 1172983 = 1759475) B1759475
theorem B1041931 : Blo 1040609 1041931 := bstep (se 1 (by rfl) ⟨781448, by rfl⟩ : syracuseStep 1041931 = 1562897) B1562897
theorem B1041943 : Blo 1040609 1041943 := bstep (se 1 (by rfl) ⟨781457, by rfl⟩ : syracuseStep 1041943 = 1562915) B1562915
theorem B1566233 : Blo 1040609 1566233 := bstep (se 2 (by rfl) ⟨587337, by rfl⟩ : syracuseStep 1566233 = 1174675) B1174675
theorem B1041963 : Blo 1040609 1041963 := bstep (se 1 (by rfl) ⟨781472, by rfl⟩ : syracuseStep 1041963 = 1562945) B1562945
theorem B1041975 : Blo 1040609 1041975 := bstep (se 1 (by rfl) ⟨781481, by rfl⟩ : syracuseStep 1041975 = 1562963) B1562963
theorem B1041995 : Blo 1040609 1041995 := bstep (se 1 (by rfl) ⟨781496, by rfl⟩ : syracuseStep 1041995 = 1562993) B1562993
theorem B1042007 : Blo 1040609 1042007 := bstep (se 1 (by rfl) ⟨781505, by rfl⟩ : syracuseStep 1042007 = 1563011) B1563011
theorem B1042027 : Blo 1040609 1042027 := bstep (se 1 (by rfl) ⟨781520, by rfl⟩ : syracuseStep 1042027 = 1563041) B1563041
theorem B1042039 : Blo 1040609 1042039 := bstep (se 1 (by rfl) ⟨781529, by rfl⟩ : syracuseStep 1042039 = 1563059) B1563059
theorem B1042059 : Blo 1040609 1042059 := bstep (se 1 (by rfl) ⟨781544, by rfl⟩ : syracuseStep 1042059 = 1563089) B1563089
theorem B1566347 : Blo 1040609 1566347 := bstep (se 1 (by rfl) ⟨1174760, by rfl⟩ : syracuseStep 1566347 = 2349521) B2349521
theorem B1042071 : Blo 1040609 1042071 := bstep (se 1 (by rfl) ⟨781553, by rfl⟩ : syracuseStep 1042071 = 1563107) B1563107
theorem B1566359 : Blo 1040609 1566359 := bstep (se 1 (by rfl) ⟨1174769, by rfl⟩ : syracuseStep 1566359 = 2349539) B2349539
theorem B1042091 : Blo 1040609 1042091 := bstep (se 1 (by rfl) ⟨781568, by rfl⟩ : syracuseStep 1042091 = 1563137) B1563137
theorem B1173163 : Blo 1040609 1173163 := bstep (se 1 (by rfl) ⟨879872, by rfl⟩ : syracuseStep 1173163 = 1759745) B1759745
theorem B1042103 : Blo 1040609 1042103 := bstep (se 1 (by rfl) ⟨781577, by rfl⟩ : syracuseStep 1042103 = 1563155) B1563155
theorem B1042123 : Blo 1040609 1042123 := bstep (se 1 (by rfl) ⟨781592, by rfl⟩ : syracuseStep 1042123 = 1563185) B1563185
theorem B1042135 : Blo 1040609 1042135 := bstep (se 1 (by rfl) ⟨781601, by rfl⟩ : syracuseStep 1042135 = 1563203) B1563203
theorem B1566425 : Blo 1040609 1566425 := bstep (se 2 (by rfl) ⟨587409, by rfl⟩ : syracuseStep 1566425 = 1174819) B1174819
theorem B1042155 : Blo 1040609 1042155 := bstep (se 1 (by rfl) ⟨781616, by rfl⟩ : syracuseStep 1042155 = 1563233) B1563233
theorem B1042167 : Blo 1040609 1042167 := bstep (se 1 (by rfl) ⟨781625, by rfl⟩ : syracuseStep 1042167 = 1563251) B1563251
theorem B1042187 : Blo 1040609 1042187 := bstep (se 1 (by rfl) ⟨781640, by rfl⟩ : syracuseStep 1042187 = 1563281) B1563281
theorem B1042199 : Blo 1040609 1042199 := bstep (se 1 (by rfl) ⟨781649, by rfl⟩ : syracuseStep 1042199 = 1563299) B1563299
theorem B1173271 : Blo 1040609 1173271 := bstep (se 1 (by rfl) ⟨879953, by rfl⟩ : syracuseStep 1173271 = 1759907) B1759907
theorem B1042219 : Blo 1040609 1042219 := bstep (se 1 (by rfl) ⟨781664, by rfl⟩ : syracuseStep 1042219 = 1563329) B1563329
theorem B1042231 : Blo 1040609 1042231 := bstep (se 1 (by rfl) ⟨781673, by rfl⟩ : syracuseStep 1042231 = 1563347) B1563347
theorem B8021825 : Blo 1040609 8021825 := bstep (se 2 (by rfl) ⟨3008184, by rfl⟩ : syracuseStep 8021825 = 6016369) B6016369
theorem B1042251 : Blo 1040609 1042251 := bstep (se 1 (by rfl) ⟨781688, by rfl⟩ : syracuseStep 1042251 = 1563377) B1563377
theorem B1566539 : Blo 1040609 1566539 := bstep (se 1 (by rfl) ⟨1174904, by rfl⟩ : syracuseStep 1566539 = 2349809) B2349809
theorem B1042263 : Blo 1040609 1042263 := bstep (se 1 (by rfl) ⟨781697, by rfl⟩ : syracuseStep 1042263 = 1563395) B1563395
theorem B1566551 : Blo 1040609 1566551 := bstep (se 1 (by rfl) ⟨1174913, by rfl⟩ : syracuseStep 1566551 = 2349827) B2349827
theorem B1042283 : Blo 1040609 1042283 := bstep (se 1 (by rfl) ⟨781712, by rfl⟩ : syracuseStep 1042283 = 1563425) B1563425
theorem B1042295 : Blo 1040609 1042295 := bstep (se 1 (by rfl) ⟨781721, by rfl⟩ : syracuseStep 1042295 = 1563443) B1563443
theorem B1042315 : Blo 1040609 1042315 := bstep (se 1 (by rfl) ⟨781736, by rfl⟩ : syracuseStep 1042315 = 1563473) B1563473
theorem B1042327 : Blo 1040609 1042327 := bstep (se 1 (by rfl) ⟨781745, by rfl⟩ : syracuseStep 1042327 = 1563491) B1563491
theorem B1566617 : Blo 1040609 1566617 := bstep (se 2 (by rfl) ⟨587481, by rfl⟩ : syracuseStep 1566617 = 1174963) B1174963
theorem B1042347 : Blo 1040609 1042347 := bstep (se 1 (by rfl) ⟨781760, by rfl⟩ : syracuseStep 1042347 = 1563521) B1563521
theorem B1042359 : Blo 1040609 1042359 := bstep (se 1 (by rfl) ⟨781769, by rfl⟩ : syracuseStep 1042359 = 1563539) B1563539
theorem B3172289 : Blo 1040609 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B1042379 : Blo 1040609 1042379 := bstep (se 1 (by rfl) ⟨781784, by rfl⟩ : syracuseStep 1042379 = 1563569) B1563569
theorem B1173451 : Blo 1040609 1173451 := bstep (se 1 (by rfl) ⟨880088, by rfl⟩ : syracuseStep 1173451 = 1760177) B1760177
theorem B1042391 : Blo 1040609 1042391 := bstep (se 1 (by rfl) ⟨781793, by rfl⟩ : syracuseStep 1042391 = 1563587) B1563587
theorem B30107609 : Blo 1040609 30107609 := bstep (se 2 (by rfl) ⟨11290353, by rfl⟩ : syracuseStep 30107609 = 22580707) B22580707
theorem B1042411 : Blo 1040609 1042411 := bstep (se 1 (by rfl) ⟨781808, by rfl⟩ : syracuseStep 1042411 = 1563617) B1563617
theorem B1042423 : Blo 1040609 1042423 := bstep (se 1 (by rfl) ⟨781817, by rfl⟩ : syracuseStep 1042423 = 1563635) B1563635
theorem B1042443 : Blo 1040609 1042443 := bstep (se 1 (by rfl) ⟨781832, by rfl⟩ : syracuseStep 1042443 = 1563665) B1563665
theorem B1566731 : Blo 1040609 1566731 := bstep (se 1 (by rfl) ⟨1175048, by rfl⟩ : syracuseStep 1566731 = 2350097) B2350097
theorem B1042455 : Blo 1040609 1042455 := bstep (se 1 (by rfl) ⟨781841, by rfl⟩ : syracuseStep 1042455 = 1563683) B1563683
theorem B1566743 : Blo 1040609 1566743 := bstep (se 1 (by rfl) ⟨1175057, by rfl⟩ : syracuseStep 1566743 = 2350115) B2350115
theorem B1042475 : Blo 1040609 1042475 := bstep (se 1 (by rfl) ⟨781856, by rfl⟩ : syracuseStep 1042475 = 1563713) B1563713
theorem B1042487 : Blo 1040609 1042487 := bstep (se 1 (by rfl) ⟨781865, by rfl⟩ : syracuseStep 1042487 = 1563731) B1563731
theorem B1173559 : Blo 1040609 1173559 := bstep (se 1 (by rfl) ⟨880169, by rfl⟩ : syracuseStep 1173559 = 1760339) B1760339
theorem B1042507 : Blo 1040609 1042507 := bstep (se 1 (by rfl) ⟨781880, by rfl⟩ : syracuseStep 1042507 = 1563761) B1563761
theorem B1042519 : Blo 1040609 1042519 := bstep (se 1 (by rfl) ⟨781889, by rfl⟩ : syracuseStep 1042519 = 1563779) B1563779
theorem B1566809 : Blo 1040609 1566809 := bstep (se 2 (by rfl) ⟨587553, by rfl⟩ : syracuseStep 1566809 = 1175107) B1175107
theorem B1042539 : Blo 1040609 1042539 := bstep (se 1 (by rfl) ⟨781904, by rfl⟩ : syracuseStep 1042539 = 1563809) B1563809
theorem B1042551 : Blo 1040609 1042551 := bstep (se 1 (by rfl) ⟨781913, by rfl⟩ : syracuseStep 1042551 = 1563827) B1563827
theorem B1042571 : Blo 1040609 1042571 := bstep (se 1 (by rfl) ⟨781928, by rfl⟩ : syracuseStep 1042571 = 1563857) B1563857
theorem B1042583 : Blo 1040609 1042583 := bstep (se 1 (by rfl) ⟨781937, by rfl⟩ : syracuseStep 1042583 = 1563875) B1563875
theorem B1042603 : Blo 1040609 1042603 := bstep (se 1 (by rfl) ⟨781952, by rfl⟩ : syracuseStep 1042603 = 1563905) B1563905
theorem B4450477 : Blo 1040609 4450477 := bstep (se 3 (by rfl) ⟨834464, by rfl⟩ : syracuseStep 4450477 = 1668929) B1668929
theorem B1042615 : Blo 1040609 1042615 := bstep (se 1 (by rfl) ⟨781961, by rfl⟩ : syracuseStep 1042615 = 1563923) B1563923
theorem B1042635 : Blo 1040609 1042635 := bstep (se 1 (by rfl) ⟨781976, by rfl⟩ : syracuseStep 1042635 = 1563953) B1563953
theorem B1042647 : Blo 1040609 1042647 := bstep (se 1 (by rfl) ⟨781985, by rfl⟩ : syracuseStep 1042647 = 1563971) B1563971
theorem B1042667 : Blo 1040609 1042667 := bstep (se 1 (by rfl) ⟨782000, by rfl⟩ : syracuseStep 1042667 = 1564001) B1564001
theorem B1173739 : Blo 1040609 1173739 := bstep (se 1 (by rfl) ⟨880304, by rfl⟩ : syracuseStep 1173739 = 1760609) B1760609
theorem B1042679 : Blo 1040609 1042679 := bstep (se 1 (by rfl) ⟨782009, by rfl⟩ : syracuseStep 1042679 = 1564019) B1564019
theorem B1042699 : Blo 1040609 1042699 := bstep (se 1 (by rfl) ⟨782024, by rfl⟩ : syracuseStep 1042699 = 1564049) B1564049
theorem B1042711 : Blo 1040609 1042711 := bstep (se 1 (by rfl) ⟨782033, by rfl⟩ : syracuseStep 1042711 = 1564067) B1564067
theorem B3959063 : Blo 1040609 3959063 := bstep (se 1 (by rfl) ⟨2969297, by rfl⟩ : syracuseStep 3959063 = 5938595) B5938595
theorem B1042731 : Blo 1040609 1042731 := bstep (se 1 (by rfl) ⟨782048, by rfl⟩ : syracuseStep 1042731 = 1564097) B1564097
theorem B1042743 : Blo 1040609 1042743 := bstep (se 1 (by rfl) ⟨782057, by rfl⟩ : syracuseStep 1042743 = 1564115) B1564115
theorem B1042763 : Blo 1040609 1042763 := bstep (se 1 (by rfl) ⟨782072, by rfl⟩ : syracuseStep 1042763 = 1564145) B1564145
theorem B1042775 : Blo 1040609 1042775 := bstep (se 1 (by rfl) ⟨782081, by rfl⟩ : syracuseStep 1042775 = 1564163) B1564163
theorem B1173847 : Blo 1040609 1173847 := bstep (se 1 (by rfl) ⟨880385, by rfl⟩ : syracuseStep 1173847 = 1760771) B1760771
theorem B1042795 : Blo 1040609 1042795 := bstep (se 1 (by rfl) ⟨782096, by rfl⟩ : syracuseStep 1042795 = 1564193) B1564193
theorem B1042807 : Blo 1040609 1042807 := bstep (se 1 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 1042807 = 1564211) B1564211
theorem B1042827 : Blo 1040609 1042827 := bstep (se 1 (by rfl) ⟨782120, by rfl⟩ : syracuseStep 1042827 = 1564241) B1564241
theorem B1042839 : Blo 1040609 1042839 := bstep (se 1 (by rfl) ⟨782129, by rfl⟩ : syracuseStep 1042839 = 1564259) B1564259
theorem B1042859 : Blo 1040609 1042859 := bstep (se 1 (by rfl) ⟨782144, by rfl⟩ : syracuseStep 1042859 = 1564289) B1564289
theorem B1042871 : Blo 1040609 1042871 := bstep (se 1 (by rfl) ⟨782153, by rfl⟩ : syracuseStep 1042871 = 1564307) B1564307
theorem B1042891 : Blo 1040609 1042891 := bstep (se 1 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 1042891 = 1564337) B1564337
theorem B1042903 : Blo 1040609 1042903 := bstep (se 1 (by rfl) ⟨782177, by rfl⟩ : syracuseStep 1042903 = 1564355) B1564355
theorem B1042923 : Blo 1040609 1042923 := bstep (se 1 (by rfl) ⟨782192, by rfl⟩ : syracuseStep 1042923 = 1564385) B1564385
theorem B1042935 : Blo 1040609 1042935 := bstep (se 1 (by rfl) ⟨782201, by rfl⟩ : syracuseStep 1042935 = 1564403) B1564403
theorem B7924229 : Blo 1040609 7924229 := bstep (se 4 (by rfl) ⟨742896, by rfl⟩ : syracuseStep 7924229 = 1485793) B1485793
theorem B1042955 : Blo 1040609 1042955 := bstep (se 1 (by rfl) ⟨782216, by rfl⟩ : syracuseStep 1042955 = 1564433) B1564433
theorem B1174027 : Blo 1040609 1174027 := bstep (se 1 (by rfl) ⟨880520, by rfl⟩ : syracuseStep 1174027 = 1761041) B1761041
theorem B1042967 : Blo 1040609 1042967 := bstep (se 1 (by rfl) ⟨782225, by rfl⟩ : syracuseStep 1042967 = 1564451) B1564451
theorem B1042987 : Blo 1040609 1042987 := bstep (se 1 (by rfl) ⟨782240, by rfl⟩ : syracuseStep 1042987 = 1564481) B1564481
theorem B1042999 : Blo 1040609 1042999 := bstep (se 1 (by rfl) ⟨782249, by rfl⟩ : syracuseStep 1042999 = 1564499) B1564499
theorem B1043019 : Blo 1040609 1043019 := bstep (se 1 (by rfl) ⟨782264, by rfl⟩ : syracuseStep 1043019 = 1564529) B1564529
theorem B1043031 : Blo 1040609 1043031 := bstep (se 1 (by rfl) ⟨782273, by rfl⟩ : syracuseStep 1043031 = 1564547) B1564547
theorem B1043051 : Blo 1040609 1043051 := bstep (se 1 (by rfl) ⟨782288, by rfl⟩ : syracuseStep 1043051 = 1564577) B1564577
theorem B1043063 : Blo 1040609 1043063 := bstep (se 1 (by rfl) ⟨782297, by rfl⟩ : syracuseStep 1043063 = 1564595) B1564595
theorem B1174135 : Blo 1040609 1174135 := bstep (se 1 (by rfl) ⟨880601, by rfl⟩ : syracuseStep 1174135 = 1761203) B1761203
theorem B1043083 : Blo 1040609 1043083 := bstep (se 1 (by rfl) ⟨782312, by rfl⟩ : syracuseStep 1043083 = 1564625) B1564625
theorem B1043095 : Blo 1040609 1043095 := bstep (se 1 (by rfl) ⟨782321, by rfl⟩ : syracuseStep 1043095 = 1564643) B1564643
theorem B1043115 : Blo 1040609 1043115 := bstep (se 1 (by rfl) ⟨782336, by rfl⟩ : syracuseStep 1043115 = 1564673) B1564673
theorem B1043127 : Blo 1040609 1043127 := bstep (se 1 (by rfl) ⟨782345, by rfl⟩ : syracuseStep 1043127 = 1564691) B1564691
theorem B1043147 : Blo 1040609 1043147 := bstep (se 1 (by rfl) ⟨782360, by rfl⟩ : syracuseStep 1043147 = 1564721) B1564721
theorem B1043159 : Blo 1040609 1043159 := bstep (se 1 (by rfl) ⟨782369, by rfl⟩ : syracuseStep 1043159 = 1564739) B1564739
theorem B1043179 : Blo 1040609 1043179 := bstep (se 1 (by rfl) ⟨782384, by rfl⟩ : syracuseStep 1043179 = 1564769) B1564769
theorem B1043191 : Blo 1040609 1043191 := bstep (se 1 (by rfl) ⟨782393, by rfl⟩ : syracuseStep 1043191 = 1564787) B1564787
theorem B1043211 : Blo 1040609 1043211 := bstep (se 1 (by rfl) ⟨782408, by rfl⟩ : syracuseStep 1043211 = 1564817) B1564817
theorem B1043223 : Blo 1040609 1043223 := bstep (se 1 (by rfl) ⟨782417, by rfl⟩ : syracuseStep 1043223 = 1564835) B1564835
theorem B2222873 : Blo 1040609 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B1043243 : Blo 1040609 1043243 := bstep (se 1 (by rfl) ⟨782432, by rfl⟩ : syracuseStep 1043243 = 1564865) B1564865
theorem B1174315 : Blo 1040609 1174315 := bstep (se 1 (by rfl) ⟨880736, by rfl⟩ : syracuseStep 1174315 = 1761473) B1761473
theorem B1043255 : Blo 1040609 1043255 := bstep (se 1 (by rfl) ⟨782441, by rfl⟩ : syracuseStep 1043255 = 1564883) B1564883
theorem B1043275 : Blo 1040609 1043275 := bstep (se 1 (by rfl) ⟨782456, by rfl⟩ : syracuseStep 1043275 = 1564913) B1564913
theorem B1043287 : Blo 1040609 1043287 := bstep (se 1 (by rfl) ⟨782465, by rfl⟩ : syracuseStep 1043287 = 1564931) B1564931
theorem B1043307 : Blo 1040609 1043307 := bstep (se 1 (by rfl) ⟨782480, by rfl⟩ : syracuseStep 1043307 = 1564961) B1564961
theorem B1043319 : Blo 1040609 1043319 := bstep (se 1 (by rfl) ⟨782489, by rfl⟩ : syracuseStep 1043319 = 1564979) B1564979
theorem B1043339 : Blo 1040609 1043339 := bstep (se 1 (by rfl) ⟨782504, by rfl⟩ : syracuseStep 1043339 = 1565009) B1565009
theorem B1043351 : Blo 1040609 1043351 := bstep (se 1 (by rfl) ⟨782513, by rfl⟩ : syracuseStep 1043351 = 1565027) B1565027
theorem B1174423 : Blo 1040609 1174423 := bstep (se 1 (by rfl) ⟨880817, by rfl⟩ : syracuseStep 1174423 = 1761635) B1761635
theorem B1043371 : Blo 1040609 1043371 := bstep (se 1 (by rfl) ⟨782528, by rfl⟩ : syracuseStep 1043371 = 1565057) B1565057
theorem B1043383 : Blo 1040609 1043383 := bstep (se 1 (by rfl) ⟨782537, by rfl⟩ : syracuseStep 1043383 = 1565075) B1565075
theorem B1043403 : Blo 1040609 1043403 := bstep (se 1 (by rfl) ⟨782552, by rfl⟩ : syracuseStep 1043403 = 1565105) B1565105
theorem B1043415 : Blo 1040609 1043415 := bstep (se 1 (by rfl) ⟨782561, by rfl⟩ : syracuseStep 1043415 = 1565123) B1565123
theorem B1043435 : Blo 1040609 1043435 := bstep (se 1 (by rfl) ⟨782576, by rfl⟩ : syracuseStep 1043435 = 1565153) B1565153
theorem B1043447 : Blo 1040609 1043447 := bstep (se 1 (by rfl) ⟨782585, by rfl⟩ : syracuseStep 1043447 = 1565171) B1565171
theorem B1043467 : Blo 1040609 1043467 := bstep (se 1 (by rfl) ⟨782600, by rfl⟩ : syracuseStep 1043467 = 1565201) B1565201
theorem B1043479 : Blo 1040609 1043479 := bstep (se 1 (by rfl) ⟨782609, by rfl⟩ : syracuseStep 1043479 = 1565219) B1565219
theorem B1043499 : Blo 1040609 1043499 := bstep (se 1 (by rfl) ⟨782624, by rfl⟩ : syracuseStep 1043499 = 1565249) B1565249
theorem B1043511 : Blo 1040609 1043511 := bstep (se 1 (by rfl) ⟨782633, by rfl⟩ : syracuseStep 1043511 = 1565267) B1565267
theorem B1043531 : Blo 1040609 1043531 := bstep (se 1 (by rfl) ⟨782648, by rfl⟩ : syracuseStep 1043531 = 1565297) B1565297
theorem B1174603 : Blo 1040609 1174603 := bstep (se 1 (by rfl) ⟨880952, by rfl⟩ : syracuseStep 1174603 = 1761905) B1761905
theorem B1043543 : Blo 1040609 1043543 := bstep (se 1 (by rfl) ⟨782657, by rfl⟩ : syracuseStep 1043543 = 1565315) B1565315
theorem B1043563 : Blo 1040609 1043563 := bstep (se 1 (by rfl) ⟨782672, by rfl⟩ : syracuseStep 1043563 = 1565345) B1565345
theorem B1043575 : Blo 1040609 1043575 := bstep (se 1 (by rfl) ⟨782681, by rfl⟩ : syracuseStep 1043575 = 1565363) B1565363
theorem B1043595 : Blo 1040609 1043595 := bstep (se 1 (by rfl) ⟨782696, by rfl⟩ : syracuseStep 1043595 = 1565393) B1565393
theorem B1043607 : Blo 1040609 1043607 := bstep (se 1 (by rfl) ⟨782705, by rfl⟩ : syracuseStep 1043607 = 1565411) B1565411
theorem B1043627 : Blo 1040609 1043627 := bstep (se 1 (by rfl) ⟨782720, by rfl⟩ : syracuseStep 1043627 = 1565441) B1565441
theorem B2223283 : Blo 1040609 2223283 := bstep (se 1 (by rfl) ⟨1667462, by rfl⟩ : syracuseStep 2223283 = 3334925) B3334925
theorem B1043639 : Blo 1040609 1043639 := bstep (se 1 (by rfl) ⟨782729, by rfl⟩ : syracuseStep 1043639 = 1565459) B1565459
theorem B1174711 : Blo 1040609 1174711 := bstep (se 1 (by rfl) ⟨881033, by rfl⟩ : syracuseStep 1174711 = 1762067) B1762067
theorem B1043659 : Blo 1040609 1043659 := bstep (se 1 (by rfl) ⟨782744, by rfl⟩ : syracuseStep 1043659 = 1565489) B1565489
theorem B1043671 : Blo 1040609 1043671 := bstep (se 1 (by rfl) ⟨782753, by rfl⟩ : syracuseStep 1043671 = 1565507) B1565507
theorem B1043691 : Blo 1040609 1043691 := bstep (se 1 (by rfl) ⟨782768, by rfl⟩ : syracuseStep 1043691 = 1565537) B1565537
theorem B1043703 : Blo 1040609 1043703 := bstep (se 1 (by rfl) ⟨782777, by rfl⟩ : syracuseStep 1043703 = 1565555) B1565555
theorem B1043723 : Blo 1040609 1043723 := bstep (se 1 (by rfl) ⟨782792, by rfl⟩ : syracuseStep 1043723 = 1565585) B1565585
theorem B1043735 : Blo 1040609 1043735 := bstep (se 1 (by rfl) ⟨782801, by rfl⟩ : syracuseStep 1043735 = 1565603) B1565603
theorem B1043755 : Blo 1040609 1043755 := bstep (se 1 (by rfl) ⟨782816, by rfl⟩ : syracuseStep 1043755 = 1565633) B1565633
theorem B1043767 : Blo 1040609 1043767 := bstep (se 1 (by rfl) ⟨782825, by rfl⟩ : syracuseStep 1043767 = 1565651) B1565651
theorem B1043787 : Blo 1040609 1043787 := bstep (se 1 (by rfl) ⟨782840, by rfl⟩ : syracuseStep 1043787 = 1565681) B1565681
theorem B1043799 : Blo 1040609 1043799 := bstep (se 1 (by rfl) ⟨782849, by rfl⟩ : syracuseStep 1043799 = 1565699) B1565699
theorem B1043819 : Blo 1040609 1043819 := bstep (se 1 (by rfl) ⟨782864, by rfl⟩ : syracuseStep 1043819 = 1565729) B1565729
theorem B1174891 : Blo 1040609 1174891 := bstep (se 1 (by rfl) ⟨881168, by rfl⟩ : syracuseStep 1174891 = 1762337) B1762337
theorem B1043831 : Blo 1040609 1043831 := bstep (se 1 (by rfl) ⟨782873, by rfl⟩ : syracuseStep 1043831 = 1565747) B1565747
theorem B1043851 : Blo 1040609 1043851 := bstep (se 1 (by rfl) ⟨782888, by rfl⟩ : syracuseStep 1043851 = 1565777) B1565777
theorem B1043863 : Blo 1040609 1043863 := bstep (se 1 (by rfl) ⟨782897, by rfl⟩ : syracuseStep 1043863 = 1565795) B1565795
theorem B1043883 : Blo 1040609 1043883 := bstep (se 1 (by rfl) ⟨782912, by rfl⟩ : syracuseStep 1043883 = 1565825) B1565825
theorem B1043895 : Blo 1040609 1043895 := bstep (se 1 (by rfl) ⟨782921, by rfl⟩ : syracuseStep 1043895 = 1565843) B1565843
theorem B1043915 : Blo 1040609 1043915 := bstep (se 1 (by rfl) ⟨782936, by rfl⟩ : syracuseStep 1043915 = 1565873) B1565873
theorem B1043927 : Blo 1040609 1043927 := bstep (se 1 (by rfl) ⟨782945, by rfl⟩ : syracuseStep 1043927 = 1565891) B1565891
theorem B1174999 : Blo 1040609 1174999 := bstep (se 1 (by rfl) ⟨881249, by rfl⟩ : syracuseStep 1174999 = 1762499) B1762499
theorem B1043947 : Blo 1040609 1043947 := bstep (se 1 (by rfl) ⟨782960, by rfl⟩ : syracuseStep 1043947 = 1565921) B1565921
theorem B1043959 : Blo 1040609 1043959 := bstep (se 1 (by rfl) ⟨782969, by rfl⟩ : syracuseStep 1043959 = 1565939) B1565939
theorem B3960323 : Blo 1040609 3960323 := bstep (se 1 (by rfl) ⟨2970242, by rfl⟩ : syracuseStep 3960323 = 5940485) B5940485
theorem B1043979 : Blo 1040609 1043979 := bstep (se 1 (by rfl) ⟨782984, by rfl⟩ : syracuseStep 1043979 = 1565969) B1565969
theorem B1043991 : Blo 1040609 1043991 := bstep (se 1 (by rfl) ⟨782993, by rfl⟩ : syracuseStep 1043991 = 1565987) B1565987
theorem B1044011 : Blo 1040609 1044011 := bstep (se 1 (by rfl) ⟨783008, by rfl⟩ : syracuseStep 1044011 = 1566017) B1566017
theorem B1044023 : Blo 1040609 1044023 := bstep (se 1 (by rfl) ⟨783017, by rfl⟩ : syracuseStep 1044023 = 1566035) B1566035
theorem B1044043 : Blo 1040609 1044043 := bstep (se 1 (by rfl) ⟨783032, by rfl⟩ : syracuseStep 1044043 = 1566065) B1566065
theorem B1044055 : Blo 1040609 1044055 := bstep (se 1 (by rfl) ⟨783041, by rfl⟩ : syracuseStep 1044055 = 1566083) B1566083
theorem B1044075 : Blo 1040609 1044075 := bstep (se 1 (by rfl) ⟨783056, by rfl⟩ : syracuseStep 1044075 = 1566113) B1566113
theorem B1044087 : Blo 1040609 1044087 := bstep (se 1 (by rfl) ⟨783065, by rfl⟩ : syracuseStep 1044087 = 1566131) B1566131
theorem B1044107 : Blo 1040609 1044107 := bstep (se 1 (by rfl) ⟨783080, by rfl⟩ : syracuseStep 1044107 = 1566161) B1566161
theorem B1175179 : Blo 1040609 1175179 := bstep (se 1 (by rfl) ⟨881384, by rfl⟩ : syracuseStep 1175179 = 1762769) B1762769
theorem B1044119 : Blo 1040609 1044119 := bstep (se 1 (by rfl) ⟨783089, by rfl⟩ : syracuseStep 1044119 = 1566179) B1566179
theorem B2223769 : Blo 1040609 2223769 := bstep (se 2 (by rfl) ⟨833913, by rfl⟩ : syracuseStep 2223769 = 1667827) B1667827
theorem B1044139 : Blo 1040609 1044139 := bstep (se 1 (by rfl) ⟨783104, by rfl⟩ : syracuseStep 1044139 = 1566209) B1566209
theorem B1044151 : Blo 1040609 1044151 := bstep (se 1 (by rfl) ⟨783113, by rfl⟩ : syracuseStep 1044151 = 1566227) B1566227
theorem B1044171 : Blo 1040609 1044171 := bstep (se 1 (by rfl) ⟨783128, by rfl⟩ : syracuseStep 1044171 = 1566257) B1566257
theorem B1044183 : Blo 1040609 1044183 := bstep (se 1 (by rfl) ⟨783137, by rfl⟩ : syracuseStep 1044183 = 1566275) B1566275
theorem B1044203 : Blo 1040609 1044203 := bstep (se 1 (by rfl) ⟨783152, by rfl⟩ : syracuseStep 1044203 = 1566305) B1566305
theorem B1044215 : Blo 1040609 1044215 := bstep (se 1 (by rfl) ⟨783161, by rfl⟩ : syracuseStep 1044215 = 1566323) B1566323
theorem B1044235 : Blo 1040609 1044235 := bstep (se 1 (by rfl) ⟨783176, by rfl⟩ : syracuseStep 1044235 = 1566353) B1566353
theorem B1044247 : Blo 1040609 1044247 := bstep (se 1 (by rfl) ⟨783185, by rfl⟩ : syracuseStep 1044247 = 1566371) B1566371
theorem B1044267 : Blo 1040609 1044267 := bstep (se 1 (by rfl) ⟨783200, by rfl⟩ : syracuseStep 1044267 = 1566401) B1566401
theorem B1044279 : Blo 1040609 1044279 := bstep (se 1 (by rfl) ⟨783209, by rfl⟩ : syracuseStep 1044279 = 1566419) B1566419
theorem B1044299 : Blo 1040609 1044299 := bstep (se 1 (by rfl) ⟨783224, by rfl⟩ : syracuseStep 1044299 = 1566449) B1566449
theorem B1044311 : Blo 1040609 1044311 := bstep (se 1 (by rfl) ⟨783233, by rfl⟩ : syracuseStep 1044311 = 1566467) B1566467
theorem B4452185 : Blo 1040609 4452185 := bstep (se 2 (by rfl) ⟨1669569, by rfl⟩ : syracuseStep 4452185 = 3339139) B3339139
theorem B1044331 : Blo 1040609 1044331 := bstep (se 1 (by rfl) ⟨783248, by rfl⟩ : syracuseStep 1044331 = 1566497) B1566497
theorem B1044343 : Blo 1040609 1044343 := bstep (se 1 (by rfl) ⟨783257, by rfl⟩ : syracuseStep 1044343 = 1566515) B1566515
theorem B1044363 : Blo 1040609 1044363 := bstep (se 1 (by rfl) ⟨783272, by rfl⟩ : syracuseStep 1044363 = 1566545) B1566545
theorem B1044375 : Blo 1040609 1044375 := bstep (se 1 (by rfl) ⟨783281, by rfl⟩ : syracuseStep 1044375 = 1566563) B1566563
theorem B1044395 : Blo 1040609 1044395 := bstep (se 1 (by rfl) ⟨783296, by rfl⟩ : syracuseStep 1044395 = 1566593) B1566593
theorem B1044407 : Blo 1040609 1044407 := bstep (se 1 (by rfl) ⟨783305, by rfl⟩ : syracuseStep 1044407 = 1566611) B1566611
theorem B1044427 : Blo 1040609 1044427 := bstep (se 1 (by rfl) ⟨783320, by rfl⟩ : syracuseStep 1044427 = 1566641) B1566641
theorem B1044439 : Blo 1040609 1044439 := bstep (se 1 (by rfl) ⟨783329, by rfl⟩ : syracuseStep 1044439 = 1566659) B1566659
theorem B1044459 : Blo 1040609 1044459 := bstep (se 1 (by rfl) ⟨783344, by rfl⟩ : syracuseStep 1044459 = 1566689) B1566689
theorem B1044471 : Blo 1040609 1044471 := bstep (se 1 (by rfl) ⟨783353, by rfl⟩ : syracuseStep 1044471 = 1566707) B1566707
theorem B1044491 : Blo 1040609 1044491 := bstep (se 1 (by rfl) ⟨783368, by rfl⟩ : syracuseStep 1044491 = 1566737) B1566737
theorem B1044503 : Blo 1040609 1044503 := bstep (se 1 (by rfl) ⟨783377, by rfl⟩ : syracuseStep 1044503 = 1566755) B1566755
theorem B1044523 : Blo 1040609 1044523 := bstep (se 1 (by rfl) ⟨783392, by rfl⟩ : syracuseStep 1044523 = 1566785) B1566785
theorem B1044535 : Blo 1040609 1044535 := bstep (se 1 (by rfl) ⟨783401, by rfl⟩ : syracuseStep 1044535 = 1566803) B1566803
theorem B1044555 : Blo 1040609 1044555 := bstep (se 1 (by rfl) ⟨783416, by rfl⟩ : syracuseStep 1044555 = 1566833) B1566833
theorem B1044567 : Blo 1040609 1044567 := bstep (se 1 (by rfl) ⟨783425, by rfl⟩ : syracuseStep 1044567 = 1566851) B1566851
theorem B1044587 : Blo 1040609 1044587 := bstep (se 1 (by rfl) ⟨783440, by rfl⟩ : syracuseStep 1044587 = 1566881) B1566881
theorem B1044599 : Blo 1040609 1044599 := bstep (se 1 (by rfl) ⟨783449, by rfl⟩ : syracuseStep 1044599 = 1566899) B1566899
theorem B2224513 : Blo 1040609 2224513 := bstep (se 2 (by rfl) ⟨834192, by rfl⟩ : syracuseStep 2224513 = 1668385) B1668385
theorem B3174977 : Blo 1040609 3174977 := bstep (se 2 (by rfl) ⟨1190616, by rfl⟩ : syracuseStep 3174977 = 2381233) B2381233
theorem B12678005 : Blo 1040609 12678005 := bstep (se 5 (by rfl) ⟨594281, by rfl⟩ : syracuseStep 12678005 = 1188563) B1188563
theorem B5272451 : Blo 1040609 5272451 := bstep (se 1 (by rfl) ⟨3954338, by rfl⟩ : syracuseStep 5272451 = 7908677) B7908677
theorem B7926659 : Blo 1040609 7926659 := bstep (se 1 (by rfl) ⟨5944994, by rfl⟩ : syracuseStep 7926659 = 11889989) B11889989
theorem B4453451 : Blo 1040609 4453451 := bstep (se 1 (by rfl) ⟨3340088, by rfl⟩ : syracuseStep 4453451 = 6680177) B6680177
theorem B3175499 : Blo 1040609 3175499 := bstep (se 1 (by rfl) ⟨2381624, by rfl⟩ : syracuseStep 3175499 = 4763249) B4763249
theorem B2225495 : Blo 1040609 2225495 := bstep (se 1 (by rfl) ⟨1669121, by rfl⟩ : syracuseStep 2225495 = 3338243) B3338243
theorem B3208627 : Blo 1040609 3208627 := bstep (se 1 (by rfl) ⟨2406470, by rfl⟩ : syracuseStep 3208627 = 4812941) B4812941
theorem B4453811 : Blo 1040609 4453811 := bstep (se 1 (by rfl) ⟨3340358, by rfl⟩ : syracuseStep 4453811 = 6680717) B6680717
theorem B3175901 : Blo 1040609 3175901 := bstep (se 3 (by rfl) ⟨595481, by rfl⟩ : syracuseStep 3175901 = 1190963) B1190963
theorem B1406489 : Blo 1040609 1406489 := bstep (se 2 (by rfl) ⟨527433, by rfl⟩ : syracuseStep 1406489 = 1054867) B1054867
theorem B73266893 : Blo 1040609 73266893 := bstep (se 3 (by rfl) ⟨13737542, by rfl⟩ : syracuseStep 73266893 = 27475085) B27475085
theorem B1111915 : Blo 1040609 1111915 := bstep (se 1 (by rfl) ⟨833936, by rfl⟩ : syracuseStep 1111915 = 1667873) B1667873
theorem B2226059 : Blo 1040609 2226059 := bstep (se 1 (by rfl) ⟨1669544, by rfl⟩ : syracuseStep 2226059 = 3339089) B3339089
theorem B4224919 : Blo 1040609 4224919 := bstep (se 1 (by rfl) ⟨3168689, by rfl⟩ : syracuseStep 4224919 = 6337379) B6337379
theorem B15005827 : Blo 1040609 15005827 := bstep (se 1 (by rfl) ⟨11254370, by rfl⟩ : syracuseStep 15005827 = 22508741) B22508741
theorem B5929139 : Blo 1040609 5929139 := bstep (se 1 (by rfl) ⟨4446854, by rfl⟩ : syracuseStep 5929139 = 8893709) B8893709
theorem B2226521 : Blo 1040609 2226521 := bstep (se 2 (by rfl) ⟨834945, by rfl⟩ : syracuseStep 2226521 = 1669891) B1669891
theorem B8911205 : Blo 1040609 8911205 := bstep (se 4 (by rfl) ⟨835425, by rfl⟩ : syracuseStep 8911205 = 1670851) B1670851
theorem B2259479 : Blo 1040609 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B3963437 : Blo 1040609 3963437 := bstep (se 3 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 3963437 = 1486289) B1486289
theorem B4127383 : Blo 1040609 4127383 := bstep (se 1 (by rfl) ⟨3095537, by rfl⟩ : syracuseStep 4127383 = 6191075) B6191075
theorem B1145707 : Blo 1040609 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B6683609 : Blo 1040609 6683609 := bstep (se 2 (by rfl) ⟨2506353, by rfl⟩ : syracuseStep 6683609 = 5012707) B5012707
theorem B15465485 : Blo 1040609 15465485 := bstep (se 3 (by rfl) ⟨2899778, by rfl⟩ : syracuseStep 15465485 = 5799557) B5799557
theorem B8911889 : Blo 1040609 8911889 := bstep (se 2 (by rfl) ⟨3341958, by rfl⟩ : syracuseStep 8911889 = 6683917) B6683917
theorem B4750609 : Blo 1040609 4750609 := bstep (se 2 (by rfl) ⟨1781478, by rfl⟩ : syracuseStep 4750609 = 3562957) B3562957
theorem B3964211 : Blo 1040609 3964211 := bstep (se 1 (by rfl) ⟨2973158, by rfl⟩ : syracuseStep 3964211 = 5946317) B5946317
theorem B1113431 : Blo 1040609 1113431 := bstep (se 1 (by rfl) ⟨835073, by rfl⟩ : syracuseStep 1113431 = 1670147) B1670147
theorem B2227699 : Blo 1040609 2227699 := bstep (se 1 (by rfl) ⟨1670774, by rfl⟩ : syracuseStep 2227699 = 3341549) B3341549
theorem B1670743 : Blo 1040609 1670743 := bstep (se 1 (by rfl) ⟨1253057, by rfl⟩ : syracuseStep 1670743 = 2506115) B2506115
theorem B5930597 : Blo 1040609 5930597 := bstep (se 4 (by rfl) ⟨555993, by rfl⟩ : syracuseStep 5930597 = 1111987) B1111987
theorem B3211073 : Blo 1040609 3211073 := bstep (se 2 (by rfl) ⟨1204152, by rfl⟩ : syracuseStep 3211073 = 2408305) B2408305
theorem B5013323 : Blo 1040609 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B2228161 : Blo 1040609 2228161 := bstep (se 2 (by rfl) ⟨835560, by rfl⟩ : syracuseStep 2228161 = 1671121) B1671121
theorem B2817995 : Blo 1040609 2817995 := bstep (se 1 (by rfl) ⟨2113496, by rfl⟩ : syracuseStep 2817995 = 4226993) B4226993
theorem B5013515 : Blo 1040609 5013515 := bstep (se 1 (by rfl) ⟨3760136, by rfl⟩ : syracuseStep 5013515 = 7520273) B7520273
theorem B5275691 : Blo 1040609 5275691 := bstep (se 1 (by rfl) ⟨3956768, by rfl⟩ : syracuseStep 5275691 = 7913537) B7913537
theorem B2818091 : Blo 1040609 2818091 := bstep (se 1 (by rfl) ⟨2113568, by rfl⟩ : syracuseStep 2818091 = 4227137) B4227137
theorem B182714737 : Blo 1040609 182714737 := bstep (se 2 (by rfl) ⟨68518026, by rfl⟩ : syracuseStep 182714737 = 137036053) B137036053
theorem B8913665 : Blo 1040609 8913665 := bstep (se 2 (by rfl) ⟨3342624, by rfl⟩ : syracuseStep 8913665 = 6685249) B6685249
theorem B9012005 : Blo 1040609 9012005 := bstep (se 4 (by rfl) ⟨844875, by rfl⟩ : syracuseStep 9012005 = 1689751) B1689751
theorem B3965881 : Blo 1040609 3965881 := bstep (se 2 (by rfl) ⟨1487205, by rfl⟩ : syracuseStep 3965881 = 2974411) B2974411
theorem B2819087 : Blo 1040609 2819087 := bstep (se 1 (by rfl) ⟨2114315, by rfl⟩ : syracuseStep 2819087 = 4228631) B4228631
theorem B5932055 : Blo 1040609 5932055 := bstep (se 1 (by rfl) ⟨4449041, by rfl⟩ : syracuseStep 5932055 = 8898083) B8898083
theorem B4457501 : Blo 1040609 4457501 := bstep (se 3 (by rfl) ⟨835781, by rfl⟩ : syracuseStep 4457501 = 1671563) B1671563
theorem B1410295 : Blo 1040609 1410295 := bstep (se 1 (by rfl) ⟨1057721, by rfl⟩ : syracuseStep 1410295 = 2115443) B2115443
theorem B5276987 : Blo 1040609 5276987 := bstep (se 1 (by rfl) ⟨3957740, by rfl⟩ : syracuseStep 5276987 = 7915481) B7915481
theorem B5277149 : Blo 1040609 5277149 := bstep (se 3 (by rfl) ⟨989465, by rfl⟩ : syracuseStep 5277149 = 1978931) B1978931
theorem B2819585 : Blo 1040609 2819585 := bstep (se 2 (by rfl) ⟨1057344, by rfl⟩ : syracuseStep 2819585 = 2114689) B2114689
theorem B6686327 : Blo 1040609 6686327 := bstep (se 1 (by rfl) ⟨5014745, by rfl⟩ : syracuseStep 6686327 = 10029491) B10029491
theorem B11863745 : Blo 1040609 11863745 := bstep (se 2 (by rfl) ⟨4448904, by rfl⟩ : syracuseStep 11863745 = 8897809) B8897809
theorem B4458185 : Blo 1040609 4458185 := bstep (se 2 (by rfl) ⟨1671819, by rfl⟩ : syracuseStep 4458185 = 3343639) B3343639
theorem B6686479 : Blo 1040609 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B5277473 : Blo 1040609 5277473 := bstep (se 2 (by rfl) ⟨1979052, by rfl⟩ : syracuseStep 5277473 = 3958105) B3958105
theorem B2230391 : Blo 1040609 2230391 := bstep (se 1 (by rfl) ⟨1672793, by rfl⟩ : syracuseStep 2230391 = 3345587) B3345587
theorem B1411273 : Blo 1040609 1411273 := bstep (se 2 (by rfl) ⟨529227, by rfl⟩ : syracuseStep 1411273 = 1058455) B1058455
theorem B1411447 : Blo 1040609 1411447 := bstep (se 1 (by rfl) ⟨1058585, by rfl⟩ : syracuseStep 1411447 = 2117171) B2117171
theorem B57117149 : Blo 1040609 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B2230843 : Blo 1040609 2230843 := bstep (se 1 (by rfl) ⟨1673132, by rfl⟩ : syracuseStep 2230843 = 3346265) B3346265
theorem B6687299 : Blo 1040609 6687299 := bstep (se 1 (by rfl) ⟨5015474, by rfl⟩ : syracuseStep 6687299 = 10030949) B10030949
theorem B5278445 : Blo 1040609 5278445 := bstep (se 3 (by rfl) ⟨989708, by rfl⟩ : syracuseStep 5278445 = 1979417) B1979417
theorem B5933969 : Blo 1040609 5933969 := bstep (se 2 (by rfl) ⟨2225238, by rfl⟩ : syracuseStep 5933969 = 4450477) B4450477
theorem B12684235 : Blo 1040609 12684235 := bstep (se 1 (by rfl) ⟨9513176, by rfl⟩ : syracuseStep 12684235 = 19026353) B19026353
theorem B10030027 : Blo 1040609 10030027 := bstep (se 1 (by rfl) ⟨7522520, by rfl⟩ : syracuseStep 10030027 = 15045041) B15045041
theorem B4459961 : Blo 1040609 4459961 := bstep (se 2 (by rfl) ⟨1672485, by rfl⟩ : syracuseStep 4459961 = 3344971) B3344971
theorem B5279255 : Blo 1040609 5279255 := bstep (se 1 (by rfl) ⟨3959441, by rfl⟩ : syracuseStep 5279255 = 7918883) B7918883
theorem B5934653 : Blo 1040609 5934653 := bstep (se 3 (by rfl) ⟨1112747, by rfl⟩ : syracuseStep 5934653 = 2225495) B2225495
theorem B18321227 : Blo 1040609 18321227 := bstep (se 1 (by rfl) ⟨13740920, by rfl⟩ : syracuseStep 18321227 = 27481841) B27481841
theorem B2036267 : Blo 1040609 2036267 := bstep (se 1 (by rfl) ⟨1527200, by rfl⟩ : syracuseStep 2036267 = 3054401) B3054401
theorem B5640941 : Blo 1040609 5640941 := bstep (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) B2115353
theorem B8918039 : Blo 1040609 8918039 := bstep (se 1 (by rfl) ⟨6688529, by rfl⟩ : syracuseStep 8918039 = 13377059) B13377059
theorem B8459437 : Blo 1040609 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B6689965 : Blo 1040609 6689965 := bstep (se 3 (by rfl) ⟨1254368, by rfl⟩ : syracuseStep 6689965 = 2508737) B2508737
theorem B4461959 : Blo 1040609 4461959 := bstep (se 1 (by rfl) ⟨3346469, by rfl⟩ : syracuseStep 4461959 = 6692939) B6692939
theorem B13342157 : Blo 1040609 13342157 := bstep (se 3 (by rfl) ⟨2501654, by rfl⟩ : syracuseStep 13342157 = 5003309) B5003309
theorem B3512591 : Blo 1040609 3512591 := bstep (se 1 (by rfl) ⟨2634443, by rfl⟩ : syracuseStep 3512591 = 5268887) B5268887
theorem B3512861 : Blo 1040609 3512861 := bstep (se 3 (by rfl) ⟨658661, by rfl⟩ : syracuseStep 3512861 = 1317323) B1317323
theorem B5282333 : Blo 1040609 5282333 := bstep (se 3 (by rfl) ⟨990437, by rfl⟩ : syracuseStep 5282333 = 1980875) B1980875
theorem B5347883 : Blo 1040609 5347883 := bstep (se 1 (by rfl) ⟨4010912, by rfl⟩ : syracuseStep 5347883 = 8021825) B8021825
theorem B11279027 : Blo 1040609 11279027 := bstep (se 1 (by rfl) ⟨8459270, by rfl⟩ : syracuseStep 11279027 = 16918541) B16918541
theorem B1317647 : Blo 1040609 1317647 := bstep (se 1 (by rfl) ⟨988235, by rfl⟩ : syracuseStep 1317647 = 1976471) B1976471
theorem B1252111 : Blo 1040609 1252111 := bstep (se 1 (by rfl) ⟨939083, by rfl⟩ : syracuseStep 1252111 = 1878167) B1878167
theorem B5282819 : Blo 1040609 5282819 := bstep (se 1 (by rfl) ⟨3962114, by rfl⟩ : syracuseStep 5282819 = 7924229) B7924229
theorem B1481915 : Blo 1040609 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B18062797 : Blo 1040609 18062797 := bstep (se 3 (by rfl) ⟨3386774, by rfl⟩ : syracuseStep 18062797 = 6773549) B6773549
theorem B6332141 : Blo 1040609 6332141 := bstep (se 3 (by rfl) ⟨1187276, by rfl⟩ : syracuseStep 6332141 = 2374553) B2374553
theorem B1482553 : Blo 1040609 1482553 := bstep (se 2 (by rfl) ⟨555957, by rfl⟩ : syracuseStep 1482553 = 1111915) B1111915
theorem B3514265 : Blo 1040609 3514265 := bstep (se 2 (by rfl) ⟨1317849, by rfl⟩ : syracuseStep 3514265 = 2635699) B2635699
theorem B160702517 : Blo 1040609 160702517 := bstep (se 5 (by rfl) ⟨7532930, by rfl⟩ : syracuseStep 160702517 = 15065861) B15065861
theorem B20029913 : Blo 1040609 20029913 := bstep (se 2 (by rfl) ⟨7511217, by rfl⟩ : syracuseStep 20029913 = 15022435) B15022435
theorem B3514967 : Blo 1040609 3514967 := bstep (se 1 (by rfl) ⟨2636225, by rfl⟩ : syracuseStep 3514967 = 5272451) B5272451
theorem B5284439 : Blo 1040609 5284439 := bstep (se 1 (by rfl) ⟨3963329, by rfl⟩ : syracuseStep 5284439 = 7926659) B7926659
theorem B1254407 : Blo 1040609 1254407 := bstep (se 1 (by rfl) ⟨940805, by rfl⟩ : syracuseStep 1254407 = 1881611) B1881611
theorem B3515453 : Blo 1040609 3515453 := bstep (se 3 (by rfl) ⟨659147, by rfl⟩ : syracuseStep 3515453 = 1318295) B1318295
theorem B5284925 : Blo 1040609 5284925 := bstep (se 3 (by rfl) ⟨990923, by rfl⟩ : syracuseStep 5284925 = 1981847) B1981847
theorem B1484039 : Blo 1040609 1484039 := bstep (se 1 (by rfl) ⟨1113029, by rfl⟩ : syracuseStep 1484039 = 2226059) B2226059
theorem B11412829 : Blo 1040609 11412829 := bstep (se 3 (by rfl) ⟨2139905, by rfl⟩ : syracuseStep 11412829 = 4279811) B4279811
theorem B1484347 : Blo 1040609 1484347 := bstep (se 1 (by rfl) ⟨1113260, by rfl⟩ : syracuseStep 1484347 = 2226521) B2226521
theorem B5940803 : Blo 1040609 5940803 := bstep (se 1 (by rfl) ⟨4455602, by rfl⟩ : syracuseStep 5940803 = 8911205) B8911205
theorem B1320619 : Blo 1040609 1320619 := bstep (se 1 (by rfl) ⟨990464, by rfl⟩ : syracuseStep 1320619 = 1980929) B1980929
theorem B6334145 : Blo 1040609 6334145 := bstep (se 2 (by rfl) ⟨2375304, by rfl⟩ : syracuseStep 6334145 = 4750609) B4750609
theorem B5941259 : Blo 1040609 5941259 := bstep (se 1 (by rfl) ⟨4455944, by rfl⟩ : syracuseStep 5941259 = 8911889) B8911889
theorem B5351453 : Blo 1040609 5351453 := bstep (se 3 (by rfl) ⟨1003397, by rfl⟩ : syracuseStep 5351453 = 2006795) B2006795
theorem B1583147 : Blo 1040609 1583147 := bstep (se 1 (by rfl) ⟨1187360, by rfl⟩ : syracuseStep 1583147 = 2374721) B2374721
theorem B11872493 : Blo 1040609 11872493 := bstep (se 3 (by rfl) ⟨2226092, by rfl⟩ : syracuseStep 11872493 = 4452185) B4452185
theorem B3516857 : Blo 1040609 3516857 := bstep (se 2 (by rfl) ⟨1318821, by rfl⟩ : syracuseStep 3516857 = 2637643) B2637643
theorem B7514653 : Blo 1040609 7514653 := bstep (se 3 (by rfl) ⟨1408997, by rfl⟩ : syracuseStep 7514653 = 2817995) B2817995
theorem B2140715 : Blo 1040609 2140715 := bstep (se 1 (by rfl) ⟨1605536, by rfl⟩ : syracuseStep 2140715 = 3211073) B3211073
theorem B1321591 : Blo 1040609 1321591 := bstep (se 1 (by rfl) ⟨991193, by rfl⟩ : syracuseStep 1321591 = 1982387) B1982387
theorem B1190543 : Blo 1040609 1190543 := bstep (se 1 (by rfl) ⟨892907, by rfl⟩ : syracuseStep 1190543 = 1785815) B1785815
theorem B1485497 : Blo 1040609 1485497 := bstep (se 2 (by rfl) ⟨557061, by rfl⟩ : syracuseStep 1485497 = 1114123) B1114123
theorem B25340633 : Blo 1040609 25340633 := bstep (se 2 (by rfl) ⟨9502737, by rfl⟩ : syracuseStep 25340633 = 19005475) B19005475
theorem B5286707 : Blo 1040609 5286707 := bstep (se 1 (by rfl) ⟨3965030, by rfl⟩ : syracuseStep 5286707 = 7930061) B7930061
theorem B1977223 : Blo 1040609 1977223 := bstep (se 1 (by rfl) ⟨1482917, by rfl⟩ : syracuseStep 1977223 = 2965835) B2965835
theorem B1321915 : Blo 1040609 1321915 := bstep (se 1 (by rfl) ⟨991436, by rfl⟩ : syracuseStep 1321915 = 1982873) B1982873
theorem B3517451 : Blo 1040609 3517451 := bstep (se 1 (by rfl) ⟨2638088, by rfl⟩ : syracuseStep 3517451 = 5276177) B5276177
theorem B2540842019 : Blo 1040609 2540842019 := bstep (se 1 (by rfl) ⟨1905631514, by rfl⟩ : syracuseStep 2540842019 = 3811263029) B3811263029
theorem B3517559 : Blo 1040609 3517559 := bstep (se 1 (by rfl) ⟨2638169, by rfl⟩ : syracuseStep 3517559 = 5276339) B5276339
theorem B5287031 : Blo 1040609 5287031 := bstep (se 1 (by rfl) ⟨3965273, by rfl⟩ : syracuseStep 5287031 = 7930547) B7930547
theorem B45165923 : Blo 1040609 45165923 := bstep (se 1 (by rfl) ⟨33874442, by rfl⟩ : syracuseStep 45165923 = 67748885) B67748885
theorem B8891795 : Blo 1040609 8891795 := bstep (se 1 (by rfl) ⟨6668846, by rfl⟩ : syracuseStep 8891795 = 13337693) B13337693
theorem B6335891 : Blo 1040609 6335891 := bstep (se 1 (by rfl) ⟨4751918, by rfl⟩ : syracuseStep 6335891 = 9503837) B9503837
theorem B1584569 : Blo 1040609 1584569 := bstep (se 2 (by rfl) ⟨594213, by rfl⟩ : syracuseStep 1584569 = 1188427) B1188427
theorem B10006193 : Blo 1040609 10006193 := bstep (se 2 (by rfl) ⟨3752322, by rfl⟩ : syracuseStep 10006193 = 7504645) B7504645
theorem B3518153 : Blo 1040609 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B21376817 : Blo 1040609 21376817 := bstep (se 2 (by rfl) ⟨8016306, by rfl⟩ : syracuseStep 21376817 = 16032613) B16032613
theorem B5288003 : Blo 1040609 5288003 := bstep (se 1 (by rfl) ⟨3966002, by rfl⟩ : syracuseStep 5288003 = 7932005) B7932005
theorem B1585225 : Blo 1040609 1585225 := bstep (se 2 (by rfl) ⟨594459, by rfl⟩ : syracuseStep 1585225 = 1188919) B1188919
theorem B2502809 : Blo 1040609 2502809 := bstep (se 2 (by rfl) ⟨938553, by rfl⟩ : syracuseStep 2502809 = 1877107) B1877107
theorem B8466605 : Blo 1040609 8466605 := bstep (se 3 (by rfl) ⟨1587488, by rfl⟩ : syracuseStep 8466605 = 3174977) B3174977
theorem B1487035 : Blo 1040609 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B2502971 : Blo 1040609 2502971 := bstep (se 1 (by rfl) ⟨1877228, by rfl⟩ : syracuseStep 2502971 = 3754457) B3754457
theorem B3518855 : Blo 1040609 3518855 := bstep (se 1 (by rfl) ⟨2639141, by rfl⟩ : syracuseStep 3518855 = 5278283) B5278283
theorem B5288327 : Blo 1040609 5288327 := bstep (se 1 (by rfl) ⟨3966245, by rfl⟩ : syracuseStep 5288327 = 7932491) B7932491
theorem B1978825 : Blo 1040609 1978825 := bstep (se 2 (by rfl) ⟨742059, by rfl⟩ : syracuseStep 1978825 = 1484119) B1484119
theorem B2634241 : Blo 1040609 2634241 := bstep (se 2 (by rfl) ⟨987840, by rfl⟩ : syracuseStep 2634241 = 1975681) B1975681
theorem B1880761 : Blo 1040609 1880761 := bstep (se 2 (by rfl) ⟨705285, by rfl⟩ : syracuseStep 1880761 = 1410571) B1410571
theorem B3519233 : Blo 1040609 3519233 := bstep (se 2 (by rfl) ⟨1319712, by rfl⟩ : syracuseStep 3519233 = 2639425) B2639425
theorem B10007347 : Blo 1040609 10007347 := bstep (se 1 (by rfl) ⟨7505510, by rfl⟩ : syracuseStep 10007347 = 15011021) B15011021
theorem B1880891 : Blo 1040609 1880891 := bstep (se 1 (by rfl) ⟨1410668, by rfl⟩ : syracuseStep 1880891 = 2821337) B2821337
theorem B1782827 : Blo 1040609 1782827 := bstep (se 1 (by rfl) ⟨1337120, by rfl⟩ : syracuseStep 1782827 = 2674241) B2674241
theorem B5715011 : Blo 1040609 5715011 := bstep (se 1 (by rfl) ⟨4286258, by rfl⟩ : syracuseStep 5715011 = 8572517) B8572517
theorem B2634839 : Blo 1040609 2634839 := bstep (se 1 (by rfl) ⟨1976129, by rfl⟩ : syracuseStep 2634839 = 3952259) B3952259
theorem B2635051 : Blo 1040609 2635051 := bstep (se 1 (by rfl) ⟨1976288, by rfl⟩ : syracuseStep 2635051 = 3952577) B3952577
theorem B2635193 : Blo 1040609 2635193 := bstep (se 2 (by rfl) ⟨988197, by rfl⟩ : syracuseStep 2635193 = 1976395) B1976395
theorem B3520043 : Blo 1040609 3520043 := bstep (se 1 (by rfl) ⟨2640032, by rfl⟩ : syracuseStep 3520043 = 5280065) B5280065
theorem B1881785 : Blo 1040609 1881785 := bstep (se 2 (by rfl) ⟨705669, by rfl⟩ : syracuseStep 1881785 = 1411339) B1411339
theorem B9647923 : Blo 1040609 9647923 := bstep (se 1 (by rfl) ⟨7235942, by rfl⟩ : syracuseStep 9647923 = 14471885) B14471885
theorem B5945177 : Blo 1040609 5945177 := bstep (se 2 (by rfl) ⟨2229441, by rfl⟩ : syracuseStep 5945177 = 4458883) B4458883
theorem B2963591 : Blo 1040609 2963591 := bstep (se 1 (by rfl) ⟨2222693, by rfl⟩ : syracuseStep 2963591 = 4445387) B4445387
theorem B5945633 : Blo 1040609 5945633 := bstep (se 2 (by rfl) ⟨2229612, by rfl⟩ : syracuseStep 5945633 = 4459225) B4459225
theorem B1587575 : Blo 1040609 1587575 := bstep (se 1 (by rfl) ⟨1190681, by rfl⟩ : syracuseStep 1587575 = 2381363) B2381363
theorem B7518599 : Blo 1040609 7518599 := bstep (se 1 (by rfl) ⟨5638949, by rfl⟩ : syracuseStep 7518599 = 11277899) B11277899
theorem B2636185 : Blo 1040609 2636185 := bstep (se 2 (by rfl) ⟨988569, by rfl⟩ : syracuseStep 2636185 = 1977139) B1977139
theorem B11876867 : Blo 1040609 11876867 := bstep (se 1 (by rfl) ⟨8907650, by rfl⟩ : syracuseStep 11876867 = 17815301) B17815301
theorem B5945885 : Blo 1040609 5945885 := bstep (se 3 (by rfl) ⟨1114853, by rfl⟩ : syracuseStep 5945885 = 2229707) B2229707
theorem B2636347 : Blo 1040609 2636347 := bstep (se 1 (by rfl) ⟨1977260, by rfl⟩ : syracuseStep 2636347 = 3954521) B3954521
theorem B2341511 : Blo 1040609 2341511 := bstep (se 1 (by rfl) ⟨1756133, by rfl⟩ : syracuseStep 2341511 = 3512267) B3512267
theorem B2636489 : Blo 1040609 2636489 := bstep (se 2 (by rfl) ⟨988683, by rfl⟩ : syracuseStep 2636489 = 1977367) B1977367
theorem B3750637 : Blo 1040609 3750637 := bstep (se 3 (by rfl) ⟨703244, by rfl⟩ : syracuseStep 3750637 = 1406489) B1406489
theorem B2341691 : Blo 1040609 2341691 := bstep (se 1 (by rfl) ⟨1756268, by rfl⟩ : syracuseStep 2341691 = 3512537) B3512537
theorem B3521339 : Blo 1040609 3521339 := bstep (se 1 (by rfl) ⟨2641004, by rfl⟩ : syracuseStep 3521339 = 5282009) B5282009
theorem B1981331 : Blo 1040609 1981331 := bstep (se 1 (by rfl) ⟨1485998, by rfl⟩ : syracuseStep 1981331 = 2971997) B2971997
theorem B2964377 : Blo 1040609 2964377 := bstep (se 2 (by rfl) ⟨1111641, by rfl⟩ : syracuseStep 2964377 = 2223283) B2223283
theorem B2341817 : Blo 1040609 2341817 := bstep (se 2 (by rfl) ⟨878181, by rfl⟩ : syracuseStep 2341817 = 1756363) B1756363
theorem B2636833 : Blo 1040609 2636833 := bstep (se 2 (by rfl) ⟨988812, by rfl⟩ : syracuseStep 2636833 = 1977625) B1977625
theorem B1981559 : Blo 1040609 1981559 := bstep (se 1 (by rfl) ⟨1486169, by rfl⟩ : syracuseStep 1981559 = 2972339) B2972339
theorem B6110437 : Blo 1040609 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B2342159 : Blo 1040609 2342159 := bstep (se 1 (by rfl) ⟨1756619, by rfl⟩ : syracuseStep 2342159 = 3513239) B3513239
theorem B2342177 : Blo 1040609 2342177 := bstep (se 2 (by rfl) ⟨878316, by rfl⟩ : syracuseStep 2342177 = 1756633) B1756633
theorem B3521825 : Blo 1040609 3521825 := bstep (se 2 (by rfl) ⟨1320684, by rfl⟩ : syracuseStep 3521825 = 2641369) B2641369
theorem B2965025 : Blo 1040609 2965025 := bstep (se 2 (by rfl) ⟨1111884, by rfl⟩ : syracuseStep 2965025 = 2223769) B2223769
theorem B2342519 : Blo 1040609 2342519 := bstep (se 1 (by rfl) ⟨1756889, by rfl⟩ : syracuseStep 2342519 = 3513779) B3513779
theorem B2571895 : Blo 1040609 2571895 := bstep (se 1 (by rfl) ⟨1928921, by rfl⟩ : syracuseStep 2571895 = 3857843) B3857843
theorem B2637431 : Blo 1040609 2637431 := bstep (se 1 (by rfl) ⟨1978073, by rfl⟩ : syracuseStep 2637431 = 3956147) B3956147
theorem B2506393 : Blo 1040609 2506393 := bstep (se 2 (by rfl) ⟨939897, by rfl⟩ : syracuseStep 2506393 = 1879795) B1879795
theorem B2506507 : Blo 1040609 2506507 := bstep (se 1 (by rfl) ⟨1879880, by rfl⟩ : syracuseStep 2506507 = 3759761) B3759761
theorem B2342699 : Blo 1040609 2342699 := bstep (se 1 (by rfl) ⟨1757024, by rfl⟩ : syracuseStep 2342699 = 3514049) B3514049
theorem B3522419 : Blo 1040609 3522419 := bstep (se 1 (by rfl) ⟨2641814, by rfl⟩ : syracuseStep 3522419 = 5283629) B5283629
theorem B11255755 : Blo 1040609 11255755 := bstep (se 1 (by rfl) ⟨8441816, by rfl⟩ : syracuseStep 11255755 = 16883633) B16883633
theorem B2670635 : Blo 1040609 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B2343059 : Blo 1040609 2343059 := bstep (se 1 (by rfl) ⟨1757294, by rfl⟩ : syracuseStep 2343059 = 3514589) B3514589
theorem B2343113 : Blo 1040609 2343113 := bstep (se 2 (by rfl) ⟨878667, by rfl⟩ : syracuseStep 2343113 = 1757335) B1757335
theorem B5423545 : Blo 1040609 5423545 := bstep (se 2 (by rfl) ⟨2033829, by rfl⟩ : syracuseStep 5423545 = 4067659) B4067659
theorem B2966017 : Blo 1040609 2966017 := bstep (se 2 (by rfl) ⟨1112256, by rfl⟩ : syracuseStep 2966017 = 2224513) B2224513
theorem B5948275 : Blo 1040609 5948275 := bstep (se 1 (by rfl) ⟨4461206, by rfl⟩ : syracuseStep 5948275 = 8922413) B8922413
theorem B2343815 : Blo 1040609 2343815 := bstep (se 1 (by rfl) ⟨1757861, by rfl⟩ : syracuseStep 2343815 = 3515723) B3515723
theorem B2638727 : Blo 1040609 2638727 := bstep (se 1 (by rfl) ⟨1979045, by rfl⟩ : syracuseStep 2638727 = 3958091) B3958091
theorem B2638777 : Blo 1040609 2638777 := bstep (se 2 (by rfl) ⟨989541, by rfl⟩ : syracuseStep 2638777 = 1979083) B1979083
theorem B2343995 : Blo 1040609 2343995 := bstep (se 1 (by rfl) ⟨1757996, by rfl⟩ : syracuseStep 2343995 = 3515993) B3515993
theorem B2344121 : Blo 1040609 2344121 := bstep (se 2 (by rfl) ⟨879045, by rfl⟩ : syracuseStep 2344121 = 1758091) B1758091
theorem B11420909 : Blo 1040609 11420909 := bstep (se 3 (by rfl) ⟨2141420, by rfl⟩ : syracuseStep 11420909 = 4282841) B4282841
theorem B20071739 : Blo 1040609 20071739 := bstep (se 1 (by rfl) ⟨15053804, by rfl⟩ : syracuseStep 20071739 = 30107609) B30107609
theorem B2344463 : Blo 1040609 2344463 := bstep (se 1 (by rfl) ⟨1758347, by rfl⟩ : syracuseStep 2344463 = 3516695) B3516695
theorem B2639375 : Blo 1040609 2639375 := bstep (se 1 (by rfl) ⟨1979531, by rfl⟩ : syracuseStep 2639375 = 3959063) B3959063
theorem B2344481 : Blo 1040609 2344481 := bstep (se 2 (by rfl) ⟨879180, by rfl⟩ : syracuseStep 2344481 = 1758361) B1758361
theorem B32097869 : Blo 1040609 32097869 := bstep (se 3 (by rfl) ⟨6018350, by rfl⟩ : syracuseStep 32097869 = 12036701) B12036701
theorem B6342437 : Blo 1040609 6342437 := bstep (se 4 (by rfl) ⟨594603, by rfl⟩ : syracuseStep 6342437 = 1189207) B1189207
theorem B2344823 : Blo 1040609 2344823 := bstep (se 1 (by rfl) ⟨1758617, by rfl⟩ : syracuseStep 2344823 = 3517235) B3517235
theorem B4278169 : Blo 1040609 4278169 := bstep (se 2 (by rfl) ⟨1604313, by rfl⟩ : syracuseStep 4278169 = 3208627) B3208627
theorem B2345003 : Blo 1040609 2345003 := bstep (se 1 (by rfl) ⟨1758752, by rfl⟩ : syracuseStep 2345003 = 3517505) B3517505
theorem B12667013 : Blo 1040609 12667013 := bstep (se 4 (by rfl) ⟨1187532, by rfl⟩ : syracuseStep 12667013 = 2375065) B2375065
theorem B10012805 : Blo 1040609 10012805 := bstep (se 4 (by rfl) ⟨938700, by rfl⟩ : syracuseStep 10012805 = 1877401) B1877401
theorem B2640073 : Blo 1040609 2640073 := bstep (se 2 (by rfl) ⟨990027, by rfl⟩ : syracuseStep 2640073 = 1980055) B1980055
theorem B2640215 : Blo 1040609 2640215 := bstep (se 1 (by rfl) ⟨1980161, by rfl⟩ : syracuseStep 2640215 = 3960323) B3960323
theorem B2345363 : Blo 1040609 2345363 := bstep (se 1 (by rfl) ⟨1759022, by rfl⟩ : syracuseStep 2345363 = 3518045) B3518045
theorem B3525011 : Blo 1040609 3525011 := bstep (se 1 (by rfl) ⟨2643758, by rfl⟩ : syracuseStep 3525011 = 5287517) B5287517
theorem B2345417 : Blo 1040609 2345417 := bstep (se 2 (by rfl) ⟨879531, by rfl⟩ : syracuseStep 2345417 = 1759063) B1759063
theorem B20007769 : Blo 1040609 20007769 := bstep (se 2 (by rfl) ⟨7502913, by rfl⟩ : syracuseStep 20007769 = 15005827) B15005827
theorem B1756039 : Blo 1040609 1756039 := bstep (se 1 (by rfl) ⟨1317029, by rfl⟩ : syracuseStep 1756039 = 2634059) B2634059
theorem B2346119 : Blo 1040609 2346119 := bstep (se 1 (by rfl) ⟨1759589, by rfl⟩ : syracuseStep 2346119 = 3519179) B3519179
theorem B2346299 : Blo 1040609 2346299 := bstep (se 1 (by rfl) ⟨1759724, by rfl⟩ : syracuseStep 2346299 = 3519449) B3519449
theorem B2968967 : Blo 1040609 2968967 := bstep (se 1 (by rfl) ⟨2226725, by rfl⟩ : syracuseStep 2968967 = 4453451) B4453451
theorem B2116999 : Blo 1040609 2116999 := bstep (se 1 (by rfl) ⟨1587749, by rfl⟩ : syracuseStep 2116999 = 3175499) B3175499
theorem B2674073 : Blo 1040609 2674073 := bstep (se 2 (by rfl) ⟨1002777, by rfl⟩ : syracuseStep 2674073 = 2005555) B2005555
theorem B2346425 : Blo 1040609 2346425 := bstep (se 2 (by rfl) ⟨879909, by rfl⟩ : syracuseStep 2346425 = 1759819) B1759819
theorem B1756687 : Blo 1040609 1756687 := bstep (se 1 (by rfl) ⟨1317515, by rfl⟩ : syracuseStep 1756687 = 2635031) B2635031
theorem B2969149 : Blo 1040609 2969149 := bstep (se 3 (by rfl) ⟨556715, by rfl⟩ : syracuseStep 2969149 = 1113431) B1113431
theorem B2969207 : Blo 1040609 2969207 := bstep (se 1 (by rfl) ⟨2226905, by rfl⟩ : syracuseStep 2969207 = 4453811) B4453811
theorem B2117267 : Blo 1040609 2117267 := bstep (se 1 (by rfl) ⟨1587950, by rfl⟩ : syracuseStep 2117267 = 3175901) B3175901
theorem B76992257 : Blo 1040609 76992257 := bstep (se 2 (by rfl) ⟨28872096, by rfl⟩ : syracuseStep 76992257 = 57744193) B57744193
theorem B2346767 : Blo 1040609 2346767 := bstep (se 1 (by rfl) ⟨1760075, by rfl⟩ : syracuseStep 2346767 = 3520151) B3520151
theorem B2346785 : Blo 1040609 2346785 := bstep (se 2 (by rfl) ⟨880044, by rfl⟩ : syracuseStep 2346785 = 1760089) B1760089
theorem B48844595 : Blo 1040609 48844595 := bstep (se 1 (by rfl) ⟨36633446, by rfl⟩ : syracuseStep 48844595 = 73266893) B73266893
theorem B152457137 : Blo 1040609 152457137 := bstep (se 2 (by rfl) ⟨57171426, by rfl⟩ : syracuseStep 152457137 = 114342853) B114342853
theorem B1757227 : Blo 1040609 1757227 := bstep (se 1 (by rfl) ⟨1317920, by rfl⟩ : syracuseStep 1757227 = 2635841) B2635841
theorem B3952759 : Blo 1040609 3952759 := bstep (se 1 (by rfl) ⟨2964569, by rfl⟩ : syracuseStep 3952759 = 5929139) B5929139
theorem B2347127 : Blo 1040609 2347127 := bstep (se 1 (by rfl) ⟨1760345, by rfl⟩ : syracuseStep 2347127 = 3520691) B3520691
theorem B1757369 : Blo 1040609 1757369 := bstep (se 2 (by rfl) ⟨659013, by rfl⟩ : syracuseStep 1757369 = 1318027) B1318027
theorem B2674945 : Blo 1040609 2674945 := bstep (se 2 (by rfl) ⟨1003104, by rfl⟩ : syracuseStep 2674945 = 2006209) B2006209
theorem B2347307 : Blo 1040609 2347307 := bstep (se 1 (by rfl) ⟨1760480, by rfl⟩ : syracuseStep 2347307 = 3520961) B3520961
theorem B2642291 : Blo 1040609 2642291 := bstep (se 1 (by rfl) ⟨1981718, by rfl⟩ : syracuseStep 2642291 = 3963437) B3963437
theorem B1561019 : Blo 1040609 1561019 := bstep (se 1 (by rfl) ⟨1170764, by rfl⟩ : syracuseStep 1561019 = 2341529) B2341529
theorem B1561079 : Blo 1040609 1561079 := bstep (se 1 (by rfl) ⟨1170809, by rfl⟩ : syracuseStep 1561079 = 2341619) B2341619
theorem B1561103 : Blo 1040609 1561103 := bstep (se 1 (by rfl) ⟨1170827, by rfl⟩ : syracuseStep 1561103 = 2341655) B2341655
theorem B1561145 : Blo 1040609 1561145 := bstep (se 2 (by rfl) ⟨585429, by rfl⟩ : syracuseStep 1561145 = 1170859) B1170859
theorem B1561223 : Blo 1040609 1561223 := bstep (se 1 (by rfl) ⟨1170917, by rfl⟩ : syracuseStep 1561223 = 2341835) B2341835
theorem B2347667 : Blo 1040609 2347667 := bstep (se 1 (by rfl) ⟨1760750, by rfl⟩ : syracuseStep 2347667 = 3521501) B3521501
theorem B2970265 : Blo 1040609 2970265 := bstep (se 2 (by rfl) ⟨1113849, by rfl⟩ : syracuseStep 2970265 = 2227699) B2227699
theorem B1561259 : Blo 1040609 1561259 := bstep (se 1 (by rfl) ⟨1170944, by rfl⟩ : syracuseStep 1561259 = 2341889) B2341889
theorem B10310323 : Blo 1040609 10310323 := bstep (se 1 (by rfl) ⟨7732742, by rfl⟩ : syracuseStep 10310323 = 15465485) B15465485
theorem B7525057 : Blo 1040609 7525057 := bstep (se 2 (by rfl) ⟨2821896, by rfl⟩ : syracuseStep 7525057 = 5643793) B5643793
theorem B1561289 : Blo 1040609 1561289 := bstep (se 2 (by rfl) ⟨585483, by rfl⟩ : syracuseStep 1561289 = 1170967) B1170967
theorem B2347721 : Blo 1040609 2347721 := bstep (se 2 (by rfl) ⟨880395, by rfl⟩ : syracuseStep 2347721 = 1760791) B1760791
theorem B1561403 : Blo 1040609 1561403 := bstep (se 1 (by rfl) ⟨1171052, by rfl⟩ : syracuseStep 1561403 = 2342105) B2342105
theorem B1561463 : Blo 1040609 1561463 := bstep (se 1 (by rfl) ⟨1171097, by rfl⟩ : syracuseStep 1561463 = 2342195) B2342195
theorem B1758071 : Blo 1040609 1758071 := bstep (se 1 (by rfl) ⟨1318553, by rfl⟩ : syracuseStep 1758071 = 2637107) B2637107
theorem B2642807 : Blo 1040609 2642807 := bstep (se 1 (by rfl) ⟨1982105, by rfl⟩ : syracuseStep 2642807 = 3964211) B3964211
theorem B4445063 : Blo 1040609 4445063 := bstep (se 1 (by rfl) ⟨3333797, by rfl⟩ : syracuseStep 4445063 = 6667595) B6667595
theorem B1561487 : Blo 1040609 1561487 := bstep (se 1 (by rfl) ⟨1171115, by rfl⟩ : syracuseStep 1561487 = 2342231) B2342231
theorem B1561529 : Blo 1040609 1561529 := bstep (se 2 (by rfl) ⟨585573, by rfl⟩ : syracuseStep 1561529 = 1171147) B1171147
theorem B1561607 : Blo 1040609 1561607 := bstep (se 1 (by rfl) ⟨1171205, by rfl⟩ : syracuseStep 1561607 = 2342411) B2342411
theorem B1561643 : Blo 1040609 1561643 := bstep (se 1 (by rfl) ⟨1171232, by rfl⟩ : syracuseStep 1561643 = 2342465) B2342465
theorem B3953731 : Blo 1040609 3953731 := bstep (se 1 (by rfl) ⟨2965298, by rfl⟩ : syracuseStep 3953731 = 5930597) B5930597
theorem B1561673 : Blo 1040609 1561673 := bstep (se 2 (by rfl) ⟨585627, by rfl⟩ : syracuseStep 1561673 = 1171255) B1171255
theorem B1561787 : Blo 1040609 1561787 := bstep (se 1 (by rfl) ⟨1171340, by rfl⟩ : syracuseStep 1561787 = 2342681) B2342681
theorem B1561847 : Blo 1040609 1561847 := bstep (se 1 (by rfl) ⟨1171385, by rfl⟩ : syracuseStep 1561847 = 2342771) B2342771
theorem B2970881 : Blo 1040609 2970881 := bstep (se 2 (by rfl) ⟨1114080, by rfl⟩ : syracuseStep 2970881 = 2228161) B2228161
theorem B1561871 : Blo 1040609 1561871 := bstep (se 1 (by rfl) ⟨1171403, by rfl⟩ : syracuseStep 1561871 = 2342807) B2342807
theorem B1561913 : Blo 1040609 1561913 := bstep (se 2 (by rfl) ⟨585717, by rfl⟩ : syracuseStep 1561913 = 1171435) B1171435
theorem B1758523 : Blo 1040609 1758523 := bstep (se 1 (by rfl) ⟨1318892, by rfl⟩ : syracuseStep 1758523 = 2637785) B2637785
theorem B3954035 : Blo 1040609 3954035 := bstep (se 1 (by rfl) ⟨2965526, by rfl⟩ : syracuseStep 3954035 = 5931053) B5931053
theorem B1561991 : Blo 1040609 1561991 := bstep (se 1 (by rfl) ⟨1171493, by rfl⟩ : syracuseStep 1561991 = 2342987) B2342987
theorem B2348423 : Blo 1040609 2348423 := bstep (se 1 (by rfl) ⟨1761317, by rfl⟩ : syracuseStep 2348423 = 3522635) B3522635
theorem B1070479 : Blo 1040609 1070479 := bstep (se 1 (by rfl) ⟨802859, by rfl⟩ : syracuseStep 1070479 = 1605719) B1605719
theorem B1562027 : Blo 1040609 1562027 := bstep (se 1 (by rfl) ⟨1171520, by rfl⟩ : syracuseStep 1562027 = 2343041) B2343041
theorem B1562057 : Blo 1040609 1562057 := bstep (se 2 (by rfl) ⟨585771, by rfl⟩ : syracuseStep 1562057 = 1171543) B1171543
theorem B1758665 : Blo 1040609 1758665 := bstep (se 2 (by rfl) ⟨659499, by rfl⟩ : syracuseStep 1758665 = 1318999) B1318999
theorem B6018583 : Blo 1040609 6018583 := bstep (se 1 (by rfl) ⟨4513937, by rfl⟩ : syracuseStep 6018583 = 9027875) B9027875
theorem B1562171 : Blo 1040609 1562171 := bstep (se 1 (by rfl) ⟨1171628, by rfl⟩ : syracuseStep 1562171 = 2343257) B2343257
theorem B2348603 : Blo 1040609 2348603 := bstep (se 1 (by rfl) ⟨1761452, by rfl⟩ : syracuseStep 2348603 = 3522905) B3522905
theorem B1562231 : Blo 1040609 1562231 := bstep (se 1 (by rfl) ⟨1171673, by rfl⟩ : syracuseStep 1562231 = 2343347) B2343347
theorem B1562255 : Blo 1040609 1562255 := bstep (se 1 (by rfl) ⟨1171691, by rfl⟩ : syracuseStep 1562255 = 2343383) B2343383
theorem B1562297 : Blo 1040609 1562297 := bstep (se 2 (by rfl) ⟨585861, by rfl⟩ : syracuseStep 1562297 = 1171723) B1171723
theorem B2348729 : Blo 1040609 2348729 := bstep (se 2 (by rfl) ⟨880773, by rfl⟩ : syracuseStep 2348729 = 1761547) B1761547
theorem B6674177 : Blo 1040609 6674177 := bstep (se 2 (by rfl) ⟨2502816, by rfl⟩ : syracuseStep 6674177 = 5005633) B5005633
theorem B1562375 : Blo 1040609 1562375 := bstep (se 1 (by rfl) ⟨1171781, by rfl⟩ : syracuseStep 1562375 = 2343563) B2343563
theorem B1562411 : Blo 1040609 1562411 := bstep (se 1 (by rfl) ⟨1171808, by rfl⟩ : syracuseStep 1562411 = 2343617) B2343617
theorem B5003059 : Blo 1040609 5003059 := bstep (se 1 (by rfl) ⟨3752294, by rfl⟩ : syracuseStep 5003059 = 7504589) B7504589
theorem B3954491 : Blo 1040609 3954491 := bstep (se 1 (by rfl) ⟨2965868, by rfl⟩ : syracuseStep 3954491 = 5931737) B5931737
theorem B1562441 : Blo 1040609 1562441 := bstep (se 2 (by rfl) ⟨585915, by rfl⟩ : syracuseStep 1562441 = 1171831) B1171831
theorem B2643799 : Blo 1040609 2643799 := bstep (se 1 (by rfl) ⟨1982849, by rfl⟩ : syracuseStep 2643799 = 3965699) B3965699
theorem B1562555 : Blo 1040609 1562555 := bstep (se 1 (by rfl) ⟨1171916, by rfl⟩ : syracuseStep 1562555 = 2343833) B2343833
theorem B1562615 : Blo 1040609 1562615 := bstep (se 1 (by rfl) ⟨1171961, by rfl⟩ : syracuseStep 1562615 = 2343923) B2343923
theorem B1562639 : Blo 1040609 1562639 := bstep (se 1 (by rfl) ⟨1171979, by rfl⟩ : syracuseStep 1562639 = 2343959) B2343959
theorem B2349071 : Blo 1040609 2349071 := bstep (se 1 (by rfl) ⟨1761803, by rfl⟩ : syracuseStep 2349071 = 3523607) B3523607
theorem B2349089 : Blo 1040609 2349089 := bstep (se 2 (by rfl) ⟨880908, by rfl⟩ : syracuseStep 2349089 = 1761817) B1761817
theorem B1562681 : Blo 1040609 1562681 := bstep (se 2 (by rfl) ⟨586005, by rfl⟩ : syracuseStep 1562681 = 1172011) B1172011
theorem B3758147 : Blo 1040609 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B16898165 : Blo 1040609 16898165 := bstep (se 5 (by rfl) ⟨792101, by rfl⟩ : syracuseStep 16898165 = 1584203) B1584203
theorem B1562759 : Blo 1040609 1562759 := bstep (se 1 (by rfl) ⟨1172069, by rfl⟩ : syracuseStep 1562759 = 2344139) B2344139
theorem B1759367 : Blo 1040609 1759367 := bstep (se 1 (by rfl) ⟨1319525, by rfl⟩ : syracuseStep 1759367 = 2639051) B2639051
theorem B2644103 : Blo 1040609 2644103 := bstep (se 1 (by rfl) ⟨1983077, by rfl⟩ : syracuseStep 2644103 = 3966155) B3966155
theorem B1562795 : Blo 1040609 1562795 := bstep (se 1 (by rfl) ⟨1172096, by rfl⟩ : syracuseStep 1562795 = 2344193) B2344193
theorem B1562825 : Blo 1040609 1562825 := bstep (se 2 (by rfl) ⟨586059, by rfl⟩ : syracuseStep 1562825 = 1172119) B1172119
theorem B2971849 : Blo 1040609 2971849 := bstep (se 2 (by rfl) ⟨1114443, by rfl⟩ : syracuseStep 2971849 = 2228887) B2228887
theorem B3954977 : Blo 1040609 3954977 := bstep (se 2 (by rfl) ⟨1483116, by rfl⟩ : syracuseStep 3954977 = 2966233) B2966233
theorem B1562939 : Blo 1040609 1562939 := bstep (se 1 (by rfl) ⟨1172204, by rfl⟩ : syracuseStep 1562939 = 2344409) B2344409
theorem B1562999 : Blo 1040609 1562999 := bstep (se 1 (by rfl) ⟨1172249, by rfl⟩ : syracuseStep 1562999 = 2344499) B2344499
theorem B2349431 : Blo 1040609 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B1563023 : Blo 1040609 1563023 := bstep (se 1 (by rfl) ⟨1172267, by rfl⟩ : syracuseStep 1563023 = 2344535) B2344535
theorem B1563065 : Blo 1040609 1563065 := bstep (se 2 (by rfl) ⟨586149, by rfl⟩ : syracuseStep 1563065 = 1172299) B1172299
theorem B1563143 : Blo 1040609 1563143 := bstep (se 1 (by rfl) ⟨1172357, by rfl⟩ : syracuseStep 1563143 = 2344715) B2344715
theorem B1563179 : Blo 1040609 1563179 := bstep (se 1 (by rfl) ⟨1172384, by rfl⟩ : syracuseStep 1563179 = 2344769) B2344769
theorem B2349611 : Blo 1040609 2349611 := bstep (se 1 (by rfl) ⟨1762208, by rfl⟩ : syracuseStep 2349611 = 3524417) B3524417
theorem B1563209 : Blo 1040609 1563209 := bstep (se 2 (by rfl) ⟨586203, by rfl⟩ : syracuseStep 1563209 = 1172407) B1172407
theorem B4446839 : Blo 1040609 4446839 := bstep (se 1 (by rfl) ⟨3335129, by rfl⟩ : syracuseStep 4446839 = 6670259) B6670259
theorem B1563323 : Blo 1040609 1563323 := bstep (se 1 (by rfl) ⟨1172492, by rfl⟩ : syracuseStep 1563323 = 2344985) B2344985
theorem B1563383 : Blo 1040609 1563383 := bstep (se 1 (by rfl) ⟨1172537, by rfl⟩ : syracuseStep 1563383 = 2345075) B2345075
theorem B4446991 : Blo 1040609 4446991 := bstep (se 1 (by rfl) ⟨3335243, by rfl⟩ : syracuseStep 4446991 = 6670487) B6670487
theorem B1563407 : Blo 1040609 1563407 := bstep (se 1 (by rfl) ⟨1172555, by rfl⟩ : syracuseStep 1563407 = 2345111) B2345111
theorem B1760015 : Blo 1040609 1760015 := bstep (se 1 (by rfl) ⟨1320011, by rfl⟩ : syracuseStep 1760015 = 2640023) B2640023
theorem B1563449 : Blo 1040609 1563449 := bstep (se 2 (by rfl) ⟨586293, by rfl⟩ : syracuseStep 1563449 = 1172587) B1172587
theorem B1563527 : Blo 1040609 1563527 := bstep (se 1 (by rfl) ⟨1172645, by rfl⟩ : syracuseStep 1563527 = 2345291) B2345291
theorem B2349971 : Blo 1040609 2349971 := bstep (se 1 (by rfl) ⟨1762478, by rfl⟩ : syracuseStep 2349971 = 3524957) B3524957
theorem B1563563 : Blo 1040609 1563563 := bstep (se 1 (by rfl) ⟨1172672, by rfl⟩ : syracuseStep 1563563 = 2345345) B2345345
theorem B1563593 : Blo 1040609 1563593 := bstep (se 2 (by rfl) ⟨586347, by rfl⟩ : syracuseStep 1563593 = 1172695) B1172695
theorem B2350025 : Blo 1040609 2350025 := bstep (se 2 (by rfl) ⟨881259, by rfl⟩ : syracuseStep 2350025 = 1762519) B1762519
theorem B1563707 : Blo 1040609 1563707 := bstep (se 1 (by rfl) ⟨1172780, by rfl⟩ : syracuseStep 1563707 = 2345561) B2345561
theorem B1563767 : Blo 1040609 1563767 := bstep (se 1 (by rfl) ⟨1172825, by rfl⟩ : syracuseStep 1563767 = 2345651) B2345651
theorem B1563791 : Blo 1040609 1563791 := bstep (se 1 (by rfl) ⟨1172843, by rfl⟩ : syracuseStep 1563791 = 2345687) B2345687
theorem B1563833 : Blo 1040609 1563833 := bstep (se 2 (by rfl) ⟨586437, by rfl⟩ : syracuseStep 1563833 = 1172875) B1172875
theorem B3955949 : Blo 1040609 3955949 := bstep (se 3 (by rfl) ⟨741740, by rfl⟩ : syracuseStep 3955949 = 1483481) B1483481
theorem B1563911 : Blo 1040609 1563911 := bstep (se 1 (by rfl) ⟨1172933, by rfl⟩ : syracuseStep 1563911 = 2345867) B2345867
theorem B1563947 : Blo 1040609 1563947 := bstep (se 1 (by rfl) ⟨1172960, by rfl⟩ : syracuseStep 1563947 = 2345921) B2345921
theorem B1760555 : Blo 1040609 1760555 := bstep (se 1 (by rfl) ⟨1320416, by rfl⟩ : syracuseStep 1760555 = 2640833) B2640833
theorem B1563977 : Blo 1040609 1563977 := bstep (se 2 (by rfl) ⟨586491, by rfl⟩ : syracuseStep 1563977 = 1172983) B1172983
theorem B1170823 : Blo 1040609 1170823 := bstep (se 1 (by rfl) ⟨878117, by rfl⟩ : syracuseStep 1170823 = 1756235) B1756235
theorem B1564091 : Blo 1040609 1564091 := bstep (se 1 (by rfl) ⟨1173068, by rfl⟩ : syracuseStep 1564091 = 2346137) B2346137
theorem B1564151 : Blo 1040609 1564151 := bstep (se 1 (by rfl) ⟨1173113, by rfl⟩ : syracuseStep 1564151 = 2346227) B2346227
theorem B1564175 : Blo 1040609 1564175 := bstep (se 1 (by rfl) ⟨1173131, by rfl⟩ : syracuseStep 1564175 = 2346263) B2346263
theorem B1564217 : Blo 1040609 1564217 := bstep (se 2 (by rfl) ⟨586581, by rfl⟩ : syracuseStep 1564217 = 1173163) B1173163
theorem B1171003 : Blo 1040609 1171003 := bstep (se 1 (by rfl) ⟨878252, by rfl⟩ : syracuseStep 1171003 = 1756505) B1756505
theorem B4447811 : Blo 1040609 4447811 := bstep (se 1 (by rfl) ⟨3335858, by rfl⟩ : syracuseStep 4447811 = 6671717) B6671717
theorem B1564295 : Blo 1040609 1564295 := bstep (se 1 (by rfl) ⟨1173221, by rfl⟩ : syracuseStep 1564295 = 2346443) B2346443
theorem B33808013 : Blo 1040609 33808013 := bstep (se 3 (by rfl) ⟨6339002, by rfl⟩ : syracuseStep 33808013 = 12678005) B12678005
theorem B1564331 : Blo 1040609 1564331 := bstep (se 1 (by rfl) ⟨1173248, by rfl⟩ : syracuseStep 1564331 = 2346497) B2346497
theorem B1760953 : Blo 1040609 1760953 := bstep (se 2 (by rfl) ⟨660357, by rfl⟩ : syracuseStep 1760953 = 1320715) B1320715
theorem B1564361 : Blo 1040609 1564361 := bstep (se 2 (by rfl) ⟨586635, by rfl⟩ : syracuseStep 1564361 = 1173271) B1173271
theorem B2973455 : Blo 1040609 2973455 := bstep (se 1 (by rfl) ⟨2230091, by rfl⟩ : syracuseStep 2973455 = 4460183) B4460183
theorem B1564475 : Blo 1040609 1564475 := bstep (se 1 (by rfl) ⟨1173356, by rfl⟩ : syracuseStep 1564475 = 2346713) B2346713
theorem B1564535 : Blo 1040609 1564535 := bstep (se 1 (by rfl) ⟨1173401, by rfl⟩ : syracuseStep 1564535 = 2346803) B2346803
theorem B1564559 : Blo 1040609 1564559 := bstep (se 1 (by rfl) ⟨1173419, by rfl⟩ : syracuseStep 1564559 = 2346839) B2346839
theorem B3956633 : Blo 1040609 3956633 := bstep (se 2 (by rfl) ⟨1483737, by rfl⟩ : syracuseStep 3956633 = 2967475) B2967475
theorem B1564601 : Blo 1040609 1564601 := bstep (se 2 (by rfl) ⟨586725, by rfl⟩ : syracuseStep 1564601 = 1173451) B1173451
theorem B1564679 : Blo 1040609 1564679 := bstep (se 1 (by rfl) ⟨1173509, by rfl⟩ : syracuseStep 1564679 = 2347019) B2347019
theorem B1171471 : Blo 1040609 1171471 := bstep (se 1 (by rfl) ⟨878603, by rfl⟩ : syracuseStep 1171471 = 1757207) B1757207
theorem B1564715 : Blo 1040609 1564715 := bstep (se 1 (by rfl) ⟨1173536, by rfl⟩ : syracuseStep 1564715 = 2347073) B2347073
theorem B1564745 : Blo 1040609 1564745 := bstep (se 2 (by rfl) ⟨586779, by rfl⟩ : syracuseStep 1564745 = 1173559) B1173559
theorem B1564859 : Blo 1040609 1564859 := bstep (se 1 (by rfl) ⟨1173644, by rfl⟩ : syracuseStep 1564859 = 2347289) B2347289
theorem B1564919 : Blo 1040609 1564919 := bstep (se 1 (by rfl) ⟨1173689, by rfl⟩ : syracuseStep 1564919 = 2347379) B2347379
theorem B1040647 : Blo 1040609 1040647 := bstep (se 1 (by rfl) ⟨780485, by rfl⟩ : syracuseStep 1040647 = 1560971) B1560971
theorem B1040655 : Blo 1040609 1040655 := bstep (se 1 (by rfl) ⟨780491, by rfl⟩ : syracuseStep 1040655 = 1560983) B1560983
theorem B1564943 : Blo 1040609 1564943 := bstep (se 1 (by rfl) ⟨1173707, by rfl⟩ : syracuseStep 1564943 = 2347415) B2347415
theorem B1564985 : Blo 1040609 1564985 := bstep (se 2 (by rfl) ⟨586869, by rfl⟩ : syracuseStep 1564985 = 1173739) B1173739
theorem B1040699 : Blo 1040609 1040699 := bstep (se 1 (by rfl) ⟨780524, by rfl⟩ : syracuseStep 1040699 = 1561049) B1561049
theorem B1761655 : Blo 1040609 1761655 := bstep (se 1 (by rfl) ⟨1321241, by rfl⟩ : syracuseStep 1761655 = 2642483) B2642483
theorem B1040775 : Blo 1040609 1040775 := bstep (se 1 (by rfl) ⟨780581, by rfl⟩ : syracuseStep 1040775 = 1561163) B1561163
theorem B1565063 : Blo 1040609 1565063 := bstep (se 1 (by rfl) ⟨1173797, by rfl⟩ : syracuseStep 1565063 = 2347595) B2347595
theorem B1040783 : Blo 1040609 1040783 := bstep (se 1 (by rfl) ⟨780587, by rfl⟩ : syracuseStep 1040783 = 1561175) B1561175
theorem B4219289 : Blo 1040609 4219289 := bstep (se 2 (by rfl) ⟨1582233, by rfl⟩ : syracuseStep 4219289 = 3164467) B3164467
theorem B3334553 : Blo 1040609 3334553 := bstep (se 2 (by rfl) ⟨1250457, by rfl⟩ : syracuseStep 3334553 = 2500915) B2500915
theorem B1565099 : Blo 1040609 1565099 := bstep (se 1 (by rfl) ⟨1173824, by rfl⟩ : syracuseStep 1565099 = 2347649) B2347649
theorem B1040827 : Blo 1040609 1040827 := bstep (se 1 (by rfl) ⟨780620, by rfl⟩ : syracuseStep 1040827 = 1561241) B1561241
theorem B1565129 : Blo 1040609 1565129 := bstep (se 2 (by rfl) ⟨586923, by rfl⟩ : syracuseStep 1565129 = 1173847) B1173847
theorem B1040903 : Blo 1040609 1040903 := bstep (se 1 (by rfl) ⟨780677, by rfl⟩ : syracuseStep 1040903 = 1561355) B1561355
theorem B1171975 : Blo 1040609 1171975 := bstep (se 1 (by rfl) ⟨878981, by rfl⟩ : syracuseStep 1171975 = 1757963) B1757963
theorem B1040911 : Blo 1040609 1040911 := bstep (se 1 (by rfl) ⟨780683, by rfl⟩ : syracuseStep 1040911 = 1561367) B1561367
theorem B1040955 : Blo 1040609 1040955 := bstep (se 1 (by rfl) ⟨780716, by rfl⟩ : syracuseStep 1040955 = 1561433) B1561433
theorem B1565243 : Blo 1040609 1565243 := bstep (se 1 (by rfl) ⟨1173932, by rfl⟩ : syracuseStep 1565243 = 2347865) B2347865
theorem B1761851 : Blo 1040609 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B1565303 : Blo 1040609 1565303 := bstep (se 1 (by rfl) ⟨1173977, by rfl⟩ : syracuseStep 1565303 = 2347955) B2347955
theorem B1041031 : Blo 1040609 1041031 := bstep (se 1 (by rfl) ⟨780773, by rfl⟩ : syracuseStep 1041031 = 1561547) B1561547
theorem B1041039 : Blo 1040609 1041039 := bstep (se 1 (by rfl) ⟨780779, by rfl⟩ : syracuseStep 1041039 = 1561559) B1561559
theorem B1565327 : Blo 1040609 1565327 := bstep (se 1 (by rfl) ⟨1173995, by rfl⟩ : syracuseStep 1565327 = 2347991) B2347991
theorem B3170963 : Blo 1040609 3170963 := bstep (se 1 (by rfl) ⟨2378222, by rfl⟩ : syracuseStep 3170963 = 4756445) B4756445
theorem B1565369 : Blo 1040609 1565369 := bstep (se 2 (by rfl) ⟨587013, by rfl⟩ : syracuseStep 1565369 = 1174027) B1174027
theorem B1041083 : Blo 1040609 1041083 := bstep (se 1 (by rfl) ⟨780812, by rfl⟩ : syracuseStep 1041083 = 1561625) B1561625
theorem B1172155 : Blo 1040609 1172155 := bstep (se 1 (by rfl) ⟨879116, by rfl⟩ : syracuseStep 1172155 = 1758233) B1758233
theorem B1041159 : Blo 1040609 1041159 := bstep (se 1 (by rfl) ⟨780869, by rfl⟩ : syracuseStep 1041159 = 1561739) B1561739
theorem B1565447 : Blo 1040609 1565447 := bstep (se 1 (by rfl) ⟨1174085, by rfl⟩ : syracuseStep 1565447 = 2348171) B2348171
theorem B5268239 : Blo 1040609 5268239 := bstep (se 1 (by rfl) ⟨3951179, by rfl⟩ : syracuseStep 5268239 = 7902359) B7902359
theorem B1041167 : Blo 1040609 1041167 := bstep (se 1 (by rfl) ⟨780875, by rfl⟩ : syracuseStep 1041167 = 1561751) B1561751
theorem B1565483 : Blo 1040609 1565483 := bstep (se 1 (by rfl) ⟨1174112, by rfl⟩ : syracuseStep 1565483 = 2348225) B2348225
theorem B1041211 : Blo 1040609 1041211 := bstep (se 1 (by rfl) ⟨780908, by rfl⟩ : syracuseStep 1041211 = 1561817) B1561817
theorem B1565513 : Blo 1040609 1565513 := bstep (se 2 (by rfl) ⟨587067, by rfl⟩ : syracuseStep 1565513 = 1174135) B1174135
theorem B3957619 : Blo 1040609 3957619 := bstep (se 1 (by rfl) ⟨2968214, by rfl⟩ : syracuseStep 3957619 = 5936429) B5936429
theorem B2974583 : Blo 1040609 2974583 := bstep (se 1 (by rfl) ⟨2230937, by rfl⟩ : syracuseStep 2974583 = 4461875) B4461875
theorem B1041287 : Blo 1040609 1041287 := bstep (se 1 (by rfl) ⟨780965, by rfl⟩ : syracuseStep 1041287 = 1561931) B1561931
theorem B1041295 : Blo 1040609 1041295 := bstep (se 1 (by rfl) ⟨780971, by rfl⟩ : syracuseStep 1041295 = 1561943) B1561943
theorem B10838947 : Blo 1040609 10838947 := bstep (se 1 (by rfl) ⟨8129210, by rfl⟩ : syracuseStep 10838947 = 16258421) B16258421
theorem B1041339 : Blo 1040609 1041339 := bstep (se 1 (by rfl) ⟨781004, by rfl⟩ : syracuseStep 1041339 = 1562009) B1562009
theorem B1565627 : Blo 1040609 1565627 := bstep (se 1 (by rfl) ⟨1174220, by rfl⟩ : syracuseStep 1565627 = 2348441) B2348441
theorem B1762249 : Blo 1040609 1762249 := bstep (se 2 (by rfl) ⟨660843, by rfl⟩ : syracuseStep 1762249 = 1321687) B1321687
theorem B1565687 : Blo 1040609 1565687 := bstep (se 1 (by rfl) ⟨1174265, by rfl⟩ : syracuseStep 1565687 = 2348531) B2348531
theorem B1041415 : Blo 1040609 1041415 := bstep (se 1 (by rfl) ⟨781061, by rfl⟩ : syracuseStep 1041415 = 1562123) B1562123
theorem B1041423 : Blo 1040609 1041423 := bstep (se 1 (by rfl) ⟨781067, by rfl⟩ : syracuseStep 1041423 = 1562135) B1562135
theorem B1565711 : Blo 1040609 1565711 := bstep (se 1 (by rfl) ⟨1174283, by rfl⟩ : syracuseStep 1565711 = 2348567) B2348567
theorem B1565753 : Blo 1040609 1565753 := bstep (se 2 (by rfl) ⟨587157, by rfl⟩ : syracuseStep 1565753 = 1174315) B1174315
theorem B1041467 : Blo 1040609 1041467 := bstep (se 1 (by rfl) ⟨781100, by rfl⟩ : syracuseStep 1041467 = 1562201) B1562201
theorem B1041543 : Blo 1040609 1041543 := bstep (se 1 (by rfl) ⟨781157, by rfl⟩ : syracuseStep 1041543 = 1562315) B1562315
theorem B1565831 : Blo 1040609 1565831 := bstep (se 1 (by rfl) ⟨1174373, by rfl⟩ : syracuseStep 1565831 = 2348747) B2348747
theorem B1041551 : Blo 1040609 1041551 := bstep (se 1 (by rfl) ⟨781163, by rfl⟩ : syracuseStep 1041551 = 1562327) B1562327
theorem B1172623 : Blo 1040609 1172623 := bstep (se 1 (by rfl) ⟨879467, by rfl⟩ : syracuseStep 1172623 = 1758935) B1758935
theorem B1565867 : Blo 1040609 1565867 := bstep (se 1 (by rfl) ⟨1174400, by rfl⟩ : syracuseStep 1565867 = 2348801) B2348801
theorem B1041595 : Blo 1040609 1041595 := bstep (se 1 (by rfl) ⟨781196, by rfl⟩ : syracuseStep 1041595 = 1562393) B1562393
theorem B1565897 : Blo 1040609 1565897 := bstep (se 2 (by rfl) ⟨587211, by rfl⟩ : syracuseStep 1565897 = 1174423) B1174423
theorem B1041671 : Blo 1040609 1041671 := bstep (se 1 (by rfl) ⟨781253, by rfl⟩ : syracuseStep 1041671 = 1562507) B1562507
theorem B1041679 : Blo 1040609 1041679 := bstep (se 1 (by rfl) ⟨781259, by rfl⟩ : syracuseStep 1041679 = 1562519) B1562519
theorem B1041723 : Blo 1040609 1041723 := bstep (se 1 (by rfl) ⟨781292, by rfl⟩ : syracuseStep 1041723 = 1562585) B1562585
theorem B1566011 : Blo 1040609 1566011 := bstep (se 1 (by rfl) ⟨1174508, by rfl⟩ : syracuseStep 1566011 = 2349017) B2349017
theorem B1566071 : Blo 1040609 1566071 := bstep (se 1 (by rfl) ⟨1174553, by rfl⟩ : syracuseStep 1566071 = 2349107) B2349107
theorem B1041799 : Blo 1040609 1041799 := bstep (se 1 (by rfl) ⟨781349, by rfl⟩ : syracuseStep 1041799 = 1562699) B1562699
theorem B1041807 : Blo 1040609 1041807 := bstep (se 1 (by rfl) ⟨781355, by rfl⟩ : syracuseStep 1041807 = 1562711) B1562711
theorem B1566095 : Blo 1040609 1566095 := bstep (se 1 (by rfl) ⟨1174571, by rfl⟩ : syracuseStep 1566095 = 2349143) B2349143
theorem B1566137 : Blo 1040609 1566137 := bstep (se 2 (by rfl) ⟨587301, by rfl⟩ : syracuseStep 1566137 = 1174603) B1174603
theorem B1041851 : Blo 1040609 1041851 := bstep (se 1 (by rfl) ⟨781388, by rfl⟩ : syracuseStep 1041851 = 1562777) B1562777
theorem B1041927 : Blo 1040609 1041927 := bstep (se 1 (by rfl) ⟨781445, by rfl⟩ : syracuseStep 1041927 = 1562891) B1562891
theorem B1566215 : Blo 1040609 1566215 := bstep (se 1 (by rfl) ⟨1174661, by rfl⟩ : syracuseStep 1566215 = 2349323) B2349323
theorem B1041935 : Blo 1040609 1041935 := bstep (se 1 (by rfl) ⟨781451, by rfl⟩ : syracuseStep 1041935 = 1562903) B1562903
theorem B1566251 : Blo 1040609 1566251 := bstep (se 1 (by rfl) ⟨1174688, by rfl⟩ : syracuseStep 1566251 = 2349377) B2349377
theorem B1041979 : Blo 1040609 1041979 := bstep (se 1 (by rfl) ⟨781484, by rfl⟩ : syracuseStep 1041979 = 1562969) B1562969
theorem B1566281 : Blo 1040609 1566281 := bstep (se 2 (by rfl) ⟨587355, by rfl⟩ : syracuseStep 1566281 = 1174711) B1174711
theorem B1042055 : Blo 1040609 1042055 := bstep (se 1 (by rfl) ⟨781541, by rfl⟩ : syracuseStep 1042055 = 1563083) B1563083
theorem B1173127 : Blo 1040609 1173127 := bstep (se 1 (by rfl) ⟨879845, by rfl⟩ : syracuseStep 1173127 = 1759691) B1759691
theorem B1042063 : Blo 1040609 1042063 := bstep (se 1 (by rfl) ⟨781547, by rfl⟩ : syracuseStep 1042063 = 1563095) B1563095
theorem B1042107 : Blo 1040609 1042107 := bstep (se 1 (by rfl) ⟨781580, by rfl⟩ : syracuseStep 1042107 = 1563161) B1563161
theorem B1566395 : Blo 1040609 1566395 := bstep (se 1 (by rfl) ⟨1174796, by rfl⟩ : syracuseStep 1566395 = 2349593) B2349593
theorem B1566455 : Blo 1040609 1566455 := bstep (se 1 (by rfl) ⟨1174841, by rfl⟩ : syracuseStep 1566455 = 2349683) B2349683
theorem B1042183 : Blo 1040609 1042183 := bstep (se 1 (by rfl) ⟨781637, by rfl⟩ : syracuseStep 1042183 = 1563275) B1563275
theorem B1042191 : Blo 1040609 1042191 := bstep (se 1 (by rfl) ⟨781643, by rfl⟩ : syracuseStep 1042191 = 1563287) B1563287
theorem B1566479 : Blo 1040609 1566479 := bstep (se 1 (by rfl) ⟨1174859, by rfl⟩ : syracuseStep 1566479 = 2349719) B2349719
theorem B1566521 : Blo 1040609 1566521 := bstep (se 2 (by rfl) ⟨587445, by rfl⟩ : syracuseStep 1566521 = 1174891) B1174891
theorem B1042235 : Blo 1040609 1042235 := bstep (se 1 (by rfl) ⟨781676, by rfl⟩ : syracuseStep 1042235 = 1563353) B1563353
theorem B1173307 : Blo 1040609 1173307 := bstep (se 1 (by rfl) ⟨879980, by rfl⟩ : syracuseStep 1173307 = 1759961) B1759961
theorem B1042311 : Blo 1040609 1042311 := bstep (se 1 (by rfl) ⟨781733, by rfl⟩ : syracuseStep 1042311 = 1563467) B1563467
theorem B1566599 : Blo 1040609 1566599 := bstep (se 1 (by rfl) ⟨1174949, by rfl⟩ : syracuseStep 1566599 = 2349899) B2349899
theorem B1042319 : Blo 1040609 1042319 := bstep (se 1 (by rfl) ⟨781739, by rfl⟩ : syracuseStep 1042319 = 1563479) B1563479
theorem B1566635 : Blo 1040609 1566635 := bstep (se 1 (by rfl) ⟨1174976, by rfl⟩ : syracuseStep 1566635 = 2349953) B2349953
theorem B1042363 : Blo 1040609 1042363 := bstep (se 1 (by rfl) ⟨781772, by rfl⟩ : syracuseStep 1042363 = 1563545) B1563545
theorem B1566665 : Blo 1040609 1566665 := bstep (se 2 (by rfl) ⟨587499, by rfl⟩ : syracuseStep 1566665 = 1174999) B1174999
theorem B1042439 : Blo 1040609 1042439 := bstep (se 1 (by rfl) ⟨781829, by rfl⟩ : syracuseStep 1042439 = 1563659) B1563659
theorem B1042447 : Blo 1040609 1042447 := bstep (se 1 (by rfl) ⟨781835, by rfl⟩ : syracuseStep 1042447 = 1563671) B1563671
theorem B3172385 : Blo 1040609 3172385 := bstep (se 2 (by rfl) ⟨1189644, by rfl⟩ : syracuseStep 3172385 = 2379289) B2379289
theorem B1042491 : Blo 1040609 1042491 := bstep (se 1 (by rfl) ⟨781868, by rfl⟩ : syracuseStep 1042491 = 1563737) B1563737
theorem B1566779 : Blo 1040609 1566779 := bstep (se 1 (by rfl) ⟨1175084, by rfl⟩ : syracuseStep 1566779 = 2350169) B2350169
theorem B1566839 : Blo 1040609 1566839 := bstep (se 1 (by rfl) ⟨1175129, by rfl⟩ : syracuseStep 1566839 = 2350259) B2350259
theorem B1042567 : Blo 1040609 1042567 := bstep (se 1 (by rfl) ⟨781925, by rfl⟩ : syracuseStep 1042567 = 1563851) B1563851
theorem B1042575 : Blo 1040609 1042575 := bstep (se 1 (by rfl) ⟨781931, by rfl⟩ : syracuseStep 1042575 = 1563863) B1563863
theorem B1566863 : Blo 1040609 1566863 := bstep (se 1 (by rfl) ⟨1175147, by rfl⟩ : syracuseStep 1566863 = 2350295) B2350295
theorem B1566905 : Blo 1040609 1566905 := bstep (se 2 (by rfl) ⟨587589, by rfl⟩ : syracuseStep 1566905 = 1175179) B1175179
theorem B1042619 : Blo 1040609 1042619 := bstep (se 1 (by rfl) ⟨781964, by rfl⟩ : syracuseStep 1042619 = 1563929) B1563929
theorem B5269697 : Blo 1040609 5269697 := bstep (se 2 (by rfl) ⟨1976136, by rfl⟩ : syracuseStep 5269697 = 3952273) B3952273
theorem B1042695 : Blo 1040609 1042695 := bstep (se 1 (by rfl) ⟨782021, by rfl⟩ : syracuseStep 1042695 = 1564043) B1564043
theorem B1042703 : Blo 1040609 1042703 := bstep (se 1 (by rfl) ⟨782027, by rfl⟩ : syracuseStep 1042703 = 1564055) B1564055
theorem B1173775 : Blo 1040609 1173775 := bstep (se 1 (by rfl) ⟨880331, by rfl⟩ : syracuseStep 1173775 = 1760663) B1760663
theorem B1042747 : Blo 1040609 1042747 := bstep (se 1 (by rfl) ⟨782060, by rfl⟩ : syracuseStep 1042747 = 1564121) B1564121
theorem B1042823 : Blo 1040609 1042823 := bstep (se 1 (by rfl) ⟨782117, by rfl⟩ : syracuseStep 1042823 = 1564235) B1564235
theorem B1042831 : Blo 1040609 1042831 := bstep (se 1 (by rfl) ⟨782123, by rfl⟩ : syracuseStep 1042831 = 1564247) B1564247
theorem B1042875 : Blo 1040609 1042875 := bstep (se 1 (by rfl) ⟨782156, by rfl⟩ : syracuseStep 1042875 = 1564313) B1564313
theorem B1042951 : Blo 1040609 1042951 := bstep (se 1 (by rfl) ⟨782213, by rfl⟩ : syracuseStep 1042951 = 1564427) B1564427
theorem B1042959 : Blo 1040609 1042959 := bstep (se 1 (by rfl) ⟨782219, by rfl⟩ : syracuseStep 1042959 = 1564439) B1564439
theorem B1043003 : Blo 1040609 1043003 := bstep (se 1 (by rfl) ⟨782252, by rfl⟩ : syracuseStep 1043003 = 1564505) B1564505
theorem B1043079 : Blo 1040609 1043079 := bstep (se 1 (by rfl) ⟨782309, by rfl⟩ : syracuseStep 1043079 = 1564619) B1564619
theorem B1043087 : Blo 1040609 1043087 := bstep (se 1 (by rfl) ⟨782315, by rfl⟩ : syracuseStep 1043087 = 1564631) B1564631
theorem B1043131 : Blo 1040609 1043131 := bstep (se 1 (by rfl) ⟨782348, by rfl⟩ : syracuseStep 1043131 = 1564697) B1564697
theorem B1043207 : Blo 1040609 1043207 := bstep (se 1 (by rfl) ⟨782405, by rfl⟩ : syracuseStep 1043207 = 1564811) B1564811
theorem B1174279 : Blo 1040609 1174279 := bstep (se 1 (by rfl) ⟨880709, by rfl⟩ : syracuseStep 1174279 = 1761419) B1761419
theorem B1043215 : Blo 1040609 1043215 := bstep (se 1 (by rfl) ⟨782411, by rfl⟩ : syracuseStep 1043215 = 1564823) B1564823
theorem B1043259 : Blo 1040609 1043259 := bstep (se 1 (by rfl) ⟨782444, by rfl⟩ : syracuseStep 1043259 = 1564889) B1564889
theorem B22571891 : Blo 1040609 22571891 := bstep (se 1 (by rfl) ⟨16928918, by rfl⟩ : syracuseStep 22571891 = 33857837) B33857837
theorem B1043335 : Blo 1040609 1043335 := bstep (se 1 (by rfl) ⟨782501, by rfl⟩ : syracuseStep 1043335 = 1565003) B1565003
theorem B1043343 : Blo 1040609 1043343 := bstep (se 1 (by rfl) ⟨782507, by rfl⟩ : syracuseStep 1043343 = 1565015) B1565015
theorem B1043387 : Blo 1040609 1043387 := bstep (se 1 (by rfl) ⟨782540, by rfl⟩ : syracuseStep 1043387 = 1565081) B1565081
theorem B1174459 : Blo 1040609 1174459 := bstep (se 1 (by rfl) ⟨880844, by rfl⟩ : syracuseStep 1174459 = 1761689) B1761689
theorem B1043463 : Blo 1040609 1043463 := bstep (se 1 (by rfl) ⟨782597, by rfl⟩ : syracuseStep 1043463 = 1565195) B1565195
theorem B1043471 : Blo 1040609 1043471 := bstep (se 1 (by rfl) ⟨782603, by rfl⟩ : syracuseStep 1043471 = 1565207) B1565207
theorem B3959837 : Blo 1040609 3959837 := bstep (se 3 (by rfl) ⟨742469, by rfl⟩ : syracuseStep 3959837 = 1484939) B1484939
theorem B1043515 : Blo 1040609 1043515 := bstep (se 1 (by rfl) ⟨782636, by rfl⟩ : syracuseStep 1043515 = 1565273) B1565273
theorem B14445701 : Blo 1040609 14445701 := bstep (se 4 (by rfl) ⟨1354284, by rfl⟩ : syracuseStep 14445701 = 2708569) B2708569
theorem B1043591 : Blo 1040609 1043591 := bstep (se 1 (by rfl) ⟨782693, by rfl⟩ : syracuseStep 1043591 = 1565387) B1565387
theorem B1043599 : Blo 1040609 1043599 := bstep (se 1 (by rfl) ⟨782699, by rfl⟩ : syracuseStep 1043599 = 1565399) B1565399
theorem B1043643 : Blo 1040609 1043643 := bstep (se 1 (by rfl) ⟨782732, by rfl⟩ : syracuseStep 1043643 = 1565465) B1565465
theorem B1043719 : Blo 1040609 1043719 := bstep (se 1 (by rfl) ⟨782789, by rfl⟩ : syracuseStep 1043719 = 1565579) B1565579
theorem B1043727 : Blo 1040609 1043727 := bstep (se 1 (by rfl) ⟨782795, by rfl⟩ : syracuseStep 1043727 = 1565591) B1565591
theorem B1043771 : Blo 1040609 1043771 := bstep (se 1 (by rfl) ⟨782828, by rfl⟩ : syracuseStep 1043771 = 1565657) B1565657
theorem B1043847 : Blo 1040609 1043847 := bstep (se 1 (by rfl) ⟨782885, by rfl⟩ : syracuseStep 1043847 = 1565771) B1565771
theorem B1043855 : Blo 1040609 1043855 := bstep (se 1 (by rfl) ⟨782891, by rfl⟩ : syracuseStep 1043855 = 1565783) B1565783
theorem B1174927 : Blo 1040609 1174927 := bstep (se 1 (by rfl) ⟨881195, by rfl⟩ : syracuseStep 1174927 = 1762391) B1762391
theorem B1043899 : Blo 1040609 1043899 := bstep (se 1 (by rfl) ⟨782924, by rfl⟩ : syracuseStep 1043899 = 1565849) B1565849
theorem B5270993 : Blo 1040609 5270993 := bstep (se 2 (by rfl) ⟨1976622, by rfl⟩ : syracuseStep 5270993 = 3953245) B3953245
theorem B7925201 : Blo 1040609 7925201 := bstep (se 2 (by rfl) ⟨2971950, by rfl⟩ : syracuseStep 7925201 = 5943901) B5943901
theorem B5631491 : Blo 1040609 5631491 := bstep (se 1 (by rfl) ⟨4223618, by rfl⟩ : syracuseStep 5631491 = 8447237) B8447237
theorem B1043975 : Blo 1040609 1043975 := bstep (se 1 (by rfl) ⟨782981, by rfl⟩ : syracuseStep 1043975 = 1565963) B1565963
theorem B1043983 : Blo 1040609 1043983 := bstep (se 1 (by rfl) ⟨782987, by rfl⟩ : syracuseStep 1043983 = 1565975) B1565975
theorem B3337757 : Blo 1040609 3337757 := bstep (se 3 (by rfl) ⟨625829, by rfl⟩ : syracuseStep 3337757 = 1251659) B1251659
theorem B1044027 : Blo 1040609 1044027 := bstep (se 1 (by rfl) ⟨783020, by rfl⟩ : syracuseStep 1044027 = 1566041) B1566041
theorem B1044103 : Blo 1040609 1044103 := bstep (se 1 (by rfl) ⟨783077, by rfl⟩ : syracuseStep 1044103 = 1566155) B1566155
theorem B1044111 : Blo 1040609 1044111 := bstep (se 1 (by rfl) ⟨783083, by rfl⟩ : syracuseStep 1044111 = 1566167) B1566167
theorem B1044155 : Blo 1040609 1044155 := bstep (se 1 (by rfl) ⟨783116, by rfl⟩ : syracuseStep 1044155 = 1566233) B1566233
theorem B3960521 : Blo 1040609 3960521 := bstep (se 2 (by rfl) ⟨1485195, by rfl⟩ : syracuseStep 3960521 = 2970391) B2970391
theorem B1044231 : Blo 1040609 1044231 := bstep (se 1 (by rfl) ⟨783173, by rfl⟩ : syracuseStep 1044231 = 1566347) B1566347
theorem B1044239 : Blo 1040609 1044239 := bstep (se 1 (by rfl) ⟨783179, by rfl⟩ : syracuseStep 1044239 = 1566359) B1566359
theorem B1044283 : Blo 1040609 1044283 := bstep (se 1 (by rfl) ⟨783212, by rfl⟩ : syracuseStep 1044283 = 1566425) B1566425
theorem B1044359 : Blo 1040609 1044359 := bstep (se 1 (by rfl) ⟨783269, by rfl⟩ : syracuseStep 1044359 = 1566539) B1566539
theorem B1044367 : Blo 1040609 1044367 := bstep (se 1 (by rfl) ⟨783275, by rfl⟩ : syracuseStep 1044367 = 1566551) B1566551
theorem B6352825 : Blo 1040609 6352825 := bstep (se 2 (by rfl) ⟨2382309, by rfl⟩ : syracuseStep 6352825 = 4764619) B4764619
theorem B1044411 : Blo 1040609 1044411 := bstep (se 1 (by rfl) ⟨783308, by rfl⟩ : syracuseStep 1044411 = 1566617) B1566617
theorem B1044487 : Blo 1040609 1044487 := bstep (se 1 (by rfl) ⟨783365, by rfl⟩ : syracuseStep 1044487 = 1566731) B1566731
theorem B1044495 : Blo 1040609 1044495 := bstep (se 1 (by rfl) ⟨783371, by rfl⟩ : syracuseStep 1044495 = 1566743) B1566743
theorem B1044539 : Blo 1040609 1044539 := bstep (se 1 (by rfl) ⟨783404, by rfl⟩ : syracuseStep 1044539 = 1566809) B1566809
theorem B14283229 : Blo 1040609 14283229 := bstep (se 3 (by rfl) ⟨2678105, by rfl⟩ : syracuseStep 14283229 = 5356211) B5356211
theorem B1667719 : Blo 1040609 1667719 := bstep (se 1 (by rfl) ⟨1250789, by rfl⟩ : syracuseStep 1667719 = 2501579) B2501579
theorem B5927681 : Blo 1040609 5927681 := bstep (se 2 (by rfl) ⟨2222880, by rfl⟩ : syracuseStep 5927681 = 4445761) B4445761
theorem B1504057 : Blo 1040609 1504057 := bstep (se 2 (by rfl) ⟨564021, by rfl⟩ : syracuseStep 1504057 = 1128043) B1128043
theorem B2814977 : Blo 1040609 2814977 := bstep (se 2 (by rfl) ⟨1055616, by rfl⟩ : syracuseStep 2814977 = 2111233) B2111233
theorem B5928137 : Blo 1040609 5928137 := bstep (se 2 (by rfl) ⟨2223051, by rfl⟩ : syracuseStep 5928137 = 4446103) B4446103
theorem B5633225 : Blo 1040609 5633225 := bstep (se 2 (by rfl) ⟨2112459, by rfl⟩ : syracuseStep 5633225 = 4224919) B4224919
theorem B3962297 : Blo 1040609 3962297 := bstep (se 2 (by rfl) ⟨1485861, by rfl⟩ : syracuseStep 3962297 = 2971723) B2971723
theorem B6780419 : Blo 1040609 6780419 := bstep (se 1 (by rfl) ⟨5085314, by rfl⟩ : syracuseStep 6780419 = 10170629) B10170629
theorem B5273099 : Blo 1040609 5273099 := bstep (se 1 (by rfl) ⟨3954824, by rfl⟩ : syracuseStep 5273099 = 7909649) B7909649
theorem B5273261 : Blo 1040609 5273261 := bstep (se 3 (by rfl) ⟨988736, by rfl⟩ : syracuseStep 5273261 = 1977473) B1977473
theorem B3176279 : Blo 1040609 3176279 := bstep (se 1 (by rfl) ⟨2382209, by rfl⟩ : syracuseStep 3176279 = 4764419) B4764419
theorem B3340217 : Blo 1040609 3340217 := bstep (se 2 (by rfl) ⟨1252581, by rfl⟩ : syracuseStep 3340217 = 2505163) B2505163
theorem B1144891 : Blo 1040609 1144891 := bstep (se 1 (by rfl) ⟨858668, by rfl⟩ : syracuseStep 1144891 = 1717337) B1717337
theorem B5503177 : Blo 1040609 5503177 := bstep (se 2 (by rfl) ⟨2063691, by rfl⟩ : syracuseStep 5503177 = 4127383) B4127383
theorem B1506319 : Blo 1040609 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B2817053 : Blo 1040609 2817053 := bstep (se 3 (by rfl) ⟨528197, by rfl⟩ : syracuseStep 2817053 = 1056395) B1056395
theorem B5274881 : Blo 1040609 5274881 := bstep (se 2 (by rfl) ⟨1978080, by rfl⟩ : syracuseStep 5274881 = 3956161) B3956161
theorem B4455739 : Blo 1040609 4455739 := bstep (se 1 (by rfl) ⟨3341804, by rfl⟩ : syracuseStep 4455739 = 6683609) B6683609
theorem B1670519 : Blo 1040609 1670519 := bstep (se 1 (by rfl) ⟨1252889, by rfl⟩ : syracuseStep 1670519 = 2505779) B2505779
theorem B2227657 : Blo 1040609 2227657 := bstep (se 2 (by rfl) ⟨835371, by rfl⟩ : syracuseStep 2227657 = 1670743) B1670743
theorem B2817737 : Blo 1040609 2817737 := bstep (se 2 (by rfl) ⟨1056651, by rfl⟩ : syracuseStep 2817737 = 2113303) B2113303
theorem B3342113 : Blo 1040609 3342113 := bstep (se 2 (by rfl) ⟨1253292, by rfl⟩ : syracuseStep 3342113 = 2506585) B2506585
theorem B3342215 : Blo 1040609 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B13369373 : Blo 1040609 13369373 := bstep (se 3 (by rfl) ⟨2506757, by rfl⟩ : syracuseStep 13369373 = 5013515) B5013515
theorem B21398579 : Blo 1040609 21398579 := bstep (se 1 (by rfl) ⟨16048934, by rfl⟩ : syracuseStep 21398579 = 32097869) B32097869
theorem B4457551 : Blo 1040609 4457551 := bstep (se 1 (by rfl) ⟨3343163, by rfl⟩ : syracuseStep 4457551 = 6686327) B6686327
theorem B5276825 : Blo 1040609 5276825 := bstep (se 2 (by rfl) ⟨1978809, by rfl⟩ : syracuseStep 5276825 = 3957619) B3957619
theorem B7931033 : Blo 1040609 7931033 := bstep (se 2 (by rfl) ⟨2974137, by rfl⟩ : syracuseStep 7931033 = 5948275) B5948275
theorem B4228291 : Blo 1040609 4228291 := bstep (se 1 (by rfl) ⟨3171218, by rfl⟩ : syracuseStep 4228291 = 6342437) B6342437
theorem B14451929 : Blo 1040609 14451929 := bstep (se 2 (by rfl) ⟨5419473, by rfl⟩ : syracuseStep 14451929 = 10838947) B10838947
theorem B38078099 : Blo 1040609 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B8915305 : Blo 1040609 8915305 := bstep (se 2 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 8915305 = 6686479) B6686479
theorem B1411511 : Blo 1040609 1411511 := bstep (se 1 (by rfl) ⟨1058633, by rfl⟩ : syracuseStep 1411511 = 2117267) B2117267
theorem B5704225 : Blo 1040609 5704225 := bstep (se 2 (by rfl) ⟨2139084, by rfl⟩ : syracuseStep 5704225 = 4278169) B4278169
theorem B3345085 : Blo 1040609 3345085 := bstep (se 3 (by rfl) ⟨627203, by rfl⟩ : syracuseStep 3345085 = 1254407) B1254407
theorem B26677025 : Blo 1040609 26677025 := bstep (se 2 (by rfl) ⟨10003884, by rfl⟩ : syracuseStep 26677025 = 20007769) B20007769
theorem B16912313 : Blo 1040609 16912313 := bstep (se 2 (by rfl) ⟨6342117, by rfl⟩ : syracuseStep 16912313 = 12684235) B12684235
theorem B13373369 : Blo 1040609 13373369 := bstep (se 2 (by rfl) ⟨5015013, by rfl⟩ : syracuseStep 13373369 = 10030027) B10030027
theorem B17797805 : Blo 1040609 17797805 := bstep (se 3 (by rfl) ⟨3337088, by rfl⟩ : syracuseStep 17797805 = 6674177) B6674177
theorem B8033701 : Blo 1040609 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B8459693 : Blo 1040609 8459693 := bstep (se 3 (by rfl) ⟨1586192, by rfl⟩ : syracuseStep 8459693 = 3172385) B3172385
theorem B3512159 : Blo 1040609 3512159 := bstep (se 1 (by rfl) ⟨2634119, by rfl⟩ : syracuseStep 3512159 = 5268239) B5268239
theorem B19044305 : Blo 1040609 19044305 := bstep (se 2 (by rfl) ⟨7141614, by rfl⟩ : syracuseStep 19044305 = 14283229) B14283229
theorem B3512321 : Blo 1040609 3512321 := bstep (se 2 (by rfl) ⟨1317120, by rfl⟩ : syracuseStep 3512321 = 2634241) B2634241
theorem B10033409 : Blo 1040609 10033409 := bstep (se 2 (by rfl) ⟨3762528, by rfl⟩ : syracuseStep 10033409 = 7525057) B7525057
theorem B13343129 : Blo 1040609 13343129 := bstep (se 2 (by rfl) ⟨5003673, by rfl⟩ : syracuseStep 13343129 = 10007347) B10007347
theorem B2005409 : Blo 1040609 2005409 := bstep (se 2 (by rfl) ⟨752028, by rfl⟩ : syracuseStep 2005409 = 1504057) B1504057
theorem B1055431 : Blo 1040609 1055431 := bstep (se 1 (by rfl) ⟨791573, by rfl⟩ : syracuseStep 1055431 = 1583147) B1583147
theorem B3513131 : Blo 1040609 3513131 := bstep (se 1 (by rfl) ⟨2634848, by rfl⟩ : syracuseStep 3513131 = 5269697) B5269697
theorem B17832797 : Blo 1040609 17832797 := bstep (se 3 (by rfl) ⟨3343649, by rfl⟩ : syracuseStep 17832797 = 6687299) B6687299
theorem B11279249 : Blo 1040609 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B8919953 : Blo 1040609 8919953 := bstep (se 2 (by rfl) ⟨3344982, by rfl⟩ : syracuseStep 8919953 = 6689965) B6689965
theorem B3513401 : Blo 1040609 3513401 := bstep (se 2 (by rfl) ⟨1317525, by rfl⟩ : syracuseStep 3513401 = 2635051) B2635051
theorem B15047927 : Blo 1040609 15047927 := bstep (se 1 (by rfl) ⟨11285945, by rfl⟩ : syracuseStep 15047927 = 22571891) B22571891
theorem B3513725 : Blo 1040609 3513725 := bstep (se 3 (by rfl) ⟨658823, by rfl⟩ : syracuseStep 3513725 = 1317647) B1317647
theorem B5709221 : Blo 1040609 5709221 := bstep (se 4 (by rfl) ⟨535239, by rfl⟩ : syracuseStep 5709221 = 1070479) B1070479
theorem B3513995 : Blo 1040609 3513995 := bstep (se 1 (by rfl) ⟨2635496, by rfl⟩ : syracuseStep 3513995 = 5270993) B5270993
theorem B5283467 : Blo 1040609 5283467 := bstep (se 1 (by rfl) ⟨3962600, by rfl⟩ : syracuseStep 5283467 = 7925201) B7925201
theorem B5644403 : Blo 1040609 5644403 := bstep (se 1 (by rfl) ⟨4233302, by rfl⟩ : syracuseStep 5644403 = 8466605) B8466605
theorem B3514913 : Blo 1040609 3514913 := bstep (se 2 (by rfl) ⟨1318092, by rfl⟩ : syracuseStep 3514913 = 2636185) B2636185
theorem B1253927 : Blo 1040609 1253927 := bstep (se 1 (by rfl) ⟨940445, by rfl⟩ : syracuseStep 1253927 = 1880891) B1880891
theorem B1876651 : Blo 1040609 1876651 := bstep (se 1 (by rfl) ⟨1407488, by rfl⟩ : syracuseStep 1876651 = 2814977) B2814977
theorem B1188551 : Blo 1040609 1188551 := bstep (se 1 (by rfl) ⟨891413, by rfl⟩ : syracuseStep 1188551 = 1782827) B1782827
theorem B3810007 : Blo 1040609 3810007 := bstep (se 1 (by rfl) ⟨2857505, by rfl⟩ : syracuseStep 3810007 = 5715011) B5715011
theorem B3515129 : Blo 1040609 3515129 := bstep (se 2 (by rfl) ⟨1318173, by rfl⟩ : syracuseStep 3515129 = 2636347) B2636347
theorem B3515399 : Blo 1040609 3515399 := bstep (se 1 (by rfl) ⟨2636549, by rfl⟩ : syracuseStep 3515399 = 5273099) B5273099
theorem B3515507 : Blo 1040609 3515507 := bstep (se 1 (by rfl) ⟨2636630, by rfl⟩ : syracuseStep 3515507 = 5273261) B5273261
theorem B1254523 : Blo 1040609 1254523 := bstep (se 1 (by rfl) ⟨940892, by rfl⟩ : syracuseStep 1254523 = 1881785) B1881785
theorem B15017309 : Blo 1040609 15017309 := bstep (se 3 (by rfl) ⟨2815745, by rfl⟩ : syracuseStep 15017309 = 5631491) B5631491
theorem B3515777 : Blo 1040609 3515777 := bstep (se 2 (by rfl) ⟨1318416, by rfl⟩ : syracuseStep 3515777 = 2636833) B2636833
theorem B7906733 : Blo 1040609 7906733 := bstep (se 3 (by rfl) ⟨1482512, by rfl⟩ : syracuseStep 7906733 = 2965025) B2965025
theorem B1975727 : Blo 1040609 1975727 := bstep (se 1 (by rfl) ⟨1481795, by rfl⟩ : syracuseStep 1975727 = 2963591) B2963591
theorem B1058383 : Blo 1040609 1058383 := bstep (se 1 (by rfl) ⟨793787, by rfl⟩ : syracuseStep 1058383 = 1587575) B1587575
theorem B5940985 : Blo 1040609 5940985 := bstep (se 2 (by rfl) ⟨2227869, by rfl⟩ : syracuseStep 5940985 = 4455739) B4455739
theorem B1320887 : Blo 1040609 1320887 := bstep (se 1 (by rfl) ⟨990665, by rfl⟩ : syracuseStep 1320887 = 1981331) B1981331
theorem B1976251 : Blo 1040609 1976251 := bstep (se 1 (by rfl) ⟨1482188, by rfl⟩ : syracuseStep 1976251 = 2964377) B2964377
theorem B16885709 : Blo 1040609 16885709 := bstep (se 3 (by rfl) ⟨3166070, by rfl⟩ : syracuseStep 16885709 = 6332141) B6332141
theorem B1878035 : Blo 1040609 1878035 := bstep (se 1 (by rfl) ⟨1408526, by rfl⟩ : syracuseStep 1878035 = 2817053) B2817053
theorem B1321039 : Blo 1040609 1321039 := bstep (se 1 (by rfl) ⟨990779, by rfl⟩ : syracuseStep 1321039 = 1981559) B1981559
theorem B3516587 : Blo 1040609 3516587 := bstep (se 1 (by rfl) ⟨2637440, by rfl⟩ : syracuseStep 3516587 = 5274881) B5274881
theorem B1976737 : Blo 1040609 1976737 := bstep (se 2 (by rfl) ⟨741276, by rfl⟩ : syracuseStep 1976737 = 1482553) B1482553
theorem B1878491 : Blo 1040609 1878491 := bstep (se 1 (by rfl) ⟨1408868, by rfl⟩ : syracuseStep 1878491 = 2817737) B2817737
theorem B1780423 : Blo 1040609 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B3517127 : Blo 1040609 3517127 := bstep (se 1 (by rfl) ⟨2637845, by rfl⟩ : syracuseStep 3517127 = 5275691) B5275691
theorem B7514909 : Blo 1040609 7514909 := bstep (se 3 (by rfl) ⟨1409045, by rfl⟩ : syracuseStep 7514909 = 2818091) B2818091
theorem B5942443 : Blo 1040609 5942443 := bstep (se 1 (by rfl) ⟨4456832, by rfl⟩ : syracuseStep 5942443 = 8913665) B8913665
theorem B6008003 : Blo 1040609 6008003 := bstep (se 1 (by rfl) ⟨4506002, by rfl⟩ : syracuseStep 6008003 = 9012005) B9012005
theorem B1879391 : Blo 1040609 1879391 := bstep (se 1 (by rfl) ⟨1409543, by rfl⟩ : syracuseStep 1879391 = 2819087) B2819087
theorem B7613939 : Blo 1040609 7613939 := bstep (se 1 (by rfl) ⟨5710454, by rfl⟩ : syracuseStep 7613939 = 11420909) B11420909
theorem B3517991 : Blo 1040609 3517991 := bstep (se 1 (by rfl) ⟨2638493, by rfl⟩ : syracuseStep 3517991 = 5276987) B5276987
theorem B13381159 : Blo 1040609 13381159 := bstep (se 1 (by rfl) ⟨10035869, by rfl⟩ : syracuseStep 13381159 = 20071739) B20071739
theorem B3518099 : Blo 1040609 3518099 := bstep (se 1 (by rfl) ⟨2638574, by rfl⟩ : syracuseStep 3518099 = 5277149) B5277149
theorem B1879723 : Blo 1040609 1879723 := bstep (se 1 (by rfl) ⟨1409792, by rfl⟩ : syracuseStep 1879723 = 2819585) B2819585
theorem B7909163 : Blo 1040609 7909163 := bstep (se 1 (by rfl) ⟨5931872, by rfl⟩ : syracuseStep 7909163 = 11863745) B11863745
theorem B3518315 : Blo 1040609 3518315 := bstep (se 1 (by rfl) ⟨2638736, by rfl⟩ : syracuseStep 3518315 = 5277473) B5277473
theorem B3518369 : Blo 1040609 3518369 := bstep (se 2 (by rfl) ⟨1319388, by rfl⟩ : syracuseStep 3518369 = 2638777) B2638777
theorem B5287841 : Blo 1040609 5287841 := bstep (se 2 (by rfl) ⟨1982940, by rfl⟩ : syracuseStep 5287841 = 3965881) B3965881
theorem B1486927 : Blo 1040609 1486927 := bstep (se 1 (by rfl) ⟨1115195, by rfl⟩ : syracuseStep 1486927 = 2230391) B2230391
theorem B1880393 : Blo 1040609 1880393 := bstep (se 2 (by rfl) ⟨705147, by rfl⟩ : syracuseStep 1880393 = 1410295) B1410295
theorem B3518963 : Blo 1040609 3518963 := bstep (se 1 (by rfl) ⟨2639222, by rfl⟩ : syracuseStep 3518963 = 5278445) B5278445
theorem B1979129 : Blo 1040609 1979129 := bstep (se 2 (by rfl) ⟨742173, by rfl⟩ : syracuseStep 1979129 = 1484347) B1484347
theorem B1979311 : Blo 1040609 1979311 := bstep (se 1 (by rfl) ⟨1484483, by rfl⟩ : syracuseStep 1979311 = 2968967) B2968967
theorem B3519503 : Blo 1040609 3519503 := bstep (se 1 (by rfl) ⟨2639627, by rfl⟩ : syracuseStep 3519503 = 5279255) B5279255
theorem B1979471 : Blo 1040609 1979471 := bstep (se 1 (by rfl) ⟨1484603, by rfl⟩ : syracuseStep 1979471 = 2969207) B2969207
theorem B51328171 : Blo 1040609 51328171 := bstep (se 1 (by rfl) ⟨38496128, by rfl⟩ : syracuseStep 51328171 = 76992257) B76992257
theorem B3520097 : Blo 1040609 3520097 := bstep (se 2 (by rfl) ⟨1320036, by rfl⟩ : syracuseStep 3520097 = 2640073) B2640073
theorem B1357511 : Blo 1040609 1357511 := bstep (se 1 (by rfl) ⟨1018133, by rfl⟩ : syracuseStep 1357511 = 2036267) B2036267
theorem B1881929 : Blo 1040609 1881929 := bstep (se 2 (by rfl) ⟨705723, by rfl⟩ : syracuseStep 1881929 = 1411447) B1411447
theorem B2963375 : Blo 1040609 2963375 := bstep (se 1 (by rfl) ⟨2222531, by rfl⟩ : syracuseStep 2963375 = 4445063) B4445063
theorem B5945359 : Blo 1040609 5945359 := bstep (se 1 (by rfl) ⟨4459019, by rfl⟩ : syracuseStep 5945359 = 8918039) B8918039
theorem B1980587 : Blo 1040609 1980587 := bstep (se 1 (by rfl) ⟨1485440, by rfl⟩ : syracuseStep 1980587 = 2970881) B2970881
theorem B2636023 : Blo 1040609 2636023 := bstep (se 1 (by rfl) ⟨1977017, by rfl⟩ : syracuseStep 2636023 = 3954035) B3954035
theorem B8894771 : Blo 1040609 8894771 := bstep (se 1 (by rfl) ⟨6671078, by rfl⟩ : syracuseStep 8894771 = 13342157) B13342157
theorem B2341385 : Blo 1040609 2341385 := bstep (se 2 (by rfl) ⟨878019, by rfl⟩ : syracuseStep 2341385 = 1756039) B1756039
theorem B2636297 : Blo 1040609 2636297 := bstep (se 2 (by rfl) ⟨988611, by rfl⟩ : syracuseStep 2636297 = 1977223) B1977223
theorem B2636327 : Blo 1040609 2636327 := bstep (se 1 (by rfl) ⟨1977245, by rfl⟩ : syracuseStep 2636327 = 3954491) B3954491
theorem B2505431 : Blo 1040609 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B2341727 : Blo 1040609 2341727 := bstep (se 1 (by rfl) ⟨1756295, by rfl⟩ : syracuseStep 2341727 = 3512591) B3512591
theorem B2636651 : Blo 1040609 2636651 := bstep (se 1 (by rfl) ⟨1977488, by rfl⟩ : syracuseStep 2636651 = 3954977) B3954977
theorem B2341907 : Blo 1040609 2341907 := bstep (se 1 (by rfl) ⟨1756430, by rfl⟩ : syracuseStep 2341907 = 3512861) B3512861
theorem B3521555 : Blo 1040609 3521555 := bstep (se 1 (by rfl) ⟨2641166, by rfl⟩ : syracuseStep 3521555 = 5282333) B5282333
theorem B2964559 : Blo 1040609 2964559 := bstep (se 1 (by rfl) ⟨2223419, by rfl⟩ : syracuseStep 2964559 = 4446839) B4446839
theorem B7519351 : Blo 1040609 7519351 := bstep (se 1 (by rfl) ⟨5639513, by rfl⟩ : syracuseStep 7519351 = 11279027) B11279027
theorem B3521879 : Blo 1040609 3521879 := bstep (se 1 (by rfl) ⟨2641409, by rfl⟩ : syracuseStep 3521879 = 5282819) B5282819
theorem B2342249 : Blo 1040609 2342249 := bstep (se 2 (by rfl) ⟨878343, by rfl⟩ : syracuseStep 2342249 = 1756687) B1756687
theorem B2637299 : Blo 1040609 2637299 := bstep (se 1 (by rfl) ⟨1977974, by rfl⟩ : syracuseStep 2637299 = 3955949) B3955949
theorem B1982303 : Blo 1040609 1982303 := bstep (se 1 (by rfl) ⟨1486727, by rfl⟩ : syracuseStep 1982303 = 2973455) B2973455
theorem B8470433 : Blo 1040609 8470433 := bstep (se 2 (by rfl) ⟨3176412, by rfl⟩ : syracuseStep 8470433 = 6352825) B6352825
theorem B2342843 : Blo 1040609 2342843 := bstep (se 1 (by rfl) ⟨1757132, by rfl⟩ : syracuseStep 2342843 = 3514265) B3514265
theorem B2637755 : Blo 1040609 2637755 := bstep (se 1 (by rfl) ⟨1978316, by rfl⟩ : syracuseStep 2637755 = 3956633) B3956633
theorem B107135011 : Blo 1040609 107135011 := bstep (se 1 (by rfl) ⟨80351258, by rfl⟩ : syracuseStep 107135011 = 160702517) B160702517
theorem B2342969 : Blo 1040609 2342969 := bstep (se 2 (by rfl) ⟨878613, by rfl⟩ : syracuseStep 2342969 = 1757227) B1757227
theorem B2113633 : Blo 1040609 2113633 := bstep (se 2 (by rfl) ⟨792612, by rfl⟩ : syracuseStep 2113633 = 1585225) B1585225
theorem B1982713 : Blo 1040609 1982713 := bstep (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) B1487035
theorem B13353275 : Blo 1040609 13353275 := bstep (se 1 (by rfl) ⟨10014956, by rfl⟩ : syracuseStep 13353275 = 20029913) B20029913
theorem B2343311 : Blo 1040609 2343311 := bstep (se 1 (by rfl) ⟨1757483, by rfl⟩ : syracuseStep 2343311 = 3514967) B3514967
theorem B3522959 : Blo 1040609 3522959 := bstep (se 1 (by rfl) ⟨2642219, by rfl⟩ : syracuseStep 3522959 = 5284439) B5284439
theorem B2113975 : Blo 1040609 2113975 := bstep (se 1 (by rfl) ⟨1585481, by rfl⟩ : syracuseStep 2113975 = 3170963) B3170963
theorem B1983055 : Blo 1040609 1983055 := bstep (se 1 (by rfl) ⟨1487291, by rfl⟩ : syracuseStep 1983055 = 2974583) B2974583
theorem B2638433 : Blo 1040609 2638433 := bstep (se 2 (by rfl) ⟨989412, by rfl⟩ : syracuseStep 2638433 = 1978825) B1978825
theorem B2343635 : Blo 1040609 2343635 := bstep (se 1 (by rfl) ⟨1757726, by rfl⟩ : syracuseStep 2343635 = 3515453) B3515453
theorem B3523283 : Blo 1040609 3523283 := bstep (se 1 (by rfl) ⟨2642462, by rfl⟩ : syracuseStep 3523283 = 5284925) B5284925
theorem B13747097 : Blo 1040609 13747097 := bstep (se 2 (by rfl) ⟨5155161, by rfl⟩ : syracuseStep 13747097 = 10310323) B10310323
theorem B2507681 : Blo 1040609 2507681 := bstep (se 2 (by rfl) ⟨940380, by rfl⟩ : syracuseStep 2507681 = 1880761) B1880761
theorem B7914995 : Blo 1040609 7914995 := bstep (se 1 (by rfl) ⟨5936246, by rfl⟩ : syracuseStep 7914995 = 11872493) B11872493
theorem B12699125 : Blo 1040609 12699125 := bstep (se 5 (by rfl) ⟨595271, by rfl⟩ : syracuseStep 12699125 = 1190543) B1190543
theorem B2344571 : Blo 1040609 2344571 := bstep (se 1 (by rfl) ⟨1758428, by rfl⟩ : syracuseStep 2344571 = 3516857) B3516857
theorem B1427143 : Blo 1040609 1427143 := bstep (se 1 (by rfl) ⟨1070357, by rfl⟩ : syracuseStep 1427143 = 2140715) B2140715
theorem B2344697 : Blo 1040609 2344697 := bstep (se 2 (by rfl) ⟨879261, by rfl⟩ : syracuseStep 2344697 = 1758523) B1758523
theorem B16893755 : Blo 1040609 16893755 := bstep (se 1 (by rfl) ⟨12670316, by rfl⟩ : syracuseStep 16893755 = 25340633) B25340633
theorem B60868421 : Blo 1040609 60868421 := bstep (se 4 (by rfl) ⟨5706414, by rfl⟩ : syracuseStep 60868421 = 11412829) B11412829
theorem B3524471 : Blo 1040609 3524471 := bstep (se 1 (by rfl) ⟨2643353, by rfl⟩ : syracuseStep 3524471 = 5286707) B5286707
theorem B2344967 : Blo 1040609 2344967 := bstep (se 1 (by rfl) ⟨1758725, by rfl⟩ : syracuseStep 2344967 = 3517451) B3517451
theorem B2639891 : Blo 1040609 2639891 := bstep (se 1 (by rfl) ⟨1979918, by rfl⟩ : syracuseStep 2639891 = 3959837) B3959837
theorem B1693894679 : Blo 1040609 1693894679 := bstep (se 1 (by rfl) ⟨1270421009, by rfl⟩ : syracuseStep 1693894679 = 2540842019) B2540842019
theorem B11290661 : Blo 1040609 11290661 := bstep (se 4 (by rfl) ⟨1058499, by rfl⟩ : syracuseStep 11290661 = 2116999) B2116999
theorem B2345039 : Blo 1040609 2345039 := bstep (se 1 (by rfl) ⟨1758779, by rfl⟩ : syracuseStep 2345039 = 3517559) B3517559
theorem B3524687 : Blo 1040609 3524687 := bstep (se 1 (by rfl) ⟨2643515, by rfl⟩ : syracuseStep 3524687 = 5287031) B5287031
theorem B6670745 : Blo 1040609 6670745 := bstep (se 2 (by rfl) ⟨2501529, by rfl⟩ : syracuseStep 6670745 = 5003059) B5003059
theorem B12863897 : Blo 1040609 12863897 := bstep (se 2 (by rfl) ⟨4823961, by rfl⟩ : syracuseStep 12863897 = 9647923) B9647923
theorem B3525065 : Blo 1040609 3525065 := bstep (se 2 (by rfl) ⟨1321899, by rfl⟩ : syracuseStep 3525065 = 2643799) B2643799
theorem B6670795 : Blo 1040609 6670795 := bstep (se 1 (by rfl) ⟨5003096, by rfl⟩ : syracuseStep 6670795 = 10006193) B10006193
theorem B2345435 : Blo 1040609 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B2640347 : Blo 1040609 2640347 := bstep (se 1 (by rfl) ⟨1980260, by rfl⟩ : syracuseStep 2640347 = 3960521) B3960521
theorem B3525335 : Blo 1040609 3525335 := bstep (se 1 (by rfl) ⟨2644001, by rfl⟩ : syracuseStep 3525335 = 5288003) B5288003
theorem B1526521 : Blo 1040609 1526521 := bstep (se 2 (by rfl) ⟨572445, by rfl⟩ : syracuseStep 1526521 = 1144891) B1144891
theorem B2345903 : Blo 1040609 2345903 := bstep (se 1 (by rfl) ⟨1759427, by rfl⟩ : syracuseStep 2345903 = 3518855) B3518855
theorem B3525551 : Blo 1040609 3525551 := bstep (se 1 (by rfl) ⟨2644163, by rfl⟩ : syracuseStep 3525551 = 5288327) B5288327
theorem B3951773 : Blo 1040609 3951773 := bstep (se 3 (by rfl) ⟨740957, by rfl⟩ : syracuseStep 3951773 = 1481915) B1481915
theorem B3951787 : Blo 1040609 3951787 := bstep (se 1 (by rfl) ⟨2963840, by rfl⟩ : syracuseStep 3951787 = 5927681) B5927681
theorem B2346155 : Blo 1040609 2346155 := bstep (se 1 (by rfl) ⟨1759616, by rfl⟩ : syracuseStep 2346155 = 3519233) B3519233
theorem B13716773 : Blo 1040609 13716773 := bstep (se 4 (by rfl) ⟨1285947, by rfl⟩ : syracuseStep 13716773 = 2571895) B2571895
theorem B1756559 : Blo 1040609 1756559 := bstep (se 1 (by rfl) ⟨1317419, by rfl⟩ : syracuseStep 1756559 = 2634839) B2634839
theorem B3952091 : Blo 1040609 3952091 := bstep (se 1 (by rfl) ⟨2964068, by rfl⟩ : syracuseStep 3952091 = 5928137) B5928137
theorem B3755483 : Blo 1040609 3755483 := bstep (se 1 (by rfl) ⟨2816612, by rfl⟩ : syracuseStep 3755483 = 5633225) B5633225
theorem B1756795 : Blo 1040609 1756795 := bstep (se 1 (by rfl) ⟨1317596, by rfl⟩ : syracuseStep 1756795 = 2635193) B2635193
theorem B2641531 : Blo 1040609 2641531 := bstep (se 1 (by rfl) ⟨1981148, by rfl⟩ : syracuseStep 2641531 = 3962297) B3962297
theorem B5000849 : Blo 1040609 5000849 := bstep (se 2 (by rfl) ⟨1875318, by rfl⟩ : syracuseStep 5000849 = 3750637) B3750637
theorem B2346695 : Blo 1040609 2346695 := bstep (se 1 (by rfl) ⟨1760021, by rfl⟩ : syracuseStep 2346695 = 3520043) B3520043
theorem B7130861 : Blo 1040609 7130861 := bstep (se 3 (by rfl) ⟨1337036, by rfl⟩ : syracuseStep 7130861 = 2674073) B2674073
theorem B2117519 : Blo 1040609 2117519 := bstep (se 1 (by rfl) ⟨1588139, by rfl⟩ : syracuseStep 2117519 = 3176279) B3176279
theorem B8147249 : Blo 1040609 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B7917911 : Blo 1040609 7917911 := bstep (se 1 (by rfl) ⟨5938433, by rfl⟩ : syracuseStep 7917911 = 11876867) B11876867
theorem B1561007 : Blo 1040609 1561007 := bstep (se 1 (by rfl) ⟨1170755, by rfl⟩ : syracuseStep 1561007 = 2341511) B2341511
theorem B1757659 : Blo 1040609 1757659 := bstep (se 1 (by rfl) ⟨1318244, by rfl⟩ : syracuseStep 1757659 = 2636489) B2636489
theorem B1561097 : Blo 1040609 1561097 := bstep (se 2 (by rfl) ⟨585411, by rfl⟩ : syracuseStep 1561097 = 1170823) B1170823
theorem B1561127 : Blo 1040609 1561127 := bstep (se 1 (by rfl) ⟨1170845, by rfl⟩ : syracuseStep 1561127 = 2341691) B2341691
theorem B2347559 : Blo 1040609 2347559 := bstep (se 1 (by rfl) ⟨1760669, by rfl⟩ : syracuseStep 2347559 = 3521339) B3521339
theorem B2970209 : Blo 1040609 2970209 := bstep (se 2 (by rfl) ⟨1113828, by rfl⟩ : syracuseStep 2970209 = 2227657) B2227657
theorem B1561211 : Blo 1040609 1561211 := bstep (se 1 (by rfl) ⟨1170908, by rfl⟩ : syracuseStep 1561211 = 2341817) B2341817
theorem B1561337 : Blo 1040609 1561337 := bstep (se 2 (by rfl) ⟨585501, by rfl⟩ : syracuseStep 1561337 = 1171003) B1171003
theorem B1561439 : Blo 1040609 1561439 := bstep (se 1 (by rfl) ⟨1171079, by rfl⟩ : syracuseStep 1561439 = 2342159) B2342159
theorem B1561451 : Blo 1040609 1561451 := bstep (se 1 (by rfl) ⟨1171088, by rfl⟩ : syracuseStep 1561451 = 2342177) B2342177
theorem B2347883 : Blo 1040609 2347883 := bstep (se 1 (by rfl) ⟨1760912, by rfl⟩ : syracuseStep 2347883 = 3521825) B3521825
theorem B2347937 : Blo 1040609 2347937 := bstep (se 2 (by rfl) ⟨880476, by rfl⟩ : syracuseStep 2347937 = 1760953) B1760953
theorem B1561679 : Blo 1040609 1561679 := bstep (se 1 (by rfl) ⟨1171259, by rfl⟩ : syracuseStep 1561679 = 2342519) B2342519
theorem B1758287 : Blo 1040609 1758287 := bstep (se 1 (by rfl) ⟨1318715, by rfl⟩ : syracuseStep 1758287 = 2637431) B2637431
theorem B1561799 : Blo 1040609 1561799 := bstep (se 1 (by rfl) ⟨1171349, by rfl⟩ : syracuseStep 1561799 = 2342699) B2342699
theorem B2348279 : Blo 1040609 2348279 := bstep (se 1 (by rfl) ⟨1761209, by rfl⟩ : syracuseStep 2348279 = 3522419) B3522419
theorem B1561961 : Blo 1040609 1561961 := bstep (se 2 (by rfl) ⟨585735, by rfl⟩ : syracuseStep 1561961 = 1171471) B1171471
theorem B1562039 : Blo 1040609 1562039 := bstep (se 1 (by rfl) ⟨1171529, by rfl⟩ : syracuseStep 1562039 = 2343059) B2343059
theorem B1562075 : Blo 1040609 1562075 := bstep (se 1 (by rfl) ⟨1171556, by rfl⟩ : syracuseStep 1562075 = 2343113) B2343113
theorem B243619649 : Blo 1040609 243619649 := bstep (se 2 (by rfl) ⟨91357368, by rfl⟩ : syracuseStep 243619649 = 182714737) B182714737
theorem B2348873 : Blo 1040609 2348873 := bstep (se 2 (by rfl) ⟨880827, by rfl⟩ : syracuseStep 2348873 = 1761655) B1761655
theorem B7231393 : Blo 1040609 7231393 := bstep (se 2 (by rfl) ⟨2711772, by rfl⟩ : syracuseStep 7231393 = 5423545) B5423545
theorem B1562543 : Blo 1040609 1562543 := bstep (se 1 (by rfl) ⟨1171907, by rfl⟩ : syracuseStep 1562543 = 2343815) B2343815
theorem B1759151 : Blo 1040609 1759151 := bstep (se 1 (by rfl) ⟨1319363, by rfl⟩ : syracuseStep 1759151 = 2638727) B2638727
theorem B3954689 : Blo 1040609 3954689 := bstep (se 2 (by rfl) ⟨1483008, by rfl⟩ : syracuseStep 3954689 = 2966017) B2966017
theorem B1562633 : Blo 1040609 1562633 := bstep (se 2 (by rfl) ⟨585987, by rfl⟩ : syracuseStep 1562633 = 1171975) B1171975
theorem B3954703 : Blo 1040609 3954703 := bstep (se 1 (by rfl) ⟨2966027, by rfl⟩ : syracuseStep 3954703 = 5932055) B5932055
theorem B2971667 : Blo 1040609 2971667 := bstep (se 1 (by rfl) ⟨2228750, by rfl⟩ : syracuseStep 2971667 = 4457501) B4457501
theorem B1562663 : Blo 1040609 1562663 := bstep (se 1 (by rfl) ⟨1171997, by rfl⟩ : syracuseStep 1562663 = 2343995) B2343995
theorem B1562747 : Blo 1040609 1562747 := bstep (se 1 (by rfl) ⟨1172060, by rfl⟩ : syracuseStep 1562747 = 2344121) B2344121
theorem B1562873 : Blo 1040609 1562873 := bstep (se 2 (by rfl) ⟨586077, by rfl⟩ : syracuseStep 1562873 = 1172155) B1172155
theorem B1562975 : Blo 1040609 1562975 := bstep (se 1 (by rfl) ⟨1172231, by rfl⟩ : syracuseStep 1562975 = 2344463) B2344463
theorem B1759583 : Blo 1040609 1759583 := bstep (se 1 (by rfl) ⟨1319687, by rfl⟩ : syracuseStep 1759583 = 2639375) B2639375
theorem B1562987 : Blo 1040609 1562987 := bstep (se 1 (by rfl) ⟨1172240, by rfl⟩ : syracuseStep 1562987 = 2344481) B2344481
theorem B29350277 : Blo 1040609 29350277 := bstep (se 4 (by rfl) ⟨2751588, by rfl⟩ : syracuseStep 29350277 = 5503177) B5503177
theorem B7526789 : Blo 1040609 7526789 := bstep (se 4 (by rfl) ⟨705636, by rfl⟩ : syracuseStep 7526789 = 1411273) B1411273
theorem B2972123 : Blo 1040609 2972123 := bstep (se 1 (by rfl) ⟨2229092, by rfl⟩ : syracuseStep 2972123 = 4458185) B4458185
theorem B1563215 : Blo 1040609 1563215 := bstep (se 1 (by rfl) ⟨1172411, by rfl⟩ : syracuseStep 1563215 = 2344823) B2344823
theorem B2349665 : Blo 1040609 2349665 := bstep (se 2 (by rfl) ⟨881124, by rfl⟩ : syracuseStep 2349665 = 1762249) B1762249
theorem B1563335 : Blo 1040609 1563335 := bstep (se 1 (by rfl) ⟨1172501, by rfl⟩ : syracuseStep 1563335 = 2345003) B2345003
theorem B8444675 : Blo 1040609 8444675 := bstep (se 1 (by rfl) ⟨6333506, by rfl⟩ : syracuseStep 8444675 = 12667013) B12667013
theorem B6675203 : Blo 1040609 6675203 := bstep (se 1 (by rfl) ⟨5006402, by rfl⟩ : syracuseStep 6675203 = 10012805) B10012805
theorem B1563497 : Blo 1040609 1563497 := bstep (se 2 (by rfl) ⟨586311, by rfl⟩ : syracuseStep 1563497 = 1172623) B1172623
theorem B1760143 : Blo 1040609 1760143 := bstep (se 1 (by rfl) ⟨1320107, by rfl⟩ : syracuseStep 1760143 = 2640215) B2640215
theorem B1563575 : Blo 1040609 1563575 := bstep (se 1 (by rfl) ⟨1172681, by rfl⟩ : syracuseStep 1563575 = 2345363) B2345363
theorem B2350007 : Blo 1040609 2350007 := bstep (se 1 (by rfl) ⟨1762505, by rfl⟩ : syracuseStep 2350007 = 3525011) B3525011
theorem B1563611 : Blo 1040609 1563611 := bstep (se 1 (by rfl) ⟨1172708, by rfl⟩ : syracuseStep 1563611 = 2345417) B2345417
theorem B3955979 : Blo 1040609 3955979 := bstep (se 1 (by rfl) ⟨2966984, by rfl⟩ : syracuseStep 3955979 = 5933969) B5933969
theorem B1564079 : Blo 1040609 1564079 := bstep (se 1 (by rfl) ⟨1173059, by rfl⟩ : syracuseStep 1564079 = 2346119) B2346119
theorem B1564169 : Blo 1040609 1564169 := bstep (se 2 (by rfl) ⟨586563, by rfl⟩ : syracuseStep 1564169 = 1173127) B1173127
theorem B1564199 : Blo 1040609 1564199 := bstep (se 1 (by rfl) ⟨1173149, by rfl⟩ : syracuseStep 1564199 = 2346299) B2346299
theorem B1760825 : Blo 1040609 1760825 := bstep (se 2 (by rfl) ⟨660309, by rfl⟩ : syracuseStep 1760825 = 1320619) B1320619
theorem B1564283 : Blo 1040609 1564283 := bstep (se 1 (by rfl) ⟨1173212, by rfl⟩ : syracuseStep 1564283 = 2346425) B2346425
theorem B2973307 : Blo 1040609 2973307 := bstep (se 1 (by rfl) ⟨2229980, by rfl⟩ : syracuseStep 2973307 = 4459961) B4459961
theorem B3956435 : Blo 1040609 3956435 := bstep (se 1 (by rfl) ⟨2967326, by rfl⟩ : syracuseStep 3956435 = 5934653) B5934653
theorem B1564409 : Blo 1040609 1564409 := bstep (se 2 (by rfl) ⟨586653, by rfl⟩ : syracuseStep 1564409 = 1173307) B1173307
theorem B1564511 : Blo 1040609 1564511 := bstep (se 1 (by rfl) ⟨1173383, by rfl⟩ : syracuseStep 1564511 = 2346767) B2346767
theorem B1564523 : Blo 1040609 1564523 := bstep (se 1 (by rfl) ⟨1173392, by rfl⟩ : syracuseStep 1564523 = 2346785) B2346785
theorem B32563063 : Blo 1040609 32563063 := bstep (se 1 (by rfl) ⟨24422297, by rfl⟩ : syracuseStep 32563063 = 48844595) B48844595
theorem B12214151 : Blo 1040609 12214151 := bstep (se 1 (by rfl) ⟨9160613, by rfl⟩ : syracuseStep 12214151 = 18321227) B18321227
theorem B101638091 : Blo 1040609 101638091 := bstep (se 1 (by rfl) ⟨76228568, by rfl⟩ : syracuseStep 101638091 = 152457137) B152457137
theorem B1564751 : Blo 1040609 1564751 := bstep (se 1 (by rfl) ⟨1173563, by rfl⟩ : syracuseStep 1564751 = 2347127) B2347127
theorem B1171579 : Blo 1040609 1171579 := bstep (se 1 (by rfl) ⟨878684, by rfl⟩ : syracuseStep 1171579 = 1757369) B1757369
theorem B1564871 : Blo 1040609 1564871 := bstep (se 1 (by rfl) ⟨1173653, by rfl⟩ : syracuseStep 1564871 = 2347307) B2347307
theorem B1761527 : Blo 1040609 1761527 := bstep (se 1 (by rfl) ⟨1321145, by rfl⟩ : syracuseStep 1761527 = 2642291) B2642291
theorem B1040679 : Blo 1040609 1040679 := bstep (se 1 (by rfl) ⟨780509, by rfl⟩ : syracuseStep 1040679 = 1561019) B1561019
theorem B1040719 : Blo 1040609 1040719 := bstep (se 1 (by rfl) ⟨780539, by rfl⟩ : syracuseStep 1040719 = 1561079) B1561079
theorem B1040735 : Blo 1040609 1040735 := bstep (se 1 (by rfl) ⟨780551, by rfl⟩ : syracuseStep 1040735 = 1561103) B1561103
theorem B1565033 : Blo 1040609 1565033 := bstep (se 2 (by rfl) ⟨586887, by rfl⟩ : syracuseStep 1565033 = 1173775) B1173775
theorem B1040763 : Blo 1040609 1040763 := bstep (se 1 (by rfl) ⟨780572, by rfl⟩ : syracuseStep 1040763 = 1561145) B1561145
theorem B1040815 : Blo 1040609 1040815 := bstep (se 1 (by rfl) ⟨780611, by rfl⟩ : syracuseStep 1040815 = 1561223) B1561223
theorem B1565111 : Blo 1040609 1565111 := bstep (se 1 (by rfl) ⟨1173833, by rfl⟩ : syracuseStep 1565111 = 2347667) B2347667
theorem B1040839 : Blo 1040609 1040839 := bstep (se 1 (by rfl) ⟨780629, by rfl⟩ : syracuseStep 1040839 = 1561259) B1561259
theorem B1040859 : Blo 1040609 1040859 := bstep (se 1 (by rfl) ⟨780644, by rfl⟩ : syracuseStep 1040859 = 1561289) B1561289
theorem B1565147 : Blo 1040609 1565147 := bstep (se 1 (by rfl) ⟨1173860, by rfl⟩ : syracuseStep 1565147 = 2347721) B2347721
theorem B3760627 : Blo 1040609 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B1040935 : Blo 1040609 1040935 := bstep (se 1 (by rfl) ⟨780701, by rfl⟩ : syracuseStep 1040935 = 1561403) B1561403
theorem B1040975 : Blo 1040609 1040975 := bstep (se 1 (by rfl) ⟨780731, by rfl⟩ : syracuseStep 1040975 = 1561463) B1561463
theorem B1172047 : Blo 1040609 1172047 := bstep (se 1 (by rfl) ⟨879035, by rfl⟩ : syracuseStep 1172047 = 1758071) B1758071
theorem B1761871 : Blo 1040609 1761871 := bstep (se 1 (by rfl) ⟨1321403, by rfl⟩ : syracuseStep 1761871 = 2642807) B2642807
theorem B1040991 : Blo 1040609 1040991 := bstep (se 1 (by rfl) ⟨780743, by rfl⟩ : syracuseStep 1040991 = 1561487) B1561487
theorem B1041019 : Blo 1040609 1041019 := bstep (se 1 (by rfl) ⟨780764, by rfl⟩ : syracuseStep 1041019 = 1561529) B1561529
theorem B1041071 : Blo 1040609 1041071 := bstep (se 1 (by rfl) ⟨780803, by rfl⟩ : syracuseStep 1041071 = 1561607) B1561607
theorem B3957437 : Blo 1040609 3957437 := bstep (se 3 (by rfl) ⟨742019, by rfl⟩ : syracuseStep 3957437 = 1484039) B1484039
theorem B1041095 : Blo 1040609 1041095 := bstep (se 1 (by rfl) ⟨780821, by rfl⟩ : syracuseStep 1041095 = 1561643) B1561643
theorem B10019537 : Blo 1040609 10019537 := bstep (se 2 (by rfl) ⟨3757326, by rfl⟩ : syracuseStep 10019537 = 7514653) B7514653
theorem B1041115 : Blo 1040609 1041115 := bstep (se 1 (by rfl) ⟨780836, by rfl⟩ : syracuseStep 1041115 = 1561673) B1561673
theorem B2974457 : Blo 1040609 2974457 := bstep (se 2 (by rfl) ⟨1115421, by rfl⟩ : syracuseStep 2974457 = 2230843) B2230843
theorem B1041191 : Blo 1040609 1041191 := bstep (se 1 (by rfl) ⟨780893, by rfl⟩ : syracuseStep 1041191 = 1561787) B1561787
theorem B1762121 : Blo 1040609 1762121 := bstep (se 2 (by rfl) ⟨660795, by rfl⟩ : syracuseStep 1762121 = 1321591) B1321591
theorem B1041231 : Blo 1040609 1041231 := bstep (se 1 (by rfl) ⟨780923, by rfl⟩ : syracuseStep 1041231 = 1561847) B1561847
theorem B1041247 : Blo 1040609 1041247 := bstep (se 1 (by rfl) ⟨780935, by rfl⟩ : syracuseStep 1041247 = 1561871) B1561871
theorem B1041275 : Blo 1040609 1041275 := bstep (se 1 (by rfl) ⟨780956, by rfl⟩ : syracuseStep 1041275 = 1561913) B1561913
theorem B1041327 : Blo 1040609 1041327 := bstep (se 1 (by rfl) ⟨780995, by rfl⟩ : syracuseStep 1041327 = 1561991) B1561991
theorem B1565615 : Blo 1040609 1565615 := bstep (se 1 (by rfl) ⟨1174211, by rfl⟩ : syracuseStep 1565615 = 2348423) B2348423
theorem B2974639 : Blo 1040609 2974639 := bstep (se 1 (by rfl) ⟨2230979, by rfl⟩ : syracuseStep 2974639 = 4461959) B4461959
theorem B1041351 : Blo 1040609 1041351 := bstep (se 1 (by rfl) ⟨781013, by rfl⟩ : syracuseStep 1041351 = 1562027) B1562027
theorem B1041371 : Blo 1040609 1041371 := bstep (se 1 (by rfl) ⟨781028, by rfl⟩ : syracuseStep 1041371 = 1562057) B1562057
theorem B1172443 : Blo 1040609 1172443 := bstep (se 1 (by rfl) ⟨879332, by rfl⟩ : syracuseStep 1172443 = 1758665) B1758665
theorem B1565705 : Blo 1040609 1565705 := bstep (se 2 (by rfl) ⟨587139, by rfl⟩ : syracuseStep 1565705 = 1174279) B1174279
theorem B1041447 : Blo 1040609 1041447 := bstep (se 1 (by rfl) ⟨781085, by rfl⟩ : syracuseStep 1041447 = 1562171) B1562171
theorem B1565735 : Blo 1040609 1565735 := bstep (se 1 (by rfl) ⟨1174301, by rfl⟩ : syracuseStep 1565735 = 2348603) B2348603
theorem B1041487 : Blo 1040609 1041487 := bstep (se 1 (by rfl) ⟨781115, by rfl⟩ : syracuseStep 1041487 = 1562231) B1562231
theorem B1041503 : Blo 1040609 1041503 := bstep (se 1 (by rfl) ⟨781127, by rfl⟩ : syracuseStep 1041503 = 1562255) B1562255
theorem B1041531 : Blo 1040609 1041531 := bstep (se 1 (by rfl) ⟨781148, by rfl⟩ : syracuseStep 1041531 = 1562297) B1562297
theorem B1565819 : Blo 1040609 1565819 := bstep (se 1 (by rfl) ⟨1174364, by rfl⟩ : syracuseStep 1565819 = 2348729) B2348729
theorem B1041583 : Blo 1040609 1041583 := bstep (se 1 (by rfl) ⟨781187, by rfl⟩ : syracuseStep 1041583 = 1562375) B1562375
theorem B1041607 : Blo 1040609 1041607 := bstep (se 1 (by rfl) ⟨781205, by rfl⟩ : syracuseStep 1041607 = 1562411) B1562411
theorem B1041627 : Blo 1040609 1041627 := bstep (se 1 (by rfl) ⟨781220, by rfl⟩ : syracuseStep 1041627 = 1562441) B1562441
theorem B1565945 : Blo 1040609 1565945 := bstep (se 2 (by rfl) ⟨587229, by rfl⟩ : syracuseStep 1565945 = 1174459) B1174459
theorem B1762553 : Blo 1040609 1762553 := bstep (se 2 (by rfl) ⟨660957, by rfl⟩ : syracuseStep 1762553 = 1321915) B1321915
theorem B1041703 : Blo 1040609 1041703 := bstep (se 1 (by rfl) ⟨781277, by rfl⟩ : syracuseStep 1041703 = 1562555) B1562555
theorem B1041743 : Blo 1040609 1041743 := bstep (se 1 (by rfl) ⟨781307, by rfl⟩ : syracuseStep 1041743 = 1562615) B1562615
theorem B1041759 : Blo 1040609 1041759 := bstep (se 1 (by rfl) ⟨781319, by rfl⟩ : syracuseStep 1041759 = 1562639) B1562639
theorem B1566047 : Blo 1040609 1566047 := bstep (se 1 (by rfl) ⟨1174535, by rfl⟩ : syracuseStep 1566047 = 2349071) B2349071
theorem B1566059 : Blo 1040609 1566059 := bstep (se 1 (by rfl) ⟨1174544, by rfl⟩ : syracuseStep 1566059 = 2349089) B2349089
theorem B1041787 : Blo 1040609 1041787 := bstep (se 1 (by rfl) ⟨781340, by rfl⟩ : syracuseStep 1041787 = 1562681) B1562681
theorem B11265443 : Blo 1040609 11265443 := bstep (se 1 (by rfl) ⟨8449082, by rfl⟩ : syracuseStep 11265443 = 16898165) B16898165
theorem B1041839 : Blo 1040609 1041839 := bstep (se 1 (by rfl) ⟨781379, by rfl⟩ : syracuseStep 1041839 = 1562759) B1562759
theorem B1172911 : Blo 1040609 1172911 := bstep (se 1 (by rfl) ⟨879683, by rfl⟩ : syracuseStep 1172911 = 1759367) B1759367
theorem B1762735 : Blo 1040609 1762735 := bstep (se 1 (by rfl) ⟨1322051, by rfl⟩ : syracuseStep 1762735 = 2644103) B2644103
theorem B1041863 : Blo 1040609 1041863 := bstep (se 1 (by rfl) ⟨781397, by rfl⟩ : syracuseStep 1041863 = 1562795) B1562795
theorem B1041883 : Blo 1040609 1041883 := bstep (se 1 (by rfl) ⟨781412, by rfl⟩ : syracuseStep 1041883 = 1562825) B1562825
theorem B1041959 : Blo 1040609 1041959 := bstep (se 1 (by rfl) ⟨781469, by rfl⟩ : syracuseStep 1041959 = 1562939) B1562939
theorem B1041999 : Blo 1040609 1041999 := bstep (se 1 (by rfl) ⟨781499, by rfl⟩ : syracuseStep 1041999 = 1562999) B1562999
theorem B1566287 : Blo 1040609 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B1042015 : Blo 1040609 1042015 := bstep (se 1 (by rfl) ⟨781511, by rfl⟩ : syracuseStep 1042015 = 1563023) B1563023
theorem B1042043 : Blo 1040609 1042043 := bstep (se 1 (by rfl) ⟨781532, by rfl⟩ : syracuseStep 1042043 = 1563065) B1563065
theorem B1042095 : Blo 1040609 1042095 := bstep (se 1 (by rfl) ⟨781571, by rfl⟩ : syracuseStep 1042095 = 1563143) B1563143
theorem B1042119 : Blo 1040609 1042119 := bstep (se 1 (by rfl) ⟨781589, by rfl⟩ : syracuseStep 1042119 = 1563179) B1563179
theorem B3565255 : Blo 1040609 3565255 := bstep (se 1 (by rfl) ⟨2673941, by rfl⟩ : syracuseStep 3565255 = 5347883) B5347883
theorem B1566407 : Blo 1040609 1566407 := bstep (se 1 (by rfl) ⟨1174805, by rfl⟩ : syracuseStep 1566407 = 2349611) B2349611
theorem B1042139 : Blo 1040609 1042139 := bstep (se 1 (by rfl) ⟨781604, by rfl⟩ : syracuseStep 1042139 = 1563209) B1563209
theorem B1042215 : Blo 1040609 1042215 := bstep (se 1 (by rfl) ⟨781661, by rfl⟩ : syracuseStep 1042215 = 1563323) B1563323
theorem B1042255 : Blo 1040609 1042255 := bstep (se 1 (by rfl) ⟨781691, by rfl⟩ : syracuseStep 1042255 = 1563383) B1563383
theorem B1042271 : Blo 1040609 1042271 := bstep (se 1 (by rfl) ⟨781703, by rfl⟩ : syracuseStep 1042271 = 1563407) B1563407
theorem B1173343 : Blo 1040609 1173343 := bstep (se 1 (by rfl) ⟨880007, by rfl⟩ : syracuseStep 1173343 = 1760015) B1760015
theorem B1566569 : Blo 1040609 1566569 := bstep (se 2 (by rfl) ⟨587463, by rfl⟩ : syracuseStep 1566569 = 1174927) B1174927
theorem B1042299 : Blo 1040609 1042299 := bstep (se 1 (by rfl) ⟨781724, by rfl⟩ : syracuseStep 1042299 = 1563449) B1563449
theorem B1042351 : Blo 1040609 1042351 := bstep (se 1 (by rfl) ⟨781763, by rfl⟩ : syracuseStep 1042351 = 1563527) B1563527
theorem B1566647 : Blo 1040609 1566647 := bstep (se 1 (by rfl) ⟨1174985, by rfl⟩ : syracuseStep 1566647 = 2349971) B2349971
theorem B1042375 : Blo 1040609 1042375 := bstep (se 1 (by rfl) ⟨781781, by rfl⟩ : syracuseStep 1042375 = 1563563) B1563563
theorem B1042395 : Blo 1040609 1042395 := bstep (se 1 (by rfl) ⟨781796, by rfl⟩ : syracuseStep 1042395 = 1563593) B1563593
theorem B1566683 : Blo 1040609 1566683 := bstep (se 1 (by rfl) ⟨1175012, by rfl⟩ : syracuseStep 1566683 = 2350025) B2350025
theorem B1042471 : Blo 1040609 1042471 := bstep (se 1 (by rfl) ⟨781853, by rfl⟩ : syracuseStep 1042471 = 1563707) B1563707
theorem B1042511 : Blo 1040609 1042511 := bstep (se 1 (by rfl) ⟨781883, by rfl⟩ : syracuseStep 1042511 = 1563767) B1563767
theorem B3958865 : Blo 1040609 3958865 := bstep (se 2 (by rfl) ⟨1484574, by rfl⟩ : syracuseStep 3958865 = 2969149) B2969149
theorem B1042527 : Blo 1040609 1042527 := bstep (se 1 (by rfl) ⟨781895, by rfl⟩ : syracuseStep 1042527 = 1563791) B1563791
theorem B1042555 : Blo 1040609 1042555 := bstep (se 1 (by rfl) ⟨781916, by rfl⟩ : syracuseStep 1042555 = 1563833) B1563833
theorem B1042607 : Blo 1040609 1042607 := bstep (se 1 (by rfl) ⟨781955, by rfl⟩ : syracuseStep 1042607 = 1563911) B1563911
theorem B1042631 : Blo 1040609 1042631 := bstep (se 1 (by rfl) ⟨781973, by rfl⟩ : syracuseStep 1042631 = 1563947) B1563947
theorem B1173703 : Blo 1040609 1173703 := bstep (se 1 (by rfl) ⟨880277, by rfl⟩ : syracuseStep 1173703 = 1760555) B1760555
theorem B1042651 : Blo 1040609 1042651 := bstep (se 1 (by rfl) ⟨781988, by rfl⟩ : syracuseStep 1042651 = 1563977) B1563977
theorem B1042727 : Blo 1040609 1042727 := bstep (se 1 (by rfl) ⟨782045, by rfl⟩ : syracuseStep 1042727 = 1564091) B1564091
theorem B1042767 : Blo 1040609 1042767 := bstep (se 1 (by rfl) ⟨782075, by rfl⟩ : syracuseStep 1042767 = 1564151) B1564151
theorem B1042783 : Blo 1040609 1042783 := bstep (se 1 (by rfl) ⟨782087, by rfl⟩ : syracuseStep 1042783 = 1564175) B1564175
theorem B1042811 : Blo 1040609 1042811 := bstep (se 1 (by rfl) ⟨782108, by rfl⟩ : syracuseStep 1042811 = 1564217) B1564217
theorem B1042863 : Blo 1040609 1042863 := bstep (se 1 (by rfl) ⟨782147, by rfl⟩ : syracuseStep 1042863 = 1564295) B1564295
theorem B22538675 : Blo 1040609 22538675 := bstep (se 1 (by rfl) ⟨16904006, by rfl⟩ : syracuseStep 22538675 = 33808013) B33808013
theorem B1042887 : Blo 1040609 1042887 := bstep (se 1 (by rfl) ⟨782165, by rfl⟩ : syracuseStep 1042887 = 1564331) B1564331
theorem B1042907 : Blo 1040609 1042907 := bstep (se 1 (by rfl) ⟨782180, by rfl⟩ : syracuseStep 1042907 = 1564361) B1564361
theorem B1042983 : Blo 1040609 1042983 := bstep (se 1 (by rfl) ⟨782237, by rfl⟩ : syracuseStep 1042983 = 1564475) B1564475
theorem B1043023 : Blo 1040609 1043023 := bstep (se 1 (by rfl) ⟨782267, by rfl⟩ : syracuseStep 1043023 = 1564535) B1564535
theorem B1043039 : Blo 1040609 1043039 := bstep (se 1 (by rfl) ⟨782279, by rfl⟩ : syracuseStep 1043039 = 1564559) B1564559
theorem B1043067 : Blo 1040609 1043067 := bstep (se 1 (by rfl) ⟨782300, by rfl⟩ : syracuseStep 1043067 = 1564601) B1564601
theorem B1043119 : Blo 1040609 1043119 := bstep (se 1 (by rfl) ⟨782339, by rfl⟩ : syracuseStep 1043119 = 1564679) B1564679
theorem B1043143 : Blo 1040609 1043143 := bstep (se 1 (by rfl) ⟨782357, by rfl⟩ : syracuseStep 1043143 = 1564715) B1564715
theorem B1043163 : Blo 1040609 1043163 := bstep (se 1 (by rfl) ⟨782372, by rfl⟩ : syracuseStep 1043163 = 1564745) B1564745
theorem B1043239 : Blo 1040609 1043239 := bstep (se 1 (by rfl) ⟨782429, by rfl⟩ : syracuseStep 1043239 = 1564859) B1564859
theorem B5270345 : Blo 1040609 5270345 := bstep (se 2 (by rfl) ⟨1976379, by rfl⟩ : syracuseStep 5270345 = 3952759) B3952759
theorem B1043279 : Blo 1040609 1043279 := bstep (se 1 (by rfl) ⟨782459, by rfl⟩ : syracuseStep 1043279 = 1564919) B1564919
theorem B1043295 : Blo 1040609 1043295 := bstep (se 1 (by rfl) ⟨782471, by rfl⟩ : syracuseStep 1043295 = 1564943) B1564943
theorem B1043323 : Blo 1040609 1043323 := bstep (se 1 (by rfl) ⟨782492, by rfl⟩ : syracuseStep 1043323 = 1564985) B1564985
theorem B1043375 : Blo 1040609 1043375 := bstep (se 1 (by rfl) ⟨782531, by rfl⟩ : syracuseStep 1043375 = 1565063) B1565063
theorem B2812859 : Blo 1040609 2812859 := bstep (se 1 (by rfl) ⟨2109644, by rfl⟩ : syracuseStep 2812859 = 4219289) B4219289
theorem B2223035 : Blo 1040609 2223035 := bstep (se 1 (by rfl) ⟨1667276, by rfl⟩ : syracuseStep 2223035 = 3334553) B3334553
theorem B1043399 : Blo 1040609 1043399 := bstep (se 1 (by rfl) ⟨782549, by rfl⟩ : syracuseStep 1043399 = 1565099) B1565099
theorem B1043419 : Blo 1040609 1043419 := bstep (se 1 (by rfl) ⟨782564, by rfl⟩ : syracuseStep 1043419 = 1565129) B1565129
theorem B3566593 : Blo 1040609 3566593 := bstep (se 2 (by rfl) ⟨1337472, by rfl⟩ : syracuseStep 3566593 = 2674945) B2674945
theorem B1043495 : Blo 1040609 1043495 := bstep (se 1 (by rfl) ⟨782621, by rfl⟩ : syracuseStep 1043495 = 1565243) B1565243
theorem B1174567 : Blo 1040609 1174567 := bstep (se 1 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 1174567 = 1761851) B1761851
theorem B1043535 : Blo 1040609 1043535 := bstep (se 1 (by rfl) ⟨782651, by rfl⟩ : syracuseStep 1043535 = 1565303) B1565303
theorem B1043551 : Blo 1040609 1043551 := bstep (se 1 (by rfl) ⟨782663, by rfl⟩ : syracuseStep 1043551 = 1565327) B1565327
theorem B1043579 : Blo 1040609 1043579 := bstep (se 1 (by rfl) ⟨782684, by rfl⟩ : syracuseStep 1043579 = 1565369) B1565369
theorem B1043631 : Blo 1040609 1043631 := bstep (se 1 (by rfl) ⟨782723, by rfl⟩ : syracuseStep 1043631 = 1565447) B1565447
theorem B1043655 : Blo 1040609 1043655 := bstep (se 1 (by rfl) ⟨782741, by rfl⟩ : syracuseStep 1043655 = 1565483) B1565483
theorem B1043675 : Blo 1040609 1043675 := bstep (se 1 (by rfl) ⟨782756, by rfl⟩ : syracuseStep 1043675 = 1565513) B1565513
theorem B1043751 : Blo 1040609 1043751 := bstep (se 1 (by rfl) ⟨782813, by rfl⟩ : syracuseStep 1043751 = 1565627) B1565627
theorem B1043791 : Blo 1040609 1043791 := bstep (se 1 (by rfl) ⟨782843, by rfl⟩ : syracuseStep 1043791 = 1565687) B1565687
theorem B1043807 : Blo 1040609 1043807 := bstep (se 1 (by rfl) ⟨782855, by rfl⟩ : syracuseStep 1043807 = 1565711) B1565711
theorem B1043835 : Blo 1040609 1043835 := bstep (se 1 (by rfl) ⟨782876, by rfl⟩ : syracuseStep 1043835 = 1565753) B1565753
theorem B1043887 : Blo 1040609 1043887 := bstep (se 1 (by rfl) ⟨782915, by rfl⟩ : syracuseStep 1043887 = 1565831) B1565831
theorem B1043911 : Blo 1040609 1043911 := bstep (se 1 (by rfl) ⟨782933, by rfl⟩ : syracuseStep 1043911 = 1565867) B1565867
theorem B1043931 : Blo 1040609 1043931 := bstep (se 1 (by rfl) ⟨782948, by rfl⟩ : syracuseStep 1043931 = 1565897) B1565897
theorem B2223625 : Blo 1040609 2223625 := bstep (se 2 (by rfl) ⟨833859, by rfl⟩ : syracuseStep 2223625 = 1667719) B1667719
theorem B3960353 : Blo 1040609 3960353 := bstep (se 2 (by rfl) ⟨1485132, by rfl⟩ : syracuseStep 3960353 = 2970265) B2970265
theorem B1044007 : Blo 1040609 1044007 := bstep (se 1 (by rfl) ⟨783005, by rfl⟩ : syracuseStep 1044007 = 1566011) B1566011
theorem B1044047 : Blo 1040609 1044047 := bstep (se 1 (by rfl) ⟨783035, by rfl⟩ : syracuseStep 1044047 = 1566071) B1566071
theorem B1044063 : Blo 1040609 1044063 := bstep (se 1 (by rfl) ⟨783047, by rfl⟩ : syracuseStep 1044063 = 1566095) B1566095
theorem B1044091 : Blo 1040609 1044091 := bstep (se 1 (by rfl) ⟨783068, by rfl⟩ : syracuseStep 1044091 = 1566137) B1566137
theorem B1044143 : Blo 1040609 1044143 := bstep (se 1 (by rfl) ⟨783107, by rfl⟩ : syracuseStep 1044143 = 1566215) B1566215
theorem B1044167 : Blo 1040609 1044167 := bstep (se 1 (by rfl) ⟨783125, by rfl⟩ : syracuseStep 1044167 = 1566251) B1566251
theorem B3960535 : Blo 1040609 3960535 := bstep (se 1 (by rfl) ⟨2970401, by rfl⟩ : syracuseStep 3960535 = 5940803) B5940803
theorem B1044187 : Blo 1040609 1044187 := bstep (se 1 (by rfl) ⟨783140, by rfl⟩ : syracuseStep 1044187 = 1566281) B1566281
theorem B1044263 : Blo 1040609 1044263 := bstep (se 1 (by rfl) ⟨783197, by rfl⟩ : syracuseStep 1044263 = 1566395) B1566395
theorem B4222763 : Blo 1040609 4222763 := bstep (se 1 (by rfl) ⟨3167072, by rfl⟩ : syracuseStep 4222763 = 6334145) B6334145
theorem B1044303 : Blo 1040609 1044303 := bstep (se 1 (by rfl) ⟨783227, by rfl⟩ : syracuseStep 1044303 = 1566455) B1566455
theorem B1044319 : Blo 1040609 1044319 := bstep (se 1 (by rfl) ⟨783239, by rfl⟩ : syracuseStep 1044319 = 1566479) B1566479
theorem B1044347 : Blo 1040609 1044347 := bstep (se 1 (by rfl) ⟨783260, by rfl⟩ : syracuseStep 1044347 = 1566521) B1566521
theorem B1044399 : Blo 1040609 1044399 := bstep (se 1 (by rfl) ⟨783299, by rfl⟩ : syracuseStep 1044399 = 1566599) B1566599
theorem B1044423 : Blo 1040609 1044423 := bstep (se 1 (by rfl) ⟨783317, by rfl⟩ : syracuseStep 1044423 = 1566635) B1566635
theorem B1044443 : Blo 1040609 1044443 := bstep (se 1 (by rfl) ⟨783332, by rfl⟩ : syracuseStep 1044443 = 1566665) B1566665
theorem B3960839 : Blo 1040609 3960839 := bstep (se 1 (by rfl) ⟨2970629, by rfl⟩ : syracuseStep 3960839 = 5941259) B5941259
theorem B3567635 : Blo 1040609 3567635 := bstep (se 1 (by rfl) ⟨2675726, by rfl⟩ : syracuseStep 3567635 = 5351453) B5351453
theorem B1044519 : Blo 1040609 1044519 := bstep (se 1 (by rfl) ⟨783389, by rfl⟩ : syracuseStep 1044519 = 1566779) B1566779
theorem B1044559 : Blo 1040609 1044559 := bstep (se 1 (by rfl) ⟨783419, by rfl⟩ : syracuseStep 1044559 = 1566839) B1566839
theorem B5271641 : Blo 1040609 5271641 := bstep (se 2 (by rfl) ⟨1976865, by rfl⟩ : syracuseStep 5271641 = 3953731) B3953731
theorem B1044575 : Blo 1040609 1044575 := bstep (se 1 (by rfl) ⟨783431, by rfl⟩ : syracuseStep 1044575 = 1566863) B1566863
theorem B1044603 : Blo 1040609 1044603 := bstep (se 1 (by rfl) ⟨783452, by rfl⟩ : syracuseStep 1044603 = 1566905) B1566905
theorem B3961325 : Blo 1040609 3961325 := bstep (se 3 (by rfl) ⟨742748, by rfl⟩ : syracuseStep 3961325 = 1485497) B1485497
theorem B8024777 : Blo 1040609 8024777 := bstep (se 2 (by rfl) ⟨3009291, by rfl⟩ : syracuseStep 8024777 = 6018583) B6018583
theorem B9630467 : Blo 1040609 9630467 := bstep (se 1 (by rfl) ⟨7222850, by rfl⟩ : syracuseStep 9630467 = 14445701) B14445701
theorem B30110615 : Blo 1040609 30110615 := bstep (se 1 (by rfl) ⟨22582961, by rfl⟩ : syracuseStep 30110615 = 45165923) B45165923
theorem B5927863 : Blo 1040609 5927863 := bstep (se 1 (by rfl) ⟨4445897, by rfl⟩ : syracuseStep 5927863 = 8891795) B8891795
theorem B4223927 : Blo 1040609 4223927 := bstep (se 1 (by rfl) ⟨3167945, by rfl⟩ : syracuseStep 4223927 = 6335891) B6335891
theorem B2225171 : Blo 1040609 2225171 := bstep (se 1 (by rfl) ⟨1668878, by rfl⟩ : syracuseStep 2225171 = 3337757) B3337757
theorem B14251211 : Blo 1040609 14251211 := bstep (se 1 (by rfl) ⟨10688408, by rfl⟩ : syracuseStep 14251211 = 21376817) B21376817
theorem B1668539 : Blo 1040609 1668539 := bstep (se 1 (by rfl) ⟨1251404, by rfl⟩ : syracuseStep 1668539 = 2502809) B2502809
theorem B1668647 : Blo 1040609 1668647 := bstep (se 1 (by rfl) ⟨1251485, by rfl⟩ : syracuseStep 1668647 = 2502971) B2502971
theorem B3962465 : Blo 1040609 3962465 := bstep (se 2 (by rfl) ⟨1485924, by rfl⟩ : syracuseStep 3962465 = 2971849) B2971849
theorem B4520279 : Blo 1040609 4520279 := bstep (se 1 (by rfl) ⟨3390209, by rfl⟩ : syracuseStep 4520279 = 6780419) B6780419
theorem B5929321 : Blo 1040609 5929321 := bstep (se 2 (by rfl) ⟨2223495, by rfl⟩ : syracuseStep 5929321 = 4446991) B4446991
theorem B1669481 : Blo 1040609 1669481 := bstep (se 2 (by rfl) ⟨626055, by rfl⟩ : syracuseStep 1669481 = 1252111) B1252111
theorem B4225517 : Blo 1040609 4225517 := bstep (se 3 (by rfl) ⟨792284, by rfl⟩ : syracuseStep 4225517 = 1584569) B1584569
theorem B3963451 : Blo 1040609 3963451 := bstep (se 1 (by rfl) ⟨2972588, by rfl⟩ : syracuseStep 3963451 = 5945177) B5945177
theorem B2226811 : Blo 1040609 2226811 := bstep (se 1 (by rfl) ⟨1670108, by rfl⟩ : syracuseStep 2226811 = 3340217) B3340217
theorem B13368037 : Blo 1040609 13368037 := bstep (se 4 (by rfl) ⟨1253253, by rfl⟩ : syracuseStep 13368037 = 2506507) B2506507
theorem B11860829 : Blo 1040609 11860829 := bstep (se 3 (by rfl) ⟨2223905, by rfl⟩ : syracuseStep 11860829 = 4447811) B4447811
theorem B3963755 : Blo 1040609 3963755 := bstep (se 1 (by rfl) ⟨2972816, by rfl⟩ : syracuseStep 3963755 = 5945633) B5945633
theorem B5012399 : Blo 1040609 5012399 := bstep (se 1 (by rfl) ⟨3759299, by rfl⟩ : syracuseStep 5012399 = 7518599) B7518599
theorem B3963923 : Blo 1040609 3963923 := bstep (se 1 (by rfl) ⟨2972942, by rfl⟩ : syracuseStep 3963923 = 5945885) B5945885
theorem B24083729 : Blo 1040609 24083729 := bstep (se 2 (by rfl) ⟨9031398, by rfl⟩ : syracuseStep 24083729 = 18062797) B18062797
theorem B3341857 : Blo 1040609 3341857 := bstep (se 2 (by rfl) ⟨1253196, by rfl⟩ : syracuseStep 3341857 = 2506393) B2506393
theorem B1113679 : Blo 1040609 1113679 := bstep (se 1 (by rfl) ⟨835259, by rfl⟩ : syracuseStep 1113679 = 1670519) B1670519
theorem B2228075 : Blo 1040609 2228075 := bstep (se 1 (by rfl) ⟨1671056, by rfl⟩ : syracuseStep 2228075 = 3342113) B3342113
theorem B2228143 : Blo 1040609 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B15007673 : Blo 1040609 15007673 := bstep (se 2 (by rfl) ⟨5627877, by rfl⟩ : syracuseStep 15007673 = 11255755) B11255755
theorem B8912915 : Blo 1040609 8912915 := bstep (se 1 (by rfl) ⟨6684686, by rfl⟩ : syracuseStep 8912915 = 13369373) B13369373
theorem B11272709 : Blo 1040609 11272709 := bstep (se 4 (by rfl) ⟨1056816, by rfl⟩ : syracuseStep 11272709 = 2113633) B2113633
theorem B2818633 : Blo 1040609 2818633 := bstep (se 2 (by rfl) ⟨1056987, by rfl⟩ : syracuseStep 2818633 = 2113975) B2113975
theorem B1671787 : Blo 1040609 1671787 := bstep (se 1 (by rfl) ⟨1253840, by rfl⟩ : syracuseStep 1671787 = 2507681) B2507681
theorem B5014169 : Blo 1040609 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B9634619 : Blo 1040609 9634619 := bstep (se 1 (by rfl) ⟨7225964, by rfl⟩ : syracuseStep 9634619 = 14451929) B14451929
theorem B5014381 : Blo 1040609 5014381 := bstep (se 3 (by rfl) ⟨940196, by rfl⟩ : syracuseStep 5014381 = 1880393) B1880393
theorem B5080009 : Blo 1040609 5080009 := bstep (se 2 (by rfl) ⟨1905003, by rfl⟩ : syracuseStep 5080009 = 3810007) B3810007
theorem B5276663 : Blo 1040609 5276663 := bstep (se 1 (by rfl) ⟨3957497, by rfl⟩ : syracuseStep 5276663 = 7914995) B7914995
theorem B3966185 : Blo 1040609 3966185 := bstep (se 2 (by rfl) ⟨1487319, by rfl⟩ : syracuseStep 3966185 = 2974639) B2974639
theorem B3343805 : Blo 1040609 3343805 := bstep (se 3 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 3343805 = 1253927) B1253927
theorem B1672697 : Blo 1040609 1672697 := bstep (se 2 (by rfl) ⟨627261, by rfl⟩ : syracuseStep 1672697 = 1254523) B1254523
theorem B5637721 : Blo 1040609 5637721 := bstep (se 2 (by rfl) ⟨2114145, by rfl⟩ : syracuseStep 5637721 = 4228291) B4228291
theorem B1411177 : Blo 1040609 1411177 := bstep (se 2 (by rfl) ⟨529191, by rfl⟩ : syracuseStep 1411177 = 1058383) B1058383
theorem B9144515 : Blo 1040609 9144515 := bstep (se 1 (by rfl) ⟨6858386, by rfl⟩ : syracuseStep 9144515 = 13716773) B13716773
theorem B1902857 : Blo 1040609 1902857 := bstep (se 2 (by rfl) ⟨713571, by rfl⟩ : syracuseStep 1902857 = 1427143) B1427143
theorem B4753673 : Blo 1040609 4753673 := bstep (se 2 (by rfl) ⟨1782627, by rfl⟩ : syracuseStep 4753673 = 3565255) B3565255
theorem B4753907 : Blo 1040609 4753907 := bstep (se 1 (by rfl) ⟨3565430, by rfl⟩ : syracuseStep 4753907 = 7130861) B7130861
theorem B1411679 : Blo 1040609 1411679 := bstep (se 1 (by rfl) ⟨1058759, by rfl⟩ : syracuseStep 1411679 = 2117519) B2117519
theorem B11274875 : Blo 1040609 11274875 := bstep (se 1 (by rfl) ⟨8456156, by rfl⟩ : syracuseStep 11274875 = 16912313) B16912313
theorem B8915579 : Blo 1040609 8915579 := bstep (se 1 (by rfl) ⟨6686684, by rfl⟩ : syracuseStep 8915579 = 13373369) B13373369
theorem B5278607 : Blo 1040609 5278607 := bstep (se 1 (by rfl) ⟨3958955, by rfl⟩ : syracuseStep 5278607 = 7917911) B7917911
theorem B11865203 : Blo 1040609 11865203 := bstep (se 1 (by rfl) ⟨8898902, by rfl⟩ : syracuseStep 11865203 = 17797805) B17797805
theorem B4460113 : Blo 1040609 4460113 := bstep (se 2 (by rfl) ⟨1672542, by rfl⟩ : syracuseStep 4460113 = 3345085) B3345085
theorem B5639795 : Blo 1040609 5639795 := bstep (se 1 (by rfl) ⟨4229846, by rfl⟩ : syracuseStep 5639795 = 8459693) B8459693
theorem B2035361 : Blo 1040609 2035361 := bstep (se 2 (by rfl) ⟨763260, by rfl⟩ : syracuseStep 2035361 = 1526521) B1526521
theorem B4755457 : Blo 1040609 4755457 := bstep (se 2 (by rfl) ⟨1783296, by rfl⟩ : syracuseStep 4755457 = 3566593) B3566593
theorem B19566851 : Blo 1040609 19566851 := bstep (se 1 (by rfl) ⟨14675138, by rfl⟩ : syracuseStep 19566851 = 29350277) B29350277
theorem B5017859 : Blo 1040609 5017859 := bstep (se 1 (by rfl) ⟨3763394, by rfl⟩ : syracuseStep 5017859 = 7526789) B7526789
theorem B10031951 : Blo 1040609 10031951 := bstep (se 1 (by rfl) ⟨7523963, by rfl⟩ : syracuseStep 10031951 = 15047927) B15047927
theorem B3806147 : Blo 1040609 3806147 := bstep (se 1 (by rfl) ⟨2854610, by rfl⟩ : syracuseStep 3806147 = 5709221) B5709221
theorem B5280713 : Blo 1040609 5280713 := bstep (se 2 (by rfl) ⟨1980267, by rfl⟩ : syracuseStep 5280713 = 3960535) B3960535
theorem B7510295 : Blo 1040609 7510295 := bstep (se 1 (by rfl) ⟨5632721, by rfl⟩ : syracuseStep 7510295 = 11265443) B11265443
theorem B1317151 : Blo 1040609 1317151 := bstep (se 1 (by rfl) ⟨987863, by rfl⟩ : syracuseStep 1317151 = 1975727) B1975727
theorem B5347757 : Blo 1040609 5347757 := bstep (se 3 (by rfl) ⟨1002704, by rfl⟩ : syracuseStep 5347757 = 2005409) B2005409
theorem B7903817 : Blo 1040609 7903817 := bstep (se 2 (by rfl) ⟨2963931, by rfl⟩ : syracuseStep 7903817 = 5927863) B5927863
theorem B3513563 : Blo 1040609 3513563 := bstep (se 1 (by rfl) ⟨2635172, by rfl⟩ : syracuseStep 3513563 = 5270345) B5270345
theorem B1875239 : Blo 1040609 1875239 := bstep (se 1 (by rfl) ⟨1406429, by rfl⟩ : syracuseStep 1875239 = 2812859) B2812859
theorem B1482023 : Blo 1040609 1482023 := bstep (se 1 (by rfl) ⟨1111517, by rfl⟩ : syracuseStep 1482023 = 2223035) B2223035
theorem B4005335 : Blo 1040609 4005335 := bstep (se 1 (by rfl) ⟨3004001, by rfl⟩ : syracuseStep 4005335 = 6008003) B6008003
theorem B1252927 : Blo 1040609 1252927 := bstep (se 1 (by rfl) ⟨939695, by rfl⟩ : syracuseStep 1252927 = 1879391) B1879391
theorem B9641857 : Blo 1040609 9641857 := bstep (se 2 (by rfl) ⟨3615696, by rfl⟩ : syracuseStep 9641857 = 7231393) B7231393
theorem B3514427 : Blo 1040609 3514427 := bstep (se 1 (by rfl) ⟨2635820, by rfl⟩ : syracuseStep 3514427 = 5271641) B5271641
theorem B3514697 : Blo 1040609 3514697 := bstep (se 2 (by rfl) ⟨1318011, by rfl⟩ : syracuseStep 3514697 = 2636023) B2636023
theorem B5349851 : Blo 1040609 5349851 := bstep (se 1 (by rfl) ⟨4012388, by rfl⟩ : syracuseStep 5349851 = 8024777) B8024777
theorem B7905761 : Blo 1040609 7905761 := bstep (se 2 (by rfl) ⟨2964660, by rfl⟩ : syracuseStep 7905761 = 5929321) B5929321
theorem B1319419 : Blo 1040609 1319419 := bstep (se 1 (by rfl) ⟨989564, by rfl⟩ : syracuseStep 1319419 = 1979129) B1979129
theorem B1483447 : Blo 1040609 1483447 := bstep (se 1 (by rfl) ⟨1112585, by rfl⟩ : syracuseStep 1483447 = 2225171) B2225171
theorem B1319647 : Blo 1040609 1319647 := bstep (se 1 (by rfl) ⟨989735, by rfl⟩ : syracuseStep 1319647 = 1979471) B1979471
theorem B5284601 : Blo 1040609 5284601 := bstep (se 2 (by rfl) ⟨1981725, by rfl⟩ : syracuseStep 5284601 = 3963451) B3963451
theorem B1254619 : Blo 1040609 1254619 := bstep (se 1 (by rfl) ⟨940964, by rfl⟩ : syracuseStep 1254619 = 1881929) B1881929
theorem B1975583 : Blo 1040609 1975583 := bstep (se 1 (by rfl) ⟨1481687, by rfl⟩ : syracuseStep 1975583 = 2963375) B2963375
theorem B1320391 : Blo 1040609 1320391 := bstep (se 1 (by rfl) ⟨990293, by rfl⟩ : syracuseStep 1320391 = 1980587) B1980587
theorem B7907219 : Blo 1040609 7907219 := bstep (se 1 (by rfl) ⟨5930414, by rfl⟩ : syracuseStep 7907219 = 11860829) B11860829
theorem B1484905 : Blo 1040609 1484905 := bstep (se 2 (by rfl) ⟨556839, by rfl⟩ : syracuseStep 1484905 = 1113679) B1113679
theorem B1321535 : Blo 1040609 1321535 := bstep (se 1 (by rfl) ⟨991151, by rfl⟩ : syracuseStep 1321535 = 1982303) B1982303
theorem B1485383 : Blo 1040609 1485383 := bstep (se 1 (by rfl) ⟨1114037, by rfl⟩ : syracuseStep 1485383 = 2228075) B2228075
theorem B5646955 : Blo 1040609 5646955 := bstep (se 1 (by rfl) ⟨4235216, by rfl⟩ : syracuseStep 5646955 = 8470433) B8470433
theorem B10005115 : Blo 1040609 10005115 := bstep (se 1 (by rfl) ⟨7503836, by rfl⟩ : syracuseStep 10005115 = 15007673) B15007673
theorem B142846681 : Blo 1040609 142846681 := bstep (se 2 (by rfl) ⟨53567505, by rfl⟩ : syracuseStep 142846681 = 107135011) B107135011
theorem B20032373 : Blo 1040609 20032373 := bstep (se 5 (by rfl) ⟨939017, by rfl⟩ : syracuseStep 20032373 = 1878035) B1878035
theorem B14265719 : Blo 1040609 14265719 := bstep (se 1 (by rfl) ⟨10699289, by rfl⟩ : syracuseStep 14265719 = 21398579) B21398579
theorem B3517883 : Blo 1040609 3517883 := bstep (se 1 (by rfl) ⟨2638412, by rfl⟩ : syracuseStep 3517883 = 5276825) B5276825
theorem B5287355 : Blo 1040609 5287355 := bstep (se 1 (by rfl) ⟨3965516, by rfl⟩ : syracuseStep 5287355 = 7931033) B7931033
theorem B8466083 : Blo 1040609 8466083 := bstep (se 1 (by rfl) ⟨6349562, by rfl⟩ : syracuseStep 8466083 = 12699125) B12699125
theorem B40578947 : Blo 1040609 40578947 := bstep (se 1 (by rfl) ⟨30434210, by rfl⟩ : syracuseStep 40578947 = 60868421) B60868421
theorem B1129263119 : Blo 1040609 1129263119 := bstep (se 1 (by rfl) ⟨846947339, by rfl⟩ : syracuseStep 1129263119 = 1693894679) B1693894679
theorem B5943401 : Blo 1040609 5943401 := bstep (se 2 (by rfl) ⟨2228775, by rfl⟩ : syracuseStep 5943401 = 4457551) B4457551
theorem B2634515 : Blo 1040609 2634515 := bstep (se 1 (by rfl) ⟨1975886, by rfl⟩ : syracuseStep 2634515 = 3951773) B3951773
theorem B2634727 : Blo 1040609 2634727 := bstep (se 1 (by rfl) ⟨1976045, by rfl⟩ : syracuseStep 2634727 = 3952091) B3952091
theorem B2503655 : Blo 1040609 2503655 := bstep (se 1 (by rfl) ⟨1877741, by rfl⟩ : syracuseStep 2503655 = 3755483) B3755483
theorem B2635001 : Blo 1040609 2635001 := bstep (se 2 (by rfl) ⟨988125, by rfl⟩ : syracuseStep 2635001 = 1976251) B1976251
theorem B1980139 : Blo 1040609 1980139 := bstep (se 1 (by rfl) ⟨1485104, by rfl⟩ : syracuseStep 1980139 = 2970209) B2970209
theorem B2635649 : Blo 1040609 2635649 := bstep (se 2 (by rfl) ⟨988368, by rfl⟩ : syracuseStep 2635649 = 1976737) B1976737
theorem B8894393 : Blo 1040609 8894393 := bstep (se 2 (by rfl) ⟨3335397, by rfl⟩ : syracuseStep 8894393 = 6670795) B6670795
theorem B162413099 : Blo 1040609 162413099 := bstep (se 1 (by rfl) ⟨121809824, by rfl⟩ : syracuseStep 162413099 = 243619649) B243619649
theorem B2341439 : Blo 1040609 2341439 := bstep (se 1 (by rfl) ⟨1756079, by rfl⟩ : syracuseStep 2341439 = 3512159) B3512159
theorem B12696203 : Blo 1040609 12696203 := bstep (se 1 (by rfl) ⟨9522152, by rfl⟩ : syracuseStep 12696203 = 19044305) B19044305
theorem B2341547 : Blo 1040609 2341547 := bstep (se 1 (by rfl) ⟨1756160, by rfl⟩ : syracuseStep 2341547 = 3512321) B3512321
theorem B2636459 : Blo 1040609 2636459 := bstep (se 1 (by rfl) ⟨1977344, by rfl⟩ : syracuseStep 2636459 = 3954689) B3954689
theorem B1981111 : Blo 1040609 1981111 := bstep (se 1 (by rfl) ⟨1485833, by rfl⟩ : syracuseStep 1981111 = 2971667) B2971667
theorem B8895419 : Blo 1040609 8895419 := bstep (se 1 (by rfl) ⟨6671564, by rfl⟩ : syracuseStep 8895419 = 13343129) B13343129
theorem B1981415 : Blo 1040609 1981415 := bstep (se 1 (by rfl) ⟨1486061, by rfl⟩ : syracuseStep 1981415 = 2972123) B2972123
theorem B2342087 : Blo 1040609 2342087 := bstep (se 1 (by rfl) ⟨1756565, by rfl⟩ : syracuseStep 2342087 = 3513131) B3513131
theorem B7519499 : Blo 1040609 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B5946635 : Blo 1040609 5946635 := bstep (se 1 (by rfl) ⟨4459976, by rfl⟩ : syracuseStep 5946635 = 8919953) B8919953
theorem B2964833 : Blo 1040609 2964833 := bstep (se 2 (by rfl) ⟨1111812, by rfl⟩ : syracuseStep 2964833 = 2223625) B2223625
theorem B2342267 : Blo 1040609 2342267 := bstep (se 1 (by rfl) ⟨1756700, by rfl⟩ : syracuseStep 2342267 = 3513401) B3513401
theorem B17841545 : Blo 1040609 17841545 := bstep (se 2 (by rfl) ⟨6690579, by rfl⟩ : syracuseStep 17841545 = 13381159) B13381159
theorem B2342393 : Blo 1040609 2342393 := bstep (se 2 (by rfl) ⟨878397, by rfl⟩ : syracuseStep 2342393 = 1756795) B1756795
theorem B3522041 : Blo 1040609 3522041 := bstep (se 2 (by rfl) ⟨1320765, by rfl⟩ : syracuseStep 3522041 = 2641531) B2641531
theorem B2637319 : Blo 1040609 2637319 := bstep (se 1 (by rfl) ⟨1977989, by rfl⟩ : syracuseStep 2637319 = 3955979) B3955979
theorem B2506297 : Blo 1040609 2506297 := bstep (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) B1879723
theorem B2342483 : Blo 1040609 2342483 := bstep (se 1 (by rfl) ⟨1756862, by rfl⟩ : syracuseStep 2342483 = 3513725) B3513725
theorem B2342663 : Blo 1040609 2342663 := bstep (se 1 (by rfl) ⟨1756997, by rfl⟩ : syracuseStep 2342663 = 3513995) B3513995
theorem B3522311 : Blo 1040609 3522311 := bstep (se 1 (by rfl) ⟨2641733, by rfl⟩ : syracuseStep 3522311 = 5283467) B5283467
theorem B2637623 : Blo 1040609 2637623 := bstep (se 1 (by rfl) ⟨1978217, by rfl⟩ : syracuseStep 2637623 = 3956435) B3956435
theorem B3522365 : Blo 1040609 3522365 := bstep (se 3 (by rfl) ⟨660443, by rfl⟩ : syracuseStep 3522365 = 1320887) B1320887
theorem B8142767 : Blo 1040609 8142767 := bstep (se 1 (by rfl) ⟨6107075, by rfl⟩ : syracuseStep 8142767 = 12214151) B12214151
theorem B1982569 : Blo 1040609 1982569 := bstep (se 2 (by rfl) ⟨743463, by rfl⟩ : syracuseStep 1982569 = 1486927) B1486927
theorem B2343275 : Blo 1040609 2343275 := bstep (se 1 (by rfl) ⟨1757456, by rfl⟩ : syracuseStep 2343275 = 3514913) B3514913
theorem B2638291 : Blo 1040609 2638291 := bstep (se 1 (by rfl) ⟨1978718, by rfl⟩ : syracuseStep 2638291 = 3957437) B3957437
theorem B2343419 : Blo 1040609 2343419 := bstep (se 1 (by rfl) ⟨1757564, by rfl⟩ : syracuseStep 2343419 = 3515129) B3515129
theorem B1982971 : Blo 1040609 1982971 := bstep (se 1 (by rfl) ⟨1487228, by rfl⟩ : syracuseStep 1982971 = 2974457) B2974457
theorem B2343545 : Blo 1040609 2343545 := bstep (se 2 (by rfl) ⟨878829, by rfl⟩ : syracuseStep 2343545 = 1757659) B1757659
theorem B26755757 : Blo 1040609 26755757 := bstep (se 3 (by rfl) ⟨5016704, by rfl⟩ : syracuseStep 26755757 = 10033409) B10033409
theorem B2343599 : Blo 1040609 2343599 := bstep (se 1 (by rfl) ⟨1757699, by rfl⟩ : syracuseStep 2343599 = 3515399) B3515399
theorem B2343671 : Blo 1040609 2343671 := bstep (se 1 (by rfl) ⟨1757753, by rfl⟩ : syracuseStep 2343671 = 3515507) B3515507
theorem B10011539 : Blo 1040609 10011539 := bstep (se 1 (by rfl) ⟨7508654, by rfl⟩ : syracuseStep 10011539 = 15017309) B15017309
theorem B2343851 : Blo 1040609 2343851 := bstep (se 1 (by rfl) ⟨1757888, by rfl⟩ : syracuseStep 2343851 = 3515777) B3515777
theorem B2639081 : Blo 1040609 2639081 := bstep (se 2 (by rfl) ⟨989655, by rfl⟩ : syracuseStep 2639081 = 1979311) B1979311
theorem B11257139 : Blo 1040609 11257139 := bstep (se 1 (by rfl) ⟨8442854, by rfl⟩ : syracuseStep 11257139 = 16885709) B16885709
theorem B2639243 : Blo 1040609 2639243 := bstep (se 1 (by rfl) ⟨1979432, by rfl⟩ : syracuseStep 2639243 = 3958865) B3958865
theorem B2344391 : Blo 1040609 2344391 := bstep (se 1 (by rfl) ⟨1758293, by rfl⟩ : syracuseStep 2344391 = 3516587) B3516587
theorem B68437561 : Blo 1040609 68437561 := bstep (se 2 (by rfl) ⟨25664085, by rfl⟩ : syracuseStep 68437561 = 51328171) B51328171
theorem B15025783 : Blo 1040609 15025783 := bstep (se 1 (by rfl) ⟨11269337, by rfl⟩ : syracuseStep 15025783 = 22538675) B22538675
theorem B2344751 : Blo 1040609 2344751 := bstep (se 1 (by rfl) ⟨1758563, by rfl⟩ : syracuseStep 2344751 = 3517127) B3517127
theorem B2640235 : Blo 1040609 2640235 := bstep (se 1 (by rfl) ⟨1980176, by rfl⟩ : syracuseStep 2640235 = 3960353) B3960353
theorem B2345327 : Blo 1040609 2345327 := bstep (se 1 (by rfl) ⟨1758995, by rfl⟩ : syracuseStep 2345327 = 3517991) B3517991
theorem B2345399 : Blo 1040609 2345399 := bstep (se 1 (by rfl) ⟨1759049, by rfl⟩ : syracuseStep 2345399 = 3518099) B3518099
theorem B2345543 : Blo 1040609 2345543 := bstep (se 1 (by rfl) ⟨1759157, by rfl⟩ : syracuseStep 2345543 = 3518315) B3518315
theorem B2345579 : Blo 1040609 2345579 := bstep (se 1 (by rfl) ⟨1759184, by rfl⟩ : syracuseStep 2345579 = 3518369) B3518369
theorem B3525227 : Blo 1040609 3525227 := bstep (se 1 (by rfl) ⟨2643920, by rfl⟩ : syracuseStep 3525227 = 5287841) B5287841
theorem B2640559 : Blo 1040609 2640559 := bstep (se 1 (by rfl) ⟨1980419, by rfl⟩ : syracuseStep 2640559 = 3960839) B3960839
theorem B2378423 : Blo 1040609 2378423 := bstep (se 1 (by rfl) ⟨1783817, by rfl⟩ : syracuseStep 2378423 = 3567635) B3567635
theorem B2640883 : Blo 1040609 2640883 := bstep (se 1 (by rfl) ⟨1980662, by rfl⟩ : syracuseStep 2640883 = 3961325) B3961325
theorem B2345975 : Blo 1040609 2345975 := bstep (se 1 (by rfl) ⟨1759481, by rfl⟩ : syracuseStep 2345975 = 3518963) B3518963
theorem B20073743 : Blo 1040609 20073743 := bstep (se 1 (by rfl) ⟨15055307, by rfl⟩ : syracuseStep 20073743 = 30110615) B30110615
theorem B2346335 : Blo 1040609 2346335 := bstep (se 1 (by rfl) ⟨1759751, by rfl⟩ : syracuseStep 2346335 = 3519503) B3519503
theorem B2969081 : Blo 1040609 2969081 := bstep (se 2 (by rfl) ⟨1113405, by rfl⟩ : syracuseStep 2969081 = 2226811) B2226811
theorem B2346731 : Blo 1040609 2346731 := bstep (se 1 (by rfl) ⟨1760048, by rfl⟩ : syracuseStep 2346731 = 3520097) B3520097
theorem B2641643 : Blo 1040609 2641643 := bstep (se 1 (by rfl) ⟨1981232, by rfl⟩ : syracuseStep 2641643 = 3962465) B3962465
theorem B2346857 : Blo 1040609 2346857 := bstep (se 2 (by rfl) ⟨880071, by rfl⟩ : syracuseStep 2346857 = 1760143) B1760143
theorem B3952745 : Blo 1040609 3952745 := bstep (se 2 (by rfl) ⟨1482279, by rfl⟩ : syracuseStep 3952745 = 2964559) B2964559
theorem B1560923 : Blo 1040609 1560923 := bstep (se 1 (by rfl) ⟨1170692, by rfl⟩ : syracuseStep 1560923 = 2341385) B2341385
theorem B1757531 : Blo 1040609 1757531 := bstep (se 1 (by rfl) ⟨1318148, by rfl⟩ : syracuseStep 1757531 = 2636297) B2636297
theorem B1757551 : Blo 1040609 1757551 := bstep (se 1 (by rfl) ⟨1318163, by rfl⟩ : syracuseStep 1757551 = 2636327) B2636327
theorem B1561151 : Blo 1040609 1561151 := bstep (se 1 (by rfl) ⟨1170863, by rfl⟩ : syracuseStep 1561151 = 2341727) B2341727
theorem B1757767 : Blo 1040609 1757767 := bstep (se 1 (by rfl) ⟨1318325, by rfl⟩ : syracuseStep 1757767 = 2636651) B2636651
theorem B2642503 : Blo 1040609 2642503 := bstep (se 1 (by rfl) ⟨1981877, by rfl⟩ : syracuseStep 2642503 = 3963755) B3963755
theorem B1561271 : Blo 1040609 1561271 := bstep (se 1 (by rfl) ⟨1170953, by rfl⟩ : syracuseStep 1561271 = 2341907) B2341907
theorem B2347703 : Blo 1040609 2347703 := bstep (se 1 (by rfl) ⟨1760777, by rfl⟩ : syracuseStep 2347703 = 3521555) B3521555
theorem B2642615 : Blo 1040609 2642615 := bstep (se 1 (by rfl) ⟨1981961, by rfl⟩ : syracuseStep 2642615 = 3963923) B3963923
theorem B2347919 : Blo 1040609 2347919 := bstep (se 1 (by rfl) ⟨1760939, by rfl⟩ : syracuseStep 2347919 = 3521879) B3521879
theorem B1561499 : Blo 1040609 1561499 := bstep (se 1 (by rfl) ⟨1171124, by rfl⟩ : syracuseStep 1561499 = 2342249) B2342249
theorem B1758199 : Blo 1040609 1758199 := bstep (se 1 (by rfl) ⟨1318649, by rfl⟩ : syracuseStep 1758199 = 2637299) B2637299
theorem B2970857 : Blo 1040609 2970857 := bstep (se 2 (by rfl) ⟨1114071, by rfl⟩ : syracuseStep 2970857 = 2228143) B2228143
theorem B1561895 : Blo 1040609 1561895 := bstep (se 1 (by rfl) ⟨1171421, by rfl⟩ : syracuseStep 1561895 = 2342843) B2342843
theorem B1758503 : Blo 1040609 1758503 := bstep (se 1 (by rfl) ⟨1318877, by rfl⟩ : syracuseStep 1758503 = 2637755) B2637755
theorem B1561979 : Blo 1040609 1561979 := bstep (se 1 (by rfl) ⟨1171484, by rfl⟩ : syracuseStep 1561979 = 2342969) B2342969
theorem B1562105 : Blo 1040609 1562105 := bstep (se 2 (by rfl) ⟨585789, by rfl⟩ : syracuseStep 1562105 = 1171579) B1171579
theorem B8902183 : Blo 1040609 8902183 := bstep (se 1 (by rfl) ⟨6676637, by rfl⟩ : syracuseStep 8902183 = 13353275) B13353275
theorem B1562207 : Blo 1040609 1562207 := bstep (se 1 (by rfl) ⟨1171655, by rfl⟩ : syracuseStep 1562207 = 2343311) B2343311
theorem B2348639 : Blo 1040609 2348639 := bstep (se 1 (by rfl) ⟨1761479, by rfl⟩ : syracuseStep 2348639 = 3522959) B3522959
theorem B2643617 : Blo 1040609 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B1758955 : Blo 1040609 1758955 := bstep (se 1 (by rfl) ⟨1319216, by rfl⟩ : syracuseStep 1758955 = 2638433) B2638433
theorem B1562423 : Blo 1040609 1562423 := bstep (se 1 (by rfl) ⟨1171817, by rfl⟩ : syracuseStep 1562423 = 2343635) B2343635
theorem B2348855 : Blo 1040609 2348855 := bstep (se 1 (by rfl) ⟨1761641, by rfl⟩ : syracuseStep 2348855 = 3523283) B3523283
theorem B9164731 : Blo 1040609 9164731 := bstep (se 1 (by rfl) ⟨6873548, by rfl⟩ : syracuseStep 9164731 = 13747097) B13747097
theorem B121690133 : Blo 1040609 121690133 := bstep (se 6 (by rfl) ⟨2852112, by rfl⟩ : syracuseStep 121690133 = 5704225) B5704225
theorem B1562729 : Blo 1040609 1562729 := bstep (se 2 (by rfl) ⟨586023, by rfl⟩ : syracuseStep 1562729 = 1172047) B1172047
theorem B2349161 : Blo 1040609 2349161 := bstep (se 2 (by rfl) ⟨880935, by rfl⟩ : syracuseStep 2349161 = 1761871) B1761871
theorem B2644073 : Blo 1040609 2644073 := bstep (se 2 (by rfl) ⟨991527, by rfl⟩ : syracuseStep 2644073 = 1983055) B1983055
theorem B1563047 : Blo 1040609 1563047 := bstep (se 1 (by rfl) ⟨1172285, by rfl⟩ : syracuseStep 1563047 = 2344571) B2344571
theorem B25385399 : Blo 1040609 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B1563131 : Blo 1040609 1563131 := bstep (se 1 (by rfl) ⟨1172348, by rfl⟩ : syracuseStep 1563131 = 2344697) B2344697
theorem B11262503 : Blo 1040609 11262503 := bstep (se 1 (by rfl) ⟨8446877, by rfl⟩ : syracuseStep 11262503 = 16893755) B16893755
theorem B2349647 : Blo 1040609 2349647 := bstep (se 1 (by rfl) ⟨1762235, by rfl⟩ : syracuseStep 2349647 = 3524471) B3524471
theorem B1563257 : Blo 1040609 1563257 := bstep (se 2 (by rfl) ⟨586221, by rfl⟩ : syracuseStep 1563257 = 1172443) B1172443
theorem B1563311 : Blo 1040609 1563311 := bstep (se 1 (by rfl) ⟨1172483, by rfl⟩ : syracuseStep 1563311 = 2344967) B2344967
theorem B1759927 : Blo 1040609 1759927 := bstep (se 1 (by rfl) ⟨1319945, by rfl⟩ : syracuseStep 1759927 = 2639891) B2639891
theorem B7527107 : Blo 1040609 7527107 := bstep (se 1 (by rfl) ⟨5645330, by rfl⟩ : syracuseStep 7527107 = 11290661) B11290661
theorem B1563359 : Blo 1040609 1563359 := bstep (se 1 (by rfl) ⟨1172519, by rfl⟩ : syracuseStep 1563359 = 2345039) B2345039
theorem B2349791 : Blo 1040609 2349791 := bstep (se 1 (by rfl) ⟨1762343, by rfl⟩ : syracuseStep 2349791 = 3524687) B3524687
theorem B4447163 : Blo 1040609 4447163 := bstep (se 1 (by rfl) ⟨3335372, by rfl⟩ : syracuseStep 4447163 = 6670745) B6670745
theorem B8575931 : Blo 1040609 8575931 := bstep (se 1 (by rfl) ⟨6431948, by rfl⟩ : syracuseStep 8575931 = 12863897) B12863897
theorem B2350043 : Blo 1040609 2350043 := bstep (se 1 (by rfl) ⟨1762532, by rfl⟩ : syracuseStep 2350043 = 3525065) B3525065
theorem B1563623 : Blo 1040609 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B1760231 : Blo 1040609 1760231 := bstep (se 1 (by rfl) ⟨1320173, by rfl⟩ : syracuseStep 1760231 = 2640347) B2640347
theorem B2350223 : Blo 1040609 2350223 := bstep (se 1 (by rfl) ⟨1762667, by rfl⟩ : syracuseStep 2350223 = 3525335) B3525335
theorem B3169469 : Blo 1040609 3169469 := bstep (se 3 (by rfl) ⟨594275, by rfl⟩ : syracuseStep 3169469 = 1188551) B1188551
theorem B1563881 : Blo 1040609 1563881 := bstep (se 2 (by rfl) ⟨586455, by rfl⟩ : syracuseStep 1563881 = 1172911) B1172911
theorem B2350313 : Blo 1040609 2350313 := bstep (se 2 (by rfl) ⟨881367, by rfl⟩ : syracuseStep 2350313 = 1762735) B1762735
theorem B1563935 : Blo 1040609 1563935 := bstep (se 1 (by rfl) ⟨1172951, by rfl⟩ : syracuseStep 1563935 = 2345903) B2345903
theorem B2350367 : Blo 1040609 2350367 := bstep (se 1 (by rfl) ⟨1762775, by rfl⟩ : syracuseStep 2350367 = 3525551) B3525551
theorem B1564103 : Blo 1040609 1564103 := bstep (se 1 (by rfl) ⟨1173077, by rfl⟩ : syracuseStep 1564103 = 2346155) B2346155
theorem B1171039 : Blo 1040609 1171039 := bstep (se 1 (by rfl) ⟨878279, by rfl⟩ : syracuseStep 1171039 = 1756559) B1756559
theorem B7921313 : Blo 1040609 7921313 := bstep (se 2 (by rfl) ⟨2970492, by rfl⟩ : syracuseStep 7921313 = 5940985) B5940985
theorem B3333899 : Blo 1040609 3333899 := bstep (se 1 (by rfl) ⟨2500424, by rfl⟩ : syracuseStep 3333899 = 5000849) B5000849
theorem B1564457 : Blo 1040609 1564457 := bstep (se 2 (by rfl) ⟨586671, by rfl⟩ : syracuseStep 1564457 = 1173343) B1173343
theorem B1564463 : Blo 1040609 1564463 := bstep (se 1 (by rfl) ⟨1173347, by rfl⟩ : syracuseStep 1564463 = 2346695) B2346695
theorem B17784683 : Blo 1040609 17784683 := bstep (se 1 (by rfl) ⟨13338512, by rfl⟩ : syracuseStep 17784683 = 26677025) B26677025
theorem B1761385 : Blo 1040609 1761385 := bstep (se 2 (by rfl) ⟨660519, by rfl⟩ : syracuseStep 1761385 = 1321039) B1321039
theorem B5431499 : Blo 1040609 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B1564937 : Blo 1040609 1564937 := bstep (se 2 (by rfl) ⟨586851, by rfl⟩ : syracuseStep 1564937 = 1173703) B1173703
theorem B1040671 : Blo 1040609 1040671 := bstep (se 1 (by rfl) ⟨780503, by rfl⟩ : syracuseStep 1040671 = 1561007) B1561007
theorem B1040731 : Blo 1040609 1040731 := bstep (se 1 (by rfl) ⟨780548, by rfl⟩ : syracuseStep 1040731 = 1561097) B1561097
theorem B1040751 : Blo 1040609 1040751 := bstep (se 1 (by rfl) ⟨780563, by rfl⟩ : syracuseStep 1040751 = 1561127) B1561127
theorem B1565039 : Blo 1040609 1565039 := bstep (se 1 (by rfl) ⟨1173779, by rfl⟩ : syracuseStep 1565039 = 2347559) B2347559
theorem B1040807 : Blo 1040609 1040807 := bstep (se 1 (by rfl) ⟨780605, by rfl⟩ : syracuseStep 1040807 = 1561211) B1561211
theorem B11887073 : Blo 1040609 11887073 := bstep (se 2 (by rfl) ⟨4457652, by rfl⟩ : syracuseStep 11887073 = 8915305) B8915305
theorem B1040891 : Blo 1040609 1040891 := bstep (se 1 (by rfl) ⟨780668, by rfl⟩ : syracuseStep 1040891 = 1561337) B1561337
theorem B1040959 : Blo 1040609 1040959 := bstep (se 1 (by rfl) ⟨780719, by rfl⟩ : syracuseStep 1040959 = 1561439) B1561439
theorem B1040967 : Blo 1040609 1040967 := bstep (se 1 (by rfl) ⟨780725, by rfl⟩ : syracuseStep 1040967 = 1561451) B1561451
theorem B1565255 : Blo 1040609 1565255 := bstep (se 1 (by rfl) ⟨1173941, by rfl⟩ : syracuseStep 1565255 = 2347883) B2347883
theorem B1565291 : Blo 1040609 1565291 := bstep (se 1 (by rfl) ⟨1173968, by rfl⟩ : syracuseStep 1565291 = 2347937) B2347937
theorem B1041119 : Blo 1040609 1041119 := bstep (se 1 (by rfl) ⟨780839, by rfl⟩ : syracuseStep 1041119 = 1561679) B1561679
theorem B1172191 : Blo 1040609 1172191 := bstep (se 1 (by rfl) ⟨879143, by rfl⟩ : syracuseStep 1172191 = 1758287) B1758287
theorem B1041199 : Blo 1040609 1041199 := bstep (se 1 (by rfl) ⟨780899, by rfl⟩ : syracuseStep 1041199 = 1561799) B1561799
theorem B1565519 : Blo 1040609 1565519 := bstep (se 1 (by rfl) ⟨1174139, by rfl⟩ : syracuseStep 1565519 = 2348279) B2348279
theorem B40035221 : Blo 1040609 40035221 := bstep (se 6 (by rfl) ⟨938325, by rfl⟩ : syracuseStep 40035221 = 1876651) B1876651
theorem B1041307 : Blo 1040609 1041307 := bstep (se 1 (by rfl) ⟨780980, by rfl⟩ : syracuseStep 1041307 = 1561961) B1561961
theorem B1041359 : Blo 1040609 1041359 := bstep (se 1 (by rfl) ⟨781019, by rfl⟩ : syracuseStep 1041359 = 1562039) B1562039
theorem B1041383 : Blo 1040609 1041383 := bstep (se 1 (by rfl) ⟨781037, by rfl⟩ : syracuseStep 1041383 = 1562075) B1562075
theorem B9495589 : Blo 1040609 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B4449437 : Blo 1040609 4449437 := bstep (se 3 (by rfl) ⟨834269, by rfl⟩ : syracuseStep 4449437 = 1668539) B1668539
theorem B1565915 : Blo 1040609 1565915 := bstep (se 1 (by rfl) ⟨1174436, by rfl⟩ : syracuseStep 1565915 = 2348873) B2348873
theorem B1041695 : Blo 1040609 1041695 := bstep (se 1 (by rfl) ⟨781271, by rfl⟩ : syracuseStep 1041695 = 1562543) B1562543
theorem B1172767 : Blo 1040609 1172767 := bstep (se 1 (by rfl) ⟨879575, by rfl⟩ : syracuseStep 1172767 = 1759151) B1759151
theorem B1041755 : Blo 1040609 1041755 := bstep (se 1 (by rfl) ⟨781316, by rfl⟩ : syracuseStep 1041755 = 1562633) B1562633
theorem B1041775 : Blo 1040609 1041775 := bstep (se 1 (by rfl) ⟨781331, by rfl⟩ : syracuseStep 1041775 = 1562663) B1562663
theorem B1566089 : Blo 1040609 1566089 := bstep (se 2 (by rfl) ⟨587283, by rfl⟩ : syracuseStep 1566089 = 1174567) B1174567
theorem B1041831 : Blo 1040609 1041831 := bstep (se 1 (by rfl) ⟨781373, by rfl⟩ : syracuseStep 1041831 = 1562747) B1562747
theorem B4449725 : Blo 1040609 4449725 := bstep (se 3 (by rfl) ⟨834323, by rfl⟩ : syracuseStep 4449725 = 1668647) B1668647
theorem B1041915 : Blo 1040609 1041915 := bstep (se 1 (by rfl) ⟨781436, by rfl⟩ : syracuseStep 1041915 = 1562873) B1562873
theorem B5269049 : Blo 1040609 5269049 := bstep (se 2 (by rfl) ⟨1975893, by rfl⟩ : syracuseStep 5269049 = 3951787) B3951787
theorem B7923257 : Blo 1040609 7923257 := bstep (se 2 (by rfl) ⟨2971221, by rfl⟩ : syracuseStep 7923257 = 5942443) B5942443
theorem B1041983 : Blo 1040609 1041983 := bstep (se 1 (by rfl) ⟨781487, by rfl⟩ : syracuseStep 1041983 = 1562975) B1562975
theorem B1173055 : Blo 1040609 1173055 := bstep (se 1 (by rfl) ⟨879791, by rfl⟩ : syracuseStep 1173055 = 1759583) B1759583
theorem B1041991 : Blo 1040609 1041991 := bstep (se 1 (by rfl) ⟨781493, by rfl⟩ : syracuseStep 1041991 = 1562987) B1562987
theorem B1042143 : Blo 1040609 1042143 := bstep (se 1 (by rfl) ⟨781607, by rfl⟩ : syracuseStep 1042143 = 1563215) B1563215
theorem B1566443 : Blo 1040609 1566443 := bstep (se 1 (by rfl) ⟨1174832, by rfl⟩ : syracuseStep 1566443 = 2349665) B2349665
theorem B1042223 : Blo 1040609 1042223 := bstep (se 1 (by rfl) ⟨781667, by rfl⟩ : syracuseStep 1042223 = 1563335) B1563335
theorem B5629783 : Blo 1040609 5629783 := bstep (se 1 (by rfl) ⟨4222337, by rfl⟩ : syracuseStep 5629783 = 8444675) B8444675
theorem B4450135 : Blo 1040609 4450135 := bstep (se 1 (by rfl) ⟨3337601, by rfl⟩ : syracuseStep 4450135 = 6675203) B6675203
theorem B11888531 : Blo 1040609 11888531 := bstep (se 1 (by rfl) ⟨8916398, by rfl⟩ : syracuseStep 11888531 = 17832797) B17832797
theorem B1042331 : Blo 1040609 1042331 := bstep (se 1 (by rfl) ⟨781748, by rfl⟩ : syracuseStep 1042331 = 1563497) B1563497
theorem B1042383 : Blo 1040609 1042383 := bstep (se 1 (by rfl) ⟨781787, by rfl⟩ : syracuseStep 1042383 = 1563575) B1563575
theorem B1566671 : Blo 1040609 1566671 := bstep (se 1 (by rfl) ⟨1175003, by rfl⟩ : syracuseStep 1566671 = 2350007) B2350007
theorem B1042407 : Blo 1040609 1042407 := bstep (se 1 (by rfl) ⟨781805, by rfl⟩ : syracuseStep 1042407 = 1563611) B1563611
theorem B1042719 : Blo 1040609 1042719 := bstep (se 1 (by rfl) ⟨782039, by rfl⟩ : syracuseStep 1042719 = 1564079) B1564079
theorem B1042779 : Blo 1040609 1042779 := bstep (se 1 (by rfl) ⟨782084, by rfl⟩ : syracuseStep 1042779 = 1564169) B1564169
theorem B1042799 : Blo 1040609 1042799 := bstep (se 1 (by rfl) ⟨782099, by rfl⟩ : syracuseStep 1042799 = 1564199) B1564199
theorem B1173883 : Blo 1040609 1173883 := bstep (se 1 (by rfl) ⟨880412, by rfl⟩ : syracuseStep 1173883 = 1760825) B1760825
theorem B1042855 : Blo 1040609 1042855 := bstep (se 1 (by rfl) ⟨782141, by rfl⟩ : syracuseStep 1042855 = 1564283) B1564283
theorem B1042939 : Blo 1040609 1042939 := bstep (se 1 (by rfl) ⟨782204, by rfl⟩ : syracuseStep 1042939 = 1564409) B1564409
theorem B1043007 : Blo 1040609 1043007 := bstep (se 1 (by rfl) ⟨782255, by rfl⟩ : syracuseStep 1043007 = 1564511) B1564511
theorem B1043015 : Blo 1040609 1043015 := bstep (se 1 (by rfl) ⟨782261, by rfl⟩ : syracuseStep 1043015 = 1564523) B1564523
theorem B67758727 : Blo 1040609 67758727 := bstep (se 1 (by rfl) ⟨50819045, by rfl⟩ : syracuseStep 67758727 = 101638091) B101638091
theorem B1043167 : Blo 1040609 1043167 := bstep (se 1 (by rfl) ⟨782375, by rfl⟩ : syracuseStep 1043167 = 1564751) B1564751
theorem B3762935 : Blo 1040609 3762935 := bstep (se 1 (by rfl) ⟨2822201, by rfl⟩ : syracuseStep 3762935 = 5644403) B5644403
theorem B1043247 : Blo 1040609 1043247 := bstep (se 1 (by rfl) ⟨782435, by rfl⟩ : syracuseStep 1043247 = 1564871) B1564871
theorem B1174351 : Blo 1040609 1174351 := bstep (se 1 (by rfl) ⟨880763, by rfl⟩ : syracuseStep 1174351 = 1761527) B1761527
theorem B1043355 : Blo 1040609 1043355 := bstep (se 1 (by rfl) ⟨782516, by rfl⟩ : syracuseStep 1043355 = 1565033) B1565033
theorem B1043407 : Blo 1040609 1043407 := bstep (se 1 (by rfl) ⟨782555, by rfl⟩ : syracuseStep 1043407 = 1565111) B1565111
theorem B1043431 : Blo 1040609 1043431 := bstep (se 1 (by rfl) ⟨782573, by rfl⟩ : syracuseStep 1043431 = 1565147) B1565147
theorem B6679691 : Blo 1040609 6679691 := bstep (se 1 (by rfl) ⟨5009768, by rfl⟩ : syracuseStep 6679691 = 10019537) B10019537
theorem B1174747 : Blo 1040609 1174747 := bstep (se 1 (by rfl) ⟨881060, by rfl⟩ : syracuseStep 1174747 = 1762121) B1762121
theorem B1043743 : Blo 1040609 1043743 := bstep (se 1 (by rfl) ⟨782807, by rfl⟩ : syracuseStep 1043743 = 1565615) B1565615
theorem B1043803 : Blo 1040609 1043803 := bstep (se 1 (by rfl) ⟨782852, by rfl⟩ : syracuseStep 1043803 = 1565705) B1565705
theorem B1043823 : Blo 1040609 1043823 := bstep (se 1 (by rfl) ⟨782867, by rfl⟩ : syracuseStep 1043823 = 1565735) B1565735
theorem B1043879 : Blo 1040609 1043879 := bstep (se 1 (by rfl) ⟨782909, by rfl⟩ : syracuseStep 1043879 = 1565819) B1565819
theorem B1043963 : Blo 1040609 1043963 := bstep (se 1 (by rfl) ⟨782972, by rfl⟩ : syracuseStep 1043963 = 1565945) B1565945
theorem B1175035 : Blo 1040609 1175035 := bstep (se 1 (by rfl) ⟨881276, by rfl⟩ : syracuseStep 1175035 = 1762553) B1762553
theorem B1044031 : Blo 1040609 1044031 := bstep (se 1 (by rfl) ⟨783023, by rfl⟩ : syracuseStep 1044031 = 1566047) B1566047
theorem B1044039 : Blo 1040609 1044039 := bstep (se 1 (by rfl) ⟨783029, by rfl⟩ : syracuseStep 1044039 = 1566059) B1566059
theorem B5271155 : Blo 1040609 5271155 := bstep (se 1 (by rfl) ⟨3953366, by rfl⟩ : syracuseStep 5271155 = 7906733) B7906733
theorem B1044191 : Blo 1040609 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B1044271 : Blo 1040609 1044271 := bstep (se 1 (by rfl) ⟨783203, by rfl⟩ : syracuseStep 1044271 = 1566407) B1566407
theorem B3764029 : Blo 1040609 3764029 := bstep (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) B1411511
theorem B1044379 : Blo 1040609 1044379 := bstep (se 1 (by rfl) ⟨783284, by rfl⟩ : syracuseStep 1044379 = 1566569) B1566569
theorem B5009309 : Blo 1040609 5009309 := bstep (se 3 (by rfl) ⟨939245, by rfl⟩ : syracuseStep 5009309 = 1878491) B1878491
theorem B1044431 : Blo 1040609 1044431 := bstep (se 1 (by rfl) ⟨783323, by rfl⟩ : syracuseStep 1044431 = 1566647) B1566647
theorem B1044455 : Blo 1040609 1044455 := bstep (se 1 (by rfl) ⟨783341, by rfl⟩ : syracuseStep 1044455 = 1566683) B1566683
theorem B5009939 : Blo 1040609 5009939 := bstep (se 1 (by rfl) ⟨3757454, by rfl⟩ : syracuseStep 5009939 = 7514909) B7514909
theorem B10711601 : Blo 1040609 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B6681149 : Blo 1040609 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B14480117 : Blo 1040609 14480117 := bstep (se 5 (by rfl) ⟨678755, by rfl⟩ : syracuseStep 14480117 = 1357511) B1357511
theorem B5075959 : Blo 1040609 5075959 := bstep (se 1 (by rfl) ⟨3806969, by rfl⟩ : syracuseStep 5075959 = 7613939) B7613939
theorem B13366397 : Blo 1040609 13366397 := bstep (se 3 (by rfl) ⟨2506199, by rfl⟩ : syracuseStep 13366397 = 5012399) B5012399
theorem B2815175 : Blo 1040609 2815175 := bstep (se 1 (by rfl) ⟨2111381, by rfl⟩ : syracuseStep 2815175 = 4222763) B4222763
theorem B5272775 : Blo 1040609 5272775 := bstep (se 1 (by rfl) ⟨3954581, by rfl⟩ : syracuseStep 5272775 = 7909163) B7909163
theorem B5272937 : Blo 1040609 5272937 := bstep (se 2 (by rfl) ⟨1977351, by rfl⟩ : syracuseStep 5272937 = 3954703) B3954703
theorem B7927145 : Blo 1040609 7927145 := bstep (se 2 (by rfl) ⟨2972679, by rfl⟩ : syracuseStep 7927145 = 5945359) B5945359
theorem B6420311 : Blo 1040609 6420311 := bstep (se 1 (by rfl) ⟨4815233, by rfl⟩ : syracuseStep 6420311 = 9630467) B9630467
theorem B2815951 : Blo 1040609 2815951 := bstep (se 1 (by rfl) ⟨2111963, by rfl⟩ : syracuseStep 2815951 = 4223927) B4223927
theorem B9500807 : Blo 1040609 9500807 := bstep (se 1 (by rfl) ⟨7125605, by rfl⟩ : syracuseStep 9500807 = 14251211) B14251211
theorem B1407241 : Blo 1040609 1407241 := bstep (se 2 (by rfl) ⟨527715, by rfl⟩ : syracuseStep 1407241 = 1055431) B1055431
theorem B17824049 : Blo 1040609 17824049 := bstep (se 2 (by rfl) ⟨6684018, by rfl⟩ : syracuseStep 17824049 = 13368037) B13368037
theorem B10025801 : Blo 1040609 10025801 := bstep (se 2 (by rfl) ⟨3759675, by rfl⟩ : syracuseStep 10025801 = 7519351) B7519351
theorem B5929847 : Blo 1040609 5929847 := bstep (se 1 (by rfl) ⟨4447385, by rfl⟩ : syracuseStep 5929847 = 8894771) B8894771
theorem B3013519 : Blo 1040609 3013519 := bstep (se 1 (by rfl) ⟨2260139, by rfl⟩ : syracuseStep 3013519 = 4520279) B4520279
theorem B1112987 : Blo 1040609 1112987 := bstep (se 1 (by rfl) ⟨834740, by rfl⟩ : syracuseStep 1112987 = 1669481) B1669481
theorem B2817011 : Blo 1040609 2817011 := bstep (se 1 (by rfl) ⟨2112758, by rfl⟩ : syracuseStep 2817011 = 4225517) B4225517
theorem B4455809 : Blo 1040609 4455809 := bstep (se 2 (by rfl) ⟨1670928, by rfl⟩ : syracuseStep 4455809 = 3341857) B3341857
theorem B3964409 : Blo 1040609 3964409 := bstep (se 2 (by rfl) ⟨1486653, by rfl⟩ : syracuseStep 3964409 = 2973307) B2973307
theorem B16055819 : Blo 1040609 16055819 := bstep (se 1 (by rfl) ⟨12041864, by rfl⟩ : syracuseStep 16055819 = 24083729) B24083729
theorem B43417417 : Blo 1040609 43417417 := bstep (se 2 (by rfl) ⟨16281531, by rfl⟩ : syracuseStep 43417417 = 32563063) B32563063
theorem B3342779 : Blo 1040609 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B6423079 : Blo 1040609 6423079 := bstep (se 1 (by rfl) ⟨4817309, by rfl⟩ : syracuseStep 6423079 = 9634619) B9634619
theorem B2229049 : Blo 1040609 2229049 := bstep (se 2 (by rfl) ⟨835893, by rfl⟩ : syracuseStep 2229049 = 1671787) B1671787
theorem B7504759 : Blo 1040609 7504759 := bstep (se 1 (by rfl) ⟨5628569, by rfl⟩ : syracuseStep 7504759 = 11257139) B11257139
theorem B2229203 : Blo 1040609 2229203 := bstep (se 1 (by rfl) ⟨1671902, by rfl⟩ : syracuseStep 2229203 = 3343805) B3343805
theorem B1115131 : Blo 1040609 1115131 := bstep (se 1 (by rfl) ⟨836348, by rfl⟩ : syracuseStep 1115131 = 1672697) B1672697
theorem B6685841 : Blo 1040609 6685841 := bstep (se 2 (by rfl) ⟨2507190, by rfl⟩ : syracuseStep 6685841 = 5014381) B5014381
theorem B6096343 : Blo 1040609 6096343 := bstep (se 1 (by rfl) ⟨4572257, by rfl⟩ : syracuseStep 6096343 = 9144515) B9144515
theorem B1672825 : Blo 1040609 1672825 := bstep (se 2 (by rfl) ⟨627309, by rfl⟩ : syracuseStep 1672825 = 1254619) B1254619
theorem B7506377 : Blo 1040609 7506377 := bstep (se 2 (by rfl) ⟨2814891, by rfl⟩ : syracuseStep 7506377 = 5629783) B5629783
theorem B5933513 : Blo 1040609 5933513 := bstep (se 2 (by rfl) ⟨2225067, by rfl⟩ : syracuseStep 5933513 = 4450135) B4450135
theorem B3345239 : Blo 1040609 3345239 := bstep (se 1 (by rfl) ⟨2508929, by rfl⟩ : syracuseStep 3345239 = 5017859) B5017859
theorem B6687967 : Blo 1040609 6687967 := bstep (se 1 (by rfl) ⟨5015975, by rfl⟩ : syracuseStep 6687967 = 10031951) B10031951
theorem B13340153 : Blo 1040609 13340153 := bstep (se 2 (by rfl) ⟨5002557, by rfl⟩ : syracuseStep 13340153 = 10005115) B10005115
theorem B90344969 : Blo 1040609 90344969 := bstep (se 2 (by rfl) ⟨33879363, by rfl⟩ : syracuseStep 90344969 = 67758727) B67758727
theorem B1250159 : Blo 1040609 1250159 := bstep (se 1 (by rfl) ⟨937619, by rfl⟩ : syracuseStep 1250159 = 1875239) B1875239
theorem B5018705 : Blo 1040609 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B5280875 : Blo 1040609 5280875 := bstep (se 1 (by rfl) ⟨3960656, by rfl⟩ : syracuseStep 5280875 = 7921313) B7921313
theorem B1317055 : Blo 1040609 1317055 := bstep (se 1 (by rfl) ⟨987791, by rfl⟩ : syracuseStep 1317055 = 1975583) B1975583
theorem B3512699 : Blo 1040609 3512699 := bstep (se 1 (by rfl) ⟨2634524, by rfl⟩ : syracuseStep 3512699 = 5269049) B5269049
theorem B5282171 : Blo 1040609 5282171 := bstep (se 1 (by rfl) ⟨3961628, by rfl⟩ : syracuseStep 5282171 = 7923257) B7923257
theorem B3512969 : Blo 1040609 3512969 := bstep (se 2 (by rfl) ⟨1317363, by rfl⟩ : syracuseStep 3512969 = 2634727) B2634727
theorem B11869577 : Blo 1040609 11869577 := bstep (se 2 (by rfl) ⟨4451091, by rfl⟩ : syracuseStep 11869577 = 8902183) B8902183
theorem B9510479 : Blo 1040609 9510479 := bstep (se 1 (by rfl) ⟨7132859, by rfl⟩ : syracuseStep 9510479 = 14265719) B14265719
theorem B3514103 : Blo 1040609 3514103 := bstep (se 1 (by rfl) ⟨2635577, by rfl⟩ : syracuseStep 3514103 = 5271155) B5271155
theorem B5644055 : Blo 1040609 5644055 := bstep (se 1 (by rfl) ⟨4233041, by rfl⟩ : syracuseStep 5644055 = 8466083) B8466083
theorem B1876321 : Blo 1040609 1876321 := bstep (se 2 (by rfl) ⟨703620, by rfl⟩ : syracuseStep 1876321 = 1407241) B1407241
theorem B1876783 : Blo 1040609 1876783 := bstep (se 1 (by rfl) ⟨1407587, by rfl⟩ : syracuseStep 1876783 = 2815175) B2815175
theorem B3515183 : Blo 1040609 3515183 := bstep (se 1 (by rfl) ⟨2636387, by rfl⟩ : syracuseStep 3515183 = 5272775) B5272775
theorem B3515291 : Blo 1040609 3515291 := bstep (se 1 (by rfl) ⟨2636468, by rfl⟩ : syracuseStep 3515291 = 5272937) B5272937
theorem B5284763 : Blo 1040609 5284763 := bstep (se 1 (by rfl) ⟨3963572, by rfl⟩ : syracuseStep 5284763 = 7927145) B7927145
theorem B6333871 : Blo 1040609 6333871 := bstep (se 1 (by rfl) ⟨4750403, by rfl⟩ : syracuseStep 6333871 = 9500807) B9500807
theorem B108275399 : Blo 1040609 108275399 := bstep (se 1 (by rfl) ⟨81206549, by rfl⟩ : syracuseStep 108275399 = 162413099) B162413099
theorem B8464135 : Blo 1040609 8464135 := bstep (se 1 (by rfl) ⟨6348101, by rfl⟩ : syracuseStep 8464135 = 12696203) B12696203
theorem B1320943 : Blo 1040609 1320943 := bstep (se 1 (by rfl) ⟨990707, by rfl⟩ : syracuseStep 1320943 = 1981415) B1981415
theorem B1878007 : Blo 1040609 1878007 := bstep (se 1 (by rfl) ⟨1408505, by rfl⟩ : syracuseStep 1878007 = 2817011) B2817011
theorem B3516425 : Blo 1040609 3516425 := bstep (se 2 (by rfl) ⟨1318659, by rfl⟩ : syracuseStep 3516425 = 2637319) B2637319
theorem B8890397 : Blo 1040609 8890397 := bstep (se 3 (by rfl) ⟨1666949, by rfl⟩ : syracuseStep 8890397 = 3333899) B3333899
theorem B1976555 : Blo 1040609 1976555 := bstep (se 1 (by rfl) ⟨1482416, by rfl⟩ : syracuseStep 1976555 = 2964833) B2964833
theorem B12855809 : Blo 1040609 12855809 := bstep (se 2 (by rfl) ⟨4820928, by rfl⟩ : syracuseStep 12855809 = 9641857) B9641857
theorem B5941943 : Blo 1040609 5941943 := bstep (se 1 (by rfl) ⟨4456457, by rfl⟩ : syracuseStep 5941943 = 8912915) B8912915
theorem B17837171 : Blo 1040609 17837171 := bstep (se 1 (by rfl) ⟨13377878, by rfl⟩ : syracuseStep 17837171 = 26755757) B26755757
theorem B3517721 : Blo 1040609 3517721 := bstep (se 2 (by rfl) ⟨1319145, by rfl⟩ : syracuseStep 3517721 = 2638291) B2638291
theorem B3517775 : Blo 1040609 3517775 := bstep (se 1 (by rfl) ⟨2638331, by rfl⟩ : syracuseStep 3517775 = 5276663) B5276663
theorem B52178269 : Blo 1040609 52178269 := bstep (se 3 (by rfl) ⟨9783425, by rfl⟩ : syracuseStep 52178269 = 19566851) B19566851
theorem B1977929 : Blo 1040609 1977929 := bstep (se 2 (by rfl) ⟨741723, by rfl⟩ : syracuseStep 1977929 = 1483447) B1483447
theorem B30060557 : Blo 1040609 30060557 := bstep (se 3 (by rfl) ⟨5636354, by rfl⟩ : syracuseStep 30060557 = 11272709) B11272709
theorem B12660785 : Blo 1040609 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B7516583 : Blo 1040609 7516583 := bstep (se 1 (by rfl) ⟨5637437, by rfl⟩ : syracuseStep 7516583 = 11274875) B11274875
theorem B5943719 : Blo 1040609 5943719 := bstep (se 1 (by rfl) ⟨4457789, by rfl⟩ : syracuseStep 5943719 = 8915579) B8915579
theorem B3519071 : Blo 1040609 3519071 := bstep (se 1 (by rfl) ⟨2639303, by rfl⟩ : syracuseStep 3519071 = 5278607) B5278607
theorem B7910135 : Blo 1040609 7910135 := bstep (se 1 (by rfl) ⟨5932601, by rfl⟩ : syracuseStep 7910135 = 11865203) B11865203
theorem B7516961 : Blo 1040609 7516961 := bstep (se 2 (by rfl) ⟨2818860, by rfl⟩ : syracuseStep 7516961 = 5637721) B5637721
theorem B20034377 : Blo 1040609 20034377 := bstep (se 2 (by rfl) ⟨7512891, by rfl⟩ : syracuseStep 20034377 = 15025783) B15025783
theorem B13382495 : Blo 1040609 13382495 := bstep (se 1 (by rfl) ⟨10036871, by rfl⟩ : syracuseStep 13382495 = 20073743) B20073743
theorem B1979387 : Blo 1040609 1979387 := bstep (se 1 (by rfl) ⟨1484540, by rfl⟩ : syracuseStep 1979387 = 2969081) B2969081
theorem B1356907 : Blo 1040609 1356907 := bstep (se 1 (by rfl) ⟨1017680, by rfl⟩ : syracuseStep 1356907 = 2035361) B2035361
theorem B2635163 : Blo 1040609 2635163 := bstep (se 1 (by rfl) ⟨1976372, by rfl⟩ : syracuseStep 2635163 = 3952745) B3952745
theorem B1979873 : Blo 1040609 1979873 := bstep (se 2 (by rfl) ⟨742452, by rfl⟩ : syracuseStep 1979873 = 1484905) B1484905
theorem B1881569 : Blo 1040609 1881569 := bstep (se 2 (by rfl) ⟨705588, by rfl⟩ : syracuseStep 1881569 = 1411177) B1411177
theorem B3520313 : Blo 1040609 3520313 := bstep (se 2 (by rfl) ⟨1320117, by rfl⟩ : syracuseStep 3520313 = 2640235) B2640235
theorem B3520475 : Blo 1040609 3520475 := bstep (se 1 (by rfl) ⟨2640356, by rfl⟩ : syracuseStep 3520475 = 5280713) B5280713
theorem B3520745 : Blo 1040609 3520745 := bstep (se 2 (by rfl) ⟨1320279, by rfl⟩ : syracuseStep 3520745 = 2640559) B2640559
theorem B190462241 : Blo 1040609 190462241 := bstep (se 2 (by rfl) ⟨71423340, by rfl⟩ : syracuseStep 190462241 = 142846681) B142846681
theorem B3521177 : Blo 1040609 3521177 := bstep (se 2 (by rfl) ⟨1320441, by rfl⟩ : syracuseStep 3521177 = 2640883) B2640883
theorem B16923599 : Blo 1040609 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B5717287 : Blo 1040609 5717287 := bstep (se 1 (by rfl) ⟨4287965, by rfl⟩ : syracuseStep 5717287 = 8575931) B8575931
theorem B2964775 : Blo 1040609 2964775 := bstep (se 1 (by rfl) ⟨2223581, by rfl⟩ : syracuseStep 2964775 = 4447163) B4447163
theorem B5946817 : Blo 1040609 5946817 := bstep (se 2 (by rfl) ⟨2230056, by rfl⟩ : syracuseStep 5946817 = 4460113) B4460113
theorem B2112979 : Blo 1040609 2112979 := bstep (se 1 (by rfl) ⟨1584734, by rfl⟩ : syracuseStep 2112979 = 3169469) B3169469
theorem B2342375 : Blo 1040609 2342375 := bstep (se 1 (by rfl) ⟨1756781, by rfl⟩ : syracuseStep 2342375 = 3513563) B3513563
theorem B6340609 : Blo 1040609 6340609 := bstep (se 2 (by rfl) ⟨2377728, by rfl⟩ : syracuseStep 6340609 = 4755457) B4755457
theorem B2342951 : Blo 1040609 2342951 := bstep (se 1 (by rfl) ⟨1757213, by rfl⟩ : syracuseStep 2342951 = 3514427) B3514427
theorem B3620999 : Blo 1040609 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B2343131 : Blo 1040609 2343131 := bstep (se 1 (by rfl) ⟨1757348, by rfl⟩ : syracuseStep 2343131 = 3514697) B3514697
theorem B2343401 : Blo 1040609 2343401 := bstep (se 2 (by rfl) ⟨878775, by rfl⟩ : syracuseStep 2343401 = 1757551) B1757551
theorem B3523067 : Blo 1040609 3523067 := bstep (se 1 (by rfl) ⟨2642300, by rfl⟩ : syracuseStep 3523067 = 5284601) B5284601
theorem B26690147 : Blo 1040609 26690147 := bstep (se 1 (by rfl) ⟨20017610, by rfl⟩ : syracuseStep 26690147 = 40035221) B40035221
theorem B2343689 : Blo 1040609 2343689 := bstep (se 2 (by rfl) ⟨878883, by rfl⟩ : syracuseStep 2343689 = 1757767) B1757767
theorem B3523337 : Blo 1040609 3523337 := bstep (se 2 (by rfl) ⟨1321251, by rfl⟩ : syracuseStep 3523337 = 2642503) B2642503
theorem B2966291 : Blo 1040609 2966291 := bstep (se 1 (by rfl) ⟨2224718, by rfl⟩ : syracuseStep 2966291 = 4449437) B4449437
theorem B2966483 : Blo 1040609 2966483 := bstep (se 1 (by rfl) ⟨2224862, by rfl⟩ : syracuseStep 2966483 = 4449725) B4449725
theorem B2344265 : Blo 1040609 2344265 := bstep (se 2 (by rfl) ⟨879099, by rfl⟩ : syracuseStep 2344265 = 1758199) B1758199
theorem B6767945 : Blo 1040609 6767945 := bstep (se 2 (by rfl) ⟨2537979, by rfl⟩ : syracuseStep 6767945 = 5075959) B5075959
theorem B30033341 : Blo 1040609 30033341 := bstep (se 3 (by rfl) ⟨5631251, by rfl⟩ : syracuseStep 30033341 = 11262503) B11262503
theorem B3524093 : Blo 1040609 3524093 := bstep (se 3 (by rfl) ⟨660767, by rfl⟩ : syracuseStep 3524093 = 1321535) B1321535
theorem B6342461 : Blo 1040609 6342461 := bstep (se 3 (by rfl) ⟨1189211, by rfl⟩ : syracuseStep 6342461 = 2378423) B2378423
theorem B2508623 : Blo 1040609 2508623 := bstep (se 1 (by rfl) ⟨1881467, by rfl⟩ : syracuseStep 2508623 = 3762935) B3762935
theorem B20072285 : Blo 1040609 20072285 := bstep (se 3 (by rfl) ⟨3763553, by rfl⟩ : syracuseStep 20072285 = 7527107) B7527107
theorem B13354915 : Blo 1040609 13354915 := bstep (se 1 (by rfl) ⟨10016186, by rfl⟩ : syracuseStep 13354915 = 20032373) B20032373
theorem B2345255 : Blo 1040609 2345255 := bstep (se 1 (by rfl) ⟨1758941, by rfl⟩ : syracuseStep 2345255 = 3517883) B3517883
theorem B3524903 : Blo 1040609 3524903 := bstep (se 1 (by rfl) ⟨2643677, by rfl⟩ : syracuseStep 3524903 = 5287355) B5287355
theorem B2345273 : Blo 1040609 2345273 := bstep (se 2 (by rfl) ⟨879477, by rfl⟩ : syracuseStep 2345273 = 1758955) B1758955
theorem B2640185 : Blo 1040609 2640185 := bstep (se 2 (by rfl) ⟨990069, by rfl⟩ : syracuseStep 2640185 = 1980139) B1980139
theorem B2967965 : Blo 1040609 2967965 := bstep (se 3 (by rfl) ⟨556493, by rfl⟩ : syracuseStep 2967965 = 1112987) B1112987
theorem B27052631 : Blo 1040609 27052631 := bstep (se 1 (by rfl) ⟨20289473, by rfl⟩ : syracuseStep 27052631 = 40578947) B40578947
theorem B3754601 : Blo 1040609 3754601 := bstep (se 2 (by rfl) ⟨1407975, by rfl⟩ : syracuseStep 3754601 = 2815951) B2815951
theorem B1756201 : Blo 1040609 1756201 := bstep (se 2 (by rfl) ⟨658575, by rfl⟩ : syracuseStep 1756201 = 1317151) B1317151
theorem B9653411 : Blo 1040609 9653411 := bstep (se 1 (by rfl) ⟨7240058, by rfl⟩ : syracuseStep 9653411 = 14480117) B14480117
theorem B1756343 : Blo 1040609 1756343 := bstep (se 1 (by rfl) ⟨1317257, by rfl⟩ : syracuseStep 1756343 = 2634515) B2634515
theorem B3952061 : Blo 1040609 3952061 := bstep (se 3 (by rfl) ⟨741011, by rfl⟩ : syracuseStep 3952061 = 1482023) B1482023
theorem B1756667 : Blo 1040609 1756667 := bstep (se 1 (by rfl) ⟨1317500, by rfl⟩ : syracuseStep 1756667 = 2635001) B2635001
theorem B2346569 : Blo 1040609 2346569 := bstep (se 2 (by rfl) ⟨879963, by rfl⟩ : syracuseStep 2346569 = 1759927) B1759927
theorem B2641481 : Blo 1040609 2641481 := bstep (se 2 (by rfl) ⟨990555, by rfl⟩ : syracuseStep 2641481 = 1981111) B1981111
theorem B4018025 : Blo 1040609 4018025 := bstep (se 2 (by rfl) ⟨1506759, by rfl⟩ : syracuseStep 4018025 = 3013519) B3013519
theorem B4280207 : Blo 1040609 4280207 := bstep (se 1 (by rfl) ⟨3210155, by rfl⟩ : syracuseStep 4280207 = 6420311) B6420311
theorem B1757099 : Blo 1040609 1757099 := bstep (se 1 (by rfl) ⟨1317824, by rfl⟩ : syracuseStep 1757099 = 2635649) B2635649
theorem B11882699 : Blo 1040609 11882699 := bstep (se 1 (by rfl) ⟨8912024, by rfl⟩ : syracuseStep 11882699 = 17824049) B17824049
theorem B1560959 : Blo 1040609 1560959 := bstep (se 1 (by rfl) ⟨1170719, by rfl⟩ : syracuseStep 1560959 = 2341439) B2341439
theorem B1561031 : Blo 1040609 1561031 := bstep (se 1 (by rfl) ⟨1170773, by rfl⟩ : syracuseStep 1561031 = 2341547) B2341547
theorem B1757639 : Blo 1040609 1757639 := bstep (se 1 (by rfl) ⟨1318229, by rfl⟩ : syracuseStep 1757639 = 2636459) B2636459
theorem B3953231 : Blo 1040609 3953231 := bstep (se 1 (by rfl) ⟨2964923, by rfl⟩ : syracuseStep 3953231 = 5929847) B5929847
theorem B1561385 : Blo 1040609 1561385 := bstep (se 2 (by rfl) ⟨585519, by rfl⟩ : syracuseStep 1561385 = 1171039) B1171039
theorem B1561391 : Blo 1040609 1561391 := bstep (se 1 (by rfl) ⟨1171043, by rfl⟩ : syracuseStep 1561391 = 2342087) B2342087
theorem B1561511 : Blo 1040609 1561511 := bstep (se 1 (by rfl) ⟨1171133, by rfl⟩ : syracuseStep 1561511 = 2342267) B2342267
theorem B2970539 : Blo 1040609 2970539 := bstep (se 1 (by rfl) ⟨2227904, by rfl⟩ : syracuseStep 2970539 = 4455809) B4455809
theorem B1561595 : Blo 1040609 1561595 := bstep (se 1 (by rfl) ⟨1171196, by rfl⟩ : syracuseStep 1561595 = 2342393) B2342393
theorem B2348027 : Blo 1040609 2348027 := bstep (se 1 (by rfl) ⟨1761020, by rfl⟩ : syracuseStep 2348027 = 3522041) B3522041
theorem B2642939 : Blo 1040609 2642939 := bstep (se 1 (by rfl) ⟨1982204, by rfl⟩ : syracuseStep 2642939 = 3964409) B3964409
theorem B10703879 : Blo 1040609 10703879 := bstep (se 1 (by rfl) ⟨8027909, by rfl⟩ : syracuseStep 10703879 = 16055819) B16055819
theorem B1561655 : Blo 1040609 1561655 := bstep (se 1 (by rfl) ⟨1171241, by rfl⟩ : syracuseStep 1561655 = 2342483) B2342483
theorem B57889889 : Blo 1040609 57889889 := bstep (se 2 (by rfl) ⟨21708708, by rfl⟩ : syracuseStep 57889889 = 43417417) B43417417
theorem B1561775 : Blo 1040609 1561775 := bstep (se 1 (by rfl) ⟨1171331, by rfl⟩ : syracuseStep 1561775 = 2342663) B2342663
theorem B2348207 : Blo 1040609 2348207 := bstep (se 1 (by rfl) ⟨1761155, by rfl⟩ : syracuseStep 2348207 = 3522311) B3522311
theorem B1758415 : Blo 1040609 1758415 := bstep (se 1 (by rfl) ⟨1318811, by rfl⟩ : syracuseStep 1758415 = 2637623) B2637623
theorem B2348243 : Blo 1040609 2348243 := bstep (se 1 (by rfl) ⟨1761182, by rfl⟩ : syracuseStep 2348243 = 3522365) B3522365
theorem B5428511 : Blo 1040609 5428511 := bstep (se 1 (by rfl) ⟨4071383, by rfl⟩ : syracuseStep 5428511 = 8142767) B8142767
theorem B2348513 : Blo 1040609 2348513 := bstep (se 2 (by rfl) ⟨880692, by rfl⟩ : syracuseStep 2348513 = 1761385) B1761385
theorem B2643425 : Blo 1040609 2643425 := bstep (se 2 (by rfl) ⟨991284, by rfl⟩ : syracuseStep 2643425 = 1982569) B1982569
theorem B1562183 : Blo 1040609 1562183 := bstep (se 1 (by rfl) ⟨1171637, by rfl⟩ : syracuseStep 1562183 = 2343275) B2343275
theorem B1562279 : Blo 1040609 1562279 := bstep (se 1 (by rfl) ⟨1171709, by rfl⟩ : syracuseStep 1562279 = 2343419) B2343419
theorem B1562363 : Blo 1040609 1562363 := bstep (se 1 (by rfl) ⟨1171772, by rfl⟩ : syracuseStep 1562363 = 2343545) B2343545
theorem B1562399 : Blo 1040609 1562399 := bstep (se 1 (by rfl) ⟨1171799, by rfl⟩ : syracuseStep 1562399 = 2343599) B2343599
theorem B1562447 : Blo 1040609 1562447 := bstep (se 1 (by rfl) ⟨1171835, by rfl⟩ : syracuseStep 1562447 = 2343671) B2343671
theorem B6674359 : Blo 1040609 6674359 := bstep (se 1 (by rfl) ⟨5005769, by rfl⟩ : syracuseStep 6674359 = 10011539) B10011539
theorem B1562567 : Blo 1040609 1562567 := bstep (se 1 (by rfl) ⟨1171925, by rfl⟩ : syracuseStep 1562567 = 2343851) B2343851
theorem B1759225 : Blo 1040609 1759225 := bstep (se 2 (by rfl) ⟨659709, by rfl⟩ : syracuseStep 1759225 = 1319419) B1319419
theorem B2643961 : Blo 1040609 2643961 := bstep (se 2 (by rfl) ⟨991485, by rfl⟩ : syracuseStep 2643961 = 1982971) B1982971
theorem B3758177 : Blo 1040609 3758177 := bstep (se 2 (by rfl) ⟨1409316, by rfl⟩ : syracuseStep 3758177 = 2818633) B2818633
theorem B1759387 : Blo 1040609 1759387 := bstep (se 1 (by rfl) ⟨1319540, by rfl⟩ : syracuseStep 1759387 = 2639081) B2639081
theorem B2644123 : Blo 1040609 2644123 := bstep (se 1 (by rfl) ⟨1983092, by rfl⟩ : syracuseStep 2644123 = 3966185) B3966185
theorem B1759495 : Blo 1040609 1759495 := bstep (se 1 (by rfl) ⟨1319621, by rfl⟩ : syracuseStep 1759495 = 2639243) B2639243
theorem B1562921 : Blo 1040609 1562921 := bstep (se 2 (by rfl) ⟨586095, by rfl⟩ : syracuseStep 1562921 = 1172191) B1172191
theorem B1759529 : Blo 1040609 1759529 := bstep (se 2 (by rfl) ⟨659823, by rfl⟩ : syracuseStep 1759529 = 1319647) B1319647
theorem B1562927 : Blo 1040609 1562927 := bstep (se 1 (by rfl) ⟨1172195, by rfl⟩ : syracuseStep 1562927 = 2344391) B2344391
theorem B1563167 : Blo 1040609 1563167 := bstep (se 1 (by rfl) ⟨1172375, by rfl⟩ : syracuseStep 1563167 = 2344751) B2344751
theorem B6773345 : Blo 1040609 6773345 := bstep (se 2 (by rfl) ⟨2540004, by rfl⟩ : syracuseStep 6773345 = 5080009) B5080009
theorem B3169115 : Blo 1040609 3169115 := bstep (se 1 (by rfl) ⟨2376836, by rfl⟩ : syracuseStep 3169115 = 4753673) B4753673
theorem B1563551 : Blo 1040609 1563551 := bstep (se 1 (by rfl) ⟨1172663, by rfl⟩ : syracuseStep 1563551 = 2345327) B2345327
theorem B1563599 : Blo 1040609 1563599 := bstep (se 1 (by rfl) ⟨1172699, by rfl⟩ : syracuseStep 1563599 = 2345399) B2345399
theorem B3169271 : Blo 1040609 3169271 := bstep (se 1 (by rfl) ⟨2376953, by rfl⟩ : syracuseStep 3169271 = 4753907) B4753907
theorem B1563689 : Blo 1040609 1563689 := bstep (se 2 (by rfl) ⟨586383, by rfl⟩ : syracuseStep 1563689 = 1172767) B1172767
theorem B1563695 : Blo 1040609 1563695 := bstep (se 1 (by rfl) ⟨1172771, by rfl⟩ : syracuseStep 1563695 = 2345543) B2345543
theorem B1563719 : Blo 1040609 1563719 := bstep (se 1 (by rfl) ⟨1172789, by rfl⟩ : syracuseStep 1563719 = 2345579) B2345579
theorem B2350151 : Blo 1040609 2350151 := bstep (se 1 (by rfl) ⟨1762613, by rfl⟩ : syracuseStep 2350151 = 3525227) B3525227
theorem B1760521 : Blo 1040609 1760521 := bstep (se 2 (by rfl) ⟨660195, by rfl⟩ : syracuseStep 1760521 = 1320391) B1320391
theorem B1563983 : Blo 1040609 1563983 := bstep (se 1 (by rfl) ⟨1172987, by rfl⟩ : syracuseStep 1563983 = 2345975) B2345975
theorem B91250081 : Blo 1040609 91250081 := bstep (se 2 (by rfl) ⟨34218780, by rfl⟩ : syracuseStep 91250081 = 68437561) B68437561
theorem B1564073 : Blo 1040609 1564073 := bstep (se 2 (by rfl) ⟨586527, by rfl⟩ : syracuseStep 1564073 = 1173055) B1173055
theorem B1564223 : Blo 1040609 1564223 := bstep (se 1 (by rfl) ⟨1173167, by rfl⟩ : syracuseStep 1564223 = 2346335) B2346335
theorem B3759863 : Blo 1040609 3759863 := bstep (se 1 (by rfl) ⟨2819897, by rfl⟩ : syracuseStep 3759863 = 5639795) B5639795
theorem B1564487 : Blo 1040609 1564487 := bstep (se 1 (by rfl) ⟨1173365, by rfl⟩ : syracuseStep 1564487 = 2346731) B2346731
theorem B1761095 : Blo 1040609 1761095 := bstep (se 1 (by rfl) ⟨1320821, by rfl⟩ : syracuseStep 1761095 = 2641643) B2641643
theorem B10149725 : Blo 1040609 10149725 := bstep (se 3 (by rfl) ⟨1903073, by rfl⟩ : syracuseStep 10149725 = 3806147) B3806147
theorem B1564571 : Blo 1040609 1564571 := bstep (se 1 (by rfl) ⟨1173428, by rfl⟩ : syracuseStep 1564571 = 2346857) B2346857
theorem B1040615 : Blo 1040609 1040615 := bstep (se 1 (by rfl) ⟨780461, by rfl⟩ : syracuseStep 1040615 = 1560923) B1560923
theorem B1171687 : Blo 1040609 1171687 := bstep (se 1 (by rfl) ⟨878765, by rfl⟩ : syracuseStep 1171687 = 1757531) B1757531
theorem B1040767 : Blo 1040609 1040767 := bstep (se 1 (by rfl) ⟨780575, by rfl⟩ : syracuseStep 1040767 = 1561151) B1561151
theorem B1040847 : Blo 1040609 1040847 := bstep (se 1 (by rfl) ⟨780635, by rfl⟩ : syracuseStep 1040847 = 1561271) B1561271
theorem B1565135 : Blo 1040609 1565135 := bstep (se 1 (by rfl) ⟨1173851, by rfl⟩ : syracuseStep 1565135 = 2347703) B2347703
theorem B1761743 : Blo 1040609 1761743 := bstep (se 1 (by rfl) ⟨1321307, by rfl⟩ : syracuseStep 1761743 = 2642615) B2642615
theorem B1565177 : Blo 1040609 1565177 := bstep (se 2 (by rfl) ⟨586941, by rfl⟩ : syracuseStep 1565177 = 1173883) B1173883
theorem B1565279 : Blo 1040609 1565279 := bstep (se 1 (by rfl) ⟨1173959, by rfl⟩ : syracuseStep 1565279 = 2347919) B2347919
theorem B1040999 : Blo 1040609 1040999 := bstep (se 1 (by rfl) ⟨780749, by rfl⟩ : syracuseStep 1040999 = 1561499) B1561499
theorem B7922285 : Blo 1040609 7922285 := bstep (se 3 (by rfl) ⟨1485428, by rfl⟩ : syracuseStep 7922285 = 2970857) B2970857
theorem B7529273 : Blo 1040609 7529273 := bstep (se 2 (by rfl) ⟨2823477, by rfl⟩ : syracuseStep 7529273 = 5646955) B5646955
theorem B1041263 : Blo 1040609 1041263 := bstep (se 1 (by rfl) ⟨780947, by rfl⟩ : syracuseStep 1041263 = 1561895) B1561895
theorem B1172335 : Blo 1040609 1172335 := bstep (se 1 (by rfl) ⟨879251, by rfl⟩ : syracuseStep 1172335 = 1758503) B1758503
theorem B1041319 : Blo 1040609 1041319 := bstep (se 1 (by rfl) ⟨780989, by rfl⟩ : syracuseStep 1041319 = 1561979) B1561979
theorem B1041403 : Blo 1040609 1041403 := bstep (se 1 (by rfl) ⟨781052, by rfl⟩ : syracuseStep 1041403 = 1562105) B1562105
theorem B1041471 : Blo 1040609 1041471 := bstep (se 1 (by rfl) ⟨781103, by rfl⟩ : syracuseStep 1041471 = 1562207) B1562207
theorem B1565759 : Blo 1040609 1565759 := bstep (se 1 (by rfl) ⟨1174319, by rfl⟩ : syracuseStep 1565759 = 2348639) B2348639
theorem B1565801 : Blo 1040609 1565801 := bstep (se 2 (by rfl) ⟨587175, by rfl⟩ : syracuseStep 1565801 = 1174351) B1174351
theorem B1762411 : Blo 1040609 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B1041615 : Blo 1040609 1041615 := bstep (se 1 (by rfl) ⟨781211, by rfl⟩ : syracuseStep 1041615 = 1562423) B1562423
theorem B1565903 : Blo 1040609 1565903 := bstep (se 1 (by rfl) ⟨1174427, by rfl⟩ : syracuseStep 1565903 = 2348855) B2348855
theorem B81126755 : Blo 1040609 81126755 := bstep (se 1 (by rfl) ⟨60845066, by rfl⟩ : syracuseStep 81126755 = 121690133) B121690133
theorem B1041819 : Blo 1040609 1041819 := bstep (se 1 (by rfl) ⟨781364, by rfl⟩ : syracuseStep 1041819 = 1562729) B1562729
theorem B1566107 : Blo 1040609 1566107 := bstep (se 1 (by rfl) ⟨1174580, by rfl⟩ : syracuseStep 1566107 = 2349161) B2349161
theorem B1762715 : Blo 1040609 1762715 := bstep (se 1 (by rfl) ⟨1322036, by rfl⟩ : syracuseStep 1762715 = 2644073) B2644073
theorem B5006863 : Blo 1040609 5006863 := bstep (se 1 (by rfl) ⟨3755147, by rfl⟩ : syracuseStep 5006863 = 7510295) B7510295
theorem B1042031 : Blo 1040609 1042031 := bstep (se 1 (by rfl) ⟨781523, by rfl⟩ : syracuseStep 1042031 = 1563047) B1563047
theorem B3565171 : Blo 1040609 3565171 := bstep (se 1 (by rfl) ⟨2673878, by rfl⟩ : syracuseStep 3565171 = 5347757) B5347757
theorem B1566329 : Blo 1040609 1566329 := bstep (se 2 (by rfl) ⟨587373, by rfl⟩ : syracuseStep 1566329 = 1174747) B1174747
theorem B1042087 : Blo 1040609 1042087 := bstep (se 1 (by rfl) ⟨781565, by rfl⟩ : syracuseStep 1042087 = 1563131) B1563131
theorem B5269211 : Blo 1040609 5269211 := bstep (se 1 (by rfl) ⟨3951908, by rfl⟩ : syracuseStep 5269211 = 7903817) B7903817
theorem B1566431 : Blo 1040609 1566431 := bstep (se 1 (by rfl) ⟨1174823, by rfl⟩ : syracuseStep 1566431 = 2349647) B2349647
theorem B1042171 : Blo 1040609 1042171 := bstep (se 1 (by rfl) ⟨781628, by rfl⟩ : syracuseStep 1042171 = 1563257) B1563257
theorem B1042207 : Blo 1040609 1042207 := bstep (se 1 (by rfl) ⟨781655, by rfl⟩ : syracuseStep 1042207 = 1563311) B1563311
theorem B1042239 : Blo 1040609 1042239 := bstep (se 1 (by rfl) ⟨781679, by rfl⟩ : syracuseStep 1042239 = 1563359) B1563359
theorem B1566527 : Blo 1040609 1566527 := bstep (se 1 (by rfl) ⟨1174895, by rfl⟩ : syracuseStep 1566527 = 2349791) B2349791
theorem B1566695 : Blo 1040609 1566695 := bstep (se 1 (by rfl) ⟨1175021, by rfl⟩ : syracuseStep 1566695 = 2350043) B2350043
theorem B1042415 : Blo 1040609 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B1173487 : Blo 1040609 1173487 := bstep (se 1 (by rfl) ⟨880115, by rfl⟩ : syracuseStep 1173487 = 1760231) B1760231
theorem B1566713 : Blo 1040609 1566713 := bstep (se 2 (by rfl) ⟨587517, by rfl⟩ : syracuseStep 1566713 = 1175035) B1175035
theorem B1566815 : Blo 1040609 1566815 := bstep (se 1 (by rfl) ⟨1175111, by rfl⟩ : syracuseStep 1566815 = 2350223) B2350223
theorem B1042587 : Blo 1040609 1042587 := bstep (se 1 (by rfl) ⟨781940, by rfl⟩ : syracuseStep 1042587 = 1563881) B1563881
theorem B1566875 : Blo 1040609 1566875 := bstep (se 1 (by rfl) ⟨1175156, by rfl⟩ : syracuseStep 1566875 = 2350313) B2350313
theorem B1042623 : Blo 1040609 1042623 := bstep (se 1 (by rfl) ⟨781967, by rfl⟩ : syracuseStep 1042623 = 1563935) B1563935
theorem B1566911 : Blo 1040609 1566911 := bstep (se 1 (by rfl) ⟨1175183, by rfl⟩ : syracuseStep 1566911 = 2350367) B2350367
theorem B1042735 : Blo 1040609 1042735 := bstep (se 1 (by rfl) ⟨782051, by rfl⟩ : syracuseStep 1042735 = 1564103) B1564103
theorem B1042971 : Blo 1040609 1042971 := bstep (se 1 (by rfl) ⟨782228, by rfl⟩ : syracuseStep 1042971 = 1564457) B1564457
theorem B1042975 : Blo 1040609 1042975 := bstep (se 1 (by rfl) ⟨782231, by rfl⟩ : syracuseStep 1042975 = 1564463) B1564463
theorem B11856455 : Blo 1040609 11856455 := bstep (se 1 (by rfl) ⟨8892341, by rfl⟩ : syracuseStep 11856455 = 17784683) B17784683
theorem B1043291 : Blo 1040609 1043291 := bstep (se 1 (by rfl) ⟨782468, by rfl⟩ : syracuseStep 1043291 = 1564937) B1564937
theorem B1043359 : Blo 1040609 1043359 := bstep (se 1 (by rfl) ⟨782519, by rfl⟩ : syracuseStep 1043359 = 1565039) B1565039
theorem B3566567 : Blo 1040609 3566567 := bstep (se 1 (by rfl) ⟨2674925, by rfl⟩ : syracuseStep 3566567 = 5349851) B5349851
theorem B5270507 : Blo 1040609 5270507 := bstep (se 1 (by rfl) ⟨3952880, by rfl⟩ : syracuseStep 5270507 = 7905761) B7905761
theorem B7924715 : Blo 1040609 7924715 := bstep (se 1 (by rfl) ⟨5943536, by rfl⟩ : syracuseStep 7924715 = 11887073) B11887073
theorem B1043503 : Blo 1040609 1043503 := bstep (se 1 (by rfl) ⟨782627, by rfl⟩ : syracuseStep 1043503 = 1565255) B1565255
theorem B1043527 : Blo 1040609 1043527 := bstep (se 1 (by rfl) ⟨782645, by rfl⟩ : syracuseStep 1043527 = 1565291) B1565291
theorem B1043679 : Blo 1040609 1043679 := bstep (se 1 (by rfl) ⟨782759, by rfl⟩ : syracuseStep 1043679 = 1565519) B1565519
theorem B5074285 : Blo 1040609 5074285 := bstep (se 3 (by rfl) ⟨951428, by rfl⟩ : syracuseStep 5074285 = 1902857) B1902857
theorem B1043943 : Blo 1040609 1043943 := bstep (se 1 (by rfl) ⟨782957, by rfl⟩ : syracuseStep 1043943 = 1565915) B1565915
theorem B1044059 : Blo 1040609 1044059 := bstep (se 1 (by rfl) ⟨783044, by rfl⟩ : syracuseStep 1044059 = 1566089) B1566089
theorem B1044295 : Blo 1040609 1044295 := bstep (se 1 (by rfl) ⟨783221, by rfl⟩ : syracuseStep 1044295 = 1566443) B1566443
theorem B5271479 : Blo 1040609 5271479 := bstep (se 1 (by rfl) ⟨3953609, by rfl⟩ : syracuseStep 5271479 = 7907219) B7907219
theorem B7925687 : Blo 1040609 7925687 := bstep (se 1 (by rfl) ⟨5944265, by rfl⟩ : syracuseStep 7925687 = 11888531) B11888531
theorem B1044447 : Blo 1040609 1044447 := bstep (se 1 (by rfl) ⟨783335, by rfl⟩ : syracuseStep 1044447 = 1566671) B1566671
theorem B3961021 : Blo 1040609 3961021 := bstep (se 3 (by rfl) ⟨742691, by rfl⟩ : syracuseStep 3961021 = 1485383) B1485383
theorem B3764477 : Blo 1040609 3764477 := bstep (se 3 (by rfl) ⟨705839, by rfl⟩ : syracuseStep 3764477 = 1411679) B1411679
theorem B4453127 : Blo 1040609 4453127 := bstep (se 1 (by rfl) ⟨3339845, by rfl⟩ : syracuseStep 4453127 = 6679691) B6679691
theorem B12219641 : Blo 1040609 12219641 := bstep (se 2 (by rfl) ⟨4582365, by rfl⟩ : syracuseStep 12219641 = 9164731) B9164731
theorem B3339539 : Blo 1040609 3339539 := bstep (se 1 (by rfl) ⟨2504654, by rfl⟩ : syracuseStep 3339539 = 5009309) B5009309
theorem B752842079 : Blo 1040609 752842079 := bstep (se 1 (by rfl) ⟨564631559, by rfl⟩ : syracuseStep 752842079 = 1129263119) B1129263119
theorem B3962267 : Blo 1040609 3962267 := bstep (se 1 (by rfl) ⟨2971700, by rfl⟩ : syracuseStep 3962267 = 5943401) B5943401
theorem B6682277 : Blo 1040609 6682277 := bstep (se 4 (by rfl) ⟨626463, by rfl⟩ : syracuseStep 6682277 = 1252927) B1252927
theorem B3339959 : Blo 1040609 3339959 := bstep (se 1 (by rfl) ⟨2504969, by rfl⟩ : syracuseStep 3339959 = 5009939) B5009939
theorem B7141067 : Blo 1040609 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B4454099 : Blo 1040609 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B1669103 : Blo 1040609 1669103 := bstep (se 1 (by rfl) ⟨1251827, by rfl⟩ : syracuseStep 1669103 = 2503655) B2503655
theorem B8910931 : Blo 1040609 8910931 := bstep (se 1 (by rfl) ⟨6683198, by rfl⟩ : syracuseStep 8910931 = 13366397) B13366397
theorem B10680893 : Blo 1040609 10680893 := bstep (se 3 (by rfl) ⟨2002667, by rfl⟩ : syracuseStep 10680893 = 4005335) B4005335
theorem B5929595 : Blo 1040609 5929595 := bstep (se 1 (by rfl) ⟨4447196, by rfl⟩ : syracuseStep 5929595 = 8894393) B8894393
theorem B6683867 : Blo 1040609 6683867 := bstep (se 1 (by rfl) ⟨5012900, by rfl⟩ : syracuseStep 6683867 = 10025801) B10025801
theorem B5930279 : Blo 1040609 5930279 := bstep (se 1 (by rfl) ⟨4447709, by rfl⟩ : syracuseStep 5930279 = 8895419) B8895419
theorem B3341729 : Blo 1040609 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B5012999 : Blo 1040609 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B3964423 : Blo 1040609 3964423 := bstep (se 1 (by rfl) ⟨2973317, by rfl⟩ : syracuseStep 3964423 = 5946635) B5946635
theorem B11894363 : Blo 1040609 11894363 := bstep (se 1 (by rfl) ⟨8920772, by rfl⟩ : syracuseStep 11894363 = 17841545) B17841545
theorem B8454145 : Blo 1040609 8454145 := bstep (se 2 (by rfl) ⟨3170304, by rfl⟩ : syracuseStep 8454145 = 6340609) B6340609
theorem B2228519 : Blo 1040609 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B17793431 : Blo 1040609 17793431 := bstep (se 1 (by rfl) ⟨13345073, by rfl⟩ : syracuseStep 17793431 = 26690147) B26690147
theorem B4457227 : Blo 1040609 4457227 := bstep (se 1 (by rfl) ⟨3342920, by rfl⟩ : syracuseStep 4457227 = 6685841) B6685841
theorem B20022227 : Blo 1040609 20022227 := bstep (se 1 (by rfl) ⟨15016670, by rfl⟩ : syracuseStep 20022227 = 30033341) B30033341
theorem B4228307 : Blo 1040609 4228307 := bstep (se 1 (by rfl) ⟨3171230, by rfl⟩ : syracuseStep 4228307 = 6342461) B6342461
theorem B1672415 : Blo 1040609 1672415 := bstep (se 1 (by rfl) ⟨1254311, by rfl⟩ : syracuseStep 1672415 = 2508623) B2508623
theorem B8128457 : Blo 1040609 8128457 := bstep (se 2 (by rfl) ⟨3048171, by rfl⟩ : syracuseStep 8128457 = 6096343) B6096343
theorem B4753561 : Blo 1040609 4753561 := bstep (se 2 (by rfl) ⟨1782585, by rfl⟩ : syracuseStep 4753561 = 3565171) B3565171
theorem B2230433 : Blo 1040609 2230433 := bstep (se 2 (by rfl) ⟨836412, by rfl⟩ : syracuseStep 2230433 = 1672825) B1672825
theorem B60229979 : Blo 1040609 60229979 := bstep (se 1 (by rfl) ⟨45172484, by rfl⟩ : syracuseStep 60229979 = 90344969) B90344969
theorem B3345803 : Blo 1040609 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B8917289 : Blo 1040609 8917289 := bstep (se 2 (by rfl) ⟨3343983, by rfl⟩ : syracuseStep 8917289 = 6687967) B6687967
theorem B69571025 : Blo 1040609 69571025 := bstep (se 2 (by rfl) ⟨26089134, by rfl⟩ : syracuseStep 69571025 = 52178269) B52178269
theorem B5281361 : Blo 1040609 5281361 := bstep (se 2 (by rfl) ⟨1980510, by rfl⟩ : syracuseStep 5281361 = 3961021) B3961021
theorem B5281523 : Blo 1040609 5281523 := bstep (se 1 (by rfl) ⟨3961142, by rfl⟩ : syracuseStep 5281523 = 7922285) B7922285
theorem B5019515 : Blo 1040609 5019515 := bstep (se 1 (by rfl) ⟨3764636, by rfl⟩ : syracuseStep 5019515 = 7529273) B7529273
theorem B3512807 : Blo 1040609 3512807 := bstep (se 1 (by rfl) ⟨2634605, by rfl⟩ : syracuseStep 3512807 = 5269211) B5269211
theorem B1809209 : Blo 1040609 1809209 := bstep (se 2 (by rfl) ⟨678453, by rfl⟩ : syracuseStep 1809209 = 1356907) B1356907
theorem B1317703 : Blo 1040609 1317703 := bstep (se 1 (by rfl) ⟨988277, by rfl⟩ : syracuseStep 1317703 = 1976555) B1976555
theorem B7904303 : Blo 1040609 7904303 := bstep (se 1 (by rfl) ⟨5928227, by rfl⟩ : syracuseStep 7904303 = 11856455) B11856455
theorem B3513671 : Blo 1040609 3513671 := bstep (se 1 (by rfl) ⟨2635253, by rfl⟩ : syracuseStep 3513671 = 5270507) B5270507
theorem B5283143 : Blo 1040609 5283143 := bstep (se 1 (by rfl) ⟨3962357, by rfl⟩ : syracuseStep 5283143 = 7924715) B7924715
theorem B8920637 : Blo 1040609 8920637 := bstep (se 3 (by rfl) ⟨1672619, by rfl⟩ : syracuseStep 8920637 = 3345239) B3345239
theorem B1318619 : Blo 1040609 1318619 := bstep (se 1 (by rfl) ⟨988964, by rfl⟩ : syracuseStep 1318619 = 1977929) B1977929
theorem B3514319 : Blo 1040609 3514319 := bstep (se 1 (by rfl) ⟨2635739, by rfl⟩ : syracuseStep 3514319 = 5271479) B5271479
theorem B5283791 : Blo 1040609 5283791 := bstep (se 1 (by rfl) ⟨3962843, by rfl⟩ : syracuseStep 5283791 = 7925687) B7925687
theorem B8921663 : Blo 1040609 8921663 := bstep (se 1 (by rfl) ⟨6691247, by rfl⟩ : syracuseStep 8921663 = 13382495) B13382495
theorem B1319591 : Blo 1040609 1319591 := bstep (se 1 (by rfl) ⟨989693, by rfl⟩ : syracuseStep 1319591 = 1979387) B1979387
theorem B1319915 : Blo 1040609 1319915 := bstep (se 1 (by rfl) ⟨989936, by rfl⟩ : syracuseStep 1319915 = 1979873) B1979873
theorem B1254379 : Blo 1040609 1254379 := bstep (se 1 (by rfl) ⟨940784, by rfl⟩ : syracuseStep 1254379 = 1881569) B1881569
theorem B4760711 : Blo 1040609 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B7120595 : Blo 1040609 7120595 := bstep (se 1 (by rfl) ⟨5340446, by rfl⟩ : syracuseStep 7120595 = 10680893) B10680893
theorem B11282399 : Blo 1040609 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B5285897 : Blo 1040609 5285897 := bstep (se 2 (by rfl) ⟨1982211, by rfl⟩ : syracuseStep 5285897 = 3964423) B3964423
theorem B11413885 : Blo 1040609 11413885 := bstep (se 3 (by rfl) ⟨2140103, by rfl⟩ : syracuseStep 11413885 = 4280207) B4280207
theorem B2501761 : Blo 1040609 2501761 := bstep (se 2 (by rfl) ⟨938160, by rfl⟩ : syracuseStep 2501761 = 1876321) B1876321
theorem B1977527 : Blo 1040609 1977527 := bstep (se 1 (by rfl) ⟨1483145, by rfl⟩ : syracuseStep 1977527 = 2966291) B2966291
theorem B1486135 : Blo 1040609 1486135 := bstep (se 1 (by rfl) ⟨1114601, by rfl⟩ : syracuseStep 1486135 = 2229203) B2229203
theorem B8564105 : Blo 1040609 8564105 := bstep (se 2 (by rfl) ⟨3211539, by rfl⟩ : syracuseStep 8564105 = 6423079) B6423079
theorem B2502377 : Blo 1040609 2502377 := bstep (se 2 (by rfl) ⟨938391, by rfl⟩ : syracuseStep 2502377 = 1876783) B1876783
theorem B10006345 : Blo 1040609 10006345 := bstep (se 2 (by rfl) ⟨3752379, by rfl⟩ : syracuseStep 10006345 = 7504759) B7504759
theorem B13381523 : Blo 1040609 13381523 := bstep (se 1 (by rfl) ⟨10036142, by rfl⟩ : syracuseStep 13381523 = 20072285) B20072285
theorem B1486841 : Blo 1040609 1486841 := bstep (se 2 (by rfl) ⟨557565, by rfl⟩ : syracuseStep 1486841 = 1115131) B1115131
theorem B1978643 : Blo 1040609 1978643 := bstep (se 1 (by rfl) ⟨1483982, by rfl⟩ : syracuseStep 1978643 = 2967965) B2967965
theorem B18035087 : Blo 1040609 18035087 := bstep (se 1 (by rfl) ⟨13526315, by rfl⟩ : syracuseStep 18035087 = 27052631) B27052631
theorem B2503067 : Blo 1040609 2503067 := bstep (se 1 (by rfl) ⟨1877300, by rfl⟩ : syracuseStep 2503067 = 3754601) B3754601
theorem B6435607 : Blo 1040609 6435607 := bstep (se 1 (by rfl) ⟨4826705, by rfl⟩ : syracuseStep 6435607 = 9653411) B9653411
theorem B2634707 : Blo 1040609 2634707 := bstep (se 1 (by rfl) ⟨1976030, by rfl⟩ : syracuseStep 2634707 = 3952061) B3952061
theorem B8893435 : Blo 1040609 8893435 := bstep (se 1 (by rfl) ⟨6670076, by rfl⟩ : syracuseStep 8893435 = 13340153) B13340153
theorem B11285513 : Blo 1040609 11285513 := bstep (se 2 (by rfl) ⟨4232067, by rfl⟩ : syracuseStep 11285513 = 8464135) B8464135
theorem B17806553 : Blo 1040609 17806553 := bstep (se 2 (by rfl) ⟨6677457, by rfl⟩ : syracuseStep 17806553 = 13354915) B13354915
theorem B7910621 : Blo 1040609 7910621 := bstep (se 3 (by rfl) ⟨1483241, by rfl⟩ : syracuseStep 7910621 = 2966483) B2966483
theorem B2504009 : Blo 1040609 2504009 := bstep (se 2 (by rfl) ⟨939003, by rfl⟩ : syracuseStep 2504009 = 1878007) B1878007
theorem B2635487 : Blo 1040609 2635487 := bstep (se 1 (by rfl) ⟨1976615, by rfl⟩ : syracuseStep 2635487 = 3953231) B3953231
theorem B1980359 : Blo 1040609 1980359 := bstep (se 1 (by rfl) ⟨1485269, by rfl⟩ : syracuseStep 1980359 = 2970539) B2970539
theorem B3520583 : Blo 1040609 3520583 := bstep (se 1 (by rfl) ⟨2640437, by rfl⟩ : syracuseStep 3520583 = 5280875) B5280875
theorem B3619007 : Blo 1040609 3619007 := bstep (se 1 (by rfl) ⟨2714255, by rfl⟩ : syracuseStep 3619007 = 5428511) B5428511
theorem B2341601 : Blo 1040609 2341601 := bstep (se 2 (by rfl) ⟨878100, by rfl⟩ : syracuseStep 2341601 = 1756201) B1756201
theorem B2341799 : Blo 1040609 2341799 := bstep (se 1 (by rfl) ⟨1756349, by rfl⟩ : syracuseStep 2341799 = 3512699) B3512699
theorem B3521447 : Blo 1040609 3521447 := bstep (se 1 (by rfl) ⟨2641085, by rfl⟩ : syracuseStep 3521447 = 5282171) B5282171
theorem B2341979 : Blo 1040609 2341979 := bstep (se 1 (by rfl) ⟨1756484, by rfl⟩ : syracuseStep 2341979 = 3512969) B3512969
theorem B6765713 : Blo 1040609 6765713 := bstep (se 2 (by rfl) ⟨2537142, by rfl⟩ : syracuseStep 6765713 = 5074285) B5074285
theorem B2112743 : Blo 1040609 2112743 := bstep (se 1 (by rfl) ⟨1584557, by rfl⟩ : syracuseStep 2112743 = 3169115) B3169115
theorem B2112847 : Blo 1040609 2112847 := bstep (se 1 (by rfl) ⟨1584635, by rfl⟩ : syracuseStep 2112847 = 3169271) B3169271
theorem B7913051 : Blo 1040609 7913051 := bstep (se 1 (by rfl) ⟨5934788, by rfl⟩ : syracuseStep 7913051 = 11869577) B11869577
theorem B60833387 : Blo 1040609 60833387 := bstep (se 1 (by rfl) ⟨45625040, by rfl⟩ : syracuseStep 60833387 = 91250081) B91250081
theorem B6340319 : Blo 1040609 6340319 := bstep (se 1 (by rfl) ⟨4755239, by rfl⟩ : syracuseStep 6340319 = 9510479) B9510479
theorem B2342735 : Blo 1040609 2342735 := bstep (se 1 (by rfl) ⟨1757051, by rfl⟩ : syracuseStep 2342735 = 3514103) B3514103
theorem B2343455 : Blo 1040609 2343455 := bstep (se 1 (by rfl) ⟨1757591, by rfl⟩ : syracuseStep 2343455 = 3515183) B3515183
theorem B2343527 : Blo 1040609 2343527 := bstep (se 1 (by rfl) ⟨1757645, by rfl⟩ : syracuseStep 2343527 = 3515291) B3515291
theorem B3523175 : Blo 1040609 3523175 := bstep (se 1 (by rfl) ⟨2642381, by rfl⟩ : syracuseStep 3523175 = 5284763) B5284763
theorem B54084503 : Blo 1040609 54084503 := bstep (se 1 (by rfl) ⟨40563377, by rfl⟩ : syracuseStep 54084503 = 81126755) B81126755
theorem B2344283 : Blo 1040609 2344283 := bstep (se 1 (by rfl) ⟨1758212, by rfl⟩ : syracuseStep 2344283 = 3516425) B3516425
theorem B30492197 : Blo 1040609 30492197 := bstep (se 4 (by rfl) ⟨2858643, by rfl⟩ : syracuseStep 30492197 = 5717287) B5717287
theorem B2344553 : Blo 1040609 2344553 := bstep (se 2 (by rfl) ⟨879207, by rfl⟩ : syracuseStep 2344553 = 1758415) B1758415
theorem B8570539 : Blo 1040609 8570539 := bstep (se 1 (by rfl) ⟨6427904, by rfl⟩ : syracuseStep 8570539 = 12855809) B12855809
theorem B2377711 : Blo 1040609 2377711 := bstep (se 1 (by rfl) ⟨1783283, by rfl⟩ : syracuseStep 2377711 = 3566567) B3566567
theorem B2345147 : Blo 1040609 2345147 := bstep (se 1 (by rfl) ⟨1758860, by rfl⟩ : syracuseStep 2345147 = 3517721) B3517721
theorem B2345183 : Blo 1040609 2345183 := bstep (se 1 (by rfl) ⟨1758887, by rfl⟩ : syracuseStep 2345183 = 3517775) B3517775
theorem B8899145 : Blo 1040609 8899145 := bstep (se 2 (by rfl) ⟨3337179, by rfl⟩ : syracuseStep 8899145 = 6674359) B6674359
theorem B2345633 : Blo 1040609 2345633 := bstep (se 2 (by rfl) ⟨879612, by rfl⟩ : syracuseStep 2345633 = 1759225) B1759225
theorem B3525281 : Blo 1040609 3525281 := bstep (se 2 (by rfl) ⟨1321980, by rfl⟩ : syracuseStep 3525281 = 2643961) B2643961
theorem B20040371 : Blo 1040609 20040371 := bstep (se 1 (by rfl) ⟨15030278, by rfl⟩ : syracuseStep 20040371 = 30060557) B30060557
theorem B8440523 : Blo 1040609 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B11881241 : Blo 1040609 11881241 := bstep (se 2 (by rfl) ⟨4455465, by rfl⟩ : syracuseStep 11881241 = 8910931) B8910931
theorem B2509651 : Blo 1040609 2509651 := bstep (se 1 (by rfl) ⟨1882238, by rfl⟩ : syracuseStep 2509651 = 3764477) B3764477
theorem B2345849 : Blo 1040609 2345849 := bstep (se 2 (by rfl) ⟨879693, by rfl⟩ : syracuseStep 2345849 = 1759387) B1759387
theorem B3525497 : Blo 1040609 3525497 := bstep (se 2 (by rfl) ⟨1322061, by rfl⟩ : syracuseStep 3525497 = 2644123) B2644123
theorem B1756073 : Blo 1040609 1756073 := bstep (se 2 (by rfl) ⟨658527, by rfl⟩ : syracuseStep 1756073 = 1317055) B1317055
theorem B2345993 : Blo 1040609 2345993 := bstep (se 2 (by rfl) ⟨879747, by rfl⟩ : syracuseStep 2345993 = 1759495) B1759495
theorem B2346047 : Blo 1040609 2346047 := bstep (se 1 (by rfl) ⟨1759535, by rfl⟩ : syracuseStep 2346047 = 3519071) B3519071
theorem B2968751 : Blo 1040609 2968751 := bstep (se 1 (by rfl) ⟨2226563, by rfl⟩ : syracuseStep 2968751 = 4453127) B4453127
theorem B13356251 : Blo 1040609 13356251 := bstep (se 1 (by rfl) ⟨10017188, by rfl⟩ : syracuseStep 13356251 = 20034377) B20034377
theorem B8146427 : Blo 1040609 8146427 := bstep (se 1 (by rfl) ⟨6109820, by rfl⟩ : syracuseStep 8146427 = 12219641) B12219641
theorem B501894719 : Blo 1040609 501894719 := bstep (se 1 (by rfl) ⟨376421039, by rfl⟩ : syracuseStep 501894719 = 752842079) B752842079
theorem B1756775 : Blo 1040609 1756775 := bstep (se 1 (by rfl) ⟨1317581, by rfl⟩ : syracuseStep 1756775 = 2635163) B2635163
theorem B2641511 : Blo 1040609 2641511 := bstep (se 1 (by rfl) ⟨1981133, by rfl⟩ : syracuseStep 2641511 = 3962267) B3962267
theorem B2969399 : Blo 1040609 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B2346875 : Blo 1040609 2346875 := bstep (se 1 (by rfl) ⟨1760156, by rfl⟩ : syracuseStep 2346875 = 3520313) B3520313
theorem B2346983 : Blo 1040609 2346983 := bstep (se 1 (by rfl) ⟨1760237, by rfl⟩ : syracuseStep 2346983 = 3520475) B3520475
theorem B2347163 : Blo 1040609 2347163 := bstep (se 1 (by rfl) ⟨1760372, by rfl⟩ : syracuseStep 2347163 = 3520745) B3520745
theorem B2347361 : Blo 1040609 2347361 := bstep (se 2 (by rfl) ⟨880260, by rfl⟩ : syracuseStep 2347361 = 1760521) B1760521
theorem B3953033 : Blo 1040609 3953033 := bstep (se 2 (by rfl) ⟨1482387, by rfl⟩ : syracuseStep 3953033 = 2964775) B2964775
theorem B3953063 : Blo 1040609 3953063 := bstep (se 1 (by rfl) ⟨2964797, by rfl⟩ : syracuseStep 3953063 = 5929595) B5929595
theorem B2347451 : Blo 1040609 2347451 := bstep (se 1 (by rfl) ⟨1760588, by rfl⟩ : syracuseStep 2347451 = 3521177) B3521177
theorem B3953519 : Blo 1040609 3953519 := bstep (se 1 (by rfl) ⟨2965139, by rfl⟩ : syracuseStep 3953519 = 5930279) B5930279
theorem B1561583 : Blo 1040609 1561583 := bstep (se 1 (by rfl) ⟨1171187, by rfl⟩ : syracuseStep 1561583 = 2342375) B2342375
theorem B1561967 : Blo 1040609 1561967 := bstep (se 1 (by rfl) ⟨1171475, by rfl⟩ : syracuseStep 1561967 = 2342951) B2342951
theorem B2413999 : Blo 1040609 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B1562087 : Blo 1040609 1562087 := bstep (se 1 (by rfl) ⟨1171565, by rfl⟩ : syracuseStep 1562087 = 2343131) B2343131
theorem B1562249 : Blo 1040609 1562249 := bstep (se 2 (by rfl) ⟨585843, by rfl⟩ : syracuseStep 1562249 = 1171687) B1171687
theorem B1562267 : Blo 1040609 1562267 := bstep (se 1 (by rfl) ⟨1171700, by rfl⟩ : syracuseStep 1562267 = 2343401) B2343401
theorem B2348711 : Blo 1040609 2348711 := bstep (se 1 (by rfl) ⟨1761533, by rfl⟩ : syracuseStep 2348711 = 3523067) B3523067
theorem B1562459 : Blo 1040609 1562459 := bstep (se 1 (by rfl) ⟨1171844, by rfl⟩ : syracuseStep 1562459 = 2343689) B2343689
theorem B2348891 : Blo 1040609 2348891 := bstep (se 1 (by rfl) ⟨1761668, by rfl⟩ : syracuseStep 2348891 = 3523337) B3523337
theorem B1562843 : Blo 1040609 1562843 := bstep (se 1 (by rfl) ⟨1172132, by rfl⟩ : syracuseStep 1562843 = 2344265) B2344265
theorem B4511963 : Blo 1040609 4511963 := bstep (se 1 (by rfl) ⟨3383972, by rfl⟩ : syracuseStep 4511963 = 6767945) B6767945
theorem B2349395 : Blo 1040609 2349395 := bstep (se 1 (by rfl) ⟨1762046, by rfl⟩ : syracuseStep 2349395 = 3524093) B3524093
theorem B2972065 : Blo 1040609 2972065 := bstep (se 2 (by rfl) ⟨1114524, by rfl⟩ : syracuseStep 2972065 = 2229049) B2229049
theorem B1563113 : Blo 1040609 1563113 := bstep (se 2 (by rfl) ⟨586167, by rfl⟩ : syracuseStep 1563113 = 1172335) B1172335
theorem B2349881 : Blo 1040609 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B1563503 : Blo 1040609 1563503 := bstep (se 1 (by rfl) ⟨1172627, by rfl⟩ : syracuseStep 1563503 = 2345255) B2345255
theorem B2349935 : Blo 1040609 2349935 := bstep (se 1 (by rfl) ⟨1762451, by rfl⟩ : syracuseStep 2349935 = 3524903) B3524903
theorem B1563515 : Blo 1040609 1563515 := bstep (se 1 (by rfl) ⟨1172636, by rfl⟩ : syracuseStep 1563515 = 2345273) B2345273
theorem B1760123 : Blo 1040609 1760123 := bstep (se 1 (by rfl) ⟨1320092, by rfl⟩ : syracuseStep 1760123 = 2640185) B2640185
theorem B5004251 : Blo 1040609 5004251 := bstep (se 1 (by rfl) ⟨3753188, by rfl⟩ : syracuseStep 5004251 = 7506377) B7506377
theorem B3955675 : Blo 1040609 3955675 := bstep (se 1 (by rfl) ⟨2966756, by rfl⟩ : syracuseStep 3955675 = 5933513) B5933513
theorem B8445161 : Blo 1040609 8445161 := bstep (se 2 (by rfl) ⟨3166935, by rfl⟩ : syracuseStep 8445161 = 6333871) B6333871
theorem B1170895 : Blo 1040609 1170895 := bstep (se 1 (by rfl) ⟨878171, by rfl⟩ : syracuseStep 1170895 = 1756343) B1756343
theorem B1171111 : Blo 1040609 1171111 := bstep (se 1 (by rfl) ⟨878333, by rfl⟩ : syracuseStep 1171111 = 1756667) B1756667
theorem B1564379 : Blo 1040609 1564379 := bstep (se 1 (by rfl) ⟨1173284, by rfl⟩ : syracuseStep 1564379 = 2346569) B2346569
theorem B1760987 : Blo 1040609 1760987 := bstep (se 1 (by rfl) ⟨1320740, by rfl⟩ : syracuseStep 1760987 = 2641481) B2641481
theorem B2678683 : Blo 1040609 2678683 := bstep (se 1 (by rfl) ⟨2009012, by rfl⟩ : syracuseStep 2678683 = 4018025) B4018025
theorem B1171399 : Blo 1040609 1171399 := bstep (se 1 (by rfl) ⟨878549, by rfl⟩ : syracuseStep 1171399 = 1757099) B1757099
theorem B1564649 : Blo 1040609 1564649 := bstep (se 2 (by rfl) ⟨586743, by rfl⟩ : syracuseStep 1564649 = 1173487) B1173487
theorem B1761257 : Blo 1040609 1761257 := bstep (se 2 (by rfl) ⟨660471, by rfl⟩ : syracuseStep 1761257 = 1320943) B1320943
theorem B7921799 : Blo 1040609 7921799 := bstep (se 1 (by rfl) ⟨5941349, by rfl⟩ : syracuseStep 7921799 = 11882699) B11882699
theorem B1040639 : Blo 1040609 1040639 := bstep (se 1 (by rfl) ⟨780479, by rfl⟩ : syracuseStep 1040639 = 1560959) B1560959
theorem B1040687 : Blo 1040609 1040687 := bstep (se 1 (by rfl) ⟨780515, by rfl⟩ : syracuseStep 1040687 = 1561031) B1561031
theorem B1171759 : Blo 1040609 1171759 := bstep (se 1 (by rfl) ⟨878819, by rfl⟩ : syracuseStep 1171759 = 1757639) B1757639
theorem B1040923 : Blo 1040609 1040923 := bstep (se 1 (by rfl) ⟨780692, by rfl⟩ : syracuseStep 1040923 = 1561385) B1561385
theorem B1040927 : Blo 1040609 1040927 := bstep (se 1 (by rfl) ⟨780695, by rfl⟩ : syracuseStep 1040927 = 1561391) B1561391
theorem B1041007 : Blo 1040609 1041007 := bstep (se 1 (by rfl) ⟨780755, by rfl⟩ : syracuseStep 1041007 = 1561511) B1561511
theorem B1041063 : Blo 1040609 1041063 := bstep (se 1 (by rfl) ⟨780797, by rfl⟩ : syracuseStep 1041063 = 1561595) B1561595
theorem B1565351 : Blo 1040609 1565351 := bstep (se 1 (by rfl) ⟨1174013, by rfl⟩ : syracuseStep 1565351 = 2348027) B2348027
theorem B1761959 : Blo 1040609 1761959 := bstep (se 1 (by rfl) ⟨1321469, by rfl⟩ : syracuseStep 1761959 = 2642939) B2642939
theorem B7135919 : Blo 1040609 7135919 := bstep (se 1 (by rfl) ⟨5351939, by rfl⟩ : syracuseStep 7135919 = 10703879) B10703879
theorem B1041103 : Blo 1040609 1041103 := bstep (se 1 (by rfl) ⟨780827, by rfl⟩ : syracuseStep 1041103 = 1561655) B1561655
theorem B38593259 : Blo 1040609 38593259 := bstep (se 1 (by rfl) ⟨28944944, by rfl⟩ : syracuseStep 38593259 = 57889889) B57889889
theorem B1041183 : Blo 1040609 1041183 := bstep (se 1 (by rfl) ⟨780887, by rfl⟩ : syracuseStep 1041183 = 1561775) B1561775
theorem B1565471 : Blo 1040609 1565471 := bstep (se 1 (by rfl) ⟨1174103, by rfl⟩ : syracuseStep 1565471 = 2348207) B2348207
theorem B1565495 : Blo 1040609 1565495 := bstep (se 1 (by rfl) ⟨1174121, by rfl⟩ : syracuseStep 1565495 = 2348243) B2348243
theorem B1565675 : Blo 1040609 1565675 := bstep (se 1 (by rfl) ⟨1174256, by rfl⟩ : syracuseStep 1565675 = 2348513) B2348513
theorem B1762283 : Blo 1040609 1762283 := bstep (se 1 (by rfl) ⟨1321712, by rfl⟩ : syracuseStep 1762283 = 2643425) B2643425
theorem B1041455 : Blo 1040609 1041455 := bstep (se 1 (by rfl) ⟨781091, by rfl⟩ : syracuseStep 1041455 = 1562183) B1562183
theorem B1041519 : Blo 1040609 1041519 := bstep (se 1 (by rfl) ⟨781139, by rfl⟩ : syracuseStep 1041519 = 1562279) B1562279
theorem B1041575 : Blo 1040609 1041575 := bstep (se 1 (by rfl) ⟨781181, by rfl⟩ : syracuseStep 1041575 = 1562363) B1562363
theorem B1041599 : Blo 1040609 1041599 := bstep (se 1 (by rfl) ⟨781199, by rfl⟩ : syracuseStep 1041599 = 1562399) B1562399
theorem B1041631 : Blo 1040609 1041631 := bstep (se 1 (by rfl) ⟨781223, by rfl⟩ : syracuseStep 1041631 = 1562447) B1562447
theorem B1041711 : Blo 1040609 1041711 := bstep (se 1 (by rfl) ⟨781283, by rfl⟩ : syracuseStep 1041711 = 1562567) B1562567
theorem B1041947 : Blo 1040609 1041947 := bstep (se 1 (by rfl) ⟨781460, by rfl⟩ : syracuseStep 1041947 = 1562921) B1562921
theorem B1173019 : Blo 1040609 1173019 := bstep (se 1 (by rfl) ⟨879764, by rfl⟩ : syracuseStep 1173019 = 1759529) B1759529
theorem B1041951 : Blo 1040609 1041951 := bstep (se 1 (by rfl) ⟨781463, by rfl⟩ : syracuseStep 1041951 = 1562927) B1562927
theorem B1042111 : Blo 1040609 1042111 := bstep (se 1 (by rfl) ⟨781583, by rfl⟩ : syracuseStep 1042111 = 1563167) B1563167
theorem B4515563 : Blo 1040609 4515563 := bstep (se 1 (by rfl) ⟨3386672, by rfl⟩ : syracuseStep 4515563 = 6773345) B6773345
theorem B8906557 : Blo 1040609 8906557 := bstep (se 3 (by rfl) ⟨1669979, by rfl⟩ : syracuseStep 8906557 = 3339959) B3339959
theorem B1042367 : Blo 1040609 1042367 := bstep (se 1 (by rfl) ⟨781775, by rfl⟩ : syracuseStep 1042367 = 1563551) B1563551
theorem B1042399 : Blo 1040609 1042399 := bstep (se 1 (by rfl) ⟨781799, by rfl⟩ : syracuseStep 1042399 = 1563599) B1563599
theorem B1042459 : Blo 1040609 1042459 := bstep (se 1 (by rfl) ⟨781844, by rfl⟩ : syracuseStep 1042459 = 1563689) B1563689
theorem B1042463 : Blo 1040609 1042463 := bstep (se 1 (by rfl) ⟨781847, by rfl⟩ : syracuseStep 1042463 = 1563695) B1563695
theorem B1042479 : Blo 1040609 1042479 := bstep (se 1 (by rfl) ⟨781859, by rfl⟩ : syracuseStep 1042479 = 1563719) B1563719
theorem B1566767 : Blo 1040609 1566767 := bstep (se 1 (by rfl) ⟨1175075, by rfl⟩ : syracuseStep 1566767 = 2350151) B2350151
theorem B1042655 : Blo 1040609 1042655 := bstep (se 1 (by rfl) ⟨781991, by rfl⟩ : syracuseStep 1042655 = 1563983) B1563983
theorem B1042715 : Blo 1040609 1042715 := bstep (se 1 (by rfl) ⟨782036, by rfl⟩ : syracuseStep 1042715 = 1564073) B1564073
theorem B1042815 : Blo 1040609 1042815 := bstep (se 1 (by rfl) ⟨782111, by rfl⟩ : syracuseStep 1042815 = 1564223) B1564223
theorem B3762703 : Blo 1040609 3762703 := bstep (se 1 (by rfl) ⟨2822027, by rfl⟩ : syracuseStep 3762703 = 5644055) B5644055
theorem B1042991 : Blo 1040609 1042991 := bstep (se 1 (by rfl) ⟨782243, by rfl⟩ : syracuseStep 1042991 = 1564487) B1564487
theorem B1174063 : Blo 1040609 1174063 := bstep (se 1 (by rfl) ⟨880547, by rfl⟩ : syracuseStep 1174063 = 1761095) B1761095
theorem B1043047 : Blo 1040609 1043047 := bstep (se 1 (by rfl) ⟨782285, by rfl⟩ : syracuseStep 1043047 = 1564571) B1564571
theorem B10021805 : Blo 1040609 10021805 := bstep (se 3 (by rfl) ⟨1879088, by rfl⟩ : syracuseStep 10021805 = 3758177) B3758177
theorem B1043423 : Blo 1040609 1043423 := bstep (se 1 (by rfl) ⟨782567, by rfl⟩ : syracuseStep 1043423 = 1565135) B1565135
theorem B1174495 : Blo 1040609 1174495 := bstep (se 1 (by rfl) ⟨880871, by rfl⟩ : syracuseStep 1174495 = 1761743) B1761743
theorem B1043451 : Blo 1040609 1043451 := bstep (se 1 (by rfl) ⟨782588, by rfl⟩ : syracuseStep 1043451 = 1565177) B1565177
theorem B1043519 : Blo 1040609 1043519 := bstep (se 1 (by rfl) ⟨782639, by rfl⟩ : syracuseStep 1043519 = 1565279) B1565279
theorem B1043839 : Blo 1040609 1043839 := bstep (se 1 (by rfl) ⟨782879, by rfl⟩ : syracuseStep 1043839 = 1565759) B1565759
theorem B1043867 : Blo 1040609 1043867 := bstep (se 1 (by rfl) ⟨782900, by rfl⟩ : syracuseStep 1043867 = 1565801) B1565801
theorem B1043935 : Blo 1040609 1043935 := bstep (se 1 (by rfl) ⟨782951, by rfl⟩ : syracuseStep 1043935 = 1565903) B1565903
theorem B1044071 : Blo 1040609 1044071 := bstep (se 1 (by rfl) ⟨783053, by rfl⟩ : syracuseStep 1044071 = 1566107) B1566107
theorem B1175143 : Blo 1040609 1175143 := bstep (se 1 (by rfl) ⟨881357, by rfl⟩ : syracuseStep 1175143 = 1762715) B1762715
theorem B1044219 : Blo 1040609 1044219 := bstep (se 1 (by rfl) ⟨783164, by rfl⟩ : syracuseStep 1044219 = 1566329) B1566329
theorem B72183599 : Blo 1040609 72183599 := bstep (se 1 (by rfl) ⟨54137699, by rfl⟩ : syracuseStep 72183599 = 108275399) B108275399
theorem B1044287 : Blo 1040609 1044287 := bstep (se 1 (by rfl) ⟨783215, by rfl⟩ : syracuseStep 1044287 = 1566431) B1566431
theorem B1044351 : Blo 1040609 1044351 := bstep (se 1 (by rfl) ⟨783263, by rfl⟩ : syracuseStep 1044351 = 1566527) B1566527
theorem B1044463 : Blo 1040609 1044463 := bstep (se 1 (by rfl) ⟨783347, by rfl⟩ : syracuseStep 1044463 = 1566695) B1566695
theorem B1044475 : Blo 1040609 1044475 := bstep (se 1 (by rfl) ⟨783356, by rfl⟩ : syracuseStep 1044475 = 1566713) B1566713
theorem B5926931 : Blo 1040609 5926931 := bstep (se 1 (by rfl) ⟨4445198, by rfl⟩ : syracuseStep 5926931 = 8890397) B8890397
theorem B1044543 : Blo 1040609 1044543 := bstep (se 1 (by rfl) ⟨783407, by rfl⟩ : syracuseStep 1044543 = 1566815) B1566815
theorem B1044583 : Blo 1040609 1044583 := bstep (se 1 (by rfl) ⟨783437, by rfl⟩ : syracuseStep 1044583 = 1566875) B1566875
theorem B1044607 : Blo 1040609 1044607 := bstep (se 1 (by rfl) ⟨783455, by rfl⟩ : syracuseStep 1044607 = 1566911) B1566911
theorem B3961295 : Blo 1040609 3961295 := bstep (se 1 (by rfl) ⟨2970971, by rfl⟩ : syracuseStep 3961295 = 5941943) B5941943
theorem B11891447 : Blo 1040609 11891447 := bstep (se 1 (by rfl) ⟨8918585, by rfl⟩ : syracuseStep 11891447 = 17837171) B17837171
theorem B26703269 : Blo 1040609 26703269 := bstep (se 4 (by rfl) ⟨2503431, by rfl⟩ : syracuseStep 26703269 = 5006863) B5006863
theorem B5011055 : Blo 1040609 5011055 := bstep (se 1 (by rfl) ⟨3758291, by rfl⟩ : syracuseStep 5011055 = 7516583) B7516583
theorem B3962479 : Blo 1040609 3962479 := bstep (se 1 (by rfl) ⟨2971859, by rfl⟩ : syracuseStep 3962479 = 5943719) B5943719
theorem B5273423 : Blo 1040609 5273423 := bstep (se 1 (by rfl) ⟨3955067, by rfl⟩ : syracuseStep 5273423 = 7910135) B7910135
theorem B5011307 : Blo 1040609 5011307 := bstep (se 1 (by rfl) ⟨3758480, by rfl⟩ : syracuseStep 5011307 = 7516961) B7516961
theorem B2226359 : Blo 1040609 2226359 := bstep (se 1 (by rfl) ⟨1669769, by rfl⟩ : syracuseStep 2226359 = 3339539) B3339539
theorem B4454851 : Blo 1040609 4454851 := bstep (se 1 (by rfl) ⟨3341138, by rfl⟩ : syracuseStep 4454851 = 6682277) B6682277
theorem B13335029 : Blo 1040609 13335029 := bstep (se 5 (by rfl) ⟨625079, by rfl⟩ : syracuseStep 13335029 = 1250159) B1250159
theorem B1112735 : Blo 1040609 1112735 := bstep (se 1 (by rfl) ⟨834551, by rfl⟩ : syracuseStep 1112735 = 1669103) B1669103
theorem B126974827 : Blo 1040609 126974827 := bstep (se 1 (by rfl) ⟨95231120, by rfl⟩ : syracuseStep 126974827 = 190462241) B190462241
theorem B7929089 : Blo 1040609 7929089 := bstep (se 2 (by rfl) ⟨2973408, by rfl⟩ : syracuseStep 7929089 = 5946817) B5946817
theorem B2817305 : Blo 1040609 2817305 := bstep (se 2 (by rfl) ⟨1056489, by rfl⟩ : syracuseStep 2817305 = 2112979) B2112979
theorem B10026301 : Blo 1040609 10026301 := bstep (se 3 (by rfl) ⟨1879931, by rfl⟩ : syracuseStep 10026301 = 3759863) B3759863
theorem B4455911 : Blo 1040609 4455911 := bstep (se 1 (by rfl) ⟨3341933, by rfl⟩ : syracuseStep 4455911 = 6683867) B6683867
theorem B27065933 : Blo 1040609 27065933 := bstep (se 3 (by rfl) ⟨5074862, by rfl⟩ : syracuseStep 27065933 = 10149725) B10149725
theorem B2227819 : Blo 1040609 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B3341999 : Blo 1040609 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B7929575 : Blo 1040609 7929575 := bstep (se 1 (by rfl) ⟨5947181, by rfl⟩ : syracuseStep 7929575 = 11894363) B11894363
theorem B11272193 : Blo 1040609 11272193 := bstep (se 2 (by rfl) ⟨4227072, by rfl⟩ : syracuseStep 11272193 = 8454145) B8454145
theorem B11862287 : Blo 1040609 11862287 := bstep (se 1 (by rfl) ⟨8896715, by rfl⟩ : syracuseStep 11862287 = 17793431) B17793431
theorem B2818871 : Blo 1040609 2818871 := bstep (se 1 (by rfl) ⟨2114153, by rfl⟩ : syracuseStep 2818871 = 4228307) B4228307
theorem B1114943 : Blo 1040609 1114943 := bstep (se 1 (by rfl) ⟨836207, by rfl⟩ : syracuseStep 1114943 = 1672415) B1672415
theorem B1672505 : Blo 1040609 1672505 := bstep (se 2 (by rfl) ⟨627189, by rfl⟩ : syracuseStep 1672505 = 1254379) B1254379
theorem B5932763 : Blo 1040609 5932763 := bstep (se 1 (by rfl) ⟨4449572, by rfl⟩ : syracuseStep 5932763 = 8899145) B8899145
theorem B2230535 : Blo 1040609 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B334596479 : Blo 1040609 334596479 := bstep (se 1 (by rfl) ⟨250947359, by rfl⟩ : syracuseStep 334596479 = 501894719) B501894719
theorem B5016937 : Blo 1040609 5016937 := bstep (se 2 (by rfl) ⟨1881351, by rfl⟩ : syracuseStep 5016937 = 3762703) B3762703
theorem B3346201 : Blo 1040609 3346201 := bstep (se 2 (by rfl) ⟨1254825, by rfl⟩ : syracuseStep 3346201 = 2509651) B2509651
theorem B3346343 : Blo 1040609 3346343 := bstep (se 1 (by rfl) ⟨2509757, by rfl⟩ : syracuseStep 3346343 = 5019515) B5019515
theorem B13341793 : Blo 1040609 13341793 := bstep (se 2 (by rfl) ⟨5003172, by rfl⟩ : syracuseStep 13341793 = 10006345) B10006345
theorem B5281199 : Blo 1040609 5281199 := bstep (se 1 (by rfl) ⟨3960899, by rfl⟩ : syracuseStep 5281199 = 7921799) B7921799
theorem B25728839 : Blo 1040609 25728839 := bstep (se 1 (by rfl) ⟨19296629, by rfl⟩ : syracuseStep 25728839 = 38593259) B38593259
theorem B3218665 : Blo 1040609 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B1318351 : Blo 1040609 1318351 := bstep (se 1 (by rfl) ⟨988763, by rfl⟩ : syracuseStep 1318351 = 1977527) B1977527
theorem B5283305 : Blo 1040609 5283305 := bstep (se 2 (by rfl) ⟨1981239, by rfl⟩ : syracuseStep 5283305 = 3962479) B3962479
theorem B5709403 : Blo 1040609 5709403 := bstep (se 1 (by rfl) ⟨4282052, by rfl⟩ : syracuseStep 5709403 = 8564105) B8564105
theorem B8921015 : Blo 1040609 8921015 := bstep (se 1 (by rfl) ⟨6690761, by rfl⟩ : syracuseStep 8921015 = 13381523) B13381523
theorem B1319095 : Blo 1040609 1319095 := bstep (se 1 (by rfl) ⟨989321, by rfl⟩ : syracuseStep 1319095 = 1978643) B1978643
theorem B5939801 : Blo 1040609 5939801 := bstep (se 2 (by rfl) ⟨2227425, by rfl⟩ : syracuseStep 5939801 = 4454851) B4454851
theorem B22520429 : Blo 1040609 22520429 := bstep (se 3 (by rfl) ⟨4222580, by rfl⟩ : syracuseStep 22520429 = 8445161) B8445161
theorem B11871035 : Blo 1040609 11871035 := bstep (se 1 (by rfl) ⟨8903276, by rfl⟩ : syracuseStep 11871035 = 17806553) B17806553
theorem B17802179 : Blo 1040609 17802179 := bstep (se 1 (by rfl) ⟨13351634, by rfl⟩ : syracuseStep 17802179 = 26703269) B26703269
theorem B3515615 : Blo 1040609 3515615 := bstep (se 1 (by rfl) ⟨2636711, by rfl⟩ : syracuseStep 3515615 = 5273423) B5273423
theorem B1320239 : Blo 1040609 1320239 := bstep (se 1 (by rfl) ⟨990179, by rfl⟩ : syracuseStep 1320239 = 1980359) B1980359
theorem B1484239 : Blo 1040609 1484239 := bstep (se 1 (by rfl) ⟨1113179, by rfl⟩ : syracuseStep 1484239 = 2226359) B2226359
theorem B8890019 : Blo 1040609 8890019 := bstep (se 1 (by rfl) ⟨6667514, by rfl⟩ : syracuseStep 8890019 = 13335029) B13335029
theorem B3516317 : Blo 1040609 3516317 := bstep (se 3 (by rfl) ⟨659309, by rfl⟩ : syracuseStep 3516317 = 1318619) B1318619
theorem B5286059 : Blo 1040609 5286059 := bstep (se 1 (by rfl) ⟨3964544, by rfl⟩ : syracuseStep 5286059 = 7929089) B7929089
theorem B1878203 : Blo 1040609 1878203 := bstep (se 1 (by rfl) ⟨1408652, by rfl⟩ : syracuseStep 1878203 = 2817305) B2817305
theorem B5286383 : Blo 1040609 5286383 := bstep (se 1 (by rfl) ⟨3964787, by rfl⟩ : syracuseStep 5286383 = 7929575) B7929575
theorem B36056335 : Blo 1040609 36056335 := bstep (se 1 (by rfl) ⟨27042251, by rfl⟩ : syracuseStep 36056335 = 54084503) B54084503
theorem B13348151 : Blo 1040609 13348151 := bstep (se 1 (by rfl) ⟨10011113, by rfl⟩ : syracuseStep 13348151 = 20022227) B20022227
theorem B5942717 : Blo 1040609 5942717 := bstep (se 3 (by rfl) ⟨1114259, by rfl⟩ : syracuseStep 5942717 = 2228519) B2228519
theorem B5942969 : Blo 1040609 5942969 := bstep (se 2 (by rfl) ⟨2228613, by rfl⟩ : syracuseStep 5942969 = 4457227) B4457227
theorem B20328131 : Blo 1040609 20328131 := bstep (se 1 (by rfl) ⟨15246098, by rfl⟩ : syracuseStep 20328131 = 30492197) B30492197
theorem B5418971 : Blo 1040609 5418971 := bstep (se 1 (by rfl) ⟨4064228, by rfl⟩ : syracuseStep 5418971 = 8128457) B8128457
theorem B1486955 : Blo 1040609 1486955 := bstep (se 1 (by rfl) ⟨1115216, by rfl⟩ : syracuseStep 1486955 = 2230433) B2230433
theorem B40153319 : Blo 1040609 40153319 := bstep (se 1 (by rfl) ⟨30114989, by rfl⟩ : syracuseStep 40153319 = 60229979) B60229979
theorem B3518909 : Blo 1040609 3518909 := bstep (se 3 (by rfl) ⟨659795, by rfl⟩ : syracuseStep 3518909 = 1319591) B1319591
theorem B1979167 : Blo 1040609 1979167 := bstep (se 1 (by rfl) ⟨1484375, by rfl⟩ : syracuseStep 1979167 = 2968751) B2968751
theorem B11875409 : Blo 1040609 11875409 := bstep (se 2 (by rfl) ⟨4453278, by rfl⟩ : syracuseStep 11875409 = 8906557) B8906557
theorem B3519773 : Blo 1040609 3519773 := bstep (se 3 (by rfl) ⟨659957, by rfl⟩ : syracuseStep 3519773 = 1319915) B1319915
theorem B5944859 : Blo 1040609 5944859 := bstep (se 1 (by rfl) ⟨4458644, by rfl⟩ : syracuseStep 5944859 = 8917289) B8917289
theorem B6338081 : Blo 1040609 6338081 := bstep (se 2 (by rfl) ⟨2376780, by rfl⟩ : syracuseStep 6338081 = 4753561) B4753561
theorem B2635355 : Blo 1040609 2635355 := bstep (se 1 (by rfl) ⟨1976516, by rfl⟩ : syracuseStep 2635355 = 3953033) B3953033
theorem B2635375 : Blo 1040609 2635375 := bstep (se 1 (by rfl) ⟨1976531, by rfl⟩ : syracuseStep 2635375 = 3953063) B3953063
theorem B46380683 : Blo 1040609 46380683 := bstep (se 1 (by rfl) ⟨34785512, by rfl⟩ : syracuseStep 46380683 = 69571025) B69571025
theorem B15218513 : Blo 1040609 15218513 := bstep (se 2 (by rfl) ⟨5706942, by rfl⟩ : syracuseStep 15218513 = 11413885) B11413885
theorem B2635679 : Blo 1040609 2635679 := bstep (se 1 (by rfl) ⟨1976759, by rfl⟩ : syracuseStep 2635679 = 3953519) B3953519
theorem B3520907 : Blo 1040609 3520907 := bstep (se 1 (by rfl) ⟨2640680, by rfl⟩ : syracuseStep 3520907 = 5281361) B5281361
theorem B3521015 : Blo 1040609 3521015 := bstep (se 1 (by rfl) ⟨2640761, by rfl⟩ : syracuseStep 3521015 = 5281523) B5281523
theorem B2341871 : Blo 1040609 2341871 := bstep (se 1 (by rfl) ⟨1756403, by rfl⟩ : syracuseStep 2341871 = 3512807) B3512807
theorem B1981513 : Blo 1040609 1981513 := bstep (se 2 (by rfl) ⟨743067, by rfl⟩ : syracuseStep 1981513 = 1486135) B1486135
theorem B18988253 : Blo 1040609 18988253 := bstep (se 3 (by rfl) ⟨3560297, by rfl⟩ : syracuseStep 18988253 = 7120595) B7120595
theorem B2342447 : Blo 1040609 2342447 := bstep (se 1 (by rfl) ⟨1756835, by rfl⟩ : syracuseStep 2342447 = 3513671) B3513671
theorem B3522095 : Blo 1040609 3522095 := bstep (se 1 (by rfl) ⟨2641571, by rfl⟩ : syracuseStep 3522095 = 5283143) B5283143
theorem B5947091 : Blo 1040609 5947091 := bstep (se 1 (by rfl) ⟨4460318, by rfl⟩ : syracuseStep 5947091 = 8920637) B8920637
theorem B2342879 : Blo 1040609 2342879 := bstep (se 1 (by rfl) ⟨1757159, by rfl⟩ : syracuseStep 2342879 = 3514319) B3514319
theorem B3522527 : Blo 1040609 3522527 := bstep (se 1 (by rfl) ⟨2641895, by rfl⟩ : syracuseStep 3522527 = 5283791) B5283791
theorem B5947775 : Blo 1040609 5947775 := bstep (se 1 (by rfl) ⟨4460831, by rfl⟩ : syracuseStep 5947775 = 8921663) B8921663
theorem B7521599 : Blo 1040609 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B3523931 : Blo 1040609 3523931 := bstep (se 1 (by rfl) ⟨2642948, by rfl⟩ : syracuseStep 3523931 = 5285897) B5285897
theorem B45074069 : Blo 1040609 45074069 := bstep (se 6 (by rfl) ⟨1056423, by rfl⟩ : syracuseStep 45074069 = 2112847) B2112847
theorem B2967293 : Blo 1040609 2967293 := bstep (se 3 (by rfl) ⟨556367, by rfl⟩ : syracuseStep 2967293 = 1112735) B1112735
theorem B48122399 : Blo 1040609 48122399 := bstep (se 1 (by rfl) ⟨36091799, by rfl⟩ : syracuseStep 48122399 = 72183599) B72183599
theorem B3951287 : Blo 1040609 3951287 := bstep (se 1 (by rfl) ⟨2963465, by rfl⟩ : syracuseStep 3951287 = 5926931) B5926931
theorem B2640863 : Blo 1040609 2640863 := bstep (se 1 (by rfl) ⟨1980647, by rfl⟩ : syracuseStep 2640863 = 3961295) B3961295
theorem B1756471 : Blo 1040609 1756471 := bstep (se 1 (by rfl) ⟨1317353, by rfl⟩ : syracuseStep 1756471 = 2634707) B2634707
theorem B7523675 : Blo 1040609 7523675 := bstep (se 1 (by rfl) ⟨5642756, by rfl⟩ : syracuseStep 7523675 = 11285513) B11285513
theorem B1756937 : Blo 1040609 1756937 := bstep (se 2 (by rfl) ⟨658851, by rfl⟩ : syracuseStep 1756937 = 1317703) B1317703
theorem B169299769 : Blo 1040609 169299769 := bstep (se 2 (by rfl) ⟨63487413, by rfl⟩ : syracuseStep 169299769 = 126974827) B126974827
theorem B1756991 : Blo 1040609 1756991 := bstep (se 1 (by rfl) ⟨1317743, by rfl⟩ : syracuseStep 1756991 = 2635487) B2635487
theorem B2347055 : Blo 1040609 2347055 := bstep (se 1 (by rfl) ⟨1760291, by rfl⟩ : syracuseStep 2347055 = 3520583) B3520583
theorem B2412671 : Blo 1040609 2412671 := bstep (se 1 (by rfl) ⟨1809503, by rfl⟩ : syracuseStep 2412671 = 3619007) B3619007
theorem B162222365 : Blo 1040609 162222365 := bstep (se 3 (by rfl) ⟨30416693, by rfl⟩ : syracuseStep 162222365 = 60833387) B60833387
theorem B1561067 : Blo 1040609 1561067 := bstep (se 1 (by rfl) ⟨1170800, by rfl⟩ : syracuseStep 1561067 = 2341601) B2341601
theorem B1561193 : Blo 1040609 1561193 := bstep (se 2 (by rfl) ⟨585447, by rfl⟩ : syracuseStep 1561193 = 1170895) B1170895
theorem B1561199 : Blo 1040609 1561199 := bstep (se 1 (by rfl) ⟨1170899, by rfl⟩ : syracuseStep 1561199 = 2341799) B2341799
theorem B2347631 : Blo 1040609 2347631 := bstep (se 1 (by rfl) ⟨1760723, by rfl⟩ : syracuseStep 2347631 = 3521447) B3521447
theorem B1561319 : Blo 1040609 1561319 := bstep (se 1 (by rfl) ⟨1170989, by rfl⟩ : syracuseStep 1561319 = 2341979) B2341979
theorem B4510475 : Blo 1040609 4510475 := bstep (se 1 (by rfl) ⟨3382856, by rfl⟩ : syracuseStep 4510475 = 6765713) B6765713
theorem B2970425 : Blo 1040609 2970425 := bstep (se 2 (by rfl) ⟨1113909, by rfl⟩ : syracuseStep 2970425 = 2227819) B2227819
theorem B7918397 : Blo 1040609 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B1561481 : Blo 1040609 1561481 := bstep (se 2 (by rfl) ⟨585555, by rfl⟩ : syracuseStep 1561481 = 1171111) B1171111
theorem B2970607 : Blo 1040609 2970607 := bstep (se 1 (by rfl) ⟨2227955, by rfl⟩ : syracuseStep 2970607 = 4455911) B4455911
theorem B18043955 : Blo 1040609 18043955 := bstep (se 1 (by rfl) ⟨13532966, by rfl⟩ : syracuseStep 18043955 = 27065933) B27065933
theorem B1561823 : Blo 1040609 1561823 := bstep (se 1 (by rfl) ⟨1171367, by rfl⟩ : syracuseStep 1561823 = 2342735) B2342735
theorem B1561865 : Blo 1040609 1561865 := bstep (se 2 (by rfl) ⟨585699, by rfl⟩ : syracuseStep 1561865 = 1171399) B1171399
theorem B1562303 : Blo 1040609 1562303 := bstep (se 1 (by rfl) ⟨1171727, by rfl⟩ : syracuseStep 1562303 = 2343455) B2343455
theorem B1562345 : Blo 1040609 1562345 := bstep (se 2 (by rfl) ⟨585879, by rfl⟩ : syracuseStep 1562345 = 1171759) B1171759
theorem B1562351 : Blo 1040609 1562351 := bstep (se 1 (by rfl) ⟨1171763, by rfl⟩ : syracuseStep 1562351 = 2343527) B2343527
theorem B2348783 : Blo 1040609 2348783 := bstep (se 1 (by rfl) ⟨1761587, by rfl⟩ : syracuseStep 2348783 = 3523175) B3523175
theorem B1562855 : Blo 1040609 1562855 := bstep (se 1 (by rfl) ⟨1172141, by rfl⟩ : syracuseStep 1562855 = 2344283) B2344283
theorem B1563035 : Blo 1040609 1563035 := bstep (se 1 (by rfl) ⟨1172276, by rfl⟩ : syracuseStep 1563035 = 2344553) B2344553
theorem B6674845 : Blo 1040609 6674845 := bstep (se 3 (by rfl) ⟨1251533, by rfl⟩ : syracuseStep 6674845 = 2503067) B2503067
theorem B1563431 : Blo 1040609 1563431 := bstep (se 1 (by rfl) ⟨1172573, by rfl⟩ : syracuseStep 1563431 = 2345147) B2345147
theorem B1563455 : Blo 1040609 1563455 := bstep (se 1 (by rfl) ⟨1172591, by rfl⟩ : syracuseStep 1563455 = 2345183) B2345183
theorem B1563755 : Blo 1040609 1563755 := bstep (se 1 (by rfl) ⟨1172816, by rfl⟩ : syracuseStep 1563755 = 2345633) B2345633
theorem B2350187 : Blo 1040609 2350187 := bstep (se 1 (by rfl) ⟨1762640, by rfl⟩ : syracuseStep 2350187 = 3525281) B3525281
theorem B13360247 : Blo 1040609 13360247 := bstep (se 1 (by rfl) ⟨10020185, by rfl⟩ : syracuseStep 13360247 = 20040371) B20040371
theorem B5627015 : Blo 1040609 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B7920827 : Blo 1040609 7920827 := bstep (se 1 (by rfl) ⟨5940620, by rfl⟩ : syracuseStep 7920827 = 11881241) B11881241
theorem B1563899 : Blo 1040609 1563899 := bstep (se 1 (by rfl) ⟨1172924, by rfl⟩ : syracuseStep 1563899 = 2345849) B2345849
theorem B2350331 : Blo 1040609 2350331 := bstep (se 1 (by rfl) ⟨1762748, by rfl⟩ : syracuseStep 2350331 = 3525497) B3525497
theorem B1170715 : Blo 1040609 1170715 := bstep (se 1 (by rfl) ⟨878036, by rfl⟩ : syracuseStep 1170715 = 1756073) B1756073
theorem B1563995 : Blo 1040609 1563995 := bstep (se 1 (by rfl) ⟨1172996, by rfl⟩ : syracuseStep 1563995 = 2345993) B2345993
theorem B1564025 : Blo 1040609 1564025 := bstep (se 2 (by rfl) ⟨586509, by rfl⟩ : syracuseStep 1564025 = 1173019) B1173019
theorem B1564031 : Blo 1040609 1564031 := bstep (se 1 (by rfl) ⟨1173023, by rfl⟩ : syracuseStep 1564031 = 2346047) B2346047
theorem B8904167 : Blo 1040609 8904167 := bstep (se 1 (by rfl) ⟨6678125, by rfl⟩ : syracuseStep 8904167 = 13356251) B13356251
theorem B1171183 : Blo 1040609 1171183 := bstep (se 1 (by rfl) ⟨878387, by rfl⟩ : syracuseStep 1171183 = 1756775) B1756775
theorem B1761007 : Blo 1040609 1761007 := bstep (se 1 (by rfl) ⟨1320755, by rfl⟩ : syracuseStep 1761007 = 2641511) B2641511
theorem B1564583 : Blo 1040609 1564583 := bstep (se 1 (by rfl) ⟨1173437, by rfl⟩ : syracuseStep 1564583 = 2346875) B2346875
theorem B3170281 : Blo 1040609 3170281 := bstep (se 2 (by rfl) ⟨1188855, by rfl⟩ : syracuseStep 3170281 = 2377711) B2377711
theorem B1564655 : Blo 1040609 1564655 := bstep (se 1 (by rfl) ⟨1173491, by rfl⟩ : syracuseStep 1564655 = 2346983) B2346983
theorem B1564775 : Blo 1040609 1564775 := bstep (se 1 (by rfl) ⟨1173581, by rfl⟩ : syracuseStep 1564775 = 2347163) B2347163
theorem B1564907 : Blo 1040609 1564907 := bstep (se 1 (by rfl) ⟨1173680, by rfl⟩ : syracuseStep 1564907 = 2347361) B2347361
theorem B1564967 : Blo 1040609 1564967 := bstep (se 1 (by rfl) ⟨1173725, by rfl⟩ : syracuseStep 1564967 = 2347451) B2347451
theorem B1041055 : Blo 1040609 1041055 := bstep (se 1 (by rfl) ⟨780791, by rfl⟩ : syracuseStep 1041055 = 1561583) B1561583
theorem B1565417 : Blo 1040609 1565417 := bstep (se 2 (by rfl) ⟨587031, by rfl⟩ : syracuseStep 1565417 = 1174063) B1174063
theorem B1041311 : Blo 1040609 1041311 := bstep (se 1 (by rfl) ⟨780983, by rfl⟩ : syracuseStep 1041311 = 1561967) B1561967
theorem B1041391 : Blo 1040609 1041391 := bstep (se 1 (by rfl) ⟨781043, by rfl⟩ : syracuseStep 1041391 = 1562087) B1562087
theorem B1041499 : Blo 1040609 1041499 := bstep (se 1 (by rfl) ⟨781124, by rfl⟩ : syracuseStep 1041499 = 1562249) B1562249
theorem B1041511 : Blo 1040609 1041511 := bstep (se 1 (by rfl) ⟨781133, by rfl⟩ : syracuseStep 1041511 = 1562267) B1562267
theorem B1565807 : Blo 1040609 1565807 := bstep (se 1 (by rfl) ⟨1174355, by rfl⟩ : syracuseStep 1565807 = 2348711) B2348711
theorem B1041639 : Blo 1040609 1041639 := bstep (se 1 (by rfl) ⟨781229, by rfl⟩ : syracuseStep 1041639 = 1562459) B1562459
theorem B1565927 : Blo 1040609 1565927 := bstep (se 1 (by rfl) ⟨1174445, by rfl⟩ : syracuseStep 1565927 = 2348891) B2348891
theorem B1565993 : Blo 1040609 1565993 := bstep (se 2 (by rfl) ⟨587247, by rfl⟩ : syracuseStep 1565993 = 1174495) B1174495
theorem B1041895 : Blo 1040609 1041895 := bstep (se 1 (by rfl) ⟨781421, by rfl⟩ : syracuseStep 1041895 = 1562843) B1562843
theorem B3007975 : Blo 1040609 3007975 := bstep (se 1 (by rfl) ⟨2255981, by rfl⟩ : syracuseStep 3007975 = 4511963) B4511963
theorem B192374261 : Blo 1040609 192374261 := bstep (se 5 (by rfl) ⟨9017543, by rfl⟩ : syracuseStep 192374261 = 18035087) B18035087
theorem B3335681 : Blo 1040609 3335681 := bstep (se 2 (by rfl) ⟨1250880, by rfl⟩ : syracuseStep 3335681 = 2501761) B2501761
theorem B1566263 : Blo 1040609 1566263 := bstep (se 1 (by rfl) ⟨1174697, by rfl⟩ : syracuseStep 1566263 = 2349395) B2349395
theorem B1042075 : Blo 1040609 1042075 := bstep (se 1 (by rfl) ⟨781556, by rfl⟩ : syracuseStep 1042075 = 1563113) B1563113
theorem B1206139 : Blo 1040609 1206139 := bstep (se 1 (by rfl) ⟨904604, by rfl⟩ : syracuseStep 1206139 = 1809209) B1809209
theorem B1566587 : Blo 1040609 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B1042335 : Blo 1040609 1042335 := bstep (se 1 (by rfl) ⟨781751, by rfl⟩ : syracuseStep 1042335 = 1563503) B1563503
theorem B1566623 : Blo 1040609 1566623 := bstep (se 1 (by rfl) ⟨1174967, by rfl⟩ : syracuseStep 1566623 = 2349935) B2349935
theorem B1042343 : Blo 1040609 1042343 := bstep (se 1 (by rfl) ⟨781757, by rfl⟩ : syracuseStep 1042343 = 1563515) B1563515
theorem B1173415 : Blo 1040609 1173415 := bstep (se 1 (by rfl) ⟨880061, by rfl⟩ : syracuseStep 1173415 = 1760123) B1760123
theorem B3336167 : Blo 1040609 3336167 := bstep (se 1 (by rfl) ⟨2502125, by rfl⟩ : syracuseStep 3336167 = 5004251) B5004251
theorem B5269535 : Blo 1040609 5269535 := bstep (se 1 (by rfl) ⟨3952151, by rfl⟩ : syracuseStep 5269535 = 7904303) B7904303
theorem B1566857 : Blo 1040609 1566857 := bstep (se 2 (by rfl) ⟨587571, by rfl⟩ : syracuseStep 1566857 = 1175143) B1175143
theorem B1042919 : Blo 1040609 1042919 := bstep (se 1 (by rfl) ⟨782189, by rfl⟩ : syracuseStep 1042919 = 1564379) B1564379
theorem B1173991 : Blo 1040609 1173991 := bstep (se 1 (by rfl) ⟨880493, by rfl⟩ : syracuseStep 1173991 = 1760987) B1760987
theorem B1043099 : Blo 1040609 1043099 := bstep (se 1 (by rfl) ⟨782324, by rfl⟩ : syracuseStep 1043099 = 1564649) B1564649
theorem B1174171 : Blo 1040609 1174171 := bstep (se 1 (by rfl) ⟨880628, by rfl⟩ : syracuseStep 1174171 = 1761257) B1761257
theorem B1043567 : Blo 1040609 1043567 := bstep (se 1 (by rfl) ⟨782675, by rfl⟩ : syracuseStep 1043567 = 1565351) B1565351
theorem B1174639 : Blo 1040609 1174639 := bstep (se 1 (by rfl) ⟨880979, by rfl⟩ : syracuseStep 1174639 = 1761959) B1761959
theorem B1043647 : Blo 1040609 1043647 := bstep (se 1 (by rfl) ⟨782735, by rfl⟩ : syracuseStep 1043647 = 1565471) B1565471
theorem B1043663 : Blo 1040609 1043663 := bstep (se 1 (by rfl) ⟨782747, by rfl⟩ : syracuseStep 1043663 = 1565495) B1565495
theorem B1043783 : Blo 1040609 1043783 := bstep (se 1 (by rfl) ⟨782837, by rfl⟩ : syracuseStep 1043783 = 1565675) B1565675
theorem B1174855 : Blo 1040609 1174855 := bstep (se 1 (by rfl) ⟨881141, by rfl⟩ : syracuseStep 1174855 = 1762283) B1762283
theorem B3173807 : Blo 1040609 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B8580809 : Blo 1040609 8580809 := bstep (se 2 (by rfl) ⟨3217803, by rfl⟩ : syracuseStep 8580809 = 6435607) B6435607
theorem B3010375 : Blo 1040609 3010375 := bstep (se 1 (by rfl) ⟨2257781, by rfl⟩ : syracuseStep 3010375 = 4515563) B4515563
theorem B11857913 : Blo 1040609 11857913 := bstep (se 2 (by rfl) ⟨4446717, by rfl⟩ : syracuseStep 11857913 = 8893435) B8893435
theorem B1044511 : Blo 1040609 1044511 := bstep (se 1 (by rfl) ⟨783383, by rfl⟩ : syracuseStep 1044511 = 1566767) B1566767
theorem B76116469 : Blo 1040609 76116469 := bstep (se 5 (by rfl) ⟨3567959, by rfl⟩ : syracuseStep 76116469 = 7135919) B7135919
theorem B6681203 : Blo 1040609 6681203 := bstep (se 1 (by rfl) ⟨5010902, by rfl⟩ : syracuseStep 6681203 = 10021805) B10021805
theorem B1668251 : Blo 1040609 1668251 := bstep (se 1 (by rfl) ⟨1251188, by rfl⟩ : syracuseStep 1668251 = 2502377) B2502377
theorem B7927631 : Blo 1040609 7927631 := bstep (se 1 (by rfl) ⟨5945723, by rfl⟩ : syracuseStep 7927631 = 11891447) B11891447
theorem B3962753 : Blo 1040609 3962753 := bstep (se 2 (by rfl) ⟨1486032, by rfl⟩ : syracuseStep 3962753 = 2972065) B2972065
theorem B5273747 : Blo 1040609 5273747 := bstep (se 1 (by rfl) ⟨3955310, by rfl⟩ : syracuseStep 5273747 = 7910621) B7910621
theorem B1669339 : Blo 1040609 1669339 := bstep (se 1 (by rfl) ⟨1252004, by rfl⟩ : syracuseStep 1669339 = 2504009) B2504009
theorem B45709541 : Blo 1040609 45709541 := bstep (se 4 (by rfl) ⟨4285269, by rfl⟩ : syracuseStep 45709541 = 8570539) B8570539
theorem B3340703 : Blo 1040609 3340703 := bstep (se 1 (by rfl) ⟨2505527, by rfl⟩ : syracuseStep 3340703 = 5011055) B5011055
theorem B3340871 : Blo 1040609 3340871 := bstep (se 1 (by rfl) ⟨2505653, by rfl⟩ : syracuseStep 3340871 = 5011307) B5011307
theorem B5274233 : Blo 1040609 5274233 := bstep (se 2 (by rfl) ⟨1977837, by rfl⟩ : syracuseStep 5274233 = 3955675) B3955675
theorem B21723805 : Blo 1040609 21723805 := bstep (se 3 (by rfl) ⟨4073213, by rfl⟩ : syracuseStep 21723805 = 8146427) B8146427
theorem B13368401 : Blo 1040609 13368401 := bstep (se 2 (by rfl) ⟨5013150, by rfl⟩ : syracuseStep 13368401 = 10026301) B10026301
theorem B1408495 : Blo 1040609 1408495 := bstep (se 1 (by rfl) ⟨1056371, by rfl⟩ : syracuseStep 1408495 = 2112743) B2112743
theorem B5275367 : Blo 1040609 5275367 := bstep (se 1 (by rfl) ⟨3956525, by rfl⟩ : syracuseStep 5275367 = 7913051) B7913051
theorem B2227999 : Blo 1040609 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B4226879 : Blo 1040609 4226879 := bstep (se 1 (by rfl) ⟨3170159, by rfl⟩ : syracuseStep 4226879 = 6340319) B6340319
theorem B3571577 : Blo 1040609 3571577 := bstep (se 2 (by rfl) ⟨1339341, by rfl⟩ : syracuseStep 3571577 = 2678683) B2678683
theorem B3964909 : Blo 1040609 3964909 := bstep (se 3 (by rfl) ⟨743420, by rfl⟩ : syracuseStep 3964909 = 1486841) B1486841
theorem B3965183 : Blo 1040609 3965183 := bstep (se 1 (by rfl) ⟨2973887, by rfl⟩ : syracuseStep 3965183 = 5947775) B5947775
theorem B3965213 : Blo 1040609 3965213 := bstep (se 3 (by rfl) ⟨743477, by rfl⟩ : syracuseStep 3965213 = 1486955) B1486955
theorem B1115003 : Blo 1040609 1115003 := bstep (se 1 (by rfl) ⟨836252, by rfl⟩ : syracuseStep 1115003 = 1672505) B1672505
theorem B5014399 : Blo 1040609 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B30049379 : Blo 1040609 30049379 := bstep (se 1 (by rfl) ⟨22537034, by rfl⟩ : syracuseStep 30049379 = 45074069) B45074069
theorem B32081599 : Blo 1040609 32081599 := bstep (se 1 (by rfl) ⟨24061199, by rfl⟩ : syracuseStep 32081599 = 48122399) B48122399
theorem B5015783 : Blo 1040609 5015783 := bstep (se 1 (by rfl) ⟨3761837, by rfl⟩ : syracuseStep 5015783 = 7523675) B7523675
theorem B1608185 : Blo 1040609 1608185 := bstep (se 2 (by rfl) ⟨603069, by rfl⟩ : syracuseStep 1608185 = 1206139) B1206139
theorem B2230895 : Blo 1040609 2230895 := bstep (se 1 (by rfl) ⟨1673171, by rfl⟩ : syracuseStep 2230895 = 3346343) B3346343
theorem B5278931 : Blo 1040609 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B12029303 : Blo 1040609 12029303 := bstep (se 1 (by rfl) ⟨9021977, by rfl⟩ : syracuseStep 12029303 = 18043955) B18043955
theorem B48075113 : Blo 1040609 48075113 := bstep (se 2 (by rfl) ⟨18028167, by rfl⟩ : syracuseStep 48075113 = 36056335) B36056335
theorem B6689249 : Blo 1040609 6689249 := bstep (se 2 (by rfl) ⟨2508468, by rfl⟩ : syracuseStep 6689249 = 5016937) B5016937
theorem B5280551 : Blo 1040609 5280551 := bstep (se 1 (by rfl) ⟨3960413, by rfl⟩ : syracuseStep 5280551 = 7920827) B7920827
theorem B5936111 : Blo 1040609 5936111 := bstep (se 1 (by rfl) ⟨4452083, by rfl⟩ : syracuseStep 5936111 = 8904167) B8904167
theorem B4461601 : Blo 1040609 4461601 := bstep (se 2 (by rfl) ⟨1673100, by rfl⟩ : syracuseStep 4461601 = 3346201) B3346201
theorem B15013619 : Blo 1040609 15013619 := bstep (se 1 (by rfl) ⟨11260214, by rfl⟩ : syracuseStep 15013619 = 22520429) B22520429
theorem B11868119 : Blo 1040609 11868119 := bstep (se 1 (by rfl) ⟨8901089, by rfl⟩ : syracuseStep 11868119 = 17802179) B17802179
theorem B101488625 : Blo 1040609 101488625 := bstep (se 2 (by rfl) ⟨38058234, by rfl⟩ : syracuseStep 101488625 = 76116469) B76116469
theorem B3513023 : Blo 1040609 3513023 := bstep (se 1 (by rfl) ⟨2634767, by rfl⟩ : syracuseStep 3513023 = 5269535) B5269535
theorem B1252135 : Blo 1040609 1252135 := bstep (se 1 (by rfl) ⟨939101, by rfl⟩ : syracuseStep 1252135 = 1878203) B1878203
theorem B3513833 : Blo 1040609 3513833 := bstep (se 2 (by rfl) ⟨1317687, by rfl⟩ : syracuseStep 3513833 = 2635375) B2635375
theorem B3612647 : Blo 1040609 3612647 := bstep (se 1 (by rfl) ⟨2709485, by rfl⟩ : syracuseStep 3612647 = 5418971) B5418971
theorem B7905275 : Blo 1040609 7905275 := bstep (se 1 (by rfl) ⟨5928956, by rfl⟩ : syracuseStep 7905275 = 11857913) B11857913
theorem B8463485 : Blo 1040609 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B5285087 : Blo 1040609 5285087 := bstep (se 1 (by rfl) ⟨3963815, by rfl⟩ : syracuseStep 5285087 = 7927631) B7927631
theorem B3515831 : Blo 1040609 3515831 := bstep (se 1 (by rfl) ⟨2636873, by rfl⟩ : syracuseStep 3515831 = 5273747) B5273747
theorem B3516155 : Blo 1040609 3516155 := bstep (se 1 (by rfl) ⟨2637116, by rfl⟩ : syracuseStep 3516155 = 5274233) B5274233
theorem B54208349 : Blo 1040609 54208349 := bstep (se 3 (by rfl) ⟨10164065, by rfl⟩ : syracuseStep 54208349 = 20328131) B20328131
theorem B1877993 : Blo 1040609 1877993 := bstep (se 2 (by rfl) ⟨704247, by rfl⟩ : syracuseStep 1877993 = 1408495) B1408495
theorem B7612537 : Blo 1040609 7612537 := bstep (se 2 (by rfl) ⟨2854701, by rfl⟩ : syracuseStep 7612537 = 5709403) B5709403
theorem B12658835 : Blo 1040609 12658835 := bstep (se 1 (by rfl) ⟨9494126, by rfl⟩ : syracuseStep 12658835 = 18988253) B18988253
theorem B3516911 : Blo 1040609 3516911 := bstep (se 1 (by rfl) ⟨2637683, by rfl⟩ : syracuseStep 3516911 = 5275367) B5275367
theorem B5286545 : Blo 1040609 5286545 := bstep (se 2 (by rfl) ⟨1982454, by rfl⟩ : syracuseStep 5286545 = 3964909) B3964909
theorem B7514795 : Blo 1040609 7514795 := bstep (se 1 (by rfl) ⟨5636096, by rfl⟩ : syracuseStep 7514795 = 11272193) B11272193
theorem B7908191 : Blo 1040609 7908191 := bstep (se 1 (by rfl) ⟨5931143, by rfl⟩ : syracuseStep 7908191 = 11862287) B11862287
theorem B6433789 : Blo 1040609 6433789 := bstep (se 3 (by rfl) ⟨1206335, by rfl⟩ : syracuseStep 6433789 = 2412671) B2412671
theorem B1879247 : Blo 1040609 1879247 := bstep (se 1 (by rfl) ⟨1409435, by rfl⟩ : syracuseStep 1879247 = 2818871) B2818871
theorem B1978195 : Blo 1040609 1978195 := bstep (se 1 (by rfl) ⟨1483646, by rfl⟩ : syracuseStep 1978195 = 2967293) B2967293
theorem B2634191 : Blo 1040609 2634191 := bstep (se 1 (by rfl) ⟨1975643, by rfl⟩ : syracuseStep 2634191 = 3951287) B3951287
theorem B1978985 : Blo 1040609 1978985 := bstep (se 2 (by rfl) ⟨742119, by rfl⟩ : syracuseStep 1978985 = 1484239) B1484239
theorem B4010633 : Blo 1040609 4010633 := bstep (se 2 (by rfl) ⟨1503987, by rfl⟩ : syracuseStep 4010633 = 3007975) B3007975
theorem B108148243 : Blo 1040609 108148243 := bstep (se 1 (by rfl) ⟨81111182, by rfl⟩ : syracuseStep 108148243 = 162222365) B162222365
theorem B1980283 : Blo 1040609 1980283 := bstep (se 1 (by rfl) ⟨1485212, by rfl⟩ : syracuseStep 1980283 = 2970425) B2970425
theorem B3520637 : Blo 1040609 3520637 := bstep (se 3 (by rfl) ⟨660119, by rfl⟩ : syracuseStep 3520637 = 1320239) B1320239
theorem B3520799 : Blo 1040609 3520799 := bstep (se 1 (by rfl) ⟨2640599, by rfl⟩ : syracuseStep 3520799 = 5281199) B5281199
theorem B17152559 : Blo 1040609 17152559 := bstep (se 1 (by rfl) ⟨12864419, by rfl⟩ : syracuseStep 17152559 = 25728839) B25728839
theorem B123681821 : Blo 1040609 123681821 := bstep (se 3 (by rfl) ⟨23190341, by rfl⟩ : syracuseStep 123681821 = 46380683) B46380683
theorem B2341961 : Blo 1040609 2341961 := bstep (se 2 (by rfl) ⟨878235, by rfl⟩ : syracuseStep 2341961 = 1756471) B1756471
theorem B3751343 : Blo 1040609 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B3522203 : Blo 1040609 3522203 := bstep (se 1 (by rfl) ⟨2641652, by rfl⟩ : syracuseStep 3522203 = 5283305) B5283305
theorem B5947343 : Blo 1040609 5947343 := bstep (se 1 (by rfl) ⟨4460507, by rfl⟩ : syracuseStep 5947343 = 8921015) B8921015
theorem B7914023 : Blo 1040609 7914023 := bstep (se 1 (by rfl) ⟨5935517, by rfl⟩ : syracuseStep 7914023 = 11871035) B11871035
theorem B5948093 : Blo 1040609 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B2343743 : Blo 1040609 2343743 := bstep (se 1 (by rfl) ⟨1757807, by rfl⟩ : syracuseStep 2343743 = 3515615) B3515615
theorem B892257277 : Blo 1040609 892257277 := bstep (se 3 (by rfl) ⟨167298239, by rfl⟩ : syracuseStep 892257277 = 334596479) B334596479
theorem B2638889 : Blo 1040609 2638889 := bstep (se 2 (by rfl) ⟨989583, by rfl⟩ : syracuseStep 2638889 = 1979167) B1979167
theorem B2344211 : Blo 1040609 2344211 := bstep (se 1 (by rfl) ⟨1758158, by rfl⟩ : syracuseStep 2344211 = 3516317) B3516317
theorem B3524039 : Blo 1040609 3524039 := bstep (se 1 (by rfl) ⟨2643029, by rfl⟩ : syracuseStep 3524039 = 5286059) B5286059
theorem B3524255 : Blo 1040609 3524255 := bstep (se 1 (by rfl) ⟨2643191, by rfl⟩ : syracuseStep 3524255 = 5286383) B5286383
theorem B8898767 : Blo 1040609 8898767 := bstep (se 1 (by rfl) ⟨6674075, by rfl⟩ : syracuseStep 8898767 = 13348151) B13348151
theorem B5720539 : Blo 1040609 5720539 := bstep (se 1 (by rfl) ⟨4290404, by rfl⟩ : syracuseStep 5720539 = 8580809) B8580809
theorem B2345939 : Blo 1040609 2345939 := bstep (se 1 (by rfl) ⟨1759454, by rfl⟩ : syracuseStep 2345939 = 3518909) B3518909
theorem B8899793 : Blo 1040609 8899793 := bstep (se 2 (by rfl) ⟨3337422, by rfl⟩ : syracuseStep 8899793 = 6674845) B6674845
theorem B7916939 : Blo 1040609 7916939 := bstep (se 1 (by rfl) ⟨5937704, by rfl⟩ : syracuseStep 7916939 = 11875409) B11875409
theorem B2346515 : Blo 1040609 2346515 := bstep (se 1 (by rfl) ⟨1759886, by rfl⟩ : syracuseStep 2346515 = 3519773) B3519773
theorem B1756903 : Blo 1040609 1756903 := bstep (se 1 (by rfl) ⟨1317677, by rfl⟩ : syracuseStep 1756903 = 2635355) B2635355
theorem B10145675 : Blo 1040609 10145675 := bstep (se 1 (by rfl) ⟨7609256, by rfl⟩ : syracuseStep 10145675 = 15218513) B15218513
theorem B2641835 : Blo 1040609 2641835 := bstep (se 1 (by rfl) ⟨1981376, by rfl⟩ : syracuseStep 2641835 = 3962753) B3962753
theorem B1757119 : Blo 1040609 1757119 := bstep (se 1 (by rfl) ⟨1317839, by rfl⟩ : syracuseStep 1757119 = 2635679) B2635679
theorem B2642017 : Blo 1040609 2642017 := bstep (se 2 (by rfl) ⟨990756, by rfl⟩ : syracuseStep 2642017 = 1981513) B1981513
theorem B2347271 : Blo 1040609 2347271 := bstep (se 1 (by rfl) ⟨1760453, by rfl⟩ : syracuseStep 2347271 = 3520907) B3520907
theorem B2347343 : Blo 1040609 2347343 := bstep (se 1 (by rfl) ⟨1760507, by rfl⟩ : syracuseStep 2347343 = 3521015) B3521015
theorem B1560953 : Blo 1040609 1560953 := bstep (se 2 (by rfl) ⟨585357, by rfl⟩ : syracuseStep 1560953 = 1170715) B1170715
theorem B1757801 : Blo 1040609 1757801 := bstep (se 2 (by rfl) ⟨659175, by rfl⟩ : syracuseStep 1757801 = 1318351) B1318351
theorem B1561247 : Blo 1040609 1561247 := bstep (se 1 (by rfl) ⟨1170935, by rfl⟩ : syracuseStep 1561247 = 2341871) B2341871
theorem B1561577 : Blo 1040609 1561577 := bstep (se 2 (by rfl) ⟨585591, by rfl⟩ : syracuseStep 1561577 = 1171183) B1171183
theorem B2348009 : Blo 1040609 2348009 := bstep (se 2 (by rfl) ⟨880503, by rfl⟩ : syracuseStep 2348009 = 1761007) B1761007
theorem B1561631 : Blo 1040609 1561631 := bstep (se 1 (by rfl) ⟨1171223, by rfl⟩ : syracuseStep 1561631 = 2342447) B2342447
theorem B2348063 : Blo 1040609 2348063 := bstep (se 1 (by rfl) ⟨1761047, by rfl⟩ : syracuseStep 2348063 = 3522095) B3522095
theorem B2970665 : Blo 1040609 2970665 := bstep (se 2 (by rfl) ⟨1113999, by rfl⟩ : syracuseStep 2970665 = 2227999) B2227999
theorem B2381051 : Blo 1040609 2381051 := bstep (se 1 (by rfl) ⟨1785788, by rfl⟩ : syracuseStep 2381051 = 3571577) B3571577
theorem B1561919 : Blo 1040609 1561919 := bstep (se 1 (by rfl) ⟨1171439, by rfl⟩ : syracuseStep 1561919 = 2342879) B2342879
theorem B2348351 : Blo 1040609 2348351 := bstep (se 1 (by rfl) ⟨1761263, by rfl⟩ : syracuseStep 2348351 = 3522527) B3522527
theorem B1758793 : Blo 1040609 1758793 := bstep (se 2 (by rfl) ⟨659547, by rfl⟩ : syracuseStep 1758793 = 1319095) B1319095
theorem B2349287 : Blo 1040609 2349287 := bstep (se 1 (by rfl) ⟨1761965, by rfl⟩ : syracuseStep 2349287 = 3523931) B3523931
theorem B8903141 : Blo 1040609 8903141 := bstep (se 4 (by rfl) ⟨834669, by rfl⟩ : syracuseStep 8903141 = 1669339) B1669339
theorem B3955175 : Blo 1040609 3955175 := bstep (se 1 (by rfl) ⟨2966381, by rfl⟩ : syracuseStep 3955175 = 5932763) B5932763
theorem B1760575 : Blo 1040609 1760575 := bstep (se 1 (by rfl) ⟨1320431, by rfl⟩ : syracuseStep 1760575 = 2640863) B2640863
theorem B2973181 : Blo 1040609 2973181 := bstep (se 3 (by rfl) ⟨557471, by rfl⟩ : syracuseStep 2973181 = 1114943) B1114943
theorem B1171291 : Blo 1040609 1171291 := bstep (se 1 (by rfl) ⟨878468, by rfl⟩ : syracuseStep 1171291 = 1756937) B1756937
theorem B1171327 : Blo 1040609 1171327 := bstep (se 1 (by rfl) ⟨878495, by rfl⟩ : syracuseStep 1171327 = 1756991) B1756991
theorem B1564553 : Blo 1040609 1564553 := bstep (se 2 (by rfl) ⟨586707, by rfl⟩ : syracuseStep 1564553 = 1173415) B1173415
theorem B1564703 : Blo 1040609 1564703 := bstep (se 1 (by rfl) ⟨1173527, by rfl⟩ : syracuseStep 1564703 = 2347055) B2347055
theorem B1040711 : Blo 1040609 1040711 := bstep (se 1 (by rfl) ⟨780533, by rfl⟩ : syracuseStep 1040711 = 1561067) B1561067
theorem B1040795 : Blo 1040609 1040795 := bstep (se 1 (by rfl) ⟨780596, by rfl⟩ : syracuseStep 1040795 = 1561193) B1561193
theorem B1040799 : Blo 1040609 1040799 := bstep (se 1 (by rfl) ⟨780599, by rfl⟩ : syracuseStep 1040799 = 1561199) B1561199
theorem B1565087 : Blo 1040609 1565087 := bstep (se 1 (by rfl) ⟨1173815, by rfl⟩ : syracuseStep 1565087 = 2347631) B2347631
theorem B1040879 : Blo 1040609 1040879 := bstep (se 1 (by rfl) ⟨780659, by rfl⟩ : syracuseStep 1040879 = 1561319) B1561319
theorem B3006983 : Blo 1040609 3006983 := bstep (se 1 (by rfl) ⟨2255237, by rfl⟩ : syracuseStep 3006983 = 4510475) B4510475
theorem B1040987 : Blo 1040609 1040987 := bstep (se 1 (by rfl) ⟨780740, by rfl⟩ : syracuseStep 1040987 = 1561481) B1561481
theorem B1565321 : Blo 1040609 1565321 := bstep (se 2 (by rfl) ⟨586995, by rfl⟩ : syracuseStep 1565321 = 1173991) B1173991
theorem B1041215 : Blo 1040609 1041215 := bstep (se 1 (by rfl) ⟨780911, by rfl⟩ : syracuseStep 1041215 = 1561823) B1561823
theorem B1041243 : Blo 1040609 1041243 := bstep (se 1 (by rfl) ⟨780932, by rfl⟩ : syracuseStep 1041243 = 1561865) B1561865
theorem B1565561 : Blo 1040609 1565561 := bstep (se 2 (by rfl) ⟨587085, by rfl⟩ : syracuseStep 1565561 = 1174171) B1174171
theorem B1041535 : Blo 1040609 1041535 := bstep (se 1 (by rfl) ⟨781151, by rfl⟩ : syracuseStep 1041535 = 1562303) B1562303
theorem B1041563 : Blo 1040609 1041563 := bstep (se 1 (by rfl) ⟨781172, by rfl⟩ : syracuseStep 1041563 = 1562345) B1562345
theorem B1041567 : Blo 1040609 1041567 := bstep (se 1 (by rfl) ⟨781175, by rfl⟩ : syracuseStep 1041567 = 1562351) B1562351
theorem B1565855 : Blo 1040609 1565855 := bstep (se 1 (by rfl) ⟨1174391, by rfl⟩ : syracuseStep 1565855 = 2348783) B2348783
theorem B1566185 : Blo 1040609 1566185 := bstep (se 2 (by rfl) ⟨587319, by rfl⟩ : syracuseStep 1566185 = 1174639) B1174639
theorem B1041903 : Blo 1040609 1041903 := bstep (se 1 (by rfl) ⟨781427, by rfl⟩ : syracuseStep 1041903 = 1562855) B1562855
theorem B1042023 : Blo 1040609 1042023 := bstep (se 1 (by rfl) ⟨781517, by rfl⟩ : syracuseStep 1042023 = 1563035) B1563035
theorem B1566473 : Blo 1040609 1566473 := bstep (se 2 (by rfl) ⟨587427, by rfl⟩ : syracuseStep 1566473 = 1174855) B1174855
theorem B1042287 : Blo 1040609 1042287 := bstep (se 1 (by rfl) ⟨781715, by rfl⟩ : syracuseStep 1042287 = 1563431) B1563431
theorem B1042303 : Blo 1040609 1042303 := bstep (se 1 (by rfl) ⟨781727, by rfl⟩ : syracuseStep 1042303 = 1563455) B1563455
theorem B1042503 : Blo 1040609 1042503 := bstep (se 1 (by rfl) ⟨781877, by rfl⟩ : syracuseStep 1042503 = 1563755) B1563755
theorem B1566791 : Blo 1040609 1566791 := bstep (se 1 (by rfl) ⟨1175093, by rfl⟩ : syracuseStep 1566791 = 2350187) B2350187
theorem B8906831 : Blo 1040609 8906831 := bstep (se 1 (by rfl) ⟨6680123, by rfl⟩ : syracuseStep 8906831 = 13360247) B13360247
theorem B1042599 : Blo 1040609 1042599 := bstep (se 1 (by rfl) ⟨781949, by rfl⟩ : syracuseStep 1042599 = 1563899) B1563899
theorem B1566887 : Blo 1040609 1566887 := bstep (se 1 (by rfl) ⟨1175165, by rfl⟩ : syracuseStep 1566887 = 2350331) B2350331
theorem B1042663 : Blo 1040609 1042663 := bstep (se 1 (by rfl) ⟨781997, by rfl⟩ : syracuseStep 1042663 = 1563995) B1563995
theorem B1042683 : Blo 1040609 1042683 := bstep (se 1 (by rfl) ⟨782012, by rfl⟩ : syracuseStep 1042683 = 1564025) B1564025
theorem B1042687 : Blo 1040609 1042687 := bstep (se 1 (by rfl) ⟨782015, by rfl⟩ : syracuseStep 1042687 = 1564031) B1564031
theorem B225733025 : Blo 1040609 225733025 := bstep (se 2 (by rfl) ⟨84649884, by rfl⟩ : syracuseStep 225733025 = 169299769) B169299769
theorem B1043055 : Blo 1040609 1043055 := bstep (se 1 (by rfl) ⟨782291, by rfl⟩ : syracuseStep 1043055 = 1564583) B1564583
theorem B1043103 : Blo 1040609 1043103 := bstep (se 1 (by rfl) ⟨782327, by rfl⟩ : syracuseStep 1043103 = 1564655) B1564655
theorem B1043183 : Blo 1040609 1043183 := bstep (se 1 (by rfl) ⟨782387, by rfl⟩ : syracuseStep 1043183 = 1564775) B1564775
theorem B1043271 : Blo 1040609 1043271 := bstep (se 1 (by rfl) ⟨782453, by rfl⟩ : syracuseStep 1043271 = 1564907) B1564907
theorem B1043311 : Blo 1040609 1043311 := bstep (se 1 (by rfl) ⟨782483, by rfl⟩ : syracuseStep 1043311 = 1564967) B1564967
theorem B3959867 : Blo 1040609 3959867 := bstep (se 1 (by rfl) ⟨2969900, by rfl⟩ : syracuseStep 3959867 = 5939801) B5939801
theorem B1043611 : Blo 1040609 1043611 := bstep (se 1 (by rfl) ⟨782708, by rfl⟩ : syracuseStep 1043611 = 1565417) B1565417
theorem B1043871 : Blo 1040609 1043871 := bstep (se 1 (by rfl) ⟨782903, by rfl⟩ : syracuseStep 1043871 = 1565807) B1565807
theorem B1043951 : Blo 1040609 1043951 := bstep (se 1 (by rfl) ⟨782963, by rfl⟩ : syracuseStep 1043951 = 1565927) B1565927
theorem B1043995 : Blo 1040609 1043995 := bstep (se 1 (by rfl) ⟨782996, by rfl⟩ : syracuseStep 1043995 = 1565993) B1565993
theorem B128249507 : Blo 1040609 128249507 := bstep (se 1 (by rfl) ⟨96187130, by rfl⟩ : syracuseStep 128249507 = 192374261) B192374261
theorem B2223787 : Blo 1040609 2223787 := bstep (se 1 (by rfl) ⟨1667840, by rfl⟩ : syracuseStep 2223787 = 3335681) B3335681
theorem B1044175 : Blo 1040609 1044175 := bstep (se 1 (by rfl) ⟨783131, by rfl⟩ : syracuseStep 1044175 = 1566263) B1566263
theorem B8908541 : Blo 1040609 8908541 := bstep (se 3 (by rfl) ⟨1670351, by rfl⟩ : syracuseStep 8908541 = 3340703) B3340703
theorem B5926679 : Blo 1040609 5926679 := bstep (se 1 (by rfl) ⟨4445009, by rfl⟩ : syracuseStep 5926679 = 8890019) B8890019
theorem B1044391 : Blo 1040609 1044391 := bstep (se 1 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 1044391 = 1566587) B1566587
theorem B1044415 : Blo 1040609 1044415 := bstep (se 1 (by rfl) ⟨783311, by rfl⟩ : syracuseStep 1044415 = 1566623) B1566623
theorem B3960809 : Blo 1040609 3960809 := bstep (se 2 (by rfl) ⟨1485303, by rfl⟩ : syracuseStep 3960809 = 2970607) B2970607
theorem B2224111 : Blo 1040609 2224111 := bstep (se 1 (by rfl) ⟨1668083, by rfl⟩ : syracuseStep 2224111 = 3336167) B3336167
theorem B1044571 : Blo 1040609 1044571 := bstep (se 1 (by rfl) ⟨783428, by rfl⟩ : syracuseStep 1044571 = 1566857) B1566857
theorem B17789057 : Blo 1040609 17789057 := bstep (se 2 (by rfl) ⟨6670896, by rfl⟩ : syracuseStep 17789057 = 13341793) B13341793
theorem B3961811 : Blo 1040609 3961811 := bstep (se 1 (by rfl) ⟨2971358, by rfl⟩ : syracuseStep 3961811 = 5942717) B5942717
theorem B3961979 : Blo 1040609 3961979 := bstep (se 1 (by rfl) ⟨2971484, by rfl⟩ : syracuseStep 3961979 = 5942969) B5942969
theorem B26768879 : Blo 1040609 26768879 := bstep (se 1 (by rfl) ⟨20076659, by rfl⟩ : syracuseStep 26768879 = 40153319) B40153319
theorem B4454135 : Blo 1040609 4454135 := bstep (se 1 (by rfl) ⟨3340601, by rfl⟩ : syracuseStep 4454135 = 6681203) B6681203
theorem B1112167 : Blo 1040609 1112167 := bstep (se 1 (by rfl) ⟨834125, by rfl⟩ : syracuseStep 1112167 = 1668251) B1668251
theorem B28965073 : Blo 1040609 28965073 := bstep (se 2 (by rfl) ⟨10861902, by rfl⟩ : syracuseStep 28965073 = 21723805) B21723805
theorem B3963239 : Blo 1040609 3963239 := bstep (se 1 (by rfl) ⟨2972429, by rfl⟩ : syracuseStep 3963239 = 5944859) B5944859
theorem B4225387 : Blo 1040609 4225387 := bstep (se 1 (by rfl) ⟨3169040, by rfl⟩ : syracuseStep 4225387 = 6338081) B6338081
theorem B30473027 : Blo 1040609 30473027 := bstep (se 1 (by rfl) ⟨22854770, by rfl⟩ : syracuseStep 30473027 = 45709541) B45709541
theorem B4291553 : Blo 1040609 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B16055333 : Blo 1040609 16055333 := bstep (se 4 (by rfl) ⟨1505187, by rfl⟩ : syracuseStep 16055333 = 3010375) B3010375
theorem B2227247 : Blo 1040609 2227247 := bstep (se 1 (by rfl) ⟨1670435, by rfl⟩ : syracuseStep 2227247 = 3340871) B3340871
theorem B8912267 : Blo 1040609 8912267 := bstep (se 1 (by rfl) ⟨6684200, by rfl⟩ : syracuseStep 8912267 = 13368401) B13368401
theorem B3964727 : Blo 1040609 3964727 := bstep (se 1 (by rfl) ⟨2973545, by rfl⟩ : syracuseStep 3964727 = 5947091) B5947091
theorem B2817919 : Blo 1040609 2817919 := bstep (se 1 (by rfl) ⟨2113439, by rfl⟩ : syracuseStep 2817919 = 4226879) B4226879
theorem B4227041 : Blo 1040609 4227041 := bstep (se 2 (by rfl) ⟨1585140, by rfl⟩ : syracuseStep 4227041 = 3170281) B3170281
theorem B5276015 : Blo 1040609 5276015 := bstep (se 1 (by rfl) ⟨3957011, by rfl⟩ : syracuseStep 5276015 = 7914023) B7914023
theorem B3965395 : Blo 1040609 3965395 := bstep (se 1 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 3965395 = 5948093) B5948093
theorem B6685865 : Blo 1040609 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B1189676369 : Blo 1040609 1189676369 := bstep (se 2 (by rfl) ⟨446128638, by rfl⟩ : syracuseStep 1189676369 = 892257277) B892257277
theorem B5932511 : Blo 1040609 5932511 := bstep (se 1 (by rfl) ⟨4449383, by rfl⟩ : syracuseStep 5932511 = 8898767) B8898767
theorem B3343855 : Blo 1040609 3343855 := bstep (se 1 (by rfl) ⟨2507891, by rfl⟩ : syracuseStep 3343855 = 5015783) B5015783
theorem B5933195 : Blo 1040609 5933195 := bstep (se 1 (by rfl) ⟨4449896, by rfl⟩ : syracuseStep 5933195 = 8899793) B8899793
theorem B5277959 : Blo 1040609 5277959 := bstep (se 1 (by rfl) ⟨3958469, by rfl⟩ : syracuseStep 5277959 = 7916939) B7916939
theorem B32050075 : Blo 1040609 32050075 := bstep (se 1 (by rfl) ⟨24037556, by rfl⟩ : syracuseStep 32050075 = 48075113) B48075113
theorem B4459499 : Blo 1040609 4459499 := bstep (se 1 (by rfl) ⟨3344624, by rfl⟩ : syracuseStep 4459499 = 6689249) B6689249
theorem B5935427 : Blo 1040609 5935427 := bstep (se 1 (by rfl) ⟨4451570, by rfl⟩ : syracuseStep 5935427 = 8903141) B8903141
theorem B601954733 : Blo 1040609 601954733 := bstep (se 3 (by rfl) ⟨112866512, by rfl⟩ : syracuseStep 601954733 = 225733025) B225733025
theorem B1251995 : Blo 1040609 1251995 := bstep (se 1 (by rfl) ⟨938996, by rfl⟩ : syracuseStep 1251995 = 1877993) B1877993
theorem B5937887 : Blo 1040609 5937887 := bstep (se 1 (by rfl) ⟨4453415, by rfl⟩ : syracuseStep 5937887 = 8906831) B8906831
theorem B1252831 : Blo 1040609 1252831 := bstep (se 1 (by rfl) ⟨939623, by rfl⟩ : syracuseStep 1252831 = 1879247) B1879247
theorem B85499671 : Blo 1040609 85499671 := bstep (se 1 (by rfl) ⟨64124753, by rfl⟩ : syracuseStep 85499671 = 128249507) B128249507
theorem B5939027 : Blo 1040609 5939027 := bstep (se 1 (by rfl) ⟨4454270, by rfl⟩ : syracuseStep 5939027 = 8908541) B8908541
theorem B11444141 : Blo 1040609 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B329818189 : Blo 1040609 329818189 := bstep (se 3 (by rfl) ⟨61840910, by rfl⟩ : syracuseStep 329818189 = 123681821) B123681821
theorem B1482889 : Blo 1040609 1482889 := bstep (se 2 (by rfl) ⟨556083, by rfl⟩ : syracuseStep 1482889 = 1112167) B1112167
theorem B1319323 : Blo 1040609 1319323 := bstep (se 1 (by rfl) ⟨989492, by rfl⟩ : syracuseStep 1319323 = 1978985) B1978985
theorem B1484831 : Blo 1040609 1484831 := bstep (se 1 (by rfl) ⟨1113623, by rfl⟩ : syracuseStep 1484831 = 2227247) B2227247
theorem B5941511 : Blo 1040609 5941511 := bstep (se 1 (by rfl) ⟨4456133, by rfl⟩ : syracuseStep 5941511 = 8912267) B8912267
theorem B2500895 : Blo 1040609 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B20032919 : Blo 1040609 20032919 := bstep (se 1 (by rfl) ⟨15024689, by rfl⟩ : syracuseStep 20032919 = 30049379) B30049379
theorem B1487263 : Blo 1040609 1487263 := bstep (se 1 (by rfl) ⟨1115447, by rfl⟩ : syracuseStep 1487263 = 2230895) B2230895
theorem B3519287 : Blo 1040609 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B42775465 : Blo 1040609 42775465 := bstep (se 2 (by rfl) ⟨16040799, by rfl⟩ : syracuseStep 42775465 = 32081599) B32081599
theorem B3520367 : Blo 1040609 3520367 := bstep (se 1 (by rfl) ⟨2640275, by rfl⟩ : syracuseStep 3520367 = 5280551) B5280551
theorem B1980443 : Blo 1040609 1980443 := bstep (se 1 (by rfl) ⟨1485332, by rfl⟩ : syracuseStep 1980443 = 2970665) B2970665
theorem B1587367 : Blo 1040609 1587367 := bstep (se 1 (by rfl) ⟨1190525, by rfl⟩ : syracuseStep 1587367 = 2381051) B2381051
theorem B10009079 : Blo 1040609 10009079 := bstep (se 1 (by rfl) ⟨7506809, by rfl⟩ : syracuseStep 10009079 = 15013619) B15013619
theorem B7912079 : Blo 1040609 7912079 := bstep (se 1 (by rfl) ⟨5934059, by rfl⟩ : syracuseStep 7912079 = 11868119) B11868119
theorem B2636783 : Blo 1040609 2636783 := bstep (se 1 (by rfl) ⟨1977587, by rfl⟩ : syracuseStep 2636783 = 3955175) B3955175
theorem B2342015 : Blo 1040609 2342015 := bstep (se 1 (by rfl) ⟨1756511, by rfl⟩ : syracuseStep 2342015 = 3513023) B3513023
theorem B2965049 : Blo 1040609 2965049 := bstep (se 2 (by rfl) ⟨1111893, by rfl⟩ : syracuseStep 2965049 = 2223787) B2223787
theorem B2342537 : Blo 1040609 2342537 := bstep (se 2 (by rfl) ⟨878451, by rfl⟩ : syracuseStep 2342537 = 1756903) B1756903
theorem B2342555 : Blo 1040609 2342555 := bstep (se 1 (by rfl) ⟨1756916, by rfl⟩ : syracuseStep 2342555 = 3513833) B3513833
theorem B2637593 : Blo 1040609 2637593 := bstep (se 2 (by rfl) ⟨989097, by rfl⟩ : syracuseStep 2637593 = 1978195) B1978195
theorem B2342825 : Blo 1040609 2342825 := bstep (se 2 (by rfl) ⟨878559, by rfl⟩ : syracuseStep 2342825 = 1757119) B1757119
theorem B2965481 : Blo 1040609 2965481 := bstep (se 2 (by rfl) ⟨1112055, by rfl⟩ : syracuseStep 2965481 = 2224111) B2224111
theorem B3522689 : Blo 1040609 3522689 := bstep (se 2 (by rfl) ⟨1321008, by rfl⟩ : syracuseStep 3522689 = 2642017) B2642017
theorem B3523391 : Blo 1040609 3523391 := bstep (se 1 (by rfl) ⟨2642543, by rfl⟩ : syracuseStep 3523391 = 5285087) B5285087
theorem B2343887 : Blo 1040609 2343887 := bstep (se 1 (by rfl) ⟨1757915, by rfl⟩ : syracuseStep 2343887 = 3515831) B3515831
theorem B2344103 : Blo 1040609 2344103 := bstep (se 1 (by rfl) ⟨1758077, by rfl⟩ : syracuseStep 2344103 = 3516155) B3516155
theorem B5948801 : Blo 1040609 5948801 := bstep (se 2 (by rfl) ⟨2230800, by rfl⟩ : syracuseStep 5948801 = 4461601) B4461601
theorem B8439223 : Blo 1040609 8439223 := bstep (se 1 (by rfl) ⟨6329417, by rfl⟩ : syracuseStep 8439223 = 12658835) B12658835
theorem B2344607 : Blo 1040609 2344607 := bstep (se 1 (by rfl) ⟨1758455, by rfl⟩ : syracuseStep 2344607 = 3516911) B3516911
theorem B3524363 : Blo 1040609 3524363 := bstep (se 1 (by rfl) ⟨2643272, by rfl⟩ : syracuseStep 3524363 = 5286545) B5286545
theorem B144197657 : Blo 1040609 144197657 := bstep (se 2 (by rfl) ⟨54074121, by rfl⟩ : syracuseStep 144197657 = 108148243) B108148243
theorem B2639911 : Blo 1040609 2639911 := bstep (se 1 (by rfl) ⟨1979933, by rfl⟩ : syracuseStep 2639911 = 3959867) B3959867
theorem B2345057 : Blo 1040609 2345057 := bstep (se 2 (by rfl) ⟨879396, by rfl⟩ : syracuseStep 2345057 = 1758793) B1758793
theorem B2640377 : Blo 1040609 2640377 := bstep (se 2 (by rfl) ⟨990141, by rfl⟩ : syracuseStep 2640377 = 1980283) B1980283
theorem B3951119 : Blo 1040609 3951119 := bstep (se 1 (by rfl) ⟨2963339, by rfl⟩ : syracuseStep 3951119 = 5926679) B5926679
theorem B2640539 : Blo 1040609 2640539 := bstep (se 1 (by rfl) ⟨1980404, by rfl⟩ : syracuseStep 2640539 = 3960809) B3960809
theorem B38620097 : Blo 1040609 38620097 := bstep (se 2 (by rfl) ⟨14482536, by rfl⟩ : syracuseStep 38620097 = 28965073) B28965073
theorem B1756127 : Blo 1040609 1756127 := bstep (se 1 (by rfl) ⟨1317095, by rfl⟩ : syracuseStep 1756127 = 2634191) B2634191
theorem B2673755 : Blo 1040609 2673755 := bstep (se 1 (by rfl) ⟨2005316, by rfl⟩ : syracuseStep 2673755 = 4010633) B4010633
theorem B2641207 : Blo 1040609 2641207 := bstep (se 1 (by rfl) ⟨1980905, by rfl⟩ : syracuseStep 2641207 = 3961811) B3961811
theorem B2641319 : Blo 1040609 2641319 := bstep (se 1 (by rfl) ⟨1980989, by rfl⟩ : syracuseStep 2641319 = 3961979) B3961979
theorem B17845919 : Blo 1040609 17845919 := bstep (se 1 (by rfl) ⟨13384439, by rfl⟩ : syracuseStep 17845919 = 26768879) B26768879
theorem B2969423 : Blo 1040609 2969423 := bstep (se 1 (by rfl) ⟨2227067, by rfl⟩ : syracuseStep 2969423 = 4454135) B4454135
theorem B2347091 : Blo 1040609 2347091 := bstep (se 1 (by rfl) ⟨1760318, by rfl⟩ : syracuseStep 2347091 = 3520637) B3520637
theorem B2347199 : Blo 1040609 2347199 := bstep (se 1 (by rfl) ⟨1760399, by rfl⟩ : syracuseStep 2347199 = 3520799) B3520799
theorem B2642159 : Blo 1040609 2642159 := bstep (se 1 (by rfl) ⟨1981619, by rfl⟩ : syracuseStep 2642159 = 3963239) B3963239
theorem B2347433 : Blo 1040609 2347433 := bstep (se 2 (by rfl) ⟨880287, by rfl⟩ : syracuseStep 2347433 = 1760575) B1760575
theorem B10703555 : Blo 1040609 10703555 := bstep (se 1 (by rfl) ⟨8027666, by rfl⟩ : syracuseStep 10703555 = 16055333) B16055333
theorem B1561307 : Blo 1040609 1561307 := bstep (se 1 (by rfl) ⟨1170980, by rfl⟩ : syracuseStep 1561307 = 2341961) B2341961
theorem B27055133 : Blo 1040609 27055133 := bstep (se 3 (by rfl) ⟨5072837, by rfl⟩ : syracuseStep 27055133 = 10145675) B10145675
theorem B2348135 : Blo 1040609 2348135 := bstep (se 1 (by rfl) ⟨1761101, by rfl⟩ : syracuseStep 2348135 = 3522203) B3522203
theorem B1561721 : Blo 1040609 1561721 := bstep (se 2 (by rfl) ⟨585645, by rfl⟩ : syracuseStep 1561721 = 1171291) B1171291
theorem B1561769 : Blo 1040609 1561769 := bstep (se 2 (by rfl) ⟨585663, by rfl⟩ : syracuseStep 1561769 = 1171327) B1171327
theorem B3757225 : Blo 1040609 3757225 := bstep (se 2 (by rfl) ⟨1408959, by rfl⟩ : syracuseStep 3757225 = 2817919) B2817919
theorem B2643151 : Blo 1040609 2643151 := bstep (se 1 (by rfl) ⟨1982363, by rfl⟩ : syracuseStep 2643151 = 3964727) B3964727
theorem B2643455 : Blo 1040609 2643455 := bstep (se 1 (by rfl) ⟨1982591, by rfl⟩ : syracuseStep 2643455 = 3965183) B3965183
theorem B2643475 : Blo 1040609 2643475 := bstep (se 1 (by rfl) ⟨1982606, by rfl⟩ : syracuseStep 2643475 = 3965213) B3965213
theorem B1562495 : Blo 1040609 1562495 := bstep (se 1 (by rfl) ⟨1171871, by rfl⟩ : syracuseStep 1562495 = 2343743) B2343743
theorem B1759259 : Blo 1040609 1759259 := bstep (se 1 (by rfl) ⟨1319444, by rfl⟩ : syracuseStep 1759259 = 2638889) B2638889
theorem B1562807 : Blo 1040609 1562807 := bstep (se 1 (by rfl) ⟨1172105, by rfl⟩ : syracuseStep 1562807 = 2344211) B2344211
theorem B2349359 : Blo 1040609 2349359 := bstep (se 1 (by rfl) ⟨1762019, by rfl⟩ : syracuseStep 2349359 = 3524039) B3524039
theorem B2349503 : Blo 1040609 2349503 := bstep (se 1 (by rfl) ⟨1762127, by rfl⟩ : syracuseStep 2349503 = 3524255) B3524255
theorem B8018621 : Blo 1040609 8018621 := bstep (se 3 (by rfl) ⟨1503491, by rfl⟩ : syracuseStep 8018621 = 3006983) B3006983
theorem B1072123 : Blo 1040609 1072123 := bstep (se 1 (by rfl) ⟨804092, by rfl⟩ : syracuseStep 1072123 = 1608185) B1608185
theorem B1563959 : Blo 1040609 1563959 := bstep (se 1 (by rfl) ⟨1172969, by rfl⟩ : syracuseStep 1563959 = 2345939) B2345939
theorem B8019535 : Blo 1040609 8019535 := bstep (se 1 (by rfl) ⟨6014651, by rfl⟩ : syracuseStep 8019535 = 12029303) B12029303
theorem B2973341 : Blo 1040609 2973341 := bstep (se 3 (by rfl) ⟨557501, by rfl⟩ : syracuseStep 2973341 = 1115003) B1115003
theorem B1564343 : Blo 1040609 1564343 := bstep (se 1 (by rfl) ⟨1173257, by rfl⟩ : syracuseStep 1564343 = 2346515) B2346515
theorem B1761223 : Blo 1040609 1761223 := bstep (se 1 (by rfl) ⟨1320917, by rfl⟩ : syracuseStep 1761223 = 2641835) B2641835
theorem B10150049 : Blo 1040609 10150049 := bstep (se 2 (by rfl) ⟨3806268, by rfl⟩ : syracuseStep 10150049 = 7612537) B7612537
theorem B1564847 : Blo 1040609 1564847 := bstep (se 1 (by rfl) ⟨1173635, by rfl⟩ : syracuseStep 1564847 = 2347271) B2347271
theorem B1564895 : Blo 1040609 1564895 := bstep (se 1 (by rfl) ⟨1173671, by rfl⟩ : syracuseStep 1564895 = 2347343) B2347343
theorem B1040635 : Blo 1040609 1040635 := bstep (se 1 (by rfl) ⟨780476, by rfl⟩ : syracuseStep 1040635 = 1560953) B1560953
theorem B22569293 : Blo 1040609 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B1171867 : Blo 1040609 1171867 := bstep (se 1 (by rfl) ⟨878900, by rfl⟩ : syracuseStep 1171867 = 1757801) B1757801
theorem B1040831 : Blo 1040609 1040831 := bstep (se 1 (by rfl) ⟨780623, by rfl⟩ : syracuseStep 1040831 = 1561247) B1561247
theorem B7627385 : Blo 1040609 7627385 := bstep (se 2 (by rfl) ⟨2860269, by rfl⟩ : syracuseStep 7627385 = 5720539) B5720539
theorem B1041051 : Blo 1040609 1041051 := bstep (se 1 (by rfl) ⟨780788, by rfl⟩ : syracuseStep 1041051 = 1561577) B1561577
theorem B1565339 : Blo 1040609 1565339 := bstep (se 1 (by rfl) ⟨1174004, by rfl⟩ : syracuseStep 1565339 = 2348009) B2348009
theorem B3957407 : Blo 1040609 3957407 := bstep (se 1 (by rfl) ⟨2968055, by rfl⟩ : syracuseStep 3957407 = 5936111) B5936111
theorem B1041087 : Blo 1040609 1041087 := bstep (se 1 (by rfl) ⟨780815, by rfl⟩ : syracuseStep 1041087 = 1561631) B1561631
theorem B1565375 : Blo 1040609 1565375 := bstep (se 1 (by rfl) ⟨1174031, by rfl⟩ : syracuseStep 1565375 = 2348063) B2348063
theorem B1041279 : Blo 1040609 1041279 := bstep (se 1 (by rfl) ⟨780959, by rfl⟩ : syracuseStep 1041279 = 1561919) B1561919
theorem B1565567 : Blo 1040609 1565567 := bstep (se 1 (by rfl) ⟨1174175, by rfl⟩ : syracuseStep 1565567 = 2348351) B2348351
theorem B67659083 : Blo 1040609 67659083 := bstep (se 1 (by rfl) ⟨50744312, by rfl⟩ : syracuseStep 67659083 = 101488625) B101488625
theorem B8578385 : Blo 1040609 8578385 := bstep (se 2 (by rfl) ⟨3216894, by rfl⟩ : syracuseStep 8578385 = 6433789) B6433789
theorem B1566191 : Blo 1040609 1566191 := bstep (se 1 (by rfl) ⟨1174643, by rfl⟩ : syracuseStep 1566191 = 2349287) B2349287
theorem B1043035 : Blo 1040609 1043035 := bstep (se 1 (by rfl) ⟨782276, by rfl⟩ : syracuseStep 1043035 = 1564553) B1564553
theorem B5270183 : Blo 1040609 5270183 := bstep (se 1 (by rfl) ⟨3952637, by rfl⟩ : syracuseStep 5270183 = 7905275) B7905275
theorem B1043135 : Blo 1040609 1043135 := bstep (se 1 (by rfl) ⟨782351, by rfl⟩ : syracuseStep 1043135 = 1564703) B1564703
theorem B1043391 : Blo 1040609 1043391 := bstep (se 1 (by rfl) ⟨782543, by rfl⟩ : syracuseStep 1043391 = 1565087) B1565087
theorem B1043547 : Blo 1040609 1043547 := bstep (se 1 (by rfl) ⟨782660, by rfl⟩ : syracuseStep 1043547 = 1565321) B1565321
theorem B1043707 : Blo 1040609 1043707 := bstep (se 1 (by rfl) ⟨782780, by rfl⟩ : syracuseStep 1043707 = 1565561) B1565561
theorem B1043903 : Blo 1040609 1043903 := bstep (se 1 (by rfl) ⟨782927, by rfl⟩ : syracuseStep 1043903 = 1565855) B1565855
theorem B1044123 : Blo 1040609 1044123 := bstep (se 1 (by rfl) ⟨783092, by rfl⟩ : syracuseStep 1044123 = 1566185) B1566185
theorem B1044315 : Blo 1040609 1044315 := bstep (se 1 (by rfl) ⟨783236, by rfl⟩ : syracuseStep 1044315 = 1566473) B1566473
theorem B36138899 : Blo 1040609 36138899 := bstep (se 1 (by rfl) ⟨27104174, by rfl⟩ : syracuseStep 36138899 = 54208349) B54208349
theorem B1044527 : Blo 1040609 1044527 := bstep (se 1 (by rfl) ⟨783395, by rfl⟩ : syracuseStep 1044527 = 1566791) B1566791
theorem B1044591 : Blo 1040609 1044591 := bstep (se 1 (by rfl) ⟨783443, by rfl⟩ : syracuseStep 1044591 = 1566887) B1566887
theorem B5009863 : Blo 1040609 5009863 := bstep (se 1 (by rfl) ⟨3757397, by rfl⟩ : syracuseStep 5009863 = 7514795) B7514795
theorem B5272127 : Blo 1040609 5272127 := bstep (se 1 (by rfl) ⟨3954095, by rfl⟩ : syracuseStep 5272127 = 7908191) B7908191
theorem B11859371 : Blo 1040609 11859371 := bstep (se 1 (by rfl) ⟨8894528, by rfl⟩ : syracuseStep 11859371 = 17789057) B17789057
theorem B5633849 : Blo 1040609 5633849 := bstep (se 2 (by rfl) ⟨2112693, by rfl⟩ : syracuseStep 5633849 = 4225387) B4225387
theorem B1669513 : Blo 1040609 1669513 := bstep (se 2 (by rfl) ⟨626067, by rfl⟩ : syracuseStep 1669513 = 1252135) B1252135
theorem B11435039 : Blo 1040609 11435039 := bstep (se 1 (by rfl) ⟨8576279, by rfl⟩ : syracuseStep 11435039 = 17152559) B17152559
theorem B20315351 : Blo 1040609 20315351 := bstep (se 1 (by rfl) ⟨15236513, by rfl⟩ : syracuseStep 20315351 = 30473027) B30473027
theorem B3964241 : Blo 1040609 3964241 := bstep (se 2 (by rfl) ⟨1486590, by rfl⟩ : syracuseStep 3964241 = 2973181) B2973181
theorem B9633725 : Blo 1040609 9633725 := bstep (se 3 (by rfl) ⟨1806323, by rfl⟩ : syracuseStep 9633725 = 3612647) B3612647
theorem B3964895 : Blo 1040609 3964895 := bstep (se 1 (by rfl) ⟨2973671, by rfl⟩ : syracuseStep 3964895 = 5947343) B5947343
theorem B2818027 : Blo 1040609 2818027 := bstep (se 1 (by rfl) ⟨2113520, by rfl⟩ : syracuseStep 2818027 = 4227041) B4227041
theorem B4457243 : Blo 1040609 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B3965867 : Blo 1040609 3965867 := bstep (se 1 (by rfl) ⟨2974400, by rfl⟩ : syracuseStep 3965867 = 5948801) B5948801
theorem B4458473 : Blo 1040609 4458473 := bstep (se 2 (by rfl) ⟨1671927, by rfl⟩ : syracuseStep 4458473 = 3343855) B3343855
theorem B11897279 : Blo 1040609 11897279 := bstep (se 1 (by rfl) ⟨8922959, by rfl⟩ : syracuseStep 11897279 = 17845919) B17845919
theorem B3172470317 : Blo 1040609 3172470317 := bstep (se 3 (by rfl) ⟨594838184, by rfl⟩ : syracuseStep 3172470317 = 1189676369) B1189676369
theorem B42733433 : Blo 1040609 42733433 := bstep (se 2 (by rfl) ⟨16025037, by rfl⟩ : syracuseStep 42733433 = 32050075) B32050075
theorem B5345747 : Blo 1040609 5345747 := bstep (se 1 (by rfl) ⟨4009310, by rfl⟩ : syracuseStep 5345747 = 8018621) B8018621
theorem B15046195 : Blo 1040609 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B3513455 : Blo 1040609 3513455 := bstep (se 1 (by rfl) ⟨2635091, by rfl⟩ : syracuseStep 3513455 = 5270183) B5270183
theorem B3514751 : Blo 1040609 3514751 := bstep (se 1 (by rfl) ⟨2636063, by rfl⟩ : syracuseStep 3514751 = 5272127) B5272127
theorem B7906247 : Blo 1040609 7906247 := bstep (se 1 (by rfl) ⟨5929685, by rfl⟩ : syracuseStep 7906247 = 11859371) B11859371
theorem B1320295 : Blo 1040609 1320295 := bstep (se 1 (by rfl) ⟨990221, by rfl⟩ : syracuseStep 1320295 = 1980443) B1980443
theorem B10692713 : Blo 1040609 10692713 := bstep (se 2 (by rfl) ⟨4009767, by rfl⟩ : syracuseStep 10692713 = 8019535) B8019535
theorem B13543567 : Blo 1040609 13543567 := bstep (se 1 (by rfl) ⟨10157675, by rfl⟩ : syracuseStep 13543567 = 20315351) B20315351
theorem B1976699 : Blo 1040609 1976699 := bstep (se 1 (by rfl) ⟨1482524, by rfl⟩ : syracuseStep 1976699 = 2965049) B2965049
theorem B1976987 : Blo 1040609 1976987 := bstep (se 1 (by rfl) ⟨1482740, by rfl⟩ : syracuseStep 1976987 = 2965481) B2965481
theorem B439757585 : Blo 1040609 439757585 := bstep (se 2 (by rfl) ⟨164909094, by rfl⟩ : syracuseStep 439757585 = 329818189) B329818189
theorem B1977185 : Blo 1040609 1977185 := bstep (se 2 (by rfl) ⟨741444, by rfl⟩ : syracuseStep 1977185 = 1482889) B1482889
theorem B3517343 : Blo 1040609 3517343 := bstep (se 1 (by rfl) ⟨2638007, by rfl⟩ : syracuseStep 3517343 = 5276015) B5276015
theorem B5287193 : Blo 1040609 5287193 := bstep (se 2 (by rfl) ⟨1982697, by rfl⟩ : syracuseStep 5287193 = 3965395) B3965395
theorem B3518639 : Blo 1040609 3518639 := bstep (se 1 (by rfl) ⟨2638979, by rfl⟩ : syracuseStep 3518639 = 5277959) B5277959
theorem B2634079 : Blo 1040609 2634079 := bstep (se 1 (by rfl) ⟨1975559, by rfl⟩ : syracuseStep 2634079 = 3951119) B3951119
theorem B11252297 : Blo 1040609 11252297 := bstep (se 2 (by rfl) ⟨4219611, by rfl⟩ : syracuseStep 11252297 = 8439223) B8439223
theorem B1782503 : Blo 1040609 1782503 := bstep (se 1 (by rfl) ⟨1336877, by rfl⟩ : syracuseStep 1782503 = 2673755) B2673755
theorem B1979615 : Blo 1040609 1979615 := bstep (se 1 (by rfl) ⟨1484711, by rfl⟩ : syracuseStep 1979615 = 2969423) B2969423
theorem B3519881 : Blo 1040609 3519881 := bstep (se 2 (by rfl) ⟨1319955, by rfl⟩ : syracuseStep 3519881 = 2639911) B2639911
theorem B18036755 : Blo 1040609 18036755 := bstep (se 1 (by rfl) ⟨13527566, by rfl⟩ : syracuseStep 18036755 = 27055133) B27055133
theorem B3521609 : Blo 1040609 3521609 := bstep (se 2 (by rfl) ⟨1320603, by rfl⟩ : syracuseStep 3521609 = 2641207) B2641207
theorem B1982227 : Blo 1040609 1982227 := bstep (se 1 (by rfl) ⟨1486670, by rfl⟩ : syracuseStep 1982227 = 2973341) B2973341
theorem B5717989 : Blo 1040609 5717989 := bstep (se 4 (by rfl) ⟨536061, by rfl⟩ : syracuseStep 5717989 = 1072123) B1072123
theorem B6766699 : Blo 1040609 6766699 := bstep (se 1 (by rfl) ⟨5075024, by rfl⟩ : syracuseStep 6766699 = 10150049) B10150049
theorem B2638271 : Blo 1040609 2638271 := bstep (se 1 (by rfl) ⟨1978703, by rfl⟩ : syracuseStep 2638271 = 3957407) B3957407
theorem B1983017 : Blo 1040609 1983017 := bstep (se 2 (by rfl) ⟨743631, by rfl⟩ : syracuseStep 1983017 = 1487263) B1487263
theorem B6669053 : Blo 1040609 6669053 := bstep (se 3 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 6669053 = 2500895) B2500895
theorem B45106055 : Blo 1040609 45106055 := bstep (se 1 (by rfl) ⟨33829541, by rfl⟩ : syracuseStep 45106055 = 67659083) B67659083
theorem B5718923 : Blo 1040609 5718923 := bstep (se 1 (by rfl) ⟨4289192, by rfl⟩ : syracuseStep 5718923 = 8578385) B8578385
theorem B57033953 : Blo 1040609 57033953 := bstep (se 2 (by rfl) ⟨21387732, by rfl⟩ : syracuseStep 57033953 = 42775465) B42775465
theorem B3524201 : Blo 1040609 3524201 := bstep (se 2 (by rfl) ⟨1321575, by rfl⟩ : syracuseStep 3524201 = 2643151) B2643151
theorem B3524633 : Blo 1040609 3524633 := bstep (se 2 (by rfl) ⟨1321737, by rfl⟩ : syracuseStep 3524633 = 2643475) B2643475
theorem B13355279 : Blo 1040609 13355279 := bstep (se 1 (by rfl) ⟨10016459, by rfl⟩ : syracuseStep 13355279 = 20032919) B20032919
theorem B2116489 : Blo 1040609 2116489 := bstep (se 2 (by rfl) ⟨793683, by rfl⟩ : syracuseStep 2116489 = 1587367) B1587367
theorem B2346191 : Blo 1040609 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B3755899 : Blo 1040609 3755899 := bstep (se 1 (by rfl) ⟨2816924, by rfl⟩ : syracuseStep 3755899 = 5633849) B5633849
theorem B2346911 : Blo 1040609 2346911 := bstep (se 1 (by rfl) ⟨1760183, by rfl⟩ : syracuseStep 2346911 = 3520367) B3520367
theorem B6672719 : Blo 1040609 6672719 := bstep (se 1 (by rfl) ⟨5004539, by rfl⟩ : syracuseStep 6672719 = 10009079) B10009079
theorem B1757855 : Blo 1040609 1757855 := bstep (se 1 (by rfl) ⟨1318391, by rfl⟩ : syracuseStep 1757855 = 2636783) B2636783
theorem B7623359 : Blo 1040609 7623359 := bstep (se 1 (by rfl) ⟨5717519, by rfl⟩ : syracuseStep 7623359 = 11435039) B11435039
theorem B1561343 : Blo 1040609 1561343 := bstep (se 1 (by rfl) ⟨1171007, by rfl⟩ : syracuseStep 1561343 = 2342015) B2342015
theorem B2642827 : Blo 1040609 2642827 := bstep (se 1 (by rfl) ⟨1982120, by rfl⟩ : syracuseStep 2642827 = 3964241) B3964241
theorem B1561691 : Blo 1040609 1561691 := bstep (se 1 (by rfl) ⟨1171268, by rfl⟩ : syracuseStep 1561691 = 2342537) B2342537
theorem B1561703 : Blo 1040609 1561703 := bstep (se 1 (by rfl) ⟨1171277, by rfl⟩ : syracuseStep 1561703 = 2342555) B2342555
theorem B1758395 : Blo 1040609 1758395 := bstep (se 1 (by rfl) ⟨1318796, by rfl⟩ : syracuseStep 1758395 = 2637593) B2637593
theorem B2348297 : Blo 1040609 2348297 := bstep (se 2 (by rfl) ⟨880611, by rfl⟩ : syracuseStep 2348297 = 1761223) B1761223
theorem B1561883 : Blo 1040609 1561883 := bstep (se 1 (by rfl) ⟨1171412, by rfl⟩ : syracuseStep 1561883 = 2342825) B2342825
theorem B3757369 : Blo 1040609 3757369 := bstep (se 2 (by rfl) ⟨1409013, by rfl⟩ : syracuseStep 3757369 = 2818027) B2818027
theorem B2643263 : Blo 1040609 2643263 := bstep (se 1 (by rfl) ⟨1982447, by rfl⟩ : syracuseStep 2643263 = 3964895) B3964895
theorem B2348459 : Blo 1040609 2348459 := bstep (se 1 (by rfl) ⟨1761344, by rfl⟩ : syracuseStep 2348459 = 3522689) B3522689
theorem B1562489 : Blo 1040609 1562489 := bstep (se 2 (by rfl) ⟨585933, by rfl⟩ : syracuseStep 1562489 = 1171867) B1171867
theorem B1759097 : Blo 1040609 1759097 := bstep (se 2 (by rfl) ⟨659661, by rfl⟩ : syracuseStep 1759097 = 1319323) B1319323
theorem B2348927 : Blo 1040609 2348927 := bstep (se 1 (by rfl) ⟨1761695, by rfl⟩ : syracuseStep 2348927 = 3523391) B3523391
theorem B1562591 : Blo 1040609 1562591 := bstep (se 1 (by rfl) ⟨1171943, by rfl⟩ : syracuseStep 1562591 = 2343887) B2343887
theorem B1562735 : Blo 1040609 1562735 := bstep (se 1 (by rfl) ⟨1172051, by rfl⟩ : syracuseStep 1562735 = 2344103) B2344103
theorem B3955007 : Blo 1040609 3955007 := bstep (se 1 (by rfl) ⟨2966255, by rfl⟩ : syracuseStep 3955007 = 5932511) B5932511
theorem B1563071 : Blo 1040609 1563071 := bstep (se 1 (by rfl) ⟨1172303, by rfl⟩ : syracuseStep 1563071 = 2344607) B2344607
theorem B2349575 : Blo 1040609 2349575 := bstep (se 1 (by rfl) ⟨1762181, by rfl⟩ : syracuseStep 2349575 = 3524363) B3524363
theorem B96131771 : Blo 1040609 96131771 := bstep (se 1 (by rfl) ⟨72098828, by rfl⟩ : syracuseStep 96131771 = 144197657) B144197657
theorem B1563371 : Blo 1040609 1563371 := bstep (se 1 (by rfl) ⟨1172528, by rfl⟩ : syracuseStep 1563371 = 2345057) B2345057
theorem B3955463 : Blo 1040609 3955463 := bstep (se 1 (by rfl) ⟨2966597, by rfl⟩ : syracuseStep 3955463 = 5933195) B5933195
theorem B20339693 : Blo 1040609 20339693 := bstep (se 3 (by rfl) ⟨3813692, by rfl⟩ : syracuseStep 20339693 = 7627385) B7627385
theorem B1760251 : Blo 1040609 1760251 := bstep (se 1 (by rfl) ⟨1320188, by rfl⟩ : syracuseStep 1760251 = 2640377) B2640377
theorem B1760359 : Blo 1040609 1760359 := bstep (se 1 (by rfl) ⟨1320269, by rfl⟩ : syracuseStep 1760359 = 2640539) B2640539
theorem B25746731 : Blo 1040609 25746731 := bstep (se 1 (by rfl) ⟨19310048, by rfl⟩ : syracuseStep 25746731 = 38620097) B38620097
theorem B1170751 : Blo 1040609 1170751 := bstep (se 1 (by rfl) ⟨878063, by rfl⟩ : syracuseStep 1170751 = 1756127) B1756127
theorem B2972999 : Blo 1040609 2972999 := bstep (se 1 (by rfl) ⟨2229749, by rfl⟩ : syracuseStep 2972999 = 4459499) B4459499
theorem B1760879 : Blo 1040609 1760879 := bstep (se 1 (by rfl) ⟨1320659, by rfl⟩ : syracuseStep 1760879 = 2641319) B2641319
theorem B1564727 : Blo 1040609 1564727 := bstep (se 1 (by rfl) ⟨1173545, by rfl⟩ : syracuseStep 1564727 = 2347091) B2347091
theorem B1564799 : Blo 1040609 1564799 := bstep (se 1 (by rfl) ⟨1173599, by rfl⟩ : syracuseStep 1564799 = 2347199) B2347199
theorem B1761439 : Blo 1040609 1761439 := bstep (se 1 (by rfl) ⟨1321079, by rfl⟩ : syracuseStep 1761439 = 2642159) B2642159
theorem B3956951 : Blo 1040609 3956951 := bstep (se 1 (by rfl) ⟨2967713, by rfl⟩ : syracuseStep 3956951 = 5935427) B5935427
theorem B1564955 : Blo 1040609 1564955 := bstep (se 1 (by rfl) ⟨1173716, by rfl⟩ : syracuseStep 1564955 = 2347433) B2347433
theorem B7135703 : Blo 1040609 7135703 := bstep (se 1 (by rfl) ⟨5351777, by rfl⟩ : syracuseStep 7135703 = 10703555) B10703555
theorem B1040871 : Blo 1040609 1040871 := bstep (se 1 (by rfl) ⟨780653, by rfl⟩ : syracuseStep 1040871 = 1561307) B1561307
theorem B1565423 : Blo 1040609 1565423 := bstep (se 1 (by rfl) ⟨1174067, by rfl⟩ : syracuseStep 1565423 = 2348135) B2348135
theorem B1041147 : Blo 1040609 1041147 := bstep (se 1 (by rfl) ⟨780860, by rfl⟩ : syracuseStep 1041147 = 1561721) B1561721
theorem B1041179 : Blo 1040609 1041179 := bstep (se 1 (by rfl) ⟨780884, by rfl⟩ : syracuseStep 1041179 = 1561769) B1561769
theorem B1762303 : Blo 1040609 1762303 := bstep (se 1 (by rfl) ⟨1321727, by rfl⟩ : syracuseStep 1762303 = 2643455) B2643455
theorem B1041663 : Blo 1040609 1041663 := bstep (se 1 (by rfl) ⟨781247, by rfl⟩ : syracuseStep 1041663 = 1562495) B1562495
theorem B1172839 : Blo 1040609 1172839 := bstep (se 1 (by rfl) ⟨879629, by rfl⟩ : syracuseStep 1172839 = 1759259) B1759259
theorem B1041871 : Blo 1040609 1041871 := bstep (se 1 (by rfl) ⟨781403, by rfl⟩ : syracuseStep 1041871 = 1562807) B1562807
theorem B1566239 : Blo 1040609 1566239 := bstep (se 1 (by rfl) ⟨1174679, by rfl⟩ : syracuseStep 1566239 = 2349359) B2349359
theorem B401303155 : Blo 1040609 401303155 := bstep (se 1 (by rfl) ⟨300977366, by rfl⟩ : syracuseStep 401303155 = 601954733) B601954733
theorem B1566335 : Blo 1040609 1566335 := bstep (se 1 (by rfl) ⟨1174751, by rfl⟩ : syracuseStep 1566335 = 2349503) B2349503
theorem B3958591 : Blo 1040609 3958591 := bstep (se 1 (by rfl) ⟨2968943, by rfl⟩ : syracuseStep 3958591 = 5937887) B5937887
theorem B1042639 : Blo 1040609 1042639 := bstep (se 1 (by rfl) ⟨781979, by rfl⟩ : syracuseStep 1042639 = 1563959) B1563959
theorem B1042895 : Blo 1040609 1042895 := bstep (se 1 (by rfl) ⟨782171, by rfl⟩ : syracuseStep 1042895 = 1564343) B1564343
theorem B3959351 : Blo 1040609 3959351 := bstep (se 1 (by rfl) ⟨2969513, by rfl⟩ : syracuseStep 3959351 = 5939027) B5939027
theorem B7629427 : Blo 1040609 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B3959549 : Blo 1040609 3959549 := bstep (se 3 (by rfl) ⟨742415, by rfl⟩ : syracuseStep 3959549 = 1484831) B1484831
theorem B1043231 : Blo 1040609 1043231 := bstep (se 1 (by rfl) ⟨782423, by rfl⟩ : syracuseStep 1043231 = 1564847) B1564847
theorem B1043263 : Blo 1040609 1043263 := bstep (se 1 (by rfl) ⟨782447, by rfl⟩ : syracuseStep 1043263 = 1564895) B1564895
theorem B1043559 : Blo 1040609 1043559 := bstep (se 1 (by rfl) ⟨782669, by rfl⟩ : syracuseStep 1043559 = 1565339) B1565339
theorem B1043583 : Blo 1040609 1043583 := bstep (se 1 (by rfl) ⟨782687, by rfl⟩ : syracuseStep 1043583 = 1565375) B1565375
theorem B1043711 : Blo 1040609 1043711 := bstep (se 1 (by rfl) ⟨782783, by rfl⟩ : syracuseStep 1043711 = 1565567) B1565567
theorem B6679817 : Blo 1040609 6679817 := bstep (se 2 (by rfl) ⟨2504931, by rfl⟩ : syracuseStep 6679817 = 5009863) B5009863
theorem B1044127 : Blo 1040609 1044127 := bstep (se 1 (by rfl) ⟨783095, by rfl⟩ : syracuseStep 1044127 = 1566191) B1566191
theorem B3961007 : Blo 1040609 3961007 := bstep (se 1 (by rfl) ⟨2970755, by rfl⟩ : syracuseStep 3961007 = 5941511) B5941511
theorem B5009633 : Blo 1040609 5009633 := bstep (se 2 (by rfl) ⟨1878612, by rfl⟩ : syracuseStep 5009633 = 3757225) B3757225
theorem B3338653 : Blo 1040609 3338653 := bstep (se 3 (by rfl) ⟨625997, by rfl⟩ : syracuseStep 3338653 = 1251995) B1251995
theorem B2226017 : Blo 1040609 2226017 := bstep (se 2 (by rfl) ⟨834756, by rfl⟩ : syracuseStep 2226017 = 1669513) B1669513
theorem B5274719 : Blo 1040609 5274719 := bstep (se 1 (by rfl) ⟨3956039, by rfl⟩ : syracuseStep 5274719 = 7912079) B7912079
theorem B1670441 : Blo 1040609 1670441 := bstep (se 2 (by rfl) ⟨626415, by rfl⟩ : syracuseStep 1670441 = 1252831) B1252831
theorem B113999561 : Blo 1040609 113999561 := bstep (se 2 (by rfl) ⟨42749835, by rfl⟩ : syracuseStep 113999561 = 85499671) B85499671
theorem B96370397 : Blo 1040609 96370397 := bstep (se 3 (by rfl) ⟨18069449, by rfl⟩ : syracuseStep 96370397 = 36138899) B36138899
theorem B6422483 : Blo 1040609 6422483 := bstep (se 1 (by rfl) ⟨4816862, by rfl⟩ : syracuseStep 6422483 = 9633725) B9633725
theorem B7931519 : Blo 1040609 7931519 := bstep (se 1 (by rfl) ⟨5948639, by rfl⟩ : syracuseStep 7931519 = 11897279) B11897279
theorem B535070873 : Blo 1040609 535070873 := bstep (se 2 (by rfl) ⟨200651577, by rfl⟩ : syracuseStep 535070873 = 401303155) B401303155
theorem B2114980211 : Blo 1040609 2114980211 := bstep (se 1 (by rfl) ⟨1586235158, by rfl⟩ : syracuseStep 2114980211 = 3172470317) B3172470317
theorem B5278121 : Blo 1040609 5278121 := bstep (se 2 (by rfl) ⟨1979295, by rfl⟩ : syracuseStep 5278121 = 3958591) B3958591
theorem B5082239 : Blo 1040609 5082239 := bstep (se 1 (by rfl) ⟨3811679, by rfl⟩ : syracuseStep 5082239 = 7623359) B7623359
theorem B2821985 : Blo 1040609 2821985 := bstep (se 2 (by rfl) ⟨1058244, by rfl⟩ : syracuseStep 2821985 = 2116489) B2116489
theorem B28513901 : Blo 1040609 28513901 := bstep (se 3 (by rfl) ⟨5346356, by rfl⟩ : syracuseStep 28513901 = 10692713) B10692713
theorem B4757135 : Blo 1040609 4757135 := bstep (se 1 (by rfl) ⟨3567851, by rfl⟩ : syracuseStep 4757135 = 7135703) B7135703
theorem B3512105 : Blo 1040609 3512105 := bstep (se 2 (by rfl) ⟨1317039, by rfl⟩ : syracuseStep 3512105 = 2634079) B2634079
theorem B1317799 : Blo 1040609 1317799 := bstep (se 1 (by rfl) ⟨988349, by rfl⟩ : syracuseStep 1317799 = 1976699) B1976699
theorem B1318123 : Blo 1040609 1318123 := bstep (se 1 (by rfl) ⟨988592, by rfl⟩ : syracuseStep 1318123 = 1977185) B1977185
theorem B20061593 : Blo 1040609 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B1188335 : Blo 1040609 1188335 := bstep (se 1 (by rfl) ⟨891251, by rfl⟩ : syracuseStep 1188335 = 1782503) B1782503
theorem B1319743 : Blo 1040609 1319743 := bstep (se 1 (by rfl) ⟨989807, by rfl⟩ : syracuseStep 1319743 = 1979615) B1979615
theorem B1484011 : Blo 1040609 1484011 := bstep (se 1 (by rfl) ⟨1113008, by rfl⟩ : syracuseStep 1484011 = 2226017) B2226017
theorem B3516479 : Blo 1040609 3516479 := bstep (se 1 (by rfl) ⟨2637359, by rfl⟩ : syracuseStep 3516479 = 5274719) B5274719
theorem B75999707 : Blo 1040609 75999707 := bstep (se 1 (by rfl) ⟨56999780, by rfl⟩ : syracuseStep 75999707 = 113999561) B113999561
theorem B9022265 : Blo 1040609 9022265 := bstep (se 2 (by rfl) ⟨3383349, by rfl⟩ : syracuseStep 9022265 = 6766699) B6766699
theorem B1322011 : Blo 1040609 1322011 := bstep (se 1 (by rfl) ⟨991508, by rfl⟩ : syracuseStep 1322011 = 1983017) B1983017
theorem B3812615 : Blo 1040609 3812615 := bstep (se 1 (by rfl) ⟨2859461, by rfl⟩ : syracuseStep 3812615 = 5718923) B5718923
theorem B72232357 : Blo 1040609 72232357 := bstep (se 4 (by rfl) ⟨6771783, by rfl⟩ : syracuseStep 72232357 = 13543567) B13543567
theorem B38022635 : Blo 1040609 38022635 := bstep (se 1 (by rfl) ⟨28516976, by rfl⟩ : syracuseStep 38022635 = 57033953) B57033953
theorem B28488955 : Blo 1040609 28488955 := bstep (se 1 (by rfl) ⟨21366716, by rfl⟩ : syracuseStep 28488955 = 42733433) B42733433
theorem B10172569 : Blo 1040609 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B2636671 : Blo 1040609 2636671 := bstep (se 1 (by rfl) ⟨1977503, by rfl⟩ : syracuseStep 2636671 = 3955007) B3955007
theorem B2636975 : Blo 1040609 2636975 := bstep (se 1 (by rfl) ⟨1977731, by rfl⟩ : syracuseStep 2636975 = 3955463) B3955463
theorem B2342303 : Blo 1040609 2342303 := bstep (se 1 (by rfl) ⟨1756727, by rfl⟩ : syracuseStep 2342303 = 3513455) B3513455
theorem B1981999 : Blo 1040609 1981999 := bstep (se 1 (by rfl) ⟨1486499, by rfl⟩ : syracuseStep 1981999 = 2972999) B2972999
theorem B2637967 : Blo 1040609 2637967 := bstep (se 1 (by rfl) ⟨1978475, by rfl⟩ : syracuseStep 2637967 = 3956951) B3956951
theorem B2343167 : Blo 1040609 2343167 := bstep (se 1 (by rfl) ⟨1757375, by rfl⟩ : syracuseStep 2343167 = 3514751) B3514751
theorem B3523769 : Blo 1040609 3523769 := bstep (se 2 (by rfl) ⟨1321413, by rfl⟩ : syracuseStep 3523769 = 2642827) B2642827
theorem B2639567 : Blo 1040609 2639567 := bstep (se 1 (by rfl) ⟨1979675, by rfl⟩ : syracuseStep 2639567 = 3959351) B3959351
theorem B2639699 : Blo 1040609 2639699 := bstep (se 1 (by rfl) ⟨1979774, by rfl⟩ : syracuseStep 2639699 = 3959549) B3959549
theorem B2344895 : Blo 1040609 2344895 := bstep (se 1 (by rfl) ⟨1758671, by rfl⟩ : syracuseStep 2344895 = 3517343) B3517343
theorem B3524795 : Blo 1040609 3524795 := bstep (se 1 (by rfl) ⟨2643596, by rfl⟩ : syracuseStep 3524795 = 5287193) B5287193
theorem B2345759 : Blo 1040609 2345759 := bstep (se 1 (by rfl) ⟨1759319, by rfl⟩ : syracuseStep 2345759 = 3518639) B3518639
theorem B2640671 : Blo 1040609 2640671 := bstep (se 1 (by rfl) ⟨1980503, by rfl⟩ : syracuseStep 2640671 = 3961007) B3961007
theorem B2346587 : Blo 1040609 2346587 := bstep (se 1 (by rfl) ⟨1759940, by rfl⟩ : syracuseStep 2346587 = 3519881) B3519881
theorem B2347001 : Blo 1040609 2347001 := bstep (se 2 (by rfl) ⟨880125, by rfl⟩ : syracuseStep 2347001 = 1760251) B1760251
theorem B2347145 : Blo 1040609 2347145 := bstep (se 2 (by rfl) ⟨880179, by rfl⟩ : syracuseStep 2347145 = 1760359) B1760359
theorem B1561001 : Blo 1040609 1561001 := bstep (se 2 (by rfl) ⟨585375, by rfl⟩ : syracuseStep 1561001 = 1170751) B1170751
theorem B2347739 : Blo 1040609 2347739 := bstep (se 1 (by rfl) ⟨1760804, by rfl⟩ : syracuseStep 2347739 = 3521609) B3521609
theorem B2642969 : Blo 1040609 2642969 := bstep (se 2 (by rfl) ⟨991113, by rfl⟩ : syracuseStep 2642969 = 1982227) B1982227
theorem B64246931 : Blo 1040609 64246931 := bstep (se 1 (by rfl) ⟨48185198, by rfl⟩ : syracuseStep 64246931 = 96370397) B96370397
theorem B7623985 : Blo 1040609 7623985 := bstep (se 2 (by rfl) ⟨2858994, by rfl⟩ : syracuseStep 7623985 = 5717989) B5717989
theorem B4281655 : Blo 1040609 4281655 := bstep (se 1 (by rfl) ⟨3211241, by rfl⟩ : syracuseStep 4281655 = 6422483) B6422483
theorem B2348585 : Blo 1040609 2348585 := bstep (se 2 (by rfl) ⟨880719, by rfl⟩ : syracuseStep 2348585 = 1761439) B1761439
theorem B1758847 : Blo 1040609 1758847 := bstep (se 1 (by rfl) ⟨1319135, by rfl⟩ : syracuseStep 1758847 = 2638271) B2638271
theorem B4446035 : Blo 1040609 4446035 := bstep (se 1 (by rfl) ⟨3334526, by rfl⟩ : syracuseStep 4446035 = 6669053) B6669053
theorem B2971495 : Blo 1040609 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B30070703 : Blo 1040609 30070703 := bstep (se 1 (by rfl) ⟨22553027, by rfl⟩ : syracuseStep 30070703 = 45106055) B45106055
theorem B2643911 : Blo 1040609 2643911 := bstep (se 1 (by rfl) ⟨1982933, by rfl⟩ : syracuseStep 2643911 = 3965867) B3965867
theorem B2349467 : Blo 1040609 2349467 := bstep (se 1 (by rfl) ⟨1762100, by rfl⟩ : syracuseStep 2349467 = 3524201) B3524201
theorem B2972315 : Blo 1040609 2972315 := bstep (se 1 (by rfl) ⟨2229236, by rfl⟩ : syracuseStep 2972315 = 4458473) B4458473
theorem B2349737 : Blo 1040609 2349737 := bstep (se 2 (by rfl) ⟨881151, by rfl⟩ : syracuseStep 2349737 = 1762303) B1762303
theorem B2349755 : Blo 1040609 2349755 := bstep (se 1 (by rfl) ⟨1762316, by rfl⟩ : syracuseStep 2349755 = 3524633) B3524633
theorem B8903519 : Blo 1040609 8903519 := bstep (se 1 (by rfl) ⟨6677639, by rfl⟩ : syracuseStep 8903519 = 13355279) B13355279
theorem B1563785 : Blo 1040609 1563785 := bstep (se 2 (by rfl) ⟨586419, by rfl⟩ : syracuseStep 1563785 = 1172839) B1172839
theorem B1760393 : Blo 1040609 1760393 := bstep (se 2 (by rfl) ⟨660147, by rfl⟩ : syracuseStep 1760393 = 1320295) B1320295
theorem B1564127 : Blo 1040609 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B1564607 : Blo 1040609 1564607 := bstep (se 1 (by rfl) ⟨1173455, by rfl⟩ : syracuseStep 1564607 = 2346911) B2346911
theorem B4448479 : Blo 1040609 4448479 := bstep (se 1 (by rfl) ⟨3336359, by rfl⟩ : syracuseStep 4448479 = 6672719) B6672719
theorem B3563831 : Blo 1040609 3563831 := bstep (se 1 (by rfl) ⟨2672873, by rfl⟩ : syracuseStep 3563831 = 5345747) B5345747
theorem B1171903 : Blo 1040609 1171903 := bstep (se 1 (by rfl) ⟨878927, by rfl⟩ : syracuseStep 1171903 = 1757855) B1757855
theorem B1040895 : Blo 1040609 1040895 := bstep (se 1 (by rfl) ⟨780671, by rfl⟩ : syracuseStep 1040895 = 1561343) B1561343
theorem B1041127 : Blo 1040609 1041127 := bstep (se 1 (by rfl) ⟨780845, by rfl⟩ : syracuseStep 1041127 = 1561691) B1561691
theorem B1041135 : Blo 1040609 1041135 := bstep (se 1 (by rfl) ⟨780851, by rfl⟩ : syracuseStep 1041135 = 1561703) B1561703
theorem B1172263 : Blo 1040609 1172263 := bstep (se 1 (by rfl) ⟨879197, by rfl⟩ : syracuseStep 1172263 = 1758395) B1758395
theorem B1565531 : Blo 1040609 1565531 := bstep (se 1 (by rfl) ⟨1174148, by rfl⟩ : syracuseStep 1565531 = 2348297) B2348297
theorem B1041255 : Blo 1040609 1041255 := bstep (se 1 (by rfl) ⟨780941, by rfl⟩ : syracuseStep 1041255 = 1561883) B1561883
theorem B1762175 : Blo 1040609 1762175 := bstep (se 1 (by rfl) ⟨1321631, by rfl⟩ : syracuseStep 1762175 = 2643263) B2643263
theorem B1565639 : Blo 1040609 1565639 := bstep (se 1 (by rfl) ⟨1174229, by rfl⟩ : syracuseStep 1565639 = 2348459) B2348459
theorem B1041659 : Blo 1040609 1041659 := bstep (se 1 (by rfl) ⟨781244, by rfl⟩ : syracuseStep 1041659 = 1562489) B1562489
theorem B1172731 : Blo 1040609 1172731 := bstep (se 1 (by rfl) ⟨879548, by rfl⟩ : syracuseStep 1172731 = 1759097) B1759097
theorem B1565951 : Blo 1040609 1565951 := bstep (se 1 (by rfl) ⟨1174463, by rfl⟩ : syracuseStep 1565951 = 2348927) B2348927
theorem B1041727 : Blo 1040609 1041727 := bstep (se 1 (by rfl) ⟨781295, by rfl⟩ : syracuseStep 1041727 = 1562591) B1562591
theorem B1041823 : Blo 1040609 1041823 := bstep (se 1 (by rfl) ⟨781367, by rfl⟩ : syracuseStep 1041823 = 1562735) B1562735
theorem B1042047 : Blo 1040609 1042047 := bstep (se 1 (by rfl) ⟨781535, by rfl⟩ : syracuseStep 1042047 = 1563071) B1563071
theorem B1566383 : Blo 1040609 1566383 := bstep (se 1 (by rfl) ⟨1174787, by rfl⟩ : syracuseStep 1566383 = 2349575) B2349575
theorem B64087847 : Blo 1040609 64087847 := bstep (se 1 (by rfl) ⟨48065885, by rfl⟩ : syracuseStep 64087847 = 96131771) B96131771
theorem B1042247 : Blo 1040609 1042247 := bstep (se 1 (by rfl) ⟨781685, by rfl⟩ : syracuseStep 1042247 = 1563371) B1563371
theorem B13559795 : Blo 1040609 13559795 := bstep (se 1 (by rfl) ⟨10169846, by rfl⟩ : syracuseStep 13559795 = 20339693) B20339693
theorem B17164487 : Blo 1040609 17164487 := bstep (se 1 (by rfl) ⟨12873365, by rfl⟩ : syracuseStep 17164487 = 25746731) B25746731
theorem B1173919 : Blo 1040609 1173919 := bstep (se 1 (by rfl) ⟨880439, by rfl⟩ : syracuseStep 1173919 = 1760879) B1760879
theorem B5007865 : Blo 1040609 5007865 := bstep (se 2 (by rfl) ⟨1877949, by rfl⟩ : syracuseStep 5007865 = 3755899) B3755899
theorem B1043151 : Blo 1040609 1043151 := bstep (se 1 (by rfl) ⟨782363, by rfl⟩ : syracuseStep 1043151 = 1564727) B1564727
theorem B1043199 : Blo 1040609 1043199 := bstep (se 1 (by rfl) ⟨782399, by rfl⟩ : syracuseStep 1043199 = 1564799) B1564799
theorem B1043303 : Blo 1040609 1043303 := bstep (se 1 (by rfl) ⟨782477, by rfl⟩ : syracuseStep 1043303 = 1564955) B1564955
theorem B1043615 : Blo 1040609 1043615 := bstep (se 1 (by rfl) ⟨782711, by rfl⟩ : syracuseStep 1043615 = 1565423) B1565423
theorem B4451537 : Blo 1040609 4451537 := bstep (se 2 (by rfl) ⟨1669326, by rfl⟩ : syracuseStep 4451537 = 3338653) B3338653
theorem B5270831 : Blo 1040609 5270831 := bstep (se 1 (by rfl) ⟨3953123, by rfl⟩ : syracuseStep 5270831 = 7906247) B7906247
theorem B1044159 : Blo 1040609 1044159 := bstep (se 1 (by rfl) ⟨783119, by rfl⟩ : syracuseStep 1044159 = 1566239) B1566239
theorem B1044223 : Blo 1040609 1044223 := bstep (se 1 (by rfl) ⟨783167, by rfl⟩ : syracuseStep 1044223 = 1566335) B1566335
theorem B5271965 : Blo 1040609 5271965 := bstep (se 3 (by rfl) ⟨988493, by rfl⟩ : syracuseStep 5271965 = 1976987) B1976987
theorem B5009825 : Blo 1040609 5009825 := bstep (se 2 (by rfl) ⟨1878684, by rfl⟩ : syracuseStep 5009825 = 3757369) B3757369
theorem B293171723 : Blo 1040609 293171723 := bstep (se 1 (by rfl) ⟨219878792, by rfl⟩ : syracuseStep 293171723 = 439757585) B439757585
theorem B4453211 : Blo 1040609 4453211 := bstep (se 1 (by rfl) ⟨3339908, by rfl⟩ : syracuseStep 4453211 = 6679817) B6679817
theorem B3339755 : Blo 1040609 3339755 := bstep (se 1 (by rfl) ⟨2504816, by rfl⟩ : syracuseStep 3339755 = 5009633) B5009633
theorem B7501531 : Blo 1040609 7501531 := bstep (se 1 (by rfl) ⟨5626148, by rfl⟩ : syracuseStep 7501531 = 11252297) B11252297
theorem B4454509 : Blo 1040609 4454509 := bstep (se 3 (by rfl) ⟨835220, by rfl⟩ : syracuseStep 4454509 = 1670441) B1670441
theorem B12024503 : Blo 1040609 12024503 := bstep (se 1 (by rfl) ⟨9018377, by rfl⟩ : syracuseStep 12024503 = 18036755) B18036755
theorem B5931305 : Blo 1040609 5931305 := bstep (se 2 (by rfl) ⟨2224239, by rfl⟩ : syracuseStep 5931305 = 4448479) B4448479
theorem B42831287 : Blo 1040609 42831287 := bstep (se 1 (by rfl) ⟨32123465, by rfl⟩ : syracuseStep 42831287 = 64246931) B64246931
theorem B96309809 : Blo 1040609 96309809 := bstep (se 2 (by rfl) ⟨36116178, by rfl⟩ : syracuseStep 96309809 = 72232357) B72232357
theorem B5935679 : Blo 1040609 5935679 := bstep (se 1 (by rfl) ⟨4451759, by rfl⟩ : syracuseStep 5935679 = 8903519) B8903519
theorem B13374395 : Blo 1040609 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B1426855661 : Blo 1040609 1426855661 := bstep (se 3 (by rfl) ⟨267535436, by rfl⟩ : syracuseStep 1426855661 = 535070873) B535070873
theorem B50666471 : Blo 1040609 50666471 := bstep (se 1 (by rfl) ⟨37999853, by rfl⟩ : syracuseStep 50666471 = 75999707) B75999707
theorem B37985273 : Blo 1040609 37985273 := bstep (se 2 (by rfl) ⟨14244477, by rfl⟩ : syracuseStep 37985273 = 28488955) B28488955
theorem B10165313 : Blo 1040609 10165313 := bstep (se 2 (by rfl) ⟨3811992, by rfl⟩ : syracuseStep 10165313 = 7623985) B7623985
theorem B5708873 : Blo 1040609 5708873 := bstep (se 2 (by rfl) ⟨2140827, by rfl⟩ : syracuseStep 5708873 = 4281655) B4281655
theorem B3513887 : Blo 1040609 3513887 := bstep (se 1 (by rfl) ⟨2635415, by rfl⟩ : syracuseStep 3513887 = 5270831) B5270831
theorem B10002041 : Blo 1040609 10002041 := bstep (se 2 (by rfl) ⟨3750765, by rfl⟩ : syracuseStep 10002041 = 7501531) B7501531
theorem B5939345 : Blo 1040609 5939345 := bstep (se 2 (by rfl) ⟨2227254, by rfl⟩ : syracuseStep 5939345 = 4454509) B4454509
theorem B3514643 : Blo 1040609 3514643 := bstep (se 1 (by rfl) ⟨2635982, by rfl⟩ : syracuseStep 3514643 = 5271965) B5271965
theorem B3515561 : Blo 1040609 3515561 := bstep (se 2 (by rfl) ⟨1318335, by rfl⟩ : syracuseStep 3515561 = 2636671) B2636671
theorem B3517289 : Blo 1040609 3517289 := bstep (se 2 (by rfl) ⟨1318983, by rfl⟩ : syracuseStep 3517289 = 2637967) B2637967
theorem B5287679 : Blo 1040609 5287679 := bstep (se 1 (by rfl) ⟨3965759, by rfl⟩ : syracuseStep 5287679 = 7931519) B7931519
theorem B1409986807 : Blo 1040609 1409986807 := bstep (se 1 (by rfl) ⟨1057490105, by rfl⟩ : syracuseStep 1409986807 = 2114980211) B2114980211
theorem B3518747 : Blo 1040609 3518747 := bstep (se 1 (by rfl) ⟨2639060, by rfl⟩ : syracuseStep 3518747 = 5278121) B5278121
theorem B1978681 : Blo 1040609 1978681 := bstep (se 2 (by rfl) ⟨742005, by rfl⟩ : syracuseStep 1978681 = 1484011) B1484011
theorem B3388159 : Blo 1040609 3388159 := bstep (se 1 (by rfl) ⟨2541119, by rfl⟩ : syracuseStep 3388159 = 5082239) B5082239
theorem B1881323 : Blo 1040609 1881323 := bstep (se 1 (by rfl) ⟨1410992, by rfl⟩ : syracuseStep 1881323 = 2821985) B2821985
theorem B2341403 : Blo 1040609 2341403 := bstep (se 1 (by rfl) ⟨1756052, by rfl⟩ : syracuseStep 2341403 = 3512105) B3512105
theorem B2964023 : Blo 1040609 2964023 := bstep (se 1 (by rfl) ⟨2223017, by rfl⟩ : syracuseStep 2964023 = 4446035) B4446035
theorem B76037069 : Blo 1040609 76037069 := bstep (se 3 (by rfl) ⟨14256950, by rfl⟩ : syracuseStep 76037069 = 28513901) B28513901
theorem B2375887 : Blo 1040609 2375887 := bstep (se 1 (by rfl) ⟨1781915, by rfl⟩ : syracuseStep 2375887 = 3563831) B3563831
theorem B2344319 : Blo 1040609 2344319 := bstep (se 1 (by rfl) ⟨1758239, by rfl⟩ : syracuseStep 2344319 = 3516479) B3516479
theorem B50742773 : Blo 1040609 50742773 := bstep (se 5 (by rfl) ⟨2378567, by rfl⟩ : syracuseStep 50742773 = 4757135) B4757135
theorem B6014843 : Blo 1040609 6014843 := bstep (se 1 (by rfl) ⟨4511132, by rfl⟩ : syracuseStep 6014843 = 9022265) B9022265
theorem B2967691 : Blo 1040609 2967691 := bstep (se 1 (by rfl) ⟨2225768, by rfl⟩ : syracuseStep 2967691 = 4451537) B4451537
theorem B2345129 : Blo 1040609 2345129 := bstep (se 2 (by rfl) ⟨879423, by rfl⟩ : syracuseStep 2345129 = 1758847) B1758847
theorem B2541743 : Blo 1040609 2541743 := bstep (se 1 (by rfl) ⟨1906307, by rfl⟩ : syracuseStep 2541743 = 3812615) B3812615
theorem B25348423 : Blo 1040609 25348423 := bstep (se 1 (by rfl) ⟨19011317, by rfl⟩ : syracuseStep 25348423 = 38022635) B38022635
theorem B195447815 : Blo 1040609 195447815 := bstep (se 1 (by rfl) ⟨146585861, by rfl⟩ : syracuseStep 195447815 = 293171723) B293171723
theorem B2968807 : Blo 1040609 2968807 := bstep (se 1 (by rfl) ⟨2226605, by rfl⟩ : syracuseStep 2968807 = 4453211) B4453211
theorem B1757065 : Blo 1040609 1757065 := bstep (se 2 (by rfl) ⟨658899, by rfl⟩ : syracuseStep 1757065 = 1317799) B1317799
theorem B1757497 : Blo 1040609 1757497 := bstep (se 2 (by rfl) ⟨659061, by rfl⟩ : syracuseStep 1757497 = 1318123) B1318123
theorem B8016335 : Blo 1040609 8016335 := bstep (se 1 (by rfl) ⟨6012251, by rfl⟩ : syracuseStep 8016335 = 12024503) B12024503
theorem B2642665 : Blo 1040609 2642665 := bstep (se 2 (by rfl) ⟨990999, by rfl⟩ : syracuseStep 2642665 = 1981999) B1981999
theorem B1757983 : Blo 1040609 1757983 := bstep (se 1 (by rfl) ⟨1318487, by rfl⟩ : syracuseStep 1757983 = 2636975) B2636975
theorem B1561535 : Blo 1040609 1561535 := bstep (se 1 (by rfl) ⟨1171151, by rfl⟩ : syracuseStep 1561535 = 2342303) B2342303
theorem B1562111 : Blo 1040609 1562111 := bstep (se 1 (by rfl) ⟨1171583, by rfl⟩ : syracuseStep 1562111 = 2343167) B2343167
theorem B1562537 : Blo 1040609 1562537 := bstep (se 2 (by rfl) ⟨585951, by rfl⟩ : syracuseStep 1562537 = 1171903) B1171903
theorem B2349179 : Blo 1040609 2349179 := bstep (se 1 (by rfl) ⟨1761884, by rfl⟩ : syracuseStep 2349179 = 3523769) B3523769
theorem B1563017 : Blo 1040609 1563017 := bstep (se 2 (by rfl) ⟨586131, by rfl⟩ : syracuseStep 1563017 = 1172263) B1172263
theorem B1759657 : Blo 1040609 1759657 := bstep (se 2 (by rfl) ⟨659871, by rfl⟩ : syracuseStep 1759657 = 1319743) B1319743
theorem B1759711 : Blo 1040609 1759711 := bstep (se 1 (by rfl) ⟨1319783, by rfl⟩ : syracuseStep 1759711 = 2639567) B2639567
theorem B1759799 : Blo 1040609 1759799 := bstep (se 1 (by rfl) ⟨1319849, by rfl⟩ : syracuseStep 1759799 = 2639699) B2639699
theorem B3168893 : Blo 1040609 3168893 := bstep (se 3 (by rfl) ⟨594167, by rfl⟩ : syracuseStep 3168893 = 1188335) B1188335
theorem B1563263 : Blo 1040609 1563263 := bstep (se 1 (by rfl) ⟨1172447, by rfl⟩ : syracuseStep 1563263 = 2344895) B2344895
theorem B2349863 : Blo 1040609 2349863 := bstep (se 1 (by rfl) ⟨1762397, by rfl⟩ : syracuseStep 2349863 = 3524795) B3524795
theorem B1563641 : Blo 1040609 1563641 := bstep (se 2 (by rfl) ⟨586365, by rfl⟩ : syracuseStep 1563641 = 1172731) B1172731
theorem B1563839 : Blo 1040609 1563839 := bstep (se 1 (by rfl) ⟨1172879, by rfl⟩ : syracuseStep 1563839 = 2345759) B2345759
theorem B1760447 : Blo 1040609 1760447 := bstep (se 1 (by rfl) ⟨1320335, by rfl⟩ : syracuseStep 1760447 = 2640671) B2640671
theorem B1564391 : Blo 1040609 1564391 := bstep (se 1 (by rfl) ⟨1173293, by rfl⟩ : syracuseStep 1564391 = 2346587) B2346587
theorem B1564667 : Blo 1040609 1564667 := bstep (se 1 (by rfl) ⟨1173500, by rfl⟩ : syracuseStep 1564667 = 2347001) B2347001
theorem B1564763 : Blo 1040609 1564763 := bstep (se 1 (by rfl) ⟨1173572, by rfl⟩ : syracuseStep 1564763 = 2347145) B2347145
theorem B1040667 : Blo 1040609 1040667 := bstep (se 1 (by rfl) ⟨780500, by rfl⟩ : syracuseStep 1040667 = 1561001) B1561001
theorem B1565159 : Blo 1040609 1565159 := bstep (se 1 (by rfl) ⟨1173869, by rfl⟩ : syracuseStep 1565159 = 2347739) B2347739
theorem B1565225 : Blo 1040609 1565225 := bstep (se 2 (by rfl) ⟨586959, by rfl⟩ : syracuseStep 1565225 = 1173919) B1173919
theorem B6677153 : Blo 1040609 6677153 := bstep (se 2 (by rfl) ⟨2503932, by rfl⟩ : syracuseStep 6677153 = 5007865) B5007865
theorem B1761979 : Blo 1040609 1761979 := bstep (se 1 (by rfl) ⟨1321484, by rfl⟩ : syracuseStep 1761979 = 2642969) B2642969
theorem B1565723 : Blo 1040609 1565723 := bstep (se 1 (by rfl) ⟨1174292, by rfl⟩ : syracuseStep 1565723 = 2348585) B2348585
theorem B20047135 : Blo 1040609 20047135 := bstep (se 1 (by rfl) ⟨15035351, by rfl⟩ : syracuseStep 20047135 = 30070703) B30070703
theorem B1762607 : Blo 1040609 1762607 := bstep (se 1 (by rfl) ⟨1321955, by rfl⟩ : syracuseStep 1762607 = 2643911) B2643911
theorem B1762681 : Blo 1040609 1762681 := bstep (se 2 (by rfl) ⟨661005, by rfl⟩ : syracuseStep 1762681 = 1322011) B1322011
theorem B1566311 : Blo 1040609 1566311 := bstep (se 1 (by rfl) ⟨1174733, by rfl⟩ : syracuseStep 1566311 = 2349467) B2349467
theorem B1566491 : Blo 1040609 1566491 := bstep (se 1 (by rfl) ⟨1174868, by rfl⟩ : syracuseStep 1566491 = 2349737) B2349737
theorem B1566503 : Blo 1040609 1566503 := bstep (se 1 (by rfl) ⟨1174877, by rfl⟩ : syracuseStep 1566503 = 2349755) B2349755
theorem B1042523 : Blo 1040609 1042523 := bstep (se 1 (by rfl) ⟨781892, by rfl⟩ : syracuseStep 1042523 = 1563785) B1563785
theorem B1173595 : Blo 1040609 1173595 := bstep (se 1 (by rfl) ⟨880196, by rfl⟩ : syracuseStep 1173595 = 1760393) B1760393
theorem B1042751 : Blo 1040609 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B1043071 : Blo 1040609 1043071 := bstep (se 1 (by rfl) ⟨782303, by rfl⟩ : syracuseStep 1043071 = 1564607) B1564607
theorem B45771965 : Blo 1040609 45771965 := bstep (se 3 (by rfl) ⟨8582243, by rfl⟩ : syracuseStep 45771965 = 17164487) B17164487
theorem B1043687 : Blo 1040609 1043687 := bstep (se 1 (by rfl) ⟨782765, by rfl⟩ : syracuseStep 1043687 = 1565531) B1565531
theorem B1174783 : Blo 1040609 1174783 := bstep (se 1 (by rfl) ⟨881087, by rfl⟩ : syracuseStep 1174783 = 1762175) B1762175
theorem B1043759 : Blo 1040609 1043759 := bstep (se 1 (by rfl) ⟨782819, by rfl⟩ : syracuseStep 1043759 = 1565639) B1565639
theorem B1043967 : Blo 1040609 1043967 := bstep (se 1 (by rfl) ⟨782975, by rfl⟩ : syracuseStep 1043967 = 1565951) B1565951
theorem B1044255 : Blo 1040609 1044255 := bstep (se 1 (by rfl) ⟨783191, by rfl⟩ : syracuseStep 1044255 = 1566383) B1566383
theorem B42725231 : Blo 1040609 42725231 := bstep (se 1 (by rfl) ⟨32043923, by rfl⟩ : syracuseStep 42725231 = 64087847) B64087847
theorem B9039863 : Blo 1040609 9039863 := bstep (se 1 (by rfl) ⟨6779897, by rfl⟩ : syracuseStep 9039863 = 13559795) B13559795
theorem B7926173 : Blo 1040609 7926173 := bstep (se 3 (by rfl) ⟨1486157, by rfl⟩ : syracuseStep 7926173 = 2972315) B2972315
theorem B3961993 : Blo 1040609 3961993 := bstep (se 2 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 3961993 = 2971495) B2971495
theorem B13563425 : Blo 1040609 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B3339883 : Blo 1040609 3339883 := bstep (se 1 (by rfl) ⟨2504912, by rfl⟩ : syracuseStep 3339883 = 5009825) B5009825
theorem B2226503 : Blo 1040609 2226503 := bstep (se 1 (by rfl) ⟨1669877, by rfl⟩ : syracuseStep 2226503 = 3339755) B3339755
theorem B5344223 : Blo 1040609 5344223 := bstep (se 1 (by rfl) ⟨4008167, by rfl⟩ : syracuseStep 5344223 = 8016335) B8016335
theorem B8916263 : Blo 1040609 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B3805915 : Blo 1040609 3805915 := bstep (se 1 (by rfl) ⟨2854436, by rfl⟩ : syracuseStep 3805915 = 5708873) B5708873
theorem B30079718549 : Blo 1040609 30079718549 := bstep (se 6 (by rfl) ⟨704993403, by rfl⟩ : syracuseStep 30079718549 = 1409986807) B1409986807
theorem B5282657 : Blo 1040609 5282657 := bstep (se 2 (by rfl) ⟨1980996, by rfl⟩ : syracuseStep 5282657 = 3961993) B3961993
theorem B30514643 : Blo 1040609 30514643 := bstep (se 1 (by rfl) ⟨22885982, by rfl⟩ : syracuseStep 30514643 = 45771965) B45771965
theorem B28483487 : Blo 1040609 28483487 := bstep (se 1 (by rfl) ⟨21362615, by rfl⟩ : syracuseStep 28483487 = 42725231) B42725231
theorem B5284115 : Blo 1040609 5284115 := bstep (se 1 (by rfl) ⟨3963086, by rfl⟩ : syracuseStep 5284115 = 7926173) B7926173
theorem B1254215 : Blo 1040609 1254215 := bstep (se 1 (by rfl) ⟨940661, by rfl⟩ : syracuseStep 1254215 = 1881323) B1881323
theorem B1484335 : Blo 1040609 1484335 := bstep (se 1 (by rfl) ⟨1113251, by rfl⟩ : syracuseStep 1484335 = 2226503) B2226503
theorem B1976015 : Blo 1040609 1976015 := bstep (se 1 (by rfl) ⟨1482011, by rfl⟩ : syracuseStep 1976015 = 2964023) B2964023
theorem B33828515 : Blo 1040609 33828515 := bstep (se 1 (by rfl) ⟨25371386, by rfl⟩ : syracuseStep 33828515 = 50742773) B50742773
theorem B4009895 : Blo 1040609 4009895 := bstep (se 1 (by rfl) ⟨3007421, by rfl⟩ : syracuseStep 4009895 = 6014843) B6014843
theorem B130298543 : Blo 1040609 130298543 := bstep (se 1 (by rfl) ⟨97723907, by rfl⟩ : syracuseStep 130298543 = 195447815) B195447815
theorem B28554191 : Blo 1040609 28554191 := bstep (se 1 (by rfl) ⟨21415643, by rfl⟩ : syracuseStep 28554191 = 42831287) B42831287
theorem B64206539 : Blo 1040609 64206539 := bstep (se 1 (by rfl) ⟨48154904, by rfl⟩ : syracuseStep 64206539 = 96309809) B96309809
theorem B33797897 : Blo 1040609 33797897 := bstep (se 2 (by rfl) ⟨12674211, by rfl⟩ : syracuseStep 33797897 = 25348423) B25348423
theorem B951237107 : Blo 1040609 951237107 := bstep (se 1 (by rfl) ⟨713427830, by rfl⟩ : syracuseStep 951237107 = 1426855661) B1426855661
theorem B2342591 : Blo 1040609 2342591 := bstep (se 1 (by rfl) ⟨1756943, by rfl⟩ : syracuseStep 2342591 = 3513887) B3513887
theorem B6668027 : Blo 1040609 6668027 := bstep (se 1 (by rfl) ⟨5001020, by rfl⟩ : syracuseStep 6668027 = 10002041) B10002041
theorem B2342753 : Blo 1040609 2342753 := bstep (se 2 (by rfl) ⟨878532, by rfl⟩ : syracuseStep 2342753 = 1757065) B1757065
theorem B2343095 : Blo 1040609 2343095 := bstep (se 1 (by rfl) ⟨1757321, by rfl⟩ : syracuseStep 2343095 = 3514643) B3514643
theorem B2343329 : Blo 1040609 2343329 := bstep (se 2 (by rfl) ⟨878748, by rfl⟩ : syracuseStep 2343329 = 1757497) B1757497
theorem B2638241 : Blo 1040609 2638241 := bstep (se 2 (by rfl) ⟨989340, by rfl⟩ : syracuseStep 2638241 = 1978681) B1978681
theorem B2343707 : Blo 1040609 2343707 := bstep (se 1 (by rfl) ⟨1757780, by rfl⟩ : syracuseStep 2343707 = 3515561) B3515561
theorem B3523553 : Blo 1040609 3523553 := bstep (se 2 (by rfl) ⟨1321332, by rfl⟩ : syracuseStep 3523553 = 2642665) B2642665
theorem B2343977 : Blo 1040609 2343977 := bstep (se 2 (by rfl) ⟨878991, by rfl⟩ : syracuseStep 2343977 = 1757983) B1757983
theorem B2344859 : Blo 1040609 2344859 := bstep (se 1 (by rfl) ⟨1758644, by rfl⟩ : syracuseStep 2344859 = 3517289) B3517289
theorem B3525119 : Blo 1040609 3525119 := bstep (se 1 (by rfl) ⟨2643839, by rfl⟩ : syracuseStep 3525119 = 5287679) B5287679
theorem B2345831 : Blo 1040609 2345831 := bstep (se 1 (by rfl) ⟨1759373, by rfl⟩ : syracuseStep 2345831 = 3518747) B3518747
theorem B2346209 : Blo 1040609 2346209 := bstep (se 2 (by rfl) ⟨879828, by rfl⟩ : syracuseStep 2346209 = 1759657) B1759657
theorem B2346281 : Blo 1040609 2346281 := bstep (se 2 (by rfl) ⟨879855, by rfl⟩ : syracuseStep 2346281 = 1759711) B1759711
theorem B1560935 : Blo 1040609 1560935 := bstep (se 1 (by rfl) ⟨1170701, by rfl⟩ : syracuseStep 1560935 = 2341403) B2341403
theorem B3954203 : Blo 1040609 3954203 := bstep (se 1 (by rfl) ⟨2965652, by rfl⟩ : syracuseStep 3954203 = 5931305) B5931305
theorem B3167849 : Blo 1040609 3167849 := bstep (se 2 (by rfl) ⟨1187943, by rfl⟩ : syracuseStep 3167849 = 2375887) B2375887
theorem B2349305 : Blo 1040609 2349305 := bstep (se 2 (by rfl) ⟨880989, by rfl⟩ : syracuseStep 2349305 = 1761979) B1761979
theorem B1562879 : Blo 1040609 1562879 := bstep (se 1 (by rfl) ⟨1172159, by rfl⟩ : syracuseStep 1562879 = 2344319) B2344319
theorem B1563419 : Blo 1040609 1563419 := bstep (se 1 (by rfl) ⟨1172564, by rfl⟩ : syracuseStep 1563419 = 2345129) B2345129
theorem B1694495 : Blo 1040609 1694495 := bstep (se 1 (by rfl) ⟨1270871, by rfl⟩ : syracuseStep 1694495 = 2541743) B2541743
theorem B26729513 : Blo 1040609 26729513 := bstep (se 2 (by rfl) ⟨10023567, by rfl⟩ : syracuseStep 26729513 = 20047135) B20047135
theorem B2350241 : Blo 1040609 2350241 := bstep (se 2 (by rfl) ⟨881340, by rfl⟩ : syracuseStep 2350241 = 1762681) B1762681
theorem B1564793 : Blo 1040609 1564793 := bstep (se 2 (by rfl) ⟨586797, by rfl⟩ : syracuseStep 1564793 = 1173595) B1173595
theorem B3956921 : Blo 1040609 3956921 := bstep (se 2 (by rfl) ⟨1483845, by rfl⟩ : syracuseStep 3956921 = 2967691) B2967691
theorem B3957119 : Blo 1040609 3957119 := bstep (se 1 (by rfl) ⟨2967839, by rfl⟩ : syracuseStep 3957119 = 5935679) B5935679
theorem B1041023 : Blo 1040609 1041023 := bstep (se 1 (by rfl) ⟨780767, by rfl⟩ : syracuseStep 1041023 = 1561535) B1561535
theorem B1041407 : Blo 1040609 1041407 := bstep (se 1 (by rfl) ⟨781055, by rfl⟩ : syracuseStep 1041407 = 1562111) B1562111
theorem B1041691 : Blo 1040609 1041691 := bstep (se 1 (by rfl) ⟨781268, by rfl⟩ : syracuseStep 1041691 = 1562537) B1562537
theorem B1566119 : Blo 1040609 1566119 := bstep (se 1 (by rfl) ⟨1174589, by rfl⟩ : syracuseStep 1566119 = 2349179) B2349179
theorem B1042011 : Blo 1040609 1042011 := bstep (se 1 (by rfl) ⟨781508, by rfl⟩ : syracuseStep 1042011 = 1563017) B1563017
theorem B3958409 : Blo 1040609 3958409 := bstep (se 2 (by rfl) ⟨1484403, by rfl⟩ : syracuseStep 3958409 = 2968807) B2968807
theorem B1566377 : Blo 1040609 1566377 := bstep (se 2 (by rfl) ⟨587391, by rfl⟩ : syracuseStep 1566377 = 1174783) B1174783
theorem B1173199 : Blo 1040609 1173199 := bstep (se 1 (by rfl) ⟨879899, by rfl⟩ : syracuseStep 1173199 = 1759799) B1759799
theorem B1042175 : Blo 1040609 1042175 := bstep (se 1 (by rfl) ⟨781631, by rfl⟩ : syracuseStep 1042175 = 1563263) B1563263
theorem B1566575 : Blo 1040609 1566575 := bstep (se 1 (by rfl) ⟨1174931, by rfl⟩ : syracuseStep 1566575 = 2349863) B2349863
theorem B33777647 : Blo 1040609 33777647 := bstep (se 1 (by rfl) ⟨25333235, by rfl⟩ : syracuseStep 33777647 = 50666471) B50666471
theorem B25323515 : Blo 1040609 25323515 := bstep (se 1 (by rfl) ⟨18992636, by rfl⟩ : syracuseStep 25323515 = 37985273) B37985273
theorem B1042427 : Blo 1040609 1042427 := bstep (se 1 (by rfl) ⟨781820, by rfl⟩ : syracuseStep 1042427 = 1563641) B1563641
theorem B6776875 : Blo 1040609 6776875 := bstep (se 1 (by rfl) ⟨5082656, by rfl⟩ : syracuseStep 6776875 = 10165313) B10165313
theorem B1042559 : Blo 1040609 1042559 := bstep (se 1 (by rfl) ⟨781919, by rfl⟩ : syracuseStep 1042559 = 1563839) B1563839
theorem B1173631 : Blo 1040609 1173631 := bstep (se 1 (by rfl) ⟨880223, by rfl⟩ : syracuseStep 1173631 = 1760447) B1760447
theorem B1042927 : Blo 1040609 1042927 := bstep (se 1 (by rfl) ⟨782195, by rfl⟩ : syracuseStep 1042927 = 1564391) B1564391
theorem B1043111 : Blo 1040609 1043111 := bstep (se 1 (by rfl) ⟨782333, by rfl⟩ : syracuseStep 1043111 = 1564667) B1564667
theorem B1043175 : Blo 1040609 1043175 := bstep (se 1 (by rfl) ⟨782381, by rfl⟩ : syracuseStep 1043175 = 1564763) B1564763
theorem B3959563 : Blo 1040609 3959563 := bstep (se 1 (by rfl) ⟨2969672, by rfl⟩ : syracuseStep 3959563 = 5939345) B5939345
theorem B1043439 : Blo 1040609 1043439 := bstep (se 1 (by rfl) ⟨782579, by rfl⟩ : syracuseStep 1043439 = 1565159) B1565159
theorem B1043483 : Blo 1040609 1043483 := bstep (se 1 (by rfl) ⟨782612, by rfl⟩ : syracuseStep 1043483 = 1565225) B1565225
theorem B4451435 : Blo 1040609 4451435 := bstep (se 1 (by rfl) ⟨3338576, by rfl⟩ : syracuseStep 4451435 = 6677153) B6677153
theorem B1043815 : Blo 1040609 1043815 := bstep (se 1 (by rfl) ⟨782861, by rfl⟩ : syracuseStep 1043815 = 1565723) B1565723
theorem B1175071 : Blo 1040609 1175071 := bstep (se 1 (by rfl) ⟨881303, by rfl⟩ : syracuseStep 1175071 = 1762607) B1762607
theorem B4517545 : Blo 1040609 4517545 := bstep (se 2 (by rfl) ⟨1694079, by rfl⟩ : syracuseStep 4517545 = 3388159) B3388159
theorem B1044207 : Blo 1040609 1044207 := bstep (se 1 (by rfl) ⟨783155, by rfl⟩ : syracuseStep 1044207 = 1566311) B1566311
theorem B1044327 : Blo 1040609 1044327 := bstep (se 1 (by rfl) ⟨783245, by rfl⟩ : syracuseStep 1044327 = 1566491) B1566491
theorem B1044335 : Blo 1040609 1044335 := bstep (se 1 (by rfl) ⟨783251, by rfl⟩ : syracuseStep 1044335 = 1566503) B1566503
theorem B8450381 : Blo 1040609 8450381 := bstep (se 3 (by rfl) ⟨1584446, by rfl⟩ : syracuseStep 8450381 = 3168893) B3168893
theorem B4453177 : Blo 1040609 4453177 := bstep (se 2 (by rfl) ⟨1669941, by rfl⟩ : syracuseStep 4453177 = 3339883) B3339883
theorem B6026575 : Blo 1040609 6026575 := bstep (se 1 (by rfl) ⟨4519931, by rfl⟩ : syracuseStep 6026575 = 9039863) B9039863
theorem B9042283 : Blo 1040609 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B50691379 : Blo 1040609 50691379 := bstep (se 1 (by rfl) ⟨38018534, by rfl⟩ : syracuseStep 50691379 = 76037069) B76037069
theorem B36143333 : Blo 1040609 36143333 := bstep (se 4 (by rfl) ⟨3388437, by rfl⟩ : syracuseStep 36143333 = 6776875) B6776875
theorem B3344573 : Blo 1040609 3344573 := bstep (se 3 (by rfl) ⟨627107, by rfl⟩ : syracuseStep 3344573 = 1254215) B1254215
theorem B5279417 : Blo 1040609 5279417 := bstep (se 2 (by rfl) ⟨1979781, by rfl⟩ : syracuseStep 5279417 = 3959563) B3959563
theorem B5937569 : Blo 1040609 5937569 := bstep (se 2 (by rfl) ⟨2226588, by rfl⟩ : syracuseStep 5937569 = 4453177) B4453177
theorem B22518431 : Blo 1040609 22518431 := bstep (se 1 (by rfl) ⟨16888823, by rfl⟩ : syracuseStep 22518431 = 33777647) B33777647
theorem B16882343 : Blo 1040609 16882343 := bstep (se 1 (by rfl) ⟨12661757, by rfl⟩ : syracuseStep 16882343 = 25323515) B25323515
theorem B8035433 : Blo 1040609 8035433 := bstep (se 2 (by rfl) ⟨3013287, by rfl⟩ : syracuseStep 8035433 = 6026575) B6026575
theorem B22552343 : Blo 1040609 22552343 := bstep (se 1 (by rfl) ⟨16914257, by rfl⟩ : syracuseStep 22552343 = 33828515) B33828515
theorem B42804359 : Blo 1040609 42804359 := bstep (se 1 (by rfl) ⟨32103269, by rfl⟩ : syracuseStep 42804359 = 64206539) B64206539
theorem B5944175 : Blo 1040609 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B20053145699 : Blo 1040609 20053145699 := bstep (se 1 (by rfl) ⟨15039859274, by rfl⟩ : syracuseStep 20053145699 = 30079718549) B30079718549
theorem B2636135 : Blo 1040609 2636135 := bstep (se 1 (by rfl) ⟨1977101, by rfl⟩ : syracuseStep 2636135 = 3954203) B3954203
theorem B1129663 : Blo 1040609 1129663 := bstep (se 1 (by rfl) ⟨847247, by rfl⟩ : syracuseStep 1129663 = 1694495) B1694495
theorem B3521771 : Blo 1040609 3521771 := bstep (se 1 (by rfl) ⟨2641328, by rfl⟩ : syracuseStep 3521771 = 5282657) B5282657
theorem B18988991 : Blo 1040609 18988991 := bstep (se 1 (by rfl) ⟨14241743, by rfl⟩ : syracuseStep 18988991 = 28483487) B28483487
theorem B2637947 : Blo 1040609 2637947 := bstep (se 1 (by rfl) ⟨1978460, by rfl⟩ : syracuseStep 2637947 = 3956921) B3956921
theorem B3522743 : Blo 1040609 3522743 := bstep (se 1 (by rfl) ⟨2642057, by rfl⟩ : syracuseStep 3522743 = 5284115) B5284115
theorem B2638079 : Blo 1040609 2638079 := bstep (se 1 (by rfl) ⟨1978559, by rfl⟩ : syracuseStep 2638079 = 3957119) B3957119
theorem B2638939 : Blo 1040609 2638939 := bstep (se 1 (by rfl) ⟨1979204, by rfl⟩ : syracuseStep 2638939 = 3958409) B3958409
theorem B2967623 : Blo 1040609 2967623 := bstep (se 1 (by rfl) ⟨2225717, by rfl⟩ : syracuseStep 2967623 = 4451435) B4451435
theorem B2673263 : Blo 1040609 2673263 := bstep (se 1 (by rfl) ⟨2004947, by rfl⟩ : syracuseStep 2673263 = 4009895) B4009895
theorem B7916453 : Blo 1040609 7916453 := bstep (se 4 (by rfl) ⟨742167, by rfl⟩ : syracuseStep 7916453 = 1484335) B1484335
theorem B22531931 : Blo 1040609 22531931 := bstep (se 1 (by rfl) ⟨16898948, by rfl⟩ : syracuseStep 22531931 = 33797897) B33797897
theorem B67588505 : Blo 1040609 67588505 := bstep (se 2 (by rfl) ⟨25345689, by rfl⟩ : syracuseStep 67588505 = 50691379) B50691379
theorem B57005045 : Blo 1040609 57005045 := bstep (se 5 (by rfl) ⟨2672111, by rfl⟩ : syracuseStep 57005045 = 5344223) B5344223
theorem B1561727 : Blo 1040609 1561727 := bstep (se 1 (by rfl) ⟨1171295, by rfl⟩ : syracuseStep 1561727 = 2342591) B2342591
theorem B4445351 : Blo 1040609 4445351 := bstep (se 1 (by rfl) ⟨3334013, by rfl⟩ : syracuseStep 4445351 = 6668027) B6668027
theorem B1561835 : Blo 1040609 1561835 := bstep (se 1 (by rfl) ⟨1171376, by rfl⟩ : syracuseStep 1561835 = 2342753) B2342753
theorem B1562063 : Blo 1040609 1562063 := bstep (se 1 (by rfl) ⟨1171547, by rfl⟩ : syracuseStep 1562063 = 2343095) B2343095
theorem B1562219 : Blo 1040609 1562219 := bstep (se 1 (by rfl) ⟨1171664, by rfl⟩ : syracuseStep 1562219 = 2343329) B2343329
theorem B1758827 : Blo 1040609 1758827 := bstep (se 1 (by rfl) ⟨1319120, by rfl⟩ : syracuseStep 1758827 = 2638241) B2638241
theorem B1562471 : Blo 1040609 1562471 := bstep (se 1 (by rfl) ⟨1171853, by rfl⟩ : syracuseStep 1562471 = 2343707) B2343707
theorem B2349035 : Blo 1040609 2349035 := bstep (se 1 (by rfl) ⟨1761776, by rfl⟩ : syracuseStep 2349035 = 3523553) B3523553
theorem B1562651 : Blo 1040609 1562651 := bstep (se 1 (by rfl) ⟨1171988, by rfl⟩ : syracuseStep 1562651 = 2343977) B2343977
theorem B1563239 : Blo 1040609 1563239 := bstep (se 1 (by rfl) ⟨1172429, by rfl⟩ : syracuseStep 1563239 = 2344859) B2344859
theorem B2350079 : Blo 1040609 2350079 := bstep (se 1 (by rfl) ⟨1762559, by rfl⟩ : syracuseStep 2350079 = 3525119) B3525119
theorem B1563887 : Blo 1040609 1563887 := bstep (se 1 (by rfl) ⟨1172915, by rfl⟩ : syracuseStep 1563887 = 2345831) B2345831
theorem B1564139 : Blo 1040609 1564139 := bstep (se 1 (by rfl) ⟨1173104, by rfl⟩ : syracuseStep 1564139 = 2346209) B2346209
theorem B1564187 : Blo 1040609 1564187 := bstep (se 1 (by rfl) ⟨1173140, by rfl⟩ : syracuseStep 1564187 = 2346281) B2346281
theorem B1564265 : Blo 1040609 1564265 := bstep (se 2 (by rfl) ⟨586599, by rfl⟩ : syracuseStep 1564265 = 1173199) B1173199
theorem B1564841 : Blo 1040609 1564841 := bstep (se 2 (by rfl) ⟨586815, by rfl⟩ : syracuseStep 1564841 = 1173631) B1173631
theorem B1040623 : Blo 1040609 1040623 := bstep (se 1 (by rfl) ⟨780467, by rfl⟩ : syracuseStep 1040623 = 1560935) B1560935
theorem B1566203 : Blo 1040609 1566203 := bstep (se 1 (by rfl) ⟨1174652, by rfl⟩ : syracuseStep 1566203 = 2349305) B2349305
theorem B1041919 : Blo 1040609 1041919 := bstep (se 1 (by rfl) ⟨781439, by rfl⟩ : syracuseStep 1041919 = 1562879) B1562879
theorem B8447597 : Blo 1040609 8447597 := bstep (se 3 (by rfl) ⟨1583924, by rfl⟩ : syracuseStep 8447597 = 3167849) B3167849
theorem B1042279 : Blo 1040609 1042279 := bstep (se 1 (by rfl) ⟨781709, by rfl⟩ : syracuseStep 1042279 = 1563419) B1563419
theorem B5269373 : Blo 1040609 5269373 := bstep (se 3 (by rfl) ⟨988007, by rfl⟩ : syracuseStep 5269373 = 1976015) B1976015
theorem B17819675 : Blo 1040609 17819675 := bstep (se 1 (by rfl) ⟨13364756, by rfl⟩ : syracuseStep 17819675 = 26729513) B26729513
theorem B1566761 : Blo 1040609 1566761 := bstep (se 2 (by rfl) ⟨587535, by rfl⟩ : syracuseStep 1566761 = 1175071) B1175071
theorem B1566827 : Blo 1040609 1566827 := bstep (se 1 (by rfl) ⟨1175120, by rfl⟩ : syracuseStep 1566827 = 2350241) B2350241
theorem B6023393 : Blo 1040609 6023393 := bstep (se 2 (by rfl) ⟨2258772, by rfl⟩ : syracuseStep 6023393 = 4517545) B4517545
theorem B20343095 : Blo 1040609 20343095 := bstep (se 1 (by rfl) ⟨15257321, by rfl⟩ : syracuseStep 20343095 = 30514643) B30514643
theorem B1043195 : Blo 1040609 1043195 := bstep (se 1 (by rfl) ⟨782396, by rfl⟩ : syracuseStep 1043195 = 1564793) B1564793
theorem B1044079 : Blo 1040609 1044079 := bstep (se 1 (by rfl) ⟨783059, by rfl⟩ : syracuseStep 1044079 = 1566119) B1566119
theorem B5074553 : Blo 1040609 5074553 := bstep (se 2 (by rfl) ⟨1902957, by rfl⟩ : syracuseStep 5074553 = 3805915) B3805915
theorem B1044251 : Blo 1040609 1044251 := bstep (se 1 (by rfl) ⟨783188, by rfl⟩ : syracuseStep 1044251 = 1566377) B1566377
theorem B1044383 : Blo 1040609 1044383 := bstep (se 1 (by rfl) ⟨783287, by rfl⟩ : syracuseStep 1044383 = 1566575) B1566575
theorem B5633587 : Blo 1040609 5633587 := bstep (se 1 (by rfl) ⟨4225190, by rfl⟩ : syracuseStep 5633587 = 8450381) B8450381
theorem B86865695 : Blo 1040609 86865695 := bstep (se 1 (by rfl) ⟨65149271, by rfl⟩ : syracuseStep 86865695 = 130298543) B130298543
theorem B12056377 : Blo 1040609 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B19036127 : Blo 1040609 19036127 := bstep (se 1 (by rfl) ⟨14277095, by rfl⟩ : syracuseStep 19036127 = 28554191) B28554191
theorem B634158071 : Blo 1040609 634158071 := bstep (se 1 (by rfl) ⟨475618553, by rfl⟩ : syracuseStep 634158071 = 951237107) B951237107
theorem B2229715 : Blo 1040609 2229715 := bstep (se 1 (by rfl) ⟨1672286, by rfl⟩ : syracuseStep 2229715 = 3344573) B3344573
theorem B5277635 : Blo 1040609 5277635 := bstep (se 1 (by rfl) ⟨3958226, by rfl⟩ : syracuseStep 5277635 = 7916453) B7916453
theorem B45059003 : Blo 1040609 45059003 := bstep (se 1 (by rfl) ⟨33794252, by rfl⟩ : syracuseStep 45059003 = 67588505) B67588505
theorem B15012287 : Blo 1040609 15012287 := bstep (se 1 (by rfl) ⟨11259215, by rfl⟩ : syracuseStep 15012287 = 22518431) B22518431
theorem B3512915 : Blo 1040609 3512915 := bstep (se 1 (by rfl) ⟨2634686, by rfl⟩ : syracuseStep 3512915 = 5269373) B5269373
theorem B7511449 : Blo 1040609 7511449 := bstep (se 2 (by rfl) ⟨2816793, by rfl⟩ : syracuseStep 7511449 = 5633587) B5633587
theorem B3383035 : Blo 1040609 3383035 := bstep (se 1 (by rfl) ⟨2537276, by rfl⟩ : syracuseStep 3383035 = 5074553) B5074553
theorem B57910463 : Blo 1040609 57910463 := bstep (se 1 (by rfl) ⟨43432847, by rfl⟩ : syracuseStep 57910463 = 86865695) B86865695
theorem B12690751 : Blo 1040609 12690751 := bstep (se 1 (by rfl) ⟨9518063, by rfl⟩ : syracuseStep 12690751 = 19036127) B19036127
theorem B13368763799 : Blo 1040609 13368763799 := bstep (se 1 (by rfl) ⟨10026572849, by rfl⟩ : syracuseStep 13368763799 = 20053145699) B20053145699
theorem B12659327 : Blo 1040609 12659327 := bstep (se 1 (by rfl) ⟨9494495, by rfl⟩ : syracuseStep 12659327 = 18988991) B18988991
theorem B24095555 : Blo 1040609 24095555 := bstep (se 1 (by rfl) ⟨18071666, by rfl⟩ : syracuseStep 24095555 = 36143333) B36143333
theorem B1978415 : Blo 1040609 1978415 := bstep (se 1 (by rfl) ⟨1483811, by rfl⟩ : syracuseStep 1978415 = 2967623) B2967623
theorem B3518585 : Blo 1040609 3518585 := bstep (se 2 (by rfl) ⟨1319469, by rfl⟩ : syracuseStep 3518585 = 2638939) B2638939
theorem B1782175 : Blo 1040609 1782175 := bstep (se 1 (by rfl) ⟨1336631, by rfl⟩ : syracuseStep 1782175 = 2673263) B2673263
theorem B3519611 : Blo 1040609 3519611 := bstep (se 1 (by rfl) ⟨2639708, by rfl⟩ : syracuseStep 3519611 = 5279417) B5279417
theorem B15021287 : Blo 1040609 15021287 := bstep (se 1 (by rfl) ⟨11265965, by rfl⟩ : syracuseStep 15021287 = 22531931) B22531931
theorem B2963567 : Blo 1040609 2963567 := bstep (se 1 (by rfl) ⟨2222675, by rfl⟩ : syracuseStep 2963567 = 4445351) B4445351
theorem B11254895 : Blo 1040609 11254895 := bstep (se 1 (by rfl) ⟨8441171, by rfl⟩ : syracuseStep 11254895 = 16882343) B16882343
theorem B5356955 : Blo 1040609 5356955 := bstep (se 1 (by rfl) ⟨4017716, by rfl⟩ : syracuseStep 5356955 = 8035433) B8035433
theorem B11879783 : Blo 1040609 11879783 := bstep (se 1 (by rfl) ⟨8909837, by rfl⟩ : syracuseStep 11879783 = 17819675) B17819675
theorem B4015595 : Blo 1040609 4015595 := bstep (se 1 (by rfl) ⟨3011696, by rfl⟩ : syracuseStep 4015595 = 6023393) B6023393
theorem B16075169 : Blo 1040609 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B1757423 : Blo 1040609 1757423 := bstep (se 1 (by rfl) ⟨1318067, by rfl⟩ : syracuseStep 1757423 = 2636135) B2636135
theorem B2347847 : Blo 1040609 2347847 := bstep (se 1 (by rfl) ⟨1760885, by rfl⟩ : syracuseStep 2347847 = 3521771) B3521771
theorem B1758631 : Blo 1040609 1758631 := bstep (se 1 (by rfl) ⟨1318973, by rfl⟩ : syracuseStep 1758631 = 2637947) B2637947
theorem B2348495 : Blo 1040609 2348495 := bstep (se 1 (by rfl) ⟨1761371, by rfl⟩ : syracuseStep 2348495 = 3522743) B3522743
theorem B1758719 : Blo 1040609 1758719 := bstep (se 1 (by rfl) ⟨1319039, by rfl⟩ : syracuseStep 1758719 = 2638079) B2638079
theorem B38003363 : Blo 1040609 38003363 := bstep (se 1 (by rfl) ⟨28502522, by rfl⟩ : syracuseStep 38003363 = 57005045) B57005045
theorem B1041151 : Blo 1040609 1041151 := bstep (se 1 (by rfl) ⟨780863, by rfl⟩ : syracuseStep 1041151 = 1561727) B1561727
theorem B1041223 : Blo 1040609 1041223 := bstep (se 1 (by rfl) ⟨780917, by rfl⟩ : syracuseStep 1041223 = 1561835) B1561835
theorem B1041375 : Blo 1040609 1041375 := bstep (se 1 (by rfl) ⟨781031, by rfl⟩ : syracuseStep 1041375 = 1562063) B1562063
theorem B1041479 : Blo 1040609 1041479 := bstep (se 1 (by rfl) ⟨781109, by rfl⟩ : syracuseStep 1041479 = 1562219) B1562219
theorem B1172551 : Blo 1040609 1172551 := bstep (se 1 (by rfl) ⟨879413, by rfl⟩ : syracuseStep 1172551 = 1758827) B1758827
theorem B1041647 : Blo 1040609 1041647 := bstep (se 1 (by rfl) ⟨781235, by rfl⟩ : syracuseStep 1041647 = 1562471) B1562471
theorem B1566023 : Blo 1040609 1566023 := bstep (se 1 (by rfl) ⟨1174517, by rfl⟩ : syracuseStep 1566023 = 2349035) B2349035
theorem B1041767 : Blo 1040609 1041767 := bstep (se 1 (by rfl) ⟨781325, by rfl⟩ : syracuseStep 1041767 = 1562651) B1562651
theorem B3958379 : Blo 1040609 3958379 := bstep (se 1 (by rfl) ⟨2968784, by rfl⟩ : syracuseStep 3958379 = 5937569) B5937569
theorem B1042159 : Blo 1040609 1042159 := bstep (se 1 (by rfl) ⟨781619, by rfl⟩ : syracuseStep 1042159 = 1563239) B1563239
theorem B1566719 : Blo 1040609 1566719 := bstep (se 1 (by rfl) ⟨1175039, by rfl⟩ : syracuseStep 1566719 = 2350079) B2350079
theorem B1042591 : Blo 1040609 1042591 := bstep (se 1 (by rfl) ⟨781943, by rfl⟩ : syracuseStep 1042591 = 1563887) B1563887
theorem B1042759 : Blo 1040609 1042759 := bstep (se 1 (by rfl) ⟨782069, by rfl⟩ : syracuseStep 1042759 = 1564139) B1564139
theorem B1042791 : Blo 1040609 1042791 := bstep (se 1 (by rfl) ⟨782093, by rfl⟩ : syracuseStep 1042791 = 1564187) B1564187
theorem B1042843 : Blo 1040609 1042843 := bstep (se 1 (by rfl) ⟨782132, by rfl⟩ : syracuseStep 1042843 = 1564265) B1564265
theorem B15034895 : Blo 1040609 15034895 := bstep (se 1 (by rfl) ⟨11276171, by rfl⟩ : syracuseStep 15034895 = 22552343) B22552343
theorem B1043227 : Blo 1040609 1043227 := bstep (se 1 (by rfl) ⟨782420, by rfl⟩ : syracuseStep 1043227 = 1564841) B1564841
theorem B28536239 : Blo 1040609 28536239 := bstep (se 1 (by rfl) ⟨21402179, by rfl⟩ : syracuseStep 28536239 = 42804359) B42804359
theorem B1044135 : Blo 1040609 1044135 := bstep (se 1 (by rfl) ⟨783101, by rfl⟩ : syracuseStep 1044135 = 1566203) B1566203
theorem B5631731 : Blo 1040609 5631731 := bstep (se 1 (by rfl) ⟨4223798, by rfl⟩ : syracuseStep 5631731 = 8447597) B8447597
theorem B1044507 : Blo 1040609 1044507 := bstep (se 1 (by rfl) ⟨783380, by rfl⟩ : syracuseStep 1044507 = 1566761) B1566761
theorem B1044551 : Blo 1040609 1044551 := bstep (se 1 (by rfl) ⟨783413, by rfl⟩ : syracuseStep 1044551 = 1566827) B1566827
theorem B13562063 : Blo 1040609 13562063 := bstep (se 1 (by rfl) ⟨10171547, by rfl⟩ : syracuseStep 13562063 = 20343095) B20343095
theorem B3962783 : Blo 1040609 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B1506217 : Blo 1040609 1506217 := bstep (se 2 (by rfl) ⟨564831, by rfl⟩ : syracuseStep 1506217 = 1129663) B1129663
theorem B422772047 : Blo 1040609 422772047 := bstep (se 1 (by rfl) ⟨317079035, by rfl⟩ : syracuseStep 422772047 = 634158071) B634158071
theorem B10716779 : Blo 1040609 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B7902845 : Blo 1040609 7902845 := bstep (se 3 (by rfl) ⟨1481783, by rfl⟩ : syracuseStep 7902845 = 2963567) B2963567
theorem B25335575 : Blo 1040609 25335575 := bstep (se 1 (by rfl) ⟨19001681, by rfl⟩ : syracuseStep 25335575 = 38003363) B38003363
theorem B38606975 : Blo 1040609 38606975 := bstep (se 1 (by rfl) ⟨28955231, by rfl⟩ : syracuseStep 38606975 = 57910463) B57910463
theorem B8912509199 : Blo 1040609 8912509199 := bstep (se 1 (by rfl) ⟨6684381899, by rfl⟩ : syracuseStep 8912509199 = 13368763799) B13368763799
theorem B16063703 : Blo 1040609 16063703 := bstep (se 1 (by rfl) ⟨12047777, by rfl⟩ : syracuseStep 16063703 = 24095555) B24095555
theorem B1318943 : Blo 1040609 1318943 := bstep (se 1 (by rfl) ⟨989207, by rfl⟩ : syracuseStep 1318943 = 1978415) B1978415
theorem B2008289 : Blo 1040609 2008289 := bstep (se 2 (by rfl) ⟨753108, by rfl⟩ : syracuseStep 2008289 = 1506217) B1506217
theorem B281848031 : Blo 1040609 281848031 := bstep (se 1 (by rfl) ⟨211386023, by rfl⟩ : syracuseStep 281848031 = 422772047) B422772047
theorem B3518423 : Blo 1040609 3518423 := bstep (se 1 (by rfl) ⟨2638817, by rfl⟩ : syracuseStep 3518423 = 5277635) B5277635
theorem B16921001 : Blo 1040609 16921001 := bstep (se 2 (by rfl) ⟨6345375, by rfl⟩ : syracuseStep 16921001 = 12690751) B12690751
theorem B10008191 : Blo 1040609 10008191 := bstep (se 1 (by rfl) ⟨7506143, by rfl⟩ : syracuseStep 10008191 = 15012287) B15012287
theorem B2341943 : Blo 1040609 2341943 := bstep (se 1 (by rfl) ⟨1756457, by rfl⟩ : syracuseStep 2341943 = 3512915) B3512915
theorem B2376233 : Blo 1040609 2376233 := bstep (se 2 (by rfl) ⟨891087, by rfl⟩ : syracuseStep 2376233 = 1782175) B1782175
theorem B2638919 : Blo 1040609 2638919 := bstep (se 1 (by rfl) ⟨1979189, by rfl⟩ : syracuseStep 2638919 = 3958379) B3958379
theorem B8439551 : Blo 1040609 8439551 := bstep (se 1 (by rfl) ⟨6329663, by rfl⟩ : syracuseStep 8439551 = 12659327) B12659327
theorem B2344841 : Blo 1040609 2344841 := bstep (se 2 (by rfl) ⟨879315, by rfl⟩ : syracuseStep 2344841 = 1758631) B1758631
theorem B19024159 : Blo 1040609 19024159 := bstep (se 1 (by rfl) ⟨14268119, by rfl⟩ : syracuseStep 19024159 = 28536239) B28536239
theorem B3754487 : Blo 1040609 3754487 := bstep (se 1 (by rfl) ⟨2815865, by rfl⟩ : syracuseStep 3754487 = 5631731) B5631731
theorem B2345723 : Blo 1040609 2345723 := bstep (se 1 (by rfl) ⟨1759292, by rfl⟩ : syracuseStep 2345723 = 3518585) B3518585
theorem B2346407 : Blo 1040609 2346407 := bstep (se 1 (by rfl) ⟨1759805, by rfl⟩ : syracuseStep 2346407 = 3519611) B3519611
theorem B10014191 : Blo 1040609 10014191 := bstep (se 1 (by rfl) ⟨7510643, by rfl⟩ : syracuseStep 10014191 = 15021287) B15021287
theorem B2641855 : Blo 1040609 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B18042853 : Blo 1040609 18042853 := bstep (se 4 (by rfl) ⟨1691517, by rfl⟩ : syracuseStep 18042853 = 3383035) B3383035
theorem B10015265 : Blo 1040609 10015265 := bstep (se 2 (by rfl) ⟨3755724, by rfl⟩ : syracuseStep 10015265 = 7511449) B7511449
theorem B7919855 : Blo 1040609 7919855 := bstep (se 1 (by rfl) ⟨5939891, by rfl⟩ : syracuseStep 7919855 = 11879783) B11879783
theorem B2677063 : Blo 1040609 2677063 := bstep (se 1 (by rfl) ⟨2007797, by rfl⟩ : syracuseStep 2677063 = 4015595) B4015595
theorem B1563401 : Blo 1040609 1563401 := bstep (se 2 (by rfl) ⟨586275, by rfl⟩ : syracuseStep 1563401 = 1172551) B1172551
theorem B2972953 : Blo 1040609 2972953 := bstep (se 2 (by rfl) ⟨1114857, by rfl⟩ : syracuseStep 2972953 = 2229715) B2229715
theorem B30039335 : Blo 1040609 30039335 := bstep (se 1 (by rfl) ⟨22529501, by rfl⟩ : syracuseStep 30039335 = 45059003) B45059003
theorem B1171615 : Blo 1040609 1171615 := bstep (se 1 (by rfl) ⟨878711, by rfl⟩ : syracuseStep 1171615 = 1757423) B1757423
theorem B1565231 : Blo 1040609 1565231 := bstep (se 1 (by rfl) ⟨1173923, by rfl⟩ : syracuseStep 1565231 = 2347847) B2347847
theorem B1565663 : Blo 1040609 1565663 := bstep (se 1 (by rfl) ⟨1174247, by rfl⟩ : syracuseStep 1565663 = 2348495) B2348495
theorem B1172479 : Blo 1040609 1172479 := bstep (se 1 (by rfl) ⟨879359, by rfl⟩ : syracuseStep 1172479 = 1758719) B1758719
theorem B1044015 : Blo 1040609 1044015 := bstep (se 1 (by rfl) ⟨783011, by rfl⟩ : syracuseStep 1044015 = 1566023) B1566023
theorem B1044479 : Blo 1040609 1044479 := bstep (se 1 (by rfl) ⟨783359, by rfl⟩ : syracuseStep 1044479 = 1566719) B1566719
theorem B10023263 : Blo 1040609 10023263 := bstep (se 1 (by rfl) ⟨7517447, by rfl⟩ : syracuseStep 10023263 = 15034895) B15034895
theorem B9041375 : Blo 1040609 9041375 := bstep (se 1 (by rfl) ⟨6781031, by rfl⟩ : syracuseStep 9041375 = 13562063) B13562063
theorem B7503263 : Blo 1040609 7503263 := bstep (se 1 (by rfl) ⟨5627447, by rfl⟩ : syracuseStep 7503263 = 11254895) B11254895
theorem B3571303 : Blo 1040609 3571303 := bstep (se 1 (by rfl) ⟨2678477, by rfl⟩ : syracuseStep 3571303 = 5356955) B5356955
theorem B7144519 : Blo 1040609 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B25365545 : Blo 1040609 25365545 := bstep (se 2 (by rfl) ⟨9512079, by rfl⟩ : syracuseStep 25365545 = 19024159) B19024159
theorem B5279903 : Blo 1040609 5279903 := bstep (se 1 (by rfl) ⟨3959927, by rfl⟩ : syracuseStep 5279903 = 7919855) B7919855
theorem B20026223 : Blo 1040609 20026223 := bstep (se 1 (by rfl) ⟨15019667, by rfl⟩ : syracuseStep 20026223 = 30039335) B30039335
theorem B24057137 : Blo 1040609 24057137 := bstep (se 2 (by rfl) ⟨9021426, by rfl⟩ : syracuseStep 24057137 = 18042853) B18042853
theorem B187898687 : Blo 1040609 187898687 := bstep (se 1 (by rfl) ⟨140924015, by rfl⟩ : syracuseStep 187898687 = 281848031) B281848031
theorem B11280667 : Blo 1040609 11280667 := bstep (se 1 (by rfl) ⟨8460500, by rfl⟩ : syracuseStep 11280667 = 16921001) B16921001
theorem B4761737 : Blo 1040609 4761737 := bstep (se 2 (by rfl) ⟨1785651, by rfl⟩ : syracuseStep 4761737 = 3571303) B3571303
theorem B3517181 : Blo 1040609 3517181 := bstep (se 3 (by rfl) ⟨659471, by rfl⟩ : syracuseStep 3517181 = 1318943) B1318943
theorem B1584155 : Blo 1040609 1584155 := bstep (se 1 (by rfl) ⟨1188116, by rfl⟩ : syracuseStep 1584155 = 2376233) B2376233
theorem B2502991 : Blo 1040609 2502991 := bstep (se 1 (by rfl) ⟨1877243, by rfl⟩ : syracuseStep 2502991 = 3754487) B3754487
theorem B16890383 : Blo 1040609 16890383 := bstep (se 1 (by rfl) ⟨12667787, by rfl⟩ : syracuseStep 16890383 = 25335575) B25335575
theorem B25737983 : Blo 1040609 25737983 := bstep (se 1 (by rfl) ⟨19303487, by rfl⟩ : syracuseStep 25737983 = 38606975) B38606975
theorem B5941672799 : Blo 1040609 5941672799 := bstep (se 1 (by rfl) ⟨4456254599, by rfl⟩ : syracuseStep 5941672799 = 8912509199) B8912509199
theorem B3522473 : Blo 1040609 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B2345615 : Blo 1040609 2345615 := bstep (se 1 (by rfl) ⟨1759211, by rfl⟩ : syracuseStep 2345615 = 3518423) B3518423
theorem B6672127 : Blo 1040609 6672127 := bstep (se 1 (by rfl) ⟨5004095, by rfl⟩ : syracuseStep 6672127 = 10008191) B10008191
theorem B1561295 : Blo 1040609 1561295 := bstep (se 1 (by rfl) ⟨1170971, by rfl⟩ : syracuseStep 1561295 = 2341943) B2341943
theorem B5002175 : Blo 1040609 5002175 := bstep (se 1 (by rfl) ⟨3751631, by rfl⟩ : syracuseStep 5002175 = 7503263) B7503263
theorem B1562153 : Blo 1040609 1562153 := bstep (se 2 (by rfl) ⟨585807, by rfl⟩ : syracuseStep 1562153 = 1171615) B1171615
theorem B1759279 : Blo 1040609 1759279 := bstep (se 1 (by rfl) ⟨1319459, by rfl⟩ : syracuseStep 1759279 = 2638919) B2638919
theorem B5626367 : Blo 1040609 5626367 := bstep (se 1 (by rfl) ⟨4219775, by rfl⟩ : syracuseStep 5626367 = 8439551) B8439551
theorem B1563227 : Blo 1040609 1563227 := bstep (se 1 (by rfl) ⟨1172420, by rfl⟩ : syracuseStep 1563227 = 2344841) B2344841
theorem B1563305 : Blo 1040609 1563305 := bstep (se 2 (by rfl) ⟨586239, by rfl⟩ : syracuseStep 1563305 = 1172479) B1172479
theorem B1563815 : Blo 1040609 1563815 := bstep (se 1 (by rfl) ⟨1172861, by rfl⟩ : syracuseStep 1563815 = 2345723) B2345723
theorem B1564271 : Blo 1040609 1564271 := bstep (se 1 (by rfl) ⟨1173203, by rfl⟩ : syracuseStep 1564271 = 2346407) B2346407
theorem B6676127 : Blo 1040609 6676127 := bstep (se 1 (by rfl) ⟨5007095, by rfl⟩ : syracuseStep 6676127 = 10014191) B10014191
theorem B6676843 : Blo 1040609 6676843 := bstep (se 1 (by rfl) ⟨5007632, by rfl⟩ : syracuseStep 6676843 = 10015265) B10015265
theorem B5268563 : Blo 1040609 5268563 := bstep (se 1 (by rfl) ⟨3951422, by rfl⟩ : syracuseStep 5268563 = 7902845) B7902845
theorem B1042267 : Blo 1040609 1042267 := bstep (se 1 (by rfl) ⟨781700, by rfl⟩ : syracuseStep 1042267 = 1563401) B1563401
theorem B10709135 : Blo 1040609 10709135 := bstep (se 1 (by rfl) ⟨8031851, by rfl⟩ : syracuseStep 10709135 = 16063703) B16063703
theorem B1043487 : Blo 1040609 1043487 := bstep (se 1 (by rfl) ⟨782615, by rfl⟩ : syracuseStep 1043487 = 1565231) B1565231
theorem B1043775 : Blo 1040609 1043775 := bstep (se 1 (by rfl) ⟨782831, by rfl⟩ : syracuseStep 1043775 = 1565663) B1565663
theorem B1338859 : Blo 1040609 1338859 := bstep (se 1 (by rfl) ⟨1004144, by rfl⟩ : syracuseStep 1338859 = 2008289) B2008289
theorem B6682175 : Blo 1040609 6682175 := bstep (se 1 (by rfl) ⟨5011631, by rfl⟩ : syracuseStep 6682175 = 10023263) B10023263
theorem B3569417 : Blo 1040609 3569417 := bstep (se 2 (by rfl) ⟨1338531, by rfl⟩ : syracuseStep 3569417 = 2677063) B2677063
theorem B6027583 : Blo 1040609 6027583 := bstep (se 1 (by rfl) ⟨4520687, by rfl⟩ : syracuseStep 6027583 = 9041375) B9041375
theorem B3963937 : Blo 1040609 3963937 := bstep (se 2 (by rfl) ⟨1486476, by rfl⟩ : syracuseStep 3963937 = 2972953) B2972953
theorem B15040889 : Blo 1040609 15040889 := bstep (se 2 (by rfl) ⟨5640333, by rfl⟩ : syracuseStep 15040889 = 11280667) B11280667
theorem B16910363 : Blo 1040609 16910363 := bstep (se 1 (by rfl) ⟨12682772, by rfl⟩ : syracuseStep 16910363 = 25365545) B25365545
theorem B3512375 : Blo 1040609 3512375 := bstep (se 1 (by rfl) ⟨2634281, by rfl⟩ : syracuseStep 3512375 = 5268563) B5268563
theorem B8036777 : Blo 1040609 8036777 := bstep (se 2 (by rfl) ⟨3013791, by rfl⟩ : syracuseStep 8036777 = 6027583) B6027583
theorem B5285249 : Blo 1040609 5285249 := bstep (se 2 (by rfl) ⟨1981968, by rfl⟩ : syracuseStep 5285249 = 3963937) B3963937
theorem B3519935 : Blo 1040609 3519935 := bstep (se 1 (by rfl) ⟨2639951, by rfl⟩ : syracuseStep 3519935 = 5279903) B5279903
theorem B13350815 : Blo 1040609 13350815 := bstep (se 1 (by rfl) ⟨10013111, by rfl⟩ : syracuseStep 13350815 = 20026223) B20026223
theorem B16038091 : Blo 1040609 16038091 := bstep (se 1 (by rfl) ⟨12028568, by rfl⟩ : syracuseStep 16038091 = 24057137) B24057137
theorem B3750911 : Blo 1040609 3750911 := bstep (se 1 (by rfl) ⟨2813183, by rfl⟩ : syracuseStep 3750911 = 5626367) B5626367
theorem B1785145 : Blo 1040609 1785145 := bstep (se 2 (by rfl) ⟨669429, by rfl⟩ : syracuseStep 1785145 = 1338859) B1338859
theorem B8896169 : Blo 1040609 8896169 := bstep (se 2 (by rfl) ⟨3336063, by rfl⟩ : syracuseStep 8896169 = 6672127) B6672127
theorem B2344787 : Blo 1040609 2344787 := bstep (se 1 (by rfl) ⟨1758590, by rfl⟩ : syracuseStep 2344787 = 3517181) B3517181
theorem B15844460797 : Blo 1040609 15844460797 := bstep (se 3 (by rfl) ⟨2970836399, by rfl⟩ : syracuseStep 15844460797 = 5941672799) B5941672799
theorem B2345705 : Blo 1040609 2345705 := bstep (se 2 (by rfl) ⟨879639, by rfl⟩ : syracuseStep 2345705 = 1759279) B1759279
theorem B2379611 : Blo 1040609 2379611 := bstep (se 1 (by rfl) ⟨1784708, by rfl⟩ : syracuseStep 2379611 = 3569417) B3569417
theorem B11260255 : Blo 1040609 11260255 := bstep (se 1 (by rfl) ⟨8445191, by rfl⟩ : syracuseStep 11260255 = 16890383) B16890383
theorem B17158655 : Blo 1040609 17158655 := bstep (se 1 (by rfl) ⟨12868991, by rfl⟩ : syracuseStep 17158655 = 25737983) B25737983
theorem B2348315 : Blo 1040609 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B8902457 : Blo 1040609 8902457 := bstep (se 2 (by rfl) ⟨3338421, by rfl⟩ : syracuseStep 8902457 = 6676843) B6676843
theorem B9526025 : Blo 1040609 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B1563743 : Blo 1040609 1563743 := bstep (se 1 (by rfl) ⟨1172807, by rfl⟩ : syracuseStep 1563743 = 2345615) B2345615
theorem B1040863 : Blo 1040609 1040863 := bstep (se 1 (by rfl) ⟨780647, by rfl⟩ : syracuseStep 1040863 = 1561295) B1561295
theorem B3334783 : Blo 1040609 3334783 := bstep (se 1 (by rfl) ⟨2501087, by rfl⟩ : syracuseStep 3334783 = 5002175) B5002175
theorem B1041435 : Blo 1040609 1041435 := bstep (se 1 (by rfl) ⟨781076, by rfl⟩ : syracuseStep 1041435 = 1562153) B1562153
theorem B1042151 : Blo 1040609 1042151 := bstep (se 1 (by rfl) ⟨781613, by rfl⟩ : syracuseStep 1042151 = 1563227) B1563227
theorem B1042203 : Blo 1040609 1042203 := bstep (se 1 (by rfl) ⟨781652, by rfl⟩ : syracuseStep 1042203 = 1563305) B1563305
theorem B125265791 : Blo 1040609 125265791 := bstep (se 1 (by rfl) ⟨93949343, by rfl⟩ : syracuseStep 125265791 = 187898687) B187898687
theorem B1042543 : Blo 1040609 1042543 := bstep (se 1 (by rfl) ⟨781907, by rfl⟩ : syracuseStep 1042543 = 1563815) B1563815
theorem B1042847 : Blo 1040609 1042847 := bstep (se 1 (by rfl) ⟨782135, by rfl⟩ : syracuseStep 1042847 = 1564271) B1564271
theorem B4450751 : Blo 1040609 4450751 := bstep (se 1 (by rfl) ⟨3338063, by rfl⟩ : syracuseStep 4450751 = 6676127) B6676127
theorem B3337321 : Blo 1040609 3337321 := bstep (se 2 (by rfl) ⟨1251495, by rfl⟩ : syracuseStep 3337321 = 2502991) B2502991
theorem B3174491 : Blo 1040609 3174491 := bstep (se 1 (by rfl) ⟨2380868, by rfl⟩ : syracuseStep 3174491 = 4761737) B4761737
theorem B7139423 : Blo 1040609 7139423 := bstep (se 1 (by rfl) ⟨5354567, by rfl⟩ : syracuseStep 7139423 = 10709135) B10709135
theorem B4224413 : Blo 1040609 4224413 := bstep (se 3 (by rfl) ⟨792077, by rfl⟩ : syracuseStep 4224413 = 1584155) B1584155
theorem B4454783 : Blo 1040609 4454783 := bstep (se 1 (by rfl) ⟨3341087, by rfl⟩ : syracuseStep 4454783 = 6682175) B6682175
theorem B10027259 : Blo 1040609 10027259 := bstep (se 1 (by rfl) ⟨7520444, by rfl⟩ : syracuseStep 10027259 = 15040889) B15040889
theorem B11273575 : Blo 1040609 11273575 := bstep (se 1 (by rfl) ⟨8455181, by rfl⟩ : syracuseStep 11273575 = 16910363) B16910363
theorem B5934971 : Blo 1040609 5934971 := bstep (se 1 (by rfl) ⟨4451228, by rfl⟩ : syracuseStep 5934971 = 8902457) B8902457
theorem B15013673 : Blo 1040609 15013673 := bstep (se 2 (by rfl) ⟨5630127, by rfl⟩ : syracuseStep 15013673 = 11260255) B11260255
theorem B4759615 : Blo 1040609 4759615 := bstep (se 1 (by rfl) ⟨3569711, by rfl⟩ : syracuseStep 4759615 = 7139423) B7139423
theorem B2500607 : Blo 1040609 2500607 := bstep (se 1 (by rfl) ⟨1875455, by rfl⟩ : syracuseStep 2500607 = 3750911) B3750911
theorem B8465309 : Blo 1040609 8465309 := bstep (se 3 (by rfl) ⟨1587245, by rfl⟩ : syracuseStep 8465309 = 3174491) B3174491
theorem B45756413 : Blo 1040609 45756413 := bstep (se 3 (by rfl) ⟨8579327, by rfl⟩ : syracuseStep 45756413 = 17158655) B17158655
theorem B1586407 : Blo 1040609 1586407 := bstep (se 1 (by rfl) ⟨1189805, by rfl⟩ : syracuseStep 1586407 = 2379611) B2379611
theorem B2341583 : Blo 1040609 2341583 := bstep (se 1 (by rfl) ⟨1756187, by rfl⟩ : syracuseStep 2341583 = 3512375) B3512375
theorem B5357851 : Blo 1040609 5357851 := bstep (se 1 (by rfl) ⟨4018388, by rfl⟩ : syracuseStep 5357851 = 8036777) B8036777
theorem B3523499 : Blo 1040609 3523499 := bstep (se 1 (by rfl) ⟨2642624, by rfl⟩ : syracuseStep 3523499 = 5285249) B5285249
theorem B83510527 : Blo 1040609 83510527 := bstep (se 1 (by rfl) ⟨62632895, by rfl⟩ : syracuseStep 83510527 = 125265791) B125265791
theorem B2967167 : Blo 1040609 2967167 := bstep (se 1 (by rfl) ⟨2225375, by rfl⟩ : syracuseStep 2967167 = 4450751) B4450751
theorem B21384121 : Blo 1040609 21384121 := bstep (se 2 (by rfl) ⟨8019045, by rfl⟩ : syracuseStep 21384121 = 16038091) B16038091
theorem B2346623 : Blo 1040609 2346623 := bstep (se 1 (by rfl) ⟨1759967, by rfl⟩ : syracuseStep 2346623 = 3519935) B3519935
theorem B8900543 : Blo 1040609 8900543 := bstep (se 1 (by rfl) ⟨6675407, by rfl⟩ : syracuseStep 8900543 = 13350815) B13350815
theorem B2969855 : Blo 1040609 2969855 := bstep (se 1 (by rfl) ⟨2227391, by rfl⟩ : syracuseStep 2969855 = 4454783) B4454783
theorem B2380193 : Blo 1040609 2380193 := bstep (se 2 (by rfl) ⟨892572, by rfl⟩ : syracuseStep 2380193 = 1785145) B1785145
theorem B4446377 : Blo 1040609 4446377 := bstep (se 2 (by rfl) ⟨1667391, by rfl⟩ : syracuseStep 4446377 = 3334783) B3334783
theorem B1563191 : Blo 1040609 1563191 := bstep (se 1 (by rfl) ⟨1172393, by rfl⟩ : syracuseStep 1563191 = 2344787) B2344787
theorem B1563803 : Blo 1040609 1563803 := bstep (se 1 (by rfl) ⟨1172852, by rfl⟩ : syracuseStep 1563803 = 2345705) B2345705
theorem B21125947729 : Blo 1040609 21125947729 := bstep (se 2 (by rfl) ⟨7922230398, by rfl⟩ : syracuseStep 21125947729 = 15844460797) B15844460797
theorem B1565543 : Blo 1040609 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B11265101 : Blo 1040609 11265101 := bstep (se 3 (by rfl) ⟨2112206, by rfl⟩ : syracuseStep 11265101 = 4224413) B4224413
theorem B4449761 : Blo 1040609 4449761 := bstep (se 2 (by rfl) ⟨1668660, by rfl⟩ : syracuseStep 4449761 = 3337321) B3337321
theorem B6350683 : Blo 1040609 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B1042495 : Blo 1040609 1042495 := bstep (se 1 (by rfl) ⟨781871, by rfl⟩ : syracuseStep 1042495 = 1563743) B1563743
theorem B5930779 : Blo 1040609 5930779 := bstep (se 1 (by rfl) ⟨4448084, by rfl⟩ : syracuseStep 5930779 = 8896169) B8896169
theorem B6684839 : Blo 1040609 6684839 := bstep (se 1 (by rfl) ⟨5013629, by rfl⟩ : syracuseStep 6684839 = 10027259) B10027259
theorem B28167930305 : Blo 1040609 28167930305 := bstep (se 2 (by rfl) ⟨10562973864, by rfl⟩ : syracuseStep 28167930305 = 21125947729) B21125947729
theorem B111347369 : Blo 1040609 111347369 := bstep (se 2 (by rfl) ⟨41755263, by rfl⟩ : syracuseStep 111347369 = 83510527) B83510527
theorem B5933695 : Blo 1040609 5933695 := bstep (se 1 (by rfl) ⟨4450271, by rfl⟩ : syracuseStep 5933695 = 8900543) B8900543
theorem B28512161 : Blo 1040609 28512161 := bstep (se 2 (by rfl) ⟨10692060, by rfl⟩ : syracuseStep 28512161 = 21384121) B21384121
theorem B114300821 : Blo 1040609 114300821 := bstep (se 6 (by rfl) ⟨2678925, by rfl⟩ : syracuseStep 114300821 = 5357851) B5357851
theorem B7510067 : Blo 1040609 7510067 := bstep (se 1 (by rfl) ⟨5632550, by rfl⟩ : syracuseStep 7510067 = 11265101) B11265101
theorem B5643539 : Blo 1040609 5643539 := bstep (se 1 (by rfl) ⟨4232654, by rfl⟩ : syracuseStep 5643539 = 8465309) B8465309
theorem B7907705 : Blo 1040609 7907705 := bstep (se 2 (by rfl) ⟨2965389, by rfl⟩ : syracuseStep 7907705 = 5930779) B5930779
theorem B1978111 : Blo 1040609 1978111 := bstep (se 1 (by rfl) ⟨1483583, by rfl⟩ : syracuseStep 1978111 = 2967167) B2967167
theorem B8467577 : Blo 1040609 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B1979903 : Blo 1040609 1979903 := bstep (se 1 (by rfl) ⟨1484927, by rfl⟩ : syracuseStep 1979903 = 2969855) B2969855
theorem B1586795 : Blo 1040609 1586795 := bstep (se 1 (by rfl) ⟨1190096, by rfl⟩ : syracuseStep 1586795 = 2380193) B2380193
theorem B10009115 : Blo 1040609 10009115 := bstep (se 1 (by rfl) ⟨7506836, by rfl⟩ : syracuseStep 10009115 = 15013673) B15013673
theorem B2964251 : Blo 1040609 2964251 := bstep (se 1 (by rfl) ⟨2223188, by rfl⟩ : syracuseStep 2964251 = 4446377) B4446377
theorem B2966507 : Blo 1040609 2966507 := bstep (se 1 (by rfl) ⟨2224880, by rfl⟩ : syracuseStep 2966507 = 4449761) B4449761
theorem B2115209 : Blo 1040609 2115209 := bstep (se 2 (by rfl) ⟨793203, by rfl⟩ : syracuseStep 2115209 = 1586407) B1586407
theorem B1561055 : Blo 1040609 1561055 := bstep (se 1 (by rfl) ⟨1170791, by rfl⟩ : syracuseStep 1561055 = 2341583) B2341583
theorem B6346153 : Blo 1040609 6346153 := bstep (se 2 (by rfl) ⟨2379807, by rfl⟩ : syracuseStep 6346153 = 4759615) B4759615
theorem B2348999 : Blo 1040609 2348999 := bstep (se 1 (by rfl) ⟨1761749, by rfl⟩ : syracuseStep 2348999 = 3523499) B3523499
theorem B15031433 : Blo 1040609 15031433 := bstep (se 2 (by rfl) ⟨5636787, by rfl⟩ : syracuseStep 15031433 = 11273575) B11273575
theorem B1564415 : Blo 1040609 1564415 := bstep (se 1 (by rfl) ⟨1173311, by rfl⟩ : syracuseStep 1564415 = 2346623) B2346623
theorem B3956647 : Blo 1040609 3956647 := bstep (se 1 (by rfl) ⟨2967485, by rfl⟩ : syracuseStep 3956647 = 5934971) B5934971
theorem B1042127 : Blo 1040609 1042127 := bstep (se 1 (by rfl) ⟨781595, by rfl⟩ : syracuseStep 1042127 = 1563191) B1563191
theorem B1042535 : Blo 1040609 1042535 := bstep (se 1 (by rfl) ⟨781901, by rfl⟩ : syracuseStep 1042535 = 1563803) B1563803
theorem B1043695 : Blo 1040609 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B1667071 : Blo 1040609 1667071 := bstep (se 1 (by rfl) ⟨1250303, by rfl⟩ : syracuseStep 1667071 = 2500607) B2500607
theorem B30504275 : Blo 1040609 30504275 := bstep (se 1 (by rfl) ⟨22878206, by rfl⟩ : syracuseStep 30504275 = 45756413) B45756413
theorem B4456559 : Blo 1040609 4456559 := bstep (se 1 (by rfl) ⟨3342419, by rfl⟩ : syracuseStep 4456559 = 6684839) B6684839
theorem B18778620203 : Blo 1040609 18778620203 := bstep (se 1 (by rfl) ⟨14083965152, by rfl⟩ : syracuseStep 18778620203 = 28167930305) B28167930305
theorem B1410139 : Blo 1040609 1410139 := bstep (se 1 (by rfl) ⟨1057604, by rfl⟩ : syracuseStep 1410139 = 2115209) B2115209
theorem B19008107 : Blo 1040609 19008107 := bstep (se 1 (by rfl) ⟨14256080, by rfl⟩ : syracuseStep 19008107 = 28512161) B28512161
theorem B5279741 : Blo 1040609 5279741 := bstep (se 3 (by rfl) ⟨989951, by rfl⟩ : syracuseStep 5279741 = 1979903) B1979903
theorem B4231453 : Blo 1040609 4231453 := bstep (se 3 (by rfl) ⟨793397, by rfl⟩ : syracuseStep 4231453 = 1586795) B1586795
theorem B5645051 : Blo 1040609 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B1976167 : Blo 1040609 1976167 := bstep (se 1 (by rfl) ⟨1482125, by rfl⟩ : syracuseStep 1976167 = 2964251) B2964251
theorem B8891045 : Blo 1040609 8891045 := bstep (se 4 (by rfl) ⟨833535, by rfl⟩ : syracuseStep 8891045 = 1667071) B1667071
theorem B1977671 : Blo 1040609 1977671 := bstep (se 1 (by rfl) ⟨1483253, by rfl⟩ : syracuseStep 1977671 = 2966507) B2966507
theorem B74231579 : Blo 1040609 74231579 := bstep (se 1 (by rfl) ⟨55673684, by rfl⟩ : syracuseStep 74231579 = 111347369) B111347369
theorem B7911593 : Blo 1040609 7911593 := bstep (se 2 (by rfl) ⟨2966847, by rfl⟩ : syracuseStep 7911593 = 5933695) B5933695
theorem B76200547 : Blo 1040609 76200547 := bstep (se 1 (by rfl) ⟨57150410, by rfl⟩ : syracuseStep 76200547 = 114300821) B114300821
theorem B2637481 : Blo 1040609 2637481 := bstep (se 2 (by rfl) ⟨989055, by rfl⟩ : syracuseStep 2637481 = 1978111) B1978111
theorem B20336183 : Blo 1040609 20336183 := bstep (se 1 (by rfl) ⟨15252137, by rfl⟩ : syracuseStep 20336183 = 30504275) B30504275
theorem B6672743 : Blo 1040609 6672743 := bstep (se 1 (by rfl) ⟨5004557, by rfl⟩ : syracuseStep 6672743 = 10009115) B10009115
theorem B1040703 : Blo 1040609 1040703 := bstep (se 1 (by rfl) ⟨780527, by rfl⟩ : syracuseStep 1040703 = 1561055) B1561055
theorem B1565999 : Blo 1040609 1565999 := bstep (se 1 (by rfl) ⟨1174499, by rfl⟩ : syracuseStep 1565999 = 2348999) B2348999
theorem B5006711 : Blo 1040609 5006711 := bstep (se 1 (by rfl) ⟨3755033, by rfl⟩ : syracuseStep 5006711 = 7510067) B7510067
theorem B10020955 : Blo 1040609 10020955 := bstep (se 1 (by rfl) ⟨7515716, by rfl⟩ : syracuseStep 10020955 = 15031433) B15031433
theorem B3762359 : Blo 1040609 3762359 := bstep (se 1 (by rfl) ⟨2821769, by rfl⟩ : syracuseStep 3762359 = 5643539) B5643539
theorem B1042943 : Blo 1040609 1042943 := bstep (se 1 (by rfl) ⟨782207, by rfl⟩ : syracuseStep 1042943 = 1564415) B1564415
theorem B5271803 : Blo 1040609 5271803 := bstep (se 1 (by rfl) ⟨3953852, by rfl⟩ : syracuseStep 5271803 = 7907705) B7907705
theorem B33846149 : Blo 1040609 33846149 := bstep (se 4 (by rfl) ⟨3173076, by rfl⟩ : syracuseStep 33846149 = 6346153) B6346153
theorem B5275529 : Blo 1040609 5275529 := bstep (se 2 (by rfl) ⟨1978323, by rfl⟩ : syracuseStep 5275529 = 3956647) B3956647
theorem B12519080135 : Blo 1040609 12519080135 := bstep (se 1 (by rfl) ⟨9389310101, by rfl⟩ : syracuseStep 12519080135 = 18778620203) B18778620203
theorem B5641937 : Blo 1040609 5641937 := bstep (se 2 (by rfl) ⟨2115726, by rfl⟩ : syracuseStep 5641937 = 4231453) B4231453
theorem B1318447 : Blo 1040609 1318447 := bstep (se 1 (by rfl) ⟨988835, by rfl⟩ : syracuseStep 1318447 = 1977671) B1977671
theorem B3514535 : Blo 1040609 3514535 := bstep (se 1 (by rfl) ⟨2635901, by rfl⟩ : syracuseStep 3514535 = 5271803) B5271803
theorem B3516641 : Blo 1040609 3516641 := bstep (se 2 (by rfl) ⟨1318740, by rfl⟩ : syracuseStep 3516641 = 2637481) B2637481
theorem B3517019 : Blo 1040609 3517019 := bstep (se 1 (by rfl) ⟨2637764, by rfl⟩ : syracuseStep 3517019 = 5275529) B5275529
theorem B1880185 : Blo 1040609 1880185 := bstep (se 2 (by rfl) ⟨705069, by rfl⟩ : syracuseStep 1880185 = 1410139) B1410139
theorem B2634889 : Blo 1040609 2634889 := bstep (se 2 (by rfl) ⟨988083, by rfl⟩ : syracuseStep 2634889 = 1976167) B1976167
theorem B3519827 : Blo 1040609 3519827 := bstep (se 1 (by rfl) ⟨2639870, by rfl⟩ : syracuseStep 3519827 = 5279741) B5279741
theorem B2508239 : Blo 1040609 2508239 := bstep (se 1 (by rfl) ⟨1881179, by rfl⟩ : syracuseStep 2508239 = 3762359) B3762359
theorem B22564099 : Blo 1040609 22564099 := bstep (se 1 (by rfl) ⟨16923074, by rfl⟩ : syracuseStep 22564099 = 33846149) B33846149
theorem B101600729 : Blo 1040609 101600729 := bstep (se 2 (by rfl) ⟨38100273, by rfl⟩ : syracuseStep 101600729 = 76200547) B76200547
theorem B11884157 : Blo 1040609 11884157 := bstep (se 3 (by rfl) ⟨2228279, by rfl⟩ : syracuseStep 11884157 = 4456559) B4456559
theorem B12672071 : Blo 1040609 12672071 := bstep (se 1 (by rfl) ⟨9504053, by rfl⟩ : syracuseStep 12672071 = 19008107) B19008107
theorem B13557455 : Blo 1040609 13557455 := bstep (se 1 (by rfl) ⟨10168091, by rfl⟩ : syracuseStep 13557455 = 20336183) B20336183
theorem B13361273 : Blo 1040609 13361273 := bstep (se 2 (by rfl) ⟨5010477, by rfl⟩ : syracuseStep 13361273 = 10020955) B10020955
theorem B4448495 : Blo 1040609 4448495 := bstep (se 1 (by rfl) ⟨3336371, by rfl⟩ : syracuseStep 4448495 = 6672743) B6672743
theorem B3763367 : Blo 1040609 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B1043999 : Blo 1040609 1043999 := bstep (se 1 (by rfl) ⟨782999, by rfl⟩ : syracuseStep 1043999 = 1565999) B1565999
theorem B3337807 : Blo 1040609 3337807 := bstep (se 1 (by rfl) ⟨2503355, by rfl⟩ : syracuseStep 3337807 = 5006711) B5006711
theorem B5927363 : Blo 1040609 5927363 := bstep (se 1 (by rfl) ⟨4445522, by rfl⟩ : syracuseStep 5927363 = 8891045) B8891045
theorem B5274395 : Blo 1040609 5274395 := bstep (se 1 (by rfl) ⟨3955796, by rfl⟩ : syracuseStep 5274395 = 7911593) B7911593
theorem B197950877 : Blo 1040609 197950877 := bstep (se 3 (by rfl) ⟨37115789, by rfl⟩ : syracuseStep 197950877 = 74231579) B74231579
theorem B1672159 : Blo 1040609 1672159 := bstep (se 1 (by rfl) ⟨1254119, by rfl⟩ : syracuseStep 1672159 = 2508239) B2508239
theorem B67733819 : Blo 1040609 67733819 := bstep (se 1 (by rfl) ⟨50800364, by rfl⟩ : syracuseStep 67733819 = 101600729) B101600729
theorem B30085465 : Blo 1040609 30085465 := bstep (se 2 (by rfl) ⟨11282049, by rfl⟩ : syracuseStep 30085465 = 22564099) B22564099
theorem B3513185 : Blo 1040609 3513185 := bstep (se 2 (by rfl) ⟨1317444, by rfl⟩ : syracuseStep 3513185 = 2634889) B2634889
theorem B3516263 : Blo 1040609 3516263 := bstep (se 1 (by rfl) ⟨2637197, by rfl⟩ : syracuseStep 3516263 = 5274395) B5274395
theorem B131967251 : Blo 1040609 131967251 := bstep (se 1 (by rfl) ⟨98975438, by rfl⟩ : syracuseStep 131967251 = 197950877) B197950877
theorem B8346053423 : Blo 1040609 8346053423 := bstep (se 1 (by rfl) ⟨6259540067, by rfl⟩ : syracuseStep 8346053423 = 12519080135) B12519080135
theorem B2343023 : Blo 1040609 2343023 := bstep (se 1 (by rfl) ⟨1757267, by rfl⟩ : syracuseStep 2343023 = 3514535) B3514535
theorem B2965663 : Blo 1040609 2965663 := bstep (se 1 (by rfl) ⟨2224247, by rfl⟩ : syracuseStep 2965663 = 4448495) B4448495
theorem B2506913 : Blo 1040609 2506913 := bstep (se 2 (by rfl) ⟨940092, by rfl⟩ : syracuseStep 2506913 = 1880185) B1880185
theorem B2344427 : Blo 1040609 2344427 := bstep (se 1 (by rfl) ⟨1758320, by rfl⟩ : syracuseStep 2344427 = 3516641) B3516641
theorem B2344679 : Blo 1040609 2344679 := bstep (se 1 (by rfl) ⟨1758509, by rfl⟩ : syracuseStep 2344679 = 3517019) B3517019
theorem B2508911 : Blo 1040609 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B3951575 : Blo 1040609 3951575 := bstep (se 1 (by rfl) ⟨2963681, by rfl⟩ : syracuseStep 3951575 = 5927363) B5927363
theorem B2346551 : Blo 1040609 2346551 := bstep (se 1 (by rfl) ⟨1759913, by rfl⟩ : syracuseStep 2346551 = 3519827) B3519827
theorem B1757929 : Blo 1040609 1757929 := bstep (se 2 (by rfl) ⟨659223, by rfl⟩ : syracuseStep 1757929 = 1318447) B1318447
theorem B7922771 : Blo 1040609 7922771 := bstep (se 1 (by rfl) ⟨5942078, by rfl⟩ : syracuseStep 7922771 = 11884157) B11884157
theorem B3761291 : Blo 1040609 3761291 := bstep (se 1 (by rfl) ⟨2820968, by rfl⟩ : syracuseStep 3761291 = 5641937) B5641937
theorem B8448047 : Blo 1040609 8448047 := bstep (se 1 (by rfl) ⟨6336035, by rfl⟩ : syracuseStep 8448047 = 12672071) B12672071
theorem B4450409 : Blo 1040609 4450409 := bstep (se 2 (by rfl) ⟨1668903, by rfl⟩ : syracuseStep 4450409 = 3337807) B3337807
theorem B9038303 : Blo 1040609 9038303 := bstep (se 1 (by rfl) ⟨6778727, by rfl⟩ : syracuseStep 9038303 = 13557455) B13557455
theorem B8907515 : Blo 1040609 8907515 := bstep (se 1 (by rfl) ⟨6680636, by rfl⟩ : syracuseStep 8907515 = 13361273) B13361273
theorem B1671275 : Blo 1040609 1671275 := bstep (se 1 (by rfl) ⟨1253456, by rfl⟩ : syracuseStep 1671275 = 2506913) B2506913
theorem B2229545 : Blo 1040609 2229545 := bstep (se 2 (by rfl) ⟨836079, by rfl⟩ : syracuseStep 2229545 = 1672159) B1672159
theorem B1672607 : Blo 1040609 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B45155879 : Blo 1040609 45155879 := bstep (se 1 (by rfl) ⟨33866909, by rfl⟩ : syracuseStep 45155879 = 67733819) B67733819
theorem B40113953 : Blo 1040609 40113953 := bstep (se 2 (by rfl) ⟨15042732, by rfl⟩ : syracuseStep 40113953 = 30085465) B30085465
theorem B5281847 : Blo 1040609 5281847 := bstep (se 1 (by rfl) ⟨3961385, by rfl⟩ : syracuseStep 5281847 = 7922771) B7922771
theorem B5938343 : Blo 1040609 5938343 := bstep (se 1 (by rfl) ⟨4453757, by rfl⟩ : syracuseStep 5938343 = 8907515) B8907515
theorem B2634383 : Blo 1040609 2634383 := bstep (se 1 (by rfl) ⟨1975787, by rfl⟩ : syracuseStep 2634383 = 3951575) B3951575
theorem B2342123 : Blo 1040609 2342123 := bstep (se 1 (by rfl) ⟨1756592, by rfl⟩ : syracuseStep 2342123 = 3513185) B3513185
theorem B2507527 : Blo 1040609 2507527 := bstep (se 1 (by rfl) ⟨1880645, by rfl⟩ : syracuseStep 2507527 = 3761291) B3761291
theorem B2343905 : Blo 1040609 2343905 := bstep (se 2 (by rfl) ⟨878964, by rfl⟩ : syracuseStep 2343905 = 1757929) B1757929
theorem B2344175 : Blo 1040609 2344175 := bstep (se 1 (by rfl) ⟨1758131, by rfl⟩ : syracuseStep 2344175 = 3516263) B3516263
theorem B2966939 : Blo 1040609 2966939 := bstep (se 1 (by rfl) ⟨2225204, by rfl⟩ : syracuseStep 2966939 = 4450409) B4450409
theorem B22256142461 : Blo 1040609 22256142461 := bstep (se 3 (by rfl) ⟨4173026711, by rfl⟩ : syracuseStep 22256142461 = 8346053423) B8346053423
theorem B1562015 : Blo 1040609 1562015 := bstep (se 1 (by rfl) ⟨1171511, by rfl⟩ : syracuseStep 1562015 = 2343023) B2343023
theorem B3954217 : Blo 1040609 3954217 := bstep (se 2 (by rfl) ⟨1482831, by rfl⟩ : syracuseStep 3954217 = 2965663) B2965663
theorem B1562951 : Blo 1040609 1562951 := bstep (se 1 (by rfl) ⟨1172213, by rfl⟩ : syracuseStep 1562951 = 2344427) B2344427
theorem B1563119 : Blo 1040609 1563119 := bstep (se 1 (by rfl) ⟨1172339, by rfl⟩ : syracuseStep 1563119 = 2344679) B2344679
theorem B1564367 : Blo 1040609 1564367 := bstep (se 1 (by rfl) ⟨1173275, by rfl⟩ : syracuseStep 1564367 = 2346551) B2346551
theorem B5632031 : Blo 1040609 5632031 := bstep (se 1 (by rfl) ⟨4224023, by rfl⟩ : syracuseStep 5632031 = 8448047) B8448047
theorem B87978167 : Blo 1040609 87978167 := bstep (se 1 (by rfl) ⟨65983625, by rfl⟩ : syracuseStep 87978167 = 131967251) B131967251
theorem B6025535 : Blo 1040609 6025535 := bstep (se 1 (by rfl) ⟨4519151, by rfl⟩ : syracuseStep 6025535 = 9038303) B9038303
theorem B1114183 : Blo 1040609 1114183 := bstep (se 1 (by rfl) ⟨835637, by rfl⟩ : syracuseStep 1114183 = 1671275) B1671275
theorem B3343369 : Blo 1040609 3343369 := bstep (se 2 (by rfl) ⟨1253763, by rfl⟩ : syracuseStep 3343369 = 2507527) B2507527
theorem B4460285 : Blo 1040609 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B26742635 : Blo 1040609 26742635 := bstep (se 1 (by rfl) ⟨20056976, by rfl⟩ : syracuseStep 26742635 = 40113953) B40113953
theorem B1486363 : Blo 1040609 1486363 := bstep (se 1 (by rfl) ⟨1114772, by rfl⟩ : syracuseStep 1486363 = 2229545) B2229545
theorem B1977959 : Blo 1040609 1977959 := bstep (se 1 (by rfl) ⟨1483469, by rfl⟩ : syracuseStep 1977959 = 2966939) B2966939
theorem B14837428307 : Blo 1040609 14837428307 := bstep (se 1 (by rfl) ⟨11128071230, by rfl⟩ : syracuseStep 14837428307 = 22256142461) B22256142461
theorem B3521231 : Blo 1040609 3521231 := bstep (se 1 (by rfl) ⟨2640923, by rfl⟩ : syracuseStep 3521231 = 5281847) B5281847
theorem B3754687 : Blo 1040609 3754687 := bstep (se 1 (by rfl) ⟨2816015, by rfl⟩ : syracuseStep 3754687 = 5632031) B5632031
theorem B4017023 : Blo 1040609 4017023 := bstep (se 1 (by rfl) ⟨3012767, by rfl⟩ : syracuseStep 4017023 = 6025535) B6025535
theorem B1756255 : Blo 1040609 1756255 := bstep (se 1 (by rfl) ⟨1317191, by rfl⟩ : syracuseStep 1756255 = 2634383) B2634383
theorem B1561415 : Blo 1040609 1561415 := bstep (se 1 (by rfl) ⟨1171061, by rfl⟩ : syracuseStep 1561415 = 2342123) B2342123
theorem B1562603 : Blo 1040609 1562603 := bstep (se 1 (by rfl) ⟨1171952, by rfl⟩ : syracuseStep 1562603 = 2343905) B2343905
theorem B1562783 : Blo 1040609 1562783 := bstep (se 1 (by rfl) ⟨1172087, by rfl⟩ : syracuseStep 1562783 = 2344175) B2344175
theorem B30103919 : Blo 1040609 30103919 := bstep (se 1 (by rfl) ⟨22577939, by rfl⟩ : syracuseStep 30103919 = 45155879) B45155879
theorem B1041343 : Blo 1040609 1041343 := bstep (se 1 (by rfl) ⟨781007, by rfl⟩ : syracuseStep 1041343 = 1562015) B1562015
theorem B1041967 : Blo 1040609 1041967 := bstep (se 1 (by rfl) ⟨781475, by rfl⟩ : syracuseStep 1041967 = 1562951) B1562951
theorem B1042079 : Blo 1040609 1042079 := bstep (se 1 (by rfl) ⟨781559, by rfl⟩ : syracuseStep 1042079 = 1563119) B1563119
theorem B3958895 : Blo 1040609 3958895 := bstep (se 1 (by rfl) ⟨2969171, by rfl⟩ : syracuseStep 3958895 = 5938343) B5938343
theorem B1042911 : Blo 1040609 1042911 := bstep (se 1 (by rfl) ⟨782183, by rfl⟩ : syracuseStep 1042911 = 1564367) B1564367
theorem B5272289 : Blo 1040609 5272289 := bstep (se 2 (by rfl) ⟨1977108, by rfl⟩ : syracuseStep 5272289 = 3954217) B3954217
theorem B58652111 : Blo 1040609 58652111 := bstep (se 1 (by rfl) ⟨43989083, by rfl⟩ : syracuseStep 58652111 = 87978167) B87978167
theorem B4457825 : Blo 1040609 4457825 := bstep (se 2 (by rfl) ⟨1671684, by rfl⟩ : syracuseStep 4457825 = 3343369) B3343369
theorem B17828423 : Blo 1040609 17828423 := bstep (se 1 (by rfl) ⟨13371317, by rfl⟩ : syracuseStep 17828423 = 26742635) B26742635
theorem B156405629 : Blo 1040609 156405629 := bstep (se 3 (by rfl) ⟨29326055, by rfl⟩ : syracuseStep 156405629 = 58652111) B58652111
theorem B9891618871 : Blo 1040609 9891618871 := bstep (se 1 (by rfl) ⟨7418714153, by rfl⟩ : syracuseStep 9891618871 = 14837428307) B14837428307
theorem B3514859 : Blo 1040609 3514859 := bstep (se 1 (by rfl) ⟨2636144, by rfl⟩ : syracuseStep 3514859 = 5272289) B5272289
theorem B1485577 : Blo 1040609 1485577 := bstep (se 2 (by rfl) ⟨557091, by rfl⟩ : syracuseStep 1485577 = 1114183) B1114183
theorem B2341673 : Blo 1040609 2341673 := bstep (se 2 (by rfl) ⟨878127, by rfl⟩ : syracuseStep 2341673 = 1756255) B1756255
theorem B20069279 : Blo 1040609 20069279 := bstep (se 1 (by rfl) ⟨15051959, by rfl⟩ : syracuseStep 20069279 = 30103919) B30103919
theorem B1981817 : Blo 1040609 1981817 := bstep (se 2 (by rfl) ⟨743181, by rfl⟩ : syracuseStep 1981817 = 1486363) B1486363
theorem B2639263 : Blo 1040609 2639263 := bstep (se 1 (by rfl) ⟨1979447, by rfl⟩ : syracuseStep 2639263 = 3958895) B3958895
theorem B2347487 : Blo 1040609 2347487 := bstep (se 1 (by rfl) ⟨1760615, by rfl⟩ : syracuseStep 2347487 = 3521231) B3521231
theorem B2678015 : Blo 1040609 2678015 := bstep (se 1 (by rfl) ⟨2008511, by rfl⟩ : syracuseStep 2678015 = 4017023) B4017023
theorem B2973523 : Blo 1040609 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B1040943 : Blo 1040609 1040943 := bstep (se 1 (by rfl) ⟨780707, by rfl⟩ : syracuseStep 1040943 = 1561415) B1561415
theorem B5006249 : Blo 1040609 5006249 := bstep (se 2 (by rfl) ⟨1877343, by rfl⟩ : syracuseStep 5006249 = 3754687) B3754687
theorem B1041735 : Blo 1040609 1041735 := bstep (se 1 (by rfl) ⟨781301, by rfl⟩ : syracuseStep 1041735 = 1562603) B1562603
theorem B1041855 : Blo 1040609 1041855 := bstep (se 1 (by rfl) ⟨781391, by rfl⟩ : syracuseStep 1041855 = 1562783) B1562783
theorem B5274557 : Blo 1040609 5274557 := bstep (se 3 (by rfl) ⟨988979, by rfl⟩ : syracuseStep 5274557 = 1977959) B1977959
theorem B13188825161 : Blo 1040609 13188825161 := bstep (se 2 (by rfl) ⟨4945809435, by rfl⟩ : syracuseStep 13188825161 = 9891618871) B9891618871
theorem B104270419 : Blo 1040609 104270419 := bstep (se 1 (by rfl) ⟨78202814, by rfl⟩ : syracuseStep 104270419 = 156405629) B156405629
theorem B13379519 : Blo 1040609 13379519 := bstep (se 1 (by rfl) ⟨10034639, by rfl⟩ : syracuseStep 13379519 = 20069279) B20069279
theorem B3516371 : Blo 1040609 3516371 := bstep (se 1 (by rfl) ⟨2637278, by rfl⟩ : syracuseStep 3516371 = 5274557) B5274557
theorem B1321211 : Blo 1040609 1321211 := bstep (se 1 (by rfl) ⟨990908, by rfl⟩ : syracuseStep 1321211 = 1981817) B1981817
theorem B3519017 : Blo 1040609 3519017 := bstep (se 2 (by rfl) ⟨1319631, by rfl⟩ : syracuseStep 3519017 = 2639263) B2639263
theorem B1980769 : Blo 1040609 1980769 := bstep (se 2 (by rfl) ⟨742788, by rfl⟩ : syracuseStep 1980769 = 1485577) B1485577
theorem B1785343 : Blo 1040609 1785343 := bstep (se 1 (by rfl) ⟨1339007, by rfl⟩ : syracuseStep 1785343 = 2678015) B2678015
theorem B2343239 : Blo 1040609 2343239 := bstep (se 1 (by rfl) ⟨1757429, by rfl⟩ : syracuseStep 2343239 = 3514859) B3514859
theorem B1561115 : Blo 1040609 1561115 := bstep (se 1 (by rfl) ⟨1170836, by rfl⟩ : syracuseStep 1561115 = 2341673) B2341673
theorem B2971883 : Blo 1040609 2971883 := bstep (se 1 (by rfl) ⟨2228912, by rfl⟩ : syracuseStep 2971883 = 4457825) B4457825
theorem B11885615 : Blo 1040609 11885615 := bstep (se 1 (by rfl) ⟨8914211, by rfl⟩ : syracuseStep 11885615 = 17828423) B17828423
theorem B1564991 : Blo 1040609 1564991 := bstep (se 1 (by rfl) ⟨1173743, by rfl⟩ : syracuseStep 1564991 = 2347487) B2347487
theorem B3337499 : Blo 1040609 3337499 := bstep (se 1 (by rfl) ⟨2503124, by rfl⟩ : syracuseStep 3337499 = 5006249) B5006249
theorem B3964697 : Blo 1040609 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B8919679 : Blo 1040609 8919679 := bstep (se 1 (by rfl) ⟨6689759, by rfl⟩ : syracuseStep 8919679 = 13379519) B13379519
theorem B8792550107 : Blo 1040609 8792550107 := bstep (se 1 (by rfl) ⟨6594412580, by rfl⟩ : syracuseStep 8792550107 = 13188825161) B13188825161
theorem B1981255 : Blo 1040609 1981255 := bstep (se 1 (by rfl) ⟨1485941, by rfl⟩ : syracuseStep 1981255 = 2971883) B2971883
theorem B3523229 : Blo 1040609 3523229 := bstep (se 3 (by rfl) ⟨660605, by rfl⟩ : syracuseStep 3523229 = 1321211) B1321211
theorem B2344247 : Blo 1040609 2344247 := bstep (se 1 (by rfl) ⟨1758185, by rfl⟩ : syracuseStep 2344247 = 3516371) B3516371
theorem B2346011 : Blo 1040609 2346011 := bstep (se 1 (by rfl) ⟨1759508, by rfl⟩ : syracuseStep 2346011 = 3519017) B3519017
theorem B2641025 : Blo 1040609 2641025 := bstep (se 2 (by rfl) ⟨990384, by rfl⟩ : syracuseStep 2641025 = 1980769) B1980769
theorem B2380457 : Blo 1040609 2380457 := bstep (se 2 (by rfl) ⟨892671, by rfl⟩ : syracuseStep 2380457 = 1785343) B1785343
theorem B2643131 : Blo 1040609 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B1562159 : Blo 1040609 1562159 := bstep (se 1 (by rfl) ⟨1171619, by rfl⟩ : syracuseStep 1562159 = 2343239) B2343239
theorem B1040743 : Blo 1040609 1040743 := bstep (se 1 (by rfl) ⟨780557, by rfl⟩ : syracuseStep 1040743 = 1561115) B1561115
theorem B139027225 : Blo 1040609 139027225 := bstep (se 2 (by rfl) ⟨52135209, by rfl⟩ : syracuseStep 139027225 = 104270419) B104270419
theorem B7923743 : Blo 1040609 7923743 := bstep (se 1 (by rfl) ⟨5942807, by rfl⟩ : syracuseStep 7923743 = 11885615) B11885615
theorem B1043327 : Blo 1040609 1043327 := bstep (se 1 (by rfl) ⟨782495, by rfl⟩ : syracuseStep 1043327 = 1564991) B1564991
theorem B2224999 : Blo 1040609 2224999 := bstep (se 1 (by rfl) ⟨1668749, by rfl⟩ : syracuseStep 2224999 = 3337499) B3337499
theorem B185369633 : Blo 1040609 185369633 := bstep (se 2 (by rfl) ⟨69513612, by rfl⟩ : syracuseStep 185369633 = 139027225) B139027225
theorem B11866661 : Blo 1040609 11866661 := bstep (se 4 (by rfl) ⟨1112499, by rfl⟩ : syracuseStep 11866661 = 2224999) B2224999
theorem B5282495 : Blo 1040609 5282495 := bstep (se 1 (by rfl) ⟨3961871, by rfl⟩ : syracuseStep 5282495 = 7923743) B7923743
theorem B1586971 : Blo 1040609 1586971 := bstep (se 1 (by rfl) ⟨1190228, by rfl⟩ : syracuseStep 1586971 = 2380457) B2380457
theorem B2641673 : Blo 1040609 2641673 := bstep (se 2 (by rfl) ⟨990627, by rfl⟩ : syracuseStep 2641673 = 1981255) B1981255
theorem B2348819 : Blo 1040609 2348819 := bstep (se 1 (by rfl) ⟨1761614, by rfl⟩ : syracuseStep 2348819 = 3523229) B3523229
theorem B1562831 : Blo 1040609 1562831 := bstep (se 1 (by rfl) ⟨1172123, by rfl⟩ : syracuseStep 1562831 = 2344247) B2344247
theorem B1564007 : Blo 1040609 1564007 := bstep (se 1 (by rfl) ⟨1173005, by rfl⟩ : syracuseStep 1564007 = 2346011) B2346011
theorem B1760683 : Blo 1040609 1760683 := bstep (se 1 (by rfl) ⟨1320512, by rfl⟩ : syracuseStep 1760683 = 2641025) B2641025
theorem B1762087 : Blo 1040609 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B1041439 : Blo 1040609 1041439 := bstep (se 1 (by rfl) ⟨781079, by rfl⟩ : syracuseStep 1041439 = 1562159) B1562159
theorem B5861700071 : Blo 1040609 5861700071 := bstep (se 1 (by rfl) ⟨4396275053, by rfl⟩ : syracuseStep 5861700071 = 8792550107) B8792550107
theorem B11892905 : Blo 1040609 11892905 := bstep (se 2 (by rfl) ⟨4459839, by rfl⟩ : syracuseStep 11892905 = 8919679) B8919679
theorem B8463845 : Blo 1040609 8463845 := bstep (se 4 (by rfl) ⟨793485, by rfl⟩ : syracuseStep 8463845 = 1586971) B1586971
theorem B123579755 : Blo 1040609 123579755 := bstep (se 1 (by rfl) ⟨92684816, by rfl⟩ : syracuseStep 123579755 = 185369633) B185369633
theorem B7911107 : Blo 1040609 7911107 := bstep (se 1 (by rfl) ⟨5933330, by rfl⟩ : syracuseStep 7911107 = 11866661) B11866661
theorem B3521663 : Blo 1040609 3521663 := bstep (se 1 (by rfl) ⟨2641247, by rfl⟩ : syracuseStep 3521663 = 5282495) B5282495
theorem B3907800047 : Blo 1040609 3907800047 := bstep (se 1 (by rfl) ⟨2930850035, by rfl⟩ : syracuseStep 3907800047 = 5861700071) B5861700071
theorem B2347577 : Blo 1040609 2347577 := bstep (se 2 (by rfl) ⟨880341, by rfl⟩ : syracuseStep 2347577 = 1760683) B1760683
theorem B2349449 : Blo 1040609 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B1761115 : Blo 1040609 1761115 := bstep (se 1 (by rfl) ⟨1320836, by rfl⟩ : syracuseStep 1761115 = 2641673) B2641673
theorem B1565879 : Blo 1040609 1565879 := bstep (se 1 (by rfl) ⟨1174409, by rfl⟩ : syracuseStep 1565879 = 2348819) B2348819
theorem B1041887 : Blo 1040609 1041887 := bstep (se 1 (by rfl) ⟨781415, by rfl⟩ : syracuseStep 1041887 = 1562831) B1562831
theorem B1042671 : Blo 1040609 1042671 := bstep (se 1 (by rfl) ⟨782003, by rfl⟩ : syracuseStep 1042671 = 1564007) B1564007
theorem B7928603 : Blo 1040609 7928603 := bstep (se 1 (by rfl) ⟨5946452, by rfl⟩ : syracuseStep 7928603 = 11892905) B11892905
theorem B5642563 : Blo 1040609 5642563 := bstep (se 1 (by rfl) ⟨4231922, by rfl⟩ : syracuseStep 5642563 = 8463845) B8463845
theorem B82386503 : Blo 1040609 82386503 := bstep (se 1 (by rfl) ⟨61789877, by rfl⟩ : syracuseStep 82386503 = 123579755) B123579755
theorem B5285735 : Blo 1040609 5285735 := bstep (se 1 (by rfl) ⟨3964301, by rfl⟩ : syracuseStep 5285735 = 7928603) B7928603
theorem B2605200031 : Blo 1040609 2605200031 := bstep (se 1 (by rfl) ⟨1953900023, by rfl⟩ : syracuseStep 2605200031 = 3907800047) B3907800047
theorem B2347775 : Blo 1040609 2347775 := bstep (se 1 (by rfl) ⟨1760831, by rfl⟩ : syracuseStep 2347775 = 3521663) B3521663
theorem B2348153 : Blo 1040609 2348153 := bstep (se 2 (by rfl) ⟨880557, by rfl⟩ : syracuseStep 2348153 = 1761115) B1761115
theorem B1565051 : Blo 1040609 1565051 := bstep (se 1 (by rfl) ⟨1173788, by rfl⟩ : syracuseStep 1565051 = 2347577) B2347577
theorem B1566299 : Blo 1040609 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B1043919 : Blo 1040609 1043919 := bstep (se 1 (by rfl) ⟨782939, by rfl⟩ : syracuseStep 1043919 = 1565879) B1565879
theorem B5274071 : Blo 1040609 5274071 := bstep (se 1 (by rfl) ⟨3955553, by rfl⟩ : syracuseStep 5274071 = 7911107) B7911107
theorem B54924335 : Blo 1040609 54924335 := bstep (se 1 (by rfl) ⟨41193251, by rfl⟩ : syracuseStep 54924335 = 82386503) B82386503
theorem B3516047 : Blo 1040609 3516047 := bstep (se 1 (by rfl) ⟨2637035, by rfl⟩ : syracuseStep 3516047 = 5274071) B5274071
theorem B3523823 : Blo 1040609 3523823 := bstep (se 1 (by rfl) ⟨2642867, by rfl⟩ : syracuseStep 3523823 = 5285735) B5285735
theorem B7523417 : Blo 1040609 7523417 := bstep (se 2 (by rfl) ⟨2821281, by rfl⟩ : syracuseStep 7523417 = 5642563) B5642563
theorem B1565183 : Blo 1040609 1565183 := bstep (se 1 (by rfl) ⟨1173887, by rfl⟩ : syracuseStep 1565183 = 2347775) B2347775
theorem B1565435 : Blo 1040609 1565435 := bstep (se 1 (by rfl) ⟨1174076, by rfl⟩ : syracuseStep 1565435 = 2348153) B2348153
theorem B1043367 : Blo 1040609 1043367 := bstep (se 1 (by rfl) ⟨782525, by rfl⟩ : syracuseStep 1043367 = 1565051) B1565051
theorem B3473600041 : Blo 1040609 3473600041 := bstep (se 2 (by rfl) ⟨1302600015, by rfl⟩ : syracuseStep 3473600041 = 2605200031) B2605200031
theorem B1044199 : Blo 1040609 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B5015611 : Blo 1040609 5015611 := bstep (se 1 (by rfl) ⟨3761708, by rfl⟩ : syracuseStep 5015611 = 7523417) B7523417
theorem B4631466721 : Blo 1040609 4631466721 := bstep (se 2 (by rfl) ⟨1736800020, by rfl⟩ : syracuseStep 4631466721 = 3473600041) B3473600041
theorem B36616223 : Blo 1040609 36616223 := bstep (se 1 (by rfl) ⟨27462167, by rfl⟩ : syracuseStep 36616223 = 54924335) B54924335
theorem B2344031 : Blo 1040609 2344031 := bstep (se 1 (by rfl) ⟨1758023, by rfl⟩ : syracuseStep 2344031 = 3516047) B3516047
theorem B2349215 : Blo 1040609 2349215 := bstep (se 1 (by rfl) ⟨1761911, by rfl⟩ : syracuseStep 2349215 = 3523823) B3523823
theorem B1043455 : Blo 1040609 1043455 := bstep (se 1 (by rfl) ⟨782591, by rfl⟩ : syracuseStep 1043455 = 1565183) B1565183
theorem B1043623 : Blo 1040609 1043623 := bstep (se 1 (by rfl) ⟨782717, by rfl⟩ : syracuseStep 1043623 = 1565435) B1565435
theorem B6687481 : Blo 1040609 6687481 := bstep (se 2 (by rfl) ⟨2507805, by rfl⟩ : syracuseStep 6687481 = 5015611) B5015611
theorem B1562687 : Blo 1040609 1562687 := bstep (se 1 (by rfl) ⟨1172015, by rfl⟩ : syracuseStep 1562687 = 2344031) B2344031
theorem B1566143 : Blo 1040609 1566143 := bstep (se 1 (by rfl) ⟨1174607, by rfl⟩ : syracuseStep 1566143 = 2349215) B2349215
theorem B6175288961 : Blo 1040609 6175288961 := bstep (se 2 (by rfl) ⟨2315733360, by rfl⟩ : syracuseStep 6175288961 = 4631466721) B4631466721
theorem B24410815 : Blo 1040609 24410815 := bstep (se 1 (by rfl) ⟨18308111, by rfl⟩ : syracuseStep 24410815 = 36616223) B36616223
theorem B8916641 : Blo 1040609 8916641 := bstep (se 2 (by rfl) ⟨3343740, by rfl⟩ : syracuseStep 8916641 = 6687481) B6687481
theorem B130191013 : Blo 1040609 130191013 := bstep (se 4 (by rfl) ⟨12205407, by rfl⟩ : syracuseStep 130191013 = 24410815) B24410815
theorem B4116859307 : Blo 1040609 4116859307 := bstep (se 1 (by rfl) ⟨3087644480, by rfl⟩ : syracuseStep 4116859307 = 6175288961) B6175288961
theorem B1041791 : Blo 1040609 1041791 := bstep (se 1 (by rfl) ⟨781343, by rfl⟩ : syracuseStep 1041791 = 1562687) B1562687
theorem B1044095 : Blo 1040609 1044095 := bstep (se 1 (by rfl) ⟨783071, by rfl⟩ : syracuseStep 1044095 = 1566143) B1566143
theorem B5944427 : Blo 1040609 5944427 := bstep (se 1 (by rfl) ⟨4458320, by rfl⟩ : syracuseStep 5944427 = 8916641) B8916641
theorem B173588017 : Blo 1040609 173588017 := bstep (se 2 (by rfl) ⟨65095506, by rfl⟩ : syracuseStep 173588017 = 130191013) B130191013
theorem B2744572871 : Blo 1040609 2744572871 := bstep (se 1 (by rfl) ⟨2058429653, by rfl⟩ : syracuseStep 2744572871 = 4116859307) B4116859307
theorem B231450689 : Blo 1040609 231450689 := bstep (se 2 (by rfl) ⟨86794008, by rfl⟩ : syracuseStep 231450689 = 173588017) B173588017
theorem B1829715247 : Blo 1040609 1829715247 := bstep (se 1 (by rfl) ⟨1372286435, by rfl⟩ : syracuseStep 1829715247 = 2744572871) B2744572871
theorem B3962951 : Blo 1040609 3962951 := bstep (se 1 (by rfl) ⟨2972213, by rfl⟩ : syracuseStep 3962951 = 5944427) B5944427
theorem B2439620329 : Blo 1040609 2439620329 := bstep (se 2 (by rfl) ⟨914857623, by rfl⟩ : syracuseStep 2439620329 = 1829715247) B1829715247
theorem B2641967 : Blo 1040609 2641967 := bstep (se 1 (by rfl) ⟨1981475, by rfl⟩ : syracuseStep 2641967 = 3962951) B3962951
theorem B154300459 : Blo 1040609 154300459 := bstep (se 1 (by rfl) ⟨115725344, by rfl⟩ : syracuseStep 154300459 = 231450689) B231450689
theorem B3252827105 : Blo 1040609 3252827105 := bstep (se 2 (by rfl) ⟨1219810164, by rfl⟩ : syracuseStep 3252827105 = 2439620329) B2439620329
theorem B205733945 : Blo 1040609 205733945 := bstep (se 2 (by rfl) ⟨77150229, by rfl⟩ : syracuseStep 205733945 = 154300459) B154300459
theorem B1761311 : Blo 1040609 1761311 := bstep (se 1 (by rfl) ⟨1320983, by rfl⟩ : syracuseStep 1761311 = 2641967) B2641967
theorem B137155963 : Blo 1040609 137155963 := bstep (se 1 (by rfl) ⟨102866972, by rfl⟩ : syracuseStep 137155963 = 205733945) B205733945
theorem B1174207 : Blo 1040609 1174207 := bstep (se 1 (by rfl) ⟨880655, by rfl⟩ : syracuseStep 1174207 = 1761311) B1761311
theorem B2168551403 : Blo 1040609 2168551403 := bstep (se 1 (by rfl) ⟨1626413552, by rfl⟩ : syracuseStep 2168551403 = 3252827105) B3252827105
theorem B1445700935 : Blo 1040609 1445700935 := bstep (se 1 (by rfl) ⟨1084275701, by rfl⟩ : syracuseStep 1445700935 = 2168551403) B2168551403
theorem B1565609 : Blo 1040609 1565609 := bstep (se 2 (by rfl) ⟨587103, by rfl⟩ : syracuseStep 1565609 = 1174207) B1174207
theorem B182874617 : Blo 1040609 182874617 := bstep (se 2 (by rfl) ⟨68577981, by rfl⟩ : syracuseStep 182874617 = 137155963) B137155963
theorem B121916411 : Blo 1040609 121916411 := bstep (se 1 (by rfl) ⟨91437308, by rfl⟩ : syracuseStep 121916411 = 182874617) B182874617
theorem B1043739 : Blo 1040609 1043739 := bstep (se 1 (by rfl) ⟨782804, by rfl⟩ : syracuseStep 1043739 = 1565609) B1565609
theorem B963800623 : Blo 1040609 963800623 := bstep (se 1 (by rfl) ⟨722850467, by rfl⟩ : syracuseStep 963800623 = 1445700935) B1445700935
theorem B81277607 : Blo 1040609 81277607 := bstep (se 1 (by rfl) ⟨60958205, by rfl⟩ : syracuseStep 81277607 = 121916411) B121916411
theorem B5140269989 : Blo 1040609 5140269989 := bstep (se 4 (by rfl) ⟨481900311, by rfl⟩ : syracuseStep 5140269989 = 963800623) B963800623
theorem B3426846659 : Blo 1040609 3426846659 := bstep (se 1 (by rfl) ⟨2570134994, by rfl⟩ : syracuseStep 3426846659 = 5140269989) B5140269989
theorem B54185071 : Blo 1040609 54185071 := bstep (se 1 (by rfl) ⟨40638803, by rfl⟩ : syracuseStep 54185071 = 81277607) B81277607
theorem B2284564439 : Blo 1040609 2284564439 := bstep (se 1 (by rfl) ⟨1713423329, by rfl⟩ : syracuseStep 2284564439 = 3426846659) B3426846659
theorem B72246761 : Blo 1040609 72246761 := bstep (se 2 (by rfl) ⟨27092535, by rfl⟩ : syracuseStep 72246761 = 54185071) B54185071
theorem B1523042959 : Blo 1040609 1523042959 := bstep (se 1 (by rfl) ⟨1142282219, by rfl⟩ : syracuseStep 1523042959 = 2284564439) B2284564439
theorem B48164507 : Blo 1040609 48164507 := bstep (se 1 (by rfl) ⟨36123380, by rfl⟩ : syracuseStep 48164507 = 72246761) B72246761
theorem B2030723945 : Blo 1040609 2030723945 := bstep (se 2 (by rfl) ⟨761521479, by rfl⟩ : syracuseStep 2030723945 = 1523042959) B1523042959
theorem B32109671 : Blo 1040609 32109671 := bstep (se 1 (by rfl) ⟨24082253, by rfl⟩ : syracuseStep 32109671 = 48164507) B48164507
theorem B1353815963 : Blo 1040609 1353815963 := bstep (se 1 (by rfl) ⟨1015361972, by rfl⟩ : syracuseStep 1353815963 = 2030723945) B2030723945
theorem B21406447 : Blo 1040609 21406447 := bstep (se 1 (by rfl) ⟨16054835, by rfl⟩ : syracuseStep 21406447 = 32109671) B32109671
theorem B28541929 : Blo 1040609 28541929 := bstep (se 2 (by rfl) ⟨10703223, by rfl⟩ : syracuseStep 28541929 = 21406447) B21406447
theorem B902543975 : Blo 1040609 902543975 := bstep (se 1 (by rfl) ⟨676907981, by rfl⟩ : syracuseStep 902543975 = 1353815963) B1353815963
theorem B601695983 : Blo 1040609 601695983 := bstep (se 1 (by rfl) ⟨451271987, by rfl⟩ : syracuseStep 601695983 = 902543975) B902543975
theorem B38055905 : Blo 1040609 38055905 := bstep (se 2 (by rfl) ⟨14270964, by rfl⟩ : syracuseStep 38055905 = 28541929) B28541929
theorem B1604522621 : Blo 1040609 1604522621 := bstep (se 3 (by rfl) ⟨300847991, by rfl⟩ : syracuseStep 1604522621 = 601695983) B601695983
theorem B25370603 : Blo 1040609 25370603 := bstep (se 1 (by rfl) ⟨19027952, by rfl⟩ : syracuseStep 25370603 = 38055905) B38055905
theorem B16913735 : Blo 1040609 16913735 := bstep (se 1 (by rfl) ⟨12685301, by rfl⟩ : syracuseStep 16913735 = 25370603) B25370603
theorem B4278726989 : Blo 1040609 4278726989 := bstep (se 3 (by rfl) ⟨802261310, by rfl⟩ : syracuseStep 4278726989 = 1604522621) B1604522621
theorem B11275823 : Blo 1040609 11275823 := bstep (se 1 (by rfl) ⟨8456867, by rfl⟩ : syracuseStep 11275823 = 16913735) B16913735
theorem B2852484659 : Blo 1040609 2852484659 := bstep (se 1 (by rfl) ⟨2139363494, by rfl⟩ : syracuseStep 2852484659 = 4278726989) B4278726989
theorem B7517215 : Blo 1040609 7517215 := bstep (se 1 (by rfl) ⟨5637911, by rfl⟩ : syracuseStep 7517215 = 11275823) B11275823
theorem B1901656439 : Blo 1040609 1901656439 := bstep (se 1 (by rfl) ⟨1426242329, by rfl⟩ : syracuseStep 1901656439 = 2852484659) B2852484659
theorem B1267770959 : Blo 1040609 1267770959 := bstep (se 1 (by rfl) ⟨950828219, by rfl⟩ : syracuseStep 1267770959 = 1901656439) B1901656439
theorem B10022953 : Blo 1040609 10022953 := bstep (se 2 (by rfl) ⟨3758607, by rfl⟩ : syracuseStep 10022953 = 7517215) B7517215
theorem B13363937 : Blo 1040609 13363937 := bstep (se 2 (by rfl) ⟨5011476, by rfl⟩ : syracuseStep 13363937 = 10022953) B10022953
theorem B845180639 : Blo 1040609 845180639 := bstep (se 1 (by rfl) ⟨633885479, by rfl⟩ : syracuseStep 845180639 = 1267770959) B1267770959
theorem B563453759 : Blo 1040609 563453759 := bstep (se 1 (by rfl) ⟨422590319, by rfl⟩ : syracuseStep 563453759 = 845180639) B845180639
theorem B8909291 : Blo 1040609 8909291 := bstep (se 1 (by rfl) ⟨6681968, by rfl⟩ : syracuseStep 8909291 = 13363937) B13363937
theorem B5939527 : Blo 1040609 5939527 := bstep (se 1 (by rfl) ⟨4454645, by rfl⟩ : syracuseStep 5939527 = 8909291) B8909291
theorem B1502543357 : Blo 1040609 1502543357 := bstep (se 3 (by rfl) ⟨281726879, by rfl⟩ : syracuseStep 1502543357 = 563453759) B563453759
theorem B1001695571 : Blo 1040609 1001695571 := bstep (se 1 (by rfl) ⟨751271678, by rfl⟩ : syracuseStep 1001695571 = 1502543357) B1502543357
theorem B7919369 : Blo 1040609 7919369 := bstep (se 2 (by rfl) ⟨2969763, by rfl⟩ : syracuseStep 7919369 = 5939527) B5939527
theorem B5279579 : Blo 1040609 5279579 := bstep (se 1 (by rfl) ⟨3959684, by rfl⟩ : syracuseStep 5279579 = 7919369) B7919369
theorem B667797047 : Blo 1040609 667797047 := bstep (se 1 (by rfl) ⟨500847785, by rfl⟩ : syracuseStep 667797047 = 1001695571) B1001695571
theorem B445198031 : Blo 1040609 445198031 := bstep (se 1 (by rfl) ⟨333898523, by rfl⟩ : syracuseStep 445198031 = 667797047) B667797047
theorem B3519719 : Blo 1040609 3519719 := bstep (se 1 (by rfl) ⟨2639789, by rfl⟩ : syracuseStep 3519719 = 5279579) B5279579
theorem B296798687 : Blo 1040609 296798687 := bstep (se 1 (by rfl) ⟨222599015, by rfl⟩ : syracuseStep 296798687 = 445198031) B445198031
theorem B2346479 : Blo 1040609 2346479 := bstep (se 1 (by rfl) ⟨1759859, by rfl⟩ : syracuseStep 2346479 = 3519719) B3519719
theorem B197865791 : Blo 1040609 197865791 := bstep (se 1 (by rfl) ⟨148399343, by rfl⟩ : syracuseStep 197865791 = 296798687) B296798687
theorem B1564319 : Blo 1040609 1564319 := bstep (se 1 (by rfl) ⟨1173239, by rfl⟩ : syracuseStep 1564319 = 2346479) B2346479
theorem B131910527 : Blo 1040609 131910527 := bstep (se 1 (by rfl) ⟨98932895, by rfl⟩ : syracuseStep 131910527 = 197865791) B197865791
theorem B1042879 : Blo 1040609 1042879 := bstep (se 1 (by rfl) ⟨782159, by rfl⟩ : syracuseStep 1042879 = 1564319) B1564319
theorem B87940351 : Blo 1040609 87940351 := bstep (se 1 (by rfl) ⟨65955263, by rfl⟩ : syracuseStep 87940351 = 131910527) B131910527
theorem B117253801 : Blo 1040609 117253801 := bstep (se 2 (by rfl) ⟨43970175, by rfl⟩ : syracuseStep 117253801 = 87940351) B87940351
theorem B625353605 : Blo 1040609 625353605 := bstep (se 4 (by rfl) ⟨58626900, by rfl⟩ : syracuseStep 625353605 = 117253801) B117253801
theorem B416902403 : Blo 1040609 416902403 := bstep (se 1 (by rfl) ⟨312676802, by rfl⟩ : syracuseStep 416902403 = 625353605) B625353605
theorem B1111739741 : Blo 1040609 1111739741 := bstep (se 3 (by rfl) ⟨208451201, by rfl⟩ : syracuseStep 1111739741 = 416902403) B416902403
theorem B741159827 : Blo 1040609 741159827 := bstep (se 1 (by rfl) ⟨555869870, by rfl⟩ : syracuseStep 741159827 = 1111739741) B1111739741
theorem B494106551 : Blo 1040609 494106551 := bstep (se 1 (by rfl) ⟨370579913, by rfl⟩ : syracuseStep 494106551 = 741159827) B741159827
theorem B329404367 : Blo 1040609 329404367 := bstep (se 1 (by rfl) ⟨247053275, by rfl⟩ : syracuseStep 329404367 = 494106551) B494106551
theorem B219602911 : Blo 1040609 219602911 := bstep (se 1 (by rfl) ⟨164702183, by rfl⟩ : syracuseStep 219602911 = 329404367) B329404367
theorem B292803881 : Blo 1040609 292803881 := bstep (se 2 (by rfl) ⟨109801455, by rfl⟩ : syracuseStep 292803881 = 219602911) B219602911
theorem B780810349 : Blo 1040609 780810349 := bstep (se 3 (by rfl) ⟨146401940, by rfl⟩ : syracuseStep 780810349 = 292803881) B292803881
theorem B1041080465 : Blo 1040609 1041080465 := bstep (se 2 (by rfl) ⟨390405174, by rfl⟩ : syracuseStep 1041080465 = 780810349) B780810349
theorem B694053643 : Blo 1040609 694053643 := bstep (se 1 (by rfl) ⟨520540232, by rfl⟩ : syracuseStep 694053643 = 1041080465) B1041080465
theorem B925404857 : Blo 1040609 925404857 := bstep (se 2 (by rfl) ⟨347026821, by rfl⟩ : syracuseStep 925404857 = 694053643) B694053643
theorem B616936571 : Blo 1040609 616936571 := bstep (se 1 (by rfl) ⟨462702428, by rfl⟩ : syracuseStep 616936571 = 925404857) B925404857
theorem B411291047 : Blo 1040609 411291047 := bstep (se 1 (by rfl) ⟨308468285, by rfl⟩ : syracuseStep 411291047 = 616936571) B616936571
theorem B1096776125 : Blo 1040609 1096776125 := bstep (se 3 (by rfl) ⟨205645523, by rfl⟩ : syracuseStep 1096776125 = 411291047) B411291047
theorem B731184083 : Blo 1040609 731184083 := bstep (se 1 (by rfl) ⟨548388062, by rfl⟩ : syracuseStep 731184083 = 1096776125) B1096776125
theorem B487456055 : Blo 1040609 487456055 := bstep (se 1 (by rfl) ⟨365592041, by rfl⟩ : syracuseStep 487456055 = 731184083) B731184083
theorem B324970703 : Blo 1040609 324970703 := bstep (se 1 (by rfl) ⟨243728027, by rfl⟩ : syracuseStep 324970703 = 487456055) B487456055
theorem B216647135 : Blo 1040609 216647135 := bstep (se 1 (by rfl) ⟨162485351, by rfl⟩ : syracuseStep 216647135 = 324970703) B324970703
theorem B144431423 : Blo 1040609 144431423 := bstep (se 1 (by rfl) ⟨108323567, by rfl⟩ : syracuseStep 144431423 = 216647135) B216647135
theorem B96287615 : Blo 1040609 96287615 := bstep (se 1 (by rfl) ⟨72215711, by rfl⟩ : syracuseStep 96287615 = 144431423) B144431423
theorem B64191743 : Blo 1040609 64191743 := bstep (se 1 (by rfl) ⟨48143807, by rfl⟩ : syracuseStep 64191743 = 96287615) B96287615
theorem B42794495 : Blo 1040609 42794495 := bstep (se 1 (by rfl) ⟨32095871, by rfl⟩ : syracuseStep 42794495 = 64191743) B64191743
theorem B28529663 : Blo 1040609 28529663 := bstep (se 1 (by rfl) ⟨21397247, by rfl⟩ : syracuseStep 28529663 = 42794495) B42794495
theorem B76079101 : Blo 1040609 76079101 := bstep (se 3 (by rfl) ⟨14264831, by rfl⟩ : syracuseStep 76079101 = 28529663) B28529663
theorem B101438801 : Blo 1040609 101438801 := bstep (se 2 (by rfl) ⟨38039550, by rfl⟩ : syracuseStep 101438801 = 76079101) B76079101
theorem B67625867 : Blo 1040609 67625867 := bstep (se 1 (by rfl) ⟨50719400, by rfl⟩ : syracuseStep 67625867 = 101438801) B101438801
theorem B45083911 : Blo 1040609 45083911 := bstep (se 1 (by rfl) ⟨33812933, by rfl⟩ : syracuseStep 45083911 = 67625867) B67625867
theorem B60111881 : Blo 1040609 60111881 := bstep (se 2 (by rfl) ⟨22541955, by rfl⟩ : syracuseStep 60111881 = 45083911) B45083911
theorem B40074587 : Blo 1040609 40074587 := bstep (se 1 (by rfl) ⟨30055940, by rfl⟩ : syracuseStep 40074587 = 60111881) B60111881
theorem B26716391 : Blo 1040609 26716391 := bstep (se 1 (by rfl) ⟨20037293, by rfl⟩ : syracuseStep 26716391 = 40074587) B40074587
theorem B17810927 : Blo 1040609 17810927 := bstep (se 1 (by rfl) ⟨13358195, by rfl⟩ : syracuseStep 17810927 = 26716391) B26716391
theorem B11873951 : Blo 1040609 11873951 := bstep (se 1 (by rfl) ⟨8905463, by rfl⟩ : syracuseStep 11873951 = 17810927) B17810927
theorem B7915967 : Blo 1040609 7915967 := bstep (se 1 (by rfl) ⟨5936975, by rfl⟩ : syracuseStep 7915967 = 11873951) B11873951
theorem B5277311 : Blo 1040609 5277311 := bstep (se 1 (by rfl) ⟨3957983, by rfl⟩ : syracuseStep 5277311 = 7915967) B7915967
theorem B3518207 : Blo 1040609 3518207 := bstep (se 1 (by rfl) ⟨2638655, by rfl⟩ : syracuseStep 3518207 = 5277311) B5277311
theorem B2345471 : Blo 1040609 2345471 := bstep (se 1 (by rfl) ⟨1759103, by rfl⟩ : syracuseStep 2345471 = 3518207) B3518207
theorem B1563647 : Blo 1040609 1563647 := bstep (se 1 (by rfl) ⟨1172735, by rfl⟩ : syracuseStep 1563647 = 2345471) B2345471
theorem B1042431 : Blo 1040609 1042431 := bstep (se 1 (by rfl) ⟨781823, by rfl⟩ : syracuseStep 1042431 = 1563647) B1563647

theorem C0 (j : ℕ) (h1 : 260152 ≤ j) (h2 : j ≤ 260851) : Blo 1040609 (4 * j + 3) := by
  interval_cases j
  · exact B1040611
  · exact B1040615
  · exact B1040619
  · exact B1040623
  · exact B1040627
  · exact B1040631
  · exact B1040635
  · exact B1040639
  · exact B1040643
  · exact B1040647
  · exact B1040651
  · exact B1040655
  · exact B1040659
  · exact B1040663
  · exact B1040667
  · exact B1040671
  · exact B1040675
  · exact B1040679
  · exact B1040683
  · exact B1040687
  · exact B1040691
  · exact B1040695
  · exact B1040699
  · exact B1040703
  · exact B1040707
  · exact B1040711
  · exact B1040715
  · exact B1040719
  · exact B1040723
  · exact B1040727
  · exact B1040731
  · exact B1040735
  · exact B1040739
  · exact B1040743
  · exact B1040747
  · exact B1040751
  · exact B1040755
  · exact B1040759
  · exact B1040763
  · exact B1040767
  · exact B1040771
  · exact B1040775
  · exact B1040779
  · exact B1040783
  · exact B1040787
  · exact B1040791
  · exact B1040795
  · exact B1040799
  · exact B1040803
  · exact B1040807
  · exact B1040811
  · exact B1040815
  · exact B1040819
  · exact B1040823
  · exact B1040827
  · exact B1040831
  · exact B1040835
  · exact B1040839
  · exact B1040843
  · exact B1040847
  · exact B1040851
  · exact B1040855
  · exact B1040859
  · exact B1040863
  · exact B1040867
  · exact B1040871
  · exact B1040875
  · exact B1040879
  · exact B1040883
  · exact B1040887
  · exact B1040891
  · exact B1040895
  · exact B1040899
  · exact B1040903
  · exact B1040907
  · exact B1040911
  · exact B1040915
  · exact B1040919
  · exact B1040923
  · exact B1040927
  · exact B1040931
  · exact B1040935
  · exact B1040939
  · exact B1040943
  · exact B1040947
  · exact B1040951
  · exact B1040955
  · exact B1040959
  · exact B1040963
  · exact B1040967
  · exact B1040971
  · exact B1040975
  · exact B1040979
  · exact B1040983
  · exact B1040987
  · exact B1040991
  · exact B1040995
  · exact B1040999
  · exact B1041003
  · exact B1041007
  · exact B1041011
  · exact B1041015
  · exact B1041019
  · exact B1041023
  · exact B1041027
  · exact B1041031
  · exact B1041035
  · exact B1041039
  · exact B1041043
  · exact B1041047
  · exact B1041051
  · exact B1041055
  · exact B1041059
  · exact B1041063
  · exact B1041067
  · exact B1041071
  · exact B1041075
  · exact B1041079
  · exact B1041083
  · exact B1041087
  · exact B1041091
  · exact B1041095
  · exact B1041099
  · exact B1041103
  · exact B1041107
  · exact B1041111
  · exact B1041115
  · exact B1041119
  · exact B1041123
  · exact B1041127
  · exact B1041131
  · exact B1041135
  · exact B1041139
  · exact B1041143
  · exact B1041147
  · exact B1041151
  · exact B1041155
  · exact B1041159
  · exact B1041163
  · exact B1041167
  · exact B1041171
  · exact B1041175
  · exact B1041179
  · exact B1041183
  · exact B1041187
  · exact B1041191
  · exact B1041195
  · exact B1041199
  · exact B1041203
  · exact B1041207
  · exact B1041211
  · exact B1041215
  · exact B1041219
  · exact B1041223
  · exact B1041227
  · exact B1041231
  · exact B1041235
  · exact B1041239
  · exact B1041243
  · exact B1041247
  · exact B1041251
  · exact B1041255
  · exact B1041259
  · exact B1041263
  · exact B1041267
  · exact B1041271
  · exact B1041275
  · exact B1041279
  · exact B1041283
  · exact B1041287
  · exact B1041291
  · exact B1041295
  · exact B1041299
  · exact B1041303
  · exact B1041307
  · exact B1041311
  · exact B1041315
  · exact B1041319
  · exact B1041323
  · exact B1041327
  · exact B1041331
  · exact B1041335
  · exact B1041339
  · exact B1041343
  · exact B1041347
  · exact B1041351
  · exact B1041355
  · exact B1041359
  · exact B1041363
  · exact B1041367
  · exact B1041371
  · exact B1041375
  · exact B1041379
  · exact B1041383
  · exact B1041387
  · exact B1041391
  · exact B1041395
  · exact B1041399
  · exact B1041403
  · exact B1041407
  · exact B1041411
  · exact B1041415
  · exact B1041419
  · exact B1041423
  · exact B1041427
  · exact B1041431
  · exact B1041435
  · exact B1041439
  · exact B1041443
  · exact B1041447
  · exact B1041451
  · exact B1041455
  · exact B1041459
  · exact B1041463
  · exact B1041467
  · exact B1041471
  · exact B1041475
  · exact B1041479
  · exact B1041483
  · exact B1041487
  · exact B1041491
  · exact B1041495
  · exact B1041499
  · exact B1041503
  · exact B1041507
  · exact B1041511
  · exact B1041515
  · exact B1041519
  · exact B1041523
  · exact B1041527
  · exact B1041531
  · exact B1041535
  · exact B1041539
  · exact B1041543
  · exact B1041547
  · exact B1041551
  · exact B1041555
  · exact B1041559
  · exact B1041563
  · exact B1041567
  · exact B1041571
  · exact B1041575
  · exact B1041579
  · exact B1041583
  · exact B1041587
  · exact B1041591
  · exact B1041595
  · exact B1041599
  · exact B1041603
  · exact B1041607
  · exact B1041611
  · exact B1041615
  · exact B1041619
  · exact B1041623
  · exact B1041627
  · exact B1041631
  · exact B1041635
  · exact B1041639
  · exact B1041643
  · exact B1041647
  · exact B1041651
  · exact B1041655
  · exact B1041659
  · exact B1041663
  · exact B1041667
  · exact B1041671
  · exact B1041675
  · exact B1041679
  · exact B1041683
  · exact B1041687
  · exact B1041691
  · exact B1041695
  · exact B1041699
  · exact B1041703
  · exact B1041707
  · exact B1041711
  · exact B1041715
  · exact B1041719
  · exact B1041723
  · exact B1041727
  · exact B1041731
  · exact B1041735
  · exact B1041739
  · exact B1041743
  · exact B1041747
  · exact B1041751
  · exact B1041755
  · exact B1041759
  · exact B1041763
  · exact B1041767
  · exact B1041771
  · exact B1041775
  · exact B1041779
  · exact B1041783
  · exact B1041787
  · exact B1041791
  · exact B1041795
  · exact B1041799
  · exact B1041803
  · exact B1041807
  · exact B1041811
  · exact B1041815
  · exact B1041819
  · exact B1041823
  · exact B1041827
  · exact B1041831
  · exact B1041835
  · exact B1041839
  · exact B1041843
  · exact B1041847
  · exact B1041851
  · exact B1041855
  · exact B1041859
  · exact B1041863
  · exact B1041867
  · exact B1041871
  · exact B1041875
  · exact B1041879
  · exact B1041883
  · exact B1041887
  · exact B1041891
  · exact B1041895
  · exact B1041899
  · exact B1041903
  · exact B1041907
  · exact B1041911
  · exact B1041915
  · exact B1041919
  · exact B1041923
  · exact B1041927
  · exact B1041931
  · exact B1041935
  · exact B1041939
  · exact B1041943
  · exact B1041947
  · exact B1041951
  · exact B1041955
  · exact B1041959
  · exact B1041963
  · exact B1041967
  · exact B1041971
  · exact B1041975
  · exact B1041979
  · exact B1041983
  · exact B1041987
  · exact B1041991
  · exact B1041995
  · exact B1041999
  · exact B1042003
  · exact B1042007
  · exact B1042011
  · exact B1042015
  · exact B1042019
  · exact B1042023
  · exact B1042027
  · exact B1042031
  · exact B1042035
  · exact B1042039
  · exact B1042043
  · exact B1042047
  · exact B1042051
  · exact B1042055
  · exact B1042059
  · exact B1042063
  · exact B1042067
  · exact B1042071
  · exact B1042075
  · exact B1042079
  · exact B1042083
  · exact B1042087
  · exact B1042091
  · exact B1042095
  · exact B1042099
  · exact B1042103
  · exact B1042107
  · exact B1042111
  · exact B1042115
  · exact B1042119
  · exact B1042123
  · exact B1042127
  · exact B1042131
  · exact B1042135
  · exact B1042139
  · exact B1042143
  · exact B1042147
  · exact B1042151
  · exact B1042155
  · exact B1042159
  · exact B1042163
  · exact B1042167
  · exact B1042171
  · exact B1042175
  · exact B1042179
  · exact B1042183
  · exact B1042187
  · exact B1042191
  · exact B1042195
  · exact B1042199
  · exact B1042203
  · exact B1042207
  · exact B1042211
  · exact B1042215
  · exact B1042219
  · exact B1042223
  · exact B1042227
  · exact B1042231
  · exact B1042235
  · exact B1042239
  · exact B1042243
  · exact B1042247
  · exact B1042251
  · exact B1042255
  · exact B1042259
  · exact B1042263
  · exact B1042267
  · exact B1042271
  · exact B1042275
  · exact B1042279
  · exact B1042283
  · exact B1042287
  · exact B1042291
  · exact B1042295
  · exact B1042299
  · exact B1042303
  · exact B1042307
  · exact B1042311
  · exact B1042315
  · exact B1042319
  · exact B1042323
  · exact B1042327
  · exact B1042331
  · exact B1042335
  · exact B1042339
  · exact B1042343
  · exact B1042347
  · exact B1042351
  · exact B1042355
  · exact B1042359
  · exact B1042363
  · exact B1042367
  · exact B1042371
  · exact B1042375
  · exact B1042379
  · exact B1042383
  · exact B1042387
  · exact B1042391
  · exact B1042395
  · exact B1042399
  · exact B1042403
  · exact B1042407
  · exact B1042411
  · exact B1042415
  · exact B1042419
  · exact B1042423
  · exact B1042427
  · exact B1042431
  · exact B1042435
  · exact B1042439
  · exact B1042443
  · exact B1042447
  · exact B1042451
  · exact B1042455
  · exact B1042459
  · exact B1042463
  · exact B1042467
  · exact B1042471
  · exact B1042475
  · exact B1042479
  · exact B1042483
  · exact B1042487
  · exact B1042491
  · exact B1042495
  · exact B1042499
  · exact B1042503
  · exact B1042507
  · exact B1042511
  · exact B1042515
  · exact B1042519
  · exact B1042523
  · exact B1042527
  · exact B1042531
  · exact B1042535
  · exact B1042539
  · exact B1042543
  · exact B1042547
  · exact B1042551
  · exact B1042555
  · exact B1042559
  · exact B1042563
  · exact B1042567
  · exact B1042571
  · exact B1042575
  · exact B1042579
  · exact B1042583
  · exact B1042587
  · exact B1042591
  · exact B1042595
  · exact B1042599
  · exact B1042603
  · exact B1042607
  · exact B1042611
  · exact B1042615
  · exact B1042619
  · exact B1042623
  · exact B1042627
  · exact B1042631
  · exact B1042635
  · exact B1042639
  · exact B1042643
  · exact B1042647
  · exact B1042651
  · exact B1042655
  · exact B1042659
  · exact B1042663
  · exact B1042667
  · exact B1042671
  · exact B1042675
  · exact B1042679
  · exact B1042683
  · exact B1042687
  · exact B1042691
  · exact B1042695
  · exact B1042699
  · exact B1042703
  · exact B1042707
  · exact B1042711
  · exact B1042715
  · exact B1042719
  · exact B1042723
  · exact B1042727
  · exact B1042731
  · exact B1042735
  · exact B1042739
  · exact B1042743
  · exact B1042747
  · exact B1042751
  · exact B1042755
  · exact B1042759
  · exact B1042763
  · exact B1042767
  · exact B1042771
  · exact B1042775
  · exact B1042779
  · exact B1042783
  · exact B1042787
  · exact B1042791
  · exact B1042795
  · exact B1042799
  · exact B1042803
  · exact B1042807
  · exact B1042811
  · exact B1042815
  · exact B1042819
  · exact B1042823
  · exact B1042827
  · exact B1042831
  · exact B1042835
  · exact B1042839
  · exact B1042843
  · exact B1042847
  · exact B1042851
  · exact B1042855
  · exact B1042859
  · exact B1042863
  · exact B1042867
  · exact B1042871
  · exact B1042875
  · exact B1042879
  · exact B1042883
  · exact B1042887
  · exact B1042891
  · exact B1042895
  · exact B1042899
  · exact B1042903
  · exact B1042907
  · exact B1042911
  · exact B1042915
  · exact B1042919
  · exact B1042923
  · exact B1042927
  · exact B1042931
  · exact B1042935
  · exact B1042939
  · exact B1042943
  · exact B1042947
  · exact B1042951
  · exact B1042955
  · exact B1042959
  · exact B1042963
  · exact B1042967
  · exact B1042971
  · exact B1042975
  · exact B1042979
  · exact B1042983
  · exact B1042987
  · exact B1042991
  · exact B1042995
  · exact B1042999
  · exact B1043003
  · exact B1043007
  · exact B1043011
  · exact B1043015
  · exact B1043019
  · exact B1043023
  · exact B1043027
  · exact B1043031
  · exact B1043035
  · exact B1043039
  · exact B1043043
  · exact B1043047
  · exact B1043051
  · exact B1043055
  · exact B1043059
  · exact B1043063
  · exact B1043067
  · exact B1043071
  · exact B1043075
  · exact B1043079
  · exact B1043083
  · exact B1043087
  · exact B1043091
  · exact B1043095
  · exact B1043099
  · exact B1043103
  · exact B1043107
  · exact B1043111
  · exact B1043115
  · exact B1043119
  · exact B1043123
  · exact B1043127
  · exact B1043131
  · exact B1043135
  · exact B1043139
  · exact B1043143
  · exact B1043147
  · exact B1043151
  · exact B1043155
  · exact B1043159
  · exact B1043163
  · exact B1043167
  · exact B1043171
  · exact B1043175
  · exact B1043179
  · exact B1043183
  · exact B1043187
  · exact B1043191
  · exact B1043195
  · exact B1043199
  · exact B1043203
  · exact B1043207
  · exact B1043211
  · exact B1043215
  · exact B1043219
  · exact B1043223
  · exact B1043227
  · exact B1043231
  · exact B1043235
  · exact B1043239
  · exact B1043243
  · exact B1043247
  · exact B1043251
  · exact B1043255
  · exact B1043259
  · exact B1043263
  · exact B1043267
  · exact B1043271
  · exact B1043275
  · exact B1043279
  · exact B1043283
  · exact B1043287
  · exact B1043291
  · exact B1043295
  · exact B1043299
  · exact B1043303
  · exact B1043307
  · exact B1043311
  · exact B1043315
  · exact B1043319
  · exact B1043323
  · exact B1043327
  · exact B1043331
  · exact B1043335
  · exact B1043339
  · exact B1043343
  · exact B1043347
  · exact B1043351
  · exact B1043355
  · exact B1043359
  · exact B1043363
  · exact B1043367
  · exact B1043371
  · exact B1043375
  · exact B1043379
  · exact B1043383
  · exact B1043387
  · exact B1043391
  · exact B1043395
  · exact B1043399
  · exact B1043403
  · exact B1043407

theorem C1 (j : ℕ) (h1 : 260852 ≤ j) (h2 : j ≤ 261151) : Blo 1040609 (4 * j + 3) := by
  interval_cases j
  · exact B1043411
  · exact B1043415
  · exact B1043419
  · exact B1043423
  · exact B1043427
  · exact B1043431
  · exact B1043435
  · exact B1043439
  · exact B1043443
  · exact B1043447
  · exact B1043451
  · exact B1043455
  · exact B1043459
  · exact B1043463
  · exact B1043467
  · exact B1043471
  · exact B1043475
  · exact B1043479
  · exact B1043483
  · exact B1043487
  · exact B1043491
  · exact B1043495
  · exact B1043499
  · exact B1043503
  · exact B1043507
  · exact B1043511
  · exact B1043515
  · exact B1043519
  · exact B1043523
  · exact B1043527
  · exact B1043531
  · exact B1043535
  · exact B1043539
  · exact B1043543
  · exact B1043547
  · exact B1043551
  · exact B1043555
  · exact B1043559
  · exact B1043563
  · exact B1043567
  · exact B1043571
  · exact B1043575
  · exact B1043579
  · exact B1043583
  · exact B1043587
  · exact B1043591
  · exact B1043595
  · exact B1043599
  · exact B1043603
  · exact B1043607
  · exact B1043611
  · exact B1043615
  · exact B1043619
  · exact B1043623
  · exact B1043627
  · exact B1043631
  · exact B1043635
  · exact B1043639
  · exact B1043643
  · exact B1043647
  · exact B1043651
  · exact B1043655
  · exact B1043659
  · exact B1043663
  · exact B1043667
  · exact B1043671
  · exact B1043675
  · exact B1043679
  · exact B1043683
  · exact B1043687
  · exact B1043691
  · exact B1043695
  · exact B1043699
  · exact B1043703
  · exact B1043707
  · exact B1043711
  · exact B1043715
  · exact B1043719
  · exact B1043723
  · exact B1043727
  · exact B1043731
  · exact B1043735
  · exact B1043739
  · exact B1043743
  · exact B1043747
  · exact B1043751
  · exact B1043755
  · exact B1043759
  · exact B1043763
  · exact B1043767
  · exact B1043771
  · exact B1043775
  · exact B1043779
  · exact B1043783
  · exact B1043787
  · exact B1043791
  · exact B1043795
  · exact B1043799
  · exact B1043803
  · exact B1043807
  · exact B1043811
  · exact B1043815
  · exact B1043819
  · exact B1043823
  · exact B1043827
  · exact B1043831
  · exact B1043835
  · exact B1043839
  · exact B1043843
  · exact B1043847
  · exact B1043851
  · exact B1043855
  · exact B1043859
  · exact B1043863
  · exact B1043867
  · exact B1043871
  · exact B1043875
  · exact B1043879
  · exact B1043883
  · exact B1043887
  · exact B1043891
  · exact B1043895
  · exact B1043899
  · exact B1043903
  · exact B1043907
  · exact B1043911
  · exact B1043915
  · exact B1043919
  · exact B1043923
  · exact B1043927
  · exact B1043931
  · exact B1043935
  · exact B1043939
  · exact B1043943
  · exact B1043947
  · exact B1043951
  · exact B1043955
  · exact B1043959
  · exact B1043963
  · exact B1043967
  · exact B1043971
  · exact B1043975
  · exact B1043979
  · exact B1043983
  · exact B1043987
  · exact B1043991
  · exact B1043995
  · exact B1043999
  · exact B1044003
  · exact B1044007
  · exact B1044011
  · exact B1044015
  · exact B1044019
  · exact B1044023
  · exact B1044027
  · exact B1044031
  · exact B1044035
  · exact B1044039
  · exact B1044043
  · exact B1044047
  · exact B1044051
  · exact B1044055
  · exact B1044059
  · exact B1044063
  · exact B1044067
  · exact B1044071
  · exact B1044075
  · exact B1044079
  · exact B1044083
  · exact B1044087
  · exact B1044091
  · exact B1044095
  · exact B1044099
  · exact B1044103
  · exact B1044107
  · exact B1044111
  · exact B1044115
  · exact B1044119
  · exact B1044123
  · exact B1044127
  · exact B1044131
  · exact B1044135
  · exact B1044139
  · exact B1044143
  · exact B1044147
  · exact B1044151
  · exact B1044155
  · exact B1044159
  · exact B1044163
  · exact B1044167
  · exact B1044171
  · exact B1044175
  · exact B1044179
  · exact B1044183
  · exact B1044187
  · exact B1044191
  · exact B1044195
  · exact B1044199
  · exact B1044203
  · exact B1044207
  · exact B1044211
  · exact B1044215
  · exact B1044219
  · exact B1044223
  · exact B1044227
  · exact B1044231
  · exact B1044235
  · exact B1044239
  · exact B1044243
  · exact B1044247
  · exact B1044251
  · exact B1044255
  · exact B1044259
  · exact B1044263
  · exact B1044267
  · exact B1044271
  · exact B1044275
  · exact B1044279
  · exact B1044283
  · exact B1044287
  · exact B1044291
  · exact B1044295
  · exact B1044299
  · exact B1044303
  · exact B1044307
  · exact B1044311
  · exact B1044315
  · exact B1044319
  · exact B1044323
  · exact B1044327
  · exact B1044331
  · exact B1044335
  · exact B1044339
  · exact B1044343
  · exact B1044347
  · exact B1044351
  · exact B1044355
  · exact B1044359
  · exact B1044363
  · exact B1044367
  · exact B1044371
  · exact B1044375
  · exact B1044379
  · exact B1044383
  · exact B1044387
  · exact B1044391
  · exact B1044395
  · exact B1044399
  · exact B1044403
  · exact B1044407
  · exact B1044411
  · exact B1044415
  · exact B1044419
  · exact B1044423
  · exact B1044427
  · exact B1044431
  · exact B1044435
  · exact B1044439
  · exact B1044443
  · exact B1044447
  · exact B1044451
  · exact B1044455
  · exact B1044459
  · exact B1044463
  · exact B1044467
  · exact B1044471
  · exact B1044475
  · exact B1044479
  · exact B1044483
  · exact B1044487
  · exact B1044491
  · exact B1044495
  · exact B1044499
  · exact B1044503
  · exact B1044507
  · exact B1044511
  · exact B1044515
  · exact B1044519
  · exact B1044523
  · exact B1044527
  · exact B1044531
  · exact B1044535
  · exact B1044539
  · exact B1044543
  · exact B1044547
  · exact B1044551
  · exact B1044555
  · exact B1044559
  · exact B1044563
  · exact B1044567
  · exact B1044571
  · exact B1044575
  · exact B1044579
  · exact B1044583
  · exact B1044587
  · exact B1044591
  · exact B1044595
  · exact B1044599
  · exact B1044603
  · exact B1044607

theorem solution (m : ℕ) (hlo : 1040609 ≤ m) (hhi : m ≤ 1044609) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 260152 ≤ j := by omega
    have hj2 : j ≤ 261151 := by omega
    have hb : Blo 1040609 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 260852 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
